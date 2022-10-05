{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnicodeSyntax   #-}
{-# LANGUAGE ViewPatterns    #-}

module GHC.Definitions.TH (
  Config (..), autoConfig, defaultConfig,
  makeDefinitions, makeDefinitionsWithConfig,
  makePattern
) where

import Data.Char       (toLower)
import Data.Constraint (Dict (..))
import Data.Maybe      (fromJust, fromMaybe)

import Language.Haskell.TH.Lib    (appE, bang, bangType, bindS, clause, conT,
                                   cxt, dataD, doE, explBidir, fieldExp,
                                   forallT, funD, implicitParamBindD,
                                   implicitParamT, implicitParamVarE, letS,
                                   noBindS, noSourceStrictness,
                                   noSourceUnpackedness, normalB, patSynD,
                                   patSynSigD, prefixPatSyn, recC, recConE,
                                   sigD, tySynD, varBangType, varE, varP, varT)
import Language.Haskell.TH.Syntax (Dec, Exp, Info (..), Lift (..), Name, Pat, Q,
                                   Quasi (..), Stmt, Type (..), VarBangType,
                                   mkName, nameBase, nameModule)

import qualified GHC.Core.Class as GHC
import qualified GHC.Plugins    as GHC
import qualified GHC.Tc.Plugin  as GHC

data Config = Config
  { recordName     ∷ String
  , implicitName   ∷ String
  , constraintName ∷ String
  , functionName   ∷ String
  , operatorTable  ∷ [(Char, String)]
  }

autoConfig ∷ String → Config
autoConfig name = Config
  { recordName     = name ++ "Record"
  , implicitName   = lower name
  , constraintName = name
  , functionName   = "find" ++ name
  , operatorTable  =
      [ ('+',  "Plus")
      , ('-',  "Minus")
      , ('*',  "Star")
      , ('=',  "Equals")
      , ('#',  "Hash")
      , ('!',  "Bang")
      , ('@',  "At")
      , ('$',  "Dollar")
      , ('%',  "Percent")
      , ('^',  "Accent")
      , ('&',  "And")
      , ('<',  "Less")
      , ('>',  "Greater")
      , ('?',  "Question")
      , ('|',  "Pipe")
      , ('/',  "Slash")
      , ('\\', "Backslash")
      , ('.',  "Dot")
      , ('~',  "Tilde")
      ]
  }

defaultConfig ∷ Config
defaultConfig = autoConfig "Definitions"

-- | Given a list of names @names@, @makeDefinitions@ constructs the following:
--
-- 1. A constraint @Definitions@.
-- 2. A function @findDefinitions ∷ 'GHC.TcPluginM' ('Dict' Definitions)@
-- 3. For each @name ∈ names@, a function @name⟨type⟩ ∷ Definitions ⇒
--    ⟨type⟩@, where @⟨type⟩@ is determined by whatever @name@ refers to, i.e. a
--    data constructor @('GHC.DataCon')@, function or value @('GHC.Var')@, or
--    type constructor @('GHC.TyCon')@.
makeDefinitions ∷ [Name] → Q [Dec]
makeDefinitions = makeDefinitionsWithConfig defaultConfig

-- | Like 'makeDefinitions', but allows some control over the generated names.
makeDefinitionsWithConfig ∷ Config → [Name] → Q [Dec]
makeDefinitionsWithConfig
    Config
      { recordName     = (mkName → recordN)
      , implicitName   = implicitN
      , constraintName = (mkName → constraintN)
      , functionName   = (mkName → functionN)
      , operatorTable  = opTable
      }
    names =
  mkConstraintTy +:
  mkRecordTy     +:
  mkFunction     +++
  concatMapM mkAccessor names
 where
  concatMapM ∷ Monad m ⇒ (a → m [b]) → [a] → m [b]
  concatMapM f = fmap concat . traverse f

  mkConstraintTy ∷  Q Dec
  mkConstraintTy = tySynD constraintN [] (implicitParamT implicitN (conT recordN))

  mkRecordTy ∷ Q Dec
  mkRecordTy = dataD (cxt []) recordN [] Nothing [recC recordN (map mkField names)] []

  mkFieldName ∷ Name → Q Name
  mkFieldName = fmap (mkName . ("_" ++) . nameBase) . mkAccessorName

  mkFieldName' ∷ Name → Q Name
  mkFieldName' = fmap (mkName . ("__" ++) . nameBase) . mkAccessorName

  mkField ∷ Name → Q VarBangType
  mkField name = do
    name' ← mkFieldName name
    varBangType name' (bangType
      (bang noSourceUnpackedness noSourceStrictness)
      (mkFieldType name))

  mkFieldType ∷ Name → Q Type
  mkFieldType name = do
    info ← qReify name
    case info of
      ClassI {}     → [t|GHC.Class|]
      ClassOpI {}   → [t|GHC.Var|]
      TyConI {}     → [t|GHC.TyCon|]
      FamilyI {}    → [t|GHC.TyCon|]
      PrimTyConI {} → [t|GHC.TyCon|]
      DataConI {}   → [t|GHC.DataCon|]
      VarI {}       → [t|GHC.Var|]
      PatSynI {}    → error "Don't know what to do with pattern synonyms yet..."
      TyVarI {}     → error "Unexpected type variable name"

  mkFunction ∷ Q [Dec]
  mkFunction = sequence
    [ sigD functionN [t| GHC.TcPluginM (Dict $(conT constraintN)) |]
    , funD functionN [clause []
        (normalB (doE
          ( map mkFunctionStmt names ++
          [ letS [implicitParamBindD implicitN (recConE recordN (map mkRecordExp names))]
          , noBindS [e|return Dict|]
          ] )))
        []]
    ]

  mkFunctionStmt ∷ Name → Q Stmt
  mkFunctionStmt name = do
    name' ← mkFieldName' name
    bindS (varP name') (mkFunctionExp name)

  mkFunctionExp ∷ Name → Q Exp
  mkFunctionExp name = do
    let md = lift (fromJust (nameModule name))
        on = lift (alphaNumNameBase name)
    info ← qReify name
    case info of
      ClassI {}     → [e|lookupClass   $md $on|]
      ClassOpI {}   → [e|lookupVar     $md $on|]
      TyConI {}     → [e|lookupTyCon   $md $on|]
      FamilyI {}    → [e|lookupTyCon   $md $on|]
      PrimTyConI {} → [e|lookupTyCon   $md $on|]
      DataConI {}   → [e|lookupDataCon $md $on|]
      VarI {}       → [e|lookupVar     $md $on|]
      PatSynI {}    → error "Don't know what to do with pattern synonyms yet..."
      TyVarI {}     → error "Unexpeced type variable name"

  mkRecordExp ∷ Name → Q (Name, Exp)
  mkRecordExp name = do
    name'  ← mkFieldName  name
    name'' ← mkFieldName' name
    fieldExp name' (varE name'')

  mkAccessor ∷ Name → Q [Dec]
  mkAccessor name = do
    acc     ← mkAccessorName name
    promote ← isDataCon      name
    name'   ← mkFieldName    name
    let defaultDefs =
          [ sigD acc [t| $(conT constraintN) ⇒ $(mkFieldType name) |]
          , funD acc [clause []
              (normalB
                (appE (varE name') (implicitParamVarE implicitN)))
              []]
          ]
        promotedDefs =
          [ sigD (mkPromotedAccessorName name) [t| $(conT constraintN) ⇒ GHC.TyCon |]
          , funD (mkPromotedAccessorName name) [clause [] (normalB [e| GHC.promoteDataCon $(varE acc)|]) []]
          ]
    sequence (defaultDefs ++ (if promote then promotedDefs else []))

  mkAccessorName ∷ Quasi m ⇒ Name → m Name
  mkAccessorName name = do
    info ← qReify name
    return . mkName . lower $ case info of
      ClassI {}     → alphaNumNameBase name ++ "Class"
      ClassOpI {}   → alphaNumNameBase name ++ "Var"
      TyConI {}     → alphaNumNameBase name ++ "TyCon"
      FamilyI {}    → alphaNumNameBase name ++ "TyCon"
      PrimTyConI {} → alphaNumNameBase name ++ "TyCon"
      DataConI {}   → alphaNumNameBase name ++ "DataCon"
      VarI {}       → alphaNumNameBase name ++ "Var"
      PatSynI {}    → error "Don't know what to do with pattern synonyms yet..."
      TyVarI {}     → error "Unexpected type variable name"

  mkPromotedAccessorName ∷ Name → Name
  mkPromotedAccessorName name = mkName ("promoted" ++ alphaNumNameBase name ++ "TyCon")

  isDataCon ∷ Quasi m ⇒ Name → m Bool
  isDataCon name = do
    info ← qReify name
    case info of
      DataConI {} → return True
      _           → return False

  alphaNumNameBase ∷ Name → String
  alphaNumNameBase = concatMap (\c → fromMaybe [c] (lookup c opTable)) . nameBase

-- | Constructs a pattern synonym for a given 'GHC.TyCon', 'GHC.DataCon', or
-- 'GHC.Var'.
makePattern ∷ String → Name → Q [Dec]
makePattern (mkName → patName) valName = do
  x  ← qNewName "x"
  ty ← qReifyType valName
  sequence
    [ patSynSigD patName (mkPatternType ty)
    , patSynD    patName (prefixPatSyn [x])
        (explBidir [clause [varP x] (normalB (mkPatternExp ty (varE x))) []])
        (mkPatternPat ty (varP x))
    ]
 where
  mkPatternType ∷ Type → Q Type
  mkPatternType (ForallT _ ctxt ty) = forallT [] (pure ctxt) (mkPatternType ty)
  mkPatternType (ConT name)
    | name == ''GHC.TyCon
   || name == ''GHC.Class   = [t| [GHC.Type] → GHC.Type |]
    | name == ''GHC.Var
   || name == ''GHC.DataCon = qNewName "a" >>= \a → [t| [GHC.Expr $(varT a)] → GHC.Expr $(varT a) |]
  mkPatternType ty = error ("Unexpected type: " ++ show ty)

  mkPatternPat ∷ Type → Q Pat → Q Pat
  mkPatternPat (ForallT _ _ ty) pat = mkPatternPat ty pat
  mkPatternPat (ConT name) pat
    | name == ''GHC.TyCon   = [p|(GHC.splitTyConApp_maybe → Just ((== $(varE valName)) → True, $pat))|]
    | name == ''GHC.Class   = [p|(GHC.splitTyConApp_maybe → Just ((== GHC.classTyCon $(varE valName)) → True, $pat))|]
    | name == ''GHC.Var     = [p|(GHC.collectArgs → (GHC.Var ((== $(varE valName)) → True), $pat))|]
    | name == ''GHC.DataCon = [p|(GHC.collectArgs → (GHC.Var ((== GHC.dataConWorkId $(varE valName)) → True), $pat))|]
  mkPatternPat ty _ = error ("Unexpected type: " ++ show ty)

  mkPatternExp ∷ Type → Q Exp → Q Exp
  mkPatternExp (ForallT _ _ ty) pat = mkPatternExp ty pat
  mkPatternExp (ConT name) pat
    | name == ''GHC.TyCon   = [e|GHC.mkTyConApp $(varE valName) $pat|]
    | name == ''GHC.Class   = [e|GHC.mkTyConApp (GHC.classTyCon $(varE valName)) $pat|]
    | name == ''GHC.Var     = [e|GHC.mkApps (GHC.Var $(varE valName)) $pat|]
    | name == ''GHC.DataCon = [e|GHC.mkConApp $(varE valName) $pat|]
  mkPatternExp ty _ = error ("Unexpected type: " ++ show ty)

lookupClass ∷ String → String → GHC.TcPluginM GHC.Class
lookupClass mn on = do
  md ← lookupModule mn
  GHC.tcLookupClass =<< GHC.lookupOrig md (GHC.mkClsOcc on)

lookupTyCon ∷ String → String → GHC.TcPluginM GHC.TyCon
lookupTyCon mn on = do
  md ← lookupModule mn
  GHC.tcLookupTyCon =<< GHC.lookupOrig md (GHC.mkTcOcc on)

lookupDataCon ∷ String → String → GHC.TcPluginM GHC.DataCon
lookupDataCon mn on = do
  md ← lookupModule mn
  GHC.tcLookupDataCon =<< GHC.lookupOrig md (GHC.mkDataOcc on)

lookupVar ∷ String → String → GHC.TcPluginM GHC.Var
lookupVar mn on = do
  md ← lookupModule mn
  GHC.tcLookupId =<< GHC.lookupOrig md (GHC.mkVarOcc on)

lookupModule ∷ String → GHC.TcPluginM GHC.Module
lookupModule mn = do
  result ← GHC.findImportedModule (GHC.mkModuleName mn) noPkgQual
  case result of
    GHC.Found _ md → return md
    _              → do
      GHC.tcPluginTrace "[ghc-definitions-th]" (GHC.text ("Could not locate module " ++ mn))
      error "lookupModule: failed"

#if MIN_VERSION_ghc(9,3,0)
noPkgQual ∷ GHC.PkgQual
noPkgQual = GHC.NoPkgQual
#else
noPkgQual ∷ Maybe GHC.FastString
noPkgQual = Nothing
#endif

lower ∷ String → String
lower ""     = ""
lower (x:xs) = toLower x : xs

infixr +:, +++

(+:) ∷ Applicative m ⇒ m a → m [a] → m [a]
x +: xs = (:) <$> x <*> xs

(+++) ∷ Applicative m ⇒ m [a] → m [a] → m [a]
xs +++ ys = (++) <$> xs <*> ys
