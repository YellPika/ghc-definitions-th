{-# LANGUAGE
    ConstraintKinds,
    CPP,
    PatternSynonyms,
    TemplateHaskell,
    ViewPatterns
  #-}

module GHC.Definitions.TH.Example where

#if MIN_VERSION_ghc(9, 0, 1)
import GHC.Builtin.Types (eqTyCon)
#else
import TysWiredIn (eqTyCon)
#endif
import GHC.Definitions.TH
import GHC.TypeNats

makeDefinitions
  [ 'id
  , ''Maybe
  , 'Nothing
  , '(+)
  , ''(-)
  , ''Ord
  ]

makePattern "MaybeTy" 'maybeTyCon
makePattern "IdExpr" 'idVar
makePattern "NothingExpr" 'nothingDataCon
makePattern "NothingTy" 'promotedNothingTyCon
makePattern "EqTy" 'eqTyCon
makePattern "MinusTy" 'minusTyCon
makePattern "OrdTy" 'ordClass