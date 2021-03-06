{-# LANGUAGE CPP             #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE ViewPatterns    #-}

module GHC.Definitions.TH.Example where

import GHC.Builtin.Types  (eqTyCon)
import GHC.Definitions.TH (makeDefinitions, makePattern)
import GHC.TypeNats       (type (-))

makeDefinitions
  [ 'id
  , ''Maybe
  , 'Nothing
  , '(+)
  , ''(-)
  , ''Ord
  ]

makePattern "MaybeTy"     'maybeTyCon
makePattern "IdExpr"      'idVar
makePattern "NothingExpr" 'nothingDataCon
makePattern "NothingTy"   'promotedNothingTyCon
makePattern "EqTy"        'eqTyCon
makePattern "MinusTy"     'minusTyCon
makePattern "OrdTy"       'ordClass
