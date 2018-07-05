------------------------------------------------------------------------
-- |
-- Module      : Verifier.SAW.Simulator.What4.FirstOrder
-- Copyright   : Galois, Inc. 2012-2015
-- License     : BSD3
-- Maintainer  : sweirich@galois.com
-- Stability   : experimental
-- Portability : non-portable (language extensions)
--
-- Connect What4's 'BaseType' with saw-core's 'FirstOrderType'
-- (both types and values of Base/FirstOrder type)
------------------------------------------------------------------------
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}

module Verifier.SAW.Simulator.What4.FirstOrder where

import Prelude
import qualified Prelude (replicate)
import Data.Proxy
import Data.Parameterized.NatRepr (natValue)
import Data.Parameterized.TraversableFC (FoldableFC(..))
import Data.Parameterized.Some
import Data.Parameterized.Context 

import Verifier.SAW.FiniteValue (FirstOrderType(..),FirstOrderValue(..))
import Verifier.SAW.Prim (Nat(..))

import What4.Interface
import What4.BaseTypes
import What4.Expr.GroundEval

import Verifier.SAW.Simulator.What4.SWord

import Data.Reflection (Given(..))

import Control.Monad.State as ST

---------------------------------------------------------------------

data TypedExpr sym where
  TypedExpr :: BaseTypeRepr ty -> SymExpr sym ty -> TypedExpr sym

---------------------------------------------------------------------

-- | Generate a new variable from a given first-order-type

newVarFOT :: forall sym. (IsSymExprBuilder sym, Given sym) =>
   FirstOrderType -> StateT Int IO (TypedExpr sym)
newVarFOT fot
  | Some r <- fotToBaseType fot
  = do nm <- nextId 
       lift $ freshVar r nm
       
  | otherwise
  = fail $ "Cannot convert FirstOrderType " ++ show fot ++ " to What4.BaseType"

-- | Generate a new variable from a given BaseType

freshVar :: forall sym ty. (IsSymExprBuilder sym, Given sym) =>
  BaseTypeRepr ty -> String -> IO (TypedExpr sym)
freshVar ty str =
  case userSymbol str of
    Right solverSymbol -> do
      c <- freshConstant (given :: sym) solverSymbol ty
      return (TypedExpr ty c)
    Left _ ->
      fail $ "Cannot create solver symbol " ++ str

nextId :: StateT Int IO String
nextId = ST.get >>= (\s-> modify (+1) >> return ("x" ++ show s))

---------------------------------------------------------------------
--
-- | Convert a type expression from SAW-core to What4
--
fotToBaseType :: FirstOrderType -> Some BaseTypeRepr
fotToBaseType FOTBit
  = Some BaseBoolRepr
fotToBaseType FOTInt
  = Some BaseIntegerRepr
fotToBaseType (FOTVec nat FOTBit)
  | Just (Some (PosNat (_ :: Proxy nat))) <- somePosNat (toInteger nat)
  = Some (BaseBVRepr (repr @nat))
  | otherwise
  = error "Cannot create 0-bit bitvector"
fotToBaseType (FOTVec nat fot) 
  | Some assn <- listToAssn (Prelude.replicate (fromInteger (unNat nat)) fot)
  = Some (BaseStructRepr assn)
fotToBaseType (FOTTuple fots) 
  | Some assn <- listToAssn fots
  = Some (BaseStructRepr assn)
fotToBaseType (FOTRec _)
  = error "TODO: convert to What4 records ?!"

listToAssn :: [FirstOrderType] -> Some (Assignment BaseTypeRepr)
listToAssn [] = Some empty
listToAssn (fot:rest) =
  case (fotToBaseType fot, listToAssn rest) of
    (Some bt, Some assn) -> Some $ extend assn bt


  
---------------------------------------------------------------------
-- Convert between BaseTypes and FirstOrderTypes
-- and between GroundValues and FirstOrderValues

natReprToNat :: NatRepr n -> Nat
natReprToNat = Nat . natValue 

typeReprToFOT :: BaseTypeRepr ty -> Either String FirstOrderType
typeReprToFOT BaseBoolRepr          = pure FOTBit
typeReprToFOT BaseNatRepr           = pure FOTInt
typeReprToFOT BaseIntegerRepr       = pure FOTInt
typeReprToFOT BaseRealRepr          = fail "No FO Real"
typeReprToFOT (BaseBVRepr w)        = pure $ FOTVec (natReprToNat w) FOTBit
typeReprToFOT BaseComplexRepr       = fail "No FO Complex"
typeReprToFOT BaseStringRepr        = fail "No FO String"
typeReprToFOT (BaseArrayRepr _ctx _b) = fail "Ugh"
typeReprToFOT (BaseStructRepr ctx)    = FOTTuple <$> assnToList ctx

assnToList :: Assignment BaseTypeRepr ctx -> Either String [FirstOrderType]
assnToList = foldrFC g (Right []) where
  g :: BaseTypeRepr x -> Either String [FirstOrderType] -> Either String [FirstOrderType]
  g ty l = (:) <$> typeReprToFOT ty <*> l

groundToFOV :: BaseTypeRepr ty -> GroundValue ty -> Either String FirstOrderValue
groundToFOV BaseBoolRepr    b       = pure $ FOVBit b
groundToFOV BaseNatRepr     _       = fail "TODO: Natural"
groundToFOV BaseIntegerRepr i       = pure $ FOVInt i
groundToFOV BaseRealRepr    _       = fail "Real is not FOV"
groundToFOV (BaseBVRepr w) bv       = pure $ FOVWord (natReprToNat w) bv
groundToFOV BaseComplexRepr       _ = fail "Complex is not FOV"
groundToFOV BaseStringRepr        _ = fail "String is not FOV"
groundToFOV (BaseArrayRepr _idx _b) _ = fail "TODO"
groundToFOV (BaseStructRepr ctx) tup = FOVTuple <$> (tupleToList ctx tup)


tupleToList :: Assignment BaseTypeRepr ctx ->
             Assignment GroundValueWrapper ctx -> Either String [FirstOrderValue]
tupleToList (viewAssign -> AssignEmpty) (viewAssign -> AssignEmpty) = Right []
tupleToList (viewAssign -> AssignExtend rs r) (viewAssign -> AssignExtend gvs gv) =
  (:) <$> groundToFOV r (unGVW gv) <*> tupleToList rs gvs 
tupleToList _ _ = error "GADTs should rule this out."




