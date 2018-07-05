------------------------------------------------------------------------
-- |
-- Module      : Verifier.SAW.Simulator.What4
-- Copyright   : Galois, Inc. 2012-2015
-- License     : BSD3
-- Maintainer  : sweirich@galois.com
-- Stability   : experimental
-- Portability : non-portable (language extensions)
-- 
-- A symbolic simulator for saw-core terms using What4.
-- (This module is derived from Verifier.SAW.Simulator.SBV)
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds#-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -fdefer-type-errors #-}

{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}


-- WithKnownNat
{-# OPTIONS_GHC -Wno-warnings-deprecations #-}


module Verifier.SAW.Simulator.What4
  (
    w4Solve,
    TypedExpr(..),
    SValue
  ) where



import qualified Control.Arrow as A

import Data.Bits
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Traversable as T
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Monad.IO.Class
import Control.Monad.State as ST

import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.Simulator as Sim
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.Prim (Nat(..))
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.Value
import Verifier.SAW.TypedAST (FieldName, ModuleMap, identName)
import Verifier.SAW.FiniteValue (FirstOrderType(..),asFirstOrderType)

import What4.Interface(SymExpr,Pred,SymInteger,IsExprBuilder,IsSymExprBuilder,userSymbol)
import qualified What4.Interface as W
import What4.BaseTypes
import GHC.TypeLits
import What4.Expr.GroundEval

import Data.Reflection (Given(..))
import Data.Parameterized.NatRepr (natValue)
import Data.Parameterized.Some

import Data.Proxy

import Verifier.SAW.Simulator.What4.SWord
import Verifier.SAW.Simulator.What4.FirstOrder

---------------------------------------------------------------------
-- the type index is a sym
data What4 (t :: *)

-- type abbreviations for uniform naming
type SBool sym = Pred sym 
type SInt  sym = SymInteger sym 
  
type instance EvalM (What4 sym) = IO
type instance VBool (What4 sym) = SBool sym
type instance VWord (What4 sym) = SWord sym
type instance VInt  (What4 sym) = SInt  sym
type instance Extra (What4 sym) = What4Extra sym

--NOTE: SValue is injective
type SValue sym = Value (What4 sym)

-- TODO: implement streams(?)
data What4Extra sym = SStream () ()
--  SStream (Integer -> IO SValue) (IORef (Map Integer SValue))

instance Show (What4Extra sym) where
  show (SStream _ _) = "<SStream>"


---------------------------------------------------------------------
---------------------------------------------------------------------

prims :: forall sym. (Given sym, IsExprBuilder sym) => Prims.BasePrims (What4 sym)
prims =
  let sym :: sym = given in
  Prims.BasePrims
  { Prims.bpAsBool  = W.asConstantPred
    -- Bitvectors
  , Prims.bpUnpack  = bvUnpack sym 
  , Prims.bpPack    = bvPack   sym 
  , Prims.bpBvAt    = bvAt     sym
  , Prims.bpBvLit   = bvLit    sym 
  , Prims.bpBvSize  = intSizeOf
  , Prims.bpBvJoin  = bvJoin   sym 
  , Prims.bpBvSlice = bvSlice  sym
    -- Conditionals
  , Prims.bpMuxBool  = W.itePred sym 
  , Prims.bpMuxWord  = bvIte     sym
  , Prims.bpMuxInt   = W.intIte  sym
  , Prims.bpMuxExtra = undefined -- TODO
    -- Booleans
  , Prims.bpTrue   = W.truePred  sym
  , Prims.bpFalse  = W.falsePred sym
  , Prims.bpNot    = W.notPred   sym
  , Prims.bpAnd    = W.andPred   sym
  , Prims.bpOr     = W.orPred    sym
  , Prims.bpXor    = W.xorPred   sym
  , Prims.bpBoolEq = W.isEq      sym
    -- Bitvector logical
  , Prims.bpBvNot  = bvNot  sym
  , Prims.bpBvAnd  = bvAnd  sym
  , Prims.bpBvOr   = bvOr   sym
  , Prims.bpBvXor  = bvXor  sym
    -- Bitvector arithmetic
  , Prims.bpBvNeg  = bvNeg  sym
  , Prims.bpBvAdd  = bvAdd  sym
  , Prims.bpBvSub  = bvSub  sym
  , Prims.bpBvMul  = bvMul  sym
  , Prims.bpBvUDiv = bvUDiv sym
  , Prims.bpBvURem = bvURem sym
  , Prims.bpBvSDiv = bvSDiv sym
  , Prims.bpBvSRem = bvSRem sym
  , Prims.bpBvLg2  = bvLg2  sym
    -- Bitvector comparisons
  , Prims.bpBvEq   = bvEq  sym
  , Prims.bpBvsle  = bvsle sym
  , Prims.bpBvslt  = bvslt sym
  , Prims.bpBvule  = bvule sym
  , Prims.bpBvult  = bvult sym
  , Prims.bpBvsge  = bvsge sym
  , Prims.bpBvsgt  = bvsgt sym
  , Prims.bpBvuge  = bvuge sym
  , Prims.bpBvugt  = bvugt sym
    -- Bitvector shift/rotate
  , Prims.bpBvRolInt = bvRolInt sym
  , Prims.bpBvRorInt = bvRorInt sym
  , Prims.bpBvShlInt = bvShlInt sym
  , Prims.bpBvShrInt = bvShrInt sym
  , Prims.bpBvRol    = bvRol sym
  , Prims.bpBvRor    = bvRor sym
  , Prims.bpBvShl    = bvShl sym
  , Prims.bpBvShr    = bvShr sym
    -- Integer operations
  , Prims.bpIntAdd = W.intAdd sym
  , Prims.bpIntSub = W.intSub sym
  , Prims.bpIntMul = W.intMul sym
  , Prims.bpIntDiv = undefined -- TODO: pure2 svQuot
  , Prims.bpIntMod = undefined -- W.intMod sym
  , Prims.bpIntNeg = W.intNeg sym
  , Prims.bpIntEq  = W.intEq sym
  , Prims.bpIntLe  = W.intLe sym
  , Prims.bpIntLt  = W.intLt sym
  , Prims.bpIntMin = undefined -- TODO: pure2 min
  , Prims.bpIntMax = undefined -- TODO: pure2 max
  }


constMap :: (Given sym, IsExprBuilder sym) => Map Ident (SValue sym)
constMap =
  Map.union (Prims.constMap prims) $
  Map.fromList
  [
  -- Shifts
    ("Prelude.bvShl" , bvShLOp)
  , ("Prelude.bvShr" , bvShROp)
  , ("Prelude.bvSShr", bvSShROp)
{-  -- Integers
  --XXX , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  , ("Prelude.bvStreamGet", bvStreamGetOp) -}
  ]


toWord :: SValue sym -> IO (SWord sym)
toWord (VWord w)    = return w
toWord (VVector vv) = error "TODO" -- symFromBits <$> traverse (fmap toBool . force) vv
toWord x            = fail $ unwords ["Verifier.SAW.Simulator.SBV.toWord", show x]


-- strictFun :: (SValue sym -> IO (SValue sym)) -> SValue sm
wordFun :: (SWord sym -> IO (SValue sym)) -> SValue sym
wordFun f = strictFun (\x -> f =<< toWord x)

-- | op :: (n :: Nat) -> bitvector n -> Nat -> bitvector n
bvShiftOp :: (SWord sym -> SWord sym -> IO (SWord sym)) ->
             (SWord sym -> Integer   -> IO (SWord sym)) -> SValue sym
bvShiftOp bvOp natOp =
  constFun  $                  -- additional argument? the size?
  wordFun   $ \x ->            -- word to shift
  return $
  strictFun $ \y ->            -- amount to shift as a nat
    case y of
      VNat i   -> VWord <$> natOp x j
        where j = i `min` toInteger (intSizeOf x)
      VToNat v -> VWord <$> (bvOp x =<< toWord v) 
      _        -> error $ unwords ["Verifier.SAW.Simulator.What4.SWord.bvShiftOp", show y]

-- bvShl :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShLOp :: forall sym. (Given sym, IsExprBuilder sym) => SValue sym
bvShLOp = bvShiftOp (bvShl    given (W.falsePred @sym given))
                    (bvShlInt given (W.falsePred @sym given))

-- bvShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShROp :: forall sym. (Given sym, IsExprBuilder sym) => SValue sym
bvShROp = bvShiftOp (bvShr    given (W.falsePred @sym given))
                    (bvShrInt given (W.falsePred @sym given))


-- bvShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvSShROp :: forall sym. (Given sym, IsExprBuilder sym) => SValue sym
bvSShROp = bvShiftOp (bvSShr    given (W.falsePred @sym given))
                     (bvSShrInt given (W.falsePred @sym given))



-----------------------------------------------------------------------
-- | A basic symbolic simulator/evaluator: interprets a saw-core Term as
-- a symbolic value

w4SolveBasic :: forall sym. (Given sym, IsSymExprBuilder sym) =>
  ModuleMap ->
  Map Ident (SValue sym) ->
  -- ^ additional primatives
  [String] ->
  -- ^ 'unints' Constants in this list are kept uninterpreted
  Term ->
  -- ^ term to simulate
  IO (SValue sym)
w4SolveBasic m addlPrims unints t = do
  let unintSet = Set.fromList unints
  let uninterpreted nm ty
        | Set.member nm unintSet = Just $ parseUninterpreted nm ty
        | otherwise              = Nothing
  cfg <- Sim.evalGlobal m (constMap `Map.union` addlPrims)
         (const parseUninterpreted)
         uninterpreted
  Sim.evalSharedTerm cfg t      


------------------------------------------------------------
-- Given a constant nm of (saw-core) type ty, construct an uninterpreted
-- constant with that type. 
-- Importantly: The types of these uninterpreted values are *not*
-- limited to What4 BaseTypes or FirstOrderTypes.

parseUninterpreted :: forall sym. (Given sym, IsSymExprBuilder sym) => 
  String -> SValue sym -> IO (SValue sym)
parseUninterpreted nm ty = case ty of
    VVecType (VNat 0) _
      -> fail "zero-width vector is always interpreted as zero"

    VVecType (VNat n) VBoolType
      | Just (Some (PosNat (_::Proxy n))) <- somePosNat n 
      -> (VWord . DBV) <$> mkUninterpreted @sym nm (BaseBVRepr (repr @n))

    VVecType (VNat n) ety
      | Just (Some (PosNat (_::Proxy n))) <- somePosNat n      
      ->  do xs <- sequence $
                  [ parseUninterpreted (nm ++ "@" ++ show i) ety
                  | i <- [0 .. n-1] ]
             return (VVector (V.fromList (map ready xs)))
  
    VBoolType
      -> VBool <$> mkUninterpreted @sym nm BaseBoolRepr

    VIntType
      -> VInt  <$> mkUninterpreted @sym nm BaseIntegerRepr

    VPiType _ rng
      -> return $
         strictFun $ \x -> do
           suffix <- flattenSValue x
           t2 <- rng (ready x)
           parseUninterpreted (nm ++ suffix) t2

    VUnitType
      -> return VUnit

    VPairType ty1 ty2
      -> do x1 <- parseUninterpreted (nm ++ ".L") ty1
            x2 <- parseUninterpreted (nm ++ ".R") ty2
            return (VPair (ready x1) (ready x2))

    _ -> fail $ "could not create uninterpreted type for " ++ show ty


-- Ambiguous type. Must include a type application to call
-- this function
mkUninterpreted :: forall sym t. (Given sym, IsSymExprBuilder sym) => 
  String -> BaseTypeRepr t -> IO (SymExpr sym t)
mkUninterpreted nm rep = 
  case W.userSymbol nm of
    Left err -> fail $ "Cannot create uninterpreted constant " ++ nm
    Right s  -> W.freshConstant (given :: sym) s rep



-- Flatten an SValue to an encoded string
-- encoded as a String.
flattenSValue :: SValue sym -> IO String
flattenSValue v = do
  case v of
    VUnit                     -> return ("")
    VPair x y                 -> do sx <- flattenSValue =<< force x
                                    sy <- flattenSValue =<< force y
                                    return (sx ++ sy)
    VEmpty                    -> return ("")
    VField _ x y              -> do sx <- flattenSValue =<< force x
                                    sy <- flattenSValue y
                                    return (sx ++ sy)
    VRecordValue elems        -> do sxs <- mapM (flattenSValue <=< force . snd) elems
                                    return (concat sxs)
    VVector (V.toList -> ts)  -> do ss <- traverse (force >=> flattenSValue) ts
                                    return (concat ss)
    VBool sb                  -> return ("")
    VWord sw                  -> return ("")
    VCtorApp i (V.toList->ts) -> do ss <- traverse (force >=> flattenSValue) ts
                                    return ("_" ++ identName i ++ concat ss)
    VNat n                    -> return ("_" ++ show n)
    _ -> fail $ "Could not create argument for " ++ show v

------------------------------------------------------------

w4Solve :: forall sym. (Given sym, IsSymExprBuilder sym) => 
         SharedContext
      -> Map Ident (SValue sym)
      -> [String]
      -> Term
      -> IO ([String], ([Maybe (TypedExpr sym)], SBool sym))
w4Solve sc ps unints t = do
  modmap <- scGetModuleMap sc
  let eval = w4SolveBasic modmap ps unints
  ty <- eval =<< scTypeOf sc t

  -- get the names of the arguments to the function
  let argNames = map fst (fst (R.asLambdaList t))
  let moreNames = [ "var" ++ show (i :: Integer) | i <- [0 ..] ]

  -- and their types
  argTs <- asPredType ty

  -- construct symbolic expressions for the variables
  (vars' :: [(Maybe (TypedExpr sym), SValue sym)]) <-
    flip evalStateT 0 $ 
    sequence (zipWith newVarsForType argTs (argNames ++ moreNames))

  -- symbolically evaluate
  bval <- eval t

  -- apply and existentially quantify
  -- prd :: ([Maybe (TypedExpr sym)], SBool sym)

  prd <- do
              let (bvs, vars) = unzip vars'
              let vars'' = fmap ready vars
              bval' <- applyAll bval vars''
              case bval' of
                VBool b -> return (bvs,b) 
                _ -> fail $ "solve: non-boolean result type. " ++ show bval'
  return (argNames, prd)

  




--
-- Pull out argument types until bottoming out at a bool type
--
asPredType :: IsSymExprBuilder sv => SValue sv -> IO [SValue sv]
asPredType v =
  case v of
    VBoolType -> return []
    VPiType v1 f ->
      do v2 <- f (error "asPredType: unsupported dependent SAW-Core type")
         vs <- asPredType v2
         return (v1 : vs)
    _ -> fail $ "non-boolean result type: " ++ show v

--
-- Convert a saw-core type expression to a FirstOrder type expression
--
vAsFirstOrderType :: forall sv. IsSymExprBuilder sv => SValue sv -> Maybe FirstOrderType
vAsFirstOrderType v =
  case v of
    VBoolType
      -> return FOTBit
    VIntType
      -> return FOTInt
    VVecType (VNat n) v2
      -> FOTVec (fromInteger n) <$> vAsFirstOrderType v2
    VUnitType
      -> return (FOTTuple [])
    VPairType v1 v2
      -> do t1 <- vAsFirstOrderType v1
            t2 <- vAsFirstOrderType v2
            case t2 of
              FOTTuple ts -> return (FOTTuple (t1 : ts))
              _ -> Nothing
    VEmptyType
      -> return (FOTRec Map.empty)
    VFieldType k v1 v2
      -> do t1 <- vAsFirstOrderType v1
            t2 <- vAsFirstOrderType v2
            case t2 of
              FOTRec tm -> return (FOTRec (Map.insert k t1 tm))
              _ -> Nothing
    (asVTupleType -> Just vs)
      -> FOTTuple <$> mapM vAsFirstOrderType vs
    VRecordType tps
      -> (FOTRec <$> Map.fromList <$>
          mapM (\(f,tp) -> (f,) <$> vAsFirstOrderType tp) tps)
    _ -> Nothing


typedToSValue :: TypedExpr sym -> IO (SValue sym)
typedToSValue (TypedExpr ty expr) =
  case ty of
    BaseBoolRepr         -> return $ VBool expr
    BaseIntegerRepr      -> return $ VInt  expr
    (BaseBVRepr w)       -> return $ withKnownNat w $ VWord (DBV expr)
    (BaseArrayRepr _ _)  -> error "TODO"
    (BaseStructRepr ctx) -> error "TODO: create symbolic struct"
    _                    -> error "Cannot handle"

newVarsForType :: forall sym. (Given sym, IsSymExprBuilder sym) => 
  SValue sym -> String -> StateT Int IO (Maybe (TypedExpr sym), SValue sym)
newVarsForType v nm =
  case vAsFirstOrderType v of
    Just fot -> do
      do te <- newVarFOT fot
         sv <- lift $ typedToSValue te
         return (Just te, sv)

    Nothing ->
      do sv <- lift $ parseUninterpreted nm v
         return (Nothing, sv)
