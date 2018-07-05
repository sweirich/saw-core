{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- need to use WithKnownNat in the definition of
-- addNat'
{-# OPTIONS_GHC -Wno-warnings-deprecations #-}


-- TODO: module exports?
module Verifier.SAW.Simulator.What4.SWord where


import GHC.TypeLits
import Data.Proxy(Proxy(..))
import Data.Parameterized.NatRepr
import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Classes

-- import What4.BaseTypes
import What4.Interface(SymBV,Pred,IsExprBuilder)
import qualified What4.Interface as W

import Data.Vector (Vector)
import qualified Data.Vector as V

-- Question: how to handle partiality in this file??
-- throw errors in IO monad? use error?

-- Question: what do the functions in What4.Interface take
-- NatRepr's as arguments instead of implicit KnownNats ?
-- then could use TypeApplications instead of constructing these
-- repr's all over the place.

-- Question: this type can also represent zero-length bitvectors
-- Should it???

-------------------------------------------------------------
-------------------------------------------------------------
-- utilities for dependently typed programming

-- Construct the representation of a number in a way that
-- works well with TypeApplications. 'knownRepr' is too polymorphic
-- and requires two additional type arguments before n.
repr :: KnownNat n => NatRepr n
repr = knownRepr

-- Runtime nats that are also positive.
-- We include the KnownNat constraint instead of a NatRepr value
-- so that we can avoid using withKnownNat
-- The 'Proxy' is necessary to allow binding 'n' when this
-- type is used as part of 'Some'
data PosNat (n :: Nat) where
  PosNat :: (1 <= n, KnownNat n) => Proxy n -> PosNat n


-- This should be added to GHC.TypeLits so that the redundant
-- check for positivity can be removed
-- annoyingly, we cannot do this check without already
-- knowing that w >= 0
somePosNat :: Integer -> Maybe (Some PosNat)
somePosNat n 
  | Just (SomeNat (_ :: Proxy n)) <- someNatVal (toInteger n), 
    Just LeqProof <- testLeq (repr @1) (repr @n) 
  = Just (Some (PosNat @n Proxy))
  | otherwise
  = Nothing

-- Add two numbers together and return a proof that their
-- result is positive.
-- I would hope that the 'leqAddPos' call can be compiled away
-- XXX TODO eliminate withKnownNat, but that requires updates
-- to the Data.Parameterized.NatRepr interface
addNat' :: forall w1 w2.
  (1 <= w1, 1 <= w2, KnownNat w1, KnownNat w2) => PosNat (w1 + w2)
addNat' =
  withKnownNat (addNat (repr @w1) (repr @w2)) $
  case (leqAddPos (repr @w1) (repr @w2)) of
    LeqProof -> PosNat @(w1 + w2) Proxy

-------------------------------------------------------------
--
-- A bitvector where the size does not appear in the type
--

data SWord sym where
  DBV :: (KnownNat w, 1<=w)  => SymBV sym w -> SWord sym
  -- ^ a bit-vector with positive length
  ZBV :: SWord sym
  -- ^ a zero-length bit vector. i.e. 0
-------------------------------------------------------------

intSizeOf :: forall sym. SWord sym -> Int
intSizeOf (DBV (_ :: SymBV sym w)) =
  fromIntegral (natValue (repr @w))
intSizeOf ZBV = 0

bvSize :: SWord sym -> Int
bvSize = intSizeOf

bvLit :: forall sym. IsExprBuilder sym =>
  sym -> Int -> Integer -> IO (SWord sym)
bvLit _ w _
  | w == 0
  = return ZBV
bvLit sym w dat
  | Just (Some (PosNat (_ :: Proxy w))) <- somePosNat (toInteger w)
  = DBV <$> W.bvLit sym (repr @w) dat
  | otherwise
  = error "bvLit: size of bitvector is < 0 or >= maxInt"

bvAt :: forall sym. IsExprBuilder sym =>
  sym -> SWord sym -> Int -> IO (Pred sym)
bvAt sym (DBV (bv :: SymBV sym w)) idx =
  W.testBitBV sym (toInteger idx) bv
bvAt _ ZBV _ = error "cannot index into empty bitvector"
  -- TODO: or could return 0?
  
bvJoin  :: forall sym. IsExprBuilder sym =>
  sym -> SWord sym -> SWord sym -> IO (SWord sym)
bvJoin _ x ZBV = return x
bvJoin _ ZBV x = return x
bvJoin sym (DBV (bv1 :: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | PosNat _ <- addNat' @w1 @w2
  = DBV <$> (W.bvConcat sym bv1 bv2)

bvSlice :: forall sym. IsExprBuilder sym =>
  sym -> Int -> Int -> SWord sym -> IO (SWord sym)
bvSlice sym idx n (DBV (bv :: SymBV sym w))
  | Just (Some (PosNat (_ :: Proxy n))) <- somePosNat (toInteger n),    
    Just (SomeNat (_ :: Proxy idx))     <- someNatVal (toInteger idx),
    Just LeqProof <- testLeq (addNat (repr @idx) (repr @n)) (repr @w)
  = DBV <$> W.bvSelect sym (repr @idx) (repr @n) bv
  | otherwise
  = error "invalid arguments to slice"
bvSlice _ _ _ ZBV = return ZBV

-- | Ceiling (log_2 x)
-- adapted from saw-core-sbv/src/Verifier/SAW/Simulator/SBV.hs
w_bvLg2 :: forall sym w. (IsExprBuilder sym, 1 <= w) => NatRepr w ->
   sym -> SymBV sym w -> IO (SymBV sym w)
w_bvLg2 w sym x = go 0
  where
    size :: Integer
    size = natValue w
    lit :: Integer -> IO (SymBV sym w)
    lit n = W.bvLit sym w n
    go :: Integer -> IO (SymBV sym w)
    go i | i < size = do
           x' <- lit (2 ^ i)
           b' <- W.bvSle sym x x'  --- TODO: should this be sle or ule ?
           th <- lit (toInteger i)
           el <- go (i + 1)
           W.bvIte sym b' th el
         | otherwise    = lit i

-- | If-then-else 
bvIte :: forall sym. IsExprBuilder sym =>
  sym -> Pred sym -> SWord sym -> SWord sym -> IO (SWord sym)
bvIte _ _ ZBV ZBV
  = return ZBV  
bvIte sym p (DBV (bv1 :: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | Just Refl <- testEquality (repr @w1) (repr @w2)    
  = DBV <$> W.bvIte sym p bv1 bv2
bvIte _ _ _ _ 
  = error "bit-vectors don't have same length"
 

----------------------------------------------------------------------
-- Convert to/from Vectors
----------------------------------------------------------------------

bvUnpack :: forall sym. IsExprBuilder sym =>
  sym -> SWord sym -> IO (Vector (Pred sym))
bvUnpack _   ZBV = return V.empty
bvUnpack sym (DBV (bv :: SymBV sym w)) =
  V.generateM (fromIntegral (natValue (repr @w)))
              (\x -> W.testBitBV sym (toInteger x) bv)

bvPack :: forall sym. IsExprBuilder sym =>
  sym -> Vector (Pred sym) -> IO (SWord sym)
bvPack sym vec = do
  vec' <- V.mapM (\p -> do
                     v1 <- bvLit sym 1 0
                     v2 <- bvLit sym 1 1
                     bvIte sym p v1 v2) vec
  
  V.foldM (bvJoin sym) ZBV vec'

----------------------------------------------------------------------
-- Generic wrapper for unary operators
----------------------------------------------------------------------
type SWordUn =
  forall sym. IsExprBuilder sym =>
  sym -> SWord sym -> IO (SWord sym)

bvUn ::  forall sym. IsExprBuilder sym =>
   (forall w. 1 <= w => sym -> SymBV sym w -> IO (SymBV sym w)) ->
   sym -> SWord sym -> IO (SWord sym)
bvUn f sym (DBV (bv :: SymBV sym w)) = DBV <$> f sym bv
bvUn _ _  ZBV = return ZBV

----------------------------------------------------------------------
-- Generic wrapper for binary operators that take two words 
-- of the same length
----------------------------------------------------------------------

type SWordBin =
  forall sym. IsExprBuilder sym =>
  sym -> SWord sym -> SWord sym -> IO (SWord sym)
type PredBin =
  forall sym. IsExprBuilder sym =>
  sym -> SWord sym -> SWord sym -> IO (Pred sym)


-- binary operations that return bitvectors
bvBin  :: forall sym. IsExprBuilder sym =>
  (forall w. 1 <= w => sym -> SymBV sym w -> SymBV sym w -> IO (SymBV sym w)) ->
  sym -> SWord sym -> SWord sym -> IO (SWord sym)
bvBin f sym (DBV (bv1 :: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | Just Refl <- testEquality (repr @w1) (repr @w2) 
  = DBV <$> f sym bv1 bv2
bvBin _ _ ZBV ZBV
  = return ZBV  
bvBin _ _ _ _ 
  = error "bit vectors must have same length"


-- binary operations that return booleans (Pred)
bvBinPred  :: forall sym. IsExprBuilder sym =>
  (forall w. 1 <= w => sym -> SymBV sym w -> SymBV sym w -> IO (Pred sym)) ->
  sym -> SWord sym -> SWord sym -> IO (Pred sym)
bvBinPred f sym (DBV (bv1:: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | Just Refl <- testEquality (repr @w1) (repr @w2) 
  = f sym bv1 bv2
bvBinPred _ _ ZBV ZBV
  = error "no zero-length bit vectors here"  
bvBinPred _ _ _ _ 
  = error "bit vectors must have same length"

 -- Bitvector logical

bvNot :: SWordUn
bvNot = bvUn W.bvNeg 

bvAnd :: SWordBin
bvAnd = bvBin W.bvAndBits

bvOr :: SWordBin
bvOr = bvBin W.bvOrBits

bvXor :: SWordBin
bvXor = bvBin W.bvXorBits

 -- Bitvector arithmetic
  
bvNeg :: SWordUn
bvNeg = bvUn W.bvNeg

bvAdd :: SWordBin
bvAdd = bvBin W.bvAdd

bvSub :: SWordBin
bvSub = bvBin W.bvSub

bvMul :: SWordBin
bvMul = bvBin W.bvMul

bvUDiv :: SWordBin
bvUDiv = bvBin W.bvUdiv

bvURem :: SWordBin
bvURem = bvBin W.bvUrem

bvSDiv :: SWordBin
bvSDiv = bvBin W.bvSdiv

bvSRem :: SWordBin
bvSRem = bvBin W.bvSrem

-- TODO
bvLg2 :: SWordUn
bvLg2 = undefined

 -- Bitvector comparisons

bvEq   :: PredBin
bvEq = bvBinPred W.bvEq

bvsle  :: PredBin
bvsle = bvBinPred W.bvSle
  
bvslt  :: PredBin
bvslt = bvBinPred W.bvSlt

bvule  :: PredBin
bvule = bvBinPred W.bvUle

bvult  :: PredBin
bvult = bvBinPred W.bvUlt

bvsge  :: PredBin
bvsge = bvBinPred W.bvSge

bvsgt  :: PredBin
bvsgt = bvBinPred W.bvSgt

bvuge  :: PredBin
bvuge = bvBinPred W.bvUge

bvugt  :: PredBin
bvugt = bvBinPred W.bvUgt

----------------------------------------
-- Bitvector shift/rotate (prims)
-- TODO
----------------------------------------

  
bvRolInt :: forall sym. IsExprBuilder sym => sym ->
              SWord sym -> Integer -> IO (SWord sym)
bvRolInt = undefined              
bvRorInt :: forall sym. IsExprBuilder sym => sym ->
              SWord sym -> Integer -> IO (SWord sym)
bvRorInt = undefined

bvRol    :: forall sym. IsExprBuilder sym => sym ->
              SWord sym -> SWord sym -> IO (SWord sym)
bvRol = undefined

bvRor    :: forall sym. IsExprBuilder sym => sym ->
              SWord sym -> SWord sym -> IO (SWord sym)
bvRor = undefined


-- in SBV: Defined in terms of svShl'
bvShlInt :: forall sym. IsExprBuilder sym => sym ->
              Pred sym -> SWord sym -> Integer -> IO (SWord sym)
bvShlInt sym p (DBV (bv :: SymBV sym w)) x
  = DBV <$> bvShl' sym (repr @w) p bv x 
bvShlInt _ _ ZBV _
  = return ZBV 

-- By default this is logical (unsigned) shift right
-- in SBV: Defined in terms of svShr'           
bvShrInt :: forall sym. IsExprBuilder sym => sym ->
              Pred sym -> SWord sym -> Integer -> IO (SWord sym)
bvShrInt sym p (DBV (bv :: SymBV sym w)) x
  = DBV <$> bvShr' sym (W.bvLshr sym) (repr @w) p bv x 
bvShrInt _ _ ZBV _
  = return ZBV

-- signed shift right
bvSShrInt :: forall sym. IsExprBuilder sym => sym ->
              Pred sym -> SWord sym -> Integer -> IO (SWord sym)
bvSShrInt sym p (DBV (bv :: SymBV sym w)) x
  = DBV <$> bvShr' sym (W.bvAshr sym) (repr @w) p bv x 
bvSShrInt _ _ ZBV _
  = return ZBV   


-- in SBV: svShiftL
bvShl    :: forall sym. IsExprBuilder sym => sym ->
              Pred sym -> SWord sym -> SWord sym -> IO (SWord sym)
bvShl sym p (DBV (bv1 :: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | Just Refl <- testEquality (repr @w1) (repr @w2) 
  = DBV <$> bvShiftL sym p bv1 bv2
bvShl _ _ ZBV ZBV
  = return ZBV
bvShl _ _ _ _
  = fail "bitvectors do not have the same length"

-- logical shiftRight
-- in SBV: svShiftR
bvShr    :: forall sym. IsExprBuilder sym => sym ->
              Pred sym -> SWord sym -> SWord sym -> IO (SWord sym)
bvShr  sym p (DBV (bv1 :: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | Just Refl <- testEquality (repr @w1) (repr @w2) 
  = DBV <$> bvShiftR sym (W.bvLshr sym) p bv1 bv2
bvShr _ _ ZBV ZBV
  = return ZBV
bvShr _ _ _ _
  = fail "bitvectors do not have the same length"

-- arithmetic shiftRight
bvSShr    :: forall sym. IsExprBuilder sym => sym ->
              Pred sym -> SWord sym -> SWord sym -> IO (SWord sym)
bvSShr  sym p (DBV (bv1 :: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | Just Refl <- testEquality (repr @w1) (repr @w2) 
  = DBV <$> bvShiftR sym (W.bvAshr sym) p bv1 bv2
bvSShr _ _ ZBV ZBV
  = return ZBV
bvSShr _ _ _ _
  = fail "bitvectors do not have the same length"  
    
----------------------------------------
-- Shift operations
----------------------------------------

-- The SBV code does this case on the predicate and then some
-- math. Not sure it is needed here. I guess it is trying to
-- control whether the newly added bit is a one (if b is true)
-- or a zero (if b is false).

bvShiftL :: forall sym w. (IsExprBuilder sym, 1 <= w) => sym ->
  Pred sym -> SymBV sym w -> SymBV sym w -> IO (SymBV sym w)
bvShiftL sym b x j = do
  nx   <- W.bvNotBits sym x
  snx  <- W.bvShl sym nx j
  nsnx <- W.bvNotBits sym snx
  W.bvIte sym b nsnx =<< W.bvShl sym x j

bvShl' :: (IsExprBuilder sym, 1 <= w) => sym ->
  NatRepr w -> Pred sym -> SymBV sym w -> Integer -> IO (SymBV sym w)
bvShl' sym rep b x i = do
  j   <- W.bvLit sym rep i   -- what if i is too big for rep bits?
  bvShiftL sym b x j


-- The shr argument should be W.bvAshr or W.bvLshr, depending
-- on whether to use arithmetic or logical shift right

bvShiftR :: forall sym w. (IsExprBuilder sym, 1 <= w) => sym ->
  (SymBV sym w -> SymBV sym w -> IO (SymBV sym w)) ->
  Pred sym -> SymBV sym w -> SymBV sym w -> IO (SymBV sym w)
bvShiftR sym shr b x j = do
  nx   <- W.bvNotBits sym x
  snx  <- W.bvShl sym nx j
  nsnx <- W.bvNotBits sym snx
  W.bvIte sym b nsnx =<< shr x j  

bvShr' :: (IsExprBuilder sym, 1 <= w) => sym ->
  (SymBV sym w -> SymBV sym w -> IO (SymBV sym w)) ->
  NatRepr w -> Pred sym -> SymBV sym w -> Integer -> IO (SymBV sym w)
bvShr' sym shr rep b x i = do
  j   <- W.bvLit sym rep i   
  bvShiftR sym shr b x j
  
  
