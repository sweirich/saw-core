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

{-# OPTIONS_GHC -fdefer-type-errors #-}


{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}


{- |
Module      : Verifier.SAW.Simulator.What4
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : sweirich@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}
module Verifier.SAW.Simulator.What4
  (
    -- what4Solve
--  , what4SolveBasic
   SValue
--  , Labeler(..)
--  , what4CodeGen_definition
--  , what4CodeGen
--  , toWord
--  , toBool
  ) where


import Control.Lens ((<&>))
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
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.Value
import Verifier.SAW.TypedAST (FieldName, ModuleMap, identName)
import Verifier.SAW.FiniteValue (FirstOrderType(..), asFirstOrderType)

import What4.Interface(SymExpr,Pred,SymInteger,IsExprBuilder)
import qualified What4.Interface as W
import What4.BaseTypes
import GHC.TypeLits
import Data.Parameterized.NatRepr

import Verifier.SAW.Simulator.What4.SWord


data What4 (t :: *)

type SBool    sym = Pred sym 
type SInteger sym = SymInteger sym 
  
type instance EvalM (What4 sym) = IO
type instance VBool (What4 sym) = Pred sym
type instance VWord (What4 sym) = SWord sym
type instance VInt  (What4 sym) = SInteger sym
type instance Extra (What4 sym) = What4Extra sym

type SValue sym = Value (What4 sym)
--type SThunk = Thunk What4

data What4Extra sym = SStream () ()
--  SStream (Integer -> IO SValue) (IORef (Map Integer SValue))

instance Show (What4Extra sym) where
  show (SStream _ _) = "<SStream>"

prims :: IsExprBuilder sym => sym -> Prims.BasePrims (What4 sym)
prims sym =
  Prims.BasePrims
  { Prims.bpAsBool  = W.asConstantPred
    -- Bitvectors
  , Prims.bpUnpack  = bvUnpack sym 
  , Prims.bpPack    = bvPack sym 
  , Prims.bpBvAt    = bvAt sym
  , Prims.bpBvLit   = bvLit sym 
  , Prims.bpBvSize  = intSizeOf
  , Prims.bpBvJoin  = bvJoin sym 
  , Prims.bpBvSlice = bvSlice sym
    -- Conditionals
  , Prims.bpMuxBool  = undefined -- W.itePred sym   (IO vs. non-IO)
  , Prims.bpMuxWord  = undefined -- W.bvIte sym
  , Prims.bpMuxInt   = undefined -- W.intIte sym
  , Prims.bpMuxExtra = undefined
    -- Booleans
  , Prims.bpTrue   = W.truePred sym
  , Prims.bpFalse  = W.falsePred sym
  , Prims.bpNot    = W.notPred sym
  , Prims.bpAnd    = W.andPred sym
  , Prims.bpOr     = W.orPred sym
  , Prims.bpXor    = W.xorPred sym
  , Prims.bpBoolEq = W.isEq sym
    -- Bitvector logical
  , Prims.bpBvNot  = bvNot sym
  , Prims.bpBvAnd  = bvAnd sym
  , Prims.bpBvOr   = bvOr sym
  , Prims.bpBvXor  = bvXor sym
    -- Bitvector arithmetic
  , Prims.bpBvNeg  = bvNeg sym
  , Prims.bpBvAdd  = bvAdd sym
  , Prims.bpBvSub  = bvSub sym
  , Prims.bpBvMul  = bvMul sym
  , Prims.bpBvUDiv = bvUDiv sym
  , Prims.bpBvURem = bvURem sym
  , Prims.bpBvSDiv = bvSDiv sym
  , Prims.bpBvSRem = bvSRem sym
  , Prims.bpBvLg2  = bvLg2 sym
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

{-
constMap :: sym -> Map Ident (SValue sym)
constMap sym =
  Map.union (Prims.constMap (prims sym)) $
  Map.fromList
  [
  -- Shifts
    ("Prelude.bvShl" , bvShLOp)
  , ("Prelude.bvShr" , bvShROp)
  , ("Prelude.bvSShr", bvSShROp)
  -- Integers
  --XXX , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  , ("Prelude.bvStreamGet", bvStreamGetOp)
  ]
-}

------------------------------------------------------------
-- Coercion functions
--
{-
vWord :: SWord sym -> SValue sym
vWord lv = VWord lv

vBool :: SBool sym -> SValue sym
vBool l = VBool l

vInteger :: SInteger sym -> SValue sym
vInteger x = VInt x

symFromBits :: sym -> Vector (SBool sym) -> IO (SWord sym)
symFromBits sym v = do
  v' <- mapM (\x -> W.bvIte sym x (bvLit sym 1 1) (bvLit sym 1 0)) v 
  V.foldM (bvJoin sym) (bvLit sym 0 0) v

toMaybeBool :: SValue sym -> Maybe (SBool sym)
toMaybeBool (VBool b) = Just b
toMaybeBool _  = Nothing

toBool :: SValue sym -> (SBool sym)
toBool (VBool b) = b
toBool sv = error $ unwords ["toBool failed:", show sv]

toWord :: SValue sym -> IO (SWord sym)
toWord (VWord w) = return w
toWord (VVector vv) =
  symFromBits <$> traverse (fmap toBool . force) vv
toWord x = fail $ unwords ["Verifier.SAW.Simulator.What4.toWord", show x]

toMaybeWord :: SValue sym -> IO (Maybe (SWord sym))
toMaybeWord (VWord w) = return (Just w)
toMaybeWord (VVector vv) = ((symFromBits <$>) . T.sequence) <$> traverse (fmap toMaybeBool . force) vv
toMaybeWord _ = return Nothing



-- | Flatten an SValue to a sequence of components, each of which is
-- either a symbolic word or a symbolic boolean. If the SValue
-- contains any values built from data constructors, then return them
-- encoded as a String.
{-
flattenSValue :: SValue sym -> IO ([SVal], String)
flattenSValue v = do
  mw <- toMaybeWord v
  case mw of
    Just w -> return ([w], "")
    Nothing ->
      case v of
        VUnit                     -> return ([], "")
        VPair x y                 -> do (xs, sx) <- flattenSValue =<< force x
                                        (ys, sy) <- flattenSValue =<< force y
                                        return (xs ++ ys, sx ++ sy)
        VEmpty                    -> return ([], "")
        VField _ x y              -> do (xs, sx) <- flattenSValue =<< force x
                                        (ys, sy) <- flattenSValue y
                                        return (xs ++ ys, sx ++ sy)
        VRecordValue elems        -> do (xss, sxs) <-
                                          unzip <$>
                                          mapM (flattenSValue <=< force . snd) elems
                                        return (concat xss, concat sxs)
        VVector (V.toList -> ts)  -> do (xss, ss) <- unzip <$> traverse (force >=> flattenSValue) ts
                                        return (concat xss, concat ss)
        VBool sb                  -> return ([sb], "")
        VWord sw                  -> return (if intSizeOf sw > 0 then [sw] else [], "")
        VCtorApp i (V.toList->ts) -> do (xss, ss) <- unzip <$> traverse (force >=> flattenSValue) ts
                                        return (concat xss, "_" ++ identName i ++ concat ss)
        VNat n                    -> return ([], "_" ++ show n)
        _ -> fail $ "Could not create sbv argument for " ++ show v
-}


------------------------------------------------------------
-- Function constructors

wordFun :: (SWord sym -> IO (SValue sym)) -> SValue sym
wordFun f = strictFun (\x -> toWord x >>= f)

------------------------------------------------------------
-- Indexing operations

-- | Lifts a strict mux operation to a lazy mux
lazyMux :: (SBool sym -> a -> a -> IO a) -> (SBool sym -> IO a -> IO a -> IO a)
lazyMux muxFn c tm fm =
  case svAsBool c of
    Just True  -> tm
    Just False -> fm
    Nothing    -> do
      t <- tm
      f <- fm
      muxFn c t f

-- selectV merger maxValue valueFn index returns valueFn v when index has value v
-- if index is greater than maxValue, it returns valueFn maxValue. Use the ite op from merger.
selectV :: (Ord a, Num a, Bits a) => (SBool sym -> b -> b -> b) -> a -> (a -> b) -> SWord sym -> b
selectV merger maxValue valueFn vx =
  case svAsInteger vx of
    Just i  -> valueFn (fromIntegral i)
    Nothing -> impl (intSizeOf vx) 0
  where
    impl _ x | x > maxValue || x < 0 = valueFn maxValue
    impl 0 y = valueFn y
    impl i y = merger (svTestBit vx j) (impl j (y `setBit` j)) (impl j y) where j = i - 1

-- Big-endian version of svTestBit
svAt :: SWord sym -> Int -> SBool sym
svAt x i = svTestBit x (intSizeOf x - 1 - i)

svUnpack :: SWord sym -> IO (Vector (SBool sym))
svUnpack x = return (V.generate (intSizeOf x) (svAt x))

asWordList :: [SValue sym] -> Maybe [SWord sym]
asWordList = go id
 where
  go f [] = Just (f [])
  go f (VWord x : xs) = go (f . (x:)) xs
  go _ _ = Nothing


----------------------------------------
-- Shift operations

-- | op :: (n :: Nat) -> bitvector n -> Nat -> bitvector n
bvShiftOp :: (SWord sym -> SWord sym -> SWord sym) -> (SWord sym -> Int -> SWord sym) -> SValue sym
bvShiftOp bvOp natOp =
  constFun $
  wordFun $ \x -> return $
  strictFun $ \y ->
    case y of
      VNat i   -> return (vWord (natOp x j))
        where j = fromInteger (i `min` toInteger (intSizeOf x))
      VToNat v -> fmap (vWord . bvOp x) (toWord v)
      _        -> error $ unwords ["Verifier.SAW.Simulator.What4.bvShiftOp", show y]

-- bvShl :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShLOp :: SValue sym
bvShLOp = bvShiftOp svShiftLeft svShl

-- bvShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShROp :: SValue sym
bvShROp = bvShiftOp svShiftRight svShr

-- bvSShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvSShROp :: SValue sym
bvSShROp = bvShiftOp bvOp natOp
  where
    bvOp w x = svUnsign (svShiftRight (svSign w) x)
    natOp w i = svUnsign (svShr (svSign w) i)

-----------------------------------------
-- Integer/bitvector conversions

-- primitive natToInt :: Nat -> Integer;
natToIntOp :: SValue sym
natToIntOp =
  Prims.natFun' "natToInt" $ \n -> return $
    VInt (literalSInteger (toInteger n))

-- primitive bvToInt :: (n::Nat) -> bitvector n -> Integer;
bvToIntOp :: SValue sym
bvToIntOp = constFun $ wordFun $ \v ->
   case svAsInteger v of
      Just i -> return $ VInt (literalSInteger i)
      Nothing -> return $ VInt (svFromIntegral KUnbounded v)

-- primitive sbvToInt :: (n::Nat) -> bitvector n -> Integer;
sbvToIntOp :: SValue sym
sbvToIntOp = constFun $ wordFun $ \v ->
   case svAsInteger (svSign v) of
      Just i -> return $ VInt (literalSInteger i)
      Nothing -> return $ VInt (svFromIntegral KUnbounded (svSign v))

-- primitive intToBv :: (n::Nat) -> Integer -> bitvector n;
intToBvOp :: SValue sym
intToBvOp =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \x ->
    case svAsInteger x of
      Just i -> return $ VWord $ literalSWord (fromIntegral n) i
      Nothing -> return $ VWord $ svFromIntegral (KBounded False (fromIntegral n)) x

------------------------------------------------------------
-- Rotations and shifts

svRol' :: SWord sym -> Integer -> SWord sym
svRol' x i = svRol x (fromInteger (i `mod` toInteger (intSizeOf x)))

svRor' :: SWord sym -> Integer -> SWord sym
svRor' x i = svRor x (fromInteger (i `mod` toInteger (intSizeOf x)))

svShl' :: SBool sym -> SWord sym -> Integer -> SWord sym
svShl' b x i = svIte b (svNot (svShl (svNot x) j)) (svShl x j)
  where j = fromInteger (i `min` toInteger (intSizeOf x))

svShr' :: SBool sym -> SWord sym -> Integer -> SWord sym
svShr' b x i = svIte b (svNot (svShr (svNot x) j)) (svShr x j)
  where j = fromInteger (i `min` toInteger (intSizeOf x))

svShiftL :: SBool sym -> SWord sym -> SWord sym -> SWord sym
svShiftL b x i = svIte b (svNot (svShiftLeft (svNot x) i)) (svShiftLeft x i)

svShiftR :: SBool sym -> SWord sym -> SWord sym -> SWord sym
svShiftR b x i = svIte b (svNot (svShiftRight (svNot x) i)) (svShiftRight x i)

------------------------------------------------------------
-- Stream operations

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: SValue sym
mkStreamOp =
  constFun $
  strictFun $ \f -> do
    r <- newIORef Map.empty
    return $ VExtra (SStream (\n -> apply f (ready (VNat n))) r)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: SValue sym
streamGetOp =
  constFun $
  strictFun $ \xs -> return $
  Prims.natFun'' "streamGetOp" $ \n -> lookupSStream xs (toInteger n)

-- bvStreamGet :: (a :: sort 0) -> (w :: Nat) -> Stream a -> bitvector w -> a;
bvStreamGetOp :: SValue sym
bvStreamGetOp =
  constFun $
  constFun $
  strictFun $ \xs -> return $
  wordFun $ \ilv ->
  selectV (lazyMux muxBVal) ((2 ^ intSizeOf ilv) - 1) (lookupSStream xs) ilv

lookupSStream :: SValue sym -> Integer -> IO (SValue sym)
lookupSStream (VExtra (SStream f r)) n = do
   m <- readIORef r
   case Map.lookup n m of
     Just v  -> return v
     Nothing -> do v <- f n
                   writeIORef r (Map.insert n v m)
                   return v
lookupSStream _ _ = fail "expected Stream"

------------------------------------------------------------
-- Ite ops

muxBVal :: SBool sym -> SValue sym -> SValue sym -> IO (SValue sym)
muxBVal = Prims.muxValue prims

extraFn :: SBool sym -> What4Extra sym -> What4Extra sym -> What4Extra sym
extraFn _ _ _ = error "iteOp: malformed arguments (extraFn)"
-}
------------------------------------------------------------
-- External interface

{-

-- | Abstract constants with names in the list 'unints' are kept as
-- uninterpreted constants; all others are unfolded.
sbvSolveBasic :: sym
              -> ModuleMap
              -> Map Ident (SValue sym)
              -> [String]
              -> Term
              -> IO (SValue sym)
sbvSolveBasic sym m addlPrims unints t = do
  let unintSet = Set.fromList unints
  let uninterpreted nm ty
        | Set.member nm unintSet = Just $ parseUninterpreted [] nm ty
        | otherwise              = Nothing
  cfg <- Sim.evalGlobal m (Map.union (constMap sym) addlPrims)
         (const (parseUninterpreted []))
         uninterpreted
  Sim.evalSharedTerm cfg t

-- given a list of What4 values, their name, and type,
-- return a symbolic value
parseUninterpreted :: [SVal] -> String -> SValue sym -> IO (SValue sym)
parseUninterpreted cws nm ty =
  case ty of
    (VPiType _ f)
      -> return $
         strictFun $ \x -> do
           (cws', suffix) <- flattenSValue sym x
           t2 <- f (ready x)
           parseUninterpreted (cws ++ cws') (nm ++ suffix) t2

    VBoolType
      -> return $ vBool $ mkUninterpreted KBool cws nm

    VIntType
      -> return $ vInteger $ mkUninterpreted KUnbounded cws nm

    (VVecType (VNat n) VBoolType)
      -> return $ vWord $ mkUninterpreted (KBounded False (fromIntegral n)) cws nm

    (VVecType (VNat n) ety)
      -> do xs <- sequence $
                  [ parseUninterpreted cws (nm ++ "@" ++ show i) ety
                  | i <- [0 .. n-1] ]
            return (VVector (V.fromList (map ready xs)))

    VUnitType
      -> return VUnit

    (VPairType ty1 ty2)
      -> do x1 <- parseUninterpreted cws (nm ++ ".L") ty1
            x2 <- parseUninterpreted cws (nm ++ ".R") ty2
            return (VPair (ready x1) (ready x2))

    VEmptyType
      -> return VEmpty

    (VFieldType f ty1 ty2)
      -> do x1 <- parseUninterpreted cws (nm ++ ".L") ty1
            x2 <- parseUninterpreted cws (nm ++ ".R") ty2
            return (VField f (ready x1) x2)

    (VRecordType elem_tps)
      -> (VRecordValue <$>
          mapM (\(f,tp) ->
                 (f,) <$> ready <$>
                 parseUninterpreted cws (nm ++ "." ++ f) tp) elem_tps)

    _ -> fail $ "could not create uninterpreted type for " ++ show ty


mkUninterpreted :: Kind -> [SVal] -> String -> SVal
mkUninterpreted k args nm = svUninterpreted k nm' Nothing args
  where nm' = "|" ++ nm ++ "|" -- enclose name to allow primes and other non-alphanum chars

asPredType :: SValue sym -> IO [SValue sym]
asPredType v =
  case v of
    VBoolType -> return []
    VPiType v1 f ->
      do v2 <- f (error "asPredType: unsupported dependent SAW-Core type")
         vs <- asPredType v2
         return (v1 : vs)
    _ -> fail $ "non-boolean result type: " ++ show v

vAsFirstOrderType :: SValue sym -> Maybe FirstOrderType
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


sbvSolve :: SharedContext
         -> Map Ident SValue sym
         -> [String]
         -> Term
         -> IO ([Maybe Labeler], Symbolic SBool)
sbvSolve sc addlPrims unints t = do
  modmap <- scGetModuleMap sc
  let eval = sbvSolveBasic modmap addlPrims unints
  ty <- eval =<< scTypeOf sc t
  let argNames = map fst (fst (R.asLambdaList t))
  let moreNames = [ "var" ++ show (i :: Integer) | i <- [0 ..] ]
  argTs <- asPredType ty
  (labels, vars) <-
    flip evalStateT 0 $ unzip <$>
    sequence (zipWith newVarsForType argTs (argNames ++ moreNames))
  bval <- eval t
  let prd = do
              bval' <- traverse (fmap ready) vars >>= (liftIO . applyAll bval)
              case bval' of
                VBool b -> return b
                _ -> fail $ "sbvSolve: non-boolean result type. " ++ show bval'
  return (labels, prd)

data Labeler
   = BoolLabel String
   | IntegerLabel String
   | WordLabel String
   | VecLabel (Vector Labeler)
   | TupleLabel (Vector Labeler)
   | RecLabel (Map FieldName Labeler)
     deriving (Show)

nextId :: StateT Int IO String
nextId = ST.get >>= (\s-> modify (+1) >> return ("x" ++ show s))

--unzipMap :: Map k (a, b) -> (Map k a, Map k b)
--unzipMap m = (fmap fst m, fmap snd m)

myfun ::(Map String (Labeler, Symbolic SValue sym)) -> (Map String Labeler, Map String (Symbolic SValue sym))
myfun = fmap fst A.&&& fmap snd

newVarsForType :: SValue sym -> String -> StateT Int IO (Maybe Labeler, Symbolic SValue)
newVarsForType v nm =
  case vAsFirstOrderType v of
    Just fot ->
      do (l, sv) <- newVars fot
         return (Just l, sv)
    Nothing ->
      do sv <- lift $ parseUninterpreted [] nm v
         return (Nothing, return sv)

newVars :: FirstOrderType -> StateT Int IO (Labeler, Symbolic SValue)
newVars FOTBit = nextId <&> \s-> (BoolLabel s, vBool <$> existsSBool s)
newVars FOTInt = nextId <&> \s-> (IntegerLabel s, vInteger <$> existsSInteger s)
newVars (FOTVec n FOTBit) =
  if n == 0
    then nextId <&> \s-> (WordLabel s, return (vWord (literalSWord 0 0)))
    else nextId <&> \s-> (WordLabel s, vWord <$> existsSWord s (fromIntegral n))
newVars (FOTVec n tp) = do
  (labels, vals) <- V.unzip <$> V.replicateM (fromIntegral n) (newVars tp)
  return (VecLabel labels, VVector <$> traverse (fmap ready) vals)
newVars (FOTTuple ts) = do
  (labels, vals) <- V.unzip <$> traverse newVars (V.fromList ts)
  return (TupleLabel labels, vTuple <$> traverse (fmap ready) (V.toList vals))
newVars (FOTRec tm) = do
  (labels, vals) <- myfun <$> (traverse newVars tm :: StateT Int IO (Map String (Labeler, Symbolic SValue)))
  return (RecLabel labels, vRecord <$> traverse (fmap ready) (vals :: (Map String (Symbolic SValue))))
-}
------------------------------------------------------------
-- Code Generation

{-
newCodeGenVars :: (Nat -> Bool) -> FirstOrderType -> StateT Int IO (What4CodeGen SValue)
newCodeGenVars _checkSz FOTBit = nextId <&> \s -> (vBool <$> svCgInput KBool s)
newCodeGenVars _checkSz FOTInt = nextId <&> \s -> (vInteger <$> svCgInput KUnbounded s)
newCodeGenVars checkSz (FOTVec n FOTBit)
  | n == 0    = nextId <&> \_ -> return (vWord (literalSWord 0 0))
  | checkSz n = nextId <&> \s -> vWord <$> cgInputSWord s (fromIntegral n)
  | otherwise = nextId <&> \s -> fail $ "Invalid codegen bit width for input variable \'" ++ s ++ "\': " ++ show n
newCodeGenVars checkSz (FOTVec n (FOTVec m FOTBit))
  | m == 0    = nextId <&> \_ -> return (VVector $ V.fromList $ replicate (fromIntegral n) (ready $ vWord (literalSWord 0 0)))
  | checkSz m = do
      let k = KBounded False (fromIntegral m)
      vals <- nextId <&> \s -> svCgInputArr k (fromIntegral n) s
      return (VVector . V.fromList . fmap (ready . vWord) <$> vals)
  | otherwise = nextId <&> \s -> fail $ "Invalid codegen bit width for input variable array \'" ++ s ++ "\': " ++ show n
newCodeGenVars checkSz (FOTVec n tp) = do
  vals <- V.replicateM (fromIntegral n) (newCodeGenVars checkSz tp)
  return (VVector <$> traverse (fmap ready) vals)
newCodeGenVars checkSz (FOTTuple ts) = do
  vals <- traverse (newCodeGenVars checkSz) ts
  return (vTuple <$> traverse (fmap ready) vals)
newCodeGenVars checkSz (FOTRec tm) = do
  vals <- traverse (newCodeGenVars checkSz) tm
  return (vRecord <$> traverse (fmap ready) vals)

cgInputSWord :: String -> Int -> What4CodeGen SWord
cgInputSWord s n = svCgInput (KBounded False n) s

argTypes :: SharedContext -> Term -> IO ([Term], Term)
argTypes sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> do
       (ts,res) <- argTypes sc t2
       return (t1:ts, res)
    _ -> return ([], t')

sbvCodeGen_definition
  :: SharedContext
  -> Map Ident SValue
  -> [String]
  -> Term
  -> (Nat -> Bool) -- ^ Allowed word sizes
  -> IO (What4CodeGen (), [FirstOrderType], FirstOrderType)
sbvCodeGen_definition sc addlPrims unints t checkSz = do
  ty <- scTypeOf sc t
  (argTs,resTy) <- argTypes sc ty
  shapes <- traverse (asFirstOrderType sc) argTs
  resultShape <- asFirstOrderType sc resTy
  modmap <- scGetModuleMap sc
  bval <- sbvSolveBasic modmap addlPrims unints t
  vars <- evalStateT (traverse (newCodeGenVars checkSz) shapes) 0
  let codegen = do
        args <- traverse (fmap ready) vars
        bval' <- liftIO (applyAll bval args)
        sbvSetResult checkSz resultShape bval'
  return (codegen, shapes, resultShape)


sbvSetResult :: (Nat -> Bool)
             -> FirstOrderType
             -> SValue sym
             -> What4CodeGen ()
sbvSetResult _checkSz FOTBit (VBool b) = do
   svCgReturn b
sbvSetResult checkSz (FOTVec n FOTBit) v
   | n == 0    = return ()
   | checkSz n = do
      w <- liftIO $ toWord v
      svCgReturn w
   | otherwise =
      fail $ "Invalid word size in result: " ++ show n
sbvSetResult checkSz ft v = do
   void $ sbvSetOutput checkSz ft v 0


sbvSetOutput :: (Nat -> Bool)
             -> FirstOrderType
             -> SValue sym
             -> Int
             -> What4CodeGen Int
sbvSetOutput _checkSz FOTBit (VBool b) i = do
   svCgOutput ("out_"++show i) b
   return $! i+1
sbvSetOutput checkSz (FOTVec n FOTBit) v i
   | n == 0    = return i
   | checkSz n = do
       w <- liftIO $ toWord v
       svCgOutput ("out_"++show i) w
       return $! i+1
   | otherwise =
       fail $ "Invalid word size in output " ++ show i ++ ": " ++ show n

sbvSetOutput checkSz (FOTVec n t) (VVector xv) i = do
   xs <- liftIO $ traverse force $ V.toList xv
   unless (toInteger n == toInteger (length xs)) $
     fail "sbvCodeGen: vector length mismatch when setting output values"
   case asWordList xs of
     Just ws -> do svCgOutputArr ("out_"++show i) ws
                   return $! i+1
     Nothing -> foldM (\i' x -> sbvSetOutput checkSz t x i') i xs
sbvSetOutput _checkSz (FOTTuple []) VUnit i =
   return i
sbvSetOutput checkSz (FOTTuple (t:ts)) (VPair l r) i = do
   l' <- liftIO $ force l
   r' <- liftIO $ force r
   sbvSetOutput checkSz t l' i >>= sbvSetOutput checkSz (FOTTuple ts) r'

sbvSetOutput checkSz (FOTTuple ts) (asVTuple -> Just thunks) i = do
   vs <- liftIO $ mapM force thunks
   foldM (\j (t,v) -> sbvSetOutput checkSz t v j) i (zip ts vs)

sbvSetOutput _checkSz (FOTRec fs) VUnit i | Map.null fs = do
   return i
sbvSetOutput checkSz (FOTRec fs) (VField fn x rec) i = do
   x' <- liftIO $ force x
   case Map.lookup fn fs of
     Just t -> do
       let fs' = Map.delete fn fs
       sbvSetOutput checkSz t x' i >>= sbvSetOutput checkSz (FOTRec fs') rec
     Nothing -> fail "sbvCodeGen: type mismatch when setting record output value"

sbvSetOutput _checkSz (FOTRec fs) (VRecordValue []) i | Map.null fs = return i

sbvSetOutput checkSz (FOTRec fs) (VRecordValue ((fn,x):rest)) i = do
   x' <- liftIO $ force x
   case Map.lookup fn fs of
     Just t -> do
       let fs' = Map.delete fn fs
       sbvSetOutput checkSz t x' i >>=
         sbvSetOutput checkSz (FOTRec fs') (VRecordValue rest)
     Nothing -> fail "sbvCodeGen: type mismatch when setting record output value"

sbvSetOutput _checkSz _ft _v _i = do
   fail "sbvCode gen: type mismatch when setting output values"


sbvCodeGen :: SharedContext
           -> Map Ident (SValue sym)
           -> [String]
           -> Maybe FilePath
           -> String
           -> Term
           -> IO ()
sbvCodeGen sc addlPrims unints path fname t = do
  -- The What4 C code generator expects only these word sizes
  let checkSz n = n `elem` [8,16,32,64]

  (codegen,_,_) <- sbvCodeGen_definition sc addlPrims unints t checkSz
  compileToC path fname codegen
-}
