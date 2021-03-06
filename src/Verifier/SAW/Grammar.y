{
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-tabs #-}

{- |
Module      : Verifier.SAW.Grammar
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Grammar
  ( Decl(..)
  , Term(..)
  , parseSAW
  , parseSAWTerm
  , lexer
  ) where

import Control.Applicative ((<$>))
import Control.Monad ()
import Control.Monad.State (State, get, gets, modify, runState)
import qualified Data.ByteString.Lazy.UTF8 as B
import Data.Maybe (isJust)
import Data.Traversable
import Data.Word
import System.Directory (getCurrentDirectory)

import Prelude hiding (mapM, sequence)

import Verifier.SAW.UntypedAST
import Verifier.SAW.Module (DefQualifier(..))
import Verifier.SAW.Lexer

}

%name parseSAW2 Module
%name parseSAWTerm2 Term

%tokentype { PosPair Token }
%monad { Parser }
%lexer { lexer } { PosPair _ TEnd }
%error { parseError }
%expect 0

%token
  '#'     { PosPair _ (TKey "#") }
  '->'    { PosPair _ (TKey "->") }
  '='     { PosPair _ (TKey "=") }
  '\\'    { PosPair _ (TKey "\\") }
  ';'     { PosPair _ (TKey ";") }
  '::'    { PosPair _ (TKey "::") }
  ','     { PosPair _ (TKey ",") }
  '.'     { PosPair _ (TKey ".") }
  '..'    { PosPair _ (TKey "..") }
  '?'     { PosPair _ (TKey "?") }
  '??'    { PosPair _ (TKey "??") }
  '???'   { PosPair _ (TKey "???") }
  '('     { PosPair _ (TKey "(") }
  ')'     { PosPair _ (TKey ")") }
  '['     { PosPair _ (TKey "[") }
  ']'     { PosPair _ (TKey "]") }
  '{'     { PosPair _ (TKey "{") }
  '}'     { PosPair _ (TKey "}") }
  '|'     { PosPair _ (TKey "|") }
  'as'        { PosPair _ (TKey "as") }
  'data'      { PosPair _ (TKey "data") }
  'hiding'    { PosPair _ (TKey "hiding") }
  'import'    { PosPair _ (TKey "import") }
  'in'        { PosPair _ (TKey "in") }
  'let'       { PosPair _ (TKey "let") }
  'module'    { PosPair _ (TKey "module") }
  'qualified' { PosPair _ (TKey "qualified") }
  'sort'      { PosPair _ (TKey "sort") }
  'Prop'      { PosPair _ (TKey "Prop") }
  'where'     { PosPair _ (TKey "where") }
  'axiom'     { PosPair _ (TKey "axiom") }
  'primitive' { PosPair _ (TKey "primitive") }
  nat      { PosPair _ (TNat _) }
  '_'      { PosPair _ (TIdent "_") }
  ident    { PosPair _ (TIdent _) }
  identrec { PosPair _ (TRecursor _) }
  string   { PosPair _ (TString _) }

%%

Module :: { Module }
Module : 'module' ModuleName 'where' list(Import) list(SAWDecl) { Module $2 $4 $5 }

ModuleName :: { PosPair ModuleName }
ModuleName : sepBy (Ident, '.') { mkPosModuleName $1 }

Import :: { Import }
Import : 'import' ModuleName opt(ModuleImports) ';'
          { Import $2 $3 }

SAWDecl :: { Decl }
SAWDecl : 'data' Ident VarCtx '::' LTerm 'where' '{' list(CtorDecl) '}'
             { DataDecl $2 $3 $5 $8 }
        | 'primitive' Ident '::' LTerm ';'
             { TypeDecl PrimQualifier $2 $4 }
        | 'axiom' Ident '::' LTerm ';'
             { TypeDecl AxiomQualifier $2 $4 }
        | Ident '::' LTerm ';' { TypeDecl NoQualifier $1 $3 }
        | Ident list(TermVar) '=' LTerm ';' { TermDef $1 $2 $4 }

ModuleImports :: { ImportConstraint }
ModuleImports : 'hiding' ImportNames { HidingImports $2 }
              | ImportNames { SpecificImports $1 }

ImportNames :: { [String] }
ImportNames : '(' sepBy(ImportName, ',') ')' { $2 }

ImportName :: { String }
ImportName : ident { tokIdent $ val $1 }

TermVar :: { TermVar }
TermVar
  : Ident { TermVar $1 }
  | '_' { UnusedVar (pos $1) }

-- A context of variables which may or may not be typed
DefVarCtx :: { [(TermVar, Maybe Term)] }
DefVarCtx : list(DefVarCtxItem) { concat $1 }

DefVarCtxItem :: { [(TermVar, Maybe Term)] }
DefVarCtxItem : TermVar { [($1, Nothing)] }
              | '(' list(TermVar) '::'  LTerm ')'
                { map (\var -> (var, Just $4)) $2 }

-- A context of variables, all of which must be typed; i.e., a list syntactic
-- elements of the form (x y z :: tp) (x2 y3 :: tp2) ...
VarCtx :: { [(TermVar, Term)] }
VarCtx : list(VarCtxItem) { concat $1 }

VarCtxItem :: { [(TermVar, Term)] }
VarCtxItem : '(' list(TermVar) '::' LTerm ')' { map (\var -> (var,$4)) $2 }

-- Constructor declaration of the form "c (x1 x2 :: tp1) ... (z1 :: tpn) :: tp"
CtorDecl :: { CtorDecl }
CtorDecl : Ident VarCtx '::' LTerm ';' { Ctor $1 $2 $4 }

Term :: { Term }
Term : LTerm { $1 }
     | LTerm '::' LTerm { TypeConstraint $1 (pos $2) $3 }

-- Term with uses of pi and lambda, but no type ascriptions
LTerm :: { Term }
LTerm : AppTerm                          { $1 }
      | PiArg '->' LTerm                 { Pi (pos $2) $1 $3 }
      | '\\' VarCtx '->' LTerm           { Lambda (pos $1) $2 $4 }

PiArg :: { [(TermVar, Term)] }
PiArg : AppTerm { mkPiArg $1 }

-- Term formed from applications of atomic expressions
AppTerm :: { Term }
AppTerm : AtomTerm                 { $1 }
        | AppTerm AtomTerm         { App $1 $2 }

AtomTerm :: { Term }
AtomTerm
  : nat                          { NatLit (pos $1) (tokNat (val $1)) }
  | string                       { StringLit (pos $1) (tokString (val $1)) }
  | Ident                        { Name $1 }
  | IdentRec                     { Recursor Nothing $1 }
  | 'Prop'                       { Sort (pos $1) propSort }
  | 'sort' nat                   { Sort (pos $1) (mkSort (tokNat (val $2))) }
  | AtomTerm '.' Ident           { RecordProj $1 (val $3) }
  | AtomTerm '.' IdentRec        {% parseRecursorProj $1 $3 }
  | AtomTerm '.' nat             {% parseTupleSelector $1 (fmap tokNat $3) }
  | '(' sepBy(Term, ',') ')'     { parseTuple (pos $1) $2 }
  | '#' '(' sepBy(Term, ',') ')'       {% parseTupleType (pos $1) $3 }
  |     '[' sepBy(Term, ',') ']'       { VecLit (pos $1) $2 }
  |     '{' sepBy(FieldValue, ',') '}' { RecordValue (pos $1) $2 }
  | '#' '{' sepBy(FieldType, ',') '}'  { RecordType  (pos $1) $3 }

    -- FIXME: old-style pairs, pair types, and pair projections
  |     '(' Term '|' Term ')'          { OldPairValue (pos $1) $2 $4 }
  | '#' '(' Term '|' Term ')'          { OldPairType (pos $1) $3 $5 }
  | AtomTerm '.' '(' nat ')'           {% mkOldTupleProj $1 (tokNat (val $4)) }

Ident :: { PosPair String }
Ident : ident { fmap tokIdent $1 }

IdentRec :: { PosPair String }
IdentRec : identrec { fmap tokRecursor $1 }

FieldValue :: { (PosPair String, Term) }
FieldValue : Ident '=' Term { ($1, $3) }

FieldType :: { (PosPair String, Term) }
FieldType : Ident '::' LTerm { ($1, $3) }

opt(q) :: { Maybe q }
  : { Nothing }
  | q { Just $1 }

-- Two elements p and r separated by q and terminated by s
sepPair(p,q,r,s) :: { (p,r) }
  : p q r s { ($1,$3) }

-- A possibly-empty list of p's separated by q.
sepBy(p,q) :: { [p] }
  : {- empty -} { [] }
  | sepBy1(p,q) { $1 }

-- A possibly-empty list of p's separated by q.
sepBy1(p,q) :: { [p] }
  : rsepBy1(p,q) { reverse $1 }

rsepBy1(p,q) :: { [p] }
  : p { [$1] }
  | rsepBy1(p,q) q p { $3 : $1 }

-- A list of 0 or more p's, terminated by q's
list(p) :: { [p] }
  : {- empty -} { [] }
  | rlist1(p) { reverse $1 }

-- A list of 0 or more p's, terminated by q's
list1(p) :: { [p] }
  : rlist1(p) { reverse $1 }

-- A reversed list of at least 1 p's
rlist1(p) :: { [p] }
  : p           { [$1]    }
  | rlist1(p) p { $2 : $1 }

{
data ParseError
  = UnexpectedLex [Word8]
  | UnexpectedEndOfBlockComment
  | UnexpectedToken Token
  | ParseError String
  | UnexpectedEnd
  deriving (Show)

type ErrorList = [PosPair ParseError]

data ParserState = PS { psInput :: AlexInput
                      , psErrors :: [PosPair ParseError]
                      }

newtype Parser a = Parser { _unParser :: State ParserState a }
  deriving (Applicative, Functor, Monad)

addError :: Pos -> ParseError -> Parser ()
addError p err = Parser $ modify $ \s -> s { psErrors = PosPair p err : psErrors s }

setInput :: AlexInput -> Parser ()
setInput inp = Parser $ modify $ \s -> s { psInput = inp }

parsePos :: Parser Pos
parsePos = Parser $ gets (pos . psInput)

lexer :: (PosPair Token -> Parser a) -> Parser a
lexer f = do
  let go prevErr next = do
        let addErrors =
              case prevErr of
                Nothing -> return ()
                Just (po,l) -> addError po (UnexpectedLex (reverse l))
        s <- Parser get
        let inp@(PosPair p (Buffer _ b)) = psInput s
            end = addErrors >> next (PosPair p TEnd)
        case alexScan inp 0 of
          AlexEOF -> end
          AlexError _ ->
            case alexGetByte inp of
              Just (w,inp') -> do
                setInput inp'
                case prevErr of
                  Nothing -> go (Just (p,[w])) next
                  Just (po,l) -> go (Just (po,w:l)) next
              Nothing -> end
          AlexSkip inp' _ -> addErrors >> setInput inp' >> go Nothing next
          AlexToken inp' l act -> do
            addErrors
            setInput inp'
            let v = act (B.toString (B.take (fromIntegral l) b))
            next (PosPair p v)
  let read i tkn =
        case val tkn of
          TCmntS -> go Nothing (read (i+1))
          TCmntE | i > 0 -> go Nothing (read (i-1))
                 | otherwise -> do
                     addError (pos tkn) (UnexpectedLex (fmap (fromIntegral . fromEnum) "-}"))
                     go Nothing (read 0)
          _ | i > 0 -> go Nothing (read i)
            | otherwise -> f tkn
  go Nothing (read (0::Integer))

-- | Run parser given a directory for the base (used for making pathname relative),
-- bytestring to parse, and parser to run.
runParser :: Parser a -> FilePath -> FilePath -> B.ByteString -> (a,ErrorList)
runParser (Parser m) base path b = (r, reverse (psErrors s))
  where initState = PS { psInput = initialAlexInput base path b, psErrors = [] }
        (r,s) = runState m initState

parseSAW :: FilePath -> FilePath -> B.ByteString -> (Module,ErrorList)
parseSAW = runParser parseSAW2

parseSAWTerm :: FilePath -> FilePath -> B.ByteString -> (Term,ErrorList)
parseSAWTerm = runParser parseSAWTerm2

parseError :: PosPair Token -> Parser a
parseError pt = do
  addError (pos pt) (UnexpectedToken (val pt))
  fail $ (ppPos (pos pt)) ++ " Parse error\n  " ++ (ppToken (val pt))

addParseError :: Pos -> String -> Parser ()
addParseError p s = addError p (ParseError s)

unexpectedIntLiteral :: Pos -> Integer -> String -> Parser ()
unexpectedIntLiteral p _ ctxt = do
  addParseError p $ "Unexpected integer literal when parsing " ++ ctxt ++ "."

unexpectedTypeConstraint :: Pos -> Parser ()
unexpectedTypeConstraint p = addParseError p "Unexpected type constraint."

unexpectedPi :: Pos -> Parser ()
unexpectedPi p = addParseError p "Unexpected pi expression"

unexpectedLambda :: Pos -> Parser ()
unexpectedLambda p = addParseError p "Unexpected lambda expression"

unexpectedOpenParen :: Pos -> Parser ()
unexpectedOpenParen p = addParseError p "Unexpected parenthesis"

-- Try to parse an expression as a list of identifiers
exprAsIdentList :: Term -> Maybe [TermVar]
exprAsIdentList (Name x) = return [TermVar x]
exprAsIdentList (App expr (Name x)) =
  (++ [TermVar x]) <$> exprAsIdentList expr
exprAsIdentList _ = Nothing

-- | Pi expressions should have one of the forms:
--
-- * '(' list(Ident) '::' LTerm ')' '->' LTerm
-- * AppTerm '->' LTerm
--
-- This function takes in a term for the LHS and tests if it is of the first
-- form, or, if not, converts the second form into the first by making a single
-- "unused" variable with the name "_"
mkPiArg :: Term -> [(TermVar, Term)]
mkPiArg (TypeConstraint (exprAsIdentList -> Just xs) _ t) =
  map (\x -> (x, t)) xs
mkPiArg lhs = [(UnusedVar (pos lhs), lhs)]

-- | Parse a tuple value @(x1, .., xn)@ as a record value whose fields are named
-- @1@, @2@, etc. As a special case, the unary tuple @(x)@ is just @x@.
parseTuple :: Pos -> [Term] -> Term
parseTuple _ [t] = t
parseTuple p ts = mkTupleValue p ts

-- | Parse a tuple type @#(x1, .., xn)@ as a record type whose fields are named
-- @1@, @2@, etc. As a special case, the unary tuple @(x)@ is just @x@.
parseTupleType :: Pos -> [Term] -> Parser Term
parseTupleType p [tp] =
  addParseError p "Tuple type may not contain a single value." >>
  return (badTerm p)
parseTupleType p tps = return $ mkTupleType p tps

-- | Parse an old-style tuple projection of the form @t.(1)@ or @t.(2)@
mkOldTupleProj :: Term -> Integer -> Parser Term
mkOldTupleProj t 1 = return $ OldPairLeft t
mkOldTupleProj t 2 = return $ OldPairRight t
mkOldTupleProj t _ =
  do addParseError (pos t) "Old-style projections must be either .(1) or .(2)"
     return (badTerm (pos t))

-- | Parse a term as a dotted list of strings
parseModuleName :: Term -> Maybe [String]
parseModuleName (RecordProj t str) = (++ [str]) <$> parseModuleName t
parseModuleName _ = Nothing

-- | Parse a qualified recursor @M1.M2...Mn.d#rec@
parseRecursorProj :: Term -> PosPair String -> Parser Term
parseRecursorProj (parseModuleName -> Just mnm) i =
  return $ Recursor (Just $ mkModuleName mnm) i
parseRecursorProj t _ =
  do addParseError (pos t) "Malformed recursor projection"
     return (badTerm (pos t))

parseTupleSelector :: Term -> PosPair Integer -> Parser Term
parseTupleSelector t i =
  if val i >= 1 then return (mkTupleSelector t (val i)) else
    do addParseError (pos t) "non-positive tuple projection index"
       return (badTerm (pos t))

-- | Crete a module name given a list of strings with the top-most
-- module name given first.
mkPosModuleName :: [PosPair String] -> PosPair ModuleName
mkPosModuleName [] = error "internal: Unexpected empty module name"
mkPosModuleName l = PosPair p (mkModuleName nms)
  where nms = fmap val l
        p = pos (last l)
}
