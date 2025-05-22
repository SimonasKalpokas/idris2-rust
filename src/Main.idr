module Main

import Core.Context
import Compiler.Common
import Idris.Driver
import Idris.Syntax

import Data.Vect
import Core.Env
import Core.Value

import Compiler.Common
import Compiler.ANF
import Libraries.Data.String.Extra
import Libraries.Data.SortedSet
import Libraries.Data.NameMap

import Idris.Doc.String
import Idris.Pretty.Annotations
import Idris.Resugar

data ArgCounter : Type where

getNextCounter : {auto a : Ref ArgCounter Nat} -> Core String
getNextCounter = do
    c <- get ArgCounter
    put ArgCounter (S c)
    pure $ show c

replicateC : Nat -> Core a -> Core (List a)
replicateC Z _ = pure []
replicateC (S n) action = do
  x <- action
  xs <- replicateC n action
  pure (x :: xs)

rangeNat : Nat -> List Nat
rangeNat n = go n []
  where
    go : Nat -> List Nat -> List Nat
    go Z acc = acc
    go (S n) acc = go n (n :: acc)

isTagged : List AConAlt -> Bool
isTagged [] = False
isTagged (MkAConAlt _ _ (Just _) _ _:: _) = True
isTagged (MkAConAlt _ _ Nothing _ _ :: _) = False

integer_switch : List AConstAlt -> Bool
integer_switch [] = True
integer_switch (MkAConstAlt c _  :: _) =
    case c of
        (I x) => True
        (I8 x) => True
        (I16 x) => True
        (I32 x) => True
        (I64 x) => True
        (B8 x) => True
        (B16 x) => True
        (B32 x) => True
        (B64 x) => True
        (BI x) => True
        (Ch x) => True
        _ => False

switch_type : List AConstAlt -> Constant
switch_type [] = WorldVal
switch_type (MkAConstAlt c _  :: _) =
    case c of
        (I x) => I x
        (I8 x) => I8 x
        (I16 x) => I16 x
        (I32 x) => I32 x
        (I64 x) => I64 x
        (B8 x) => B8 x
        (B16 x) => B16 x
        (B32 x) => B32 x
        (B64 x) => B64 x
        (BI x) => BI x
        (Ch x) => Ch x
        (Str x) => Str x
        (Db x) => Db x
        _ => WorldVal

mapWithIndex : (Nat -> a -> b) -> List a -> List b
mapWithIndex f xs = go 0 xs
  where
    go : Nat -> List a -> List b
    go _ [] = []
    go i (x :: xs) = f i x :: go (i + 1) xs

rustAVar : AVar -> String
rustAVar (ALocal i) = "val_v" ++ show i
rustAVar ANull = "Rc::new(()) as Rc<dyn Any>"

showRustCleanStringChar : Char -> String -> String
showRustCleanStringChar ' ' = ("_" ++)
showRustCleanStringChar '!' = ("_bang" ++)
showRustCleanStringChar '"' = ("_quotation" ++)
showRustCleanStringChar '#' = ("_number" ++)
showRustCleanStringChar '$' = ("_dollar" ++)
showRustCleanStringChar '%' = ("_percent" ++)
showRustCleanStringChar '&' = ("_and" ++)
showRustCleanStringChar '\'' = ("_tick" ++)
showRustCleanStringChar '(' = ("_parenOpen" ++)
showRustCleanStringChar ')' = ("_parenClose" ++)
showRustCleanStringChar '*' = ("_star" ++)
showRustCleanStringChar '+' = ("_plus" ++)
showRustCleanStringChar ',' = ("_comma" ++)
showRustCleanStringChar '-' = ("__" ++)
showRustCleanStringChar '.' = ("_dot" ++)
showRustCleanStringChar '/' = ("_slash" ++)
showRustCleanStringChar ':' = ("_colon" ++)
showRustCleanStringChar ';' = ("_semicolon" ++)
showRustCleanStringChar '<' = ("_lt" ++)
showRustCleanStringChar '=' = ("_eq" ++)
showRustCleanStringChar '>' = ("_gt" ++)
showRustCleanStringChar '?' = ("_question" ++)
showRustCleanStringChar '@' = ("_at" ++)
showRustCleanStringChar '[' = ("_bracketOpen" ++)
showRustCleanStringChar '\\' = ("_backslash" ++)
showRustCleanStringChar ']' = ("_bracketClose" ++)
showRustCleanStringChar '^' = ("_hat" ++)
showRustCleanStringChar '_' = ("_" ++)
showRustCleanStringChar '`' = ("_backquote" ++)
showRustCleanStringChar '{' = ("_braceOpen" ++)
showRustCleanStringChar '|' = ("_or" ++)
showRustCleanStringChar '}' = ("_braceClose" ++)
showRustCleanStringChar '~' = ("_tilde" ++)
showRustCleanStringChar c = strCons c

showRustCleanString : List Char -> String -> String
showRustCleanString [] = id
showRustCleanString (c ::cs) = (showRustCleanStringChar c) . showRustCleanString cs

rustCleanString : String -> String
rustCleanString cs = showRustCleanString (unpack cs) ""

getTmpVarName : {auto a : Ref ArgCounter Nat} -> Core String
getTmpVarName = pure $ "tmp_" ++ !(getNextCounter)

rustUserName : UserName -> String
rustUserName (Basic str) = str
rustUserName (Field str) = "." ++ str
rustUserName Underscore = "_"

rustName : Name -> String
rustName (NS ns n) = rustCleanString (showNSWithSep "_" ns) ++ "_" ++ rustName n
rustName (UN n) = rustCleanString $ rustUserName n
rustName (MN str i) = rustCleanString str ++ "_" ++ (rustCleanString $ show i)
rustName (PV n i) = "pat__" ++ rustName n
rustName (DN str n) = rustName n
rustName (Nested i n) = "n__" ++ rustCleanString (show i) ++ "_" ++ rustName n
rustName (CaseBlock x y) = "case__" ++ rustCleanString (show x) ++ "_" ++ rustCleanString (show y)
rustName (WithBlock x y) = "with__" ++ rustCleanString (show x) ++ "_" ++ rustCleanString (show y)
rustName (Resolved i) = "fn__" ++ rustCleanString (show i)

rustType : PrimType -> String
rustType IntType = "Int"
rustType Int8Type = "Int"
rustType Int16Type = "Int"
rustType Int32Type = "Int"
rustType Int64Type = "Int"
rustType IntegerType = "Int"
rustType Bits8Type = "Int"
rustType Bits16Type = "Int"
rustType Bits32Type = "Int"
rustType Bits64Type = "Int"
rustType StringType = "String"
rustType CharType = "Char"
rustType DoubleType = "Double"
rustType WorldType = "World"

rustTypeName : Name -> String
rustTypeName (UN (Basic "Int")) = "IntType"
rustTypeName (UN (Basic "Int8")) = "IntType"
rustTypeName (UN (Basic "Int16")) = "IntType"
rustTypeName (UN (Basic "Int32")) = "IntType"
rustTypeName (UN (Basic "Int64")) = "IntType"
rustTypeName (UN (Basic "Integer")) = "IntType"
rustTypeName (UN (Basic "Bits8")) = "IntType"
rustTypeName (UN (Basic "Bits16")) = "IntType"
rustTypeName (UN (Basic "Bits32")) = "IntType"
rustTypeName (UN (Basic "Bits64")) = "IntType"
rustTypeName (UN (Basic "String")) = "StringType"
rustTypeName (UN (Basic "Char")) = "CharType"
rustTypeName (UN (Basic "Double")) = "DoubleType"
rustTypeName (UN (Basic "World")) = "WorldType"
rustTypeName _ = "Unexpected name"

rustPrimType : PrimType -> String
rustPrimType t = "IdrisMetaType::\{rustType t}"

showConstant : Constant -> String
showConstant (I i) = show i
showConstant (I8 i) = show i
showConstant (I16 i) = show i
showConstant (I32 i) = show i
showConstant (I64 i) = show i
showConstant (BI i) = show i
showConstant (B8 m) = show m
showConstant (B16 m) = show m
showConstant (B32 m) = show m
showConstant (B64 m) = show m
showConstant (Str str) = "\{show str}.to_string()"
showConstant (Ch c) = show c
showConstant (Db dbl) = show dbl
showConstant (PrT pty) = rustPrimType pty
showConstant WorldVal = "()"

rustConstant : Constant -> String
rustConstant c = "Rc::new(\{showConstant c}) as Rc<dyn Any>"

rustOp : {0 arity : Nat} -> PrimFn arity -> Vect arity String -> String
rustOp (Neg ty)      [x]       = "idris2_negate_"  ++  rustType ty ++ "(vec![" ++ x ++ "])"
rustOp StrLength     [x]       = "stringLength(vec![" ++ x ++ "])"
rustOp StrHead       [x]       = "head(vec![" ++ x ++ "])"
rustOp StrTail       [x]       = "tail(vec![" ++ x ++ "])"
rustOp StrReverse    [x]       = "reverse(vec![" ++ x ++ "])"
rustOp (Cast i o)    [x]       = "idris2_cast_" ++ (rustType i) ++ "_to_" ++ (rustType o) ++ "(vec![" ++ x ++ "])"
rustOp DoubleExp     [x]       = "exp(vec![" ++ x ++ "])"
rustOp DoubleLog     [x]       = "log(vec![" ++ x ++ "])"
rustOp DoublePow     [x, y]    = "pow(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp DoubleSin     [x]       = "sin(vec![" ++ x ++ "])"
rustOp DoubleCos     [x]       = "cos(vec![" ++ x ++ "])"
rustOp DoubleTan     [x]       = "tan(vec![" ++ x ++ "])"
rustOp DoubleASin    [x]       = "asin(vec![" ++ x ++ "])"
rustOp DoubleACos    [x]       = "acos(vec![" ++ x ++ "])"
rustOp DoubleATan    [x]       = "atan(vec![" ++ x ++ "])"
rustOp DoubleSqrt    [x]       = "sqrt(vec![" ++ x ++ "])"
rustOp DoubleFloor   [x]       = "floor(vec![" ++ x ++ "])"
rustOp DoubleCeiling [x]       = "ceil(vec![" ++ x ++ "])"
rustOp (Add ty)      [x, y]    = "idris2_add_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (Sub ty)      [x, y]    = "idris2_sub_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (Mul ty)      [x, y]    = "idris2_mul_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (Div ty)      [x, y]    = "idris2_div_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (Mod ty)      [x, y]    = "idris2_mod_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (ShiftL ty)   [x, y]    = "idris2_shiftl_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (ShiftR ty)   [x, y]    = "idris2_shiftr_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (BAnd ty)     [x, y]    = "idris2_and_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (BOr ty)      [x, y]    = "idris2_or_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (BXOr ty)     [x, y]    = "idris2_xor_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (LT ty)       [x, y]    = "idris2_lt_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (GT ty)       [x, y]    = "idris2_gt_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (EQ ty)       [x, y]    = "idris2_eq_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (LTE ty)      [x, y]    = "idris2_lte_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp (GTE ty)      [x, y]    = "idris2_gte_" ++ rustType ty ++ "(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp StrIndex      [x, i]    = "strIndex(vec![" ++ x ++ ", " ++ i ++ "])"
rustOp StrCons       [x, y]    = "strCons(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp StrAppend     [x, y]    = "strAppend(vec![" ++ x ++ ", " ++ y ++ "])"
rustOp StrSubstr     [x, y, z] = "strSubstr(vec![" ++ x ++ ", " ++ y  ++ ", " ++ z ++ "])"
rustOp BelieveMe     [_, _, x] = x
rustOp Crash         [_, msg]  = "idris2_crash(vec![" ++ msg ++ "])"
rustOp fn args = show fn ++ "(vec![" ++ (showSep ", " $ toList args) ++ "])"

rustStatementsFromANF : {auto a : Ref ArgCounter Nat} 
                      -> ANF 
                      -> Core String
rustStatementsFromANF (AV fc x) = pure $ "val_" ++ show x ++ ".clone()"
rustStatementsFromANF (AAppName fc _ n args) = do
  let argsStr = String.Extra.join ", " $ 
         map (\x => "val_" ++ show x ++ ".clone()") args 
  pure "\{rustName n}(\{argsStr})"

rustStatementsFromANF (AUnderApp fc name missing args) = do
  let argsStr = String.Extra.join ", " $ 
         map (\x => "val_" ++ show x ++ ".clone()") args
  let fnArgsLen = length args + missing
  let fnArgsStr = String.Extra.join ", " $ 
         map (\x => "Rc<dyn Any>") [1..fnArgsLen]
  let fnType = "fn(\{fnArgsStr}) -> Rc<dyn Any>"
  pure "Rc::new((\{show missing}, vec![\{argsStr}] as Vec<Rc<dyn Any>>, Rc::new(\{rustName name} as \{fnType}) as Rc<dyn Any>)) as Rc<dyn Any>"
rustStatementsFromANF (AApp fc _ closure arg) = pure $ "idris2_apply_closure(\{"&val_" ++ show closure}, \{rustAVar arg}.clone())"
rustStatementsFromANF (ALet fc var value body) = do 
  valueStr <- rustStatementsFromANF value
  let defStr = "let \{"val_v" ++ show var} = \{valueStr};"
  coreLift $ putStrLn $ defStr
  rustStatementsFromANF body
rustStatementsFromANF (ACon fc name coninfo tag args) = do
  let argsStr = String.Extra.join ", " $ 
    mapWithIndex (\ind, x => "\{"val_" ++ show x}.clone()") args 
  case tag of 
       Nothing => pure "Rc::new(IdrisMetaType::\{rustTypeName name}) as Rc<dyn Any>"
       Just tag' => pure "Rc::new((\{show tag'}, vec![\{argsStr}] as Vec<Rc<dyn Any>>)) as Rc<dyn Any>"
rustStatementsFromANF (AOp fc _ op args) = do 
  let argsStr = map (\x => "val_" ++ show x ++ ".clone()") args 
  let ret = rustOp op argsStr
  pure ret
rustStatementsFromANF (AExtPrim fc lazy n xs) = ?rustStatementsFromANF_rhs_7
rustStatementsFromANF (AConCase fc sc alts mDef) = do
  let sc' = "val_" ++ show sc
  tmpRetName <- getTmpVarName
  case isTagged alts of
       False => coreLift $ putStrLn $ "let \{tmpRetName} = match \{sc'}.downcast_ref::<IdrisMetaType>() {"
       True => coreLift $ putStrLn $ "let \{tmpRetName} = match \{sc'}.downcast_ref::<(i32, Vec<Rc<dyn Any>>)>() {"
  _ <- foldlC (\els, (MkAConAlt name coninfo tag args body) => do
      case tag of 
           Nothing => coreLift $ putStrLn $ "Some(IdrisMetaType::\{rustTypeName name}) => {"
           Just tag' => coreLift $ putStrLn $ "Some((\{show tag'}, args)) => {"

      _ <- foldlC (\k, arg => do
          coreLift $ putStrLn $ "let \{"val_v" ++ show arg} = args.get(\{show k}).unwrap().clone();"
          pure (S k) ) 0 args
      
      b <- rustStatementsFromANF body
      coreLift $ putStrLn $ b 
      coreLift $ putStrLn "}"
      pure "} else ") "" alts
  case mDef of
      Nothing => do
          coreLift $ putStrLn $ "_ => panic!(\"Reached unreachable state\")"
          pure ()
      Just body => do
          coreLift $ putStrLn $ "_ => {"
          b <- rustStatementsFromANF body
          coreLift $ putStrLn $ b 
          coreLift $ putStrLn $ "}"
          pure ()
  coreLift $ putStrLn $ "};"
  pure tmpRetName
rustStatementsFromANF (AConstCase fc sc alts mDef) = do
  let sc' = "val_" ++ show sc
  tmpRetName <- getTmpVarName
  case integer_switch alts of
      True => coreLift $ putStrLn $ "let \{tmpRetName} = match \{sc'}.downcast_ref::<i32>() {"
      False => case switch_type alts of
          Str x => coreLift $ putStrLn $ "let \{tmpRetName} = match \{sc'}.downcast_ref::<String>() {"
          Db  x => coreLift $ putStrLn $ "let \{tmpRetName} = match \{sc'}.downcast_ref::<f64>() {"
          x => throw $ InternalError "[refc] AConstCase : unsupported type. \{show fc} \{show x}"
  case integer_switch alts of
      True => do
          _ <- foldlC (\els, (MkAConstAlt c body) => do
              coreLift $ putStrLn $ "Some(\{show c}) => {"
              b <- rustStatementsFromANF body
              coreLift $ putStrLn $ b
              coreLift $ putStrLn "}"
              pure "} else ") "" alts
          pure ()

      False => do
          _ <- foldlC (\els, (MkAConstAlt c body) => do
              case c of
                  Str x => coreLift $ putStrLn $ "Some(ref s) if *s == \{show x} => {"
                  Db  x => coreLift $ putStrLn $ "Some(\{show x}) => {"
                  x => throw $ InternalError "[refc] AConstCase : unsupported type. \{show fc} \{show x}"
              b <- rustStatementsFromANF body
              coreLift $ putStrLn $ b
              coreLift $ putStrLn $ "}"
              pure "} else ") "" alts
          pure ()
  case mDef of
      Nothing => do
          coreLift $ putStrLn $ "_ => panic!(\"Reached unreachable state\")"
          pure ()
      Just body => do
          coreLift $ putStrLn $ "_ => {"
          b <- rustStatementsFromANF body
          coreLift $ putStrLn $ b 
          coreLift $ putStrLn $ "}"
          pure ()
  coreLift $ putStrLn $ "};"
  pure tmpRetName

rustStatementsFromANF (APrimVal fc cst) = pure $ "\{rustConstant cst}"
rustStatementsFromANF (AErased fc) = pure "Rc::new(()) as Rc<dyn Any>"
rustStatementsFromANF (ACrash fc str) = ?rustStatementsFromANF_rhs_12

termToRustNames : {vars: _} -> Term vars -> List String
termToRustNames (Local fc isLet idx p) = [show $ nameAt p]
termToRustNames (Ref fc nt name) = [show name]
termToRustNames (Meta fc n i ts) = ?termToRustNames_rhs_2
termToRustNames (Bind _ name (Pi _ _ _ ty) scope) = (termToRustNames ty) ++ (termToRustNames scope)
termToRustNames (Bind _ name _ scope) = ?termToRustNames_rhs_3
termToRustNames (App _ fn arg) = [show fn, show arg]
termToRustNames (As fc side as pat) = ?termToRustNames_rhs_5
termToRustNames (TDelayed fc lz t) = ?termToRustNames_rhs_6
termToRustNames (TDelay fc lz ty arg) = ?termToRustNames_rhs_7
termToRustNames (TForce fc lz t) = ?termToRustNames_rhs_8
termToRustNames (PrimVal fc c) = [show c]
termToRustNames (Erased fc why) = ?termToRustNames_rhs_10
termToRustNames (TType fc n) = [show n]

header : Core ()
header = do
    coreLift $ putStrLn $ """
        mod support;
        use core::panic;
        use support::*;
        """

footer : Core ()
footer = do
    coreLift $ putStrLn $ """
        // main function
        fn main() {
          __mainExpression_0();
        }
        """

createRustFunctions : {auto c : Ref Ctxt Defs} 
                    -> {auto a : Ref ArgCounter Nat}
                    -> {auto s : Ref Syn SyntaxInfo}
                    -> (Name, ANFDef)
                    -> Core ()
createRustFunctions (name, MkAFun args anf) = do 
  let argsStr = String.Extra.join ", " $ 
         map (\x => "val_v" ++ show x ++ ": Rc<dyn Any>") args
  let fn = "fn \{rustName name}(\{argsStr}) -> Rc<dyn Any> {"

  coreLift $ putStrLn $ fn

  -- let argsStrs = mapWithIndex (\ind, x => "let \{"val_v" ++ show x} = args.get(\{show ind}).unwrap().clone();") args
  --
  -- _ <- traverse (coreLift . putStrLn) argsStrs
  value <- rustStatementsFromANF anf
  coreLift $ putStrLn $ "return " ++ value ++ ";"
  coreLift $ putStrLn $ "}"
  pure ()
createRustFunctions (name, MkACon tag arity nt) = do
  pure ()
createRustFunctions (n, MkAForeign ccs fargs ret) = do
  pure ()
createRustFunctions (n, MkAError exp) = throw $ InternalError "Error with expression: \{show exp}"
-- not really total but this way this internal error does not contaminate everything else

generateRustSourceFile : {auto ctxt : Ref Ctxt Defs}
                       -> {auto s : Ref Syn SyntaxInfo}
                       -> List (Name, ANFDef)
                       -> Core ()
generateRustSourceFile defs = do
  _ <- newRef ArgCounter 0
  header
  traverse_ createRustFunctions defs
  footer

compile :
  Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
  (tmpDir : String) -> (execDir : String) ->
  ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile _ defs _ outputDir term outfile = do
  compData <- getCompileData False ANF term
  let defs = anf compData

  generateRustSourceFile defs
  pure Nothing

execute :
  Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
  (execDir : String) -> ClosedTerm -> Core ()
execute defs syn dir term = do coreLift $ putStrLn "Maybe in an hour."

rustCodegen : Codegen
rustCodegen = MkCG compile execute Nothing Nothing

main : IO ()
main = mainWithCodegens [("rust", rustCodegen)]
