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
import Compiler.LambdaLift
import Compiler.CompileExpr
import Compiler.VMCode
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

mapWithIndex : (Nat -> a -> b) -> List a -> List b
mapWithIndex f xs = go 0 xs
  where
    go : Nat -> List a -> List b
    go _ [] = []
    go i (x :: xs) = f i x :: go (i + 1) xs

showcCleanStringChar : Char -> String -> String
showcCleanStringChar ' ' = ("_" ++)
showcCleanStringChar '!' = ("_bang" ++)
showcCleanStringChar '"' = ("_quotation" ++)
showcCleanStringChar '#' = ("_number" ++)
showcCleanStringChar '$' = ("_dollar" ++)
showcCleanStringChar '%' = ("_percent" ++)
showcCleanStringChar '&' = ("_and" ++)
showcCleanStringChar '\'' = ("_tick" ++)
showcCleanStringChar '(' = ("_parenOpen" ++)
showcCleanStringChar ')' = ("_parenClose" ++)
showcCleanStringChar '*' = ("_star" ++)
showcCleanStringChar '+' = ("_plus" ++)
showcCleanStringChar ',' = ("_comma" ++)
showcCleanStringChar '-' = ("__" ++)
showcCleanStringChar '.' = ("_dot" ++)
showcCleanStringChar '/' = ("_slash" ++)
showcCleanStringChar ':' = ("_colon" ++)
showcCleanStringChar ';' = ("_semicolon" ++)
showcCleanStringChar '<' = ("_lt" ++)
showcCleanStringChar '=' = ("_eq" ++)
showcCleanStringChar '>' = ("_gt" ++)
showcCleanStringChar '?' = ("_question" ++)
showcCleanStringChar '@' = ("_at" ++)
showcCleanStringChar '[' = ("_bracketOpen" ++)
showcCleanStringChar '\\' = ("_backslash" ++)
showcCleanStringChar ']' = ("_bracketClose" ++)
showcCleanStringChar '^' = ("_hat" ++)
showcCleanStringChar '_' = ("_" ++)
showcCleanStringChar '`' = ("_backquote" ++)
showcCleanStringChar '{' = ("_braceOpen" ++)
showcCleanStringChar '|' = ("_or" ++)
showcCleanStringChar '}' = ("_braceClose" ++)
showcCleanStringChar '~' = ("_tilde" ++)
showcCleanStringChar c = strCons c

showcCleanString : List Char -> String -> String
showcCleanString [] = id
showcCleanString (c ::cs) = (showcCleanStringChar c) . showcCleanString cs

cCleanString : String -> String
cCleanString cs = showcCleanString (unpack cs) ""

getTmpVarName : {auto a : Ref ArgCounter Nat} -> Core String
getTmpVarName = pure $ "tmp_" ++ !(getNextCounter)

rustUserName : UserName -> String
rustUserName (Basic str) = str
rustUserName (Field str) = "." ++ str
rustUserName Underscore = "_"

rustName : Name -> String
rustName (NS ns n) = cCleanString (showNSWithSep "_" ns) ++ "_" ++ rustName n
rustName (UN n) = cCleanString $ rustUserName n
rustName (MN str i) = cCleanString str ++ "_" ++ (cCleanString $ show i)
rustName (PV n i) = "pat__" ++ rustName n
rustName (DN str n) = rustName n
rustName (Nested x n) = ?rustName_rhs_5
rustName (CaseBlock str i) = ?rustName_rhs_6
rustName (WithBlock str i) = ?rustName_rhs_7
rustName (Resolved i) = ?rustName_rhs_8

rustConstant : Constant -> String
rustConstant (I i) = "IdrisType::Int(\{show i})"
rustConstant (I8 i) = "IdrisType::Int(\{show i})"
rustConstant (I16 i) = "IdrisType::Int(\{show i})"
rustConstant (I32 i) = "IdrisType::Int(\{show i})"
rustConstant (I64 i) = "IdrisType::Int(\{show i})"
rustConstant (BI i) = "IdrisType::Int(\{show i})"
rustConstant (B8 m) = "IdrisType::Int(\{show m})"
rustConstant (B16 m) = "IdrisType::Int(\{show m})"
rustConstant (B32 m) = "IdrisType::Int(\{show m})"
rustConstant (B64 m) = "IdrisType::Int(\{show m})"
rustConstant (Str str) = "IdrisType::String(\{show str})"
rustConstant (Ch c) = "IdrisType::Char(\{show c})"
rustConstant (Db dbl) = "IdrisType::Double(\{show dbl})"
rustConstant (PrT pty) = "TODO: resolve rustConstant PrT, got value: " ++ show pty
rustConstant WorldVal = "TODO: resolve rustConstant WorldVal"

varName : AVar -> String
varName (ALocal i) = "var_" ++ (show i)
varName (ANull)    = "NULL"

cPrimType : PrimType -> String
cPrimType IntType = "Int64"
cPrimType Int8Type = "Int8"
cPrimType Int16Type = "Int16"
cPrimType Int32Type = "Int32"
cPrimType Int64Type = "Int64"
cPrimType IntegerType = "Integer"
cPrimType Bits8Type = "Bits8"
cPrimType Bits16Type = "Bits16"
cPrimType Bits32Type = "Bits32"
cPrimType Bits64Type = "Bits64"
cPrimType StringType = "string"
cPrimType CharType = "Char"
cPrimType DoubleType = "Double"
cPrimType WorldType = "void"

rustOp : {0 arity : Nat} -> PrimFn arity -> Vect arity String -> String
rustOp (Neg ty)      [x]       = "idris2_negate_"  ++  cPrimType ty ++ "(" ++ x ++ ")"
rustOp StrLength     [x]       = "stringLength(" ++ x ++ ")"
rustOp StrHead       [x]       = "head(" ++ x ++ ")"
rustOp StrTail       [x]       = "tail(" ++ x ++ ")"
rustOp StrReverse    [x]       = "reverse(" ++ x ++ ")"
rustOp (Cast i o)    [x]       = "idris2_cast_" ++ (cPrimType i) ++ "_to_" ++ (cPrimType o) ++ "(" ++ x ++ ")"
rustOp DoubleExp     [x]       = "idris2_mkDouble(exp(idris2_vp_to_Double(" ++ x ++ ")))"
rustOp DoubleLog     [x]       = "idris2_mkDouble(log(idris2_vp_to_Double(" ++ x ++ ")))"
rustOp DoublePow     [x, y]    = "idris2_mkDouble(pow(idris2_vp_to_Double(" ++ x ++ "), idris2_vp_to_Double(" ++ y ++ ")))"
rustOp DoubleSin     [x]       = "idris2_mkDouble(sin(idris2_vp_to_Double(" ++ x ++ ")))"
rustOp DoubleCos     [x]       = "idris2_mkDouble(cos(idris2_vp_to_Double(" ++ x ++ ")))"
rustOp DoubleTan     [x]       = "idris2_mkDouble(tan(idris2_vp_to_Double(" ++ x ++ ")))"
rustOp DoubleASin    [x]       = "idris2_mkDouble(asin(idris2_vp_to_Double(" ++ x ++ ")))"
rustOp DoubleACos    [x]       = "idris2_mkDouble(acos(idris2_vp_to_Double(" ++ x ++ ")))"
rustOp DoubleATan    [x]       = "idris2_mkDouble(atan(idris2_vp_to_Double(" ++ x ++ ")))"
rustOp DoubleSqrt    [x]       = "idris2_mkDouble(sqrt(idris2_vp_to_Double(" ++ x ++ ")))"
rustOp DoubleFloor   [x]       = "idris2_mkDouble(floor(idris2_vp_to_Double(" ++ x ++ ")))"
rustOp DoubleCeiling [x]       = "idris2_mkDouble(ceil(idris2_vp_to_Double(" ++ x ++ ")))"
rustOp (Add ty)      [x, y]    = "idris2_add_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (Sub ty)      [x, y]    = "idris2_sub_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (Mul ty)      [x, y]    = "idris2_mul_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (Div ty)      [x, y]    = "idris2_div_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (Mod ty)      [x, y]    = "idris2_mod_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (ShiftL ty)   [x, y]    = "idris2_shiftl_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (ShiftR ty)   [x, y]    = "idris2_shiftr_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (BAnd ty)     [x, y]    = "idris2_and_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (BOr ty)      [x, y]    = "idris2_or_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (BXOr ty)     [x, y]    = "idris2_xor_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (LT ty)       [x, y]    = "idris2_lt_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (GT ty)       [x, y]    = "idris2_gt_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (EQ ty)       [x, y]    = "idris2_eq_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (LTE ty)      [x, y]    = "idris2_lte_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp (GTE ty)      [x, y]    = "idris2_gte_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
rustOp StrIndex      [x, i]    = "strIndex(" ++ x ++ ", " ++ i ++ ")"
rustOp StrCons       [x, y]    = "strCons(" ++ x ++ ", " ++ y ++ ")"
rustOp StrAppend     [x, y]    = "strAppend(" ++ x ++ ", " ++ y ++ ")"
rustOp StrSubstr     [x, y, z] = "strSubstr(" ++ x ++ ", " ++ y  ++ ", " ++ z ++ ")"
rustOp BelieveMe     [_, _, x] = "idris2_newReference(" ++ x ++ ")"
rustOp Crash         [_, msg]  = "idris2_crash(" ++ msg ++ ");"
rustOp fn args = show fn ++ "(" ++ (showSep ", " $ toList args) ++ ")"

rustStatementsFromANF : {auto a : Ref ArgCounter Nat} 
                      -> ANF 
                      -> Core String
rustStatementsFromANF (AV fc x) = pure $ "val_" ++ show x
rustStatementsFromANF (AAppName fc _ n args) = do
  let argsStr = String.Extra.join ", " $ 
         map (\x => "&val_" ++ show x) args 
  pure "\{rustName n}(\{argsStr})"

rustStatementsFromANF (AUnderApp fc name missing args) = do
  tmpArgs <- replicateC missing getTmpVarName
  let tmpArgsStr = String.Extra.join ", " $
         map ("&"++) tmpArgs
  let argsStr = String.Extra.join ", " $ 
         (map (\x => "&val_" ++ show x) args) ++ tmpArgs
  pure "|\{tmpArgsStr}| \{rustName name}(\{argsStr})"
rustStatementsFromANF (AApp fc _ closure arg) = pure "app"
rustStatementsFromANF (ALet fc var value body) = do 
  valueStr <- rustStatementsFromANF value
  let defStr = "let \{"val_v" ++ show var} = \{valueStr};"
  coreLift $ putStrLn $ defStr
  rustStatementsFromANF body
rustStatementsFromANF (ACon fc name coninfo tag args) = do
        if coninfo == NIL || coninfo == NOTHING || coninfo == ZERO || coninfo == UNIT
            then pure "Box::new(()) as Box<dyn Any> /* \{show name} \{show coninfo} */"
            else do
                let argsStr = String.Extra.join ",\n" $ 
                    mapWithIndex (\ind, x => "v\{show ind}: \{"&val_" ++ show x}") args 
                pure "Box::new(\{rustName name} {\n\{argsStr}\n}) as Box<dyn Any>"
rustStatementsFromANF (AOp fc _ op args) = do 
  let argsStr = map (\x => "&val_" ++ show x) args 
  let ret = rustOp op argsStr
  pure ret
rustStatementsFromANF (AExtPrim fc lazy n xs) = ?rustStatementsFromANF_rhs_7
rustStatementsFromANF (AConCase fc sc alts mDef) = do
  let sc' = "val_" ++ show sc
  tmpCastName <- getTmpVarName
  tmpRetName <- getTmpVarName
  coreLift $ putStr $ "let \{tmpRetName} = "
  _ <- foldlC (\els, (MkAConAlt name coninfo tag args body) => do
      let erased = coninfo == NIL || coninfo == NOTHING || coninfo == ZERO || coninfo == UNIT
      if erased then coreLift $ putStrLn $ "\{els}if () == \{sc'} /* \{show name} \{show coninfo} ERASED */ {"
          else coreLift $ putStrLn $ "\{els}if let Ok(\{tmpCastName}) = \{sc'}.downcast::<\{rustName name}>() /* \{show name} \{show coninfo} */ {"

      _ <- foldlC (\k, arg => do
          coreLift $ putStrLn $ "let \{"&val_v" ++ show arg} = \{tmpCastName}.v\{show k};"
          pure (S k) ) 0 args
      
      b <- rustStatementsFromANF body
      coreLift $ putStrLn $ b
      pure "} else ") "" alts
  case mDef of
      Nothing => do
          coreLift $ putStrLn $ "} else {\npanic!(\"Reached unreachable state\");"
          pure ()
      Just body => do
          coreLift $ putStrLn $ "} else (here) {"
          pure ()
  coreLift $ putStrLn $ "};"
  pure tmpRetName
rustStatementsFromANF (AConstCase fc sc alts def) = do
  let sc' = "val_" ++ show sc
  tmpCastName <- getTmpVarName
  tmpRetName <- getTmpVarName
  case integer_switch alts of
      True => do
          coreLift $ putStrLn $ "let \{tmpCastName} = \{sc'}.downcast_ref::<i64>().unwrap();"
          coreLift $ putStr $ "let \{tmpRetName} = "
          _ <- foldlC (\els, (MkAConstAlt c body) => do
              coreLift $ putStrLn $ "\{els}if *\{tmpCastName} == \{show c} {"
              b <- rustStatementsFromANF body
              coreLift $ putStrLn $ b
              pure "} else ") "" alts
          pure ()

      False => do
          _ <- foldlC (\els, (MkAConstAlt c body) => do
              case c of
                  Str x => coreLift $ putStrLn $ "\{els}if (! strcmp(\{show x}, ((Value_String *)\{sc'})->str)) {"
                  Db  x => coreLift $ putStrLn $ "\{els}if (((Value_Double *)\{sc'})->d == \{show x}) {"
                  x => throw $ InternalError "[refc] AConstCase : unsupported type. \{show fc} \{show x}"
              pure "} else ") "" alts
          pure ()

  case def of
      Nothing => do
          coreLift $ putStrLn $ "} else {\npanic!(\"Reached unreachable state\");"
          pure ()
      Just body => do
          coreLift $ putStrLn $ "} else {"
          b <- rustStatementsFromANF body
          coreLift $ putStrLn $ b
  coreLift $ putStrLn $ "};"
  pure tmpRetName

rustStatementsFromANF (APrimVal fc cst) = pure $ "\{rustConstant cst}"
rustStatementsFromANF (AErased fc) = ?rustStatementsFromANF_rhs_11
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

createRustFunctions : {auto c : Ref Ctxt Defs} 
                    -> {auto a : Ref ArgCounter Nat}
                    -> {auto s : Ref Syn SyntaxInfo}
                    -> (Name, ANFDef)
                    -> Core ()
createRustFunctions (name, MkAFun args anf) = do 
  -- defs <- get Ctxt
  -- Just globalDef <- lookupCtxtExact name (gamma defs)
  --   | Nothing => do
  --     coreLift $ putStrLn $ "Name \{rustName name} not found in the context"
  --     pure ()
  -- type <- normaliseHoles defs [] globalDef.type
  -- type <- toFullNames type
  -- let names = termToRustNames type
  --
  -- coreLift $ putStrLn $ rustName name 
  -- coreLift $ putStrLn $ show names
  -- coreLift $ putStrLn $ show type
  -- coreLift $ putStrLn $ show names

  -- mty <- do Just gdef <- lookupCtxtExact n (gamma defs)
  --             | Nothing => pure Nothing
  --           let UN _ = dropNS n
  --             | _ => pure Nothing
  --           coreLift $ putStrLn $ show $ gdef.type
  --           ty <- toFullNames gdef.type
  --           pure (Just ty)
      -- coreLift $ putStrLn $ rustName n 
      -- pure ()

  -- coreLift $ putStrLn $ show $ gdef.type
  let argsStr = String.Extra.join ", " $ 
         map (\x => "val_v" ++ show x ++ ": &IdrisType") args 
  let fn = "fn \{rustName name}(\{argsStr}) -> IdrisType {"

  coreLift $ putStrLn $ fn
  value <- rustStatementsFromANF anf
  coreLift $ putStrLn $ "return " ++ value ++ ";"
  coreLift $ putStrLn $ "}"
  pure ()
createRustFunctions (name, MkACon tag arity nt) = do
  defs <- get Ctxt
  mty <- do Just gdef <- lookupCtxtExact name (gamma defs)
              | Nothing => pure Nothing
            let UN _ = dropNS name
              | _ => pure Nothing
            coreLift $ putStrLn $ show $ gdef.type
            ty <- toFullNames gdef.type
            pure (Just ty)
  coreLift $ putStrLn $ show $ mty
  coreLift $ putStrLn $ "struct \{rustName name} {"
  _ <- traverse (\i => do
            coreLift $ putStrLn $ "v\{show i}: &IdrisType,"
            pure ()) $ rangeNat arity
  coreLift $ putStrLn $ "}"
  pure ()
createRustFunctions (n, MkAForeign ccs fargs x) = do
  defs <- get Ctxt
  Just gdef <- lookupCtxtExact n (gamma defs)
    | Nothing => do
      coreLift $ putStrLn $ rustName n 
      pure ()
  let UN _ = dropNS n
    | _ => do
      coreLift $ putStrLn $ "Name \{rustName n} not found in the context"
      pure ()

  pure ()
  -- coreLift $ putStrLn $ "MkAForeign not implemented yet"
  pure ()
createRustFunctions (n, MkAError x) = do
  defs <- get Ctxt
  Just gdef <- lookupCtxtExact n (gamma defs)
    | Nothing => do
      coreLift $ putStrLn $ rustName n 
      pure ()
  let UN _ = dropNS n
    | _ => do
      coreLift $ putStrLn $ "Name \{rustName n} not found in the context"
      pure ()

  pure ()
  -- coreLift $ putStrLn $ "MkAError not implemented yet"
  pure ()

generateRustSourceFile : {auto ctxt : Ref Ctxt Defs}
                       -> {auto s : Ref Syn SyntaxInfo}
                       -> List (Name, ANFDef)
                       -> Core ()
generateRustSourceFile defs = do
  _ <- newRef ArgCounter 0
  traverse_ createRustFunctions defs


compile :
  Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
  (tmpDir : String) -> (execDir : String) ->
  ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile syn defs tmp dir term file = do 
  compData <- getCompileData False ANF term
  let defs = anf compData
  let ndefs = namedDefs compData
  let ldefs = lambdaLifted compData
  -- coreLift $ putStrLn $ show defs
  -- coreLift $ putStrLn $ show ldefs
  -- coreLift $ putStrLn $ show ndefs
  -- coreLift $ putStrLn $ show $ vmcode compData

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
