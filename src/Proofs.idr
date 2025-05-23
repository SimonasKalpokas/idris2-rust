module Proofs

import Core.Context

import Data.Vect
import Libraries.Data.NameMap

data PrimFun : Nat -> Type where
    Add : PrimFun 2
    Sub : PrimFun 2
    Mul : PrimFun 2
    Div : PrimFun 2

data Var : Type where
    VLocal : Nat -> Var
    VNull : Var

data ValSrc : Type where
    VSInt : Int -> ValSrc
    VSChar : Char -> ValSrc
    VSString : String -> ValSrc
    VSDouble : Double -> ValSrc

data ValTgt : Type where
    VTInt : Int -> ValTgt
    VTChar : Char -> ValTgt
    VTString : String -> ValTgt
    VTDbl : Double -> ValTgt

data ValEq : ValSrc -> ValTgt -> Type where
    EqInt : (n : Int) -> ValEq (VSInt n) (VTInt n)
    EqChar : (c : Char) -> ValEq (VSChar c) (VTChar c)
    EqString : (s : String) -> ValEq (VSString s) (VTString s)
    EqDbl : (d : Double) -> ValEq (VSDouble d) (VTDbl d)

valEqRefl2 : ValEq (VSInt v) (VTInt v') -> v = v'
valEqRefl2 (EqInt n) = Refl

data ValEqList : List ValSrc -> List ValTgt -> Type where
    ValEqNil : ValEqList [] []
    ValEqCons : ValEq v v' -> ValEqList vs1 vs2
                -> ValEqList (v :: vs1) (v' :: vs2)

compileVal : ValSrc -> ValTgt
compileVal (VSInt i) = VTInt i
compileVal (VSChar c) = VTChar c
compileVal (VSString s) = VTString s
compileVal (VSDouble d) = VTDbl d

valEqRefl : { v: ValSrc } -> ValEq v (compileVal v)
valEqRefl { v = VSInt n } = EqInt n
valEqRefl { v = VSChar c } = EqChar c
valEqRefl { v = VSString s } = EqString s
valEqRefl { v = VSDouble d } = EqDbl d

data TinyANF : Type where
    AV : Var -> TinyANF
    APrimVal : ValSrc -> TinyANF
    ALet : Nat -> TinyANF -> TinyANF -> TinyANF
    AOp: (0 arity : Nat) -> PrimFun arity -> Vect arity Var -> TinyANF
    AAppName : Name -> List Var -> TinyANF

data RustIR : Type where
    RV : Var -> RustIR
    RPrimVal : ValTgt -> RustIR
    RLet : Nat -> RustIR -> RustIR -> RustIR
    ROp: (0 arity : Nat) -> PrimFun arity -> Vect arity Var -> RustIR
    RAppName : Name -> List Var -> RustIR

data CompileExpr : TinyANF -> RustIR -> Type where
    CEVal : CompileExpr (AV x) (RV x)
    CEPrimVal : CompileExpr (APrimVal i) (RPrimVal (compileVal i))
    CELet : CompileExpr e1 e1'
              -> CompileExpr e2 e2'
              -> CompileExpr (ALet v e1 e2) (RLet v e1' e2')
    CEOp : {0 arity : _ } -> { fun : PrimFun arity } -> { args : Vect arity Var} 
        -> CompileExpr (AOp arity fun args) (ROp arity fun args)
    CEAppName : CompileExpr (AAppName f args) (RAppName f args)

data EnvVal : Type -> Type where
    EVVal : t -> EnvVal t
    EVNull : EnvVal t

data EnvValEq : EnvVal t -> EnvVal t' -> Type where
    EVEq : ValEq v v' -> EnvValEq (EVVal v) (EVVal v')
    EVNullEq : EnvValEq EVNull EVNull

EnvTiny : Type
EnvTiny = List (EnvVal ValSrc)

EnvTgt : Type
EnvTgt = List (EnvVal ValTgt)

data CompileEnv : EnvTiny -> EnvTgt -> Type where
    CEEmpty : CompileEnv [] []
    CECons : EnvValEq v v' -> CompileEnv env1 env2
              -> CompileEnv (v :: env1) (v' :: env2)

FunEnvSrc : Type
FunEnvSrc = List (Name, List Nat, TinyANF)

FunEnvTgt : Type
FunEnvTgt = List (Name, List Nat, RustIR)

data CompileFEnv : FunEnvSrc -> FunEnvTgt -> Type where
    CFEEmpty : CompileFEnv [] []
    CFECons : {f:_} -> CompileExpr body body'
                -> CompileFEnv restSrc restTgt
                -> CompileFEnv ((f, inArgs, body) :: restSrc)
                               ((f, inArgs, body') :: restTgt)

findSrc : (f : Name) -> FunEnvSrc -> Maybe (List Nat, TinyANF)
findSrc _ [] = Nothing
findSrc f ((f', inArgs, body) :: rest) with (nameEq f f')
    findSrc f ((f, inArgs, body) :: rest) | (Just Refl) = Just (inArgs, body)
    findSrc f ((f', inArgs, body) :: rest) | (Nothing) = findSrc f rest

findTgt : (f : Name) -> FunEnvTgt -> Maybe (List Nat, RustIR)
findTgt _ [] = Nothing
findTgt f ((f', inArgs, body) :: rest) with (nameEq f f')
    findTgt f ((f, inArgs, body) :: rest) | (Just Refl) = Just (inArgs, body)
    findTgt f ((f', inArgs, body) :: rest) | (Nothing) = findTgt f rest

fenvRel : { f : Name } -> { fEnv : FunEnvSrc } -> { fEnv' : FunEnvTgt } -> { body : _ } -> { body' : _ }
    -> CompileFEnv fEnv fEnv' 
    -> findSrc f fEnv = Just (inArgs, body)
    -> findTgt f fEnv' = Just (inArgs', body')
    -> inArgs = inArgs'
fenvRel {f} (CFECons {f=f'} ce ce') pf pf' with (nameEq f f')
    fenvRel {f} (CFECons {f} ce ce') Refl Refl | (Just Refl) = Refl
    fenvRel (CFECons ce ce') pf pf' | (Nothing) = fenvRel ce' pf pf'

fenvRel2 : { f : Name } -> { fEnv : FunEnvSrc } -> { fEnv' : FunEnvTgt } -> { inArgs : List Nat } -> { inArgs' : List Nat }
    -> CompileFEnv fEnv fEnv' 
    -> findSrc f fEnv = Just (inArgs, body)
    -> findTgt f fEnv' = Just (inArgs', body')
    -> CompileExpr body body'
fenvRel2 {f} (CFECons {f=f'} ce ce') pf pf' with (nameEq f f')
    fenvRel2 {f} (CFECons {f} ce ce') Refl Refl | (Just Refl) = ce
    fenvRel2 (CFECons ce ce') pf pf' | (Nothing) = fenvRel2 ce' pf pf'


index : Var -> List a -> Maybe a
index _ [] = Nothing
index (VLocal Z) (x :: xs) = Just x
index (VLocal (S i)) (x :: xs) = index (VLocal i) xs
index VNull _ = Nothing

reorderArgs: List Nat -> List a -> List a
reorderArgs [] _ = []
reorderArgs slots args = 
    map (\(_, x) => x) $
    sortBy (\(x, _), (y, _) => compare x y) $
    zip slots args

indexMany : List Var -> List a -> Maybe (List a)
indexMany [] _ = Just []
indexMany (x :: xs) env with (index x env)
    indexMany (x :: xs) env | (Nothing) = Nothing
    indexMany (x :: xs) env | (Just v) with (indexMany xs env)
        indexMany (x :: xs) env | (Just v) | (Just vs) = Just (v :: vs)
        indexMany (x :: xs) env | (Just v) | (Nothing) = Nothing
-- indexMany (x :: xs) env = 
--     case index x env of
--         Just v => case indexMany xs env of
--             Just vs => Just (v :: vs)
--             Nothing => Nothing
--         Nothing => Nothing

data IsVar : a -> Var -> List (EnvVal a) -> Type where
     First : IsVar n (VLocal Z) ((EVVal n) :: ns)
     Later : IsVar n (VLocal i) ns -> IsVar n (VLocal (S i)) (m :: ns)

data AreVars : List (EnvVal a) -> List Var -> List (EnvVal a)-> Type where
    AVNil : AreVars [] [] env
    AVCons : IsVar v (VLocal x) env -> AreVars vs xs env -> AreVars ((EVVal v) :: vs) ((VLocal x) :: xs) env
    AVConsNull : AreVars vs xs env -> AreVars (EVNull :: vs) (VNull :: xs) env

data IsIntSrc : Int -> Var -> EnvTiny -> Type where
    IISFirst : IsIntSrc n (VLocal Z) ((EVVal (VSInt n)) :: env)
    IISLater : IsIntSrc n (VLocal i) env -> IsIntSrc n (VLocal (S i)) (m :: env)

data AreIntsSrc : Vect n Int -> Vect n Var -> EnvTiny -> Type where
    AISNil : AreIntsSrc Nil Nil env
    AISCons : IsIntSrc v (VLocal x) env -> AreIntsSrc vs xs env -> AreIntsSrc (v::vs) ((VLocal x)::xs) env

data IsIntTgt : Int -> Var -> EnvTgt -> Type where
    IITFirst : IsIntTgt n (VLocal Z) ((EVVal (VTInt n)) :: env)
    IITLater : IsIntTgt n (VLocal i) env -> IsIntTgt n (VLocal (S i)) (m :: env)

data AreIntsTgt : Vect n Int -> Vect n Var -> EnvTgt -> Type where
    AITNil : AreIntsTgt Nil Nil env
    AITCons : IsIntTgt v (VLocal x) env -> AreIntsTgt vs xs env -> AreIntsTgt (v::vs) ((VLocal x)::xs) env

data Elem : (x: Nat) -> (as : List a) -> a -> Type where
    EHead : Elem Z (a :: as) a
    ETail : Elem x as m -> Elem (S x) (a :: as) m

data ReorderRel : (xs: List Nat) -> (as: List a) -> List a -> Type where
    RNil : ReorderRel [] xs []
    RCons : Elem x as a
              -> ReorderRel xs as rest
              -> ReorderRel (x :: xs) as (a :: rest)

data EvalPrimFun : PrimFun n -> Vect n Int -> Int -> Type where
    EAdd : EvalPrimFun Add (x :: y :: Nil) (x + y)
    ESub : EvalPrimFun Sub (x :: y :: Nil) (x - y)
    EMul : EvalPrimFun Mul (x :: y :: Nil) (x * y)
    EDiv : EvalPrimFun Div (x :: y :: Nil) (div x y)

data EvalTiny : FunEnvSrc -> TinyANF -> EnvTiny -> ValSrc -> Type where
    ESV : (0 prf : IsVar v x env) -> EvalTiny funEnv (AV x) env v
    ESPrimVal : EvalTiny funEnv (APrimVal i) env i
    ESLet : {v1 : _ } -> EvalTiny funEnv e1 env v1
              -> EvalTiny funEnv e2 ((EVVal v1) :: env) v2
              -> EvalTiny funEnv (ALet v e1 e2) env v2
    ESOp : {arity: _} -> { f : PrimFun arity } -> { args : Vect arity Var } -> { argVals : Vect arity Int }
                -> AreIntsSrc argVals args env
                -> EvalPrimFun f argVals v
                -> EvalTiny funEnv (AOp arity f args) env (VSInt v)
    ESAppName : { body : TinyANF } -> { inArgs : List Nat } -> { args' : _ } -> { newEnv : _ }
                -> findSrc f funEnv = Just (inArgs, body)
                -> AreVars args' args env
                -> ReorderRel inArgs args' newEnv
                -> EvalTiny funEnv body newEnv v
                -> EvalTiny funEnv (AAppName f args) env v

data EvalTgt : FunEnvTgt -> RustIR -> EnvTgt -> ValTgt -> Type where
    ETV : (0 prf : IsVar v x env) -> EvalTgt funEnv (RV x) env v
    ETPrimVal : EvalTgt funEnv (RPrimVal i) env i
    ETLet : {v1 : _} -> EvalTgt funEnv e1 env v1
              -> EvalTgt funEnv e2 ((EVVal v1) :: env) v2
              -> EvalTgt funEnv (RLet v e1 e2) env v2
    ETOp : {0 arity: _} -> { f : PrimFun arity } -> { args : Vect arity Var } -> { argVals : Vect arity Int }
                -> AreIntsTgt argVals args env
                -> EvalPrimFun f argVals v
                -> EvalTgt funEnv (ROp arity f args) env (VTInt v)
    ETAppName : { body : RustIR } -> { inArgs : List Nat } -> { args' : _ } -> { newEnv : _ }
                -> findTgt f funEnv = Just (inArgs, body)
                -> AreVars args' args env
                -> ReorderRel inArgs args' newEnv
                -> EvalTgt funEnv body newEnv v
                -> EvalTgt funEnv (RAppName f args) env v

-- Bijection 

compileExpr : TinyANF -> RustIR
compileExpr (AV x) = RV x
compileExpr (APrimVal i) = RPrimVal (compileVal i)
compileExpr (ALet v e1 e2) = RLet v (compileExpr e1) (compileExpr e2)
compileExpr (AOp arity fun args) = ROp arity fun args
compileExpr (AAppName f args) = RAppName f args

decompileVal : ValTgt -> ValSrc
decompileVal (VTInt i) = VSInt i
decompileVal (VTChar c) = VSChar c
decompileVal (VTString s) = VSString s
decompileVal (VTDbl d) = VSDouble d

decompileExpr : RustIR -> TinyANF
decompileExpr (RV x) = AV x
decompileExpr (RPrimVal i) = APrimVal (decompileVal i)
decompileExpr (RLet v e1 e2) = ALet v (decompileExpr e1) (decompileExpr e2)
decompileExpr (ROp arity fun args) = AOp arity fun args
decompileExpr (RAppName f args) = AAppName f args

injectionVal : ( s : ValSrc) -> decompileVal (compileVal s) = s
injectionVal (VSInt i) = Refl
injectionVal (VSChar c) = Refl
injectionVal (VSString s) = Refl
injectionVal (VSDouble d) = Refl

injection : ( s: TinyANF) -> decompileExpr (compileExpr s) = s
injection (AV x) = Refl
injection (AOp arity fun args) = Refl
injection (ALet v e1 e2) = 
    let e1' = injection e1
        e2' = injection e2
    in rewrite e1' in rewrite e2' in Refl
injection (AAppName f args) = Refl
injection (APrimVal i) = rewrite injectionVal i in Refl

surjectionVal : (s : ValTgt) -> compileVal (decompileVal s) = s
surjectionVal (VTInt i) = Refl
surjectionVal (VTChar c) = Refl
surjectionVal (VTString s) = Refl
surjectionVal (VTDbl d) = Refl

surjection : (s : RustIR) -> compileExpr (decompileExpr s) = s
surjection (RV x) = Refl
surjection (RPrimVal i) = rewrite surjectionVal i in Refl
surjection (RLet v e1 e2) = 
    let e1' = surjection e1
        e2' = surjection e2
    in rewrite e1' in rewrite e2' in Refl
surjection (ROp arity fun args) = Refl
surjection (RAppName f args) = Refl

-- Semantic preservation theorem 

lookupRel : (x: Var) -> 
    (env: EnvTiny) -> 
    (env': EnvTgt) -> 
    CompileEnv env env' -> 
    (0 prf : IsVar v x env) ->
    (0 prf' : IsVar v' x env') ->
    ValEq v v'
lookupRel (VLocal Z) ((EVVal v) :: vs) ((EVVal v') :: vs') (CECons (EVEq pf) ce) First First = pf
lookupRel (VLocal (S i)) (vt :: vs) (vt' :: vs') (CECons vEq ce) (Later l) (Later l') = lookupRel (VLocal i) vs vs' ce l l'
lookupRel VNull [] [] CEEmpty _ _ impossible

valEqListPreservation : ( args : List Var )
    -> ( env : EnvTiny )
    -> ( env' : EnvTgt )
    -> CompileEnv env env'
    -> AreVars argVals args env
    -> AreVars argVals' args env'
    -> CompileEnv argVals argVals'
valEqListPreservation [] _ _ _ AVNil AVNil = CEEmpty
valEqListPreservation ((VLocal x) :: xs) env env' ce (AVCons prf rest) (AVCons prf' rest') =
    let pf = lookupRel (VLocal x) env env' ce prf prf'
        pfRest = valEqListPreservation xs env env' ce rest rest'
    in CECons (EVEq pf) pfRest
valEqListPreservation (VNull :: xs) env env' ce (AVConsNull rest) (AVConsNull rest') =
    let pfRest = valEqListPreservation xs env env' ce rest rest'
    in CECons EVNullEq pfRest

lookupVecRel : (x: Var) -> 
    (env: EnvTiny) -> 
    (env': EnvTgt) -> 
    CompileEnv env env' -> 
    (prf : IsIntSrc v x env) ->
    (0 prf' : IsIntTgt v' x env') ->
    ValEq (VSInt v) (VTInt v')
lookupVecRel (VLocal Z) ((EVVal (VSInt v)) :: vs) ((EVVal (VTInt v')) :: vs') (CECons (EVEq pf) ce) IISFirst IITFirst = pf
lookupVecRel (VLocal (S i)) (vt :: vs) (vt' :: vs') (CECons vEq ce) (IISLater l) (IITLater l') = lookupVecRel (VLocal i) vs vs' ce l l'
lookupVecRel VNull [] [] CEEmpty _ _ impossible

valEqVecPreservation : {n : Nat} -> {argVals : Vect n Int} -> {argVals' : Vect n Int}
    -> ( args : Vect n Var )
    -> ( env : EnvTiny )
    -> ( env' : EnvTgt )
    -> CompileEnv env env'
    -> AreIntsSrc argVals args env
    -> AreIntsTgt argVals' args env'
    -> argVals = argVals'
valEqVecPreservation Nil _ _ _ AISNil AITNil = Refl
valEqVecPreservation ((VLocal x) :: xs) env env' ce (AISCons prf rest) (AITCons prf' rest') =
    let pf = lookupVecRel (VLocal x) env env' ce prf prf'
        pfRest = valEqVecPreservation xs env env' ce rest rest'
    in rewrite valEqRefl2 pf in rewrite pfRest in Refl

data AreInBounds : List Nat -> List a -> Type where
    AIBNil : AreInBounds [] xs
    AIBCons : InBounds k xs -> AreInBounds ks xs -> AreInBounds (k :: ks) xs

elemRel : CompileEnv env env' 
    -> Elem n env a 
    -> Elem n env' a'
    -> EnvValEq a a'
elemRel (CECons vEq _) (EHead) (EHead) = vEq
elemRel (CECons _ ce) (ETail prf) (ETail prf') = elemRel ce prf prf'

compileArgsPreserve : { env : EnvTiny } -> { env' : EnvTgt }
    -> {inArgs : List Nat}
    -> inArgs = inArgs'
    -> CompileEnv env env'
    -> ReorderRel inArgs env envSrc
    -> ReorderRel inArgs' env' envSrc'
    -> CompileEnv envSrc envSrc'
compileArgsPreserve {inArgs=[]} Refl ce RNil RNil = CEEmpty
compileArgsPreserve {inArgs=(x :: xs)} Refl ce (RCons elem rest) (RCons elem' rest') =
    let pf = elemRel ce elem elem'
        pfRest = compileArgsPreserve Refl ce rest rest'
    in CECons pf pfRest

valEqPrimFun : {f : PrimFun n} -> {args : Vect n Int} -> {v : Int}
    -> {pf: args = args'}
    -> EvalPrimFun f args v
    -> EvalPrimFun f args' v'
    -> ValEq (VSInt v) (VTInt v')
valEqPrimFun {v=x+y} {args=(x::y::Nil)} {pf=Refl} EAdd EAdd = EqInt (x+y)
valEqPrimFun {v=x-y} {args=(x::y::Nil)} {pf=Refl} ESub ESub = EqInt (x-y)
valEqPrimFun {v=x*y} {args=(x::y::Nil)} {pf=Refl} EMul EMul = EqInt (x*y)
valEqPrimFun {v=div x y} {args=(x::y::Nil)} {pf=Refl} EDiv EDiv = EqInt (div x y)

theorem_semantic_preservation :
    {e : TinyANF} ->
    {eTgt : RustIR} ->
    { fEnv : FunEnvSrc } ->
    { fEnvTgt : FunEnvTgt } ->
    { env : EnvTiny } ->
    { envTgt : EnvTgt } ->
    { v : ValSrc } ->
    { v' : ValTgt } ->
    EvalTiny fEnv e env v ->
    CompileEnv env envTgt ->
    CompileFEnv fEnv fEnvTgt ->
    CompileExpr e eTgt ->
    EvalTgt fEnvTgt eTgt envTgt v' ->
    ValEq v v'
theorem_semantic_preservation (ESPrimVal) ce cfe (CEPrimVal) (ETPrimVal) = valEqRefl
theorem_semantic_preservation (ESV {x} l) ce cfe (CEVal) (ETV l') = lookupRel x env envTgt ce l l'
theorem_semantic_preservation (ESLet {v1} e1 e2) ce cfe (CELet ce1 ce2) (ETLet ce1' ce2') = 
    let pf1 = theorem_semantic_preservation e1 ce cfe ce1 ce1'
        ce' = CECons (EVEq pf1) ce
        pf2 = theorem_semantic_preservation e2 ce' cfe ce2 ce2'
    in pf2
theorem_semantic_preservation (ESAppName {args} l t r s) ce cfe (CEAppName) (ETAppName {inArgs=inArgs'} l' t' r' s') = 
    let compiledArgs = valEqListPreservation args env envTgt ce t t'
        inArgsRel = fenvRel cfe l l'
        compiledEnv = compileArgsPreserve inArgsRel compiledArgs r r'
        compileBody = fenvRel2 cfe l l'
    in theorem_semantic_preservation s compiledEnv cfe compileBody s'
theorem_semantic_preservation (ESOp {args} {arity} ints fun {argVals}) ce cfe (CEOp) (ETOp {arity} ints' fun' {v=v'} {f=f'} {argVals=argVals'}) =
    let pf = valEqVecPreservation {n=arity} args env envTgt ce ints ints'
    in valEqPrimFun {pf} fun fun'

