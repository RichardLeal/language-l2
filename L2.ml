(*++++++++++++++++++++++++++++++++++++++*)
(*  Interpretador para L1               *)
(*   - inferência de tipos              *)
(*   - avaliador big step com ambiente  *)
(*++++++++++++++++++++++++++++++++++++++*)

(**+++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*  SINTAXE ABSTRATA, AMBIENTE de TIPOS e de VALORES  *)
(*++++++++++++++++++++++++++++++++++++++++++++++++++++*)

(* +++++++++++++++++ TIPOS +++++++++++++++++*)
(* T ∈ Types *)
(* T ::= int | bool | T1 → T2 | T1 ∗ T2 | T ref | unit *)
type tipo =
    TyInt (* T-Int, tipo inteiro *)
  | TyBool (* T-Bool, tipo booleano *)
  | TyFn of tipo * tipo (* T-Fn, tipo função *)
  | TyPair of tipo * tipo (* T-Pair, tipos pares ordenados *)

(* +++++++++++++++++ EXPRESSÕES +++++++++++++++++*)
(* Identificadores de variáveis são representados como strings *)
type ident = string
(* Conjunto de operadores binário *)
type op = Sum (* + *) | Sub (* - *) | Mult (* * *) | Eq (* = *) | Gt (* > *) | Lt (* < *) | Geq (* >= *) | Leq (* <= *)

(* e ∈ Expr *)
(* e ::= n | b | (e1, e2) | fst e | snd e | e1 op e2 | if e1 then e2 else e3 | x | e1 e2
   | fn x: T ⇒ e | let x: T = e1 in e2 | let rec f: T1 → T2 = (fn x: T1 ⇒ e1) in e2 
   | e1 := e2 | !e | new e | skip | while e1 do e2 | e1;e2 | l *)
type expr =
  | Num of int (* n *)
  | Var of ident (* x *)
  | True (* b *)
  | False (* b *)
  | Binop of op * expr * expr (* e1 op e2 *)
  | Pair of expr * expr (* (e1, e2) *)
  | Fst of expr (* fst e *)
  | Snd of expr (* snd e *)
  | If of expr * expr * expr (* if e1 then e2 else e3 *)
  | Fn of ident * tipo * expr (* fn x: T ⇒ e *)
  | App of expr * expr (* e1 e2 *)
  | Let of ident * tipo * expr * expr (* let x: T = e1 in e2 *)
  | LetRec of ident * tipo * expr  * expr (* let rec f: T1 → T2 = (fn x: T1 ⇒ e1) in e2 *)
     
(* ++++++++++++++++++ AMBIENTE ++++++++++++++++++*)
(* Ambiente de tipos Γ *)
type tenv = (ident * tipo) list (* Γ *)

(* ++++++++++++++++++ VALORES +++++++++++++++++++*)
(* v ∈ Values *)
(* v ::= n | b | fn: T ⇒ e | l *)
type valor =
    VNum of int (* n *)
  | VTrue (* b *)
  | VFalse (* b *)
  | VPair of valor * valor (* (v1, v2) *)
  | VClos  of ident * expr * renv (* Γ ⊢ fn: T ⇒ e *)
  | VRclos of ident * ident * expr * renv (* Γ ⊢ fn: T ⇒ e *)
and 
  renv = (ident * valor) list (* Ambiente de tipos em runtime Γ *)
    
(* ++++++++++++++++++ AMBIENTE ++++++++++++++++++*)
(* funções polimórficas para ambientes *)
(* As regras do sistema de tipo são da forma Γ ⊢ e :T, lido “ a expressão é do tipo T dadas as informacões acerca do tipo de identificadores 
   que são mantidas em Γ ”. O ambientede tipos Γ captura a essência de uma tabela de símbolos de um compilador/interpretador formalizada aqui
   como uma funcão de identificadores declarados para seus tipos. A notacão Γ(x) pode ser vista como uma abstracão para uma operacão lookup(Γ, x) *)
(* T-Var−lookpup retorna erro se x nao foi declarado *)    
let rec lookup a k =
  match a with
    [] -> None
  | (y,i) :: tl -> if (y=k) then Some i else lookup tl k 
       
(* A notação Γ,x : T (usada na regra para funções, let, e let rec), representa a operação update(Γ,(x,T)) *)
let rec update a k i =
  (k,i) :: a   

(* exceções que não devem ocorrer  *)
exception BugParser
exception BugTypeInfer
  
(**+++++++++++++++++++++++++++++++++++++++++*)
(*         INFERÊNCIA DE TIPOS              *)
(*++++++++++++++++++++++++++++++++++++++++++*)
exception TypeError of string

let rec typeinfer (tenv:tenv) (e:expr) : tipo =
  match e with

  (* T-Int  *)
  | Num _ -> TyInt

  (* T-Var *)
  | Var x ->
      (match lookup tenv x with
         Some t -> t
       | None -> raise (TypeError ("variavel nao declarada:" ^ x)))

  (* T-Bool *)
  | True  -> TyBool
  | False -> TyBool

  (*T-OP-Bin operadores binários *)
  | Binop(oper,e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      if t1 = TyInt && t2 = TyInt then
        (match oper with
           Sum | Sub | Mult -> TyInt
         | Eq | Lt | Gt | Geq | Leq -> TyBool)
      else raise (TypeError "operando nao é do tipo int")

  (* T-Pair *)
  | Pair(e1,e2) -> TyPair(typeinfer tenv e1, typeinfer tenv e2)

  (* T-Fst *)
  | Fst e1 ->
      (match typeinfer tenv e1 with
         TyPair(t1,_) -> t1
       | _ -> raise (TypeError "fst espera tipo par"))

  (* T-Snd  *)
  | Snd e1 ->
      (match typeinfer tenv e1 with
         TyPair(_,t2) -> t2
       | _ -> raise (TypeError "fst espera tipo par"))

  (* T-If  *)
  | If(e1,e2,e3) ->
      (match typeinfer tenv e1 with
         TyBool ->
           let t2 = typeinfer tenv e2 in
           let t3 = typeinfer tenv e3
           in if t2 = t3 then t2
              else raise (TypeError "then/else com tipos diferentes")
       | _ -> raise (TypeError "condição de IF não é do tipo bool"))

  (* T-Fn *)
  | Fn(x,t,e1) ->
      let t1 = typeinfer (update tenv x t) e1
      in TyFn(t,t1)

  (* T-App *)
  | App(e1,e2) ->
      (match typeinfer tenv e1 with
         TyFn(t, t') ->  if (typeinfer tenv e2) = t then t'
           else raise (TypeError "tipo argumento errado" )
       | _ -> raise (TypeError "tipo função era esperado"))

  (* T-Let *)
  | Let(x,t,e1,e2) ->
      if (typeinfer tenv e1) = t then typeinfer (update tenv x t) e2
      else raise (TypeError "expr nao é do tipo declarado em Let" )

  (* T-LetRec *)
  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) ->
      let tenv_com_tf = update tenv f tf in
      let tenv_com_tf_tx = update tenv_com_tf x tx in
      if (typeinfer tenv_com_tf_tx e1) = t2
      then typeinfer tenv_com_tf e2
      else raise (TypeError "tipo da funcao diferente do declarado")
  | LetRec _ -> raise BugParser           
  
(**+++++++++++++++++++++++++++++++++++++++++*)
(*                 AVALIADOR                *)
(*++++++++++++++++++++++++++++++++++++++++++*)

let compute (oper: op) (v1: valor) (v2: valor) : valor =
  match (oper, v1, v2) with
    (Sum, VNum(n1), VNum(n2)) -> VNum (n1 + n2)
  | (Sub, VNum(n1), VNum(n2)) -> VNum (n1 - n2)
  | (Mult, VNum(n1),VNum(n2)) -> VNum (n1 * n2)
  | (Eq, VNum(n1), VNum(n2))  -> if (n1 = n2)  then VTrue else VFalse
  | (Gt, VNum(n1), VNum(n2))  -> if (n1 > n2)  then VTrue else VFalse
  | (Lt, VNum(n1), VNum(n2))  -> if (n1 < n2)  then VTrue else VFalse
  | (Geq, VNum(n1), VNum(n2)) -> if (n1 >= n2) then VTrue else VFalse
  | (Leq, VNum(n1), VNum(n2)) -> if (n1 <= n2) then VTrue else VFalse
  | _ -> raise BugTypeInfer

(* ++++++++ SEMÂNTICA OPERACIONAL ++++++++*)
let rec eval (renv:renv) (e:expr) : valor =
  match e with
    Num n -> VNum n
  | True -> VTrue
  | False -> VFalse


  | Var x ->
      (match lookup renv x with
         Some v -> v
       | None -> raise BugTypeInfer)
      
  | Binop(oper,e1,e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      compute oper v1 v2

  | Pair(e1,e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2
      in VPair(v1,v2)

  | Fst e ->
      (match eval renv e with
       | VPair(v1,_) -> v1
       | _ -> raise BugTypeInfer)

  | Snd e ->
      (match eval renv e with
       | VPair(_,v2) -> v2
       | _ -> raise BugTypeInfer)

  (*If*)
  | If(e1,e2,e3) ->
      (match eval renv e1 with
         VTrue  -> eval renv e2
       | VFalse -> eval renv e3
       | _ -> raise BugTypeInfer )

  (*E-β*)
  | Fn (x,_,e1) ->  VClos(x,e1,renv)

  (*E-App*)
  | App(e1,e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      (match v1 with
         VClos(x,ebdy,renv') ->
           let renv'' = update renv' x v2
           in eval renv'' ebdy

       | VRclos(f,x,ebdy,renv') ->
           let renv''  = update renv' x v2 in
           let renv''' = update renv'' f v1
           in eval renv''' ebdy
       | _ -> raise BugTypeInfer)

  | Let(x,_,e1,e2) ->
      let v1 = eval renv e1
      in eval (update renv x v1) e2

  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let renv'= update renv f (VRclos(f,x,e1,renv))
      in eval renv' e2
        
        
  | LetRec _ -> raise BugParser
                  
                  
(* função auxiliar que converte tipo para string *)

let rec ttos (t:tipo) : string =
  match t with
    TyInt  -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyPair(t1,t2) ->  "("  ^ (ttos t1) ^ " * "   ^ (ttos t2) ^ ")"

(* função auxiliar que converte valor para string *)

let rec vtos (v: valor) : string =
  match v with
    VNum n -> string_of_int n
  | VTrue -> "true"
  | VFalse -> "false"
  | VPair(v1, v2) ->
      "(" ^ vtos v1 ^ "," ^ vtos v1 ^ ")"
  | VClos _ ->  "fn"
  | VRclos _ -> "fn"

(* principal do interpretador *)

let int_bse (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let v = eval [] e
    in  print_string ((vtos v) ^ " : " ^ (ttos t))
  with
    TypeError msg ->  print_string ("erro de tipo - " ^ msg)
   
 (* as exceções abaixo nao podem ocorrer   *)
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"
  | BugParser     ->  print_string "corrigir bug no parser para let rec"
                        



 (* +++++++++++++++++++++++++++++++++++++++*)
 (*                TESTES                  *)
 (*++++++++++++++++++++++++++++++++++++++++*)



(*
     let x:int = 2 
     in let foo: int --> int = fn y:int => x + y 
        in let x: int = 5
           in foo 10 
*)

let e'' = Let("x", TyInt, Num 5, App(Var "foo", Num 10))

let e'  = Let("foo", TyFn(TyInt,TyInt), Fn("y", TyInt, Binop(Sum, Var "x", Var "y")), e'')

let tst = Let("x", TyInt, Num(2), e') 
    
    (*
     let x:int = 2 
     in let foo: int --> int = fn y:int => x + y 
        in let x: int = 5
           in foo 
*)


let e2 = Let("x", TyInt, Num 5, Var "foo")

let e1  = Let("foo", TyFn(TyInt,TyInt), Fn("y", TyInt, Binop(Sum, Var "x", Var "y")), e2)

let tst2 = Let("x", TyInt, Num(2), e1) 