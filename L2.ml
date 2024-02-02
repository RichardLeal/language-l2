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
  | TyRef of tipo
  | TyUnit

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
  | Asg of expr * expr

  (* Os operadores unários new e ! são usados para alocar uma posicão de memória e para acessar o valor contido
     em uma determinada posicão de memória *)
  | Dref of expr (* !e *)
  | New of expr (* new e *)

  | Seq of expr * expr
  | Whl of expr * expr
  | Skip
     
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
  | VClos of ident * expr * renv (* Γ ⊢ fn: T ⇒ e *)
  | VRclos of ident * ident * expr * renv (* Γ ⊢ fn: T ⇒ e *)
  | VSkip
  | VIdent of ident
and 
(* Ambiente de tipos em runtime*)
(* Esse ambiente ρ corresponde ao ambiente vigente no momento em que a função é avaliada como valor.
  O closure carrega esse ambiente para dar sentido às variáveis que possam ocorrer dentro do corpoda função,
  mas cujos valores foram definidos fora docorpo da funcão (chamadas de variáveis livres da funcão).
  Esse mecanismo é chamado de escopo estático.*)
  renv = (ident * valor) list 

type mem = (ident * valor) list
    
(* ++++++++++++++++++ AMBIENTE ++++++++++++++++++*)
(* funções polimórficas para ambientes *)
(* As regras do sistema de tipo são da forma Γ ⊢ e :T, lido “ a expressão é do tipo T dadas as informacões acerca do tipo de identificadores 
   que são mantidas em Γ ”. O ambientede tipos Γ captura a essência de uma tabela de símbolos de um compilador/interpretador formalizada aqui
   como uma funcão de identificadores declarados para seus tipos. A notacão Γ(x) pode ser vista como uma abstracão para uma operacão lookup(Γ, x) *)
(* T-Var−lookpup retorna erro se x nao foi declarado *)    
let rec lookup environment identifier =
  match environment with
    [] -> None
  | (headIdentifier, headType) :: tail 
    -> if (headIdentifier=identifier) then Some headType else lookup tail identifier
       
(* A notação Γ,x : T (usada na regra para funções, let, e let rec), representa a operação update(Γ,(x,T)) *)
(* update(Γ,(x,T)) *)
(* update(environment,(identifier, typeIdentifier)) *)
let rec update environment identifier typeIdentifier = 
  (match environment with
   | [] -> (identifier, typeIdentifier) :: environment
   | (headIdentifier, headType) :: tail -> 
       if (headIdentifier=identifier) then (identifier, typeIdentifier) :: tail
       else (headIdentifier, headType) :: (update tail identifier typeIdentifier)) 

(* Função recursiva lastAddress encontra o valor máximo de uma lista de strings que representam números inteiros.
   Cada string address na lista é convertida para um inteiro usando int_of_string, e o máximo entre o valor convertido 
   e o máximo atual (actualPositionMem) é calculado recursivamente. A função retorna o valor máximo encontrado.*)
let rec lastAddress mem actualPositionMem =
  (match mem with
   | [] -> actualPositionMem 
   | (positionMemHead, valorPositionMem) :: tail -> 
       let positionMemHeadConvertedToInt = int_of_string positionMemHead in 
       lastAddress tail (max positionMemHeadConvertedToInt actualPositionMem))

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
  
  (* T-Skip *)
  | Skip -> TyUnit

  (* T-Atr *)
  | Asg(e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      (match t1 with
         TyRef(t) ->
           if t2 = t then TyUnit
           else raise (TypeError "ref e atribuicao de tipos diferentes")
       | _ -> raise (TypeError "era esperado um tipo ref"))

  (* T-Deref *)
  | Dref(e1) ->
      let t1 = typeinfer tenv e1 in
      (match t1 with
         TyRef(t) -> t
       | _ -> raise (TypeError "era esperado um tipo ref"))

  (*  *)
  | Whl(e1, e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      (match (t1, t2) with
         (TyBool, TyUnit) -> TyUnit
       | _ -> raise (TypeError "era esperado um tipo bool e um tipo unit"))

  (* T-New *)
  | New(e1) -> TyRef(typeinfer tenv e1)

  (* T-Seq *)
  | Seq(e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      (match t1 with
         TyUnit -> t2
       | _ -> raise (TypeError "era esperado um tipo unit"))
  
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
let rec eval (renv:renv) (mem:mem) (e:expr) : (valor * mem) =
  match e with
  | Num n -> (VNum n, mem)
  | True -> (VTrue, mem)
  | False -> (VFalse, mem)

  | Var x ->
      (match lookup renv x with
         Some v -> (v, mem)
       | None -> raise BugTypeInfer)
      
  | Binop(oper,e1,e2) ->
      let (v1, mem) = eval renv mem e1 in
      let (v2, mem) = eval renv mem e2 in
      (compute oper v1 v2, mem)

  | Pair(e1,e2) ->
      let (v1, mem) = eval renv mem e1 in
      let (v2, mem) = eval renv mem e2
      in (VPair(v1,v2), mem)

  | Fst e ->
      (match eval renv mem e with
       | (VPair(v1,_), mem) -> (v1, mem)
       | _ -> raise BugTypeInfer)

  | Snd e ->
      (match eval renv mem e with
       | (VPair(v2,_), mem) -> (v2, mem)
       | _ -> raise BugTypeInfer)

  (*If*)
  | If(e1,e2,e3) ->
      let (v1, mem) = eval renv mem e1 in
      (match v1 with
         VTrue  -> eval renv mem e2
       | VFalse -> eval renv mem e3
       | _ -> raise BugTypeInfer )

  (*E-β*)
  (*Ao invés de realizar a substituição de identificadores por valores, é construída uma estrutura
  de dados (ambiente) que descreve a substituição. A substituição só é feita sob demanda ao nos
   depararmos com variáveis. Ao utilizarmos esse modelo, contudo, precisamos ser mais cuidadosos com 
   questões de escopo. O valor ⟨x,e,ρ⟩ é denominada closure e representa uma função ao comseu argumento x,
    seu corpo e e o ambiente ρ. Esse ambiente ρ corresponde ao ambiente vigente no momento em que
    a função eavaliada com o valor. O closure carrega esse ambiente para dar sentido as variáveis
    que possam ocorrer dentro do corpo da função mas cujos valores foram definidos fora do corpo 
    da função(chamadas de variáveis livres da função). Esse mecanismo é chamado de escopo estático. 
    Se isso não fosse feito, os valores das variáveis livres da função seriam obtidos no ambiente 
vigente no momento da chamada da função o que é conhecido como escopo dinâmico.*)
  | Fn (x,_,e1) ->  (VClos(x,e1,renv), mem)

  (*E-App*)
  | App(e1,e2) ->
      let (v1, mem) = eval renv mem e1 in
      let (v2, mem) = eval renv mem e2 in
      (match v1 with
         VClos(x,ebdy,renv') ->
           let renv'' = update renv' x v2
           in eval renv'' mem ebdy

       | VRclos(f,x,ebdy,renv') ->
           let renv''  = update renv' x v2 in
           let renv''' = update renv'' f v1
           in eval renv''' mem ebdy
       | _ -> raise BugTypeInfer)

  | Let(x,_,e1,e2) ->
      let  (v1, mem) = eval renv mem e1
      in eval (update renv x v1) mem e2

  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let renv'= update renv f (VRclos(f,x,e1,renv))
      in eval renv' mem e2
        
  | LetRec _ -> raise BugParser

  
  | Skip -> (VSkip, mem)
                  
  | Asg(e1,e2) ->
      let (v1, mem) = eval renv mem e1 in 
      let (v2, mem) = eval renv mem e2 in
      (match v1 with 
         VIdent(t) -> 
           (match lookup mem t with
              Some a -> (VSkip, update mem t v2) 
            | None -> raise BugTypeInfer) 
       | _ -> raise BugTypeInfer)
      
  | Dref(e) -> 
      let (v, mem) = eval renv mem e in
      (match v with 
         VIdent(t) ->
           (match lookup mem t with
              Some a -> (a, mem)
            | None -> raise BugTypeInfer) 
       | _ -> raise BugTypeInfer) 
      
  | New(e) ->
      let (v, mem) = eval renv mem e in (* quando e avaliar para um valor*)
      let i = Printf.sprintf "%d" ((lastAddress mem 0) + 1) in (* pegamos uma posição de mem não alocada *)
      (VIdent(i), update mem i v) (* então atualizamos a mem e retornamos o endereço *)
      
  (* skip quando da certo o loop*)    
  | Whl(e1, e2) ->  eval renv mem (If (e1, Seq(e2, Whl(e1, e2)), Skip)) 
                      
  | Seq(e1,e2) ->
      let (v1, mem) = eval renv mem e1 in
      (match v1 with
         VSkip -> eval renv mem e2
       | _ -> raise BugTypeInfer)
                  
                  
(* função auxiliar que converte tipo para string *)

let rec ttos (t:tipo) : string =
  match t with
    TyInt  -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyPair(t1,t2) ->  "("  ^ (ttos t1) ^ " * "   ^ (ttos t2) ^ ")"
  (*| TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"*)
  | TyRef(t) ->  "Ref("  ^ (ttos t) ^ ")"
  | TyUnit -> "unit"

(* função auxiliar que converte valor para string *)

let rec vtos (v: valor) : string =
  match v with
  | VNum n -> string_of_int n
  | VTrue -> "true"
  | VFalse -> "false"
  | VClos _ ->  "fn"
  | VRclos _ -> "fn"
  | VSkip -> "skip"
  | VIdent _ -> "ident" 
  | VPair _ -> "pair"  

(* principal do interpretador *)

let int_bse (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let (v, mem) = eval [] [] e
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
    o programa abaixo retorna
        valor   = 7 
        memória = [(l1, 4)] 
    
    let x : int ref = new 3 in  -- x = end 1; 
    let y : int = !x in  --  y = 3
        (x := !x + 1);   -- 
        y + !x
*) 
let teste1 = Let("x", TyRef TyInt, New (Num 3),
                 Let("y", TyInt, Dref (Var "x"),
                     Seq(Asg(Var "x", Binop(Sum, Dref(Var "x"), Num 1)),
                         Binop(Sum, Var "y",  Dref (Var "x")))))
                                                                 
(*
        o programa abaixo retorna
        valor   = 1 
        memória = [(l1, 1)] 

     let x: int ref  = new 0 in
     let y: int ref  = x in
        x := 1;
        !y
*) 
let teste2 = Let("x", TyRef TyInt, New (Num 0),
                 Let("y", TyRef TyInt, Var "x",
                     Seq(Asg(Var "x", Num 1),
                         Dref (Var "y"))))
                                           
(*  
    o programa abaixo retorna
    valor   = 3
    memória = [(l1, 2)]
    

let counter : int ref = new 0  in 
let next_val : unit -> int =
  fn ():unit  =>
        counter := (!counter) + 1;
  !counter
in  (next_val()  + next_val())  
    *) 
let counter1 = Let("counter", TyRef TyInt, New (Num 0),
                   Let("next_val", TyFn(TyUnit, TyInt),
                       Fn("w", TyUnit,
                          Seq(Asg(Var "counter",Binop(Sum, Dref(Var "counter"), Num 1)),
                              Dref (Var "counter"))),
                       Binop(Sum, App (Var "next_val", Skip),
                             App (Var "next_val", Skip))))
  
(*   
     o programa abaixo retorna
     valor = 120
     memória = [(l2, 120), (l1,0) ]
     
let fat (x:int) : int = 

let z : int ref = new x in
let y : int ref = new 1 in 
while (!z > 0) (
    y :=  !y * !z;
    z :=  !z - 1;
  );
  ! y
in
fat 5
       
       
       
  SEM açucar sintático
    
let fat : int-->int = fn x:int => 

                           let z : int ref = new x in
                           let y : int ref = new 1 in 
        
                           while (!z > 0) (
                               y :=  !y * !z;
                               z :=  !z - 1;
                             );
                             ! y
in
fat 5
*)
let whilefat = Whl(Binop(Gt, Dref (Var "z"), Num 0),
                   Seq( Asg(Var "y", Binop(Mult, Dref (Var "y"), Dref (Var "z"))),
                        Asg(Var "z", Binop(Sub, Dref (Var "z"), Num 1)))
                  )
                             
let bodyfat = Let("z", TyRef TyInt, New (Var "x"),
                  Let("y", TyRef TyInt, New (Num 1), Seq (whilefat, Dref (Var "y"))))
    
let impfat = Let("fat", TyFn(TyInt,TyInt), Fn("x", TyInt, bodyfat), App(Var "fat", Num 5))


(* Testes antigos  *)


(* Escopo Estático (ou Léxico): *)
(* Característica Principal: O escopo de uma variável é determinado pelo local onde a variável é declarada no código-fonte. *)
(* Como Funciona: A resolução de identificadores é feita no momento da compilação, com base na estrutura léxica (estrutura de blocos) do código. *)

(* Escopo Dinâmico: *)
(* Característica Principal: O escopo de uma variável é determinado pelo contexto de execução durante o tempo de execução do programa. *)
(* Como Funciona: A resolução de identificadores é feita no momento da execução, com base nas variáveis disponíveis no momento da chamada da função.*)

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