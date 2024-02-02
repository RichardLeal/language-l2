TESTE 1
--------


Com açúcar sintático

let x: int ref = new 3  
let y: int     = !x  

{
    x := !x + 1;  
    y + !x
}


Sem açúcar sintático

let x: int ref = new 3  in
let y: int     = !x  in
     x := !x + 1; 
     y + !x


O programa  retorna  valor = 7  e memória com 4 em l0 

AST em OCAML:

let teste1 = Let("x", TyRef TyInt, New (Num 3),
             Let("y", TyInt, Dref (Var "x"), 
                 Seq(Asg(Var "x", Binop(Sum, Dref(Var "x"), Num 1)), 
                     Binop(Sum, Var "y",  Dref (Var "x"))))) 
 

==============================================
TESTE 
--------

O programa abaixo retorna valor = 1 e memória com 1 em l0 
    

 let x: int ref  = new 0 in 
 let y: int ref  = x     in 
    x := 1;
    !y

AST em OCAML:   

let teste2 = Let("x", TyRef TyInt, New (Num 0),
             Let("y", TyRef TyInt, Var "x", 
                 Seq(Asg(Var "x", Num 1), 
                     Dref (Var "y"))))

==============================================
TESTE 3
-------

O programa abaixo retorna  valor = 3 e memória com 2 em l0 
   
Com açúcar sintático 

  let counter : int ref = new 0

  let next_val (z:unit) : int  =
       {
        counter := (!counter) + 1;
        !counter
       }

   (next_val skip)  +  (next_val skip) 

Sem açúcar sintático

  let counter : int ref = new 0  in

  let next_val : unit --> int  =
       fun (z:unit) => 
            (counter := (!counter) + 1;
            !counter)            in

  (next_val skip)  +  (next_val skip) 
      

AST em OCAML:     

let counter1 = Let("counter", TyRef TyInt, New (Num 0),
               Let("next_val", TyFn(TyUnit, TyInt),
                   Fn("w", TyUnit, 
                      Seq(Asg(Var "counter",Binop(Sum, Dref(Var "counter"), Num 1)),
                          Dref (Var "counter"))),
                   Binop(Sum, App (Var "next_val", Skip), 
                              App (Var "next_val", Skip))))


==========================================================================    
TESTE 4
-------

O programa abaixo retorna  valor = 120
e memória com 0 em l0 e 120 em l2 
 
COM açucar sintático


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
   


AST em OCAML:       

let whilefat = Whl(Binop(Gt, Dref (Var "z"), Num 0), 
               Seq( Asg(Var "y", Binop(Mult, Dref (Var "y"), Dref (Var "z"))), 
                    Asg(Var "z", Binop(Sub,  Dref (Var "z"), Num 1)))                       
              ) 
                           
                         
let bodyfat = Let("z", 
              TyRef TyInt, 
              New (Var "x"),
              Let("y", 
                  TyRef TyInt, 
                  New (Num 1), 
                  Seq (whilefat, Dref (Var "y"))))

let impfat = Let("fat", 
             TyFn(TyInt,TyInt), 
             Fn("x", TyInt, bodyfat), 
             App(Var "fat", Num 5))
   

