(**********************)
(*   Problem 1        *)
(**********************)

type exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

type env = (var*exp) list

(* test cases *)
let pgm1 = LET ("x", CONST 1, VAR "x")
let pgm2 = 
  LET ("f", PROC ("x", VAR "x"), 
    IF (CALL (VAR "f", ISZERO (CONST 0)), 
        CALL (VAR "f", CONST 11), 
        CALL (VAR "f", CONST 22)))
let pgm3 = LET ("x", ADD (CONST 1, ISZERO (CONST 0)), CONST 2)

(* You can define datatypes and helper functions as necessary *)
let empty_env = []
let extend (x,e) env = (x,e)::env
let rec is_exist env x =
  match env with
  |[] -> false
  |(y,_)::tl -> (y=x)||(is_exist tl x)
let rec find env x = 
  match env with
  |[] -> raise(Failure "Env is empty")
  |(y,e)::tl -> if(y=x) then e else find tl x
let rec remove env x =
  match env with
  |[] -> []
  |(v,e)::tl -> if x=v then remove tl x else (v,e)::(remove tl x)


let rec is_unused : var -> exp -> bool
= fun v exp ->
  match exp with
  | CONST _ -> true
  | READ -> true
  | VAR x -> not (x=v)
  | ADD (e1,e2)
  | SUB (e1,e2)
  | MUL (e1,e2)
  | DIV (e1,e2)
  | CALL (e1,e2) -> (is_unused v e1)&&(is_unused v e2)
  | ISZERO e -> is_unused v e
  | IF (e1,e2,e3) -> (is_unused v e1)&&(is_unused v e2)&&(is_unused v e3)
  | PROC (x,e) -> if(x=v) then true else is_unused v e
  | LET (x,e1,e2) -> if(x=v) then is_unused v e1 else (is_unused v e1) && (is_unused v e2)
  | LETREC (v1,v2,e1,e2) -> if(v=v1) then true else if(v=v2) then is_unused v e2 else (is_unused v e1) && (is_unused v e2)

let rec erase_let : exp -> env -> exp
= fun exp env ->
  match exp with
  | CONST _ -> exp
  | VAR v ->
    if is_exist env v then find env v
    else exp
  | ADD (e1,e2) ->
    let e1 = erase_let e1 env in
    let e2 = erase_let e2 env in
    ADD(e1,e2)
  | SUB (e1,e2) ->
    let e1 = erase_let e1 env in
    let e2 = erase_let e2 env in
    SUB(e1,e2)
  | MUL (e1,e2) ->
    let e1 = erase_let e1 env in
    let e2 = erase_let e2 env in
    MUL(e1,e2)
  | DIV (e1,e2) ->
    let e1 = erase_let e1 env in
    let e2 = erase_let e2 env in
    DIV(e1,e2)
  | ISZERO e ->
    let e = erase_let e env in
    ISZERO e
  | READ -> exp
  | IF (e1,e2,e3) ->  
    let e1 = erase_let e1 env in
    let e2 = erase_let e2 env in
    let e3 = erase_let e3 env in
    IF (e1,e2,e3)
  | LET (v,e1,e2) ->
    let e1 = erase_let e1 env in
    if(is_unused v e2) then
      let e2 = erase_let e2 env in
      LET (v,e1,e2)
    else
      erase_let e2 (extend (v,e1) env) 
  | LETREC (v1,v2,e1,e2) ->
    let e1 = erase_let e1 (remove (remove env v1) v2) in
    let e2 = erase_let e2 (remove env v1) in
    LETREC(v1,v2,e1,e2)
  | PROC (v,e) ->
    let e = erase_let e (remove env v) in
    PROC(v,e)
  | CALL (e1,e2) ->
    let e1 = erase_let e1 env in
    let e2 = erase_let e2 env in
    CALL(e1,e2)



let rec expand : exp -> exp 
= fun exp -> erase_let exp empty_env
  

(**********************)
(*   Problem 2        *)
(**********************)

type lambda = V of var
            | P of var * lambda
            | C of lambda * lambda
and var = string

let rec list_mem : var list -> var -> bool
= fun env v ->
  match env with
  |[] -> false
  |hd::tl -> (hd=v)||(list_mem tl v)

let rec help_check : lambda -> var list -> bool
= fun lam env ->
  match lam with
  |V v -> list_mem env v
  |P (v,l) -> help_check l (v::env)
  |C (l1,l2) -> (help_check l1 env) && (help_check l2 env)

let rec check : lambda -> bool
= fun lam -> help_check lam []
