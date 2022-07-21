type program = exp
and exp = 
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
  | NEWREF of exp 
  | DEREF of exp
  | SETREF of exp * exp
  | SEQ of exp * exp
  | BEGIN of exp
and var = string

type value = 
    Int of int 
  | Bool of bool 
  | Closure of var * exp * env 
  | RecClosure of var * var * exp * env
  | Loc of loc
and env = var -> value
and loc = int
and mem = loc -> value

(* conversion of value to string *)
let value2str v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Loc l -> "Loc "^(string_of_int l)
  | Closure (x,e,env) -> "Closure "
  | RecClosure (f,x,e,env) -> "RecClosure "^f

(* environment *)
let empty_env : env = fun x -> raise (Failure "Environment is empty")
let extend_env : var * value -> env -> env 
=fun (x,v) e -> fun y -> if x = y then v else (e y)
let apply_env : env -> var -> value 
=fun e x -> e x

(* memory *)
let empty_mem : mem = fun _ -> raise (Failure "Memory is empty")
let extend_mem : loc * value -> mem -> mem
=fun (l,v) m -> fun y -> if l = y then v else (m y)
let apply_mem : mem -> loc -> value 
=fun m l -> m l

(* use the function 'new_location' to generate a fresh memory location *)
let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

(*****************************************************************)
(* TODO: Implement the eval function. Modify this function only. *)
(*****************************************************************)
let rec eval : exp -> env -> mem -> value * mem
=fun exp env mem ->
  match exp with
  | CONST n -> (Int (n),mem)
  | VAR v -> ((env v),mem) 
  | ADD (e1,e2) -> 
    let (v1,mem1) = eval e1 env mem in
    let (v2,mem2) = eval e2 env mem1 in
    begin match (v1,v2) with
    |(Int n1,Int n2) -> (Int (n1+n2),mem2)
    |_ -> raise (UndefinedSemantics)
    end
  | SUB (e1,e2) ->
    let (v1,mem1) = eval e1 env mem in
    let (v2,mem2) = eval e2 env mem1 in
    begin match (v1,v2) with
    |(Int n1,Int n2) -> (Int (n1-n2),mem2)
    |_ -> raise (UndefinedSemantics)
    end
  | MUL (e1,e2) ->
    let (v1,mem1) = eval e1 env mem in
    let (v2,mem2) = eval e2 env mem1 in
    begin match (v1,v2) with
    |(Int n1,Int n2) -> (Int (n1*n2),mem2)
    |_ -> raise (UndefinedSemantics)
    end
  | DIV (e1,e2) ->
    let (v1,mem1) = eval e1 env mem in
    let (v2,mem2) = eval e2 env mem1 in
    begin match (v1,v2) with
    |(Int n1,Int n2) -> (Int (n1/n2),mem2)
    |_ -> raise (UndefinedSemantics)
    end
  | ISZERO e ->
    let (v1,mem1) = eval e env mem in
    begin match v1 with
    |Int n1 -> (Bool (n1=0),mem1)
    |_ -> raise (UndefinedSemantics)
    end
  | READ -> (Int(read_int ()),mem)
  | IF (e1,e2,e3) ->
    let (v1,mem1) = eval e1 env mem in
    begin match v1 with
    |Bool b -> if b then (eval e2 env mem1) else (eval e3 env mem1)
    |_ -> raise (UndefinedSemantics)
    end
  | LET (x,e1,e2) ->
    let (v1,mem1) = eval e1 env mem in
    eval e2 (extend_env (x,v1) env) mem1
  | LETREC (f,x,e1,e2) ->
    eval e2 (extend_env (f,RecClosure(f,x,e1,env)) env) mem
  | PROC (x,e) ->
    (Closure(x,e,env),mem)
  | CALL (e1,e2) ->
    let (v1,mem1) = eval e1 env mem in
    begin match v1 with
    |Closure(x,e,env') ->
      let (v2,mem2) = eval e2 env mem1 in
      eval e (extend_env (x,v2) env') mem2
    |RecClosure(f,x,e,env') ->
      let (v2,mem2) = eval e2 env mem1 in
      eval e (extend_env (f,v1) (extend_env (x,v2) env')) mem2
    |_ -> raise (UndefinedSemantics)
    end
  | NEWREF e ->
    let loc = new_location () in
    let (v1,mem1) = eval e env mem in
    (Loc loc,extend_mem (loc,v1) mem1)
  | DEREF e ->
    let (v1,mem1) = eval e env mem in
    begin match v1 with
    |Loc loc -> ((mem1 loc),mem1)
    |_ -> raise (UndefinedSemantics)
    end
  | SETREF (e1,e2) ->
    let (v1,mem1) = eval e1 env mem in
    begin match v1 with
    |Loc loc -> 
      let (v2,mem2) = eval e2 env mem1 in
      (v2,extend_mem (loc,v2) mem2)
    |_ -> raise (UndefinedSemantics)
    end
  | SEQ (e1,e2) ->
    let (v1,mem1) = eval e1 env mem in
    eval e2 env mem1
  | BEGIN e -> eval e env mem
(* driver code *)
let run : program -> value
=fun pgm -> (fun (v,_) -> v) (eval pgm empty_env empty_mem) 
