type aexp = 
  | CONST of int 
  | VAR of var
  | ADD of aexp * aexp 
  | MUL of aexp * aexp 
  | SUB of aexp * aexp
  
and bexp = 
  | TRUE 
  | FALSE 
  | EQ of aexp * aexp 
  | LT of aexp * aexp 
  | NOT of bexp 
  | AND of bexp * bexp

and stmt =
  | ASSIGN of var * aexp 
  | SKIP
  | SEQ of stmt * stmt
  | IF of bexp * stmt * stmt
  | WHILE of bexp * stmt
  | BLOCK of var * aexp * stmt
  | READ of var
  | PRINT of aexp 
and var = string
type program = stmt

type value = Int of int
type loc = Loc of int 
type env = var -> loc
type mem = loc -> value

let empty_env = fun x -> raise (Failure ("Undefined variable: " ^ x))
let extend_env (x,v) e = fun y -> if x = y then v else (e y)
let apply_env e x = e x

let empty_mem = fun _ -> raise (Failure "Memory is empty")
let extend_mem (l,v) m = fun y -> if l = y then v else (m y)
let apply_mem m l = m l

let counter = ref 0
let new_location () = counter:=!counter+1; Loc (!counter)

exception NotImplemented

let rec eval_aexp : aexp -> env -> mem -> int
=fun a env mem ->
  match a with
  | CONST n -> n
  | VAR x -> let (Int n) = apply_mem mem (apply_env env x) in n
  | ADD (a1, a2) -> (eval_aexp a1 env mem) + (eval_aexp a2 env mem)
  | MUL (a1, a2) -> (eval_aexp a1 env mem) * (eval_aexp a2 env mem)
  | SUB (a1, a2) -> (eval_aexp a1 env mem) - (eval_aexp a2 env mem)

and eval_bexp : bexp -> env -> mem -> bool
=fun b env mem -> 
  match b with 
  | TRUE -> true
  | FALSE -> false
  | EQ (a1, a2) -> (eval_aexp a1 env mem) = (eval_aexp a2 env mem) 
  | LT (a1, a2) -> (eval_aexp a1 env mem) <= (eval_aexp a2 env mem) 
  | NOT b1 -> (eval_bexp b1 env mem) = false
  | AND (b1, b2) -> (eval_bexp b1 env mem) && (eval_bexp b2 env mem)

let rec eval : stmt -> env -> mem -> mem
=fun s env mem -> 
  match s with
  | READ x -> extend_mem (apply_env env x, Int (read_int())) mem (* Do not modify *)
  | PRINT e -> print_int (eval_aexp e env mem); print_newline(); mem (* Do not modify *)
  | ASSIGN (x, a) ->
    let v = eval_aexp a env mem in
    let l = apply_env env x in
    extend_mem (l, Int v) mem
  | SKIP -> mem 
  | SEQ (s1, s2) -> 
    let mem' = eval s1 env mem in
    eval s2 env mem'
  | IF (b, s1, s2) -> if (eval_bexp b env mem) then eval s1 env mem else eval s2 env mem
  | WHILE (b, s1) -> 
    if (eval_bexp b env mem) then 
      let mem' = eval s1 env mem in
      eval s env mem'
    else mem
  | BLOCK (x, a, s1) ->
    let v = eval_aexp a env mem in
    let l = new_location () in
    let env' = extend_env (x, l) env in
    let mem' = extend_mem (l, Int v) mem in
    eval s1 env' mem'

let execute : program -> unit 
=fun pgm -> (ignore (eval pgm empty_env empty_mem))