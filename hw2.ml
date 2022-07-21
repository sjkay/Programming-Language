(* problem 1*)
type btree = Empty | Node of int * btree * btree

let rec mirror : btree -> btree
= fun t -> 
  match t with
  | Empty -> Empty
  | Node (n, t1, t2) -> Node (n, mirror t2, mirror t1)


(* problem 2*)
type nat = ZERO | SUCC of nat

let rec natadd : nat -> nat -> nat 
= fun n1 n2 -> 
  match n2 with
  | ZERO -> n1
  | SUCC n -> natadd (SUCC n1) n

let rec natmul : nat -> nat -> nat 
= fun n1 n2 -> 
  match n2 with
  | ZERO -> ZERO
  | SUCC n -> natadd n1 (natmul n1 n)

let rec natexp : nat -> nat -> nat 
= fun n1 n2 -> 
  match n2 with
  | ZERO -> SUCC ZERO
  | SUCC n -> natmul n1 (natexp n1 n)

(* problem 3*)
type formula =
    True
  | False
  | Var of string
  | Neg of formula
  | And of formula * formula
  | Or of formula * formula
  | Imply of formula * formula
  | Iff of formula * formula

type env = (string * bool) list

let extend_env x b e = (x,b)::e

let rec find_env x e = 
  match e with
  |[] -> raise (Failure "Env error")
  |(id,b)::tl -> if(x=id) then b else find_env x tl

let rec fold f l a =
  match l with
  | [] -> a
  | hd::tl -> f hd (fold f tl a)

let rec is_exist : string list -> string -> bool
= fun l str ->
  match l with
  |[] -> false
  |hd::tl -> (hd=str) || (is_exist tl str)

let rec eval : formula -> env -> bool
= fun f env ->
  match f with
  |True -> true
  |False -> false
  |Var v -> find_env v env
  |Neg f -> not (eval f env)
  |And (f1,f2) -> (eval f1 env) && (eval f2 env)
  |Or (f1,f2) -> (eval f1 env) || (eval f2 env)
  |Imply (f1,f2) -> (eval f2 env) || (not (eval f1 env))
  |Iff (f1,f2) -> (eval f1 env) = (eval f2 env)

let rec make_varlist : formula -> string list -> string list
= fun f result->
  match f with
  |Var v -> if(is_exist result v) then result else v::result
  |Neg f -> make_varlist f result
  |And (f1,f2) -> let result = make_varlist f1 result in make_varlist f2 result
  |Or (f1,f2) -> let result = make_varlist f1 result in make_varlist f2 result
  |Imply (f1,f2) -> let result = make_varlist f1 result in make_varlist f2 result
  |Iff (f1,f2) -> let result = make_varlist f1 result in make_varlist f2 result
  |_ -> result

let rec gen_env : string list -> env -> env list
= fun vars env ->
  match vars with
  |[] -> [env]
  |hd::tl -> 
    (gen_env tl (extend_env hd true env)) @ (gen_env tl (extend_env hd false env))

let rec sat : formula -> bool
= fun f ->
  let vars = make_varlist f [] in
  let enumerative_envs = gen_env vars [] in
  fold (fun env r-> r || (eval f env)) enumerative_envs false
  
(* problem 4*)
type aexp =
  | Const of int
  | Var of string
  | Power of string * int
  | Times of aexp list
  | Sum of aexp list

let rec map : (aexp * string -> aexp) -> aexp list * string -> aexp list
= fun f (l, x) -> 
  match l with
  | [] -> []
  | hd::tl -> (f (hd, x))::(map f (tl, x))

let rec diff : aexp * string -> aexp
= fun (e,x) -> 
  match e with
  | Const n -> Const 0
  | Var a -> if (a <> x) then Const 0 else Const 1
  | Power (a, n) -> if (a <> x) then Const 0 else Times [Const n; Power (a, n-1)]
  | Times l ->
    begin
      match l with
      | [] -> Const 0
      | hd::tl -> Sum [Times ((diff (hd, x))::tl); Times [hd; diff ((Times tl), x)]]
    end
  | Sum l -> Sum (map diff (l, x))

(* problem 5*)
type exp = X
         | INT of int
         | ADD of exp * exp
         | SUB of exp * exp
         | MUL of exp * exp
         | DIV of exp * exp
         | SIGMA of exp * exp * exp

let rec apply : exp -> int -> exp
= fun e n ->
  match e with
  | INT n -> INT n
  | ADD (e1, e2) -> ADD ((apply e1 n), (apply e2 n))
  | SUB (e1, e2) -> SUB ((apply e1 n), (apply e2 n))
  | MUL (e1, e2) -> MUL ((apply e1 n), (apply e2 n))
  | DIV (e1, e2) -> DIV ((apply e1 n), (apply e2 n))
  | SIGMA (e1, e2, e3) -> SIGMA ((apply e1 n), (apply e2 n), e3)
  | X -> INT n

let rec calculator : exp -> int
= fun e -> 
  match e with
  | INT n -> n
  | ADD (e1, e2) -> (calculator e1) + (calculator e2)
  | SUB (e1, e2) -> (calculator e1) - (calculator e2)
  | MUL (e1, e2) -> (calculator e1) * (calculator e2)
  | DIV (e1, e2) -> (calculator e1) / (calculator e2)
  | SIGMA (e1, e2, e3) -> 
    let i = calculator e1 in
    let j = calculator e2 in 
    if (i > j) then raise (Failure "SIGMA Error") 
    else if (i = j) then (calculator (apply e3 i))
    else (calculator (apply e3 i)) + (calculator (SIGMA (ADD (e1, INT 1), e2, e3))) 
  | X -> raise (Failure "X is must in SIGMA")


(* problem 6*)
type mobile = branch * branch     (* left and rigth branches *)
and branch = SimpleBranch of length * weight
           | CompoundBranch of length * mobile
and length = int
and weight = int

let rec mobile_weight : mobile -> int
= fun m -> 
  match m with
  | (SimpleBranch (l1, w1), SimpleBranch (l2, w2)) -> w1 + w2
  | (SimpleBranch (l1, w1), CompoundBranch (l2, m2)) -> w1 + (mobile_weight m2)
  | (CompoundBranch (l1, m1), SimpleBranch (l2, w2)) -> (mobile_weight m1) + w2
  | (CompoundBranch (l1, m1), CompoundBranch (l2, m2)) -> (mobile_weight m1) + (mobile_weight m2)

let rec balanced : mobile -> bool
= fun m -> 
  match m with
  | (SimpleBranch (l1, w1), SimpleBranch (l2, w2)) -> (l1 * w1) = (l2 * w2)
  | (SimpleBranch (l1, w1), CompoundBranch (l2, m2)) -> ((l1 * l1) = (l2 * (mobile_weight m2))) && (balanced m2)
  | (CompoundBranch (l1, m1), SimpleBranch (l2, w2)) -> (balanced m1) && ((l1 * (mobile_weight m1)) = (l2 * w2)) 
  | (CompoundBranch (l1, m1), CompoundBranch (l2, m2)) -> (balanced m1) && (balanced m2) && ((l1 * (mobile_weight m1)) = (l2 * (mobile_weight m2)))

(* problem 7*)
type digit = ZERO | ONE
type bin = digit list

let rec rev lst = 
  match lst with
  |[] -> []
  |hd::tl -> (rev tl)@[hd]

let rec length lst = 
  match lst with
  |[] -> 0
  |hd::tl -> 1+(length tl)

let rec expand : bin -> int -> bin
= fun b n ->
  if(n=0) then b else expand (b@[ZERO]) (n-1)

let rec gen_bins : bin -> bin -> int -> bin list
= fun b1 b2 n->
  match b1 with
  |[] -> []
  |hd::tl -> 
    begin match hd with
    |ZERO -> gen_bins tl b2 (n-1)
    |ONE -> (expand b2 n)::(gen_bins tl b2 (n-1))
    end

let rec bin_add : bin -> bin -> int -> bin
= fun b1 b2 carry->
  match (b1,b2) with
  |([],[]) -> if(carry=1) then [ONE] else []
  |(n1,[]) -> if(carry=0) then n1 else bin_add [ONE] n1 0
  |([],n1) -> bin_add b2 b1 carry
  |(h1::t1,h2::t2) -> 
    begin match (h1,h2) with
    |(ONE,ONE) -> if(carry=1) then ONE::(bin_add t1 t2 1) else ZERO::(bin_add t1 t2 1)
    |(ZERO,ZERO) -> if(carry=1) then ONE::(bin_add t1 t2 0) else ZERO::(bin_add t1 t2 0)
    |_ -> if(carry=1) then ZERO::(bin_add t1 t2 1) else ONE::(bin_add t1 t2 0)
    end

let rec bin_sum : bin list -> bin -> bin
= fun bins result ->
  match bins with
  |[] -> result
  |hd::tl -> bin_sum tl (rev (bin_add (rev hd) (rev result) 0))

let bmul : bin -> bin -> bin
= fun b1 b2 -> 
  let bins = gen_bins b1 b2 ((length b1)-1) in
  let result = bin_sum bins [] in
  result

