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
and var = string

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ "\n")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty -> 
  match e with
  | CONST n -> (ty, TyInt)::[]
  | VAR x -> (ty, (TEnv.find tenv x))::[]
  | ADD (e1, e2) 
  | SUB (e1, e2) 
  | MUL (e1, e2)
  | DIV (e1, e2) -> (ty, TyInt)::((gen_equations tenv e1 TyInt)@(gen_equations tenv e2 TyInt))
  | ISZERO e -> (ty, TyBool)::(gen_equations tenv e TyInt)
  | READ -> (ty, TyInt)::[]
  | IF (e1, e2 ,e3)-> (gen_equations tenv e1 TyBool)@(gen_equations tenv e2 ty)@(gen_equations tenv e3 ty)
  | LET (x, e1, e2) ->
    let t1 = fresh_tyvar() in
    (gen_equations tenv e1 t1)@(gen_equations (TEnv.extend (x, t1) tenv) e2 ty)
  | LETREC (f, x, e1, e2) -> 
    let t1 = fresh_tyvar() in
    let t2 = fresh_tyvar() in
    let func_type = TyFun (t2, t1) in
    (gen_equations (TEnv.extend (f, func_type) (TEnv.extend (x, t2) tenv)) e1 t1)@(gen_equations (TEnv.extend (f, func_type) tenv) e2 ty)
  | PROC (x, e) ->
    let t1 = fresh_tyvar() in
    let t2 = fresh_tyvar() in
    (ty, TyFun(t1, t2))::(gen_equations (TEnv.extend (x, t1) tenv) e t2)
  | CALL (e1, e2) ->
    let t1 = fresh_tyvar() in
    (gen_equations tenv e1 (TyFun (t1, ty)))@(gen_equations tenv e2 t1)

let rec find_var : tyvar -> typ -> bool
= fun x t ->
  match t with
  |TyInt -> false
  |TyBool -> false
  |TyVar y -> if x = y then true else false
  |TyFun(t1, t2) -> (find_var x t1) || (find_var x t2)

let rec unify : typ -> typ -> Subst.t -> Subst.t
= fun typ1 typ2 subst ->
  match (typ1, typ2) with
  |(TyInt, TyInt) -> subst
  |(TyBool, TyBool) -> subst
  |(TyVar x, typ) -> 
    begin
      match typ with 
      |TyVar y -> 
        if x = y then subst else Subst.extend x typ subst
      |TyFun(t1, t2) ->
        if ((find_var x t1) || (find_var x t2)) then raise TypeError
        else Subst.extend x typ subst
      |_ -> Subst.extend x typ subst
    end
  |(typ, TyVar x) -> unify (TyVar x) typ subst
  |(TyFun(t1, t2), TyFun(t1',t2')) ->
    let subst' = unify t1 t1' subst in
    let t3 = Subst.apply t2 subst' in
    let t4 = Subst.apply t2' subst' in
      unify t3 t4 subst'
  |(_, _) -> raise TypeError

let rec unify_all : typ_eqn -> Subst.t -> Subst.t
= fun eqns subst ->
  match eqns with
  |[] -> subst
  |(typ1, typ2)::tl ->
    let subst' = unify (Subst.apply typ1 subst) (Subst.apply typ2 subst) subst in
    unify_all tl subst'
  
let solve : typ_eqn -> Subst.t
=fun eqns -> 
  unify_all eqns Subst.empty

(* typeof: Do not modify this function *)
let typeof : exp -> typ 
=fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns in
  try 
    let subst = solve eqns in
    let ty = Subst.apply new_tv subst in
     print_endline "= Substitution = ";
      Subst.print subst;
      print_endline "";
      print_endline ("Type of the given program: " ^ string_of_type ty);
      print_endline "";
      ty
  with TypeError -> (print_endline "The program does not have type. Rejected."); exit (1)