open Printf
open Util
open Ast
open Num

(** Keeps manifests produced by the compilation phase, for use during the linking phase. Avoids writing manifest files to disk. *)
let manifest_map: (string * string list) list ref = ref []
let jardeps_map: (string * string list) list ref = ref []

(* Region: some auxiliary types and functions *)

let lookup env x = List.assoc x env
let update env x t = (x, t)::env
let string_of_env env = String.concat "; " (List.map (function (x, t) -> x ^ " = " ^ t) env)

let is_lemma k = match k with Lemma(_) -> true | _ -> false

let printff format = kfprintf (fun _ -> flush stdout) stdout format

(** Internal pattern. Either a pattern from the source code, or a term pattern. A term pattern (TermPat t) matches a term t' if t and t' are definitely_equal. *)
type 'termnode pat0 = SrcPat of pat | TermPat of 'termnode
(** A heap chunk. *)
type chunk_info =
  PredicateChunkSize of int (* Size of this chunk with respect to the first chunk of the precondition; used to check lemma termination. *)
type 'termnode chunk =
  Chunk of
    ('termnode (* Predicate name *) * bool (* true if a declared predicate's symbol; false in a scenario where predicate names are passed as values. Used to avoid prover queries. *) ) *
    type_ list *  (* Type arguments *)
    'termnode *  (* Coefficient of fractional permission *)
    'termnode list *  (* Arguments; their prover type is as per the instantiated parameter types, not the generic ones. *)
    chunk_info option
type 'termnode heap = 'termnode chunk list
type 'termnode env = (string * 'termnode) list
(** Execution trace. For error reporting. *)
type branch = LeftBranch | RightBranch
type 'termnode context =
  Assuming of 'termnode
| Executing of 'termnode heap * 'termnode env * loc * string
| PushSubcontext
| PopSubcontext
| Branching of branch
type node_type = ExecNode of string * int list | BranchNode | SuccessNode | ErrorNode
type node = Node of node_type * node list ref

(* Returns the locations of the "call stack" of the current execution step. *)
let get_callers (ctxts: 'termnode context list): loc option list =
  let rec iter lo ls ctxts =
    match ctxts with
      [] -> ls
    | Executing (_, _, l, _)::ctxts -> iter (Some l) ls ctxts
    | PushSubcontext::ctxts -> iter lo (lo::ls) ctxts
    | PopSubcontext::ctxts -> let ls = match ls with [] -> [] | _::ls -> ls in iter None ls ctxts
    | _::ctxts -> iter lo ls ctxts
  in
  iter None [] (List.rev ctxts)

let get_root_caller ctxts = match List.rev (get_callers ctxts) with Some l::_ -> Some l | _ -> None

let rec string_of_type t =
  match t with
    Bool -> "bool"
  | Void -> "void"
  | Int (Signed, k) -> "int" ^ string_of_int ((1 lsl k) * 8)
  | Int (Unsigned, k) -> "uint" ^ string_of_int ((1 lsl k) * 8)
  | Float -> "float"
  | Double -> "double"
  | LongDouble -> "long double"
  | RealType -> "real"
  | InductiveType (i, []) -> i
  | InductiveType (i, targs) -> i ^ "<" ^ String.concat ", " (List.map string_of_type targs) ^ ">"
  | ObjType l -> "class " ^ l
  | StructType sn -> "struct " ^ sn
  | PtrType t -> string_of_type t ^ " *"
  | FuncType ft -> ft
  | PredType (tparams, ts, inputParamCount, inductiveness) ->
    let tparamsText = if tparams = [] then "" else "<" ^ String.concat ", " tparams ^ ">" in
    let paramTypesText =
      let typesText ts = String.concat ", " (List.map string_of_type ts) in
      match inputParamCount with
        None -> typesText ts
      | Some n ->
        let (ts1, ts2) = take_drop n ts in
        typesText ts1 ^ ";" ^ if ts2 = [] then "" else " " ^ typesText ts2
    in
    let inductivenessText = match inductiveness with Inductiveness_Inductive -> "" | Inductiveness_CoInductive -> "co" in
    Printf.sprintf "%spredicate%s(%s)" inductivenessText tparamsText paramTypesText
  | PureFuncType (t1, t2) ->
    let (pts, rt) =  (* uncurry *)
      let rec iter pts rt =
        match rt with
          PureFuncType (t1, t2) -> iter (t1::pts) t2
        | _ -> (List.rev pts, rt)
      in
      iter [t1] t2
    in
    Printf.sprintf "fixpoint(%s, %s)" (String.concat ", " (List.map string_of_type pts)) (string_of_type rt)
  | BoxIdType -> "box"
  | HandleIdType -> "handle"
  | AnyType -> "any"
  | TypeParam x -> x
  | InferredType (_, t) -> begin match !t with None -> "?" | Some t -> string_of_type t end
  | ArrayType(t) -> (string_of_type t) ^ "[]"
  | StaticArrayType(t, s) -> (string_of_type t) ^ "[" ^ (string_of_int s) ^ "]" 
  | ClassOrInterfaceName(n) -> n (* not a real type; used only during type checking *)
  | PackageName(n) -> n (* not a real type; used only during type checking *)
  | RefType(t) -> "ref " ^ (string_of_type t)
  | AbstractType x -> x

let string_of_targs targs =
  if targs = [] then "" else "<" ^ String.concat ", " (List.map string_of_type targs) ^ ">"

(* This assumes the termnodes have already been converted to strings. *)
let string_of_chunk (Chunk ((g, literal), targs, coef, ts, size): string chunk): string =
  (if coef = "1" then "" else "[" ^ coef ^ "]") ^ g ^ string_of_targs targs ^ "(" ^ String.concat ", " ts ^ ")"

let string_of_heap h = String.concat " * " (List.map string_of_chunk h)

let string_of_context c =
  match c with
    Assuming t -> "Assuming " ^ t
  | Executing (h, env, l, s) -> "Heap: " ^ string_of_heap h ^ "\nEnv: " ^ string_of_env env ^ "\n" ^ string_of_loc l ^ ": " ^ s
  | PushSubcontext -> "Entering subcontext"
  | PopSubcontext -> "Leaving subcontext"

exception SymbolicExecutionError of string context list * loc * string * string option

let full_name pn n = if pn = "" then n else pn ^ "." ^ n

type options = {
  option_verbose: int;
  option_disable_overflow_check: bool;
  option_allow_should_fail: bool;
  option_emit_manifest: bool;
  option_vroots: (string * string) list;
  option_allow_assume: bool;
  option_simplify_terms: bool;
  option_runtime: string option;
  option_provides: string list;
  option_keep_provide_files: bool;
  option_include_paths: string list;
  option_define_macros: string list;
  option_safe_mode: bool; (* for invocation through web interface *)
  option_header_whitelist: string list;
  option_use_java_frontend : bool;
  option_enforce_annotations : bool;
  option_allow_undeclared_struct_types: bool;
  option_data_model: data_model
} (* ?options *)

(* Region: verify_program_core: the toplevel function *)

(* result of symbolic execution; used instead of unit to detect branches not guarded by push and pop calls *)
type symexec_result = SymExecSuccess

let rec string_of_expr ?(verbose=false) =
  let kind name =
    if verbose then
      name ^ "#"
    else ""
  in function
  | True loc -> "true"
  | False loc -> "false"
  | Null loc -> "null"
  | Var (loc, name) -> (kind "Var") ^ name
  | WVar (loc, name, iscope) -> (kind "WVar") ^ name
  | TruncatingExpr (loc, e) -> (kind "Tunc") ^ string_of_expr ~verbose e
  | Operation (loc, op, exprs) -> (kind "Oper") ^ string_of_operation ~verbose op exprs
  | WOperation (loc, op, exprs, type_) -> (kind "WOper") ^ string_of_operation ~verbose op exprs
  | IntLit (loc, value, decimal, u_suffix, int_literal_lsuffix) ->
    Big_int.string_of_big_int value
  | WIntLit (loc, value) -> Big_int.string_of_big_int value
  | RealLit (loc, value) -> string_of_num value
  | StringLit (loc, value) -> "\"" ^ value ^ "\""
  | ClassLit (loc, string (* class literal in java *)) -> "ClassLit TBI"
  | Read (loc, expr, string (* lezen van een veld; hergebruiken voor java field access *)) -> "Read TBI"
  | ArrayLengthExpr (loc, expr) -> "ArrayLengthExpr TBI"
  | WRead (loc, expr, string1, string2, type_, bool, constant_value, ghostness) -> "WRead TBI"
  | WReadInductiveField (loc, expr (* The expression which results an instance of the inductive, data type. (usually just a variable) *), string (* inductive data type name *), string1 (* constructor name *), string2 (* field name *), type_l (* type arguments *)) -> "WReadInductiveField TBI"
  | ReadArray (loc, expr1, expr2) -> "ReadArray TBI"
  | WReadArray (loc, expr1, type_, expr2) -> "WReadArray TBI"
  | Deref (loc, expr, type_1 (* pointee type *) (* pointer dereference *)) -> "Deref TBI"
  | CallExpr (loc, name, type_args, family_arg_pats, arg_pats, _) ->
    (kind "CallE") ^ name ^
    (if type_args != [] then
       "<" ^ (String.concat ", " ["...";"..."](*List.map string_of_type type_args**)) ^ ">"
     else "") ^
    (if family_arg_pats != [] then
       "(" ^ (String.concat ", " (List.map (string_of_pat ~verbose) family_arg_pats)) ^ ")"
    else "") ^
    "(" ^ (String.concat ", " (List.map (string_of_pat ~verbose) arg_pats)) ^ ")"
  | ExprCallExpr ((* Call whose callee is an expression instead of a plain identifier *) loc, expr, expr_list) -> "ExprCallExpr TBI"
  | WFunPtrCall (loc, string, expr_list) -> "WFunPtrCall TBI"
  | WPureFunCall (loc, name, arg_types, args) ->
    (kind "WPure") ^ name ^ "(" ^ (String.concat ", " (List.map (string_of_expr ~verbose) args)) ^ ")"
  | WPureFunValueCall (loc, calee, args) ->
    (kind "WPureV") ^ "(" ^ (string_of_expr ~verbose calee) ^ ")" ^
    "(" ^ (String.concat ", " (List.map (string_of_expr ~verbose) args)) ^ ")"
  | WFunCall (loc, string, type_list, expr_list) -> "WFunCall TBI"
  | WMethodCall (loc, string1 (* declaring class or interface *), string (* method name *), type_list (* parameter types (not including receiver) *), expr_list (* args, including receiver if instance method *), method_binding) -> "WMethodCall TBI"
  | NewArray (loc, type_expr, expr) -> "NewArray TBI"
  | NewObject (loc, string, expr_list) -> "NewObject TBI"
  | NewArrayWithInitializer (loc, type_expr, expr_list) -> "NewArrayWithInitializer TBI"
  | IfExpr (loc, expr1, expr2, expr) -> "IfExpr TBI"
  | SwitchExpr (loc, expr, switch_expr_clause_list, loc_expr_option (* default clause *)) -> "SwitchExpr TBI"
  | WSwitchExpr (loc, expr, string, (* inductive type, fully qualified *) type_list, (* type arguments *) switch_expr_clause_list, loc_expr_option, (* default clause *) string_type_list, (* type environment *) type_ (* result type *)) -> "WSwitchExpr TBI"
  | PredNameExpr (loc, string (* naam van predicaat en line of code*)) -> "PredNameExpr TBI"
  | CastExpr (loc, type_expr, expr (* cast *)) -> "CastExpr TBI"
  | Upcast (expr, type_1 (* from *), type_2 (* to *)  (* Not generated by the parser; inserted by the typechecker. Required to prevent bad downcasts during autoclose. *)) -> "Upcast TBI"
  | TypedExpr (expr, type_  (* Not generated by the parser. In 'TypedExpr (e, t)', 't' should be the type of 'e'. Allows typechecked expression 'e' to be used where a not-yet-typechecked expression is expected. *)) -> "TypedExpr TBI"
  | WidenedParameterArgument (expr (* Appears only as part of LitPat (WidenedParameterArgument e). Indicates that the predicate parameter is considered to range over a larger set (e.g. Object instead of class C). *)) -> "WidenedParameterArgument TBI"
  | SizeofExpr (loc, type_expr) -> "SizeofExpr TBI"
  | AddressOf (loc, expr) -> "AddressOf TBI"
  | ProverTypeConversion (prover_type1, prover_type2, expr  (* Generated during type checking in the presence of type parameters, to get the prover types right *)) -> "(" ^ string_of_prover_type prover_type2 ^ ")(" ^ string_of_expr ~verbose expr ^ ")"
  | ArrayTypeExpr' (loc, expr) (* horrible hack --- for well-formed programs, this exists only during parsing *) -> "ArrayTypeExpr' TBI"
  | AssignExpr (loc, expr1, expr2) -> "AssignExpr TBI"
  | AssignOpExpr (loc, expr, operator, expr1, bool (* true = return value of lhs before operation *)) -> "AssignOpExpr TBI"
  | WAssignOpExpr (loc, expr1, string, expr2, bool) -> "WAssignOpExpr TBI"
  | InstanceOfExpr (loc, expr, type_expr) -> "InstanceOfExpr TBI"
  | SuperMethodCall (loc, string, expr_list) -> "SuperMethodCall TBI"
  | WSuperMethodCall (loc, string1 (*superclass*), string2, expr_list1, xxx) -> "WSuperMethodCall TBI"
  | InitializerList (loc, expr_list) -> "InitializerList TBI"
  | SliceExpr (loc, pat_option1, pat_option2) -> "SliceExpr TBI"
  | PointsTo (loc, expr, pat) -> "PointsTo TBI"
  | WPointsTo (loc, expr, type_, pat) -> "WPointsTo TBI"
  | PredAsn (loc, predref, type_expr_list, pat_list1 , pat_list2) ->
    (kind "Pred") ^ predref#name ^
    (if type_expr_list != [] then "<" ^ "..." ^ ">" else "") ^
    (if pat_list1 != [] then "(" ^ (String.concat ", " (List.map (string_of_pat ~verbose) pat_list2)) ^ ")" else "") ^
    "(" ^ (String.concat ", " (List.map (string_of_pat ~verbose) pat_list2)) ^ ")"
  | WPredAsn (loc, predref, bool, type_list, pat_list1, pat_list2) ->
    (kind "WPred") ^ predref#name ^
    (if type_list != [] then "<" ^ "..." ^ ">" else "") ^
    (if pat_list1 != [] then "(" ^ (String.concat ", " (List.map (string_of_pat ~verbose) pat_list2)) ^ ")" else "") ^
    "(" ^ (String.concat ", " (List.map (string_of_pat ~verbose) pat_list2)) ^ ")"
  | InstPredAsn (loc, expr1, string, expr2, (* index *) pat_list) -> "InstPredAsn TBI"
  | WInstPredAsn (loc, expr_option, string1 (* static type *), class_finality (* finality of static type *), string2 (* family type *), string3, expr (* index *), pat_list) -> "WInstPredAsn TBI"
  | ExprAsn ((* uitdrukking regel-expr *) loc, expr) -> (kind "EAsn") ^ string_of_expr ~verbose expr
  | Sep ((* separating conjunction *) loc, asn1, asn2) -> string_of_expr ~verbose asn1 ^ " &*& " ^ string_of_expr ~verbose asn2
  | IfAsn ((* if-predicate in de vorm expr? p1:p2 regel-expr-p1-p2 *) loc, cond, then_expr, else_expr) ->
    "(" ^ string_of_expr ~verbose cond ^ ") ? " ^ string_of_expr ~verbose then_expr ^ " : " ^ string_of_expr ~verbose else_expr
  | SwitchAsn ((* switch over cons van inductive type regel-expr-clauses*) loc, expr, switch_asn_clause_list) -> "SwitchAsn TBI"
  | WSwitchAsn ((* switch over cons van inductive type regel-expr-clauses*) loc, expr, string, (* inductive type (fully qualified) *) wswitch_asn_clause_list) -> "WSwitchAsn TBI"
  | EmpAsn ( (* als "emp" bij requires/ensures staat -regel-*) loc) -> "EmpAsn TBI"
  | ForallAsn (loc, type_expr, string, expr) -> "ForallAsn TBI"
  | CoefAsn ((* fractional permission met coeff-predicate*) loc, pat, asn) -> "CoefAsn TBI"
  | EnsuresAsn (loc, asn) -> "EnsuresAsn TBI"
  | MatchAsn (loc, expr, pat) -> "MatchAsn TBI"
  | WMatchAsn (loc, expr, pat, type_) -> "WMatchAsn TBI"
and string_of_pat ~verbose = function
  | LitPat expr -> string_of_expr ~verbose expr
  | VarPat (loc, name) -> "?" ^ name
  | DummyPat -> "_"
  | CtorPat (loc, name, params) ->
    (if verbose then "Ctor#" else "") ^
    name ^ "(" ^ (String.concat ", " (List.map (string_of_pat ~verbose) params)) ^ ")"
  | WCtorPat (loc, name, types1, str, types2, types3, params) ->
    (if verbose then "WCtor#" else "") ^
    name ^ "(" ^ (String.concat ", " (List.map (string_of_pat ~verbose) params)) ^ ")"
and string_of_operation ~verbose op args =
  match op, args with
  | Add, [lhs;rhs] -> string_of_expr ~verbose lhs ^ " + " ^ string_of_expr ~verbose rhs
  | Add, _ -> "Odd number of args for Add"
  | Sub, [lhs;rhs] -> string_of_expr ~verbose lhs ^ " - " ^ string_of_expr ~verbose rhs
  | Sub, _ -> "Odd number of args for Sub"
  | PtrDiff, _ -> "(TBI " ^ (String.concat " " (List.map (string_of_expr ~verbose) args)) ^ ")"
  | Le, [lhs;rhs] -> string_of_expr ~verbose lhs ^ " <= " ^ string_of_expr ~verbose rhs
  | Le, _ -> "Odd number of args for Le"
  | Ge, [lhs;rhs] -> string_of_expr ~verbose lhs ^ " >= " ^ string_of_expr ~verbose rhs
  | Ge, _ -> "Odd number of args for Ge"
  | Lt, [lhs;rhs] -> string_of_expr ~verbose lhs ^ " < " ^ string_of_expr ~verbose rhs
  | Lt, _ -> "Odd number of args for Lt"
  | Gt, [lhs;rhs] -> string_of_expr ~verbose lhs ^ " > " ^ string_of_expr ~verbose rhs
  | Gt, _ -> "Odd number of args for Gt"
  | Eq, [lhs;rhs] -> string_of_expr ~verbose lhs ^ " == " ^ string_of_expr ~verbose rhs
  | Eq, _ -> "Odd number of args for Eq"
  | Neq, [lhs;rhs] -> string_of_expr ~verbose lhs ^ " != " ^ string_of_expr ~verbose rhs
  | Neq, _ -> "Odd number of args for Neq"
  | And, [lhs;rhs] -> string_of_expr ~verbose lhs ^ " && " ^ string_of_expr ~verbose rhs
  | And, _ -> "Odd number of args for And"
  | Or, [lhs;rhs] -> string_of_expr ~verbose lhs ^ " || " ^ string_of_expr ~verbose rhs
  | Or, _ -> "Odd number of args for Or"
  | Xor, _ -> "(TBI " ^ (String.concat " " (List.map (string_of_expr ~verbose) args)) ^ ")"
  | Not, [arg] -> "!" ^ string_of_expr ~verbose arg
  | Not, _ -> "Wrong number of args for Not"
  | Mul, _ -> "(TBI " ^ (String.concat " " (List.map (string_of_expr ~verbose) args)) ^ ")"
  | Div, _ -> "(TBI " ^ (String.concat " " (List.map (string_of_expr ~verbose) args)) ^ ")"
  | Mod, _ -> "(TBI " ^ (String.concat " " (List.map string_of_expr args)) ^ ")"
  | BitNot, _ -> "(TBI " ^ (String.concat " " (List.map (string_of_expr ~verbose) args)) ^ ")"
  | BitAnd, _ -> "(TBI " ^ (String.concat " " (List.map (string_of_expr ~verbose) args)) ^ ")"
  | BitXor, _ -> "(TBI " ^ (String.concat " " (List.map (string_of_expr ~verbose) args)) ^ ")"
  | BitOr, _ -> "(TBI " ^ (String.concat " " (List.map (string_of_expr ~verbose) args)) ^ ")"
  | ShiftLeft, _ -> "(TBI " ^ (String.concat " " (List.map (string_of_expr ~verbose) args)) ^ ")"
  | ShiftRight, _ -> "(TBI " ^ (String.concat " " (List.map (string_of_expr ~verbose) args)) ^ ")"
and string_of_prover_type = function
  | ProverInt -> "int"
  | ProverBool -> "bool"
  | ProverReal -> "float"
  | ProverInductive -> "inductive"

(*
   free_vars contains the variable names that can be assigned in the e1 expression.
   assignments are the assignments the the variables imposed by the caller.
   assignments lhs must always be a subset of free_vars.
   assignments is add-only.
*)
let rec reducible_exprs verbose free_vars assignments e1 e2 =
  let pats_literal pats =
    List.for_all (function LitPat _ -> true | _ -> false ) pats
  in
  let get_lit_pat_exprs pats =
    pats |> List.map (function LitPat e -> e | _ -> failwith "non literal pattern")
  in
  let handle_pure_fun_call name1 name2 args1 args2 =
    if (not (String.equal name1 name2) ||
        List.length args1 != List.length args2) then
      None
    else
      List.fold_left2 (fun acc expr1 expr2 ->
          match acc with
          | Some assignments ->
            reducible_exprs verbose free_vars assignments expr1 expr2
          | None -> None)
        (Some assignments) args1 args2
  in
  let handle_call_with_pats name1 name2 pats1 pats2 =
    if (pats_literal pats1) && (pats_literal pats2) then
      handle_pure_fun_call
        name1 name2
        (get_lit_pat_exprs pats1)
        (get_lit_pat_exprs pats2)
    else None
  in
  match e1, e2 with
  | True _, True _ -> Some assignments
  | False _, False _ -> Some assignments
  | Null _, Null _ -> Some assignments
  | IntLit (_, value1, _, _, _),
    IntLit (_, value2, _, _, _)
  | IntLit (_, value1, _, _, _),
    WIntLit (_, value2)
  | WIntLit (_, value1),
    IntLit (_, value2, _, _, _)
  | WIntLit (_, value1),
    WIntLit (_, value2) ->
    if Big_int.eq_big_int value1 value2 then Some assignments else None
  | RealLit (_, value1),
    RealLit (_, value2) ->
    if value1 = value2 then Some assignments else None
  | ExprAsn (_, e1), _ -> reducible_exprs verbose free_vars assignments e1 e2
  | _, ExprAsn (_, e2) -> reducible_exprs verbose free_vars assignments e1 e2
  | Var (_, name1), Var (loc, name2)
  | Var (_, name1), WVar (loc, name2, _)
  | WVar (_, name1, _), Var (loc, name2)
  | WVar (_, name1, _), WVar (loc, name2, _) ->
    if (List.mem name1 free_vars) then begin
      match List.assoc_opt name1 assignments with
      | None -> Some ((name1, Var (loc, name2))::assignments)
      | Some Var (_, x)
      | Some WVar (_, x, _) -> if String.equal x name2 then Some assignments else None
      | Some _ -> None
    end else if String.equal name1 name2 then Some assignments else None
  | WVar (loc, name1, _), _
  | Var (loc, name1), _ ->
    if (List.mem name1 free_vars) then begin
      match List.assoc_opt name1 assignments with
      | None -> Some ((name1, e2)::assignments)
      | Some _ -> None
    end else None (* TODO: allow the case when the assignment is the same value (ignoring loc) *)
  | Operation (_, op1, exprs1), Operation (_, op2, exprs2)
  | Operation (_, op1, exprs1), WOperation (_, op2, exprs2, _)
  | WOperation (_, op1, exprs1, _), Operation (_, op2, exprs2)
  | WOperation (_, op1, exprs1, _), WOperation (_, op2, exprs2, _) ->
    if (op1 != op2 || List.length exprs1 != List.length exprs2) then None
    else
      List.fold_left2 (fun acc expr1 expr2 ->
          match acc with
          | Some assignments ->
            reducible_exprs verbose free_vars assignments expr1 expr2
          | None -> None)
        (Some assignments) exprs1 exprs2
  | WPureFunCall (_, name1, _, args1),
    CallExpr (_, name2, _, _, args2, _) ->
    if pats_literal args2 then
      handle_pure_fun_call name1 name2 args1 (get_lit_pat_exprs args2)
    else None
  | CallExpr (_, name1, _, _, args1, _),
    WPureFunCall (_, name2, _, args2) ->
    if pats_literal args1 then
      handle_pure_fun_call name1 name2 (get_lit_pat_exprs args1) args2
    else None
  | WPureFunCall (_, name1, _, args1),
    WPureFunCall (_, name2, _, args2) ->
    handle_pure_fun_call name1 name2 args1 args2
  | PredAsn (_, predref1, _, _, pat_list1),
    PredAsn (_, predref2, _, _, pat_list2)
  | PredAsn (_, predref1, _, _, pat_list1),
    WPredAsn (_, predref2, _, _, _, pat_list2)
  | WPredAsn (_, predref1, _, _, _, pat_list1),
    PredAsn (_, predref2, _, _, pat_list2)
  | WPredAsn (_, predref1, _, _, _, pat_list1),
    WPredAsn (_, predref2, _, _, _, pat_list2) ->
    handle_call_with_pats predref1#name predref2#name pat_list1 pat_list2
  | CallExpr (_, name1, _, _, pat_list1, _),
    WPredAsn (_, predref2, _, _, _, pat_list2) ->
    handle_call_with_pats name1 predref2#name pat_list1 pat_list2
  | WPredAsn (_, predref1, _, _, _, pat_list1),
    CallExpr (_, name2, _, _, pat_list2, _) ->
    handle_call_with_pats predref1#name name2 pat_list1 pat_list2
  | CallExpr (_, name1, _, _, pat_list1, _),
    PredAsn (_, predref2, _, _, pat_list2) ->
    handle_call_with_pats name1 predref2#name pat_list1 pat_list2
  | PredAsn (_, predref1, _, _, pat_list1),
    CallExpr (_, name2, _, _, pat_list2, _) ->
    handle_call_with_pats predref1#name name2 pat_list1 pat_list2
  | _, _ ->
    if verbose then
      Printf.printf "mismatch %s ~~~ %s\n"
        (string_of_expr ~verbose:true e1)
        (string_of_expr ~verbose:true e2);
    None
