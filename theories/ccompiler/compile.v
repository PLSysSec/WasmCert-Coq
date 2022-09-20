Require Import Program.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.
Require Import Wasm.datatypes.
Require Import Wasm.typing.
Require Import Wasm.ccompiler.num_conv.
Require Import Wasm.ccompiler.type.
Require Import Wasm.ccompiler.stack.

(* While this compiler is incomplete, all unfinished portions will be stubbed
 * out rather than produce errors.
 *
 * This is because the finished compiler will, if all goes as planned, not fail
 * on any input -- instead it will use preconditions such as "well-typed".
 * 
 * As such, it would be unnecessarily complicated to manipulate `option`s.
 *)

Definition compile_value (v : value) : Clight.expr :=
  let t := compile_value_type (type_of_value v) in
  match v with
  | VAL_int32 x => Econst_int (int_of x) t
  | VAL_int64 x => Econst_long (long_of x) t
  | VAL_float32 x => Econst_single x t
  | VAL_float64 x => Econst_float x t
  end.

Definition compile_const (v : value) (r : ident) : Clight.statement :=
  Sset r (compile_value v).

Definition compile_unop (vt : value_type) (o : unop) (r x: ident)
  : Clight.statement :=
  let t : type := compile_value_type vt in
  match o with
  | Unop_f UOF_neg => Sset r (Eunop Oneg (Etempvar x t) t)
  | _ => Sskip (* TODO *)
  end.

Definition compile_binop (vt : value_type) (o : binop) (r x y : ident)
  : Clight.statement :=
  let t : type := compile_value_type vt in
  match o with
  | Binop_i BOI_add => Sset r (Ebinop Oadd (Etempvar x t) (Etempvar y t) t)
  | _ => Sskip (* TODO *)
  end.

Program Definition compile_instr
  (ctx : t_context)
  (i : basic_instruction)
  (ft : function_type)
  (has_ty : be_typing ctx [i] ft)
  (s : stack)
  (s_correct : stack_typing s (fun_input ft))
  : Clight.statement * { s : stack | stack_typing s (fun_output ft) } :=
  (Sskip, _).

Record static : Type :=
  { t_ctx : t_context
  ; input : expr
  ; type : function_type
  ; well_typed : be_typing t_ctx input type
  }.

Record accum : Type :=
  { bkg : static
  ; left : expr (* NOT reversed *)
  (*
  ; ty_left : function_type
  ; left_typed : be_typing bkg.(t_ctx) left ty_left
  ; left_matches : fun_input ty_left = fun_input bkg.(type)
   *)
  ; right : expr
  ; zipper : left ++ right = bkg.(input)
  ; result : statement
  ; stack_ty : stack
  }.

Definition basic_t_context (ft : function_type) : t_context :=
  {| tc_types_t := []
   ; tc_func_t := []
   ; tc_global := []
   ; tc_table := []
   ; tc_memory := []
   ; tc_local := []
   ; tc_label := []
   ; tc_return := let (_, o) := ft in Some o
   |}.

Definition initial_accum (input : expr) (type : function_type) (well_typed : be_typing (basic_t_context type) input type) : accum :=
  {| bkg :=
       {| t_ctx := basic_t_context type
        ; input := input
        ; type := type
        ; well_typed := well_typed
        |}
   ; left := []
   ; right := input
   ; zipper := ltac:(auto)
   ; result := Sskip
   ; stack_ty := empty_stack
   |}.

Program Fixpoint compile_expr_go (a : accum) {measure (length a.(right))}
: { a : accum | a.(right) = [] } :=
  match a.(right) with
  | [] => a
  | i :: is =>
      let
        foo := 1
      in
        compile_expr_go
          {| bkg := a.(bkg)
           ; left := a.(left) ++ [i]
           ; right := is
           ; zipper := _
           ; result := a.(result)
           ; stack_ty := a.(stack_ty)
           |}
  end.
Obligation 2 of compile_expr_go.
  rewrite <- a.(zipper).
  rewrite <- Heq_anonymous.
  remember (left a) as l.
  rewrite <- app_assoc.
  simpl.
  reflexivity.
Qed.
