Require Import Coq.ZArith.BinInt.
From Wasm Require Import datatypes.
From Wasm Require Import ccompiler.num_conv.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.

Scheme Equality for prod.
Scheme Equality for Z.

Definition compile_value_type (t : value_type) : Ctypes.type :=
  match t with
  | T_i32 => Tint I32 Unsigned noattr
  | T_i64 => Tlong Unsigned noattr
  | T_f32 => Tfloat F32 noattr
  | T_f64 => Tfloat F64 noattr
  end.

(* TODO: make the conversions between Wasm and Compcert ints cleaner *)
Definition compile_value (v : value) : Clight.expr :=
  match v with
  | VAL_int32 x =>
      let t' := compile_value_type T_i32 in
        Econst_int (int_of x) t'
  | VAL_int64 x =>
      let t' := compile_value_type T_i64 in
        Econst_long (long_of x) t'
  | VAL_float32 x =>
      let t' := compile_value_type T_f32 in
      Econst_single x t'
  | VAL_float64 x =>
      let t' := compile_value_type T_f64 in
      Econst_float x t'
  end.

Definition compile_const (v : value) (r : ident) : Clight.statement :=
  Sset r (compile_value v).

Definition compile_unop (vt : value_type) (u : unop) (r : ident) (x : ident)
  : option Clight.statement :=
  match u with
  | Unop_f UOF_neg =>
      let t : type := compile_value_type vt in
      Some (Sset r (Eunop Oneg (Etempvar x t) t))
  | _ => None
  end.

(*
Module Type UNIQUE.
  Parameter t : Set.
  Parameter eqb : t -> t -> bool.
End UNIQUE.

Module Unique(Import U : UNIQUE).
  Definition store : Type := list t.
  Fixpoint get_go (i : positive) (x : t) (s : store) : positive * store :=
    match s with
    | nil => (i, cons x nil)
    | cons y s' =>
        if eqb x y
        then (i, s')
        else let (i', s'') := get_go (Pos.succ i) x s'
        in (i', cons y s'')
    end.
  Definition get : t -> store -> positive * store := get_go 1.
End Unique.

Module VarUNIQUE <: UNIQUE.
  Definition t : Set := value_type * Z.
  Definition eqb : t -> t -> bool := prod_beq value_type Z value_type_beq Z_beq.
End VarUNIQUE.

Module VarUnique := Unique(VarUNIQUE).

Definition var (t : value_type) (i : Z) (s : VarUnique.store)
  : ident * VarUnique.store :=
  VarUnique.get (t, i) s.
*)
