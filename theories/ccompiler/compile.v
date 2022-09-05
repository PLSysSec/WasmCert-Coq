Require Import Coq.ZArith.BinInt.
From Wasm Require Import datatypes.
From Wasm Require Import ccompiler.num_conv.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.

Definition compile_value_type (t : value_type) : Ctypes.type :=
  match t with
  | T_i32 => Tint I32 Unsigned noattr
  | T_i64 => Tlong Unsigned noattr
  | T_f32 => Tfloat F32 noattr
  | T_f64 => Tfloat F64 noattr
  end.

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
  : option Clight.statement :=
  let t : type := compile_value_type vt in
  match o with
  | Unop_f UOF_neg => Some (Sset r (Eunop Oneg (Etempvar x t) t))
  | _ => None
  end.

Definition compile_binop (vt : value_type) (o : binop) (r x y : ident)
  : option Clight.statement :=
  let t : type := compile_value_type vt in
  match o with
  | Binop_i BOI_add => Some (Sset r (Ebinop Oadd (Etempvar x t) (Etempvar y t) t))
  | _ => None
  end.
