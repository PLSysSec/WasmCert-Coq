From Wasm Require Import numerics datatypes.
From compcert Require Import Integers.

Definition int_of (x : Wasm_int.Int32.int) : int :=
  Integers.Int.mkint
    (Wasm_int.Int32.intval x) (Wasm_int.Int32.intrange x).

Definition long_of (x : Wasm_int.Int64.int) : int64 :=
  Integers.Int64.mkint
    (Wasm_int.Int64.intval x) (Wasm_int.Int64.intrange x).

Definition type_of_value (x : value) : value_type :=
  match x with
  | VAL_int32 _ => T_i32
  | VAL_int64 _ => T_i64
  | VAL_float32 _ => T_f32
  | VAL_float64 _ => T_f64
  end.
