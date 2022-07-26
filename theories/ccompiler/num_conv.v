From Wasm Require Import numerics.
From compcert Require Import Integers.

Definition int_of (x : Wasm_int.Int32.int) : int :=
  Integers.Int.mkint
    (Wasm_int.Int32.intval x) (Wasm_int.Int32.intrange x).

Definition long_of (x : Wasm_int.Int64.int) : int64 :=
  Integers.Int64.mkint
    (Wasm_int.Int64.intval x) (Wasm_int.Int64.intrange x).
