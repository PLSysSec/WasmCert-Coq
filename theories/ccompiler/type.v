Require Import Wasm.datatypes.
Require Import compcert.cfrontend.Ctypes.

Definition compile_value_type (t : value_type) : Ctypes.type :=
  match t with
  | T_i32 => Tint I32 Unsigned noattr
  | T_i64 => Tlong Unsigned noattr
  | T_f32 => Tfloat F32 noattr
  | T_f64 => Tfloat F64 noattr
  end.
