From Wasm Require Import datatypes.
From Wasm Require Import ccompiler.compile.
Require Import compcert.lib.Integers.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.AST.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.

Definition val_equiv (v : value) : val :=
  match v with
  | VAL_int32 x => Vint (Integers.Int.mkint (Wasm_int.Int32.intval x) (Wasm_int.Int32.intrange x))
  | VAL_int64 x => Vlong (Integers.Int64.mkint (Wasm_int.Int64.intval x) (Wasm_int.Int64.intrange x))
  | VAL_float32 x => Vsingle x
  | VAL_float64 x => Vfloat x
  end.

Lemma lit_equiv :
  forall (ge : genv) (e : env) (te : temp_env) (m : mem),
  forall (c : value),
  eval_expr ge e te m (fst (compile_const' c)) (val_equiv c).
Proof.
  intros; unfold compile_const'; destruct c; eauto using eval_expr.
Qed.
