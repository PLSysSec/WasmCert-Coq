Require Import Coq.Lists.List.
Import ListNotations.
From Wasm Require Import datatypes opsem.
From Wasm Require Import ccompiler.compile ccompiler.num_conv.
Require Import compcert.lib.Integers.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.AST.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.common.Events.
Require Import compcert.lib.Maps.

Definition val_equiv (v : value) : val :=
  match v with
  | VAL_int32 x => Vint (int_of x)
  | VAL_int64 x => Vlong (long_of x)
  | VAL_float32 x => Vsingle x
  | VAL_float64 x => Vfloat x
  end.

Lemma value_equiv :
  forall (ge : genv) (e : env) (le : temp_env) (m : mem),
  forall c : value,
  eval_expr ge e le m (compile_value c) (val_equiv c).
Proof.
  intros. unfold compile_value. destruct c; eauto using eval_expr.
Qed.

  (* TODO: reflexive transitive closure of Clight.step *)
Lemma unop_equiv :
  forall (ge : genv) (function_entry : function -> list val -> mem -> env -> temp_env -> mem -> Prop) (f : function) (k : cont) (e : env) (m : mem)
         (vt : value_type) (u : unop) (r : ident) (x : ident) (v v' : value)
         (le : temp_env) (s : statement),
  reduce_simple [AI_basic (BI_const v); AI_basic (BI_unop vt u)]
                [AI_basic (BI_const v')] ->
  compile_unop vt u r x = Some s ->
  PTree.get x le = Some (val_equiv v) ->
  exists (s' : statement) (le' : temp_env),
  step ge function_entry (State f s k e le m) E0 (State f s' k e le' m) /\
  PTree.get r le' = Some (val_equiv v').
Proof.
  intros.
  exists Sskip.
  exists (PTree.set r (val_equiv v') le).
  split.
  2: apply PTree.gss.
  destruct u.
  - admit.
  - admit.
