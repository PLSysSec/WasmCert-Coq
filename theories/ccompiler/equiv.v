Require Import Coq.Lists.List.
Import ListNotations.
From mathcomp Require Import eqtype.
From Wasm Require Import datatypes opsem typing.
From Wasm Require Import ccompiler.compile ccompiler.num_conv.
Require Import compcert.lib.Integers.
Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Cop.
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
         (le : temp_env) (s : statement)
         (ai ai' : list administrative_instruction) (ft : function_type) (host_function : eqType) (sr : store_record host_function) (C : t_context),
  unop_type_agree vt u ->
  ai = [AI_basic (BI_const v); AI_basic (BI_unop vt u)] ->
  ai' = [AI_basic (BI_const v')] ->
  reduce_simple ai ai' ->
  e_typing sr C ai ft ->
  e_typing sr C ai' ft ->
  compile_unop vt u r x = Some s ->
  PTree.get x le = Some (val_equiv v) ->
  exists (s' : statement) (le' : temp_env),
  step ge function_entry (State f s k e le m) E0 (State f s' k e le' m) /\
  PTree.get r le' = Some (val_equiv v').
Proof.
  intros.
  exists Sskip.
  exists (PTree.set r (val_equiv v') le).
  split. 2: apply PTree.gss.
  destruct u; destruct u; unfold compile_unop in H5; try discriminate. (* TODO: remove when totalizing *)
  inversion H5. clear H5.
  apply step_set.
  apply eval_Eunop with (v1:=val_equiv v).
  2: {
    unfold sem_unary_operation.
    unfold sem_neg.
    unfold classify_neg.
    unfold compile_value_type.
    unfold typeof.
    destruct vt; inversion H; clear op H5.
    destruct v. inversion H3. clear s1 C0 H7 H9 H11 tf.
    rewrite H0 in H10. unfold to_e_list in H10.  destruct bes.
    { unfold seq.map in H10. discriminate. }
    rewrite map_cons in H10. destruct bes.
    { unfold seq.map in H10. discriminate. }
    rewrite map_cons in H10. destruct bes.
    2: { rewrite map_cons in H10. discriminate. }
    inversion H10. rewrite H9 in H5. rewrite H11 in H5. clear H9 H10 H11 b b0.
    inversion H5. clear H10 C0.
    unfold app in H7. destruct es.
    { discriminate. }
    destruct es.
    2: { destruct es; discriminate. } 
    inversion H7. rewrite H13 in H9. rewrite H14 in H11. clear b e0 H13 H14 H7.
    inversion H9. inversion H11. rewrite <- H19 in H15. discriminate.
    }
