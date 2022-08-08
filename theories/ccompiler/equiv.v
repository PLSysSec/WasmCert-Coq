Require Import Coq.Lists.List.
Import ListNotations.
From mathcomp Require Import ssreflect eqtype seq.
From Wasm Require Import datatypes opsem typing.
From Wasm Require Import ccompiler.compile ccompiler.num_conv.
From Wasm Require Import type_preservation.
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

Ltac some_equational :=
  repeat progress match goal with
    | [ _ : Some _ = None |- _ ] => discriminate
    | [ _ : None = Some _ |- _ ] => discriminate
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    end.

Ltac to_e_list_destruct :=
  repeat progress match goal with
    | [ H : to_e_list ?l = cons _ _ |- _ ] => destruct l; simpl in H; try discriminate; inversion H; clear H; subst
    | [ H : to_e_list ?l = [] |- _ ] => destruct l; simpl in H; try discriminate
    | [ H : [] = [] |- _ ] => clear H
    end.

Ltac invert_be_typing:=
  repeat match goal with
  | H: (?es ++ [::?e])%list = [::_] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _; _] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _; _; _] |- _ =>
    extract_listn
  | H: be_typing _ [::] _ |- _ =>
    apply empty_typing in H; subst
  | H: be_typing _ [:: BI_const _] _ |- _ =>
    apply BI_const_typing in H; subst
  | H: be_typing _ [:: BI_const _; BI_const _] _ |- _ =>
    apply BI_const2_typing in H; subst
  | H: be_typing _ [:: BI_const _; BI_const _; BI_const _] _ |- _ =>
    apply BI_const3_typing in H; subst
  | H: be_typing _ [::BI_unop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Unop_typing in H; destruct H as [H1 [ts H2]]; subst
  | H: be_typing _ [::BI_binop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Binop_typing in H; destruct H as [H1 [ts H2]]; subst
  | H: be_typing _ [::BI_testop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Testop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_relop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Relop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_cvtop _ _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Cvtop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_drop] _ |- _ =>
    apply Drop_typing in H; destruct H; subst
  | H: be_typing _ [::BI_select] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Select_typing in H; destruct H as [ts [t [H1 H2]]]; subst
  | H: be_typing _ [::BI_if _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply If_typing in H; destruct H as [ts [H1 [H2 [H3 H4]]]]; subst
  | H: be_typing _ [::BI_br_if _] _ |- _ =>
    let ts := fresh "ts" in
    let ts' := fresh "ts'" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Br_if_typing in H; destruct H as [ts [ts' [H1 [H2 [H3 H4]]]]]; subst
  | H: be_typing _ [::BI_br_table _ _] _ |- _ =>
    let ts := fresh "ts" in
    let ts' := fresh "ts'" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Br_table_typing in H; destruct H as [ts [ts' [H1 H2]]]; subst
  | H: be_typing _ [::BI_tee_local _] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Tee_local_typing in H; destruct H as [ts [t [H1 [H2 [H3 H4]]]]]; subst
  | H: be_typing _ (_ ++ _) _ |- _ =>
    let ts1 := fresh "ts1" in
    let ts2 := fresh "ts2" in
    let ts3 := fresh "ts3" in
    let ts4 := fresh "ts4" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply composition_typing in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]]
  | H: be_typing _ [::_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: _ ++ [::_] = _ ++ [::_] |- _ =>
    apply concat_cancel_last in H; destruct H; subst
  | H : be_typing _ _ ?ft |- _ =>
    is_var ft; destruct ft
  end.

Lemma f32_neg : forall s : Floats.float32, Floats.Float32.neg s = Wasm_float.Float32.fneg s.
Proof.
Admitted.
Lemma f64_neg : forall s : Floats.float, Floats.Float.neg s = Wasm_float.Float64.fneg s.
Proof.
Admitted.

(* TODO: reflexive transitive closure of Clight.step *)
Lemma unop_equiv :
  forall (ge : genv) (function_entry : function -> list val -> mem -> env -> temp_env -> mem -> Prop) (f : function) (k : cont) (e : env) (m : mem)
         (vt : value_type) (u : unop) (r : ident) (x : ident) (v v' : value)
         (le : temp_env) (s : statement)
         (bi : list basic_instruction) (ai' : list administrative_instruction) (ft : function_type) (host_function : eqType) (sr : store_record host_function) (C : t_context),
  unop_type_agree vt u ->
  bi = [BI_const v; BI_unop vt u] ->
  ai' = to_e_list [BI_const v'] ->
  reduce_simple (to_e_list bi) ai' ->
  be_typing C bi ft ->
  compile_unop vt u r x = Some s ->
  PTree.get x le = Some (val_equiv v) ->
  exists (s' : statement) (le' : temp_env),
  step ge function_entry (State f s k e le m) E0 (State f s' k e le' m) /\
  PTree.get r le' = Some (val_equiv v').
Proof.
  intros.
  exists Sskip.
  exists (PTree.set r (val_equiv v') le).

  split; try solve [ apply PTree.gss ].
  destruct u as [[] | []]; unfold compile_unop in *; some_equational. (* TODO: remove when totalizing *)
  apply step_set; eapply eval_Eunop; try solve [ eauto using eval_expr ]. (* TODO: tactify the eval *)
  - destruct vt; simpl; match goal with [ H : unop_type_agree _ _ |- _ ] => inversion H; clear H; subst end;
    invert_be_typing; destruct v; simpl in *; try discriminate;
    match goal with [ H : reduce_simple _ _ |- _ ] => inversion H; clear H; subst end;
    unfold sem_neg; simpl; f_equal; f_equal; auto using f32_neg, f64_neg.
Qed.
