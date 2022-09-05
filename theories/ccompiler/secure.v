Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
From Wasm Require Import ccompiler.compile.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.common.Events.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.

Section SEMANTICS.

Variable ge : genv.

Definition function_entry : function -> list val -> mem -> env -> temp_env -> mem -> Prop :=
  function_entry2 ge.

Definition step := step ge function_entry.

Inductive valid : state -> Prop :=
  | valid_final : forall (s : state) (x : int), final_state s x -> valid s
  | valid_step : forall (s1 s2 : state) (e : trace), step s1 e s2 -> valid s2 -> valid s1
  .

Definition well_defined (p : Clight.program) : Prop :=
  forall (s : state), initial_state p s -> valid s.

Program Definition simple_program (f : function) : Clight.program :=
  {|
    prog_defs := [(1%positive, Gfun (Internal f))];
    prog_public := [1%positive];
    prog_main := 1%positive;
    prog_types := [];
    prog_comp_env := PTree.empty _;
    prog_comp_env_eq := _
  |}.

Definition trivial_function : function :=
  {|
    fn_return := Tint I32 Signed noattr;
    fn_callconv := cc_default;
    fn_params := [];
    fn_vars := [];
    fn_temps := [];
    fn_body := Sreturn (Some (Econst_int (Int.repr 0%Z) (Tint I32 Signed noattr)))
  |}.

Ltac some_equational :=
  repeat progress
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    end.

Import Globalenvs.Genv.
Import Coqlib.

Lemma nil_disjoint : forall A : Type, @list_disjoint A [] [].
Proof.
  intros.
  unfold list_disjoint.
  intros.
  unfold In in H0.
  inversion H0.
Qed.

Theorem trivial_function_ok : well_defined (simple_program trivial_function).
Proof.
  unfold well_defined.
  intros.
  destruct H.
  subst ge0.
  unfold find_symbol in H0.
  simpl in H0.
  rewrite PTree.gss in H0.
  some_equational.
  subst b.
  unfold find_funct_ptr in H1.
  simpl in H1.
  some_equational.
  subst f.
  eapply valid_step.
  1:{
    unfold step.
    apply step_internal_function.
    unfold function_entry.
    apply function_entry2_intro; unfold trivial_function; simpl.
    - apply list_norepet_nil.
    - apply list_norepet_nil.
    - apply nil_disjoint.
    - apply alloc_variables_nil.
    - eauto.
  }
  eapply valid_step.
  1:{
    simpl.
    eapply step_return_1.
    - apply eval_Econst_int.
    - simpl.
      unfold Cop.sem_cast.
      simpl.
      destruct Archi.ptr64.
      + eauto.
      + eauto.
    - simpl. eauto.
  }
  eapply valid_final.
  apply final_state_intro.
Qed.
