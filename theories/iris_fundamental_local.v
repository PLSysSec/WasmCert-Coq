From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules.
Require Export datatypes host operations properties opsem typing.
Require Export iris_logrel iris_fundamental_helpers.
Import uPred.

Section fundamental.
  Import DummyHosts. (* placeholder *)

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !wtablimitG Σ, !wmemlimitG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Lemma interp_instance_change_label lbs C i :
    interp_instance (HWP:=HWP) C i -∗ interp_instance (HWP:=HWP) (upd_label C lbs) i.
  Proof. destruct C,i;simpl. auto. Qed.

  Lemma interp_instance_change_return ret C i :
    interp_instance (HWP:=HWP) C i -∗ interp_instance (HWP:=HWP) (upd_return C ret) i.
  Proof. destruct C,i;simpl. auto. Qed.

  Lemma interp_instance_change_local locs C i :
    interp_instance (HWP:=HWP) C i -∗ interp_instance (HWP:=HWP) (upd_local C locs) i.
  Proof. destruct C,i;simpl. auto. Qed.
  
  (* ----------------------------------------- LOCAL --------------------------------------- *)

  Lemma typing_local C es τ1 τ2 τs :
    (∀ C es τ, be_typing C es τ -> ⊢ semantic_typing (HWP:=HWP) C (to_e_list es) τ) ->
    (tc_label C) = [] ∧ (tc_return C) = None ->
    be_typing (upd_local (upd_label (upd_return C (Some τ2)) [τ2]) (τ1 ++ τs)) es (Tf [] τ2) ->
    ⊢ semantic_typing_local (HWP:=HWP) C es τs (Tf τ1 τ2).
  Proof.
    intros be_fundamental Hnil Htyping.
    iSplit;[auto|].
    iIntros (i) "#Hi". iIntros (f vs) "Hf Hown #Hv".
    apply be_fundamental in Htyping.
    iDestruct (Htyping) as "Ht".
    iDestruct (interp_instance_change_label [τ2] with "Hi") as "Hi'".
    iDestruct (interp_instance_change_return (Some τ2) with "Hi'") as "Hi''".
    iDestruct (interp_instance_change_local τ1 with "Hi''") as "Hi_final".
    iSpecialize ("Ht" $! _ (LH_rec [] (length τ2) [] (LH_base [] []) []) with "[$Hi_final] []").
    { unfold interp_ctx. iSimpl. repeat (iSplit;[by auto|]).
      iSplit =>//. unfold interp_ctx_continuation.
      iSimpl. iExists _,_,_,_,_,(LH_base [] []). iSplit;[eauto|].
      repeat (iSplit;[by auto|]). iModIntro.
      iIntros (v f') "#Hv' [Hf' Hfv']".
      iExists τ2. rewrite app_nil_l !app_nil_r.
      iApply wp_value;[done|].
      iSplitR;[|iExists _;iFrame].
      iLeft. iFrame "Hv'". }

    unfold interp_expression_closed.
    iApply (wp_frame_bind with "Hf").
    iIntros "Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_label_bind.
    iDestruct ("Ht" $! _ (immV []) with "[$Hf Hown] []") as "Hcont".
    { iExists _. iFrame. iSplit;eauto. }
    { iRight. iExists _. iSplit;eauto. }
    iSimpl in "Hcont". unfold interp_expression.

    iApply (wp_wand with "Hcont").
    iClear "Ht".
    iIntros (v) "[Hv' Hf0]".
    iDestruct "Hf0" as (f0) "[Hf0 Hf0v]".
    iDestruct "Hv'" as "[[-> | Hv'] | [Hbr | Hret]]";simpl language.of_val.
    { rewrite -(app_nil_l [AI_trap]) -(app_nil_r [AI_trap]).
      iApply (wp_wand_ctx _ _ _ (λ vs, _ ∗ ↪[frame] _)%I with "[Hf0]").
      { iApply wp_trap_ctx;eauto. }
      iIntros (v) "[-> Hf]".
      iExists _. iFrame. iIntros "Hf".
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗ ↪[frame] _)%I with "[Hf]").
      { iApply (wp_frame_trap with "Hf");eauto. }
      iIntros (v) "[-> Hf]".
      iFrame.
      iDestruct "Hf0v" as (?) "[_ [_ Hown]]". iFrame.
      by iLeft. }
    
    { iDestruct "Hv'" as (v' ->) "#Hv'".
      iSimpl.
      iApply (wp_wand_ctx _ _ _ (λ vs, ⌜vs = immV _⌝ ∗ ↪[frame] _)%I with "[Hf0]").
      { iApply (wp_val_return with "Hf0");[apply v_to_e_is_const_list|].
        iIntros "Hf".
        rewrite app_nil_l app_nil_r.
        rewrite of_val_imm.
        iApply wp_value;[done|].
        iFrame. eauto. }
      iIntros (v) "[-> Hf]".
      iExists _. iFrame. iIntros "Hf".
      iDestruct (big_sepL2_length with "Hv'") as %Hlen.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = immV _⌝ ∗ ↪[frame] _)%I with "[Hf]").
      { iApply (wp_frame_value with "Hf");eauto. 1: apply to_of_val.
        rewrite fmap_length. auto. }
      iIntros (v) "[-> Hf]". iFrame.
      iDestruct "Hf0v" as (?) "[_ [_ Hown]]".
      iFrame. iRight. iExists _. eauto. }
    
    { rewrite fixpoint_interp_br_eq.
      iDestruct "Hbr" as (n vh vs' p -> Hbase Hdepth) "Hbr".
      apply lh_depth_ge in Hdepth as Hle.
      iDestruct "Hbr" as (τs' ws' k es1 lh' es' lh'' τs'' Hlook Hlayer) "Hbr".
      iDestruct "Hbr" as (Hdepth' Hmin) "[#Hws' _]".
      simpl in Hlayer.
      destruct (n - p) eqn:Heqnp;[|simplify_eq].
      assert (n = p) as HH;[lia|]. simpl of_val.
      simplify_eq.
      destruct Hmin as [lh3 Hmin%lh_minus_Ind_Equivalent].
      inversion Hmin;simplify_eq. simpl lh_depth.
      pose proof (vfill_to_lfilled vh [AI_basic (BI_br p)]) as [_ Hfill].
      (* apply lfilled_depth in Hfill as Hdepth''. *)
      replace (lh_depth (lh_of_vh vh)) with (iris.lh_depth (lh_of_vh vh)) in Hdepth ;
        last done. rewrite Hdepth in Hfill. 
      iDestruct "Hws'" as "[%Hcontr|Hws']";[done|iDestruct "Hws'" as (ww Heqw) "Hws'"].
      iDestruct (big_sepL2_length with "Hws'") as %Hlen. rewrite !app_length in Hlen.
      rewrite -(take_drop (length (τs'')) ww). inversion Heqw.
      rewrite -(take_drop (length (τs'')) ww) in H0.
      eapply lfilled_get_base_pull in H0 as [lh' Hlh'];[|eauto].
      iIntros (LI Hfill'%lfilled_Ind_Equivalent). inversion Hfill';simplify_eq.
      inversion H8;simplify_eq. repeat erewrite app_nil_l,app_nil_r.      
      iDestruct (big_sepL2_app_inv with "Hws'") as "[Hws1 Hws2]".
      { right. rewrite drop_length. lia. }
      iDestruct (big_sepL2_length with "Hws2") as %Hlen2.
      simpl in Hlook. inversion Hlook;subst τs'.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = immV _⌝ ∗ ↪[frame] _)%I with "[Hf0]").
      { iApply (wp_br with "Hf0") ;[| |apply Hlh'|];[apply const_list_of_val|by rewrite /= fmap_length|].
        iNext. iIntros "Hf". rewrite app_nil_r.
        iApply wp_value;[done|].
        iFrame;eauto. }
      iIntros (v) "[-> Hf]".
      iExists _. iFrame. iIntros "Hf".
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = immV _⌝ ∗ ↪[frame] _)%I with "[Hf]").
      { iApply (wp_frame_value with "Hf");eauto. 1: apply to_of_val.
        rewrite fmap_length. auto. }
      iIntros (v) "[-> Hf]". iFrame.
      iDestruct "Hf0v" as (?) "[_ [_ Hown]]". iFrame.
      iRight. iExists _. eauto. }
    
    { iDestruct "Hret" as (vh vs' -> Hbase) "Hret".
      iDestruct "Hret" as (τs'') "[#Hws' _]".
      iDestruct "Hws'" as "[%Hcontr|Hws']";[done|iDestruct "Hws'" as (ww Heqw) "Hws'"].
      iDestruct (big_sepL2_length with "Hws'") as %Hlen. rewrite !app_length in Hlen.
      rewrite -(take_drop (length (τs'')) ww). inversion Heqw.
      rewrite -(take_drop (length (τs'')) ww) in H0. rewrite H0 in Hbase.
      iDestruct (big_sepL2_app_inv with "Hws'") as "[Hws1 Hws2]".
      { right. rewrite drop_length. lia. }
      iDestruct (big_sepL2_length with "Hws2") as %Hlen2.
      simpl of_val.
      pose proof (sfill_to_lfilled vh [AI_basic BI_return]) as Hfill.
      eapply lfilled_simple_get_base_pull in Hbase as [lh' Hlh'];[|eauto].
      iIntros (LI Hfill'%lfilled_Ind_Equivalent). inversion Hfill';simplify_eq.
      inversion H9;simplify_eq. repeat erewrite app_nil_l,app_nil_r.
      rewrite sfill_label.
      eassert (of_val (retV _) = sfill _ _) as <-;[eauto|].
      iApply wp_value;[done|].
      iExists _. iFrame. iIntros "Hf".
      simpl of_val.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = immV _⌝ ∗ ↪[frame] _)%I with "[Hf]").
      { iApply wp_return;cycle 2.
        { rewrite -(app_nil_l [AI_label _ _ _])  -(app_nil_r [AI_label _ _ _]).
          apply lfilled_Ind_Equivalent. constructor;auto.
          apply lfilled_Ind_Equivalent. apply Hlh'. }
        { iApply wp_value;[done|]. iFrame;eauto. }
        { apply to_of_val. }
        { rewrite fmap_length. auto. } }
      iIntros (v) "[-> Hf]". iFrame.
      iSplitR;[iRight;iExists _;eauto|].
      iDestruct "Hf0v" as (?) "[_ [_ Hown]]". iFrame. }
  Qed.    

End fundamental.
