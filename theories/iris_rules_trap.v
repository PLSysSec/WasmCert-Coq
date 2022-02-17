From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export datatypes host operations properties opsem iris_rules_control iris_properties.
Require Export iris_wp_def stdpp_aux.

(* empty lists, frame and context rules *)

Close Scope byte_scope.

Section trap_rules.
  Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

  Let val := iris.val.
  Let expr := iris.expr.
  Let to_val := iris.to_val.

  Lemma wp_trap (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (vs1 es2 : expr) f :
    const_list vs1 ->
    Φ trapV -∗
    ↪[frame] f -∗
    WP vs1 ++ [AI_trap] ++ es2 @ s; E {{ v, Φ v ∗ ↪[frame] f }}.
  Proof.
    iLöb as "IH" forall (s E vs1 es2 f). 
    iIntros (Hconst) "HΦ Hf".
    destruct (iris.to_val (vs1 ++ [AI_trap] ++ es2)) eqn:Hsome.
    { destruct vs1,es2 =>//;[|by erewrite to_val_not_trap_interweave in Hsome;auto..].
      rewrite app_nil_l app_nil_r.
      iApply wp_value;[|iFrame]. done. }
    iApply wp_unfold.
    repeat rewrite /wp_pre /=.
    rewrite Hsome.
    iIntros (σ ns κ κs nt) "Hσ".
    iApply fupd_frame_l.
    iSplit.
    { iPureIntro.
      destruct s =>//.
      unfold iris_wp_def.reducible, reducible.
      eexists _,[AI_trap],σ,_.
      destruct σ as [[[? ?]?]?]. simpl.
      repeat split;eauto.
      eapply r_simple,rs_trap.
      2: instantiate (1 := LH_base vs1 es2);apply lfilled_Ind_Equivalent;by constructor.
      destruct vs1,es2 =>//; destruct vs1 =>//. }
    { iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls".
      iIntros (e2 σ2 efs Hstep).
      iModIntro. iNext. iModIntro.
      iMod "Hcls". iModIntro.
      assert (lfilled 0 (LH_base vs1 es2) [AI_trap] (vs1 ++ (AI_trap :: es2))) as Hfill.
      { apply lfilled_Ind_Equivalent. constructor. done. }
      destruct σ as [[[? ?]?]?].
      destruct σ2 as [[[? ?]?]?].
      simpl in *. destruct Hstep as [Hstep [-> ->]].
      eapply trap_reduce in Hstep as Hred;[|apply Hfill].
      destruct Hred as [lh' [Hfill' Heq]]. simplify_eq.
      iApply bi.sep_exist_l. iExists _. iFrame. iSplit =>//.
      iIntros "Hf".
      apply lfilled_Ind_Equivalent in Hfill';inversion Hfill';subst.
      iApply ("IH" with "[] HΦ Hf"). auto.
    }
  Qed.
  

  Lemma wp_seq_trap (s : stuckness) (E : coPset) (es1 es2 : language.expr wasm_lang) f f' :
    ↪[frame] f ∗
     (↪[frame] f -∗ WP es1 @ s; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }})
     ⊢ WP (es1 ++ es2) @ s; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}.
  Proof.
    iIntros "[Hf Hes1]".
    iLöb as "IH" forall (s E es1 es2 f f').
    iApply wp_unfold.
    repeat rewrite wp_unfold /wp_pre /=.
    destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
    {
      destruct vs.
      {
        apply to_val_cat in Hetov as [-> Hev2].
        apply iris.of_to_val in Hev2 as <-.
        iMod ("Hes1" with "Hf") as "[%Hcontr _]". done.
      }
      {
        apply to_val_trap_is_singleton in Hetov.
        apply app_eq_singleton in Hetov as [[-> ->]|[-> ->]].
        all:iMod ("Hes1" with "Hf") as "[%Hcontr Hf]"; try done. auto.
      }
    }
    (* Ind *)
    iIntros (σ ns κ κs nt) "Hσ".
    destruct (iris.to_val es1) as [vs|] eqn:Hes.
    { apply of_to_val in Hes as <-.
    iMod ("Hes1" with "Hf") as "[%Heq Hf]". subst.
    iApply fupd_frame_l.
    iSplit.
    { iPureIntro.
      destruct s =>//.
      unfold iris_wp_def.reducible, reducible.
      eexists _,[AI_trap],σ,_.
      destruct σ as [[[? ?]?]?]. simpl.
      repeat split;eauto.
      eapply r_simple,rs_trap.
      2: instantiate (1 := LH_base [] es2);apply lfilled_Ind_Equivalent;by constructor.
      destruct es2 =>//. }
    { iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls".
      iIntros (e2 σ2 efs Hstep).
      iModIntro. iNext. iModIntro.
      iMod "Hcls". iModIntro.
      assert (lfilled 0 (LH_base [] es2) [AI_trap] (of_val trapV ++ es2)) as Hfill.
      { apply lfilled_Ind_Equivalent. constructor. done. }
      destruct σ as [[[? ?]?]?].
      destruct σ2 as [[[? ?]?]?].
      simpl in *. destruct Hstep as [Hstep [-> ->]].
      eapply trap_reduce in Hstep as Hred;[|apply Hfill].
      destruct Hred as [lh' [Hfill' Heq]]. simplify_eq.
      apply lfilled_Ind_Equivalent in Hfill'. inversion Hfill';subst.
      iApply bi.sep_exist_l. iExists _. iFrame. iSplit =>//.
      iIntros "Hf". erewrite app_assoc.
      iApply ("IH" with "[$Hf]").
      iIntros "Hf".
      iApply wp_trap;eauto. }
  }
  { destruct σ as [[[? ?]?]?].
    set (σ:=(s0,s1,l,i)).
    iDestruct "Hσ" as "(?&?&?&?&Hfr&?)".
    iDestruct (ghost_map_lookup with "Hfr Hf") as %Heq1.
    iSpecialize ("Hes1" with "[$]").
    iSpecialize ("Hes1" $! σ ns κ κs nt with "[$]").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      by apply append_reducible.
    - iIntros (e2 σ2 efs HStep).
      assert (κ = [] /\ efs = []) as [-> ->]; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
      apply prim_step_split_reduce_r in HStep; last by [].
      destruct HStep as [[es'' [-> HStep]] | [n [m [lh [Hlf1 [Hlf2 ->]]]]]].
      + iSpecialize ("H2" $! es'' σ2 [] HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        destruct σ2 as [[[??] ?]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes'' & Hefs)".
        iApply bi.sep_exist_l. iExists f1.
        iFrame. (* iSplit =>//. *)
        iIntros "?".
        iSpecialize ("IH" with "[$]").
        iApply "IH". eauto.
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
        { unfold iris.prim_step.
          destruct σ as [[[??]?]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          move => HContra; subst.
          by destruct n.
        }
        iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        destruct σ as [[[??] ?]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes'' & Hefs)".
        iApply bi.sep_exist_l.  iExists f1.
        iDestruct "Hσ" as "(?&?&?&?&Hfr&?)".
        iDestruct (ghost_map_lookup with "Hfr Hf1") as %Heq.
        iDestruct ("Hes''" with "Hf1") as "Hes''".
        rewrite wp_unfold /wp_pre /=.
        iMod "Hes''" as "[_ Hf1]".
        iDestruct (ghost_map_lookup with "Hfr Hf1") as %Heq'.
        simplify_map_eq.
        (* iModIntro. *)
        iFrame. (* iApply fupd_frame_r. iSplit =>//. *)
        iModIntro. iIntros "Hf".
        erewrite cons_middle.
        erewrite app_assoc.
        iApply ("IH" with "[$Hf]").
        iIntros "Hf".
        iApply wp_trap;auto. }
  Qed.

  Lemma wp_val_trap (s : stuckness) (E : coPset) v0 (es1 : language.expr wasm_lang) f f' :
    ↪[frame] f ∗
     (↪[frame] f -∗ WP es1 @ NotStuck; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }})
     ⊢ WP ((AI_basic (BI_const v0)) :: es1) @ s; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}.
  Proof.
  (* This also needs an iLob. *)
  iLöb as "IH" forall (v0 es1 f f').
  iIntros "(Hntrap & H)".
  (* iApply wp_unfold.                *)
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { repeat rewrite wp_unfold /wp_pre /= Hes.
    iMod ("H"  with "Hntrap") as "[%Hcontr Hf]". subst.
    apply to_val_trap_is_singleton in Hes as ->.
    rewrite -(app_nil_r [AI_trap]). rewrite separate1.
    iApply (wp_trap with "[] [Hf]");auto. }
  { repeat rewrite wp_unfold /wp_pre /= Hes.
    iApply wp_unfold. rewrite /wp_pre /=.
    rewrite Hes. 
    iIntros (?????) "?".
    iDestruct ("H" with "[$]") as "H".
    iSpecialize ("H" $! σ1 ns κ κs nt with "[$]").
    iMod "H" as "[%Hred H]".
    iModIntro.
    iSplit.
    { iPureIntro.
      destruct s =>//. rewrite separate1.
      eapply prepend_reducible;eauto. }
    iIntros (es2 σ2 efs HStep).
    rewrite separate1 in HStep.
    apply prim_step_obs_efs_empty in HStep as Heq. simplify_eq.
    apply reduce_ves in HStep as [[-> Hstep] | [lh [lh' [Hfill1 [Hfill2 ->]]]]].
    { iSpecialize ("H" $! _ _ _ Hstep).
      repeat (iMod "H"; iModIntro; try iNext).
      iDestruct "H" as "[$ Ha]".
      iDestruct "Ha" as (a) "[Hf [Ha _]]".
      iExists _. iFrame. simpl.
      iSplit =>//. iIntros "Hf".
      iApply "IH". iFrame. }
    { apply lfilled_Ind_Equivalent in Hfill1.
      apply lfilled_Ind_Equivalent in Hfill2.
      inversion Hfill1;inversion Hfill2;simplify_eq.
      assert (iris.prim_step (vs0 ++ [AI_trap] ++ es'0)%SEQ σ2 [] [AI_trap] σ2 []) as Hstep'.
      { destruct σ2 as [[[??] ?]?]. split =>//.
        apply r_simple; eapply rs_trap => //.
        2: apply lfilled_Ind_Equivalent;constructor=>//.
        destruct vs0;[|destruct vs0 =>//].
        destruct es'0;[|destruct es'0 =>//].
        erewrite app_nil_l, app_nil_r in Hes. done.
      }
      iSpecialize ("H" $! _ _ _ Hstep').
      repeat (iMod "H"; iModIntro; try iNext).
      iDestruct "H" as "[$ Ha]".
      iDestruct "Ha" as (a) "[Hf [Ha _]]".
      iExists _. iFrame. simpl.
      iSplit =>//. iIntros "Hf".
      iDestruct ("Ha" with "Hf") as "Ha".
      rewrite wp_unfold /wp_pre /=.
      iMod "Ha" as "[_ Hf]".
      erewrite cons_middle.
      iApply wp_trap;auto. } 
    auto.
  }
  Qed.
      
  Lemma wp_val_app_trap' (s : stuckness) (E : coPset) vs (es : language.expr wasm_lang) f f' :
    ↪[frame] f ∗
     (↪[frame] f -∗ WP es @ NotStuck ; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}%I)
     ⊢ WP ((v_to_e_list vs) ++ es) @ s ; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}%I.
  Proof.
    iInduction vs as [|c vs] "IH" forall (s E es).
    { simpl.
      iIntros "[Hf HWP]".
      destruct s.
      2: iApply wp_stuck_weaken.
      all: iDestruct ("HWP" with "Hf") as "HWP".
      all: iApply (wp_wand with "HWP").
      all: iIntros (v).
      all: destruct v => /=.
      all: iIntros "HΦ" => //.
    }
    { iIntros "[Hf HWP]".
      iSimpl.
      iApply wp_val_trap.
      iFrame. iIntros "Hf".
      iApply ("IH" $! _ _ _ with "[Hf HWP]") => //=.
      iFrame.
    }
  Qed.
  
  Lemma wp_val_app_trap (s : stuckness) (E : coPset) vs v' (es : language.expr wasm_lang) f f' :
    iris.to_val vs = Some (immV v') ->
    ↪[frame] f ∗
     (↪[frame] f -∗ WP es @ NotStuck ; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f'}}%I)
     ⊢ WP (vs ++ es) @ s ; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}%I.
  Proof.
    iIntros "%Hves [Hf Hwp]".
    apply iris.of_to_val in Hves; subst.
    iApply wp_val_app_trap'.
    by iFrame.
  Qed.

  Lemma wp_label_trap s E LI vs n es' es'' f f':
    const_list vs ->
    ↪[frame] f -∗
    (↪[frame] f -∗ WP LI @ E {{ w, ⌜w = trapV⌝ ∗  ↪[frame]f' }}) -∗
    WP vs ++ [AI_label n es' LI] ++ es'' @ s; E {{ w, ⌜w = trapV⌝ ∗  ↪[frame]f' }}.
  Proof.
    iLöb as "IH" forall (vs LI n es' f f' es'' s).
    iIntros (Hconst) "Hf Hcont".
    destruct (iris.to_val LI) eqn:He.
    { iDestruct ("Hcont" with "Hf") as "Hcont".
      iDestruct (wp_unfold with "Hcont") as "Hcont".
      rewrite /wp_pre /= He.
      iMod "Hcont" as "[%Hcontr Hf]". subst.
      apply to_val_trap_is_singleton in He as ->.
      apply const_list_is_val in Hconst as [v Hv].
      iApply wp_val_app_trap;eauto. iFrame.
      iIntros "Hf".
      rewrite separate1.
      iApply wp_seq_trap. iFrame. iIntros "Hf".
      iApply (wp_label_trap with "Hf");auto. }
    { apply const_list_is_val in Hconst as [v Hv].
      iApply wp_val_app_trap;eauto. iFrame.
      iIntros "Hf".
      iApply wp_seq_trap. iFrame. iIntros "Hf".
      iDestruct ("Hcont" with "Hf") as "Hcont".
      iDestruct (wp_unfold with "Hcont") as "Hcont".
      iApply wp_unfold.
      rewrite /wp_pre /= He.
      iIntros (σ ns κ κs nt) "Hσ".
      iSpecialize ("Hcont" $! σ 0 [] [] 0).
      iDestruct ("Hcont" with "[$]") as "H".
      iMod "H" as "[%Hred H]".
      iModIntro.
      assert (lfilled 1 (LH_rec [] n es' (LH_base [] []) []) (LI ++ []) [AI_label n es' LI]) as Hfill.
      { apply lfilled_Ind_Equivalent.
        rewrite -(app_nil_l [AI_label n es' LI]) -(app_nil_r [AI_label n es' LI]).
        constructor=>//.
        apply lfilled_Ind_Equivalent. cbn. erewrite app_nil_r, app_nil_r. by rewrite eqseqE. }
      iSplit.
      { iPureIntro.
        unfold iris_wp_def.reducible, reducible.
        destruct Hred as [? [? [? [? ?]]]].
        exists [], [AI_label n es' x0],x1,[].
        destruct x1 as [[[? ?] ?] ?].
        destruct σ as [[[? ?] ?] ?].
        split =>//.
        eapply r_label. apply H.
        erewrite app_nil_r in Hfill. apply Hfill.
        apply lfilled_Ind_Equivalent.
        rewrite -(app_nil_l [AI_label n es' x0]) -(app_nil_r [AI_label n es' x0]).
        constructor=>//.
        apply lfilled_Ind_Equivalent. cbn. by rewrite eqseqE app_nil_r. }
      iIntros (e2 σ2 efs Hstep).
      apply prim_step_obs_efs_empty in Hstep as Heq. simplify_eq.
      
      eapply lfilled_prim_step_split_reduce_r in Hstep as Hstep';[|eauto|auto].
      destruct Hstep' as [[e' [Hstep' Hfill']]|[[lh Hfill'] ->]].
      { apply lfilled_Ind_Equivalent in Hfill'. inversion Hfill';subst.
        inversion H8;simplify_eq.
        apply prim_step_obs_efs_empty in Hstep as Heq;simplify_eq.
        iSpecialize ("H" $! _ _ _ Hstep').
        repeat (iMod "H"; iModIntro; try iNext).
        destruct σ2 as [[[? ?]?]?].
        iDestruct ("H") as "[$ H]".
        iDestruct "H" as (f0) "[Hf [H _]]".
        iExists f0. iFrame.
        iSplit =>//. iIntros "Hf".
        repeat erewrite app_nil_r,app_nil_l. erewrite app_nil_r.
        iDestruct ("IH" $! [] _ _ es' _ _ [] with "[] Hf H") as "H";auto. }
      { destruct σ2 as [[[? ?] ?] ?].
        set (σ2 := (s0,s1,l,i)).
        destruct Hstep as [Hstep _].
        erewrite app_nil_r in Hfill.
        eapply lfilled_trans in Hfill as Hfillf;[|apply Hfill'].
        destruct Hfillf as [lh'' Hlh''].
        eapply trap_reduce_nested in Hlh'' as [Heq _];[|eauto].
        destruct Heq as [lh' [j [Hj Hle]]].
        apply lfilled_Ind_Equivalent in Hfill'.
        inversion Hfill';subst.
        assert (iris.prim_step (vs0 ++ [AI_trap] ++ es'0)%SEQ σ2 [] [AI_trap] σ2 []) as Hstep'.
        { destruct σ2 as [[[? ?] ?] ?].
          split =>//.
          eapply r_simple,rs_trap.
          2: instantiate (1 := LH_base vs0 es'0);apply lfilled_Ind_Equivalent;by constructor.
          destruct vs0,es'0 =>//; destruct vs0 =>//. }
        iSpecialize ("H" $! _ _ _ Hstep').
        repeat (iMod "H"; iModIntro; try iNext).
        iDestruct "H" as "[$ H]".
        iDestruct "H" as (a) "[Hf [H _]]".
        iExists _. iFrame. iSplit =>//.
        iIntros "Hf".
        iDestruct ("H" with "Hf") as "H".
        iDestruct (wp_unfold with "H") as "H".
        rewrite /wp_pre /=. iMod "H" as "[_ Hf]".
        assert (j = 0 ∨ j = 1) as [-> | ->];[lia|..].
        { apply lfilled_Ind_Equivalent in Hj;inversion Hj;subst.
          iApply wp_trap;auto. }
        { apply lfilled_Ind_Equivalent in Hj;inversion Hj;subst. inversion H2;subst.
          iApply ("IH" with "[] Hf []");auto.
          iIntros "Hf".
          iApply wp_trap;auto.
        }
      }
    }
  Qed.

    
  Lemma wp_seq_trap_ctx (s : stuckness) (E : coPset) (es1 es2 : language.expr wasm_lang) f f' i lh :
    ↪[frame] f ∗
     (↪[frame] f -∗ WP es1 @ NotStuck; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }})
     ⊢ WP (es1 ++ es2) @ s; E CTX i; lh {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}.
  Proof.
    iIntros "[Hf Hes1]".
    iInduction i as [|i] "IH" forall (E es1 es2 lh f f' s).
    { iIntros (LI Hfilled).
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled;subst.
      erewrite app_assoc.
      iApply (wp_seq_trap with "[Hf Hes1]"). iFrame.
      iIntros "Hf".
      apply const_list_is_val in H as Hv.
      destruct Hv as [v Hv].
      iApply (wp_val_app_trap with "[-]");eauto.
      iFrame. iIntros "Hf".
      iApply (wp_seq_trap with "[-]");eauto.
      iFrame. }
    { iIntros (LI Hfilled).
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled;subst.
      iApply (wp_label_trap with "Hf");auto.
      iIntros "Hf".
      iDestruct ("IH" $! _ _ _ _ _ _ NotStuck with "Hf Hes1") as "H".
      apply lfilled_Ind_Equivalent in H1.
      iSpecialize ("H" $! _ H1). auto.
    }
  Qed.

  
  (* Lemma wp_seq_trap_or (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) f : *)

  (*   (↪[frame] f ∗ (¬ (Ψ trapV)) ∗ *)
  (*    (↪[frame] f -∗ WP es1 @ s; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ∃ f', ↪[frame] f' }}) ∗ *)
  (*    ∀ w f', Ψ w ∗ ↪[frame] f' -∗ WP (iris.of_val w ++ es2) @ s; E {{ v, Φ v ∗ ∃ f', ↪[frame] f' }})%I *)
  (*    ⊢ WP (es1 ++ es2) @ s; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ∃ f', ↪[frame] f' }}. *)
  (* Proof. *)
  (*   iIntros "(Hf & Htrap & Hes1 & Hcont)". *)
    

    
  
End trap_rules.
