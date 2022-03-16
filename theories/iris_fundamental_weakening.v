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

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* -------------------------------------- WEAKENING -------------------------------------- *)

  Lemma typing_weakening C es t1s t2s ts : (⊢ semantic_typing (HWP:=HWP) C (to_e_list es) (Tf t1s t2s)) ->
                                           ⊢ semantic_typing (HWP:=HWP) C (to_e_list es) (Tf (ts ++ t1s) (ts ++ t2s)).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (HIH i lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { iApply iRewrite_nil_l.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_app_inv_r with "Hv") as (ws1 ws2 Heq) "[Hv1 Hv2]".
    rewrite Heq. simpl of_val. rewrite fmap_app - app_assoc.

    iApply (wp_wand with "[-]");cycle 1.
    { iIntros (v) "H". unfold interp_val. rewrite -or_assoc. iExact "H". }

    iApply wp_val_can_trap_app;[apply to_val_fmap|].
    iFrame.
    iSplitR.
    { iModIntro. iIntros "[Hcontr | Hcontr]";[by iDestruct "Hcontr" as (? ?) "_"|].
      rewrite fixpoint_interp_br_eq. iDestruct "Hcontr" as (? ? ? ?) "_". done. }
    iIntros "Hf".

    assert ((λ v : value, AI_basic (BI_const v)) <$> ws2 = of_val (immV ws2)) as ->;[auto|].

    iApply (wp_wand with "[-]").
    { iApply (HIH with "[] [] [-]");iFrame "∗ # %".
      iRight. iExists _. iSplit;eauto. }

    iIntros (v) "[Hw Hf0]".
    iFrame.
    iDestruct "Hw" as "[[Hw|#Hw]|Hw]".
    { by iLeft. }
    { iRight. iLeft.
      iDestruct "Hw" as (ws' ->) "Hw".
      iSimpl. iExists _. iSplit;eauto.
      iApply big_sepL2_app;eauto. }
    { iRight. iRight.
      rewrite fixpoint_interp_br_eq.
      iDestruct "Hw" as (j w' e' ->) "Hbr".
      iApply fixpoint_interp_br_eq.
      unfold val_combine.
      iExists j,(ws1 ++ w'),e'. iSplit;[auto|].
      iDestruct "Hbr" as (? ? ? ? ? ? ? ?) "(H&H0&H1&H2&H3&H4)".
      iExists _,_,_,_,_,_,_,(ts ++ τs''). iFrame "H H0 H1 H2".
      iSplitL "H3".
      { iDestruct "H3" as "[%Hcontr|#Hw]";[done|].
        iRight.
        iDestruct "Hw" as (w0 Heq') "Hw". simplify_eq.
        iExists _. iSplit;eauto.
        rewrite -app_assoc.
        iApply big_sepL2_app;eauto. }
      iDestruct (big_sepL2_length with "Hv1") as %Hlen1.
      rewrite app_length -drop_drop -Hlen1 drop_app. iFrame.
    }
  Qed.
    

End fundamental.
