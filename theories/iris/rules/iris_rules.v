From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules_structural
        iris_rules_pure
        iris_rules_control
        iris_rules_resources
        iris_rules_calls
        iris_rules_trap
        iris_rules_bind.
Require Export datatypes host operations properties opsem.

Close Scope byte_scope.

Section derived_rules.

  Context `{!wasmG Σ}.

  Lemma wp_ctx_bind' (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) e i lh :
    WP e @ s; E {{ w, WP of_val w @ s; E CTX i; lh {{ w, Φ w }} }} -∗
    WP e @ s; E CTX i; lh {{ w, Φ w }}.
  Proof.
    iIntros "He".
    destruct (empty_base lh) eqn:Hlhbase.
    unfold wp_wasm_ctx.
    iIntros (les Hlf).
    Search empty_base.
    eapply can_empty_base in Hlhbase => //.
    destruct Hlhbase as [es' [Hlf0 [Hlfi Hempty]]].
    iApply (wp_ctx_bind with "[He]") => //.
    move/lfilledP in Hlf0.
    inversion Hlf0; subst; clear Hlf0.
    iApply (wp_base_push with "[He]") => //; last first.
    { iPureIntro.
      instantiate (2 := e).
      instantiate (1 := es'0).
      instantiate (1 := LH_base [::] [::]).
      instantiate (1 := 0).
      unfold lfilled, lfill => //=.
      apply/eqP.
      by rewrite app_nil_r.
    }
    unfold frame_base.
    rewrite cat0s cats0.
    
    iLöb as "IH" forall (s E).
    (* iApply wp_unfold. *)
    destruct (iris.to_val e) as [vs0|] eqn:Hetov.
    { iApply wp_unfold.
      unfold wp_pre. simpl language.to_val. rewrite Hetov'; simpl.
      iIntros (σ ns κ κs nt) "Hσ".
      destruct σ as [[ ? ?] ?].
      iDestruct "Hσ" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hframe") as %Hlook.
      iMod (ghost_map_update f with "Hff Hframe") as "[Hff Hframe]".
      iDestruct ("H" with "Hframe") as "H".
      iDestruct (wp_unfold with "H") as "H".
      rewrite /wp_pre /= Hetov.
      iMod ("H") as "Hf".
      iDestruct "Hf" as (f') "[H Hf]".
      rewrite wp_frame_rewrite.
      iDestruct (ghost_map_lookup with "Hff Hf") as %Hlook'.
      iMod (ghost_map_update f0 with "Hff Hf") as "[Hff Hf]".
      rewrite !insert_insert. rewrite lookup_insert in Hlook'. inversion Hlook'.
      iDestruct ("H" with "Hf") as "H".
      iDestruct (wp_unfold with "H") as "H".
      rewrite /wp_pre /=.
      apply of_to_val in Hetov as Heq. rewrite Heq.
      subst f. rewrite Hetov'.
      rewrite lookup_insert in Hlook;inversion Hlook.
      iSpecialize ("H" $! (_,_,_) 0 κ [] 0 with "[$H1 $H2 $H3 $H4 $H5 $H6 $Hff]").
      iMod "H" as "[? H]". iModIntro. iFrame. }
    { iApply wp_unfold. unfold wp_pre. simpl. rewrite Hetov'.
      iIntros (σ ns κ κs nt) "Hσ".
      destruct σ as [[ ? ?] ?].
      iDestruct "Hσ" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hframe") as %Hlook.
      rewrite lookup_insert in Hlook;inversion Hlook.
      
      iMod (ghost_map_update f with "Hff Hframe") as "[Hff Hframe]".
      rewrite insert_insert.
      iDestruct ("H" with "Hframe") as "H". destruct f.
      iDestruct (wp_unfold with "H") as "H". rewrite /wp_pre /= Hetov.
      iSpecialize ("H" $! (_,_,_) 0 κ [] 0). 
      iDestruct ("H" with "[$H1 $H2 $H3 $H4 $H5 $H6 $Hff]") as "H".

      iMod "H" as "[%Hred H]".
    Search wp.
Admitted.
    
End derived_rules.
