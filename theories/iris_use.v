(** Example of Iris usage **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export datatypes host operations properties opsem.
Require Import Coq.Program.Equality.

Import uPred.

Set Default Proof Using "Type". (* what is this? *)

Close Scope byte_scope.

Let expr := iris.expr.
Let val := iris.val.
Let to_val := iris.to_val.


Section Host.

Import DummyHosts.
  
(*
Variable host_function : eqType.

Let host := host.host host_function.
Let function_closure := function_closure host_function.
Let store_record := store_record host_function.

Variable host_instance : host.
 *)
Let reduce := @reduce host_function host_instance.


Canonical Structure wasm_lang := Language wasm_mixin.
 
Let reducible := @reducible wasm_lang.

Class irisG (Σ : gFunctors) := IrisG {
  iris_invG :> invG Σ;

  (** The state interpretation is an invariant that should hold in
  between each step of reduction. Here [Λstate] is the global state,
  the first [nat] is the number of steps already performed by the
  program, [list Λobservation] are the remaining observations, and the
  last [nat] is the number of forked-off threads (not the total number
  of threads, which is one higher because there is always a main
  thread). *)
  state_interp : state → nat → list (observation) → nat → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : val → iProp Σ;

  (** Number of additional logical steps (i.e., later modality in the
  definition of WP) per physical step, depending on the physical steps
  counter. In addition to these steps, the definition of WP adds one
  extra later per physical step to make sure that there is at least
  one later for each physical step. *)
  num_laters_per_step : nat → nat;

  (** When performing pure steps, the state interpretation needs to be
  adapted for the change in the [ns] parameter.

  Note that we use an empty-mask fancy update here. We could also use
  a basic update or a bare magic wand, the expressiveness of the
  framework would be the same. If we removed the modality here, then
  the client would have to include the modality it needs as part of
  the definition of [state_interp]. Since adding the modality as part
  of the definition [state_interp_mono] does not significantly
  complicate the formalization in Iris, we prefer simplifying the
  client. *)
  state_interp_mono σ ns κs nt:
    state_interp σ ns κs nt ={∅}=∗ state_interp σ (S ns) κs nt
}.
Global Opaque iris_invG.

(* TODO: change the fields to use actual sensible names *)
Class wfuncG Σ := WFuncG {
  func_invG :> invG Σ;
  func_gen_hsG :> gen_heapG N function_closure Σ;
}.

Class wtabG Σ := WTabG {
  tab_gen_hsG :> gen_heapG (N*N) funcelem Σ;
}.

Class wmemG Σ := WMemG {
  mem_gen_hsG :> gen_heapG (N*N) byte Σ;
}.

Class wmemsizeG Σ := WMemsizeG {
  memsize_gen_hsG :> gen_heapG N N Σ;
}.

Class wglobG Σ := WGlobG {
  glob_gen_hsG :> gen_heapG N global Σ;
}.

Class wframeG Σ := WFrameG {
  locs_gen_hsG :> ghost_mapG Σ unit frame;
}.

Definition frameGName : positive := 10%positive.

Notation "n ↦[wf]{ q } v" := (mapsto (L:=N) (V:=function_closure) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wf]{ q } v") : bi_scope.
Notation "n ↦[wf] v" := (mapsto (L:=N) (V:=function_closure) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wf] v") : bi_scope.
Notation "n ↦[wt]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=funcelem) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wt]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wt][ i ] v" := (mapsto (L:=N*N) (V:=funcelem) (n, i) (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wt][ i ] v") : bi_scope.
Notation "n ↦[wm]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wm]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wm][ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wm][ i ] v") : bi_scope.
Notation "n ↦[wmlength] v" := (mapsto (L:=N) (V:=N) n (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wmlength] v") : bi_scope.
Notation "n ↦[wg]{ q } v" := (mapsto (L:=N) (V:=global) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wg]{ q } v").
Notation "n ↦[wg] v" := (mapsto (L:=N) (V:=global) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wg] v") .
Notation " ↪[frame]{ q } v" := (ghost_map_elem frameGName tt q v%V)
                           (at level 20, q at level 5, format " ↪[frame]{ q } v") .
Notation " ↪[frame] v" := (ghost_map_elem frameGName tt (DfracOwn 1) v%V)
                           (at level 20, format " ↪[frame] v").

Definition proph_id := positive. (* ??? *)


(*
(* Memory size predicate using Monotone? *)
Definition R : relation N := fun x y => (x<y)%N.

Class MemsizeG Σ := memsizeG {
    MemsizeIG_monauth :> inG Σ (authUR (monotoneUR R));
}.

Definition MemsizeΣ := #[GFunctor (authUR (monotoneUR R))].

Instance subG_MonRefIGΣ {Σ} : subG MemsizeΣ Σ → MemsizeG Σ.
Proof. solve_inG. Qed.

Context `{!MemsizeG Σ}.

Definition mem_size_exact (γ: gname) sz := (own γ (● (principal R sz)))%I.

(* This should not be necessary *)
Definition mem_size_at_least (γ: gname) sz := (own γ (◯ (principal R sz)))%I.

(* Have to convert to 1-indexed, since Iris ghost names only allow positive. *)
Definition gen_mem_size (l: list memory) :=
  ([∗ list] i ↦ m ∈ l, mem_size_exact (Pos.of_succ_nat i) (mem_size m))%I.


Print gen_heap_interp.
 *)

Instance eqdecision_frame: EqDecision frame.
Proof. decidable_equality. Qed.

Definition stack_agree (cs: list frame) (f: frame) : Prop :=
  last cs = Some f.

(* TODO: Global Instance doesn't seem to actually make this global... *)
Global Instance heapG_irisG `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, wmemsizeG Σ, !wglobG Σ, !wframeG Σ} : irisG Σ := {
  iris_invG := func_invG; (* ??? *)
  state_interp σ _ κs _ :=
    let: (_, s, locs, inst) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
      (ghost_map_auth frameGName 1 (<[ tt := Build_frame locs inst ]> ∅)) ∗ 
      (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems))))
      
    )%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
}.




(* Defining a Wasm-specific WP with frame existence *)

Section Wasm_wp.
Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

Definition wasm_wp_pre (s : stuckness)
    (wp : coPset -d> expr -d> (val -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> expr -d> (val -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  (match iris.to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ns κ κs nt,
     (state_interp σ1 ns (κ ++ κs) nt) ={E,∅}=∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝
         ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
     ∃ f, state_interp σ2 (S ns) κs (length efs + nt) ∗
         (* Although it's an existential, we know what it must be. *)  
         ↪[frame] f ∗
         (↪[frame] f -∗ wp E e2 Φ) ∗
         [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post
end)%I.

Global Instance wasm_wp_pre_contractive s: Contractive (wasm_wp_pre s).
Proof.
  rewrite /wasm_wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 24 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IH]; simpl => //.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Global Instance wasm_wp_def : Wp wasm_lang (iProp Σ) stuckness :=
  λ (s: stuckness), fixpoint (wasm_wp_pre s).

(* Seal is a mechanism that stdpp uses to avoid definitions being automatically
   unfolded. *)
Definition wasm_wp_aux : seal (@wasm_wp_def). Proof. by exists wasm_wp_def. Qed.
Definition wasm_wp' := wasm_wp_aux.(unseal).
Global Arguments wasm_wp' {Λ Σ _}.
Global Existing Instance wasm_wp'.
Lemma wasm_wp_eq: wp = @wasm_wp_def.
Proof. rewrite -wasm_wp_aux.(seal_eq) //. Qed.

(* Reprove some useful auxiliary lemmas *)
Lemma wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ wasm_wp_pre s (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite wasm_wp_eq. apply (fixpoint_unfold (wasm_wp_pre s)). Qed.

Lemma wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite wp_unfold /wasm_wp_pre to_of_val. auto. Qed.

Lemma wp_strong_mono s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 ->
  WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wasm_wp_pre.
  destruct (iris.to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 ns κ κs nt) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[% H]".
  iModIntro. iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
  iMod ("H" with "[//]") as "H". iIntros "!> !>".
  iMod "H".
  simpl.
  iMod "H" as (f1) "(Hσ & Hf1 & H & Hefs)".
  iMod "Hclose" as "_".
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "Hmask".
  iMod "Hmask". iModIntro. iExists f1. iFrame. iSplitR "Hefs".
  - iIntros "Hf1".
    iSpecialize ("H" with "Hf1").                             
    by iApply ("IH" with "[//] H HΦ").
  - iApply (big_sepL_impl with "Hefs"); iIntros "!>" (k ef _).
    iIntros "H". iApply ("IH" with "[] H"); auto.
Qed.

Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply wp_value_fupd'. Qed.
Lemma wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. rewrite wp_value_fupd'. auto. Qed.
Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply wp_value'. Qed.

Lemma wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand_l s E e Q Φ :
  Q ∗ WP e @ s; E {{ v, Q -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "[HQ HWP]". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

(* Some lifting lemmas restated and reproved *)
Lemma wp_lift_step_fupd s E Φ e1 :
  iris.to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅}=∗ ▷ |={∅,E}=>
   ∃ f, state_interp σ2 (S ns) κs (length efs + nt) ∗
      ↪[frame] f ∗
      (↪[frame] f -∗ WP e2 @ s; E {{ Φ }}) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
    ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  (* Somehow, this lemma can no longer be automatically proved in one unfold. *)
  rewrite wp_unfold /wasm_wp_pre=>->. iIntros "H".
  iIntros (σ ns κ κs nt) "Hσ".
  iSpecialize ("H" $! σ ns κ κs nt with "[$]").
  iMod "H" as "(%Hred & H)".
  iModIntro.
  iSplit => //.
  iIntros (es' σ' efs HStep).
  iSpecialize ("H" $! es' σ' efs with "[% //]").
  repeat iMod "H".
  repeat iModIntro.
  simpl.
  iMod "H" as (f) "H".
  iModIntro.
  by iExists f.
Qed.

Lemma wp_lift_stuck E Φ e :
  iris.to_val e = None →
  (∀ ns σ κs nt, state_interp σ ns κs nt ={E,∅}=∗ ⌜stuck e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  rewrite wp_unfold /wasm_wp_pre=>->. iIntros "H" (σ1 ns κ κs nt) "Hσ".
  iMod ("H" with "[$]") as %[? Hirr]. iModIntro. iSplit; first done.
  iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
Qed.

Lemma wp_lift_step s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      ∃ f, state_interp σ2 ns κs (length efs + nt) ∗
      ↪[frame] f ∗
      (↪[frame] f -∗ WP e2 @ s; E {{ Φ }}) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (?????) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]". iIntros "!> * % !> !>". by iApply "H".
Qed.

Lemma wp_lift_atomic_step_fupd {s E1 E2 Φ} e1 :
  iris.to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E1}[E2]▷=∗
      ∃ f, state_interp σ2 ns κs (length efs + nt) ∗
      ↪[frame] f ∗
      (↪[frame] f -∗ from_option Φ False (iris.to_val e2)) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E1 _ e1)=>//; iIntros (σ1 ns κ κs nt) "Hσ1".
  iMod ("H" $! σ1 with "[$]") as "[$ H]".
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "Hclose" (e2 σ2 efs ?). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#]") as "H"; [done|].
  iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as (f1) "($ & Hf1 & HQ & $)".
  (* This is actually very interesting -- the order of resource consumption
     is important! *)
  iModIntro.
  iExists f1.
  iFrame.
  iIntros "?"; iSpecialize ("HQ" with "[$]").
  destruct (iris.to_val e2) eqn:?; last by iExFalso.
  iApply wp_value; last done. by apply of_to_val.
Qed.

Lemma wp_lift_atomic_step {s E Φ} e1 :
  iris.to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ∃ f, state_interp σ2 ns κs (length efs + nt) ∗
      ↪[frame] f ∗         
      (↪[frame] f -∗ from_option Φ False (iris.to_val e2)) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (?????) "?". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!> *". iIntros (Hstep) "!> !>".
  by iApply "H".
Qed.

End Wasm_wp.

(* A Definition of a context dependent WP for WASM expressions *)

Definition wp_wasm_ctx `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}
          (s : stuckness) (E : coPset) (e : language.expr wasm_lang)
           (Φ : val -> iProp Σ) (i : nat) (lh : lholed) : iProp Σ := 
  ∀ LI, ⌜lfilled i lh e LI⌝ -∗ WP LI @ s; E {{ Φ }}.

Notation "'WP' e @ s ; E 'CTX' i ; lh {{ Φ } }" := (wp_wasm_ctx s E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh {{ Φ } }" := (wp_wasm_ctx NotStuck E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh ? {{ Φ } }" := (wp_wasm_ctx MaybeStuck E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e 'CTX' i ; lh {{ Φ } }" := (wp_wasm_ctx NotStuck ⊤ e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e 'CTX' i ; lh ? {{ Φ } }" := (wp_wasm_ctx MaybeStuck ⊤ e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ s ; E 'CTX_EMPTY' {{ Φ } }" := (wp_wasm_ctx s E e%E Φ 0 (LH_base [] []))
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.


Notation "'WP' e @ s ; E 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx s E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ s ; E 'CTX_EMPTY' {{ v , Q } }" := (wp_wasm_ctx s E e%E (λ v, Q) 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx NotStuck E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @ '[' E  '/' ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx MaybeStuck E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' E  '/' ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx NotStuck ⊤ e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx MaybeStuck ⊤ e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.




Definition wp_wasm_frame `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}
          (s : stuckness) (E : coPset) (es : language.expr wasm_lang)
          (Φ : val -> iProp Σ) (n: nat) (f: frame) : iProp Σ :=
  
  WP [AI_local n f es] @ s; E {{ Φ }}.

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ Φ } }" := (wp_wasm_frame s E e%E Φ n f)
  (at level 20, only parsing) : bi_scope.

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ v , Q } }" := (wp_wasm_frame s E e%E (λ v, Q) n f)
  (at level 20, e, Q, n, f at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ; f ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* wp for instructions *)

Section lifting.
Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

(* Predicate for memory blocks *)

(* TODO: switch to monotone implementation of mem_size once we have that? *)
Definition mem_block (n: N) (m: memory) :=
  (([∗ list] i ↦ b ∈ (m.(mem_data).(ml_data)), n ↦[wm][ (N.of_nat i) ] b ) ∗
     n ↦[wmlength] mem_length m)%I.
(* mem_size_exact (N.succ_pos n) (mem_size m))%I*)

Definition mem_block_at_pos (n: N) (l:bytes) k :=
  ([∗ list] i ↦ b ∈ l, n ↦[wm][ (N.of_nat (N.to_nat k+i)) ] b)%I.


Notation "n ↦[wmblock] m" := (mem_block n m)
                           (at level 20, format "n ↦[wmblock] m"): bi_scope.
Notation "n ↦[wms][ i ] l" := (mem_block_at_pos n l i)
                                (at level 20, format "n ↦[wms][ i ] l"): bi_scope.




Definition mem_block_equiv (m1 m2: memory) :=
  m1.(mem_data).(ml_data) = m2.(mem_data).(ml_data).

Notation "m1 ≡ₘ m2" := (mem_block_equiv m1 m2)
                        (at level 70, format "m1 ≡ₘ m2").


(* empty lists, frame and context rules *)

Lemma wp_wasm_empty_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) e :
  ⊢ WP e @ s ; E {{ Φ }} ∗-∗ WP e @ s ; E CTX_EMPTY {{ Φ }}.
Proof.
  iSplit.
  { iIntros "HWP". iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill. subst. erewrite app_nil_l; erewrite app_nil_r. done. }
  { iIntros "HWP".
    iDestruct ("HWP" $! e with "[]") as "$".
    iPureIntro. cbn. rewrite app_nil_r eqseqE. apply eq_refl. }
Qed.

Lemma wp_nil (s : stuckness) (E : coPset) (Φ : iProp Σ) f :
  ↪[frame] f ∗ Φ ⊢ WP [] @ s ; E CTX_EMPTY {{ fun v => Φ }}%I.
Proof.
  iIntros "(Hframe & H)". iApply wp_wasm_empty_ctx.
  by rewrite wp_unfold /wasm_wp_pre.
Qed.

Lemma wp_seq_ctx (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) :
  (WP es1 @ NotStuck; E {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ WP (iris.of_val w ++ es2) @ s; E CTX i; lh {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E CTX i; lh {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ i lh).
{ iIntros "[Hes1 Hes2]".
  (* iDestruct (wp_wasm_empty_ctx with "Hes1") as "Hes1". *)
  iIntros (LI Hfilled).
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val LI) as [vs|] eqn:Hetov.
  { destruct vs.
    { pose proof (filled_is_val_imm _ _ _ _ _ Hetov Hfilled) as
        [vs [es' [-> [-> [Hconst1 Hconst2]]]]].
      apply const_list_is_val in Hconst1 as [v1 Hv1].
      apply const_list_is_val in Hconst2 as [v2 Hv2].
      edestruct fill_val as [vs12 [Hvs12 Heql]];eauto.
      assert (Hvs12':=Hvs12).
      apply to_val_cat in Hvs12' as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      iMod "Hes1".
      iSpecialize ("Hes2" with "Hes1").
      unfold iris.of_val.
      rewrite - fmap_app take_drop.
      rewrite of_val_imm.
      pose proof (lfilled_swap (iris.of_val (immV vs12)) Hfilled) as [LI' Hfilled'].
      iSpecialize ("Hes2" $! _ Hfilled').
      rewrite wp_unfold /wasm_wp_pre /=.
      assert (iris.to_val LI' = Some (immV l)) as ->;[|iFrame].
      apply lfilled_Ind_Equivalent in Hfilled'. inversion Hfilled';subst.
      apply to_val_cat_inv;auto. apply to_val_cat_inv;auto. apply iris.to_of_val.
    }
    { apply to_val_trap_is_singleton in Hetov. subst.
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled;subst.
      2: { exfalso. do 2 destruct vs =>//=. }
      apply app_eq_singleton in H as [[HH HH']|[HH HH']];subst.
      { exfalso. destruct es1,es2,es' =>//=. }
      apply app_eq_singleton in HH' as [[HH HH']|[HH HH']];subst.
      { apply app_eq_singleton in HH as [[-> ->]|[-> ->]].
        simpl.
        all:iMod "Hes1".
        all: iSpecialize ("Hes2" with "Hes1").
        all:rewrite /=.
        all: iDestruct (wp_wasm_empty_ctx with "Hes2") as "Hes2".
        all:by rewrite wp_unfold /wasm_wp_pre /=. }
      { destruct es1,es2 =>//=.
        iMod "Hes1".
        iSpecialize ("Hes2" with "Hes1").
        rewrite /=.
        iSpecialize ("Hes2" $! [AI_trap] with "[]").
        { iPureIntro. constructor. }
        by rewrite wp_unfold /wasm_wp_pre /=.  }
    }
  }
  {
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    iSpecialize ("Hes2" $! _ Hfilled).
    rewrite wp_unfold /wasm_wp_pre /=.
    rewrite Hetov.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "[$]").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "[$]").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      apply append_reducible with (es2:=es2) in H1;auto.
      eapply lfilled_reducible. apply Hfilled. auto.
    - iIntros (e2 σ2 efs HStep').
      eapply lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1].
      destruct Heq as [e' [HStep'' Hlfilled']].
      apply prim_step_obs_efs_empty in HStep'' as Hemp. inversion Hemp;subst;clear Hemp.
      apply prim_step_obs_efs_empty in HStep' as Hemp. inversion Hemp;subst;clear Hemp.
      iSpecialize ("H2" $! e' σ2 [] HStep'').
      iMod "H2".
      repeat iModIntro.
      repeat iMod "H2".
      iModIntro.
      iDestruct "H2" as (f1) "(Hσ & Hf1 & Hes'' & Hefs)".
      iExists f1.
      iFrame.
      iSplit => //.
      iIntros "?"; iSpecialize ("Hes''" with "[$]").
      iDestruct ("IH" with "[$Hes'' $Hes2]") as "Hcont".
      by iApply "Hcont".
  } } }
Qed.

(*
value1
value2
value3
Trap
expr3
expr2
expr1

could reduce to either a Trap directly, or 
value1
Trap
expr1,

But ultimately they reduce to a single Trap.
*)

(*
Lemma wp_trap s E es Φ:
  WP @ s; E ([AI_trap] ++ es) {{ w, Φ w }} ⊢
  |={E}=> Φ trapV.
Proof.
  rewrite wp_unfold/ wp_pre.
Admitted.
 *)

(* behaviour of seq might be a bit unusual due to how reductions work. *)
(* Note that the sequence wp is also true without the premise that Ψ doesn't trap, but it is very tricky to prove that version. The following is the fault-avoiding version.*)
Lemma wp_seq (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  (¬ Ψ trapV) ∗ 
  (WP es1 @ s; E {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ WP (iris.of_val w ++ es2) @ s; E {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ).
  iIntros "(Hntrap & Hes1 & Hes2)".
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
  {
    destruct vs.
    {
      apply to_val_cat in Hetov as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      iMod "Hes1".
      iSpecialize ("Hes2" with "Hes1").
      unfold iris.of_val.
      rewrite - fmap_app take_drop.
      rewrite of_val_imm.
      rewrite wp_unfold /wasm_wp_pre /=.
      rewrite of_val_imm iris.to_of_val.
      by iAssumption.
    }
    {
      apply to_val_trap_is_singleton in Hetov.
      apply app_eq_singleton in Hetov as [[-> ->]|[-> ->]].
      all:iMod "Hes1".
      all: iSpecialize ("Hes2" with "Hes1").
      all:rewrite /=.
      all:by rewrite wp_unfold /wasm_wp_pre /=. 
    }
  }
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    rewrite wp_unfold /wasm_wp_pre /=.
    rewrite Hetov.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "[$]").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
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
        iDestruct "H2" as (f1) "(Hσ & Hf1 & Hes'' & Hefs)".
        iExists f1.
        iFrame.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        iApply "IH".
        by iFrame. 
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
        iDestruct "H2" as (f1) "(Hσ & Hf1 & Hes'' & Hefs)".
        iExists f1.
        iModIntro.
        iFrame.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        replace [AI_trap] with (iris.of_val trapV) => //.
        repeat rewrite wp_unfold /wasm_wp_pre /=.
        destruct (iris.to_val (take n es1 ++ AI_trap :: drop m (es1 ++ es2))%SEQ) eqn:Hx.
        * iMod "Hes''".
          by iSpecialize ("Hntrap" with "Hes''").
        * iIntros (?????) "?".
          iMod "Hes''".
          by iSpecialize ("Hntrap" with "Hes''").
  }
Qed.

(*
(* This requires inverting wp again........ It would be really amazing
   if we can actually prove this, since I can't find anywhere in Iris where
   this has been done. *)
Lemma wp_trap_lfilled (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (es : language.expr wasm_lang) (lh: lholed):
  lfilled 0 lh [AI_trap] es ->
  WP es @ s; E {{ v, Φ v }} ⊢
  |={E}=> Φ trapV.
Proof.
  move => Hlf.
  iIntros "H".
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  move/lfilledP in Hlf.
  inversion Hlf; subst; clear Hlf.
  (* if both vs and es' are empty then we're good: wp_value is directly applicable. *)
  destruct (iris.to_val (vs ++ [AI_trap] ++ es')) as [v|] eqn:Hetov.
  {
    destruct v.
    (* actual value, which is impossible *)
    {
      apply to_val_cat in Hetov as [Hvs He].
      apply to_val_cat in He as [Het He'].
      simpl in Het.
      by inversion He'.
    }
    (* trapV *)
    {
      apply iris.of_to_val in Hetov.
      simpl in Hetov.
      destruct vs; by [destruct es' | destruct vs].
    }
  }
  rewrite Hetov.
  (* We now need to feed an explicit configuration and state to the premise. *)
Admitted.

Lemma wp_seq_trap (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  (WP es1 @ s; E {{ w, ⌜ w = trapV ⌝ }} ∗
  WP ([AI_trap] ++ es2) @ s; E {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
Proof.
  iIntros "(Hes1 & Hes2)".
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
  {
    destruct vs.
    {
      apply to_val_cat in Hetov as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      by iMod "Hes1" as "%Hes1".
    }
    {
      apply to_val_trap_is_singleton in Hetov.
      apply app_eq_singleton in Hetov as [[-> ->]|[-> ->]] => //.
      iMod "Hes1" => //.
      by iDestruct "Hes1" as "%Hes1".
    }
  }
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1" as "->".
    destruct es2 => //.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "Hσ").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "Hσ").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      by apply append_reducible.
    - iIntros (e2 σ2 efs HStep).
      apply prim_step_split_reduce_r_correct in HStep; last by [].
      destruct HStep as [[es'' [-> HStep]] | [n [m [Hlf [-> HStep]]]]].
      + iSpecialize ("H2" $! es'' σ2 efs HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        destruct σ2 as [[??] ?].
        iDestruct "H2" as "(Hσ & Hes'' & Hefs)".
        iFrame.
Admitted.
*)

(* The following operation mirrors the opsem of AI_trap *)
(* in which a trap value swallows all other stack values *)
Definition val_combine (v1 v2 : val) :=
  match v1 with
  | immV l => match v2 with
             | immV l' => immV (l ++ l')
             | trapV => trapV
             end
  | trapV => trapV
  end.

(* Knowing hypothesis "Hred : objs -> _" (with frames (locs, inst) and (locs', inst')),
   attempts to exfalso away most of the possible ways Hred could hold, leaving the user
   with only the one possible desired case. Tactic will also attempt to trivially solve
   this one case, but may give it to user if attempt fails. *)

(*
Ltac only_one_reduction Hred objs locs inst locs' inst' :=
  let a := fresh "a" in
  let aft := fresh "aft" in
  let bef := fresh "bef" in
  let e := fresh "e" in
  let e' := fresh "e'" in
  let es := fresh "es" in
  let es0 := fresh "es" in
  let es1 := fresh "es" in
  let es2 := fresh "es" in
  let f := fresh "f" in
  let f' := fresh "f" in
  let g := fresh "g" in
  let hs := fresh "hs" in
  let hs' := fresh "hs" in
  let H := fresh "H" in
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  let Hconst := fresh "Hconst" in
  let Heqes0 := fresh "Heqes" in
  let Heqes2 := fresh "Heqes" in
  let Heqg := fresh "Heqg" in
  let Ht1s := fresh "Ht1s" in
  let Ht2s := fresh "Ht2s" in
  let Hvs := fresh "Hvs" in
  let Hxl1 := fresh "Hxl1" in
  let IHreduce := fresh "IHreduce" in
  let k := fresh "k" in
  let l := fresh "l" in
  let l' := fresh "l" in
  let les := fresh "les" in
  let les' := fresh "les" in
  let lh := fresh "lh" in
  let m := fresh "m" in
  let n0 := fresh "n" in
  let n' := fresh "n" in
  let s := fresh "s" in
  let t1s := fresh "t1s" in
  let t2s := fresh "t2s" in
  let vs := fresh "vs" in
  remember objs as es0 eqn:Heqes0 ;
  remember {| f_locs := locs ; f_inst := inst |} as f eqn:Heqf ;
  remember {| f_locs := locs' ; f_inst := inst' |} as f' eqn:Heqf' ;
  apply Logic.eq_sym in Heqes0 ;
  induction Hred as [e e' s ? hs H | | | | | a | a | a | | | | | | | | | | | | | | | |
                      s ? es les s' f' es' les' k lh hs hs' Hred IHreduce H0 H1 | ];
  (* induction on the reduction. Most cases will be trivially solved by the following
     two attemps : *)
  (try by inversion Heqes0) ;
  (try by found_intruse (AI_invoke a) Heqes0 Hxl1) ;
  (* reduce_simple case : *)
  first (destruct H as [ | | | | | | | | | | | | | | 
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                  | | | | | | | | | | | | | 
                         es' lh Htrap' H0 ]  ;
         (* by case_analysis on the reduce_simple. most cases solved by just the 
            following inversion ; some cases need a little extra help *)
         inversion Heqes0 as [[ Hhd ]] ; subst ;
         (try by found_intruse (AI_basic (BI_block (Tf t1s t2s) es)) Hhd Hxl1) ;
         (try by found_intruse (AI_basic (BI_loop (Tf t1s t2s) es)) Hhd Hxl1) ;
         (try by filled_trap H0 Hxl1) ) ;
  (* lfilled case *)
  last (rewrite <- Heqes0 in H0 ;
        (* the simple_filled tactic unfolds lfilled, solves the case where k>0,
           and in the case k=0 leaves user with hypothesis H0 modified to now be
           les = bef ++ es ++ aft *)
        simple_filled2 H0 k lh bef aft n0 l l' ;
        first
          ( apply Logic.eq_sym in H0 ;
            remember ([] : seq.seq administrative_instruction) as g eqn:Heqg in s;
            let rec auxb H0 :=
              (* We maintain as an invariant that when auxb H0 is called,
                 H0 is the hypothesis "H0 : bef ++ es ++ aft = [some explicit sequence]" *)
              ( let b0 := fresh "b" in
                let Hb0 := fresh "Hb" in
                let H2 := fresh "H" in
                destruct bef as [| b0 bef ] ;
                [ (* case bef = []. Our invariant gives us that
                     "H0 : es ++ aft = [some explicit sequence]".
                     Recall g was defined as [] with "Heqg : g = []". *)
                  let rec auxe H0 g Heqg :=
                    (* We maintain as an invariant than when auxe H0 g Heqg is called,
                       H0 is the hypothesis "H0 : es ++ aft = [some explicit sequence]",
                       Hred is the hypothesis "Hred : (g ++ es) -> es'",
                       and Heqg is "Heqg : g = [some (other) explicit sequence]" *)
                    ( let e0 := fresh "e" in
                      let g' := fresh "g" in
                      let He0 := fresh "He" in
                      let Heqg' := fresh "Heqg" in
                      let H2 := fresh "H" in
                      destruct es as [| e0 es] ;
                      [ (* case es = []. Our invariants give us that
                           "Hred : g -> es' " with g described explicitly in Heqg.
                           Thus to conclude, we can … *)
                        rewrite <- Heqg in Hred ;
                        remember g as es2 eqn:Heqes2 in Hred ;
                        apply Logic.eq_sym in Heqes2 ;
                        rewrite Heqg in Heqes2 ;
                        (* use our induction hypothesis 
                           (case where bef = aft = []), or …  *)
                        (( by simpl in H0 ; rewrite H0 in H1 ;
                           unfold lfilled, lfill in H1 ;
                           destruct (const_list []) ; [| false_assumption] ;
                           apply b2p in H1 ; rewrite H1 ; rewrite app_nil_r ;
                           apply IHreduce ; subst ; trivial) +
                           (* use no_reduce (case where bef or aft is nonempty, and thus
                              g is shorter than the original objs). Strict subsequences
                              of valid reduction sequences tend to not reduce, so this
                              will work most of the time *)
                           (exfalso ; no_reduce Heqes2 Hred) )
                      | (* case es = e0 :: es. Our invariant gives us that
                           "H0 : e0 :: es ++ aft = [some explicit sequence]". We can
                           try to conclude by inverting H0, in case the explicit sentence is
                           empty *)
                        (by inversion H0) +
                          (* else, we know the explicit sentence is nonempty. 
                             Now by inverting H0 we get 
                             "H2 : es ++ aft = [some shorter explicit sequence]"
                             The invariant also gives us
                             "Hred : (g ++ e0 :: es) -> es'", so to maintain the invariant  
                             we define g' to be g ++ [e0] and create an equation Heqg' that
                             describes g' explicitly *)
                          ( inversion H0 as [[ He0 H2 ]] ;
                            rewrite He0 in Hred ;
                            remember (g ++ [e0]) as g' eqn:Heqg' ;
                            rewrite Heqg in Heqg' ;
                            rewrite He0 in Heqg' ;
                            simpl in Heqg' ;
                            (* we can now make a recursive call to auxe. The length of the
                               explicit list in H2 has strictly decreased *)
                            auxe H2 g' Heqg'
                          )
                      ]
                    ) in auxe H0 g Heqg
                | (* case bef = b0 :: bef. Our invariant gives us that
                     "H0 : b0 :: bef ++ es ++ aft = [some explicit sequence]".
                     We can attempt to conclude by inverting H0, which will work if
                     the explicit sequence is empty *)
                  (by inversion H0 ) +
                    (* else, we know the explicit sequence is nonempty, so by inverting
                       H0, we get "H2 : bef ++ es ++ aft = [some explicit sequence]" *)
                    ( inversion H0 as [[ Hb0 H2 ]] ;
                      auxb H2 )
                ]
              ) in auxb H0
          )
       ) ;        
  (* at this point, only one case should be remaining.
     we attempt to solve this case too trivially, as the following line is often
     what user would be going to do next anyway *)
  try by inversion Heqes0 ; subst ; inversion Heqf' ; subst ; iFrame.
*)

(* An attempt at making reduce_det a proved lemma. Work in progress

Lemma reduce_det: forall hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2,
  reduce hs f ws es hs1 f1 ws1 es1 ->
  reduce hs f ws es hs2 f2 ws2 es2 ->
  ( In (AI_basic BI_grow_memory) es -> False ) ->
  ( forall a, In (AI_invoke a) es -> False) -> 
  (hs1, f1, ws1, es1) = (hs2, f2, ws2, es2).
Proof.
  intros hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2 Hred1 Hred2 Hgrow_memory Hinvoke.
  destruct es as [ | e0 es ].
  { empty_list_no_reduce Hred1. }
  destruct es as [ | e1 es ].
  { remember [e0] as es.
    apply Logic.eq_sym in Heqes.
    destruct e0.
    destruct b ; try by exfalso ; no_reduce Heqes Hred1. *)

Lemma wp_val (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v0 : value) (es : language.expr wasm_lang) :
  (* Like for wp_seq, this lemma is true without the trap condition, but would
     be problematic to prove without it. *)
  ((¬ Φ trapV) ∗
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV [v0]) v))  }}
  ⊢ WP ((AI_basic (BI_const v0)) :: es) @ s ; E {{ v, Φ v }})%I.
Proof.
  (* This also needs an iLob. *)
  iLöb as "IH" forall (v0 es Φ).
  iIntros "(Hntrap & H)".
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  destruct (iris.to_val es) as [vs|] eqn:Hes.
  {
    destruct vs; first by apply of_to_val in Hes as <-.
    iIntros (?????) "?".
    iMod "H".
    by iSpecialize ("Hntrap" with "H").
  }
  {
    iIntros (σ ns κ κs nt) "Hσ".
    iSpecialize ("H" $! σ ns κ κs nt with "[$]").
    iMod "H".
    iModIntro.
    iDestruct "H" as "(%H1 & H)".
    iSplit.
    - iPureIntro.
      destruct s => //=.
      rewrite - cat1s.
      by eapply prepend_reducible; eauto.
    - iIntros (es2 σ2 efs HStep).
      rewrite -cat1s in HStep.
      eapply reduce_ves in H1; last by apply HStep.
      assert (κ = [] /\ efs = []) as [-> ->]; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
      destruct H1 as [[-> HStep2] | [lh1 [lh2 [Hlf1 [Hlf2 ->]]]]].
      + iSpecialize ("H" $! (drop 1 es2) σ2 [] HStep2).
        iMod "H".
        repeat iModIntro.
        repeat iMod "H".
        iModIntro.
        iDestruct "H" as (f1) "(Hσ & Hf1 & Hes & Hefs)".
        iSimpl.
        iExists f1.
        iFrame.
        iSplit => //.
        iIntros "?"; iSpecialize ("Hes" with "[$]").
        iApply "IH".
        by iFrame.
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        move/lfilledP in Hlf2.
        inversion Hlf2; subst; clear Hlf2.
        assert (iris.prim_step (vs0 ++ [AI_trap] ++ es'0) σ2 [] [AI_trap] σ2 []) as HStep2.
        { unfold iris.prim_step.
          destruct σ2 as [[[??]?]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          - move => HContra.
            by replace (vs0 ++ [AI_trap] ++ es'0)%SEQ with [AI_trap] in Hes.
          - apply/lfilledP.
            by apply LfilledBase.
        }
        iSpecialize ("H" $! [AI_trap] σ2 [] HStep2).
        iMod "H".
        repeat iModIntro.
        repeat iMod "H".
        iDestruct "H" as (f1) "(Hσ & Hf1 & Hes & Hefs)".
        iExists f1.
        iFrame.
        iModIntro.
        iSplit => //.
        iIntros "?"; iSpecialize ("Hes" with "[$]").
        repeat rewrite wp_unfold /wasm_wp_pre /=.
        destruct (iris.to_val (vs ++ AI_trap :: es')%SEQ) eqn:Hx.
        * iMod "Hes".
          by iSpecialize ("Hntrap" with "Hes").
        * iIntros (?????) "?".
          iMod "Hes".
          by iSpecialize ("Hntrap" with "Hes").
  }
Qed.
  
Lemma wp_val_app' (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs (es : language.expr wasm_lang) :
  (* □ is required here -- this knowledge needs to be persistent instead of 
     one-off. *)
  (□ (¬ Φ trapV )) ∗
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV vs) v)) }}%I
  ⊢ WP ((v_to_e_list vs) ++ es) @ s ; E {{ v, Φ v }}%I.

Proof.
  iInduction vs as [|c vs] "IH" forall (Φ s E es).
  { simpl.
    iIntros "(#Hntrap & HWP)".
    destruct s.
    2: iApply wp_stuck_weaken.
    all: iApply (wp_wand with "HWP").
    all: iIntros (v).
    all: destruct v => /=.
    all: iIntros "HΦ" => //.
  }
  { iIntros "(#Hntrap & HWP)".
    iSimpl.
    iApply wp_val.
    iSplitR => //.
    iApply "IH" => //=.
    iSplit => //.
    iApply (wp_mono with "HWP").
    iIntros (vs') "HΦ".
    iSimpl. destruct vs';auto.
  }
Qed.
  
Lemma wp_val_app (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs v' (es : language.expr wasm_lang) :
  iris.to_val vs = Some (immV v') ->
  (□ (¬ Φ trapV )) ∗
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV v') v)) }}%I
  ⊢ WP (vs ++ es) @ s ; E {{ v, Φ v }}%I.
Proof.
  iIntros "%Hves [#Hntrap Hwp]".
  apply iris.of_to_val in Hves; subst.
  iApply wp_val_app'.
  by iFrame.
Qed.
                                  
(* basic instructions with simple(pure) reductions *)

(* numerics *)

(* Axiom only_one_reduction_placeholder: False.

(* placeholder until the actual tactic is sorted *)
Ltac only_one_reduction H es locs inst locs' inst':=
  exfalso; by apply only_one_reduction_placeholder. *)


Ltac only_one_reduction H :=
  let Hstart := fresh "Hstart" in
  let a := fresh "a" in
  let Hstart1 := fresh "Hstart" in
  let Hstart2 := fresh "Hstart" in
  let Hσ := fresh "Hσ" in 
  eapply reduce_det in H
      as [H | [ Hstart | [ [a Hstart] | (Hstart & Hstart1 & Hstart2 & Hσ)]]] ;
  last (by repeat econstructor) ;
  first (try inversion H ; subst ; clear H => /=; match goal with [f: frame |- _] => iExists f; iFrame; by iIntros | _ => idtac end) ;
  try by repeat (unfold first_instr in Hstart ; simpl in Hstart) ; inversion Hstart.

Lemma wp_unop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v' : value) (t: value_type) (op: unop) f0:
  app_unop op v = v' ->
  ↪[frame] f0 -∗
   Φ (immV [v']) -∗
  WP [AI_basic (BI_const v); AI_basic (BI_unop t op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hunop) "Hf HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[[ hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. apply r_simple. rewrite <- Hunop. apply rs_unop.
  - destruct σ as [[[hs ws] locs] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H.
Qed.
 
Lemma wp_binop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 v : value) (t: value_type) (op: binop) f0:
  app_binop op v1 v2 = Some v ->
  ↪[frame] f0 -∗
  Φ (immV [v]) -∗
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hbinop) "Hf HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v)], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_binop_success.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.
                                                                  

(* There is a problem with this case: AI_trap is not a value in our language.
   This can of course be circumvented if we only consider 'successful reductions',
   but otherwise this needs some special treatment. *)

(* 20210929: with [::AI_trap] potentially becoming a value, this might get proved at some point *)
Lemma wp_binop_failure (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 : value) (t: value_type) (op: binop) f0:
  app_binop op v1 v2 = None ->
  Φ trapV -∗
  ↪[frame] f0 -∗
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hbinop) "Hf HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_binop_failure.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.
    
Lemma wp_relop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 : value) (b: bool) (t: value_type) (op: relop) f0:
  app_relop op v1 v2 = b ->
  ↪[frame] f0 -∗
  Φ (immV [(VAL_int32 (wasm_bool b))]) -∗
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Hrelop) "Hf HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (wasm_bool b)))], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_relop.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.

Lemma wp_testop_i32 (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v : i32) (b: bool) (t: value_type) (op: testop) f0:
  app_testop_i (e:=i32t) op v = b ->
  ↪[frame] f0 -∗
  Φ (immV [(VAL_int32 (wasm_bool b))]) -∗
    WP [AI_basic (BI_const (VAL_int32 v)); AI_basic (BI_testop T_i32 op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Htestop) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (wasm_bool b)))], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_testop_i32.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.

Lemma wp_testop_i64 (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v : i64) (b: bool) (t: value_type) (op: testop) f0:
  app_testop_i (e:=i64t) op v = b ->
  ↪[frame] f0 -∗
  Φ (immV [(VAL_int32 (wasm_bool b))]) -∗
    WP [AI_basic (BI_const (VAL_int64 v)); AI_basic (BI_testop T_i64 op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Htestop) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (wasm_bool b)))], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_testop_i64.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.

Lemma wp_cvtop_convert (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v': value) (t1 t2: value_type) (sx: option sx) f0:
  cvt t2 sx v = Some v' ->
  types_agree t1 v ->
  ↪[frame] f0 -∗
  Φ (immV [v']) -∗
    WP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hcvtop Htype) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_convert_success.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.

Lemma wp_cvtop_reinterpret (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v': value) (t1 t2: value_type) f0:
  wasm_deserialise (bits v) t2 = v' ->
  types_agree t1 v ->
  ↪[frame] f0 -∗
  Φ (immV [v']) -∗
    WP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hcvtop Htype) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_reinterpret.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.

(* Non-numerics -- stack operations, control flows *)

Lemma wp_nop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) f0:
  ↪[frame] f0 -∗
  Φ (immV []) -∗
    WP [AI_basic (BI_nop)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_nop.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.




Lemma wp_drop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) v f0 :
  ↪[frame] f0 -∗
  Φ (immV []) -∗
    WP [AI_basic (BI_const v) ; AI_basic BI_drop] @ s; E {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf0 HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[[ hs ws ] locs ] inst ].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple ; apply rs_drop.
  - destruct σ as [[[ hs ws ] locs ] inst ].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[ hs' ws' ] locs' ] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H.
Qed.

Lemma wp_select_false (s: stuckness) (E :coPset) (Φ : val -> iProp Σ) n v1 v2 f0 :
  n = Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  Φ (immV [v2]) -∗ WP [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                      AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_select) ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hn) "Hf0 HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v2)], σ, [].
    destruct σ as [[[ hs ws ] locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply r_simple ; by apply rs_select_false.
  - destruct σ as [[[ hs ws ] locs ] inst ].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[ hs' ws' ] locs' ] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H.
Qed.

Lemma wp_select_true (s: stuckness) (E : coPset) (Φ: val -> iProp Σ) n v1 v2 f0 :
  n <> Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  Φ (immV [v1]) -∗ WP [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                      AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_select) ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hn) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v1)], σ, [].
    destruct σ as [[[ hs ws ] locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply r_simple ; by apply rs_select_true.
  - destruct σ as [[[ hs ws ] locs ] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[ hs' ws' ] locs' ] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H.
Qed.
    
(* Control flows *)

            
Lemma wp_br (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n vs es i LI lh f0:
  const_list vs ->
  length vs = n ->
  lfilled i lh (vs ++ [::AI_basic (BI_br i)]) LI ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP (vs ++ es) @ s; E {{ v, Φ v ∗ ↪[frame] f0 }})
  -∗ WP [AI_label n es LI] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hvs Hlen Hfill) "Hf0 HΦ".
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  - iPureIntro. destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], (vs ++ es), σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    constructor. econstructor =>//.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H;
    try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_br i)]
                    (vs ++ [AI_basic (BI_br i)])) ;
      first (by unfold lfilled, lfill ; rewrite Hvs ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill'] ;
    eapply lfilled_implies_starts in Hfill' => //= ;
    unfold first_instr in Hstart ; simpl in Hstart ;
    unfold first_instr in Hfill' ; rewrite Hfill' in Hstart ;
    inversion Hstart.
Qed.

Lemma wp_block (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s  f0 :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_label m [::] (vs ++ to_e_list es)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }})
  -∗ WP (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hvs Hlen1 Hlen2 Hlen3) "Hf0 HΦ".
  iApply wp_lift_step => //=.
  apply to_val_cat_None2. done.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  - iPureIntro. destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], _, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    constructor. econstructor =>//.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H as [H | [Hstart | [ [a Hstart] |
                                               (Hstart & Hstart1 & Hstart2 & Hσ) ]]];
      last (by eapply r_simple, rs_block) ;
      first (inversion H; subst; clear H ; by iExists f0; iFrame) ;
      rewrite first_instr_const in Hstart => //=.
Qed.

Lemma wp_label_value (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es m ctx v f0 :
  iris.to_val es = Some (immV v) -> 
  ↪[frame] f0 -∗
  Φ (immV v) -∗ WP [::AI_label m ctx es] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hval) "Hf0 HP".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], es, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.  apply rs_label_const.
    eapply to_val_const_list. apply Hval.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es1 σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H as [H | [Hstart | [ [a Hstart] | (Hstart & Hstart1 & Hstart2
                                                             & Hσ)]]] ;
      (try by apply r_simple ; apply rs_label_const ;
       eapply to_val_const_list ; apply Hval) .
    + (* The only possible case. *)
      inversion H; subst; clear H.
      rewrite Hval.
      iExists f0.
      iFrame.
      iSplit => //.
      by iIntros.
    (* All of the rest are impossible reductions since es is a value. *)
    all: try by unfold first_instr in Hstart ; simpl in Hstart ;
      remember (find_first_some (map first_instr_instr es)) as fes ;
      destruct fes => //= ;
                     apply to_val_const_list in Hval ;
                     eapply starts_implies_not_constant in Hval ; first (by exfalso) ;
                     unfold first_instr ; rewrite <- Heqfes.
Qed.
(* This lemma turned out not being used in wp_label_trap ; leaving it here for possible
   future usage *)
(*
Lemma lfilled_trap_to_val k lh LI :
  lfilled k lh [AI_trap] LI ->
  (LI = [AI_trap] \/ to_val LI = None).
Proof.
  intro Hfill. destruct k ; unfold lfilled, lfill in Hfill.
  { destruct lh ; last by false_assumption.
    destruct (const_list l) ; last by false_assumption.
    apply b2p in Hfill. subst.
    induction l.
    { destruct l0. { left ; by rewrite app_nil_r. }
      right. unfold to_val, iris.to_val => //=. } 
    right. destruct IHl as [Htrap | HNone].
    apply app_eq_unit in Htrap as [[ -> Htrap ] | [ _ Habs]].
    apply app_eq_unit in Htrap as [[ Habs _ ] | [ _ ->  ]] => //=.
    destruct a => //=. destruct b => //=.
    apply app_eq_nil in Habs as [? ?] => //=.
    replace ((a :: l)%SEQ ++ [AI_trap] ++ l0) with ([a] ++ (l ++ [AI_trap] ++ l0)).
    by apply to_val_cat_None2. done. }
  fold lfill in Hfill. destruct lh ; first by false_assumption.
  destruct (const_list l) ; last by false_assumption.
  destruct (lfill _ _ _ ) ; last by false_assumption.
  apply b2p in Hfill. right.
  subst ; induction l ; first unfold to_val, iris.to_val => //=.
  replace ((a :: l)%SEQ ++ (AI_label n l0 l2 :: l1)%SEQ) with
    ([a] ++ (l ++ AI_label n l0 l2 :: l1)) ; last done.
  by apply to_val_cat_None2.
Qed.
  *)
    

Lemma wp_label_trap (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es m ctx f0 :
  iris.to_val es = Some trapV -> 
  ↪[frame] f0 -∗
  Φ trapV -∗ WP [::AI_label m ctx es] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hval) "Hf0 HP".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply to_val_trap_is_singleton in Hval as ->.
    apply r_simple.  apply rs_label_trap.
  - apply to_val_trap_is_singleton in Hval as ->.
    destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es1 σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    (* Here, the conclusion of reduce_det is not strong enough, so we re-do the proof
       of this subcase by hand, since in this particular case, we can get a 
       stronger result *)
    remember [AI_label m ctx [AI_trap]] as es0.
    remember {| f_locs := locs ; f_inst := inst |} as f.
    remember {| f_locs := locs' ; f_inst := inst' |} as f'.
    rewrite <- app_nil_l in Heqes0.
    induction H ; (try by inversion Heqes0) ;
      try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
    { destruct H ; (try by inversion Heqes0) ;
        try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
      - inversion Heqes0 ; subst. inversion H.
      - inversion Heqes0 ; subst. inversion Heqf' ; subst.
        iExists f0.
        iFrame. iSplit => //. by iIntros.
      - inversion Heqes0 ; subst. simple_filled H1 i lh bef aft n l l'.
        found_intruse (AI_basic (BI_br 0)) H1 Hxl1.
        apply in_or_app. right. apply in_or_app. left.
        apply in_or_app. right => //=. by left.
      - rewrite Heqes0 in H0. filled_trap H0 Hxl1. }
    rewrite Heqes0 in H0.
    unfold lfilled, lfill in H0 ; destruct k.
    { destruct lh ; last by false_assumption.
      destruct (const_list l) ; last by false_assumption.
      apply b2p, Logic.eq_sym in H0 ; simpl in H0.
      apply app_eq_unit in H0 as [[ -> H0 ] | [_ Habs]].
      apply app_eq_unit in H0 as [[ -> _] | [-> ->]] => //=.
      apply test_no_reduce0 in H. by exfalso.
      unfold lfilled, lfill in H1 ; simpl in H1. apply b2p in H1.
      rewrite app_nil_r in H1 ; subst.
      apply IHreduce => //=.
      apply app_eq_nil in Habs as [-> _].
      by apply test_no_reduce0 in H. }
    fold lfill in H0. destruct lh ; first by false_assumption.
    destruct (const_list l) ; last by false_assumption.
    remember (lfill _ _ _) as fill ; destruct fill ; last by false_assumption.
    apply b2p, Logic.eq_sym in H0. simpl in H0.
    apply app_eq_unit in H0 as [[ _ H0 ] | [ _ Habs]].
    inversion H0 ; subst.
    unfold lfill in Heqfill ; destruct k.
    { destruct lh ; last by inversion Heqfill.
      destruct (const_list l0) ; inversion Heqfill.
      apply Logic.eq_sym, app_eq_unit in H3 as [[ _ H3 ]|[ _ Habs]].
      apply app_eq_unit in H3 as [[ -> _ ]|[ -> _]].
      by apply test_no_reduce0 in H.
      by apply test_no_reduce_trap in H.
      apply app_eq_nil in Habs as [-> _] ; by apply test_no_reduce0 in H. }
    fold lfill in Heqfill.
    destruct lh ; first by inversion Heqfill.
    destruct (const_list l0) ; last by inversion Heqfill.
    destruct (lfill k lh es) ; inversion Heqfill.
    found_intruse (AI_label n l1 l3) H3 Hxl1.
    inversion Habs.
Qed.

Lemma wp_val_return (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs vs' es' es'' n f0 :
  const_list vs ->
  ↪[frame] f0 -∗
  (↪[frame] f0 -∗ WP vs' ++ vs ++ es'' @ s; E {{ v, Φ v ∗ ↪[frame] f0 }})
  -∗ WP vs @ s; E CTX 1; LH_rec vs' n es' (LH_base [] []) es'' {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hconst) "Hf0 HWP".
  iLöb as "IH".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  inversion Hfill;subst.
  inversion H8;subst.
  assert (vs' ++ [AI_label n es' ([] ++ vs ++ [])] ++ es''
          = ((vs' ++ [AI_label n es' ([] ++ vs ++ [])]) ++ es''))%SEQ as ->.
  { erewrite app_assoc. auto. }
  apply const_list_is_val in Hconst as [v1 Hv1].
  apply const_list_is_val in H7 as [v2 Hv2].
  eapply to_val_cat_inv in Hv1 as Hvv;[|apply Hv2].
  iApply (wp_seq _ _ _ (λ v, (⌜v = immV (v2 ++ v1)⌝ ∗ ↪[frame] f0)%I)).
  iSplitR; first by iIntros "(%H & ?)".
  iSplitR "HWP".
  - iApply wp_val_app; first by apply Hv2.
    iSplit; first by iIntros "!> (%H & ?)".
    iApply (wp_label_value with "[$]") => //=; first by erewrite app_nil_r; apply Hv1 .
  - iIntros (w) "(-> & Hf0)".
    erewrite iris.of_to_val => //.
    rewrite app_assoc.
    by iApply "HWP".
Qed.

Lemma wp_base (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs vs' es'' :
  const_list vs ->
  WP vs' ++ vs ++ es'' @ s; E {{ Φ }}
  ⊢ WP vs @ s; E CTX 0; LH_base vs' es'' {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  inversion Hfill;subst. iFrame.
Qed.

Fixpoint push_base (lh : lholed) n es' vs_pre es_post :=
  match lh with
  | LH_base vs_pre' es_post' => LH_rec vs_pre' n es' (LH_base vs_pre es_post) es_post'
  | LH_rec vs m es'' lh' es => LH_rec vs m es'' (push_base lh' n es' vs_pre es_post) es
  end.

Fixpoint frame_base (lh : lholed) l1 l2 :=
  match lh with
  | LH_base vs es => LH_base (vs ++ l1) (l2 ++ es)
  | LH_rec vs m es' lh' es => LH_rec vs m es' (frame_base lh' l1 l2) es
  end.

Lemma lfilledInd_push i : ∀ lh n es' es LI l1 l2,
  const_list l1 ->
  lfilledInd i lh ([::AI_label n es' (l1 ++ es ++ l2)]) LI ->
  lfilledInd (S i) (push_base lh n es' l1 l2) es LI.
Proof.
  induction i.
  all: intros lh n es' es LI l1 l2 Hconst Hfill.
  { inversion Hfill;subst.
    constructor. auto. constructor. auto.
    (* apply lfilled_Ind_Equivalent. cbn. rewrite eqseqE app_nil_r. done.  *)}
  { inversion Hfill;subst. simpl. constructor. auto.
    apply IHi. auto. auto. }
Qed.
Lemma lfilledInd_frame i : ∀ lh l1 es l2 LI,
    const_list l1 ->
    lfilledInd i lh (l1 ++ es ++ l2) LI ->
    lfilledInd i (frame_base lh l1 l2) (es) LI.
Proof.
  induction i.
  all: intros lh l1 es l2 LI Hconst Hfill.
  { inversion Hfill;subst.
    assert (vs ++ (l1 ++ es ++ l2) ++ es'
            = (vs ++ l1) ++ es ++ (l2 ++ es'))%SEQ as ->.
    { repeat erewrite app_assoc. auto. }
    constructor. apply const_list_concat;auto. }
  { inversion Hfill;subst. simpl. constructor. auto.
    apply IHi. auto. auto. }
Qed.
      

Lemma wp_base_push (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es l1 l2 i lh :
  const_list l1 ->
  WP es @ s; E CTX i; frame_base lh l1 l2 {{ Φ }}
  ⊢ WP l1 ++ es ++ l2 @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  apply lfilledInd_frame in Hfill.
  iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
  iPureIntro. by apply lfilled_Ind_Equivalent. auto.
Qed.
Lemma wp_label_push (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh n es' l1 l2 :
  const_list l1 ->
  WP es @ s; E CTX S i; push_base lh n es' l1 l2 {{ Φ }}
  ⊢ WP [::AI_label n es' (l1 ++ es ++ l2)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  apply lfilledInd_push in Hfill.
  iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
  iPureIntro. by apply lfilled_Ind_Equivalent. auto.
Qed.
Lemma wp_label_push_nil (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh n es' :
  WP es @ s; E CTX S i; push_base lh n es' [] [] {{ Φ }}
  ⊢ WP [::AI_label n es' es] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros "HWP".
  iDestruct (wp_label_push with "HWP") as "HWP". auto.
  erewrite app_nil_l. erewrite app_nil_r. done.
Qed.

Lemma lfilled_to_val i  :
  ∀ lh es LI, is_Some (iris.to_val LI) ->
  lfilled i lh es LI ->
  is_Some (iris.to_val es).
Proof.
  induction i.
   { intros lh es LI [x Hsome] Hfill.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill;subst.
    destruct (to_val es) eqn:Hnone;eauto.
    exfalso.
    apply (to_val_cat_None1 _ es') in Hnone.
    apply (to_val_cat_None2 vs) in Hnone.
    rewrite Hnone in Hsome. done.
  }
  { intros lh es LI Hsome Hfill.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill;simplify_eq.
    clear -Hsome. exfalso.
    induction vs =>//=.
    simpl in Hsome. by inversion Hsome.
    simpl in Hsome; inversion Hsome.
    destruct a =>//=.
    destruct b =>//=.
    destruct (iris.to_val (vs ++ [AI_label n es' LI0] ++ es'')%SEQ) eqn:Hcontr.
    apply IHvs;eauto.
    rewrite Hcontr in H. done.
    destruct vs;done.
  }
Qed.

Lemma wp_block_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (i : nat) (lh : lholed) vs t1s t2s es n m f0:
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_label m [::] (vs ++ to_e_list es)] @ s; E CTX i; lh {{ Φ }})
  -∗ WP (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hconst Hn Hn' Hm) "Hf0 HWP".
  iIntros (LI Hfill).
  destruct (iris.to_val LI) eqn:Hcontr.
  { apply lfilled_to_val in Hfill as [v' Hv];eauto.
    assert (iris.to_val [AI_basic (BI_block (Tf t1s t2s) es)] = None) as Hnone;auto.
    apply (to_val_cat_None2 vs) in Hnone.
    rewrite Hv in Hnone. done. }
  unfold wp_wasm_ctx.
  repeat rewrite wp_unfold /wasm_wp_pre/=.
  rewrite Hcontr.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  { iPureIntro. destruct s;auto.
    apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].
    eexists [],_,σ,[]. simpl.
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple. eapply rs_block.
    apply Hconst. apply Hn. apply Hn'. apply Hm. eauto. eauto. }
  destruct σ as [[[hs ws] locs] inst] => //=.
  iApply fupd_mask_intro;[solve_ndisj|].
  iIntros "Hcls" (es1 σ2 efs HStep) "!>!>!>".
  iMod "Hcls". iModIntro.
  destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
  apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
  destruct Hfill' as [LI' Hfill'].
  destruct HStep as [H [-> ->]].
  eapply reduce_det in H as [ H | [Hstart | [ [a Hstart] | (Hstart & Hstart1 & Hstart2
                                                            & Hσ)]]] ;
    try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_block (Tf t1s t2s) es)]
                  (vs ++ [AI_basic (BI_block (Tf t1s t2s) es)])) ;
    first (unfold lfilled, lfill ; rewrite Hconst ; by rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill''] ;
    eapply lfilled_implies_starts in Hfill'' ; (try done) ;
    rewrite Hfill'' in Hstart ; inversion Hstart => //=.
  2: { eapply r_label. apply r_simple. eapply rs_block;eauto. all: eauto. }
  inversion H; subst; clear H.
  iExists f0.
  iFrame. iSplit => //.
  iIntros "Hf0".
  iSpecialize ("HWP" with "[$]").
  by iSpecialize ("HWP" with "[%]").
Qed.

Lemma wp_br_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n vs es i lh vs' es' f0:
  const_list vs ->
  length vs = n ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP (vs' ++ vs ++ es ++ es') @ s; E {{ Φ }})
  -∗ WP vs ++ [::AI_basic (BI_br i)] @ s; E CTX S i; LH_rec vs' n es lh es' {{ Φ }}.
Proof.
  iIntros (Hvs Hlen) "Hf0 HΦ".
  iIntros (LI Hfill).
  destruct (iris.to_val LI) eqn:Hcontr.
  { apply lfilled_to_val in Hfill as [v' Hv];eauto.
    assert (iris.to_val [AI_basic (BI_br i)] = None) as Hnone;auto.
    apply (to_val_cat_None2 (vs)) in Hnone.
    rewrite Hv in Hnone. done. }
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  { apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
    iPureIntro. destruct s;auto.
    apply lfilled_Ind_Equivalent in H8 as Hfill'.
    apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
    destruct Hfill'' as [LI' Hfill''].    
    eexists [],_,σ,[].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.   
    eapply r_label with (lh:=(LH_base vs' es')).
    2: { erewrite cons_middle. apply lfilled_Ind_Equivalent.
         econstructor;auto. }
    2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
    apply r_simple. eapply rs_br.
    apply Hvs. auto. eauto. }
  destruct σ as [[[hs ws] locs] inst] => //=.
  iApply fupd_mask_intro;[solve_ndisj|].
  iIntros "Hcls !>" (es1 σ2 efs HStep).
  iMod "Hcls". iModIntro.
  destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
  apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
  apply lfilled_Ind_Equivalent in H8 as Hfill'.
  apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
  destruct Hfill'' as [LI' Hfill''].    
  destruct HStep as [H [-> ->]]. 
  eapply reduce_det in H as [H | [ Hstart | [ [a Hstart] | (Hstart & Hstart1 & Hstart2 &
                                                              Hσ)]]] ;
    try by apply lfilled_Ind_Equivalent in Hfill ;
    assert (lfilled 0 (LH_base vs []) [AI_basic (BI_br i)]
                    (vs ++ [AI_basic (BI_br i)])) ;
    first (unfold lfilled, lfill ; rewrite Hvs ; by rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln ; (try done) ;
    rewrite Hfilln in Hstart ; inversion Hstart => //=. 
  2: { eapply r_label with (lh:=(LH_base vs' es')).
       2: { apply lfilled_Ind_Equivalent.
            econstructor;auto. }
       2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
       apply r_simple. eapply rs_br. apply Hvs. all:eauto. }
  inversion H; subst; clear H.
  iExists f0.
  iFrame. iSplit => //.
  iIntros "Hf0".
  iSpecialize ("HΦ" with "[$]").
  by erewrite !app_assoc.
Qed.

Lemma wp_loop_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s i lh f0:
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] @ s; E CTX i; lh {{ Φ }})
  -∗ WP vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hvs Hn Hn' Hm) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill].
    assert (iris.to_val [AI_basic (BI_loop (Tf t1s t2s) es)] = None) as HH;auto.
    apply (to_val_cat_None2 vs) in HH. rewrite Hfill in HH. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H as [ H | [Hstart | [ [a Hstart] | (Hstart & Hstart1 & Hstart2
                                                            & Hσ)]]] ;
    try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_loop (Tf t1s t2s) es)]
                  (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)])) ;
    first (unfold lfilled, lfill ; rewrite Hvs ; by rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill''] ;
    eapply lfilled_implies_starts in Hfill'' ; (try done) ;
    rewrite Hfill'' in Hstart ; inversion Hstart => //=.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
  iExists f0.
  iFrame. iSplit => //.
  iIntros "Hf0".
  iSpecialize ("HP" with "[$]").
  by iSpecialize ("HP" with "[%]").
Qed.

Lemma wp_loop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s f0:
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] @ s; E {{ Φ }})
  -∗ WP vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)] @ s; E {{ Φ }}.
Proof.
  iIntros (Hvs Hn Hn' Hm) "Hf0 HP".
  iApply wp_wasm_empty_ctx. iApply (wp_loop_ctx with "[$]") => //.
  iNext.
  iIntros "?"; iSpecialize ("HP" with "[$]").
  by iApply wp_wasm_empty_ctx. 
Qed.

Lemma wp_if_true_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s i lh f0:
  n ≠ Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_block tf e1s)] @ s; E CTX i; lh {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hn) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_if_true;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
    + iExists f0.
      iFrame.
      iIntros "?"; iSpecialize ("HP" with "[$]").
      by iApply "HP".
    all: by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                    [AI_basic (BI_if tf e1s e2s)]
                    [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
Qed.

Lemma wp_if_true (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s f0:
  n ≠ Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_block tf e1s)] @ s; E {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "Hf0 HP".
  iApply wp_wasm_empty_ctx. iApply (wp_if_true_ctx with "[$]");eauto.
  iNext. iIntros "?"; iSpecialize ("HP" with "[$]").
  by iApply wp_wasm_empty_ctx.
Qed.
  
Lemma wp_if_false_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s i lh f0:
  n = Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_block tf e2s)] @ s; E CTX i; lh {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hn) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H as [H | [ Hstart | [[ a Hstart ] |
                                               (Hstart & Hstart1 & Hstart2 & Hσ)]]] ;
    try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                    [AI_basic (BI_if tf e1s e2s)]
                    [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    iExists f0.
    iFrame.
    iSplit => //.
    iIntros "?"; iSpecialize ("HP" with "[$]").
    by iApply "HP".
Qed.

Lemma wp_if_false (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s f0:
  n = Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_block tf e2s)] @ s; E {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "Hf0 HP".
  iApply wp_wasm_empty_ctx. iApply (wp_if_false_ctx with "[$]");eauto.
  iNext. iIntros "?". iApply wp_wasm_empty_ctx.
  by iApply "HP".
Qed.

Lemma wp_br_if_true_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i j lh f0:
  n ≠ Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br i)] @ s; E CTX j; lh {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E CTX j; lh {{ Φ }}.
Proof.
  iIntros (Hn) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_br_if_true;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H ;
    try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                    [AI_basic (BI_br_if i)]
                    [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_br_if i)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
    iExists f0; iFrame.
    iIntros "?". by iApply ("HP" with "[$]").
Qed.

Lemma wp_br_if_true (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i f0:
  n ≠ Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br i)] @ s; E {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "Hf0 HP".
  iApply wp_wasm_empty_ctx. iApply (wp_br_if_true_ctx with "[$]");eauto.
  iNext. iIntros "?". iApply wp_wasm_empty_ctx. by iApply ("HP" with "[$]").
Qed.

(* The following expression reduces to a value reguardless of context, 
   and thus does not need a context aware version *)
Lemma wp_br_if_false (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i f0:
  n = Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [])
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E {{ Φ }}.
Proof.
  iIntros (Hn) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_br_if_false.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.


Lemma wp_br_table_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j k lh f0:
  ssrnat.leq (S (Wasm_int.nat_of_uint i32m c)) (length iss) ->
  List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br j)] @ s; E CTX k; lh {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E CTX k; lh {{ Φ }}.
Proof.
  iIntros (Hiss Hj) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. apply rs_br_table;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H ;
     try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 c))] [])
                    [AI_basic (BI_br_table iss i)]
                    [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_br_table iss i)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
    iExists f0; iFrame.
    iIntros "?"; by iApply ("HP" with "[$]").
Qed.
Lemma wp_br_table (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j f0:
  ssrnat.leq (S (Wasm_int.nat_of_uint i32m c)) (length iss) ->
  List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br j)] @ s; E {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E {{ Φ }}.
Proof.
  iIntros (? ?) "Hf0 HP".
  iApply wp_wasm_empty_ctx. iApply (wp_br_table_ctx with "[$]");eauto.
  iNext. iIntros "?". iApply wp_wasm_empty_ctx. by iApply ("HP" with "[$]"). 
Qed.

Lemma wp_br_table_length_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j lh f0:
  ssrnat.leq (length iss) (Wasm_int.nat_of_uint i32m c) ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br i)] @ s; E CTX j; lh {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E CTX j; lh {{ Φ }}.
Proof.
  iIntros (Hiss) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. apply rs_br_table_length;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H ;
     try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 c))] [])
                    [AI_basic (BI_br_table iss i)]
                    [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_br_table iss i)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
    iExists f0; iFrame.
    iIntros "?"; by iApply ("HP" with "[$]").
Qed.

Lemma wp_br_table_length (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i f0:
  ssrnat.leq (length iss) (Wasm_int.nat_of_uint i32m c) ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br i)] @ s; E {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "Hf0 HP".
  iApply wp_wasm_empty_ctx. iApply (wp_br_table_length_ctx with "[$]");eauto.
  iNext. iIntros "?". iApply wp_wasm_empty_ctx. by iApply ("HP" with "[$]").
Qed.

 (*| rs_return :
      forall n i vs es lh f,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic BI_return]) es ->
        reduce_simple [::AI_local n f es] vs*)
(* return is a contextual rule, but it is also a function rule. Before we tackle with wp, 
   we must have set up the way in which to handle AI_local. 
   intuitively, AI_local functions as a fresh bind, in a fresh ctx, very similar to wp_seq_ctx 
   solution idea: another WP now that can abstract away the AI_local "wrapper", using AI_local 
   instead of AI_label. Note that AI_label and contexts can still occur within an AI_local....
   Main difference is that AI_local is not nested in the same way as label, in which label 
   knows about the nesting structure for br, whereas local "stops" br from exiting.

   Why is there a need for a new WP? because there can be a nested label structure inside a 
   label, and we need to have knowledge of that for the return instruction. The label wrapper
   is always the outermost layer! so current ctxWP does not work for that reason.
*)
(* Frame rules attempt *)

Lemma wp_frame_rewrite (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) es n f:
  WP es @ s; E FRAME n; f {{ v, Φ v }} ⊢
  WP [AI_local n f es] @ s; E {{ v, Φ v }}.
Proof.
  trivial.
Qed.
  
Lemma wp_return (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) es vs vs0 n f0 f i lh:
  iris.to_val vs = Some (immV vs0) ->
  length vs = n ->
  lfilled i lh (vs ++ [AI_basic BI_return]) es ->
  WP vs @ s; E {{ v, Φ v ∗ ↪[frame] f0 }} -∗
  WP [AI_local n f es] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}%I.
Proof.
  iIntros (Hval Hlen Hlf) "HΦ".
  iApply wp_lift_atomic_step => //=.
  rewrite wp_unfold /wasm_wp_pre /=.
  rewrite Hval.
  iIntros (σ ns κ κs nt) "Hσ !>".
  assert (const_list vs) as Hcvs; first by apply to_val_const_list in Hval.
  iSplit.
  - iPureIntro. destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], vs, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    constructor. econstructor =>//.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iModIntro.
    iIntros (es1 σ2 efs HStep).
    iMod "HΦ" as "(HΦ & Hf0)".
    iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
    + iExists f0.
      rewrite Hval.
      iFrame.
      by iIntros "?".
    all: assert (lfilled 0 (LH_base vs []) [AI_basic (BI_return)]
                    (vs ++ [AI_basic (BI_return)]));
      first (by unfold lfilled, lfill ; rewrite Hcvs ; rewrite app_nil_r);
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hlf) as [lh' Hfill'] ;
    eapply lfilled_implies_starts in Hfill' => //= ;
    unfold first_instr in Hstart ; simpl in Hstart ;
    unfold first_instr in Hfill' ; rewrite Hfill' in Hstart ;
    inversion Hstart.
Qed.

Lemma wp_frame_return (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) vs vs0 n f0 f i lh LI:
  iris.to_val vs = Some (immV vs0) ->
  length vs = n ->
  lfilled i lh (vs ++ [AI_basic BI_return]) LI ->
  ( WP vs @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}
  ⊢ WP LI @ s; E FRAME n ; f {{ v, Φ v ∗ ↪[frame] f0 }}).
Proof.
  iIntros (Hval Hlen Hlf) "HΦ".
  by iApply wp_return.
Qed.


Lemma AI_local_reduce hs ws f0 hs' ws' f0' n f es es0':
  reduce hs ws f0 [AI_local n f es] hs' ws' f0' es0' ->
  exists f' es', f0 = f0' /\ es0' = [AI_local n f' es'] /\ reduce hs ws f es hs' ws' f' es'.
Proof.
Admitted.

(*
Lemma AI_local_reduce_frame_indep hs ws f0 n f es hs' ws' f0' es0' f1:
  reduce hs ws f0 [AI_local n f es] hs' ws' f0' es0' ->
  reduce hs ws f1 [AI_local n f es] hs' ws' f1 es0'.
Proof.
Admitted.

Lemma AI_local_reduce_frame_const hs ws f0 n f es hs' ws' f0' es0':
  reduce hs ws f0 [AI_local n f es] hs' ws' f0' es0' ->
  f0 = f0'.
Proof.
Admitted.
*)

(* This is not true (corner cases), but assumed for convenience temporarily. It
   is almost the same as the prim_step_split lemma.
   TODO: change to use the prim_step_split lemma instead.
 *)
Lemma reduce_tmp es1 es2 es' hs ws f hs' ws' f':
  iris.to_val es1 = None ->
  reduce hs ws f (es1 ++ es2) hs' ws' f' es' ->
  exists es1', reduce hs ws f es1 hs' ws' f' es1' /\ es' = (es1' ++ es2).
Proof.
Admitted.





(* Trying to resolve the problem by naively not allowing any consumption of ↪ in
   the WP premises.

   However, we then cannot connect the resulting frame after executing es1 to 
   that at the start of es2: the only way to achieve that is to have a 
   ↪[frame] in the post condition of es1; but to prove any WP with that post
   condition, we need to provide a ↪[frame] to its precondition as well; 
   so we will need two copies of the same ↪ to prove any WP, rendering the 
   spec useless.

   What we need in the post condition is some predicate like ↪ which gives
   us the knowledge of the new frame, but does not actually assert any 
   ownership -- in some sense, we need to be able to assert 0 ownership of 
   something while still asserting the knowledge of that value. This seems to
   be a weird feature to ask for, however.
 *)
(* Upd: THIS IS DONE!!!!
        Note how the post condition successfully prevents the leakage of any
        frame resources from the inner to the outer frame via Ψ -- the outer 
        frame predicate remains unchanged despite that it could undergo 
        arbitrary changes inside the frames. *)
Lemma wp_frame_seq es1 es2 n (f0 f f': frame) E Ψ Φ:
  ( ↪[frame] f0) -∗
  (¬ (Ψ trapV)) -∗
  ((↪[frame] f) -∗ WP es1 @ NotStuck; E {{ v, ↪[frame] f' ∗ Ψ v }}) -∗
  (∀ w, ↪[frame] f0 -∗ (Ψ w) -∗ WP (iris.of_val w ++ es2) @ NotStuck; E FRAME n; f' {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
  (WP (es1 ++ es2) @ NotStuck; E FRAME n ; f {{ v, Φ v ∗ ↪[frame]f0 }}).
(* WP [AI_local n f (es1 ++ es2)] @ NotStuck; E {{ v, Φ v }} *)
Proof.
  iLöb as "IH" forall (f0 f f' E es1 es2 Ψ Φ n).
  iIntros "Hf0 Hntrap Hwp1 Hwp2".
  unfold wp_wasm_frame.
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  destruct (iris.to_val es1) as [vs|] eqn:Hetov.
  
  { (* when es1 is a value, the post condition of the first wp needs to
       provide enough information for the second wp to work. *)
    iIntros (σ ns κ κs nt) "Hσ".
    destruct σ as [[[hs ws] locs] inst].
    iDestruct "Hσ" as "(Hfunc&Ht&Hm&Hg& Hframe & Hmemlen)".
    (* We must always remember to link the frame predicate to the state interp:
       else we lose their relationship when we update the state later. *)
    iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf".
    rewrite lookup_insert in Hf.
    inversion Hf; subst; clear Hf.
    iMod (ghost_map_update with "Hframe Hf0") as "(Hframe & Hf0)".
    instantiate (1 := f).
    iSpecialize ("Hwp1" with "[$]").
    iMod "Hwp1" as "(Hf' & HΨ)".
    (* Again, must remember to link f' to the state interp here *)
    iDestruct (ghost_map_lookup with "Hframe Hf'") as "%Hf'".
    rewrite lookup_insert in Hf'.
    inversion Hf'; subst; clear Hf'.
    iMod (ghost_map_update with "Hframe Hf'") as "(Hframe & Hf')".
    instantiate (1 := (Build_frame locs inst)).
    iSpecialize ("Hwp2" $! vs with "[$] [$]").
    rewrite wp_unfold /wasm_wp_pre /=.
    repeat rewrite insert_insert.
    iSpecialize ("Hwp2" $! (hs, ws, locs, inst) ns κ κs nt
                   with "[$Hfunc $Ht $Hm $Hg Hframe $Hmemlen]"); first by destruct f'.
    iMod "Hwp2" as "(%Hreducible & Hwp2)".
    iModIntro.
    apply of_to_val in Hetov as <-.
    by iSplit.
  }
  { 
    iIntros (σ ns κ κs nt) "Hσ".
    destruct σ as [[[hs ws] locs] inst].
    iDestruct "Hσ" as "(Hf & Ht & Hm & Hg & Hframe & Hmemlen)".
    iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
    rewrite lookup_insert in Hf0.
    inversion Hf0; subst; clear Hf0.
    iMod (ghost_map_update with "Hframe Hf0") as "(Hframe & Hfx)".
    instantiate (1 := f).
    iSpecialize ("Hwp1" with "Hfx").
    iSpecialize ("Hwp1" $! (hs, ws, f.(f_locs), f.(f_inst)) ns [] κs nt).
    rewrite insert_insert.
    iSpecialize ("Hwp1" with "[$Hf $Ht $Hm $Hg $Hmemlen Hframe]"); first by destruct f => /=.
    iMod "Hwp1" as "(%Hreducible & Hwp1)".
    iModIntro.
    iSplit.
    { (* reducibility of seq within AI_local. *)
      iPureIntro.
      unfold reducible, language.reducible, language.prim_step in *.
      destruct Hreducible as [κ' [es'[σ'[efs HStep]]]].
      destruct σ' as [[[hs' ws'] locs'] inst'].
      exists κ', [AI_local n (Build_frame locs' inst') (es' ++ es2)], (hs', ws', locs, inst), [].
      simpl in *.
      destruct HStep as [Hreduce [-> ->]].
      repeat split => //.
      apply r_local.
      destruct f.
      by apply r_elimr.
    }
    iIntros (es' σ' efs HStep).
    destruct σ' as [[[hs' ws'] locs'] inst'].

    inversion HStep as [Hreduce [-> ->]].
    apply AI_local_reduce in Hreduce as [f'' [es'' [Hf0 [-> Hreduce]]]].
    inversion Hf0; subst; clear Hf0.
    apply reduce_tmp in Hreduce as [es1' [Hreduce' ->]] => //.
    iSpecialize ("Hwp1" $! es1' (hs', ws', f''.(f_locs), f''.(f_inst)) [] with "[%]"); first ((repeat split); by destruct f, f'') => //=.
  
    (* We can't eliminate all the modalities -- one fupd needs to remain for us
       to update the frame back. But the masks in Hwp1 can be stripped *)
    iMod "Hwp1".
    do 2 iModIntro.
    iMod "Hwp1".
    iModIntro.
    iMod "Hwp1".

    iDestruct "Hwp1" as (f1) "((?&?&?&?& Hframe &?) & Hf1 & Hwp1 & ?)".

    (* Establish the relationship between f1 and f'' the cell gets consumed. This
       is also the reason that we can have an arbitrary existential in the 
       definition of the weakest precondition fixpoint. *)
    iDestruct (ghost_map_lookup with "Hframe Hf1") as "%Hf".
    rewrite lookup_insert in Hf.
    inversion Hf; subst; clear Hf.
    
    
    (* Now we do have the ↪; modify the ghost_map back to f0 *)
    iMod (ghost_map_update with "Hframe Hf1") as "(Hframe & Hf1)".
    instantiate (1 := Build_frame locs' inst').
    rewrite insert_insert.
    iExists (Build_frame locs' inst').
  
    iModIntro.
    iFrame => /=.

    iIntros "Hf1".
    
    iApply ("IH" with "[Hf1] [Hntrap] [Hwp1]") => //.
    destruct f''.
    iIntros "?"; iSpecialize ("Hwp1" with "[$]").
    by iAssumption.
  }
(*
   The key that enables the above to be proved is the modification of wp: instead
   of only knowing that a frame predicate exists at the end, we now know that
   it exists at each step. Note that this could not have worked without changing
   the wp: the statement that there is always a frame ownership is not an
   universal property of Iris, but a property of the Wasm semantics instead.
   As a result, we need this specific version of wp to prove this result.
   Also, we need to prove that every reduction respects this preservation of 
   the existence of a frame ownership.
 *)
Qed.

(* This is provable, of course. But how can we deal with recursive functions
   by this and the above? *)
Lemma wp_invoke_native E vcs ves finst ts1 ts2 ts es a Φ m f0:
  iris.to_val ves = Some (immV vcs) ->
  length vcs = length ts1 ->
  length ts2 = m ->
  ↪[frame] f0 -∗
  (↪[frame] f0 -∗ WP ([AI_basic (BI_block (Tf [] ts2) es)]) @ NotStuck; E FRAME m; (Build_frame (vcs ++ n_zeros ts) finst) {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
  (N.of_nat a) ↦[wf] (FC_func_native finst (Tf ts1 ts2) ts es) -∗
  WP (ves ++ [AI_invoke a]) @ NotStuck; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  move => Htoval Harglen Hretlen.
  iIntros "Hf0 Hwp Hfunc".
  iApply wp_lift_step; first by apply to_val_cat_None2.
  
  iIntros (σ n κ κs nt) "Hσ".
  destruct σ as [[[hs ws] locs] inst].
  iDestruct "Hσ" as "(Hf & Ht & Hm & Hg & Hframe & Hmemlen)".
  iDestruct (gen_heap_valid with "Hf Hfunc") as "%Hfunc".
  rewrite gmap_of_list_lookup Nat2N.id in Hfunc.
  rewrite - nth_error_lookup in Hfunc.
          
  assert (reduce hs ws {|f_locs := locs; f_inst := inst|} (ves ++ [AI_invoke a]) hs ws {|f_locs := locs; f_inst := inst|} ([AI_local m (Build_frame (vcs ++ n_zeros ts) finst) [AI_basic (BI_block (Tf [] ts2) es)]])) as Hred.
  {
    eapply r_invoke_native; first by apply Hfunc.
    all: try by eauto.
    apply iris.of_to_val in Htoval.
    subst.
    by elim vcs.
  }
  
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "Hmask".
  iSplit.
  (* reducibility *)
  - iPureIntro.
    exists [].
    eexists.
    exists (hs, ws, locs, inst), [].
    simpl.
    by repeat split => //.
    
  - iIntros (es' σ' efs HStep).
    destruct σ' as [[[hs' ws'] locs'] inst'].

    iModIntro.
    iMod "Hmask".
    iModIntro.
    iSimpl.

    inversion HStep as [Hred' [-> ->]].
    (* Wait, we do not have reduce_det for invoke; but it ought to be true... *)
    admit.
    (*eapply reduce_det in Hred => //.
    inversion Hred; subst; clear Hred.

    iExists f0.
    
    by iFrame.*)
Admitted.
(*
(*
  The sequence rule for AI_local, like wp_seq_ctx for AI_label.
  However, this is much more complicated:
  - we're not remembering the entire call stack in the WP assertion, so there's
    some deduction required;
  - resources for the frame need to be create in-place for the instructions
    inside the frame. This needs to be done in a similar fashion as
    gen_heap_alloc.
*)
Lemma wp_frame_seq (s: stuckness) (E: coPset) (Φ Ψ: val -> iProp Σ) (es1 es2: language.expr wasm_lang) (wf wf': frame) (n: nat) (P: iProp Σ) (cs: list frame):
  length wf.(f_locs) = length wf'.(f_locs) ->
  ((¬ Ψ trapV) ∗
    ((P ∗ stack_interp (rcons cs wf)) -∗
     WP es1 @ NotStuck; E {{ w, Ψ w ∗ stack_interp (rcons cs wf') }}) ∗
  (∀ w, (Ψ w ∗ stack_interp cs) -∗ WP (iris.of_val w ++ es2) @ s; E FRAME n; wf' {{ v, Φ v ∗ stack_interp cs }})
  ⊢ (P ∗ stack_interp cs) -∗ WP es1 ++ es2 @ s; E FRAME n; wf {{ v, Φ v ∗ stack_interp cs }})%I.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ wf wf' n P cs).
  iIntros (Hflen) "(Hntrap & Hes1 & Hes2)".
  iIntros "(HP & Hcs)".
  unfold wp_return_frame.
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  iIntros (σ ns κ κs nt) "hσ".
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "hmask".
  iSplit.
  { (* reducibility *)admit. }
  iIntros (es' σ' efs HStep).
  destruct σ as [[[hs ws] locs] inst].
  destruct σ' as [[[hs' ws'] locs'] inst'].
  iDestruct "Hσ" as "(Hf & Ht & Hm & Hg & Hcsi & Hγ)".
  iDestruct "Hcsi" as (cs0) "(Hcs0 & %Hstack)".
  iMod (gen_heap_update with "Hcs0 Hli") as "(Hl & Hli)".
Admitted.

Definition xx i := (VAL_int32 (Wasm_int.int_of_Z i32m i)).
Definition xb b := (VAL_int32 (wasm_bool b)).

Definition my_add : expr :=
  [AI_basic (BI_const (xx 3));
     AI_basic (BI_const (xx 2));
  AI_basic (BI_binop T_i32 (Binop_i BOI_add))].

Lemma frame_ex1 f f0 s E:
  frame_interp f ⊢ WP [AI_local 1 f0 (my_add ++ [AI_basic BI_return])] @ s; E {{ v, ⌜ v = immV [xx 5] ⌝ ∗ frame_interp f }}.
Proof.
  iIntros "Hf".
  iApply wp_frame_rewrite.
  iApply wp_frame_seq => //.
  instantiate (1 := fun x => (⌜ x = immV [xx 5] ⌝)%I).
  instantiate (1 := (emp)%I).
  2: { by iFrame. }
  iSplit; first trivial.
  iSplitL.
  - iIntros "[_ H]".
    iApply wp_wand.
    instantiate (1 := fun x => (⌜ x = immV [xx 5] ⌝)%I); first by iApply wp_binop.
    iSimpl.
    iIntros (v Hv).
    subst.
    by iFrame.
  - iIntros (w) "[%Hw Hf]".
    subst.
    iApply wp_frame_return; last by iFrame; eauto.
    + by instantiate (1 := [AI_basic (BI_const (xx 5))]).
    + trivial.
    + instantiate (1 := LH_base [::] [::]).
      instantiate (1 := 0).
      by unfold lfilled, lfill => /=.
Qed.
*)
                      
(*
Definition frame_push_local (ls: lstack) n f := rcons ls (n, f, 0, LH_base [::] [::]).
 *)
(*
Fixpoint inner_frame (ls: lstack) : option frame :=
  match ls with
  | [::] => None
  | [::(n, f, k, lh)] => Some f
  | cf :: cs => inner_frame cs
  end.

Fixpoint update_inner_frame (ls: lstack) (f: frame) : option lstack :=
  match ls with
  | [::] => None
  | [::(n, f', k, lh)] => Some [::(n, f, k, lh)]
  | cf :: cs => match update_inner_frame cs f with
              | Some ls' => Some (cf :: ls')
              | None => None
              end
  end.
*)


(* 
  The main difference here is that, changes in frames (AI_local) have impact on the local variables from the aspect of the internal expression, which are part of the state -- while pushing a label has no such impact. 

  We need to somehow account for this whenever we enter or leave a call frame. In particular, in both the 2nd and the 3rd premises, we need to give them resources of the locals and current instance -- whatever they produce, the corresponding modification needs to be made to the frame stored in the lstack construct. In some sense we're providing a wrapper for the internal instructions to execute.
 *)

(* Firstly, we could enter a local frame by temporarily forget about the current frame and construct the new frame 
   resources in place. 

   We ensure that no frame resources from inside is leaked to the outer frame by forcing the inner frame information 
   to be separated by (frame_interp f'); the requirement that f' has the same number of locals guarantee that no local
   variable inside the frame could escape from the frame.
   

 *)
(*
Lemma wp_frame_push_local (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) n f n0 f0 es:
  (*  length f.(f_locs) = length f'.(f_locs) -> *)
  WP es @ NotStuck; E FRAME n ; f {{ v, Φ v }} ⊢
  WP [AI_local n f es] @ s; E FRAME n0 ; f0 {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es Φ n f n0 f0).
  iIntros "Hwp".
  unfold wp_return_frame.
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  iIntros (σ ????) "Hσ".
  destruct σ as [[[hs ws] locs] inst].
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "Hmask".
  iSplit.
  { destruct s => //=.
    iSpecialize ("Hwp" $! (hs, ws, locs, inst) ns κ κs nt with "Hσ").
    iPureIntro.
    econstructor.
    eexists.
    (* This will not work, instead it's just for observation. *)
    exists (hs, ws, locs, inst), [].
    unfold language.prim_step => /=.
    repeat split => //.
    apply r_local.
    admit.
  }
Admitted.
*)

(* basic instructions with non-simple(non-pure) reductions *)

(* Function related *)

Lemma wp_call: False.
Proof.
Admitted.

Lemma wp_call_indirect: False.
Proof.
Admitted.



(* Instance related *)
(*
Lemma wp_get_local (s : stuckness) (E : coPset) (v: value) (i: nat) (ϕ: val -> Prop):
  ϕ (immV [v]) ->
  N.of_nat i ↦[wl] v ⊢
  WP ([AI_basic (BI_get_local i)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ N.of_nat i ↦[wl] v }}.
Proof.
  iIntros (Hϕ) "Hli".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] inst].
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ? & ?)".
  iDestruct (gen_heap_valid with "Hl Hli") as "%Hli".
  rewrite gmap_of_list_lookup Nat2N.id in Hli.
  rewrite - nth_error_lookup in Hli.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v)], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by apply r_get_local.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.

Lemma wp_set_local (s : stuckness) (E : coPset) (v v0: value) (i: nat) (ϕ: val -> Prop):
  ϕ (immV []) ->
  N.of_nat i ↦[wl] v0 ⊢
  WP ([AI_basic (BI_const v); AI_basic (BI_set_local i)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ N.of_nat i ↦[wl] v }}.
Proof.
  iIntros (Hϕ) "Hli".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] inst].
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ? & ?)".
  iDestruct (gen_heap_valid with "Hl Hli") as "%Hli".
  assert (i < length locs) as Hlength.
    { rewrite gmap_of_list_lookup Nat2N.id in Hli.
      by apply lookup_lt_Some in Hli.
    }
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], (hs, ws, set_nth v locs i v, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_set_local => //=.
    unfold lt in Hlength.
    (* Here, we need to prove [ ssrnat.leq a b ] from hypothesis [ a <= b ].
       I gave up, could someone help ? *) admit.
  - iIntros "!>" (es σ2 efs HStep).
    (* modify locs[i]. This has to be done before the update modality is used. *)
    iMod (gen_heap_update with "Hl Hli") as "(Hl & Hli)".
    iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H as [H | [ Hstart | [[ a Hstart ] | (Hstart & Hstart1 & Hstart2
                                                               & Hσ)]]] ;
      last (eapply r_set_local with (f' := {| f_locs := set_nth v locs i v; f_inst := inst |}); eauto) ;
    try by unfold first_instr in Hstart ; simpl in Hstart ; inversion Hstart.
    inversion H; subst; clear H.
    iFrame.
    repeat iSplit => //.
    rewrite - gmap_of_list_insert; rewrite Nat2N.id => //.
    by erewrite fmap_insert_set_nth.
    simpl. unfold lt in Hlength. (* same problem with ssreflect as above *) admit.
Admitted.


(* tee_local is not atomic in the Iris sense, since it requires 2 steps to be reduced to a value. *)
Lemma wp_tee_local (s : stuckness) (E : coPset) (v v0: value) (n: nat) (ϕ: val -> Prop):
  (not (ϕ trapV)) ->
  ϕ (immV [v]) ->
  N.of_nat n ↦[wl] v0 ⊢
  WP ([AI_basic (BI_const v); AI_basic (BI_tee_local n)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ N.of_nat n ↦[wl] v }}.
Proof.
  iIntros (Hntrap Hϕ) "Hli".
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  destruct σ as [[[hs ws] locs] inst].
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "Hfupd".
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ? & ?)".
  iDestruct (gen_heap_valid with "Hl Hli") as "%Hli".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v); AI_basic (BI_const v); AI_basic (BI_set_local n)], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_tee_local => //.
  - iIntros "!>" (es σ2 efs HStep).
    iMod "Hfupd".
    iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
    inversion H; subst; clear H.
    iFrame.
    repeat iSplit => //.
    iApply wp_val => //=.
    iSplitR => //; first by iIntros "(%HContra & _)". 
    iApply wp_mono; last iApply wp_set_local; eauto => //.
Qed.

(* r_get_global involves finding the reference index to the global store via
   the instance first. *)

(* TODO: Weaken the ownership of instance (and global) *)
Lemma wp_get_global (s : stuckness) (E : coPset) (v: value) (inst: instance) (n: nat) (ϕ: val -> Prop) (g: global) (k: nat):
  inst.(inst_globs) !! n = Some k ->
  g.(g_val) = v ->
  ϕ (immV [v]) ->
  (↦[wi] inst ∗
  N.of_nat k ↦[wg] g) ⊢
                      WP ([AI_basic (BI_get_global n)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ ↦[wi] inst ∗ N.of_nat k ↦[wg] g }}.
Proof.
  iIntros (Hinstg Hgval Hϕ) "(Hinst & Hglob)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hg & ? & Hi & ?)".
  iDestruct (gen_heap_valid with "Hg Hglob") as "%Hglob".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  rewrite gmap_of_list_lookup Nat2N.id in Hglob.
  rewrite - nth_error_lookup in Hglob.
  rewrite - nth_error_lookup in Hinstg.
  rewrite lookup_insert in Hinst.
  inversion Hinst; subst; clear Hinst.
  assert ( sglob_val (host_function:=host_function) ws
                     (f_inst {| f_locs := locs; f_inst := inst |}) n =
           Some (g_val g) ) as Hsglob.
  { unfold sglob_val, option_map, sglob, option_bind, sglob_ind => /=.
    by rewrite Hinstg Hglob.
  }
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (g_val g))], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by apply r_get_global.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] winst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.
(*
Print  sglob_val.
Print supdate_glob.
*)
Lemma wp_set_global (s : stuckness) (E : coPset) (v:value) (inst :instance) (n:nat)
      (Φ : val -> Prop) (g: global) (k:nat):
  inst.(inst_globs) !! n = Some k ->
  Φ (immV []) ->
  ( ↦[wi] inst ∗
    N.of_nat k ↦[wg] g) ⊢
                        WP [AI_basic (BI_const v) ; AI_basic (BI_set_global n)] @ s ; E {{ w,  ⌜ Φ w ⌝ ∗ ↦[wi] inst ∗ N.of_nat k ↦[wg] {| g_mut := g_mut g ; g_val := v |} }}.
Proof.
  iIntros (Hinstg HΦ) "[Hinst Hglob]".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[ hs ws] locs ] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hg & ? & Hi & ?)". 
  iDestruct (gen_heap_valid with "Hg Hglob") as "%Hglob".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  rewrite gmap_of_list_lookup Nat2N.id in Hglob.
  rewrite - nth_error_lookup in Hglob.
  rewrite - nth_error_lookup in Hinstg.
  rewrite lookup_insert in Hinst.
  inversion Hinst ; subst ; clear Hinst.
  iDestruct (gen_heap_update with "Hg Hglob") as "H".
  remember {|
      s_funcs := datatypes.s_funcs ws;
      s_tables := datatypes.s_tables ws;
      s_mems := datatypes.s_mems ws;
      s_globals :=
        update_list_at (datatypes.s_globals ws) k
          {| g_mut := g_mut g; g_val := v |}
    |} as ws'.
  assert ( supdate_glob (host_function := host_function) ws
                     (f_inst {| f_locs := locs ; f_inst := inst |}) n v =
             Some ws') as Hsglob.
  { unfold supdate_glob, option_bind, sglob_ind, supdate_glob_s, option_map => /=.
    by rewrite Hinstg Hglob Heqws'. }
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], (hs, ws', locs, inst), [].
    unfold language.prim_step => /=. repeat split => /=.
    by apply r_set_global.
  - iIntros "!>" (es σ2 efs Hstep). iMod "H". iModIntro. 
    destruct σ2 as [[[ hs2 ws2 ] locs' ] inst'].
    destruct Hstep as (H & -> & ->).
    eapply reduce_det in H as [H | [Hstart | [[a Hstart] | (Hstart & Hstart1 & Hstart2
                                                            & Hσ)]]] ;
      last (by econstructor) ; try by unfold first_instr in Hstart ; inversion Hstart.
    inversion H ; subst ; clear H.
    iDestruct "H" as "[Hg Hk]". iFrame.
    destruct ws => //=. simpl in Hsglob.
    assert (N.to_nat (N.of_nat k) < length s_globals) as Hlen.
    { rewrite Nat2N.id. simpl in Hglob. apply nth_error_Some.
      rewrite Hglob ; done. }
    rewrite <- (gmap_of_list_insert (l:= s_globals) {| g_mut := g_mut g ;
                                                     g_val := v |} (n := N.of_nat k) Hlen).
    rewrite Nat2N.id.
    cut (<[k:={| g_mut := g_mut g ; g_val := v |}]> s_globals =
           update_list_at s_globals k {| g_mut := g_mut g ; g_val := v |}).
    intro Heq ; rewrite Heq. repeat iSplit => //=.
    rewrite Nat2N.id in Hlen. unfold update_list_at.
    clear - Hlen. 
    generalize dependent s_globals. 
    induction k ; intros s_globals Hlen. 
    { destruct s_globals.
      { exfalso. simpl in Hlen. lia. }
      simpl. unfold drop. done. }
    destruct s_globals. { exfalso ; simpl in Hlen ; lia. }
    simpl. simpl in IHk. assert (k < (length s_globals)). { simpl in Hlen. lia. }
    rewrite (IHk s_globals H). done.
Qed.


Lemma update_list_same_dom (l : seq.seq global) k v :
  k < length l -> 
  dom (gset N) (gmap_of_list l) = dom (gset N) (gmap_of_list (update_list_at l k v)).
Proof.
  induction k ; unfold update_list_at. 
  destruct l. simpl. intro ; exfalso ; lia.
  intro ; simpl. destruct l. simpl. unfold gmap_of_list. simpl.
  unfold dom, gset_dom, mapset.mapset_dom, mapset.mapset_dom_with, merge, gmap_merge.
  unfold merge, pmap.Pmerge. Search (gmap_of_list _).
  
Admitted. *)

(* Auxiliary lemmas for load/store *)

Lemma store_length (m m': memory) (n: N) (off: static_offset) (bs: bytes) (l: nat) :
  store m n off bs l = Some m' ->
  length m.(mem_data).(ml_data) = length m'.(mem_data).(ml_data).
Proof.
Admitted.

Lemma mem_equiv_length (m m': memory):
  m ≡ₘ m' ->
  mem_length m = mem_length m'.
Proof.
  move => Hm.
  unfold mem_length, memory_list.mem_length.
  by rewrite Hm.
Qed.

Lemma store_data_inj (m1 m2 m1': memory) (n: N) (off: static_offset) (bs: bytes) (l: nat) :
  m1 ≡ₘ m2 ->
  store m1 n off bs l = Some m1' ->
  exists m2', store m2 n off bs l = Some m2' /\ m1' ≡ₘ m2'.
Proof.
  move => Hmequiv Hstore.
  Print memory_list.
  exists (Build_memory (Build_memory_list (ml_init (mem_data m2)) (ml_data (mem_data m1'))) (mem_max_opt m2)).
  unfold store in Hstore.
  unfold store.
Admitted.

Lemma update_list_at_insert {T: Type} (l: list T) (x: T) (n: nat):
  n < length l ->
  update_list_at l n x = <[n := x]> l.
Proof.
  move => Hlen.
  unfold update_list_at.
  move: n x Hlen.
  elim: l => //=.
  - move => n.
    by destruct n; lia.
  - move => a l IH n x Hlen.
    destruct n => //=.
    f_equal.
    apply IH.
    lia.
Qed.
    
(* A version of gen_heap_update specifically for wasm memories. *)
Lemma gen_heap_update_big_wm σ n ml ml':
  gen_heap_interp σ -∗ 
  ([∗ list] i ↦ b ∈ ml, N.of_nat n ↦[wm][N.of_nat i] b) ==∗
  gen_heap_interp ((new_2d_gmap_at_n (N.of_nat n) ml') ∪ σ) ∗
  ([∗ list] i ↦ b ∈ ml', N.of_nat n ↦[wm][N.of_nat i] b).
Proof.
(*  revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
  { rewrite left_id_L. auto. }
  iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
  decompose_map_disjoint.
  rewrite !big_opM_insert // -insert_union_l //.
  by iMod (gen_heap_alloc with "Hσ'σ") as "($ & $ & $)";
    first by apply lookup_union_None.*)
Admitted.


Lemma length_bits v t:
  types_agree t v -> length (bits v) = t_length t.
Proof.
  intros. unfold bits.
  destruct v ; destruct t ; by inversion H.
Qed.


Lemma memory_in_bounds m i b :
  (ml_data (mem_data m)) !! i = Some b -> i < N.to_nat (mem_length m) .
Proof.
  intros. 
  apply lookup_lt_Some in H. unfold mem_length, memory_list.mem_length.
  lia.
Qed.

Lemma those_app {A} (l1 : list (option A)) l2 tl1 tl2 :
  those l1 = Some tl1 -> those l2 = Some tl2 -> those (l1 ++ l2) = Some (tl1 ++ tl2).
Proof.
  generalize dependent tl1. induction l1 ; intros.
  unfold those in H ; inversion H. by rewrite app_nil_l.
  rewrite <- those_those0 in H. 
  unfold those0 in H. destruct a ; try by inversion H.
  fold (those0 l1) in H. rewrite those_those0 in H.
  destruct tl1 ; destruct (those l1) ; inversion H.
  assert (those (l1 ++ l2) = Some (l ++ tl2)) ; first by eapply IHl1.
  rewrite <- those_those0. unfold those0 => //=.
  fold (those0 (l1 ++ l2)). rewrite those_those0 H1. simpl. by subst.
Qed.

Lemma those_app_inv {A} (l1 : list (option A)) l2 tl :
  those (l1 ++ l2) = Some tl ->
  exists tl1 tl2, those l1 = Some tl1 /\ those l2 = Some tl2 /\ tl1 ++ tl2 = tl.
Proof.
  generalize dependent tl ; induction l1 ; intros.
  eexists _, _ ; repeat split => //=.
  rewrite <- app_comm_cons in H.
  rewrite <- those_those0 in H.
  unfold those0 in H. destruct a eqn:Ha ; try by inversion H.
  destruct (those0 (l1 ++ l2)) eqn:Hth ; unfold those0 in Hth ; rewrite Hth in H ;
    try by inversion H.
  fold (those0 (l1 ++ l2)) in Hth.
  rewrite those_those0 in Hth.
  rewrite Hth in IHl1.
  assert (Some l = Some l) ; first done.
  destruct (IHl1 l H0) as (tl1 & tl2 & Hth1 & Hth2 & Htl).
  rewrite <- those_those0.
  unfold those0. fold (those0 l1).
  unfold option_map. rewrite those_those0 Hth1.
  eexists _,_ ; repeat split => //=. rewrite Htl.
  unfold option_map in H. by inversion H.
Qed.

Lemma map_app {A B} (l1 : list A) l2 (f : A -> B) : map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  induction l1 ; intros ; try done.
  simpl. by rewrite IHl1.
Qed. 

Lemma take_drop {A} n (l : list A) : n < length l -> l = seq.take n l ++ seq.drop n l.
Proof.
  intros. generalize dependent n. induction l ; intros.  by inversion H.
  destruct n. by unfold take, drop.
  simpl. rewrite <- (IHl n) => //=. simpl in H ; lia.
Qed.


Lemma those_map_Some (f : nat -> option byte) (l : list byte) :
  (forall x : nat, x < length l -> f x = l !! x) ->
  those (map f (iota 0 (length l))) = Some l.
Proof.
  remember (length l) as n. generalize dependent l.
  induction n ; intros.
  { apply Logic.eq_sym, nil_length_inv in Heqn ; subst ; by unfold those. }
  destruct l ; first by inversion Heqn. 
  cut (exists ys y, b :: l = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (b :: l)) ;
    exists (List.last (b :: l) b) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].
  rewrite Htail. rewrite Htail in Heqn. rewrite Htail in H.
  rewrite app_length in Heqn. simpl in Heqn.
  rewrite Nat.add_1_r in Heqn. inversion Heqn.
  assert (forall x, x < n -> f x = ys !! x).
  { intros. rewrite H ; last lia.
    rewrite lookup_app_l => //=. by rewrite <- H1. }
  destruct n. rewrite <- H1. apply Logic.eq_sym, nil_length_inv in H1. rewrite H1.
  unfold those => //=. rewrite H. rewrite H1 => //=. lia.
  rewrite (take_drop (length ys) (iota 0 (S (length ys)))).
  rewrite take_iota. 
  unfold ssrnat.minn. 
  replace (S (length ys - 1)) with (length ys) ; last by rewrite <- H1 ; lia.
  rewrite ssrnat.leqnn.
  rewrite drop_iota => //=.
  unfold ssrnat.addn , ssrnat.addn_rec. replace (0+length ys) with (length ys) ; last lia.
  unfold ssrnat.subn, ssrnat.subn_rec. replace (S (length ys) - length ys) with 1 ; last lia.
  simpl.
  rewrite map_app. apply those_app. rewrite <- H1. apply (IHn ys H1 H0).
  unfold those => //=. rewrite H. 
  rewrite list_lookup_middle => //=. rewrite <- H1 ; lia.
  replace (length (iota 0 (S (length ys)))) with (seq.size (iota 0 (S (length ys)))) ;
    last done.
  rewrite size_iota. lia.
Qed.




Lemma wms_is_load n k off v m t ws :
  types_agree t v -> s_mems (host_function := host_function) ws !! n = Some m ->
  (N.of_nat n ↦[wms][ k + off ] (bits v) -∗
            gen_heap_interp (gmap_of_memory (s_mems ws))
            -∗ ⌜ load m k off (t_length t) = Some (bits v) ⌝).
Proof.
  iIntros (Htv Hm) "Hwms Hm".
  iAssert ( (∀ i, ⌜ i < length (bits v) ⌝ -∗
                               ⌜ (ml_data (mem_data m)) !! (N.to_nat (k + off + N.of_nat i))
                  = (bits v) !! i ⌝)%I ) as "%Hmeq".
  { iIntros (i) "%Hi".
    iDestruct (big_sepL_lookup with "Hwms") as "H" => //.
    destruct (nth_lookup_or_length (bits v) i (encode 1)) => //=.
    lia.
    iDestruct (gen_heap_valid with "Hm H") as "%H".
    rewrite gmap_of_list_2d_lookup list_lookup_fmap Nat2N.id Hm in H.
    unfold memory_to_list in H. simpl in H. rewrite Nat2N.id in H.
    iPureIntro. replace (N.to_nat (k + off + N.of_nat i)) with
      (N.to_nat (k + off) + i). rewrite H.
    apply Logic.eq_sym.
    destruct (nth_lookup_or_length (bits v) i (encode 1)) => //=.
    lia. lia. } 
  iPureIntro.
  unfold load.
  assert (length (bits v) > 0). erewrite length_bits => //=. destruct t ; simpl ; lia.
  replace (k + (off + N.of_nat (t_length t)) <=? mem_length m)%N with true.
  unfold read_bytes, mem_lookup.
  remember (t_length t) as tl.
  induction tl. { simpl. unfold those => //=. erewrite <- length_bits in Heqtl => //=.
                  apply Logic.eq_sym, nil_length_inv in Heqtl. by rewrite Heqtl. }
  rewrite Heqtl. erewrite <- length_bits => //=.
  apply those_map_Some => //=.
  intros.
  rewrite nth_error_lookup. by apply Hmeq.
  apply Logic.eq_sym, N.leb_le.
  assert (ml_data (mem_data m) !! N.to_nat (k + off + N.of_nat (length (bits v) - 1)) =
            (bits v) !! (length (bits v) - 1)). apply Hmeq ; first lia.
  destruct (nth_lookup_or_length (bits v) (length (bits v) - 1) (encode 1)) => //=. 
  rewrite e in H0.
  apply memory_in_bounds in H0. unfold lt in H0.
  replace (S (N.to_nat (k + off + N.of_nat (length (bits v) - 1)))) with
    (N.to_nat (k + (off + N.of_nat (t_length t)))) in H0. lia.
  rewrite <- N2Nat.inj_succ. 
  rewrite <- N.add_succ_r. 
  rewrite <- Nat2N.inj_succ.
  replace (S (length (bits v) - 1)) with (length (bits v)) ; last lia.
  erewrite length_bits => //=. rewrite N.add_assoc. done.
  lia.
Qed.

Lemma if_load_then_store m addr off val1 val2 size :
  load m addr off size = Some val1 ->
  exists m', store m addr off val2 size = Some m'.
Proof.
  intro Hload.
  unfold store.
  unfold load in Hload.
  rewrite <- N.add_assoc.
  destruct (addr + (off + N.of_nat size) <=? mem_length m)%N ;
    try by inversion Hload.
  unfold write_bytes.
  unfold read_bytes in Hload.
  generalize dependent val1.
  induction size ; intros.
  - by eexists.
  - rewrite (take_drop size (iota 0 (S size))) in Hload.
    rewrite take_iota in Hload.
    unfold ssrnat.minn in Hload. 
    rewrite ssrnat.leqnn in Hload.
    rewrite drop_iota in Hload.
    unfold ssrnat.addn, ssrnat.addn_rec in Hload.
    replace (0+size) with size in Hload ; last lia.
    unfold ssrnat.subn, ssrnat.subn_rec in Hload.
    replace (S size - size) with 1 in Hload ; last lia.
    simpl in Hload.
    rewrite map_app in Hload.
    destruct (those_app_inv _ _ _ Hload) as (tl1 & tl2 & Hth1 & Hth2 & Htl).
    apply IHsize in Hth1.
    destruct Hth1 as [m' Hm].


    simpl. destruct val2 => //=. unfold fold_lefti => //=.
    (* Work in progress *)
    Admitted.



Lemma deserialise_bits v t :
  types_agree t v -> wasm_deserialise (bits v) t = v.
Proof.
  intros Htv.
  unfold wasm_deserialise.
  destruct t ;
    unfold bits ;
    destruct v ; (try by inversion Htv).
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small.
  by rewrite Wasm_int.Int32.repr_unsigned.
  destruct s ; simpl ; replace (two_power_pos (_ * _))
    with Wasm_int.Int32.modulus ; [lia | done].
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small.
  by rewrite Wasm_int.Int64.repr_unsigned.
  destruct s ; simpl ; replace (two_power_pos (_ * _))
    with Wasm_int.Int64.modulus ; [lia | done].
  rewrite Memdata.decode_encode_int_4.
  by rewrite Wasm_float.FloatSize32.of_to_bits.
  rewrite Memdata.decode_encode_int_8.
  by rewrite Wasm_float.FloatSize64.of_to_bits.
Qed.

(* Not quite sure this lemma is even true *)
(*
Lemma bits_deserialise bs t :
  bits (wasm_deserialise bs t) = bs.
Proof.
  unfold wasm_deserialise.
  destruct t.
  unfold bits.
  unfold serialise_i32.
  rewrite Wasm_int.Int32.unsigned_repr.
  Search (Memdata.encode_int _ (Memdata.decode_int _)).
  Search (Memdata.decode_int (Memdata.encode_int _ _)).
  rewrite Memdata.encode_decode_int. *)


Lemma no_memory_no_memories ws n :
  s_mems (host_function := host_function) ws !! n = None ->
  forall k, gmap_of_memory (s_mems ws) !! (N.of_nat n, k) = None.
Proof.
  intros.
  unfold gmap_of_memory.
  rewrite gmap_of_list_2d_lookup => //=.
  rewrite Nat2N.id. 
  rewrite list_lookup_fmap H => //=.
Qed.



Lemma wms_implies_smems_is_Some ws n k b bs :
  gen_heap_interp (gmap_of_memory (s_mems ws)) -∗
                  ([∗ list] i ↦ b  ∈ (b :: bs), mapsto (L:=N*N) (V:=byte)
                                                     (N.of_nat n, N.of_nat (N.to_nat k+i))
                                                     (DfracOwn 1) b) -∗
                  (([∗ list] i ↦ b  ∈ (b :: bs), mapsto (L:=N*N) (V:=byte)
                                                     (N.of_nat n, N.of_nat (N.to_nat k+i))
                                                     (DfracOwn 1) b) ∗
                                                                     gen_heap_interp (gmap_of_memory (s_mems ws)) ∗
                            ⌜ exists m, s_mems (host_function := host_function) ws !! n = Some m ⌝).
Proof.
  iIntros "Hm Hwms".
  unfold big_opL.
  iDestruct "Hwms" as "[Hwm Hwms]".
  rewrite Nat.add_0_r. rewrite N2Nat.id.
  iDestruct (gen_heap_valid with "Hm Hwm") as "%Hm".
  iSplitR "Hm".
  - by iSplitL "Hwm".
  - iSplitL => //=. iPureIntro.
    destruct (s_mems ws !! n) as [m|] eqn:Hn ; first by eexists.
    rewrite no_memory_no_memories in Hm => //=.
Qed.



Lemma wp_load (s:stuckness) (E:coPset) (t:value_type) (v:value)
      (inst:instance) (off: static_offset) (a: alignment_exponent)
      (k: i32) (n:nat) (Φ:val -> Prop) (f0: frame):
  types_agree t v ->
  f0.(f_inst).(inst_memory) !! 0 = Some n ->
  Φ (immV [v]) ->
  ( ↪[frame] f0 ∗
     N.of_nat n ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ]
     (bits v) ⊢
     (WP [AI_basic (BI_const (VAL_int32 k)) ;
          AI_basic (BI_load t None a off)] @ s; E {{ w, ⌜ Φ w ⌝ ∗ ↪[frame] f0 ∗ (N.of_nat n) ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ](bits v) }})).
Proof.
  iIntros (Htv Hinstn HΦ) "[Hf0 Hwms]".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & Hframe & Hγ)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0.
  inversion Hf0; subst; clear Hf0.
  destruct (bits v) eqn:Hb.
  destruct v ; inversion Hb.
  iDestruct (wms_implies_smems_is_Some with "Hm Hwms") as "(Hwms & Hm & %Hm)".
  destruct Hm as [m Hm].
  rewrite <- Hb.
  iDestruct (wms_is_load with "Hwms Hm") as "%Hload" => //=.
  rewrite - nth_error_lookup in Hm.
  rewrite - nth_error_lookup in Hinstn.
  simpl in Hinstn.
  destruct (inst_memory winst) eqn:Hinstmem => //.
  inversion Hinstn; subst; clear Hinstn.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], [AI_basic (BI_const _)], (hs, ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_load_success => //.
    unfold smem_ind.
    by rewrite Hinstmem.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    iExists {| f_locs := locs; f_inst := winst |}.
    (*only_one_reduction H.
    rewrite deserialise_bits in H => //=.
    inversion H ; subst. iFrame. by iPureIntro.
Qed.
*)
Admitted.


Lemma wp_store (s: stuckness) (E: coPset) (t: value_type) (v: value) (*(mem mem': memory)*) (vinit : value) (off: static_offset) (a: alignment_exponent) (k: i32) (n: nat) (ϕ: val -> Prop) (f0: frame) :
  types_agree t v -> types_agree t vinit ->
  f0.(f_inst).(inst_memory) !! 0 = Some n ->
  (*store mem (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = Some mem' -> *)
  ϕ (immV []) ->
  ( ↪[frame] f0 ∗
  N.of_nat n ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ] (bits vinit)) ⊢
  (WP ([AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t None a off)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ ↪[frame] f0 ∗ (N.of_nat n) ↦[wms][ Wasm_int.N_of_uint i32m k + off ] (bits v) }}).
Proof.
  iIntros (Hvt Hvti Hinstn Hϕ) "[Hf0 Hwms]".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & Hframe & Hγ)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0.
  inversion Hf0; subst; clear Hf0.
  destruct (bits vinit) eqn:Hb. destruct vinit ; inversion Hb.
  iDestruct (wms_implies_smems_is_Some with "Hm Hwms") as "(Hwms & Hm & %Hm)".
  destruct Hm as [m Hm].
  rewrite <- Hb.
  iDestruct (wms_is_load with "Hwms Hm") as "%Hload" => //=.
  rewrite - nth_error_lookup in Hm.
  rewrite - nth_error_lookup in Hinstn.
  simpl in Hinstn.
  destruct (inst_memory winst) eqn: Hinstmem => //.
  inversion Hinstn; subst; clear Hinstn.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    edestruct if_load_then_store as [mem Hsomemem] => //=. (* This lemma is currently admitted *)
    eexists [], [], (hs, _ (*upd_s_mem ws (update_list_at (s_mems ws) n m') *), locs, winst), [].
    repeat split => //.
    eapply r_store_success => //=.
    unfold smem_ind.
    by rewrite Hinstmem.
  - iIntros "!>" (es σ2 efs HStep).
    iExists {| f_locs := locs; f_inst := winst |}.
    (* Work in progress *)
Admitted.

(* These might be helpful for completing the proof above : *)
(*
    (* Need something like gen_heap_update_big here to update all at once *)
    iMod (gen_heap_update_big_wm with "Hm Hwmdata") as "(Hm & Hwmdata)".
    iModIntro.
    destruct σ2 as [[[hs2 ws2] locs2] winst2].
    destruct HStep as [HStep [-> ->]].
    only_one_reduction HStep.
(*     eapply reduce_det in HStep; last by eapply r_store_success.e *)
    inversion HStep; subst; clear HStep => /=.
    iFrame.
    rewrite update_list_at_insert; last by rewrite nth_error_lookup in Hm; apply lookup_lt_Some in Hm.
    erewrite gmap_of_memory_insert_block => //; [ idtac | by rewrite - nth_error_lookup | by apply store_length in Hstore'; lia ].
    rewrite list_fmap_insert.
    assert (mem_length m' = mem_length m) as Hmsize.
    { apply store_length in Hstore'. by unfold mem_length, memory_list.mem_length; rewrite Hstore'. }
    rewrite Hmsize.
    assert (mem_length mem' = mem_length mem) as Hmsize'.
    { apply mem_equiv_length in Hmem.
      apply mem_equiv_length in Hmdata'.
      lia.
    }
    rewrite Hmsize'.
    rewrite list_insert_id; last by rewrite list_lookup_fmap; rewrite - nth_error_lookup; rewrite Hm.
    rewrite Hmdata' Hwmlength'.
    by iFrame.
Qed. *)


(*
Lemma wp_current_memory (s: stuckness) (E: coPset) (k: nat) (n: N) (inst: instance) (mem: memory) (ϕ: val -> Prop) :
  inst.(inst_memory) !! 0 = Some k ->
  ϕ (immV [(VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (N.div n page_size))))]) ->
  ( ↦[wi] inst ∗
   (N.of_nat k) ↦[wmlength] n) ⊢
   WP ([AI_basic (BI_current_memory)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ ↦[wi] inst ∗ (N.of_nat k) ↦[wmlength] n }}.
Proof.
  iIntros (Hi Hϕ) "[Hinst Hmemlength]".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & ? & Hi & Hγ)".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  iDestruct (gen_heap_valid with "Hγ Hmemlength") as "%Hmemlength".
  rewrite lookup_insert in Hinst.
  inversion Hinst; subst; clear Hinst.
  rewrite - nth_error_lookup in Hi.
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hmemlength => /=.
  destruct (s_mems ws !! k) eqn:Hmemlookup => //.
  rewrite - nth_error_lookup in Hmemlookup.
  simpl in Hmemlength.
  inversion Hmemlength; clear Hmemlength.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (N.div n page_size)))))], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_current_memory => //.
    unfold mem_size.
    by f_equal.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.

Lemma reduce_grow_memory hs ws f c hs' ws' f' es' k mem mem':
  f.(f_inst).(inst_memory) !! 0 = Some k ->
  nth_error (s_mems ws) k = Some mem ->
  reduce hs ws f [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_grow_memory)] hs' ws' f' es' ->
  ((hs', ws', f', es') = (hs, ws, f, [AI_basic (BI_const (VAL_int32 int32_minus_one))] ) \/
   (hs', ws', f', es') = (hs, (upd_s_mem ws (update_list_at (s_mems ws) k mem')), f, [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))))]) /\
  mem_grow mem (Wasm_int.N_of_uint i32m c) = Some mem').
Proof.
  move => Hinst Hmem HReduce.
  destruct f as [locs inst].
  destruct f' as [locs' inst'].
  (*only_one_reduction HReduce [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))))] locs inst locs' inst'.*)
Admitted.

Lemma wp_grow_memory (s: stuckness) (E: coPset) (k: nat) (n: N) (inst: instance) (mem: memory) (Φ Ψ: val -> iProp Σ) (c: i32) :
  inst.(inst_memory) !! 0 = Some k ->
  match mem_max_opt mem with
  | Some maxlim => (mem_size mem + (Wasm_int.N_of_uint i32m c) <=? maxlim)%N
  | None => true
  end ->
  (Φ (immV [VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))]) ∗
  (Ψ (immV [VAL_int32 int32_minus_one])) ∗
   ↦[wi] inst ∗
     (N.of_nat k) ↦[wmblock] mem ) ⊢ WP ([AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_grow_memory)]) @ s; E {{ w, ((Φ w ∗ (N.of_nat k) ↦[wmblock] {| mem_data:= {| ml_init := ml_init mem.(mem_data); ml_data := ml_data mem.(mem_data) ++ repeat (#00)%byte (N.to_nat ((Wasm_int.N_of_uint i32m c) * page_size)) |}; mem_max_opt:= mem_max_opt mem |}) ∨ (Ψ w ∗ (N.of_nat k) ↦[wmblock] mem)) ∗ ↦[wi] inst  }}.
Proof.
  iIntros (Hi Hmsizelim) "(HΦ & HΨ & Hinst & Hmemblock)".
  iDestruct "Hmemblock" as "(Hmemdata & Hmemlength)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & ? & Hi & Hγ)".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  iDestruct (gen_heap_valid with "Hγ Hmemlength") as "%Hmemlength".
  rewrite lookup_insert in Hinst.
  inversion Hinst; subst; clear Hinst.
  rewrite - nth_error_lookup in Hi.
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hmemlength => /=.
  destruct (s_mems ws !! k) eqn:Hmemlookup => //.
  simpl in Hmemlength.
  inversion Hmemlength as [Hmemlength']; clear Hmemlength.
  iAssert ( (∀ i, ⌜(ml_data (mem_data mem)) !! i = (ml_data (mem_data m)) !! i ⌝)%I) as "%Hmeq".
  {
    iIntros (i).
    destruct (ml_data (mem_data mem) !! i) eqn:Hmd.
    - iDestruct (big_sepL_lookup with "Hmemdata") as "H" => //.
      iDestruct (gen_heap_valid with "Hm H") as "%H".
      rewrite gmap_of_list_2d_lookup list_lookup_fmap Nat2N.id Hmemlookup in H.
      unfold memory_to_list in H.
      simpl in H.
      by rewrite Nat2N.id in H.
    - apply lookup_ge_None in Hmd.
      iPureIntro.
      symmetry.
      apply lookup_ge_None.
      unfold mem_length, memory_list.mem_length in Hmemlength'.
      lia.
  }
  iAssert (⌜mem ≡ₘm⌝%I) as "%Hmem".
  {
    unfold mem_block_equiv.
    by rewrite (list_eq (ml_data (mem_data mem)) (ml_data (mem_data m))).
  }
  iSplit.
  assert (exists mem', mem_grow mem (Wasm_int.N_of_uint i32m c) = Some mem') as [mem' Hmem'].
  { unfold mem_grow.
    destruct (mem_max_opt mem) eqn:Hmaxsize; eexists => //.
    by rewrite Hmsizelim.
  }
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))))], (hs, (upd_s_mem ws (update_list_at (s_mems ws) k mem')), locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_grow_memory_success => //.
    rewrite - nth_error_lookup in Hmemlookup.
    rewrite Hmemlookup.
    f_equal.
  (* There's a small bug in memory_list: mem_grow should not be using ml_init but #00 instead. Finish this when that is fixed *)
    admit.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    (* DO NOT USE reduce_det here -- grow_memory is NOT determinstic. *)
    eapply reduce_grow_memory in H; [ idtac | by rewrite - nth_error_lookup | by rewrite nth_error_lookup ].
    destruct H as [HReduce | [HReduce Hmem']]; inversion HReduce; subst; clear HReduce; iFrame.
    (* failure *)
    + iSplit => //.
      iRight.
      iFrame.
      by rewrite Hmemlength'.
    (* success *)
    + admit.
Admitted.



*)


End lifting.

(* What should a function spec look like?
  A (Wasm) function closure is of the form

    FC_func_native inst ft vts bes

  but this is not an expression nor a value, so we need to define our custom version of wp for it, like

    ▷ WP (FC_func_native inst ft vts bes) {{ v, Φ v }}.

    ( Would WP bes {{ ... }} be enough? )

  to express our function specs.

  What should such a wp require (to be established), and how to use it? 

  Given a spec in the above form, we expect to be able to use it to
    figure out a spec for Invoke i, when s.funcs[i] is a Wasm function...
 
  s.funcs[a] = FC_func_native i (Tf t1s t2s) ts bes ->
  f' = {| inst := i; locs := vcs ++ zs |} ->
  ... ->
  (hs, s, f, ves ++ [AI_invoke a]) ↪ 
  (hs, s, f, [AI_local m f' [AI_basic (BI_block (Tf [] t2s) bes)]])

Lemma invoke_native_spec `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ} (s : stuckness) (E : coPset) (Φs: list (val -> iProp Σ)) inst ft vts bes :
  [∗ list] i ↦ Φ ∈ Φs, (i ↦[wf] FC_func_native inst ft vts bes ∗ □ (WP (FC_func_native inst ft vts bes)
*)

End Host.

Local Hint Resolve language.val_irreducible : core.
Local Hint Resolve to_of_val : core.
Local Hint Unfold language.irreducible : core.

