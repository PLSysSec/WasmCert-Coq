From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
(* From iris.bi Require Export weakestpre. *)
Require Export datatypes (* host *) operations properties opsem.
Require Export iris_locations iris_properties iris_atomicity iris_wp stdpp_aux.

Import uPred.

Set Default Proof Using "Type".

Close Scope byte_scope.

Definition expr := iris.expr.
Definition val := iris.val.
Definition to_val := iris.to_val.

(* Defining a Wasm-specific WP with frame existence *)



Canonical Structure wasm_lang := Language wasm_mixin.
 
Local Definition reducible := @reducible wasm_lang.
Local Definition state := state wasm_lang.

Implicit Type σ : state.

Class wasmG Σ :=
  WasmG {
      func_invG :> invGS Σ;
      func_gen_hsG :> gen_heapGS N function_closure Σ;
      
      tab_gen_hsG :> gen_heapGS (N*N) funcelem Σ;
      
      tabsize_hsG :> gen_heapGS N nat Σ;
      
      tablimit_hsG :> gen_heapGS N (option N) Σ;

      mem_gen_hsG :> gen_heapGS (N*N) byte Σ;

      memsize_gen_hsG :> gen_heapGS N N Σ;

      memlimit_hsG :> gen_heapGS N (option N) Σ;

      glob_gen_hsG :> gen_heapGS N global Σ;

      locs_gen_hsG :> ghost_mapG Σ unit frame;

      frameGName :> gname
    }.

Definition proph_id := positive. (* ??? *)


Instance eqdecision_frame: EqDecision frame.
Proof. decidable_equality. Qed.

Definition gen_heap_wasm_store `{!wasmG Σ} (s: store_record) : iProp Σ :=
  ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
   (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
   (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
   (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
   (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems)))) ∗
   (gen_heap_interp (gmap_of_list (fmap tab_size s.(s_tables)))) ∗
   (gen_heap_interp (gmap_of_list (fmap mem_max_opt s.(s_mems)))) ∗
   (gen_heap_interp (gmap_of_list (fmap table_max_opt s.(s_tables)))))%I.

(* TODO: let this use the above gen_heap as well. Currently too much a hassle as this needs to update every file. *)
Global Instance heapG_irisG `{!wasmG Σ} : irisGS wasm_lang Σ := {
  iris_invGS := func_invG; (* ??? *)
  state_interp σ _ κs _ :=
    let: (s, locs, inst) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
      (ghost_map_auth frameGName 1 (<[ tt := Build_frame locs inst ]> ∅)) ∗ 
      (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems)))) ∗
      (gen_heap_interp (gmap_of_list (fmap tab_size s.(s_tables)))) ∗
      (gen_heap_interp (gmap_of_list (fmap mem_max_opt s.(s_mems)))) ∗
      (gen_heap_interp (gmap_of_list (fmap table_max_opt s.(s_tables))))
      
    )%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
  }.

(* Section Host_wp_import.
  (* Host wp must depend on the same memory model as for wasm *)
  Context `{!wasmG Σ}.

  Record host_program_logic := {
      wp_host (s : stuckness) : coPset -d> host_function -d> seq.seq value -d> (result -d> iPropO Σ) -d> iPropO Σ;
      wp_host_not_stuck : (forall σ ns κs nt Φ h E vcs t1s t2s a, (let '(hs,s,_,_) := σ in
                                              s_funcs s !! a = Some (FC_func_host (Tf t1s t2s) h)) ->
                                              state_interp σ ns κs nt -∗
                                              wp_host NotStuck E h vcs Φ ={E}=∗
                                              state_interp σ ns κs nt ∗ wp_host NotStuck E h vcs Φ ∗
                                              ⌜(let '(hs,s,_,_) := σ in (∃ hs' s' r, host_application hs s (Tf t1s t2s) h vcs hs' (Some (s',r))) ∨
                                               (∃ hs', host_application hs s (Tf t1s t2s) h vcs hs' None))⌝);
      wp_host_step_red : (∀ σ ns κ κs nt Φ h E vcs t1s t2s, (
                                                               
                                              state_interp σ ns (κ ++ κs) nt -∗
                                              wp_host NotStuck E h vcs Φ ={E,∅}=∗
                                              (∀ σ' r, ⌜(let '(hs,s,_,_) := σ in let '(hs',s',_,_) := σ' in host_application hs s (Tf t1s t2s) h vcs hs' (Some (s',r)))⌝
                                              ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
                                                 state_interp σ' (S ns) κs nt ∗ Φ r) ∗
                                              (∀ σ', ⌜(let '(hs,s,_,_) := σ in let '(hs',_,_,_) := σ' in host_application hs s (Tf t1s t2s) h vcs hs' None)⌝
                                              ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
                                                 state_interp σ' (S ns) κs nt ∗ wp_host NotStuck E h vcs Φ)));
    }.
  
End Host_wp_import. *)

(* Resource ownerships *)
Notation "n ↦[wf]{ q } v" := (mapsto (L:=N) (V:=function_closure) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wf]{ q } v") : bi_scope.
Notation "n ↦[wf] v" := (mapsto (L:=N) (V:=function_closure) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wf] v") : bi_scope.
Notation "n ↦[wt]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=funcelem) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wt]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wt][ i ] v" := (mapsto (L:=N*N) (V:=funcelem) (n, i) (DfracOwn 1) v%V)
                           (at level 20, format "n ↦[wt][ i ] v") : bi_scope.
Notation "n ↪[wtsize] m" := (mapsto (L:=N) (V:=nat) n (DfracDiscarded) m%V)
                              (at level 20, format "n ↪[wtsize] m") : bi_scope.
Notation "n ↪[wtlimit] m" := (mapsto (L:=N) (V:=option N) n (DfracDiscarded) m%V)
                              (at level 20, format "n ↪[wtlimit] m") : bi_scope.
Notation "n ↦[wm]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wm]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wm][ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wm][ i ] v") : bi_scope.
Notation "n ↦[wmlength] v" := (mapsto (L:=N) (V:=N) n (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wmlength] v") : bi_scope.
Notation "n ↪[wmlimit] v" := (mapsto (L:=N) (V:=option N) n (DfracDiscarded) v% V)
                           (at level 20, format "n ↪[wmlimit] v") : bi_scope.
Notation "n ↦[wg]{ q } v" := (mapsto (L:=N) (V:=global) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wg]{ q } v").
Notation "n ↦[wg] v" := (mapsto (L:=N) (V:=global) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wg] v") .
Notation " ↪[frame]{ q } v" := (ghost_map_elem frameGName tt q v%V)
                           (at level 20, q at level 5, format " ↪[frame]{ q } v") .
Notation " ↪[frame] v" := (ghost_map_elem frameGName tt (DfracOwn 1) v%V)
                           (at level 20, format " ↪[frame] v").

(* Predicates for memory blocks and whole tables *)  
Definition mem_block `{!wasmG Σ} (n: N) (m: memory) :=
  (([∗ list] i ↦ b ∈ (m.(mem_data).(ml_data)), n ↦[wm][ (N.of_nat i) ] b ) ∗
     n ↦[wmlength] mem_length m ∗ n ↪[wmlimit] (mem_max_opt m))%I.

Definition mem_block_at_pos `{!wasmG Σ} (n: N) (l:bytes) k :=
  ([∗ list] i ↦ b ∈ l, n ↦[wm][ (N.of_nat (N.to_nat k+i)) ] b)%I.

Definition tab_block `{!wasmG Σ} (n: N) (tab: tableinst) :=
  (([∗ list] i ↦ tabelem ∈ (tab.(table_data)), n ↦[wt][ (N.of_nat i) ] tabelem ) ∗
     (n ↪[wtsize] (tab_size tab)) ∗ (n ↪[wtlimit] (table_max_opt tab)))%I.


Notation "n ↦[wmblock] m" := (mem_block n m)
                           (at level 20, format "n ↦[wmblock] m"): bi_scope.
Notation "n ↦[wms][ i ] l" := (mem_block_at_pos n l i)
                                (at level 20, format "n ↦[wms][ i ] l"): bi_scope.
Notation "n ↦[wtblock] t" := (tab_block n t)
                           (at level 20, format "n ↦[wtblock] t"): bi_scope.

Section Wasm_wp.
  Context `{!wasmG Σ}.

  Global Instance wp_wasm : Wp (iProp Σ) (expr) (val) stuckness.
  Proof using Σ wasmG0.
    eapply wp'. Unshelve. exact frame. exact (λ f,  ↪[frame] f)%I. Defined.

End Wasm_wp.

(* A Definition of a context dependent WP for WASM expressions *)

Definition wp_wasm_ctx `{!wasmG Σ}
          (s : stuckness) (E : coPset) (e : language.expr wasm_lang)
           (Φ : val -> iProp Σ) (i : nat) (lh : lholed) : iProp Σ := 
  ∀ LI, ⌜lfilled i lh e LI⌝ -∗ WP LI @ s; E {{ Φ }}.


Definition wp_wasm_frame `{!wasmG Σ}
          (s : stuckness) (E : coPset) (es : language.expr wasm_lang)
          (Φ : val -> iProp Σ) (n: nat) (f: frame) : iProp Σ :=
  
  WP [AI_local n f es] @ s; E {{ Φ }}.

Definition wp_wasm_ctx_frame `{!wasmG Σ}
          (s : stuckness) (E : coPset) (es : language.expr wasm_lang)
          (Φ : val -> iProp Σ) (n: nat) (f: frame) (i : nat) (lh : lholed) : iProp Σ :=
  
  ∀ LI, ⌜lfilled i lh es LI⌝ -∗ WP [AI_local n f LI] @ s; E {{ Φ }}.


(* Notations *)

(* Context wps for blocks *)
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

(* Frame wps for Local *)

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ Φ } }" := (wp_wasm_frame s E e%E Φ n f)
  (at level 20, only parsing) : bi_scope.

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ v , Q } }" := (wp_wasm_frame s E e%E (λ v, Q) n f)
  (at level 20, e, Q, n, f at level 200,
    format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "'WP' e @ s ; E 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx_frame s E e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ s ; E 'FRAME' n ; f 'CTX_EMPTY' {{ v , Q } }" := (wp_wasm_ctx_frame s E e%E (λ v, Q) n f 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx_frame NotStuck E e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @ '[' E  '/' ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'FRAME' n ; f 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx_frame MaybeStuck E e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' E  '/' ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx_frame NotStuck ⊤ e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'FRAME' n ; f 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx_frame MaybeStuck ⊤ e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* Tactics *)
Ltac only_one_reduction H :=
  let Hstart := fresh "Hstart" in
  let a := fresh "a" in
  let Hstart1 := fresh "Hstart" in
  let Hstart2 := fresh "Hstart" in
  let Hσ := fresh "Hσ" in 
  eapply reduce_det in H
      as [H | [ [i0 Hstart] | (* [ [a [cl [tf [h [i0 [Hstart [Hnth Hcl]]]]]]] | *) (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)(* ] *)]] ;
  last (by repeat econstructor) ;
  first (try inversion H ; subst ; clear H => /=; match goal with [f: frame |- _] => iExists f; iFrame; by iIntros | _ => idtac end) ;
  try by repeat (unfold first_instr in Hstart ; simpl in Hstart) ; inversion Hstart.
