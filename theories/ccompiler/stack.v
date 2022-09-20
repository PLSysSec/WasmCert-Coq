Require Import Coq.PArith.BinPos.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import compcert.common.AST.
Require Import Wasm.datatypes.

Record stack_elt : Set :=
  { ty : value_type
  ; id : ident
  }.

Record stack : Set :=
  { elts : list stack_elt
  ; next_id : ident
  ; types : list value_type
  }.

Definition empty_stack : stack :=
  {| elts := []
   ; next_id := 1%positive
   ; types := []
   |}.

Definition push_stack (s : stack) (t : value_type) : stack :=
  {| elts := {| ty := t; id := s.(next_id) |} :: s.(elts)
   ; next_id := Pos.succ s.(next_id)
   ; types := s.(types) ++ [t]
   |}.

Definition stack_typing (s : stack) (vts : list value_type) : Prop :=
  Forall2 (fun e ty' => e.(ty) = ty') s.(elts) vts.
