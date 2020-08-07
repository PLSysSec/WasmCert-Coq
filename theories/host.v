(** Axiomatisation of the host. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import common datatypes.
From ITree Require Import ITree ITreeFacts.

Import Monads.

Set Implicit Arguments.

(** * General host definitions **)

Section Parameterised.

(** We assume a set of host functions. **)
Variable host_function : Type.

Let store_record := store_record host_function.

(** The application of a host function either:
  - returns [Some (st', result)], returning a new Wasm store and a result (which can be [Trap]),
  - diverges, represented as [None].
  This can be non-deterministic. **)

(** We provide two versions of the host.
  One based on a relation, to be used in the operational semantics,
  and one computable based on the [host_monad] monad, to be used in the interpreter.
  There is no host state in the host monad: it is entirely caught by the (state) monad. **)

Record host := {
    host_state : eqType (** For the relation-based version, we assume some kind of host state. **) ;
    host_application : host_state -> store_record -> host_function -> seq value ->
                       host_state -> option (store_record * result) -> Prop
                       (** An application of the host function. **)
    (* FIXME: Should the resulting [host_state] be part of the [option]?
      (See https://github.com/rems-project/wasm_coq/issues/16#issuecomment-616402508
       for a discussion about this.) *)
  }.

Record executable_host := make_executable_host {
    host_event : Type -> Type (** The events that the host actions can yield. **) ;
    host_monad : Monad host_event (** They form a monad. **) ;
    host_apply : store_record -> host_function -> seq value ->
                 host_event (option (store_record * result))
                 (** The application of a host function, returning a value in the monad. **)
  }.

(** Relation between [host] and [executable_host]. **)
(* TODO
Record host_spec := {
  }.
*)

End Parameterised.

Arguments host_application [_ _].
Arguments host_apply [_ _].


(** * Extractible module **)

(** The definitions of the previous section are based on dependent types, which are very
  practical to manipulate them in Coq, but do not extract very well.
  The following is an extract-friendly adaptation using modules. **)

Module Type Executable_Host.

Parameter host_function : Type.
Parameter host_event : Type -> Type.
Parameter host_monad : Monad host_event.

Parameter host_apply : store_record host_function -> host_function -> seq value ->
                       host_event (option (store_record host_function * result)).

End Executable_Host.

(** Such a module can easily be converted into an [executable_host] definition. **)

Module convert_to_executable_host (H : Executable_Host).

Export H.

Definition executable_host := executable_host host_function.
Definition store_record := store_record host_function.

Definition executable_host_instance : executable_host :=
  make_executable_host host_monad host_apply.

End convert_to_executable_host.


(** * Host instantiations **)

(** ** Dummy host **)

From ExtLib Require Import IdentityMonad.

(** This host provides no function. **)

Module DummyHost : Executable_Host.

Definition host_function := void.
Definition host_event := ident.
Definition host_monad := Monad_ident.
Definition store_record := store_record host_function.
Definition host_apply (_ : store_record) :=
  of_void (seq value -> ident (option (store_record * result))).

End DummyHost.

Module DummyHosts.

Module Exec := convert_to_executable_host DummyHost.
Export Exec.

Definition host := host host_function.

Definition host_instance : host := {|
    host_state := unit_eqType ;
    host_application _ _ _ _ _ _ := False
  |}.

(* TODO: host_spec *)

End DummyHosts.
