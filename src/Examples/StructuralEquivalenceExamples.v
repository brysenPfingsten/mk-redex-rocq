From Stdlib Require Import List.
From MkRedex.Execution Require StructuralUnifier.
From MkRedex.Language Require Terms Substitution Unification.
From MkRedex.Correctness Require Import StructuralUnificationBridge.
Import ListNotations.
Set Default Goal Selector "!".

(** These use the equivalence theorem to derive facts about the pre-existing
    inductive relation from computations of the indexed algorithm. *)
Example occurs_failure_transfers_to_Unify :
  Unification.Unify (Terms.tvar 0) (Terms.tcons (Terms.tvar 0) Terms.tnil) [] None.
Proof.
  apply (proj1 (mgu_failure_iff_Unify_failure 1
    (StructuralUnifier.var StructuralUnifier.f0)
    (StructuralUnifier.fork (StructuralUnifier.var StructuralUnifier.f0) StructuralUnifier.leaf))).
  reflexivity.
Qed.

Example constructor_clash_transfers_to_Unify :
  Unification.Unify Terms.tnil (Terms.tnat 0) [] None.
Proof.
  apply (proj1 (mgu_failure_iff_Unify_failure 0 StructuralUnifier.leaf
    (StructuralUnifier.atom (StructuralUnifier.number 0)))).
  reflexivity.
Qed.

Example renumbering_success_transfers_to_Unify :
  exists answer,
    Unification.Unify (Terms.tcons (Terms.tvar 0) (Terms.tvar 0))
      (Terms.tcons Terms.tnil (Terms.tvar 1)) [] (Some answer).
Proof.
  apply (proj1 (mgu_success_iff_Unify_success 2
    (StructuralUnifier.fork (StructuralUnifier.var StructuralUnifier.f0)
      (StructuralUnifier.var StructuralUnifier.f0))
    (StructuralUnifier.fork StructuralUnifier.leaf
      (StructuralUnifier.var (StructuralUnifier.fs StructuralUnifier.f0))))).
  eexists. reflexivity.
Qed.
