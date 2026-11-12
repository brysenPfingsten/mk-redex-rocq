From MkRedex.Language Require Import Terms Substitution Scoping ScopedUnification Solver.
From MkRedex.Correctness Require Import StructuralAdapter StructuralSafety StructuralUnificationBridge.
From MkRedex.Execution Require Import Unifier.
Set Default Goal Selector "!".

(** The reference implementation retains its exact binding-list procedure,
    but the search machine only uses the abstract solver contract. *)
Definition reference_relation c t u s result : Prop :=
  valid_unification c s t u /\ MkRedex.Language.Unification.Unify t u s result.

Definition reference_solver : Solver.
Proof.
  refine {| solve_relation := reference_relation |}.
  - intros c s t u Hvalid. destruct Hvalid as [Ha [Hs [Ht Hu]]].
    destruct (unify_fn_cert c s t u Ha Hs Ht Hu) as [r Hr].
    exists r. split; [exact (conj Ha (conj Hs (conj Ht Hu)))|exact Hr].
  - intros c t u s a b [_ Ha] [_ Hb]. eapply MkRedex.Language.Unification.Unify_functional; eassumption.
  - intros c t u s answer [[Ha [Hs [Ht Hu]]] H]. split.
    + exact (ScopedUnification.Unify_closed c t u s answer Ht Hu Hs H).
    + eapply MkRedex.Language.Unification.Unify_acyclic; eassumption.
  - intros c t u s result [Ha [Hs [Ht Hu]]] [_ H] rho.
    apply (Unify_result_models c s t u result Ha Hs Ht Hu H rho).
Defined.

Definition structural_relation c t u s result : Prop :=
  valid_unification c s t u /\ solve_state c s t u = Some result.

Definition structural_solver : Solver.
Proof.
  refine {| solve_relation := structural_relation |}.
  - intros c s t u Hvalid.
    destruct (solve_state c s t u) as [r|] eqn:E.
    + exists r. split; assumption.
    + exfalso. destruct Hvalid as [Ha [Hs [Ht Hu]]].
      destruct (solve_state_valid c s t u Ha Hs Ht Hu) as [r [Er _]]. congruence.
  - intros c t u s a b [_ Ha] [_ Hb]. congruence.
  - intros c t u s answer [_ H]. eapply solve_state_safe. exact H.
  - intros c t u s result [Ha [Hs [Ht Hu]]] [_ H] rho.
    destruct (solve_state_valid c s t u Ha Hs Ht Hu) as [r [Er Hrel]].
    assert (E : r = result) by congruence. subst r.
    destruct (ScopedUnification.Unify_total c s t u Ha Hs Ht Hu) as [legacy Hlegacy].
    rewrite (proj2 (Hrel legacy Hlegacy) rho).
    apply (Unify_result_models c s t u legacy Ha Hs Ht Hu Hlegacy rho).
Defined.
