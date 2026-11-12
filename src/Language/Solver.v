From Stdlib Require Import List.
From MkRedex.Language Require Import Terms Substitution Scoping.
From MkRedex.Denotational Require Import Denotation.
Set Default Goal Selector "!".

Definition valid_unification (c : nat) (s : sub) (t u : term) : Prop :=
  acyclic_sub s /\ closed_sub c s /\ closed_term 0 c t /\ closed_term 0 c u.

Definition result_models (rho : valuation) (result : option sub) : Prop :=
  match result with None => False | Some answer => satisfies_sub rho answer end.

(** Solvers may choose different binding directions and representations.
    Each solver is deterministic, preserves the runtime domain, and computes
    exactly the compatible ground solutions of the new equality. *)
Class Solver : Type := {
  solve_relation : nat -> term -> term -> sub -> option sub -> Prop;
  solve_cert : forall c s t u, valid_unification c s t u ->
    {result : option sub | solve_relation c t u s result};
  solve_functional : forall c t u s a b,
    solve_relation c t u s a -> solve_relation c t u s b -> a = b;
  solve_safe : forall c t u s answer,
    solve_relation c t u s (Some answer) ->
    closed_sub c answer /\ acyclic_sub answer;
  solve_models : forall c t u s result,
    valid_unification c s t u -> solve_relation c t u s result -> forall rho,
    result_models rho result <->
    satisfies_sub rho s /\
      exists v, eval_term rho nil t = Some v /\ eval_term rho nil u = Some v
}.

Section Contract.
Context `{solver : Solver}.

Definition Solve := solve_relation.
Definition solver_fn (t u : term) (s : sub) (c : nat)
  (Ha : acyclic_sub s) (Hs : closed_sub c s)
  (Ht : closed_term 0 c t) (Hu : closed_term 0 c u) : option sub :=
  proj1_sig (solve_cert c s t u (conj Ha (conj Hs (conj Ht Hu)))).

Theorem solver_fn_spec : forall c s t u Ha Hs Ht Hu result,
  Solve c t u s result <-> solver_fn t u s c Ha Hs Ht Hu = result.
Proof.
  intros c s t u Ha Hs Ht Hu result. unfold solver_fn.
  destruct (solve_cert c s t u _) as [out Hout]. simpl. split.
  - intro H. eapply solve_functional; eassumption.
  - intro E. subst result. exact Hout.
Qed.

Lemma Solve_total : forall c s t u,
  acyclic_sub s -> closed_sub c s -> closed_term 0 c t -> closed_term 0 c u ->
  exists result, Solve c t u s result.
Proof.
  intros c s t u Ha Hs Ht Hu.
  destruct (solve_cert c s t u (conj Ha (conj Hs (conj Ht Hu)))) as [r Hr]. eauto.
Qed.

Lemma Solve_ground_complete : forall c rho s t u v,
  acyclic_sub s -> closed_sub c s -> closed_term 0 c t -> closed_term 0 c u ->
  satisfies_sub rho s -> eval_term rho nil t = Some v -> eval_term rho nil u = Some v ->
  exists answer, Solve c t u s (Some answer) /\ satisfies_sub rho answer.
Proof.
  intros c rho s t u v Ha Hs Ht Hu Hmodel Et Eu.
  destruct (Solve_total c s t u Ha Hs Ht Hu) as [[answer|] Hsolve].
  - exists answer. split; [exact Hsolve|].
    apply (proj2 (solve_models c t u s _ (conj Ha (conj Hs (conj Ht Hu))) Hsolve rho)).
    split; [exact Hmodel|]. exists v. split; assumption.
  - exfalso. apply (proj2 (solve_models c t u s _
      (conj Ha (conj Hs (conj Ht Hu))) Hsolve rho)).
    split; [exact Hmodel|]. exists v. split; assumption.
Qed.
End Contract.
