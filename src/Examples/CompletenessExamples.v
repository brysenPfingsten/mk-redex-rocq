From MkRedex.Language Require Import Scoping ScopedUnification Terms Goals Substitution Environments Trees.
From Stdlib Require Import List Arith Lia.
From MkRedex.Denotational Require Import Denotation.
From MkRedex.Operational Require Import WellFormed.
From MkRedex.Execution Require Import Executable.
From MkRedex.Correctness Require Import Completeness.
Import ListNotations.
Set Default Goal Selector "!".

(** A recursive branch precedes the base clause. The base clause allocates
    a fresh variable, binds it to seven, and equates the caller's argument
    with it. Completeness must account for all of these features together. *)
Definition sevens_body : goal :=
  gdisj (grelcall 0 [tpar 0])
    (gfresh 1 (gconj (gunify (tpar 0) (tnat 7))
                     (gunify (tpar 1) (tpar 0)))).
Definition sevens_env : env := [(1,sevens_body)].
Definition sevens_query : goal := grelcall 0 [tvar 0].
Definition seven_valuation : valuation := fun _ => gnat 7.

Lemma sevens_env_closed : closed_env sevens_env.
Proof.
  intros r n body Hlook. destruct r as [|r]; simpl in Hlook.
  - inversion Hlook; subst. unfold sevens_body. simpl. repeat split; try lia. constructor; [simpl; lia|constructor].
  - destruct r; discriminate.
Qed.
Lemma sevens_query_closed : closed_goal sevens_env 0 1 sevens_query.
Proof. simpl. repeat split; try lia. constructor; [simpl; lia|constructor]. Qed.
Lemma sevens_query_solution : solution sevens_env [0] sevens_query seven_valuation.
Proof.
  exists seven_valuation. split; [apply agrees_on_refl|].
  eapply Sat_call with (arity := 1) (body := sevens_body) (values := [gnat 7]);
    try reflexivity.
  apply Sat_disj_right. eapply Sat_fresh with (values := [gnat 7]); [reflexivity|].
  apply Sat_conj; eapply Sat_unify; reflexivity.
Qed.

Example sevens_is_eventually_emitted : exists fuel answer,
  In answer (observed_answers
    (run_steps sevens_env sevens_env_closed fuel (initial_expr 1 sevens_query)
      (initial_expr_ok sevens_env 1 sevens_query sevens_query_closed))) /\
  represents [0] answer seven_valuation.
Proof.
  apply (proj1 (source_solution_iff_runner_answer sevens_env sevens_env_closed
    1 [0] sevens_query sevens_query_closed ltac:(constructor; [lia|constructor]) seven_valuation)).
  exact sevens_query_solution.
Qed.

Example sevens_never_emits_a_non_solution : forall fuel answer rho,
  In answer (observed_answers
    (run_steps sevens_env sevens_env_closed fuel (initial_expr 1 sevens_query)
      (initial_expr_ok sevens_env 1 sevens_query sevens_query_closed))) ->
  represents [0] answer rho -> solution sevens_env [0] sevens_query rho.
Proof.
  intros fuel answer rho Hin Hrepr.
  apply (proj2 (source_solution_iff_runner_answer sevens_env sevens_env_closed
    1 [0] sevens_query sevens_query_closed ltac:(constructor; [lia|constructor]) rho)).
  exists fuel,answer. split; assumption.
Qed.
