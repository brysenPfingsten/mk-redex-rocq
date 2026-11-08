From Stdlib Require Import List Arith.
From MkRedex.Language Require Import Goals Substitution Environments Trees.
From MkRedex.Semantics Require Import Denotation WellFormed Reduction Executable RunnerCorrespondence.
Import ListNotations.
Set Default Goal Selector "!".

Definition initial_expr (counter : nat) (g : goal) : expr :=
  ([], tgoal g (mkstate [] counter)).

Lemma initial_expr_ok : forall G counter g,
  closed_goal G 0 counter g -> ok_expr G (initial_expr counter g).
Proof.
  intros G counter g Hgoal. unfold initial_expr, ok_expr. simpl.
  split.
  - exists counter. split; [apply Nat.le_refl|]. split; [exact Hgoal|exact I].
  - split.
    + split; [exact Hgoal|exact I].
    + split; [constructor|].
      intros x. constructor. intros y [t [Hlookup _]]. discriminate.

Qed.

(** Completeness specification. Its proof is [source_search_completeness]
    in [CompletenessProof.v]. Query variables must already be allocated. *)
Definition reduction_complete (G : env) (counter : nat) (query : list nat)
  (g : goal) : Prop :=
  forall rho, solution G query g rho ->
  exists e answer,
    multi G (initial_expr counter g) e /\
    In answer (observed_answers e) /\ represents query answer rho.

Definition runner_complete (G : env) (Henv : closed_env G)
  (counter : nat) (query : list nat) (g : goal)
  (Hok : ok_expr G (initial_expr counter g)) : Prop :=
  forall rho, solution G query g rho ->
  exists fuel answer,
    In answer (observed_answers (run_steps G Henv fuel (initial_expr counter g) Hok)) /\
    represents query answer rho.

(** Transfer to the extracted runner needs no further fairness or
    unification argument. Used by [CompletenessProof.v]. *)
Theorem reduction_completeness_transfers_to_runner : forall G Henv counter query g Hok,
  reduction_complete G counter query g -> runner_complete G Henv counter query g Hok.
Proof.
  intros G Henv counter query g Hok Hcomplete rho Hsolution.
  destruct (Hcomplete rho Hsolution) as [e [answer [Hrun [Hin Hrepr]]]].
  destruct (multi_run_steps G _ e Hrun Henv Hok) as [fuel Heq].
  exists fuel, answer. rewrite Heq. split; assumption.
Qed.

(** Full specification with scoping and query-allocation hypotheses.
    Proved in [CompletenessProof.v], without adding axioms. *)
Definition source_search_complete : Prop :=
  forall G counter query g,
    closed_env G -> closed_goal G 0 counter g ->
    Forall (fun x => x < counter) query ->
    reduction_complete G counter query g.
