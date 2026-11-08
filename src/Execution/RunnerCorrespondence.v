From MkRedex.Language Require Import Scoping ScopedUnification Trees Environments.
From Stdlib Require Import List Arith.
From MkRedex.Operational Require Import Reduction Determinism WellFormed Delay.
From MkRedex.Execution Require Import Executable.
Import ListNotations.
Set Default Goal Selector "!".

Lemma next_step_checked_none : forall G Henv e Hok,
  next_step_checked G Henv e Hok = None -> next_step G e Hok = None.
Proof.
  intros G Henv e Hok Hnone.
  unfold next_step_checked in Hnone.
  revert Hnone. generalize (next_step_sound G e Hok).
  destruct (next_step G e Hok); intros Hsound Hnone; [discriminate|reflexivity].
Qed.

(** Exact correspondence, including fuel values before termination. *)
Theorem run_steps_exact : forall G n e e',
  steps_n G n e e' -> forall Henv Hok,
  run_steps G Henv n e Hok = e'.
Proof.
  intros G n e e' Hrun. induction Hrun; intros Henv Hok; cbn [run_steps].
  - reflexivity.
  - destruct (next_step_checked G Henv e1 Hok)
      as [[next [Hnext Hvalid]]|] eqn:E.
    + pose proof (step_deterministic G e1 next e2 Hnext H) as Heq.
      subst next. apply IHHrun.
    + apply next_step_checked_none in E.
      pose proof (next_step_complete G e1 Hok e2 H) as Hsome.
      rewrite E in Hsome. discriminate Hsome.
Qed.

Lemma multi_steps_n : forall G e e',
  multi G e e' -> exists n, steps_n G n e e'.
Proof.
  intros G e e' Hrun. induction Hrun.
  - exists 0. constructor.
  - destruct IHHrun as [n Hn]. exists (S n). econstructor; eassumption.
Qed.

Corollary multi_run_steps : forall G e e',
  multi G e e' -> forall Henv Hok,
  exists fuel, run_steps G Henv fuel e Hok = e'.
Proof.
  intros G e e' Hrun Henv Hok.
  destruct (multi_steps_n G e e' Hrun) as [n Hn].
  exists n. apply run_steps_exact. exact Hn.
Qed.
