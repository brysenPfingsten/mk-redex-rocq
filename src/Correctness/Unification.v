From MkRedex.Correctness Require Export GroundUnification.
From MkRedex.Language Require Import Solver.
From MkRedex.Denotational Require Import Denotation.
From MkRedex.Execution Require Import Executable.
Set Default Goal Selector "!".

Section WithSolver.
Context `{solver : Solver}.

(** The machine uses this semantic contract, independently of binding-list
    orientation, extension order, or eager substitution expansion. *)
Theorem solver_unification_answer_sound : forall G query c t u initial answer rho,
  valid_unification c initial t u ->
  Solve c t u initial (Some answer) ->
  represents query (Substitution.mkstate answer c) rho ->
  solution G query (Goals.gunify t u) rho.
Proof.
  intros G query c t u initial answer rho Hvalid Hsolve [sigma [Hagree Hmodel]].
  exists sigma. split; [exact Hagree|].
  apply (proj1 (solve_models c t u initial _ Hvalid Hsolve sigma)) in Hmodel.
  destruct Hmodel as [_ [v [Et Eu]]]. eapply Sat_unify; eassumption.
Qed.
End WithSolver.
