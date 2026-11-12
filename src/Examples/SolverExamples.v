From Stdlib Require Import List.
From MkRedex.Correctness Require Import StructuralAdapter StructuralUnificationBridge SolverIndependence.
From MkRedex.Execution Require Import DefaultSolver.
From MkRedex.Correctness Require Import Completeness.
Import ListNotations.
Set Default Goal Selector "!".

(** Original variable 1 survives the elimination of variable 0. *)
Example restore_surviving_id :
  solve_state 2 [] (Terms.tvar 0) (Terms.tvar 1) = Some (Some [(0, Terms.tvar 1)]).
Proof. reflexivity. Qed.

Example restore_middle_id :
  solve_state 3 [] (Terms.tvar 1) (Terms.tvar 2) = Some (Some [(1, Terms.tvar 2)]).
Proof. reflexivity. Qed.

Example reject_out_of_scope : solve_state 1 [] (Terms.tvar 1) Terms.tnil = None.
Proof. reflexivity. Qed.

Example reject_occurs_equation :
  solve_state 1 [] (Terms.tvar 0) (Terms.tcons (Terms.tvar 0) Terms.tnil) = Some None.
Proof. reflexivity. Qed.

Example reject_clash : solve_state 0 [] (Terms.tnat 0) Terms.tnil = Some None.
Proof. reflexivity. Qed.

Example solve_under_existing_binding :
  solve_state 2 [(0, Terms.tnat 7)] (Terms.tvar 1) (Terms.tcons (Terms.tvar 0) Terms.tnil) =
    Some (Some [(1, Terms.tcons (Terms.tnat 7) Terms.tnil); (0, Terms.tnat 7)]).
Proof. reflexivity. Qed.

Example respect_visible_lookup :
  solve_state 1 [(0, Terms.tnat 7); (0, Terms.tnat 8)] (Terms.tvar 0) (Terms.tnat 7) =
    Some (Some [(0, Terms.tnat 7)]).
Proof. reflexivity. Qed.

Example follow_existing_alias :
  solve_state 3 [(0, Terms.tvar 1); (1, Terms.tnat 7)] (Terms.tvar 2) (Terms.tvar 0) =
    Some (Some [(2, Terms.tnat 7); (1, Terms.tnat 7); (0, Terms.tvar 1)]).
Proof. reflexivity. Qed.

Example existing_binding_clash :
  solve_state 1 [(0, Terms.tnat 7)] (Terms.tvar 0) (Terms.tnat 8) = Some None.
Proof. reflexivity. Qed.


(** The theorem compares ordered answers at the same step budget, for any
    valid source program, rather than requiring identical binding lists. *)
Example reference_and_structural_preserve_answer_order : forall G Henv counter g
  (Hgoal : Scoping.closed_goal G 0 counter g) fuel query,
  List.Forall2
    (fun a b => forall rho, Denotation.represents query a rho <-> Denotation.represents query b rho)
    (Trees.observed_answers
      (@Executable.run_steps reference_solver G Henv fuel (initial_expr counter g)
        (initial_expr_ok G counter g Hgoal)))
    (Trees.observed_answers
      (@Executable.run_steps structural_solver G Henv fuel (initial_expr counter g)
        (initial_expr_ok G counter g Hgoal))).
Proof.
  intros. apply ordered_answers_solver_independent. apply expr_equiv_refl.
Qed.
