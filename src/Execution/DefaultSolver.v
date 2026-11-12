From MkRedex.Execution Require Export Solvers.

(** Public execution uses structural unification; generic proofs import
    [Solver] directly and quantify over the implementation instead. *)
#[export] Instance default_solver : Solver.Solver := structural_solver.
