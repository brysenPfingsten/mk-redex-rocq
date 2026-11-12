From Stdlib Require Import Extraction.
From MkRedex.Language Require Import Trees.
From MkRedex.Execution Require Import Executable Interface DefaultSolver.
From MkRedex.Examples Require Import Relations.

(** Specialize the public extraction roots to the chosen concrete solver. *)
Definition next_step := @Executable.next_step default_solver.
Definition run_steps := @Executable.run_steps default_solver.
Definition checked_run := @Interface.checked_run default_solver.

Extraction Language OCaml.
Set Extraction Output Directory "extract".
Extraction Inline Executable.next_step Executable.run_steps Interface.checked_run.
Extraction "search.ml" observed_answers MkRedex.Language.Unification.walk_valid next_step run_steps checked_run relation_library.
