From Stdlib Require Import Extraction.
From MkRedex.Language Require Import Trees.
From MkRedex.Execution Require Import Interface Solvers.
From MkRedex.Examples Require Import Relations.

(** Both instances share the same machine, validation and reporting code.
    These roots are separate from the production extraction interface. *)
Definition reference_execute := @Interface.execute reference_solver.
Definition structural_execute := @Interface.execute structural_solver.
Definition reference_checked_run := @Interface.checked_run reference_solver.
Definition structural_checked_run := @Interface.checked_run structural_solver.

(** Kernel roots: the harness constructs each representation before timing
    and retains the native accumulator between equations. *)
Definition reference_unify := Unifier.unify_fn_cert.
Definition structural_unify := StructuralUnifier.amgu.

Extraction Language OCaml.
Set Extraction Output Directory "extract".
Extraction "benchmark_search.ml" reference_execute structural_execute
  reference_checked_run structural_checked_run reference_unify structural_unify
  observed_answers relation_library.
