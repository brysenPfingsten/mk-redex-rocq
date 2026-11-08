From Stdlib Require Import Extraction.
From MkRedex.Language Require Import Trees.
From MkRedex.Semantics Require Import Executable Interface.

Extraction Language OCaml.
Set Extraction Output Directory "extract".
Extraction "search.ml" observed_answers next_step run_steps checked_run.
