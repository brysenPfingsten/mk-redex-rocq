# Extracted search demo

From the repository root, after `make`:

```sh
rocq c -Q src MkRedex extract/Extract.v
ocamlc -c extract/search.mli
ocamlc -I extract -c extract/search.ml
ocamlc -I extract extract/search.cmo extract/demo.ml -o extract/demo
extract/demo
```

The demo runs a disjunction of two successes and reports two observed
answers. `run_steps` takes a finite fuel value, so it always returns. Its
Rocq theorem applies to a closed environment and a well-formed starting
expression; the extracted OCaml types omit those proof arguments.

`head_fn_spec`, `next_step_spec`, and `run_steps_multi` inherit the
proof-irrelevance and dependent functional-extensionality assumptions of
the existing `unify_fn_spec`. Extraction erases those proof terms.
