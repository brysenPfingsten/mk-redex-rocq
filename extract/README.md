# Checked miniKanren runner

From the repository root, with Rocq, its standard library, OCaml and Make
available (or inside `nix develop`):

```sh
make -C extract all
extract/mk-search --fuel 1 extract/examples/seven.sexp
extract/mk-search --fuel 10 --trace extract/examples/seven.sexp
make -C extract test
```

The build compiles the Rocq development, extracts `search.ml`/`search.mli`,
and builds the CLI and the original demo. `nix build` also builds and tests
the executable, then installs it at `result/bin/mk-search` alongside the
Rocq libraries. When using a Git flake, new source files must be tracked
for Nix to include them.

The first command-line example prints:

```text
status: complete
steps: 1
answers: 1
answer 1: {q0 = 7}
```

`complete` means search has reached a terminal state. A completed failed
search has zero answers. `fuel exhausted` means work remains; answers found
so far are still returned. The test for completion inspects the final state,
so reaching success on the last permitted step reports `complete`. At zero
fuel an already successful goal is complete, while an active goal is exhausted.
Fuel counts reduction steps, not wall-clock time or unification suboperations.
To search further, rerun with larger fuel. No raw checkpoint/state input is
accepted by this source-program interface.

Exit statuses are 0 for completed search, 2 for invalid input or usage, and
3 for exhausted fuel. Invalid inputs are reported on stderr. `--trace` prints
the initial state and every successor, including substitutions, allocation
counters, selected branches and delays. Without `--trace`, no trace is stored.
Trace length is the actual executed step count plus one. Unsuccessful search
and fuel exhaustion are distinct from invalid input.

## Program format

Files contain one S-expression. Semicolon comments and quoted strings with
`\n`, `\r`, `\t`, `\\` and `\"` escapes are supported. Strings are byte strings.
The four fields may be in any order but must each occur exactly once.
Use `(relations standard)` to load the certified example library
(`appendo`=0, `membero`=1, `listo`=2), or supply explicit definitions:

```lisp
(program
  (relations
    (relation 1
      (fresh 1
        (conj (unify (par 0) (nat 7))
              (unify (par 1) (par 0))))))
  (counter 1)
  (query 0)
  (goal (call 0 (var 0))))
```

Relation indices are zero-based positions in `relations`. A relation entry
gives its arity and body. `counter` reserves IDs `0 .. counter-1` before
execution. `query` lists the IDs to display, in display order; it may be
empty. Execution always starts with an empty substitution. Relation
parameters and `fresh` bind `(par N)` indices, with the innermost fresh block
occupying the lowest indices. `(var N)` refers to an allocated runtime ID.

Terms:

```lisp
(var N)  (par N)  (nat N)  (sym "symbol")  (str "text")
(bool true)  (bool false)  nil  (cons TERM TERM)
```

Goals:

```lisp
success
(unify TERM TERM)
(call RELATION-ID TERM ...)
(disj GOAL GOAL)
(conj GOAL GOAL)
(fresh WIDTH GOAL)
```

Numbers must be nonnegative machine integers. Naturals remain unary in the
reference extraction. This is a reference interpreter, not an optimized
large-integer implementation.

Examples include `seven.sexp`, recursive `sevens.sexp`, symbolic
`residual.sexp`, and rejected `bad-call.sexp`. `sevens.sexp` keeps searching
and can repeatedly emit the same projected answer, so it normally exits 3.
Projection fully applies substitutions, including inside pairs. Unbound
variables print as `_N`; their IDs are local existential names in each
answer. Shared residual IDs within an answer denote the same variable.

## Validation and guarantees

`Input.v` decides the existing well-formedness specifications:

- Every relation body is scoped under its declared parameters, contains no
  allocated logic variables, and uses existing relations with correct arities.
- The source goal uses valid parameters, allocated variables, relation indices
  and arities. Fresh binders extend parameter scope, not preallocated IDs.
- Every query ID is below the initial counter.

Invalid environments, goals and query lists are distinguished. The CLI
parser separately diagnoses malformed syntax, negative numbers, missing or
duplicate fields, unknown fields (including attempts to supply raw states),
and bad command-line options. Initial states cannot inject cyclic or
otherwise invalid substitutions: the checked source interface constructs
its own empty substitution. Cyclic *constraints* in a valid goal are still
accepted; the certified occurs check makes those branches fail normally.

`checked_run` has no proof arguments. It performs validation before entering
the certified machine. Rejection occurs exactly for requests failing the
well-formedness specification; every evaluated report refines `run_validated`.
`Interface.v` proves agreement with `run_steps`, terminal-status correctness,
step bounds, exhausted-fuel consumption, trace transitions/endpoints and
projection correctness against relational `ApplySub`. It transfers source
soundness and completeness to the validated runner.

The OCaml `Frontend` module supplies an abstract parsed-program type, the
`run` entry point and display. Its parser and printer are handwritten; the
semantic validator, execution, status classification, trace collection and
substitution projection are extracted from Rocq. Generated `Search` also
exports low-level functions whose erased proof preconditions remain the
caller's responsibility. Use `Frontend.run` or `Search.checked_run` for
untrusted program inputs, rather than `run_validated`, `next_step` or
`run_steps` directly.

Proofs inherit the existing proof irrelevance and dependent functional
extensionality assumptions of executable unification. Extraction, OCaml
compilation, parsing and display are outside the Rocq kernel's verification.
See `../METATHEORY.md` for the full semantic result and scope.

## Verification

`make -C extract check` additionally runs `coqchk` on every module in
`_CoqProject`. This is the target used by `nix flake check -L` and the package
check phase. The package source excludes compiled artifacts so local
pre-push checks rebuild source proofs.

`make -C extract test` runs the original eight execution checks, thirty
checked-interface tests, twenty-nine representative-relation checks, and CLI
integration checks. These cover invalid
scope/arity/lookup, fresh binding, occurs-check failure, nested substitution
projection, recursive search, exact fuel boundaries, trace endpoints, parser
errors and exit statuses. `InputExamples.v` also checks concrete validator
rejections directly in Rocq.

See [the relation examples](examples/README.md) for queries in multiple
directions, expected answers, residual sharing and infinite symbolic search.
