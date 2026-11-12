# miniKanren reduction semantics in Rocq

This repository formalizes a fine-grained miniKanren search machine and proves that its executable implementation finds exactly the solutions of an independent source-level semantics. 
The reduction semantics is the main specification: search trees record which disjunction branch is selected, where execution is delayed, and which conjunctions are waiting for an answer.
The extracted OCaml runner computes these same steps.
The machine is parameterized by a correct deterministic unifier; its search behavior is independent of substitution representation.

The language has equality by unification with an occurs check, conjunction, disjunction, fresh variables, and recursive relations.
Terms include symbols, strings, natural numbers, Booleans, the empty list, and pairs. 
Disequality, negation, cuts, and constraint stores beyond substitutions are not included.

## Main results

| Result | Statement and source |
| --- | --- |
| Determinism | `step_deterministic`: an expression has at most one next expression. [Operational/Determinism.v](src/Operational/Determinism.v) |
| Machine safety | `progress`, `step_ok`, and `multi_ok`: valid expressions are terminal or can step, and execution preserves the runtime invariant. [Operational/WellFormed.v](src/Operational/WellFormed.v) |
| Scheduling | `global_no_stranding`: a chosen delay occurrence is released after finitely many steps in a valid execution. [Operational/DelayFairness.v](src/Operational/DelayFairness.v) |
| Unification | `Solver` requires deterministic outcomes, exact preservation of compatible ground solutions, and scoped acyclic results. The default implementation uses structurally recursive indexed unification. [Solver contract](src/Language/Solver.v), [implementations](src/Execution/Solvers.v) |
| Solver independence | `ordered_answers_solver_independent` preserves answer order and multiplicity at every step budget. `execute_solver_independent` also preserves executed step counts and trace structure, comparing substitutions by their meaning. [Correspondence](src/Correctness/SolverIndependence.v) |
| Search soundness | `search_soundness`: every ground assignment represented by an observed answer satisfies the original goal on the query variables. [Correctness/Soundness.v](src/Correctness/Soundness.v) |
| Search completeness | `source_search_completeness`: every source solution is represented by an answer in some finite execution prefix. [Correctness/Completeness.v](src/Correctness/Completeness.v) |
| Executable correspondence | `next_step_spec`, `run_steps_exact`, and `multi_run_steps`: executable steps agree with reduction, and every finite reduction endpoint can be reproduced with enough fuel. [Execution](src/Execution) |
| Checked interface | Invalid source requests are rejected before execution; reports have certified completion status, traces, and substitution projection. [Execution/Interface.v](src/Execution/Interface.v) |

The combined theorem, `source_solution_iff_runner_answer`, says that a ground assignment on the original query variables satisfies the source goal if and only if some finite-fuel run observes an answer representing that assignment.
It assumes a closed relation environment, a correctly scoped source goal, and query IDs below the initial allocation counter.
The initial substitution is empty.
Search may be infinite: the theorem gives a finite prefix for each solution, not a bound for completing the entire search.

Answers are symbolic substitutions and can represent infinitely many ground assignments.
Projection hides internal fresh variables.
The denotation is a set of ground solutions; it does not prescribe answer order or multiplicity.
Those are operational properties of the reduction semantics and its traces.
The solver-independence theorem preserves them across correct solver implementations: corresponding symbolic answers have the same meaning, although their binding lists or free variable representatives can differ.

## Build and verify

The Nix flake pins Rocq, its standard library, and OCaml.
From a checkout with all source files tracked:

```sh
nix build
nix flake check -L
```

`nix build` installs the Rocq libraries and `result/bin/mk-search`.
Both commands build the proofs and executable, run independent `coqchk` auditing of every module registered in `_CoqProject`, and run the executable tests.
The flake excludes local compiled artifacts, so existing `.vo` or OCaml object files cannot bypass source compilation.
Checks run on the current platform; the flake declares Linux and Darwin on x86-64 and AArch64.

```

For interactive proof development or a local build:

```sh
nix develop
make -f Makefile.coq all
make -C extract check
```

The development shell generates `Makefile.coq`. Without Nix, provide Rocq,
the Rocq standard library, OCaml, and Make on `PATH`, then run:

```sh
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq all
make -C extract check
```

`make -C extract test` runs the executable tests without the additional `coqchk` pass.
The test suite includes basic execution checks, interface checks, relation checks, and CLI integration checks.

## Run a query

Build the local executable with `make -C extract all`, or use `result/bin/mk-search` after `nix build`.
This example asks for every split of the list `[1,2]`:

```sh
extract/mk-search --fuel 200 extract/examples/appendo-splits.sexp
```

```text
status: complete
steps: 48
answers: 3
answer 1: {q0 = nil; q1 = (1 . (2 . nil))}
answer 2: {q0 = (1 . nil); q1 = (2 . nil)}
answer 3: {q0 = (1 . (2 . nil)); q1 = nil}
```

`--fuel` limits reduction steps. 
`complete` means search reached a terminal state; `fuel exhausted` means work remains, and already observed answers are retained.
Exit codes are 0 for completion, 2 for invalid input, and 3 for exhausted fuel.
`--trace` prints the initial expression and each successor.
Fuel does not measure wall-clock time or the internal work of unification.

Programs are S-expressions containing relation definitions, an initial allocation counter, a list of query IDs, and a goal.
The interface validates scope, relation lookup, and call arity before constructing the initial state.
For example:

```lisp
(program
  (relations standard)
  (counter 1)
  (query 0)
  (goal (call 0 (cons (nat 1) nil) (cons (nat 2) nil) (var 0))))
```

The standard library assigns indices 0, 1, and 2 to `appendo`, `membero`, and `listo`.
It is defined in Rocq and extracted into the runner.
Explicit user relation definitions are supported as well.
See the [executable guide](extract/README.md) for the complete input grammar, status semantics, and OCaml interface, and the [example guide](extract/examples/README.md) for forward, backward, partial, and infinite queries with expected answers.

## Read the formalization

The source is organized by responsibility:

```text
src/Language/       syntax, substitution, scoping, relational unification
src/Operational/    reduction, invariants, determinism, delay scheduling
src/Denotational/   ground meaning, opening, valuations, finite derivations
src/Correctness/    unification models, search soundness and completeness
src/Execution/      executable functions, validation, reports and extraction API
src/Examples/       syntax tests, semantic examples and standard relations
extract/            extraction entry point, OCaml frontend, programs and tests
```

Start with `Language/Terms.v`, `Goals.v`, and `Trees.v`, then `Operational/Reduction.v`.
The [architecture guide](docs/architecture.md) explains the module boundaries and dependencies.
The [proof guide](docs/proofs.md) explains the major proofs in natural language, including their invariants, induction measures, and difficult cases.

The default solver uses the McBride-style algorithm in
`Execution/StructuralUnifier.v`, with scope-indexed terms and ordinary nested
structural recursion. It is integrated through `Execution/Solvers.v` and the
semantic contract in `Language/Solver.v`. The proof guide explains conversion,
runtime safety, and the solver-independence argument. The [structural unification guide](docs/structural-unification.md) describes the indexed algorithm and its runtime adapter.

Rocq clients can import `MkRedex.Execution.DefaultSolver` to select this instance,
or supply a solver explicitly to the generic definitions. The public OCaml
`next_step`, `run_steps`, and `checked_run` entry points retain their existing
signatures; the CLI and `Frontend.run` interface are unchanged.

## Scope and trust

The generic source and executable soundness/completeness theorems, structural unifier, and solver-independence theorems have no axiom dependencies.
The reference executable unifier retains its existing proof irrelevance and dependent functional extensionality dependencies.
The answer-projection theorem still uses dependent functional extensionality from the existing substitution-application development.
There are no admitted proofs or project-defined axioms.

The semantic validator, stepper, status classification, trace collection, and answer projection are extracted from Rocq.
The OCaml parser and printer are handwritten.
Extraction, the OCaml compiler, and the runtime remain part of the trusted path from formal functions to printed output.

Use `Frontend.run` or extracted `checked_run` for external source programs.
Low-level extracted functions have erased proof preconditions and are not input-validation boundaries.
Raw runtime checkpoint import is not exposed; requests construct their own empty initial substitution.

The project is distributed under the [MIT license](LICENSE).
