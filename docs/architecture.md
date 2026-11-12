# Source organization

The reduction rules describe the runtime machine; the denotation describes
which ground assignments solve a source goal. These descriptions share
syntax but are deliberately separate. Correctness modules connect them, and
execution modules turn the rules into functions and a checked public API.
This division makes it possible to read the machine without first reading
the completeness proof, or to inspect the source meaning without learning
the scheduler representation.

## Language and scoping

`Language/Terms.v` and `Goals.v` define the source syntax and parameter
opening. `Substitution.v` defines substitutions, runtime states, relational
walking and substitution application, and substitution acyclicity.
`Environments.v` represents a relation environment as an indexed list of
arity/body pairs. `Trees.v` defines runtime trees, active contexts, terminal
expressions, and ordered observations. These runtime data structures remain
in the language layer because reduction, denotation bridges, and execution
all use them without requiring the reduction rules themselves.

`Language/Scoping.v` collects the counter and binder bounds. `closed_term d c`
allows bound parameter indices below `d` and allocated variable IDs below
`c`. `closed_goal` checks calls against the environment, and `closed_tree`
checks tree structure against a global counter bound. The module also proves
opening safety and the scoping of fresh argument blocks. It contains no
small-step machine theorem and does not depend on the reduction rules.

`Language/Unification.v` specifies the reference unification procedure and its general
metatheory: functionality, extension, acyclicity, total walking/application,
soundness, most-generality, and failure completeness. This remains a single
substantial module because the proofs share a model/factorization vocabulary
and a common dependency chain. `Language/ScopedUnification.v` adds the
results needing allocation bounds: preservation of closed substitutions and
totality of unification. The executable unifier is separate in
`Execution/Unifier.v`; machine preservation no longer has to contain its
fuel-search implementation.

`Language/Solver.v` defines the implementation-independent contract used by
reduction. Each implementation selects a deterministic outcome that represents
exactly the old constraints together with the new equality and preserves runtime
scope and acyclicity. `Execution/Solvers.v` packages the reference and structural
implementations. `Execution/DefaultSolver.v` chooses the structural one for public
execution. Generic operational, executable, and correctness modules quantify over
a `Solver`, so their theorems apply to either instance.

`Execution/StructuralUnifier.v` implements the indexed structural algorithm.
Its semantic proofs are in `Correctness/StructuralUnification.v` and
`StructuralUnificationBridge.v`. `StructuralAdapter.v` converts both terms and
existing runtime substitutions, restores original variable IDs, and establishes
ground-model equivalence. `StructuralSafety.v` proves decoded stores are scoped
and acyclic. `Correctness/GroundUnification.v` contains the reference procedure's
ground-model and MGU proofs; `Correctness/Unification.v` exposes the solver-level
answer theorem without tying search to that procedure.

`Correctness/SolverIndependence.v` relates different solver instances step for
step. Equivalent trees retain source syntax and scheduling constructors while
allowing different equivalent substitution lists. Equal-budget runs have ordered,
pointwise equivalent answers; reporting runs have equal executed step counts and
pointwise equivalent traces. See the proof guide for the invariants.

Concrete opening and term-size examples live in `Examples/SyntaxExamples.v`.
They are compiled and audited like the rest of the development, but are not
part of the core syntax interface.

## Operational semantics

`Operational/Reduction.v` defines `Head`, contextual `step`, and finite
`multi` execution. It also proves monotonicity of answer observations.
`Determinism.v` establishes unique decomposition and one-step determinism.
`WellFormed.v` defines local-state constraints, substitution acyclicity for
active work, and the public `ok_expr` invariant. Its main results are
initialization, preservation, and progress. Scoping and unification totality
are prerequisites imported from the language layer.

The scheduling proof is divided according to the obligation being discharged:

| Module | Responsibility |
| --- | --- |
| `Delay.v` | Context composition, fixed-length runs, local delay movement, a decreasing burst measure, and immediate branch handoff |
| `DelayTracking.v` | One distinguished delay occurrence, its erasure to a real tree, carry/release correspondence, and finite trace tracking |
| `Scheduling.v` | Lifting bursts through disjunctions and focusing a finite disjunction shell using a local scheduler index |
| `DelayFairness.v` | Lifting tracked traces through conjunction continuations and proving global eventual activation/release |

Occurrence tracking has its own module because a syntactic tree is not an
occurrence: two branches may contain equal delay payloads. The marking
constructors identify one position, and erasure/correspondence theorems
justify every instrumented step against ordinary reduction. Scheduling and
fairness use that infrastructure rather than defining another executable
machine.

## Denotational semantics

`Denotational/Denotation.v` defines ground values, term interpretation,
inductive satisfaction, substitution models, and projection onto query
variables. Recursive calls have finite satisfaction derivations, giving the
least interpretation of relation definitions. This module does not mention
search trees or the step relation.

`Opening.v` proves that lexical parameter interpretation agrees with opening.
`Valuations.v` proves agreement below an allocation counter and extension over
a fresh block. `Derivations.v` attaches a logical-work index to finite source
derivations and shows that opening and valuation transport preserve that
index. These modules depend on source scoping, not on search scheduling.

## Correctness proofs

`Correctness/GroundUnification.v` connects ground valuations to substitution
application and the reference unifier's models. It proves both directions of
ground correctness, constructs finite ground substitutions for valuations, and
packages the reference procedure's MGU guarantees. `Correctness/Unification.v`
re-exports these results and proves the answer-level consequence of the abstract
solver contract. Separating the reference mathematics from machine execution
lets the contract and structural instance precede the generic reduction proofs
without introducing a dependency cycle.

`Soundness.v` interprets trees and expressions and proves backward semantic
preservation through a step and through a finite run. `Completeness.v` keeps
the initial-state definition, completeness specification, runner transfer,
and main induction together. The specification is immediately followed by
the supporting witness invariant and its proof, rather than living in a
separate file that might be mistaken for a completed theorem.

Completeness uses two auxiliary developments. `Focus.v` adapts occurrence
fairness to arbitrary chosen work, preserving the conjunctions on its path.
`Success.v` handles successful states: either expose an observed answer or
start the next conjunction continuation. Neither changes the runtime rules.
The final theorem in `Completeness.v`, `source_solution_iff_runner_answer`,
combines soundness and completeness for finite-fuel execution.

## Execution and external input

`Execution/Unifier.v` computes unification outcomes with certificates.
`Executable.v` computes head steps and the selected contextual step, then
iterates them with finite fuel. `RunnerCorrespondence.v` proves exact
correspondence with fixed-length finite runs and that every finite reduction
endpoint is obtained for some fuel.

`Input.v` decides the existing environment, goal-scoping, and query-allocation
specifications. `Interface.v` uses those certificates to construct a valid
initial state and produce reports. It includes optional traces, completion
classification, actual step counts, and normalized query bindings. The
interface imports the correctness developments to transfer the semantic
results; the low-level stepper does not depend on the public interface.

`extract/Extract.v` chooses OCaml and names the extracted entry points.
`frontend.ml` parses source programs and displays reports; `frontend.mli`
keeps parsed programs abstract. `cli.ml` handles files, options, and exit
statuses. The handwritten layer calls the certified checker rather than
reimplementing scope or arity validation. The generated `search.ml` and
`search.mli` and compiled objects are build artifacts, not maintained source.

## Examples, tests, and verification

`Examples/Relations.v` contains the extracted `appendo`, `membero`, and
`listo` definitions and source-level satisfaction lemmas. The other example
modules check syntax opening, semantic edge cases, validator rejection, and
a combined recursive query. Files under `extract/examples` are executable
inputs; their guide records expected answers and explains infinite examples.

`_CoqProject` registers every Rocq module under `MkRedex`. Adding a module
requires updating that list. `extract/Makefile` derives its `coqchk` module
list from `_CoqProject`, so isolated example modules receive the same audit
as modules transitively imported by the runner. The Nix flake builds from
filtered source, runs that audit and the executable tests, and installs the
libraries and CLI. It does not install a pre-push hook or require a hosted CI
service: `nix flake check -L` is the common local verification entry point.
