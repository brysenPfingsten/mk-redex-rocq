# Structurally recursive unification

`Execution/StructuralUnifier.v` implements the algorithm from sections 3–6
of Conor McBride, *First-order unification by structural recursion*, JFP
13(6), 2003, [DOI](https://doi.org/10.1017/S0956796803004957).

The algorithm is now the default unifier used by the search executable.
`Language/Solver.v` specifies its required behavior in terms of ground solutions,
runtime scope, acyclicity, and deterministic outcomes. The machine does not
require its binding lists to match the reference algorithm's representation.
`Execution/Solvers.v` certifies both implementations against that contract, and
`Correctness/SolverIndependence.v` proves that they preserve ordered search
behavior at every reduction-step budget.

## Data and API

`Fin n` is an inductive finite set. `Term n` contains variables from that set,
rigid constants, and binary pairs. The rigid tags distinguish symbols, strings,
natural numbers, Booleans, and the empty list. Thus symbols and strings with
the same character sequence still clash. `leaf` abbreviates the empty-list
constant; `fork` is the pair constructor. Bound source parameters are absent
from this runtime term language: they must be opened before runtime unification.

`Sub m n` is a function from `Fin m` to `Term n`. `apply` extends a substitution
to terms by structural recursion. `compose tau sigma` applies `sigma` first,
then `tau`. `thin n x` embeds the remaining variables into the scope containing
`x`; `thick n x` deletes and renumbers a variable, or reports that it is `x`.
`check x t` returns a term in the smaller scope exactly along the computational
paths where deleting `x` succeeds. The proof establishes its interpretation through thinning and rules out
ground equality after a failed check against a non-variable term. `for_ r x` substitutes the smaller-scope term `r` for `x` and
renumbers the other variables.

`AList m n` records an elimination sequence from `m` variables to `n`.
`anil` preserves the scope. `asnoc sigma r x` adds an elimination from `S m`
to `m`, followed by `sigma`. `sub` interprets the sequence as a function.
`append sigma n tau` composes a source-first sequence with a following one;
`acompose tau sigma` gives the paper's composition order, applying `sigma`
first and `tau` second.

The entry points are:

```coq
amgu : forall m, Term m -> Term m -> Acc m -> option (Acc m)
mgu  : forall {m}, Term m -> Term m -> option (Acc m)
```

Here `Acc m` abbreviates `{n : nat & AList m n}`. `mgu` starts with the
identity accumulator. A successful result provides the remaining variable
count and an elimination sequence; callers interpret it with `sub` and
`apply`. Unlike the old API, no acyclicity proofs, list substitutions, or
fuel arguments are supplied. Variable identities in the result belong to
the reduced scope, rather than the original natural-number-ID space.

## Why the guard checker accepts it

`amgu` explicitly recurses on its natural-number scope. At each scope it
contains a local `fix go` whose structural argument is the first term.
Rigid pair/pair problems call this local function on the first term's two
strict subterms, threading the accumulator returned by the first call into
the second. Nothing requires that newly computed accumulator to be smaller.

For a variable equation, `flex` inspects the accumulator. An empty accumulator
uses `flexFlex` or `flexRigid` directly. A nonempty accumulator exposes an
elimination from `S m` to `m`. Applying that elimination to both inputs makes
them terms over `m`; the callback is the outer recursive function `amgu m`.
The exposed elimination is reattached to a successful result. Term growth
is permitted in that call because its scope is structurally smaller.

The empty-scope case cannot contain a variable. `fin0_elim`, `fin_view`, and
`acc_view` use explicit dependent return clauses to expose the necessary
indices. No equality casts, dependent destruction, proof irrelevance,
functional extensionality, well-founded recursion, or guard-checking overrides
are used. The correctness proofs reason about function-valued substitutions pointwise.

## Correctness and equivalence

`Correctness/StructuralUnification.v` proves a refinement invariant for
`amgu`. An accumulator represents a ground valuation when that valuation
factors through its functional substitution. A successful result represents
exactly the input accumulator's valuations that equate the two input terms;
a failed result represents none. The proof uses ordinary induction on the
scope and on the first term, matching the algorithm's nested recursion.
Finite-set views, thinning/thickening, the occurs check, and single-variable
factorization are proved without dependent-destruction axioms or functional
extensionality. Starting with the identity accumulator gives `mgu_correct`.

`Correctness/StructuralUnificationBridge.v` erases indexed variables to their
natural-number IDs and encodes rigid constructors into the original term
language. It proves that erasure preserves both scope and ground term
interpretation. Existing ground correctness results for `Unify` then identify
the original binding list's models with the same equality condition.

The main theorem is `structural_Unify_equivalence`: for any two indexed
terms, there is a unique original `Unify` result that agrees with `mgu` on
failure and on every represented ground valuation. The corollaries
`mgu_failure_iff_Unify_failure` and `mgu_success_iff_Unify_success` state
success/failure agreement directly. `valid_terms_structural_equivalence`
proves coverage of the original valid term language: every pair of terms
closed at parameter depth zero and a finite allocation bound can be indexed,
and the resulting computation has this equivalence. `index_term_sound` and
`index_term_complete` justify that structural conversion.
`amgu_Unify_equivalent` handles nonempty
input states under a representation premise equating the input binding list's
models with those of the indexed accumulator.

Success/failure agreement additionally requires that a successful output
cannot have an empty ground solution set. Every AList has a model by assigning
values to its residual variables. A finite closed acyclic binding list also
has a model: total relational substitution application normalizes each of
its finitely many variables, and a constructive finite-choice induction
collects their ground interpretations. This uses neither an executable
well-founded application function nor a choice axiom.

The equivalence compares represented solutions; it does not equate a
renumbering AList with a literal binding list. The original algorithm's exact
output list is deliberately outside the new machine contract. A separate
symbolic factorization theorem against all function-valued candidate
substitutions has not been developed; the machine uses the exact ground-model
contract instead.

## Connection to runtime states

`Correctness/StructuralAdapter.v` supplies `solve_state`, which accepts the
existing allocation counter, binding list, and two runtime terms. Its outer
option distinguishes conversion rejection from a legitimate unification
failure. On valid runtime inputs conversion cannot reject. It builds an indexed
accumulator from the visible bindings, runs `amgu`, and decodes the result with
original IDs restored. Duplicate shadowed bindings are interpreted by lookup,
so they do not add unintended constraints.

The adapter's semantic theorem establishes failure agreement and equality of
ground models with the reference outcome. `Correctness/StructuralSafety.v`
proves that decoded results stay within the original counter and remain
acyclic. `Execution/Solvers.v` combines those properties into `structural_solver`.
The generic machine uses its certified `solver_fn`, and `DefaultSolver.v`
selects this implementation for public extraction.

The representation conversion currently rebuilds the accumulator for each
unification call. No performance improvement is claimed without measurements.
The search runner still accepts a reduction-step budget: internal structural
termination of unification does not make recursive source search terminate.

## Verification

`Examples/StructuralUnifierExamples.v` contains fifteen definitional-equality
checks plus two `Compute` commands, covering binding, occurs failures,
constructor clashes, postponement, renumbering and composition. The separate
`Examples/StructuralEquivalenceExamples.v` uses the equivalence corollaries
to transfer indexed computations into the original `Unify` relation for an
occurs failure, a constructor clash and a renumbering success.

`Examples/SolverExamples.v` additionally checks runtime conversion, scope
rejection, existing aliases, shadowing, and failure under an existing binding.
It specializes the ordered-answer correspondence to the reference and
structural implementations.

`Print Assumptions` reports `Closed under the global context` for the algorithm,
its ground correctness proofs, the structural solver instance, and the core
search correspondence theorems. The full build and `coqchk` audit register these
modules. The executable, checked-interface, representative-relation, and CLI
tests exercise the structural implementation through the public entry points.
The answer-projection theorem retains the existing functional-extensionality
dependency of substitution application; see [the proof guide](proofs.md) for
precise trust boundaries.
