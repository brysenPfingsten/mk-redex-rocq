# Proof guide

This guide describes why the main arguments work, not just where their statements occur.
The source links identify the formal definitions and supporting lemmas.
All proofs use the same `Head` and `step` relations; the marked trees used below are proof annotations whose erasures are ordinary runtime trees.

## Conventions and the final statement

A term has two kinds of variables.
`tpar i` is a bound de Bruijn index: its meaning comes from a lexical block of relation parameters or fresh binders.
`tvar x` is an allocated logic-variable ID.
A state contains a substitution and a counter naming the next ID available for allocation.
These roles are separate even though both indices are natural numbers.

An expression is an accumulated list of answer states paired with a search tree.
Disjunction nodes indicate the selected side, and a conjunction node contains a left subtree plus a suspended right goal.
A top-level success is terminal and is itself an observed answer, even when it has not been moved into the accumulated list.
`observed_answers` includes both locations.

The source denotation interprets terms as finite ground values.
A valuation assigns such a value to every logic-variable ID; a separate lexical list interprets parameters.
Goal satisfaction is inductive.
In particular, a recursive call is justified by a finite derivation for its body.
A relation that only calls itself has no solutions; a recursive relation with a base clause can have solutions with finite proofs even when its search is infinite.

The final theorem, `source_solution_iff_runner_answer`, is in [Correctness/Completeness.v](../src/Correctness/Completeness.v). 
Fix a closed environment, a source goal scoped at the initial counter, and original query IDs below that counter.
Starting with an empty substitution, a ground assignment on those IDs satisfies the source goal exactly when some finite fuel budget produces an observed answer representing that assignment.

Representation means that the answer substitution can be satisfied by a valuation agreeing with the proposed assignment on the query IDs.
Other IDs are existentially hidden.
This allows a symbolic answer to represent many ground solutions and makes internal allocation names irrelevant.
It also explains the allocation hypothesis: an original query ID must not later be reused as a newly allocated existential variable.

## Unification

### Walking, substitution application, and acyclicity

[Language/Substitution.v](../src/Language/Substitution.v) specifies `Walk`, which follows bindings at the head of a term, and `ApplySub`, which also recursively expands both components of a pair.
Their functionality proofs induct over one derivation and invert a competing derivation.
A variable lookup either finds the same binding in both derivations or is absent in both; pair components then agree by the induction hypotheses.

Acyclicity rules out an infinite chain of dependencies between bound variables.
It is stated as well-foundedness of the relation saying that one variable occurs in another variable's binding.
The totality arguments in [Language/Unification.v](../src/Language/Unification.v) combine this well-founded dependency relation with structural descent through pairs.
Following a binding cannot continue indefinitely, and descending into a pair cannot continue indefinitely without either reaching a constructor or following another binding.
Thus valid substitutions have total relational walking and application.

The executable application function uses the corresponding well-founded recursion, rather than guessing a fuel bound from substitution length.
That distinction matters: binding chains and constructor depth both contribute to expansion.
The graph theorem `apply_sub_spec` proves that the computed result is exactly the relational `ApplySub` result.

### Soundness, most-generality, and failure

Relational unification first walks both input heads, then applies `UnifyW`.
Successful variable binding requires that the variable be unbound and that the occurs check pass.
Equal rigid constructors succeed; incompatible rigid constructors fail.
Pair unification processes the first components and then processes the second components in the resulting substitution.

The success proof follows this derivation.
It establishes that substitution extension does not destroy earlier bindings or their meaning.
The occurs condition makes the added binding acyclic.
For pairs, the first recursive result establishes equality of the heads; extension compatibility transports that equality through the second recursive result, which establishes equality of the tails.
The resulting substituted pairs are therefore equal.

Most-generality uses `models_sub`: a candidate substitution respects each binding of the current substitution when both sides are interpreted through the candidate.
If a candidate respects the input bindings and unifies the terms, it must also respect each binding introduced by the algorithm.
In a variable case this follows from the equality the candidate already imposes; in a pair case the argument is applied successively to both recursive calls.
The model argument yields a factorization through the computed substitution.

Failure completeness examines each failing rule.
Different rigid constructors cannot become equal.
A failure in a pair component contradicts a candidate that unifies the whole pair.
For occurs failure, a ground finite value would have to contain itself as a proper subvalue after interpreting dependencies; a size argument rules that out.
The general failure theorem is phrased in terms of models so that candidates need not keep input bindings syntactically unchanged.

### Totality on scoped inputs and execution

[Language/ScopedUnification.v](../src/Language/ScopedUnification.v) proves `Unify_total`.
Ordinary structural induction is insufficient: solving a pair's first components can enlarge substitutions and expand the second components.
The proof instead uses a lexicographic pair:

1. the number of still-unbound IDs below the allocation counter;
2. the sum of the sizes of the fully substituted terms.

A genuinely changed successful substitution binds an available ID, decreasing the first component.
If the substitution is unchanged, recursive pair work has smaller substituted components, decreasing the second component.
The first coordinate may decrease even if substitution expansion increases term size.
Closure keeps the relevant variable domain finite, and acyclicity supplies the substituted terms used to state the measure.
Walking lifts the result for already-walked terms to arbitrary valid inputs.

[Execution/Unifier.v](../src/Execution/Unifier.v) implements a fuel-indexed attempt that returns either a certified unification outcome or insufficient fuel.
Induction on a relational derivation shows that every derivation is recognized at all sufficiently large fuel values.
Totality supplies a relational outcome, so searching increasing fuel must eventually find a successful attempt.
Functionality then proves `unify_fn_spec`: the function and relation have exactly the same outcome on valid inputs.
This establishes termination but is not an efficiency bound.

### A single solver-correctness contract

`unification_correct_result c s t u result`, in [Correctness/Unification.v](../src/Correctness/Unification.v), packages the individual results into one property.
Its specification field identifies the outcome selected by the relational solver.
Its failure field states an if-and-only-if: the outcome is `None` exactly when no compatible acyclic unifier exists.
Its success field states that the returned substitution is a `most_general_extension` of the input.

A compatible unifier is acyclic, models the original bindings through substitution application, and unifies the two terms.
Modeling the input is more general than requiring its bindings to be copied literally: a competing solution may already have expanded those bindings.
The acyclicity condition is essential because the relational definition of unifier quantifies over substitution-application results; without total application, that condition could hold vacuously.

A most general extension remains closed at the same allocation counter, is acyclic, prefixes new bindings to the original substitution, preserves each visible old lookup, and unifies the terms.
Every compatible acyclic unifier factors through it.
These clauses make the operational representation and mathematical MGU property explicit in the same contract.

`unification_correct` proves that valid inputs have exactly one outcome satisfying this contract.
First, `Unify_mgu` collects closure, acyclicity, extension, non-rebinding, soundness, and model-based most-generality for a successful relational outcome.
Then `Unify_correct_result` packages any relational outcome: failure completeness excludes compatible solutions in the failure case, while a successful output is itself a compatible solution, which proves the reverse direction of the failure equivalence.
Functionality establishes exact agreement with the specified relational outcome.
Finally, `Unify_total` supplies an outcome, and the contract's specification field makes it unique.
This uniqueness belongs to the specified solver; different substitution representations can still be equally general mathematically.

`unify_fn_correct` proves the same contract for the actual value computed by `unify_fn`.
Its graph-equivalence theorem supplies a relational derivation for that value, and the packaging lemma supplies the full contract.
The executable function is total on its proof-indexed valid domain; the theorem does not add a uniform bound on its internal fuel search.
The relational contract theorem has no axiom dependencies; the executable theorem inherits the existing assumptions of executable unification.

### Ground valuations and the unifier

[Correctness/Unification.v](../src/Correctness/Unification.v) connects these syntactic results to the source meaning.
A valuation satisfying a substitution gives a variable the same value as its visible binding.
Induction over `Walk` and `ApplySub` therefore shows that they preserve ground interpretation.
The relational success theorem then gives ground equality of unified inputs.

For the converse, `ground_sub c rho` binds every ID below `c` to a quoted version of its ground value under `rho`.
This finite substitution is acyclic because its range contains no variables.
On closed terms, substitution by `ground_sub` agrees with valuation interpretation.
If `rho` satisfies the input substitution and equates the inputs, the finite grounding is a model and unifier of those inputs.
Failure completeness excludes a failing outcome; unification totality supplies a successful one.
Most-generality shows that the grounding models the output substitution, and a reflection lemma converts that statement back to satisfaction by `rho`.
Thus successful unification preserves the very ground solution used as the completeness witness.

## Determinism and machine safety

### Unique decomposition

[Operational/Determinism.v](../src/Operational/Determinism.v) proves that two candidate contextual head reductions cannot select different redex positions.
The proof compares their context shapes.
Distinct disjunction orientations cannot both be active, and an enclosing head redex excludes a competing selected-child head redex.
The technical lemmas characterize which atomic shapes a plugged head redex cannot have.
This also separates contextual head steps from the three root-only operations: delay release and answer promotion from either side.

Once the positions coincide, `Head_functional` gives the same destination.
Its only computationally nontrivial case is equality, where unification functionality identifies the outcome.
Combining unique decomposition with the mutually exclusive root cases yields `step_deterministic`.

### Preservation

The runtime invariant in [Language/WellFormed.v](../src/Language/WellFormed.v) combines `ok_tree` with `ok_sub` for accumulated answers. `ok_sub` requires both scoped bindings and acyclicity, so every active and accumulated substitution satisfies the same contract. [Operational/WellFormed.v](../src/Operational/WellFormed.v) proves preservation and progress.
`ok_tree` checks goals, substitutions, and pending relation calls at each state's own counter, including relation existence and arity.
A conjunction's continuation must be valid for every state in its left subtree. An existential goal-scoping check also validates the continuation when that subtree has no states.

Head preservation is proved by cases on the head rule.
Unification uses closure and acyclicity of the output substitution.
Fresh allocation opens with the consecutive IDs starting at the local counter, raises that counter, and uses opening safety to establish closure of the body.
Proceed lookup uses the closed environment and the arity premise to open the relation body.
Structural rules preserve the needed state/continuation relationships.

The `ok_tree` preservation argument needs more than replacing a valid redex by a valid reduct.
A surrounding conjunction mentions all states reachable through its left subtree.
State-transfer lemmas establish that its suspended goal remains closed at the counters produced by the head rewrite.
This handles fresh allocation and the distribution of a continuation across disjunctions.
Context replacement lemmas lift the head results to the full expression.
Promotion moves a state into the answer list and uses its local closure facts there.
Induction on `multi` extends one-step preservation to finite runs.

### Progress

Progress inducts on the runtime tree.
Failure and a top-level success are terminal.
An equality has a unification outcome by totality.
A relation call first delays; a pending proceed node has a valid lookup and arity from closure.
A fresh goal can allocate and open directly.
For compound trees, either the selected child can step or its terminal/delay shape enables a structural head rule or root promotion.
The continuation obligations ensure that resuming a conjunction remains within the valid syntax.
These cases exclude a stuck valid active goal without assuming that every search ends.

## Delay scheduling and global no-stranding

### Local movement and finite bursts

[Operational/Delay.v](../src/Operational/Delay.v) first proves an exact local bound: a delay on the selected path moves across one context frame per head step.
Induction on context depth constructs the trace.
A conjunction moves inside the delay; crossing a disjunction changes its selected side.
Once the delay reaches the root, one further step releases it.

An inactive delay first needs its branch to receive a turn.
For that argument, a burst stops at a terminal expression or a root delay.
Ordinary tree size does not decrease through all burst rules: proceeding can expose a large relation body, and conjunction distribution can duplicate continuations.
The proof uses the count of active proceed nodes as the first coordinate and a weighted structural-work measure as the second.
Work under a delay is ignored because reaching that delay ends the burst.
Proceed reduces the first coordinate even when its body enlarges the tree; administrative rewrites reduce the second coordinate.
Well-founded induction, using progress and preservation, produces a finite burst.
Its terminal or delay boundary lets a waiting disjunction branch take a turn.

### Tracking the chosen occurrence

[Operational/DelayTracking.v](../src/Operational/DelayTracking.v) distinguishes one delay by its position.
`erase_marked` removes the annotation.
A carry step preserves the occurrence, while a release step removes that particular delay.
`marked_step_correspondence` classifies real steps from erased marked states as carries or releases and proves the reverse projection.
Induction extends this classification over finite traces.
This prevents a proof from claiming success merely because some other syntactically equal delay was released.

When the marker is active, structural delay movement finishes the argument.
The difficult part is preserving it while other work runs or while the surrounding tree is rearranged.

### Focusing a finite shell

[Operational/Scheduling.v](../src/Operational/Scheduling.v) lifts finite bursts through disjunction contexts.
A selected sibling eventually succeeds, fails, or yields a delay.
Success is promoted or reassociated, failure is pruned, and a delay rotates selection.
Each outcome permits a finite handoff toward the marked subtree.

Counting all waiting nodes globally is not a valid termination argument: reassociation changes their placement and conjunction execution can create new disjunctions.
The proof instead fixes an inner marked subtree and measures the finite disjunction shell currently surrounding it.
A macro handoff either puts that subtree on the selected path or strictly decreases the shell's `scheduler_index`.
Well-founded induction gives `disj_shell_eventually_focused`.
The index is a local proof measure, not a claim that a global property of every runtime step decreases.

### Conjunction and the global theorem

[Operational/DelayFairness.v](../src/Operational/DelayFairness.v) handles the obstacle to simply replaying a local trace inside an arbitrary context.
A local answer under conjunction is not a top-level answer: it starts the right goal, possibly distributing that goal across a disjunction and moving the marked work into a waiting position.

The contextual carry lemmas inspect a local step, perform the corresponding outer rewrite, and describe the resulting finite shell around the residual marked work.
The shell-focusing theorem gives that work another turn before the next local step is lifted.
Induction on a finite local carry trace lifts the entire trace through conjunction or disjunction.
Answer-list rebasing allows the surrounding computation to have emitted additional answers.

Finally, `eventually_active` inducts on the marked tree.
An outer delay is released first.
Conjunction and disjunction cases use the contextual lifting results on the induction witness for the marked child.
Once active, the local release argument yields `global_no_stranding`.
This concerns an actual chosen runtime delay occurrence, not an arbitrary recursive call hidden in unexecuted source syntax.
Determinism makes its finite release prefix agree with any execution that continues taking steps; no independent scheduler fairness axiom is assumed.

## Search soundness

[Correctness/Soundness.v](../src/Correctness/Soundness.v) gives remaining work a meaning under a fixed ground valuation.
An active goal requires both a model of its state's substitution and source satisfaction of its goal.
A proceed node has the meaning of its relation call.
Delay preserves meaning, disjunction is union, and conjunction requires both the left work and the suspended goal under the same valuation.
Expression meaning additionally includes valuations satisfying already accumulated answers.

The central lemma works backward: if the destination of a head step has a meaning, so does its source.
For unification, a model of the successful output satisfies the old bindings and makes the compared terms equal.
For fresh, the ground values assigned to the new IDs witness the source existential; opening correspondence gives satisfaction of the unopened body.
Proceed uses the same opening correspondence for relation arguments.
Reassociation, delay movement, and continuation distribution preserve the relevant unions and conjunctions.

A context-monotonicity lemma lifts this implication to contextual head steps.
For promotion, satisfaction of the newly accumulated answer supplies the success disjunct in the preceding tree. 
Induction on a finite run repeatedly applies backward preservation, using runtime preservation to discharge its validity assumptions.
An observed final success is handled alongside the accumulated answers.

If an answer represents a proposed query assignment, take the valuation witness from that representation and run this argument backward.
At the initial expression the accumulated list is empty, so its meaning must come from satisfaction of the original goal.
The witness already agrees with the query assignment, which establishes projected source satisfaction.
This is `search_soundness`; runner reachability gives executable soundness.

## Search completeness

### Why the soundness proof cannot be reversed

A fixed valuation can satisfy `fresh x. x = 7` even if it currently assigns zero to the ID that the machine will allocate for `x`.
Source satisfaction chooses an existential value, while allocation chooses an ID.
Forward reasoning must therefore change valuation values for new IDs without changing old constraints or the original query.
The checked counterexample in [Examples/DenotationExamples.v](../src/Examples/DenotationExamples.v) makes this failure of fixed-valuation simulation explicit.

[Denotational/Valuations.v](../src/Denotational/Valuations.v) proves that scoped goals and closed substitutions depend only on values below their counter.
`extend_valuation` writes the existentially chosen values into the new block and agrees with the old valuation below its start.
Consequently it preserves the current substitution and any pending continuation scoped at the old counter.
The opening theorem then turns the source body's lexical witness into a witness for the runtime body with allocated IDs.

### From delay fairness to arbitrary work

Completeness needs to schedule chosen work that need not already be a delay.
[Correctness/Focus.v](../src/Correctness/Focus.v) uses the existing occurrence machinery without changing the machine.
In a proof-only tree, wrap the chosen work in a marked delay.
This preserves tree validity, states occurring in the subtree, and acyclicity.
Apply eventual activation to that tree, but stop its carry trace at the first active occurrence.

Before activation, a carry cannot inspect or bubble the distinguished delay itself.
Each such step is therefore valid when the marked position contains the original arbitrary work instead.
`inactive_carry_fill` proves this parametricity by cases on the carry rules.
Removing the synthetic wrapper from the finite prefix gives a trace in the original step relation.
`focus_work` also proves that the list of conjunction continuations on the chosen path is unchanged.
This preservation is necessary for the logical witness used by the main induction.

### Propagating a success

[Correctness/Success.v](../src/Correctness/Success.v) uses head-only traces: each step is a contextual head rewrite and can therefore be lifted through another active context.
Induction on an active context propagates a chosen success.
Disjunction reassociation exposes that answer on the appropriate side.
A conjunction either consumes the success immediately or distributes its continuation over the exposed disjunction and then consumes it in the chosen branch.
The result is either an observable answer or the next suspended goal with the same successful state.
It is not enough to observe an answer in a subtree and assume it survives as a top-level answer.

### The decreasing logical witness

[Denotational/Derivations.v](../src/Denotational/Derivations.v) annotates finite satisfaction derivations with a natural-number work index.
Success has index zero, equality has index one, and compound goals include overhead in addition to their successful subderivations.
Opening and valuation agreement preserve this index.
A pending list adds one unit per goal as well as each goal's index, so even consuming a successful goal decreases the pending measure.

The main theorem `pending_finds_answer` in [Correctness/Completeness.v](../src/Correctness/Completeness.v) assumes a successful derivation for the current goal and for each continuation on the chosen path, plus a valuation satisfying the current substitution.
It performs well-founded induction on their total pending work:

- Focus the current work. This may take many runtime steps, but it preserves the logical witness and the continuation list.
- For equality, ground unification completeness supplies a successful result that retains the valuation model. Replace equality by success, decreasing logical work.
- For disjunction, follow the branch used by the satisfaction derivation. The other branch remains in the runtime tree. The focusing lemma handles it if the chosen branch is waiting.
- For conjunction, start its left goal and push the right derivation onto the continuation list. The constructor's overhead makes this split decrease total pending work despite adding a list entry.
- For fresh, extend the valuation on the new block and transport the current and continuation witnesses. Existing query values and bindings are retained.
- For a relation call, perform its delay-producing step, focus the proceed work, unfold the body, and use semantic opening to retain its finite source derivation with smaller work.
- For success, expose an observed answer or start the next continuation. Starting that continuation removes the current pending entry and decreases the measure even when its derivation index was zero.

Runtime preservation supplies validity after every constructed prefix.
The final answer has a substitution model agreeing with the original valuation below the initial counter, hence on the original query IDs.
Starting this general theorem with a one-element pending list gives `source_search_completeness`.

The work index is not a runtime bound.
Focusing may run unrelated branches for an arbitrarily large finite number of steps.
The theorem says that a particular finitely justified ground solution appears after finite search; it neither decides when an unsuccessful infinite search should stop nor provides a uniform fuel bound for all solutions.

## Execution, validation, and reports

[Execution/Executable.v](../src/Execution/Executable.v) proves separate sound and complete graph theorems for executable head reduction.
`active_head_fn` first checks an enclosing head rewrite and otherwise descends only along the selected child.
The decomposition lemmas exclude a competing enclosing head rule when a selected contextual redex exists.
Root delay release and answer promotion complete `next_step_spec`.

The finite runner uses preservation to supply the next recursive call's validity witness.
Induction on fuel proves its output is reachable by `multi`.
[Execution/RunnerCorrespondence.v](../src/Execution/RunnerCorrespondence.v) proves the converse for a specified number of steps: the computed first step must agree with the relational first step by determinism, and induction handles the tail.
Every finite `multi` run has a step count, so every such endpoint can be reproduced by some fuel.
This transfers reduction completeness to the runner and combines it with soundness in the final equivalence theorem.

[Execution/Input.v](../src/Execution/Input.v) decides the existing propositions rather than introducing a second validity specification.
It traverses terms and goals, checks relation lookup and arity, validates bodies at parameter depth equal to their arity and allocation bound zero, and checks query IDs.
A successful result carries proofs of these propositions.
The rejection and acceptance theorems establish that no valid request is rejected and no invalid request is accepted.
Recursion in the source environment does not make the checker recursive through relation calls: calls check their signatures, and each relation body is traversed once as syntax.

[Execution/Interface.v](../src/Execution/Interface.v) constructs the empty initial substitution and runs with those certificates.
Its reporting runner has the same final expression as `run_steps`.
Terminal classification inspects the final syntax, which handles completion exactly at the fuel boundary without taking an extra step.
Induction proves that stopping early implies a terminal expression and that exhausted runs consume the supplied step budget.

The trace proof records the initial state and every actual successor; adjacent entries satisfy `step`, the last entry is the reported final state, and its length is the executed step count plus one.
Projection requires a further invariant: promoted answer substitutions are acyclic.
This is proved over steps and finite runs, then combined with `apply_sub_spec`.
`Forall2` relates each displayed binding, in query order, to relational substitution application on the corresponding answer state.
Thus projection expands deep bindings without altering the answers they describe.

The checked-run refinement theorem identifies every accepted report with one of these certified runs.
Soundness and completeness are transferred through its agreement with `run_steps`; parsing and printing remain outside these proofs.

## Assumptions and verification boundaries

The relational search soundness/completeness and ground unification results are closed under the global context: `Print Assumptions` reports no axiom dependencies.
Executable results inherit proof irrelevance and dependent functional extensionality used in the executable unification development.
Proof irrelevance identifies proofs of the same proposition; dependent functional extensionality identifies dependent functions with pointwise equal outputs.
These assumptions concern proof infrastructure rather than adding an unproved fairness or completeness premise.

Compilation checks the proof terms, and `coqchk` independently checks all registered compiled modules.
The executable tests check parser/display and integration behavior in addition to the extracted functions.
They do not replace the universal proofs.
Extraction, OCaml compilation and runtime, and the handwritten parser/printer remain outside the kernel's verification of the source theorems.
The checked entry point validates source requests; low-level extracted functions still have erased preconditions, and raw runtime checkpoints are not accepted by the public source interface.
