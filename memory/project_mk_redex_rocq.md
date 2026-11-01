---
name: project-mk-redex-rocq
description: Rocq (Coq) formalization of mk-redex miniKanren reduction semantics — current state, design decisions, and open proof obligations
metadata:
  type: project
---

Coq/Rocq formalization of a small-step reduction semantics for miniKanren (mk-redex). Goals: prove metatheory (determinism, progress, preservation) and eventually equivalence with a denotational semantics (deferred — design not settled yet).

**Why:** `make -f Makefile.coq` to compile (the top-level `make` only checks if Makefile.coq is up to date, it does not invoke it).

## Current architecture

- `src/Language/Terms.v` — term type: `tvar` (logic var), `tpar` (de Bruijn param), atoms, `tcons`
- `src/Language/Goals.v` — goal type: `gsucc`, `gunify`, `grelcall`, `gdisj`, `gconj`, `gfresh k`
- `src/Language/Substitution.v` — `walk`, `occurs`, `apply_sub`, `acyclic_sub`, **`Unify` inductive** (11 constructors), theorem stubs
- `src/Language/Environments.v` — `env = list (nat * goal)`
- `src/Language/Trees.v` — `tree`, `expr`, `ctx`, `plug`
- `src/Semantics/Reduction.v` — **`Head` inductive** (20 constructors), `step`, `multi`
- `src/Semantics/WellFormed.v` — closedness predicates, `tight_tree`, `ok_expr`, preservation lemmas
- `src/Semantics/Determinism.v` — determinism lemmas and theorem

## Key design decisions (2026-10-31)

Switched from computational `unify_f`/`head` functions to inductive relations `Unify` and `Head`. Motivations:
- `head` as a 70-line pattern-match caused enormous case-analysis proofs in WellFormed.v
- Inductive relations allow induction on derivations for metatheory proofs
- `Unify` inductive has 11 constructors covering all cases (var-same, var-bind, var-fail, sym-bind, sym-fail, cons-ok, cons-fail, cons-clash-r, cons-clash-l, rigid-eq, rigid-neq)
- `Head` inductive has 20 constructors (2 for unify success/fail, 18 for tree reduction rules)

**How to apply:** always use induction on `Unify`/`Head` derivations for proofs, not pattern matching on term structure.

## Open proof obligations (all Admitted)

**Substitution.v:**
- `Unify_functional` — Unify result is unique
- `Unify_extends` — success extends the substitution
- `Unify_acyclic` — success preserves acyclic_sub
- `Unify_sound` — success produces a genuine unifier (needs apply_sub)

**WellFormed.v:**
- `Unify_closed` — success on closed terms gives closed sub
- `Head_closed` — Head step preserves existence of closed bound
- `Head_tight` — Head step preserves tight_tree invariant
- `Head_closed_goal_transfer` — states in head reduct have closed goals

**Reduction.v:**
- `Head_functional` — Head is deterministic (needed for step_deterministic)

**Determinism.v:**
- `Head_plug_stable` — plugging a redex into non-hole context kills redex
- `unique_decomp` — unique context decomposition (uses Head_plug_stable)
- `step_deterministic` — follows from unique_decomp + Head_functional

## Proved

- `step_ok`, `multi_ok` — preservation of ok_expr (compile against Admitted dependencies)
- `Head_no_delay/promoteL/promoteR` — Head does not fire on delay/promote shapes
- `Head_ctx_disjL/R/conj_excl` — Head fires only on context slot
- `ctx_not_delay/promoteL/promoteR` — S_ctx incompatible with other step shapes
- All closedness infrastructure in WellFormed.v
- `plug_tight_head` — proved (uses Admitted Head_closed_goal_transfer)
