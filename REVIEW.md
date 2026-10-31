# Formalization Review

Issues and suggestions beyond the unification correctness stubs in `Substitution.v`
and `WellFormed.v`, which are tracked directly in those files.

---

## Foundational Issues

### `closed_program` and `ok_expr` are disconnected

`WellFormed.v` defines both `closed_program` (line 63) and `ok_expr` (line 853),
and all theorems (`progress`, `step_ok`, `multi_ok`) use `ok_expr`.  There is no
lemma connecting them.  A user setting up a concrete program starts with
`closed_program` and has no path to apply any theorem.

**Missing lemma:**
```coq
Lemma closed_program_ok : forall G e,
  closed_env G -> closed_program G e -> ok_expr G e.
```

`closed_expr` (line 71) is also defined but never used anywhere.  Delete it or
wire it into `closed_program` / `ok_expr`.

---

### `open_term` out-of-range shifting is uncommented

When `nth_error args (i - d) = None` (i.e. `i - d >= length args`), `open_term`
returns `tpar (i - length args)` — a de Bruijn shift for parameters that belong to
an outer binder.  This is load-bearing for nested `gfresh` to compose correctly,
but there is no comment explaining it and no compositional lemma.

**Missing lemma:**
```coq
(* Sequential opens compose: opening args2 into a term that was already
   opened with args1 equals a single open with the composed substitution. *)
Lemma open_term_compose : forall d1 d2 args1 args2 t, ...
```

Without this, the correctness of the two-step `gfresh` → `grelcall` sequence
(first `open` substitutes relation arguments, then the fresh step calls `open`
again for the body) rests on unverified assumptions about how `open_term` nests.

---

### Potential bug in `unify` fuel bound

The fuel in `unify` is `S (tsize t1 + tsize t2 + length s)`.  After calling
`walk t1 s` and `walk t2 s`, the walked terms `a` and `b` can be strictly larger
than `t1` and `t2` (if a variable is bound to a large term in `s`).  The recursive
`tcons` case passes `a1, b1` as sub-terms of `a, b` to a call with fuel reduced by
one — but `tsize a1 + tsize b1` can exceed `tsize t1 + tsize t2`.

Proving `unify_fuel_sufficient` (stub in `Substitution.v`) will either verify the
bound or expose that the correct bound is:

```coq
Definition sum_tsize (s : sub) : nat := fold_right (fun '(_, t) acc => tsize t + acc) 0 s.

Definition unify (t1 t2 : term) (s : sub) : option sub :=
  unify_f (S (tsize t1 + tsize t2 + sum_tsize s)) t1 t2 s.
```

---

### `gfresh k` is undocumented and unjustified

Standard miniKanren uses `fresh x. g` (one variable).  Your `gfresh k g`
introduces `k` variables at once, and the `closed_goal` predicate increments both
the depth and counter by `k` simultaneously.  This is a deliberate design choice
but it is never justified or discussed, and there is no lemma showing that
`gfresh k g` is equivalent to `k` nested `gfresh 1` applications (if that is even
intended to hold).

---

## Naming and Design Problems

### `plug_injective` is misnamed

`Determinism.v` line 192:
```coq
Lemma plug_injective: forall E r1 r2,
  plug E r1 = plug E r2 -> r1 = r2.
```
This is injectivity in the redex argument for a *fixed* context `E`, not
injectivity of `plug` in general.  Rename to `plug_inj_redex` or `plug_cancel`.

---

### `step_shape` in `Progress.v` is redundant

`step_shape G t` (Progress.v line 25) is an inductive that mirrors the four
constructors of `step`.  `tree_progress` produces a `step_shape`, then
`progress` immediately inverts it to build a `step`.  The intermediate type buys
nothing.  `tree_progress` could directly produce `exists e', G |= (ans, t) --> e'`
and eliminate the `inversion` + reconstruction at the call site.

---

### `closed_goal` is not monotone in the environment

```coq
| grelcall r ts =>
    match nth_error G r with
    | Some (n, _) => List.length ts = n /\ Forall (closed_term d c) ts
    | None        => False
    end
```

`closed_goal G d c g` refers into `G` by index.  If `G` is extended (new
relations appended), existing indices still resolve correctly, so
`closed_goal G d c g -> closed_goal (G ++ G') d c g` should hold — but there is
no `closed_goal_weaken` lemma.  If you ever want to reason about programs in a
larger environment, this will be needed.

---

## Proof Quality

### Three proofs are much larger than necessary

**`plug_redex` (Determinism.v lines 59–190, ~130 lines)**
The proof is a massive case split that rediscovers the same fact for each
constructor: plugging a redex into a non-hole context changes the root, so `head`
returns `None`.  Split into one helper per context constructor:
```coq
Lemma plug_redex_disjL : forall G E t r, head G r <> None -> E <> chole ->
  head G (tdisjL (plug E r) t) = None.
```
Then `plug_redex` follows by induction with trivial cases.

**`unify_f_closed` (WellFormed.v lines 294–354)**
Fifty near-identical `injection H as <-; repeat split; assumption` arms after an
initial case split.  A tactic like:
```coq
Ltac close_unify := try (injection H as <-; simpl; repeat split; assumption).
```
applied with `all: close_unify` after the main destruct would collapse this to
roughly 15 lines.

**`head_closed_goal_transfer` (WellFormed.v lines 677–807)**
Exists entirely to propagate the `tight_tree` invariant through head steps for the
`tconj` case.  Breaking it into per-constructor helper lemmas
(`hcgt_tgoal`, `hcgt_tproceed`, `hcgt_tconj`, `hcgt_tdisj`) would make each
piece readable and independently checkable.

---

### `tight_tree` for `tconj` deserves a comment

```coq
| tconj t' g => tight_tree G t' /\
                (forall s, state_in t' s -> closed_goal G 0 (st_cnt s) g)
```

The universally quantified `s` is necessary because different branches of `t'`
can have different counters (from independent `gfresh` firings), so `g` must be
closed with respect to all of them.  A one-line comment to this effect would save
the next reader significant confusion.

---

## Missing Theorems

Beyond the unification correctness stubs already in `Substitution.v`:

### Declarative semantics and soundness

The biggest gap in the current formalization: there is no declarative (relational)
semantics and no soundness theorem connecting the operational semantics to it.
A natural target:

```coq
(* Declarative: σ is a solution for g in G *)
Inductive satisfies (G : env) : sub -> goal -> Prop := ...

(* Soundness: every state in the answer stream satisfies the initial query *)
Theorem soundness : forall G q ans t,
  closed_env G -> ok_expr G ([], tgoal q (mkstate [] 0)) ->
  multi G ([], tgoal q (mkstate [] 0)) (ans, t) ->
  forall s, In s ans -> satisfies G (st_sub s) q.
```

### `closed_program → ok_expr`

See the disconnect issue above.  This is the entry-point lemma that makes all
existing theorems applicable to concrete programs.

### `open` composition

```coq
Lemma open_compose : forall args1 args2 g,
  open args1 (open args2 g) = open (map (fun t => open_term 0 args1 t) args2) g.
```
(Or whatever the correct statement is — working it out will verify that the
nested `gfresh` semantics is self-consistent.)

### `closed_goal` weakening in environment

```coq
Lemma closed_goal_weaken_env : forall G G' d c g,
  closed_goal G d c g -> closed_goal (G ++ G') d c g.
```

### `apply_sub` fuel adequacy

```coq
Lemma apply_sub_fuel_ok : forall t s,
  acyclic_sub s ->
  apply_sub_f (S (List.length s) * S (tsize t)) t s =
  apply_sub_f (S (S (List.length s) * S (tsize t))) t s.
```

This must be proved before `unify_sound` can be stated without a fuel hypothesis.
