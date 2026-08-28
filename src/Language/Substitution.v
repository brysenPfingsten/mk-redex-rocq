From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import MkRedex.Language.Terms.
Set Default Goal Selector "!".

Definition sub := list (nat * term).

Fixpoint lookup (x : nat) (s : sub) : option term :=
  match s with
  | [] => None
  | (y, t) :: s' => if Nat.eqb x y then Some t else lookup x s'
  end.

Fixpoint walk_f (fuel : nat) (t : term) (s : sub) : term :=
  match fuel with
  | 0 => t
  | S f =>
      match t with
      | tvar x => match lookup x s with
                  | Some u => walk_f f u s
                  | None => t
                  end
      | _ => t
      end
  end.

Definition walk (t : term) (s : sub) : term := walk_f (S (List.length s)) t s.

Fixpoint occurs (x : nat) (t : term) : bool :=
  match t with
  | tvar y => Nat.eqb x y
  | tcons a b => orb (occurs x a) (occurs x b)
  | _ => false
  end.

Fixpoint unify_f (fuel : nat) (t1 t2 : term) (s : sub) : option sub :=
  match fuel with
  | 0 => None
  | S f =>
      let a := walk t1 s in
      let b := walk t2 s in
      match a, b with
      | tvar x, tvar y => if Nat.eqb x y then Some s else Some ((x, b) :: s)
      | tvar x, _ => if occurs x b then None else Some ((x, b) :: s)
      | _, tvar y => if occurs y a then None else Some ((y, a) :: s)
      | tcons a1 a2, tcons b1 b2 =>
          match unify_f f a1 b1 s with
          | Some s1 => unify_f f a2 b2 s1
          | None => None
          end
      | _, _ => if term_eqb a b then Some s else None
      end
  end.

Definition unify (t1 t2 : term) (s : sub) : option sub :=
  unify_f (S (tsize t1 + tsize t2 + List.length s)) t1 t2 s.

Record state : Type := mkstate {
  st_sub : sub;
  st_cnt : nat
}.

(* ================================================================== *)
(*  apply_sub                                                           *)
(* ================================================================== *)

(** [walk] only chases the top-level variable chain; [apply_sub_f] additionally
    recurses into [tcons] so every logic variable in the term is eliminated.
    Fuel bounds recursion; the adequate bound for acyclic [s] is established
    by [apply_sub_fuel_ok] (to be proved). *)
Fixpoint apply_sub_f (fuel : nat) (t : term) (s : sub) : term :=
  match fuel with
  | 0    => walk t s
  | S f  =>
      let t' := walk t s in
      match t' with
      | tcons a b => tcons (apply_sub_f f a s) (apply_sub_f f b s)
      | _         => t'
      end
  end.

Definition apply_sub (t : term) (s : sub) : term :=
  apply_sub_f (S (List.length s) * S (tsize t)) t s.

(* ================================================================== *)
(*  acyclic_sub                                                         *)
(* ================================================================== *)

(** A substitution is acyclic if there is a variable ranking under which every
    binding maps to terms whose [tvar] nodes rank strictly lower.  This is the
    invariant that guarantees [walk_f (S (length s))] never exhausts its fuel.
    A per-binding check using [occurs] is NOT equivalent: a cycle [x→y→x]
    passes individual [occurs] tests because the fuel-limited [walk] masks the
    cycle. *)
Definition acyclic_sub (s : sub) : Prop :=
  exists rank : nat -> nat,
    forall x t, lookup x s = Some t ->
    forall y, occurs y t = true -> rank y < rank x.

(* ================================================================== *)
(*  Walk lemmas                                                         *)
(* ================================================================== *)

(** W1: [walk t s] always terminates at a fixed point: if the result is a
    [tvar x], then [x] has no binding in [s]. *)
Lemma walk_result_form : forall t s,
  match walk t s with
  | tvar x => lookup x s = None
  | _      => True
  end.
Proof. Admitted.

(** W2: For acyclic [s], any fuel >= [S (length s)] gives the same result.
    The chain length from any variable is bounded by the rank function,
    which in turn is bounded by the size of the domain of [s]. *)
Lemma walk_fuel_sufficient : forall fuel t s,
  acyclic_sub s ->
  fuel >= S (List.length s) ->
  walk_f fuel t s = walk_f (S (List.length s)) t s.
Proof. Admitted.

(** W3: Walking the result of walking is a no-op for acyclic [s]. *)
Lemma walk_idempotent : forall t s,
  acyclic_sub s -> walk (walk t s) s = walk t s.
Proof. Admitted.

(** W4: Adding [(x, walk t s)] to [s] preserves acyclicity, provided [x] is
    currently unbound and does not appear in [walk t s].  This is exactly the
    precondition checked by the occurs test in [unify_f] before each binding. *)
Lemma walk_occurs_acyclic : forall x t s,
  acyclic_sub s ->
  lookup x s = None ->
  occurs x (walk t s) = false ->
  acyclic_sub ((x, walk t s) :: s).
Proof. Admitted.

(* ================================================================== *)
(*  Unification lemmas                                                  *)
(* ================================================================== *)

(** U1: The output substitution extends the input — [s] is a suffix of [s']. *)
Lemma unify_f_extends : forall fuel t1 t2 s s',
  unify_f fuel t1 t2 s = Some s' ->
  exists prefix, s' = prefix ++ s.
Proof. Admitted.

(** U2: Unification preserves acyclicity.  The occurs check in each variable
    binding case discharges the [walk_occurs_acyclic] precondition. *)
Lemma unify_f_acyclic : forall fuel t1 t2 s s',
  acyclic_sub s ->
  unify_f fuel t1 t2 s = Some s' ->
  acyclic_sub s'.
Proof. Admitted.

(** U3: The fuel bound in [unify] is never the limiting factor; [None] means
    genuine non-unifiability, not exhaustion.
    WARNING: the current bound [S (tsize t1 + tsize t2 + length s)] uses
    [length s] as a proxy for the sizes of terms stored in [s].  If [walk]
    expands a variable to a large term, the actual work after walking can
    exceed this bound.  Proving this lemma will either confirm the bound or
    expose that it must be strengthened to [S (tsize t1 + tsize t2 + sum_tsize s)]
    where [sum_tsize s] is the sum of [tsize] over all terms in [s]. *)
Lemma unify_fuel_sufficient : forall t1 t2 s,
  acyclic_sub s ->
  unify_f (S (tsize t1 + tsize t2 + List.length s)) t1 t2 s =
  unify_f (S (S (tsize t1 + tsize t2 + List.length s))) t1 t2 s.
Proof. Admitted.

(** U4: Soundness — the returned substitution unifies the two input terms
    when applied deeply.  Proof proceeds by induction on fuel, using W3
    (idempotent walk) and U2 (acyclicity preserved) at each binding step. *)
Lemma unify_sound : forall t1 t2 s s',
  acyclic_sub s ->
  unify t1 t2 s = Some s' ->
  apply_sub t1 s' = apply_sub t2 s'.
Proof. Admitted.

(** U5: Minimality (MGU) — any other unifier [σ] that is consistent with
    the input [s] is also consistent with the output [s'].  Together with U4
    this makes [s'] a most-general unifier.  Needed for completeness of the
    answer stream. *)
Lemma unify_mgu : forall t1 t2 s s',
  acyclic_sub s ->
  unify t1 t2 s = Some s' ->
  forall σ,
    (forall x t, lookup x s  = Some t -> walk (tvar x) σ = walk t σ) ->
    apply_sub t1 σ = apply_sub t2 σ ->
    (forall x t, lookup x s' = Some t -> walk (tvar x) σ = walk t σ).
Proof. Admitted.

(** U6: Completeness of failure — if [unify] returns [None] then no
    extension of [s] can unify the terms.  The contrapositive of U5. *)
Lemma unify_failure_complete : forall t1 t2 s σ,
  acyclic_sub s ->
  (forall x t, lookup x s = Some t -> walk (tvar x) σ = walk t σ) ->
  unify t1 t2 s = None ->
  apply_sub t1 σ <> apply_sub t2 σ.
Proof. Admitted.
