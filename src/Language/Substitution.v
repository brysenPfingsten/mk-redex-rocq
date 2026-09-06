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

Fixpoint sum_tsize (s : sub) : nat :=
  match s with
  | []           => 0
  | (_, t) :: s' => tsize t + sum_tsize s'
  end.

Definition unify (t1 t2 : term) (s : sub) : option sub :=
  unify_f (S (tsize t1 + tsize t2 + sum_tsize s)) t1 t2 s.

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

(** Auxiliary: [walk_f] on a non-variable returns its input unchanged. *)
Lemma walk_f_nonvar_id : forall fuel t s,
  (forall x, t <> tvar x) -> walk_f fuel t s = t.
Proof.
  intros [|f] t s Hnt; simpl.
  - reflexivity.
  - destruct t; try reflexivity.
    exfalso. exact (Hnt _ eq_refl).
Qed.

(** Auxiliary: a binding's value is no larger than the whole substitution. *)
Lemma lookup_tsize_le_sum : forall x s u,
  lookup x s = Some u -> tsize u <= sum_tsize s.
Proof.
  induction s as [| [y v] s' IH]; intros u Hl.
  - discriminate.
  - simpl in Hl. destruct (Nat.eqb x y).
    + injection Hl as <-. simpl. lia.
    + apply IH in Hl. simpl. lia.
Qed.

(* ================================================================== *)
(*  Unification lemmas                                                  *)
(* ================================================================== *)

(** U1: The output substitution extends the input — [s] is a suffix of [s']. *)
Lemma unify_f_extends : forall fuel t1 t2 s s',
  unify_f fuel t1 t2 s = Some s' ->
  exists prefix, s' = prefix ++ s.
Proof.
  induction fuel as [|f IHf]; intros t1 t2 s s' Huf.
  - discriminate.
  - simpl in Huf.
    destruct (walk t1 s) as [x|i1|q1|r1|n1|bl1| |a1 a2],
             (walk t2 s) as [y|i2|q2|r2|n2|bl2| |c1 c2].
    + destruct (Nat.eqb x y).
      * injection Huf as <-. exists []. reflexivity.
      * injection Huf as <-. exists [(x, tvar y)]. reflexivity.
    + destruct (occurs x (tpar i2));
      [discriminate | injection Huf as <-; exists [(x, tpar i2)]; reflexivity].
    + destruct (occurs x (tsym q2));
      [discriminate | injection Huf as <-; exists [(x, tsym q2)]; reflexivity].
    + destruct (occurs x (tstr r2));
      [discriminate | injection Huf as <-; exists [(x, tstr r2)]; reflexivity].
    + destruct (occurs x (tnat n2));
      [discriminate | injection Huf as <-; exists [(x, tnat n2)]; reflexivity].
    + destruct (occurs x (tbool bl2));
      [discriminate | injection Huf as <-; exists [(x, tbool bl2)]; reflexivity].
    + destruct (occurs x tnil);
      [discriminate | injection Huf as <-; exists [(x, tnil)]; reflexivity].
    + destruct (occurs x (tcons c1 c2));
      [discriminate | injection Huf as <-; exists [(x, tcons c1 c2)]; reflexivity].
    + destruct (occurs y (tpar i1));
      [discriminate | injection Huf as <-; exists [(y, tpar i1)]; reflexivity].
    + destruct (term_eqb (tpar i1) (tpar i2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tpar i1) (tsym q2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tpar i1) (tstr r2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tpar i1) (tnat n2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tpar i1) (tbool bl2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tpar i1) tnil);
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tpar i1) (tcons c1 c2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (occurs y (tsym q1));
      [discriminate | injection Huf as <-; exists [(y, tsym q1)]; reflexivity].
    + destruct (term_eqb (tsym q1) (tpar i2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tsym q1) (tsym q2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tsym q1) (tstr r2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tsym q1) (tnat n2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tsym q1) (tbool bl2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tsym q1) tnil);
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tsym q1) (tcons c1 c2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (occurs y (tstr r1));
      [discriminate | injection Huf as <-; exists [(y, tstr r1)]; reflexivity].
    + destruct (term_eqb (tstr r1) (tpar i2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tstr r1) (tsym q2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tstr r1) (tstr r2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tstr r1) (tnat n2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tstr r1) (tbool bl2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tstr r1) tnil);
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tstr r1) (tcons c1 c2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (occurs y (tnat n1));
      [discriminate | injection Huf as <-; exists [(y, tnat n1)]; reflexivity].
    + destruct (term_eqb (tnat n1) (tpar i2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tnat n1) (tsym q2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tnat n1) (tstr r2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tnat n1) (tnat n2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tnat n1) (tbool bl2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tnat n1) tnil);
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tnat n1) (tcons c1 c2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (occurs y (tbool bl1));
      [discriminate | injection Huf as <-; exists [(y, tbool bl1)]; reflexivity].
    + destruct (term_eqb (tbool bl1) (tpar i2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tbool bl1) (tsym q2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tbool bl1) (tstr r2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tbool bl1) (tnat n2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tbool bl1) (tbool bl2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tbool bl1) tnil);
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tbool bl1) (tcons c1 c2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (occurs y tnil);
      [discriminate | injection Huf as <-; exists [(y, tnil)]; reflexivity].
    + destruct (term_eqb tnil (tpar i2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb tnil (tsym q2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb tnil (tstr r2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb tnil (tnat n2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb tnil (tbool bl2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb tnil tnil);
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb tnil (tcons c1 c2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (occurs y (tcons a1 a2));
      [discriminate | injection Huf as <-; exists [(y, tcons a1 a2)]; reflexivity].
    + destruct (term_eqb (tcons a1 a2) (tpar i2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tcons a1 a2) (tsym q2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tcons a1 a2) (tstr r2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tcons a1 a2) (tnat n2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tcons a1 a2) (tbool bl2));
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (term_eqb (tcons a1 a2) tnil);
      [injection Huf as <-; exists []; reflexivity | discriminate].
    + destruct (unify_f f a1 c1 s) as [s1|] eqn:Hs1.
      * apply IHf in Hs1 as [p1 Hp1].
        apply IHf in Huf as [p2 Hp2].
        exists (p2 ++ p1). subst. rewrite app_assoc. reflexivity.
      * discriminate.
Qed.

(** U2: Unification preserves acyclicity.  The occurs check in each variable
    binding case discharges the [walk_occurs_acyclic] precondition. *)
Lemma unify_f_acyclic : forall fuel t1 t2 s s',
  acyclic_sub s ->
  unify_f fuel t1 t2 s = Some s' ->
  acyclic_sub s'.
Proof. Admitted.

(* ================================================================== *)
(*  U3 support: depth measure and helper lemmas                        *)
(* ================================================================== *)

(** Number of [tcons] layers in a term — the actual recursion depth
    that [unify_f] must traverse when it reaches a pair. *)
Fixpoint tcons_depth (t : term) : nat :=
  match t with
  | tcons a b => S (Nat.max (tcons_depth a) (tcons_depth b))
  | _         => 0
  end.

(** The total [tcons] recursion depth needed by [unify_f t1 t2 s] after
    walking both terms.  This is the quantity we want to bound. *)
Definition unify_depth (t1 t2 : term) (s : sub) : nat :=
  tcons_depth (walk t1 s) + tcons_depth (walk t2 s).

(** [tcons_depth] is everywhere bounded by [tsize]. *)
Lemma tcons_depth_le_tsize : forall t, tcons_depth t <= tsize t.
Proof.
  induction t; simpl; lia.
Qed.

(** For any fuel, [walk_f] moves [tcons_depth] by at most [sum_tsize s] above
    the starting depth. *)
Lemma walk_f_tcons_depth_bound : forall fuel t s,
  tcons_depth (walk_f fuel t s) <= Nat.max (tcons_depth t) (sum_tsize s).
Proof.
  induction fuel as [|f IHf]; intros t s.
  - simpl. apply Nat.le_max_l.
  - simpl. destruct t as [x| | | | | | |a b]; try apply Nat.le_max_l.
    destruct (lookup x s) as [u|] eqn:Hlook.
    + specialize (IHf u s).
      pose proof (lookup_tsize_le_sum x s u Hlook).
      pose proof (tcons_depth_le_tsize u). simpl. lia.
    + simpl. lia.
Qed.

(** Monotonicity: more fuel cannot turn a success into a failure. *)
Lemma unify_f_mono : forall n m t1 t2 s s',
  n <= m ->
  unify_f n t1 t2 s = Some s' ->
  unify_f m t1 t2 s = Some s'.
Proof.
  induction n as [|n IHn]; intros m t1 t2 s s' Hnm Huf.
  - discriminate.
  - destruct m as [|m]; [lia |].
    simpl in *.
    destruct (walk t1 s) as [x|i|sym|str|nat'|bool'| |a1 a2],
             (walk t2 s) as [y|j|sym2|str2|nat2'|bool2'| |b1 b2];
    try exact Huf.
    (* Only the tcons/tcons case is not solved by exact Huf *)
    destruct (unify_f n a1 b1 s) as [s1|] eqn:Hs1.
    + apply IHn with (m := m) in Hs1; [| lia].
      rewrite Hs1.
      apply IHn with (m := m); [lia | exact Huf].
    + discriminate.
Qed.

(** At fuel >= [unify_depth t1 t2 s], adding one more unit of fuel is a
    no-op — the function has already seen everything it needs to see.
    We state this at [S fuel] on both sides because [unify_f 0] is always
    [None] regardless of depth, so the interesting threshold starts at 1. *)
Lemma unify_f_depth_stable : forall fuel t1 t2 s,
  fuel >= unify_depth t1 t2 s ->
  unify_f (S fuel) t1 t2 s = unify_f (S (S fuel)) t1 t2 s.
Proof. Admitted.

(** [unify_depth] is bounded by the sum of term sizes plus the sizes of
    terms stored in [s] (because [walk] can return any term bound in [s]). *)
Lemma unify_depth_bound : forall t1 t2 s,
  unify_depth t1 t2 s <= tsize t1 + tsize t2 + sum_tsize s.
Proof. Admitted.

(** U3: The fuel bound in [unify] is never the limiting factor; [None] means
    genuine non-unifiability, not exhaustion. *)
Lemma unify_fuel_sufficient : forall t1 t2 s,
  acyclic_sub s ->
  unify_f (S (tsize t1 + tsize t2 + sum_tsize s)) t1 t2 s =
  unify_f (S (S (tsize t1 + tsize t2 + sum_tsize s))) t1 t2 s.
Proof.
  intros t1 t2 s _.
  (* unify_f_depth_stable needs: tsize t1 + tsize t2 + sum_tsize s >= unify_depth t1 t2 s *)
  apply unify_f_depth_stable.
  exact (unify_depth_bound t1 t2 s).
Qed.

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
