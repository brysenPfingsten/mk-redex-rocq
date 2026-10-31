From Stdlib Require Import List String Bool Arith Lia Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".
Notation "x && y" := (andb x y).

Inductive term : Type :=
  | tvar  : nat -> term
  | tpar  : nat -> term
  | tsym  : string -> term
  | tstr  : string -> term
  | tnat  : nat -> term
  | tbool : bool -> term
  | tnil  : term
  | tcons : term -> term -> term.

Fixpoint term_eqb (t1 t2 : term) : bool :=
  match t1, t2 with
  | tvar a, tvar b   => Nat.eqb a b
  | tpar a, tpar b   => Nat.eqb a b
  | tsym a, tsym b   => String.eqb a b
  | tstr a, tstr b   => String.eqb a b
  | tnat a, tnat b   => Nat.eqb a b
  | tbool a, tbool b => Bool.eqb a b
  | tnil, tnil       => true
  | tcons a1 a2, tcons b1 b2 => (term_eqb a1 b1) && (term_eqb a2 b2)
  | _, _ => false
  end.

Fixpoint tsize (t : term) : nat :=
  match t with
  | tcons a b => S (tsize a + tsize b)
  | _ => 1
  end.

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

Definition acyclic_sub (s : sub) : Prop :=
  exists rank : nat -> nat,
    forall x t, lookup x s = Some t ->
    forall y, occurs y t = true -> rank y < rank x.

Lemma walk_f_nonvar_id : forall fuel t s,
  (forall x, t <> tvar x) -> walk_f fuel t s = t.
Proof.
  intros [|f] t s Hnt; simpl.
  - reflexivity.
  - destruct t; try reflexivity.
    exfalso. exact (Hnt _ eq_refl).
Qed.

Lemma walk_f_acyclic_aux : forall (rank_fn : nat -> nat) s,
  (forall x' t, lookup x' s = Some t ->
   forall y, occurs y t = true -> rank_fn y < rank_fn x') ->
  forall n x fuel,
  rank_fn x <= n ->
  fuel > n ->
  match walk_f fuel (tvar x) s with
  | tvar y => lookup y s = None
  | _ => True
  end.
Proof.
  intros rank_fn s Hrank.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros x fuel Hrx Hfuel.
  destruct fuel as [|f]; [lia|].
  simpl.
  destruct (lookup x s) as [u|] eqn:Hlook.
  - destruct u as [y|i|q|r|k|b| |a1 a2].
    + assert (Hry : rank_fn y < rank_fn x).
      { exact (Hrank x (tvar y) Hlook y (Nat.eqb_refl y)). }
      apply IHn with (rank_fn y); lia.
    + rewrite walk_f_nonvar_id; [trivial | intros z H; discriminate].
    + rewrite walk_f_nonvar_id; [trivial | intros z H; discriminate].
    + rewrite walk_f_nonvar_id; [trivial | intros z H; discriminate].
    + rewrite walk_f_nonvar_id; [trivial | intros z H; discriminate].
    + rewrite walk_f_nonvar_id; [trivial | intros z H; discriminate].
    + rewrite walk_f_nonvar_id; [trivial | intros z H; discriminate].
    + rewrite walk_f_nonvar_id; [trivial | intros z H; discriminate].
  - trivial.
Qed.

Lemma walk_f_acyclic_result : forall (rank_fn : nat -> nat) x s fuel,
  (forall x' t, lookup x' s = Some t ->
   forall y, occurs y t = true -> rank_fn y < rank_fn x') ->
  fuel > rank_fn x ->
  match walk_f fuel (tvar x) s with
  | tvar y => lookup y s = None
  | _ => True
  end.
Proof.
  intros rank_fn x s fuel Hrank Hfuel.
  exact (walk_f_acyclic_aux rank_fn s Hrank (rank_fn x) x fuel (Nat.le_refl _) Hfuel).
Qed.

(* ---- W4: walk_occurs_acyclic ---- *)
Lemma walk_occurs_acyclic : forall x t s,
  acyclic_sub s ->
  lookup x s = None ->
  occurs x (walk t s) = false ->
  acyclic_sub ((x, walk t s) :: s).
Proof.
  intros x t s [rank Hrank] Hnone Hocc.
Admitted.

(* ---- W1: walk_result_form ---- *)
Lemma walk_result_form : forall t s,
  acyclic_sub s ->
  match walk t s with
  | tvar x => lookup x s = None
  | _      => True
  end.
Proof.
  intros t s [rank Hrank].
Admitted.

(* ---- W2: walk_fuel_sufficient ---- *)
Lemma walk_fuel_sufficient : forall fuel t s,
  acyclic_sub s ->
  fuel >= S (List.length s) ->
  walk_f fuel t s = walk_f (S (List.length s)) t s.
Proof.
  intros fuel t s [rank Hrank] Hge.
Admitted.

(* ---- W3: walk_idempotent ---- *)
Lemma walk_idempotent : forall t s,
  acyclic_sub s -> walk (walk t s) s = walk t s.
Proof.
  intros t s Hac.
Admitted.
