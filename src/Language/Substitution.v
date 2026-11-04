From Stdlib Require Import List Arith.
Import ListNotations.
Require Import MkRedex.Language.Terms.
Set Default Goal Selector "!".

(* Substitutions *)

Definition sub := list (nat * term).

Lemma sub_eq_dec : forall s1 s2 : sub, {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
  decide equality; [apply term_eq_dec | apply Nat.eq_dec].
Defined.

Fixpoint lookup (x : nat) (s : sub) : option term :=
  match s with
  | [] => None
  | (y, t) :: s' => if Nat.eqb x y then Some t else lookup x s'
  end.

(* Walk *)

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

Inductive Walk (s : sub) : term -> term -> Prop :=
  | W_free  : forall x, lookup x s = None -> Walk s (tvar x) (tvar x)
  | W_bound : forall x u r, lookup x s = Some u -> Walk s u r -> Walk s (tvar x) r
  | W_rigid : forall t, (forall x, t <> tvar x) -> Walk s t t.

Lemma Walk_functional : forall s t out1 out2,
  Walk s t out1 -> Walk s t out2 -> out1 = out2.
Proof.
  intros s t1 t2 out Ht1.
  induction Ht1; intros Ht2; inversion Ht2; subst;
  try reflexivity; try congruence.
  apply IHHt1. rewrite -> H in H1. injection H1 as ->. exact H2.
Qed.

(* Occurs Check *)

Fixpoint occurs (x : nat) (t : term) : bool :=
  match t with
  | tvar y => Nat.eqb x y
  | tcons a b => orb (occurs x a) (occurs x b)
  | _ => false
  end.

Inductive DeepOccurs (s : sub) (x : nat) : term -> Prop :=
  | DO_var  : DeepOccurs s x (tvar x)
  | DO_walk : forall y t,
      lookup y s = Some t ->
      DeepOccurs s x t ->
      DeepOccurs s x (tvar y)
  | DO_cons_l : forall a b, DeepOccurs s x a -> DeepOccurs s x (tcons a b)
  | DO_cons_r : forall a b, DeepOccurs s x b -> DeepOccurs s x (tcons a b).

Inductive ApplySub (s : sub) : term -> term -> Prop :=
  | AS_free  : forall x,
      lookup x s = None ->
      ApplySub s (tvar x) (tvar x)
  | AS_bound : forall x u r,
      lookup x s = Some u ->
      ApplySub s u r ->
      ApplySub s (tvar x) r
  | AS_cons  : forall a b a' b',
      ApplySub s a a' ->
      ApplySub s b b' ->
      ApplySub s (tcons a b) (tcons a' b')
  | AS_rigid : forall t,
      (forall x, t <> tvar x) ->
      (forall a b, t <> tcons a b) ->
      ApplySub s t t.

Lemma ApplySub_functional : forall s t out1 out2,
  ApplySub s t out1 -> ApplySub s t out2 -> out1 = out2.
Proof.
  intros s t out1 out2 Hout1. generalize dependent out2.
  induction Hout1; intros out2 Hout2; inversion Hout2; subst;
  try reflexivity; try congruence.
  - apply IHHout1. rewrite -> H in H1. injection H1 as <-. exact H2.
  - apply IHHout1_1 in H1 as <-. apply IHHout1_2 in H3 as <-. reflexivity.
Qed.

(* Acyclicity *)

Definition acyclic_sub (s : sub) : Prop :=
  well_founded (fun y x => exists t, lookup x s = Some t /\ occurs y t = true).

Record state : Type := mkstate {
  st_sub : sub;
  st_cnt : nat
}.
