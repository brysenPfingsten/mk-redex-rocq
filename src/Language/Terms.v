From Stdlib Require Import List String Bool Arith.
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

Lemma term_eq_dec : forall t u : term, {t = u} + {t <> u}.
Proof.
  decide equality; try apply Nat.eq_dec; try apply String.string_dec;
    try apply Bool.bool_dec.
Defined.

(** * term_eqb *)
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
Notation "x =? y" := (term_eqb x y).

Theorem term_eqb_refl : forall t,
  t =? t = true.
Proof.
  induction t; simpl; 
  try apply Nat.eqb_refl; 
  try apply String.eqb_refl.
  - destruct b; reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

(** https://www.chargueraud.org/research/2009/ln/main.pdf *)
Fixpoint open_term (d : nat) (args : list term) (t : term) : term :=
  match t with
  | tpar i =>
      if i <? d then tpar i
      else match nth_error args (i - d) with
           | Some u => u
           | None => tpar (i - List.length args)
           end
  | tcons a b => tcons (open_term d args a) (open_term d args b)
  | _ => t
  end.

(** * tsize *)
Fixpoint tsize (t : term) : nat :=
  match t with
  | tcons a b => S (tsize a + tsize b)
  | _ => 1
  end.
