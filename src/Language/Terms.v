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

Theorem eqb_refl : forall t,
  t =? t = true.
Proof.
  induction t; simpl; 
  try apply Nat.eqb_refl; 
  try apply String.eqb_refl.
  - destruct b; reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

(** * open_term *)
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

Definition a : term := tsym "a".
Definition b : term := tsym "b".
 
(** ** The parameter that gets filled *)
Example ot_hit0 : open_term 0 [a; b] (tpar 0) = a.
Proof. reflexivity. Qed.
Example ot_hit1 : open_term 0 [a; b] (tpar 1) = b.
Proof. reflexivity. Qed.
 
(** ** Depth shields inner binders *)
Example ot_shielded : open_term 2 [a; b] (tpar 1) = tpar 1.
Proof. reflexivity. Qed.
Example ot_boundary_open : open_term 2 [a; b] (tpar 2) = a.
Proof. reflexivity. Qed.
 
(** ** With depth d, tpar (d+j) looks up args[j]. *)
Example ot_depth_offset : open_term 3 [a; b] (tpar 4) = b.
Proof. reflexivity. Qed.
 
(** ** Out-of-range indices shift down by length args *)
Example ot_oob : open_term 0 [a] (tpar 3) = tpar 2.
Proof. reflexivity. Qed.
Example ot_oob2 : open_term 0 [a; b] (tpar 5) = tpar 3.
Proof. reflexivity. Qed.
 
(** ** Non-parameter terms pass through unchanged *)
Example ot_tvar  : open_term 0 [a; b] (tvar 0)      = tvar 0.
Proof. reflexivity. Qed.
Example ot_tvar5 : open_term 0 [a; b] (tvar 5)      = tvar 5.
Proof. reflexivity. Qed.
Example ot_sym   : open_term 0 [a; b] (tsym "z")    = tsym "z".
Proof. reflexivity. Qed.
Example ot_nat   : open_term 0 [a; b] (tnat 7)      = tnat 7.
Proof. reflexivity. Qed.
Example ot_bool  : open_term 0 [a; b] (tbool true)  = tbool true.
Proof. reflexivity. Qed.
Example ot_nil   : open_term 0 [a; b] tnil          = tnil.
Proof. reflexivity. Qed.
 
(** ** Structural recursion through tcons *)
Example ot_cons :
  open_term 0 [a; b] (tcons (tpar 0) (tcons (tpar 1) tnil))
  = tcons a (tcons b tnil).
Proof. reflexivity. Qed.
 
Example ot_cons_mix :
  open_term 1 [a] (tcons (tpar 0) (tcons (tpar 1) (tvar 9)))
  = tcons (tpar 0) (tcons a (tvar 9)).
Proof. reflexivity. Qed.
 
(** ** Empty args is the identity *)
Example ot_empty_par : open_term 0 [] (tpar 4) = tpar 4.
Proof. reflexivity. Qed.
Example ot_empty_any : open_term 3 [] (tcons (tpar 0) (tvar 2)) = tcons (tpar 0) (tvar 2).
Proof. reflexivity. Qed.


(** * tsize *)
Fixpoint tsize (t : term) : nat :=
  match t with
  | tcons a b => S (tsize a + tsize b)
  | _ => 1
  end.

(** *** Test tsize *)
Example tsize_var : tsize (tvar 0) = 1.
Proof. reflexivity. Qed.
Example tsize_par : tsize (tpar 0) = 1.
Proof. reflexivity. Qed.
Example tsize_sym : tsize (tsym "a") = 1.
Proof. reflexivity. Qed.
Example tsize_str : tsize (tstr "a") = 1.
Proof. reflexivity. Qed.
Example tsize_nat : tsize (tnat 0) = 1.
Proof. reflexivity. Qed.
Example tsize_true : tsize (tbool true) = 1.
Proof. reflexivity. Qed.
Example tsize_false : tsize (tbool false) = 1.
Proof. reflexivity. Qed.
Example tsize_nil : tsize tnil = 1.
Proof. reflexivity. Qed.
Example tsize_cons :
  tsize (tcons (tcons (tnat 0) tnil) (tcons (tnat 1) (tcons (tstr "a") tnil))) = 9.
Proof. reflexivity. Qed.
