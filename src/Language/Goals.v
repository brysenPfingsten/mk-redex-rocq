From MkRedex.Language Require Import Terms.
From Stdlib Require Import List String Arith.
Import ListNotations.
Set Default Goal Selector "!".


Inductive goal : Type :=
  | gsucc    : goal                     (* T *)
  | gunify   : term -> term -> goal     (* t =? t *)
  | grelcall : nat -> list term -> goal (* r t ... The nat is the index into env. *)
  | gdisj    : goal -> goal -> goal     (* g ∨ g *)
  | gconj    : goal -> goal -> goal     (* g ∧ g *)
  | gfresh   : nat -> goal -> goal.     (* ∃ (x_1..x_k) g *)

Fixpoint open_goal (d : nat) (args : list term) (g : goal) : goal :=
  match g with
  | gsucc         => gsucc
  | gunify t1 t2  => gunify (open_term d args t1) (open_term d args t2)
  | grelcall r ts => grelcall r (map (open_term d args) ts)
  | gdisj g1 g2   => gdisj (open_goal d args g1) (open_goal d args g2)
  | gconj g1 g2   => gconj (open_goal d args g1) (open_goal d args g2)
  | gfresh k g1   => gfresh k (open_goal (d + k) args g1)
  end.

Definition open (args : list term) (g : goal) : goal := open_goal 0 args g.

(* Properties *)
Close Scope string_scope.

Lemma nth_error_nil : forall (A : Type) k, nth_error (@nil A) k = None.
Proof. intros A k. destruct k; reflexivity. Qed.

Lemma open_term_nil_id : forall d t, open_term d [] t = t.
Proof.
  intros d t. revert d. induction t; intro d; simpl; try reflexivity.
  - (* tpar n *) destruct (Nat.ltb n d).
    * reflexivity.
    * rewrite nth_error_nil, Nat.sub_0_r. reflexivity.
  - (* tcons *) rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma open_goal_nil_id : forall d g, open_goal d [] g = g.
Proof.
  intros d g. revert d. induction g; intro d; simpl;
    repeat rewrite open_term_nil_id; try reflexivity.
  - (* grelcall *) f_equal. rewrite <- (map_id l) at 2.
    apply map_ext. intro. apply open_term_nil_id.
  - (* gdisj *) rewrite IHg1, IHg2. reflexivity.
  - (* gconj *) rewrite IHg1, IHg2. reflexivity.
  - (* gfresh  *) rewrite IHg. reflexivity.
Qed.

Corollary open_nil_id : forall g, open [] g = g.
Proof. intro g. apply open_goal_nil_id. Qed.
