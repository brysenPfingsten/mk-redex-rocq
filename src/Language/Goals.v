From MkRedex Require Import Language.Terms.
From Stdlib Require Import List String Arith.
Import ListNotations.

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

(* Tests *)
(* gunify opens both sides. *)
Example og_uni : open [a; b] (gunify (tpar 0) (tpar 1)) = gunify a b.
Proof. reflexivity. Qed.

(* grelcall maps over its argument list; the relation index is untouched. *)
Example og_call :
  open [a; b] (grelcall 3 [tpar 0; tpar 1; tsym "z"])
  = grelcall 3 [a; b; tsym "z"].
Proof. reflexivity. Qed.

(* gdisj / gconj recurse into both goals. *)
Example og_dis :
  open [a; b] (gdisj (gunify (tpar 0) (tpar 0)) (gunify (tpar 1) (tpar 1)))
  = gdisj (gunify a a) (gunify b b).
Proof. reflexivity. Qed.

Example og_con :
  open [a] (gconj (gunify (tpar 0) (tsym "z")) gsucc)
  = gconj (gunify a (tsym "z")) gsucc.
Proof. reflexivity. Qed.

(** gfresh raises the depth by its width *)

(* One binder of width 1: tpar 0 is shielded, tpar 1 refers to the group. *)
Example og_ex1 :
  open [a] (gfresh 1 (gunify (tpar 1) (tpar 0)))
  = gfresh 1 (gunify a (tpar 0)).
Proof. reflexivity. Qed.

(* Width-k binder: the k slots 0..k-1 are shielded, tpar k reaches args[0]. *)
Example og_ex_width :
  open [a; b] (gfresh 3 (gunify (tpar 3) (tpar 4)))
  = gfresh 3 (gunify a b).
Proof. reflexivity. Qed.

(* Nested binders accumulate: gfresh 2 then gfresh 1 shields 0..2, tpar 3 -> args[0]. *)
Example og_ex_nested :
  open [a] (gfresh 2 (gfresh 1 (gunify (tpar 0) (tpar 3))))
  = gfresh 2 (gfresh 1 (gunify (tpar 0) a)).
Proof. reflexivity. Qed.

Definition foo_body : goal := gfresh 1 (gunify (tpar 1) (tpar 0)).

(* "Substitute Relation Body": foo("cat") opens the head parameter. *)
Example step_subst_body :
  open [tsym "cat"] foo_body = gfresh 1 (gunify (tsym "cat") (tpar 0)).
Proof. reflexivity. Qed.

(* "Substitute Fresh Variables": the exists body gets a fresh tvar
   drawn from counter c = 0. Note tpar 0 becomes the LOGIC variable tvar 0. *)
Example step_fresh_vars :
  open (map tvar (seq 0 1)) (gunify (tsym "cat") (tpar 0))
  = gunify (tsym "cat") (tvar 0).
Proof. reflexivity. Qed.

(* A second exists in the same run draws the next counter value. *)
Example step_fresh_vars_next :
  open (map tvar (seq 1 2)) (gunify (tpar 0) (tpar 1))
  = gunify (tvar 1) (tvar 2).
Proof. reflexivity. Qed.


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
