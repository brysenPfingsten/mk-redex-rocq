From Stdlib Require Import List String Arith.
From MkRedex.Language Require Import Terms Goals.
Import ListNotations.
Set Default Goal Selector "!".

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

Definition fresh_equality_body : goal := gfresh 1 (gunify (tpar 1) (tpar 0)).

(* "Substitute Relation Body": the relation called with "cat" opens the head parameter. *)
Example step_subst_body :
  open [tsym "cat"] fresh_equality_body = gfresh 1 (gunify (tsym "cat") (tpar 0)).
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
