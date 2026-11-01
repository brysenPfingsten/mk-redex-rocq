From Stdlib Require Import List Arith.
Import ListNotations.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees.
Set Default Goal Selector "!".

(* ================================================================== *)
(*  Head — inductive head-reduction relation                           *)
(* ================================================================== *)

(** [Head G r r'] holds when tree [r] reduces to [r'] by a single head step
    in environment [G].  Constructors correspond one-to-one with the
    mk-redex head-reduction rules. *)
Inductive Head (G : env) : tree -> tree -> Prop :=

  (* ---- Goal rules ---- *)

  | H_unify_ok : forall t1 t2 s s',
      Unify t1 t2 (st_sub s) (Some s') ->
      Head G (tgoal (gunify t1 t2) s)
             (tgoal gsucc (mkstate s' (st_cnt s)))

  | H_unify_fail : forall t1 t2 s,
      Unify t1 t2 (st_sub s) None ->
      Head G (tgoal (gunify t1 t2) s) tfail

  | H_disj : forall g1 g2 s,
      Head G (tgoal (gdisj g1 g2) s)
             (tdisjL (tgoal g1 s) (tgoal g2 s))

  | H_conj : forall g1 g2 s,
      Head G (tgoal (gconj g1 g2) s)
             (tconj (tgoal g1 s) g2)

  | H_fresh : forall k g s,
      Head G (tgoal (gfresh k g) s)
             (tgoal (open (map tvar (seq (st_cnt s) k)) g)
                    (mkstate (st_sub s) (st_cnt s + k)))

  | H_relcall : forall r ts s,
      Head G (tgoal (grelcall r ts) s)
             (tdelay (tproceed r ts s))

  (* ---- Proceed rule ---- *)

  | H_proceed : forall r ts s n body,
      nth_error G r = Some (n, body) ->
      length ts = n ->
      Head G (tproceed r ts s) (tgoal (open ts body) s)

  (* ---- Conjunction rules ---- *)

  | H_prune_conj : forall g,
      Head G (tconj tfail g) tfail

  | H_succ_conj : forall g s,
      Head G (tconj (tgoal gsucc s) g) (tgoal g s)

  | H_left_ans_conj : forall s t2 g,
      Head G (tconj (tdisjL (tgoal gsucc s) t2) g)
             (tdisjL (tconj (tgoal gsucc s) g) (tconj t2 g))

  | H_right_ans_conj : forall s t1 g,
      Head G (tconj (tdisjR t1 (tgoal gsucc s)) g)
             (tdisjR (tconj t1 g) (tconj (tgoal gsucc s) g))

  | H_delay_conj : forall t g,
      Head G (tconj (tdelay t) g) (tdelay (tconj t g))

  (* ---- Disjunction rules ---- *)

  | H_prune_left : forall t,
      Head G (tdisjL tfail t) t

  | H_prune_right : forall t,
      Head G (tdisjR t tfail) t

  | H_assoc_ll : forall s r r2,
      Head G (tdisjL (tdisjL (tgoal gsucc s) r) r2)
             (tdisjL (tgoal gsucc s) (tdisjL r r2))

  | H_assoc_lr : forall r s r2,
      Head G (tdisjL (tdisjR r (tgoal gsucc s)) r2)
             (tdisjR (tdisjL r r2) (tgoal gsucc s))

  | H_assoc_rl : forall r2 s r,
      Head G (tdisjR r2 (tdisjL (tgoal gsucc s) r))
             (tdisjL (tgoal gsucc s) (tdisjR r2 r))

  | H_assoc_rr : forall r2 r s,
      Head G (tdisjR r2 (tdisjR r (tgoal gsucc s)))
             (tdisjR (tdisjR r2 r) (tgoal gsucc s))

  | H_delay_left : forall r1 r2,
      Head G (tdisjL (tdelay r1) r2) (tdelay (tdisjR r1 r2))

  | H_delay_right : forall r2 r1,
      Head G (tdisjR r2 (tdelay r1)) (tdelay (tdisjL r2 r1)).

Hint Constructors Head : core.

(** [Head] is functional: each tree has at most one head reduct. *)
Lemma Head_functional : forall G r r' r'',
  Head G r r' -> Head G r r'' -> r' = r''.
Proof.
  intros.
  inversion H; inversion H0; subst;
  try discriminate; try congruence;
  injection H5 as <- <-; subst;
  apply Unify_functional with (1:=H1) in H4.
  - injection H4 as <-. reflexivity.
  - discriminate H4.
  - discriminate H4.
Qed.

(* ================================================================== *)
(*  Step and multi-step                                                 *)
(* ================================================================== *)

Reserved Notation "G '|=' e '-->' e'" (at level 40, e at level 39).

Inductive step (G : env) : expr -> expr -> Prop :=
  | S_ctx : forall ans E r r',
      Head G r r' ->
      G |= (ans, plug E r) --> (ans, plug E r')
  | S_delay : forall ans t,
      G |= (ans, tdelay t) --> (ans, t)
  | S_promoteL : forall ans s t,
      G |= (ans, tdisjL (tgoal gsucc s) t) --> (ans ++ [s], t)
  | S_promoteR : forall ans s t,
      G |= (ans, tdisjR t (tgoal gsucc s)) --> (ans ++ [s], t)

where "G '|=' e '-->' e'" := (step G e e').

Hint Constructors step : core.

Inductive multi (G : env) : expr -> expr -> Prop :=
  | multi_refl : forall e, multi G e e
  | multi_step : forall e1 e2 e3,
      G |= e1 --> e2 -> multi G e2 e3 -> multi G e1 e3.

Hint Constructors multi : core.
