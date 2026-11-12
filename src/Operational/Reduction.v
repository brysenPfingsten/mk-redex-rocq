From Stdlib Require Import List Arith.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees.
Import ListNotations.
Set Default Goal Selector "!".

From MkRedex.Language Require Import Solver.
Section WithSolver.
Context `{solver : Solver}.

(* ================================================================== *)
(*  Head — inductive head-reduction relation                           *)
(* ================================================================== *)

(** [Head G r r'] holds when tree [r] reduces to [r'] by a single head step
    in environment [G].  Constructors correspond one-to-one with the
    mk-redex head-reduction rules. The implicit [Solver] parameter fixes a
    deterministic implementation of the semantic unification contract;
    search rules do not prescribe its binding-list representation. *)
Inductive Head (G : env) : tree -> tree -> Prop :=

  (* ---- Goal rules ---- *)

  | H_unify_ok : forall t1 t2 s s',
      Solve (st_cnt s) t1 t2 (st_sub s) (Some s') ->
      Head G (tgoal (gunify t1 t2) s)
             (tgoal gsucc (mkstate s' (st_cnt s)))

  | H_unify_fail : forall t1 t2 s,
      Solve (st_cnt s) t1 t2 (st_sub s) None ->
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
  intros G r r' r'' H H'.
  inversion H; inversion H'; subst; try discriminate; try congruence;
    repeat match goal with
    | E : tgoal (gunify _ _) _ = tgoal (gunify _ _) _ |- _ =>
        injection E; intros; subst
    end;
    match goal with
    | A : Solve _ _ _ _ _, B : Solve _ _ _ _ _ |- _ =>
        pose proof (solve_functional _ _ _ _ _ _ A B) as E;
        inversion E; reflexivity
    end.
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

(** A step can add an answer, but never retract an observed answer. *)
Lemma Head_source_no_final_answer : forall G r r',
  Head G r r' -> final_answer r = [].
Proof.
  intros G r r' Hhead. inversion Hhead; reflexivity.
Qed.

Lemma step_observed_answers_prefix : forall G e e',
  G |= e --> e' ->
  exists added, observed_answers e' = observed_answers e ++ added.
Proof.
  intros G e e' Hstep. destruct Hstep; unfold observed_answers; simpl.
  - assert (Hsrc : final_answer (plug E r) = []). {
      destruct E; simpl; try reflexivity.
      exact (Head_source_no_final_answer G r r' H).
    }
    rewrite Hsrc. exists (final_answer (plug E r')).
    rewrite app_nil_r. reflexivity.
  - exists (final_answer t). rewrite app_nil_r. reflexivity.
  - exists (s :: final_answer t).
    rewrite app_nil_r. induction ans as [|a ans IH]; simpl; congruence.
  - exists (s :: final_answer t).
    rewrite app_nil_r. induction ans as [|a ans IH]; simpl; congruence.
Qed.

Inductive multi (G : env) : expr -> expr -> Prop :=
  | multi_refl : forall e, multi G e e
  | multi_step : forall e1 e2 e3,
      G |= e1 --> e2 -> multi G e2 e3 -> multi G e1 e3.

Hint Constructors multi : core.

Lemma multi_observed_answers_prefix : forall G e e',
  multi G e e' ->
  exists added, observed_answers e' = observed_answers e ++ added.
Proof.
  intros G e e' Hmulti. induction Hmulti.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (step_observed_answers_prefix G e1 e2 H) as [a Ha].
    destruct IHHmulti as [b Hb].
    exists (a ++ b). rewrite Hb, Ha, app_assoc. reflexivity.
Qed.

End WithSolver.

Notation "G '|=' e '-->' e'" := (step G e e')
  (at level 40, e at level 39).
