From Stdlib Require Import List Arith.
Import ListNotations.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees.
Require Import MkRedex.Semantics.Reduction MkRedex.Semantics.WellFormed.
Set Default Goal Selector "!".

(* Any tdelay directly under a combinator is immediately a head redex follows by computation. *)
Lemma delay_not_stranded_conj : forall G t g,
  head G (tconj (tdelay t) g) = Some (tdelay (tconj t g)).
Proof. reflexivity. Qed.

Lemma delay_not_stranded_disjL : forall G t r2,
  head G (tdisjL (tdelay t) r2) = Some (tdelay (tdisjR t r2)).
Proof. reflexivity. Qed.

Lemma delay_not_stranded_disjR : forall G r2 t,
  head G (tdisjR r2 (tdelay t)) = Some (tdelay (tdisjL r2 t)).
Proof. reflexivity. Qed.

(* Final configurations and step-shape classification *)
Definition is_final (t : tree) : Prop :=
  t = tfail \/ exists s, t = tgoal gsucc s.

(* Which top-level step rule applies to a tree. *)
Inductive step_shape (G : env) : tree -> Prop :=
  | SS_ctx      : forall E r r',
      head G r = Some r' ->
      step_shape G (plug E r)
  | SS_delay    : forall t,
      step_shape G (tdelay t)
  | SS_promoteL : forall s t2,
      step_shape G (tdisjL (tgoal gsucc s) t2)
  | SS_promoteR : forall t1 s,
      step_shape G (tdisjR t1 (tgoal gsucc s)).

(* Progress for trees *)
Lemma tree_progress : forall G t,
  closed_env G ->
  (exists c, closed_tree G c t) ->
  tight_tree G t ->
  is_final t \/ step_shape G t.
Proof.
  intros G t HcG.
  induction t as
    [ | g s
      | t' IHt'
      | n l s
      | tc IHtc gc
      | tL IHtL tR IHtR
      | tL IHtL tR IHtR ];
  intros [c Hclosed] Htt.

  (* tfail: final *)
  - left. left. reflexivity.

  (* tgoal g s *)
  - destruct g.
    + (* gsucc: value *)
      left. right. exists s. reflexivity.
    + (* gunify: head always produces Some *)
      right.
      destruct (unify t t0 (st_sub s)) eqn:Eu.
      * apply (SS_ctx G chole (tgoal (gunify t t0) s)
                      (tgoal gsucc (mkstate s0 (st_cnt s)))).
        simpl. rewrite Eu. reflexivity.
      * apply (SS_ctx G chole (tgoal (gunify t t0) s) tfail).
        simpl. rewrite Eu. reflexivity.
    + (* grelcall: Delay rule *)
      right.
      apply (SS_ctx G chole (tgoal (grelcall n l) s) (tdelay (tproceed n l s))).
      reflexivity.
    + (* gdisj: DistrDisj *)
      right.
      apply (SS_ctx G chole (tgoal (gdisj g1 g2) s) (tdisjL (tgoal g1 s) (tgoal g2 s))).
      reflexivity.
    + (* gconj: DistrConj *)
      right.
      apply (SS_ctx G chole (tgoal (gconj g1 g2) s) (tconj (tgoal g1 s) g2)).
      reflexivity.
    + (* gfresh: SubstFresh *)
      right.
      apply (SS_ctx G chole (tgoal (gfresh n g) s)
               (tgoal (open (map tvar (seq (st_cnt s) n)) g)
                      (mkstate (st_sub s) (st_cnt s + n)))).
      reflexivity.

  (* tdelay t': S_delay applies *)
  - right. apply SS_delay.

  (* tproceed n l s: Proceed rule, arity given by closed_tree *)
  - simpl in Hclosed.
    destruct (nth_error G n) as [[n0 body]|] eqn:En.
    + destruct Hclosed as [_ [Hlen _]].
      right.
      apply (SS_ctx G chole (tproceed n l s) (tgoal (open l body) s)).
      simpl. rewrite En. rewrite <- Hlen. rewrite Nat.eqb_refl. reflexivity.
    + exact (False_ind _ Hclosed).

  (* tconj tc gc *)
  - simpl in Hclosed, Htt.
    destruct Hclosed as [Hct _].
    destruct Htt as [Htt1 _].
    destruct (IHtc (ex_intro _ c Hct) Htt1) as [Hfin | Hss].
    + (* tc is final *)
      destruct Hfin as [-> | [s ->]].
      * (* PruneConj: tconj tfail g -> tfail *)
        right. apply (SS_ctx G chole (tconj tfail gc) tfail). reflexivity.
      * (* SuccConj: tconj (tgoal gsucc s) g -> tgoal g s *)
        right. apply (SS_ctx G chole (tconj (tgoal gsucc s) gc) (tgoal gc s)). reflexivity.
    + (* tc can step: invert to find which shape *)
      inversion Hss; subst.
      * (* tc = plug E r with head G r = Some r': lift via cconj *)
        right.
        apply (SS_ctx G (cconj E gc) r r').
        exact H.
      * (* tc = tdelay t0: DelayConj *)
        right.
        apply (SS_ctx G chole (tconj (tdelay t) gc) (tdelay (tconj t gc))).
        reflexivity.
      * (* tc = tdisjL (tgoal gsucc s) t2: LeftAnsConj *)
        right.
        apply (SS_ctx G chole
                 (tconj (tdisjL (tgoal gsucc s) t2) gc)
                 (tdisjL (tconj (tgoal gsucc s) gc) (tconj t2 gc))).
        reflexivity.
      * (* tc = tdisjR t1 (tgoal gsucc s): RightAnsConj *)
        right.
        apply (SS_ctx G chole
                 (tconj (tdisjR t1 (tgoal gsucc s)) gc)
                 (tdisjR (tconj t1 gc) (tconj (tgoal gsucc s) gc))).
        reflexivity.

  (* tdisjL tL tR: recurse on left branch *)
  - simpl in Hclosed, Htt.
    destruct Hclosed as [HctL _].
    destruct Htt as [HttL _].
    destruct (IHtL (ex_intro _ c HctL) HttL) as [Hfin | Hss].
    + destruct Hfin as [-> | [s ->]].
      * (* PruneLeft: tdisjL tfail tR -> tR *)
        right. apply (SS_ctx G chole (tdisjL tfail tR) tR). reflexivity.
      * (* tL = tgoal gsucc s: S_promoteL *)
        right. apply (SS_promoteL G s tR).
    + inversion Hss; subst.
      * (* lift ctx step on tL via cdisjL *)
        right.
        apply (SS_ctx G (cdisjL E tR) r r').
        exact H.
      * (* tL = tdelay t0: DelayLeft *)
        right.
        apply (SS_ctx G chole (tdisjL (tdelay t) tR) (tdelay (tdisjR t tR))).
        reflexivity.
      * (* tL = tdisjL (tgoal gsucc s) t2: AssocLeftLeft *)
        right.
        apply (SS_ctx G chole
                 (tdisjL (tdisjL (tgoal gsucc s) t2) tR)
                 (tdisjL (tgoal gsucc s) (tdisjL t2 tR))).
        reflexivity.
      * (* tL = tdisjR t1 (tgoal gsucc s): AssocLeftRight *)
        right.
        apply (SS_ctx G chole
                 (tdisjL (tdisjR t1 (tgoal gsucc s)) tR)
                 (tdisjR (tdisjL t1 tR) (tgoal gsucc s))).
        reflexivity.

  (* tdisjR tL tR: recurse on right branch *)
  - simpl in Hclosed, Htt.
    destruct Hclosed as [_ HctR].
    destruct Htt as [_ HttR].
    destruct (IHtR (ex_intro _ c HctR) HttR) as [Hfin | Hss].
    + destruct Hfin as [-> | [s ->]].
      * (* PruneRight: tdisjR tL tfail -> tL *)
        right. apply (SS_ctx G chole (tdisjR tL tfail) tL). reflexivity.
      * (* tR = tgoal gsucc s: S_promoteR *)
        right. apply (SS_promoteR G tL s).
    + inversion Hss; subst.
      * (* lift ctx step on tR via cdisjR *)
        right.
        apply (SS_ctx G (cdisjR tL E) r r').
        exact H.
      * (* tR = tdelay t0: DelayRight *)
        right.
        apply (SS_ctx G chole (tdisjR tL (tdelay t)) (tdelay (tdisjL tL t))).
        reflexivity.
      * (* tR = tdisjL (tgoal gsucc s) t2: AssocRightLeft *)
        right.
        apply (SS_ctx G chole
                 (tdisjR tL (tdisjL (tgoal gsucc s) t2))
                 (tdisjL (tgoal gsucc s) (tdisjR tL t2))).
        reflexivity.
      * (* tR = tdisjR t1 (tgoal gsucc s): AssocRightRight *)
        right.
        apply (SS_ctx G chole
                 (tdisjR tL (tdisjR t1 (tgoal gsucc s)))
                 (tdisjR (tdisjR tL t1) (tgoal gsucc s))).
        reflexivity.
Qed.

Theorem progress : forall G e,
  closed_env G ->
  ok_expr G e ->
  is_final (snd e) \/ exists e', G |= e --> e'.
Proof.
  intros G [ans t] HcG Hok.
  simpl.
  destruct Hok as [[c Hclosed] [Htt _]].
  simpl in Hclosed, Htt.
  destruct (tree_progress G t HcG (ex_intro _ c Hclosed) Htt) as [Hfin | Hss].
  - left. exact Hfin.
  - right.
    inversion Hss; subst.
    + exists (ans, plug E r'). apply S_ctx. exact H.
    + exists (ans, t0).        apply S_delay.
    + exists (ans ++ [s], t2). apply S_promoteL.
    + exists (ans ++ [s], t1). apply S_promoteR.
Qed.

Theorem progress_and_preservation : forall G e e',
  closed_env G ->
  ok_expr G e ->
  multi G e e' ->
  is_final (snd e') \/ exists e'', G |= e' --> e''.
Proof.
  intros G e e' HcG Hok Hmulti.
  apply progress.
  - exact HcG.
  - exact (multi_ok G e e' Hmulti HcG Hok).
Qed.
