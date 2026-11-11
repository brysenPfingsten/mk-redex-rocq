From Stdlib Require Import List Arith Lia.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees Unification WellFormed WellFormedProperties ScopedUnification.
From MkRedex.Operational Require Import Reduction.
Import ListNotations.
Set Default Goal Selector "!".

Lemma ok_tree_proceed_open_args : forall G r ts s,
  ok_tree G (tproceed r ts s) -> runtime_open_args (st_cnt s) ts.
Proof.
  intros G r ts s Hok. simpl in Hok.
  destruct (nth_error G r) as [[n body]|]; [exact (proj1 (proj2 Hok)) | contradiction].
Qed.

Lemma plug_ok_tree_inv : forall G E r,
  ok_tree G (plug E r) -> ok_tree G r.
Proof.
  intros G E. induction E; intros r H; simpl in *.
  - exact H.
  - exact (IHE _ (proj1 H)).
  - exact (IHE _ (proj2 H)).
  - exact (IHE _ (proj1 H)).
Qed.

Lemma state_in_tgoal_eq : forall g s s', state_in (tgoal g s) s' -> s' = s.
Proof. intros g s s' H. inversion H. subst. reflexivity. Qed.

Lemma state_in_conj_inv : forall t g s, state_in (tconj t g) s -> state_in t s.
Proof. intros t g s H. inversion H. assumption. Qed.

Lemma state_in_disjL_inv : forall t1 t2 s,
  state_in (tdisjL t1 t2) s -> state_in t1 s \/ state_in t2 s.
Proof.
  intros t1 t2 s H. inversion H; [left | right]; assumption.
Qed.

Lemma state_in_disjR_inv : forall t1 t2 s,
  state_in (tdisjR t1 t2) s -> state_in t1 s \/ state_in t2 s.
Proof.
  intros t1 t2 s H. inversion H; [left | right]; assumption.
Qed.

Lemma state_in_plug_into : forall E r s,
  state_in r s -> state_in (plug E r) s.
Proof.
  induction E; intros r s H; simpl;
  try (constructor; apply IHE; assumption).
  exact H.
Qed.

(* A head step can copy, discard, or advance states, but cannot introduce
   a state with a smaller counter than its source. *)
Lemma Head_state_counter : forall G r r',
  Head G r r' -> forall s', state_in r' s' ->
  exists s, state_in r s /\ st_cnt s <= st_cnt s'.
Proof.
  intros G r r' Hhead.
  induction Hhead; intros out Hsin;
    repeat match goal with
    | H : state_in tfail _ |- _ => inversion H
    | H : state_in (tdelay _) _ |- _ => inversion H; subst; clear H
    | H : state_in (tconj _ _) _ |- _ => inversion H; subst; clear H
    | H : state_in (tdisjL _ _) _ |- _ => inversion H; subst; clear H
    | H : state_in (tdisjR _ _) _ |- _ => inversion H; subst; clear H
    | H : state_in (tgoal _ _) _ |- _ => inversion H; subst; clear H
    | H : state_in (tproceed _ _ _) _ |- _ => inversion H; subst; clear H
    end;
    try (exists s; split; [eauto 10 | simpl; lia]);
    try (exists out; split; [eauto 10 | lia]).
Qed.

(* Every state in r' has a corresponding state in r with counter <= st_cnt s',
   so any ok_goal condition transfers across a head step. *)
Lemma Head_ok_goal_transfer : forall G r r' g,
  Head G r r' ->
  (forall s, state_in r s -> ok_goal G 0 (st_cnt s) g) ->
  forall s', state_in r' s' -> ok_goal G 0 (st_cnt s') g.
Proof.
  intros G r r' g Hhead Hclosed s' Hsin.
  destruct (Head_state_counter G r r' Hhead s' Hsin) as [s [Hin Hle]].
  exact (ok_goal_mono G 0 0 (st_cnt s) (st_cnt s') g
           (Nat.le_refl 0) Hle (Hclosed s Hin)).
Qed.

Lemma Head_ok_tree : forall G t t',
  ok_env G -> ok_tree G t -> Head G t t' ->
  ok_tree G t'.
Proof.
  intros G t t' Hce Htt Hhead.
  destruct Hhead; simpl in *; try tauto.
  - destruct Htt as [[Ht1 Ht2] Hsub]. split; [exact I |].
    split.
    + exact (Unify_scoped (st_cnt s) t1 t2 (st_sub s) s' Ht1 Ht2 (proj1 Hsub) H).
    + exact (Unify_acyclic t1 t2 (st_sub s) s' (proj2 Hsub) H).
  - destruct Htt as [[Hg1 Hg2] Hsub]. split.
    + split; assumption.
    + split.
      * exists (st_cnt s). exact Hg2.
      * intros out Hin. apply state_in_tgoal_eq in Hin. subst. exact Hg2.
  - destruct Htt as [Hg Hsub]. split.
    + apply open_goal_ok.
      * rewrite length_map, length_seq, Nat.add_0_r.
        apply (ok_goal_mono G k k (st_cnt s) (st_cnt s + k) g); try lia.
        exact Hg.
      * exact (fresh_args_ok (st_cnt s) (st_cnt s) k (Nat.le_refl _)).
    + split.
      * apply scoped_sub_mono with (c := st_cnt s); [lia | exact (proj1 Hsub)].
      * exact (proj2 Hsub).
  - destruct Htt as [Hgoal Hsub].
    destruct (nth_error G r) as [[arity body]|] eqn:Hlook; simpl in Hgoal.
    + destruct Hgoal as [Hlen Hargs]. exact (conj Hlen (conj Hargs Hsub)).
    + contradiction.
  - rewrite H in Htt.
    destruct Htt as [Hlen [Hargs Hsub]]. split; [|exact Hsub].
    apply open_ok.
    + rewrite Hlen.
      apply (ok_goal_mono G n n 0 (st_cnt s) body); try lia.
      exact (Hce r n body H).
    + exact Hargs.
  - destruct Htt as [[_ Hsub] [_ Hcont]]. split; [|exact Hsub].
    exact (Hcont s (SI_tgoal gsucc s)).
  - destruct Htt as [[Hs Ht2] [Hex Hcont]]. split.
    + split; [exact Hs|]. split; [exact Hex|]. intros out Hin.
      apply state_in_tgoal_eq in Hin. subst.
      apply Hcont. apply SI_tdisjL_l. constructor.
    + split; [exact Ht2|]. split; [exact Hex|]. intros out Hin.
      apply Hcont. apply SI_tdisjL_r. exact Hin.
  - destruct Htt as [[Ht1 Hs] [Hex Hcont]]. split.
    + split; [exact Ht1|]. split; [exact Hex|]. intros out Hin.
      apply Hcont. apply SI_tdisjR_l. exact Hin.
    + split; [exact Hs|]. split; [exact Hex|]. intros out Hin.
      apply state_in_tgoal_eq in Hin. subst.
      apply Hcont. apply SI_tdisjR_r. constructor.
  - destruct Htt as [Ht [Hex Hcont]]. split; [exact Ht|].
    split; [exact Hex|].
    intros out Hin. apply Hcont. apply SI_tdelay. exact Hin.
Qed.

(* Any state in plug E r' is either in plug E r or directly in r'. *)
Lemma state_in_plug_or : forall E r r' s,
  state_in (plug E r') s ->
  state_in (plug E r) s \/ state_in r' s.
Proof.
  induction E; intros r r' s Hsin; simpl in *.
  - right. exact Hsin.
  - destruct (state_in_disjL_inv _ _ _ Hsin) as [Hl | Hr].
    + destruct (IHE r r' s Hl) as [H | H].
      * left. apply SI_tdisjL_l. exact H.
      * right. exact H.
    + left. apply SI_tdisjL_r. exact Hr.
  - destruct (state_in_disjR_inv _ _ _ Hsin) as [Hl | Hr].
    + left. apply SI_tdisjR_l. exact Hl.
    + destruct (IHE r r' s Hr) as [H | H].
      * left. apply SI_tdisjR_r. exact H.
      * right. exact H.
  - destruct (IHE r r' s (state_in_conj_inv _ _ _ Hsin)) as [H | H].
    + left. apply SI_tconj. exact H.
    + right. exact H.
Qed.

Lemma plug_ok_tree_head : forall G E r r',
  ok_env G ->
  ok_tree G (plug E r) ->
  Head G r r' ->
  ok_tree G r' ->
  ok_tree G (plug E r').
Proof.
  intros G E. induction E; intros r r' HcG Htt Hhead Htr'; simpl in *.
  - exact Htr'.
  - destruct Htt as [Htt1 Htt2].
    exact (conj (IHE r r' HcG Htt1 Hhead Htr') Htt2).
  - destruct Htt as [Htt1 Htt2].
    exact (conj Htt1 (IHE r r' HcG Htt2 Hhead Htr')).
  - destruct Htt as [Htt1 [Hex Hfg]]. repeat split.
    + exact (IHE r r' HcG Htt1 Hhead Htr').
    + exact Hex.
    + intros s Hsin.
      destruct (state_in_plug_or _ r r' s Hsin) as [Hin | Hin].
      * exact (Hfg s Hin).
      * apply (Head_ok_goal_transfer G r r' _ Hhead);
          [intros s0 Hsin0; exact (Hfg s0 (state_in_plug_into _ r s0 Hsin0)) | exact Hin].
Qed.

Lemma step_ok : forall G e e',
  ok_env G -> ok_expr G e -> G |= e --> e' -> ok_expr G e'.
Proof.
  intros G e e' HcG Hoke Hstep.
  destruct Hstep.
  - (* S_ctx: (ans, plug E r) --> (ans, plug E r') *)
    destruct Hoke as [Htt Hfa].
    split; simpl.
    + apply (plug_ok_tree_head G E r r' HcG Htt H).
      apply (Head_ok_tree G r r' HcG).
      * exact (plug_ok_tree_inv G E r Htt).
      * exact H.
    + exact Hfa.
  - (* S_delay: (ans, tdelay t) --> (ans, t) *)
    destruct Hoke as [Htt Hfa].
    split; simpl in *.
    + exact Htt.
    + exact Hfa.
  - (* S_promoteL: (ans, tdisjL (tgoal gsucc s) t) --> (ans ++ [s], t) *)
    destruct Hoke as [Htt Hfa].
    simpl in Htt.
    destruct Htt as [Hts Htt].
    split; simpl.
    + exact Htt.
    + rewrite Forall_app. split.
      * exact Hfa.
      * constructor; [exact (proj2 Hts) | constructor].
  - (* S_promoteR: (ans, tdisjR t (tgoal gsucc s)) --> (ans ++ [s], t) *)
    destruct Hoke as [Htt Hfa].
    simpl in Htt.
    destruct Htt as [Htt Hts].
    split; simpl.
    + exact Htt.
    + rewrite Forall_app. split.
      * exact Hfa.
      * constructor; [exact (proj2 Hts) | constructor].
Qed.

Theorem multi_ok : forall G e e',
  multi G e e' -> ok_env G -> ok_expr G e -> ok_expr G e'.
Proof.
  intros G e e' Hmulti HG Hok.
  induction Hmulti.
  - exact Hok.
  - apply IHHmulti. exact (step_ok G e1 e2 HG Hok H).
Qed.

(** A step in the scheduled child induces a step of its parent.  The
    promotion and delay cases use the corresponding scheduling rules. *)
Lemma step_conj_context : forall G ans t t' g,
  G |= (ans, t) --> t' ->
  exists e', G |= (ans, tconj t g) --> e'.
Proof.
  intros G ans t t' g Hstep. inversion Hstep; subst; clear Hstep.
  - eexists. eapply S_ctx with (E := cconj E g). eassumption.
  - eexists. apply S_ctx with (E := chole). apply H_delay_conj.
  - eexists. apply S_ctx with (E := chole). apply H_left_ans_conj.
  - eexists. apply S_ctx with (E := chole). apply H_right_ans_conj.
Qed.

Lemma step_disjL_context : forall G ans t t' u,
  G |= (ans, t) --> t' ->
  exists e', G |= (ans, tdisjL t u) --> e'.
Proof.
  intros G ans t t' u Hstep. inversion Hstep; subst; clear Hstep.
  - eexists. eapply S_ctx with (E := cdisjL E u). eassumption.
  - eexists. apply S_ctx with (E := chole). apply H_delay_left.
  - eexists. apply S_ctx with (E := chole). apply H_assoc_ll.
  - eexists. apply S_ctx with (E := chole). apply H_assoc_lr.
Qed.

Lemma step_disjR_context : forall G ans t t' u,
  G |= (ans, t) --> t' ->
  exists e', G |= (ans, tdisjR u t) --> e'.
Proof.
  intros G ans t t' u Hstep. inversion Hstep; subst; clear Hstep.
  - eexists. eapply S_ctx with (E := cdisjR u E). eassumption.
  - eexists. apply S_ctx with (E := chole). apply H_delay_right.
  - eexists. apply S_ctx with (E := chole). apply H_assoc_rl.
  - eexists. apply S_ctx with (E := chole). apply H_assoc_rr.
Qed.

Theorem tree_progress : forall G t ans,
  ok_tree G t ->
  is_value (ans, t) \/ exists e', G |= (ans, t) --> e'.
Proof.
  intros G t. induction t; intros ans Htree.
  - left. exact I.
  - destruct g.
    + left. exact I.
    + right. simpl in Htree. destruct Htree as [Hgoal Hsub].
      simpl in Hgoal. destruct Hgoal as [Ht1 Ht2].
      destruct (Unify_total (st_cnt s) (st_sub s) t t0
        (proj2 Hsub) (proj1 Hsub) Ht1 Ht2) as [[s'|] Hunify].
      * eexists. apply S_ctx with (E := chole). apply H_unify_ok. exact Hunify.
      * eexists. apply S_ctx with (E := chole). apply H_unify_fail. exact Hunify.
    + right. eexists. apply S_ctx with (E := chole). apply H_relcall.
    + right. eexists. apply S_ctx with (E := chole). apply H_disj.
    + right. eexists. apply S_ctx with (E := chole). apply H_conj.
    + right. eexists. apply S_ctx with (E := chole). apply H_fresh.
  - right. eexists. apply S_delay.
  - right. simpl in Htree.
    destruct (nth_error G n) as [[arity body]|] eqn:Hlook;
      [|contradiction].
    destruct Htree as [Hlen _].
    eexists. apply S_ctx with (E := chole).
    eapply H_proceed; eassumption.
  - right. simpl in Htree.
    destruct (IHt ans (proj1 Htree))
      as [Hvalue | [e' Hstep]].
    + destruct t; simpl in Hvalue; try contradiction.
      * eexists. apply S_ctx with (E := chole). apply H_prune_conj.
      * destruct g0; try contradiction.
        eexists. apply S_ctx with (E := chole). apply H_succ_conj.
    + exact (step_conj_context G ans t e' g Hstep).
  - right. simpl in Htree.
    destruct Htree as [Ht1 Ht2].
    destruct (IHt1 ans Ht1) as [Hvalue | [e' Hstep]].
    + destruct t1; simpl in Hvalue; try contradiction.
      * eexists. apply S_ctx with (E := chole). apply H_prune_left.
      * destruct g; try contradiction. eexists. apply S_promoteL.
    + exact (step_disjL_context G ans t1 e' t2 Hstep).
  - right. simpl in Htree.
    destruct Htree as [Ht1 Ht2].
    destruct (IHt2 ans Ht2) as [Hvalue | [e' Hstep]].
    + destruct t2; simpl in Hvalue; try contradiction.
      * eexists. apply S_ctx with (E := chole). apply H_prune_right.
      * destruct g; try contradiction. eexists. apply S_promoteR.
    + exact (step_disjR_context G ans t2 e' t1 Hstep).
Qed.

(** Tree progress classifies the selected child as reducible, terminal, or
    delayed. Each boundary shape enables the appropriate parent rewrite or
    root promotion/release. Total unification and valid proceed lookup exclude
    stuck atomic goals. This theorem guarantees a next step or a terminal
    expression, not eventual termination of search. *)
Theorem progress : forall G e,
  ok_expr G e -> is_value e \/ exists e', G |= e --> e'.
Proof.
  intros G [ans t] [Htree _].
  exact (tree_progress G t ans Htree).
Qed.
