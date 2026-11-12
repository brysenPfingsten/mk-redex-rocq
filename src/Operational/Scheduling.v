From Stdlib Require Import Arith.Wf_nat.
From MkRedex.Language Require Import Scoping ScopedUnification Goals Substitution Environments Trees.
From Stdlib Require Import List Lia Arith.
From MkRedex.Operational Require Import Reduction WellFormed Determinism Delay DelayTracking.
Import ListNotations.
Set Default Goal Selector "!".

From MkRedex.Language Require Import Solver.
Section WithSolver.
Context `{solver : Solver}.


(** Finite bursts and disjunction handoff.  A burst stops before a root
    delay release, so lifting it preserves the marked occurrence. *)

Lemma marked_burst_step_lift_left : forall G ans active ans' next m,
  G |= (ans, active) --> (ans', next) ->
  (forall t, active <> tdelay t) ->
  carried_multi G (ans, mark_disjL_right active m)
                  (ans', mark_disjL_right next m).
Proof.
  intros G ans active ans' next m Hstep Hnotdelay.
  inversion Hstep; subst; clear Hstep.
  - eapply carried_step.
    + eapply carry_waiting_left_head. eassumption.
    + constructor.
  - exfalso. eapply Hnotdelay. reflexivity.
  - eapply carried_step with
      (m' := (ans, mark_disjL_right (tgoal gsucc s)
                    (mark_disjL_right next m))).
    + apply carry_waiting_left_assoc_ll.
    + eapply carried_step.
      * apply carry_waiting_left_answer.
      * constructor.
  - eapply carried_step with
      (m' := (ans, mark_disjR_left (mark_disjL_right next m)
                    (tgoal gsucc s))).
    + apply carry_waiting_left_assoc_lr.
    + eapply carried_step.
      * apply carry_waiting_right_answer.
      * constructor.
Qed.

Lemma marked_burst_step_lift_right : forall G ans active ans' next m,
  G |= (ans, active) --> (ans', next) ->
  (forall t, active <> tdelay t) ->
  carried_multi G (ans, mark_disjR_left m active)
                  (ans', mark_disjR_left m next).
Proof.
  intros G ans active ans' next m Hstep Hnotdelay.
  inversion Hstep; subst; clear Hstep.
  - eapply carried_step.
    + eapply carry_waiting_right_head. eassumption.
    + constructor.
  - exfalso. eapply Hnotdelay. reflexivity.
  - eapply carried_step with
      (m' := (ans, mark_disjL_right (tgoal gsucc s)
                    (mark_disjR_left m next))).
    + apply carry_waiting_right_assoc_rl.
    + eapply carried_step.
      * apply carry_waiting_left_answer.
      * constructor.
  - eapply carried_step with
      (m' := (ans, mark_disjR_left (mark_disjR_left m next)
                    (tgoal gsucc s))).
    + apply carry_waiting_right_assoc_rr.
    + eapply carried_step.
      * apply carry_waiting_right_answer.
      * constructor.
Qed.

Lemma marked_burst_lift_left : forall G e e' m,
  burst_steps G e e' ->
  carried_multi G (fst e, mark_disjL_right (snd e) m)
                  (fst e', mark_disjL_right (snd e') m).
Proof.
  intros G e e' m Hburst. induction Hburst.
  - constructor.
  - destruct e1 as [ans active], e2 as [ans' next]. simpl in *.
    eapply carried_multi_trans.
    + eapply marked_burst_step_lift_left; eassumption.
    + exact IHHburst.
Qed.

Lemma marked_burst_lift_right : forall G e e' m,
  burst_steps G e e' ->
  carried_multi G (fst e, mark_disjR_left m (snd e))
                  (fst e', mark_disjR_left m (snd e')).
Proof.
  intros G e e' m Hburst. induction Hburst.
  - constructor.
  - destruct e1 as [ans active], e2 as [ans' next]. simpl in *.
    eapply carried_multi_trans.
    + eapply marked_burst_step_lift_right; eassumption.
    + exact IHHburst.
Qed.

(** Contexts, rotations, and the shell rank. *)

(** The other disjunct gets a turn after one finite burst, regardless of
    whether the marker is already active inside that disjunct. *)
Inductive selected_marker (m : marked_tree) : marked_tree -> Prop :=
  | selected_same : selected_marker m m
  | selected_left : forall other,
      selected_marker m (mark_disjL_left m other)
  | selected_right : forall other,
      selected_marker m (mark_disjR_right other m).

Lemma selected_marker_active : forall m selected,
  active_mark m -> selected_marker m selected -> active_mark selected.
Proof.
  intros m selected Hactive Hselected. inversion Hselected; subst;
    simpl; exact Hactive.
Qed.

(** This index ranks only the disjunction shell surrounding a fixed
    marked subtree.  Active frames contribute a zero bit; waiting
    frames contribute a one bit.  A handoff strictly decreases it. *)
Fixpoint scheduler_index (m : marked_tree) : nat :=
  match m with
  | mark_here _ => 0
  | mark_under_delay m' | mark_under_conj m' _ => scheduler_index m'
  | mark_disjL_left m' _ | mark_disjR_right _ m' =>
      2 * scheduler_index m'
  | mark_disjL_right _ m' | mark_disjR_left m' _ =>
      S (2 * scheduler_index m')
  end.

Fixpoint plug_active_mark (E : ctx) (m : marked_tree) : marked_tree :=
  match E with
  | chole => m
  | cdisjL E' other => mark_disjL_left (plug_active_mark E' m) other
  | cdisjR other E' => mark_disjR_right other (plug_active_mark E' m)
  | cconj E' g => mark_under_conj (plug_active_mark E' m) g
  end.

Fixpoint rotate_mark (E : ctx) (m : marked_tree) : marked_tree :=
  match E with
  | chole => m
  | cdisjL E' other => mark_disjR_left (rotate_mark E' m) other
  | cdisjR other E' => mark_disjL_right other (rotate_mark E' m)
  | cconj E' g => mark_under_conj (rotate_mark E' m) g
  end.

Lemma erase_plug_active_mark : forall E m,
  erase_mark (plug_active_mark E m) = plug E (erase_mark m).
Proof. induction E; intros m; simpl; congruence. Qed.

Lemma lift_head_carry : forall G ans E m m' K r r',
  marked_carry G (ans, m) (ans, m') ->
  erase_mark m = plug K r -> erase_mark m' = plug K r' ->
  Head G r r' ->
  marked_carry G (ans, plug_active_mark E m)
                 (ans, plug_active_mark E m').
Proof.
  intros G ans E. induction E; intros m m' K r r' Hcarry Hsrc Hdst Hhead;
    simpl; [exact Hcarry |..].
  - eapply carry_disjL_active_head with (E := compose_ctx E K);
      [eapply IHE; eassumption |..].
    + rewrite erase_plug_active_mark, plug_compose, Hsrc. reflexivity.
    + rewrite erase_plug_active_mark, plug_compose, Hdst. reflexivity.
    + exact Hhead.
  - eapply carry_disjR_active_head with (E := compose_ctx E K);
      [eapply IHE; eassumption |..].
    + rewrite erase_plug_active_mark, plug_compose, Hsrc. reflexivity.
    + rewrite erase_plug_active_mark, plug_compose, Hdst. reflexivity.
    + exact Hhead.
  - eapply carry_conj_head with (E := compose_ctx E K);
      [eapply IHE; eassumption |..].
    + rewrite erase_plug_active_mark, plug_compose, Hsrc. reflexivity.
    + rewrite erase_plug_active_mark, plug_compose, Hdst. reflexivity.
    + exact Hhead.
Qed.

Inductive head_carry_multi (G : env) (ans : list state) :
    marked_tree -> marked_tree -> Prop :=
  | head_carry_refl : forall m, head_carry_multi G ans m m
  | head_carry_step : forall m m' m'' E r r',
      marked_carry G (ans, m) (ans, m') ->
      erase_mark m = plug E r -> erase_mark m' = plug E r' ->
      Head G r r' -> head_carry_multi G ans m' m'' ->
      head_carry_multi G ans m m''.

Lemma head_carry_to_carried : forall G ans m m',
  head_carry_multi G ans m m' ->
  carried_multi G (ans, m) (ans, m').
Proof.
  intros G ans m m' Htrace. induction Htrace.
  - constructor.
  - eapply carried_step; eassumption.
Qed.

Lemma head_carry_trans : forall G ans m m' m'',
  head_carry_multi G ans m m' ->
  head_carry_multi G ans m' m'' ->
  head_carry_multi G ans m m''.
Proof.
  intros G ans m m' m'' Hfirst. revert m''.
  induction Hfirst; intros target Hsecond; [exact Hsecond |].
  eapply head_carry_step; try eassumption.
  apply IHHfirst. exact Hsecond.
Qed.

Lemma head_carry_lift : forall G ans outer m m',
  head_carry_multi G ans m m' ->
  head_carry_multi G ans (plug_active_mark outer m)
                         (plug_active_mark outer m').
Proof.
  intros G ans outer m m' Htrace. induction Htrace.
  - constructor.
  - eapply head_carry_step with
      (E := compose_ctx outer E) (r := r) (r' := r').
    + eapply lift_head_carry; eassumption.
    + rewrite erase_plug_active_mark, plug_compose, H0. reflexivity.
    + rewrite erase_plug_active_mark, plug_compose, H1. reflexivity.
    + exact H2.
    + exact IHHtrace.
Qed.

Lemma bubble_enclosing_delay : forall G ans E m,
  head_carry_multi G ans (plug_active_mark E (mark_under_delay m))
    (mark_under_delay (rotate_mark E m)).
Proof.
  intros G ans E. induction E; intros m; simpl.
  - constructor.
  - eapply head_carry_trans.
    + apply head_carry_lift with (outer := cdisjL chole t).
      apply IHE.
    + eapply head_carry_step with (E := chole).
      * apply carry_inactive_disjL_delay.
      * reflexivity.
      * reflexivity.
      * apply H_delay_left.
      * constructor.
  - eapply head_carry_trans.
    + apply head_carry_lift with (outer := cdisjR t chole).
      apply IHE.
    + eapply head_carry_step with (E := chole).
      * apply carry_inactive_disjR_delay.
      * reflexivity.
      * reflexivity.
      * apply H_delay_right.
      * constructor.
  - eapply head_carry_trans.
    + apply head_carry_lift with (outer := cconj chole g).
      apply IHE.
    + eapply head_carry_step with (E := chole).
      * apply carry_inactive_conj_delay.
      * reflexivity.
      * reflexivity.
      * apply H_delay_conj.
      * constructor.
Qed.

Lemma release_enclosing_delay_in_context : forall G ans E m,
  carried_multi G (ans, plug_active_mark E (mark_under_delay m))
                  (ans, rotate_mark E m).
Proof.
  intros G ans E m.
  eapply carried_multi_trans.
  - apply head_carry_to_carried. apply bubble_enclosing_delay.
  - eapply carried_step; [apply carry_outer_delay | constructor].
Qed.

Lemma contextual_waiting_delay_left : forall G ans E body m,
  carried_multi G
    (ans, plug_active_mark E (mark_disjL_right (tdelay body) m))
    (ans, rotate_mark E (mark_disjR_right body m)).
Proof.
  intros G ans E body m.
  eapply carried_multi_trans.
  - eapply carried_step; [|constructor].
    eapply lift_head_carry with (K := chole).
    + apply carry_waiting_left_delay.
    + reflexivity.
    + reflexivity.
    + apply H_delay_left.
  - apply release_enclosing_delay_in_context.
Qed.

Lemma contextual_waiting_delay_right : forall G ans E body m,
  carried_multi G
    (ans, plug_active_mark E (mark_disjR_left m (tdelay body)))
    (ans, rotate_mark E (mark_disjL_left m body)).
Proof.
  intros G ans E body m.
  eapply carried_multi_trans.
  - eapply carried_step; [|constructor].
    eapply lift_head_carry with (K := chole).
    + apply carry_waiting_right_delay.
    + reflexivity.
    + reflexivity.
    + apply H_delay_right.
  - apply release_enclosing_delay_in_context.
Qed.

Lemma contextual_waiting_fail_left : forall G ans E m,
  marked_carry G
    (ans, plug_active_mark E (mark_disjL_right tfail m))
    (ans, plug_active_mark E m).
Proof.
  intros G ans E m. eapply lift_head_carry with (K := chole).
  - apply carry_waiting_left_fail.
  - reflexivity.
  - reflexivity.
  - apply H_prune_left.
Qed.

Lemma contextual_waiting_fail_right : forall G ans E m,
  marked_carry G
    (ans, plug_active_mark E (mark_disjR_left m tfail))
    (ans, plug_active_mark E m).
Proof.
  intros G ans E m. eapply lift_head_carry with (K := chole).
  - apply carry_waiting_right_fail.
  - reflexivity.
  - reflexivity.
  - apply H_prune_right.
Qed.

Fixpoint disj_only_ctx (E : ctx) : Prop :=
  match E with
  | chole => True
  | cdisjL E' _ | cdisjR _ E' => disj_only_ctx E'
  | cconj _ _ => False
  end.

Lemma answer_bubbles_left : forall G ans E s m,
  disj_only_ctx E ->
  head_carry_multi G ans
    (plug_active_mark E (mark_disjL_right (tgoal gsucc s) m))
    (mark_disjL_right (tgoal gsucc s) (plug_active_mark E m)).
Proof.
  intros G ans E. induction E; intros s m Hctx; simpl in *.
  - constructor.
  - eapply head_carry_trans.
    + apply head_carry_lift with (outer := cdisjL chole t).
      apply IHE. exact Hctx.
    + eapply head_carry_step with (E := chole).
      * apply carry_active_outer_ll.
      * reflexivity.
      * reflexivity.
      * apply H_assoc_ll.
      * constructor.
  - eapply head_carry_trans.
    + apply head_carry_lift with (outer := cdisjR t chole).
      apply IHE. exact Hctx.
    + eapply head_carry_step with (E := chole).
      * apply carry_active_outer_rl.
      * reflexivity.
      * reflexivity.
      * apply H_assoc_rl.
      * constructor.
  - contradiction.
Qed.

Lemma answer_bubbles_right : forall G ans E s m,
  disj_only_ctx E ->
  head_carry_multi G ans
    (plug_active_mark E (mark_disjR_left m (tgoal gsucc s)))
    (mark_disjR_left (plug_active_mark E m) (tgoal gsucc s)).
Proof.
  intros G ans E. induction E; intros s m Hctx; simpl in *.
  - constructor.
  - eapply head_carry_trans.
    + apply head_carry_lift with (outer := cdisjL chole t).
      apply IHE. exact Hctx.
    + eapply head_carry_step with (E := chole).
      * apply carry_active_outer_lr.
      * reflexivity.
      * reflexivity.
      * apply H_assoc_lr.
      * constructor.
  - eapply head_carry_trans.
    + apply head_carry_lift with (outer := cdisjR t chole).
      apply IHE. exact Hctx.
    + eapply head_carry_step with (E := chole).
      * apply carry_active_outer_rr.
      * reflexivity.
      * reflexivity.
      * apply H_assoc_rr.
      * constructor.
  - contradiction.
Qed.

Lemma contextual_waiting_answer_left : forall G ans E s m,
  disj_only_ctx E ->
  carried_multi G
    (ans, plug_active_mark E (mark_disjL_right (tgoal gsucc s) m))
    (ans ++ [s], plug_active_mark E m).
Proof.
  intros G ans E s m Hctx.
  eapply carried_multi_trans.
  - apply head_carry_to_carried. apply answer_bubbles_left. exact Hctx.
  - eapply carried_step; [apply carry_waiting_left_answer | constructor].
Qed.

Lemma contextual_waiting_answer_right : forall G ans E s m,
  disj_only_ctx E ->
  carried_multi G
    (ans, plug_active_mark E (mark_disjR_left m (tgoal gsucc s)))
    (ans ++ [s], plug_active_mark E m).
Proof.
  intros G ans E s m Hctx.
  eapply carried_multi_trans.
  - apply head_carry_to_carried. apply answer_bubbles_right. exact Hctx.
  - eapply carried_step; [apply carry_waiting_right_answer | constructor].
Qed.

Lemma contextual_burst_step_left : forall G ans active ans' next E m,
  G |= (ans, active) --> (ans', next) ->
  (forall body, active <> tdelay body) ->
  disj_only_ctx E ->
  carried_multi G
    (ans, plug_active_mark E (mark_disjL_right active m))
    (ans', plug_active_mark E (mark_disjL_right next m)).
Proof.
  intros G ans active ans' next E m Hstep Hnotdelay Hctx.
  inversion Hstep; subst; clear Hstep.
  - eapply carried_step; [|constructor].
    eapply lift_head_carry with (K := cdisjL E0 (erase_mark m)).
    + eapply carry_waiting_left_head. eassumption.
    + reflexivity.
    + reflexivity.
    + eassumption.
  - exfalso. eapply Hnotdelay. reflexivity.
  - eapply carried_multi_trans.
    + eapply carried_step; [|constructor].
      eapply lift_head_carry with (K := chole).
      * apply carry_waiting_left_assoc_ll.
      * reflexivity.
      * reflexivity.
      * apply H_assoc_ll.
    + apply contextual_waiting_answer_left. exact Hctx.
  - eapply carried_multi_trans.
    + eapply carried_step; [|constructor].
      eapply lift_head_carry with (K := chole).
      * apply carry_waiting_left_assoc_lr.
      * reflexivity.
      * reflexivity.
      * apply H_assoc_lr.
    + apply contextual_waiting_answer_right. exact Hctx.
Qed.

Lemma contextual_burst_step_right : forall G ans active ans' next E m,
  G |= (ans, active) --> (ans', next) ->
  (forall body, active <> tdelay body) ->
  disj_only_ctx E ->
  carried_multi G
    (ans, plug_active_mark E (mark_disjR_left m active))
    (ans', plug_active_mark E (mark_disjR_left m next)).
Proof.
  intros G ans active ans' next E m Hstep Hnotdelay Hctx.
  inversion Hstep; subst; clear Hstep.
  - eapply carried_step; [|constructor].
    eapply lift_head_carry with (K := cdisjR (erase_mark m) E0).
    + eapply carry_waiting_right_head. eassumption.
    + reflexivity.
    + reflexivity.
    + eassumption.
  - exfalso. eapply Hnotdelay. reflexivity.
  - eapply carried_multi_trans.
    + eapply carried_step; [|constructor].
      eapply lift_head_carry with (K := chole).
      * apply carry_waiting_right_assoc_rl.
      * reflexivity.
      * reflexivity.
      * apply H_assoc_rl.
    + apply contextual_waiting_answer_left. exact Hctx.
  - eapply carried_multi_trans.
    + eapply carried_step; [|constructor].
      eapply lift_head_carry with (K := chole).
      * apply carry_waiting_right_assoc_rr.
      * reflexivity.
      * reflexivity.
      * apply H_assoc_rr.
    + apply contextual_waiting_answer_right. exact Hctx.
Qed.

Lemma contextual_burst_left : forall G e e' E m,
  burst_steps G e e' -> disj_only_ctx E ->
  carried_multi G
    (fst e, plug_active_mark E (mark_disjL_right (snd e) m))
    (fst e', plug_active_mark E (mark_disjL_right (snd e') m)).
Proof.
  intros G e e' E m Hburst Hctx. induction Hburst.
  - constructor.
  - destruct e1 as [ans active], e2 as [ans' next]. simpl in *.
    eapply carried_multi_trans.
    + eapply contextual_burst_step_left; eassumption.
    + exact IHHburst.
Qed.

Lemma contextual_burst_right : forall G e e' E m,
  burst_steps G e e' -> disj_only_ctx E ->
  carried_multi G
    (fst e, plug_active_mark E (mark_disjR_left m (snd e)))
    (fst e', plug_active_mark E (mark_disjR_left m (snd e'))).
Proof.
  intros G e e' E m Hburst Hctx. induction Hburst.
  - constructor.
  - destruct e1 as [ans active], e2 as [ans' next]. simpl in *.
    eapply carried_multi_trans.
    + eapply contextual_burst_step_right; eassumption.
    + exact IHHburst.
Qed.

Theorem contextual_disj_handoff_left : forall G ans E active m,
  closed_env G -> ok_expr G (ans, active) -> disj_only_ctx E ->
  exists target,
    carried_multi G
      (ans, plug_active_mark E (mark_disjL_right active m)) target /\
    (snd target = plug_active_mark E m \/
     exists body,
       snd target = rotate_mark E (mark_disjR_right body m)).
Proof.
  intros G ans E active m Henv Hok Hctx.
  destruct (finite_burst_marked G (ans, active) Henv Hok)
    as [[out yielded] [Hburst Hend]].
  pose proof (contextual_burst_left G (ans, active)
    (out, yielded) E m Hburst Hctx) as Hlift. simpl in Hlift.
  destruct Hend as [Hvalue | [body Hdelay]].
  - destruct yielded; simpl in Hvalue; try contradiction.
    + exists (out, plug_active_mark E m). split; [|left; reflexivity].
      eapply carried_multi_trans; [exact Hlift |].
      eapply carried_step; [apply contextual_waiting_fail_left | constructor].
    + destruct g; try contradiction.
      exists (out ++ [s], plug_active_mark E m).
      split; [|left; reflexivity].
      eapply carried_multi_trans; [exact Hlift |].
      apply contextual_waiting_answer_left. exact Hctx.
  - simpl in Hdelay. subst yielded.
    exists (out, rotate_mark E (mark_disjR_right body m)).
    split; [|right; eexists; reflexivity].
    eapply carried_multi_trans; [exact Hlift |].
    apply contextual_waiting_delay_left.
Qed.

Theorem contextual_disj_handoff_right : forall G ans E active m,
  closed_env G -> ok_expr G (ans, active) -> disj_only_ctx E ->
  exists target,
    carried_multi G
      (ans, plug_active_mark E (mark_disjR_left m active)) target /\
    (snd target = plug_active_mark E m \/
     exists body,
       snd target = rotate_mark E (mark_disjL_left m body)).
Proof.
  intros G ans E active m Henv Hok Hctx.
  destruct (finite_burst_marked G (ans, active) Henv Hok)
    as [[out yielded] [Hburst Hend]].
  pose proof (contextual_burst_right G (ans, active)
    (out, yielded) E m Hburst Hctx) as Hlift. simpl in Hlift.
  destruct Hend as [Hvalue | [body Hdelay]].
  - destruct yielded; simpl in Hvalue; try contradiction.
    + exists (out, plug_active_mark E m). split; [|left; reflexivity].
      eapply carried_multi_trans; [exact Hlift |].
      eapply carried_step; [apply contextual_waiting_fail_right | constructor].
    + destruct g; try contradiction.
      exists (out ++ [s], plug_active_mark E m).
      split; [|left; reflexivity].
      eapply carried_multi_trans; [exact Hlift |].
      apply contextual_waiting_answer_right. exact Hctx.
  - simpl in Hdelay. subst yielded.
    exists (out, rotate_mark E (mark_disjL_left m body)).
    split; [|right; eexists; reflexivity].
    eapply carried_multi_trans; [exact Hlift |].
    apply contextual_waiting_delay_right.
Qed.

Lemma contextual_handoff_index_left : forall E active m,
  scheduler_index (plug_active_mark E (mark_disjL_right active m)) =
  S (scheduler_index (rotate_mark E (mark_disjR_right active m))).
Proof. induction E; intros active m; simpl; try lia; rewrite IHE; lia. Qed.

Lemma contextual_handoff_index_right : forall E active m,
  scheduler_index (plug_active_mark E (mark_disjR_left m active)) =
  S (scheduler_index (rotate_mark E (mark_disjL_left m active))).
Proof. induction E; intros active m; simpl; try lia; rewrite IHE; lia. Qed.

Lemma scheduler_index_plug_active_strict : forall E m n,
  scheduler_index m < scheduler_index n ->
  scheduler_index (plug_active_mark E m) <
  scheduler_index (plug_active_mark E n).
Proof.
  induction E; intros m n Hless; simpl; auto; specialize (IHE m n Hless); lia.
Qed.

Lemma scheduler_index_plug_active_congr : forall E m n,
  scheduler_index m = scheduler_index n ->
  scheduler_index (plug_active_mark E m) =
  scheduler_index (plug_active_mark E n).
Proof.
  induction E; intros m n Heq; simpl; auto;
    rewrite IHE by exact Heq; reflexivity.
Qed.

Lemma rotate_mark_index_congr : forall E m n,
  scheduler_index m = scheduler_index n ->
  scheduler_index (rotate_mark E m) = scheduler_index (rotate_mark E n).
Proof.
  induction E; intros m n Hindex; simpl; auto;
    rewrite IHE by exact Hindex; reflexivity.
Qed.

Lemma contextual_waiting_delay_rank_left : forall E body m,
  scheduler_index (rotate_mark E (mark_disjR_right body m)) <
    scheduler_index (plug_active_mark E (mark_disjL_right (tdelay body) m)).
Proof.
  intros E body m. rewrite contextual_handoff_index_left.
  assert (Hsame : scheduler_index (rotate_mark E (mark_disjR_right body m)) =
    scheduler_index (rotate_mark E (mark_disjR_right (tdelay body) m)))
    by (apply rotate_mark_index_congr; reflexivity).
  lia.
Qed.

Lemma contextual_waiting_delay_rank_right : forall E body m,
  scheduler_index (rotate_mark E (mark_disjL_left m body)) <
    scheduler_index (plug_active_mark E (mark_disjR_left m (tdelay body))).
Proof.
  intros E body m. rewrite contextual_handoff_index_right.
  assert (Hsame : scheduler_index (rotate_mark E (mark_disjL_left m body)) =
    scheduler_index (rotate_mark E (mark_disjL_left m (tdelay body))))
    by (apply rotate_mark_index_congr; reflexivity).
  lia.
Qed.

Lemma plug_active_compose : forall outer inner m,
  plug_active_mark (compose_ctx outer inner) m =
  plug_active_mark outer (plug_active_mark inner m).
Proof. induction outer; intros inner m; simpl; congruence. Qed.

Lemma disj_only_compose : forall outer inner,
  disj_only_ctx outer -> disj_only_ctx inner ->
  disj_only_ctx (compose_ctx outer inner).
Proof.
  induction outer; intros inner Houter Hinner; simpl in *;
    auto; contradiction.
Qed.

Lemma ok_expr_disjL_right : forall G ans active waiting,
  ok_expr G (ans, tdisjL active waiting) -> ok_expr G (ans, waiting).
Proof.
  intros G ans active waiting [[c Hclosed] [Htight [Hans Hacyclic]]].
  simpl in Hclosed, Htight, Hacyclic.
  repeat split.
  - exists c. exact (proj2 Hclosed).
  - exact (proj2 Htight).
  - exact Hans.
  - exact (proj2 Hacyclic).
Qed.

Lemma ok_expr_disjR_left : forall G ans waiting active,
  ok_expr G (ans, tdisjR waiting active) -> ok_expr G (ans, waiting).
Proof.
  intros G ans waiting active [[c Hclosed] [Htight [Hans Hacyclic]]].
  simpl in Hclosed, Htight, Hacyclic.
  repeat split.
  - exists c. exact (proj1 Hclosed).
  - exact (proj1 Htight).
  - exact Hans.
  - exact (proj1 Hacyclic).
Qed.

Lemma ok_expr_disj_context : forall G ans E t,
  disj_only_ctx E ->
  ok_expr G (ans, plug E t) -> ok_expr G (ans, t).
Proof.
  intros G ans E. induction E; intros t0 Hctx Hok; simpl in *.
  - exact Hok.
  - apply IHE; [exact Hctx |].
    eapply ok_expr_disjL_left; eassumption.
  - apply IHE; [exact Hctx |].
    eapply ok_expr_disjR_right; eassumption.
  - contradiction.
Qed.

Theorem immediate_waiting_mark_handoff_left : forall G ans active m,
  closed_env G ->
  ok_expr G (ans, tdisjL active (erase_mark m)) ->
  exists target,
    carried_multi G (ans, mark_disjL_right active m) target /\
    selected_marker m (snd target).
Proof.
  intros G ans active m Henv Hok.
  destruct (finite_burst_marked G (ans, active) Henv
    (ok_expr_disjL_left G ans active (erase_mark m) Hok))
    as [[out yielded] [Hburst Hend]].
  pose proof (marked_burst_lift_left G (ans, active)
    (out, yielded) m Hburst) as Hlift. simpl in Hlift.
  destruct Hend as [Hvalue | [body Hdelay]].
  - destruct yielded; simpl in Hvalue; try contradiction.
    + exists (out, m). split; [|constructor].
      eapply carried_multi_trans; [exact Hlift |].
      eapply carried_step; [apply carry_waiting_left_fail | constructor].
    + destruct g; try contradiction.
      exists (out ++ [s], m). split; [|constructor].
      eapply carried_multi_trans; [exact Hlift |].
      eapply carried_step; [apply carry_waiting_left_answer | constructor].
  - simpl in Hdelay. subst yielded.
    exists (out, mark_disjR_right body m). split; [|constructor].
    eapply carried_multi_trans; [exact Hlift |].
    eapply carried_step with
      (m' := (out, mark_under_delay (mark_disjR_right body m))).
    + apply carry_waiting_left_delay.
    + eapply carried_step; [apply carry_outer_delay | constructor].
Qed.

Theorem immediate_waiting_mark_handoff_right : forall G ans active m,
  closed_env G ->
  ok_expr G (ans, tdisjR (erase_mark m) active) ->
  exists target,
    carried_multi G (ans, mark_disjR_left m active) target /\
    selected_marker m (snd target).
Proof.
  intros G ans active m Henv Hok.
  destruct (finite_burst_marked G (ans, active) Henv
    (ok_expr_disjR_right G ans (erase_mark m) active Hok))
    as [[out yielded] [Hburst Hend]].
  pose proof (marked_burst_lift_right G (ans, active)
    (out, yielded) m Hburst) as Hlift. simpl in Hlift.
  destruct Hend as [Hvalue | [body Hdelay]].
  - destruct yielded; simpl in Hvalue; try contradiction.
    + exists (out, m). split; [|constructor].
      eapply carried_multi_trans; [exact Hlift |].
      eapply carried_step; [apply carry_waiting_right_fail | constructor].
    + destruct g; try contradiction.
      exists (out ++ [s], m). split; [|constructor].
      eapply carried_multi_trans; [exact Hlift |].
      eapply carried_step; [apply carry_waiting_right_answer | constructor].
  - simpl in Hdelay. subst yielded.
    exists (out, mark_disjL_left m body). split; [|constructor].
    eapply carried_multi_trans; [exact Hlift |].
    eapply carried_step with
      (m' := (out, mark_under_delay (mark_disjL_left m body))).
    + apply carry_waiting_right_delay.
    + eapply carried_step; [apply carry_outer_delay | constructor].
Qed.

Corollary immediate_waiting_mark_selected_left : forall G ans active m,
  closed_env G ->
  ok_expr G (ans, tdisjL active (erase_mark m)) ->
  active_mark m ->
  exists target,
    carried_multi G (ans, mark_disjL_right active m) target /\
    active_mark (snd target).
Proof.
  intros G ans active m Henv Hok Hactive.
  destruct (immediate_waiting_mark_handoff_left G ans active m Henv Hok)
    as [target [Hrun Hselected]].
  exists target. split; [exact Hrun |].
  eapply selected_marker_active; eassumption.
Qed.

Corollary immediate_waiting_mark_selected_right : forall G ans active m,
  closed_env G ->
  ok_expr G (ans, tdisjR (erase_mark m) active) ->
  active_mark m ->
  exists target,
    carried_multi G (ans, mark_disjR_left m active) target /\
    active_mark (snd target).
Proof.
  intros G ans active m Henv Hok Hactive.
  destruct (immediate_waiting_mark_handoff_right G ans active m Henv Hok)
    as [target [Hrun Hselected]].
  exists target. split; [exact Hrun |].
  eapply selected_marker_active; eassumption.
Qed.

Corollary immediate_waiting_mark_finishes_left : forall G ans active m,
  closed_env G ->
  ok_expr G (ans, tdisjL active (erase_mark m)) ->
  active_mark m ->
  exists e', tracked_finish G (ans, mark_disjL_right active m) e'.
Proof.
  intros G ans active m Henv Hok Hactive.
  destruct (immediate_waiting_mark_selected_left G ans active m
    Henv Hok Hactive) as [[out marked] [Hrun Hselected]].
  destruct (active_mark_tracked_finish G out marked Hselected)
    as [e' Hfinish].
  exists e'. eapply carried_multi_finish; eassumption.
Qed.

Corollary immediate_waiting_mark_finishes_right : forall G ans active m,
  closed_env G ->
  ok_expr G (ans, tdisjR (erase_mark m) active) ->
  active_mark m ->
  exists e', tracked_finish G (ans, mark_disjR_left m active) e'.
Proof.
  intros G ans active m Henv Hok Hactive.
  destruct (immediate_waiting_mark_selected_right G ans active m
    Henv Hok Hactive) as [[out marked] [Hrun Hselected]].
  destruct (active_mark_tracked_finish G out marked Hselected)
    as [e' Hfinish].
  exists e'. eapply carried_multi_finish; eassumption.
Qed.

(** Focusing a finite shell of disjunctions. *)

(** A shell records scheduler disjunctions outside an arbitrary marked
    subtree.  Focusing this shell must not inspect the subtree: in
    particular it can contain a conjunction. *)
Inductive disj_shell (inner : marked_tree) : marked_tree -> Prop :=
  | shell_here : disj_shell inner inner
  | shell_active_left : forall m other,
      disj_shell inner m -> disj_shell inner (mark_disjL_left m other)
  | shell_waiting_left : forall active m,
      disj_shell inner m -> disj_shell inner (mark_disjL_right active m)
  | shell_waiting_right : forall m active,
      disj_shell inner m -> disj_shell inner (mark_disjR_left m active)
  | shell_active_right : forall other m,
      disj_shell inner m -> disj_shell inner (mark_disjR_right other m).

Lemma disj_shell_plug_active : forall inner m E,
  disj_shell inner m -> disj_only_ctx E ->
  disj_shell inner (plug_active_mark E m).
Proof.
  intros inner m E Hshell Hctx. induction E; simpl in *;
    try constructor; auto; contradiction.
Qed.

Lemma disj_shell_rotate : forall inner m E,
  disj_shell inner m -> disj_only_ctx E ->
  disj_shell inner (rotate_mark E m).
Proof.
  intros inner m E Hshell Hctx. induction E; simpl in *;
    try constructor; auto; contradiction.
Qed.

Lemma disj_shell_macro : forall G ans inner m E,
  disj_shell inner m -> disj_only_ctx E ->
  closed_env G ->
  ok_expr G (erase_marked (ans, plug_active_mark E m)) ->
  (exists K,
      disj_only_ctx K /\
      plug_active_mark E m = plug_active_mark K inner) \/
  exists target,
    carried_multi G (ans, plug_active_mark E m) target /\
    disj_shell inner (snd target) /\
    scheduler_index (snd target) <
      scheduler_index (plug_active_mark E m).
Proof.
  intros G ans inner m E Hshell. revert E.
  induction Hshell; intros E Hctx Henv Hok.
  - left. exists E. split; [exact Hctx | reflexivity].
  - set (E' := compose_ctx E (cdisjL chole other)).
    assert (Heq : plug_active_mark E' m =
      plug_active_mark E (mark_disjL_left m other)).
    { unfold E'. rewrite plug_active_compose. reflexivity. }
    rewrite <- Heq in Hok |- *.
    apply IHHshell; try assumption.
    unfold E'. apply disj_only_compose; simpl; auto.
  - right.
    assert (Hactive : ok_expr G (ans, active)).
    { unfold erase_marked in Hok. simpl in Hok.
      rewrite erase_plug_active_mark in Hok. simpl in Hok.
      apply (ok_expr_disjL_left G ans active (erase_mark m)).
      eapply ok_expr_disj_context; eassumption. }
    destruct (contextual_disj_handoff_left G ans E active m
      Henv Hactive Hctx) as [target [Hrun [Hsame | [body Hrot]]]].
    + exists target. split; [exact Hrun |].
      split.
      * rewrite Hsame. eapply disj_shell_plug_active; eassumption.
      * rewrite Hsame. apply scheduler_index_plug_active_strict.
        simpl. lia.
    + exists target. split; [exact Hrun |].
      split.
      * rewrite Hrot. apply disj_shell_rotate; [|exact Hctx].
        constructor. exact Hshell.
      * rewrite Hrot.
        pose proof (contextual_waiting_delay_rank_left E body m)
          as Hless.
        assert (Heq : scheduler_index
          (plug_active_mark E (mark_disjL_right active m)) =
          scheduler_index
            (plug_active_mark E (mark_disjL_right (tdelay body) m)))
          by (apply scheduler_index_plug_active_congr; reflexivity).
        lia.
  - right.
    assert (Hactive : ok_expr G (ans, active)).
    { unfold erase_marked in Hok. simpl in Hok.
      rewrite erase_plug_active_mark in Hok. simpl in Hok.
      apply (ok_expr_disjR_right G ans (erase_mark m) active).
      eapply ok_expr_disj_context; eassumption. }
    destruct (contextual_disj_handoff_right G ans E active m
      Henv Hactive Hctx) as [target [Hrun [Hsame | [body Hrot]]]].
    + exists target. split; [exact Hrun |].
      split.
      * rewrite Hsame. eapply disj_shell_plug_active; eassumption.
      * rewrite Hsame. apply scheduler_index_plug_active_strict.
        simpl. lia.
    + exists target. split; [exact Hrun |].
      split.
      * rewrite Hrot. apply disj_shell_rotate; [|exact Hctx].
        constructor. exact Hshell.
      * rewrite Hrot.
        pose proof (contextual_waiting_delay_rank_right E body m)
          as Hless.
        assert (Heq : scheduler_index
          (plug_active_mark E (mark_disjR_left m active)) =
          scheduler_index
            (plug_active_mark E (mark_disjR_left m (tdelay body))))
          by (apply scheduler_index_plug_active_congr; reflexivity).
        lia.
  - set (E' := compose_ctx E (cdisjR other chole)).
    assert (Heq : plug_active_mark E' m =
      plug_active_mark E (mark_disjR_right other m)).
    { unfold E'. rewrite plug_active_compose. reflexivity. }
    rewrite <- Heq in Hok |- *.
    apply IHHshell; try assumption.
    unfold E'. apply disj_only_compose; simpl; auto.
Qed.

Theorem disj_shell_eventually_focused : forall G ans inner m,
  closed_env G -> ok_expr G (erase_marked (ans, m)) ->
  disj_shell inner m ->
  exists out K,
    carried_multi G (ans, m) (out, plug_active_mark K inner) /\
    disj_only_ctx K.
Proof.
  intros G ans inner m Henv Hok Hshell.
  set (index := fun p : marked_expr => scheduler_index (snd p)).
  assert (Hmain : forall n current,
    index current = n ->
    ok_expr G (erase_marked current) ->
    disj_shell inner (snd current) ->
    exists out K,
      carried_multi G current (out, plug_active_mark K inner) /\
      disj_only_ctx K).
  { apply (well_founded_induction lt_wf
      (fun n => forall current,
        index current = n ->
        ok_expr G (erase_marked current) ->
        disj_shell inner (snd current) ->
        exists out K,
          carried_multi G current (out, plug_active_mark K inner) /\
          disj_only_ctx K)).
    intros n IH [current_ans current] Hrank Hcurrent Hshell_current.
    destruct (disj_shell_macro G current_ans inner current chole
      Hshell_current I Henv Hcurrent)
      as [[K [Hctx Hshape]] |
          [next [Hrun [Hnext Hless]]]].
    - simpl in Hshape.
      exists current_ans, K. split; [|exact Hctx].
      rewrite Hshape. constructor.
    - assert (Hlower : index next < n).
      { unfold index in *. simpl in *. lia. }
      destruct (IH (index next) Hlower next eq_refl
        (carried_multi_ok G (current_ans, current) next
          Henv Hcurrent Hrun) Hnext)
        as [out [K [Htail Hctx]]].
      exists out, K. split; [|exact Hctx].
      eapply carried_multi_trans; eassumption.
  }
  exact (Hmain (index (ans, m)) (ans, m) eq_refl Hok Hshell).
Qed.

End WithSolver.
