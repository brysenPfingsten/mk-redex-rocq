From Stdlib Require Import Arith.Wf_nat.
From MkRedex.Language Require Import WellFormed Scoping ScopedUnification Goals Substitution Environments Trees.
From Stdlib Require Import List Lia Arith.
From MkRedex.Operational Require Import Reduction WellFormed Determinism Delay.
Import ListNotations.
Set Default Goal Selector "!".


(** Marked occurrences and the active path. *)

(** A proof-only tree with exactly one distinguished delay occurrence.
    Erasing the distinction gives the existing runtime tree.  The marker
    avoids confusing two syntactically equal delays in different branches. *)
Inductive marked_tree : Type :=
  | mark_here : tree -> marked_tree
  | mark_under_delay : marked_tree -> marked_tree
  | mark_under_conj : marked_tree -> goal -> marked_tree
  | mark_disjL_left : marked_tree -> tree -> marked_tree
  | mark_disjL_right : tree -> marked_tree -> marked_tree
  | mark_disjR_left : marked_tree -> tree -> marked_tree
  | mark_disjR_right : tree -> marked_tree -> marked_tree.

Fixpoint erase_mark (m : marked_tree) : tree :=
  match m with
  | mark_here body => tdelay body
  | mark_under_delay m' => tdelay (erase_mark m')
  | mark_under_conj m' g => tconj (erase_mark m') g
  | mark_disjL_left m' other => tdisjL (erase_mark m') other
  | mark_disjL_right other m' => tdisjL other (erase_mark m')
  | mark_disjR_left m' other => tdisjR (erase_mark m') other
  | mark_disjR_right other m' => tdisjR other (erase_mark m')
  end.

Definition marked_expr : Type := (list state * marked_tree)%type.

Definition erase_marked (m : marked_expr) : expr :=
  (fst m, erase_mark (snd m)).

(** The marked delay is on the scheduler's active path.  A delay under
    another delay becomes active only after the outer delay is released. *)
Fixpoint active_mark (m : marked_tree) : Prop :=
  match m with
  | mark_here _ => True
  | mark_under_delay _ => False
  | mark_under_conj m' _ => active_mark m'
  | mark_disjL_left m' _ => active_mark m'
  | mark_disjL_right _ _ => False
  | mark_disjR_left _ _ => False
  | mark_disjR_right _ m' => active_mark m'
  end.

Lemma active_mark_exposed : forall m,
  active_mark m ->
  exists E body, erase_mark m = plug E (tdelay body).
Proof.
  induction m; simpl; intros Hactive; try contradiction.
  - exists chole, t. reflexivity.
  - destruct (IHm Hactive) as [E [body Heq]].
    exists (cconj E g), body. simpl. now rewrite Heq.
  - destruct (IHm Hactive) as [E [body Heq]].
    exists (cdisjL E t), body. simpl. now rewrite Heq.
  - destruct (IHm Hactive) as [E [body Heq]].
    exists (cdisjR t E), body. simpl. now rewrite Heq.
Qed.

Theorem active_mark_eventually_released : forall G ans m,
  active_mark m ->
  exists E body,
    multi G (erase_marked (ans, m)) (ans, delay_payload E body).
Proof.
  intros G ans m Hactive.
  destruct (active_mark_exposed m Hactive) as [E [body Heq]].
  exists E, body. unfold erase_marked. simpl. rewrite Heq.
  apply active_delay_eventually_scheduled.
Qed.

Lemma marked_not_value : forall m,
  ~ is_value (erase_marked m).
Proof.
  intros [ans m] Hvalue. destruct m; simpl in Hvalue; contradiction.
Qed.

Corollary marked_progress : forall G m,
  ok_expr G (erase_marked m) ->
  exists e', G |= erase_marked m --> e'.
Proof.
  intros G m Hok.
  destruct (progress G (erase_marked m) Hok) as [Hvalue | Hstep].
  - exfalso. exact (marked_not_value m Hvalue).
  - exact Hstep.
Qed.

(** Tracking a runtime step.  Releasing an enclosing delay retains the
    marker; releasing [mark_here] finishes it. *)

Inductive marked_release (G : env) : marked_expr -> expr -> Prop :=
  | marked_release_root : forall ans body,
      marked_release G (ans, mark_here body) (ans, body).

Lemma marked_release_erases : forall G m e',
  marked_release G m e' -> G |= erase_marked m --> e'.
Proof. intros G m e' Hrelease. destruct Hrelease. apply S_delay. Qed.

(** One movement of the marked delay through the active path. *)
Inductive marked_bubble (G : env) : marked_tree -> marked_tree -> Prop :=
  | bubble_conj : forall body g,
      marked_bubble G (mark_under_conj (mark_here body) g)
                      (mark_here (tconj body g))
  | bubble_disjL : forall body other,
      marked_bubble G (mark_disjL_left (mark_here body) other)
                      (mark_here (tdisjR body other))
  | bubble_disjR : forall body other,
      marked_bubble G (mark_disjR_right other (mark_here body))
                      (mark_here (tdisjL other body))
  | bubble_under_conj : forall m m' g,
      marked_bubble G m m' ->
      marked_bubble G (mark_under_conj m g) (mark_under_conj m' g)
  | bubble_under_disjL : forall m m' other,
      marked_bubble G m m' ->
      marked_bubble G (mark_disjL_left m other)
                      (mark_disjL_left m' other)
  | bubble_under_disjR : forall m m' other,
      marked_bubble G m m' ->
      marked_bubble G (mark_disjR_right other m)
                      (mark_disjR_right other m').

Lemma marked_bubble_head_context : forall G m m',
  marked_bubble G m m' ->
  exists E r r',
    erase_mark m = plug E r /\
    erase_mark m' = plug E r' /\ Head G r r'.
Proof.
  intros G m m' Hbubble. induction Hbubble.
  - exists chole, (tconj (tdelay body) g), (tdelay (tconj body g)).
    repeat split; try reflexivity. apply H_delay_conj.
  - exists chole, (tdisjL (tdelay body) other),
      (tdelay (tdisjR body other)).
    repeat split; try reflexivity. apply H_delay_left.
  - exists chole, (tdisjR other (tdelay body)),
      (tdelay (tdisjL other body)).
    repeat split; try reflexivity. apply H_delay_right.
  - destruct IHHbubble as [E [r [r' [Hsrc [Hdst Hhead]]]]].
    exists (cconj E g), r, r'. simpl. repeat split;
      try rewrite Hsrc; try rewrite Hdst; try reflexivity; exact Hhead.
  - destruct IHHbubble as [E [r [r' [Hsrc [Hdst Hhead]]]]].
    exists (cdisjL E other), r, r'. simpl. repeat split;
      try rewrite Hsrc; try rewrite Hdst; try reflexivity; exact Hhead.
  - destruct IHHbubble as [E [r [r' [Hsrc [Hdst Hhead]]]]].
    exists (cdisjR other E), r, r'. simpl. repeat split;
      try rewrite Hsrc; try rewrite Hdst; try reflexivity; exact Hhead.
Qed.

Lemma marked_bubble_erases : forall G ans m m',
  marked_bubble G m m' ->
  G |= erase_marked (ans, m) --> erase_marked (ans, m').
Proof.
  intros G ans m m' Hbubble.
  destruct (marked_bubble_head_context G m m' Hbubble)
    as [E [r [r' [Hsrc [Hdst Hhead]]]]].
  unfold erase_marked. simpl. rewrite Hsrc, Hdst.
  apply S_ctx. exact Hhead.
Qed.

Fixpoint active_depth (m : marked_tree) : nat :=
  match m with
  | mark_here _ => 0
  | mark_under_conj m' _ => S (active_depth m')
  | mark_disjL_left m' _ => S (active_depth m')
  | mark_disjR_right _ m' => S (active_depth m')
  | _ => 0
  end.

Lemma active_mark_bubbles : forall G m,
  active_mark m ->
  (exists body, m = mark_here body) \/
  exists m', marked_bubble G m m' /\
    active_mark m' /\ active_depth m' < active_depth m.
Proof.
  intros G m. induction m; simpl; intros Hactive; try contradiction.
  - left. eexists. reflexivity.
  - destruct (IHm Hactive) as [[body Heq] | [m' [Hb [Ha Hless]]]].
    + subst m. right. exists (mark_here (tconj body g)).
      repeat split; try constructor; simpl; lia.
    + right. exists (mark_under_conj m' g).
      repeat split; try (constructor; exact Hb); simpl; try assumption; lia.
  - destruct (IHm Hactive) as [[body Heq] | [m' [Hb [Ha Hless]]]].
    + subst m. right. exists (mark_here (tdisjR body t)).
      repeat split; try constructor; simpl; lia.
    + right. exists (mark_disjL_left m' t).
      repeat split; try (constructor; exact Hb); simpl; try assumption; lia.
  - destruct (IHm Hactive) as [[body Heq] | [m' [Hb [Ha Hless]]]].
    + subst m. right. exists (mark_here (tdisjL t body)).
      repeat split; try constructor; simpl; lia.
    + right. exists (mark_disjR_right t m').
      repeat split; try (constructor; exact Hb); simpl; try assumption; lia.
Qed.

(** Carry rules cover head rewrites, context propagation, delay
    rotation, answer reassociation, and promotion. *)
Inductive marked_carry (G : env) : marked_expr -> marked_expr -> Prop :=
  | carry_bubble : forall ans m m',
      marked_bubble G m m' ->
      marked_carry G (ans, m) (ans, m')
  | carry_outer_delay : forall ans m,
      marked_carry G (ans, mark_under_delay m) (ans, m)
  | carry_marked_conj_delay : forall ans body g,
      marked_carry G (ans, mark_under_conj (mark_here body) g)
                     (ans, mark_here (tconj body g))
  | carry_marked_disjL_delay : forall ans body other,
      marked_carry G (ans, mark_disjL_left (mark_here body) other)
                     (ans, mark_here (tdisjR body other))
  | carry_marked_disjR_delay : forall ans body other,
      marked_carry G (ans, mark_disjR_right other (mark_here body))
                     (ans, mark_here (tdisjL other body))
  | carry_waiting_left_head : forall ans E r r' m,
      Head G r r' ->
      marked_carry G (ans, mark_disjL_right (plug E r) m)
                     (ans, mark_disjL_right (plug E r') m)
  | carry_waiting_right_head : forall ans E r r' m,
      Head G r r' ->
      marked_carry G (ans, mark_disjR_left m (plug E r))
                     (ans, mark_disjR_left m (plug E r'))
  | carry_waiting_left_assoc_ll : forall ans s rest m,
      marked_carry G
        (ans, mark_disjL_right (tdisjL (tgoal gsucc s) rest) m)
        (ans, mark_disjL_right (tgoal gsucc s)
               (mark_disjL_right rest m))
  | carry_waiting_left_assoc_lr : forall ans s rest m,
      marked_carry G
        (ans, mark_disjL_right (tdisjR rest (tgoal gsucc s)) m)
        (ans, mark_disjR_left (mark_disjL_right rest m)
               (tgoal gsucc s))
  | carry_waiting_right_assoc_rl : forall ans s rest m,
      marked_carry G
        (ans, mark_disjR_left m (tdisjL (tgoal gsucc s) rest))
        (ans, mark_disjL_right (tgoal gsucc s)
               (mark_disjR_left m rest))
  | carry_waiting_right_assoc_rr : forall ans s rest m,
      marked_carry G
        (ans, mark_disjR_left m (tdisjR rest (tgoal gsucc s)))
        (ans, mark_disjR_left (mark_disjR_left m rest)
               (tgoal gsucc s))
  | carry_waiting_left_delay : forall ans active m,
      marked_carry G (ans, mark_disjL_right (tdelay active) m)
                     (ans, mark_under_delay (mark_disjR_right active m))
  | carry_waiting_right_delay : forall ans active m,
      marked_carry G (ans, mark_disjR_left m (tdelay active))
                     (ans, mark_under_delay (mark_disjL_left m active))
  | carry_waiting_left_fail : forall ans m,
      marked_carry G (ans, mark_disjL_right tfail m) (ans, m)
  | carry_waiting_right_fail : forall ans m,
      marked_carry G (ans, mark_disjR_left m tfail) (ans, m)
  | carry_waiting_left_answer : forall ans s m,
      marked_carry G (ans, mark_disjL_right (tgoal gsucc s) m)
                     (ans ++ [s], m)
  | carry_waiting_right_answer : forall ans s m,
      marked_carry G (ans, mark_disjR_left m (tgoal gsucc s))
                     (ans ++ [s], m)
  | carry_inactive_conj_delay : forall ans m g,
      marked_carry G (ans, mark_under_conj (mark_under_delay m) g)
                     (ans, mark_under_delay (mark_under_conj m g))
  | carry_inactive_conj_left_answer : forall ans s m g,
      marked_carry G
        (ans, mark_under_conj
                (mark_disjL_right (tgoal gsucc s) m) g)
        (ans, mark_disjL_right (tconj (tgoal gsucc s) g)
                (mark_under_conj m g))
  | carry_inactive_conj_right_answer : forall ans s m g,
      marked_carry G
        (ans, mark_under_conj
                (mark_disjR_left m (tgoal gsucc s)) g)
        (ans, mark_disjR_left (mark_under_conj m g)
                (tconj (tgoal gsucc s) g))
  | carry_inactive_disjL_delay : forall ans m other,
      marked_carry G
        (ans, mark_disjL_left (mark_under_delay m) other)
        (ans, mark_under_delay (mark_disjR_left m other))
  | carry_inactive_disjR_delay : forall ans m other,
      marked_carry G
        (ans, mark_disjR_right other (mark_under_delay m))
        (ans, mark_under_delay (mark_disjL_right other m))
  | carry_conj_head : forall ans m m' g E r r',
      marked_carry G (ans, m) (ans, m') ->
      erase_mark m = plug E r -> erase_mark m' = plug E r' ->
      Head G r r' ->
      marked_carry G (ans, mark_under_conj m g)
                     (ans, mark_under_conj m' g)
  | carry_disjL_active_head : forall ans m m' other E r r',
      marked_carry G (ans, m) (ans, m') ->
      erase_mark m = plug E r -> erase_mark m' = plug E r' ->
      Head G r r' ->
      marked_carry G (ans, mark_disjL_left m other)
                     (ans, mark_disjL_left m' other)
  | carry_disjR_active_head : forall ans m m' other E r r',
      marked_carry G (ans, m) (ans, m') ->
      erase_mark m = plug E r -> erase_mark m' = plug E r' ->
      Head G r r' ->
      marked_carry G (ans, mark_disjR_right other m)
                     (ans, mark_disjR_right other m')
  | carry_active_outer_ll : forall ans s m other,
      marked_carry G
        (ans, mark_disjL_left
                (mark_disjL_right (tgoal gsucc s) m) other)
        (ans, mark_disjL_right (tgoal gsucc s)
                (mark_disjL_left m other))
  | carry_active_outer_lr : forall ans s m other,
      marked_carry G
        (ans, mark_disjL_left
                (mark_disjR_left m (tgoal gsucc s)) other)
        (ans, mark_disjR_left (mark_disjL_left m other)
                (tgoal gsucc s))
  | carry_active_outer_rl : forall ans s m other,
      marked_carry G
        (ans, mark_disjR_right other
                (mark_disjL_right (tgoal gsucc s) m))
        (ans, mark_disjL_right (tgoal gsucc s)
                (mark_disjR_right other m))
  | carry_active_outer_rr : forall ans s m other,
      marked_carry G
        (ans, mark_disjR_right other
                (mark_disjR_left m (tgoal gsucc s)))
        (ans, mark_disjR_left (mark_disjR_right other m)
                (tgoal gsucc s)).

Lemma marked_carry_erases : forall G m m',
  marked_carry G m m' -> G |= erase_marked m --> erase_marked m'.
Proof.
  intros G m m' Hcarry. destruct Hcarry; simpl;
  try solve [apply marked_bubble_erases; assumption
    | apply S_delay
    | apply S_ctx with (E := chole); constructor].
  - apply S_ctx with (E := cdisjL E (erase_mark m)). assumption.
  - apply S_ctx with (E := cdisjR (erase_mark m) E). assumption.
  - apply S_promoteL.
  - apply S_promoteR.
  - unfold erase_marked. simpl. rewrite H, H0.
    apply S_ctx with (E := cconj E g). exact H1.
  - unfold erase_marked. simpl. rewrite H, H0.
    apply S_ctx with (E := cdisjL E other). exact H1.
  - unfold erase_marked. simpl. rewrite H, H0.
    apply S_ctx with (E := cdisjR other E). exact H1.
Qed.

Lemma head_mark_tracks : forall G ans m out,
  Head G (erase_mark m) out ->
  exists m', marked_carry G (ans, m) (ans, m') /\ erase_mark m' = out.
Proof.
  intros G ans m out Hhead.
  (* Once inversion identifies the head rule, only the corresponding
     carry constructor and its erasure equation remain. *)
  Ltac finish_head_case :=
    eexists; split; [eauto using marked_carry | reflexivity].
  destruct m; simpl in Hhead;
    inversion Hhead; subst; try discriminate;
    try solve [finish_head_case].
  all: destruct m; simpl in *; try discriminate;
    try solve [finish_head_case].
  all: try (inversion H0; subst; clear H0);
    try discriminate;
    try solve [finish_head_case].
  all: try (inversion H1; subst; clear H1);
    try discriminate;
    try solve [finish_head_case].
  all: match goal with
    | H : tgoal _ _ = erase_mark ?inner |- _ =>
        destruct inner; simpl in H; discriminate
    | H : erase_mark ?inner = tgoal _ _ |- _ =>
        destruct inner; simpl in H; discriminate
    end.
Qed.

Lemma plug_head_mark_tracks : forall G ans E m r r',
  erase_mark m = plug E r -> Head G r r' ->
  exists m', marked_carry G (ans, m) (ans, m') /\
             erase_mark m' = plug E r'.
Proof.
  intros G ans E. induction E; intros m r r' Hshape Hhead.
  - simpl in Hshape. subst r. exact (head_mark_tracks G ans m r' Hhead).
  - destruct m; simpl in Hshape; try discriminate;
      inversion Hshape; subst.
    + destruct (IHE m r r' ltac:(congruence) Hhead)
        as [next [Hcarry Herase]].
      exists (mark_disjL_left next t). split.
      * eapply carry_disjL_active_head; eassumption.
      * simpl. now rewrite Herase.
    + exists (mark_disjL_right (plug E r') m). split.
      * apply carry_waiting_left_head. exact Hhead.
      * reflexivity.
  - destruct m; simpl in Hshape; try discriminate;
      inversion Hshape; subst.
    + exists (mark_disjR_left m (plug E r')). split.
      * apply carry_waiting_right_head. exact Hhead.
      * reflexivity.
    + destruct (IHE m r r' ltac:(congruence) Hhead)
        as [next [Hcarry Herase]].
      exists (mark_disjR_right t next). split.
      * eapply carry_disjR_active_head; eassumption.
      * simpl. now rewrite Herase.
  - destruct m; simpl in Hshape; try discriminate;
      inversion Hshape; subst.
    destruct (IHE m r r' ltac:(congruence) Hhead)
      as [next [Hcarry Herase]].
    exists (mark_under_conj next g). split.
    + eapply carry_conj_head; eassumption.
    + simpl. now rewrite Herase.
Qed.

Theorem step_mark_tracks : forall G m e',
  G |= erase_marked m --> e' ->
  (exists m', marked_carry G m m' /\ erase_marked m' = e') \/
  marked_release G m e'.
Proof.
  intros G [ans m] e' Hstep.
  inversion Hstep; subst; clear Hstep.
  - destruct (plug_head_mark_tracks G ans E m r r'
      ltac:(symmetry; exact H1) H2) as [next [Hcarry Herase]].
    left. exists (ans, next). split; [exact Hcarry |].
    unfold erase_marked. simpl. now rewrite Herase.
  - destruct m; simpl in *; try discriminate.
    + right. inversion H1; subst. constructor.
    + left. exists (ans, m). split.
      * apply carry_outer_delay.
      * unfold erase_marked. simpl. congruence.
  - destruct m; simpl in *; try discriminate.
    + inversion H1; subst. exfalso.
      destruct m; discriminate.
    + left. exists (ans ++ [s], m). split.
      * inversion H1; subst. apply carry_waiting_left_answer.
      * unfold erase_marked. simpl. congruence.
  - destruct m; simpl in *; try discriminate.
    + left. exists (ans ++ [s], m). split.
      * inversion H1; subst. apply carry_waiting_right_answer.
      * unfold erase_marked. simpl. congruence.
    + inversion H1; subst. exfalso.
      destruct m; discriminate.
Qed.

(** This equivalence is the connection to the operational semantics in
    [Reduction].  The destination of a carry is compared only after
    erasure, because the runtime has no marker.  The release case is
    separate because the chosen occurrence no longer exists afterward. *)
Theorem marked_step_correspondence : forall G m e',
  G |= erase_marked m --> e' <->
  (exists m', marked_carry G m m' /\ erase_marked m' = e') \/
  marked_release G m e'.
Proof.
  intros G [ans m] e'. split.
  - apply step_mark_tracks.
  - intros [[m' [Hcarry Heq]] | Hrelease].
    + rewrite <- Heq. exact (marked_carry_erases _ _ _ Hcarry).
    + exact (marked_release_erases _ _ _ Hrelease).
Qed.

(** Finite carrying traces and release. *)

Inductive tracked_finish (G : env) : marked_expr -> expr -> Prop :=
  | tracked_release : forall m e',
      marked_release G m e' -> tracked_finish G m e'
  | tracked_continue : forall m m' e',
      marked_carry G m m' -> tracked_finish G m' e' ->
      tracked_finish G m e'.

Theorem active_mark_tracked_finish : forall G ans m,
  active_mark m -> exists e', tracked_finish G (ans, m) e'.
Proof.
  intros G ans m Hactive.
  assert (Hmain : forall n m, active_depth m <= n -> active_mark m ->
    exists e', tracked_finish G (ans, m) e').
  { induction n as [|n IH]; intros current Hdepth Hcurrent;
      destruct (active_mark_bubbles G current Hcurrent)
        as [[body Heq] | [next [Hbubble [Hnext Hless]]]].
    - subst current. exists (ans, body).
      apply tracked_release. constructor.
    - lia.
    - subst current. exists (ans, body).
      apply tracked_release. constructor.
    - destruct (IH next ltac:(lia) Hnext) as [out Hfinish].
      exists out. eapply tracked_continue.
      + apply carry_bubble. exact Hbubble.
      + exact Hfinish.
  }
  exact (Hmain (active_depth m) m (le_n _) Hactive).
Qed.

Inductive carried_multi (G : env) : marked_expr -> marked_expr -> Prop :=
  | carried_refl : forall m, carried_multi G m m
  | carried_step : forall m m' m'',
      marked_carry G m m' -> carried_multi G m' m'' ->
      carried_multi G m m''.

Lemma carried_multi_erases : forall G m m',
  carried_multi G m m' -> multi G (erase_marked m) (erase_marked m').
Proof.
  intros G m m' Hrun. induction Hrun.
  - constructor.
  - eapply multi_step; [apply marked_carry_erases; eassumption | exact IHHrun].
Qed.

Lemma carried_multi_ok : forall G m m',
  ok_env G -> ok_expr G (erase_marked m) ->
  carried_multi G m m' -> ok_expr G (erase_marked m').
Proof.
  intros G m m' Henv Hok Hrun.
  eapply multi_ok; [apply carried_multi_erases; exact Hrun | exact Henv | exact Hok].
Qed.

Lemma carried_multi_finish : forall G m m' e',
  carried_multi G m m' -> tracked_finish G m' e' ->
  tracked_finish G m e'.
Proof.
  intros G m m' e' Hrun Hfinish. induction Hrun.
  - exact Hfinish.
  - eapply tracked_continue; [exact H |].
    apply IHHrun. exact Hfinish.
Qed.

Lemma carried_multi_trans : forall G m m' m'',
  carried_multi G m m' -> carried_multi G m' m'' ->
  carried_multi G m m''.
Proof.
  intros G m m' m'' Hfirst. revert m''.
  induction Hfirst; intros target Hsecond; [exact Hsecond |].
  eapply carried_step; [exact H |].
  apply IHHfirst. exact Hsecond.
Qed.

Lemma tracked_finish_reaches_active : forall G m e',
  tracked_finish G m e' ->
  exists m', carried_multi G m m' /\ active_mark (snd m').
Proof.
  intros G m e' Hfinish. induction Hfinish.
  - destruct H. exists (ans, mark_here body).
    split; [constructor | exact I].
  - destruct IHHfinish as [at_active [Hrun Hactive]].
    exists at_active. split; [|exact Hactive].
    eapply carried_step; eassumption.
Qed.

Theorem tracked_finish_iff_eventually_active : forall G m,
  (exists e', tracked_finish G m e') <->
  (exists m', carried_multi G m m' /\ active_mark (snd m')).
Proof.
  intros G m. split.
  - intros [e' Hfinish]. eapply tracked_finish_reaches_active;
      eassumption.
  - intros [[ans marked] [Hrun Hactive]].
    destruct (active_mark_tracked_finish G ans marked Hactive)
      as [e' Hfinish].
    exists e'. eapply carried_multi_finish; eassumption.
Qed.

(** Along any finite execution, the chosen occurrence survives until
    its own release.  A release may be followed by arbitrary reduction,
    so the right-hand case records the prefix at which it happened. *)
Theorem multi_mark_tracks : forall G m e',
  multi G (erase_marked m) e' ->
  (exists m', carried_multi G m m' /\ erase_marked m' = e') \/
  (exists m' released,
    carried_multi G m m' /\ marked_release G m' released /\
    multi G released e').
Proof.
  intros G m e' Hrun. remember (erase_marked m) as start eqn:Hstart.
  revert m Hstart.
  induction Hrun; intros marked Hstart.
  - left. exists marked. split; [apply carried_refl | symmetry; exact Hstart].
  - subst e1.
    destruct (step_mark_tracks G marked e2 H) as
      [[next [Hcarry Herase]] | Hrelease].
    + destruct (IHHrun next (eq_sym Herase)) as
        [[final [Hprefix Hfinal]] |
         [site [released [Hprefix [Hreleased Htail]]]]].
      * left. exists final. split; [|exact Hfinal].
        eapply carried_step; eassumption.
      * right. exists site, released. repeat split; try assumption.
        eapply carried_step; eassumption.
    + right. exists marked, e2. repeat split; try assumption.
      * constructor.
Qed.
