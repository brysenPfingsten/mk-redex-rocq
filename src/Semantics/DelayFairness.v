From Stdlib Require Import List Lia Arith.Wf_nat.
Import ListNotations.
From MkRedex.Language Require Import Goals Substitution Environments Trees.
From MkRedex.Semantics Require Import Reduction WellFormed Determinism Delay.
Set Default Goal Selector "!".

(** Global no-stranding for one chosen delay occurrence.

    The question is about an *occurrence*, not a piece of syntax: if two
    branches contain identical [tdelay] trees, we must show that the one
    chosen at the start is eventually scheduled.  [marked_tree] records
    its unique position.  [erase_marked] forgets this proof annotation
    and returns an ordinary runtime expression.  The constructors for
    disjunction record both which child the scheduler selects ([tdisjL]
    selects left, [tdisjR] selects right) and which child contains the
    marker.  A marked delay is [active_mark] when it lies on the selected
    path.  A delay inside another delay is inactive until the enclosing
    delay is released.

    There is only one operational semantics: [step] in [Reduction].
    [marked_carry] is an instrumented description of a runtime step that
    preserves the chosen occurrence; [marked_release] describes the step
    that removes that occurrence itself.  The carry constructors look
    like a second step relation because a runtime tree has no place to
    store the marker.  [marked_step_correspondence] proves their exact
    relationship: a runtime step from an erased marked expression exists
    precisely when it can be classified as a carry with the same erased
    destination or as release.  Its forward half is [step_mark_tracks];
    its reverse half uses [marked_carry_erases] and
    [marked_release_erases].  The classification covers answer promotion
    and answer reassociation as well as ordinary head rewrites.  Thus a
    marker cannot silently disappear during an ordinary runtime step.
    [multi_mark_tracks] extends this fact over any finite runtime trace:
    either the occurrence is still present at its endpoint, or a prefix
    released it.  Conversely, [tracked_finish_erases] projects every
    marked release witness to a real finite [multi] execution.

    Once the marker is active, it needs no fairness assumption.  The
    scheduler's delay-rotation rules move it outward through a finite
    active context; [active_depth] strictly decreases at each rotation.
    At the root, the [S_delay] step releases it.  This is the easy half
    of the argument, formalized by [active_mark_tracked_finish].

    The difficult half is reaching the active path.  If a disjunction
    selects the other child, that child cannot run forever without a
    handoff: [finite_burst_marked] in [Delay] says that, under
    [closed_env] and [ok_expr], a selected burst reaches a final value
    (success or failure) or a root delay in finitely many steps.  Success
    is promoted, failure is pruned, and a delay rotates past the
    disjunction.  Each case gives the waiting child a turn.  The
    immediate handoff lemmas prove these cases for one waiting node.

    A global count of waiting nodes is not a valid decreasing measure.
    Answer reassociation can rearrange disjunctions, and conjunction can
    create a new disjunction when it extends an answer with its right
    goal.  Instead, [scheduler_index] measures a *local finite shell* of
    disjunctions around the subtree we currently want to focus.  One
    finite-burst handoff either focuses that subtree or strictly lowers
    this shell index.  Well-founded induction in
    [disj_shell_eventually_focused] finishes the local scheduling task.

    A finite trace inside a subtree cannot simply be replayed under an
    arbitrary context: a conjunction may promote an answer and spawn a
    continuation, changing both the answer list and the disjunctions
    around the subtree.  [marked_carry_cases] separates a local step
    into a head rewrite, release of an enclosing delay, or promotion on
    either side.  [marked_carry_rebase] handles a changed answer list.
    [contextual_disj_trace_lift] and
    [contextual_conjunction_trace_lift] lift each local carry through its
    outer context, run any newly selected continuation for a finite
    burst, refocus the marked subtree, and then lift the rest of the
    trace.  These are finite-trace lemmas, so the proof never assumes an
    infinite scheduler trace is fair.

    Finally, [eventually_active] inducts over the marked tree.  For an
    enclosing delay it first releases that delay; for conjunction and
    disjunction it lifts the induction hypothesis through the enclosing
    constructor using the lemmas above.  The equivalence
    [tracked_finish_iff_eventually_active] joins that result to the
    active-path release proof, yielding [global_no_stranding].  The
    theorem gives a finite runtime execution releasing the exact chosen
    occurrence, provided the starting expression is well formed in a
    closed environment.  Since [step_deterministic] proves runtime
    one-step determinism, this finite prefix is forced for any execution
    that continues taking steps. *)

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

Lemma erase_mark_not_goal : forall m g s,
  erase_mark m <> tgoal g s.
Proof. intros m g s. destruct m; discriminate. Qed.

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
      apply (erase_mark_not_goal m gsucc s). 
      symmetry. assumption.
    + left. exists (ans ++ [s], m). split.
      * inversion H1; subst. apply carry_waiting_left_answer.
      * unfold erase_marked. simpl. congruence.
  - destruct m; simpl in *; try discriminate.
    + left. exists (ans ++ [s], m). split.
      * inversion H1; subst. apply carry_waiting_right_answer.
      * unfold erase_marked. simpl. congruence.
    + inversion H1; subst. exfalso.
      apply (erase_mark_not_goal m gsucc s). symmetry. eassumption.
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
  intros G m e'. split.
  - apply step_mark_tracks.
  - intros [[m' [Hcarry Heq]] | Hrelease].
    + rewrite <- Heq. now apply marked_carry_erases.
    + now apply marked_release_erases.
Qed.


(** Finite carrying traces and release. *)

Inductive tracked_finish (G : env) : marked_expr -> expr -> Prop :=
  | tracked_release : forall m e',
      marked_release G m e' -> tracked_finish G m e'
  | tracked_continue : forall m m' e',
      marked_carry G m m' -> tracked_finish G m' e' ->
      tracked_finish G m e'.

Lemma tracked_finish_erases : forall G m e',
  tracked_finish G m e' -> multi G (erase_marked m) e'.
Proof.
  intros G m e' Hfinish. induction Hfinish.
  - eapply multi_step; [apply marked_release_erases; eassumption | constructor].
  - eapply multi_step; [apply marked_carry_erases; eassumption | exact IHHfinish].
Qed.

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
  closed_env G -> ok_expr G (erase_marked m) ->
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

Lemma contextual_conjunction_answer_shell_left : forall G ans E s m g,
  closed_env G -> disj_only_ctx E ->
  ok_expr G (erase_marked (ans, plug_active_mark E
    (mark_under_conj (mark_disjL_right (tgoal gsucc s) m) g))) ->
  exists target,
    carried_multi G
      (ans, plug_active_mark E
        (mark_under_conj (mark_disjL_right (tgoal gsucc s) m) g))
      target /\
    disj_shell (mark_under_conj m g) (snd target).
Proof.
  intros G ans E s m g Henv Hctx Hok.
  set (active := tconj (tgoal gsucc s) g).
  set (residual := mark_under_conj m g).
  set (mid := mark_disjL_right active residual).
  assert (Hcarry : marked_carry G
    (ans, plug_active_mark E
      (mark_under_conj (mark_disjL_right (tgoal gsucc s) m) g))
    (ans, plug_active_mark E mid)).
  { unfold mid, active, residual.
    eapply lift_head_carry with (K := chole).
    - apply carry_inactive_conj_left_answer.
    - reflexivity.
    - reflexivity.
    - apply H_left_ans_conj. }
  assert (Hokmid : ok_expr G (erase_marked (ans, plug_active_mark E mid))).
  { eapply step_ok; [exact Henv | exact Hok |].
    apply marked_carry_erases. exact Hcarry. }
  assert (Hactive : ok_expr G (ans, active)).
  { unfold mid, erase_marked in Hokmid. simpl in Hokmid.
    rewrite erase_plug_active_mark in Hokmid.
    eapply ok_expr_disjL_left.
    eapply ok_expr_disj_context; eassumption. }
  destruct (contextual_disj_handoff_left G ans E active residual
    Henv Hactive Hctx) as [target [Hrun [Hsame | [body Hrot]]]].
  - exists target. split.
    + eapply carried_step; eassumption.
    + rewrite Hsame. unfold residual.
      apply disj_shell_plug_active; [constructor | exact Hctx].
  - exists target. split.
    + eapply carried_step; eassumption.
    + rewrite Hrot. unfold residual.
      apply disj_shell_rotate; [constructor; constructor | exact Hctx].
Qed.

Lemma contextual_conjunction_answer_shell_right : forall G ans E s m g,
  closed_env G -> disj_only_ctx E ->
  ok_expr G (erase_marked (ans, plug_active_mark E
    (mark_under_conj (mark_disjR_left m (tgoal gsucc s)) g))) ->
  exists target,
    carried_multi G
      (ans, plug_active_mark E
        (mark_under_conj (mark_disjR_left m (tgoal gsucc s)) g))
      target /\
    disj_shell (mark_under_conj m g) (snd target).
Proof.
  intros G ans E s m g Henv Hctx Hok.
  set (active := tconj (tgoal gsucc s) g).
  set (residual := mark_under_conj m g).
  set (mid := mark_disjR_left residual active).
  assert (Hcarry : marked_carry G
    (ans, plug_active_mark E
      (mark_under_conj (mark_disjR_left m (tgoal gsucc s)) g))
    (ans, plug_active_mark E mid)).
  { unfold mid, active, residual.
    eapply lift_head_carry with (K := chole).
    - apply carry_inactive_conj_right_answer.
    - reflexivity.
    - reflexivity.
    - apply H_right_ans_conj. }
  assert (Hokmid : ok_expr G (erase_marked (ans, plug_active_mark E mid))).
  { eapply step_ok; [exact Henv | exact Hok |].
    apply marked_carry_erases. exact Hcarry. }
  assert (Hactive : ok_expr G (ans, active)).
  { unfold mid, erase_marked in Hokmid. simpl in Hokmid.
    rewrite erase_plug_active_mark in Hokmid.
    eapply ok_expr_disjR_right.
    eapply ok_expr_disj_context; eassumption. }
  destruct (contextual_disj_handoff_right G ans E active residual
    Henv Hactive Hctx) as [target [Hrun [Hsame | [body Hrot]]]].
  - exists target. split.
    + eapply carried_step; eassumption.
    + rewrite Hsame. unfold residual.
      apply disj_shell_plug_active; [constructor | exact Hctx].
  - exists target. split.
    + eapply carried_step; eassumption.
    + rewrite Hrot. unfold residual.
      apply disj_shell_rotate; [constructor; constructor | exact Hctx].
Qed.


Lemma ok_expr_plug_inv : forall G ans E t,
  ok_expr G (ans, plug E t) -> ok_expr G (ans, t).
Proof.
  intros G ans E t [[c Hclosed] [Htight [Hans Hacyclic]]].
  repeat split.
  - exists c. eapply plug_closed_inv; eassumption.
  - eapply plug_tight_inv; eassumption.
  - exact Hans.
  - eapply plug_acyclic_inv; eassumption.
Qed.

Lemma active_mark_plug_active : forall E m,
  active_mark m -> active_mark (plug_active_mark E m).
Proof.
  induction E; intros m Hactive; simpl; auto.
Qed.


(** Lifting finite marked traces through contexts. *)

(** Every carry is either a head reduction, an enclosing-delay release,
    or one of the two answer promotions.  This classification supports
    finite-trace lifting through further scheduler contexts. *)
Lemma append_answer_changes_length : forall (ans : list state) s,
  ans <> ans ++ [s].
Proof.
  intros ans s Heq. apply (f_equal (@length state)) in Heq.
  rewrite length_app in Heq. simpl in Heq. lia.
Qed.

Lemma marked_carry_cases : forall G ans m ans' m',
  marked_carry G (ans, m) (ans', m') ->
  (ans' = ans /\ exists E r r',
    erase_mark m = plug E r /\
    erase_mark m' = plug E r' /\ Head G r r') \/
  (exists inner,
    ans' = ans /\ m = mark_under_delay inner /\ m' = inner) \/
  (exists s inner,
    ans' = ans ++ [s] /\
    m = mark_disjL_right (tgoal gsucc s) inner /\ m' = inner) \/
  (exists s inner,
    ans' = ans ++ [s] /\
    m = mark_disjR_left inner (tgoal gsucc s) /\ m' = inner).
Proof.
  intros G ans m ans' m' Hcarry.
  pose proof (marked_carry_erases G (ans, m) (ans', m') Hcarry)
    as Hstep.
  unfold erase_marked in Hstep. simpl in Hstep.
  inversion Hstep; subst; clear Hstep.
  - left. split; [reflexivity |].
    exists E, r, r'. repeat split; auto.
  - destruct m; simpl in H1; try discriminate.
    all: inversion Hcarry; subst; try solve [inversion H0].
    right. left. exists m'. repeat split; reflexivity.
  - destruct m; simpl in H1; try discriminate.
    all: try solve [destruct m; simpl in H1; discriminate].
    inversion Hcarry; subst; try discriminate.
    all: try solve [exfalso;
      apply (append_answer_changes_length ans s); congruence].
    right. right. left. exists s0, m'.
    repeat split; reflexivity.
  - destruct m; simpl in H1; try discriminate.
    all: try solve [destruct m; simpl in H1; discriminate].
    inversion Hcarry; subst; try discriminate.
    all: try solve [exfalso;
      apply (append_answer_changes_length ans s); congruence].
    right. right. right. exists s0, m'.
    repeat split; reflexivity.
Qed.

Lemma marked_carry_rebase : forall G p q,
  marked_carry G p q -> forall current,
  exists out,
    marked_carry G (current, snd p) (out, snd q) /\
    (fst p = fst q -> out = current).
Proof.
  intros G p q Hcarry.
  induction Hcarry; intros current; simpl;
    try solve [exists current; split;
      [eauto using marked_carry | reflexivity]].
  - exists (current ++ [s]). split.
    + apply carry_waiting_left_answer.
    + intros Heq. exfalso.
      apply (append_answer_changes_length ans s). exact Heq.
  - exists (current ++ [s]). split.
    + apply carry_waiting_right_answer.
    + intros Heq. exfalso.
      apply (append_answer_changes_length ans s). exact Heq.
  - destruct (IHHcarry current) as [out [Hreb Hsame]].
    specialize (Hsame eq_refl). subst out.
    exists current. split; [|reflexivity].
    eapply carry_conj_head; eassumption.
  - destruct (IHHcarry current) as [out [Hreb Hsame]].
    specialize (Hsame eq_refl). subst out.
    exists current. split; [|reflexivity].
    eapply carry_disjL_active_head; eassumption.
  - destruct (IHHcarry current) as [out [Hreb Hsame]].
    specialize (Hsame eq_refl). subst out.
    exists current. split; [|reflexivity].
    eapply carry_disjR_active_head; eassumption.
Qed.

Lemma contextual_conjunction_carry_shell : forall G ans m ans' m' g E global_ans,
  marked_carry G (ans, m) (ans', m') ->
  closed_env G -> disj_only_ctx E ->
  ok_expr G (erase_marked
    (global_ans, plug_active_mark E (mark_under_conj m g))) ->
  exists target,
    carried_multi G
      (global_ans, plug_active_mark E (mark_under_conj m g)) target /\
    disj_shell (mark_under_conj m' g) (snd target).
Proof.
  intros G ans m ans' m' g E global_ans Hcarry Henv Hctx Hok.
  destruct (marked_carry_cases G ans m ans' m' Hcarry)
    as [[Hans [K [r [r' [Hsrc [Hdst Hhead]]]]]] |
        [[inner [Hans [Hsrc Hdst]]] |
         [[s [inner [Hans [Hsrc Hdst]]]] |
          [s [inner [Hans [Hsrc Hdst]]]]]]].
  - subst ans'.
    destruct (marked_carry_rebase G (ans, m) (ans, m') Hcarry
      global_ans) as [rebased [Hreb Hsame]].
    specialize (Hsame eq_refl). subst rebased.
    assert (Hinner : marked_carry G
      (global_ans, mark_under_conj m g)
      (global_ans, mark_under_conj m' g)).
    { eapply carry_conj_head with (E := K);
        [exact Hreb | exact Hsrc | exact Hdst | exact Hhead]. }
    exists (global_ans, plug_active_mark E (mark_under_conj m' g)).
    split.
    + eapply carried_step; [|constructor].
      eapply lift_head_carry with (K := cconj K g).
      * exact Hinner.
      * simpl. rewrite Hsrc. reflexivity.
      * simpl. rewrite Hdst. reflexivity.
      * exact Hhead.
    + apply disj_shell_plug_active; [constructor | exact Hctx].
  - subst ans' m m'.
    exists (global_ans, rotate_mark E (mark_under_conj inner g)).
    split.
    + eapply carried_step.
      * eapply lift_head_carry with (K := chole).
        -- apply carry_inactive_conj_delay.
        -- reflexivity.
        -- reflexivity.
        -- apply H_delay_conj.
      * apply release_enclosing_delay_in_context.
    + apply disj_shell_rotate; [constructor | exact Hctx].
  - subst ans' m m'.
    eapply contextual_conjunction_answer_shell_left; eassumption.
  - subst ans' m m'.
    eapply contextual_conjunction_answer_shell_right; eassumption.
Qed.

Theorem contextual_conjunction_trace_lift : forall G local_start local_end g,
  carried_multi G local_start local_end ->
  forall ans E,
    closed_env G -> disj_only_ctx E ->
    ok_expr G (erase_marked (ans, plug_active_mark E
      (mark_under_conj (snd local_start) g))) ->
    exists out K,
      carried_multi G
        (ans, plug_active_mark E
          (mark_under_conj (snd local_start) g))
        (out, plug_active_mark K
          (mark_under_conj (snd local_end) g)) /\
      disj_only_ctx K.
Proof.
  intros G local_start local_end g Hrun.
  induction Hrun; intros ans E Henv Hctx Hok.
  - exists ans, E. split; [constructor | exact Hctx].
  - destruct m as [local_ans marked].
    destruct m' as [local_out next].
    destruct (contextual_conjunction_carry_shell G local_ans marked
      local_out next g E ans H Henv Hctx Hok)
      as [[shell_ans shell_tree] [Hstep_shell Hshell]].
    assert (Hokshell : ok_expr G
      (erase_marked (shell_ans, shell_tree))).
    { eapply carried_multi_ok; eassumption. }
    destruct (disj_shell_eventually_focused G shell_ans
      (mark_under_conj next g) shell_tree Henv Hokshell Hshell)
      as [focused_ans [K [Hfocus Hfocused]]].
    assert (Hokfocused : ok_expr G (erase_marked
      (focused_ans, plug_active_mark K (mark_under_conj next g)))).
    { eapply carried_multi_ok; eassumption. }
    destruct (IHHrun focused_ans K Henv Hfocused Hokfocused)
      as [out [K' [Htail Hctx']]].
    exists out, K'. split; [|exact Hctx'].
    eapply carried_multi_trans; [exact Hstep_shell |].
    eapply carried_multi_trans; eassumption.
Qed.

Corollary conjunction_preserves_eventual_active : forall G ans m g,
  closed_env G ->
  ok_expr G (erase_marked (ans, mark_under_conj m g)) ->
  (exists local_ans local_target,
    carried_multi G (local_ans, m) local_target /\
    active_mark (snd local_target)) ->
  exists target,
    carried_multi G (ans, mark_under_conj m g) target /\
    active_mark (snd target).
Proof.
  intros G ans m g Henv Hok
    [local_ans [local_target [Hlocal Hactive]]].
  destruct (contextual_conjunction_trace_lift G
    (local_ans, m) local_target g Hlocal ans chole Henv I Hok)
    as [out [K [Hrun Hctx]]].
  exists (out, plug_active_mark K
    (mark_under_conj (snd local_target) g)).
  split; [exact Hrun |].
  apply active_mark_plug_active. simpl. exact Hactive.
Qed.

Lemma contextual_disj_carry_shell : forall G ans m ans' m' E global_ans,
  marked_carry G (ans, m) (ans', m') ->
  disj_only_ctx E ->
  exists target,
    carried_multi G (global_ans, plug_active_mark E m) target /\
    disj_shell m' (snd target).
Proof.
  intros G ans m ans' m' E global_ans Hcarry Hctx.
  destruct (marked_carry_cases G ans m ans' m' Hcarry)
    as [[Hans [K [r [r' [Hsrc [Hdst Hhead]]]]]] |
        [[inner [Hans [Hsrc Hdst]]] |
         [[s [inner [Hans [Hsrc Hdst]]]] |
          [s [inner [Hans [Hsrc Hdst]]]]]]].
  - subst ans'.
    destruct (marked_carry_rebase G (ans, m) (ans, m') Hcarry
      global_ans) as [rebased [Hreb Hsame]].
    specialize (Hsame eq_refl). subst rebased.
    exists (global_ans, plug_active_mark E m'). split.
    + eapply carried_step; [|constructor].
      eapply lift_head_carry with (K := K);
        [exact Hreb | exact Hsrc | exact Hdst | exact Hhead].
    + apply disj_shell_plug_active; [constructor | exact Hctx].
  - subst ans' m m'.
    exists (global_ans, rotate_mark E inner). split.
    + apply release_enclosing_delay_in_context.
    + apply disj_shell_rotate; [constructor | exact Hctx].
  - subst ans' m m'.
    exists (global_ans ++ [s], plug_active_mark E inner). split.
    + apply contextual_waiting_answer_left. exact Hctx.
    + apply disj_shell_plug_active; [constructor | exact Hctx].
  - subst ans' m m'.
    exists (global_ans ++ [s], plug_active_mark E inner). split.
    + apply contextual_waiting_answer_right. exact Hctx.
    + apply disj_shell_plug_active; [constructor | exact Hctx].
Qed.

Theorem contextual_disj_trace_lift : forall G local_start local_end,
  carried_multi G local_start local_end ->
  forall ans E,
    closed_env G -> disj_only_ctx E ->
    ok_expr G (erase_marked
      (ans, plug_active_mark E (snd local_start))) ->
    exists out K,
      carried_multi G
        (ans, plug_active_mark E (snd local_start))
        (out, plug_active_mark K (snd local_end)) /\
      disj_only_ctx K.
Proof.
  intros G local_start local_end Hrun.
  induction Hrun; intros ans E Henv Hctx Hok.
  - exists ans, E. split; [constructor | exact Hctx].
  - destruct m as [local_ans marked].
    destruct m' as [local_out next].
    destruct (contextual_disj_carry_shell G local_ans marked
      local_out next E ans H Hctx)
      as [[shell_ans shell_tree] [Hstep_shell Hshell]].
    assert (Hokshell : ok_expr G
      (erase_marked (shell_ans, shell_tree))).
    { eapply carried_multi_ok; eassumption. }
    destruct (disj_shell_eventually_focused G shell_ans
      next shell_tree Henv Hokshell Hshell)
      as [focused_ans [K [Hfocus Hfocused]]].
    assert (Hokfocused : ok_expr G
      (erase_marked (focused_ans, plug_active_mark K next))).
    { eapply carried_multi_ok; eassumption. }
    destruct (IHHrun focused_ans K Henv Hfocused Hokfocused)
      as [out [K' [Htail Hctx']]].
    exists out, K'. split; [|exact Hctx'].
    eapply carried_multi_trans; [exact Hstep_shell |].
    eapply carried_multi_trans; eassumption.
Qed.

Corollary disj_shell_preserves_eventual_active : forall G ans inner shell,
  closed_env G -> ok_expr G (erase_marked (ans, shell)) ->
  disj_shell inner shell ->
  (exists local_ans local_target,
    carried_multi G (local_ans, inner) local_target /\
    active_mark (snd local_target)) ->
  exists target,
    carried_multi G (ans, shell) target /\ active_mark (snd target).
Proof.
  intros G ans inner shell Henv Hok Hshell
    [local_ans [local_target [Hlocal Hactive]]].
  destruct (disj_shell_eventually_focused G ans inner shell
    Henv Hok Hshell) as [focused_ans [E [Hfocus Hctx]]].
  assert (Hokfocus : ok_expr G
    (erase_marked (focused_ans, plug_active_mark E inner))).
  { eapply carried_multi_ok; eassumption. }
  destruct (contextual_disj_trace_lift G
    (local_ans, inner) local_target Hlocal
    focused_ans E Henv Hctx Hokfocus)
    as [out [K [Htrace Hctx']]].
  exists (out, plug_active_mark K (snd local_target)).
  split.
  - eapply carried_multi_trans; eassumption.
  - apply active_mark_plug_active. exact Hactive.
Qed.


(** Global no-stranding. *)

Theorem eventually_active : forall G marked,
  closed_env G -> ok_expr G (erase_marked marked) ->
  exists target,
    carried_multi G marked target /\ active_mark (snd target).
Proof.
  intros G [ans m] Henv Hok. revert ans Hok.
  induction m; intros ans Hok.
  - exists (ans, mark_here t). split; [constructor | exact I].
  - assert (Hokinner : ok_expr G (erase_marked (ans, m))).
    { eapply step_ok; [exact Henv | exact Hok |].
      apply marked_carry_erases. apply carry_outer_delay. }
    destruct (IHm ans Hokinner) as [target [Hrun Hactive]].
    exists target. split; [|exact Hactive].
    eapply carried_step; [apply carry_outer_delay | exact Hrun].
  - assert (Hokinner : ok_expr G (erase_marked (ans, m))).
    { unfold erase_marked in Hok |- *. simpl in *.
      exact (ok_expr_plug_inv G ans (cconj chole g)
        (erase_mark m) Hok). }
    destruct (IHm ans Hokinner) as [target [Hrun Hactive]].
    eapply conjunction_preserves_eventual_active;
      [exact Henv | exact Hok |].
    exists ans, target. split; assumption.
  - assert (Hokinner : ok_expr G (erase_marked (ans, m))).
    { unfold erase_marked in Hok |- *. simpl in *.
      eapply ok_expr_disjL_left; exact Hok. }
    destruct (IHm ans Hokinner) as [target [Hrun Hactive]].
    eapply disj_shell_preserves_eventual_active
      with (inner := m) (shell := mark_disjL_left m t);
      [exact Henv | exact Hok | constructor; constructor |].
    exists ans, target. split; assumption.
  - assert (Hokinner : ok_expr G (erase_marked (ans, m))).
    { unfold erase_marked in Hok |- *. simpl in *.
      eapply ok_expr_disjL_right; exact Hok. }
    destruct (IHm ans Hokinner) as [target [Hrun Hactive]].
    eapply disj_shell_preserves_eventual_active
      with (inner := m) (shell := mark_disjL_right t m);
      [exact Henv | exact Hok | constructor; constructor |].
    exists ans, target. split; assumption.
  - assert (Hokinner : ok_expr G (erase_marked (ans, m))).
    { unfold erase_marked in Hok |- *. simpl in *.
      eapply ok_expr_disjR_left; exact Hok. }
    destruct (IHm ans Hokinner) as [target [Hrun Hactive]].
    eapply disj_shell_preserves_eventual_active
      with (inner := m) (shell := mark_disjR_left m t);
      [exact Henv | exact Hok | constructor; constructor |].
    exists ans, target. split; assumption.
  - assert (Hokinner : ok_expr G (erase_marked (ans, m))).
    { unfold erase_marked in Hok |- *. simpl in *.
      eapply ok_expr_disjR_right; exact Hok. }
    destruct (IHm ans Hokinner) as [target [Hrun Hactive]].
    eapply disj_shell_preserves_eventual_active
      with (inner := m) (shell := mark_disjR_right t m);
      [exact Henv | exact Hok | constructor; constructor |].
    exists ans, target. split; assumption.
Qed.

(** Every well-formed marked occurrence reaches the active path, then
    releases after finitely many further steps. *)
Theorem global_no_stranding : forall G marked,
  closed_env G -> ok_expr G (erase_marked marked) ->
  exists out, tracked_finish G marked out.
Proof.
  intros G marked Henv Hok.
  apply (proj2 (tracked_finish_iff_eventually_active G marked)).
  exact (eventually_active G marked Henv Hok).
Qed.
