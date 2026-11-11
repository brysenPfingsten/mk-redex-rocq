From Stdlib Require Import Arith.Wf_nat.
From MkRedex.Language Require Import WellFormed Scoping ScopedUnification Goals Substitution Environments Trees.
From Stdlib Require Import List Lia Arith.
From MkRedex.Operational Require Import Reduction WellFormed Determinism Delay DelayTracking Scheduling.
Import ListNotations.
Set Default Goal Selector "!".


Lemma contextual_conjunction_answer_shell_left : forall G ans E s m g,
  ok_env G -> disj_only_ctx E ->
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
  ok_env G -> disj_only_ctx E ->
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
  intros G ans E t [Htree Hans].
  split.
  - eapply plug_ok_tree_inv; eassumption.
  - exact Hans.
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
  ok_env G -> disj_only_ctx E ->
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
    ok_env G -> disj_only_ctx E ->
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
  ok_env G ->
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
    ok_env G -> disj_only_ctx E ->
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
  ok_env G -> ok_expr G (erase_marked (ans, shell)) ->
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
  ok_env G -> ok_expr G (erase_marked marked) ->
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
(** Induction over marked-tree position first reaches the selected path.
    Contextual trace lifting preserves the occurrence when answers distribute
    conjunction continuations; shell focusing restores its turn after those
    rearrangements. Once active, finite context depth bounds outward delay
    movement and release. Erasure projects the entire witness to ordinary
    reduction. No additional fairness premise is assumed. *)
Theorem global_no_stranding : forall G marked,
  ok_env G -> ok_expr G (erase_marked marked) ->
  exists out, tracked_finish G marked out.
Proof.
  intros G marked Henv Hok.
  apply (proj2 (tracked_finish_iff_eventually_active G marked)).
  exact (eventually_active G marked Henv Hok).
Qed.
