From Stdlib Require Import List Arith Lia.
Import ListNotations.
From MkRedex.Language Require Import Terms Goals Environments Trees.
From MkRedex.Semantics Require Import Reduction WellFormed Determinism.
Set Default Goal Selector "!".

(** [compose_ctx outer inner] puts [inner] in the hole of [outer]. *)
Fixpoint compose_ctx (outer inner : ctx) : ctx :=
  match outer with
  | chole => inner
  | cdisjL E other => cdisjL (compose_ctx E inner) other
  | cdisjR other E => cdisjR other (compose_ctx E inner)
  | cconj E g => cconj (compose_ctx E inner) g
  end.

Lemma plug_compose : forall outer inner t,
  plug (compose_ctx outer inner) t = plug outer (plug inner t).
Proof.
  intros outer inner t. induction outer; simpl;
    try rewrite IHouter; reflexivity.
Qed.

Fixpoint ctx_depth (E : ctx) : nat :=
  match E with
  | chole => 0
  | cdisjL E _ | cdisjR _ E | cconj E _ => S (ctx_depth E)
  end.

Lemma ctx_depth_compose : forall outer inner,
  ctx_depth (compose_ctx outer inner) =
  ctx_depth outer + ctx_depth inner.
Proof.
  induction outer; intros inner; simpl; try rewrite IHouter; lia.
Qed.

(** This is the tree placed under the delay after it bubbles to the root.
    A disjunction changes its active side as the delay rotates out. *)
Fixpoint delay_payload (E : ctx) (t : tree) : tree :=
  match E with
  | chole => t
  | cdisjL E other => tdisjR (delay_payload E t) other
  | cdisjR other E => tdisjL other (delay_payload E t)
  | cconj E g => tconj (delay_payload E t) g
  end.

(** Exact length, so the theorem below gives a concrete scheduling bound. *)
Inductive steps_n (G : env) : nat -> expr -> expr -> Prop :=
  | steps_n_zero : forall e, steps_n G 0 e e
  | steps_n_succ : forall n e1 e2 e3,
      G |= e1 --> e2 -> steps_n G n e2 e3 ->
      steps_n G (S n) e1 e3.

Lemma steps_n_plus : forall G m n e1 e2 e3,
  steps_n G m e1 e2 -> steps_n G n e2 e3 ->
  steps_n G (m + n) e1 e3.
Proof.
  intros G m n e1 e2 e3 Hfirst Hsecond.
  induction Hfirst; simpl; [exact Hsecond |].
  eapply steps_n_succ; eauto.
Qed.

Lemma steps_n_multi : forall G n e e',
  steps_n G n e e' -> multi G e e'.
Proof.
  intros G n e e' Hsteps. induction Hsteps.
  - constructor.
  - eapply multi_step; eassumption.
Qed.

Lemma steps_n_deterministic : forall G n e e1 e2,
  steps_n G n e e1 -> steps_n G n e e2 -> e1 = e2.
Proof.
  intros G n e e1 target Hfirst. revert target.
  induction Hfirst as [e|n a b c Hstep Htail IH]; intros target Hsecond.
  - inversion Hsecond. reflexivity.
  - inversion Hsecond as [|n' a' b' c' Hstep' Htail']; subst.
    assert (Heq : b = b') by (eapply step_deterministic; eassumption).
    subst b'. exact (IH _ Htail').
Qed.

(** An exposed delay crosses exactly one evaluation-context frame per
    head step.  [outer] lets the induction lift each move through all
    frames that have not yet been crossed. *)
Theorem delay_bubbles_in_context : forall G ans E outer t,
  steps_n G (ctx_depth E)
    (ans, plug outer (plug E (tdelay t)))
    (ans, plug outer (tdelay (delay_payload E t))).
Proof.
  intros G ans E. induction E; intros outer body; simpl.
  - constructor.
  - replace (S (ctx_depth E)) with (ctx_depth E + 1) by lia.
    specialize (IHE (compose_ctx outer (cdisjL chole t)) body).
    repeat rewrite plug_compose in IHE. simpl in IHE.
    eapply steps_n_plus; [exact IHE |].
    eapply steps_n_succ.
    + apply S_ctx with (E := outer). apply H_delay_left.
    + constructor.
  - replace (S (ctx_depth E)) with (ctx_depth E + 1) by lia.
    specialize (IHE (compose_ctx outer (cdisjR t chole)) body).
    repeat rewrite plug_compose in IHE. simpl in IHE.
    eapply steps_n_plus; [exact IHE |].
    eapply steps_n_succ.
    + apply S_ctx with (E := outer). apply H_delay_right.
    + constructor.
  - replace (S (ctx_depth E)) with (ctx_depth E + 1) by lia.
    specialize (IHE (compose_ctx outer (cconj chole g)) body).
    repeat rewrite plug_compose in IHE. simpl in IHE.
    eapply steps_n_plus; [exact IHE |].
    eapply steps_n_succ.
    + apply S_ctx with (E := outer). apply H_delay_conj.
    + constructor.
Qed.

Corollary active_delay_released : forall G ans E t,
  steps_n G (S (ctx_depth E))
    (ans, plug E (tdelay t))
    (ans, delay_payload E t).
Proof.
  intros G ans E t.
  replace (S (ctx_depth E)) with (ctx_depth E + 1) by lia.
  eapply steps_n_plus.
  - exact (delay_bubbles_in_context G ans E chole t).
  - eapply steps_n_succ.
    + apply S_delay.
    + constructor.
Qed.

Corollary active_delay_eventually_scheduled : forall G ans E t,
  multi G (ans, plug E (tdelay t))
    (ans, delay_payload E t).
Proof.
  intros G ans E t.
  eapply steps_n_multi. apply active_delay_released.
Qed.

(** Determinism rules out a competing schedule that postpones this
    exposed delay.  This theorem does not claim that a delay in an
    inactive branch is already exposed. *)
Corollary active_delay_forced : forall G ans E t e',
  steps_n G (S (ctx_depth E)) (ans, plug E (tdelay t)) e' ->
  e' = (ans, delay_payload E t).
Proof.
  intros G ans E t e' Hsteps.
  eapply steps_n_deterministic.
  - exact Hsteps.
  - apply active_delay_released.
Qed.

(** A relation call first creates a delay, which then crosses the active
    context and is released.  The continuation may be on the suspended
    side of a disjunction after the rotation, as intended by the search
    scheduler. *)
Corollary relation_call_delay_released : forall G ans E r ts s,
  steps_n G (S (S (ctx_depth E)))
    (ans, plug E (tgoal (grelcall r ts) s))
    (ans, delay_payload E (tproceed r ts s)).
Proof.
  intros G ans E r ts s.
  eapply steps_n_succ.
  - apply S_ctx with (E := E). apply H_relcall.
  - apply active_delay_released.
Qed.

(** Once the currently selected branch exposes a delay, the two
    disjunction rules rotate it away and select the waiting branch. *)
Theorem delay_handoff_left : forall G ans E t waiting,
  steps_n G (S (S (ctx_depth E)))
    (ans, tdisjL (plug E (tdelay t)) waiting)
    (ans, tdisjR (delay_payload E t) waiting).
Proof.
  intros G ans E t waiting.
  replace (S (S (ctx_depth E))) with (ctx_depth E + 2) by lia.
  eapply steps_n_plus.
  - exact (delay_bubbles_in_context G ans E (cdisjL chole waiting) t).
  - eapply steps_n_succ.
    + apply S_ctx with (E := chole). apply H_delay_left.
    + eapply steps_n_succ.
      * apply S_delay.
      * constructor.
Qed.

Theorem delay_handoff_right : forall G ans E t waiting,
  steps_n G (S (S (ctx_depth E)))
    (ans, tdisjR waiting (plug E (tdelay t)))
    (ans, tdisjL waiting (delay_payload E t)).
Proof.
  intros G ans E t waiting.
  replace (S (S (ctx_depth E))) with (ctx_depth E + 2) by lia.
  eapply steps_n_plus.
  - exact (delay_bubbles_in_context G ans E (cdisjR waiting chole) t).
  - eapply steps_n_succ.
    + apply S_ctx with (E := chole). apply H_delay_right.
    + eapply steps_n_succ.
      * apply S_delay.
      * constructor.
Qed.

(** Work until the next delay reaches the root.  [tproceed] can unfold an
    arbitrarily large relation body, so its count is the first component
    of a lexicographic measure.  The weighted second component pays for
    administrative reassociation and continuation distribution.  Work
    under a delay is omitted because reaching that delay ends the burst. *)
Fixpoint goal_work (g : goal) : nat :=
  match g with
  | gsucc => 1
  | gunify _ _ | grelcall _ _ => 2
  | gdisj g1 g2 => 2 * goal_work g1 + goal_work g2 + 2
  | gconj g1 g2 => (goal_work g2 + 3) * goal_work g1 + 2
  | gfresh _ g' => S (goal_work g')
  end.

Lemma goal_work_positive : forall g, 0 < goal_work g.
Proof.
  induction g; simpl; nia.
Qed.

Lemma goal_work_open_goal : forall d args g,
  goal_work (open_goal d args g) = goal_work g.
Proof.
  intros d args g. revert d.
  induction g; intros d; simpl; try reflexivity;
    try rewrite IHg1, IHg2; try rewrite IHg; reflexivity.
Qed.

Fixpoint proceed_count (t : tree) : nat :=
  match t with
  | tfail | tgoal _ _ | tdelay _ => 0
  | tproceed _ _ _ => 1
  | tconj t' _ => proceed_count t'
  | tdisjL t1 t2 | tdisjR t1 t2 => proceed_count t1 + proceed_count t2
  end.

Fixpoint tree_work (t : tree) : nat :=
  match t with
  | tfail => 1
  | tgoal g _ => goal_work g
  | tdelay _ => 0
  | tproceed _ _ _ => 1
  | tconj t' g => (goal_work g + 3) * tree_work t' + 1
  | tdisjL t1 t2 => 2 * tree_work t1 + tree_work t2 + 1
  | tdisjR t1 t2 => tree_work t1 + 2 * tree_work t2 + 1
  end.

Lemma Head_burst_decreases : forall G r r',
  Head G r r' ->
  proceed_count r' < proceed_count r \/
  (proceed_count r' = proceed_count r /\ tree_work r' < tree_work r).
Proof.
  intros G r r' Hhead. destruct Hhead; simpl;
    try rewrite goal_work_open_goal;
    try pose proof (goal_work_positive g);
    try (right; split; [lia | nia]);
    try (left; lia).
  - right. split; [reflexivity |].
    unfold open. rewrite goal_work_open_goal. lia.
  - destruct (proceed_count r2) eqn:Hcount.
    + right. split; lia.
    + left. lia.
  - destruct (proceed_count r2) eqn:Hcount.
    + right. split; lia.
    + left. lia.
Qed.

Lemma plug_burst_decreases : forall E r r',
  (proceed_count r' < proceed_count r \/
   (proceed_count r' = proceed_count r /\ tree_work r' < tree_work r)) ->
  proceed_count (plug E r') < proceed_count (plug E r) \/
  (proceed_count (plug E r') = proceed_count (plug E r) /\
   tree_work (plug E r') < tree_work (plug E r)).
Proof.
  induction E; intros r r' Hdec; simpl; [exact Hdec |..];
    specialize (IHE r r' Hdec);
    destruct IHE as [Hcount | [Hcount Hwork]];
    try pose proof (goal_work_positive g);
    [left | right | left | right | left | right];
    try split; nia.
Qed.

Lemma step_before_root_delay_decreases : forall G e e',
  G |= e --> e' ->
  (forall t, snd e <> tdelay t) ->
  lex_count_size
    (proceed_count (snd e'), tree_work (snd e'))
    (proceed_count (snd e), tree_work (snd e)).
Proof.
  intros G e e' Hstep Hnotdelay.
  destruct Hstep; unfold lex_count_size; simpl.
  - exact (plug_burst_decreases E r r' (Head_burst_decreases G r r' H)).
  - exfalso. eapply Hnotdelay. reflexivity.
  - right. simpl. split; lia.
  - right. simpl. split; lia.
Qed.

Definition burst_end (e : expr) : Prop :=
  is_value e \/ exists t, snd e = tdelay t.

Lemma burst_end_dec : forall e, {burst_end e} + {~ burst_end e}.
Proof.
  intros [ans t]. unfold burst_end.
  destruct t;
    try (right; intros [Hvalue | [body Hdelay]];
      [simpl in Hvalue; contradiction | discriminate Hdelay]).
  - left. left. exact I.
  - destruct g;
      try (right; intros [Hvalue | [body Hdelay]];
        [simpl in Hvalue; contradiction | discriminate Hdelay]).
    left. left. exact I.
  - left. right. eexists. reflexivity.
Qed.

(** A burst stops before any root [S_delay] step. *)
Inductive burst_steps (G : env) : expr -> expr -> Prop :=
  | burst_stop : forall e, burst_steps G e e
  | burst_next : forall e1 e2 e3,
      (forall t, snd e1 <> tdelay t) ->
      G |= e1 --> e2 -> burst_steps G e2 e3 ->
      burst_steps G e1 e3.

Lemma burst_steps_multi : forall G e e',
  burst_steps G e e' -> multi G e e'.
Proof.
  intros G e e' Hburst. induction Hburst.
  - constructor.
  - eapply multi_step; eassumption.
Qed.

(** Between two root-delay releases there is only a finite burst of
    ordinary work.  A recursive relation call introduces another delay
    before its body is unfolded again. *)
Theorem finite_burst_marked : forall G e,
  closed_env G -> ok_expr G e ->
  exists e', burst_steps G e e' /\ burst_end e'.
Proof.
  intros G e Henv Hok.
  set (measure := fun e : expr =>
    (proceed_count (snd e), tree_work (snd e))).
  assert (Hmain : forall m, forall e,
    measure e = m -> ok_expr G e ->
    exists e', burst_steps G e e' /\ burst_end e').
  { apply (well_founded_induction lex_count_size_wf
      (fun m => forall e, measure e = m -> ok_expr G e ->
        exists e', burst_steps G e e' /\ burst_end e')).
    intros m IH current Hmeasure Hcurrent.
    destruct (burst_end_dec current) as [Hend | Hnotend].
    - exists current. split; [constructor | exact Hend].
    - destruct (progress G current Hcurrent) as [Hvalue | [next Hstep]].
      + exfalso. apply Hnotend. left. exact Hvalue.
      + assert (Hnotdelay : forall t, snd current <> tdelay t).
        { intros t Heq. apply Hnotend. right. exists t. exact Heq. }
        pose proof (step_before_root_delay_decreases G current next
          Hstep Hnotdelay) as Hless.
        change (lex_count_size (measure next) (measure current)) in Hless.
        rewrite Hmeasure in Hless.
        destruct (IH (measure next) Hless next eq_refl
          (step_ok G current next Henv Hcurrent Hstep))
          as [outcome [Htail Hend]].
        exists outcome. split.
        * eapply burst_next; eassumption.
        * exact Hend.
  }
  exact (Hmain (measure e) e eq_refl Hok).
Qed.

Corollary finite_burst : forall G e,
  closed_env G -> ok_expr G e ->
  exists e', multi G e e' /\ burst_end e'.
Proof.
  intros G e Henv Hok.
  destruct (finite_burst_marked G e Henv Hok) as [e' [Hburst Hend]].
  exists e'. split; [exact (burst_steps_multi G e e' Hburst) | exact Hend].
Qed.

Lemma multi_trans : forall G e1 e2 e3,
  multi G e1 e2 -> multi G e2 e3 -> multi G e1 e3.
Proof.
  intros G e1 e2 target Hfirst. revert target.
  induction Hfirst; intros target Hsecond; [exact Hsecond |].
  eapply multi_step.
  - eassumption.
  - apply IHHfirst. exact Hsecond.
Qed.

Lemma burst_step_lift_left : forall G ans active ans' next waiting,
  G |= (ans, active) --> (ans', next) ->
  (forall t, active <> tdelay t) ->
  multi G (ans, tdisjL active waiting)
          (ans', tdisjL next waiting).
Proof.
  intros G ans active ans' next waiting Hstep Hnotdelay.
  inversion Hstep; subst; clear Hstep.
  - eapply multi_step.
    + eapply S_ctx with (E := cdisjL E waiting). eassumption.
    + constructor.
  - exfalso. eapply Hnotdelay. reflexivity.
  - eapply multi_step with
      (e2 := (ans, tdisjL (tgoal gsucc s) (tdisjL next waiting))).
    + apply S_ctx with (E := chole). apply H_assoc_ll.
    + eapply multi_step.
      * apply S_promoteL.
      * constructor.
  - eapply multi_step with
      (e2 := (ans, tdisjR (tdisjL next waiting) (tgoal gsucc s))).
    + apply S_ctx with (E := chole). apply H_assoc_lr.
    + eapply multi_step.
      * apply S_promoteR.
      * constructor.
Qed.

Lemma burst_step_lift_right : forall G ans active ans' next waiting,
  G |= (ans, active) --> (ans', next) ->
  (forall t, active <> tdelay t) ->
  multi G (ans, tdisjR waiting active)
          (ans', tdisjR waiting next).
Proof.
  intros G ans active ans' next waiting Hstep Hnotdelay.
  inversion Hstep; subst; clear Hstep.
  - eapply multi_step.
    + eapply S_ctx with (E := cdisjR waiting E). eassumption.
    + constructor.
  - exfalso. eapply Hnotdelay. reflexivity.
  - eapply multi_step with
      (e2 := (ans, tdisjL (tgoal gsucc s) (tdisjR waiting next))).
    + apply S_ctx with (E := chole). apply H_assoc_rl.
    + eapply multi_step.
      * apply S_promoteL.
      * constructor.
  - eapply multi_step with
      (e2 := (ans, tdisjR (tdisjR waiting next) (tgoal gsucc s))).
    + apply S_ctx with (E := chole). apply H_assoc_rr.
    + eapply multi_step.
      * apply S_promoteR.
      * constructor.
Qed.

Lemma burst_lift_left : forall G e e' waiting,
  burst_steps G e e' ->
  multi G (fst e, tdisjL (snd e) waiting)
          (fst e', tdisjL (snd e') waiting).
Proof.
  intros G e e' waiting Hburst. induction Hburst.
  - constructor.
  - destruct e1 as [ans active], e2 as [ans' next]. simpl in *.
    eapply multi_trans.
    + eapply burst_step_lift_left; eassumption.
    + exact IHHburst.
Qed.

Lemma burst_lift_right : forall G e e' waiting,
  burst_steps G e e' ->
  multi G (fst e, tdisjR waiting (snd e))
          (fst e', tdisjR waiting (snd e')).
Proof.
  intros G e e' waiting Hburst. induction Hburst.
  - constructor.
  - destruct e1 as [ans active], e2 as [ans' next]. simpl in *.
    eapply multi_trans.
    + eapply burst_step_lift_right; eassumption.
    + exact IHHburst.
Qed.

(** Even if the other branch performs arbitrarily much finite work, it
    must eventually yield or terminate.  The waiting sibling then becomes
    the selected branch. *)
Theorem waiting_branch_selected_left : forall G ans active waiting,
  closed_env G -> ok_expr G (ans, active) ->
  exists ans' E,
    multi G (ans, tdisjL active waiting) (ans', plug E waiting).
Proof.
  intros G ans active waiting Henv Hok.
  destruct (finite_burst_marked G (ans, active) Henv Hok)
    as [[out yielded] [Hburst Hend]].
  pose proof (burst_lift_left G (ans, active) (out, yielded)
    waiting Hburst) as Hlift.
  simpl in Hlift.
  destruct Hend as [Hvalue | [body Hdelay]].
  - destruct yielded; simpl in Hvalue; try contradiction.
    + exists out, chole. simpl.
      eapply multi_trans; [exact Hlift |].
      eapply multi_step; [apply S_ctx with (E := chole); apply H_prune_left | constructor].
    + destruct g; try contradiction.
      exists (out ++ [s]), chole. simpl.
      eapply multi_trans; [exact Hlift |].
      eapply multi_step; [apply S_promoteL | constructor].
  - simpl in Hdelay. subst yielded. exists out, (cdisjR body chole). simpl.
    eapply multi_trans; [exact Hlift |].
    eapply steps_n_multi.
    exact (delay_handoff_left G out chole body waiting).
Qed.

Theorem waiting_branch_selected_right : forall G ans active waiting,
  closed_env G -> ok_expr G (ans, active) ->
  exists ans' E,
    multi G (ans, tdisjR waiting active) (ans', plug E waiting).
Proof.
  intros G ans active waiting Henv Hok.
  destruct (finite_burst_marked G (ans, active) Henv Hok)
    as [[out yielded] [Hburst Hend]].
  pose proof (burst_lift_right G (ans, active) (out, yielded)
    waiting Hburst) as Hlift.
  simpl in Hlift.
  destruct Hend as [Hvalue | [body Hdelay]].
  - destruct yielded; simpl in Hvalue; try contradiction.
    + exists out, chole. simpl.
      eapply multi_trans; [exact Hlift |].
      eapply multi_step; [apply S_ctx with (E := chole); apply H_prune_right | constructor].
    + destruct g; try contradiction.
      exists (out ++ [s]), chole. simpl.
      eapply multi_trans; [exact Hlift |].
      eapply multi_step; [apply S_promoteR | constructor].
  - simpl in Hdelay. subst yielded. exists out, (cdisjL chole body). simpl.
    eapply multi_trans; [exact Hlift |].
    eapply steps_n_multi.
    exact (delay_handoff_right G out chole body waiting).
Qed.

Lemma ok_expr_disjL_left : forall G ans active waiting,
  ok_expr G (ans, tdisjL active waiting) -> ok_expr G (ans, active).
Proof.
  intros G ans active waiting [[c Hclosed] [Htight [Hans Hacyclic]]].
  simpl in Hclosed, Htight, Hacyclic.
  repeat split.
  - exists c. exact (proj1 Hclosed).
  - exact (proj1 Htight).
  - exact Hans.
  - exact (proj1 Hacyclic).
Qed.

Lemma ok_expr_disjR_right : forall G ans waiting active,
  ok_expr G (ans, tdisjR waiting active) -> ok_expr G (ans, active).
Proof.
  intros G ans waiting active [[c Hclosed] [Htight [Hans Hacyclic]]].
  simpl in Hclosed, Htight, Hacyclic.
  repeat split.
  - exists c. exact (proj2 Hclosed).
  - exact (proj2 Htight).
  - exact Hans.
  - exact (proj2 Hacyclic).
Qed.

(** A delay waiting as the other immediate disjunct is eventually
    released, regardless of how many finite steps the selected branch
    needs before its next yield. *)
Theorem waiting_delay_released_left : forall G ans active E t,
  closed_env G ->
  ok_expr G (ans, tdisjL active (plug E (tdelay t))) ->
  exists ans' F,
    multi G (ans, tdisjL active (plug E (tdelay t)))
            (ans', delay_payload F t).
Proof.
  intros G ans active E t Henv Hok.
  destruct (waiting_branch_selected_left G ans active
    (plug E (tdelay t)) Henv
    (ok_expr_disjL_left G ans active (plug E (tdelay t)) Hok))
    as [ans' [F Hselected]].
  exists ans', (compose_ctx F E).
  eapply multi_trans with
    (e2 := (ans', plug (compose_ctx F E) (tdelay t))).
  - rewrite plug_compose. exact Hselected.
  - apply active_delay_eventually_scheduled.
Qed.

Theorem waiting_delay_released_right : forall G ans active E t,
  closed_env G ->
  ok_expr G (ans, tdisjR (plug E (tdelay t)) active) ->
  exists ans' F,
    multi G (ans, tdisjR (plug E (tdelay t)) active)
            (ans', delay_payload F t).
Proof.
  intros G ans active E t Henv Hok.
  destruct (waiting_branch_selected_right G ans active
    (plug E (tdelay t)) Henv
    (ok_expr_disjR_right G ans (plug E (tdelay t)) active Hok))
    as [ans' [F Hselected]].
  exists ans', (compose_ctx F E).
  eapply multi_trans with
    (e2 := (ans', plug (compose_ctx F E) (tdelay t))).
  - rewrite plug_compose. exact Hselected.
  - apply active_delay_eventually_scheduled.
Qed.
