From MkRedex.Operational Require Import DelayTracking Scheduling Reduction WellFormed Delay DelayFairness.
From MkRedex.Language Require Import Scoping ScopedUnification Goals Substitution Environments Trees.
From Stdlib Require Import List Lia.
Import ListNotations.
Set Default Goal Selector "!".

From MkRedex.Language Require Import Solver.
Section WithSolver.
Context `{solver : Solver}.

(** Replace the distinguished delay occurrence by arbitrary work. Until the
    occurrence is selected, scheduler steps cannot inspect that work. *)
Fixpoint fill_mark (m : marked_tree) (work : tree) : tree :=
  match m with
  | mark_here _ => work
  | mark_under_delay m => tdelay (fill_mark m work)
  | mark_under_conj m g => tconj (fill_mark m work) g
  | mark_disjL_left m t => tdisjL (fill_mark m work) t
  | mark_disjL_right t m => tdisjL t (fill_mark m work)
  | mark_disjR_left m t => tdisjR (fill_mark m work) t
  | mark_disjR_right t m => tdisjR t (fill_mark m work)
  end.

Lemma bubble_active : forall G m m', marked_bubble G m m' -> active_mark m.
Proof. intros G m m' H. induction H; simpl; assumption || exact I. Qed.

(** A head step outside an inactive occurrence is parametric in its contents. *)
Lemma inactive_carry_head : forall G ans m m',
  marked_carry G (ans,m) (ans,m') -> ~ active_mark m ->
  (exists E r r', erase_mark m = plug E r /\ erase_mark m' = plug E r' /\ Head G r r') ->
  forall work, exists E r r',
    fill_mark m work = plug E r /\ fill_mark m' work = plug E r' /\ Head G r r'.
Proof.
  intros G ans m m' Hcarry. remember (ans,m) as p eqn:Ep in Hcarry.
  remember (ans,m') as q eqn:Eq in Hcarry.
  revert ans m m' Ep Eq.
  induction Hcarry; intros current source dest Ep Eq Hnot Hhead work;
    inversion Ep; inversion Eq; subst; simpl in Hnot |- *;
    try contradiction.
  - exfalso. apply Hnot. eapply bubble_active; eassumption.
  - destruct Hhead as [E [r [r' [Hs [Ht Hr]]]]].
    exfalso. destruct E; simpl in Hs; try discriminate.
    subst r. inversion Hr.
  - exists (cdisjL E (fill_mark m work)), r, r'. repeat split; assumption || reflexivity.
  - exists (cdisjR (fill_mark m work) E), r, r'. repeat split; assumption || reflexivity.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_assoc_ll.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_assoc_lr.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_assoc_rl.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_assoc_rr.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_delay_left.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_delay_right.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_prune_left.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_prune_right.
  - exfalso. apply (append_answer_changes_length current s). congruence.
  - exfalso. apply (append_answer_changes_length current s). congruence.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_delay_conj.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_left_ans_conj.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_right_ans_conj.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_delay_left.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_delay_right.
  - assert (Hinner : exists K a b, erase_mark m = plug K a /\ erase_mark m' = plug K b /\ Head G a b).
    { exists E, r, r'. repeat split; assumption. }
    destruct (IHHcarry current m m' eq_refl eq_refl Hnot Hinner work) as [K [a [b [Ha [Hb Hab]]]]].
    exists (cconj K g), a, b. simpl. rewrite Ha, Hb. repeat split; assumption || reflexivity.
  - assert (Hinner : exists K a b, erase_mark m = plug K a /\ erase_mark m' = plug K b /\ Head G a b).
    { exists E, r, r'. repeat split; assumption. }
    destruct (IHHcarry current m m' eq_refl eq_refl Hnot Hinner work) as [K [a [b [Ha [Hb Hab]]]]].
    exists (cdisjL K other), a, b. simpl. rewrite Ha, Hb. repeat split; assumption || reflexivity.
  - assert (Hinner : exists K a b, erase_mark m = plug K a /\ erase_mark m' = plug K b /\ Head G a b).
    { exists E, r, r'. repeat split; assumption. }
    destruct (IHHcarry current m m' eq_refl eq_refl Hnot Hinner work) as [K [a [b [Ha [Hb Hab]]]]].
    exists (cdisjR other K), a, b. simpl. rewrite Ha, Hb. repeat split; assumption || reflexivity.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_assoc_ll.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_assoc_lr.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_assoc_rl.
  - eexists chole. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. apply H_assoc_rr.
Qed.

Lemma active_mark_dec : forall m, {active_mark m} + {~ active_mark m}.
Proof. induction m; simpl; auto. Qed.

Lemma inactive_carry_fill : forall G ans m ans' m',
  marked_carry G (ans,m) (ans',m') -> ~ active_mark m -> forall work,
  step G (ans,fill_mark m work) (ans',fill_mark m' work).
Proof.
  intros G ans m ans' m' Hcarry Hnot work.
  destruct (marked_carry_cases G ans m ans' m' Hcarry)
    as [[-> Hhead]|[[inner [-> [-> ->]]]|[[s [inner [-> [-> ->]]]]|[s [inner [-> [-> ->]]]]]]].
  - destruct (inactive_carry_head G ans m m' Hcarry Hnot Hhead work)
      as [E [r [r' [Hs [Ht Hr]]]]].
    rewrite Hs, Ht. apply S_ctx. exact Hr.
  - apply S_delay.
  - apply S_promoteL.
  - apply S_promoteR.
Qed.

Fixpoint marked_goals (m : marked_tree) : list goal :=
  match m with
  | mark_here _ => []
  | mark_under_delay m => marked_goals m
  | mark_under_conj m g => marked_goals m ++ [g]
  | mark_disjL_left m _ | mark_disjL_right _ m
  | mark_disjR_left m _ | mark_disjR_right _ m => marked_goals m
  end.

Lemma inactive_carry_goals : forall G ans m ans' m',
  marked_carry G (ans,m) (ans',m') -> ~ active_mark m ->
  marked_goals m = marked_goals m'.
Proof.
  intros G ans m ans' m' Hcarry. remember (ans,m) as p eqn:Ep in Hcarry.
  remember (ans',m') as q eqn:Eq in Hcarry. revert ans m ans' m' Ep Eq.
  induction Hcarry; intros current source out dest Ep Eq Hnot;
    inversion Ep; inversion Eq; subst; simpl in Hnot |- *;
    try contradiction; try reflexivity.
  - exfalso. apply Hnot. eapply bubble_active; eassumption.
  - f_equal. eapply IHHcarry; reflexivity || exact Hnot.
  - eapply IHHcarry; reflexivity || exact Hnot.
  - eapply IHHcarry; reflexivity || exact Hnot.
Qed.

Lemma carry_until_active_fill : forall G start finish,
  carried_multi G start finish -> active_mark (snd finish) ->
  forall work, exists out target,
    multi G (fst start,fill_mark (snd start) work) (out,fill_mark target work) /\
    active_mark target /\ marked_goals (snd start) = marked_goals target.
Proof.
  intros G start finish Hrun. induction Hrun; intros Hactive work.
  - exists (fst m), (snd m). split; [constructor|]. split; [exact Hactive|reflexivity].
  - destruct (active_mark_dec (snd m)) as [Halready|Hnot].
    + exists (fst m), (snd m). split; [constructor|]. split; [exact Halready|reflexivity].
    + destruct (IHHrun Hactive work) as [out [target [Htail [Hact Hgoals]]]].
      exists out, target. split.
      * eapply multi_step; [|exact Htail].
        destruct m as [ans mark], m' as [ans' mark']; simpl in *.
        eapply inactive_carry_fill; eassumption.
      * split; [exact Hact|]. rewrite <- Hgoals.
        destruct m as [ans mark], m' as [ans' mark']; simpl in *.
        eapply inactive_carry_goals; eassumption.
Qed.

Theorem arbitrary_work_eventually_active : forall G ans m work,
  closed_env G -> ok_expr G (erase_marked (ans,m)) ->
  exists out target,
    multi G (ans,fill_mark m work) (out,fill_mark target work) /\
    active_mark target /\ marked_goals m = marked_goals target.
Proof.
  intros G ans m work Henv Hok.
  destruct (eventually_active G (ans,m) Henv Hok) as [target [Hrun Hactive]].
  exact (carry_until_active_fill G (ans,m) target Hrun Hactive work).
Qed.

Fixpoint remark (m : marked_tree) (work : tree) : marked_tree :=
  match m with
  | mark_here _ => mark_here work
  | mark_under_delay m => mark_under_delay (remark m work)
  | mark_under_conj m g => mark_under_conj (remark m work) g
  | mark_disjL_left m t => mark_disjL_left (remark m work) t
  | mark_disjL_right t m => mark_disjL_right t (remark m work)
  | mark_disjR_left m t => mark_disjR_left (remark m work) t
  | mark_disjR_right t m => mark_disjR_right t (remark m work)
  end.

Lemma remark_erase : forall m work, erase_mark (remark m work) = fill_mark m (tdelay work).
Proof. induction m; intros work; simpl; congruence. Qed.
Lemma remark_fill : forall m work t, fill_mark (remark m work) t = fill_mark m t.
Proof. induction m; intros work t0; simpl; congruence. Qed.
Lemma remark_goals : forall m work, marked_goals (remark m work) = marked_goals m.
Proof. induction m; intros work; simpl; congruence. Qed.

Lemma fill_delay_states : forall m work s,
  state_in (fill_mark m (tdelay work)) s <-> state_in (fill_mark m work) s.
Proof.
  induction m; intros work s; simpl; split; intro H; inversion H; subst;
    eauto using state_in.
  all: try solve [constructor; eapply IHm; eassumption].
  all: try solve [apply SI_tdisjL_l; eapply IHm; eassumption
    |apply SI_tdisjL_r; eapply IHm; eassumption
    |apply SI_tdisjR_l; eapply IHm; eassumption
    |apply SI_tdisjR_r; eapply IHm; eassumption].
Qed.

Lemma fill_delay_closed : forall m work G c,
  closed_tree G c (fill_mark m (tdelay work)) <-> closed_tree G c (fill_mark m work).
Proof. induction m; intros work G c; simpl; try tauto; specialize (IHm work G c); tauto. Qed.
Lemma fill_delay_acyclic : forall m work,
  acyclic_tree (fill_mark m (tdelay work)) <-> acyclic_tree (fill_mark m work).
Proof. induction m; intros work; simpl; try tauto; specialize (IHm work); tauto. Qed.
Lemma fill_delay_tight : forall m work G,
  tight_tree G (fill_mark m (tdelay work)) <-> tight_tree G (fill_mark m work).
Proof.
  induction m; intros work G; simpl; try tauto;
    try (specialize (IHm work G); tauto).
  rewrite IHm. split; intros [Ht Hcont]; split; [exact Ht| |exact Ht|].
  - intros s Hs. apply Hcont. apply (proj2 (fill_delay_states m work s)). exact Hs.
  - intros s Hs. apply Hcont. apply (proj1 (fill_delay_states m work s)). exact Hs.
Qed.
Lemma fill_delay_ok : forall G ans m work,
  ok_expr G (ans,fill_mark m work) -> ok_expr G (ans,fill_mark m (tdelay work)).
Proof.
  intros G ans m work [[c Hclosed] [Ht [Ha Hacyc]]].
  split; [exists c; apply fill_delay_closed; exact Hclosed|].
  split; [apply fill_delay_tight; exact Ht|].
  split; [exact Ha|apply fill_delay_acyclic; exact Hacyc].
Qed.

Theorem focus_work : forall G ans m work,
  closed_env G -> ok_expr G (ans,fill_mark m work) ->
  exists out target,
    multi G (ans,fill_mark m work) (out,fill_mark target work) /\
    active_mark target /\ marked_goals m = marked_goals target.
Proof.
  intros G ans m work Henv Hok.
  assert (Hmarked : ok_expr G (erase_marked (ans,remark m work))).
  { unfold erase_marked. simpl. rewrite remark_erase. apply fill_delay_ok. exact Hok. }
  destruct (arbitrary_work_eventually_active G ans (remark m work) work Henv Hmarked)
    as [out [target [Hrun [Hactive Hgoals]]]].
  rewrite remark_fill in Hrun. rewrite remark_goals in Hgoals.
  exists out, target. split; [exact Hrun|]. split; assumption.
Qed.

End WithSolver.
