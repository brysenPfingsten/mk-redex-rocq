From Stdlib Require Import Arith.Wf_nat.
From MkRedex.Operational Require Import DelayTracking Scheduling WellFormed Reduction Delay DelayFairness.
From MkRedex.Language Require Import Scoping ScopedUnification Goals Substitution Environments Trees Terms.
From Stdlib Require Import List Arith Lia.
From MkRedex.Denotational Require Import Denotation Opening Valuations Derivations.
From MkRedex.Execution Require Import Executable RunnerCorrespondence.
From MkRedex.Correctness Require Import Unification Focus Success Soundness.
Import ListNotations.
Set Default Goal Selector "!".

From MkRedex.Language Require Import Solver.
Section WithSolver.
Context `{solver : Solver}.

Definition initial_expr (counter : nat) (g : goal) : expr :=
  ([], tgoal g (mkstate [] counter)).

Lemma initial_expr_ok : forall G counter g,
  closed_goal G 0 counter g -> ok_expr G (initial_expr counter g).
Proof.
  intros G counter g Hgoal. unfold initial_expr, ok_expr. simpl.
  split.
  - exists counter. split; [apply Nat.le_refl|]. split; [exact Hgoal|exact I].
  - split.
    + split; [exact Hgoal|exact I].
    + split; [constructor|].
      intros x. constructor. intros y [t [Hlookup _]]. discriminate.

Qed.

(** Completeness specification. Its proof is [source_search_completeness]
    in [Completeness.v]. Query variables must already be allocated. *)
Definition reduction_complete (G : env) (counter : nat) (query : list nat)
  (g : goal) : Prop :=
  forall rho, solution G query g rho ->
  exists e answer,
    multi G (initial_expr counter g) e /\
    In answer (observed_answers e) /\ represents query answer rho.

Definition runner_complete (G : env) (Henv : closed_env G)
  (counter : nat) (query : list nat) (g : goal)
  (Hok : ok_expr G (initial_expr counter g)) : Prop :=
  forall rho, solution G query g rho ->
  exists fuel answer,
    In answer (observed_answers (run_steps G Henv fuel (initial_expr counter g) Hok)) /\
    represents query answer rho.

(** Transfer to the extracted runner needs no further fairness or
    unification argument. Used by [Completeness.v]. *)
Theorem reduction_completeness_transfers_to_runner : forall G Henv counter query g Hok,
  reduction_complete G counter query g -> runner_complete G Henv counter query g Hok.
Proof.
  intros G Henv counter query g Hok Hcomplete rho Hsolution.
  destruct (Hcomplete rho Hsolution) as [e [answer [Hrun [Hin Hrepr]]]].
  destruct (multi_run_steps G _ e Hrun Henv Hok) as [fuel Heq].
  exists fuel, answer. rewrite Heq. split; assumption.
Qed.

(** Full specification with scoping and query-allocation hypotheses.
    Proved in [Completeness.v], without adding axioms. *)
Definition source_search_complete : Prop :=
  forall G counter query g,
    closed_env G -> closed_goal G 0 counter g ->
    Forall (fun x => x < counter) query ->
    reduction_complete G counter query g.


Inductive pending (G : env) (rho : valuation) : nat -> list goal -> Prop :=
| pending_nil : pending G rho 0 []
| pending_cons : forall n m g gs,
    derives G rho n [] g -> pending G rho m gs ->
    pending G rho (1+n+m) (g::gs).

Lemma pending_agrees : forall G rho n gs,
  pending G rho n gs -> forall sigma c,
  closed_env G -> Forall (closed_goal G 0 c) gs -> agrees_below c rho sigma ->
  pending G sigma n gs.
Proof.
  intros G rho n gs H. induction H; intros sigma c Henv Hclosed Hagree.
  - constructor.
  - inversion Hclosed; subst. apply pending_cons.
    + eapply derives_agrees; eassumption.
    + eapply IHpending; eassumption.
Qed.

Lemma state_in_fill : forall m work s,
  state_in work s -> state_in (fill_mark m work) s.
Proof. induction m; intros work s H; simpl; eauto using state_in. Qed.

Lemma pending_goals_closed : forall G m work s,
  tight_tree G (fill_mark m work) -> state_in work s ->
  Forall (closed_goal G 0 (st_cnt s)) (marked_goals m).
Proof.
  intros G m. induction m; intros work s Htight Hstate; simpl in *.
  - constructor.
  - eapply IHm; eassumption.
  - destruct Htight as [Ht Hcont]. apply Forall_app. split.
    + eapply IHm; eassumption.
    + constructor; [apply Hcont; apply state_in_fill; exact Hstate|constructor].
  - eapply IHm; [exact (proj1 Htight)|exact Hstate].
  - eapply IHm; [exact (proj2 Htight)|exact Hstate].
  - eapply IHm; [exact (proj1 Htight)|exact Hstate].
  - eapply IHm; [exact (proj2 Htight)|exact Hstate].
Qed.

Definition finds (G : env) (rho : valuation) (c : nat) (start : expr) : Prop :=
  exists finish answer sigma,
    multi G start finish /\ In answer (observed_answers finish) /\
    satisfies_sub sigma (st_sub answer) /\ agrees_below c rho sigma.

Lemma finds_prefix : forall G rho c e e',
  multi G e e' -> finds G rho c e' -> finds G rho c e.
Proof.
  intros G rho c e e' Hrun [finish [answer [sigma [Htail Hrest]]]].
  exists finish,answer,sigma. split; [eapply multi_trans; eassumption|exact Hrest].
Qed.
Lemma finds_change : forall G rho sigma c d e,
  agrees_below c rho sigma -> c <= d -> finds G sigma d e -> finds G rho c e.
Proof.
  intros G rho sigma c d e Hagree Hle [finish [answer [tau [Hrun [Hin [Hmodel Htau]]]]]].
  exists finish,answer,tau. split; [exact Hrun|]. split; [exact Hin|].
  split; [exact Hmodel|]. intros x Hx. rewrite (Hagree x Hx). apply Htau. lia.
Qed.

Lemma active_goal_step : forall G ans m g s t,
  active_mark m -> Head G (tgoal g s) t ->
  step G (ans,fill_mark m (tgoal g s)) (ans,fill_mark m t).
Proof.
  intros G ans m g s t Hactive Hhead.
  destruct (active_fill_context m Hactive) as [E [He Hg]].
  rewrite !He. apply S_ctx. exact Hhead.
Qed.

(** Induct on total logical work in the current finite source derivation and
    its suspended continuations. First focus the chosen runtime work without
    changing that continuation list. Unification retains its ground model;
    fresh allocation extends the valuation only above the old counter;
    disjunction follows the source witness and conjunction pushes its right
    derivation. Success either becomes observable or consumes the next pending
    goal. Every recursive call decreases logical work, although the focusing
    prefixes need not have a uniform runtime bound. See docs/proofs.md. *)
Theorem pending_finds_answer : forall budget,
  forall G rho ans m g s,
  closed_env G -> ok_expr G (ans,fill_mark m (tgoal g s)) ->
  satisfies_sub rho (st_sub s) ->
  pending G rho budget (g::marked_goals m) ->
  finds G rho (st_cnt s) (ans,fill_mark m (tgoal g s)).
Proof.
  intro budget. pattern budget. apply (well_founded_induction lt_wf). clear budget. intros budget IH G rho ans m g s Henv Hok Hmodel Hp.
  destruct (focus_work G ans m (tgoal g s) Henv Hok)
    as [out [target [Hfocus [Hactive Hgoals]]]].
  apply (finds_prefix G rho (st_cnt s) _ _ Hfocus).
  assert (Hokfocus : ok_expr G (out,fill_mark target (tgoal g s))).
  { eapply multi_ok; eassumption. }
  rewrite Hgoals in Hp.
  destruct (active_fill_context target Hactive) as [E [He HEgoals]].
  assert (Htight : tight_tree G (fill_mark target (tgoal g s)))
    by exact (proj1 (proj2 Hokfocus)).
  assert (Hlocal : tight_tree G (tgoal g s)).
  { apply (plug_tight_inv G E). rewrite <- He. exact Htight. }
  assert (Hacyclic : acyclic_sub (st_sub s)).
  { apply (plug_acyclic_inv E (tgoal g s)). rewrite <- He.
    exact (proj2 (proj2 (proj2 Hokfocus))). }
  assert (Hcontinuations : Forall (closed_goal G 0 (st_cnt s)) (marked_goals target)).
  { eapply pending_goals_closed; [exact Htight|constructor]. }
  inversion Hp as [|n rest current gs Hd Htail Hcost Hshape]; subst current gs budget.
  inversion Hd; subst g n.
  - destruct (success_context G E s) as [u [Hrun [[Hnone Hready]|[h [gs [next [Hstack [Hu Hnext]]]]]]]].
    + destruct (ready_observed G out s u Hready) as [finish [Hfinish Hin]].
      exists finish,s,rho. split.
      * rewrite He. eapply multi_trans; [apply hsteps_multi; exact Hrun|exact Hfinish].
      * split; [exact Hin|]. split; [exact Hmodel|intros x Hx; reflexivity].
    + assert (Hrun' : multi G (out,fill_mark target (tgoal gsucc s))
          (out,fill_mark next (tgoal h s))).
      { rewrite He, <- Hu. apply hsteps_multi. exact Hrun. }
      apply (finds_prefix G rho (st_cnt s) _ _ Hrun').
      apply (IH rest ltac:(lia) G rho out next h s Henv).
      * eapply multi_ok; eassumption.
      * exact Hmodel.
      * rewrite Hnext. rewrite <- HEgoals, Hstack in Htail. exact Htail.
  - destruct Hlocal as [[Ht Hu] Hsub].
    destruct (Solve_ground_complete (st_cnt s) rho (st_sub s) t u v
      Hacyclic Hsub Ht Hu Hmodel H H0) as [s' [Hunify Hmodel']].
    set (state' := mkstate s' (st_cnt s)).
    assert (Hstep : step G (out,fill_mark target (tgoal (gunify t u) s))
      (out,fill_mark target (tgoal gsucc state'))).
    { apply active_goal_step; [exact Hactive|apply H_unify_ok; exact Hunify]. }
    apply (finds_prefix G rho (st_cnt s) _ _ (multi_step G _ _ _ Hstep (multi_refl G _))).
    apply (IH (1+0+rest) ltac:(lia) G rho out target gsucc state' Henv).
    + eapply step_ok; eassumption.
    + exact Hmodel'.
    + apply pending_cons; [constructor|exact Htail].
  - set (next := ctx_mark E (mark_disjL_left (mark_here tfail) (tgoal b s))).
    assert (Hstep : step G (out,fill_mark target (tgoal (gdisj a b) s))
      (out,fill_mark next (tgoal a s))).
    { unfold next. rewrite ctx_mark_fill, He. apply S_ctx. apply H_disj. }
    apply (finds_prefix G rho (st_cnt s) _ _ (multi_step G _ _ _ Hstep (multi_refl G _))).
    apply (IH (1+n0+rest) ltac:(lia) G rho out next a s Henv).
    + eapply step_ok; eassumption.
    + exact Hmodel.
    + apply pending_cons; [assumption|]. unfold next. rewrite ctx_mark_goals. simpl.
      rewrite HEgoals. exact Htail.
  - set (next := ctx_mark E (mark_disjL_right (tgoal a s) (mark_here tfail))).
    assert (Hstep : step G (out,fill_mark target (tgoal (gdisj a b) s))
      (out,fill_mark next (tgoal b s))).
    { unfold next. rewrite ctx_mark_fill, He. apply S_ctx. apply H_disj. }
    apply (finds_prefix G rho (st_cnt s) _ _ (multi_step G _ _ _ Hstep (multi_refl G _))).
    apply (IH (1+n0+rest) ltac:(lia) G rho out next b s Henv).
    + eapply step_ok; eassumption.
    + exact Hmodel.
    + apply pending_cons; [assumption|]. unfold next. rewrite ctx_mark_goals. simpl.
      rewrite HEgoals. exact Htail.
  - set (next := ctx_mark E (mark_under_conj (mark_here tfail) b)).
    assert (Hstep : step G (out,fill_mark target (tgoal (gconj a b) s))
      (out,fill_mark next (tgoal a s))).
    { unfold next. rewrite ctx_mark_fill, He. apply S_ctx. apply H_conj. }
    apply (finds_prefix G rho (st_cnt s) _ _ (multi_step G _ _ _ Hstep (multi_refl G _))).
    apply (IH (1+n0+(1+m0+rest)) ltac:(lia) G rho out next a s Henv).
    + eapply step_ok; eassumption.
    + exact Hmodel.
    + apply pending_cons; [exact H|]. unfold next. rewrite ctx_mark_goals. simpl.
      rewrite HEgoals. apply pending_cons; assumption.
  - set (sigma := extend_valuation rho (st_cnt s) values).
    set (args := map tvar (seq (st_cnt s) k)).
    set (state' := mkstate (st_sub s) (st_cnt s+k)).
    pose proof (extend_valuation_old rho (st_cnt s) values) as Hagree.
    destruct Hlocal as [Hbody Hsub]. simpl in Hbody.
    assert (Hmodel' : satisfies_sub sigma (st_sub s)).
    { eapply satisfies_sub_agrees; eassumption. }
    assert (Hargs : runtime_open_args (st_cnt s+k) args).
    { apply fresh_args_open_args. reflexivity. }
    assert (Heval : eval_terms sigma [] args = Some values).
    { unfold args. rewrite <- H. apply eval_fresh_block. }
    assert (Hopened : derives G sigma n0 [] (open args body)).
    { eapply derives_open; [exact Hargs|exact Heval|].
      rewrite app_nil_r in H0. eapply derives_agrees; eassumption. }
    assert (Hstep : step G (out,fill_mark target (tgoal (gfresh k body) s))
      (out,fill_mark target (tgoal (open args body) state'))).
    { apply active_goal_step; [exact Hactive|apply H_fresh]. }
    apply (finds_prefix G rho (st_cnt s) _ _ (multi_step G _ _ _ Hstep (multi_refl G _))).
    apply (finds_change G rho sigma (st_cnt s) (st_cnt state') _ Hagree ltac:(simpl;lia)).
    apply (IH (1+n0+rest) ltac:(lia) G sigma out target (open args body) state' Henv).
    + eapply step_ok; eassumption.
    + exact Hmodel'.
    + apply pending_cons; [exact Hopened|]. eapply pending_agrees; eassumption.
  - set (delayed := ctx_mark E (mark_under_delay (mark_here tfail))).
    assert (Hcall : step G (out,fill_mark target (tgoal (grelcall r args) s))
      (out,fill_mark delayed (tproceed r args s))).
    { unfold delayed. rewrite ctx_mark_fill, He. apply S_ctx. apply H_relcall. }
    assert (Hokcall : ok_expr G (out,fill_mark delayed (tproceed r args s))).
    { eapply step_ok; eassumption. }
    destruct (focus_work G out delayed (tproceed r args s) Henv Hokcall)
      as [called [selected [Hscheduled [Hselected Hstack]]]].
    assert (Hokselected : ok_expr G (called,fill_mark selected (tproceed r args s))).
    { eapply multi_ok; eassumption. }
    destruct (active_fill_context selected Hselected) as [K [HK HKgoals]].
    assert (Hproceed : step G (called,fill_mark selected (tproceed r args s))
      (called,fill_mark selected (tgoal (open args body) s))).
    { rewrite !HK. apply S_ctx. eapply H_proceed; eassumption. }
    assert (Hargs : runtime_open_args (st_cnt s) args).
    { apply (closed_goal_relcall_open_args G (st_cnt s) r args). exact (proj1 Hlocal). }
    assert (Hopened : derives G rho n0 [] (open args body)).
    { eapply derives_open; eassumption. }
    apply (finds_prefix G rho (st_cnt s) _ _ (multi_step G _ _ _ Hcall (multi_refl G _))).
    apply (finds_prefix G rho (st_cnt s) _ _ Hscheduled).
    apply (finds_prefix G rho (st_cnt s) _ _ (multi_step G _ _ _ Hproceed (multi_refl G _))).
    apply (IH (1+n0+rest) ltac:(lia) G rho called selected (open args body) s Henv).
    + eapply step_ok; eassumption.
    + exact Hmodel.
    + apply pending_cons; [exact Hopened|].
      unfold delayed in Hstack. rewrite ctx_mark_goals in Hstack. simpl in Hstack.
      rewrite <- Hstack, HEgoals. exact Htail.
Qed.

Theorem source_search_completeness : source_search_complete.
Proof.
  intros G counter query g Henv Hclosed Hquery rho [sigma [Hquery_agree Hsat]].
  destruct (satisfaction_derives G sigma [] g Hsat) as [n Hderive].
  assert (Hp : pending G sigma (1+n+0) [g]).
  { apply pending_cons; [exact Hderive|constructor]. }
  pose proof (pending_finds_answer (1+n+0) G sigma [] (mark_here tfail) g
    (mkstate [] counter) Henv (initial_expr_ok G counter g Hclosed)
    (satisfies_sub_nil sigma) Hp) as Hfinds.
  destruct Hfinds as [finish [answer [tau [Hrun [Hin [Hmodel Hagree]]]]]].
  exists finish,answer. split; [exact Hrun|]. split; [exact Hin|].
  exists tau. split; [|exact Hmodel]. intros x Hx.
  rewrite <- (Hagree x).
  - apply Hquery_agree. exact Hx.
  - rewrite Forall_forall in Hquery. exact (Hquery x Hx).
Qed.

Corollary executable_search_completeness : forall G Henv counter query g
  (Hclosed : closed_goal G 0 counter g)
  (Hquery : Forall (fun x => x < counter) query),
  runner_complete G Henv counter query g (initial_expr_ok G counter g Hclosed).
Proof.
  intros G Henv counter query g Hclosed Hquery.
  apply reduction_completeness_transfers_to_runner.
  apply source_search_completeness; assumption.
Qed.

(** The executable finds exactly the ground source solutions, with answers
    compared only on the original, already allocated query variables. *)
Theorem source_solution_iff_runner_answer : forall G Henv counter query g
  (Hclosed : closed_goal G 0 counter g)
  (Hquery : Forall (fun x => x < counter) query) rho,
  solution G query g rho <->
  exists fuel answer,
    In answer (observed_answers
      (run_steps G Henv fuel (initial_expr counter g) (initial_expr_ok G counter g Hclosed))) /\
    represents query answer rho.
Proof.
  intros G Henv counter query g Hclosed Hquery rho. split.
  - apply (executable_search_completeness G Henv counter query g Hclosed Hquery).
  - intros [fuel [answer [Hin Hrepr]]].
    eapply executable_search_soundness; eassumption.
Qed.

End WithSolver.
