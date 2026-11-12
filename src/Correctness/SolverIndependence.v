From Stdlib Require Import List.
From MkRedex.Language Require Import Terms Goals Substitution Trees Scoping Solver Environments.
From MkRedex.Denotational Require Import Denotation.
From MkRedex.Correctness Require Import GroundUnification.
From MkRedex.Operational Require Import Reduction WellFormed Determinism.
From MkRedex.Execution Require Import Executable RunnerCorrespondence Interface.
Import ListNotations.
Set Default Goal Selector "!".

Definition sub_equiv (a b : sub) : Prop :=
  forall rho, satisfies_sub rho a <-> satisfies_sub rho b.
Definition state_equiv (a b : state) : Prop :=
  st_cnt a = st_cnt b /\ sub_equiv (st_sub a) (st_sub b).

Inductive tree_equiv : tree -> tree -> Prop :=
| EQ_fail : tree_equiv tfail tfail
| EQ_goal : forall g a b, state_equiv a b -> tree_equiv (tgoal g a) (tgoal g b)
| EQ_proceed : forall r args a b, state_equiv a b ->
    tree_equiv (tproceed r args a) (tproceed r args b)
| EQ_delay : forall a b, tree_equiv a b -> tree_equiv (tdelay a) (tdelay b)
| EQ_conj : forall a b g, tree_equiv a b -> tree_equiv (tconj a g) (tconj b g)
| EQ_disjL : forall a b c d, tree_equiv a b -> tree_equiv c d ->
    tree_equiv (tdisjL a c) (tdisjL b d)
| EQ_disjR : forall a b c d, tree_equiv a b -> tree_equiv c d ->
    tree_equiv (tdisjR a c) (tdisjR b d).

Definition expr_equiv (a b : expr) : Prop :=
  Forall2 state_equiv (fst a) (fst b) /\ tree_equiv (snd a) (snd b).

Definition outcome_equiv (a b : option sub) : Prop :=
  match a,b with
  | None,None => True
  | Some a,Some b => sub_equiv a b
  | _,_ => False
  end.

Lemma solver_outcomes_equiv : forall (left right : Solver) c t u a b result,
  valid_unification c a t u -> valid_unification c b t u -> sub_equiv a b ->
  @Solve left c t u a result ->
  exists other, @Solve right c t u b other /\ outcome_equiv result other.
Proof.
  intros left right c t u a b result Ha Hb Heq Hleft.
  destruct (@solve_cert right c b t u Hb) as [other Hright].
  exists other. split; [exact Hright|].
  pose proof (@solve_models left c t u a result Ha Hleft) as ML.
  pose proof (@solve_models right c t u b other Hb Hright) as MR.
  destruct result as [x|]; destruct other as [y|]; simpl; [| | |exact I].
  - intro rho. specialize (ML rho). specialize (MR rho). specialize (Heq rho).
    cbn [Solver.result_models] in ML, MR. tauto.
  - destruct (@solve_safe left c t u a x Hleft) as [Hc Hacyc].
    destruct (acyclic_closed_has_model c x Hacyc Hc) as [rho Hrho].
    apply (proj1 (ML rho)) in Hrho. apply (proj2 (MR rho)).
    destruct Hrho as [Hmodel Hterm]. split; [apply (proj1 (Heq rho)); exact Hmodel|exact Hterm].
  - destruct (@solve_safe right c t u b y Hright) as [Hc Hacyc].
    destruct (acyclic_closed_has_model c y Hacyc Hc) as [rho Hrho].
    apply (proj1 (MR rho)) in Hrho. apply (proj2 (ML rho)).
    destruct Hrho as [Hmodel Hterm]. split; [apply (proj2 (Heq rho)); exact Hmodel|exact Hterm].
Qed.

Ltac invert_tree_shapes :=
  repeat match goal with
  | H : tree_equiv tfail _ |- _ => inversion H; subst; clear H
  | H : tree_equiv (tgoal _ _) _ |- _ => inversion H; subst; clear H
  | H : tree_equiv (tproceed _ _ _) _ |- _ => inversion H; subst; clear H
  | H : tree_equiv (tdelay _) _ |- _ => inversion H; subst; clear H
  | H : tree_equiv (tconj _ _) _ |- _ => inversion H; subst; clear H
  | H : tree_equiv (tdisjL _ _) _ |- _ => inversion H; subst; clear H
  | H : tree_equiv (tdisjR _ _) _ |- _ => inversion H; subst; clear H
  end.

Lemma head_solver_correspondence : forall (left right : Solver) G a a' b,
  tight_tree G a -> acyclic_tree a -> tight_tree G b -> acyclic_tree b ->
  tree_equiv a b -> @Head left G a a' ->
  exists b', @Head right G b b' /\ tree_equiv a' b'.
Proof.
  intros left right G a a' b Hta Haa Htb Hab Heq Hhead.
  destruct Hhead; invert_tree_shapes; simpl in *.
  - match goal with H : state_equiv s ?target |- _ =>
      rename target into other; destruct H as [Hcnt Hmodels] end.
    destruct Hta as [[Ht Hu] Hs]. destruct Htb as [[Ht' Hu'] Hs'].
    rewrite <- Hcnt in Ht', Hu', Hs'.
    destruct (solver_outcomes_equiv left right (st_cnt s) t1 t2 (st_sub s) (st_sub other)
      (Some s') (conj Haa (conj Hs (conj Ht Hu)))
      (conj Hab (conj Hs' (conj Ht' Hu'))) Hmodels H) as [[answer|] [Hsolve Hout]];
      [|contradiction].
    exists (tgoal gsucc (mkstate answer (st_cnt other))). split.
    + constructor. rewrite <- Hcnt. exact Hsolve.
    + constructor. split; [exact Hcnt|exact Hout].
  - match goal with H : state_equiv s ?target |- _ =>
      rename target into other; destruct H as [Hcnt Hmodels] end.
    destruct Hta as [[Ht Hu] Hs]. destruct Htb as [[Ht' Hu'] Hs'].
    rewrite <- Hcnt in Ht', Hu', Hs'.
    destruct (solver_outcomes_equiv left right (st_cnt s) t1 t2 (st_sub s) (st_sub other)
      None (conj Haa (conj Hs (conj Ht Hu)))
      (conj Hab (conj Hs' (conj Ht' Hu'))) Hmodels H) as [[answer|] [Hsolve Hout]];
      [contradiction|].
    exists tfail. split; [constructor; rewrite <- Hcnt; exact Hsolve|constructor].
  - eexists. split; [constructor|]. constructor; constructor; assumption.
  - eexists. split; [constructor|]. constructor. constructor. assumption.
  - match goal with H : state_equiv s ?target |- _ =>
      rename target into other; destruct H as [Hcnt Hmodels] end.
    eexists. split; [constructor|]. rewrite Hcnt.
    constructor. split; [reflexivity|exact Hmodels].
  - eexists. split; [constructor|]. constructor. constructor. assumption.
  - eexists. split; [eapply H_proceed; [eassumption|reflexivity]|]. constructor. assumption.
  - eexists. split; constructor.
  - eexists. split; [constructor|]. constructor. assumption.
  - eexists. split; [constructor|]. repeat first [assumption | constructor].
  - eexists. split; [constructor|]. repeat first [assumption | constructor].
  - eexists. split; [constructor|]. repeat first [assumption | constructor].
  - eexists. split; [constructor|]. repeat first [assumption | constructor].
  - eexists. split; [constructor|]. repeat first [assumption | constructor].
  - eexists. split; [constructor|]. repeat first [assumption | constructor].
  - eexists. split; [constructor|]. repeat first [assumption | constructor].
  - eexists. split; [constructor|]. repeat first [assumption | constructor].
  - eexists. split; [constructor|]. repeat first [assumption | constructor].
  - eexists. split; [constructor|]. repeat first [assumption | constructor].
  - eexists. split; [constructor|]. repeat first [assumption | constructor].
Qed.

Inductive context_equiv : ctx -> ctx -> Prop :=
| EQ_hole : context_equiv chole chole
| EQ_ctxL : forall a b t u, context_equiv a b -> tree_equiv t u ->
    context_equiv (cdisjL a t) (cdisjL b u)
| EQ_ctxR : forall a b t u, context_equiv a b -> tree_equiv t u ->
    context_equiv (cdisjR t a) (cdisjR u b)
| EQ_ctxConj : forall a b g, context_equiv a b ->
    context_equiv (cconj a g) (cconj b g).

Lemma plug_equiv : forall a b t u,
  context_equiv a b -> tree_equiv t u -> tree_equiv (plug a t) (plug b u).
Proof.
  intros a b t u H. induction H; intro Htu; simpl;
    repeat first [assumption | constructor | apply IHcontext_equiv].
Qed.

Lemma plug_equiv_inv : forall E r t,
  tree_equiv (plug E r) t ->
  exists F u, t = plug F u /\ context_equiv E F /\ tree_equiv r u.
Proof.
  induction E; intros r target H; simpl in H.
  - exists chole,target. split; [reflexivity|]. split; [constructor|exact H].
  - inversion H; subst.
    match goal with H : tree_equiv (plug E r) ?b |- _ =>
      destruct (IHE r b H) as [F [u [-> [HF Hu]]]] end.
    eexists (cdisjL F _). exists u. split; [reflexivity|]. split; [constructor; eassumption|exact Hu].
  - inversion H; subst.
    match goal with H : tree_equiv (plug E r) ?b |- _ =>
      destruct (IHE r b H) as [F [u [-> [HF Hu]]]] end.
    eexists (cdisjR _ F). exists u. split; [reflexivity|]. split; [constructor; eassumption|exact Hu].
  - inversion H; subst.
    match goal with H : tree_equiv (plug E r) ?b |- _ =>
      destruct (IHE r b H) as [F [u [-> [HF Hu]]]] end.
    eexists (cconj F _). exists u. split; [reflexivity|]. split; [constructor; exact HF|exact Hu].
Qed.

(** One reduction step is matched by exactly one reduction step, including
    the selected disjunction orientation, delays, and answer promotions. *)
Theorem step_solver_correspondence : forall (left right : Solver) G a a' b,
  ok_expr G a -> ok_expr G b -> expr_equiv a b -> @step left G a a' ->
  exists b', @step right G b b' /\ expr_equiv a' b'.
Proof.
  intros left right G a a' b Ha Hb [Hans Htrees] Hstep.
  destruct b as [answers target]. simpl in Hans, Htrees.
  destruct Hstep; simpl in *.
  - destruct (plug_equiv_inv E r target Htrees) as [F [u [-> [HE Hu]]]].
    pose proof (@ok_expr_plug_root G ans E r Ha) as Hra.
    pose proof (@ok_expr_plug_root G answers F u Hb) as Hrb.
    destruct Hra as [_ [Hta [_ Haa]]]. destruct Hrb as [_ [Htb [_ Hab]]].
    destruct (head_solver_correspondence left right G r r' u Hta Haa Htb Hab Hu H)
      as [out [Hout Heq]].
    exists (answers, plug F out). split.
    + apply S_ctx. exact Hout.
    + split; [exact Hans|apply plug_equiv; assumption].
  - inversion Htrees; subst. eexists. split; [apply S_delay|]. split; eassumption.
  - invert_tree_shapes. eexists. split; [apply S_promoteL|]. split; simpl.
    + apply Forall2_app; [exact Hans|]. constructor; [assumption|constructor].
    + assumption.
  - invert_tree_shapes. eexists. split; [apply S_promoteR|]. split; simpl.
    + apply Forall2_app; [exact Hans|]. constructor; [assumption|constructor].
    + assumption.
Qed.

Lemma expr_equiv_value : forall a b,
  expr_equiv a b -> (is_value a <-> is_value b).
Proof.
  intros [ans a] [answers b] [_ H]. simpl in H. unfold is_value. simpl.
  inversion H; subst; simpl; try tauto.
  all: try (destruct g; simpl; tauto).
Qed.

Lemma value_next_step_none : forall (solver : Solver) G e Hok,
  is_value e -> @next_step solver G e Hok = None.
Proof.
  intros solver G [ans t] Hok H. destruct t; simpl in H; try contradiction.
  - reflexivity.
  - destruct g; simpl in H; try contradiction. reflexivity.
Qed.

(** Equal step budgets preserve the complete ordered list of symbolic
    answer meanings, as well as all search-control structure. *)
Theorem run_steps_solver_independent : forall (left right : Solver) G Henv fuel a b Ha Hb,
  expr_equiv a b ->
  expr_equiv (@run_steps left G Henv fuel a Ha) (@run_steps right G Henv fuel b Hb).
Proof.
  intros left right G Henv fuel. induction fuel as [|fuel IH]; intros a b Ha Hb Heq;
    cbn [run_steps]; [exact Heq|].
  destruct (@next_step_checked left G Henv a Ha) as [[a' [Hsa Hva]]|] eqn:Ea;
  destruct (@next_step_checked right G Henv b Hb) as [[b' [Hsb Hvb]]|] eqn:Eb.
  - destruct (step_solver_correspondence left right G a a' b Ha Hb Heq Hsa)
      as [out [Hout Hrelated]].
    assert (out = b') by (eapply (@step_deterministic right); eassumption).
    subst out. apply IH. exact Hrelated.
  - apply next_step_checked_none in Eb.
    destruct (step_solver_correspondence left right G a a' b Ha Hb Heq Hsa)
      as [out [Hout _]].
    pose proof (@next_step_complete right G b Hb out Hout) as E.
    rewrite Eb in E. discriminate.
  - apply next_step_checked_none in Ea.
    pose proof (@next_step_none_value left G a Ha Ea) as Hvalue.
    apply (proj1 (expr_equiv_value a b Heq)) in Hvalue.
    pose proof (value_next_step_none right G b Hb Hvalue) as Evalue.
    pose proof (@next_step_complete right G b Hb b' Hsb) as E.
    rewrite Evalue in E. discriminate.
  - exact Heq.
Qed.

Lemma final_answers_equiv : forall a b,
  tree_equiv a b -> Forall2 state_equiv (final_answer a) (final_answer b).
Proof.
  intros a b H. inversion H; subst; simpl; try constructor.
  destruct g; simpl; constructor; [assumption|constructor].
Qed.

Lemma observed_answers_equiv : forall a b,
  expr_equiv a b -> Forall2 state_equiv (observed_answers a) (observed_answers b).
Proof.
  intros a b [Hans Htrees]. unfold observed_answers.
  apply Forall2_app; [exact Hans|apply final_answers_equiv; exact Htrees].
Qed.

Lemma state_equiv_represents : forall a b,
  state_equiv a b -> forall query rho,
  represents query a rho <-> represents query b rho.
Proof.
  intros a b [_ H] query rho. unfold represents. split.
  - intros [sigma [Hagree Hmodel]]. exists sigma. split; [exact Hagree|].
    apply (proj1 (H sigma)). exact Hmodel.
  - intros [sigma [Hagree Hmodel]]. exists sigma. split; [exact Hagree|].
    apply (proj2 (H sigma)). exact Hmodel.
Qed.

Theorem ordered_answers_solver_independent : forall (left right : Solver)
  G Henv fuel a b Ha Hb query,
  expr_equiv a b ->
  Forall2 (fun x y => forall rho, represents query x rho <-> represents query y rho)
    (observed_answers (@run_steps left G Henv fuel a Ha))
    (observed_answers (@run_steps right G Henv fuel b Hb)).
Proof.
  intros left right G Henv fuel a b Ha Hb query Heq.
  pose proof (observed_answers_equiv _ _
    (run_steps_solver_independent left right G Henv fuel a b Ha Hb Heq)) as H.
  induction H; constructor; [apply state_equiv_represents; exact H|exact IHForall2].
Qed.

Lemma state_equiv_refl : forall s, state_equiv s s.
Proof. intro s. split; [reflexivity|intro rho; reflexivity]. Qed.
Lemma tree_equiv_refl : forall t, tree_equiv t t.
Proof. intro t. induction t; constructor; try assumption; apply state_equiv_refl. Qed.
Lemma expr_equiv_refl : forall e, expr_equiv e e.
Proof.
  intros [ans t]. split; simpl.
  - induction ans; constructor; [apply state_equiv_refl|exact IHans].
  - apply tree_equiv_refl.
Qed.

Lemma checked_next_solver_equiv : forall (left right : Solver) G Henv a b Ha Hb,
  expr_equiv a b ->
  match @next_step_checked left G Henv a Ha, @next_step_checked right G Henv b Hb with
  | Some (exist _ a' _), Some (exist _ b' _) => expr_equiv a' b'
  | None,None => True
  | _,_ => False
  end.
Proof.
  intros left right G Henv a b Ha Hb Heq.
  destruct (@next_step_checked left G Henv a Ha) as [[a' [Hsa Hva]]|] eqn:Ea;
  destruct (@next_step_checked right G Henv b Hb) as [[b' [Hsb Hvb]]|] eqn:Eb;
    [| | |exact I].
  - destruct (step_solver_correspondence left right G a a' b Ha Hb Heq Hsa)
      as [out [Hout Hrelated]].
    assert (out = b') by (eapply (@step_deterministic right); eassumption).
    subst out. exact Hrelated.
  - apply next_step_checked_none in Eb.
    destruct (step_solver_correspondence left right G a a' b Ha Hb Heq Hsa)
      as [out [Hout _]].
    pose proof (@next_step_complete right G b Hb out Hout) as E.
    rewrite Eb in E. discriminate.
  - apply next_step_checked_none in Ea.
    pose proof (@next_step_none_value left G a Ha Ea) as Hvalue.
    apply (proj1 (expr_equiv_value a b Heq)) in Hvalue.
    pose proof (value_next_step_none right G b Hb Hvalue) as Evalue.
    pose proof (@next_step_complete right G b Hb b' Hsb) as E.
    rewrite Evalue in E. discriminate.
Qed.

Theorem execute_solver_independent : forall (left right : Solver)
  G Henv capture fuel a b Ha Hb,
  expr_equiv a b ->
  let x := @execute left G Henv capture fuel a Ha in
  let y := @execute right G Henv capture fuel b Hb in
  expr_equiv (execution_final x) (execution_final y) /\
  execution_steps x = execution_steps y /\
  Forall2 expr_equiv (execution_trace x) (execution_trace y).
Proof.
  intros left right G Henv capture fuel. induction fuel as [|fuel IH];
    intros a b Ha Hb Heq; cbn [execute].
  - split; [exact Heq|]. split; [reflexivity|].
    destruct capture; simpl; constructor; [exact Heq|constructor].
  - pose proof (checked_next_solver_equiv left right G Henv a b Ha Hb Heq) as Hnext.
    destruct (@next_step_checked left G Henv a Ha) as [[a' [Hsa Hva]]|];
    destruct (@next_step_checked right G Henv b Hb) as [[b' [Hsb Hvb]]|];
      try contradiction; cbn [execution_final execution_steps execution_trace].
    + destruct (IH a' b' Hva Hvb Hnext) as [Hfinal [Hsteps Htrace]].
      split; [exact Hfinal|]. split; [congruence|].
      destruct capture; simpl; [constructor; assumption|constructor].
    + split; [exact Heq|]. split; [reflexivity|].
      destruct capture; simpl; constructor; [exact Heq|constructor].
Qed.
