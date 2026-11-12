From Stdlib Require Import List Arith Lia.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees Unification Scoping ScopedUnification.
From MkRedex.Operational Require Import Reduction.
Import ListNotations.
Set Default Goal Selector "!".

From MkRedex.Language Require Import Solver.
Section WithSolver.
Context `{solver : Solver}.

Lemma Head_closed : forall G c t t',
  closed_env G -> closed_tree G c t -> Head G t t' ->
  exists c', closed_tree G c' t'.
Proof.
  intros G c t t' Hce Hct Hhead.
  induction Hhead; simpl in *;
  try (exists c; easy).
  - exists c.
    destruct Hct as (Hlte & (Hct1 & Hct2) & Hcs).
    pose proof (proj1 (solve_safe _ _ _ _ _ H)) as Hlocal.
    pose proof (closed_sub_mono (st_cnt s) c s' Hlte Hlocal) as Hcs'.
    repeat split; assumption.
  - exists (c + k).
    destruct Hct as (Hlte & Hcg & Hcs).
    repeat split.
    * lia.
    * apply open_goal_closed.
      + rewrite length_map, length_seq, Nat.add_0_r.
        apply (closed_goal_mono G k k c (c + k) g); try lia.
        exact Hcg.
      + exact (fresh_args_closed (st_cnt s) c k Hlte).
    * apply closed_sub_mono with (c:=c).
      + lia.
      + assumption.
  - exists c.
    destruct (nth_error G r);
    try destruct p; easy.
  - exists c.
    rewrite H in Hct.
    destruct Hct as (Hcnt & Hlen & Hargs & Hsub).
    repeat split; try assumption.
    apply open_closed.
    + rewrite H0.
      apply (closed_goal_mono G n n 0 c body); try lia.
      exact (Hce r n body H).
    + exact Hargs.
Qed.

Inductive state_in : tree -> state -> Prop :=
  | SI_tgoal    : forall g s,     state_in (tgoal g s) s
  | SI_tdelay   : forall t s,     state_in t s -> state_in (tdelay t) s
  | SI_tproceed : forall r ts s,  state_in (tproceed r ts s) s
  | SI_tconj    : forall t g s,   state_in t s -> state_in (tconj t g) s
  | SI_tdisjL_l : forall t1 t2 s, state_in t1 s -> state_in (tdisjL t1 t2) s
  | SI_tdisjL_r : forall t1 t2 s, state_in t2 s -> state_in (tdisjL t1 t2) s
  | SI_tdisjR_l : forall t1 t2 s, state_in t1 s -> state_in (tdisjR t1 t2) s
  | SI_tdisjR_r : forall t1 t2 s, state_in t2 s -> state_in (tdisjR t1 t2) s
  .

Hint Constructors state_in : core.

Lemma closed_tree_state_counter : forall G c t s,
  closed_tree G c t -> state_in t s -> st_cnt s <= c.
Proof.
  intros G c t s Hclosed Hin. revert c Hclosed.
  induction Hin; intros c Hclosed; simpl in Hclosed.
  - lia.
  - apply IHHin. exact Hclosed.
  - destruct (nth_error G r) as [[n body]|]; [lia | contradiction].
  - apply IHHin. exact (proj1 Hclosed).
  - apply IHHin. exact (proj1 Hclosed).
  - apply IHHin. exact (proj2 Hclosed).
  - apply IHHin. exact (proj1 Hclosed).
  - apply IHHin. exact (proj2 Hclosed).
Qed.

Fixpoint tight_tree (G : env) (t : tree) : Prop :=
  match t with
  | tfail           => True
  | tgoal g s       => closed_goal G 0 (st_cnt s) g /\ closed_sub (st_cnt s) (st_sub s)
  | tdelay t'       => tight_tree G t'
  | tproceed r ts s => closed_sub (st_cnt s) (st_sub s) /\
                        Forall (closed_term 0 (st_cnt s)) ts
  | tconj t' g      => tight_tree G t' /\
                        (forall s, state_in t' s -> closed_goal G 0 (st_cnt s) g)
  | tdisjL t1 t2    => tight_tree G t1 /\ tight_tree G t2
  | tdisjR t1 t2    => tight_tree G t1 /\ tight_tree G t2
  end.

(** Each active state has an acyclic substitution.  This is the
    termination precondition for walking and unification. *)
Fixpoint acyclic_tree (t : tree) : Prop :=
  match t with
  | tfail => True
  | tgoal _ s | tproceed _ _ s => acyclic_sub (st_sub s)
  | tdelay t' | tconj t' _ => acyclic_tree t'
  | tdisjL t1 t2 | tdisjR t1 t2 => acyclic_tree t1 /\ acyclic_tree t2
  end.

Lemma closed_sub_zero_nil : forall s, closed_sub 0 s -> s = [].
Proof.
  intros [|[x u] s] Hclosed; [reflexivity | simpl in Hclosed; lia].
Qed.

Lemma closed_tree_zero_acyclic : forall G t,
  closed_tree G 0 t -> acyclic_tree t.
Proof.
  intros G t. induction t; simpl; intros Hclosed; try exact I.
  - destruct Hclosed as [_ [_ Hsub]].
    apply closed_sub_zero_nil in Hsub. subst. unfold acyclic_sub.
    intros x. constructor. intros y [u [Hlookup _]].
    rewrite Hsub in Hlookup. discriminate Hlookup.
  - exact (IHt Hclosed).
  - destruct (nth_error G n) as [[arity body]|]; [|contradiction].
    destruct Hclosed as [_ [_ [_ Hsub]]].
    apply closed_sub_zero_nil in Hsub. subst. unfold acyclic_sub.
    intros x. constructor. intros y [u [Hlookup _]].
    rewrite Hsub in Hlookup. discriminate Hlookup.
  - exact (IHt (proj1 Hclosed)).
  - destruct Hclosed as [H1 H2]. split; [apply IHt1 | apply IHt2]; assumption.
  - destruct Hclosed as [H1 H2]. split; [apply IHt1 | apply IHt2]; assumption.
Qed.

(** At the initial global bound zero, every state counter is zero, so
    global closure also supplies each local tightness obligation. *)
Lemma closed_tree_zero_tight : forall G t,
  closed_tree G 0 t -> tight_tree G t.
Proof.
  intros G t. induction t; simpl; intros Hclosed.
  - exact I.
  - destruct Hclosed as [Hcnt [Hg Hsub]].
    assert (st_cnt s = 0) by lia. rewrite H. split; assumption.
  - apply IHt. exact Hclosed.
  - destruct (nth_error G n) as [[arity body]|]; [|contradiction].
    destruct Hclosed as [Hcnt [Hlen [Hargs Hsub]]].
    assert (st_cnt s = 0) by lia. rewrite H. split; assumption.
  - destruct Hclosed as [Htree Hg]. split.
    + apply IHt. exact Htree.
    + intros s Hin.
      assert (st_cnt s = 0) by
        (pose proof (closed_tree_state_counter G 0 t s Htree Hin); lia).
      rewrite H. exact Hg.
  - destruct Hclosed as [H1 H2]. split; [apply IHt1 | apply IHt2]; assumption.
  - destruct Hclosed as [H1 H2]. split; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma tight_tree_proceed_open_args : forall G r ts s,
  tight_tree G (tproceed r ts s) -> runtime_open_args (st_cnt s) ts.
Proof. intros G r ts s Htight. exact (proj2 Htight). Qed.

Corollary tight_tree_proceed_tpar_free : forall G r ts s,
  tight_tree G (tproceed r ts s) -> Forall tpar_free ts.
Proof.
  intros G r ts s Htight. apply runtime_open_args_tpar_free with (c := st_cnt s).
  exact (tight_tree_proceed_open_args G r ts s Htight).
Qed.

(* The tight sub for a success state follows directly. *)
Lemma tight_tgoal_sub : forall G g s,
  tight_tree G (tgoal g s) -> closed_sub (st_cnt s) (st_sub s).
Proof. intros G g s [_ Hs]. exact Hs. Qed.

Lemma plug_tight_inv : forall G E r,
  tight_tree G (plug E r) -> tight_tree G r.
Proof.
  intros G E. induction E; intros r H; simpl in *.
  - exact H.
  - exact (IHE _ (proj1 H)).
  - exact (IHE _ (proj2 H)).
  - exact (IHE _ (proj1 H)).
Qed.

Lemma state_in_plug_mono : forall E r r' s,
  (forall s0, state_in r' s0 -> state_in r s0) ->
  state_in (plug E r') s ->
  state_in (plug E r) s.
Proof.
  induction E; intros r r' s Hsin Hsinr'; simpl in *.
  - apply Hsin. exact Hsinr'.
  - inversion Hsinr'; subst.
    * apply SI_tdisjL_l. apply IHE with r'; assumption.
    * apply SI_tdisjL_r. assumption.
  - inversion Hsinr'; subst.
    * apply SI_tdisjR_l. assumption.
    * apply SI_tdisjR_r. apply IHE with r'; assumption.
  - inversion Hsinr'; subst.
    apply SI_tconj. apply IHE with r'; assumption.
Qed.

Lemma plug_tight : forall G E r r',
  tight_tree G (plug E r) ->
  tight_tree G r' ->
  (forall s, state_in r' s -> state_in r s) ->
  tight_tree G (plug E r').
Proof.
  intros G E. revert G. induction E;
  intros G r r' Httplug Httr' Hsin; simpl in *.
  - exact Httr'.
  - split.
    * destruct Httplug. apply (IHE G r r'); assumption.
    * exact (proj2 Httplug).
  - split.
    * exact (proj1 Httplug).
    * destruct Httplug. apply (IHE G r r'); assumption.
  - split.
    * destruct Httplug. apply (IHE G r r'); assumption.
    * intros s Hsinr'.
      destruct Httplug as [_ H]. apply H.
      exact (state_in_plug_mono E r r' s Hsin Hsinr').
Qed.

Lemma state_in_tgoal_eq : forall g s s', state_in (tgoal g s) s' -> s' = s.
Proof. intros g s s' H. inversion H. subst. reflexivity. Qed.

Lemma state_in_delay_inv : forall t s, state_in (tdelay t) s -> state_in t s.
Proof. intros t s H. inversion H. assumption. Qed.

Lemma state_in_proceed_eq : forall r ts s s', state_in (tproceed r ts s) s' -> s' = s.
Proof. intros r ts s s' H. inversion H. subst. reflexivity. Qed.

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
  induction E; intros r s H; simpl.
  - exact H.
  - apply SI_tdisjL_l. apply IHE. exact H.
  - apply SI_tdisjR_r. apply IHE. exact H.
  - apply SI_tconj.    apply IHE. exact H.
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
   so any closed_goal condition transfers across a head step. *)
Lemma Head_closed_goal_transfer : forall G r r' g,
  Head G r r' ->
  (forall s, state_in r s -> closed_goal G 0 (st_cnt s) g) ->
  forall s', state_in r' s' -> closed_goal G 0 (st_cnt s') g.
Proof.
  intros G r r' g Hhead Hclosed s' Hsin.
  destruct (Head_state_counter G r r' Hhead s' Hsin) as [s [Hin Hle]].
  exact (closed_goal_mono G 0 0 (st_cnt s) (st_cnt s') g
           (Nat.le_refl 0) Hle (Hclosed s Hin)).
Qed.

Lemma Head_tight : forall G t t',
  closed_env G -> tight_tree G t -> Head G t t' ->
  tight_tree G t'.
Proof.
  intros G t t' Hce Htt Hhead.
  destruct Hhead; simpl in *; try tauto.
  - destruct Htt as [[Ht1 Ht2] Hsub]. split; [exact I |].
    exact (proj1 (solve_safe _ _ _ _ _ H)).
  - destruct Htt as [[Hg1 Hg2] Hsub]. split.
    + split; assumption.
    + intros out Hin. apply state_in_tgoal_eq in Hin. subst. exact Hg2.
  - destruct Htt as [Hg Hsub]. split.
    + apply open_goal_closed.
      * rewrite length_map, length_seq, Nat.add_0_r.
        apply (closed_goal_mono G k k (st_cnt s) (st_cnt s + k) g); try lia.
        exact Hg.
      * exact (fresh_args_closed (st_cnt s) (st_cnt s) k (Nat.le_refl _)).
    + apply closed_sub_mono with (c := st_cnt s); [lia | exact Hsub].
  - destruct Htt as [Hgoal Hsub].
    destruct (nth_error G r) as [[arity body]|] eqn:Hlook; simpl in Hgoal.
    + exact (conj Hsub (proj2 Hgoal)).
    + contradiction.
  - destruct Htt as [Hsub Hargs]. split; [|exact Hsub].
    apply open_closed.
    + rewrite H0.
      apply (closed_goal_mono G n n 0 (st_cnt s) body); try lia.
      exact (Hce r n body H).
    + exact Hargs.
  - destruct Htt as [[_ Hsub] Hcont]. split; [|exact Hsub].
    exact (Hcont s (SI_tgoal gsucc s)).
  - destruct Htt as [[Hs Ht2] Hcont]. split.
    + split; [exact Hs |]. intros out Hin.
      apply state_in_tgoal_eq in Hin. subst.
      apply Hcont. apply SI_tdisjL_l. constructor.
    + split; [exact Ht2 |]. intros out Hin.
      apply Hcont. apply SI_tdisjL_r. exact Hin.
  - destruct Htt as [[Ht1 Hs] Hcont]. split.
    + split; [exact Ht1 |]. intros out Hin.
      apply Hcont. apply SI_tdisjR_l. exact Hin.
    + split; [exact Hs |]. intros out Hin.
      apply state_in_tgoal_eq in Hin. subst.
      apply Hcont. apply SI_tdisjR_r. constructor.
  - destruct Htt as [Ht Hcont]. split; [exact Ht |].
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

Lemma plug_tight_head : forall G E r r',
  closed_env G ->
  tight_tree G (plug E r) ->
  Head G r r' ->
  tight_tree G r' ->
  tight_tree G (plug E r').
Proof.
  intros G E. induction E; intros r r' HcG Htt Hhead Htr'; simpl in *.
  - exact Htr'.
  - destruct Htt as [Htt1 Htt2].
    exact (conj (IHE r r' HcG Htt1 Hhead Htr') Htt2).
  - destruct Htt as [Htt1 Htt2].
    exact (conj Htt1 (IHE r r' HcG Htt2 Hhead Htr')).
  - destruct Htt as [Htt1 Hfg]. split.
    + exact (IHE r r' HcG Htt1 Hhead Htr').
    + intros s Hsin.
      destruct (state_in_plug_or _ r r' s Hsin) as [Hin | Hin].
      * exact (Hfg s Hin).
      * apply (Head_closed_goal_transfer G r r' _ Hhead);
          [intros s0 Hsin0; exact (Hfg s0 (state_in_plug_into _ r s0 Hsin0)) | exact Hin].
Qed.

Lemma Head_acyclic : forall G r r',
  acyclic_tree r -> Head G r r' -> acyclic_tree r'.
Proof.
  intros G r r' Hac Hhead.
  destruct Hhead; simpl in *; try tauto.
  - exact (proj2 (solve_safe _ _ _ _ _ H)).
Qed.

Lemma plug_acyclic_inv : forall E r,
  acyclic_tree (plug E r) -> acyclic_tree r.
Proof.
  induction E; intros r Hac; simpl in *; try exact Hac;
    apply IHE; tauto.
Qed.

Lemma plug_acyclic : forall E r r',
  acyclic_tree (plug E r) -> acyclic_tree r' ->
  acyclic_tree (plug E r').
Proof.
  induction E; intros r r' Hplug Hr'; simpl in *; try exact Hr'.
  - split; [eapply IHE; [exact (proj1 Hplug) | exact Hr'] | exact (proj2 Hplug)].
  - split; [exact (proj1 Hplug) | eapply IHE; [exact (proj2 Hplug) | exact Hr']].
  - eapply IHE; eassumption.
Qed.

Definition ok_expr (G : env) (e : expr) : Prop :=
  (exists c, closed_tree G c (snd e)) /\
  tight_tree G (snd e) /\
  Forall (fun s => closed_sub (st_cnt s) (st_sub s)) (fst e) /\
  acyclic_tree (snd e).

Lemma closed_program_env : forall G e,
  closed_program G e -> closed_env G.
Proof.
  intros G e [Hdefs _] r n body Hlook.
  rewrite Forall_forall in Hdefs.
  assert (Hin : In (n, body) G) by (eapply nth_error_In; exact Hlook).
  exact (Hdefs (n, body) Hin).
Qed.

Theorem closed_program_ok : forall G e,
  closed_program G e -> closed_env G /\ ok_expr G e.
Proof.
  intros G e Hprogram. split.
  - exact (closed_program_env G e Hprogram).
  - destruct Hprogram as [_ [Htree Hans]].
    repeat split.
    + exists 0. exact Htree.
    + exact (closed_tree_zero_tight G (snd e) Htree).
    + exact Hans.
    + exact (closed_tree_zero_acyclic G (snd e) Htree).
Qed.

Lemma step_ok : forall G e e',
  closed_env G -> ok_expr G e -> G |= e --> e' -> ok_expr G e'.
Proof.
  intros G e e' HcG Hoke Hstep.
  destruct Hstep.
  - (* S_ctx: (ans, plug E r) --> (ans, plug E r') *)
    destruct Hoke as [[c Hclosed] [Htt [Hfa Hac]]].
    repeat split; simpl.
    + apply (plug_closed_inv G c E r) in Hclosed as Hcr.
      destruct (Head_closed G c r r' HcG Hcr H) as [c' Hcr'].
      exists (Nat.max c c').
      apply (plug_closed G (Nat.max c c') E r r').
      * exact (closed_tree_mono G c _ _ (Nat.le_max_l c c') Hclosed).
      * exact (closed_tree_mono G c' _ _ (Nat.le_max_r c c') Hcr').
    + apply (plug_tight_head G E r r' HcG Htt H).
      apply (Head_tight G r r' HcG).
      * exact (plug_tight_inv G E r Htt).
      * exact H.
    + exact Hfa.
    + apply (plug_acyclic E r r').
      * exact Hac.
      * apply (Head_acyclic G r r').
        -- exact (plug_acyclic_inv E r Hac).
        -- exact H.
  - (* S_delay: (ans, tdelay t) --> (ans, t) *)
    destruct Hoke as [[c Hclosed] [Htt [Hfa Hac]]].
    repeat split; simpl in *.
    + exists c. exact Hclosed.
    + exact Htt.
    + exact Hfa.
    + exact Hac.
  - (* S_promoteL: (ans, tdisjL (tgoal gsucc s) t) --> (ans ++ [s], t) *)
    destruct Hoke as [[c Hclosed] [Htt [Hfa Hac]]].
    simpl in Hclosed, Htt.
    destruct Hclosed as [_ Hct].
    destruct Htt as [Hts Htt].
    repeat split; simpl.
    + exists c. exact Hct.
    + exact Htt.
    + rewrite Forall_app. split.
      * exact Hfa.
      * constructor; [exact (proj2 Hts) | constructor].
    + exact (proj2 Hac).
  - (* S_promoteR: (ans, tdisjR t (tgoal gsucc s)) --> (ans ++ [s], t) *)
    destruct Hoke as [[c Hclosed] [Htt [Hfa Hac]]].
    simpl in Hclosed, Htt.
    destruct Hclosed as [Hct _].
    destruct Htt as [Htt Hts].
    repeat split; simpl.
    + exists c. exact Hct.
    + exact Htt.
    + rewrite Forall_app. split.
      * exact Hfa.
      * constructor; [exact (proj2 Hts) | constructor].
    + exact (proj1 Hac).
Qed.

Lemma multi_ok : forall G e e',
  multi G e e' -> closed_env G -> ok_expr G e -> ok_expr G e'.
Proof.
  intros G e e' Hmulti HG Hok.
  induction Hmulti.
  - exact Hok.
  - apply IHHmulti. exact (step_ok G e1 e2 HG Hok H).
Qed.

Corollary closed_program_multi_ok : forall G e e',
  closed_program G e -> multi G e e' -> ok_expr G e'.
Proof.
  intros G e e' Hprogram Hmulti.
  destruct (closed_program_ok G e Hprogram) as [Henv Hok].
  exact (multi_ok G e e' Hmulti Henv Hok).
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

Theorem tree_progress : forall G c t ans,
  closed_tree G c t -> tight_tree G t -> acyclic_tree t ->
  is_value (ans, t) \/ exists e', G |= (ans, t) --> e'.
Proof.
  intros G c t. induction t; intros ans Hclosed Htight Hacyclic.
  - left. exact I.
  - destruct g.
    + left. exact I.
    + right. simpl in Htight. destruct Htight as [Hgoal Hsub].
      simpl in Hgoal. destruct Hgoal as [Ht1 Ht2].
      destruct (Solve_total (st_cnt s) (st_sub s) t t0
        Hacyclic Hsub Ht1 Ht2) as [[s'|] Hunify].
      * eexists. apply S_ctx with (E := chole). apply H_unify_ok. exact Hunify.
      * eexists. apply S_ctx with (E := chole). apply H_unify_fail. exact Hunify.
    + right. eexists. apply S_ctx with (E := chole). apply H_relcall.
    + right. eexists. apply S_ctx with (E := chole). apply H_disj.
    + right. eexists. apply S_ctx with (E := chole). apply H_conj.
    + right. eexists. apply S_ctx with (E := chole). apply H_fresh.
  - right. eexists. apply S_delay.
  - right. simpl in Hclosed.
    destruct (nth_error G n) as [[arity body]|] eqn:Hlook;
      [|contradiction].
    destruct Hclosed as [_ [Hlen _]].
    eexists. apply S_ctx with (E := chole).
    eapply H_proceed; eassumption.
  - right. simpl in Hclosed, Htight, Hacyclic.
    destruct (IHt ans (proj1 Hclosed) (proj1 Htight) Hacyclic)
      as [Hvalue | [e' Hstep]].
    + destruct t; simpl in Hvalue; try contradiction.
      * eexists. apply S_ctx with (E := chole). apply H_prune_conj.
      * destruct g0; try contradiction.
        eexists. apply S_ctx with (E := chole). apply H_succ_conj.
    + exact (step_conj_context G ans t e' g Hstep).
  - right. simpl in Hclosed, Htight, Hacyclic.
    destruct Hclosed as [Hc1 Hc2].
    destruct Htight as [Ht1 Ht2].
    destruct Hacyclic as [Ha1 Ha2].
    destruct (IHt1 ans Hc1 Ht1 Ha1) as [Hvalue | [e' Hstep]].
    + destruct t1; simpl in Hvalue; try contradiction.
      * eexists. apply S_ctx with (E := chole). apply H_prune_left.
      * destruct g; try contradiction. eexists. apply S_promoteL.
    + exact (step_disjL_context G ans t1 e' t2 Hstep).
  - right. simpl in Hclosed, Htight, Hacyclic.
    destruct Hclosed as [Hc1 Hc2].
    destruct Htight as [Ht1 Ht2].
    destruct Hacyclic as [Ha1 Ha2].
    destruct (IHt2 ans Hc2 Ht2 Ha2) as [Hvalue | [e' Hstep]].
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
  intros G [ans t] [[c Hclosed] [Htight [_ Hacyclic]]].
  exact (tree_progress G c t ans Hclosed Htight Hacyclic).
Qed.

Corollary closed_program_progress : forall G e,
  closed_program G e -> is_value e \/ exists e', G |= e --> e'.
Proof.
  intros G e Hprogram.
  destruct (closed_program_ok G e Hprogram) as [_ Hok].
  exact (progress G e Hok).
Qed.

Corollary closed_program_multi_progress : forall G e e',
  closed_program G e -> multi G e e' ->
  is_value e' \/ exists e'', G |= e' --> e''.
Proof.
  intros G e e' Hprogram Hmulti.
  apply progress. exact (closed_program_multi_ok G e e' Hprogram Hmulti).
Qed.

End WithSolver.
