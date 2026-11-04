From Stdlib Require Import List Arith Lia Logic.ProofIrrelevance Logic.ConstructiveEpsilon.
Import ListNotations.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees Unification.
Require Import MkRedex.Semantics.Reduction.
Set Default Goal Selector "!".

Fixpoint closed_term (d c : nat) (t : term) : Prop :=
  match t with
  | tvar n    => n < c
  | tpar i    => i < d
  | tcons a b => closed_term d c a /\ closed_term d c b
  | _         => True
  end.

(** Operational opening arguments cannot contain a bound parameter index.
    In particular, an argument inserted beneath [gfresh] cannot be captured. *)
Fixpoint tpar_free (t : term) : Prop :=
  match t with
  | tpar _ => False
  | tcons a b => tpar_free a /\ tpar_free b
  | _ => True
  end.

Lemma closed_term_zero_tpar_free : forall c t,
  closed_term 0 c t -> tpar_free t.
Proof.
  intros c t. induction t; simpl; try easy.
  intros [Ha Hb]. split; [apply IHt1 | apply IHt2]; assumption.
Qed.

Definition runtime_open_args (c : nat) (args : list term) : Prop :=
  Forall (closed_term 0 c) args.

Lemma runtime_open_args_tpar_free : forall c args,
  runtime_open_args c args -> Forall tpar_free args.
Proof.
  intros c args Hargs. apply Forall_forall.
  intros t Hin. apply closed_term_zero_tpar_free with (c := c).
  eapply Forall_forall; eassumption.
Qed.

Fixpoint closed_sub (c : nat) (s : sub) : Prop :=
  match s with
  | []           => True
  | (n, t) :: s' => n < c /\ closed_term 0 c t /\ closed_sub c s'
  end.

(** Number of IDs below [c] that are still unbound in [s]. *)
Fixpoint free_count (c : nat) (s : sub) : nat :=
  match c with
  | 0 => 0
  | S c' => free_count c' s +
      match lookup c' s with None => 1 | Some _ => 0 end
  end.

Lemma free_count_bind_above : forall c s x u,
  c <= x -> free_count c ((x, u) :: s) = free_count c s.
Proof.
  induction c as [|c IH]; intros s x u Hle; simpl; [reflexivity |].
  rewrite IH by lia.
  simpl. destruct (Nat.eqb_spec c x); [lia | reflexivity].
Qed.

Lemma free_count_bind_below : forall c s x u,
  x < c -> lookup x s = None ->
  free_count c ((x, u) :: s) < free_count c s.
Proof.
  induction c as [|c IH]; intros s x u Hlt Hfree; [lia |].
  destruct (Nat.eq_dec x c) as [-> | Hneq].
  - simpl. rewrite free_count_bind_above by lia.
    simpl. rewrite Nat.eqb_refl, Hfree. lia.
  - simpl. destruct (Nat.eqb_spec c x); [lia |].
    pose proof (IH s x u ltac:(lia) Hfree). lia.
Qed.

Fixpoint closed_goal (G : env) (d c : nat) (g : goal) : Prop :=
  match g with
  | gsucc        => True
  | gunify t1 t2 => closed_term d c t1 /\ closed_term d c t2
  | grelcall r ts =>
      match nth_error G r with
      | Some (n, _) => List.length ts = n /\ Forall (closed_term d c) ts
      | None        => False
      end
  | gdisj g1 g2  => closed_goal G d c g1 /\ closed_goal G d c g2
  | gconj g1 g2  => closed_goal G d c g1 /\ closed_goal G d c g2
  | gfresh k g1  => closed_goal G (d + k) c g1
  end.

Example fresh_binds_parameter_index :
  closed_goal [] 0 0 (gfresh 1 (gunify (tpar 0) tnil)).
Proof. simpl. lia. Qed.

Example fresh_does_not_preallocate_logic_variable :
  ~ closed_goal [] 0 0 (gfresh 1 (gunify (tvar 0) tnil)).
Proof. simpl. lia. Qed.

Fixpoint closed_tree (G : env) (c : nat) (t : tree) : Prop :=
  match t with
  | tfail           => True
  | tgoal g s       =>
      st_cnt s <= c /\
      closed_goal G 0 c g /\
      closed_sub c (st_sub s)
  | tdelay t'       => closed_tree G c t'
  | tproceed r ts s =>
      match nth_error G r with
      | Some (n, _) =>
          st_cnt s <= c /\
          List.length ts = n /\
          Forall (closed_term 0 c) ts /\
          closed_sub c (st_sub s)
      | None => False
      end
  | tconj t' g      =>
      closed_tree G c t' /\
      closed_goal G 0 c g
  | tdisjL t1 t2    => closed_tree G c t1 /\ closed_tree G c t2
  | tdisjR t1 t2    => closed_tree G c t1 /\ closed_tree G c t2
  end.

Definition closed_program (G : env) (e : expr) : Prop :=
  Forall (fun '(n, g) => closed_goal G n 0 g) G /\
  closed_tree G 0 (snd e) /\
  Forall (fun s => closed_sub (st_cnt s) (st_sub s)) (fst e).

Definition closed_env (G : env) : Prop :=
  forall r n b, nth_error G r = Some (n, b) -> closed_goal G n 0 b.

Definition closed_expr (G : env) (c : nat) (e : expr) : Prop :=
  closed_tree G c (snd e).

(** A pending relation call in a closed runtime tree supplies arguments
    closed at parameter depth zero. *)
Lemma closed_tree_proceed_open_args : forall G c r ts s,
  closed_tree G c (tproceed r ts s) -> runtime_open_args c ts.
Proof.
  intros G c r ts s Hclosed. simpl in Hclosed.
  destruct (nth_error G r) as [[n body]|]; [|contradiction].
  exact (proj1 (proj2 (proj2 Hclosed))).
Qed.

Lemma closed_goal_relcall_open_args : forall G c r ts,
  closed_goal G 0 c (grelcall r ts) -> runtime_open_args c ts.
Proof.
  intros G c r ts Hclosed. simpl in Hclosed.
  destruct (nth_error G r) as [[n body]|]; [|contradiction].
  exact (proj2 Hclosed).
Qed.

Lemma open_term_closed : forall d c t args,
  closed_term (length args + d) c t ->
  Forall (closed_term d c) args ->
  closed_term d c (open_term d args t).
Proof.
  intros d c t. revert d c.
  induction t; intros d c args H1 H2; simpl in *.
  1, 3, 4, 5, 6, 7: exact H1.
  - destruct (n <? d) eqn:E.
    * unfold closed_term. apply Nat.ltb_lt. exact E.
    * destruct (nth_error args (n - d)) eqn:E2.
      + eapply Forall_forall in H2.
        -- apply H2.
        -- eapply nth_error_In. exact E2.
      + simpl. apply nth_error_None in E2. lia.
  - destruct H1 as [H1a H1b]. split.
    * apply IHt1; assumption.
    * apply IHt2; assumption.
Qed.

Lemma closed_term_mono : forall d d' c c' t,
  d <= d' -> c <= c' -> closed_term d c t -> closed_term d' c' t.
Proof.
  intros d d' c c'. induction t; simpl; intros.
  3, 4, 5, 6, 7: exact H1.
  1, 2: lia.
  destruct H1. split; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma open_goal_closed : forall G d c g args,
  closed_goal G (length args + d) c g ->
  Forall (closed_term d c) args ->
  closed_goal G d c (open_goal d args g).
Proof.
  intros G d c g. revert d c.
  induction g; intros d c args H1 H2; simpl in *.
  - (*succ*) exact H1.
  - (*unify*) destruct H1 as [Hct1 Hct2].
    split; apply open_term_closed; assumption.
  - (*relcall*) destruct (nth_error G n).
    * destruct p as [n0 g0].
      destruct H1 as [Hlen Hforall].
      split.
      + rewrite length_map. exact Hlen.
      + rewrite Forall_map.
        eapply Forall_impl.
        -- intros t Ht. apply open_term_closed.
           ** exact Ht.
           ** exact H2.
        -- exact Hforall.
    * exact H1.
  - (*disj*) destruct H1 as [Hg1 Hg2]. split.
    * apply IHg1; assumption.
    * apply IHg2; assumption.
  - (*conj*) destruct H1 as [Hg1 Hg2]. split.
    * apply IHg1; assumption.
    * apply IHg2; assumption.
  - (*fresh*) apply IHg.
    * rewrite Nat.add_assoc. exact H1.
    * eapply Forall_impl.
      + intros t Ht.
        apply (closed_term_mono d (d + n) c c).
        1, 2: lia.
        exact Ht.
      + exact H2.
Qed.

Lemma open_closed : forall G c g args,
  closed_goal G (length args) c g ->
  Forall (closed_term 0 c) args ->
  closed_goal G 0 c (open args g).
Proof.
  intros G c g. revert G c.
  induction g; intros G c args H1 H2; simpl in *.
  - (*succ*) exact H1.
  - (*unify*) destruct H1 as [Ht Ht0].
    split; apply open_term_closed.
    2, 4: exact H2.
    * rewrite Nat.add_0_r. exact Ht.
    * rewrite Nat.add_0_r. exact Ht0.
  - (*relcall*) destruct (nth_error G n).
    * destruct p as [n0 g0].
      destruct H1 as [Hlen Hforall].
      split.
      + rewrite length_map. exact Hlen.
      + clear Hlen. induction Hforall as [| x l' Hx _ IH]; constructor.
        -- apply open_term_closed.
           ** rewrite Nat.add_0_r. exact Hx.
           ** exact H2.
        -- exact IH.
    * exact H1.
  - (*disj*) destruct H1 as [Hg1 Hg2]. split.
    * apply IHg1; assumption.
    * apply IHg2; assumption.
  - (*conj*) destruct H1 as [Hg1 Hg2]. split.
    * apply IHg1; assumption.
    * apply IHg2; assumption.
  - (*fresh*) apply open_goal_closed.
    * exact H1.
    * eapply Forall_impl.
      + intros t Ht.
        eapply closed_term_mono with (d:=0) (d':=n) (c:=c) (c':=c).
        1, 2: lia.
        exact Ht.
      + exact H2.
Qed.

(** This is the opening rule used by both [H_proceed] and [H_fresh].
    [runtime_open_args] entails [tpar_free] for every argument, including
    when [open_goal] descends beneath nested [gfresh] binders. *)
Lemma open_runtime_closed : forall G c g args,
  closed_goal G (length args) c g ->
  runtime_open_args c args ->
  closed_goal G 0 c (open args g).
Proof. exact open_closed. Qed.

Lemma closed_sub_mono : forall c c' s,
  c <= c' -> closed_sub c s -> closed_sub c' s.
Proof.
  intros c c' s Hle. induction s as [|[n t] s' IH]; simpl; [tauto|].
  intros [Hn [Ht Hs']]. repeat split.
  - lia.
  - exact (closed_term_mono 0 0 c c' _ (Nat.le_refl 0) Hle Ht).
  - apply IH. exact Hs'.
Qed.

Lemma closed_goal_mono : forall G d d' c c' g,
  d <= d' -> c <= c' -> closed_goal G d c g -> closed_goal G d' c' g.
Proof.
  intros G d d' c c' g. revert d d' c c'.
  induction g; simpl; intros d d' c c' Hd Hc H.
  - exact H.
  - destruct H. split; eapply closed_term_mono; eassumption.
  - destruct (nth_error G n); [|exact H].
    destruct p. destruct H as [Hlen Hfa]. split.
    * exact Hlen.
    * eapply Forall_impl; [|exact Hfa].
      intros t Ht. eapply closed_term_mono; eassumption.
  - destruct H. split; [eapply IHg1 | eapply IHg2]; eassumption.
  - destruct H. split; [eapply IHg1 | eapply IHg2]; eassumption.
  - apply IHg with (d := d + n) (c := c); [lia | lia | exact H].
Qed.

Lemma closed_tree_mono : forall G c c' t,
  c <= c' -> closed_tree G c t -> closed_tree G c' t.
Proof.
  intros G c c' t Hle. induction t; simpl; intros H.
  - exact H.
  - destruct H as [Hcnt [Hg Hs]]. repeat split.
    * lia.
    * exact (closed_goal_mono G 0 0 c c' _ (Nat.le_refl 0) Hle Hg).
    * exact (closed_sub_mono c c' _ Hle Hs).
  - apply IHt. exact H.
  - destruct (nth_error G n); [|exact H]. destruct p.
    destruct H as [Hcnt [Hlen [Hfa Hs]]]. repeat split.
    * lia.
    * exact Hlen.
    * eapply Forall_impl; [|exact Hfa]. intros t' Ht'.
      exact (closed_term_mono 0 0 c c' _ (Nat.le_refl 0) Hle Ht').
    * eapply closed_sub_mono; eassumption.
  - destruct H as [Ht Hg]. split.
    * apply IHt. exact Ht.
    * exact (closed_goal_mono G 0 0 c c' _ (Nat.le_refl 0) Hle Hg).
  - destruct H. split; [apply IHt1 | apply IHt2]; assumption.
  - destruct H. split; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma plug_closed_inv : forall G c E r,
  closed_tree G c (plug E r) -> closed_tree G c r.
Proof.
  intros G c E. induction E; intros r H; simpl in *.
  - exact H.
  - destruct H as [H _]. apply IHE in H. exact H.
  - destruct H as [_ H]. apply IHE in H. exact H.
  - destruct H as [H _]. apply IHE in H. exact H.
Qed.

Lemma plug_closed : forall G c E r r',
  closed_tree G c (plug E r) -> closed_tree G c r' -> closed_tree G c (plug E r').
Proof.
  intros G c E. induction E; intros r r' H1 H2; simpl in *.
  - exact H2.
  - destruct H1 as [Hplug Ht]. split.
    * apply (IHE r r') in Hplug; assumption.
    * exact Ht.
  - destruct H1 as [Ht Hplug]. split.
    * exact Ht.
    * apply (IHE r r') in Hplug; assumption.
  - destruct H1 as [Hplug Hg]. split.
    * apply (IHE r r') in Hplug; assumption.
    * exact Hg.
Qed.

(* Looking up in a closed sub gives a closed term *)
Lemma lookup_closed : forall c x s t,
  closed_sub c s -> lookup x s = Some t -> closed_term 0 c t.
Proof.
  induction s as [|[y u] s' IH]; intros t Hs Hlook; simpl in *.
  - discriminate Hlook.
  - destruct Hs as [_ [Hu Hs']].
    destruct (x =? y)%nat.
    * injection Hlook as <-. exact Hu.
    * apply IH; assumption.
Qed.

(* Walking a closed term through a closed sub yields a closed term *)
Lemma walk_f_closed : forall fuel c t s,
  closed_term 0 c t -> closed_sub c s -> closed_term 0 c (walk_f fuel t s).
Proof.
  induction fuel as [|fuel' IH]; intros c t s Ht Hs; simpl in *.
  - exact Ht.
  - destruct t.
    2, 3, 4, 5, 6, 7, 8: exact Ht.
    destruct (lookup n s) eqn:E.
    * apply IH.
      + apply lookup_closed with (x:=n) (s:=s); assumption.
      + exact Hs.
    * exact Ht.
Qed.

Lemma walk_closed : forall c t s,
  closed_term 0 c t -> closed_sub c s -> closed_term 0 c (walk t s).
Proof.
  intros. unfold walk. apply walk_f_closed; assumption.
Qed.

Lemma Walk_closed : forall c t1 t2 s,
  closed_term 0 c t1 ->
  closed_sub c s ->
  Walk s t1 t2 ->
  closed_term 0 c t2.
Proof.
  intros c t1 t2 s Hct Hcs Hwalk.
  induction Hwalk; try assumption.
  apply IHHwalk. exact (lookup_closed _ _ _ _ Hcs H).
Qed.


(** A successful [Unify] on closed terms yields a closed substitution. *)
Lemma UnifyW_closed : forall c w1 w2 s s',
  closed_term 0 c w1 ->
  closed_term 0 c w2 ->
  closed_sub c s ->
  UnifyW w1 w2 s (Some s') ->
  closed_sub c s'.
Proof.
  intros c w1 w2 s s' Hct1 Hct2 Hcs HunifyW.
  remember (Some s') as r eqn:Hr.
  revert s' Hr Hct1 Hct2 Hcs.
  induction HunifyW;
  intros s_final Hr Hct1 Hct2 Hcs;
  try congruence; simpl in *.
  - injection Hr as <-. repeat split; assumption.
  - injection Hr as <-. repeat split; assumption.
  - destruct Hct1 as [Hcta1 Hcta2].
    destruct Hct2 as [Hctb1 Hctb2].
    pose proof (Walk_closed _ _ _ _ Hcta1 Hcs H) as Hctwa1.
    pose proof (Walk_closed _ _ _ _ Hctb1 Hcs H0) as Hctwb1.
    assert (Hcs1 : closed_sub c s1).
    { eapply IHHunifyW1; try eassumption; try reflexivity.  }
    pose proof (Walk_closed _ _ _ _ Hcta2 Hcs1 H1) as Hctwa2.
    pose proof (Walk_closed _ _ _ _ Hctb2 Hcs1 H2) as Hctwb2.
    eapply IHHunifyW2; try eassumption.
Qed.

Lemma UnifyW_free_count : forall c w1 w2 s s',
  closed_term 0 c w1 -> closed_term 0 c w2 -> closed_sub c s ->
  UnifyW w1 w2 s (Some s') ->
  free_count c s' <= free_count c s /\
  (s' <> s -> free_count c s' < free_count c s).
Proof.
  intros c w1 w2 s s' Ht1 Ht2 Hsub Hunify.
  remember (Some s') as result eqn:Hr.
  revert s' Hr Ht1 Ht2 Hsub.
  induction Hunify; intros out Hr Ht1 Ht2 Hsub;
    try discriminate Hr.
  - injection Hr as <-. split; [lia | congruence].
  - injection Hr as <-.
    assert (Hlt : free_count c ((x, u) :: s) < free_count c s).
    { apply free_count_bind_below; [exact Ht1 | exact H]. }
    split; lia.
  - injection Hr as <-.
    assert (Hlt : free_count c ((y, u) :: s) < free_count c s).
    { apply free_count_bind_below; [exact Ht2 | exact H]. }
    split; lia.
  - destruct Ht1 as [Ha1 Ha2], Ht2 as [Hb1 Hb2].
    pose proof (Walk_closed c a1 wa1 s Ha1 Hsub H) as Hwa1.
    pose proof (Walk_closed c b1 wb1 s Hb1 Hsub H0) as Hwb1.
    destruct (IHHunify1 s1 eq_refl Hwa1 Hwb1 Hsub) as [Hle1 Hstrict1].
    pose proof (UnifyW_closed c wa1 wb1 s s1 Hwa1 Hwb1 Hsub Hunify1)
      as Hsub1.
    pose proof (Walk_closed c a2 wa2 s1 Ha2 Hsub1 H1) as Hwa2.
    pose proof (Walk_closed c b2 wb2 s1 Hb2 Hsub1 H2) as Hwb2.
    destruct (IHHunify2 out Hr Hwa2 Hwb2 Hsub1) as [Hle2 Hstrict2].
    split; [lia |].
    intro Hneq. destruct (sub_eq_dec s1 s) as [-> | Hneq1].
    + exact (Hstrict2 Hneq).
    + pose proof (Hstrict1 Hneq1). lia.
  - injection Hr as <-. split; [lia | congruence].
Qed.

Definition lex_count_size (p q : nat * nat) : Prop :=
  fst p < fst q \/ (fst p = fst q /\ snd p < snd q).

Lemma lex_count_size_wf : well_founded lex_count_size.
Proof.
  intros [n m]. revert m.
  induction n using lt_wf_ind; intro m.
  induction m using lt_wf_ind.
  constructor. intros [n' m'] [Hless | [Heq Hless]]; simpl in *.
  - apply H; exact Hless.
  - subst n'. apply H0. exact Hless.
Qed.

Lemma UnifyW_var_left_total : forall s x u,
  acyclic_sub s -> lookup x s = None -> exists r, UnifyW (tvar x) u s r.
Proof.
  intros s x u Hacyclic Hfree.
  destruct (term_eq_dec u (tvar x)) as [-> | Hneq].
  - exists (Some s). constructor.
  - destruct (DeepOccurs_dec s Hacyclic x u) as [Hocc | Hocc].
    + exists None. apply UW_var_fail; assumption.
    + exists (Some ((x, u) :: s)). apply UW_var_bind; assumption.
Qed.

Lemma UnifyW_var_right_total : forall s u y,
  acyclic_sub s -> lookup y s = None ->
  (forall z, u <> tvar z) -> exists r, UnifyW u (tvar y) s r.
Proof.
  intros s u y Hacyclic Hfree Hnotvar.
  destruct (DeepOccurs_dec s Hacyclic y u) as [Hocc | Hocc].
  - exists None. apply UW_sym_fail; assumption.
  - exists (Some ((y, u) :: s)). apply UW_sym_bind; assumption.
Qed.

Lemma UnifyW_rigid_total : forall s u v,
  (forall x, u <> tvar x) -> (forall x, v <> tvar x) ->
  (forall a b, u <> tcons a b) ->
  (forall a b, v <> tcons a b) ->
  exists r, UnifyW u v s r.
Proof.
  intros s u v Huv Hvv Huc Hvc.
  destruct (term_eq_dec u v) as [-> | Hneq].
  - exists (Some s). apply UW_rigid_eq; assumption.
  - exists None. apply UW_rigid_neq; assumption.
Qed.

Definition UnifyW_var_left_choice : forall s x u,
  acyclic_sub s -> lookup x s = None ->
  {r : option sub | UnifyW (tvar x) u s r}.
Proof.
  intros s x u Hacyclic Hfree.
  destruct (term_eq_dec u (tvar x)) as [-> | Hneq].
  - exists (Some s). constructor.
  - destruct (DeepOccurs_dec s Hacyclic x u) as [Hocc | Hocc].
    + exists None. apply UW_var_fail; assumption.
    + exists (Some ((x, u) :: s)). apply UW_var_bind; assumption.
Defined.

Definition UnifyW_var_right_choice : forall s u y,
  acyclic_sub s -> lookup y s = None ->
  (forall z, u <> tvar z) ->
  {r : option sub | UnifyW u (tvar y) s r}.
Proof.
  intros s u y Hacyclic Hfree Hnotvar.
  destruct (DeepOccurs_dec s Hacyclic y u) as [Hocc | Hocc].
  - exists None. apply UW_sym_fail; assumption.
  - exists (Some ((y, u) :: s)). apply UW_sym_bind; assumption.
Defined.

Definition UnifyW_rigid_choice : forall s u v,
  (forall x, u <> tvar x) -> (forall x, v <> tvar x) ->
  (forall a b, u <> tcons a b) ->
  (forall a b, v <> tcons a b) ->
  {r : option sub | UnifyW u v s r}.
Proof.
  intros s u v Huv Hvv Huc Hvc.
  destruct (term_eq_dec u v) as [-> | Hneq].
  - exists (Some s). apply UW_rigid_eq; assumption.
  - exists None. apply UW_rigid_neq; assumption.
Defined.

Theorem UnifyW_total : forall c s w1 w2,
  acyclic_sub s -> closed_sub c s ->
  closed_term 0 c w1 -> closed_term 0 c w2 ->
  Walk s w1 w1 -> Walk s w2 w2 ->
  exists r, UnifyW w1 w2 s r.
Proof.
  intro c.
  assert (Hmain : forall p : nat * nat,
      forall s w1 w2 r1 r2,
      acyclic_sub s -> closed_sub c s ->
      closed_term 0 c w1 -> closed_term 0 c w2 ->
      Walk s w1 w1 -> Walk s w2 w2 ->
      ApplySub s w1 r1 -> ApplySub s w2 r2 ->
      p = (free_count c s, tsize r1 + tsize r2) ->
      exists r, UnifyW w1 w2 s r). {
    apply (well_founded_induction lex_count_size_wf
      (fun p => forall s w1 w2 r1 r2,
        acyclic_sub s -> closed_sub c s ->
        closed_term 0 c w1 -> closed_term 0 c w2 ->
        Walk s w1 w1 -> Walk s w2 w2 ->
        ApplySub s w1 r1 -> ApplySub s w2 r2 ->
        p = (free_count c s, tsize r1 + tsize r2) ->
        exists r, UnifyW w1 w2 s r)).
    intros [n m] IH s w1 w2 r1 r2 Hacyclic Hsub Hc1 Hc2
           Hw1 Hw2 Happ1 Happ2 Hp.
    injection Hp as Hn Hm. subst n m.
    destruct w1; destruct w2;
      try solve [
        apply UnifyW_var_left_total; [exact Hacyclic |
          eapply Walk_tvar_free; exact Hw1]
      | apply UnifyW_var_right_total; [exact Hacyclic |
          eapply Walk_tvar_free; exact Hw2 | intros z Heq; discriminate Heq]
      | (exists None; apply UW_cons_clash_r; intros; discriminate)
      | (exists None; apply UW_cons_clash_l; intros; discriminate)
      | (apply UnifyW_rigid_total; intros; discriminate)].
    destruct Hc1 as [Hca1 Hca2], Hc2 as [Hcb1 Hcb2].
    destruct (ApplySub_total s Hacyclic w1_1) as [ra1 Ha1].
    destruct (ApplySub_total s Hacyclic w1_2) as [ra2 Ha2].
    destruct (ApplySub_total s Hacyclic w2_1) as [rb1 Hb1].
    destruct (ApplySub_total s Hacyclic w2_2) as [rb2 Hb2].
    assert (Hr1 : r1 = tcons ra1 ra2) by
      (eapply ApplySub_functional; [exact Happ1 | constructor; eassumption]).
    assert (Hr2 : r2 = tcons rb1 rb2) by
      (eapply ApplySub_functional; [exact Happ2 | constructor; eassumption]).
    destruct (Walk_total s Hacyclic w1_1) as [wa1 Hwa1].
    destruct (Walk_total s Hacyclic w2_1) as [wb1 Hwb1].
    assert (Hcwa1 : closed_term 0 c wa1) by
      exact (Walk_closed c w1_1 wa1 s Hca1 Hsub Hwa1).
    assert (Hcwb1 : closed_term 0 c wb1) by
      exact (Walk_closed c w2_1 wb1 s Hcb1 Hsub Hwb1).
    assert (Happa1 : ApplySub s wa1 ra1) by
      (eapply Walk_ApplySub_compat; [exact Hwa1 | intros; assumption | exact Ha1]).
    assert (Happb1 : ApplySub s wb1 rb1) by
      (eapply Walk_ApplySub_compat; [exact Hwb1 | intros; assumption | exact Hb1]).
    assert (Hlex1 : lex_count_size
      (free_count c s, tsize ra1 + tsize rb1)
      (free_count c s, tsize r1 + tsize r2)).
    { right. split; [reflexivity |]. rewrite Hr1, Hr2. simpl. lia. }
    destruct (IH _ Hlex1 s wa1 wb1 ra1 rb1 Hacyclic Hsub
      Hcwa1 Hcwb1 (Walk_idempotent s w1_1 wa1 Hwa1)
      (Walk_idempotent s w2_1 wb1 Hwb1) Happa1 Happb1 eq_refl)
      as [[s1 |] Hfirst].
    2: { exists None. eapply UW_cons_fail; eassumption. }
    assert (Hac1 : acyclic_sub s1) by
      exact (UnifyW_acyclic wa1 wb1 s s1 Hacyclic Hfirst).
    assert (Hsub1 : closed_sub c s1) by
      exact (UnifyW_closed c wa1 wb1 s s1 Hcwa1 Hcwb1 Hsub Hfirst).
    destruct (Walk_total s1 Hac1 w1_2) as [wa2 Hwa2].
    destruct (Walk_total s1 Hac1 w2_2) as [wb2 Hwb2].
    assert (Hcwa2 : closed_term 0 c wa2) by
      exact (Walk_closed c w1_2 wa2 s1 Hca2 Hsub1 Hwa2).
    assert (Hcwb2 : closed_term 0 c wb2) by
      exact (Walk_closed c w2_2 wb2 s1 Hcb2 Hsub1 Hwb2).
    destruct (ApplySub_total s1 Hac1 wa2) as [outa2 Happa2].
    destruct (ApplySub_total s1 Hac1 wb2) as [outb2 Happb2].
    assert (Hlex2 : lex_count_size
      (free_count c s1, tsize outa2 + tsize outb2)
      (free_count c s, tsize r1 + tsize r2)).
    { destruct (sub_eq_dec s1 s) as [-> | Hneq].
      - right. split; [reflexivity |].
        assert (Heqa : outa2 = ra2) by
          (eapply ApplySub_functional; [exact Happa2 |
            eapply Walk_ApplySub_compat; [exact Hwa2 | intros; assumption | exact Ha2]]).
        assert (Heqb : outb2 = rb2) by
          (eapply ApplySub_functional; [exact Happb2 |
            eapply Walk_ApplySub_compat; [exact Hwb2 | intros; assumption | exact Hb2]]).
        subst outa2 outb2. rewrite Hr1, Hr2. simpl. lia.
      - left. exact (proj2 (UnifyW_free_count c wa1 wb1 s s1
          Hcwa1 Hcwb1 Hsub Hfirst) Hneq).
    }
    destruct (IH _ Hlex2 s1 wa2 wb2 outa2 outb2 Hac1 Hsub1
      Hcwa2 Hcwb2 (Walk_idempotent s1 w1_2 wa2 Hwa2)
      (Walk_idempotent s1 w2_2 wb2 Hwb2) Happa2 Happb2 eq_refl)
      as [result Hsecond].
    exists result. eapply UW_cons_ok; eassumption.
  }
  intros s w1 w2 Hacyclic Hsub Hc1 Hc2 Hw1 Hw2.
  destruct (ApplySub_total s Hacyclic w1) as [r1 Happ1].
  destruct (ApplySub_total s Hacyclic w2) as [r2 Happ2].
  exact (Hmain (free_count c s, tsize r1 + tsize r2)
           s w1 w2 r1 r2 Hacyclic Hsub Hc1 Hc2 Hw1 Hw2
           Happ1 Happ2 eq_refl).
Qed.

Corollary Unify_total : forall c s t1 t2,
  acyclic_sub s -> closed_sub c s ->
  closed_term 0 c t1 -> closed_term 0 c t2 ->
  exists r, Unify t1 t2 s r.
Proof.
  intros c s t1 t2 Hacyclic Hsub Ht1 Ht2.
  destruct (Walk_total s Hacyclic t1) as [w1 Hw1].
  destruct (Walk_total s Hacyclic t2) as [w2 Hw2].
  assert (Hcw1 : closed_term 0 c w1) by
    exact (Walk_closed c t1 w1 s Ht1 Hsub Hw1).
  assert (Hcw2 : closed_term 0 c w2) by
    exact (Walk_closed c t2 w2 s Ht2 Hsub Hw2).
  destruct (UnifyW_total c s w1 w2 Hacyclic Hsub Hcw1 Hcw2
    (Walk_idempotent s t1 w1 Hw1) (Walk_idempotent s t2 w2 Hw2))
    as [result Hresult].
  exists result. exists w1, w2. repeat split; assumption.
Qed.

Fixpoint UnifyW_fuel (fuel : nat) (s : sub) (Hacyclic : acyclic_sub s)
  (w1 w2 : term) (Hw1 : Walk s w1 w1) (Hw2 : Walk s w2 w2)
  {struct fuel} : option {r : option sub | UnifyW w1 w2 s r}.
Proof.
  destruct fuel as [|fuel].
  - exact None.
  - destruct w1; destruct w2;
      try solve [
        exact (Some (UnifyW_var_left_choice s n _ Hacyclic
          (Walk_tvar_free s (tvar n) n Hw1)))
      | (refine (Some (UnifyW_var_right_choice s _ _ Hacyclic _ _));
          [eapply Walk_tvar_free; exact Hw2 |
           intros z Heq; discriminate Heq])
      | refine (Some (exist _ None _));
          (apply UW_cons_clash_r || apply UW_cons_clash_l);
          intros; discriminate
      | (refine (Some (UnifyW_rigid_choice s _ _ _ _ _ _));
          intros; discriminate)].
    set (wa1 := walk_valid s Hacyclic w1_1).
    set (wb1 := walk_valid s Hacyclic w2_1).
    assert (Hwa1 : Walk s w1_1 wa1) by
      (apply (proj2 (walk_valid_spec s Hacyclic w1_1 wa1)); reflexivity).
    assert (Hwb1 : Walk s w2_1 wb1) by
      (apply (proj2 (walk_valid_spec s Hacyclic w2_1 wb1)); reflexivity).
    destruct (UnifyW_fuel fuel s Hacyclic wa1 wb1
      (Walk_idempotent s w1_1 wa1 Hwa1)
      (Walk_idempotent s w2_1 wb1 Hwb1))
      as [[first Hfirst] |].
    2: exact None.
    destruct first as [s1 |].
    + assert (Hac1 : acyclic_sub s1) by
        exact (UnifyW_acyclic wa1 wb1 s s1 Hacyclic Hfirst).
      set (wa2 := walk_valid s1 Hac1 w1_2).
      set (wb2 := walk_valid s1 Hac1 w2_2).
      assert (Hwa2 : Walk s1 w1_2 wa2) by
        (apply (proj2 (walk_valid_spec s1 Hac1 w1_2 wa2)); reflexivity).
      assert (Hwb2 : Walk s1 w2_2 wb2) by
        (apply (proj2 (walk_valid_spec s1 Hac1 w2_2 wb2)); reflexivity).
      destruct (UnifyW_fuel fuel s1 Hac1 wa2 wb2
        (Walk_idempotent s1 w1_2 wa2 Hwa2)
        (Walk_idempotent s1 w2_2 wb2 Hwb2))
        as [[result Hsecond] |].
      * refine (Some (exist _ result _)).
        eapply UW_cons_ok; eassumption.
      * exact None.
    + refine (Some (exist _ None _)).
      eapply UW_cons_fail; eassumption.
Defined.

Lemma UnifyW_fuel_noncons : forall fuel s Hacyclic w1 w2 Hw1 Hw2,
  0 < fuel ->
  (forall a1 a2 b1 b2,
      w1 <> tcons a1 a2 \/ w2 <> tcons b1 b2) ->
  exists result, UnifyW_fuel fuel s Hacyclic w1 w2 Hw1 Hw2 = Some result.
Proof.
  intros [|fuel] s Hacyclic w1 w2 Hw1 Hw2 Hfuel Hnotcons;
    [lia |].
  destruct w1; destruct w2; simpl; try (eexists; reflexivity).
  exfalso. destruct (Hnotcons w1_1 w1_2 w2_1 w2_2);
    apply H; reflexivity.
Qed.

Lemma UnifyW_fuel_eventual : forall w1 w2 s r,
  UnifyW w1 w2 s r ->
  forall Hacyclic Hw1 Hw2,
  exists threshold, forall fuel,
    threshold <= fuel ->
    exists result,
      UnifyW_fuel fuel s Hacyclic w1 w2 Hw1 Hw2 = Some result.
Proof.
  intros w1 w2 s r Hunify. induction Hunify;
    intros Hacyclic Hw1 Hw2;
    try solve [
      exists 1; intros fuel Hfuel;
      eapply UnifyW_fuel_noncons; [lia | intros; left; discriminate]
    | exists 1; intros fuel Hfuel;
      eapply UnifyW_fuel_noncons; [lia | intros; right; discriminate]
    | exists 1; intros fuel Hfuel;
      eapply UnifyW_fuel_noncons; [lia | intros; first [left; eauto | right; eauto]]].
  - assert (Ewa1 : walk_valid s Hacyclic a1 = wa1) by
      (apply (walk_valid_of_Walk s a1 wa1 H Hacyclic)).
    assert (Ewb1 : walk_valid s Hacyclic b1 = wb1) by
      (apply (walk_valid_of_Walk s b1 wb1 H0 Hacyclic)).
    subst wa1 wb1.
    destruct (IHHunify1 Hacyclic
      (Walk_idempotent s a1 (walk_valid s Hacyclic a1)
        (proj2 (walk_valid_spec s Hacyclic a1
          (walk_valid s Hacyclic a1)) eq_refl))
      (Walk_idempotent s b1 (walk_valid s Hacyclic b1)
        (proj2 (walk_valid_spec s Hacyclic b1
          (walk_valid s Hacyclic b1)) eq_refl))) as [N1 HN1].
    assert (Hac1 : acyclic_sub s1) by
      (eapply UnifyW_acyclic; eassumption).
    assert (Ewa2 : walk_valid s1 Hac1 a2 = wa2) by
      (apply (walk_valid_of_Walk s1 a2 wa2 H1 Hac1)).
    assert (Ewb2 : walk_valid s1 Hac1 b2 = wb2) by
      (apply (walk_valid_of_Walk s1 b2 wb2 H2 Hac1)).
    subst wa2 wb2.
    destruct (IHHunify2 Hac1
      (Walk_idempotent s1 a2 (walk_valid s1 Hac1 a2)
        (proj2 (walk_valid_spec s1 Hac1 a2
          (walk_valid s1 Hac1 a2)) eq_refl))
      (Walk_idempotent s1 b2 (walk_valid s1 Hac1 b2)
        (proj2 (walk_valid_spec s1 Hac1 b2
          (walk_valid s1 Hac1 b2)) eq_refl))) as [N2 HN2].
    exists (S (Nat.max N1 N2)). intros [|fuel] Hfuel; [lia |].
    simpl UnifyW_fuel.
    destruct (HN1 fuel ltac:(lia)) as [first Hfirst].
    rewrite Hfirst. destruct first as [res Hres].
    assert (Heq : res = Some s1) by
      (eapply UnifyW_functional; eassumption).
    subst res. simpl.
    replace (UnifyW_acyclic (walk_valid s Hacyclic a1)
      (walk_valid s Hacyclic b1) s s1 Hacyclic Hres) with Hac1
      by apply proof_irrelevance.
    destruct (HN2 fuel ltac:(lia)) as [second Hsecond].
    rewrite Hsecond. destruct second as [result Hresult].
    simpl. eexists. reflexivity.
  - assert (Ewa1 : walk_valid s Hacyclic a1 = wa1) by
      (apply (walk_valid_of_Walk s a1 wa1 H Hacyclic)).
    assert (Ewb1 : walk_valid s Hacyclic b1 = wb1) by
      (apply (walk_valid_of_Walk s b1 wb1 H0 Hacyclic)).
    subst wa1 wb1.
    destruct (IHHunify Hacyclic
      (Walk_idempotent s a1 (walk_valid s Hacyclic a1)
        (proj2 (walk_valid_spec s Hacyclic a1
          (walk_valid s Hacyclic a1)) eq_refl))
      (Walk_idempotent s b1 (walk_valid s Hacyclic b1)
        (proj2 (walk_valid_spec s Hacyclic b1
          (walk_valid s Hacyclic b1)) eq_refl))) as [N HN].
    exists (S N). intros [|fuel] Hfuel; [lia |].
    simpl UnifyW_fuel.
    destruct (HN fuel ltac:(lia)) as [first Hfirst].
    rewrite Hfirst. destruct first as [res Hres].
    assert (Heq : res = None) by
      (eapply UnifyW_functional; eassumption).
    subst res. simpl. eexists. reflexivity.
  - exists 1. intros fuel Hfuel.
    eapply UnifyW_fuel_noncons; [lia |].
    intros a b c0 d. right. eauto.
Qed.

(** Search increasing fuel values.  [UnifyW_total] and
    [UnifyW_fuel_eventual] ensure this search terminates on valid inputs. *)
Definition UnifyW_fn : forall c s w1 w2,
  acyclic_sub s -> closed_sub c s ->
  closed_term 0 c w1 -> closed_term 0 c w2 ->
  Walk s w1 w1 -> Walk s w2 w2 ->
  {r : option sub | UnifyW w1 w2 s r}.
Proof.
  intros c s w1 w2 Hacyclic Hsub Hc1 Hc2 Hw1 Hw2.
  set (P := fun fuel => exists result,
    UnifyW_fuel fuel s Hacyclic w1 w2 Hw1 Hw2 = Some result).
  assert (Hdec : forall fuel, {P fuel} + {~ P fuel}).
  { intro fuel. unfold P.
    destruct (UnifyW_fuel fuel s Hacyclic w1 w2 Hw1 Hw2)
      as [result |] eqn:E.
    - left. exists result. reflexivity.
    - right. intros [result Hr]. discriminate Hr.
  }
  assert (Hex : exists fuel, P fuel).
  { destruct (UnifyW_total c s w1 w2 Hacyclic Hsub Hc1 Hc2 Hw1 Hw2)
      as [r Hr].
    destruct (UnifyW_fuel_eventual w1 w2 s r Hr Hacyclic Hw1 Hw2)
      as [threshold Hthreshold].
    exists threshold. exact (Hthreshold threshold (Nat.le_refl _)).
  }
  destruct (constructive_indefinite_description_nat P Hdec Hex)
    as [fuel Hfuel].
  unfold P in Hfuel.
  destruct (UnifyW_fuel fuel s Hacyclic w1 w2 Hw1 Hw2)
    as [result |] eqn:E.
  - exact result.
  - exfalso. destruct Hfuel as [result Hr]. discriminate Hr.
Defined.

Definition unify_fn_cert : forall c s t1 t2,
  acyclic_sub s -> closed_sub c s ->
  closed_term 0 c t1 -> closed_term 0 c t2 ->
  {r : option sub | Unify t1 t2 s r}.
Proof.
  intros c s t1 t2 Hacyclic Hsub Ht1 Ht2.
  set (w1 := walk_valid s Hacyclic t1).
  set (w2 := walk_valid s Hacyclic t2).
  assert (Hw1 : Walk s t1 w1) by
    (apply (proj2 (walk_valid_spec s Hacyclic t1 w1)); reflexivity).
  assert (Hw2 : Walk s t2 w2) by
    (apply (proj2 (walk_valid_spec s Hacyclic t2 w2)); reflexivity).
  assert (Hcw1 : closed_term 0 c w1) by
    exact (Walk_closed c t1 w1 s Ht1 Hsub Hw1).
  assert (Hcw2 : closed_term 0 c w2) by
    exact (Walk_closed c t2 w2 s Ht2 Hsub Hw2).
  destruct (UnifyW_fn c s w1 w2 Hacyclic Hsub Hcw1 Hcw2
    (Walk_idempotent s t1 w1 Hw1)
    (Walk_idempotent s t2 w2 Hw2)) as [result Hresult].
  exists result. exists w1, w2. repeat split; assumption.
Defined.

Definition unify_fn (t1 t2 : term) (s : sub) (c : nat)
  (Hacyclic : acyclic_sub s) (Hsub : closed_sub c s)
  (Ht1 : closed_term 0 c t1) (Ht2 : closed_term 0 c t2)
  : option sub :=
  proj1_sig (unify_fn_cert c s t1 t2 Hacyclic Hsub Ht1 Ht2).

Theorem unify_fn_spec : forall c s t1 t2 Hacyclic Hsub Ht1 Ht2 result,
  Unify t1 t2 s result <->
  unify_fn t1 t2 s c Hacyclic Hsub Ht1 Ht2 = result.
Proof.
  intros c s t1 t2 Hacyclic Hsub Ht1 Ht2 result.
  unfold unify_fn. destruct (unify_fn_cert c s t1 t2 Hacyclic Hsub Ht1 Ht2)
    as [out Hout]. simpl. split.
  - intro Hrel. exact (Unify_functional t1 t2 s out result Hout Hrel).
  - intro Heq. subst result. exact Hout.
Qed.


Lemma Unify_closed : forall c t1 t2 s s',
  closed_term 0 c t1 ->
  closed_term 0 c t2 ->
  closed_sub c s ->
  Unify t1 t2 s (Some s') ->
  closed_sub c s'.
Proof.
  intros c t1 t2 s s' Hct1 Hct2 Hcs Hunify.
  destruct Hunify as (w1 & w2 & Hw1 & Hw2 & HunifyW).
  pose proof (Walk_closed _ _ _ _ Hct1 Hcs Hw1) as Hctw1.
  pose proof (Walk_closed _ _ _ _ Hct2 Hcs Hw2) as Hctw2.
  exact (UnifyW_closed c w1 w2 s s' Hctw1 Hctw2 Hcs HunifyW).
Qed.

Lemma in_map_seq : forall {A : Type} (n a b : nat) (f : nat -> A),
  (forall x y, f x = f y -> x = y) ->
  (In (f n) (map f (seq a b)) <-> a <= n < a + b).
Proof.
  intros A n a b f Hinj.
  split; intros H.
  - apply in_map_iff in H.
    destruct H as [m [Hfm Hseq]].
    apply Hinj in Hfm.
    subst m. apply in_seq. exact Hseq.
  - apply in_map_iff.
    exists n.
    split.
    + reflexivity.
    + apply in_seq.
      exact H.
Qed.

Lemma fresh_args_closed : forall start bound k,
  start <= bound ->
  Forall (closed_term 0 (bound + k)) (map tvar (seq start k)).
Proof.
  intros start bound k Hle. apply Forall_forall. intros t Hin.
  apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
  apply in_seq in Hi. simpl. lia.
Qed.

Lemma fresh_args_open_args : forall start bound k,
  start <= bound ->
  runtime_open_args (bound + k) (map tvar (seq start k)).
Proof. exact fresh_args_closed. Qed.

Corollary fresh_args_tpar_free : forall start k,
  Forall tpar_free (map tvar (seq start k)).
Proof.
  intros start k. apply runtime_open_args_tpar_free with (c := start + k).
  apply fresh_args_open_args. lia.
Qed.

Lemma Head_closed : forall G c t t',
  closed_env G -> closed_tree G c t -> Head G t t' ->
  exists c', closed_tree G c' t'.
Proof.
  intros G c t t' Hce Hct Hhead.
  induction Hhead; simpl in *;
  try (exists c; easy).
  - exists c.
    destruct Hct as (Hlte & (Hct1 & Hct2) & Hcs).
    pose proof (Unify_closed _ _ _ _ _ Hct1 Hct2 Hcs H) as Hcs'.
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
  | SI_tgoal    : forall g s,           state_in (tgoal g s) s
  | SI_tdelay   : forall t s,           state_in t s -> state_in (tdelay t) s
  | SI_tproceed : forall r ts s,        state_in (tproceed r ts s) s
  | SI_tconj    : forall t g s,         state_in t s -> state_in (tconj t g) s
  | SI_tdisjL_l : forall t1 t2 s,      state_in t1 s -> state_in (tdisjL t1 t2) s
  | SI_tdisjL_r : forall t1 t2 s,      state_in t2 s -> state_in (tdisjL t1 t2) s
  | SI_tdisjR_l : forall t1 t2 s,      state_in t1 s -> state_in (tdisjR t1 t2) s
  | SI_tdisjR_r : forall t1 t2 s,      state_in t2 s -> state_in (tdisjR t1 t2) s
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
    exact (Unify_closed (st_cnt s) t1 t2 (st_sub s) s' Ht1 Ht2 Hsub H).
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

Definition ok_expr (G : env) (e : expr) : Prop :=
  (exists c, closed_tree G c (snd e)) /\
  tight_tree G (snd e) /\
  Forall (fun s => closed_sub (st_cnt s) (st_sub s)) (fst e).

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
Qed.

Lemma step_ok : forall G e e',
  closed_env G -> ok_expr G e -> G |= e --> e' -> ok_expr G e'.
Proof.
  intros G e e' HcG Hoke Hstep.
  destruct Hstep.
  - (* S_ctx: (ans, plug E r) --> (ans, plug E r') *)
    destruct Hoke as [[c Hclosed] [Htt Hfa]].
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
  - (* S_delay: (ans, tdelay t) --> (ans, t) *)
    destruct Hoke as [[c Hclosed] [Htt Hfa]].
    repeat split; simpl in *.
    + exists c. exact Hclosed.
    + exact Htt.
    + exact Hfa.
  - (* S_promoteL: (ans, tdisjL (tgoal gsucc s) t) --> (ans ++ [s], t) *)
    destruct Hoke as [[c Hclosed] [Htt Hfa]].
    simpl in Hclosed, Htt.
    destruct Hclosed as [_ Hct].
    destruct Htt as [Hts Htt].
    repeat split; simpl.
    + exists c. exact Hct.
    + exact Htt.
    + rewrite Forall_app. split.
      * exact Hfa.
      * constructor; [exact (proj2 Hts) | constructor].
  - (* S_promoteR: (ans, tdisjR t (tgoal gsucc s)) --> (ans ++ [s], t) *)
    destruct Hoke as [[c Hclosed] [Htt Hfa]].
    simpl in Hclosed, Htt.
    destruct Hclosed as [Hct _].
    destruct Htt as [Htt Hts].
    repeat split; simpl.
    + exists c. exact Hct.
    + exact Htt.
    + rewrite Forall_app. split.
      * exact Hfa.
      * constructor; [exact (proj2 Hts) | constructor].
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
