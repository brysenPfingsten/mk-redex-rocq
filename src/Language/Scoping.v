From Stdlib Require Import List Arith Lia.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees Unification.
Import ListNotations.
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
