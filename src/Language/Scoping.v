From Stdlib Require Import List Arith Lia.
From MkRedex.Language Require Import WellFormed Terms Substitution Goals Environments Unification.
Import ListNotations.
Set Default Goal Selector "!".

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

Lemma ok_goal_relcall_open_args : forall G c r ts,
  ok_goal G 0 c (grelcall r ts) -> runtime_open_args c ts.
Proof.
  intros G c r ts Hclosed. simpl in Hclosed.
  destruct (nth_error G r) as [[n body]|]; [|contradiction].
  exact (proj2 Hclosed).
Qed.

Lemma open_term_closed : forall d c t args,
  ok_term (length args + d) c t ->
  Forall (ok_term d c) args ->
  ok_term d c (open_term d args t).
Proof.
  intros d c t. revert d c.
  induction t; intros d c args H1 H2; simpl in *.
  1, 3, 4, 5, 6, 7: exact H1.
  - destruct (n <? d) eqn:E.
    * unfold ok_term. apply Nat.ltb_lt. exact E.
    * destruct (nth_error args (n - d)) eqn:E2.
      + eapply Forall_forall in H2.
        -- apply H2.
        -- eapply nth_error_In. exact E2.
      + simpl. apply nth_error_None in E2. lia.
  - destruct H1 as [H1a H1b]. split.
    * apply IHt1; assumption.
    * apply IHt2; assumption.
Qed.

Lemma ok_term_mono : forall d d' c c' t,
  d <= d' -> c <= c' -> ok_term d c t -> ok_term d' c' t.
Proof.
  intros d d' c c'. induction t; simpl; intros.
  3, 4, 5, 6, 7: exact H1.
  1, 2: lia.
  destruct H1. split; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma open_goal_closed : forall G d c g args,
  ok_goal G (length args + d) c g ->
  Forall (ok_term d c) args ->
  ok_goal G d c (open_goal d args g).
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
        apply (ok_term_mono d (d + n) c c).
        1, 2: lia.
        exact Ht.
      + exact H2.
Qed.

Lemma open_closed : forall G c g args,
  ok_goal G (length args) c g ->
  Forall (ok_term 0 c) args ->
  ok_goal G 0 c (open args g).
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
        eapply ok_term_mono with (d:=0) (d':=n) (c:=c) (c':=c).
        1, 2: lia.
        exact Ht.
      + exact H2.
Qed.

Lemma scoped_sub_mono : forall c c' s,
  c <= c' -> scoped_sub c s -> scoped_sub c' s.
Proof.
  intros c c' s Hle. induction s as [|[n t] s' IH]; simpl; [tauto|].
  intros [Hn [Ht Hs']]. repeat split.
  - lia.
  - exact (ok_term_mono 0 0 c c' _ (Nat.le_refl 0) Hle Ht).
  - apply IH. exact Hs'.
Qed.

Lemma ok_goal_mono : forall G d d' c c' g,
  d <= d' -> c <= c' -> ok_goal G d c g -> ok_goal G d' c' g.
Proof.
  intros G d d' c c' g. revert d d' c c'.
  induction g; simpl; intros d d' c c' Hd Hc H.
  - exact H.
  - destruct H. split; eapply ok_term_mono; eassumption.
  - destruct (nth_error G n); [|exact H].
    destruct p. destruct H as [Hlen Hfa]. split.
    * exact Hlen.
    * eapply Forall_impl; [|exact Hfa].
      intros t Ht. eapply ok_term_mono; eassumption.
  - destruct H. split; [eapply IHg1 | eapply IHg2]; eassumption.
  - destruct H. split; [eapply IHg1 | eapply IHg2]; eassumption.
  - apply IHg with (d := d + n) (c := c); [lia | lia | exact H].
Qed.

(* Looking up in a closed sub gives a closed term *)
Lemma lookup_closed : forall c x s t,
  scoped_sub c s -> lookup x s = Some t -> ok_term 0 c t.
Proof.
  induction s as [|[y u] s' IH]; intros t Hs Hlook; simpl in *.
  - discriminate Hlook.
  - destruct Hs as [_ [Hu Hs']].
    destruct (x =? y)%nat.
    * injection Hlook as <-. exact Hu.
    * apply IH; assumption.
Qed.

Lemma Walk_closed : forall c t1 t2 s,
  ok_term 0 c t1 ->
  scoped_sub c s ->
  Walk s t1 t2 ->
  ok_term 0 c t2.
Proof.
  intros c t1 t2 s Hct Hcs Hwalk.
  induction Hwalk; try assumption.
  apply IHHwalk. exact (lookup_closed _ _ _ _ Hcs H).
Qed.

Lemma fresh_args_closed : forall start bound k,
  start <= bound ->
  Forall (ok_term 0 (bound + k)) (map tvar (seq start k)).
Proof.
  intros start bound k Hle. apply Forall_forall. intros t Hin.
  apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
  apply in_seq in Hi. simpl. lia.
Qed.

Lemma fresh_args_open_args : forall start bound k,
  start <= bound ->
  runtime_open_args (bound + k) (map tvar (seq start k)).
Proof. exact fresh_args_closed. Qed.
