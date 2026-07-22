From Stdlib Require Import List Arith Lia.
Import ListNotations.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees.
Require Import MkRedex.Semantics.Reduction.
Set Default Goal Selector "!".

Fixpoint closed_term (d c : nat) (t : term) : Prop :=
  match t with
  | tnil      => True
  | tvar n    => n < c
  | tpar i    => i < d
  | tsym _    => True
  | tstr _    => True
  | tnat _    => True
  | tbool _   => True
  | tcons a b => closed_term d c a /\ closed_term d c b
  end.

Fixpoint closed_sub (c : nat) (s : sub) : Prop :=
  match s with
  | []           => True
  | (n, t) :: s' => n < c /\ closed_term 0 c t /\ closed_sub c s'
  end.

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
  | gfresh k g1  => closed_goal G (d + k) (c + k) g1
  end.

Fixpoint closed_tree (G : env) (c : nat) (t : tree) : Prop :=
  match t with
  | tfail           => True
  | tgoal g s       =>
      st_cnt s <= c /\
      closed_goal G 0 (st_cnt s) g /\
      closed_sub (st_cnt s) (st_sub s)
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
        apply (closed_term_mono d (d + n) c (c + n)).
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
        eapply closed_term_mono with (d:=0) (d':=n) (c:=c) (c':=c+n).
        1, 2: lia.
        exact Ht.
      + exact H2.
Qed.

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
  - apply IHg with (d := d + n) (c := c + n); [lia | lia | exact H].
Qed.

Lemma closed_tree_mono : forall G c c' t,
  c <= c' -> closed_tree G c t -> closed_tree G c' t.
Proof.
  intros G c c' t Hle. induction t; simpl; intros H.
  - exact H.
  - destruct H as [Hg Hs]. repeat split.
    * lia.
    * exact (proj1 Hs).
    * exact (proj2 Hs).
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



(* Successfully unifying two closed terms in a closed sub yields a closed sub *)
Lemma unify_f_closed : forall fuel c t1 t2 s s',
  closed_term 0 c t1 -> closed_term 0 c t2 -> closed_sub c s ->
  unify_f fuel t1 t2 s = Some s' -> closed_sub c s'.
Proof.
  induction fuel as [|f IH]; intros c t1 t2 s s' Ht1 Ht2 Hcs H.
  - unfold unify_f in H. discriminate.
  - assert (Ha : closed_term 0 c (walk t1 s)) by (apply walk_closed; assumption).
    assert (Hb : closed_term 0 c (walk t2 s)) by (apply walk_closed; assumption).
    destruct (walk t1 s) eqn:Et1; destruct (walk t2 s) eqn: Et2;
    unfold unify_f in H; rewrite Et1 in H; rewrite Et2 in H;
    simpl in H, Ha, Hb; try discriminate H.
    * destruct (Nat.eqb n n0).
      + injection H as <-. exact Hcs.
      + injection H as <-. simpl. repeat split; assumption.
    * lia.
    * injection H as <-. repeat split; assumption.
    * injection H as <-. repeat split; assumption.
    * injection H as <-. repeat split; assumption.
    * injection H as <-. repeat split; assumption.
    * injection H as <-. repeat split; assumption.
    * destruct (occurs _ _); simpl in H.
      + discriminate H.
      + destruct (occurs _ _).
        -- discriminate H.
        -- injection H as <-. destruct Hb as [Hb1 Hb2]. repeat split; assumption.
    * injection H as <-. repeat split; assumption.
    * destruct ((n =? n0)%nat).
      + injection H as <-. exact Hcs.
      + discriminate H.
    * injection H as <-. simpl. repeat split; assumption.
    * destruct (String.eqb _ _).
      + injection H as <-. exact Hcs.
      + discriminate H.
    * injection H as <-. simpl. repeat split; assumption.
    * destruct (String.eqb _ _).
      + injection H as <-. exact Hcs.
      + discriminate H.
    * injection H as <-. simpl. repeat split; assumption.
    * destruct ((n =? n0)%nat).
      + injection H as <-. exact Hcs.
      + discriminate H.
    * injection H as <-. simpl. repeat split; assumption.
    * destruct (Bool.eqb _ _).
      + injection H as <-. simpl. repeat split; assumption.
      + discriminate H.
    * injection H as <-. simpl. repeat split; assumption.
    * injection H as <-. simpl. repeat split; assumption.
    * destruct (occurs _ _); simpl in H.
      + discriminate H.
      + destruct (occurs _ _).
        -- discriminate H.
        -- injection H as <-. destruct Ha as [Ha1 Ha2]. repeat split; assumption.
    * destruct Ha as [Ha1 Ha2], Hb as [Hb1 Hb2].
      change (match unify_f f t3 t5 s with
              | Some s1 => unify_f f t4 t6 s1
              | None => None
              end = Some s') in H.
      destruct (unify_f f t3 t5 s) eqn:E1; [|discriminate H].
      assert (Hs1 : closed_sub c s0) by (eapply IH; [exact Ha1 | exact Hb1 | exact Hcs | exact E1]).
      eapply IH; [exact Ha2 | exact Hb2 | exact Hs1 | exact H].
Qed.

Lemma unify_closed : forall c t1 t2 s s',
  closed_term 0 c t1 ->
  closed_term 0 c t2 ->
  closed_sub c s -> 
  unify t1 t2 s = Some s' -> 
  closed_sub c s'.
Proof.
  intros. unfold unify in H2. exact (unify_f_closed _ _ _ _ _ _ H H0 H1 H2).
Qed.

Lemma head_closed : forall G c t t',
  closed_env G -> closed_tree G c t -> head G t = Some t' ->
  exists c', closed_tree G c' t'.
Proof.
  intros G c t t' HG Ht Hhead.
  destruct t; simpl in *.
  - (*tfail*) discriminate Hhead.
  - (*tgoal*) destruct g; destruct Ht as [Hlt [Hcg Hcs]].
    * (*gsucc*) discriminate.
    * (*gunify*) exists c.
      destruct (unify t t0 (st_sub s)) eqn:Eunify. 
      + injection Hhead as <-. simpl. repeat split.
        -- exact Hlt.
        -- simpl in Hcg. destruct Hcg as [Hct Hct0].
           apply (unify_closed (st_cnt s) t t0 (st_sub s) s0); try assumption.
      + injection Hhead as <-. simpl. apply I.
    * (*relcall*) exists c. injection Hhead as <-. simpl.
      destruct (nth_error G n) eqn:E.
      + destruct p; simpl in Hcg; rewrite E in Hcg; destruct Hcg. repeat split.
        -- exact Hlt.
        -- exact H.
        -- eapply Forall_impl.
           ** intros t Ht. exact (closed_term_mono 0 0 (st_cnt s) c t (Nat.le_refl 0) Hlt Ht).
           ** exact H0.
        -- eapply closed_sub_mono; eassumption.
      + simpl in Hcg. rewrite E in Hcg. destruct Hcg.
    * (*disj*) exists c. injection Hhead as <-. simpl. repeat split.
      1, 3, 4, 6: assumption.
      + exact (proj1 Hcg).
      + exact (proj2 Hcg).
    * (*conj*) exists c. injection Hhead as <-. simpl. repeat split.
      1, 3: assumption.
      + exact (proj1 Hcg).
      + simpl in Hcg. destruct Hcg as [_ Hcg].
        exact (closed_goal_mono G 0 0 (st_cnt s) c g2 (Nat.le_refl 0) Hlt Hcg).
    * (*fresh*) exists (c + n). injection Hhead as <-. simpl. repeat split.
      + lia. 
      + apply open_goal_closed.
         -- simpl in Hcg. 
            rewrite length_map. rewrite length_seq. rewrite Nat.add_0_r.
            exact Hcg.
         -- rewrite Forall_map. apply Forall_forall.
            intros x Hx.
            apply in_seq in Hx.
            simpl. lia. 
      + exact (closed_sub_mono (st_cnt s) (st_cnt s + n) (st_sub s) (Nat.le_add_r _ _ ) Hcs).
  - (*tdelay*) discriminate Hhead.
  - (*tproceed*) destruct (nth_error G n) eqn:Ea.
    * exists c. 
      destruct p as [n0 body]. 
      destruct Ht as [Hle [Hlen [Hfa Hcs]]].
      rewrite <- Hlen, Nat.eqb_refl in Hhead.
      injection Hhead as <-.
      repeat split.
      + exact Hle.
      + apply open_closed.
         -- rewrite Hlen.
            exact (closed_goal_mono G n0 n0 0 (st_cnt s) body
                     (Nat.le_refl n0) (Nat.le_0_l (st_cnt s))
                     (HG n n0 body Ea)).




Lemma tgoal_sub_wf : forall G c g s,
  closed_tree G c (tgoal g s) ->
  closed_sub (st_cnt s) (st_sub s).

Lemma step_closed : forall G c e e',
  closed_env G ->
  closed_tree G c (snd e) ->
  Forall (fun s => closed_sub (st_cnt s) (st_sub s)) (fst e) ->
  G |= e --> e' ->
  exists c',
    closed_tree G c' (snd e') /\
    Forall (fun s => closed_sub (st_cnt s) (st_sub s)) (fst e').

Lemma multi_closed : forall G e e',
  multi G e e' ->
  forall c,
    closed_env G ->
    closed_tree G c (snd e) ->
    Forall (fun s => closed_sub (st_cnt s) (st_sub s)) (fst e) ->
    exists c',
      closed_tree G c' (snd e') /\
      Forall (fun s => closed_sub (st_cnt s) (st_sub s)) (fst e').
