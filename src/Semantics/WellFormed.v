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
        apply closed_term_mono with (d:=d) (d':=d+n) (c:=c) (c':=c+n).
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
  - destruct H as [Hcnt [Hg Hs]]. repeat split.
    * lia.
    * exact (closed_goal_mono G 0 0 c c' _ (Nat.le_refl 0) Hle Hg).
    * eapply closed_sub_mono; eassumption.
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
  - discriminate Hhead.
  - destruct g.
    * (*gsucc*) discriminate.
    * (*gunify*)
      destruct Ht as [Hcnt [Htcg Htcs]].
      destruct (unify t t0 (st_sub s)) eqn:E.
      + injection Hhead as <-. exists c. simpl.
        refine (conj _ (conj I _)).
        -- lia.
        -- eapply unify_closed.
           ** simpl in Htcg. exact (proj1 Htcg).
           ** simpl in Htcg. exact (proj2 Htcg).
           ** exact Htcs.
           ** exact E.
      + injection Hhead as <-. exists c. exact I.
    * (*grelcall*)
      destruct Ht as [Hcnt [Htcg Htcs]].
      injection Hhead as <-. exists c. simpl.
      destruct (nth_error G n) eqn:E.
      + destruct p. repeat split.
        -- lia.
        -- simpl in Htcg. rewrite E in Htcg. exact (proj1 Htcg).
        -- eapply Forall_impl.
           ** intros a Ha. exact Ha.
           ** simpl in Htcg. rewrite E in Htcg. exact (proj2 Htcg).
        -- exact Htcs.
      + simpl in Htcg. rewrite E in Htcg. exact Htcg.
    * (*gdisj*)
      destruct Ht as [Hcnt [Htcg Htcs]].
      injection Hhead as <-. exists c. simpl. repeat split.
      + lia.
      + simpl in Htcg. exact (proj1 Htcg).
      + exact Htcs.
      + lia.
      + simpl in Htcg. exact (proj2 Htcg).
      + exact Htcs.
    * (*gconj*)
      destruct Ht as [Hcnt [Htcg Htcs]].
      injection Hhead as <-. exists c. simpl. split.
      + repeat split.
        -- exact Hcnt.
        -- simpl in Htcg. exact (proj1 Htcg).
        -- exact Htcs.
      + simpl in Htcg. exact (proj2 Htcg).
    * (*gfresh*)
      destruct Ht as [Hcnt [Htcg Htcs]].
      injection Hhead as <-. exists (c + n). simpl. repeat split.
      + lia.
      + apply open_closed.
        -- rewrite length_map, length_seq. simpl in Htcg. exact Htcg.
        -- apply Forall_forall. intros x Hin.
           apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
           apply in_seq in Hi. simpl. lia.
      + exact (closed_sub_mono c (c + n) _ (Nat.le_add_r c n) Htcs).
  - (* tdelay *)
    discriminate Hhead.
  - (* tproceed *)
    destruct (nth_error G n) eqn:E; [|exact (False_ind _ Ht)].
    destruct p as [arity body].
    destruct Ht as [Hcnt [Hlen [Hfa Htcs]]].
    destruct (Nat.eqb (length l) arity) eqn:Eqa; [|discriminate Hhead].
    injection Hhead as <-. exists c.
    apply Nat.eqb_eq in Eqa.
    simpl. refine (conj Hcnt (conj _ Htcs)).
    apply open_closed.
    + rewrite Hlen.
      exact (closed_goal_mono G arity arity 0 c _ (Nat.le_refl arity) (Nat.le_0_l c) (HG n arity body E)).
    + exact Hfa.
  - (* tconj: tconj t g_outer; remaining cases after discriminate: tfail, tgoal, tdelay, tdisjL, tdisjR *)
    destruct t as [| gc sc | td | rp lp sp | tci gci | tl1 tl2 | tr1 tr2];
      simpl in Hhead; try discriminate Hhead.
    * (* PruneConj: tconj tfail g_outer *)
      injection Hhead as <-. exists c. exact I.
    * (* SuccConj: tconj (tgoal gc sc) g_outer — any gc *)
      injection Hhead as <-.
      destruct Ht as [[Hcnt [_ Htcs]] Hg].
      exists c. split; [exact Hcnt | split; [exact Hg | exact Htcs]].
    * (* DelayConj: tconj (tdelay td) g_outer *)
      injection Hhead as <-.
      destruct Ht as [Htct Hg].
      exists c. split; [exact Htct | exact Hg].
    * (* LeftAnsConj: tconj (tdisjL tl1 tl2) g_outer *)
      destruct tl1 as [| gl1 sl1 | | | | tll1 tlr1 | trl1 trr1];
        simpl in Hhead; try discriminate Hhead.
      (* only tl1 = tgoal gl1 sl1 survives *)
      injection Hhead as <-.
      destruct Ht as [[Htct1 Htct2] Hg].
      exists c. split.
      + split; [exact Htct1 | exact Hg].
      + split; [exact Htct2 | exact Hg].
    * (* RightAnsConj: tconj (tdisjR tr1 tr2) g_outer *)
      destruct tr2 as [| gr2 sr2 | | | | tll2 tlr2 | trl2 trr2];
        simpl in Hhead; try discriminate Hhead.
      (* only tr2 = tgoal gr2 sr2 survives *)
      injection Hhead as <-.
      destruct Ht as [[Htct1 Htct2] Hg].
      exists c. split.
      + split; [exact Htct1 | exact Hg].
      + split; [exact Htct2 | exact Hg].
  - (* tdisjL: tdisjL t1 t2; remaining: tfail, tdelay, tdisjL, tdisjR *)
    destruct t1 as [| g1 s1 | td1 | | | tl1a tl1b | tr1a tr1b];
      simpl in Hhead; try discriminate Hhead.
    * (* PruneLeft: tdisjL tfail t2 *)
      injection Hhead as <-. exists c. exact (proj2 Ht).
    * (* DelayLeft: tdisjL (tdelay td1) t2 *)
      injection Hhead as <-. exists c.
      destruct Ht as [Htl Htr]. split; [exact Htl | exact Htr].
    * (* AssocLeftLeft: tdisjL (tdisjL tl1a tl1b) t2 *)
      destruct tl1a as [| gll sll | | | | | ];
        simpl in Hhead; try discriminate Hhead.
      (* only tl1a = tgoal gll sll survives *)
      injection Hhead as <-.
      destruct Ht as [[Htll Htlr] Htr].
      exists c. split; [exact Htll | split; [exact Htlr | exact Htr]].
    * (* AssocLeftRight: tdisjL (tdisjR tr1a tr1b) t2 *)
      destruct tr1b as [| grl srl | | | | | ];
        simpl in Hhead; try discriminate Hhead.
      (* only tr1b = tgoal grl srl survives *)
      injection Hhead as <-.
      destruct Ht as [[Htll Htlr] Htr].
      exists c. split; [split; [exact Htll | exact Htr] | exact Htlr].
  - (* tdisjR: tdisjR t1 t2; remaining: tfail, tdelay, tdisjL, tdisjR *)
    destruct t2 as [| g2 s2 | td2 | | | tl2a tl2b | tr2a tr2b];
      simpl in Hhead; try discriminate Hhead.
    * (* PruneRight: tdisjR t1 tfail *)
      injection Hhead as <-. exists c. exact (proj1 Ht).
    * (* DelayRight: tdisjR t1 (tdelay td2) → tdelay (tdisjL t1 td2) *)
      injection Hhead as <-.
      destruct Ht as [Htl Htr].
      exists c. split; [exact Htl | exact Htr].
    * (* AssocRightLeft: tdisjR t1 (tdisjL tl2a tl2b) *)
      destruct tl2a as [| grl2 srl2 | | | | | ];
        simpl in Hhead; try discriminate Hhead.
      (* only tl2a = tgoal grl2 srl2 survives *)
      injection Hhead as <-.
      destruct Ht as [Htl [Htrl Htrr]].
      exists c. split; [exact Htrl | split; [exact Htl | exact Htrr]].
    * (* AssocRightRight: tdisjR t1 (tdisjR tr2a tr2b) *)
      destruct tr2b as [| grr2 srr2 | | | | | ];
        simpl in Hhead; try discriminate Hhead.
      (* only tr2b = tgoal grr2 srr2 survives *)
      injection Hhead as <-.
      destruct Ht as [Htl [Htrl Htrr]].
      exists c. split; [split; [exact Htl | exact Htrl] | exact Htrr].
Qed.
