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

(** A successful [Unify] on closed terms yields a closed substitution. *)
Lemma Unify_closed : forall c t1 t2 s s',
  closed_term 0 c t1 ->
  closed_term 0 c t2 ->
  closed_sub c s ->
  Unify t1 t2 s (Some s') ->
  closed_sub c s'.
Proof. Admitted.

Lemma Head_closed : forall G c t t',
  closed_env G -> closed_tree G c t -> Head G t t' ->
  exists c', closed_tree G c' t'.
Proof. Admitted.


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

Lemma Head_tight : forall G t t',
  closed_env G -> tight_tree G t -> Head G t t' ->
  tight_tree G t'.
Proof. Admitted.


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

(* Every state in r' has a corresponding state in r with counter <= st_cnt s',
   so any closed_goal condition transfers across a head step. *)
Lemma Head_closed_goal_transfer : forall G r r' g,
  Head G r r' ->
  (forall s, state_in r s -> closed_goal G 0 (st_cnt s) g) ->
  forall s', state_in r' s' -> closed_goal G 0 (st_cnt s') g.
Proof. Admitted.

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
