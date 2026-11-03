From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import MkRedex.Language.Terms.
Require Import MkRedex.Language.Substitution.
Set Default Goal Selector "!".

(* UnifyW *)

Inductive UnifyW : term -> term -> sub -> option sub -> Prop :=

  | UW_var_same : forall x s,
      UnifyW (tvar x) (tvar x) s (Some s)

  | UW_var_bind : forall x u s,
      lookup x s = None ->
      u <> tvar x ->
      ~ DeepOccurs s x u ->
      UnifyW (tvar x) u s (Some ((x, u) :: s))

  | UW_var_fail : forall x u s,
      u <> tvar x ->
      DeepOccurs s x u ->
      UnifyW (tvar x) u s None

  | UW_sym_bind : forall u y s,
      lookup y s = None ->
      (forall z, u <> tvar z) ->
      ~ DeepOccurs s y u ->
      UnifyW u (tvar y) s (Some ((y, u) :: s))

  | UW_sym_fail : forall u y s,
      (forall z, u <> tvar z) ->
      DeepOccurs s y u ->
      UnifyW u (tvar y) s None

  | UW_cons_ok : forall a1 a2 b1 b2 wa1 wb1 wa2 wb2 s s1 r,
      Walk s a1 wa1 ->
      Walk s b1 wb1 ->
      UnifyW wa1 wb1 s (Some s1) ->
      Walk s1 a2 wa2 ->
      Walk s1 b2 wb2 ->
      UnifyW wa2 wb2 s1 r ->
      UnifyW (tcons a1 a2) (tcons b1 b2) s r

  | UW_cons_fail : forall a1 a2 b1 b2 wa1 wb1 s,
      Walk s a1 wa1 ->
      Walk s b1 wb1 ->
      UnifyW wa1 wb1 s None ->
      UnifyW (tcons a1 a2) (tcons b1 b2) s None

  | UW_cons_clash_r : forall a1 a2 v s,
      (forall x, v <> tvar x) ->
      (forall c1 c2, v <> tcons c1 c2) ->
      UnifyW (tcons a1 a2) v s None

  | UW_cons_clash_l : forall u b1 b2 s,
      (forall x, u <> tvar x) ->
      (forall c1 c2, u <> tcons c1 c2) ->
      UnifyW u (tcons b1 b2) s None

  | UW_rigid_eq : forall u s,
      (forall x, u <> tvar x) ->
      (forall a b, u <> tcons a b) ->
      UnifyW u u s (Some s)

  | UW_rigid_neq : forall u v s,
      u <> v ->
      (forall x, u <> tvar x) ->
      (forall x, v <> tvar x) ->
      (forall a b, u <> tcons a b) ->
      (forall a b, v <> tcons a b) ->
      UnifyW u v s None.

Hint Constructors UnifyW : core.

Definition Unify (t1 t2 : term) (s : sub) (r : option sub) : Prop :=
  exists w1 w2, Walk s t1 w1 /\ Walk s t2 w2 /\ UnifyW w1 w2 s r.

Hint Unfold Unify : core.

(* Functionality *)

Lemma UnifyW_functional : forall w1 w2 s r r',
  UnifyW w1 w2 s r -> UnifyW w1 w2 s r' -> r = r'.
Proof.
  intros w1 w2 s r r' H.
  generalize dependent r'.
  induction H; intros r' H'; inversion H'; subst;
  try reflexivity; try congruence;
  try (exfalso; match goal with H : forall _ _, _ <> tcons _ _ |- _ => exact (H _ _ eq_refl) end);
  try (exfalso; match goal with H : forall _, tvar _ <> tvar _ |- _ => exact (H _ eq_refl) end).
  - (* UW_cons_ok vs UW_cons_ok *)
    match goal with
    | Hwa1 : Walk s a1 ?wa1, Hwa1' : Walk s a1 ?wa1',
      Hwb1 : Walk s b1 ?wb1, Hwb1' : Walk s b1 ?wb1',
      IH1 : forall r', UnifyW ?wa1 ?wb1 s r' -> Some s1 = r',
      Huw1' : UnifyW ?wa1' ?wb1' s (Some _)
      |- _ =>
      rewrite (Walk_functional s a1 _ _ Hwa1 Hwa1') in IH1;
      rewrite (Walk_functional s b1 _ _ Hwb1 Hwb1') in IH1;
      apply IH1 in Huw1'; injection Huw1' as <-
    end;
    match goal with
    | Hwa2 : Walk s1 a2 ?wa2, Hwa2' : Walk s1 a2 ?wa2',
      Hwb2 : Walk s1 b2 ?wb2, Hwb2' : Walk s1 b2 ?wb2',
      IH2 : forall r', UnifyW ?wa2 ?wb2 s1 r' -> r = r'
      |- _ =>
      rewrite (Walk_functional s1 a2 _ _ Hwa2 Hwa2') in IH2;
      rewrite (Walk_functional s1 b2 _ _ Hwb2 Hwb2') in IH2
    end;
    eauto.
  - (* UW_cons_ok vs UW_cons_fail *)
    match goal with
    | Hwa1 : Walk s a1 ?wa1, Hwa1' : Walk s a1 ?wa1',
      Hwb1 : Walk s b1 ?wb1, Hwb1' : Walk s b1 ?wb1',
      IH1 : forall r', UnifyW ?wa1 ?wb1 s r' -> Some s1 = r',
      Huw1' : UnifyW ?wa1' ?wb1' s None
      |- _ =>
      rewrite (Walk_functional s a1 _ _ Hwa1 Hwa1') in IH1;
      rewrite (Walk_functional s b1 _ _ Hwb1 Hwb1') in IH1;
      apply IH1 in Huw1'; discriminate
    end.
  - (* UW_cons_fail vs UW_cons_ok *)
    match goal with
    | Hwa1 : Walk s a1 ?wa1, Hwa1' : Walk s a1 ?wa1',
      Hwb1 : Walk s b1 ?wb1, Hwb1' : Walk s b1 ?wb1',
      IH1 : forall r', UnifyW ?wa1 ?wb1 s r' -> None = r',
      Huw1' : UnifyW ?wa1' ?wb1' s (Some _)
      |- _ =>
      rewrite (Walk_functional s a1 _ _ Hwa1 Hwa1') in IH1;
      rewrite (Walk_functional s b1 _ _ Hwb1 Hwb1') in IH1;
      apply IH1 in Huw1'; discriminate
    end.
Qed.

Lemma Unify_functional : forall t1 t2 s r r',
  Unify t1 t2 s r -> Unify t1 t2 s r' -> r = r'.
Proof.
  unfold Unify. intros.
  destruct H as (w1 & w2 & Hw1 & Hw2 & Hu),
           H0 as (w1' & w2' & Hw1' & Hw2' & Hu').
  rewrite (Walk_functional _ _ _ _ Hw1 Hw1') in Hu.
  rewrite (Walk_functional _ _ _ _ Hw2 Hw2') in Hu.
  exact (UnifyW_functional _ _ _ _ _ Hu Hu').
Qed.

(* Structural Properties *)

Lemma UnifyW_extends : forall w1 w2 s r,
  UnifyW w1 w2 s r ->
  forall s', r = Some s' -> exists prefix, s' = prefix ++ s.
Proof.
  intros w1 w2 s r H.
  induction H; intros s' Hr; inversion Hr; subst.
  - exists []. reflexivity.
  - exists [(x, u)]. reflexivity.
  - exists [(y, u)]. reflexivity.
  - destruct (IHUnifyW1 s1 eq_refl) as [p1 Hp1].
    destruct (IHUnifyW2 s' eq_refl) as [p2 Hp2].
    rewrite Hp1 in Hp2. exists (p2 ++ p1).
    rewrite <- app_assoc. exact Hp2.
  - exists []. reflexivity.
Qed.

Lemma Unify_extends : forall t1 t2 s r,
  Unify t1 t2 s r ->
  forall s', r = Some s' -> exists prefix, s' = prefix ++ s.
Proof.
  unfold Unify. intros t1 t2 s r Hu s' Hr.
  destruct Hu as (w1 & w2 & _ & _ & Hu).
  exact (UnifyW_extends _ _ _ _ Hu s' Hr).
Qed.

Lemma UnifyW_norebind : forall w1 w2 s r,
  UnifyW w1 w2 s r ->
  forall s', r = Some s' ->
  forall z t, lookup z s = Some t -> lookup z s' = Some t.
Proof.
  intros w1 w2 s r Hunify.
  induction Hunify; intros s'' Hr z t Hz; inversion Hr; subst.
  - exact Hz.
  - simpl. destruct (Nat.eqb_spec z x) as [-> | ]; [congruence | exact Hz].
  - simpl. destruct (Nat.eqb_spec z y) as [-> | ]; [congruence | exact Hz].
  - exact (IHHunify2 s'' eq_refl z t (IHHunify1 s1 eq_refl z t Hz)).
  - exact Hz.
Qed.

Lemma lookup_app_r : forall (x : nat) (prefix s : sub),
  lookup x prefix = None ->
  lookup x (prefix ++ s) = lookup x s.
Proof.
  intros x prefix. induction prefix as [| [y t] rest IH]; intros s Hpre; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x y); [discriminate | exact (IH s Hpre)].
Qed.

Lemma ApplySub_suffix_extend : forall s s',
  (forall x t, lookup x s = Some t -> lookup x s' = Some t) ->
  forall t r, ApplySub s' t r ->
  exists v, ApplySub s t v /\ ApplySub s' v r.
Proof.
  intros s s' Hext t r Happ.
  induction Happ as [x Hfree | x u r Hlook Hsubu IHsubu
                    | a b a' b' Ha IHa Hb IHb
                    | t Hnotvar Hnotcons].
  - assert (Hs : lookup x s = None). {
      destruct (lookup x s) as [u|] eqn:Heq; [| reflexivity].
      pose proof (Hext x u Heq). congruence. }
    exists (tvar x). exact (conj (AS_free s x Hs) (AS_free s' x Hfree)).
  - destruct IHsubu as [v_u [Hv_u_s Hv_u_s']].
    destruct (lookup x s) as [u1|] eqn:Hs_x.
    + rewrite (Hext x u1 Hs_x) in Hlook. injection Hlook as ->.
      exists v_u. exact (conj (AS_bound s x u v_u Hs_x Hv_u_s) Hv_u_s').
    + exists (tvar x). exact (conj (AS_free s x Hs_x) (AS_bound s' x u r Hlook Hsubu)).
  - destruct IHa as [va [Hsa Hs'a]], IHb as [vb [Hsb Hs'b]].
    exists (tcons va vb).
    exact (conj (AS_cons s a b va vb Hsa Hsb) (AS_cons s' va vb a' b' Hs'a Hs'b)).
  - exists t. exact (conj (AS_rigid s t Hnotvar Hnotcons) (AS_rigid s' t Hnotvar Hnotcons)).
Qed.

Lemma Walk_ApplySub_compat : forall s t w,
  Walk s t w ->
  forall s', (forall x u, lookup x s = Some u -> lookup x s' = Some u) ->
  forall r, ApplySub s' t r -> ApplySub s' w r.
Proof.
  intros s t w Hwalk.
  induction Hwalk as [x Hfree | x u w Hlook _ IH | t Hnotvar];
  intros s' Hext r Happ.
  - exact Happ.
  - assert (Hx' : lookup x s' = Some u) by exact (Hext x u Hlook).
    inversion Happ; subst.
    + congruence.
    + match goal with H1 : lookup x s' = Some ?u0, H2 : ApplySub s' ?u0 r |- _ =>
        rewrite Hx' in H1; injection H1 as <-; exact (IH s' Hext r H2) end.
    + exfalso; match goal with H : forall _ : nat, tvar _ <> tvar _ |- _ =>
        exact (H x eq_refl) end.
  - exact Happ.
Qed.

(* Acyclicity Preservation *)

Lemma occurs_trans_DeepOccurs : forall s x c t,
  occurs c t = true -> DeepOccurs s x (tvar c) -> DeepOccurs s x t.
Proof.
  intros s x c. induction t; simpl; intros H HDO; try discriminate H.
  - apply Nat.eqb_eq in H. subst. exact HDO.
  - destruct (occurs c t1) eqn:H1.
    + apply DO_cons_l. exact (IHt1 eq_refl HDO).
    + simpl in H. apply DO_cons_r. exact (IHt2 H HDO).
Qed.

Lemma UnifyW_acyclic_gen : forall w1 w2 s r,
  UnifyW w1 w2 s r ->
  acyclic_sub s ->
  forall s', r = Some s' -> acyclic_sub s'.
Proof.
  unfold acyclic_sub.
  intros w1 w2 s r Hunify.
  induction Hunify; intros Hacyclic s'' Hr; inversion Hr; subst.
  - exact Hacyclic.
  - assert (step_E : forall a,
        ~ DeepOccurs s x (tvar a) ->
        Acc (fun y z => exists t, lookup z ((x, u) :: s) = Some t /\ occurs y t = true) a).
    { apply (well_founded_ind Hacyclic (fun a =>
          ~ DeepOccurs s x (tvar a) ->
          Acc (fun y z => exists t, lookup z ((x, u) :: s) = Some t /\ occurs y t = true) a)).
      intros a IH HnDO.
      assert (Hax : a <> x) by (intro Heq; subst; exact (HnDO (DO_var s x))).
      apply Acc_intro. intros c (ta & Hla & Hoc).
      simpl in Hla. rewrite (proj2 (Nat.eqb_neq a x) Hax) in Hla.
      assert (HnDOt : ~ DeepOccurs s x ta)
        by (intro Hd; exact (HnDO (DO_walk s x a ta Hla Hd))).
      apply (IH c (ex_intro _ ta (conj Hla Hoc))).
      intro Hdc; exact (HnDOt (occurs_trans_DeepOccurs s x c ta Hoc Hdc)). }
    assert (acc_x :
        Acc (fun y z => exists t, lookup z ((x, u) :: s) = Some t /\ occurs y t = true) x).
    { apply Acc_intro. intros c (tx & Hlx & Hoc).
      simpl in Hlx. rewrite Nat.eqb_refl in Hlx. simpl in Hlx. injection Hlx as <-.
      apply step_E.
      intro Hdc; exact (H1 (occurs_trans_DeepOccurs s x c u Hoc Hdc)). }
    intro a. destruct (Nat.eqb_spec a x) as [-> | Hax].
    + exact acc_x.
    + revert a Hax.
      apply (well_founded_ind Hacyclic (fun a => a <> x ->
          Acc (fun y z => exists t, lookup z ((x, u) :: s) = Some t /\ occurs y t = true) a)).
      intros a IH Hax.
      apply Acc_intro. intros c (ta & Hla & Hoc).
      simpl in Hla. rewrite (proj2 (Nat.eqb_neq a x) Hax) in Hla.
      destruct (Nat.eqb_spec c x) as [-> | Hcx].
      * exact acc_x.
      * exact (IH c (ex_intro _ ta (conj Hla Hoc)) Hcx).
  - assert (step_E : forall a,
        ~ DeepOccurs s y (tvar a) ->
        Acc (fun c z => exists t, lookup z ((y, u) :: s) = Some t /\ occurs c t = true) a).
    { apply (well_founded_ind Hacyclic (fun a =>
          ~ DeepOccurs s y (tvar a) ->
          Acc (fun c z => exists t, lookup z ((y, u) :: s) = Some t /\ occurs c t = true) a)).
      intros a IH HnDO.
      assert (Hay : a <> y) by (intro Heq; subst; exact (HnDO (DO_var s y))).
      apply Acc_intro. intros c (ta & Hla & Hoc).
      simpl in Hla. rewrite (proj2 (Nat.eqb_neq a y) Hay) in Hla.
      assert (HnDOt : ~ DeepOccurs s y ta)
        by (intro Hd; exact (HnDO (DO_walk s y a ta Hla Hd))).
      apply (IH c (ex_intro _ ta (conj Hla Hoc))).
      intro Hdc; exact (HnDOt (occurs_trans_DeepOccurs s y c ta Hoc Hdc)). }
    assert (acc_y :
        Acc (fun c z => exists t, lookup z ((y, u) :: s) = Some t /\ occurs c t = true) y).
    { apply Acc_intro. intros c (ty & Hly & Hoc).
      simpl in Hly. rewrite Nat.eqb_refl in Hly. simpl in Hly. injection Hly as <-.
      apply step_E.
      intro Hdc; exact (H1 (occurs_trans_DeepOccurs s y c u Hoc Hdc)). }
    intro a. destruct (Nat.eqb_spec a y) as [-> | Hay].
    + exact acc_y.
    + revert a Hay.
      apply (well_founded_ind Hacyclic (fun a => a <> y ->
          Acc (fun c z => exists t, lookup z ((y, u) :: s) = Some t /\ occurs c t = true) a)).
      intros a IH Hay.
      apply Acc_intro. intros c (ta & Hla & Hoc).
      simpl in Hla. rewrite (proj2 (Nat.eqb_neq a y) Hay) in Hla.
      destruct (Nat.eqb_spec c y) as [-> | Hcy].
      * exact acc_y.
      * exact (IH c (ex_intro _ ta (conj Hla Hoc)) Hcy).
  - apply IHHunify2.
    + exact (IHHunify1 Hacyclic s1 eq_refl).
    + reflexivity.
  - exact Hacyclic.
Qed.

Lemma UnifyW_acyclic : forall w1 w2 s s',
  acyclic_sub s -> UnifyW w1 w2 s (Some s') -> acyclic_sub s'.
Proof.
  intros w1 w2 s s' Hacyclic Hunify.
  exact (UnifyW_acyclic_gen w1 w2 s (Some s') Hunify Hacyclic s' eq_refl).
Qed.

Lemma Unify_acyclic : forall t1 t2 s s',
  acyclic_sub s -> Unify t1 t2 s (Some s') -> acyclic_sub s'.
Proof.
  intros t1 t2 s s' Hacyclic Hunify.
  destruct Hunify as (w1 & w2 & Hw1 & Hw2 & Hu).
  exact (UnifyW_acyclic w1 w2 s s' Hacyclic Hu).
Qed.

(* Soundness *)

Lemma UnifyW_sound_gen : forall w1 w2 s r,
  UnifyW w1 w2 s r ->
  acyclic_sub s ->
  forall s', r = Some s' ->
  forall r1 r2, ApplySub s' w1 r1 -> ApplySub s' w2 r2 -> r1 = r2.
Proof.
  intros w1 w2 s r Hunify.
  induction Hunify; intros Hacyclic s'' Hr r1 r2 HApp1 HApp2; inversion Hr; subst.
  - exact (ApplySub_functional _ _ _ _ HApp1 HApp2).
  - assert (Hlu : lookup x ((x, u) :: s) = Some u) by (simpl; rewrite Nat.eqb_refl; reflexivity).
    inversion HApp1; subst; try congruence.
    match goal with H1 : lookup x ((x, u) :: s) = Some ?u0, H2 : ApplySub _ ?u0 r1 |- _ =>
      rewrite Hlu in H1; injection H1 as <-; exact (ApplySub_functional _ _ _ _ H2 HApp2) end.
  - assert (Hly : lookup y ((y, u) :: s) = Some u) by (simpl; rewrite Nat.eqb_refl; reflexivity).
    inversion HApp2; subst; try congruence.
    match goal with H1 : lookup y ((y, u) :: s) = Some ?u0, H2 : ApplySub _ ?u0 r2 |- _ =>
      rewrite Hly in H1; injection H1 as <-; exact (ApplySub_functional _ _ _ _ HApp1 H2) end.
  - assert (Hs1 : acyclic_sub s1) by exact (UnifyW_acyclic_gen _ _ _ _ Hunify1 Hacyclic s1 eq_refl).
    inversion HApp1 as [| | ? ? ra1 ra2 H1a H1b |]; subst.
    2: { exfalso; match goal with H : forall _ _, _ <> tcons _ _ |- _ => exact (H _ _ eq_refl) end. }
    inversion HApp2 as [| | ? ? rb1 rb2 H2a H2b |]; subst.
    2: { exfalso; match goal with H : forall _ _, _ <> tcons _ _ |- _ => exact (H _ _ eq_refl) end. }
    assert (Hext12 : forall z t, lookup z s1 = Some t -> lookup z s'' = Some t) by
      exact (UnifyW_norebind _ _ _ _ Hunify2 s'' eq_refl).
    assert (Hext01 : forall z t, lookup z s = Some t -> lookup z s1 = Some t) by
      exact (UnifyW_norebind _ _ _ _ Hunify1 s1 eq_refl).
    assert (Hwa2 : ApplySub s'' wa2 ra2) by
      exact (Walk_ApplySub_compat s1 a2 wa2 H1 s'' Hext12 ra2 H1b).
    assert (Hwb2 : ApplySub s'' wb2 rb2) by
      exact (Walk_ApplySub_compat s1 b2 wb2 H2 s'' Hext12 rb2 H2b).
    assert (Heq2 : ra2 = rb2) by exact (IHHunify2 Hs1 s'' eq_refl _ _ Hwa2 Hwb2).
    assert (Heq1 : ra1 = rb1). {
      destruct (ApplySub_suffix_extend s1 s'' Hext12 a1 ra1 H1a) as [v1 [Hv1_s1 Hv1_s'']].
      destruct (ApplySub_suffix_extend s1 s'' Hext12 b1 rb1 H2a) as [v2 [Hv2_s1 Hv2_s'']].
      assert (Hwa1 : ApplySub s1 wa1 v1) by
        exact (Walk_ApplySub_compat s a1 wa1 H s1 Hext01 v1 Hv1_s1).
      assert (Hwb1 : ApplySub s1 wb1 v2) by
        exact (Walk_ApplySub_compat s b1 wb1 H0 s1 Hext01 v2 Hv2_s1).
      assert (v1 = v2) by exact (IHHunify1 Hacyclic s1 eq_refl v1 v2 Hwa1 Hwb1).
      subst v2. exact (ApplySub_functional _ _ _ _ Hv1_s'' Hv2_s''). }
    subst. reflexivity.
  - exact (ApplySub_functional _ _ _ _ HApp1 HApp2).
Qed.

Lemma UnifyW_sound : forall w1 w2 s s',
  acyclic_sub s -> UnifyW w1 w2 s (Some s') ->
  forall r1 r2, ApplySub s' w1 r1 -> ApplySub s' w2 r2 -> r1 = r2.
Proof.
  intros w1 w2 s s' Hacyclic Hunify.
  exact (UnifyW_sound_gen w1 w2 s (Some s') Hunify Hacyclic s' eq_refl).
Qed.

Lemma Unify_sound : forall t1 t2 s s',
  acyclic_sub s -> Unify t1 t2 s (Some s') ->
  forall r1 r2, ApplySub s' t1 r1 -> ApplySub s' t2 r2 -> r1 = r2.
Proof.
  intros t1 t2 s s' Hacyclic Hunify r1 r2 HApp1 HApp2.
  destruct Hunify as (w1 & w2 & Hw1 & Hw2 & Hu).
  assert (Hext : forall x u, lookup x s = Some u -> lookup x s' = Some u) by
    exact (UnifyW_norebind _ _ _ _ Hu s' eq_refl).
  apply (Walk_ApplySub_compat s t1 w1 Hw1 s' Hext) in HApp1.
  apply (Walk_ApplySub_compat s t2 w2 Hw2 s' Hext) in HApp2.
  exact (UnifyW_sound w1 w2 s s' Hacyclic Hu r1 r2 HApp1 HApp2).
Qed.

(* Helpers for Completeness *)

Lemma Walk_tvar_free : forall s t y,
  Walk s t (tvar y) -> lookup y s = None.
Proof.
  intros s.
  enough (H : forall t w, Walk s t w -> forall y, w = tvar y -> lookup y s = None).
  { intros t y Hwalk. exact (H t (tvar y) Hwalk y eq_refl). }
  intros t w Hwalk.
  induction Hwalk as [x Hfree | x u w' Hlook _ IH | t' Hnotvar];
  intros y Heq.
  - injection Heq as ->. exact Hfree.
  - exact (IH y Heq).
  - exfalso. exact (Hnotvar y Heq).
Qed.

Lemma ApplySub_total : forall s, acyclic_sub s -> forall t, exists r, ApplySub s t r.
Proof.
  intros s Hac.
  assert (core : forall t,
      (forall y, occurs y t = true -> exists r, ApplySub s (tvar y) r) ->
      exists r, ApplySub s t r). {
    intro t. induction t; intros Hfree.
    - exact (Hfree n (Nat.eqb_refl n)).
    - eexists; apply AS_rigid; intros; discriminate.
    - eexists; apply AS_rigid; intros; discriminate.
    - eexists; apply AS_rigid; intros; discriminate.
    - eexists; apply AS_rigid; intros; discriminate.
    - eexists; apply AS_rigid; intros; discriminate.
    - eexists; apply AS_rigid; intros; discriminate.
    - assert (H1 : exists ra, ApplySub s t1 ra). {
        apply IHt1. intros y Hy. apply Hfree. simpl. rewrite Hy. reflexivity.
      }
      assert (H2 : exists rb, ApplySub s t2 rb). {
        apply IHt2. intros y Hy. apply Hfree. simpl. rewrite Hy.
        destruct (occurs y t1); reflexivity.
      }
      destruct H1 as [ra Ha].
      destruct H2 as [rb Hb].
      exact (ex_intro _ (tcons ra rb) (AS_cons s _ _ ra rb Ha Hb)).
  }
  assert (Hvar : forall y, exists r, ApplySub s (tvar y) r). {
    apply (well_founded_ind Hac). intros x IH.
    destruct (lookup x s) as [u|] eqn:Hlook.
    - assert (Hu : exists r, ApplySub s u r). {
        apply (core u). intros z Hz.
        exact (IH z (ex_intro _ u (conj eq_refl Hz))).
      }
      destruct Hu as [r Hr].
      exact (ex_intro _ r (AS_bound s x u r Hlook Hr)).
    - exact (ex_intro _ (tvar x) (AS_free s x Hlook)).
  }
  intro t. apply (core t). intros y _. exact (Hvar y).
Qed.

Lemma DeepOccurs_tsize : forall s x u,
  DeepOccurs s x u ->
  forall s2,
    (forall y t, lookup y s = Some t -> lookup y s2 = Some t) ->
    forall r1, ApplySub s2 (tvar x) r1 ->
    forall r2, ApplySub s2 u r2 ->
    tsize r1 <= tsize r2.
Proof.
  intros s x u HDO.
  induction HDO as [
    | y t' Hly HDO' IH
    | a b HDO' IH
    | a b HDO' IH
  ]; intros s2 Hext r1 Happ1 r2 Happ2.
  - (* DO_var: u = tvar x *)
    rewrite (ApplySub_functional _ _ _ _ Happ1 Happ2). apply Nat.le_refl.
  - (* DO_walk: u = tvar y, lookup y s = Some t' *)
    assert (Hly2 : lookup y s2 = Some t') by exact (Hext y t' Hly).
    inversion Happ2 as [y' Hfree | y' u' r' Hlook Hsubu | | ]; subst.
    + congruence.
    + rewrite Hly2 in Hlook. injection Hlook as <-.
      exact (IH s2 Hext r1 Happ1 r2 Hsubu).
    + exfalso. match goal with H : forall _, tvar _ <> tvar _ |- _ => exact (H y eq_refl) end.
  - (* DO_cons_l: u = tcons a b, DeepOccurs s x a *)
    inversion Happ2 as [| | a' b' ra rb Ha Hb | t' Hnotvar Hnotcons]; subst.
    { assert (H : tsize r1 <= tsize ra) by exact (IH s2 Hext r1 Happ1 ra Ha).
      simpl. lia. }
    { exfalso. exact (Hnotcons a b eq_refl). }
  - (* DO_cons_r: u = tcons a b, DeepOccurs s x b *)
    inversion Happ2 as [| | a' b' ra rb Ha Hb | t' Hnotvar Hnotcons]; subst.
    { assert (H : tsize r1 <= tsize rb) by exact (IH s2 Hext r1 Happ1 rb Hb).
      simpl. lia. }
    { exfalso. exact (Hnotcons a b eq_refl). }
Qed.

(* Completeness and Most General Unifier *)

(** A substitution [s] unifies [t1] and [t2] if it maps them to the same term. *)
Definition unifier (s : sub) (t1 t2 : term) : Prop :=
  forall r1 r2, ApplySub s t1 r1 -> ApplySub s t2 r2 -> r1 = r2.

(** [m] is more general than [s]: [s] factors through [m] via some [s'].
    That is, [s = s' ∘ m] pointwise over terms. *)
Definition more_general (m s : sub) : Prop :=
  exists s', forall t r1 r2,
    ApplySub s  t  r1 ->
    ApplySub m  t  r2 ->
    ApplySub s' r2 r1.

(** The substitution produced by unification is the most general unifier:
    any acyclic unifier of [t1] and [t2] that extends [s] factors through it.
    Acyclicity is needed because [unifier] is otherwise vacuous when
    [ApplySub] has no result for one of the terms. *)
Definition models_sub (s2 m : sub) : Prop :=
  forall x u, lookup x m = Some u ->
    forall r, ApplySub s2 (tvar x) r -> ApplySub s2 u r.

Lemma models_sub_of_extension : forall s s2,
  (forall x u, lookup x s = Some u -> lookup x s2 = Some u) ->
  models_sub s2 s.
Proof.
  intros s s2 Hext x u Hlook r Happ.
  pose proof (Hext x u Hlook) as Hlook2.
  inversion Happ; subst; try congruence.
Qed.

Lemma Walk_ApplySub_model : forall s t w,
  Walk s t w -> forall s2, models_sub s2 s ->
  forall r, ApplySub s2 t r -> ApplySub s2 w r.
Proof.
  intros s t w Hwalk.
  induction Hwalk; intros s2 Hmodel out Happ.
  - exact Happ.
  - apply IHHwalk; [exact Hmodel |].
    exact (Hmodel x u H out Happ).
  - exact Happ.
Qed.

Lemma models_sub_bind : forall s2 s x u,
  lookup x s = None -> models_sub s2 s ->
  (forall r, ApplySub s2 (tvar x) r -> ApplySub s2 u r) ->
  models_sub s2 ((x, u) :: s).
Proof.
  intros s2 s x u Hfree Hmodel Hnew z v Hlook r Happ.
  simpl in Hlook. destruct (Nat.eqb_spec z x) as [-> | Hneq].
  - injection Hlook as <-. exact (Hnew r Happ).
  - exact (Hmodel z v Hlook r Happ).
Qed.

Lemma models_sub_factor : forall s2 m,
  models_sub s2 m -> more_general m s2.
Proof.
  intros s2 m Hmodel. exists s2.
  intros t r1 r2 Hs2 Hm.
  revert r1 Hs2.
  induction Hm; intros r1 Hs2.
  - exact Hs2.
  - apply IHHm. exact (Hmodel x u H r1 Hs2).
  - inversion Hs2; subst; try congruence.
    constructor; [apply IHHm1 | apply IHHm2]; assumption.
  - exact Hs2.
Qed.

Lemma unifier_walk_model : forall s t1 t2 w1 w2 s2,
  acyclic_sub s2 -> models_sub s2 s ->
  Walk s t1 w1 -> Walk s t2 w2 ->
  unifier s2 t1 t2 -> unifier s2 w1 w2.
Proof.
  intros s t1 t2 w1 w2 s2 Hac Hmodel Hw1 Hw2 Hunit r1 r2 Hr1 Hr2.
  destruct (ApplySub_total s2 Hac t1) as [v1 Hv1].
  destruct (ApplySub_total s2 Hac t2) as [v2 Hv2].
  assert (Hwv1 : ApplySub s2 w1 v1) by
    exact (Walk_ApplySub_model s t1 w1 Hw1 s2 Hmodel v1 Hv1).
  assert (Hwv2 : ApplySub s2 w2 v2) by
    exact (Walk_ApplySub_model s t2 w2 Hw2 s2 Hmodel v2 Hv2).
  assert (v1 = v2) by exact (Hunit v1 v2 Hv1 Hv2).
  assert (r1 = v1) by exact (ApplySub_functional _ _ _ _ Hr1 Hwv1).
  assert (r2 = v2) by exact (ApplySub_functional _ _ _ _ Hr2 Hwv2).
  congruence.
Qed.

Lemma unifier_cons_parts : forall s2 a1 a2 b1 b2,
  acyclic_sub s2 ->
  unifier s2 (tcons a1 a2) (tcons b1 b2) ->
  unifier s2 a1 b1 /\ unifier s2 a2 b2.
Proof.
  intros s2 a1 a2 b1 b2 Hac Hunit. split.
  - intros ra rb Ha Hb.
    destruct (ApplySub_total s2 Hac a2) as [ra2 Ha2].
    destruct (ApplySub_total s2 Hac b2) as [rb2 Hb2].
    pose proof (Hunit _ _ (AS_cons s2 a1 a2 ra ra2 Ha Ha2)
                            (AS_cons s2 b1 b2 rb rb2 Hb Hb2)) as Heq.
    congruence.
  - intros ra rb Ha Hb.
    destruct (ApplySub_total s2 Hac a1) as [ra1 Ha1].
    destruct (ApplySub_total s2 Hac b1) as [rb1 Hb1].
    pose proof (Hunit _ _ (AS_cons s2 a1 a2 ra1 ra Ha1 Ha)
                            (AS_cons s2 b1 b2 rb1 rb Hb1 Hb)) as Heq.
    congruence.
Qed.

Lemma UnifyW_models_gen : forall w1 w2 s r,
  UnifyW w1 w2 s r ->
  forall s', r = Some s' -> forall s2,
    acyclic_sub s2 -> models_sub s2 s ->
    unifier s2 w1 w2 -> models_sub s2 s'.
Proof.
  intros w1 w2 s r Hunify.
  induction Hunify; intros s' Hr s2 Hac Hmodel Hunit;
    inversion Hr; subst; try exact Hmodel.
  - apply models_sub_bind; [assumption | assumption |].
    intros v Hv.
    destruct (ApplySub_total s2 Hac u) as [vu Hvu].
    rewrite (Hunit v vu Hv Hvu). exact Hvu.
  - apply models_sub_bind; [assumption | assumption |].
    intros v Hv.
    destruct (ApplySub_total s2 Hac u) as [vu Hvu].
    rewrite <- (Hunit vu v Hvu Hv). exact Hvu.
  - destruct (unifier_cons_parts s2 a1 a2 b1 b2 Hac Hunit) as [Hunit1 Hunit2].
    assert (Hwalk1 : unifier s2 wa1 wb1) by
      exact (unifier_walk_model s a1 b1 wa1 wb1 s2 Hac Hmodel H H0 Hunit1).
    assert (Hmodel1 : models_sub s2 s1) by
      exact (IHHunify1 s1 eq_refl s2 Hac Hmodel Hwalk1).
    assert (Hwalk2 : unifier s2 wa2 wb2) by
      exact (unifier_walk_model s1 a2 b2 wa2 wb2 s2 Hac Hmodel1 H1 H2 Hunit2).
    exact (IHHunify2 s' eq_refl s2 Hac Hmodel1 Hwalk2).
Qed.

Lemma Unify_most_general_model : forall t1 t2 s s',
  Unify t1 t2 s (Some s') ->
  forall s2,
    acyclic_sub s2 ->
    models_sub s2 s ->
    unifier s2 t1 t2 ->
    more_general s' s2.
Proof.
  intros t1 t2 s s' Hunify s2 Hac2 Hmodel Hunit.
  destruct Hunify as (w1 & w2 & Hw1 & Hw2 & Hu).
  assert (Hwalkunit : unifier s2 w1 w2) by
    exact (unifier_walk_model s t1 t2 w1 w2 s2 Hac2 Hmodel Hw1 Hw2 Hunit).
  apply models_sub_factor.
  exact (UnifyW_models_gen w1 w2 s (Some s') Hu s' eq_refl s2 Hac2 Hmodel Hwalkunit).
Qed.

Lemma Unify_most_general : forall t1 t2 s s',
  acyclic_sub s ->
  Unify t1 t2 s (Some s') ->
  forall s2,
    acyclic_sub s2 ->
    (forall x u, lookup x s = Some u -> lookup x s2 = Some u) ->
    unifier s2 t1 t2 ->
    more_general s' s2.
Proof.
  intros t1 t2 s s' _ Hunify s2 Hac2 Hext Hunit.
  apply (Unify_most_general_model t1 t2 s s' Hunify s2 Hac2).
  - exact (models_sub_of_extension s s2 Hext).
  - exact Hunit.
Qed.

Lemma more_general_models : forall m s2,
  acyclic_sub m -> acyclic_sub s2 ->
  more_general m s2 -> models_sub s2 m.
Proof.
  intros m s2 Hacm Hacs2 [factor Hfactor] x u Hlook r Hx.
  destruct (ApplySub_total m Hacm u) as [mu Hmu].
  destruct (ApplySub_total s2 Hacs2 u) as [ru Hru].
  assert (Hfactor_x : ApplySub factor mu r) by
    exact (Hfactor (tvar x) r mu Hx (AS_bound m x u mu Hlook Hmu)).
  assert (Hfactor_u : ApplySub factor mu ru) by
    exact (Hfactor u ru mu Hru Hmu).
  assert (r = ru) by exact (ApplySub_functional _ _ _ _ Hfactor_x Hfactor_u).
  subst. exact Hru.
Qed.

Lemma DeepOccurs_tsize_model : forall s x u,
  DeepOccurs s x u -> forall s2,
  models_sub s2 s ->
  forall r1, ApplySub s2 (tvar x) r1 ->
  forall r2, ApplySub s2 u r2 ->
  tsize r1 <= tsize r2.
Proof.
  intros s x u HDO. induction HDO;
    intros s2 Hmodel r1 Happ1 r2 Happ2.
  - rewrite (ApplySub_functional _ _ _ _ Happ1 Happ2). apply Nat.le_refl.
  - exact (IHHDO s2 Hmodel r1 Happ1 r2 (Hmodel y t H r2 Happ2)).
  - inversion Happ2 as [| | a' b' ra rb Ha Hb | t' Hnotvar Hnotcons]; subst.
    + assert (Hle : tsize r1 <= tsize ra) by
        exact (IHHDO s2 Hmodel r1 Happ1 ra Ha).
      simpl. lia.
    + exact (False_rect _ (Hnotcons a b eq_refl)).
  - inversion Happ2 as [| | a' b' ra rb Ha Hb | t' Hnotvar Hnotcons]; subst.
    + assert (Hle : tsize r1 <= tsize rb) by
        exact (IHHDO s2 Hmodel r1 Happ1 rb Hb).
      simpl. lia.
    + exact (False_rect _ (Hnotcons a b eq_refl)).
Qed.

(** A failing unification cannot be satisfied by an acyclic substitution
    that respects the input bindings. *)
Lemma UnifyW_complete_fail_model : forall w1 w2 s,
  acyclic_sub s ->
  UnifyW w1 w2 s None ->
  forall t1 t2, Walk s t1 w1 -> Walk s t2 w2 ->
  forall s2, acyclic_sub s2 -> models_sub s2 s ->
  ~ unifier s2 t1 t2.
Proof.
  intros w1 w2 s Hacacylic HunifyW.
  remember None as r eqn:Hr.
  induction HunifyW; intros t1 t2 Hw1 Hw2 s2 Hacacylic2 Hmodel Hunifier;
  inversion Hr; subst; try clear Hr.
  - rename H into Hneq. rename H0 into HDO.
    destruct (ApplySub_total s2 Hacacylic2 t1) as [r1 Hr1].
    destruct (ApplySub_total s2 Hacacylic2 t2) as [r2 Hr2].
    assert (Heq : r1 = r2) by exact (Hunifier r1 r2 Hr1 Hr2).
    assert (Hx : ApplySub s2 (tvar x) r1) by
      exact (Walk_ApplySub_model s t1 (tvar x) Hw1 s2 Hmodel r1 Hr1).
    assert (Hu : ApplySub s2 u r2) by
      exact (Walk_ApplySub_model s t2 u Hw2 s2 Hmodel r2 Hr2).
    subst r2.
    inversion HDO as [| y t' Hly HDO' | a b HDO' | a b HDO']; subst.
    + exact (Hneq eq_refl).
    + pose proof (Walk_tvar_free s t2 y Hw2) as Hfree. congruence.
    + inversion Hu as [| | a' b' ra rb Ha Hb | t'' Hnotvar Hnotcons]; subst.
      { pose proof (DeepOccurs_tsize_model s x a HDO' s2 Hmodel (tcons ra rb) Hx ra Ha) as Hts.
        simpl in Hts. lia. }
      { exfalso. exact (Hnotcons a b eq_refl). }
    + inversion Hu as [| | a' b' ra rb Ha Hb | t'' Hnotvar Hnotcons]; subst.
      { pose proof (DeepOccurs_tsize_model s x b HDO' s2 Hmodel (tcons ra rb) Hx rb Hb) as Hts.
        simpl in Hts. lia. }
      { exfalso. exact (Hnotcons a b eq_refl). }
  - rename H into Hneq. rename H0 into HDO.
    destruct (ApplySub_total s2 Hacacylic2 t1) as [r1 Hr1].
    destruct (ApplySub_total s2 Hacacylic2 t2) as [r2 Hr2].
    assert (Heq : r1 = r2) by exact (Hunifier r1 r2 Hr1 Hr2).
    assert (Hu : ApplySub s2 u r1).
    { eapply Walk_ApplySub_model; eassumption. }
    assert (Hy : ApplySub s2 (tvar y) r2).
    { eapply Walk_ApplySub_model; eassumption. }
    subst r1.
    inversion HDO as [| x t' Hly HDO' | a b HDO' | a b HDO']; subst.
    * exact (Hneq y eq_refl).
    * pose proof (Walk_tvar_free _ _ _ Hw1) as Hfree. congruence.
    * inversion Hu as [| | a' b' ra rb Ha Hb | t'' Hnotvar Hnotcons]; subst.
      + pose proof (DeepOccurs_tsize_model _ _ _ HDO' s2 Hmodel (tcons ra rb) Hy ra Ha) as Hts.
        simpl in Hts. lia.
      + exact (Hnotcons a b eq_refl).
    * inversion Hu as [| | a' b' ra rb Ha Hb | t'' Hnotvar Hnotcons]; subst.
      + pose proof (DeepOccurs_tsize_model _ _ _ HDO' s2 Hmodel (tcons ra rb) Hy rb Hb) as Hts.
        simpl in Hts. lia.
      + exact (Hnotcons a b eq_refl).
  - (* U_cons_ok *)
    assert (Hunitcons : unifier s2 (tcons a1 a2) (tcons b1 b2)) by
      exact (unifier_walk_model s t1 t2 (tcons a1 a2) (tcons b1 b2)
                s2 Hacacylic2 Hmodel Hw1 Hw2 Hunifier).
    destruct (unifier_cons_parts s2 a1 a2 b1 b2 Hacacylic2 Hunitcons)
      as [Hunit1 Hunit2].
    assert (Hfirst : Unify a1 b1 s (Some s1)). {
      exists wa1, wb1. repeat split; assumption.
    }
    assert (Hmg : more_general s1 s2) by
      exact (Unify_most_general_model a1 b1 s s1 Hfirst
                s2 Hacacylic2 Hmodel Hunit1).
    assert (Hac1 : acyclic_sub s1) by
      exact (UnifyW_acyclic wa1 wb1 s s1 Hacacylic HunifyW1).
    assert (Hmodel1 : models_sub s2 s1) by
      exact (more_general_models s1 s2 Hac1 Hacacylic2 Hmg).
    exact (IHHunifyW2 Hac1 eq_refl a2 b2 H1 H2 s2 Hacacylic2 Hmodel1 Hunit2).
  - (* UW_cons_fail: Walk s a1 wa1, Walk s b1 wb1, UnifyW wa1 wb1 s None *)
    apply (IHHunifyW Hacacylic eq_refl a1 b1 H H0 s2 Hacacylic2 Hmodel).
    intros ra1 rb1 Ha1 Hb1.
    destruct (ApplySub_total s2 Hacacylic2 a2) as [ra2 Ha2].
    destruct (ApplySub_total s2 Hacacylic2 b2) as [rb2 Hb2].
    destruct (ApplySub_total s2 Hacacylic2 t1) as [r1 Hr1].
    destruct (ApplySub_total s2 Hacacylic2 t2) as [r2 Hr2].
    assert (Heq : r1 = r2) by exact (Hunifier r1 r2 Hr1 Hr2).
    assert (Hcons1 : ApplySub s2 (tcons a1 a2) r1) by
      exact (Walk_ApplySub_model s t1 (tcons a1 a2) Hw1 s2 Hmodel r1 Hr1).
    assert (Hcons2 : ApplySub s2 (tcons b1 b2) r2) by
      exact (Walk_ApplySub_model s t2 (tcons b1 b2) Hw2 s2 Hmodel r2 Hr2).
    assert (Hr1eq : r1 = tcons ra1 ra2) by
      exact (ApplySub_functional _ _ _ _ Hcons1 (AS_cons s2 a1 a2 ra1 ra2 Ha1 Ha2)).
    assert (Hr2eq : r2 = tcons rb1 rb2) by
      exact (ApplySub_functional _ _ _ _ Hcons2 (AS_cons s2 b1 b2 rb1 rb2 Hb1 Hb2)).
    assert (Heq_cons : tcons ra1 ra2 = tcons rb1 rb2) by congruence.
    injection Heq_cons; intros; congruence.
  - destruct (ApplySub_total s2 Hacacylic2 t1) as [r1 Hr1].
    destruct (ApplySub_total s2 Hacacylic2 t2) as [r2 Hr2].
    assert (Heq : r1 = r2) by exact (Hunifier r1 r2 Hr1 Hr2).
    assert (Hcons : ApplySub s2 (tcons a1 a2) r1).
    { eapply Walk_ApplySub_model; eassumption. }
    assert (Hv : ApplySub s2 v r2).
    { eapply Walk_ApplySub_model; eassumption. }
    subst.
    inversion Hcons; inversion Hv; subst; congruence.
  - destruct (ApplySub_total s2 Hacacylic2 t1) as [r1 Hr1].
    destruct (ApplySub_total s2 Hacacylic2 t2) as [r2 Hr2].
    assert (Heq : r1 = r2) by exact (Hunifier r1 r2 Hr1 Hr2).
    assert (Hu : ApplySub s2 u r1).
    { eapply Walk_ApplySub_model; eassumption. }
    assert (Hcons : ApplySub s2 (tcons b1 b2) r2).
    { eapply Walk_ApplySub_model; eassumption. }
    subst.
    inversion Hu; inversion Hcons; subst; congruence.
  - destruct (ApplySub_total s2 Hacacylic2 t1) as [r1 Hr1].
    destruct (ApplySub_total s2 Hacacylic2 t2) as [r2 Hr2].
    assert (Heq : r1 = r2) by exact (Hunifier r1 r2 Hr1 Hr2).
    assert (Hu : ApplySub s2 u r1).
    { eapply Walk_ApplySub_model; eassumption. }
    assert (Hv : ApplySub s2 v r2).
    { eapply Walk_ApplySub_model; eassumption. }
    subst.
    inversion Hu; inversion Hv; subst; congruence.
Qed.

(** In particular, no acyclic extension of the input substitution unifies the terms. *)
Lemma Unify_complete_fail : forall t1 t2 s,
  acyclic_sub s ->
  Unify t1 t2 s None ->
  forall s2,
    acyclic_sub s2 ->
    (forall x u, lookup x s = Some u -> lookup x s2 = Some u) ->
    ~ unifier s2 t1 t2.
Proof.
  intros t1 t2 s Hacs (w1 & w2 & Hw1 & Hw2 & Hu) s2 Hac2 Hext.
  exact (UnifyW_complete_fail_model w1 w2 s Hacs Hu
           t1 t2 Hw1 Hw2 s2 Hac2 (models_sub_of_extension s s2 Hext)).
Qed.
