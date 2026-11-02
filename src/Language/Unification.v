From Stdlib Require Import List Arith.
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

  | UW_cons_ok : forall a1 a2 b1 b2 s s1 r,
      UnifyW a1 b1 s (Some s1) ->
      UnifyW a2 b2 s1 r ->
      UnifyW (tcons a1 a2) (tcons b1 b2) s r

  | UW_cons_fail : forall a1 a2 b1 b2 s,
      UnifyW a1 b1 s None ->
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
  induction H as
  [ | | | |
  | a1 a2 b1 b2 sc s1 rc Hfst IHfst Hsnd IHsnd
  | a1 a2 b1 b2 sc Hfst IHfst
  | | | | ];
  intros r' H';
  inversion H' as
  [ | | | |
  | a1' a2' b1' b2' sc' s1' rc' Hfst' IHfst' Hsnd' IHsnd'
  | a1' a2' b1' b2' sc' Hfst' IHfst'
  | | | | ];
  subst;
  try reflexivity; try congruence;
  try (exfalso; match goal with H : forall _ _, _ <> tcons _ _ |- _ => exact (H _ _ eq_refl) end);
  try (exfalso; match goal with H : forall _, tvar _ <> tvar _ |- _ => exact (H _ eq_refl) end).
  - apply IHfst in Hfst'. injection Hfst' as <-.
    apply IHsnd in IHfst'. exact IHfst'.
  - exfalso. apply IHfst in Hfst'. inversion Hfst'.
  - exfalso. apply IHfst in Hfst'. inversion Hfst'.
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
    assert (Heq2 : ra2 = rb2) by exact (IHHunify2 Hs1 s'' eq_refl _ _ H1b H2b).
    assert (Heq1 : ra1 = rb1). {
      assert (Hext : forall x t, lookup x s1 = Some t -> lookup x s'' = Some t) by
        exact (UnifyW_norebind _ _ _ _ Hunify2 s'' eq_refl).
      destruct (ApplySub_suffix_extend s1 s'' Hext a1 ra1 H1a) as [v1 [Hv1_s1 Hv1_s'']].
      destruct (ApplySub_suffix_extend s1 s'' Hext b1 rb1 H2a) as [v2 [Hv2_s1 Hv2_s'']].
      assert (v1 = v2) by exact (IHHunify1 Hacyclic s1 eq_refl v1 v2 Hv1_s1 Hv2_s1).
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
