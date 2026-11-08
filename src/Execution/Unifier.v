From Stdlib Require Import List Arith Lia Logic.ProofIrrelevance Logic.ConstructiveEpsilon.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees Unification Scoping ScopedUnification.
Import ListNotations.
Set Default Goal Selector "!".


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
