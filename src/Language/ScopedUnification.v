From Stdlib Require Import List Arith Lia.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees Unification WellFormed Scoping.
Import ListNotations.
Set Default Goal Selector "!".

(** A successful [Unify] on closed terms yields a closed substitution. *)
Lemma UnifyW_closed : forall c w1 w2 s s',
  ok_term 0 c w1 ->
  ok_term 0 c w2 ->
  scoped_sub c s ->
  UnifyW w1 w2 s (Some s') ->
  scoped_sub c s'.
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
    assert (Hcs1 : scoped_sub c s1).
    { eapply IHHunifyW1; try eassumption; try reflexivity.  }
    pose proof (Walk_closed _ _ _ _ Hcta2 Hcs1 H1) as Hctwa2.
    pose proof (Walk_closed _ _ _ _ Hctb2 Hcs1 H2) as Hctwb2.
    eapply IHHunifyW2; try eassumption.
Qed.

Lemma UnifyW_free_count : forall c w1 w2 s s',
  ok_term 0 c w1 -> ok_term 0 c w2 -> scoped_sub c s ->
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

(** Totality uses lexicographic induction on the number of unbound allocated
    IDs and the size of fully substituted inputs. A changed substitution
    decreases the first coordinate; unchanged-substitution pair recursion
    decreases the second. Walking and acyclicity supply the fully substituted
    terms. See docs/proofs.md, Unification, for the two pair-recursion cases. *)
Theorem UnifyW_total : forall c s w1 w2,
  acyclic_sub s -> scoped_sub c s ->
  ok_term 0 c w1 -> ok_term 0 c w2 ->
  Walk s w1 w1 -> Walk s w2 w2 ->
  exists r, UnifyW w1 w2 s r.
Proof.
  intro c.
  assert (Hmain : forall p : nat * nat,
      forall s w1 w2 r1 r2,
      acyclic_sub s -> scoped_sub c s ->
      ok_term 0 c w1 -> ok_term 0 c w2 ->
      Walk s w1 w1 -> Walk s w2 w2 ->
      ApplySub s w1 r1 -> ApplySub s w2 r2 ->
      p = (free_count c s, tsize r1 + tsize r2) ->
      exists r, UnifyW w1 w2 s r). {
    apply (well_founded_induction lex_count_size_wf
      (fun p => forall s w1 w2 r1 r2,
        acyclic_sub s -> scoped_sub c s ->
        ok_term 0 c w1 -> ok_term 0 c w2 ->
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
    assert (Hcwa1 : ok_term 0 c wa1) by
      exact (Walk_closed c w1_1 wa1 s Hca1 Hsub Hwa1).
    assert (Hcwb1 : ok_term 0 c wb1) by
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
    assert (Hsub1 : scoped_sub c s1) by
      exact (UnifyW_closed c wa1 wb1 s s1 Hcwa1 Hcwb1 Hsub Hfirst).
    destruct (Walk_total s1 Hac1 w1_2) as [wa2 Hwa2].
    destruct (Walk_total s1 Hac1 w2_2) as [wb2 Hwb2].
    assert (Hcwa2 : ok_term 0 c wa2) by
      exact (Walk_closed c w1_2 wa2 s1 Hca2 Hsub1 Hwa2).
    assert (Hcwb2 : ok_term 0 c wb2) by
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
  acyclic_sub s -> scoped_sub c s ->
  ok_term 0 c t1 -> ok_term 0 c t2 ->
  exists r, Unify t1 t2 s r.
Proof.
  intros c s t1 t2 Hacyclic Hsub Ht1 Ht2.
  destruct (Walk_total s Hacyclic t1) as [w1 Hw1].
  destruct (Walk_total s Hacyclic t2) as [w2 Hw2].
  assert (Hcw1 : ok_term 0 c w1) by
    exact (Walk_closed c t1 w1 s Ht1 Hsub Hw1).
  assert (Hcw2 : ok_term 0 c w2) by
    exact (Walk_closed c t2 w2 s Ht2 Hsub Hw2).
  destruct (UnifyW_total c s w1 w2 Hacyclic Hsub Hcw1 Hcw2
    (Walk_idempotent s t1 w1 Hw1) (Walk_idempotent s t2 w2 Hw2))
    as [result Hresult].
  exists result. exists w1, w2. repeat split; assumption.
Qed.

Lemma Unify_closed : forall c t1 t2 s s',
  ok_term 0 c t1 ->
  ok_term 0 c t2 ->
  scoped_sub c s ->
  Unify t1 t2 s (Some s') ->
  scoped_sub c s'.
Proof.
  intros c t1 t2 s s' Hct1 Hct2 Hcs Hunify.
  destruct Hunify as (w1 & w2 & Hw1 & Hw2 & HunifyW).
  pose proof (Walk_closed _ _ _ _ Hct1 Hcs Hw1) as Hctw1.
  pose proof (Walk_closed _ _ _ _ Hct2 Hcs Hw2) as Hctw2.
  exact (UnifyW_closed c w1 w2 s s' Hctw1 Hctw2 Hcs HunifyW).
Qed.
