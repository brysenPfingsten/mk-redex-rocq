From Stdlib Require Import List Arith.
Import ListNotations.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees.
Require Import MkRedex.Semantics.Reduction.
Set Default Goal Selector "!".

Lemma Head_no_delay : forall G t r, ~Head G (tdelay t) r.
Proof. intros G t r H. inversion H. Qed.
Lemma Head_no_promoteL : forall G s t r, ~Head G (tdisjL (tgoal gsucc s) t) r.
Proof. intros G s t r H. inversion H. Qed.
Lemma Head_no_promoteR : forall G t s r, ~Head G (tdisjR t (tgoal gsucc s)) r.
Proof. intros G t s r H. inversion H. Qed.

Lemma plug_neq_atomic : forall G E r r_out,
  Head G r r_out ->
  plug E r <> tfail /\
  (forall d, plug E r <> tdelay d) /\
  (forall sv tv, plug E r <> tdisjL (tgoal gsucc sv) tv) /\
  (forall tv sv, plug E r <> tdisjR tv (tgoal gsucc sv)) /\
  (forall sv, plug E r <> tgoal gsucc sv).
Proof.
  intros G E r r_out HHead. induction E; simpl.
  - repeat split.
    + intro H. subst. inversion HHead.
    + intros d H. subst. exact (Head_no_delay _ _ _ HHead).
    + intros sv tv H. subst. exact (Head_no_promoteL _ _ _ _ HHead).
    + intros tv sv H. subst. exact (Head_no_promoteR _ _ _ _ HHead).
    + intros sv H. subst. inversion HHead.
  - destruct IHE as [_ [_ [_ [_ IH5]]]]. repeat split; try discriminate.
    intros sv tv H. injection H as H1 _. exact (IH5 sv H1).
  - destruct IHE as [_ [_ [_ [_ IH5]]]]. repeat split; try discriminate.
    intros tv sv H. injection H as _ H2. exact (IH5 sv H2).
  - repeat split; discriminate.
Qed.

Lemma Head_plug_stable : forall G E r r_out,
  Head G r r_out -> E <> chole -> forall r', ~Head G (plug E r) r'.
Proof.
  intros G E r r_out HHead HNotHole r' Hplug.
  destruct E; [contradiction | | |]; simpl in Hplug;
  destruct (plug_neq_atomic G E r r_out HHead) as [Hf [Hd [Hll [Hlr Hg]]]];
  inversion Hplug;
  first [ apply Hf; congruence
        | eapply Hd; congruence
        | eapply Hll; congruence
        | eapply Hlr; congruence
        | eapply Hg; congruence ].
Qed.

(* Helper: the "chole vs non-chole" exfalso cases all have the same shape.
   r_redex is the term that is a Head redex; E_ctx is the non-chole context
   wrapping the other term; Hstep is the plugging equation; Hstep_dir is
   whether we need to rewrite forwards or backwards. *)

Lemma plug_head_contradiction : forall G E r r_out r' t,
  Head G r r_out ->
  E <> chole ->
  plug E r = t ->
  Head G t r' ->
  False.
Proof.
  intros G E r r_out r' t HHead HNH Hplug Hhead.
  apply (Head_plug_stable G E r r_out HHead HNH r').
  rewrite Hplug.
  exact Hhead.
Qed.

Lemma unique_decomp : forall G E1 E2 r1 r2,
  plug E1 r1 = plug E2 r2 ->
  (exists r1', Head G r1 r1') ->
  (exists r2', Head G r2 r2') ->
  E1 = E2 /\ r1 = r2.
Proof.
  intros G E1.
  induction E1 as [| E1' IHE1 t1 | t1 E1' IHE1 | E1' IHE1 g1];
  intros E2 r1 r2 Hplug Hhead1 Hhead2;
  destruct E2 as [| E2' t2 | t2 E2' | E2' g2];
  simpl in Hplug.

  - (* chole / chole: Hplug : r1 = r2 *)
    split.
    + reflexivity.
    + exact Hplug.

  - (* chole / cdisjL: r1 = tdisjL (plug E2' r2) t2, but r1 is a Head redex
       while tdisjL (plug E2' r2) t2 = plug (cdisjL E2' t2) r2 is not. *)
    exfalso.
    destruct Hhead1 as [r1' Hhead1].
    destruct Hhead2 as [r2' Hhead2].
    apply (plug_head_contradiction G (cdisjL E2' t2) r2 r2' r1' r1).
    + exact Hhead2.
    + discriminate.
    + simpl. exact (eq_sym Hplug).
    + exact Hhead1.

  - (* chole / cdisjR: r1 = tdisjR t2 (plug E2' r2) *)
    exfalso.
    destruct Hhead1 as [r1' Hhead1].
    destruct Hhead2 as [r2' Hhead2].
    apply (plug_head_contradiction G (cdisjR t2 E2') r2 r2' r1' r1).
    + exact Hhead2.
    + discriminate.
    + simpl. exact (eq_sym Hplug).
    + exact Hhead1.

  - (* chole / cconj: r1 = tconj (plug E2' r2) g2 *)
    exfalso.
    destruct Hhead1 as [r1' Hhead1].
    destruct Hhead2 as [r2' Hhead2].
    apply (plug_head_contradiction G (cconj E2' g2) r2 r2' r1' r1).
    + exact Hhead2.
    + discriminate.
    + simpl. exact (eq_sym Hplug).
    + exact Hhead1.

  - (* cdisjL / chole: tdisjL (plug E1' r1) t1 = r2 *)
    exfalso.
    destruct Hhead1 as [r1' Hhead1].
    destruct Hhead2 as [r2' Hhead2].
    apply (plug_head_contradiction G (cdisjL E1' t1) r1 r1' r2' r2).
    + exact Hhead1.
    + discriminate.
    + simpl. exact Hplug.
    + exact Hhead2.

  - (* cdisjL / cdisjL *)
    injection Hplug as Hinner Ht.
    destruct (IHE1 E2' r1 r2 Hinner Hhead1 Hhead2) as [HE Hr].
    split.
    + rewrite HE, Ht. reflexivity.
    + exact Hr.

  - discriminate.
  - discriminate.

  - (* cdisjR / chole: tdisjR t1 (plug E1' r1) = r2 *)
    exfalso.
    destruct Hhead1 as [r1' Hhead1].
    destruct Hhead2 as [r2' Hhead2].
    apply (plug_head_contradiction G (cdisjR t1 E1') r1 r1' r2' r2).
    + exact Hhead1.
    + discriminate.
    + simpl. exact Hplug.
    + exact Hhead2.

  - discriminate.

  - (* cdisjR / cdisjR *)
    injection Hplug as Ht Hinner.
    destruct (IHE1 E2' r1 r2 Hinner Hhead1 Hhead2) as [HE Hr].
    split.
    + rewrite HE, Ht. reflexivity.
    + exact Hr.

  - discriminate.

  - (* cconj / chole: tconj (plug E1' r1) g1 = r2 *)
    exfalso.
    destruct Hhead1 as [r1' Hhead1].
    destruct Hhead2 as [r2' Hhead2].
    apply (plug_head_contradiction G (cconj E1' g1) r1 r1' r2' r2).
    + exact Hhead1.
    + discriminate.
    + simpl. exact Hplug.
    + exact Hhead2.

  - discriminate.
  - discriminate.

  - (* cconj / cconj *)
    injection Hplug as Hinner Hg.
    destruct (IHE1 E2' r1 r2 Hinner Hhead1 Hhead2) as [HE Hr].
    split.
    + rewrite HE, Hg. reflexivity.
    + exact Hr.
Qed.
