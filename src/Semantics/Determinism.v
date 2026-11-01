From Stdlib Require Import List Arith.
Import ListNotations.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees.
Require Import MkRedex.Semantics.Reduction.
Set Default Goal Selector "!".

(* ================================================================== *)
(*  Plug shape lemmas (unchanged)                                       *)
(* ================================================================== *)

Lemma plug_eq_tgoal : forall E r g s,
  plug E r = tgoal g s -> E = chole /\ r = tgoal g s.
Proof.
  intros E r g s H. destruct E; simpl in H; try discriminate.
  split; [reflexivity | exact H].
Qed.

Lemma plug_eq_tdelay : forall E r t,
  plug E r = tdelay t -> E = chole /\ r = tdelay t.
Proof.
  intros E r t H. destruct E; simpl in H; try discriminate.
  split; [reflexivity | exact H].
Qed.

Lemma plug_injective : forall E r1 r2,
  plug E r1 = plug E r2 -> r1 = r2.
Proof.
  induction E; simpl in *; intros.
  1: assumption.
  1-3: apply IHE; inversion H; reflexivity.
Qed.

(* ================================================================== *)
(*  Head does not fire on promote/delay shapes                         *)
(* ================================================================== *)

Lemma Head_no_delay : forall G t r,
  ~Head G (tdelay t) r.
Proof.
  intros G t r H. inversion H.
Qed.

Lemma Head_no_promoteL : forall G s t r,
  ~Head G (tdisjL (tgoal gsucc s) t) r.
Proof.
  intros G s t r H. inversion H.
Qed.

Lemma Head_no_promoteR : forall G t s r,
  ~Head G (tdisjR t (tgoal gsucc s)) r.
Proof.
  intros G t s r H. inversion H.
Qed.

(* ================================================================== *)
(*  Head fires only on the context slot's subtree                      *)
(* ================================================================== *)

(** If [Head] fires on a [tdisjL] node, the left subtree is not a redex. *)
Lemma Head_ctx_disjL_excl : forall G t1 t2 r,
  Head G (tdisjL t1 t2) r -> forall r', ~Head G t1 r'.
Proof.
  intros G t1 t2 r Hh r' Ht1.
  inversion Hh; subst; inversion Ht1.
Qed.

(** If [Head] fires on a [tdisjR] node, the right subtree is not a redex. *)
Lemma Head_ctx_disjR_excl : forall G t1 t2 r,
  Head G (tdisjR t1 t2) r -> forall r', ~Head G t2 r'.
Proof.
  intros G t1 t2 r Hh r' Ht2.
  inversion Hh; subst; inversion Ht2.
Qed.

(** If [Head] fires on a [tconj] node, the left subtree is not a redex. *)
Lemma Head_ctx_conj_excl : forall G t g r,
  Head G (tconj t g) r -> forall r', ~Head G t r'.
Proof.
  intros G t g r Hh r' Ht.
  inversion Hh; subst; inversion Ht.
Qed.

(* ================================================================== *)
(*  Plugging a redex into a non-hole context kills the redex           *)
(* ================================================================== *)

(** plug E r cannot match the shapes that Head inspects on its LHS. *)
Lemma plug_neq_atomic : forall G E r r_out,
  Head G r r_out ->
  plug E r <> tfail /\
  (forall d, plug E r <> tdelay d) /\
  (forall sv tv, plug E r <> tdisjL (tgoal gsucc sv) tv) /\
  (forall tv sv, plug E r <> tdisjR tv (tgoal gsucc sv)) /\
  (forall sv, plug E r <> tgoal gsucc sv).
Proof.
  intros G E r r_out HHead.
  induction E; simpl.
  - repeat split.
    + intro H. subst. inversion HHead.
    + intros d H. subst. exact (Head_no_delay _ _ _ HHead).
    + intros sv tv H. subst. exact (Head_no_promoteL _ _ _ _ HHead).
    + intros tv sv H. subst. exact (Head_no_promoteR _ _ _ _ HHead).
    + intros sv H. subst. inversion HHead.
  - destruct IHE as [_ [_ [_ [_ IH5]]]].
    repeat split; try discriminate.
    intros sv tv H. injection H as H1 _. exact (IH5 sv H1).
  - destruct IHE as [_ [_ [_ [_ IH5]]]].
    repeat split; try discriminate.
    intros tv sv H. injection H as _ H2. exact (IH5 sv H2).
  - repeat split; discriminate.
Qed.

(** If [Head G r _] and [E ≠ chole], then [Head] does not fire on [plug E r]. *)
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

(* ================================================================== *)
(*  Unique decomposition                                                *)
(* ================================================================== *)

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
  simpl in Hplug; try discriminate.

  - (* chole / chole *)
    split.
    + reflexivity.
    + exact Hplug.

  - (* chole / cdisjL *)
    exfalso.
    destruct Hhead1 as [r1' Hhead1].
    destruct Hhead2 as [r2' Hhead2].
    apply (plug_head_contradiction G (cdisjL E2' t2) r2 r2' r1' r1).
    + exact Hhead2.
    + discriminate.
    + simpl. exact (eq_sym Hplug).
    + exact Hhead1.

  - (* chole / cdisjR *)
    exfalso.
    destruct Hhead1 as [r1' Hhead1].
    destruct Hhead2 as [r2' Hhead2].
    apply (plug_head_contradiction G (cdisjR t2 E2') r2 r2' r1' r1).
    + exact Hhead2.
    + discriminate.
    + simpl. exact (eq_sym Hplug).
    + exact Hhead1.

  - (* chole / cconj *)
    exfalso.
    destruct Hhead1 as [r1' Hhead1].
    destruct Hhead2 as [r2' Hhead2].
    apply (plug_head_contradiction G (cconj E2' g2) r2 r2' r1' r1).
    + exact Hhead2.
    + discriminate.
    + simpl. exact (eq_sym Hplug).
    + exact Hhead1.

  - (* cdisjL / chole *)
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

  - (* cdisjR / chole *)
    exfalso.
    destruct Hhead1 as [r1' Hhead1].
    destruct Hhead2 as [r2' Hhead2].
    apply (plug_head_contradiction G (cdisjR t1 E1') r1 r1' r2' r2).
    + exact Hhead1.
    + discriminate.
    + simpl. exact Hplug.
    + exact Hhead2.

  - (* cdisjR / cdisjR *)
    injection Hplug as Ht Hinner.
    destruct (IHE1 E2' r1 r2 Hinner Hhead1 Hhead2) as [HE Hr].
    split.
    + rewrite HE, Ht. reflexivity.
    + exact Hr.

  - (* cconj / chole *)
    exfalso.
    destruct Hhead1 as [r1' Hhead1].
    destruct Hhead2 as [r2' Hhead2].
    apply (plug_head_contradiction G (cconj E1' g1) r1 r1' r2' r2).
    + exact Hhead1.
    + discriminate.
    + simpl. exact Hplug.
    + exact Hhead2.

  - (* cconj / cconj *)
    injection Hplug as Hinner Hg.
    destruct (IHE1 E2' r1 r2 Hinner Hhead1 Hhead2) as [HE Hr].
    split.
    + rewrite HE, Hg. reflexivity.
    + exact Hr.
Qed.



(* ================================================================== *)
(*  S_ctx is incompatible with the other step shapes                   *)
(* ================================================================== *)

Lemma ctx_not_delay : forall G E r r' t,
  Head G r r' -> plug E r = tdelay t -> False.
Proof.
  intros G E r r' t H Hplug.
  apply plug_eq_tdelay in Hplug. destruct Hplug as [-> ->].
  exact (Head_no_delay G t r' H).
Qed.

Lemma ctx_not_promoteL : forall G E r r' s t,
  Head G r r' -> plug E r = tdisjL (tgoal gsucc s) t -> False.
Proof.
  intros G E r r' s t H Hplug.
  destruct E; simpl in Hplug; try discriminate.
  - rewrite Hplug in H. exact (Head_no_promoteL G s t r' H).
  - injection Hplug as Hg _.
    apply plug_eq_tgoal in Hg. destruct Hg as [-> ->].
    inversion H.
Qed.

Lemma ctx_not_promoteR : forall G E r r' t s,
  Head G r r' -> plug E r = tdisjR t (tgoal gsucc s) -> False.
Proof.
  intros G E r r' t s H Hplug.
  destruct E; simpl in Hplug; try discriminate.
  - rewrite Hplug in H. exact (Head_no_promoteR G t s r' H).
  - injection Hplug as _ Hg.
    apply plug_eq_tgoal in Hg. destruct Hg as [-> ->].
    inversion H.
Qed.

(* ================================================================== *)
(*  Determinism                                                         *)
(* ================================================================== *)

(** Follows from [unique_decomp] (S_ctx/S_ctx case) and [Head_functional]
    (to equate the two reducts once the contexts and redexes coincide),
    plus [ctx_not_delay/promoteL/promoteR] for the cross cases. *)
Theorem step_deterministic : forall G e e1 e2,
  G |= e --> e1 ->
  G |= e --> e2 ->
  e1 = e2.
Proof.
  intros. 
  inversion H; inversion H0; subst; simpl in *;
  try congruence.
  - injection H5 as <- Hplug. 

