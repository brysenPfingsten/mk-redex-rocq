From Stdlib Require Import List Arith.
Import ListNotations.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees.
Require Import MkRedex.Semantics.Reduction.
Set Default Goal Selector "!".

(* Plugging into a non-hole context produces tdisjL/tdisjR/tconj at the root *)
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


(* Promote/delay shapes *)
Lemma head_tdelay_none   : forall G t,   head G (tdelay t) = None.                 Proof. reflexivity. Qed.
Lemma head_promoteL_none : forall G s t, head G (tdisjL (tgoal gsucc s) t) = None. Proof. reflexivity. Qed.
Lemma head_promoteR_none : forall G t s, head G (tdisjR t (tgoal gsucc s)) = None. Proof. reflexivity. Qed.


(** Whenever head fires on a composite node, the sub-tree in the context slot has head = None.*)
Lemma head_ctx_disjL_excl : forall G t1 t2,
  head G (tdisjL t1 t2) <> None -> head G t1 = None.
Proof. 
  intros G t1 t2 Hne.
  destruct t1; simpl in *; try reflexivity; try contradiction.
  - destruct t1_1; simpl in *; try reflexivity; try contradiction.
  - destruct t1_2; simpl in *; try reflexivity; contradiction.
Qed.

Lemma head_ctx_disjR_excl : forall G t1 t2,
  head G (tdisjR t1 t2) <> None -> head G t2 = None.
Proof.
  intros G t1 t2 Hne.
  destruct t2; simpl in *; try reflexivity; try contradiction.
  - destruct t2_1; simpl in *; try reflexivity; contradiction.
  - destruct t2_2; simpl in *; try reflexivity; contradiction.
Qed.

Lemma head_ctx_conj_excl : forall G t g,
  head G (tconj t g) <> None -> head G t = None.
Proof. 
  intros G t g Hne.
  destruct t; simpl in *; try reflexivity; try contradiction.
  - destruct g0; try reflexivity; contradiction.
  - destruct t1; try reflexivity; contradiction.
  - destruct t2; try reflexivity; contradiction.
Qed.

(* Plug destroys redex-ness *)
Lemma plug_redex : forall G E r,
  head G r <> None -> E <> chole -> head G (plug E r) = None.
Proof.
  intros G E r Hheadne HEne. induction E.
  - contradiction.
  - destruct E; destruct r; simpl in *;
    try reflexivity; try contradiction.
    * destruct r1; try reflexivity;
      destruct g; try reflexivity; contradiction.
    * destruct r2; try reflexivity.
      destruct g; try reflexivity; contradiction.
    * destruct (plug E (tgoal g s)) eqn:Eplug; try reflexivity.
      destruct g0; try reflexivity.
      exfalso.
      destruct E; simpl in Eplug; try discriminate.
      inversion Eplug; subst.
      apply Hheadne.
      reflexivity.
    * destruct (plug E (tproceed n l s)) eqn:Eplug;
      try reflexivity. destruct g; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tconj r g)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tdisjL r1 r2)) eqn:Eplug;
      try reflexivity. destruct g; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tdisjR r1 r2)) eqn:Eplug;
      try reflexivity. destruct g; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tgoal g s)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      exfalso. destruct E; simpl in Eplug; try discriminate.
      destruct g; try discriminate. apply Hheadne. reflexivity.
    * destruct (plug E (tproceed n l s)) eqn:Eplug;
      try reflexivity. destruct g; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tconj r g)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tdisjL r1 r2)) eqn:Eplug;
      try reflexivity. destruct g; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tdisjR r1 r2)) eqn:Eplug;
      try reflexivity. destruct g; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
  - destruct E; destruct r; simpl in *;
    try reflexivity; try discriminate;
    try (exfalso; apply Hheadne; reflexivity).
    * destruct r1; try reflexivity.
      destruct g; try reflexivity.
      exfalso. apply Hheadne. reflexivity.
    * destruct r2; try reflexivity.
      destruct g; try reflexivity.
      exfalso. apply Hheadne. reflexivity.
    * destruct (plug E (tgoal g s)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      destruct E; simpl in Eplug; try discriminate.
      destruct g; try discriminate.
      exfalso. apply Hheadne. reflexivity.
    * destruct (plug E (tproceed n l s)) eqn:Eplug;
      try reflexivity. destruct g; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tconj r g)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tdisjL r1 r2)) eqn:Eplug;
      try reflexivity. destruct g; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tdisjR r1 r2)) eqn:Eplug;
      try reflexivity. destruct g; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tgoal g s)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      exfalso. destruct E; simpl in Eplug; try discriminate.
      destruct g; try discriminate.
      apply Hheadne. reflexivity.
    * destruct (plug E (tproceed n l s)) eqn:Eplug;
      try reflexivity. destruct g; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tconj r g)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tdisjL r1 r2)) eqn:Eplug;
      try reflexivity. destruct g; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tdisjR r1 r2)) eqn:Eplug;
      try reflexivity. destruct g; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
  - destruct E; destruct r; simpl in *;
    try reflexivity; 
    try (exfalso; apply Hheadne; reflexivity);
    try (first [ destruct g | destruct g0 | destruct r1 | destruct r2 ]; try reflexivity; exfalso; apply Hheadne; reflexivity).
    * destruct g0; try reflexivity.
      exfalso. apply Hheadne. reflexivity.
    * destruct r1; try reflexivity.
      exfalso. apply Hheadne. reflexivity.
    * destruct r2; try reflexivity.
      exfalso. apply Hheadne. reflexivity.
    * destruct (plug E (tgoal g0 s)) eqn:Eplug;
      try reflexivity. destruct g1; try reflexivity.
      exfalso. destruct E; simpl in Eplug; try discriminate.
      destruct g0; try discriminate. apply Hheadne. reflexivity.
    * destruct (plug E (tproceed n l s)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tconj r g0)) eqn:Eplug;
      try reflexivity. destruct g1; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tdisjL r1 r2)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tdisjR r1 r2)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tgoal g0 s)) eqn:Eplug;
      try reflexivity. destruct g1; try reflexivity.
      exfalso. destruct E; simpl in Eplug; try discriminate.
      destruct g0; try discriminate. apply Hheadne. reflexivity.
    * destruct (plug E (tproceed n l s)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tconj r g0)) eqn:Eplug;
      try reflexivity. destruct g1; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tdisjL r1 r2)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
    * destruct (plug E (tdisjR r1 r2)) eqn:Eplug;
      try reflexivity. destruct g0; try reflexivity.
      exfalso. destruct E; simpl in Eplug; discriminate.
Qed.

Lemma plug_injective: forall E r1 r2,
  plug E r1 = plug E r2 -> r1 = r2.
Proof.
  induction E; simpl in *; intros.
  1: assumption.
  1-3: apply IHE; inversion H; reflexivity.
Qed.


(* Unique decomposition *)
Lemma unique_decomp : forall G E1 E2 r1 r2,
  plug E1 r1 = plug E2 r2 ->
  head G r1 <> None ->
  head G r2 <> None ->
  E1 = E2 /\ r1 = r2.
Proof.
  intros G E1. revert G. induction E1; 
  intros G E2 r1 r2 Hplug Hhead1 Hhead2; 
  destruct E2; simpl in *; try discriminate.
  - rewrite Hplug. split; reflexivity.
  - exfalso. apply Hhead1. rewrite Hplug.
    change (head G (plug (cdisjL E2 t) r2) = None).
    apply plug_redex; [exact Hhead2 | discriminate].
  - exfalso. apply Hhead1. rewrite Hplug.
    change (head G (plug (cdisjR t E2) r2) = None).
    apply plug_redex; [exact Hhead2 | discriminate].
  - exfalso. apply Hhead1. rewrite Hplug.
    change (head G (plug (cconj E2 g) r2) = None).
    apply plug_redex; [exact Hhead2 | discriminate].
  - exfalso. apply Hhead2. rewrite <- Hplug.
    change (head G (plug (cdisjL E1 t) r1) = None).
    apply plug_redex; [exact Hhead1 | discriminate].
  - injection Hplug as Hinner Ht. subst.
    destruct (IHE1 G E2 r1 r2 Hinner Hhead1 Hhead2) as [-> ->]; auto.
  - exfalso. apply Hhead2. rewrite <- Hplug.
    change (head G (plug (cdisjR t E1) r1) = None).
    apply plug_redex; [exact Hhead1 | discriminate].
  - injection Hplug as Ht Hinner. subst.
    destruct (IHE1 G E2 r1 r2 Hinner Hhead1 Hhead2) as [-> ->]; auto.
  - exfalso. apply Hhead2. rewrite <- Hplug.
    change (head G (plug (cconj E1 g) r1) = None).
    apply plug_redex; [exact Hhead1 | discriminate].
  - injection Hplug as Hinner Hg. subst.
    destruct (IHE1 G E2 r1 r2 Hinner Hhead1 Hhead2) as [-> ->]; auto.
Qed.

(* S_ctx cannot fire when the tree's root is a promote/delay form *)
Lemma ctx_not_delay : forall G E r r' t,
  head G r = Some r' -> plug E r = tdelay t -> False.
Proof.
  intros G E r r' t H Hplug.
  apply plug_eq_tdelay in Hplug. destruct Hplug as [-> ->].
  rewrite head_tdelay_none in H. discriminate.
Qed.

Lemma ctx_not_promoteL : forall G E r r' s t,
  head G r = Some r' -> plug E r = tdisjL (tgoal gsucc s) t -> False.
Proof.
  intros G E r r' s t H Hplug.
  destruct E; simpl in Hplug; try discriminate.
  - rewrite Hplug in H. rewrite head_promoteL_none in H. discriminate.
  - injection Hplug as Hg _. apply plug_eq_tgoal in Hg.
    destruct Hg as [_ ->]. simpl in H. discriminate.
Qed.

Lemma ctx_not_promoteR : forall G E r r' t s,
  head G r = Some r' -> plug E r = tdisjR t (tgoal gsucc s) -> False.
Proof.
  intros G E r r' t s H Hplug.
  destruct E; simpl in Hplug; try discriminate.
  - rewrite Hplug in H. rewrite head_promoteR_none in H. discriminate.
  - injection Hplug as _ Hg. apply plug_eq_tgoal in Hg.
    destruct Hg as [_ ->]. simpl in H. discriminate.
Qed.

(* Determinism *)
Theorem step_deterministic : forall G e e1 e2,
  G |= e --> e1 ->
  G |= e --> e2 ->
  e1 = e2.
Proof.
  intros G [ans t] e1 e2 HstepE HstepE0.
  inversion HstepE; subst; inversion HstepE0; subst;
  try discriminate; try reflexivity.
  - (* S_ctx / S_ctx *)
    assert (Hne  : head G r  <> None) by (rewrite H2; discriminate).
    assert (Hne0 : head G r0 <> None) by (rewrite H3; discriminate).
    destruct (unique_decomp G E0 E r0 r H1 Hne0 Hne) as [-> ->].
    rewrite H2 in H3. injection H3 as ->. reflexivity.
  - exfalso. eapply ctx_not_delay;    [exact H2 | symmetry; exact H1].
  - exfalso. eapply ctx_not_promoteL; [exact H2 | symmetry; exact H1].
  - exfalso. eapply ctx_not_promoteR; [exact H2 | symmetry; exact H1].
  - exfalso. eapply ctx_not_delay;    [exact H2 | exact H1].
  - exfalso. eapply ctx_not_promoteL; [exact H2 | exact H1].
  - exfalso. eapply ctx_not_promoteR; [exact H2 | exact H1].
Qed.
