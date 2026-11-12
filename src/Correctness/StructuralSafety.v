From Stdlib Require Import List Arith Bool Lia.
From MkRedex.Correctness Require Import StructuralAdapter StructuralUnificationBridge.
Import ListNotations.
Set Default Goal Selector "!".

Lemma lookup_app : forall k a b,
  Substitution.lookup k (a ++ b) =
  match Substitution.lookup k a with Some t => Some t | None => Substitution.lookup k b end.
Proof.
  intros k a. induction a as [|[x t] a IH]; intro b; simpl; [reflexivity|].
  destruct (Nat.eqb k x); [reflexivity|apply IH].
Qed.

Lemma lookup_in : forall bindings k t,
  Substitution.lookup k bindings = Some t -> In (k,t) bindings.
Proof.
  induction bindings as [|[x u] bindings IH]; intros k t H; simpl in H.
  - discriminate.
  - destruct (Nat.eqb k x) eqn:E.
    + apply Nat.eqb_eq in E. inversion H; subst. left. reflexivity.
    + right. apply IH. exact H.
Qed.

Lemma erase_with_closed : forall n (t : StructuralUnifier.Term n) names bound,
  (forall x, names x < bound) -> Scoping.closed_term 0 bound (erase_with names t).
Proof.
  intros n t. induction t; intros names bound H; simpl.
  - apply H.
  - destruct r; exact I.
  - split; [apply IHt1|apply IHt2]; exact H.
Qed.

Lemma closed_sub_app : forall bound a b,
  Scoping.closed_sub bound a -> Scoping.closed_sub bound b -> Scoping.closed_sub bound (a ++ b).
Proof.
  intros bound a. induction a as [|[k t] a IH]; intros b Ha Hb; simpl in *.
  - exact Hb.
  - destruct Ha as [Hk [Ht Ha]]. repeat split; try assumption. apply IH; assumption.
Qed.

Theorem decode_closed : forall m n (sigma : StructuralUnifier.AList m n) names bound,
  (forall x, names x < bound) -> Scoping.closed_sub bound (decode sigma names).
Proof.
  intros m n sigma. induction sigma; intros names bound H; simpl; [exact I|].
  apply closed_sub_app.
  - apply IHsigma. intro x. apply H.
  - split; [apply H|]. split; [apply erase_with_closed; intro x; apply H|exact I].
Qed.

Lemma erase_with_occurs : forall n (t : StructuralUnifier.Term n) names k,
  Substitution.occurs k (erase_with names t) = true -> exists x, k = names x.
Proof.
  intros n t. induction t; intros names k H; simpl in H.
  - apply Nat.eqb_eq in H. eauto.
  - destruct r; discriminate.
  - apply orb_true_iff in H. destruct H as [H|H]; [apply IHt1|apply IHt2]; exact H.
Qed.

Lemma decode_rhs_range : forall m n (sigma : StructuralUnifier.AList m n) names k t v,
  In (k,t) (decode sigma names) -> Substitution.occurs v t = true -> exists x, v = names x.
Proof.
  intros m n sigma. induction sigma; intros names k u v Hin Hv; simpl in Hin.
  - contradiction.
  - apply in_app_or in Hin. destruct Hin as [Hin|[Hin|Hin]].
    + destruct (IHsigma _ _ _ _ Hin Hv) as [y E]. exists (StructuralUnifier.thin m f y). exact E.
    + inversion Hin; subst. destruct (erase_with_occurs _ t _ v Hv) as [y E].
      exists (StructuralUnifier.thin m f y). exact E.
    + contradiction.
Qed.

Lemma acyclic_snoc_fresh : forall bindings x t,
  Substitution.acyclic_sub bindings -> Substitution.lookup x bindings = None ->
  (forall k u, Substitution.lookup k bindings = Some u -> Substitution.occurs x u = false) ->
  Substitution.occurs x t = false -> Substitution.acyclic_sub (bindings ++ [(x,t)]).
Proof.
  intros bindings x t Ha Hnone Havoid Ht.
  assert (Hlookup : forall k, k <> x ->
    Substitution.lookup k (bindings ++ [(x,t)]) = Substitution.lookup k bindings).
  { intros k Hk. rewrite lookup_app. destruct (Substitution.lookup k bindings); [reflexivity|].
    simpl. destruct (Nat.eqb k x) eqn:E; [apply Nat.eqb_eq in E; contradiction|reflexivity]. }
  assert (Hlift : forall k, Acc (fun y z => exists u,
    Substitution.lookup z bindings = Some u /\ Substitution.occurs y u = true) k -> k <> x ->
    Acc (fun y z => exists u,
      Substitution.lookup z (bindings ++ [(x,t)]) = Some u /\ Substitution.occurs y u = true) k).
  { intros k Hacc. induction Hacc as [k Hacc IH]. intro Hk. constructor.
    intros y [u [Hlu Hy]]. rewrite Hlookup in Hlu by exact Hk.
    apply IH.
    - exists u. split; assumption.
    - intro E. subst y. rewrite (Havoid k u Hlu) in Hy. discriminate. }
  intro k. destruct (Nat.eq_dec k x) as [->|Hk].
  - constructor. intros y [u [Hlu Hy]].
    rewrite lookup_app, Hnone in Hlu. simpl in Hlu. rewrite Nat.eqb_refl in Hlu.
    injection Hlu as <-. apply Hlift; [apply Ha|].
    intro E. subst y. rewrite Ht in Hy. discriminate.
  - apply Hlift; [apply Ha|exact Hk].
Qed.

Theorem decode_acyclic : forall m n (sigma : StructuralUnifier.AList m n) names,
  injective names -> Substitution.acyclic_sub (decode sigma names).
Proof.
  intros m n sigma. induction sigma; intros names Hnames; simpl.
  - intro x. constructor. intros y [t [H _]]. discriminate H.
  - set (rest := fun y => names (StructuralUnifier.thin m f y)).
    assert (Hnone : Substitution.lookup (names f) (decode sigma rest) = None).
    { destruct (Substitution.lookup (names f) (decode sigma rest)) as [u|] eqn:E; [|reflexivity].
      apply lookup_in in E. destruct (decode_keys _ _ sigma rest _ _ E) as [y Ey].
      unfold rest in Ey. apply Hnames in Ey.
      exfalso. exact (thin_not_removed m f y (eq_sym Ey)). }
    apply acyclic_snoc_fresh.
    + apply IHsigma. apply restrict_injective. exact Hnames.
    + exact Hnone.
    + intros k u Hu. destruct (Substitution.occurs (names f) u) eqn:E; [|reflexivity].
      apply lookup_in in Hu.
      destruct (decode_rhs_range _ _ sigma rest _ _ _ Hu E) as [y Ey].
      unfold rest in Ey. apply Hnames in Ey.
      exfalso. exact (thin_not_removed m f y (eq_sym Ey)).
    + destruct (Substitution.occurs (names f) (erase_with rest t)) eqn:E; [|reflexivity].
      destruct (erase_with_occurs _ t rest _ E) as [y Ey].
      unfold rest in Ey. apply Hnames in Ey.
      exfalso. exact (thin_not_removed m f y (eq_sym Ey)).
Qed.

Corollary decode_acc_safe : forall m (acc : StructuralUnifier.Acc m),
  Scoping.closed_sub m (decode_acc acc) /\ Substitution.acyclic_sub (decode_acc acc).
Proof.
  intros m [n sigma]. split.
  - apply decode_closed. apply fin_nat_bound.
  - apply decode_acyclic. apply fin_nat_injective.
Qed.

Theorem solve_state_safe : forall bound initial t u answer,
  solve_state bound initial t u = Some (Some answer) ->
  Scoping.closed_sub bound answer /\ Substitution.acyclic_sub answer.
Proof.
  intros bound initial t u answer H. unfold solve_state in H.
  destruct (encode_sub bound initial) as [acc|]; [|discriminate].
  destruct (index_term bound t), (index_term bound u); try discriminate.
  unfold decode_result in H. destruct (StructuralUnifier.amgu bound t0 t1 acc) as [out|]; [|discriminate].
  injection H as <-. apply decode_acc_safe.
Qed.
