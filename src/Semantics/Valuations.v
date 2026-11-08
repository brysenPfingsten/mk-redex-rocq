From Stdlib Require Import List Arith Lia.
From MkRedex.Language Require Import Terms Goals Substitution Environments.
From MkRedex.Semantics Require Import Denotation DenotationOpening WellFormed.
Import ListNotations.
Set Default Goal Selector "!".

Definition agrees_below (c : nat) (rho sigma : valuation) : Prop :=
  forall x, x < c -> rho x = sigma x.

Lemma eval_term_agrees : forall t d c rho sigma beta,
  closed_term d c t -> agrees_below c rho sigma ->
  eval_term rho beta t = eval_term sigma beta t.
Proof.
  induction t; intros d c rho sigma beta Hclosed Hagree; simpl in *;
    try reflexivity.
  - rewrite (Hagree n Hclosed). reflexivity.
  - destruct Hclosed as [Ha Hb].
    rewrite (IHt1 d c rho sigma beta Ha Hagree),
      (IHt2 d c rho sigma beta Hb Hagree). reflexivity.
Qed.

Lemma eval_terms_agrees : forall ts d c rho sigma beta,
  Forall (closed_term d c) ts -> agrees_below c rho sigma ->
  eval_terms rho beta ts = eval_terms sigma beta ts.
Proof.
  intros ts d c rho sigma beta H. induction H; intro Hagree; simpl.
  - reflexivity.
  - rewrite (eval_term_agrees x d c rho sigma beta H Hagree), IHForall by exact Hagree.
    reflexivity.
Qed.

Theorem satisfies_agrees : forall G rho beta g,
  satisfies G rho beta g -> forall sigma d c,
  closed_env G -> closed_goal G d c g -> agrees_below c rho sigma ->
  satisfies G sigma beta g.
Proof.
  intros G rho beta g Hsat. induction Hsat; intros sigma d c Henv Hclosed Hagree;
    simpl in Hclosed.
  - constructor.
  - destruct Hclosed as [Ht Hu]. eapply Sat_unify.
    + rewrite <- (eval_term_agrees t d c rho sigma beta Ht Hagree). exact H.
    + rewrite <- (eval_term_agrees u d c rho sigma beta Hu Hagree). exact H0.
  - apply Sat_disj_left. eapply IHHsat; [exact Henv|exact (proj1 Hclosed)|exact Hagree].
  - apply Sat_disj_right. eapply IHHsat; [exact Henv|exact (proj2 Hclosed)|exact Hagree].
  - apply Sat_conj.
    + eapply IHHsat1; [exact Henv|exact (proj1 Hclosed)|exact Hagree].
    + eapply IHHsat2; [exact Henv|exact (proj2 Hclosed)|exact Hagree].
  - eapply Sat_fresh; [exact H|]. eapply IHHsat; eassumption.
  - rewrite H in Hclosed. destruct Hclosed as [Harity Hargs].
    eapply Sat_call; [exact H|exact H0| |].
    + rewrite <- (eval_terms_agrees args d c rho sigma beta Hargs Hagree). exact H1.
    + eapply IHHsat; [exact Henv| |exact Hagree].
      eapply closed_goal_mono; [apply Nat.le_refl|apply Nat.le_0_l|].
      exact (Henv r arity body H).
Qed.

Lemma satisfies_sub_agrees : forall c rho sigma s,
  closed_sub c s -> agrees_below c rho sigma -> satisfies_sub rho s ->
  satisfies_sub sigma s.
Proof.
  intros c rho sigma s Hclosed Hagree Hmodel x t Hlook.
  assert (Hb : x < c /\ closed_term 0 c t).
  { clear Hmodel. revert Hclosed Hlook. induction s as [|[y u] s IH]; intros Hclosed Hlook; [discriminate|].
    simpl in *. destruct Hclosed as [Hy [Hu Htail]].
    destruct (Nat.eqb_spec x y) as [->|Hneq].
    - inversion Hlook; subst. split; assumption.
    - apply IH; assumption. }
  destruct Hb as [Hx Ht].
  rewrite <- (eval_term_agrees t 0 c rho sigma [] Ht Hagree), <- (Hagree x Hx).
  apply Hmodel. exact Hlook.
Qed.

(** Override exactly one newly allocated block. *)
Definition extend_valuation (rho : valuation) (start : nat) (values : list ground)
  : valuation := fun x =>
  if x <? start then rho x
  else match nth_error values (x - start) with Some v => v | None => rho x end.

Lemma extend_valuation_old : forall rho start values,
  agrees_below start rho (extend_valuation rho start values).
Proof.
  intros rho start values x Hx. unfold extend_valuation.
  rewrite (proj2 (Nat.ltb_lt x start) Hx). reflexivity.
Qed.

Lemma extend_valuation_new : forall rho start values i v,
  nth_error values i = Some v -> extend_valuation rho start values (start + i) = v.
Proof.
  intros rho start values i v Hnth. unfold extend_valuation.
  rewrite (proj2 (Nat.ltb_ge (start + i) start) ltac:(lia)).
  replace (start + i - start) with i by lia. rewrite Hnth. reflexivity.
Qed.

Lemma eval_fresh_block : forall rho start values,
  eval_terms (extend_valuation rho start values) []
    (map tvar (seq start (List.length values))) = Some values.
Proof.
  intros rho start values.
  assert (Haux : forall len offset vs,
    (forall i v, nth_error vs i = Some v ->
      extend_valuation rho start values (offset + i) = v) ->
    List.length vs = len ->
    eval_terms (extend_valuation rho start values) [] (map tvar (seq offset len)) = Some vs).
  { induction len as [|len IH]; intros offset vs Hvals Hlen.
    - destruct vs; [reflexivity|discriminate].
    - destruct vs as [|v vs]; [discriminate|]. simpl in Hlen. injection Hlen as Hlen.
      simpl. pose proof (Hvals 0 v eq_refl) as Hv. rewrite Nat.add_0_r in Hv. rewrite Hv.
      rewrite (IH (S offset) vs).
      + reflexivity.
      + intros i u Hi. replace (S offset + i) with (offset + S i) by lia.
        apply Hvals. exact Hi.
      + exact Hlen. }
  apply Haux; [|reflexivity]. intros i v Hi. apply extend_valuation_new. exact Hi.
Qed.

Theorem fresh_witness_extension : forall G rho c s k body values,
  closed_env G -> closed_sub c s -> closed_goal G k c body ->
  satisfies_sub rho s -> List.length values = k ->
  satisfies G rho values body ->
  let sigma := extend_valuation rho c values in
  agrees_below c rho sigma /\ satisfies_sub sigma s /\
  satisfies G sigma [] (open (map tvar (seq c k)) body).
Proof.
  intros G rho c s k body values Henv Hsub Hbody Hmodel Hlen Hsat sigma.
  pose proof (extend_valuation_old rho c values) as Hagree.
  split; [exact Hagree|]. split.
  - eapply satisfies_sub_agrees; eassumption.
  - assert (Ha : runtime_open_args (c + k) (map tvar (seq c k))).
    { apply fresh_args_open_args. reflexivity. }
    assert (He : eval_terms sigma [] (map tvar (seq c k)) = Some values).
    { rewrite <- Hlen. apply eval_fresh_block. }
    apply (proj2 (satisfies_open G sigma (c + k) (map tvar (seq c k)) values body Ha He)).
    eapply satisfies_agrees; eassumption.
Qed.
