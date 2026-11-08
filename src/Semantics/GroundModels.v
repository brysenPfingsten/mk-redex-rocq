From Stdlib Require Import List Arith Lia.
From MkRedex.Language Require Import Terms Substitution Unification.
From MkRedex.Semantics Require Import Denotation WellFormed GroundUnification.
Import ListNotations.
Set Default Goal Selector "!".

Fixpoint quote (v : ground) : term :=
  match v with
  | gsym s => tsym s | gstr s => tstr s | gnat n => tnat n
  | gbool b => tbool b | gnil => tnil
  | gcons a b => tcons (quote a) (quote b)
  end.

Lemma quote_eval : forall v rho beta,
  eval_term rho beta (quote v) = Some v.
Proof. induction v; intros rho beta; simpl; try reflexivity. rewrite IHv1, IHv2. reflexivity. Qed.

Lemma quote_apply : forall v s, ApplySub s (quote v) (quote v).
Proof.
  induction v; intro sigma; simpl; try (apply AS_rigid; intros; discriminate).
  apply AS_cons; [apply IHv1|apply IHv2].
Qed.

Lemma quote_occurs : forall v x, occurs x (quote v) = false.
Proof. induction v; intro x; simpl; try reflexivity. rewrite IHv1, IHv2. reflexivity. Qed.

Definition ground_sub (c : nat) (rho : valuation) : sub :=
  map (fun x => (x, quote (rho x))) (seq 0 c).

Lemma lookup_ground_sub : forall c rho x,
  lookup x (ground_sub c rho) = if x <? c then Some (quote (rho x)) else None.
Proof.
  intros c rho x. unfold ground_sub.
  assert (Haux : forall start len,
    lookup x (map (fun y => (y, quote (rho y))) (seq start len)) =
    if (start <=? x) && (x <? start + len) then Some (quote (rho x)) else None).
  { intros start len. revert start. induction len as [|len IH]; intro start; simpl.
    - destruct (Nat.leb_spec start x); destruct (Nat.ltb_spec x (start + 0));
        simpl; try reflexivity; lia.
    - destruct (Nat.eqb_spec x start) as [->|Hneq].
      + rewrite Nat.leb_refl. destruct (Nat.ltb_spec start (start + S len)); [reflexivity|lia].
      + rewrite IH. destruct (Nat.leb_spec (S start) x);
          destruct (Nat.ltb_spec x (S start + len));
          destruct (Nat.leb_spec start x);
          destruct (Nat.ltb_spec x (start + S len)); simpl; try reflexivity; lia. }
  rewrite Haux. simpl. reflexivity.
Qed.

Lemma ground_sub_acyclic : forall c rho, acyclic_sub (ground_sub c rho).
Proof.
  intros c rho x. constructor. intros y [t [Hlookup Hoccurs]].
  rewrite lookup_ground_sub in Hlookup.
  destruct (x <? c); [|discriminate]. inversion Hlookup; subst t.
  rewrite quote_occurs in Hoccurs. discriminate.
Qed.

Lemma ground_sub_apply : forall t c rho v,
  closed_term 0 c t -> eval_term rho [] t = Some v ->
  ApplySub (ground_sub c rho) t (quote v).
Proof.
  induction t; intros c rho v Hclosed Heval; simpl in *;
    try (inversion Heval; subst; apply AS_rigid; intros; discriminate).
  - inversion Heval; subst. eapply AS_bound.
    + rewrite lookup_ground_sub. rewrite (proj2 (Nat.ltb_lt n c) Hclosed). reflexivity.
    + apply quote_apply.
  - lia.
  - destruct Hclosed as [Ha Hb].
    destruct (eval_term rho [] t1) eqn:Ea; [|discriminate].
    destruct (eval_term rho [] t2) eqn:Eb; [|discriminate].
    inversion Heval; subst v. simpl. apply AS_cons; [eapply IHt1|eapply IHt2]; eassumption.
Qed.

Lemma lookup_closed_binding : forall c s x t,
  closed_sub c s -> lookup x s = Some t -> x < c /\ closed_term 0 c t.
Proof.
  intros c s. induction s as [|[y u] s IH]; intros x t Hs Hlook; [discriminate|].
  simpl in *. destruct Hs as [Hy [Hu Hs]].
  destruct (Nat.eqb_spec x y) as [->|Hneq].
  - inversion Hlook; subst. split; assumption.
  - eapply IH; eassumption.
Qed.

Lemma ground_sub_models : forall c rho s,
  closed_sub c s -> satisfies_sub rho s -> models_sub (ground_sub c rho) s.
Proof.
  intros c rho s Hclosed Hmodel x t Hlook r Happ.
  destruct (lookup_closed_binding c s x t Hclosed Hlook) as [Hx Ht].
  assert (Hxapp : ApplySub (ground_sub c rho) (tvar x) (quote (rho x))).
  { eapply ground_sub_apply; [exact Hx|reflexivity]. }
  pose proof (ApplySub_functional _ _ _ _ Happ Hxapp) as ->.
  apply ground_sub_apply; [exact Ht|apply Hmodel; exact Hlook].
Qed.

Lemma ground_sub_unifier : forall c rho t u v,
  closed_term 0 c t -> closed_term 0 c u ->
  eval_term rho [] t = Some v -> eval_term rho [] u = Some v ->
  unifier (ground_sub c rho) t u.
Proof.
  intros c rho t u v Ht Hu Et Eu a b Ha Hb.
  pose proof (ground_sub_apply t c rho v Ht Et) as Hta.
  pose proof (ground_sub_apply u c rho v Hu Eu) as Hua.
  rewrite (ApplySub_functional _ _ _ _ Ha Hta), (ApplySub_functional _ _ _ _ Hb Hua).
  reflexivity.
Qed.

Theorem ground_solution_unification_succeeds : forall c rho s t u v,
  acyclic_sub s -> closed_sub c s ->
  closed_term 0 c t -> closed_term 0 c u -> satisfies_sub rho s ->
  eval_term rho [] t = Some v -> eval_term rho [] u = Some v ->
  exists s', Unify t u s (Some s').
Proof.
  intros c rho s t u v Hacyc Hsub Ht Hu Hmodel Et Eu.
  destruct (Unify_total c s t u Hacyc Hsub Ht Hu) as [[s'|] Hresult].
  - exists s'. exact Hresult.
  - destruct Hresult as [w1 [w2 [Hw1 [Hw2 Hfail]]]].
    exfalso. eapply (UnifyW_complete_fail_model w1 w2 s Hacyc Hfail
      t u Hw1 Hw2 (ground_sub c rho)).
    + apply ground_sub_acyclic.
    + apply ground_sub_models; assumption.
    + eapply ground_sub_unifier; eassumption.
Qed.

Lemma ground_sub_models_reflect : forall c rho s,
  closed_sub c s -> models_sub (ground_sub c rho) s -> satisfies_sub rho s.
Proof.
  intros c rho s Hclosed Hmodel x t Hlook.
  destruct (lookup_closed_binding c s x t Hclosed Hlook) as [Hx Ht].
  assert (Hxapp : ApplySub (ground_sub c rho) (tvar x) (quote (rho x))).
  { eapply ground_sub_apply; [exact Hx|reflexivity]. }
  pose proof (Hmodel x t Hlook _ Hxapp) as Happ.
  rewrite (ApplySub_denotation _ _ _ Happ rho).
  - apply quote_eval.
  - intros y u Hlookup. rewrite lookup_ground_sub in Hlookup.
    destruct (y <? c); [|discriminate]. inversion Hlookup; subst u. apply quote_eval.
Qed.

Theorem ground_unification_complete : forall c rho s t u v,
  acyclic_sub s -> closed_sub c s ->
  closed_term 0 c t -> closed_term 0 c u -> satisfies_sub rho s ->
  eval_term rho [] t = Some v -> eval_term rho [] u = Some v ->
  exists s', Unify t u s (Some s') /\ satisfies_sub rho s'.
Proof.
  intros c rho s t u v Hacyc Hsub Ht Hu Hmodel Et Eu.
  destruct (ground_solution_unification_succeeds c rho s t u v
    Hacyc Hsub Ht Hu Hmodel Et Eu) as [s' Hresult].
  exists s'. split; [exact Hresult|].
  apply (ground_sub_models_reflect c rho s').
  - exact (Unify_closed c t u s s' Ht Hu Hsub Hresult).
  - apply more_general_models.
    + eapply Unify_acyclic; eassumption.
    + apply ground_sub_acyclic.
    + apply (Unify_most_general_model t u s s' Hresult (ground_sub c rho)).
      * apply ground_sub_acyclic.
      * apply ground_sub_models; assumption.
      * eapply ground_sub_unifier; eassumption.
Qed.
