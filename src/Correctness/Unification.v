From MkRedex.Language Require Import Scoping ScopedUnification Terms Goals Substitution Unification Trees.
From Stdlib Require Import List Arith Lia.
From MkRedex.Denotational Require Import Denotation.
From MkRedex.Operational Require Import WellFormed Reduction.
From MkRedex.Execution Require Import Executable.
Import ListNotations.
Set Default Goal Selector "!".

Lemma eval_term_closed_total : forall t d c rho beta,
  closed_term d c t -> List.length beta = d ->
  exists v, eval_term rho beta t = Some v.
Proof.
  induction t; intros d c rho beta Hclosed Hlen; simpl in *;
    try (eexists; reflexivity).
  - destruct (nth_error beta n) eqn:E.
    + eexists. reflexivity.
    + apply nth_error_None in E. lia.
  - destruct Hclosed as [Ha Hb].
    destruct (IHt1 d c rho beta Ha Hlen) as [a Ea].
    destruct (IHt2 d c rho beta Hb Hlen) as [b Eb].
    rewrite Ea, Eb. eexists. reflexivity.
Qed.

Lemma Unify_ground_sound : forall c s t u s' rho,
  acyclic_sub s -> closed_term 0 c t ->
  Unify t u s (Some s') -> satisfies_sub rho s' ->
  exists v, eval_term rho [] t = Some v /\ eval_term rho [] u = Some v.
Proof.
  intros c s t u s' rho Hacyc Hclosed Hu Hmodel.
  pose proof (Unify_acyclic t u s s' Hacyc Hu) as Hacyc'.
  destruct (ApplySub_total s' Hacyc' t) as [a Ha].
  destruct (ApplySub_total s' Hacyc' u) as [b Hb].
  pose proof (Unify_sound t u s s' Hacyc Hu a b Ha Hb) as E.
  subst b.
  destruct (eval_term_closed_total t 0 c rho [] Hclosed eq_refl) as [v Hv].
  exists v. split; [exact Hv|].
  rewrite (ApplySub_denotation s' u a Hb rho Hmodel).
  rewrite <- (ApplySub_denotation s' t a Ha rho Hmodel). exact Hv.
Qed.

Lemma Unify_ground_old_bindings : forall s t u s' rho,
  Unify t u s (Some s') -> satisfies_sub rho s' -> satisfies_sub rho s.
Proof.
  intros s t u s' rho [w1 [w2 [Hw1 [Hw2 Hu]]]] Hmodel x v Hlook.
  apply Hmodel. exact (UnifyW_norebind w1 w2 s (Some s') Hu s' eq_refl x v Hlook).
Qed.

(** A successful operational unification answer represents only valuations
    satisfying the source equality. The existential witness is the SAME
    witness used to represent the answer, including hidden fresh IDs. *)
Theorem unification_answer_sound : forall G query c t u s s' rho,
  acyclic_sub s -> closed_term 0 c t ->
  Unify t u s (Some s') ->
  represents query (mkstate s' c) rho ->
  solution G query (gunify t u) rho.
Proof.
  intros G query c t u s s' rho Hacyc Hclosed Hu [sigma [Hagree Hmodel]].
  exists sigma. split; [exact Hagree|].
  destruct (Unify_ground_sound c s t u s' sigma Hacyc Hclosed Hu Hmodel)
    as [v [Ht Hu']].
  eapply Sat_unify; eassumption.
Qed.

(** The connection also applies when the success is reached by the certified
    executable one-step interface, rather than supplied as a Unify proof. *)
Theorem executable_unification_answer_sound : forall G query c t u s s' rho Hok,
  acyclic_sub (st_sub s) -> closed_term 0 c t ->
  next_step G ([], tgoal (gunify t u) s) Hok =
    Some ([], tgoal gsucc s') ->
  represents query s' rho -> solution G query (gunify t u) rho.
Proof.
  intros G query c t u s s' rho Hok Hacyc Hclosed Hnext Hrepr.
  pose proof (next_step_sound G _ Hok _ Hnext) as Hstep.
  inversion Hstep; subst.
  - destruct E; simpl in *; try discriminate.
    subst r r'. inversion H0; subst.
    eapply unification_answer_sound; eassumption.
Qed.

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
