From MkRedex.Language Require Import Scoping ScopedUnification Terms Goals Substitution Unification Trees.
From Stdlib Require Import List Arith Lia.
From MkRedex.Denotational Require Import Denotation.
From MkRedex.Execution Require Import Unifier.
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

(** A competing solution need not contain the input bindings literally: it
    must satisfy them through substitution application. Requiring acyclicity
    prevents [unifier] from holding vacuously because application has no result. *)
Definition compatible_unifier (s : sub) (t u : term) (candidate : sub) : Prop :=
  acyclic_sub candidate /\ models_sub candidate s /\ unifier candidate t u.

(** Success preserves the runtime domain and every visible input binding,
    solves the equality, and is at least as general as every compatible
    acyclic solution. Prefix extension additionally records the operational
    representation of substitutions as lists with new bindings at the front. *)
Record most_general_extension (c : nat) (s : sub) (t u : term) (answer : sub) : Prop := {
  mgu_closed : closed_sub c answer;
  mgu_acyclic : acyclic_sub answer;
  mgu_extends : exists prefix, answer = prefix ++ s;
  mgu_preserves_bindings : forall x v, lookup x s = Some v -> lookup x answer = Some v;
  mgu_unifies : unifier answer t u;
  mgu_most_general : forall candidate,
    compatible_unifier s t u candidate -> more_general answer candidate
}.

(** One complete contract for an outcome. Exact agreement with [Unify]
    identifies the specified operational outcome, rather than claiming that
    all mathematically equivalent MGUs are syntactically identical. *)
Record unification_correct_result (c : nat) (s : sub) (t u : term)
  (result : option sub) : Prop := {
  unification_spec : forall other, Unify t u s other <-> other = result;
  unification_failure : result = None <-> ~ exists candidate, compatible_unifier s t u candidate;
  unification_success : forall answer, result = Some answer ->
    most_general_extension c s t u answer
}.

Lemma Unify_mgu : forall c s t u answer,
  acyclic_sub s -> closed_sub c s -> closed_term 0 c t -> closed_term 0 c u ->
  Unify t u s (Some answer) -> most_general_extension c s t u answer.
Proof.
  intros c s t u answer Hacyc Hsub Ht Hu Hresult. constructor.
  - exact (Unify_closed c t u s answer Ht Hu Hsub Hresult).
  - exact (Unify_acyclic t u s answer Hacyc Hresult).
  - eapply Unify_extends; [exact Hresult|reflexivity].
  - destruct Hresult as [w1 [w2 [_ [_ Hw]]]].
    exact (UnifyW_norebind w1 w2 s (Some answer) Hw answer eq_refl).
  - exact (Unify_sound t u s answer Hacyc Hresult).
  - intros candidate [Hac [Hmodel Hunit]].
    exact (Unify_most_general_model t u s answer Hresult candidate Hac Hmodel Hunit).
Qed.

Lemma Unify_correct_result : forall c s t u result,
  acyclic_sub s -> closed_sub c s -> closed_term 0 c t -> closed_term 0 c u ->
  Unify t u s result -> unification_correct_result c s t u result.
Proof.
  intros c s t u result Hacyc Hsub Ht Hu Hresult.
  assert (Hsuccess : forall answer, result = Some answer -> most_general_extension c s t u answer).
  { intros answer E. subst result. eapply Unify_mgu; eassumption. }
  constructor.
  - intro other. split.
    + intro Hother. eapply Unify_functional; [exact Hother|exact Hresult].
    + intro E. subst other. exact Hresult.
  - split.
    + intro E. subst result. intros [candidate [Hac [Hmodel Hunit]]].
      destruct Hresult as [w1 [w2 [Hw1 [Hw2 Hfail]]]].
      exact (UnifyW_complete_fail_model w1 w2 s Hacyc Hfail
        t u Hw1 Hw2 candidate Hac Hmodel Hunit).
    + intro Hnone. destruct result as [answer|]; [|reflexivity].
      exfalso. apply Hnone. exists answer.
      pose proof (Hsuccess answer eq_refl) as Hmgu.
      split; [exact (mgu_acyclic c s t u answer Hmgu)|]. split.
      * apply models_sub_of_extension. exact (mgu_preserves_bindings c s t u answer Hmgu).
      * exact (mgu_unifies c s t u answer Hmgu).
  - exact Hsuccess.
Qed.

(** Total correctness of the relational solver: valid inputs have exactly
    one specified outcome, and that outcome decides existence of compatible
    unifiers and computes a most general extension on success. The smaller
    lemmas supply the algebraic facts; totality and functionality assemble
    them into this single contract. See docs/proofs.md, Unification. *)
Theorem unification_correct : forall c s t u,
  acyclic_sub s -> closed_sub c s -> closed_term 0 c t -> closed_term 0 c u ->
  exists! result, unification_correct_result c s t u result.
Proof.
  intros c s t u Hacyc Hsub Ht Hu.
  destruct (Unify_total c s t u Hacyc Hsub Ht Hu) as [result Hresult].
  exists result. split.
  - eapply Unify_correct_result; eassumption.
  - intros other Hother.
    apply (proj1 (unification_spec c s t u other Hother result)). exact Hresult.
Qed.

(** The executable function is total on its proof-indexed valid domain and
    satisfies the same contract. Its internal increasing-fuel search is
    justified by unification totality, not by an assumed runtime fuel bound. *)
Theorem unify_fn_correct : forall c s t u Hacyc Hsub Ht Hu,
  unification_correct_result c s t u (unify_fn t u s c Hacyc Hsub Ht Hu).
Proof.
  intros c s t u Hacyc Hsub Ht Hu.
  apply Unify_correct_result; try assumption.
  apply (proj2 (unify_fn_spec c s t u Hacyc Hsub Ht Hu _)). reflexivity.
Qed.

Lemma ApplySub_closed : forall s t r,
  Substitution.ApplySub s t r -> forall c,
  Scoping.closed_sub c s -> Scoping.closed_term 0 c t -> Scoping.closed_term 0 c r.
Proof.
  intros s t r H. induction H; intros c Hs Ht; simpl in *; try exact Ht.
  - apply IHApplySub; [exact Hs|]. eapply Scoping.lookup_closed; eassumption.
  - destruct Ht as [Ha Hb]. split; [apply IHApplySub1|apply IHApplySub2]; assumption.
Qed.

Lemma finite_ground_choice : forall c (P : nat -> Denotation.ground -> Prop),
  (forall x, x<c -> exists v, P x v) ->
  exists rho : Denotation.valuation, forall x, x<c -> P x (rho x).
Proof.
  induction c; intros P H.
  - exists (fun _ => Denotation.gnil). intros x Hx. lia.
  - destruct (IHc P ltac:(intros x Hx; apply H; lia)) as [rho Hr].
    destruct (H c ltac:(lia)) as [v Hv].
    exists (fun x => if Nat.eq_dec x c then v else rho x).
    intros x Hx. destruct (Nat.eq_dec x c) as [->|Hneq]; [exact Hv|apply Hr; lia].
Qed.

(** A finite acyclic binding store always has a ground model. Choose the
    interpretations of its finitely many normalized variables constructively;
    no choice axiom or well-founded executable application function is used. *)
Lemma acyclic_closed_has_model : forall c s,
  Substitution.acyclic_sub s -> Scoping.closed_sub c s -> exists rho, Denotation.satisfies_sub rho s.
Proof.
  intros c s Hacyc Hclosed.
  set (base := (fun _ => Denotation.gnil) : Denotation.valuation).
  set (P := fun x v => forall r, Substitution.ApplySub s (Terms.tvar x) r -> Denotation.eval_term base [] r = Some v).
  assert (Hex : forall x, x<c -> exists v, P x v).
  { intros x Hx. destruct (MkRedex.Language.Unification.ApplySub_total s Hacyc (Terms.tvar x)) as [r Hr].
    pose proof (ApplySub_closed s (Terms.tvar x) r Hr c Hclosed Hx) as Hcr.
    destruct (eval_term_closed_total r 0 c base [] Hcr eq_refl) as [v Hv].
    exists v. intros other Hother.
    pose proof (Substitution.ApplySub_functional s (Terms.tvar x) r other Hr Hother) as <-. exact Hv. }
  destruct (finite_ground_choice c P Hex) as [rho Hrho].
  assert (Hnorm : forall t r, Scoping.closed_term 0 c t -> Substitution.ApplySub s t r ->
    Denotation.eval_term rho [] t = Denotation.eval_term base [] r).
  { intro t. induction t; intros r Ht Happ; simpl in Ht.
    - symmetry. apply Hrho; assumption.
    - lia.
    - inversion Happ; subst; reflexivity.
    - inversion Happ; subst; reflexivity.
    - inversion Happ; subst; reflexivity.
    - inversion Happ; subst; reflexivity.
    - inversion Happ; subst; reflexivity.
    - destruct Ht as [Ha Hb]. inversion Happ; subst.
      + simpl. rewrite (IHt1 _ Ha H1), (IHt2 _ Hb H3). reflexivity.
      + exfalso. apply (H0 t1 t2). reflexivity. }
  exists rho. intros x t Hlook.
  destruct (lookup_closed_binding c s x t Hclosed Hlook) as [Hx Ht].
  destruct (MkRedex.Language.Unification.ApplySub_total s Hacyc t) as [r Happ].
  rewrite (Hnorm t r Ht Happ).
  apply (Hrho x Hx r). eapply Substitution.AS_bound; eassumption.
Qed.

