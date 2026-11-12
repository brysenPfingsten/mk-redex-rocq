From Stdlib Require Import List Arith Lia.
From MkRedex.Execution Require StructuralUnifier.
From MkRedex.Language Require Terms Substitution Unification Scoping ScopedUnification.
From MkRedex.Denotational Require Denotation.
From MkRedex.Correctness Require Export GroundUnification.
From MkRedex.Correctness Require StructuralUnification.
Import ListNotations.
Set Default Goal Selector "!".

Fixpoint fin_nat {n} (x : StructuralUnifier.Fin n) : nat :=
  match x with StructuralUnifier.f0 => 0 | StructuralUnifier.fs y => S (fin_nat y) end.
Lemma fin_nat_bound : forall n (x : StructuralUnifier.Fin n), fin_nat x < n.
Proof. intros n x. induction x; simpl; lia. Qed.

Definition erase_rigid (a : StructuralUnifier.Rigid) : Terms.term :=
  match a with StructuralUnifier.symbol s => Terms.tsym s | StructuralUnifier.text s => Terms.tstr s
  | StructuralUnifier.number n => Terms.tnat n | StructuralUnifier.boolean b => Terms.tbool b | StructuralUnifier.empty => Terms.tnil end.
Fixpoint erase {n} (t : StructuralUnifier.Term n) : Terms.term :=
  match t with StructuralUnifier.var x => Terms.tvar (fin_nat x)
  | StructuralUnifier.atom a => erase_rigid a | StructuralUnifier.fork a b => Terms.tcons (erase a) (erase b) end.
Definition restrict {n} (rho : Denotation.valuation) : StructuralUnifier.Fin n -> Denotation.ground := fun x => rho (fin_nat x).

Lemma erase_closed : forall n (t : StructuralUnifier.Term n), Scoping.closed_term 0 n (erase t).
Proof.
  intros n t. induction t; simpl.
  - apply fin_nat_bound.
  - destruct r; exact I.
  - split; assumption.
Qed.
Lemma eval_erase : forall n (t : StructuralUnifier.Term n) rho,
  Denotation.eval_term rho [] (erase t) = Some (StructuralUnification.eval (restrict rho) t).
Proof.
  intros n t. induction t; intro rho; simpl.
  - reflexivity.
  - destruct r; reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.
Lemma erase_equality : forall n (t u : StructuralUnifier.Term n) rho,
  (exists v, Denotation.eval_term rho [] (erase t) = Some v /\ Denotation.eval_term rho [] (erase u) = Some v) <->
  StructuralUnification.eval (restrict rho) t = StructuralUnification.eval (restrict rho) u.
Proof.
  intros n t u rho. rewrite !eval_erase. split.
  - intros [v [Ht Hu]]. congruence.
  - intro E. exists (StructuralUnification.eval (restrict rho) t). split; congruence.
Qed.

Definition old_result_models (rho : Denotation.valuation) (result : option Substitution.sub) : Prop :=
  match result with None => False | Some sigma => Denotation.satisfies_sub rho sigma end.

(** The original inductive relation also computes exactly the ground solutions
    of its input substitution together with its equality constraint. *)
Lemma Unify_result_models : forall c initial t u result,
  Substitution.acyclic_sub initial -> Scoping.closed_sub c initial ->
  Scoping.closed_term 0 c t -> Scoping.closed_term 0 c u ->
  MkRedex.Language.Unification.Unify t u initial result -> forall rho,
  old_result_models rho result <->
  Denotation.satisfies_sub rho initial /\
    exists v, Denotation.eval_term rho [] t = Some v /\ Denotation.eval_term rho [] u = Some v.
Proof.
  intros c initial t u [answer|] Hacyc Hsub Ht Hu Hresult rho.
  - split.
    + intro Hmodel. split.
      * eapply GroundUnification.Unify_ground_old_bindings; eassumption.
      * exact (GroundUnification.Unify_ground_sound c initial t u answer rho Hacyc Ht Hresult Hmodel).
    + intros [Hmodel [v [Et Eu]]].
      destruct (GroundUnification.ground_unification_complete c rho initial t u v Hacyc Hsub Ht Hu Hmodel Et Eu)
        as [answer' [Hresult' Hmodel']].
      pose proof (MkRedex.Language.Unification.Unify_functional t u initial _ _ Hresult Hresult') as E.
      injection E as <-. exact Hmodel'.
  - split; [contradiction|]. intros [Hmodel [v [Et Eu]]].
    destruct (GroundUnification.ground_unification_complete c rho initial t u v Hacyc Hsub Ht Hu Hmodel Et Eu)
      as [answer [Hsuccess _]].
    pose proof (MkRedex.Language.Unification.Unify_functional t u initial _ _ Hresult Hsuccess). discriminate.
Qed.

(** Equivalence at an arbitrary related input state. The representation
    premise compares input solution sets; the conclusion compares outputs.
    No equality between a renumbering AList and a binding list is required. *)
Theorem amgu_Unify_equivalent : forall n (t u : StructuralUnifier.Term n) acc initial result,
  Substitution.acyclic_sub initial -> Scoping.closed_sub n initial ->
  (forall rho, Denotation.satisfies_sub rho initial <-> StructuralUnification.models (restrict rho) acc) ->
  MkRedex.Language.Unification.Unify (erase t) (erase u) initial result -> forall rho,
  old_result_models rho result <->
  StructuralUnification.result_models (restrict rho) (StructuralUnifier.amgu n t u acc).
Proof.
  intros n t u acc initial result Hacyc Hsub Hinput Hresult rho.
  rewrite (Unify_result_models n initial (erase t) (erase u) result Hacyc Hsub
    (erase_closed n t) (erase_closed n u) Hresult rho).
  rewrite Hinput, erase_equality. symmetry. apply StructuralUnification.amgu_result_models.
Qed.

Lemma empty_acyclic : Substitution.acyclic_sub [].
Proof. intro x. constructor. intros y [t [Hlookup _]]. discriminate. Qed.

Theorem mgu_Unify_equivalent : forall n (t u : StructuralUnifier.Term n) result,
  MkRedex.Language.Unification.Unify (erase t) (erase u) [] result -> forall rho,
  old_result_models rho result <-> StructuralUnification.result_models (restrict rho) (StructuralUnifier.mgu t u).
Proof.
  intros n t u result Hresult.
  apply (amgu_Unify_equivalent n t u (existT _ n StructuralUnifier.anil) [] result empty_acyclic I).
  - intro rho. split; [intros _; apply StructuralUnification.models_nil|intros _; apply Denotation.satisfies_sub_nil].
  - exact Hresult.
Qed.

Theorem mgu_has_equivalent_Unify_result : forall n (t u : StructuralUnifier.Term n),
  exists result, MkRedex.Language.Unification.Unify (erase t) (erase u) [] result /\
    forall rho, old_result_models rho result <-> StructuralUnification.result_models (restrict rho) (StructuralUnifier.mgu t u).
Proof.
  intros n t u.
  destruct (ScopedUnification.Unify_total n [] (erase t) (erase u) empty_acyclic I
    (erase_closed n t) (erase_closed n u)) as [result Hresult].
  exists result. split; [exact Hresult|apply mgu_Unify_equivalent; exact Hresult].
Qed.

Fixpoint fin_index (n k : nat) : option (StructuralUnifier.Fin n) :=
  match n as m return option (StructuralUnifier.Fin m) with
  | 0 => None
  | S n => match k with 0 => Some StructuralUnifier.f0 | S k =>
      match fin_index n k with None => None | Some x => Some (StructuralUnifier.fs x) end end
  end.
Lemma fin_index_nat : forall n (x : StructuralUnifier.Fin n), fin_index n (fin_nat x) = Some x.
Proof. intros n x. induction x; simpl; [reflexivity|rewrite IHx; reflexivity]. Qed.
Definition extend {n} (rho : StructuralUnifier.Fin n -> Denotation.ground) : Denotation.valuation := fun k =>
  match fin_index n k with None => Denotation.gnil | Some x => rho x end.
Lemma restrict_extend : forall n (rho : StructuralUnifier.Fin n -> Denotation.ground) x,
  restrict (extend rho) x = rho x.
Proof. intros n rho x. unfold restrict,extend. rewrite fin_index_nat. reflexivity. Qed.

Lemma indexed_models_inhabited : forall m (acc : StructuralUnifier.Acc m), exists rho, StructuralUnification.models rho acc.
Proof.
  intros m [n sigma]. exists (fun x => StructuralUnification.eval (fun _ => Denotation.gnil) (StructuralUnifier.sub sigma x)).
  exists (fun _ => Denotation.gnil). reflexivity.
Qed.
Lemma indexed_models_extend : forall m acc (rho : StructuralUnifier.Fin m -> Denotation.ground),
  StructuralUnification.models rho acc -> StructuralUnification.models (restrict (extend rho)) acc.
Proof.
  intros m [n sigma] rho [gamma Hgamma]. exists gamma. intro x.
  rewrite restrict_extend. apply Hgamma.
Qed.

Theorem amgu_Unify_failure : forall n (t u : StructuralUnifier.Term n) acc initial result,
  Substitution.acyclic_sub initial -> Scoping.closed_sub n initial ->
  (forall rho, Denotation.satisfies_sub rho initial <-> StructuralUnification.models (restrict rho) acc) ->
  MkRedex.Language.Unification.Unify (erase t) (erase u) initial result ->
  (StructuralUnifier.amgu n t u acc = None <-> result = None).
Proof.
  intros n t u acc initial result Hacyc Hsub Hinput Hresult.
  pose proof (amgu_Unify_equivalent n t u acc initial result Hacyc Hsub Hinput Hresult) as Hequiv.
  split.
  - intro E. destruct result as [answer|]; [|reflexivity].
    pose proof (MkRedex.Language.Unification.Unify_acyclic _ _ _ _ Hacyc Hresult) as Hacout.
    pose proof (ScopedUnification.Unify_closed n _ _ _ _ (erase_closed n t)
      (erase_closed n u) Hsub Hresult) as Hclout.
    destruct (acyclic_closed_has_model n answer Hacout Hclout) as [rho Hrho].
    apply (Hequiv rho) in Hrho. rewrite E in Hrho. contradiction.
  - intro E. subst result. destruct (StructuralUnifier.amgu n t u acc) as [out|] eqn:Eout; [|reflexivity].
    destruct (indexed_models_inhabited n out) as [rho Hrho].
    apply indexed_models_extend in Hrho.
    pose proof (proj2 (Hequiv (extend rho))) as H.
    specialize (H Hrho). contradiction.
Qed.

Theorem mgu_Unify_failure : forall n (t u : StructuralUnifier.Term n) result,
  MkRedex.Language.Unification.Unify (erase t) (erase u) [] result ->
  (StructuralUnifier.mgu t u = None <-> result = None).
Proof.
  intros n t u result Hresult.
  apply (amgu_Unify_failure n t u (existT _ n StructuralUnifier.anil) [] result empty_acyclic I).
  - intro rho. split; [intros _; apply StructuralUnification.models_nil|intros _; apply Denotation.satisfies_sub_nil].
  - exact Hresult.
Qed.

(** The legacy outcome is unique syntactically. The indexed result agrees
    on failure and on every represented ground valuation, without equating
    representations or identifying equivalent MGUs as literal binding lists. *)
Theorem structural_Unify_equivalence : forall n (t u : StructuralUnifier.Term n),
  exists! result,
    MkRedex.Language.Unification.Unify (erase t) (erase u) [] result /\
    (StructuralUnifier.mgu t u = None <-> result = None) /\
    forall rho, old_result_models rho result <-> StructuralUnification.result_models (restrict rho) (StructuralUnifier.mgu t u).
Proof.
  intros n t u.
  destruct (mgu_has_equivalent_Unify_result n t u) as [result [Hresult Hequiv]].
  exists result. split.
  - split; [exact Hresult|]. split; [apply mgu_Unify_failure; exact Hresult|exact Hequiv].
  - intros other [Hother _]. eapply MkRedex.Language.Unification.Unify_functional; eassumption.
Qed.

Corollary mgu_failure_iff_Unify_failure : forall n (t u : StructuralUnifier.Term n),
  StructuralUnifier.mgu t u = None <-> MkRedex.Language.Unification.Unify (erase t) (erase u) [] None.
Proof.
  intros n t u. split.
  - intro E. destruct (mgu_has_equivalent_Unify_result n t u) as [result [Hresult _]].
    apply (proj1 (mgu_Unify_failure n t u result Hresult)) in E. subst result. exact Hresult.
  - intro Hresult. apply (proj2 (mgu_Unify_failure n t u None Hresult)). reflexivity.
Qed.

Corollary mgu_success_iff_Unify_success : forall n (t u : StructuralUnifier.Term n),
  (exists acc, StructuralUnifier.mgu t u = Some acc) <->
  exists answer, MkRedex.Language.Unification.Unify (erase t) (erase u) [] (Some answer).
Proof.
  intros n t u. split.
  - intros [acc E]. destruct (mgu_has_equivalent_Unify_result n t u) as [[answer|] [Hresult _]].
    + exists answer. exact Hresult.
    + pose proof (proj2 (mgu_Unify_failure n t u None Hresult) eq_refl) as Hnone.
      rewrite E in Hnone. discriminate.
  - intros [answer Hresult]. destruct (StructuralUnifier.mgu t u) as [acc|] eqn:E; [exists acc; reflexivity|].
    pose proof (proj1 (mgu_Unify_failure n t u (Some answer) Hresult) E). discriminate.
Qed.

Lemma fin_index_sound : forall n k x, fin_index n k = Some x -> fin_nat x = k.
Proof.
  induction n; intros k x H; [discriminate|]. destruct k; simpl in H.
  - inversion H; reflexivity.
  - destruct (fin_index n k) eqn:E; [|discriminate]. inversion H; subst. simpl.
    f_equal. eapply IHn; eassumption.
Qed.
Lemma fin_index_complete : forall n k, k<n -> exists x, fin_index n k = Some x.
Proof.
  induction n; intros k H; [lia|]. destruct k; simpl.
  - exists StructuralUnifier.f0. reflexivity.
  - destruct (IHn k ltac:(lia)) as [x Hx]. rewrite Hx. eexists. reflexivity.
Qed.

(** Proof-side conversion of valid legacy runtime syntax; parameters are
    deliberately rejected. The live execution interface is unchanged. *)
Fixpoint index_term (n : nat) (t : Terms.term) : option (StructuralUnifier.Term n) :=
  match t with
  | Terms.tvar k => match fin_index n k with None => None | Some x => Some (StructuralUnifier.var x) end
  | Terms.tpar _ => None
  | Terms.tsym s => Some (StructuralUnifier.atom (StructuralUnifier.symbol s))
  | Terms.tstr s => Some (StructuralUnifier.atom (StructuralUnifier.text s))
  | Terms.tnat k => Some (StructuralUnifier.atom (StructuralUnifier.number k))
  | Terms.tbool b => Some (StructuralUnifier.atom (StructuralUnifier.boolean b))
  | Terms.tnil => Some StructuralUnifier.leaf
  | Terms.tcons a b => match index_term n a, index_term n b with
      | Some a', Some b' => Some (StructuralUnifier.fork a' b') | _, _ => None end
  end.

Lemma index_term_sound : forall t n indexed,
  index_term n t = Some indexed -> erase indexed = t.
Proof.
  induction t; intros bound indexed H; simpl in H; try (inversion H; reflexivity).
  - destruct (fin_index bound n) eqn:E; [|discriminate]. inversion H; subst. simpl.
    f_equal. eapply fin_index_sound; eassumption.
  - destruct (index_term bound t1) eqn:Ea; [|discriminate].
    destruct (index_term bound t2) eqn:Eb; [|discriminate]. inversion H; subst. simpl.
    rewrite (IHt1 _ _ Ea), (IHt2 _ _ Eb). reflexivity.
Qed.
Lemma index_term_complete : forall t n,
  Scoping.closed_term 0 n t -> exists indexed, index_term n t = Some indexed.
Proof.
  induction t; intros bound H; simpl in *; try (eexists; reflexivity).
  - destruct (fin_index_complete bound n H) as [x Hx]. rewrite Hx. eexists. reflexivity.
  - lia.
  - destruct H as [Ha Hb]. destruct (IHt1 bound Ha) as [a Ea], (IHt2 bound Hb) as [b Eb].
    rewrite Ea,Eb. eexists. reflexivity.
Qed.

Theorem valid_terms_structural_equivalence : forall n t u,
  Scoping.closed_term 0 n t -> Scoping.closed_term 0 n u ->
  exists indexed_t indexed_u,
    index_term n t = Some indexed_t /\ index_term n u = Some indexed_u /\
    exists! result,
      MkRedex.Language.Unification.Unify t u [] result /\
      (StructuralUnifier.mgu indexed_t indexed_u = None <-> result = None) /\
      forall rho, old_result_models rho result <->
        StructuralUnification.result_models (restrict rho) (StructuralUnifier.mgu indexed_t indexed_u).
Proof.
  intros n t u Ht Hu.
  destruct (index_term_complete t n Ht) as [it Hit], (index_term_complete u n Hu) as [iu Hiu].
  exists it,iu. split; [exact Hit|]. split; [exact Hiu|].
  rewrite <- (index_term_sound t n it Hit), <- (index_term_sound u n iu Hiu).
  apply structural_Unify_equivalence.
Qed.
