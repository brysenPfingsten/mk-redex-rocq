From Stdlib Require Import List Arith Lia.
From MkRedex.Execution Require StructuralUnifier.
From MkRedex.Language Require Terms Substitution Unification Scoping ScopedUnification.
From MkRedex.Denotational Require Denotation.
From MkRedex.Correctness Require Unification StructuralUnification.
Import ListNotations.
Set Default Goal Selector "!".
Module I := StructuralUnifier.
Module C := StructuralUnification.
Module T := Terms.
Module S := Substitution.
Module O := MkRedex.Language.Unification.
Module W := Scoping.
Module U := MkRedex.Correctness.Unification.
Module D := Denotation.

Fixpoint fin_nat {n} (x : I.Fin n) : nat :=
  match x with I.f0 => 0 | I.fs y => S (fin_nat y) end.
Lemma fin_nat_bound : forall n (x : I.Fin n), fin_nat x < n.
Proof. intros n x. induction x; simpl; lia. Qed.

Definition erase_rigid (a : I.Rigid) : T.term :=
  match a with I.symbol s => T.tsym s | I.text s => T.tstr s
  | I.number n => T.tnat n | I.boolean b => T.tbool b | I.empty => T.tnil end.
Fixpoint erase {n} (t : I.Term n) : T.term :=
  match t with I.var x => T.tvar (fin_nat x)
  | I.atom a => erase_rigid a | I.fork a b => T.tcons (erase a) (erase b) end.
Definition restrict {n} (rho : D.valuation) : I.Fin n -> D.ground := fun x => rho (fin_nat x).

Lemma erase_closed : forall n (t : I.Term n), W.closed_term 0 n (erase t).
Proof.
  intros n t. induction t; simpl.
  - apply fin_nat_bound.
  - destruct r; exact I.
  - split; assumption.
Qed.
Lemma eval_erase : forall n (t : I.Term n) rho,
  D.eval_term rho [] (erase t) = Some (C.eval (restrict rho) t).
Proof.
  intros n t. induction t; intro rho; simpl.
  - reflexivity.
  - destruct r; reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.
Lemma erase_equality : forall n (t u : I.Term n) rho,
  (exists v, D.eval_term rho [] (erase t) = Some v /\ D.eval_term rho [] (erase u) = Some v) <->
  C.eval (restrict rho) t = C.eval (restrict rho) u.
Proof.
  intros n t u rho. rewrite !eval_erase. split.
  - intros [v [Ht Hu]]. congruence.
  - intro E. exists (C.eval (restrict rho) t). split; congruence.
Qed.

Definition old_result_models (rho : D.valuation) (result : option S.sub) : Prop :=
  match result with None => False | Some sigma => D.satisfies_sub rho sigma end.

(** The original inductive relation also computes exactly the ground solutions
    of its input substitution together with its equality constraint. *)
Lemma Unify_result_models : forall c initial t u result,
  S.acyclic_sub initial -> W.closed_sub c initial ->
  W.closed_term 0 c t -> W.closed_term 0 c u ->
  O.Unify t u initial result -> forall rho,
  old_result_models rho result <->
  D.satisfies_sub rho initial /\
    exists v, D.eval_term rho [] t = Some v /\ D.eval_term rho [] u = Some v.
Proof.
  intros c initial t u [answer|] Hacyc Hsub Ht Hu Hresult rho.
  - split.
    + intro Hmodel. split.
      * eapply U.Unify_ground_old_bindings; eassumption.
      * exact (U.Unify_ground_sound c initial t u answer rho Hacyc Ht Hresult Hmodel).
    + intros [Hmodel [v [Et Eu]]].
      destruct (U.ground_unification_complete c rho initial t u v Hacyc Hsub Ht Hu Hmodel Et Eu)
        as [answer' [Hresult' Hmodel']].
      pose proof (O.Unify_functional t u initial _ _ Hresult Hresult') as E.
      injection E as <-. exact Hmodel'.
  - split; [contradiction|]. intros [Hmodel [v [Et Eu]]].
    destruct (U.ground_unification_complete c rho initial t u v Hacyc Hsub Ht Hu Hmodel Et Eu)
      as [answer [Hsuccess _]].
    pose proof (O.Unify_functional t u initial _ _ Hresult Hsuccess). discriminate.
Qed.

(** Equivalence at an arbitrary related input state. The representation
    premise compares input solution sets; the conclusion compares outputs.
    No equality between a renumbering AList and a binding list is required. *)
Theorem amgu_Unify_equivalent : forall n (t u : I.Term n) acc initial result,
  S.acyclic_sub initial -> W.closed_sub n initial ->
  (forall rho, D.satisfies_sub rho initial <-> C.models (restrict rho) acc) ->
  O.Unify (erase t) (erase u) initial result -> forall rho,
  old_result_models rho result <->
  C.result_models (restrict rho) (I.amgu n t u acc).
Proof.
  intros n t u acc initial result Hacyc Hsub Hinput Hresult rho.
  rewrite (Unify_result_models n initial (erase t) (erase u) result Hacyc Hsub
    (erase_closed n t) (erase_closed n u) Hresult rho).
  rewrite Hinput, erase_equality. symmetry. apply C.amgu_result_models.
Qed.

Lemma empty_acyclic : S.acyclic_sub [].
Proof. intro x. constructor. intros y [t [Hlookup _]]. discriminate. Qed.

Theorem mgu_Unify_equivalent : forall n (t u : I.Term n) result,
  O.Unify (erase t) (erase u) [] result -> forall rho,
  old_result_models rho result <-> C.result_models (restrict rho) (I.mgu t u).
Proof.
  intros n t u result Hresult.
  apply (amgu_Unify_equivalent n t u (existT _ n I.anil) [] result empty_acyclic I).
  - intro rho. split; [intros _; apply C.models_nil|intros _; apply D.satisfies_sub_nil].
  - exact Hresult.
Qed.

Theorem mgu_has_equivalent_Unify_result : forall n (t u : I.Term n),
  exists result, O.Unify (erase t) (erase u) [] result /\
    forall rho, old_result_models rho result <-> C.result_models (restrict rho) (I.mgu t u).
Proof.
  intros n t u.
  destruct (ScopedUnification.Unify_total n [] (erase t) (erase u) empty_acyclic I
    (erase_closed n t) (erase_closed n u)) as [result Hresult].
  exists result. split; [exact Hresult|apply mgu_Unify_equivalent; exact Hresult].
Qed.

Lemma ApplySub_closed : forall s t r,
  S.ApplySub s t r -> forall c,
  W.closed_sub c s -> W.closed_term 0 c t -> W.closed_term 0 c r.
Proof.
  intros s t r H. induction H; intros c Hs Ht; simpl in *; try exact Ht.
  - apply IHApplySub; [exact Hs|]. eapply W.lookup_closed; eassumption.
  - destruct Ht as [Ha Hb]. split; [apply IHApplySub1|apply IHApplySub2]; assumption.
Qed.

Lemma finite_ground_choice : forall c (P : nat -> D.ground -> Prop),
  (forall x, x<c -> exists v, P x v) ->
  exists rho : D.valuation, forall x, x<c -> P x (rho x).
Proof.
  induction c; intros P H.
  - exists (fun _ => D.gnil). intros x Hx. lia.
  - destruct (IHc P ltac:(intros x Hx; apply H; lia)) as [rho Hr].
    destruct (H c ltac:(lia)) as [v Hv].
    exists (fun x => if Nat.eq_dec x c then v else rho x).
    intros x Hx. destruct (Nat.eq_dec x c) as [->|Hneq]; [exact Hv|apply Hr; lia].
Qed.

(** A finite acyclic binding store always has a ground model. Choose the
    interpretations of its finitely many normalized variables constructively;
    no choice axiom or well-founded executable application function is used. *)
Lemma acyclic_closed_has_model : forall c s,
  S.acyclic_sub s -> W.closed_sub c s -> exists rho, D.satisfies_sub rho s.
Proof.
  intros c s Hacyc Hclosed.
  set (base := (fun _ => D.gnil) : D.valuation).
  set (P := fun x v => forall r, S.ApplySub s (T.tvar x) r -> D.eval_term base [] r = Some v).
  assert (Hex : forall x, x<c -> exists v, P x v).
  { intros x Hx. destruct (O.ApplySub_total s Hacyc (T.tvar x)) as [r Hr].
    pose proof (ApplySub_closed s (T.tvar x) r Hr c Hclosed Hx) as Hcr.
    destruct (U.eval_term_closed_total r 0 c base [] Hcr eq_refl) as [v Hv].
    exists v. intros other Hother.
    pose proof (S.ApplySub_functional s (T.tvar x) r other Hr Hother) as <-. exact Hv. }
  destruct (finite_ground_choice c P Hex) as [rho Hrho].
  assert (Hnorm : forall t r, W.closed_term 0 c t -> S.ApplySub s t r ->
    D.eval_term rho [] t = D.eval_term base [] r).
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
  destruct (U.lookup_closed_binding c s x t Hclosed Hlook) as [Hx Ht].
  destruct (O.ApplySub_total s Hacyc t) as [r Happ].
  rewrite (Hnorm t r Ht Happ).
  apply (Hrho x Hx r). eapply S.AS_bound; eassumption.
Qed.

Fixpoint fin_index (n k : nat) : option (I.Fin n) :=
  match n as m return option (I.Fin m) with
  | 0 => None
  | S n => match k with 0 => Some I.f0 | S k =>
      match fin_index n k with None => None | Some x => Some (I.fs x) end end
  end.
Lemma fin_index_nat : forall n (x : I.Fin n), fin_index n (fin_nat x) = Some x.
Proof. intros n x. induction x; simpl; [reflexivity|rewrite IHx; reflexivity]. Qed.
Definition extend {n} (rho : I.Fin n -> D.ground) : D.valuation := fun k =>
  match fin_index n k with None => D.gnil | Some x => rho x end.
Lemma restrict_extend : forall n (rho : I.Fin n -> D.ground) x,
  restrict (extend rho) x = rho x.
Proof. intros n rho x. unfold restrict,extend. rewrite fin_index_nat. reflexivity. Qed.

Lemma indexed_models_inhabited : forall m (acc : I.Acc m), exists rho, C.models rho acc.
Proof.
  intros m [n sigma]. exists (fun x => C.eval (fun _ => D.gnil) (I.sub sigma x)).
  exists (fun _ => D.gnil). reflexivity.
Qed.
Lemma indexed_models_extend : forall m acc (rho : I.Fin m -> D.ground),
  C.models rho acc -> C.models (restrict (extend rho)) acc.
Proof.
  intros m [n sigma] rho [gamma Hgamma]. exists gamma. intro x.
  rewrite restrict_extend. apply Hgamma.
Qed.

Theorem amgu_Unify_failure : forall n (t u : I.Term n) acc initial result,
  S.acyclic_sub initial -> W.closed_sub n initial ->
  (forall rho, D.satisfies_sub rho initial <-> C.models (restrict rho) acc) ->
  O.Unify (erase t) (erase u) initial result ->
  (I.amgu n t u acc = None <-> result = None).
Proof.
  intros n t u acc initial result Hacyc Hsub Hinput Hresult.
  pose proof (amgu_Unify_equivalent n t u acc initial result Hacyc Hsub Hinput Hresult) as Hequiv.
  split.
  - intro E. destruct result as [answer|]; [|reflexivity].
    pose proof (O.Unify_acyclic _ _ _ _ Hacyc Hresult) as Hacout.
    pose proof (ScopedUnification.Unify_closed n _ _ _ _ (erase_closed n t)
      (erase_closed n u) Hsub Hresult) as Hclout.
    destruct (acyclic_closed_has_model n answer Hacout Hclout) as [rho Hrho].
    apply (Hequiv rho) in Hrho. rewrite E in Hrho. contradiction.
  - intro E. subst result. destruct (I.amgu n t u acc) as [out|] eqn:Eout; [|reflexivity].
    destruct (indexed_models_inhabited n out) as [rho Hrho].
    apply indexed_models_extend in Hrho.
    pose proof (proj2 (Hequiv (extend rho))) as H.
    specialize (H Hrho). contradiction.
Qed.

Theorem mgu_Unify_failure : forall n (t u : I.Term n) result,
  O.Unify (erase t) (erase u) [] result ->
  (I.mgu t u = None <-> result = None).
Proof.
  intros n t u result Hresult.
  apply (amgu_Unify_failure n t u (existT _ n I.anil) [] result empty_acyclic I).
  - intro rho. split; [intros _; apply C.models_nil|intros _; apply D.satisfies_sub_nil].
  - exact Hresult.
Qed.

(** The legacy outcome is unique syntactically. The indexed result agrees
    on failure and on every represented ground valuation, without equating
    representations or identifying equivalent MGUs as literal binding lists. *)
Theorem structural_Unify_equivalence : forall n (t u : I.Term n),
  exists! result,
    O.Unify (erase t) (erase u) [] result /\
    (I.mgu t u = None <-> result = None) /\
    forall rho, old_result_models rho result <-> C.result_models (restrict rho) (I.mgu t u).
Proof.
  intros n t u.
  destruct (mgu_has_equivalent_Unify_result n t u) as [result [Hresult Hequiv]].
  exists result. split.
  - split; [exact Hresult|]. split; [apply mgu_Unify_failure; exact Hresult|exact Hequiv].
  - intros other [Hother _]. eapply O.Unify_functional; eassumption.
Qed.

Corollary mgu_failure_iff_Unify_failure : forall n (t u : I.Term n),
  I.mgu t u = None <-> O.Unify (erase t) (erase u) [] None.
Proof.
  intros n t u. split.
  - intro E. destruct (mgu_has_equivalent_Unify_result n t u) as [result [Hresult _]].
    apply (proj1 (mgu_Unify_failure n t u result Hresult)) in E. subst result. exact Hresult.
  - intro Hresult. apply (proj2 (mgu_Unify_failure n t u None Hresult)). reflexivity.
Qed.

Corollary mgu_success_iff_Unify_success : forall n (t u : I.Term n),
  (exists acc, I.mgu t u = Some acc) <->
  exists answer, O.Unify (erase t) (erase u) [] (Some answer).
Proof.
  intros n t u. split.
  - intros [acc E]. destruct (mgu_has_equivalent_Unify_result n t u) as [[answer|] [Hresult _]].
    + exists answer. exact Hresult.
    + pose proof (proj2 (mgu_Unify_failure n t u None Hresult) eq_refl) as Hnone.
      rewrite E in Hnone. discriminate.
  - intros [answer Hresult]. destruct (I.mgu t u) as [acc|] eqn:E; [exists acc; reflexivity|].
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
  - exists I.f0. reflexivity.
  - destruct (IHn k ltac:(lia)) as [x Hx]. rewrite Hx. eexists. reflexivity.
Qed.

(** Proof-side conversion of valid legacy runtime syntax; parameters are
    deliberately rejected. The live execution interface is unchanged. *)
Fixpoint index_term (n : nat) (t : T.term) : option (I.Term n) :=
  match t with
  | T.tvar k => match fin_index n k with None => None | Some x => Some (I.var x) end
  | T.tpar _ => None
  | T.tsym s => Some (I.atom (I.symbol s))
  | T.tstr s => Some (I.atom (I.text s))
  | T.tnat k => Some (I.atom (I.number k))
  | T.tbool b => Some (I.atom (I.boolean b))
  | T.tnil => Some I.leaf
  | T.tcons a b => match index_term n a, index_term n b with
      | Some a', Some b' => Some (I.fork a' b') | _, _ => None end
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
  W.closed_term 0 n t -> exists indexed, index_term n t = Some indexed.
Proof.
  induction t; intros bound H; simpl in *; try (eexists; reflexivity).
  - destruct (fin_index_complete bound n H) as [x Hx]. rewrite Hx. eexists. reflexivity.
  - lia.
  - destruct H as [Ha Hb]. destruct (IHt1 bound Ha) as [a Ea], (IHt2 bound Hb) as [b Eb].
    rewrite Ea,Eb. eexists. reflexivity.
Qed.

Theorem valid_terms_structural_equivalence : forall n t u,
  W.closed_term 0 n t -> W.closed_term 0 n u ->
  exists indexed_t indexed_u,
    index_term n t = Some indexed_t /\ index_term n u = Some indexed_u /\
    exists! result,
      O.Unify t u [] result /\
      (I.mgu indexed_t indexed_u = None <-> result = None) /\
      forall rho, old_result_models rho result <->
        C.result_models (restrict rho) (I.mgu indexed_t indexed_u).
Proof.
  intros n t u Ht Hu.
  destruct (index_term_complete t n Ht) as [it Hit], (index_term_complete u n Hu) as [iu Hiu].
  exists it,iu. split; [exact Hit|]. split; [exact Hiu|].
  rewrite <- (index_term_sound t n it Hit), <- (index_term_sound u n iu Hiu).
  apply structural_Unify_equivalence.
Qed.
