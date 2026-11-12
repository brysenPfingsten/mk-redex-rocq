From Stdlib Require Import List Arith Lia.
From MkRedex.Correctness Require Import StructuralUnificationBridge.
Import ListNotations.
Set Default Goal Selector "!".

(** Restore original variable IDs after each scope reduction. The map is
    restricted through [thin], never reset to the new consecutive indices. *)
Fixpoint erase_with {n} (names : StructuralUnifier.Fin n -> nat) (t : StructuralUnifier.Term n) : Terms.term :=
  match t with
  | StructuralUnifier.var x => Terms.tvar (names x)
  | StructuralUnifier.atom a => erase_rigid a
  | StructuralUnifier.fork a b => Terms.tcons (erase_with names a) (erase_with names b)
  end.

Fixpoint decode {m n} (sigma : StructuralUnifier.AList m n) : (StructuralUnifier.Fin m -> nat) -> Substitution.sub :=
  match sigma in StructuralUnifier.AList i j return (StructuralUnifier.Fin i -> nat) -> Substitution.sub with
  | StructuralUnifier.anil => fun _ => []
  | @StructuralUnifier.asnoc i j tail t x => fun names =>
      let rest := fun y => names (StructuralUnifier.thin i x y) in
      decode tail rest ++ [(names x, erase_with rest t)]
  end.

Definition decode_acc {m} (acc : StructuralUnifier.Acc m) : Substitution.sub :=
  match acc with existT _ n sigma => decode sigma (@fin_nat m) end.

Lemma eval_erase_with : forall n (t : StructuralUnifier.Term n) names rho,
  Denotation.eval_term rho [] (erase_with names t) =
  Some (StructuralUnification.eval (fun x => rho (names x)) t).
Proof.
  intros n t. induction t; intros names rho; simpl.
  - reflexivity.
  - destruct r; reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma thin_injective : forall n x (a b : StructuralUnifier.Fin n),
  StructuralUnifier.thin n x a = StructuralUnifier.thin n x b -> a = b.
Proof.
  intros n x a b E.
  apply (f_equal (StructuralUnifier.thick n x)) in E.
  rewrite !StructuralUnification.thick_thin in E. congruence.
Qed.

Lemma thin_not_removed : forall n x (y : StructuralUnifier.Fin n), StructuralUnifier.thin n x y <> x.
Proof.
  intros n x y E. apply (f_equal (StructuralUnifier.thick n x)) in E.
  rewrite StructuralUnification.thick_thin, StructuralUnification.thick_same in E. discriminate.
Qed.

Definition injective {n} (names : StructuralUnifier.Fin n -> nat) :=
  forall x y, names x = names y -> x = y.

Lemma restrict_injective : forall n names x,
  @injective (S n) names ->
  injective (fun y => names (StructuralUnifier.thin n x y)).
Proof.
  intros n names x H a b E. apply (thin_injective n x).
  apply H. exact E.
Qed.

Lemma decode_keys : forall m n (sigma : StructuralUnifier.AList m n) names k t,
  In (k,t) (decode sigma names) -> exists x, k = names x.
Proof.
  intros m n sigma. induction sigma; intros names k u H; simpl in H.
  - contradiction.
  - apply in_app_or in H. destruct H as [H|[H|H]].
    + destruct (IHsigma _ _ _ H) as [y E].
      exists (StructuralUnifier.thin m f y). exact E.
    + inversion H; subst. exists f. reflexivity.
    + contradiction.
Qed.

Lemma decode_nodup : forall m n (sigma : StructuralUnifier.AList m n) names,
  injective names -> NoDup (map fst (decode sigma names)).
Proof.
  intros m n sigma. induction sigma; intros names Hnames; simpl.
  - constructor.
  - rewrite map_app. apply NoDup_app.
    + apply IHsigma. apply restrict_injective. exact Hnames.
    + constructor; [simpl; tauto|constructor].
    + intros k Hin Hlast. simpl in Hlast.
    destruct Hlast as [<-|[]].
    apply in_map_iff in Hin. destruct Hin as [[k u] [E Hin]]. simpl in E. subst k.
    destruct (decode_keys _ _ sigma _ _ _ Hin) as [y E].
    apply Hnames in E. exact (thin_not_removed m f y (eq_sym E)).
Qed.

(** With no shadowed keys, visible lookup constraints are exactly the
    conjunction of the equations written in the binding list. *)
Lemma lookup_equations : forall bindings rho,
  NoDup (map fst bindings) ->
  (Denotation.satisfies_sub rho bindings <->
   Forall (fun p => Denotation.eval_term rho [] (snd p) = Some (rho (fst p))) bindings).
Proof.
  induction bindings as [|[k t] rest IH]; intros rho Hnd; simpl in *.
  - split.
    + intro H. exact (Forall_nil _).
    + intro H. apply Denotation.satisfies_sub_nil.
  - inversion Hnd as [|? ? Hnot Htail]; subst.
    rewrite Forall_cons_iff. rewrite <- (IH rho Htail).
    split.
    + intro H. split.
      * apply (H k t). simpl. rewrite Nat.eqb_refl. reflexivity.
      * intros x u Hu. apply (H x u). simpl.
        destruct (Nat.eqb x k) eqn:E; [|exact Hu].
        apply Nat.eqb_eq in E. subst x. exfalso. apply Hnot.
        apply in_map_iff. exists (k,u). split; [reflexivity|].
        clear -Hu. induction rest as [|[j v] rest IH]; simpl in Hu.
        -- discriminate.
        -- destruct (Nat.eqb k j) eqn:E.
           ++ apply Nat.eqb_eq in E. inversion Hu; subst. left. reflexivity.
           ++ right. apply IH. exact Hu.
    + intros [Ht Hrest] x u Hu. simpl in Hu.
      destruct (Nat.eqb x k) eqn:E.
      * apply Nat.eqb_eq in E. inversion Hu; subst. exact Ht.
      * apply Hrest. exact Hu.
Qed.

Lemma models_snoc_equations : forall m n (sigma : StructuralUnifier.AList m n) t x rho,
  StructuralUnification.models rho (existT _ n (StructuralUnifier.asnoc sigma t x)) <->
  StructuralUnification.models (fun y => rho (StructuralUnifier.thin m x y)) (existT _ n sigma) /\
  StructuralUnification.eval (fun y => rho (StructuralUnifier.thin m x y)) t = rho x.
Proof.
  intros m n sigma t x rho. rewrite StructuralUnification.models_snoc. split.
  - intros [gamma [Hmodel Hgamma]].
    assert (E : forall y, gamma y = rho (StructuralUnifier.thin m x y)).
    { intro y. specialize (Hgamma (StructuralUnifier.thin m x y)).
      unfold StructuralUnifier.for_ in Hgamma. rewrite StructuralUnification.thick_thin in Hgamma. exact Hgamma. }
    split.
    + destruct Hmodel as [eta Heta]. exists eta. intro y. rewrite <- E. apply Heta.
    + specialize (Hgamma x). unfold StructuralUnifier.for_ in Hgamma.
      rewrite StructuralUnification.thick_same in Hgamma. simpl in Hgamma.
      rewrite <- Hgamma. apply StructuralUnification.eval_ext. intro y. symmetry. apply E.
  - intros [Hmodel Heq]. exists (fun y => rho (StructuralUnifier.thin m x y)).
    split; [exact Hmodel|]. intro y. unfold StructuralUnifier.for_.
    pose proof (StructuralUnification.thick_view m x y) as Hv.
    destruct (StructuralUnifier.thick m x y); simpl.
    + rewrite Hv. reflexivity.
    + subst y. exact Heq.
Qed.

Theorem decode_models : forall m n (sigma : StructuralUnifier.AList m n) names rho,
  injective names ->
  (Denotation.satisfies_sub rho (decode sigma names) <->
   StructuralUnification.models (fun x => rho (names x)) (existT _ n sigma)).
Proof.
  intros m n sigma. induction sigma; intros names rho Hnames.
  - split; [intro H; apply StructuralUnification.models_nil|intro H; apply Denotation.satisfies_sub_nil].
  - rewrite (lookup_equations _ rho (decode_nodup _ _ _ _ Hnames)).
    cbn [decode]. rewrite Forall_app, Forall_cons_iff.
    rewrite <- (lookup_equations _ rho
      (decode_nodup _ _ sigma _ (restrict_injective _ _ f Hnames))).
    rewrite (IHsigma _ rho (restrict_injective _ _ f Hnames)).
    cbn [fst snd].
    rewrite eval_erase_with, models_snoc_equations.
    split.
    + intros [H [E _]]. split; [exact H|congruence].
    + intros [H E]. split; [exact H|]. split; [congruence|constructor].
Qed.

Lemma fin_nat_injective : forall n, @injective n (@fin_nat n).
Proof.
  intros n x. induction x; intros y E.
  - StructuralUnification.split_fin y; simpl in E; [discriminate|reflexivity].
  - StructuralUnification.split_fin y; simpl in E; [|discriminate].
    f_equal. apply IHx. congruence.
Qed.

Corollary decode_acc_models : forall m (acc : StructuralUnifier.Acc m) rho,
  Denotation.satisfies_sub rho (decode_acc acc) <-> StructuralUnification.models (restrict rho) acc.
Proof.
  intros m [n sigma] rho. apply decode_models. apply fin_nat_injective.
Qed.

Definition decode_result {m} (result : option (StructuralUnifier.Acc m)) : option Substitution.sub :=
  option_map decode_acc result.

Theorem decode_result_models : forall m (result : option (StructuralUnifier.Acc m)) rho,
  old_result_models rho (decode_result result) <->
  StructuralUnification.result_models (restrict rho) result.
Proof.
  intros m [acc|] rho; [apply decode_acc_models|reflexivity].
Qed.

Corollary decoded_amgu_equivalent : forall n (t u : StructuralUnifier.Term n) acc initial result,
  Substitution.acyclic_sub initial -> Scoping.closed_sub n initial ->
  (forall rho, Denotation.satisfies_sub rho initial <-> StructuralUnification.models (restrict rho) acc) ->
  MkRedex.Language.Unification.Unify (erase t) (erase u) initial result -> forall rho,
  old_result_models rho (decode_result (StructuralUnifier.amgu n t u acc)) <->
  old_result_models rho result.
Proof.
  intros n t u acc initial result Ha Hc Hinput Hresult rho.
  rewrite decode_result_models. symmetry.
  eapply amgu_Unify_equivalent; eassumption.
Qed.

(** Encode visible runtime bindings as equations. Enumerating the allocated
    IDs uses [lookup], so shadowed entries do not become extra constraints.
    This traversal is structural on [keys], not a unification fuel bound. *)
Fixpoint encode_keys (bound : nat) (keys : list nat) (initial : Substitution.sub)
  (acc : StructuralUnifier.Acc bound) : option (StructuralUnifier.Acc bound) :=
  match keys with
  | [] => Some acc
  | k :: rest =>
      match Substitution.lookup k initial with
      | None => encode_keys bound rest initial acc
      | Some t =>
          match fin_index bound k, index_term bound t with
          | Some x, Some v =>
              match StructuralUnifier.amgu bound (StructuralUnifier.var x) v acc with
              | None => None
              | Some next => encode_keys bound rest initial next
              end
          | _, _ => None
          end
      end
  end.

Definition encode_sub (bound : nat) (initial : Substitution.sub) : option (StructuralUnifier.Acc bound) :=
  encode_keys bound (seq 0 bound) initial (existT _ bound StructuralUnifier.anil).

Lemma encode_keys_models : forall keys bound initial acc rho,
  Forall (fun k => k < bound) keys -> Scoping.closed_sub bound initial ->
  (StructuralUnification.result_models (restrict rho) (encode_keys bound keys initial acc) <->
   StructuralUnification.models (restrict rho) acc /\
   Forall (fun k => forall t, Substitution.lookup k initial = Some t ->
     Denotation.eval_term rho [] t = Some (rho k)) keys).
Proof.
  induction keys as [|k keys IH]; intros bound initial acc rho Hkeys Hclosed.
  - cbn [encode_keys StructuralUnification.result_models]. split.
    + intro H. split; [exact H|constructor].
    + intros [H _]. exact H.
  - inversion Hkeys as [|? ? Hk Hrest]; subst.
    cbn [encode_keys]. rewrite Forall_cons_iff.
    destruct (Substitution.lookup k initial) as [t|] eqn:Et.
    + destruct (GroundUnification.lookup_closed_binding bound initial k t Hclosed Et) as [_ Ht].
      destruct (fin_index_complete bound k Hk) as [x Ex].
      destruct (index_term_complete t bound Ht) as [v Ev]. rewrite Ex, Ev.
      assert (Heval : Denotation.eval_term rho [] t = Some (StructuralUnification.eval (restrict rho) v)).
      { rewrite <- (index_term_sound t bound v Ev). apply eval_erase. }
      assert (Hx : fin_nat x = k) by (apply fin_index_sound; exact Ex).
      pose proof (StructuralUnification.amgu_result_models bound (StructuralUnifier.var x) v acc (restrict rho)) as Hstep.
      change (StructuralUnification.result_models (restrict rho) (StructuralUnifier.amgu bound (StructuralUnifier.var x) v acc) <->
        StructuralUnification.models (restrict rho) acc /\ rho (fin_nat x) = StructuralUnification.eval (restrict rho) v) in Hstep.
      rewrite Hx in Hstep.
      destruct (StructuralUnifier.amgu bound (StructuralUnifier.var x) v acc) as [next|] eqn:E.
      * rewrite (IH bound initial next rho Hrest Hclosed).
        cbn [StructuralUnification.result_models] in Hstep. split.
        -- intros [Hnext Htail]. apply Hstep in Hnext. destruct Hnext as [Hacc Heq].
           split; [exact Hacc|]. split; [|exact Htail].
           intros u Eu. injection Eu as <-. congruence.
        -- intros [Hacc [Hhead Htail]]. split; [|exact Htail]. apply Hstep.
           split; [exact Hacc|]. specialize (Hhead t eq_refl). congruence.
      * cbn [StructuralUnification.result_models] in *. split; [contradiction|].
        intros [Hacc [Hhead Htail]]. apply (proj2 Hstep).
        split; [exact Hacc|]. specialize (Hhead t eq_refl). congruence.
    + rewrite (IH bound initial acc rho Hrest Hclosed). split.
      * intros [Hacc Htail]. split; [exact Hacc|]. split; [|exact Htail].
        intros t E. discriminate.
      * intros [Hacc [_ Htail]]. split; assumption.
Qed.

Theorem encode_sub_models : forall bound initial rho,
  Scoping.closed_sub bound initial ->
  (StructuralUnification.result_models (restrict rho) (encode_sub bound initial) <->
   Denotation.satisfies_sub rho initial).
Proof.
  intros bound initial rho Hclosed. unfold encode_sub.
  rewrite encode_keys_models.
  - split.
    + intros [_ H]. rewrite Forall_forall in H. intros k t Et. apply (H k).
      * apply in_seq. pose proof (GroundUnification.lookup_closed_binding bound initial k t Hclosed Et).
        lia.
      * exact Et.
    + intro H. split; [apply StructuralUnification.models_nil|]. apply Forall_forall.
      intros k _. intros t Et. apply H. exact Et.
  - apply Forall_forall. intros k H. apply in_seq in H. lia.
  - exact Hclosed.
Qed.

Theorem encode_sub_success : forall bound initial,
  Substitution.acyclic_sub initial -> Scoping.closed_sub bound initial ->
  exists acc, encode_sub bound initial = Some acc.
Proof.
  intros bound initial Ha Hc.
  destruct (acyclic_closed_has_model bound initial Ha Hc) as [rho Hrho].
  pose proof (proj2 (encode_sub_models bound initial rho Hc) Hrho) as H.
  destruct (encode_sub bound initial) as [acc|]; [eauto|contradiction].
Qed.

Definition solve_state (bound : nat) (initial : Substitution.sub) (t u : Terms.term)
  : option (option Substitution.sub) :=
  match encode_sub bound initial, index_term bound t, index_term bound u with
  | Some acc, Some s, Some v => Some (decode_result (StructuralUnifier.amgu bound s v acc))
  | _, _, _ => None
  end.

Theorem solve_state_valid : forall bound initial t u,
  Substitution.acyclic_sub initial -> Scoping.closed_sub bound initial ->
  Scoping.closed_term 0 bound t -> Scoping.closed_term 0 bound u ->
  exists result,
    solve_state bound initial t u = Some result /\
    (forall legacy, MkRedex.Language.Unification.Unify t u initial legacy ->
      (result = None <-> legacy = None) /\
      forall rho, old_result_models rho result <-> old_result_models rho legacy).
Proof.
  intros bound initial t u Ha Hc Ht Hu.
  destruct (encode_sub_success bound initial Ha Hc) as [acc Ea].
  destruct (index_term_complete t bound Ht) as [s Es].
  destruct (index_term_complete u bound Hu) as [v Ev].
  assert (Hinput : forall rho,
    Denotation.satisfies_sub rho initial <-> StructuralUnification.models (restrict rho) acc).
  { intro rho. pose proof (encode_sub_models bound initial rho Hc) as H.
    rewrite Ea in H. symmetry. exact H. }
  exists (decode_result (StructuralUnifier.amgu bound s v acc)). split.
  - unfold solve_state. rewrite Ea, Es, Ev. reflexivity.
  - intros legacy Hlegacy.
    rewrite <- (index_term_sound t bound s Es), <- (index_term_sound u bound v Ev) in Hlegacy.
    split.
    + rewrite <- (amgu_Unify_failure bound s v acc initial legacy Ha Hc Hinput Hlegacy).
      unfold decode_result. destruct (StructuralUnifier.amgu bound s v acc); simpl; split; congruence.
    + intro rho. eapply decoded_amgu_equivalent; eassumption.
Qed.
