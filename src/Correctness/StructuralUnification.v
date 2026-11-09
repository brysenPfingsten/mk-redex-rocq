From Stdlib Require Import Arith Lia.
From MkRedex.Execution Require Import StructuralUnifier.
From MkRedex.Denotational Require Import Denotation.
Set Default Goal Selector "!".

Definition rebuild {n} (v : option (Fin n)) : Fin (S n) :=
  match v with None => f0 | Some x => fs x end.

Lemma fin_eta : forall n (x : Fin n),
  match n as k return Fin k -> Prop with
  | 0 => fun _ => True
  | S k => fun x => rebuild (fin_view x) = x
  end x.
Proof. intros n x. destruct x; reflexivity. Qed.

Ltac split_fin x :=
  let H := fresh "Hview" in
  pose proof (fin_eta _ x) as H;
  change (rebuild (fin_view x) = x) in H;
  destruct (fin_view x); simpl in H; subst x.

Lemma thick_thin : forall n (x : Fin (S n)) y,
  thick n x (thin n x y) = Some y.
Proof.
  induction n; intros x y.
  - exact (fin0_elim y).
  - split_fin x; split_fin y; simpl; try reflexivity.
    rewrite IHn. reflexivity.
Qed.

Lemma thick_same : forall n (x : Fin (S n)), thick n x x = None.
Proof.
  induction n; intro x; [reflexivity|].
  split_fin x; simpl; [rewrite IHn|]; reflexivity.
Qed.

Lemma thick_view : forall n (x y : Fin (S n)),
  match thick n x y with None => y=x | Some z => y=thin n x z end.
Proof.
  induction n; intros x y.
  - split_fin x; [exact (fin0_elim f)|].
    split_fin y; [exact (fin0_elim f)|reflexivity].
  - split_fin x; split_fin y; simpl; try reflexivity.
    match goal with |- context [thick n ?a ?b] =>
      pose proof (IHn a b) as H; destruct (thick n a b); simpl in *; congruence end.
Qed.

Definition value (a : Rigid) : ground :=
  match a with
  | symbol s => gsym s | text s => gstr s | number n => gnat n
  | boolean b => gbool b | empty => gnil
  end.
Fixpoint eval {n} (rho : Fin n -> ground) (t : Term n) : ground :=
  match t with var x => rho x | atom a => value a
  | fork a b => gcons (eval rho a) (eval rho b) end.
Fixpoint size (v : ground) : nat :=
  match v with gcons a b => S (size a + size b) | _ => 1 end.

Lemma eval_ext : forall n (t : Term n) rho sigma,
  (forall x, rho x = sigma x) -> eval rho t = eval sigma t.
Proof.
  intros n t. induction t; intros rho sigma H; simpl.
  - apply H.
  - reflexivity.
  - rewrite (IHt1 rho sigma H), (IHt2 rho sigma H). reflexivity.
Qed.
Lemma eval_apply : forall m n (sigma : Sub m n) rho t,
  eval rho (apply sigma t) = eval (fun x => eval rho (sigma x)) t.
Proof.
  intros m n sigma rho t. induction t; simpl; try reflexivity.
  rewrite IHt1, IHt2. reflexivity.
Qed.
Lemma check_sound : forall n x (t : Term (S n)) r,
  check x t = Some r -> forall rho,
  eval rho t = eval (fun y => rho (thin n x y)) r.
Proof.
  intros n x t. induction t; intros out H rho; simpl in H.
  - pose proof (thick_view n x f) as Hv.
    destruct (thick n x f); [|discriminate]. inversion H; subst.
    simpl. congruence.
  - inversion H; reflexivity.
  - destruct (check x t1) eqn:Ea; [|discriminate].
    destruct (check x t2) eqn:Eb; [|discriminate]. inversion H; subst.
    simpl. rewrite (IHt1 _ eq_refl rho), (IHt2 _ eq_refl rho). reflexivity.
Qed.
Lemma check_failure_size : forall n x (t : Term (S n)),
  check x t = None -> forall rho, size (rho x) <= size (eval rho t).
Proof.
  intros n x t. induction t; intros H rho; simpl in *.
  - pose proof (thick_view n x f) as Hv.
    destruct (thick n x f); [discriminate|]. subst f. lia.
  - discriminate.
  - destruct (check x t1) eqn:Ea.
    + destruct (check x t2) eqn:Eb; [discriminate|].
      pose proof (IHt2 eq_refl rho). lia.
    + pose proof (IHt1 eq_refl rho). lia.
Qed.
Lemma check_failure_rigid : forall n x (t : Term (S n)),
  (forall y, t <> var y) -> check x t = None -> forall rho,
  eval rho t <> rho x.
Proof.
  intros n x t Hrig Hcheck rho. destruct t; simpl in *.
  - exfalso. apply (Hrig f). reflexivity.
  - discriminate.
  - destruct (check x t1) eqn:Ea.
    + destruct (check x t2) eqn:Eb; [discriminate|].
      pose proof (check_failure_size n x t2 Eb rho). intro E. rewrite <- E in H. simpl in H. lia.
    + pose proof (check_failure_size n x t1 Ea rho). intro E. rewrite <- E in H. simpl in H. lia.
Qed.

Definition models {m} (rho : Fin m -> ground) (acc : Acc m) : Prop :=
  match acc with existT _ n sigma =>
    exists gamma, forall x, eval gamma (sub sigma x) = rho x
  end.
Lemma models_nil : forall n rho, @models n rho (existT _ n anil).
Proof. intros n rho. exists rho. reflexivity. Qed.

Lemma eliminate_factor : forall n x (t : Term (S n)) r,
  check x t = Some r -> forall rho,
  (rho x = eval rho t <->
   exists gamma, forall y, eval gamma (for_ r x y) = rho y).
Proof.
  intros n x t r Hcheck rho. split.
  - intro Heq. exists (fun y => rho (thin n x y)). intro y.
    unfold for_. pose proof (thick_view n x y) as Hv.
    destruct (thick n x y); simpl.
    + f_equal. symmetry. exact Hv.
    + subst y. rewrite <- (check_sound n x t r Hcheck rho). symmetry. exact Heq.
  - intros [gamma Hgamma].
    rewrite <- (Hgamma x). unfold for_ at 1. rewrite thick_same.
    rewrite (check_sound n x t r Hcheck rho). simpl.
    apply eval_ext. intro y. specialize (Hgamma (thin n x y)).
    unfold for_ in Hgamma. rewrite thick_thin in Hgamma. simpl in Hgamma. exact Hgamma.
Qed.

Lemma models_snoc : forall m n (sigma : AList m n) r z rho,
  models rho (existT _ n (asnoc sigma r z)) <->
  exists gamma, models gamma (existT _ n sigma) /\
    forall x, eval gamma (for_ r z x) = rho x.
Proof.
  intros m n sigma r z rho. split.
  - intros [eta Heta]. exists (fun y => eval eta (sub sigma y)). split.
    + exists eta. reflexivity.
    + intro x. specialize (Heta x).
      change (eval eta (apply (sub sigma) (for_ r z x)) = rho x) in Heta.
      rewrite eval_apply in Heta. exact Heta.
  - intros [gamma [[eta Heta] Hgamma]]. exists eta. intro x.
    change (eval eta (apply (sub sigma) (for_ r z x)) = rho x).
    rewrite eval_apply. rewrite <- (Hgamma x). apply eval_ext. exact Heta.
Qed.

Definition restore {m} (v : AccView m) : Acc (S m) :=
  match v with no_binding => existT _ (S m) anil
  | has_binding n sigma r z => existT _ n (asnoc sigma r z) end.
Lemma acc_eta : forall m (acc : Acc (S m)), restore (acc_view acc) = acc.
Proof.
  assert (H : forall i j (sigma : AList i j),
    match i as k return AList k j -> Prop with
    | 0 => fun _ => True
    | S k => fun sigma => restore (acc_view (existT _ j sigma)) = existT _ j sigma
    end sigma).
  { intros i j sigma. destruct sigma; [destruct n|]; reflexivity. }
  intros m [n sigma]. exact (H (S m) n sigma).
Qed.

Definition correct {m} (s t : Term m) (acc : Acc m) (result : option (Acc m)) : Prop :=
  forall rho, match result with
  | None => ~ (models rho acc /\ eval rho s = eval rho t)
  | Some out => models rho out <-> models rho acc /\ eval rho s = eval rho t
  end.

Lemma models_single : forall n x (t : Term (S n)) r,
  check x t = Some r -> forall rho,
  models rho (existT _ n (asnoc anil r x)) <-> rho x = eval rho t.
Proof.
  intros n x t r Hcheck rho. rewrite models_snoc.
  rewrite (eliminate_factor n x t r Hcheck rho). split.
  - intros [gamma [_ H]]. exists gamma. exact H.
  - intros [gamma H]. exists gamma. split; [apply models_nil|exact H].
Qed.
Lemma flexFlex_models : forall n (x y : Fin (S n)) rho,
  models rho (flexFlex x y) <-> rho x = rho y.
Proof.
  intros n x y rho. unfold flexFlex. pose proof (thick_view n x y) as Hv.
  destruct (thick n x y) as [z|] eqn:E.
  - apply (models_single n x (var y) (var z)). simpl. rewrite E. reflexivity.
  - subst y. split; [reflexivity|intro H; apply models_nil].
Qed.
Lemma correct_sym : forall n (s t : Term n) acc result,
  correct s t acc result -> correct t s acc result.
Proof.
  intros n s t acc [out|] H rho; specialize (H rho); simpl in *;
    assert (E : eval rho s = eval rho t <-> eval rho t = eval rho s)
      by (split; intro E; symmetry; exact E); tauto.
Qed.

Lemma flex_correct : forall m recurse,
  (forall s t acc, correct s t acc (recurse s t acc)) ->
  forall x t acc, correct (var x) t acc (flex m recurse x t acc).
Proof.
  intros m recurse Hrec x t acc.
  pose proof (acc_eta m acc) as Heta.
  unfold flex. destruct (acc_view acc) as [|n sigma r z] eqn:Eview;
    simpl in Heta; subst acc.
  - destruct t as [y|a|a b].
    + intro rho. simpl. rewrite flexFlex_models. split.
      * intro H. split; [apply models_nil|exact H].
      * tauto.
    + unfold flexRigid. destruct (check x (atom a)) as [u|] eqn:E.
      * intro rho. rewrite (models_single m x (atom a) u E rho).
        split; [intro H; split; [apply models_nil|exact H]|tauto].
      * discriminate.
    + unfold flexRigid. destruct (check x (fork a b)) as [u|] eqn:E.
      * intro rho. rewrite (models_single m x (fork a b) u E rho).
        split; [intro H; split; [apply models_nil|exact H]|tauto].
      * intros rho [_ Heq]. symmetry in Heq.
        exact (check_failure_rigid m x (fork a b) ltac:(intros; discriminate) E rho Heq).
  - set (left := apply (for_ r z) (var x)).
    set (right := apply (for_ r z) t).
    specialize (Hrec left right (existT _ n sigma)).
    destruct (recurse left right (existT _ n sigma)) as [[p tau]|] eqn:E.
    + intro rho. rewrite !models_snoc. split.
      * intros [gamma [Htau Hgamma]].
        apply (Hrec gamma) in Htau as [Hsigma Heq]. split.
        -- exists gamma. split; assumption.
        -- unfold left,right in Heq. rewrite !eval_apply in Heq.
           simpl in Heq. change (rho x = eval rho t). rewrite <- (Hgamma x).
           rewrite <- (eval_ext _ t _ rho Hgamma). exact Heq.
      * intros [[gamma [Hsigma Hgamma]] Heq]. exists gamma. split; [|exact Hgamma].
        apply (Hrec gamma). split; [exact Hsigma|].
        unfold left,right. rewrite !eval_apply. simpl.
        rewrite (Hgamma x), (eval_ext _ t _ rho Hgamma). exact Heq.
    + intros rho [Hmodel Heq]. apply models_snoc in Hmodel.
      destruct Hmodel as [gamma [Hsigma Hgamma]]. apply (Hrec gamma). split; [exact Hsigma|].
      unfold left,right. rewrite !eval_apply. simpl.
      rewrite (Hgamma x), (eval_ext _ t _ rho Hgamma). exact Heq.
Qed.

Lemma value_injective : forall a b, value a = value b -> a=b.
Proof. intros a b. destruct a; destruct b; simpl; intro H; inversion H; reflexivity. Qed.
Lemma ground_cons_eq : forall a b c d,
  gcons a b = gcons c d <-> a=c /\ b=d.
Proof. intros a b c d. split; [intro H; inversion H; tauto|intros [-> ->]; reflexivity]. Qed.

Lemma pair_correct : forall m (a b c d : Term m) acc first second,
  correct a c acc first ->
  (forall next, correct b d next (second next)) ->
  correct (fork a b) (fork c d) acc
    (match first with None => None | Some next => second next end).
Proof.
  intros m a b c d acc [next|] second Hfirst Hsecond.
  - specialize (Hsecond next). destruct (second next) as [out|]; intro rho;
      specialize (Hfirst rho); specialize (Hsecond rho); simpl in *;
      rewrite ground_cons_eq; tauto.
  - intros rho [Hmodel Heq]. apply (Hfirst rho). split; [exact Hmodel|].
    injection Heq. tauto.
Qed.

Theorem amgu_correct : forall m (s t : Term m) acc,
  correct s t acc (amgu m s t acc).
Proof.
  induction m as [|m IHm].
  - intro s. induction s as [x|a|a IHa b IHb]; intros t acc.
    + exact (fin0_elim x).
    + destruct t as [y|b|c d]; [exact (fin0_elim y)| |].
      * cbn [amgu]. destruct (rigid_eq_dec a b) as [->|Hneq].
        -- intro rho. simpl. split; [intro H; split; [exact H|reflexivity]|tauto].
        -- intros rho [_ Heq]. apply Hneq. apply value_injective. exact Heq.
      * intros rho [_ Heq]. destruct a; discriminate Heq.
    + destruct t as [y|c|c d].
      * exact (fin0_elim y).
      * intros rho [_ Heq]. destruct c; discriminate Heq.
      * change (correct (fork a b) (fork c d) acc
          (match amgu 0 a c acc with None => None | Some next => amgu 0 b d next end)).
        apply pair_correct; [apply IHa|intro next; apply IHb].
  - intro s. induction s as [x|a|a IHa b IHb]; intros t acc.
    + change (correct (var x) t acc (flex m (amgu m) x t acc)).
      apply flex_correct. exact IHm.
    + destruct t as [y|b|c d].
      * apply correct_sym. change (correct (var y) (atom a) acc (flex m (amgu m) y (atom a) acc)).
        apply flex_correct. exact IHm.
      * cbn [amgu]. destruct (rigid_eq_dec a b) as [->|Hneq].
        -- intro rho. simpl. split; [intro H; split; [exact H|reflexivity]|tauto].
        -- intros rho [_ Heq]. apply Hneq. apply value_injective. exact Heq.
      * intros rho [_ Heq]. destruct a; discriminate Heq.
    + destruct t as [y|c|c d].
      * apply correct_sym. change (correct (var y) (fork a b) acc (flex m (amgu m) y (fork a b) acc)).
        apply flex_correct. exact IHm.
      * intros rho [_ Heq]. destruct c; discriminate Heq.
      * change (correct (fork a b) (fork c d) acc
          (match amgu (S m) a c acc with None => None | Some next => amgu (S m) b d next end)).
        apply pair_correct; [apply IHa|intro next; apply IHb].
Qed.

Definition result_models {m} (rho : Fin m -> ground) (result : option (Acc m)) : Prop :=
  match result with None => False | Some acc => models rho acc end.

Theorem mgu_correct : forall m (s t : Term m) rho,
  result_models rho (mgu s t) <-> eval rho s = eval rho t.
Proof.
  intros m s t rho. pose proof (amgu_correct m s t (existT _ m anil) rho) as H.
  unfold mgu. destruct (amgu m s t (existT _ m anil)); simpl in *;
    pose proof (models_nil m rho); tauto.
Qed.

Theorem amgu_result_models : forall m (s t : Term m) acc rho,
  result_models rho (amgu m s t acc) <-> models rho acc /\ eval rho s = eval rho t.
Proof.
  intros m s t acc rho. pose proof (amgu_correct m s t acc rho) as H.
  destruct (amgu m s t acc); simpl in *; tauto.
Qed.
