From MkRedex.Operational Require Import DelayTracking Scheduling Reduction Delay DelayFairness.
From Stdlib Require Import List Arith.
From MkRedex.Language Require Import Goals Substitution Trees Environments.
From MkRedex.Correctness Require Import Focus.
Import ListNotations.
Set Default Goal Selector "!".

Fixpoint ctx_goals (E : ctx) : list goal :=
  match E with
  | chole => []
  | cconj E g => ctx_goals E ++ [g]
  | cdisjL E _ | cdisjR _ E => ctx_goals E
  end.

Lemma active_fill_context : forall m,
  active_mark m -> exists E,
    (forall work, fill_mark m work = plug E work) /\ ctx_goals E = marked_goals m.
Proof.
  induction m; simpl; intro H; try contradiction.
  - exists chole. split; reflexivity.
  - destruct (IHm H) as [E [He Hg]]. exists (cconj E g).
    split; [intro work; simpl; rewrite He; reflexivity|simpl; rewrite Hg; reflexivity].
  - destruct (IHm H) as [E [He Hg]]. exists (cdisjL E t).
    split; [intro work; simpl; rewrite He; reflexivity|exact Hg].
  - destruct (IHm H) as [E [He Hg]]. exists (cdisjR t E).
    split; [intro work; simpl; rewrite He; reflexivity|exact Hg].
Qed.

Fixpoint ctx_mark (E : ctx) (m : marked_tree) : marked_tree :=
  match E with
  | chole => m
  | cconj E g => mark_under_conj (ctx_mark E m) g
  | cdisjL E t => mark_disjL_left (ctx_mark E m) t
  | cdisjR t E => mark_disjR_right t (ctx_mark E m)
  end.
Lemma ctx_mark_fill : forall E m work,
  fill_mark (ctx_mark E m) work = plug E (fill_mark m work).
Proof. induction E; intros m work; simpl; congruence. Qed.
Lemma ctx_mark_goals : forall E m,
  marked_goals (ctx_mark E m) = marked_goals m ++ ctx_goals E.
Proof.
  induction E; intros m; simpl; try (rewrite app_nil_r; reflexivity);
    rewrite IHE; try reflexivity. rewrite app_assoc. reflexivity.
Qed.

Inductive hsteps (G : env) : tree -> tree -> Prop :=
| hs_refl : forall t, hsteps G t t
| hs_step : forall t E r r' u,
    t = plug E r -> Head G r r' -> hsteps G (plug E r') u -> hsteps G t u.
Lemma hsteps_trans : forall G a b c, hsteps G a b -> hsteps G b c -> hsteps G a c.
Proof. intros G a b c H. induction H; intro Htail; [exact Htail|]. eapply hs_step; [exact H|exact H0|apply IHhsteps; exact Htail]. Qed.
Lemma hsteps_lift : forall G a b E, hsteps G a b -> hsteps G (plug E a) (plug E b).
Proof.
  intros G a b outer H. induction H.
  - constructor.
  - subst t. eapply hs_step with (E := compose_ctx outer E).
    + rewrite plug_compose. reflexivity.
    + exact H0.
    + rewrite plug_compose. exact IHhsteps.
Qed.
Lemma hsteps_multi : forall G a b ans, hsteps G a b -> multi G (ans,a) (ans,b).
Proof.
  intros G a b ans H. induction H.
  - constructor.
  - subst t. eapply multi_step; [apply S_ctx; exact H0|exact IHhsteps].
Qed.

Inductive ready (s : state) : tree -> Prop :=
| ready_one : ready s (tgoal gsucc s)
| ready_left : forall t, ready s (tdisjL (tgoal gsucc s) t)
| ready_right : forall t, ready s (tdisjR t (tgoal gsucc s)).

Lemma ready_disj_left : forall G s t other,
  ready s t -> exists u, hsteps G (tdisjL t other) u /\ ready s u.
Proof.
  intros G s t other H. destruct H.
  - eexists. split; constructor.
  - eexists. split. { eapply hs_step with (E := chole); [reflexivity|apply H_assoc_ll|constructor]. } constructor.
  - eexists. split. { eapply hs_step with (E := chole); [reflexivity|apply H_assoc_lr|constructor]. } constructor.
Qed.
Lemma ready_disj_right : forall G s t other,
  ready s t -> exists u, hsteps G (tdisjR other t) u /\ ready s u.
Proof.
  intros G s t other H. destruct H.
  - eexists. split; constructor.
  - eexists. split. { eapply hs_step with (E := chole); [reflexivity|apply H_assoc_rl|constructor]. } constructor.
  - eexists. split. { eapply hs_step with (E := chole); [reflexivity|apply H_assoc_rr|constructor]. } constructor.
Qed.
Lemma ready_conj : forall G s t g,
  ready s t -> exists m,
    hsteps G (tconj t g) (fill_mark m (tgoal g s)) /\ marked_goals m = [].
Proof.
  intros G s t g H. destruct H.
  - exists (mark_here tfail). split; [|reflexivity].
    eapply hs_step with (E := chole); [reflexivity|apply H_succ_conj|constructor].
  - exists (mark_disjL_left (mark_here tfail) (tconj t g)). split; [|reflexivity].
    eapply hs_step with (E := chole); [reflexivity|apply H_left_ans_conj|].
    eapply hs_step with (E := cdisjL chole (tconj t g));
      [reflexivity|apply H_succ_conj|constructor].
  - exists (mark_disjR_right (tconj t g) (mark_here tfail)). split; [|reflexivity].
    eapply hs_step with (E := chole); [reflexivity|apply H_right_ans_conj|].
    eapply hs_step with (E := cdisjR (tconj t g) chole);
      [reflexivity|apply H_succ_conj|constructor].
Qed.

Theorem success_context : forall G E s,
  exists u, hsteps G (plug E (tgoal gsucc s)) u /\
    ((ctx_goals E = [] /\ ready s u) \/
     exists g gs m, ctx_goals E = g::gs /\
       u = fill_mark m (tgoal g s) /\ marked_goals m = gs).
Proof.
  intros G E. induction E; intro s; simpl.
  - exists (tgoal gsucc s). split; [constructor|left; split; [reflexivity|constructor]].
  - destruct (IHE s) as [u [Hrun [[Hnone Hready]|[g [gs [m [Hgoals [Hu Hm]]]]]]]].
    + destruct (ready_disj_left G s u t Hready) as [v [Htail Hv]].
      exists v. split.
      * eapply hsteps_trans; [apply (hsteps_lift G _ _ (cdisjL chole t) Hrun)|exact Htail].
      * left. split; assumption.
    + exists (tdisjL u t). split; [apply (hsteps_lift G _ _ (cdisjL chole t) Hrun)|].
      right. exists g,gs,(mark_disjL_left m t). split; [exact Hgoals|]. split; [simpl; rewrite Hu; reflexivity|exact Hm].
  - destruct (IHE s) as [u [Hrun [[Hnone Hready]|[g [gs [m [Hgoals [Hu Hm]]]]]]]].
    + destruct (ready_disj_right G s u t Hready) as [v [Htail Hv]].
      exists v. split.
      * eapply hsteps_trans; [apply (hsteps_lift G _ _ (cdisjR t chole) Hrun)|exact Htail].
      * left. split; assumption.
    + exists (tdisjR t u). split; [apply (hsteps_lift G _ _ (cdisjR t chole) Hrun)|].
      right. exists g,gs,(mark_disjR_right t m). split; [exact Hgoals|]. split; [simpl; rewrite Hu; reflexivity|exact Hm].
  - destruct (IHE s) as [u [Hrun [[Hnone Hready]|[h [gs [m [Hgoals [Hu Hm]]]]]]]].
    + destruct (ready_conj G s u g Hready) as [m [Htail Hm]].
      exists (fill_mark m (tgoal g s)). split.
      * eapply hsteps_trans; [apply (hsteps_lift G _ _ (cconj chole g) Hrun)|exact Htail].
      * right. exists g,[],m. rewrite Hnone. split; [reflexivity|]. split; [reflexivity|exact Hm].
    + exists (tconj u g). split; [apply (hsteps_lift G _ _ (cconj chole g) Hrun)|].
      right. exists h,(gs++[g]),(mark_under_conj m g).
      rewrite Hgoals. split; [reflexivity|]. split; simpl; [rewrite Hu|rewrite Hm]; reflexivity.
Qed.

Lemma ready_observed : forall G ans s t,
  ready s t -> exists e,
    multi G (ans,t) e /\ In s (observed_answers e).
Proof.
  intros G ans s t H. destruct H.
  - exists (ans,tgoal gsucc s). split; [constructor|]. unfold observed_answers; simpl.
    apply in_or_app. right. left. reflexivity.
  - exists (ans++[s],t). split; [eapply multi_step; [apply S_promoteL|constructor]|].
    unfold observed_answers; simpl. apply in_or_app. left. apply in_or_app. right. left. reflexivity.
  - exists (ans++[s],t). split; [eapply multi_step; [apply S_promoteR|constructor]|].
    unfold observed_answers; simpl. apply in_or_app. left. apply in_or_app. right. left. reflexivity.
Qed.
