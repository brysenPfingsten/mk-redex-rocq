From MkRedex.Language Require Import WellFormed WellFormedProperties Terms Goals.
From Stdlib Require Import List Arith Lia.
From MkRedex.Denotational Require Import Denotation.
Import ListNotations.
Set Default Goal Selector "!".

Lemma eval_term_no_parameters : forall t c rho beta,
  ok_term 0 c t -> eval_term rho beta t = eval_term rho [] t.
Proof.
  induction t; intros c rho beta H; simpl in *; try reflexivity; try lia.
  destruct H as [Ha Hb]. rewrite (IHt1 c rho beta Ha), (IHt2 c rho beta Hb).
  reflexivity.
Qed.

Lemma eval_terms_nth : forall rho beta args values i t,
  eval_terms rho beta args = Some values -> nth_error args i = Some t ->
  nth_error values i = eval_term rho beta t.
Proof.
  intros rho beta args. induction args as [|a args IH]; intros values i t H Hnth;
    simpl in H.
  - destruct i; discriminate Hnth.
  - destruct (eval_term rho beta a) eqn:Ea; [|discriminate].
    destruct (eval_terms rho beta args) eqn:Eargs; [|discriminate].
    inversion H; subst values. destruct i; simpl in *.
    + inversion Hnth; subst. symmetry. exact Ea.
    + eapply IH; [reflexivity | exact Hnth].
Qed.

Lemma eval_term_open : forall t rho c args values prefix beta,
  runtime_open_args c args -> eval_terms rho [] args = Some values ->
  eval_term rho (prefix ++ beta) (open_term (List.length prefix) args t) =
  eval_term rho (prefix ++ values ++ beta) t.
Proof.
  induction t; intros rho c args values prefix beta Hargs Heval; simpl;
    try reflexivity.
  - pose proof (eval_terms_length rho [] args values Heval) as Hlen.
    destruct (Nat.ltb_spec n (List.length prefix)) as [Hlt|Hge].
    + simpl. rewrite !nth_error_app1 by exact Hlt. reflexivity.
    + rewrite nth_error_app2 by lia.
      destruct (nth_error args (n - List.length prefix)) as [u|] eqn:E.
      * assert (Huc : ok_term 0 c u).
        { eapply Forall_forall; [exact Hargs|]. eapply nth_error_In. exact E. }
        rewrite (eval_term_no_parameters u c rho (prefix ++ beta) Huc).
        rewrite nth_error_app1.
        -- symmetry. eapply eval_terms_nth; eassumption.
        -- rewrite <- Hlen. apply nth_error_Some.
           intro Hnone. rewrite E in Hnone. discriminate.
      * apply nth_error_None in E. simpl.
        rewrite !nth_error_app2 by lia.
        f_equal. lia.
  - rewrite (IHt1 rho c args values prefix beta Hargs Heval),
      (IHt2 rho c args values prefix beta Hargs Heval). reflexivity.
Qed.

Lemma eval_terms_open : forall ts rho c args values prefix beta,
  runtime_open_args c args -> eval_terms rho [] args = Some values ->
  eval_terms rho (prefix ++ beta)
    (map (open_term (List.length prefix) args) ts) =
  eval_terms rho (prefix ++ values ++ beta) ts.
Proof.
  induction ts as [|t ts IH]; intros rho c args values prefix beta Ha He;
    simpl; [reflexivity|].
  rewrite (eval_term_open t rho c args values prefix beta Ha He),
    (IH rho c args values prefix beta Ha He). reflexivity.
Qed.

Theorem satisfies_open_goal : forall g G rho c args values prefix beta,
  runtime_open_args c args -> eval_terms rho [] args = Some values ->
  (satisfies G rho (prefix ++ beta)
     (open_goal (List.length prefix) args g) <->
   satisfies G rho (prefix ++ values ++ beta) g).
Proof.
  induction g; intros G rho c args values prefix beta Ha He; simpl.
  - split; intro H; constructor.
  - split; intro H; inversion H; subst;
      eapply Sat_unify;
      first [rewrite <- (eval_term_open t rho c args values prefix beta Ha He)
            |rewrite (eval_term_open t rho c args values prefix beta Ha He)
            |rewrite <- (eval_term_open t0 rho c args values prefix beta Ha He)
            |rewrite (eval_term_open t0 rho c args values prefix beta Ha He)];
      eassumption.
  - split; intro H; inversion H; subst.
    + eapply Sat_call; [eassumption| | |eassumption].
      * rewrite length_map. reflexivity.
      * rewrite <- (eval_terms_open l rho c args values prefix beta Ha He).
        eassumption.
    + eapply Sat_call; [eassumption| | |eassumption].
      * rewrite length_map. reflexivity.
      * rewrite (eval_terms_open l rho c args values prefix beta Ha He).
        eassumption.
  - split; intro H; inversion H; subst.
    + apply Sat_disj_left. apply (proj1 (IHg1 G rho c args values prefix beta Ha He)). assumption.
    + apply Sat_disj_right. apply (proj1 (IHg2 G rho c args values prefix beta Ha He)). assumption.
    + apply Sat_disj_left. apply (proj2 (IHg1 G rho c args values prefix beta Ha He)). assumption.
    + apply Sat_disj_right. apply (proj2 (IHg2 G rho c args values prefix beta Ha He)). assumption.
  - split; intro H; inversion H; subst; apply Sat_conj.
    + apply (proj1 (IHg1 G rho c args values prefix beta Ha He)). assumption.
    + apply (proj1 (IHg2 G rho c args values prefix beta Ha He)). assumption.
    + apply (proj2 (IHg1 G rho c args values prefix beta Ha He)). assumption.
    + apply (proj2 (IHg2 G rho c args values prefix beta Ha He)). assumption.
  - split; intro H; inversion H; subst;
      eapply Sat_fresh with (values := values0); [reflexivity| |reflexivity|].
    + rewrite app_assoc. apply (proj1 (IHg G rho c args values (values0 ++ prefix) beta Ha He)).
      rewrite length_app, Nat.add_comm. rewrite <- app_assoc. assumption.
    + rewrite app_assoc in H4.
      pose proof (proj2 (IHg G rho c args values (values0 ++ prefix) beta Ha He) H4) as Hbody.
      rewrite length_app, Nat.add_comm in Hbody.
      rewrite <- app_assoc in Hbody. exact Hbody.
Qed.

Corollary satisfies_open : forall G rho c args values g,
  runtime_open_args c args -> eval_terms rho [] args = Some values ->
  (satisfies G rho [] (open args g) <-> satisfies G rho values g).
Proof.
  intros G rho c args values g Ha He.
  pose proof (satisfies_open_goal g G rho c args values [] [] Ha He) as H.
  simpl in H. rewrite app_nil_r in H. exact H.
Qed.
