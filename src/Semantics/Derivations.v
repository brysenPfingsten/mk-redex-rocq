From Stdlib Require Import List Arith Lia.
From MkRedex.Language Require Import Terms Goals Environments.
From MkRedex.Semantics Require Import Denotation DenotationOpening Valuations WellFormed.
Import ListNotations.
Set Default Goal Selector "!".

(** A finite source proof with a decreasing work index. The index counts
    logical work, not runtime steps or scheduling time. *)
Inductive derives (G : env) (rho : valuation) : nat -> list ground -> goal -> Prop :=
| D_success : forall beta, derives G rho 0 beta gsucc
| D_unify : forall beta t u v,
    eval_term rho beta t = Some v -> eval_term rho beta u = Some v ->
    derives G rho 1 beta (gunify t u)
| D_left : forall n beta a b, derives G rho n beta a ->
    derives G rho (2+n) beta (gdisj a b)
| D_right : forall n beta a b, derives G rho n beta b ->
    derives G rho (2+n) beta (gdisj a b)
| D_conj : forall n m beta a b,
    derives G rho n beta a -> derives G rho m beta b ->
    derives G rho (2+n+m) beta (gconj a b)
| D_fresh : forall n beta k body values,
    List.length values = k -> derives G rho n (values ++ beta) body ->
    derives G rho (2+n) beta (gfresh k body)
| D_call : forall n beta r args arity body values,
    nth_error G r = Some (arity,body) -> List.length args = arity ->
    eval_terms rho beta args = Some values -> derives G rho n values body ->
    derives G rho (2+n) beta (grelcall r args).

Lemma satisfaction_derives : forall G rho beta g,
  satisfies G rho beta g -> exists n, derives G rho n beta g.
Proof.
  intros G rho beta g H. induction H.
  - exists 0. constructor.
  - exists 1. eapply D_unify; eassumption.
  - destruct IHsatisfies as [n Hn]. exists (2+n). apply D_left. exact Hn.
  - destruct IHsatisfies as [n Hn]. exists (2+n). apply D_right. exact Hn.
  - destruct IHsatisfies1 as [n Hn], IHsatisfies2 as [m Hm].
    exists (2+n+m). apply D_conj; assumption.
  - destruct IHsatisfies as [n Hn]. exists (2+n). eapply D_fresh; eassumption.
  - destruct IHsatisfies as [n Hn]. exists (2+n). eapply D_call; eassumption.
Qed.

Lemma derives_satisfaction : forall G rho n beta g,
  derives G rho n beta g -> satisfies G rho beta g.
Proof. intros G rho n beta g H. induction H; econstructor; eassumption. Qed.

Theorem derives_agrees : forall G rho n beta g,
  derives G rho n beta g -> forall sigma d c,
  closed_env G -> closed_goal G d c g -> agrees_below c rho sigma ->
  derives G sigma n beta g.
Proof.
  intros G rho n beta g Hsat. induction Hsat; intros sigma d c Henv Hclosed Hagree;
    simpl in Hclosed.
  - constructor.
  - destruct Hclosed as [Ht Hu]. eapply D_unify.
    + rewrite <- (eval_term_agrees t d c rho sigma beta Ht Hagree). exact H.
    + rewrite <- (eval_term_agrees u d c rho sigma beta Hu Hagree). exact H0.
  - apply D_left. eapply IHHsat; [exact Henv|exact (proj1 Hclosed)|exact Hagree].
  - apply D_right. eapply IHHsat; [exact Henv|exact (proj2 Hclosed)|exact Hagree].
  - apply D_conj.
    + eapply IHHsat1; [exact Henv|exact (proj1 Hclosed)|exact Hagree].
    + eapply IHHsat2; [exact Henv|exact (proj2 Hclosed)|exact Hagree].
  - eapply D_fresh; [exact H|]. eapply IHHsat; eassumption.
  - rewrite H in Hclosed. destruct Hclosed as [Harity Hargs].
    eapply D_call; [exact H|exact H0| |].
    + rewrite <- (eval_terms_agrees args d c rho sigma beta Hargs Hagree). exact H1.
    + eapply IHHsat; [exact Henv| |exact Hagree].
      eapply closed_goal_mono; [apply Nat.le_refl|apply Nat.le_0_l|].
      exact (Henv r arity body H).
Qed.

Lemma derives_open_goal : forall g G rho c args values prefix beta n,
  runtime_open_args c args -> eval_terms rho [] args = Some values ->
  derives G rho n (prefix ++ values ++ beta) g ->
  derives G rho n (prefix ++ beta) (open_goal (List.length prefix) args g).
Proof.
  induction g; intros G rho c args values prefix beta cost Ha He Hd; simpl;
    inversion Hd; subst.
  - constructor.
  - eapply D_unify.
    + rewrite (eval_term_open t rho c args values prefix beta Ha He). eassumption.
    + rewrite (eval_term_open t0 rho c args values prefix beta Ha He). eassumption.
  - eapply D_call; [eassumption|rewrite length_map; reflexivity| |eassumption].
    rewrite (eval_terms_open l rho c args values prefix beta Ha He). eassumption.
  - apply D_left. eapply IHg1; eassumption.
  - apply D_right. eapply IHg2; eassumption.
  - apply D_conj; [eapply IHg1|eapply IHg2]; eassumption.
  - eapply D_fresh with (values := values0); [reflexivity|].
    assert (Hb : derives G rho n0 ((values0 ++ prefix) ++ values ++ beta) g).
    { rewrite <- app_assoc. eassumption. }
    pose proof (IHg G rho c args values (values0 ++ prefix) beta n0 Ha He Hb) as Hopen.
    rewrite length_app, Nat.add_comm in Hopen.
    rewrite <- app_assoc in Hopen. exact Hopen.
Qed.

Corollary derives_open : forall G rho c args values n g,
  runtime_open_args c args -> eval_terms rho [] args = Some values ->
  derives G rho n values g -> derives G rho n [] (open args g).
Proof.
  intros G rho c args values n g Ha He Hd.
  pose proof (derives_open_goal g G rho c args values [] [] n Ha He) as H.
  simpl in H. rewrite app_nil_r in H. apply H. exact Hd.
Qed.
