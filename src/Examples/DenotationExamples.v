From Stdlib Require Import List.
From MkRedex.Language Require Import Terms Goals Environments Substitution Trees.
From MkRedex.Denotational Require Import Denotation.
From MkRedex.Operational Require Import Reduction.
From MkRedex.Correctness Require Import Soundness.
Import ListNotations.
Set Default Goal Selector "!".

Example unproductive_recursion : forall rho beta,
  ~ satisfies [(0, grelcall 0 [])] rho beta (grelcall 0 []).
Proof.
  intros rho beta H.
  remember (grelcall 0 []) as g eqn:E in H at 2.
  induction H; inversion E; subst.
  simpl in H. inversion H; subst. apply IHsatisfies. reflexivity.
Qed.

Example recursive_relation_with_base : forall rho,
  satisfies [(0, gdisj (grelcall 0 []) gsucc)] rho [] (grelcall 0 []).
Proof.
  intro rho. eapply Sat_call; try reflexivity.
  apply Sat_disj_right. constructor.
Qed.

Example fresh_distinct_from_outer_parameter : forall rho,
  satisfies [] rho [gnat 3]
    (gfresh 1 (gconj (gunify (tpar 0) (tnat 7))
                    (gunify (tpar 1) (tnat 3)))).
Proof.
  intro rho. eapply Sat_fresh with (values := [gnat 7]); [reflexivity|].
  apply Sat_conj; eapply Sat_unify; reflexivity.
Qed.

Example malformed_parameter_rejected : forall rho,
  ~ satisfies [] rho [] (gunify (tpar 0) (tpar 0)).
Proof.
  intros rho H. inversion H; subst. discriminate.
Qed.

(** Why completeness cannot simply reverse the soundness simulation:
    allocating fresh variables may require changing the valuation above the
    old counter. Here the source is satisfied, but the chosen fixed valuation
    assigns zero to the newly allocated variable, whose constraint is one. *)
Example fixed_valuation_forward_simulation_fails :
  let rho : valuation := fun _ => gnat 0 in
  let before : expr :=
    ([], tgoal (gfresh 1 (gunify (tpar 0) (tnat 1))) (mkstate [] 0)) in
  let after : expr :=
    ([], tgoal (gunify (tvar 0) (tnat 1)) (mkstate [] 1)) in
  step [] before after /\ expr_meaning [] rho before /\ ~ expr_meaning [] rho after.
Proof.
  simpl. split.
  - apply (S_ctx [] [] chole _ _). apply H_fresh.
  - split.
    + right. split; [apply satisfies_sub_nil|].
      eapply Sat_fresh with (values := [gnat 1]); [reflexivity|].
      eapply Sat_unify; reflexivity.
    + intros [[s [Hin _]]|[_ Hsat]]; [contradiction|].
      inversion Hsat; subst. simpl in *. congruence.
Qed.
