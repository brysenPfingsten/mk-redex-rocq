From Stdlib Require Import List Arith Lia.
From MkRedex.Language Require Import Terms Goals Substitution Unification Trees.
From MkRedex.Semantics Require Import Denotation WellFormed Reduction Executable.
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
