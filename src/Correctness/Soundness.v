From MkRedex.Language Require Import WellFormed Scoping ScopedUnification Terms Goals Substitution Environments Trees Unification.
From Stdlib Require Import List Arith.
From MkRedex.Denotational Require Import Denotation Opening.
From MkRedex.Correctness Require Import Unification.
From MkRedex.Operational Require Import Reduction WellFormed.
From MkRedex.Execution Require Import Executable.
Import ListNotations.
Set Default Goal Selector "!".

(** A valuation solves the work remaining in a tree. Conjunction uses the
    same valuation for its suspended continuation and for its left subtree. *)
Fixpoint tree_meaning (G : env) (rho : valuation) (t : tree) : Prop :=
  match t with
  | tfail => False
  | tgoal g s => satisfies_sub rho (st_sub s) /\ satisfies G rho [] g
  | tproceed r args s =>
      satisfies_sub rho (st_sub s) /\ satisfies G rho [] (grelcall r args)
  | tdelay t => tree_meaning G rho t
  | tconj t g => tree_meaning G rho t /\ satisfies G rho [] g
  | tdisjL a b | tdisjR a b => tree_meaning G rho a \/ tree_meaning G rho b
  end.

Definition expr_meaning (G : env) (rho : valuation) (e : expr) : Prop :=
  (exists s, In s (fst e) /\ satisfies_sub rho (st_sub s)) \/
  tree_meaning G rho (snd e).

Lemma eval_terms_total : forall rho c args,
  runtime_open_args c args -> exists values, eval_terms rho [] args = Some values.
Proof.
  intros rho c args H. induction H as [|t ts Ht Hts IH]; simpl.
  - eexists. reflexivity.
  - destruct (eval_term_closed_total t 0 c rho [] Ht eq_refl) as [v Hv].
    destruct IH as [vs Hvs]. rewrite Hv, Hvs. eexists. reflexivity.
Qed.

Lemma Head_meaning_backward : forall G t t' rho,
  ok_env G -> ok_tree G t ->
  Head G t t' -> tree_meaning G rho t' -> tree_meaning G rho t.
Proof.
  intros G t t' rho Henv Htree Hhead.
  destruct Hhead; simpl in *; intro Hmeaning;
    try tauto.
  - destruct Hmeaning as [Hmodel Hsucc]. split.
    + eapply Unify_ground_old_bindings; eassumption.
    + destruct Htree as [[Ht Hu] Hsub].
      destruct (Unify_ground_sound (st_cnt s) (st_sub s) t1 t2 s' rho
        (proj2 Hsub) Ht H Hmodel) as [v [Hv1 Hv2]].
      eapply Sat_unify; eassumption.
  - destruct Hmeaning as [[Hm Ha] | [Hm Hb]]; split; try exact Hm.
    + apply Sat_disj_left. exact Ha.
    + apply Sat_disj_right. exact Hb.
  - destruct Hmeaning as [[Hmodel Ha] Hb].
    split; [exact Hmodel|]. apply Sat_conj; assumption.
  - destruct Hmeaning as [Hmodel Hbody]. split; [exact Hmodel|].
    set (args := map tvar (seq (st_cnt s) k)) in *.
    pose proof (fresh_args_open_args (st_cnt s) (st_cnt s) k (le_n _)) as Ha.
    destruct (eval_terms_total rho (st_cnt s + k) args Ha) as [values He].
    eapply Sat_fresh with (values := values).
    + pose proof (eval_terms_length rho [] args values He) as Hlen.
      unfold args in Hlen. rewrite length_map, length_seq in Hlen. symmetry. exact Hlen.
    + rewrite app_nil_r. apply (proj1 (satisfies_open G rho (st_cnt s + k) args values g Ha He)).
      exact Hbody.
  - destruct Hmeaning as [Hmodel Hbody]. split; [exact Hmodel|].
    pose proof (ok_tree_proceed_open_args G r ts s Htree) as Ha.
    destruct (eval_terms_total rho (st_cnt s) ts Ha) as [values He].
    eapply Sat_call; [exact H|exact H0|exact He|].
    apply (proj1 (satisfies_open G rho (st_cnt s) ts values body Ha He)). exact Hbody.
  - destruct Hmeaning as [Hmodel Hg]. split.
    + split; [exact Hmodel|constructor].
    + exact Hg.
Qed.

Lemma plug_meaning_monotone : forall G rho E t t',
  (tree_meaning G rho t' -> tree_meaning G rho t) ->
  tree_meaning G rho (plug E t') -> tree_meaning G rho (plug E t).
Proof.
  intros G rho E. induction E; intros r r' Himp Hmeaning; simpl in *; try tauto; specialize (IHE r r' Himp); tauto.
Qed.

Theorem step_meaning_backward : forall G e e' rho,
  ok_env G -> ok_expr G e -> step G e e' ->
  expr_meaning G rho e' -> expr_meaning G rho e.
Proof.
  intros G e e' rho Henv Hok Hstep Hmeaning.
  destruct Hstep; unfold expr_meaning in *; simpl in *.
  - destruct Hmeaning as [Hans|Htree]; [left; exact Hans|right].
    apply (plug_meaning_monotone G rho E r r'); [|exact Htree].
    apply Head_meaning_backward; try assumption.
    + apply (plug_ok_tree_inv G E r). exact (proj1 Hok).
  - exact Hmeaning.
  - destruct Hmeaning as [[a [Hin Hmodel]]|Htree].
    + apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      * left. exists a. split; assumption.
      * simpl in Hin. destruct Hin as [<-|Hfalse]; [|contradiction].
        right. left. split; [exact Hmodel|constructor].
    + right. right. exact Htree.
  - destruct Hmeaning as [[a [Hin Hmodel]]|Htree].
    + apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      * left. exists a. split; assumption.
      * simpl in Hin. destruct Hin as [<-|Hfalse]; [|contradiction].
        right. right. split; [exact Hmodel|constructor].
    + right. left. exact Htree.
Qed.

Theorem multi_meaning_backward : forall G e e' rho,
  ok_env G -> ok_expr G e -> multi G e e' ->
  expr_meaning G rho e' -> expr_meaning G rho e.
Proof.
  intros G e e' rho Henv Hok Hrun. revert Hok.
  induction Hrun; intros Hok Hmeaning; [exact Hmeaning|].
  eapply step_meaning_backward; [exact Henv|exact Hok|exact H|].
  apply IHHrun; [eapply step_ok; eassumption|exact Hmeaning].
Qed.

Lemma observed_answer_meaning : forall G rho e answer,
  In answer (observed_answers e) -> satisfies_sub rho (st_sub answer) ->
  expr_meaning G rho e.
Proof.
  intros G rho [ans t] answer Hin Hmodel.
  unfold observed_answers in Hin. simpl in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - left. exists answer. split; assumption.
  - right. destruct t; simpl in Hin; try contradiction.
    destruct g; simpl in Hin; try contradiction.
    destruct Hin as [<-|Hfalse]; [|contradiction].
    simpl. split; [exact Hmodel|constructor].
Qed.

(** Main search soundness: every observed answer from a finite reduction
    represents only source solutions, projected onto the original query. *)
Theorem search_soundness : forall G query g s e answer rho,
  ok_env G -> ok_expr G ([], tgoal g s) ->
  multi G ([], tgoal g s) e ->
  In answer (observed_answers e) -> represents query answer rho ->
  solution G query g rho.
Proof.
  intros G query g s e answer rho Henv Hok Hrun Hin [sigma [Hagree Hmodel]].
  pose proof (observed_answer_meaning G sigma e answer Hin Hmodel) as Hmeaning.
  pose proof (multi_meaning_backward G ([], tgoal g s) e sigma Henv Hok Hrun Hmeaning) as Hstart.
  destruct Hstart as [[a [Hfalse _]]|[_ Hsat]]; [contradiction|].
  exists sigma. split; assumption.
Qed.

Corollary executable_search_soundness : forall G Henv query fuel g s Hok answer rho,
  In answer (observed_answers (run_steps G Henv fuel ([], tgoal g s) Hok)) ->
  represents query answer rho -> solution G query g rho.
Proof.
  intros G Henv query fuel g s Hok answer rho Hin Hrepr.
  eapply search_soundness; [exact Henv|exact Hok|apply run_steps_multi|exact Hin|exact Hrepr].
Qed.
