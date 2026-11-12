From MkRedex.Language Require Import Scoping ScopedUnification Terms Substitution Goals Environments Trees.
From Stdlib Require Import List Arith.
From MkRedex.Operational Require Import Reduction WellFormed Determinism.
Import ListNotations.
Set Default Goal Selector "!".

From MkRedex.Language Require Import Solver.
Section WithSolver.
Context `{solver : Solver}.

(** Executable small-step search on well-formed inputs.

    [head_fn] checks the head rules at one tree node.  [active_head_fn]
    first tries that node, then follows only the child selected by the
    scheduler; a head rule at an enclosing node takes priority.  The
    proof of completeness uses [Head_plug_stable] to rule out a competing
    enclosing head rewrite.  [next_step] adds the three root-only rules:
    delay release and answer promotion from either disjunction state.

    The validity arguments supply unification's acyclicity and scoping
    invariants and are erased from OCaml.  [head_fn_spec] and
    [next_step_spec] relate the functions to [Head] and [step], the
    inductive specifications.  [run_steps] iterates the function for a
    finite fuel budget, using preservation between iterations. *)

(** One executable head rewrite.  The well-formedness witness supplies the
    invariants needed by [solver_fn]; it is erased from extracted code. *)
Definition head_fn (G : env) (r : tree)
  (Hok : ok_expr G ([], r)) : option tree.
Proof.
  destruct r as [|g s|body|rel ts s|left g|left right|left right].
  - exact None.
  - destruct g as [|t1 t2|rel ts|g1 g2|g1 g2|k g].
    + exact None.
    + destruct Hok as [_ [Htight [_ Hacyclic]]].
      simpl in Htight. destruct Htight as [[Ht1 Ht2] Hsub].
      destruct (solver_fn t1 t2 (st_sub s) (st_cnt s)
        Hacyclic Hsub Ht1 Ht2) as [sub'|].
      * exact (Some (tgoal gsucc (mkstate sub' (st_cnt s)))).
      * exact (Some tfail).
    + exact (Some (tdelay (tproceed rel ts s))).
    + exact (Some (tdisjL (tgoal g1 s) (tgoal g2 s))).
    + exact (Some (tconj (tgoal g1 s) g2)).
    + exact (Some (tgoal (open (map tvar (seq (st_cnt s) k)) g)
        (mkstate (st_sub s) (st_cnt s + k)))).
  - exact None.
  - destruct (nth_error G rel) as [[arity body]|].
    + exact (Some (tgoal (open ts body) s)).
    + exact None.
  - exact (match left with
      | tfail => Some tfail
      | tgoal gsucc s0 => Some (tgoal g s0)
      | tdelay body => Some (tdelay (tconj body g))
      | tdisjL (tgoal gsucc s0) tail =>
          Some (tdisjL (tconj (tgoal gsucc s0) g) (tconj tail g))
      | tdisjR prefix (tgoal gsucc s0) =>
          Some (tdisjR (tconj prefix g) (tconj (tgoal gsucc s0) g))
      | _ => None
      end).
  - exact (match left with
      | tfail => Some right
      | tdelay body => Some (tdelay (tdisjR body right))
      | tdisjL (tgoal gsucc s0) tail =>
          Some (tdisjL (tgoal gsucc s0) (tdisjL tail right))
      | tdisjR prefix (tgoal gsucc s0) =>
          Some (tdisjR (tdisjL prefix right) (tgoal gsucc s0))
      | _ => None
      end).
  - exact (match right with
      | tfail => Some left
      | tdelay body => Some (tdelay (tdisjL left body))
      | tdisjL (tgoal gsucc s0) tail =>
          Some (tdisjL (tgoal gsucc s0) (tdisjR left tail))
      | tdisjR prefix (tgoal gsucc s0) =>
          Some (tdisjR (tdisjR left prefix) (tgoal gsucc s0))
      | _ => None
      end).
Defined.

Theorem head_fn_sound : forall G r Hok out,
  head_fn G r Hok = Some out -> Head G r out.
Proof.
  intros G r Hok out Hresult.
  destruct r as [|g s|body|rel ts s|left g|left right|left right];
    simpl in Hresult; try discriminate.
  - destruct g as [|t1 t2|rel ts|g1 g2|g1 g2|k g];
      simpl in Hresult; try discriminate;
      try (inversion Hresult; subst; constructor).
    destruct Hok as [_ [Htight [_ Hacyclic]]].
    simpl in Htight. destruct Htight as [[Ht1 Ht2] Hsub].
    destruct (solver_fn t1 t2 (st_sub s) (st_cnt s)
      Hacyclic Hsub Ht1 Ht2) as [sub'|] eqn:Huni;
      inversion Hresult; subst.
    + apply H_unify_ok.
      apply (proj2 (solver_fn_spec (st_cnt s) (st_sub s) t1 t2
        Hacyclic Hsub Ht1 Ht2 (Some sub'))). exact Huni.
    + apply H_unify_fail.
      apply (proj2 (solver_fn_spec (st_cnt s) (st_sub s) t1 t2
        Hacyclic Hsub Ht1 Ht2 None)). exact Huni.
  - destruct (nth_error G rel) as [[arity def]|] eqn:Hlookup;
      simpl in Hresult; try discriminate.
    inversion Hresult; subst. eapply H_proceed; [exact Hlookup |].
    destruct Hok as [[c Hclosed] _]. simpl in Hclosed.
    rewrite Hlookup in Hclosed. exact (proj1 (proj2 Hclosed)).
  - repeat match type of Hresult with
      | context [match ?x with _ => _ end] => destruct x
      end;
      simpl in Hresult; try discriminate;
      inversion Hresult; subst; eauto using Head.
  - repeat match type of Hresult with
      | context [match ?x with _ => _ end] => destruct x
      end;
      simpl in Hresult; try discriminate;
      inversion Hresult; subst; eauto using Head.
  - repeat match type of Hresult with
      | context [match ?x with _ => _ end] => destruct x
      end;
      simpl in Hresult; try discriminate;
      inversion Hresult; subst; eauto using Head.
Qed.

Theorem head_fn_complete : forall G r Hok out,
  Head G r out -> head_fn G r Hok = Some out.
Proof.
  intros G r Hok out Hhead.
  destruct Hhead; simpl; try reflexivity.
  - destruct Hok as [_ [Htight [_ Hacyclic]]].
    simpl in Htight. destruct Htight as [[Ht1 Ht2] Hsub].
    simpl. rewrite (proj1 (solver_fn_spec (st_cnt s) (st_sub s)
      t1 t2 Hacyclic Hsub Ht1 Ht2 (Some s')) H). reflexivity.
  - destruct Hok as [_ [Htight [_ Hacyclic]]].
    simpl in Htight. destruct Htight as [[Ht1 Ht2] Hsub].
    simpl. rewrite (proj1 (solver_fn_spec (st_cnt s) (st_sub s)
      t1 t2 Hacyclic Hsub Ht1 Ht2 None) H). reflexivity.
  - now rewrite H.
Qed.

Theorem head_fn_spec : forall G r Hok out,
  Head G r out <-> head_fn G r Hok = Some out.
Proof.
  intros G r Hok out. split.
  - apply head_fn_complete.
  - apply head_fn_sound.
Qed.

Lemma ok_expr_plug_root : forall G ans E r,
  ok_expr G (ans, plug E r) -> ok_expr G ([], r).
Proof.
  intros G ans E r [[c Hclosed] [Htight [_ Hacyclic]]].
  repeat split.
  - exists c. eapply plug_closed_inv; eassumption.
  - eapply plug_tight_inv; eassumption.
  - constructor.
  - eapply plug_acyclic_inv; eassumption.
Qed.

Lemma head_fn_absent_under_context : forall G E r r' Hok,
  E <> chole -> Head G r r' ->
  head_fn G (plug E r) Hok = None.
Proof.
  intros G E r r' Hok Hnonempty Hhead.
  destruct (head_fn G (plug E r) Hok) as [out|] eqn:Hresult;
    [|reflexivity].
  exfalso. eapply Head_plug_stable;
    [exact Hhead | exact Hnonempty |].
  eapply head_fn_sound. exact Hresult.
Qed.

(** Search only the currently selected child of each context.  A head
    rewrite at the root takes priority over one deeper in the tree. *)
Fixpoint active_head_fn (G : env) (t : tree)
  (Hok : ok_expr G ([], t)) {struct t} : option tree.
Proof.
  destruct (head_fn G t Hok) as [out|] eqn:Hroot.
  - exact (Some out).
  - destruct t as [|g s|body|rel ts s|child g|left right|left right].
    + exact None.
    + exact None.
    + exact None.
    + exact None.
    + destruct (active_head_fn G child
        (ok_expr_plug_root G [] (cconj chole g) child Hok))
        as [next|].
      * exact (Some (tconj next g)).
      * exact None.
    + destruct (active_head_fn G left
        (ok_expr_plug_root G [] (cdisjL chole right) left Hok))
        as [next|].
      * exact (Some (tdisjL next right)).
      * exact None.
    + destruct (active_head_fn G right
        (ok_expr_plug_root G [] (cdisjR left chole) right Hok))
        as [next|].
      * exact (Some (tdisjR left next)).
      * exact None.
Defined.

Theorem active_head_fn_sound : forall G t Hok out,
  active_head_fn G t Hok = Some out ->
  exists E r r', t = plug E r /\ out = plug E r' /\ Head G r r'.
Proof.
  intros G t. induction t; intros Hok out Hresult;
    cbn [active_head_fn] in Hresult.
  all: destruct (head_fn G _ Hok) eqn:Hroot;
    try solve [inversion Hresult; subst;
      exists chole; eexists; eexists; simpl;
      repeat split; eauto using head_fn_sound | discriminate].
  - destruct (active_head_fn G t
      (ok_expr_plug_root G [] (cconj chole g) t Hok))
      as [childout|] eqn:Hchild; simpl in Hresult; try discriminate.
    inversion Hresult; subst out.
    destruct (IHt _ _ Hchild) as [E [r [r' [Hsrc [Hdst Hhead]]]]].
    exists (cconj E g), r, r'. simpl.
    repeat split; try rewrite Hsrc; try rewrite Hdst;
      try reflexivity. exact Hhead.
  - destruct (active_head_fn G t1
      (ok_expr_plug_root G [] (cdisjL chole t2) t1 Hok))
      as [childout|] eqn:Hchild; simpl in Hresult; try discriminate.
    inversion Hresult; subst out.
    destruct (IHt1 _ _ Hchild) as [E [r [r' [Hsrc [Hdst Hhead]]]]].
    exists (cdisjL E t2), r, r'. simpl.
    repeat split; try rewrite Hsrc; try rewrite Hdst;
      try reflexivity. exact Hhead.
  - destruct (active_head_fn G t2
      (ok_expr_plug_root G [] (cdisjR t1 chole) t2 Hok))
      as [childout|] eqn:Hchild; simpl in Hresult; try discriminate.
    inversion Hresult; subst out.
    destruct (IHt2 _ _ Hchild) as [E [r [r' [Hsrc [Hdst Hhead]]]]].
    exists (cdisjR t1 E), r, r'. simpl.
    repeat split; try rewrite Hsrc; try rewrite Hdst;
      try reflexivity. exact Hhead.
Qed.

Lemma active_head_fn_root : forall G t Hok out,
  head_fn G t Hok = Some out ->
  active_head_fn G t Hok = Some out.
Proof.
  intros G t Hok out Hroot. destruct t;
    cbn [active_head_fn]; rewrite Hroot; reflexivity.
Qed.

Theorem active_head_fn_complete : forall G E r r' Hok,
  Head G r r' ->
  active_head_fn G (plug E r) Hok = Some (plug E r').
Proof.
  intros G E. induction E; intros r r' Hok Hhead;
    cbn [plug active_head_fn].
  - apply active_head_fn_root. now apply head_fn_complete.
  - pose proof (head_fn_absent_under_context G (cdisjL E t)
      r r' Hok ltac:(discriminate) Hhead) as Hnone.
    cbn [plug] in Hnone. rewrite Hnone. cbn.
    rewrite (IHE r r' (ok_expr_plug_root G []
      (cdisjL chole t) (plug E r) Hok) Hhead). reflexivity.
  - pose proof (head_fn_absent_under_context G (cdisjR t E)
      r r' Hok ltac:(discriminate) Hhead) as Hnone.
    cbn [plug] in Hnone. rewrite Hnone. cbn.
    rewrite (IHE r r' (ok_expr_plug_root G []
      (cdisjR t chole) (plug E r) Hok) Hhead). reflexivity.
  - pose proof (head_fn_absent_under_context G (cconj E g)
      r r' Hok ltac:(discriminate) Hhead) as Hnone.
    cbn [plug] in Hnone. rewrite Hnone. cbn.
    rewrite (IHE r r' (ok_expr_plug_root G []
      (cconj chole g) (plug E r) Hok) Hhead). reflexivity.
Qed.

(** The answer list changes only at the two top-level promotion rules.
    All other rewrites are found by [active_head_fn]. *)
Definition next_step (G : env) (e : expr)
  (Hok : ok_expr G e) : option expr.
Proof.
  destruct e as [ans t].
  destruct (active_head_fn G t (ok_expr_plug_root G ans chole t Hok))
    as [next|].
  - exact (Some (ans, next)).
  - exact (match t with
      | tdelay body => Some (ans, body)
      | tdisjL (tgoal gsucc s) waiting => Some (ans ++ [s], waiting)
      | tdisjR waiting (tgoal gsucc s) => Some (ans ++ [s], waiting)
      | _ => None
      end).
Defined.

Theorem next_step_sound : forall G e Hok e',
  next_step G e Hok = Some e' -> G |= e --> e'.
Proof.
  intros G [ans t] Hok e' Hresult.
  unfold next_step in Hresult. simpl in Hresult.
  destruct (active_head_fn G t (ok_expr_plug_root G ans chole t Hok))
    as [next|] eqn:Hhead.
  - inversion Hresult; subst e'.
    destruct (active_head_fn_sound G t
      (ok_expr_plug_root G ans chole t Hok) next Hhead)
      as [E [r [r' [Hsrc [Hdst Hr]]]]].
    rewrite Hsrc, Hdst. apply S_ctx. exact Hr.
  - destruct t; simpl in Hresult; try discriminate.
    + inversion Hresult; subst. constructor.
    + destruct t1; simpl in Hresult; try discriminate.
      destruct g; simpl in Hresult; try discriminate.
      inversion Hresult; subst. constructor.
    + destruct t2; simpl in Hresult; try discriminate.
      destruct g; simpl in Hresult; try discriminate.
      inversion Hresult; subst. constructor.
Qed.

Theorem next_step_complete : forall G e Hok e',
  G |= e --> e' -> next_step G e Hok = Some e'.
Proof.
  intros G e Hok e' Hstep. destruct Hstep.
  - unfold next_step. simpl.
    rewrite (active_head_fn_complete G E r r'
      (ok_expr_plug_root G ans chole (plug E r) Hok) H).
    reflexivity.
  - unfold next_step. simpl.
    destruct (active_head_fn G (tdelay t)
      (ok_expr_plug_root G ans chole (tdelay t) Hok))
      as [out|] eqn:Hhead; [|reflexivity].
    destruct (active_head_fn_sound G (tdelay t) _ out Hhead)
      as [E [r [r' [Hsrc [_ Hr]]]]].
    destruct (plug_neq_atomic G E r r' Hr) as [_ [Hno _]].
    exfalso. apply (Hno t). symmetry. exact Hsrc.
  - unfold next_step. simpl.
    destruct (active_head_fn G (tdisjL (tgoal gsucc s) t)
      (ok_expr_plug_root G ans chole
        (tdisjL (tgoal gsucc s) t) Hok))
      as [out|] eqn:Hhead; [|reflexivity].
    destruct (active_head_fn_sound G
      (tdisjL (tgoal gsucc s) t) _ out Hhead)
      as [E [r [r' [Hsrc [_ Hr]]]]].
    destruct (plug_neq_atomic G E r r' Hr) as [_ [_ [Hno _]]].
    exfalso. apply (Hno s t). symmetry. exact Hsrc.
  - unfold next_step. simpl.
    destruct (active_head_fn G (tdisjR t (tgoal gsucc s))
      (ok_expr_plug_root G ans chole
        (tdisjR t (tgoal gsucc s)) Hok))
      as [out|] eqn:Hhead; [|reflexivity].
    destruct (active_head_fn_sound G
      (tdisjR t (tgoal gsucc s)) _ out Hhead)
      as [E [r [r' [Hsrc [_ Hr]]]]].
    destruct (plug_neq_atomic G E r r' Hr) as [_ [_ [_ [Hno _]]]].
    exfalso. apply (Hno t s). symmetry. exact Hsrc.
Qed.

Theorem next_step_spec : forall G e Hok e',
  G |= e --> e' <-> next_step G e Hok = Some e'.
Proof.
  intros G e Hok e'. split.
  - apply next_step_complete.
  - apply next_step_sound.
Qed.

Lemma next_step_none_value : forall G e Hok,
  next_step G e Hok = None -> is_value e.
Proof.
  intros G e Hok Hnone.
  destruct (progress G e Hok) as [Hvalue | [next Hstep]];
    [exact Hvalue |].
  apply (proj1 (next_step_spec G e Hok next)) in Hstep.
  rewrite Hnone in Hstep. discriminate.
Qed.

(** Bundle the output with preservation so the recursive runner can pattern
    match on an ordinary option.  The proof fields disappear on extraction. *)
Definition next_step_checked (G : env) (Henv : closed_env G)
  (e : expr) (Hok : ok_expr G e) :
  option {next : expr | G |= e --> next /\ ok_expr G next}.
Proof.
  destruct (next_step G e Hok) as [next|] eqn:Hnext.
  - exact (Some (exist _ next
      (conj (next_step_sound G e Hok next Hnext)
        (step_ok G e next Henv Hok
          (next_step_sound G e Hok next Hnext))))).
  - exact None.
Defined.

(** Execute at most [fuel] steps.  Preservation supplies the proof needed
    by the next call; extraction removes these proof arguments. *)
Fixpoint run_steps (G : env) (Henv : closed_env G)
  (fuel : nat) (e : expr) (Hok : ok_expr G e) {struct fuel} : expr.
Proof.
  destruct fuel as [|fuel].
  - exact e.
  - destruct (next_step_checked G Henv e Hok)
      as [[next [Hstep Hvalid]]|].
    + exact (run_steps G Henv fuel next Hvalid).
    + exact e.
Defined.

Theorem run_steps_multi : forall G Henv fuel e Hok,
  multi G e (run_steps G Henv fuel e Hok).
Proof.
  intros G Henv fuel. induction fuel as [|fuel IH];
    intros e Hok; cbn [run_steps].
  - constructor.
  - destruct (next_step_checked G Henv e Hok)
      as [[next [Hstep Hvalid]]|].
    + eapply multi_step.
      * exact Hstep.
      * apply IH.
    + constructor.
Qed.

Corollary run_steps_answers_prefix : forall G Henv fuel e Hok,
  exists added,
    observed_answers (run_steps G Henv fuel e Hok) =
    observed_answers e ++ added.
Proof.
  intros G Henv fuel e Hok.
  eapply multi_observed_answers_prefix.
  apply run_steps_multi.
Qed.

End WithSolver.
