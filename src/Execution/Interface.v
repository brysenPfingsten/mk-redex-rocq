From MkRedex.Language Require Import WellFormed WellFormedProperties ScopedUnification Terms Goals Substitution Unification Environments Trees.
From Stdlib Require Import List Arith Lia Logic.ProofIrrelevance.
From MkRedex.Denotational Require Import Denotation.
From MkRedex.Execution Require Import Input Executable RunnerCorrespondence.
From MkRedex.Operational Require Import Reduction WellFormed.
From MkRedex.Correctness Require Import Completeness Soundness.
Import ListNotations.
Set Default Goal Selector "!".


Definition terminalb (e : expr) : bool :=
  match snd e with tfail | tgoal gsucc _ => true | _ => false end.
Lemma terminalb_spec : forall e, terminalb e = true <-> is_value e.
Proof. intros [ans t]. unfold terminalb,is_value; simpl. destruct t; simpl; try solve [intuition discriminate]. destruct g; simpl; intuition discriminate. Qed.

Record execution := {
  execution_final : expr;
  execution_steps : nat;
  execution_trace : list expr
}.

(** The optional trace contains the initial expression and every successor.
    At zero fuel we inspect terminal syntax, without taking another step. *)
Fixpoint execute (G : env) (Henv : ok_env G) (capture : bool)
  (fuel : nat) (e : expr) (Hok : ok_expr G e) {struct fuel} : execution.
Proof.
  destruct fuel as [|fuel].
  - exact {| execution_final := e; execution_steps := 0;
             execution_trace := if capture then [e] else [] |}.
  - destruct (next_step_checked G Henv e Hok) as [[next [Hstep Hvalid]]|].
    + pose (tail := execute G Henv capture fuel next Hvalid).
      exact {| execution_final := execution_final tail;
               execution_steps := S (execution_steps tail);
               execution_trace := if capture then e :: execution_trace tail else [] |}.
    + exact {| execution_final := e; execution_steps := 0;
               execution_trace := if capture then [e] else [] |}.
Defined.

Theorem execute_final : forall G Henv capture fuel e Hok,
  execution_final (execute G Henv capture fuel e Hok) = run_steps G Henv fuel e Hok.
Proof.
  intros G Henv capture fuel. induction fuel; intros e Hok; cbn [execute run_steps].
  - reflexivity.
  - destruct (next_step_checked G Henv e Hok) as [[next [Hs Hv]]|]; simpl;
      [apply IHfuel|reflexivity].
Qed.
Lemma execute_steps_bound : forall G Henv capture fuel e Hok,
  execution_steps (execute G Henv capture fuel e Hok) <= fuel.
Proof.
  intros G Henv capture fuel. induction fuel; intros e Hok; cbn [execute execution_steps]; [lia|].
  destruct (next_step_checked G Henv e Hok) as [[next [Hs Hv]]|]; simpl; [specialize (IHfuel next Hv)|]; lia.
Qed.

Inductive trace_steps (G : env) : list expr -> Prop :=
| trace_single : forall e, trace_steps G [e]
| trace_next : forall e e' tail,
    step G e e' -> trace_steps G (e'::tail) -> trace_steps G (e::e'::tail).

Theorem execute_trace : forall G Henv fuel e Hok,
  exists tail, execution_trace (execute G Henv true fuel e Hok) = e::tail /\
    trace_steps G (e::tail) /\
    List.length (e::tail) = S (execution_steps (execute G Henv true fuel e Hok)).
Proof.
  intros G Henv fuel. induction fuel; intros e Hok; cbn [execute].
  - exists []. split; [reflexivity|]. split; [constructor|reflexivity].
  - destruct (next_step_checked G Henv e Hok) as [[next [Hs Hv]]|]; simpl.
    + destruct (IHfuel next Hv) as [tail [Ht [Htrace Hlen]]].
      rewrite Ht. exists (next::tail). split; [reflexivity|]. split.
      * constructor; assumption.
      * simpl in *. lia.
    + exists []. split; [reflexivity|]. split; [constructor|reflexivity].
Qed.

Lemma observed_answers_acyclic : forall G e,
  ok_expr G e ->
  Forall (fun s => acyclic_sub (st_sub s)) (observed_answers e).
Proof.
  intros G [ans t] [Htree Hans]. unfold observed_answers. simpl.
  apply Forall_app. split.
  - eapply Forall_impl; [|exact Hans]. intros s Hs. exact (proj2 Hs).
  - destruct t; simpl; try solve [constructor].
    destruct g; simpl; try solve [constructor].
    constructor; [exact (proj2 (proj2 Htree))|constructor].
Qed.

Definition project_answer (query : list nat) (s : state)
  (Hacyc : acyclic_sub (st_sub s)) : list (nat * term) :=
  map (fun x => (x,apply_sub (tvar x) (st_sub s) Hacyc)) query.

Definition project_answers (query : list nat) (answers : list state)
  (Hacyc : Forall (fun s => acyclic_sub (st_sub s)) answers) : list (list (nat * term)).
Proof.
  induction answers as [|s answers IH]; [exact []|].
  exact (project_answer query s (Forall_inv Hacyc) :: IH (Forall_inv_tail Hacyc)).
Defined.

Inductive completion := Complete | FuelExhausted.
Record report := {
  report_completion : completion;
  report_steps : nat;
  report_answers : list (list (nat * term));
  report_execution : execution
}.
Inductive response := InputRejected : input_error -> response | Evaluated : report -> response.

Definition run_validated (G : env) (counter : nat) (query : list nat) (g : goal)
  (Hvalid : valid_request G counter query g) (fuel : nat) (capture : bool) : report.
Proof.
  destruct Hvalid as [Henv [Hgoal Hquery]].
    pose (Hok := initial_expr_ok G counter g Hgoal).
    pose (result := execute G Henv capture fuel (initial_expr counter g) Hok).
    assert (Hanswers : Forall (fun s => acyclic_sub (st_sub s))
      (observed_answers (execution_final result))).
    { unfold result. rewrite execute_final. eapply observed_answers_acyclic.
      eapply multi_ok; [apply run_steps_multi|exact Henv|exact Hok]. }
    exact {| report_completion := if terminalb (execution_final result) then Complete else FuelExhausted;
      report_steps := execution_steps result;
      report_answers := project_answers query (observed_answers (execution_final result)) Hanswers;
      report_execution := result |}.
Defined.

Definition checked_run (G : env) (counter : nat) (query : list nat) (g : goal)
  (fuel : nat) (capture : bool) : response :=
  match validate_request G counter query g with
  | Rejected err => InputRejected err
  | Accepted Hvalid => Evaluated (run_validated G counter query g Hvalid fuel capture)
  end.

Theorem checked_run_accepts_only_valid : forall G counter query g fuel capture r,
  checked_run G counter query g fuel capture = Evaluated r ->
  valid_request G counter query g.
Proof.
  intros G counter query g fuel capture r H.
  unfold checked_run in H. destruct (validate_request G counter query g);
    [discriminate|assumption].
Qed.

Theorem checked_run_accepts_valid : forall G counter query g fuel capture,
  valid_request G counter query g -> exists r,
  checked_run G counter query g fuel capture = Evaluated r.
Proof.
  intros G counter query g fuel capture Hv. unfold checked_run.
  destruct (validate_request G counter query g) eqn:E.
  - exfalso. exact (validate_request_complete G counter query g i Hv E).
  - eexists. reflexivity.
Qed.

Lemma run_validated_final : forall G counter query g Hvalid fuel capture,
  execution_final (report_execution (run_validated G counter query g Hvalid fuel capture)) =
  run_steps G (proj1 Hvalid) fuel (initial_expr counter g)
    (initial_expr_ok G counter g (proj1 (proj2 Hvalid))).
Proof.
  intros G counter query g [Henv [Hgoal Hquery]] fuel capture.
  unfold run_validated. simpl.
  replace (proj1 (conj Henv (conj Hgoal Hquery))) with Henv by apply proof_irrelevance.
  replace (proj1 (proj2 (conj Henv (conj Hgoal Hquery)))) with Hgoal by apply proof_irrelevance.
  apply execute_final.
Qed.

Theorem run_validated_status : forall G counter query g Hv fuel capture,
  report_completion (run_validated G counter query g Hv fuel capture) = Complete <->
  is_value (execution_final (report_execution (run_validated G counter query g Hv fuel capture))).
Proof.
  intros G counter query g [Henv [Hgoal Hquery]] fuel capture.
  unfold run_validated. simpl.
  rewrite <- terminalb_spec.
  destruct (terminalb (execution_final (execute G Henv capture fuel (initial_expr counter g)
    (initial_expr_ok G counter g Hgoal)))); intuition discriminate.
Qed.

Definition projected_answer (query : list nat) (s : state) (bindings : list (nat * term)) : Prop :=
  Forall2 (fun x binding => fst binding = x /\ ApplySub (st_sub s) (tvar x) (snd binding)) query bindings.

Lemma project_answer_spec : forall query s Hacyc,
  projected_answer query s (project_answer query s Hacyc).
Proof.
  intros query s Hacyc. unfold projected_answer,project_answer. induction query; simpl.
  - constructor.
  - constructor; [|exact IHquery]. split; [reflexivity|]. apply (proj2 (apply_sub_spec (st_sub s) Hacyc (tvar a) _)). reflexivity.
Qed.
Lemma project_answers_spec : forall query answers Hacyc,
  Forall2 (projected_answer query) answers (project_answers query answers Hacyc).
Proof.
  intros query answers. induction answers; intro Hacyc; simpl.
  - constructor.
  - constructor; [apply project_answer_spec|apply IHanswers].
Qed.

Theorem run_validated_projection : forall G counter query g Hv fuel capture,
  Forall2 (projected_answer query)
    (observed_answers (execution_final (report_execution (run_validated G counter query g Hv fuel capture))))
    (report_answers (run_validated G counter query g Hv fuel capture)).
Proof.
  intros G counter query g [Henv [Hgoal Hquery]] fuel capture.
  unfold run_validated. simpl. apply project_answers_spec.
Qed.

Theorem run_validated_soundness : forall G counter query g Hv fuel capture answer rho,
  In answer (observed_answers
    (execution_final (report_execution (run_validated G counter query g Hv fuel capture)))) ->
  represents query answer rho -> solution G query g rho.
Proof.
  intros G counter query g Hv fuel capture answer rho Hin Hrepr.
  rewrite run_validated_final in Hin.
  eapply executable_search_soundness; eassumption.
Qed.

Theorem run_validated_completeness : forall G counter query g Hv capture rho,
  solution G query g rho -> exists fuel answer,
  In answer (observed_answers
    (execution_final (report_execution (run_validated G counter query g Hv fuel capture)))) /\
  represents query answer rho.
Proof.
  intros G counter query g Hv capture rho Hsolution.
  destruct (proj1 (source_solution_iff_runner_answer G (proj1 Hv) counter query g
    (proj1 (proj2 Hv)) (proj2 (proj2 Hv)) rho) Hsolution) as [fuel [answer [Hin Hr]]].
  exists fuel,answer. rewrite run_validated_final. split; assumption.
Qed.

Theorem run_validated_complete_exhaustive : forall G counter query g Hv fuel capture,
  report_completion (run_validated G counter query g Hv fuel capture) = Complete ->
  forall rho, solution G query g rho -> exists answer,
    In answer (observed_answers
      (execution_final (report_execution (run_validated G counter query g Hv fuel capture)))) /\
    represents query answer rho.
Proof.
  intros G counter query g Hv fuel capture Hcomplete rho Hsolution.
  eapply terminated_search_exhaustive.
  - exact (proj1 Hv).
  - exact (proj1 (proj2 Hv)).
  - exact (proj2 (proj2 Hv)).
  - rewrite run_validated_final. apply run_steps_multi.
  - apply (proj1 (run_validated_status G counter query g Hv fuel capture)). exact Hcomplete.
  - exact Hsolution.
Qed.

Lemma execute_early_stop : forall G Henv capture fuel e Hok,
  execution_steps (execute G Henv capture fuel e Hok) < fuel ->
  is_value (execution_final (execute G Henv capture fuel e Hok)).
Proof.
  intros G Henv capture fuel. induction fuel; intros e Hok Hlt; cbn [execute execution_steps] in Hlt; [lia|].
  cbn [execute]. destruct (next_step_checked G Henv e Hok) as [[next [Hs Hv]]|] eqn:E;
    simpl in *.
  - apply IHfuel. lia.
  - apply next_step_none_value with (Hok := Hok).
    apply next_step_checked_none in E. exact E.
Qed.

Theorem run_validated_exhausted : forall G counter query g Hv fuel capture,
  report_completion (run_validated G counter query g Hv fuel capture) = FuelExhausted ->
  report_steps (run_validated G counter query g Hv fuel capture) = fuel.
Proof.
  intros G counter query g [Henv [Hgoal Hquery]] fuel capture.
  unfold run_validated. simpl. intro Hstatus.
  pose proof (execute_steps_bound G Henv capture fuel (initial_expr counter g)
    (initial_expr_ok G counter g Hgoal)) as Hle.
  destruct (Nat.lt_ge_cases (execution_steps (execute G Henv capture fuel
    (initial_expr counter g) (initial_expr_ok G counter g Hgoal))) fuel) as [Hlt|Hge]; [|lia].
  pose proof (execute_early_stop G Henv capture fuel (initial_expr counter g)
    (initial_expr_ok G counter g Hgoal) Hlt) as Hvalue.
  apply terminalb_spec in Hvalue. rewrite Hvalue in Hstatus. discriminate.
Qed.

Lemma last_nonempty_default : forall {A : Type} (x : A) xs a b,
  last (x::xs) a = last (x::xs) b.
Proof. intros A x xs. revert x. induction xs; intros x da db; simpl; [reflexivity|apply IHxs]. Qed.

Theorem execute_trace_last : forall G Henv fuel e Hok,
  last (execution_trace (execute G Henv true fuel e Hok)) e =
    execution_final (execute G Henv true fuel e Hok).
Proof.
  intros G Henv fuel. induction fuel; intros e Hok; cbn [execute]; [reflexivity|].
  destruct (next_step_checked G Henv e Hok) as [[next [Hs Hv]]|]; simpl; [|reflexivity].
  pose proof (execute_trace G Henv fuel next Hv) as [tail [Ht _]].
  pose proof (IHfuel next Hv) as IH. rewrite Ht in *. simpl.
  change (last (next::tail) e = execution_final (execute G Henv true fuel next Hv)). rewrite (last_nonempty_default next tail e next). exact IH.
Qed.

Theorem checked_run_refines : forall G counter query g fuel capture r,
  checked_run G counter query g fuel capture = Evaluated r ->
  exists Hv : valid_request G counter query g,
    r = run_validated G counter query g Hv fuel capture.
Proof.
  intros G counter query g fuel capture r Hrun. unfold checked_run in Hrun.
  destruct (validate_request G counter query g) as [err|Hv]; [discriminate|].
  inversion Hrun; subst. exists Hv. reflexivity.
Qed.

Theorem checked_run_rejects_exactly_invalid : forall G counter query g fuel capture,
  (exists err, checked_run G counter query g fuel capture = InputRejected err) <->
  ~ valid_request G counter query g.
Proof.
  intros G counter query g fuel capture. split.
  - intros [err Hreject] Hv.
    destruct (checked_run_accepts_valid G counter query g fuel capture Hv) as [r Haccept].
    rewrite Haccept in Hreject. discriminate.
  - intro Hinvalid. unfold checked_run.
    destruct (validate_request G counter query g) as [err|Hv].
    + exists err. reflexivity.
    + contradiction.
Qed.
