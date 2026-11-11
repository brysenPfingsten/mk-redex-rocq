From MkRedex.Language Require Import WellFormed WellFormedProperties Terms Goals Environments.
From Stdlib Require Import List Arith.
Import ListNotations.
Set Default Goal Selector "!".

Fixpoint forall_dec {A : Type} (P : A -> Prop)
  (dec : forall x, {P x}+{~P x}) (xs : list A) : {Forall P xs}+{~Forall P xs}.
Proof.
  destruct xs as [|x xs]; [left; constructor|].
  destruct (dec x) as [Hx|Hx]; [|right; intro H; inversion H; contradiction].
  destruct (forall_dec A P dec xs) as [Hs|Hs].
  - left. constructor; assumption.
  - right. intro H. inversion H; contradiction.
Defined.

Definition ok_term_dec : forall d c t, {ok_term d c t}+{~ok_term d c t}.
Proof.
  intros d c t. induction t; simpl; try (left; exact I).
  - apply lt_dec.
  - apply lt_dec.
  - destruct IHt1, IHt2; [left|right|right|right]; tauto.
Defined.

Fixpoint ok_goal_dec (G : env) (d c : nat) (g : goal)
  : {ok_goal G d c g}+{~ok_goal G d c g}.
Proof.
  destruct g; simpl.
  - left. exact I.
  - destruct (ok_term_dec d c t), (ok_term_dec d c t0);
      [left|right|right|right]; tauto.
  - destruct (nth_error G n) as [[arity body]|]; [|right; tauto].
    destruct (Nat.eq_dec (length l) arity),
      (forall_dec (ok_term d c) (ok_term_dec d c) l);
      [left|right|right|right]; tauto.
  - destruct (ok_goal_dec G d c g1), (ok_goal_dec G d c g2);
      [left|right|right|right]; tauto.
  - destruct (ok_goal_dec G d c g1), (ok_goal_dec G d c g2);
      [left|right|right|right]; tauto.
  - apply (ok_goal_dec G (d+n) c g).
Defined.

Definition ok_env_dec (G : env) : {ok_env G}+{~ok_env G}.
Proof.
  destruct (forall_dec (fun '(n,g) => ok_goal G n 0 g)
    (fun '(n,g) => ok_goal_dec G n 0 g) G) as [Hdefs|Hdefs].
  - left. intros r n body Hlook.
    rewrite Forall_forall in Hdefs. apply (Hdefs (n,body)). eapply nth_error_In; eassumption.
  - right. intro Henv. apply Hdefs. apply Forall_forall.
    intros [n body] Hin. apply In_nth_error in Hin. destruct Hin as [r Hr].
    exact (Henv r n body Hr).
Defined.

Definition valid_request (G : env) (counter : nat) (query : list nat) (g : goal) : Prop :=
  ok_env G /\ ok_goal G 0 counter g /\ Forall (fun x => x < counter) query.

Inductive input_error := InvalidEnvironment | InvalidGoal | InvalidQuery.
Inductive validation (P : Prop) : Type :=
| Rejected : input_error -> validation P
| Accepted : P -> validation P.
Arguments Rejected {P} _.
Arguments Accepted {P} _.

Definition validate_request (G : env) (counter : nat) (query : list nat) (g : goal)
  : validation (valid_request G counter query g).
Proof.
  destruct (ok_env_dec G) as [Henv|Henv]; [|exact (Rejected InvalidEnvironment)].
  destruct (ok_goal_dec G 0 counter g) as [Hgoal|Hgoal]; [|exact (Rejected InvalidGoal)].
  destruct (forall_dec (fun x => x < counter) (fun x => lt_dec x counter) query)
    as [Hquery|Hquery]; [|exact (Rejected InvalidQuery)].
  exact (Accepted (conj Henv (conj Hgoal Hquery))).
Defined.

Theorem validate_request_complete : forall G counter query g err,
  valid_request G counter query g -> validate_request G counter query g <> Rejected err.
Proof.
  intros G counter query g err [Henv [Hgoal Hquery]].
  unfold validate_request.
  destruct (ok_env_dec G); [|contradiction].
  destruct (ok_goal_dec G 0 counter g); [|contradiction].
  destruct (forall_dec (fun x => x < counter) (fun x => lt_dec x counter) query);
    [discriminate|contradiction].
Qed.

Theorem validate_request_sound : forall G counter query g H,
  validate_request G counter query g = Accepted H -> valid_request G counter query g.
Proof. intros G counter query g H _. exact H. Qed.
