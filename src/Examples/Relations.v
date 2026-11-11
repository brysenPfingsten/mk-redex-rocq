From MkRedex.Language Require Import WellFormed Scoping ScopedUnification Terms Goals Environments.
From Stdlib Require Import List Arith Lia.
From MkRedex.Denotational Require Import Denotation.
From MkRedex.Correctness Require Import Unification.
From MkRedex.Operational Require Import WellFormed.
Import ListNotations.
Set Default Goal Selector "!".

(** Indices in [relation_library]: appendo=0, membero=1, listo=2.
    The comments give parameter names BEFORE and AFTER each fresh block. *)
Definition appendo : goal :=
  (* xs=0, ys=1, zs=2 *)
  gdisj
    (gconj (gunify (tpar 0) tnil) (gunify (tpar 1) (tpar 2)))
    (* h=0, tail=1, rest=2, xs=3, ys=4, zs=5 *)
    (gfresh 3
      (gconj (gunify (tpar 3) (tcons (tpar 0) (tpar 1)))
        (gconj (gunify (tpar 5) (tcons (tpar 0) (tpar 2)))
          (grelcall 0 [tpar 1; tpar 4; tpar 2])))).

Definition membero : goal :=
  (* x=0, xs=1; after fresh: h=0, tail=1, x=2, xs=3 *)
  gfresh 2
    (gconj (gunify (tpar 3) (tcons (tpar 0) (tpar 1)))
      (gdisj (gunify (tpar 2) (tpar 0)) (grelcall 1 [tpar 2; tpar 1]))).

Definition listo : goal :=
  (* xs=0; after fresh: h=0, tail=1, xs=2 *)
  gdisj (gunify (tpar 0) tnil)
    (gfresh 2
      (gconj (gunify (tpar 2) (tcons (tpar 0) (tpar 1)))
        (grelcall 2 [tpar 1]))).

Definition relation_library : env := [(3,appendo); (2,membero); (1,listo)].

Theorem relation_library_closed : ok_env relation_library.
Proof.
  intros r arity body Hlook. destruct r as [|[|[|r]]]; simpl in Hlook.
  all: try solve [destruct r; discriminate].
  all: inversion Hlook; subst; unfold appendo,membero,listo; simpl;
    repeat split; try lia; repeat constructor; simpl; lia.
Qed.

Fixpoint ground_list (xs : list ground) : ground :=
  match xs with [] => gnil | x::xs => gcons x (ground_list xs) end.

Lemma appendo_body_holds : forall xs ys rho,
  satisfies relation_library rho
    [ground_list xs;ground_list ys;ground_list (xs++ys)] appendo.
Proof.
  induction xs as [|x xs IH]; intros ys rho.
  - apply Sat_disj_left. apply Sat_conj; eapply Sat_unify; reflexivity.
  - apply Sat_disj_right.
    eapply Sat_fresh with (values := [x;ground_list xs;ground_list (xs++ys)]); [reflexivity|].
    apply Sat_conj; [eapply Sat_unify; reflexivity|].
    apply Sat_conj; [eapply Sat_unify; reflexivity|].
    eapply Sat_call with (arity := 3) (body := appendo)
      (values := [ground_list xs;ground_list ys;ground_list (xs++ys)]);
      try reflexivity. apply IH.
Qed.

(** A source-level specification example, independent of the stepper. *)
Theorem appendo_concatenates : forall xs ys rho,
  satisfies relation_library rho []
    (grelcall 0 [quote (ground_list xs);quote (ground_list ys);quote (ground_list (xs++ys))]).
Proof.
  intros xs ys rho. eapply Sat_call with (arity := 3) (body := appendo)
    (values := [ground_list xs;ground_list ys;ground_list (xs++ys)]); try reflexivity.
  - simpl. rewrite !quote_eval. reflexivity.
  - apply appendo_body_holds.
Qed.

Lemma membero_body_holds : forall xs x rho,
  In x xs -> satisfies relation_library rho [x;ground_list xs] membero.
Proof.
  induction xs as [|h xs IH]; intros x rho Hin; [contradiction|].
  eapply Sat_fresh with (values := [h;ground_list xs]); [reflexivity|].
  apply Sat_conj; [eapply Sat_unify; reflexivity|].
  destruct Hin as [<-|Hin].
  - apply Sat_disj_left. eapply Sat_unify; reflexivity.
  - apply Sat_disj_right. eapply Sat_call with (arity := 2) (body := membero)
      (values := [x;ground_list xs]); try reflexivity. apply IH. exact Hin.
Qed.

Theorem membero_contains : forall xs x rho,
  In x xs -> satisfies relation_library rho []
    (grelcall 1 [quote x;quote (ground_list xs)]).
Proof.
  intros xs x rho Hin. eapply Sat_call with (arity := 2) (body := membero)
    (values := [x;ground_list xs]); try reflexivity.
  - simpl. rewrite !quote_eval. reflexivity.
  - apply membero_body_holds. exact Hin.
Qed.

Lemma listo_body_holds : forall xs rho,
  satisfies relation_library rho [ground_list xs] listo.
Proof.
  induction xs as [|h xs IH]; intro rho.
  - apply Sat_disj_left. eapply Sat_unify; reflexivity.
  - apply Sat_disj_right. eapply Sat_fresh with (values := [h;ground_list xs]); [reflexivity|].
    apply Sat_conj; [eapply Sat_unify; reflexivity|].
    eapply Sat_call with (arity := 1) (body := listo)
      (values := [ground_list xs]); try reflexivity. apply IH.
Qed.

Theorem listo_accepts_finite_lists : forall xs rho,
  satisfies relation_library rho [] (grelcall 2 [quote (ground_list xs)]).
Proof.
  intros xs rho. eapply Sat_call with (arity := 1) (body := listo)
    (values := [ground_list xs]); try reflexivity.
  - simpl. rewrite quote_eval. reflexivity.
  - apply listo_body_holds.
Qed.
