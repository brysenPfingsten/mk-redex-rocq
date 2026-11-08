From Stdlib Require Import List String Arith Lia.
From MkRedex.Language Require Import Terms Goals Substitution Environments.
Import ListNotations.
Set Default Goal Selector "!".

(** Ground values deliberately have neither logic variables nor parameters. *)
Inductive ground : Type :=
| gsym : string -> ground
| gstr : string -> ground
| gnat : nat -> ground
| gbool : bool -> ground
| gnil : ground
| gcons : ground -> ground -> ground.

Definition valuation := nat -> ground.

(** Missing lexical parameters are rejected rather than assigned a default. *)
Fixpoint eval_term (rho : valuation) (beta : list ground) (t : term)
  : option ground :=
  match t with
  | tvar x => Some (rho x)
  | tpar i => nth_error beta i
  | tsym s => Some (gsym s)
  | tstr s => Some (gstr s)
  | tnat n => Some (gnat n)
  | tbool b => Some (gbool b)
  | tnil => Some gnil
  | tcons a b =>
      match eval_term rho beta a, eval_term rho beta b with
      | Some x, Some y => Some (gcons x y)
      | _, _ => None
      end
  end.

Fixpoint eval_terms (rho : valuation) (beta : list ground) (ts : list term)
  : option (list ground) :=
  match ts with
  | [] => Some []
  | t :: ts =>
      match eval_term rho beta t, eval_terms rho beta ts with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

(** Finite derivations give recursive definitions their least interpretation.
    Relation bodies receive a new parameter block; fresh extends the current
    block. This definition mentions no runtime trees or scheduling. *)
Inductive satisfies (G : env) (rho : valuation) : list ground -> goal -> Prop :=
| Sat_success : forall beta, satisfies G rho beta gsucc
| Sat_unify : forall beta t u v,
    eval_term rho beta t = Some v ->
    eval_term rho beta u = Some v ->
    satisfies G rho beta (gunify t u)
| Sat_disj_left : forall beta a b,
    satisfies G rho beta a -> satisfies G rho beta (gdisj a b)
| Sat_disj_right : forall beta a b,
    satisfies G rho beta b -> satisfies G rho beta (gdisj a b)
| Sat_conj : forall beta a b,
    satisfies G rho beta a -> satisfies G rho beta b ->
    satisfies G rho beta (gconj a b)
| Sat_fresh : forall beta k body values,
    List.length values = k ->
    satisfies G rho (values ++ beta) body ->
    satisfies G rho beta (gfresh k body)
| Sat_call : forall beta r args arity body values,
    nth_error G r = Some (arity, body) ->
    List.length args = arity ->
    eval_terms rho beta args = Some values ->
    satisfies G rho values body ->
    satisfies G rho beta (grelcall r args).

(** A ground valuation solves every visible binding of the substitution.
    Lookup, rather than list membership, matches operational shadowing. *)
Definition satisfies_sub (rho : valuation) (s : sub) : Prop :=
  forall x t, lookup x s = Some t -> eval_term rho [] t = Some (rho x).

Definition agrees_on (query : list nat) (rho sigma : valuation) : Prop :=
  forall x, In x query -> rho x = sigma x.

(** Existentially hide allocations outside the explicit original query. *)
Definition represents (query : list nat) (answer : state) (rho : valuation)
  : Prop :=
  exists sigma, agrees_on query sigma rho /\ satisfies_sub sigma (st_sub answer).

Definition solution (G : env) (query : list nat) (g : goal) (rho : valuation)
  : Prop :=
  exists sigma, agrees_on query sigma rho /\ satisfies G sigma [] g.

Lemma satisfies_sub_nil : forall rho, satisfies_sub rho [].
Proof. intros rho x t H. discriminate H. Qed.

Lemma agrees_on_refl : forall query rho, agrees_on query rho rho.
Proof. intros query rho x H. reflexivity. Qed.

Lemma agrees_on_sym : forall query rho sigma,
  agrees_on query rho sigma -> agrees_on query sigma rho.
Proof. intros query rho sigma H x Hin. symmetry. apply H. exact Hin. Qed.

Lemma represents_empty : forall query rho c,
  represents query (mkstate [] c) rho.
Proof.
  intros query rho c. exists rho. split.
  - apply agrees_on_refl.
  - apply satisfies_sub_nil.
Qed.

Lemma eval_terms_length : forall rho beta ts vs,
  eval_terms rho beta ts = Some vs -> List.length ts = List.length vs.
Proof.
  intros rho beta ts. induction ts as [|t ts IH]; intros vs H; simpl in H.
  - inversion H. reflexivity.
  - destruct (eval_term rho beta t); [|discriminate].
    destruct (eval_terms rho beta ts) eqn:E; [|discriminate].
    inversion H; subst. simpl. f_equal. apply IH. reflexivity.
Qed.

Lemma Walk_denotation : forall s t w,
  Walk s t w -> forall rho, satisfies_sub rho s ->
  eval_term rho [] t = eval_term rho [] w.
Proof.
  intros s t w H. induction H; intros rho Hs.
  - reflexivity.
  - simpl. rewrite <- IHWalk by exact Hs. symmetry. exact (Hs x u H).
  - reflexivity.
Qed.

Lemma ApplySub_denotation : forall s t u,
  ApplySub s t u -> forall rho, satisfies_sub rho s ->
  eval_term rho [] t = eval_term rho [] u.
Proof.
  intros s t u H. induction H; intros rho Hs.
  - reflexivity.
  - simpl. rewrite <- IHApplySub by exact Hs. symmetry. exact (Hs x u H).
  - simpl. rewrite IHApplySub1, IHApplySub2 by exact Hs. reflexivity.
  - reflexivity.
Qed.

Lemma satisfies_sub_bind : forall rho s x t,
  satisfies_sub rho s -> eval_term rho [] t = Some (rho x) ->
  satisfies_sub rho ((x,t) :: s).
Proof.
  intros rho s x t Hs Heq y u Hlook. simpl in Hlook.
  destruct (Nat.eqb_spec y x) as [->|Hneq].
  - inversion Hlook; subst. exact Heq.
  - exact (Hs y u Hlook).
Qed.

Example fresh_reflexive : forall G rho,
  satisfies G rho [] (gfresh 1 (gunify (tpar 0) (tpar 0))).
Proof.
  intros G rho. eapply Sat_fresh with (values := [gnil]).
  - reflexivity.
  - eapply Sat_unify; reflexivity.
Qed.
