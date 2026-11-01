From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import MkRedex.Language.Terms.
Set Default Goal Selector "!".

Definition sub := list (nat * term).

Fixpoint lookup (x : nat) (s : sub) : option term :=
  match s with
  | [] => None
  | (y, t) :: s' => if Nat.eqb x y then Some t else lookup x s'
  end.

Fixpoint walk_f (fuel : nat) (t : term) (s : sub) : term :=
  match fuel with
  | 0 => t
  | S f =>
      match t with
      | tvar x => match lookup x s with
                  | Some u => walk_f f u s
                  | None => t
                  end
      | _ => t
      end
  end.

Definition walk (t : term) (s : sub) : term := walk_f (S (List.length s)) t s.

Fixpoint occurs (x : nat) (t : term) : bool :=
  match t with
  | tvar y => Nat.eqb x y
  | tcons a b => orb (occurs x a) (occurs x b)
  | _ => false
  end.

(** [apply_sub t s] walks [t] under [s] and recurses into [tcons] to
    eliminate all logic variables.  Fuel bounds the recursion depth. *)
Fixpoint apply_sub_f (fuel : nat) (t : term) (s : sub) : term :=
  match fuel with
  | 0 => walk t s
  | S f =>
      match walk t s with
      | tcons a b => tcons (apply_sub_f f a s) (apply_sub_f f b s)
      | u => u
      end
  end.

Definition apply_sub (t : term) (s : sub) : term :=
  apply_sub_f (List.length s) t s.

(** A substitution is acyclic if there exists a variable ranking that strictly
    decreases along every binding, guaranteeing that [walk] terminates before
    exhausting its fuel. *)
Definition acyclic_sub (s : sub) : Prop :=
  exists rank : nat -> nat,
    forall x t, lookup x s = Some t ->
    forall y, occurs y t = true -> rank y < rank x.

Record state : Type := mkstate {
  st_sub : sub;
  st_cnt : nat
}.

(* ================================================================== *)
(*  Unify — inductive unification relation                             *)
(* ================================================================== *)

(** [Unify t1 t2 s r] means: unifying [t1] and [t2] under substitution [s]
    yields result [r].  Each constructor first fixes the walked forms via
    [walk t1 s] and [walk t2 s], then case-splits on their shapes.

    A term is called "rigid" if it is neither a [tvar] nor a [tcons]. *)
Inductive Unify : term -> term -> sub -> option sub -> Prop :=

  (** Both walk to the same variable: identity. *)
  | U_var_same : forall t1 t2 s x,
      walk t1 s = tvar x ->
      walk t2 s = tvar x ->
      Unify t1 t2 s (Some s)

  (** Left walks to [x], right walks to something other than [tvar x],
      no occurs check fails: bind [x] to the right walk result. *)
  | U_var_bind : forall t1 t2 s x u,
      walk t1 s = tvar x ->
      walk t2 s = u ->
      u <> tvar x ->
      occurs x u = false ->
      Unify t1 t2 s (Some ((x, u) :: s))

  (** Left walks to [x], right walks to something other than [tvar x],
      occurs check fails: fail. *)
  | U_var_fail : forall t1 t2 s x u,
      walk t1 s = tvar x ->
      walk t2 s = u ->
      u <> tvar x ->
      occurs x u = true ->
      Unify t1 t2 s None

  (** Right walks to [y], left walks to a non-variable,
      no occurs check fails: bind [y] to the left walk result. *)
  | U_sym_bind : forall t1 t2 s y u,
      walk t1 s = u ->
      walk t2 s = tvar y ->
      (forall z, u <> tvar z) ->
      occurs y u = false ->
      Unify t1 t2 s (Some ((y, u) :: s))

  (** Right walks to [y], left walks to a non-variable,
      occurs check fails: fail. *)
  | U_sym_fail : forall t1 t2 s y u,
      walk t1 s = u ->
      walk t2 s = tvar y ->
      (forall z, u <> tvar z) ->
      occurs y u = true ->
      Unify t1 t2 s None

  (** Both walk to [tcons]: unify first components; if that succeeds,
      continue with second components in the extended substitution. *)
  | U_cons_ok : forall t1 t2 s a1 a2 b1 b2 s1 r,
      walk t1 s = tcons a1 a2 ->
      walk t2 s = tcons b1 b2 ->
      Unify a1 b1 s (Some s1) ->
      Unify a2 b2 s1 r ->
      Unify t1 t2 s r

  (** Both walk to [tcons]: first component fails immediately. *)
  | U_cons_fail : forall t1 t2 s a1 a2 b1 b2,
      walk t1 s = tcons a1 a2 ->
      walk t2 s = tcons b1 b2 ->
      Unify a1 b1 s None ->
      Unify t1 t2 s None

  (** Left walks to [tcons], right walks to a rigid term: clash. *)
  | U_cons_clash_r : forall t1 t2 s a1 a2 v,
      walk t1 s = tcons a1 a2 ->
      walk t2 s = v ->
      (forall x, v <> tvar x) ->
      (forall c1 c2, v <> tcons c1 c2) ->
      Unify t1 t2 s None

  (** Right walks to [tcons], left walks to a rigid term: clash. *)
  | U_cons_clash_l : forall t1 t2 s u b1 b2,
      walk t1 s = u ->
      walk t2 s = tcons b1 b2 ->
      (forall x, u <> tvar x) ->
      (forall c1 c2, u <> tcons c1 c2) ->
      Unify t1 t2 s None

  (** Both walk to the same rigid term: succeed. *)
  | U_rigid_eq : forall t1 t2 s u,
      walk t1 s = u ->
      walk t2 s = u ->
      (forall x, u <> tvar x) ->
      (forall a b, u <> tcons a b) ->
      Unify t1 t2 s (Some s)

  (** Both walk to different rigid terms: clash. *)
  | U_rigid_neq : forall t1 t2 s u v,
      walk t1 s = u ->
      walk t2 s = v ->
      u <> v ->
      (forall x, u <> tvar x) ->
      (forall x, v <> tvar x) ->
      (forall a b, u <> tcons a b) ->
      (forall a b, v <> tcons a b) ->
      Unify t1 t2 s None.

Hint Constructors Unify : core.

(* ================================================================== *)
(*  Unify properties                                                   *)
(* ================================================================== *)

(** The result of [Unify] is uniquely determined by its inputs. *)
Lemma Unify_functional : forall t1 t2 s r r',
  Unify t1 t2 s r -> Unify t1 t2 s r' -> r = r'.
Proof. 
  intros t1 t2 s r r' H_Unify_r.
  generalize dependent r'.
  induction H_Unify_r; intros r' H_Unify_r'; inversion H_Unify_r';
  try reflexivity; try congruence; subst;
  rewrite H in H1; injection H1 as <- <-;
  rewrite H0 in H2; injection H2 as <- <-.
  - apply IHH_Unify_r1 in H3.
    injection H3 as <-.
    apply IHH_Unify_r2. exact H4.
  - apply IHH_Unify_r1 in H3.
    inversion H3.
  - apply IHH_Unify_r in H3. discriminate.
Qed.
    

(** A successful [Unify] extends the substitution: [s] is a suffix of [s']. *)
Lemma Unify_extends : forall t1 t2 s s',
  Unify t1 t2 s (Some s') -> exists prefix, s' = prefix ++ s.
Proof. Admitted.

  

(** A successful [Unify] on an acyclic substitution yields an acyclic
    substitution. *)
Lemma Unify_acyclic : forall t1 t2 s s',
  acyclic_sub s -> Unify t1 t2 s (Some s') -> acyclic_sub s'.
Proof. Admitted.

(** Soundness: if [Unify t1 t2 s (Some s')], then [s'] unifies [t1] and [t2]
    under deep application. *)
Lemma Unify_sound : forall t1 t2 s s',
  acyclic_sub s -> Unify t1 t2 s (Some s') ->
  apply_sub t1 s' = apply_sub t2 s'.
Proof. Admitted.
