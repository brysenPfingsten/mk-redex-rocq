From Stdlib Require Import List Arith Lia.
From MkRedex.Language Require Import Terms Substitution Goals Environments Trees Unification.
Import ListNotations.
Set Default Goal Selector "!".

(** [d] is the number of lexical parameters in scope: [tpar i] needs [i < d].
    [c] is the next unallocated logic-variable ID: [tvar n] needs [n < c].
    A runtime goal starts at depth zero, [gfresh k] adds [k] inside its body,
    and a relation body starts at the relation's declared arity. *)
Fixpoint ok_term (d c : nat) (t : term) : Prop :=
  match t with
  | tvar n    => n < c
  | tpar i    => i < d
  | tcons a b => ok_term d c a /\ ok_term d c b
  | _         => True
  end.

Fixpoint scoped_sub (c : nat) (s : sub) : Prop :=
  match s with
  | []           => True
  | (n, t) :: s' => n < c /\ ok_term 0 c t /\ scoped_sub c s'
  end.

(** A runtime substitution is both scoped and acyclic. *)
Definition ok_sub (c : nat) (s : sub) : Prop :=
  scoped_sub c s /\ acyclic_sub s.

Fixpoint ok_goal (G : env) (d c : nat) (g : goal) : Prop :=
  match g with
  | gsucc        => True
  | gunify t1 t2 => ok_term d c t1 /\ ok_term d c t2
  | grelcall r ts =>
      match nth_error G r with
      | Some (n, _) => length ts = n /\ Forall (ok_term d c) ts
      | None        => False
      end
  | gdisj g1 g2  => ok_goal G d c g1 /\ ok_goal G d c g2
  | gconj g1 g2  => ok_goal G d c g1 /\ ok_goal G d c g2
  | gfresh k g1  => ok_goal G (d + k) c g1
  end.

Definition ok_env (G : env) : Prop :=
  forall r n b, nth_error G r = Some (n, b) -> ok_goal G n 0 b.

Definition runtime_open_args (c : nat) (args : list term) : Prop :=
  Forall (ok_term 0 c) args.

(** The states appearing anywhere in a tree, including suspended branches. *)
Inductive state_in : tree -> state -> Prop :=
  | SI_tgoal    : forall g s,     state_in (tgoal g s) s
  | SI_tdelay   : forall t s,     state_in t s -> state_in (tdelay t) s
  | SI_tproceed : forall r ts s,  state_in (tproceed r ts s) s
  | SI_tconj    : forall t g s,   state_in t s -> state_in (tconj t g) s
  | SI_tdisjL_l : forall t1 t2 s, state_in t1 s -> state_in (tdisjL t1 t2) s
  | SI_tdisjL_r : forall t1 t2 s, state_in t2 s -> state_in (tdisjL t1 t2) s
  | SI_tdisjR_l : forall t1 t2 s, state_in t1 s -> state_in (tdisjR t1 t2) s
  | SI_tdisjR_r : forall t1 t2 s, state_in t2 s -> state_in (tdisjR t1 t2) s.

Hint Constructors state_in : core.

(** Every node uses its state's allocation counter. A continuation is valid
    for each state in its left subtree; the existential check also validates
    it when that subtree has no states. *)
Fixpoint ok_tree (G : env) (t : tree) : Prop :=
  match t with
  | tfail           => True
  | tgoal g s       => ok_goal G 0 (st_cnt s) g /\ ok_sub (st_cnt s) (st_sub s)
  | tdelay t'       => ok_tree G t'
  | tproceed r ts s =>
      match nth_error G r with
      | Some (n, _) => length ts = n /\
          Forall (ok_term 0 (st_cnt s)) ts /\
          ok_sub (st_cnt s) (st_sub s)
      | None => False
      end
  | tconj t' g      => ok_tree G t' /\
      (exists c, ok_goal G 0 c g) /\
      (forall s, state_in t' s -> ok_goal G 0 (st_cnt s) g)
  | tdisjL t1 t2    => ok_tree G t1 /\ ok_tree G t2
  | tdisjR t1 t2    => ok_tree G t1 /\ ok_tree G t2
  end.

Definition ok_expr (G : env) (e : expr) : Prop :=
  ok_tree G (snd e) /\
  Forall (fun s => ok_sub (st_cnt s) (st_sub s)) (fst e).

Example fresh_binds_parameter_index :
  ok_goal [] 0 0 (gfresh 1 (gunify (tpar 0) tnil)).
Proof. simpl. lia. Qed.

Example fresh_does_not_preallocate_logic_variable :
  ~ ok_goal [] 0 0 (gfresh 1 (gunify (tvar 0) tnil)).
Proof. simpl. lia. Qed.

Example dead_continuation_still_checks_relation :
  ~ ok_tree [] (tconj tfail (grelcall 0 [])).
Proof. simpl. intros [_ [[c Hcall] _]]. exact Hcall. Qed.

Example continuation_uses_its_states_counter :
  ~ ok_tree []
      (tconj (tgoal gsucc (mkstate [] 1)) (gunify (tvar 1) tnil)).
Proof.
  simpl. intros [_ [_ Hcont]].
  specialize (Hcont (mkstate [] 1) (SI_tgoal gsucc (mkstate [] 1))).
  simpl in Hcont. lia.
Qed.
