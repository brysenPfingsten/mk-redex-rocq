From Stdlib Require Import List.
Import ListNotations.
Require Import MkRedex.Language.Terms MkRedex.Language.Substitution MkRedex.Language.Goals.
Set Default Goal Selector "!".

Inductive tree : Type :=
  | tfail    : tree
  (*| tans     : state -> tree*)
  | tgoal    : goal -> state -> tree
  | tdelay   : tree -> tree
  | tproceed : nat -> list term -> state -> tree
  | tconj    : tree -> goal -> tree
  | tdisjL   : tree -> tree -> tree
  | tdisjR   : tree -> tree -> tree.

Definition expr : Type := (list state * tree)%type.

Definition is_value (e : expr) : Prop :=
  match snd e with
  | tfail => True
  (*| tans _ => True*)
  | tgoal gsucc _ => True
  | _ => False
  end.

Inductive ctx : Type :=
  | chole  : ctx
  | cdisjL : ctx -> tree -> ctx
  | cdisjR : tree -> ctx -> ctx
  | cconj  : ctx -> goal -> ctx.

Fixpoint plug (E : ctx) (t : tree) : tree :=
  match E with
  | chole => t
  | cdisjL E' s => tdisjL (plug E' t) s
  | cdisjR s E' => tdisjR s (plug E' t)
  | cconj E' g => tconj (plug E' t) g
  end.
