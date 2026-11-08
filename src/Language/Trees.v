From Stdlib Require Import List.
Import ListNotations.
Set Default Goal Selector "!".

Require Import MkRedex.Language.Terms MkRedex.Language.Substitution MkRedex.Language.Goals.

Inductive tree : Type :=
  | tfail    : tree
  | tgoal    : goal -> state -> tree
  | tdelay   : tree -> tree
  | tproceed : nat -> list term -> state -> tree
  | tconj    : tree -> goal -> tree
  | tdisjL   : tree -> tree -> tree
  | tdisjR   : tree -> tree -> tree.

Definition expr : Type := (list state * tree)%type.

(** Answers already promoted into the list, plus a final top-level success. *)
Definition final_answer (t : tree) : list state :=
  match t with
  | tgoal gsucc s => [s]
  | _ => []
  end.

Definition observed_answers (e : expr) : list state :=
  fst e ++ final_answer (snd e).

Definition is_value (e : expr) : Prop :=
  match snd e with
  | tfail => True
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
