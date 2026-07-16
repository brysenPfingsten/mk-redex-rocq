From Stdlib Require Import List Arith.
Import ListNotations.
From MkRedex.Language Require Import Terms Substitution Goals Trees Environments.
Set Default Goal Selector "!".

Definition head (G : env) (t : tree) : option tree :=
  match t with
  (*Unify*)
  | tgoal (gunify t1 t2) s => 
      match unify t1 t2 (st_sub s) with
      (*UnifySucc*)
      | Some s' => Some (tgoal gsucc (mkstate s' (st_cnt s)))
      (*UnifyFail*)
      | None => Some tfail
      end
  (*DistrDisj*)
  | tgoal (gdisj g1 g2) s => Some (tdisjL (tgoal g1 s) (tgoal g2 s))
  (*DistrConj*)
  | tgoal (gconj g1 g2) s => Some (tconj (tgoal g1 s) g2)
  (*SubstFresh*)
  | tgoal (gfresh k g) s => 
      let c := st_cnt s in
      Some (tgoal (open (map tvar (seq c k)) g)
           (mkstate (st_sub s) (c + k)))
  (*Delay*)
  | tgoal (grelcall r ts) s => Some (tdelay (tproceed r ts s))
  (*Proceed*)
  | tproceed r ts s => 
      match nth_error G r with
      | Some (n, body) => 
          if Nat.eqb (List.length ts) n
          then Some (tgoal (open ts body) s)
          else None
      | None => None
      end
  (*PruneConj*)
  | tconj tfail _ => Some tfail
  (*SuccConj*)
  | tconj (tgoal tsucc s) g => Some (tgoal g s)
  (*LeftAnsConj*)
  | tconj (tdisjL (tgoal tsucc s) t) g => 
      Some (tdisjL (tconj (tgoal tsucc s) g)
                   (tconj t g))
  (*RightAnsConj*)
  | tconj (tdisjR t (tgoal tsucc s)) g =>
      Some (tdisjR (tconj t g)
                   (tconj (tgoal tsucc s) g))
  (*DelayConj*)
  | tconj (tdelay t) g => Some (tdelay (tconj t g))
  (*PruneLeft*)
  | tdisjL tfail r => Some r
  (*PruneRight*)
  | tdisjR r tfail => Some r
  (*AssocLeftLeft*)
  | tdisjL (tdisjL (tgoal tsucc s) r) r2 =>
      Some (tdisjL (tgoal tsucc s) (tdisjL r r2))
  (*AssocLeftRight*)
  | tdisjL (tdisjR r (tgoal tsucc s)) r2 =>
      Some (tdisjR (tdisjL r r2) (tgoal tsucc s))
  (*AssocRightLeft*)
  | tdisjR r2 (tdisjL (tgoal tsucc s) r) =>
      Some (tdisjL (tgoal tsucc s) (tdisjR r2 r))
  (*AssocRightRight*)
  | tdisjR r2 (tdisjR r (tgoal tsucc s)) =>
      Some (tdisjR (tdisjR r2 r) (tgoal tsucc s))
  (*DelayLeft*)
  | tdisjL (tdelay r1) r2 => Some (tdelay (tdisjR r1 r2))
  (*DelayRight*)
  | tdisjR r2 (tdelay r1) => Some (tdelay (tdisjL r2 r1))

  | _ => None
  end.

Definition redex (G : env) (t : tree) : Prop := head G t <> None.


Reserved Notation "G '|=' e '-->' e'" (at level 40, e at level 39).

Inductive step (G : env) : expr -> expr -> Prop :=
  | S_ctx : forall ans E r r',
      head G r = Some r' ->
      G |= (ans, plug E r) --> (ans, plug E r')
  | S_delay : forall ans t,
      G |= (ans, tdelay t) --> (ans, t)
  | S_promoteL : forall ans s t,
      G |= (ans, tdisjL (tgoal gsucc s) t) --> (ans ++ [s], t)
  | S_promoteR : forall ans s t,
      G |= (ans, tdisjR t (tgoal gsucc s)) --> (ans ++ [s], t)

where "G '|=' e '-->' e'" := (step G e e').

Hint Constructors step : core.

Inductive multi (G : env) : expr -> expr -> Prop :=
  | multi_refl : forall e, multi G e e
  | multi_step : forall e1 e2 e3,
      G |= e1 --> e2 -> multi G e2 e3 -> multi G e1 e3.

Hint Constructors multi : core.
