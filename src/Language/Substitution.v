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

Fixpoint unify_f (fuel : nat) (t1 t2 : term) (s : sub) : option sub :=
  match fuel with
  | 0 => None
  | S f =>
      let a := walk t1 s in
      let b := walk t2 s in
      match a, b with
      | tvar x, tvar y => if Nat.eqb x y then Some s else Some ((x, b) :: s)
      | tvar x, _ => if occurs x b then None else Some ((x, b) :: s)
      | _, tvar y => if occurs y a then None else Some ((y, a) :: s)
      | tcons a1 a2, tcons b1 b2 =>
          match unify_f f a1 b1 s with
          | Some s1 => unify_f f a2 b2 s1
          | None => None
          end
      | _, _ => if term_eqb a b then Some s else None
      end
  end.

Definition unify (t1 t2 : term) (s : sub) : option sub :=
  unify_f (S (tsize t1 + tsize t2 + List.length s)) t1 t2 s.

Record state : Type := mkstate {
  st_sub : sub;
  st_cnt : nat
}.
