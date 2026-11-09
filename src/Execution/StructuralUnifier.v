From Stdlib Require Import String Bool Arith.
Set Default Goal Selector "!".

(** McBride-style first-order unification. Every substitution elimination
    reduces the variable index; pair descent reduces the first term. No
    well-founded recursion or proof-indexed computation is used here. *)
Inductive Fin : nat -> Type :=
| f0 : forall {n}, Fin (S n)
| fs : forall {n}, Fin n -> Fin (S n).

Definition fin0_elim {A : Type} (x : Fin 0) : A :=
  match x in Fin k return match k with 0 => A | S _ => unit end with
  | f0 => tt
  | fs _ => tt
  end.

(** A constructive view of a successor-sized finite set. The return clause
    exposes the predecessor index without equality casts or inversion axioms. *)
Definition fin_view {n} (x : Fin (S n)) : option (Fin n) :=
  match x in Fin k return match k with 0 => unit | S j => option (Fin j) end with
  | f0 => None
  | fs y => Some y
  end.

Inductive Rigid : Type :=
| symbol : string -> Rigid
| text : string -> Rigid
| number : nat -> Rigid
| boolean : bool -> Rigid
| empty : Rigid.

Definition rigid_eq_dec : forall a b : Rigid, {a=b}+{a<>b}.
Proof.
  decide equality; try apply string_dec; try apply Nat.eq_dec; try apply Bool.bool_dec.
Defined.

Inductive Term (n : nat) : Type :=
| var : Fin n -> Term n
| atom : Rigid -> Term n
| fork : Term n -> Term n -> Term n.
Arguments var {n} _.
Arguments atom {n} _.
Arguments fork {n} _ _.
Definition leaf {n} : Term n := atom empty.

Definition Sub (m n : nat) := Fin m -> Term n.
Fixpoint apply {m n} (sigma : Sub m n) (t : Term m) : Term n :=
  match t with
  | var x => sigma x
  | atom a => atom a
  | fork a b => fork (apply sigma a) (apply sigma b)
  end.
Definition compose {l m n} (tau : Sub m n) (sigma : Sub l m) : Sub l n :=
  fun x => apply tau (sigma x).

Fixpoint thin (n : nat) : Fin (S n) -> Fin n -> Fin (S n) :=
  match n as k return Fin (S k) -> Fin k -> Fin (S k) with
  | 0 => fun _ y => fin0_elim y
  | S k => fun x y =>
      match fin_view x with
      | None => fs y
      | Some x' => match fin_view y with
          | None => f0
          | Some y' => fs (thin k x' y')
          end
      end
  end.

Fixpoint thick (n : nat) : Fin (S n) -> Fin (S n) -> option (Fin n) :=
  match n as k return Fin (S k) -> Fin (S k) -> option (Fin k) with
  | 0 => fun _ _ => None
  | S k => fun x y =>
      match fin_view x with
      | None => fin_view y
      | Some x' => match fin_view y with
          | None => Some f0
          | Some y' => match thick k x' y' with
              | None => None
              | Some z => Some (fs z)
              end
          end
      end
  end.

Fixpoint check {n} (x : Fin (S n)) (t : Term (S n)) : option (Term n) :=
  match t with
  | var y => match thick n x y with None => None | Some z => Some (var z) end
  | atom a => Some (atom a)
  | fork a b => match check x a, check x b with
      | Some a', Some b' => Some (fork a' b')
      | _, _ => None
      end
  end.

Definition for_ {n} (t : Term n) (x : Fin (S n)) : Sub (S n) n :=
  fun y => match thick n x y with None => t | Some z => var z end.

Inductive AList : nat -> nat -> Type :=
| anil : forall {n}, AList n n
| asnoc : forall {m n}, AList m n -> Term m -> Fin (S m) -> AList (S m) n.
Arguments anil {n}.
Arguments asnoc {m n} _ _ _.

Fixpoint sub {m n} (sigma : AList m n) : Sub m n :=
  match sigma in AList i j return Sub i j with
  | @anil k => fun x => var x
  | @asnoc i j tau t x => compose (sub tau) (for_ t x)
  end.

Fixpoint append {l m} (sigma : AList l m) : forall n, AList m n -> AList l n :=
  match sigma in AList i j return forall n, AList j n -> AList i n with
  | anil => fun _ tau => tau
  | asnoc tail t x => fun n tau => asnoc (append tail n tau) t x
  end.

Definition Acc (m : nat) := { n : nat & AList m n }.

(** The existential target index is carried with a nonempty accumulator.
    Matching on its source index exposes exactly one eliminated variable. *)
Inductive AccView (m : nat) : Type :=
| no_binding : AccView m
| has_binding : forall n, AList m n -> Term m -> Fin (S m) -> AccView m.
Arguments no_binding {m}.
Arguments has_binding {m} n _ _ _.

Definition acc_view {m} (acc : Acc (S m)) : AccView m :=
  match acc with
  | existT _ n sigma =>
      match sigma in AList i j return match i with 0 => unit | S k => AccView k end with
      | @anil k => match k as i return match i with 0 => unit | S j => AccView j end with
          | 0 => tt
          | S j => no_binding
          end
      | @asnoc i j tail t x => has_binding j tail t x
      end
  end.

(** Functional composition order: [acompose rho sigma] applies [sigma]
    first and [rho] second, matching the paper's [rho ++ sigma]. *)
Definition acompose {l m n} (rho : AList m n) (sigma : AList l m) : AList l n :=
  append sigma n rho.

Definition flexFlex {m} (x y : Fin (S m)) : Acc (S m) :=
  match thick m x y with
  | None => existT _ (S m) anil
  | Some z => existT _ m (asnoc anil (var z) x)
  end.

Definition flexRigid {m} (x : Fin (S m)) (t : Term (S m)) : option (Acc (S m)) :=
  match check x t with
  | None => None
  | Some t' => Some (existT _ m (asnoc anil t' x))
  end.

(** The recursive callback operates at the predecessor scope. For an empty
    accumulator solve one flex equation; otherwise postpone it through the
    exposed elimination and reattach that elimination to the smaller result. *)
Definition flex (m : nat)
  (recurse : Term m -> Term m -> Acc m -> option (Acc m))
  (x : Fin (S m)) (t : Term (S m)) (acc : Acc (S m)) : option (Acc (S m)) :=
  match acc_view acc with
  | no_binding =>
      match t with
      | var y => Some (flexFlex x y)
      | _ => flexRigid x t
      end
  | has_binding n sigma r z =>
      match recurse (apply (for_ r z) (var x)) (apply (for_ r z) t) (existT _ n sigma) with
      | None => None
      | Some (existT _ p tau) => Some (existT _ p (asnoc tau r z))
      end
  end.

(** Nested structural recursion: outer descent on [m] handles postponement;
    inner descent on [s] handles both pair-component calls. The accumulator
    returned by the first pair call is not used as a termination argument. *)
Fixpoint amgu (m : nat) {struct m} : Term m -> Term m -> Acc m -> option (Acc m) :=
  match m as k return Term k -> Term k -> Acc k -> option (Acc k) with
  | 0 =>
      fix go (s : Term 0) {struct s} : Term 0 -> Acc 0 -> option (Acc 0) :=
        fun t acc => match s with
        | var x => fin0_elim x
        | atom a => match t with
            | var y => fin0_elim y
            | atom b => if rigid_eq_dec a b then Some acc else None
            | fork _ _ => None
            end
        | fork a b => match t with
            | fork c d => match go a c acc with
                | None => None
                | Some next => go b d next
                end
            | _ => None
            end
        end
  | S k =>
      fix go (s : Term (S k)) {struct s} : Term (S k) -> Acc (S k) -> option (Acc (S k)) :=
        fun t acc => match s with
        | var x => flex k (amgu k) x t acc
        | atom a => match t with
            | var y => flex k (amgu k) y s acc
            | atom b => if rigid_eq_dec a b then Some acc else None
            | fork _ _ => None
            end
        | fork a b => match t with
            | var y => flex k (amgu k) y s acc
            | atom _ => None
            | fork c d => match go a c acc with
                | None => None
                | Some next => go b d next
                end
            end
        end
  end.

Definition mgu {m} (s t : Term m) : option (Acc m) :=
  amgu m s t (existT _ m anil).
