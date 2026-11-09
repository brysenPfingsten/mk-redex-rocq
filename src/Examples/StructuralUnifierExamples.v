From Stdlib Require Import String.
From MkRedex.Execution Require Import StructuralUnifier.
Set Default Goal Selector "!".

(** Observe the reduced scope and both substituted inputs. This tests the
    result's interpretation, not just that the algorithm reports success. *)
Definition observe {m} (s t : Term m) : option {n : nat & (Term n * Term n)%type} :=
  match mgu s t with
  | None => None
  | Some (existT _ n sigma) =>
      Some (existT _ n (apply (sub sigma) s, apply (sub sigma) t))
  end.

Example bind_to_constant :
  observe (var (@f0 0)) (atom (number 7)) =
    Some (existT _ 0 (atom (number 7), atom (number 7))).
Proof. reflexivity. Qed.

Example occurs_failure :
  mgu (var (@f0 0)) (fork (var f0) leaf) = None.
Proof. reflexivity. Qed.

Example constructor_clash :
  @mgu 0 leaf (atom (number 0)) = None.
Proof. reflexivity. Qed.

Example same_constructor_different_values :
  @mgu 0 (atom (number 1)) (atom (number 2)) = None.
Proof. reflexivity. Qed.

Example renumbering_and_postponement :
  observe (fork (var (@f0 1)) (var f0)) (fork leaf (var (fs f0))) =
    Some (existT _ 0 (fork leaf leaf,fork leaf leaf)).
Proof. reflexivity. Qed.

(** Removing the middle variable shifts the last variable down one slot.
    The untouched original variable remains free in the reduced scope. *)
Example middle_variable_elimination :
  observe (var (@fs 2 f0)) (var (fs (fs f0))) =
    Some (existT _ 2 (var (fs f0), var (fs f0))).
Proof. reflexivity. Qed.

Example identical_variables_do_not_eliminate :
  observe (var (@f0 1)) (var f0) =
    Some (existT _ 2 (var f0,var f0)).
Proof. reflexivity. Qed.

Example distinct_variables_eliminate_once :
  observe (var (@f0 1)) (var (fs f0)) =
    Some (existT _ 1 (var f0,var f0)).
Proof. reflexivity. Qed.

Example postponed_occurs_failure :
  mgu (fork (var (@f0 1)) (var (fs f0)))
      (fork (var (fs f0)) (fork (var f0) leaf)) = None.
Proof. reflexivity. Qed.

Example rigid_symmetry :
  observe (atom (symbol "cat")) (var (@f0 0)) =
    Some (existT _ 0 (atom (symbol "cat"),atom (symbol "cat"))).
Proof. reflexivity. Qed.

Example preserve_distinct_literal_tags :
  @mgu 0 (atom (symbol "cat")) (atom (text "cat")) = None.
Proof. reflexivity. Qed.

Example closed_pair :
  @observe 0 (fork (atom (boolean true)) leaf)
             (fork (atom (boolean true)) leaf) =
    Some (existT _ 0 (fork (atom (boolean true)) leaf,
                     fork (atom (boolean true)) leaf)).
Proof. reflexivity. Qed.

Example thinning_skips_middle :
  thin 2 (fs f0) (fs f0) = fs (fs f0).
Proof. reflexivity. Qed.

Example thickening_rejects_deleted_variable :
  thick 2 (fs f0) (fs f0) = None.
Proof. reflexivity. Qed.

Example empty_accumulator_composition :
  append (@anil 1) 0 (asnoc anil leaf f0) = asnoc anil leaf f0.
Proof. reflexivity. Qed.

Compute observe (fork (var (@f0 1)) (var f0)) (fork leaf (var (fs f0))).
Compute mgu (var (@f0 0)) (fork (var f0) leaf).
