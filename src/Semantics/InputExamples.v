From Stdlib Require Import List.
From MkRedex.Language Require Import Terms Goals.
From MkRedex.Semantics Require Import Input.
Import ListNotations.

Example rejects_unknown_relation :
  validate_request [] 0 [] (grelcall 0 []) = Rejected InvalidGoal.
Proof. reflexivity. Qed.
Example rejects_wrong_arity :
  validate_request [(1,gsucc)] 0 [] (grelcall 0 []) = Rejected InvalidGoal.
Proof. reflexivity. Qed.
Example rejects_unallocated_query :
  validate_request [] 0 [0] gsucc = Rejected InvalidQuery.
Proof. reflexivity. Qed.
Example rejects_bad_environment :
  validate_request [(0,grelcall 1 [])] 0 [] gsucc = Rejected InvalidEnvironment.
Proof. reflexivity. Qed.
Example rejects_raw_variable_under_fresh :
  validate_request [] 0 [] (gfresh 1 (gunify (tvar 0) tnil)) = Rejected InvalidGoal.
Proof. reflexivity. Qed.
