From Stdlib Require Import List Lia.
From MkRedex.Language Require Import Terms Goals Substitution Trees WellFormed.
Import ListNotations.
Set Default Goal Selector "!".

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
