From MkRedex.Language Require Import Goals.
From Stdlib Require Import Nat.
Set Default Goal Selector "!".


Definition env := list (nat * goal).
