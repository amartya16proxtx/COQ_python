From Cdcl Require Import Lib Syntax Lit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition id {A} (x : A) : A := x.

Definition compose {A B C} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).
Notation "g >>> f" := (compose g f) (at level 40, left associativity).

Lemma id_comp {A B} (f : A -> B) : id >>> f = f.
Proof.
  reflexivity.
Qed.
