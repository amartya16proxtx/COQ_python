From Cdcl Require Import Lib Syntax Lit.

Definition id {A} (x : A) : A := x.

Definition comp {A B C} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).

Notation "g >>> f" := (comp g f) (at level 40, left associativity).

Lemma id_comp {A B} (f : A -> B) : id >>> f = f.
Proof.
  reflexivity.
Qed.
