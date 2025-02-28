From Cdcl Require Import Lib Syntax Lit.

Inductive t (A: Type) :=
| mk : A -> LitSet.t -> t A.

Definition eval_and_list' {A: Type} (l: list (t A)) : bool :=
  fold_left (fun b t => andb b (LitSet.is_empty (snd t))) l true.

Theorem eval_and_list_rev : forall l : list (t bool), eval_and_list' (rev l) <-> eval_and_list' l.
Proof.
  induction l.
  - simpl. tauto.
  - simpl. rewrite eval_and_list_app. simpl. tauto.
Qed.

Definition eval_and_list_app {A: Type} (l1 l2: list (t A)) : eval_and_list' (l1 ++ l2) <-> (eval_and_list' l1 && eval_and_list' l2).
Proof.
  induction l1.
  - simpl. tauto.
  - simpl. rewrite IHl1. simpl. tauto.
Qed.

Definition mk_elt {A: Type} (e:A) : t A := mk e LitSet.empty.