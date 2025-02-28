From Coq Require Import List.
From Cdcl Require Import Lib Syntax Lit.

Inductive t (A: Type) :=
| mk : A -> LitSet.t -> t A.

Definition mk_elt {A: Type} (e:A) : t A := mk e LitSet.empty.

Fixpoint eval_and_list' {A: Type} (l: list (t A)) : bool :=
  match l with
  | nil => true
  | cons h t => andb (LitSet.is_empty (snd h)) (eval_and_list' t)
  end.

Lemma eval_and_list_app {A: Type} : forall l1 l2 : list (t A),
  eval_and_list' (l1 ++ l2) <-> andb (eval_and_list' l1) (eval_and_list' l2).
Proof.
  induction l1; simpl.
  - tauto.
  - intros. rewrite IHl1. tauto.
Qed.

Theorem eval_and_list_rev : forall {A: Type} (l: list (t A)), 
  eval_and_list' (rev l) <-> eval_and_list' l.
Proof.
  intros A. induction l; simpl.
  - tauto.
  - rewrite eval_and_list_app. simpl. tauto.
Qed.