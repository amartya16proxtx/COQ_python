From Cdcl Require Import Lib Syntax Lit.

Require Import Bool ZifyBool ZArith ZifyUint63 Uint63 Lia List.

Inductive t (A : Type) : Type :=
  | mk : A -> LitSet.t -> t A.

Definition eval_and_list' {A} (l : list (t A)) :=
  forallb (fun e => LitSet.is_empty (projT2 e)) l.

Lemma eval_and_list_rev : forall {A} (l : list (t A)),
  eval_and_list' (rev l) <-> eval_and_list' l.
Proof.
  intros A l.
  induction l.
  - simpl. tauto.
  - rewrite eval_and_list'_app. simpl. tauto.
Qed.

Lemma eval_and_list'_app {A} (l1 l2 : list (t A)) :
  eval_and_list' (l1 ++ l2) <-> eval_and_list' l1 /\ eval_and_list' l2.
Proof.
  unfold eval_and_list'.
  induction l1.
  - simpl. split; intros H; auto.
  - simpl. split; intros H; destruct H; constructor; auto.
Qed.

