Require Import List.
Import ListNotations.
Require Import LambekSyntax.

Fixpoint pullMultLeft (X: formula) (x: str) :=
  match x with
  | [] => X
  | X' :: x' => pullMultLeft (X ° X') x'
  end.

Fixpoint pullMultRight (X : formula) (x : str) :=
  match x with
  | [] => X
  | (X'::x') => X ° (pullMultRight X' x')
  end.

Lemma pullMultLeftSplit X x A:
  pullMultLeft X (x ++ [A]) = pullMultLeft X x ° A.
Proof.
  generalize dependent X.
  induction x as [| X' x].
  - auto.
  - intros X. simpl.
    apply (IHx (X ° X')).
Qed.
