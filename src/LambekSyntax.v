Require Import List.
Import ListNotations.

(* elementary category *)
Definition elem_cat: Type := nat.

Inductive formula :=
| var (a: elem_cat)
| leftDiv (a b: formula)
| rightDiv (a b: formula)
| mul (a b: formula).

Notation "x ° y" := (mul x y) (at level 40, left associativity).
Notation "x // y" := (rightDiv x y) (at level 40, no associativity).
Notation "x \\ y" := (leftDiv x y) (at level 40, no associativity).

Definition str := list formula.
Definition sequent: Type := (str * formula).

Definition nonEmptySequent (s: sequent) :=
  match s with
    (x, A) => x <> []
  end.

Notation "s ⇒ c" := (s, c) (at level 50, no associativity).

Inductive genProof (Γ: list sequent): sequent -> Prop :=
| inGamma (s: sequent) (_: In s Γ) (_: nonEmptySequent s): genProof Γ s
| identity (a: formula): genProof Γ ([a], a)
| leftArrow (y: str) (X: formula) (x: str) (A B: formula) (z: str) (C: formula)
            (p1: genProof Γ ((X::x) ⇒ A))
            (p2: genProof Γ ((y ++ B :: z) ⇒ C))
  : genProof Γ ((y ++ (X::x) ++ (A \\ B) :: z) ⇒ C)
| arrowLeft (X: formula) (x: str) (A B: formula) (p: genProof Γ ((A :: X :: x), B))
  : genProof Γ ((X::x) ⇒ A \\ B)
| rightArrow (y: str) (B A: formula) (X: formula) (x z: str) (C: formula)
             (p1: genProof Γ ((X::x) ⇒ A))
             (p2: genProof Γ ((y ++ B::z) ⇒ C))
  : genProof Γ ((y ++ (B // A) :: X :: x ++ z) ⇒ C)
| arrowRight (X: formula) (x: str) (A B: formula) (p: genProof Γ ((X :: x ++ [A]) ⇒ B))
  : genProof Γ ((X::x) ⇒ B // A)
| mulArrow (x: str) (A B: formula) (y: str) (C: formula)
           (p: genProof Γ ((x ++ A :: B :: y) ⇒ C))
  : genProof Γ ((x ++ (A ° B) :: y) ⇒ C)
| arrowMul (X: formula) (x: str) (Y: formula) (y: str) (A B: formula)
           (p1: genProof Γ ((X::x) ⇒ A))
           (p2: genProof Γ ((Y::y) ⇒ B))
  : genProof Γ ((X :: x ++ Y :: y) ⇒ A ° B).

Definition proofWithNonEmptyPremises (Γ: list sequent) (s: sequent): Prop :=
  (forall (s': sequent), In s' Γ -> nonEmptySequent s') /\
  genProof Γ s.

Notation "Γ ⊢ s" := (proofWithNonEmptyPremises Γ s) (at level 60, no associativity).
