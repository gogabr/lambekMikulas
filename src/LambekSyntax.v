Require Import List.
Import ListNotations.

Definition types: Type := nat.

Inductive Formula :=
| var (a: types)
| leftDiv (a b: Formula)
| rightDiv (a b: Formula)
| mul (a b: Formula).

Notation "x ° y" := (mul x y) (at level 40, left associativity).
Notation "x // y" := (rightDiv x y) (at level 40, no associativity).
Notation "x \\ y" := (leftDiv x y) (at level 40, no associativity).

Definition str := list Formula.
Definition sequent: Type := (str * Formula).

Definition nonEmptySequent (s: sequent) :=
  match s with
    (x, A) => x <> []
  end.

Notation "s ⇒ c" := (s, c) (at level 50, no associativity).

Inductive GenProof (Γ: list sequent): sequent -> Prop :=
| inGamma (s: sequent) (_: In s Γ) (_: nonEmptySequent s): GenProof Γ s
| identity (a: Formula): GenProof Γ ([a], a)
| leftArrow (y: str) (X: Formula) (x: str) (A B: Formula) (z: str) (C: Formula)
            (p1: GenProof Γ ((X::x) ⇒ A))
            (p2: GenProof Γ ((y ++ B :: z) ⇒ C))
  : GenProof Γ ((y ++ (X::x) ++ (A \\ B) :: z) ⇒ C)
| arrowLeft (X: Formula) (x: str) (A B: Formula) (p: GenProof Γ ((A :: X :: x), B))
  : GenProof Γ ((X::x) ⇒ A \\ B)
| rightArrow (y: str) (B A: Formula) (X: Formula) (x z: str) (C: Formula)
             (p1: GenProof Γ ((X::x) ⇒ A))
             (p2: GenProof Γ ((y ++ B::z) ⇒ C))
  : GenProof Γ ((y ++ (B // A) :: X :: x ++ z) ⇒ C)
| arrowRight (X: Formula) (x: str) (A B: Formula) (p: GenProof Γ ((X :: x ++ [A]) ⇒ B))
  : GenProof Γ ((X::x) ⇒ B // A)
| mulArrow (x: str) (A B: Formula) (y: str) (C: Formula)
           (p: GenProof Γ ((x ++ A :: B :: y) ⇒ C))
  : GenProof Γ ((x ++ (A ° B) :: y) ⇒ C)
| arrowMul (X: Formula) (x: str) (Y: Formula) (y: str) (A B: Formula)
           (p1: GenProof Γ ((X::x) ⇒ A))
           (p2: GenProof Γ ((Y::y) ⇒ B))
  : GenProof Γ ((X :: x ++ Y :: y) ⇒ A ° B).

Definition ProofWithNonEmptyPremises (Γ: list sequent) (s: sequent): Prop :=
  (forall (s': sequent), In s' Γ -> nonEmptySequent s') /\
  GenProof Γ s.

Notation "Γ ⊢ s" := (ProofWithNonEmptyPremises Γ s) (at level 60, no associativity).
