
Require Import List.
Import ListNotations.
From Coq Require Import Relations.

Section LambekCalculus.
  Variable types: Type.

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

  Notation "s ⇒ c" := (s, c) (at level 50, no associativity).

  Inductive GenProof (Γ: list sequent): sequent -> Prop :=
    | inGamma (s: sequent) (_: In s Γ): GenProof Γ s
    | identity (a: Formula): GenProof Γ ([a], a)
    | leftArrow (y: str)
                (X: Formula) (x: str)
                (A B: Formula)
                (z: str)
                (C: Formula)
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
       : GenProof Γ ((X::x) ⇒ B \\ A)
     | mulArrow (x: str) (A B: Formula) (y: str) (C: Formula)
                (p: GenProof Γ ((x ++ A :: B :: y) ⇒ C))
       : GenProof Γ ((x ++ (A ° B) :: y) ⇒ C)
     | arrowMul (X: Formula) (x: str) (Y: Formula) (y: str) (A B: Formula)
                (p1: GenProof Γ ((X::x) ⇒ A))
                (p2: GenProof Γ ((Y::y) ⇒ B))
       : GenProof Γ ((X :: x ++ Y :: y) ⇒ A ° B).

  Notation "Γ ⊢ s" := (GenProof Γ s) (at level 60, no associativity).

   (* Lemma FormulaProof (x: str) (X: Formula) (C: Formula):  *)
   (*   Proof (x ++ [X], C) <-> Proof ([fold_right mul X x], C). *)
   (* Proof. *)
   (*   generalize dependent C. *)
   (*   induction x ; simpl. *)
   (*   - tauto. *)
   (*   - split. *)
   (*     + intro. *)
   (*       assert ([mul a (fold_right mul X x)] = [] ++ (mul a (fold_right mul X x))::[]) as RW by auto. *)
   (*       rewrite RW. *)
   (*       apply mulArrow. *)
   (*       simpl. *)
   (*       assert ([a; fold_right mul X x] = [a] ++ [fold_right mul X x]) as RW1 by auto. *)
   (*       rewrite RW1. *)
(*
         assert (a :: x ++ [X] = [] ++ a :: x ++ [X]) as RW by auto.
         rewrite RW.
         apply mulArrow.
         apply (mulArrow [] a (fold_right mul X x) [] C _).
*)

   Section Semantics.

     Variable U: Type.
     Variable W: relation U.
     Variable t: transitive U W.

     Definition Wpoint := sig (fun x: U*U => W (fst x) (snd x)).
     Definition Cf (x y: Wpoint) (e: snd (proj1_sig x) = fst (proj1_sig y)) : Wpoint.
     Proof.
       destruct x as [x px]. destruct x as [a b].
       destruct y as [y py]. destruct y as [b' c].
       simpl in e. rewrite <- e in py.
       exists (a,c).
       simpl. simpl in px. simpl in py.
       apply (t _ _ _ px py).
     Defined.

     Definition C (x y z: Wpoint): Prop := fst (proj1_sig x) = fst (proj1_sig z)
                                           /\ snd (proj1_sig x) = fst (proj1_sig y)
                                           /\ snd (proj1_sig y) = snd (proj1_sig z).

     Definition subW := Wpoint -> Prop.

     Variable valuation: types -> subW.

     Fixpoint formValuation (A: Formula): subW :=
       match A with
       | var X => valuation X
       | mul A B =>
         let av := formValuation A in
         let bv := formValuation B in
         fun z: Wpoint => exists x, av x /\ exists y, bv y /\ C x y z
       | leftDiv A B =>
         let av := formValuation A in
         let bv := formValuation B in
         fun y: Wpoint => forall x (_: av x) z (_: C x y z), bv z
       | rightDiv B A =>
         let av := formValuation A in
         let bv := formValuation B in
         fun x: Wpoint => forall y (_: av y) z (_: C x y z), bv z
       end .

     Fixpoint strValuation (X: Formula) (x: str): subW :=
       match x with
       | [] => formValuation X
       | (A :: x') => strValuation (X ° A) x'
       end.

     Definition seqValuation (s: sequent): subW :=
       match s with
       | (X :: x, A) => fun p => (formValuation A p)  \/ not (strValuation X x p)
       | ([], A) => fun _ => False
       end.

     Definition seqTrue (s: sequent): Prop :=
       forall p, seqValuation s p.

   End Semantics.

   Definition semConsequence (Γ: list sequent) (s: sequent) :=
     forall (U: Set) (W: relation U) (v: types -> subW U W),
       (forall s', (In s' Γ) -> seqTrue U W v s') -> seqTrue U W v s.


   Notation "Γ ⊨ s" := (semConsequence Γ s) (at level 60, no associativity).


   Lemma Soundness: forall Γ s, Γ ⊢ s -> Γ ⊨ s.
   Proof.
   Admitted.

   Lemma Completeness: forall Γ s, Γ ⊨ s -> Γ ⊢ s.
   Admitted.


End LambekCalculus.
