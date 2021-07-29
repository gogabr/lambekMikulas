
Require Import List.
Import ListNotations.
From Coq Require Import Relations.
Require Import Coq.Logic.Classical_Prop.

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

  Definition nonEmptySequent (s: sequent) :=
    match s with
      (x, A) => x <> []
    end.

  Notation "s ⇒ c" := (s, c) (at level 50, no associativity).

  Inductive GenProof (Γ: list sequent): sequent -> Prop :=
    | inGamma (s: sequent) (_: In s Γ) (_: nonEmptySequent s): GenProof Γ s
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

     Definition Wpred (x: U*U) := W (fst x) (snd x).
     Definition Wpoint := sig Wpred.
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

   Lemma strAssoc: forall X Y Z p,
       formValuation ((X ° Y) ° Z)  p <-> formValuation (X ° (Y ° Z)) p.
     Proof.
       intros. simpl. split; intros.
       { destruct H as [w [[x [FVX [y [FVY Cxyw]]]] [z [FVZ Cwzp]]]].
          exists x. split. 1:assumption.
          destruct Cxyw as [Cxyw1 [Cxyw2 Cxyw3]].
          destruct Cwzp as [Cwzp1 [Cwzp2 Cwzp3]].
          unfold C.
          destruct x as  [[u1 u2] Wx].
          destruct y as [[u2' u3] Wy].
          destruct z as [[u3' u4] Wz].
          destruct w as [[u1' u3''] Ww].
          destruct p as [[u1'' u4'] Wp].
          simpl in *. subst.
          set (w' := exist Wpred (u2', u4') (t _ _ _ Wy Wz)).
          exists w'. split. 2:auto.
          set (y := exist Wpred (u2', u3') Wy).
          exists y. split. 1: assumption.
          set (z := exist Wpred (u3', u4') Wz).
          exists z. split. 1: assumption.
          auto. }
       destruct H as [x [FVX [w [[y [FVY [z [FVZ Cyzw]]]] Cxwp]]]].
       destruct Cyzw as [Cyzw1 [Cyzw2 Cyzw3]].
       destruct Cxwp as [Cxwp1 [Cxwp2 Cxwp3]].
       destruct x as [[u1 u2] Wx].
       destruct y as [[u2' u3] Wy].
       destruct z as [[u3' u4] Wz].
       destruct w as [[u2'' u4'] Ww].
       destruct p as [[u1' u4''] Wp].
       simpl in *. subst.
       set (w' := exist Wpred (u1', u3') (t _ _ _ Wx Wy)).
       exists w'. split.
       - set (x := exist Wpred (u1', u2'') Wx).
         exists x. split. 1:assumption.
         set (y := exist Wpred (u2'', u3') Wy).
         exists y. split. 1:assumption.
         unfold C. auto.
       - set (z := exist Wpred (u3', u4'') Wz).
         exists z. split. 1:assumption.
         unfold C. auto.
     Qed.
   End Semantics.

   Definition semConsequence (Γ: list sequent) (s: sequent) :=
     (forall s', In s' Γ -> nonEmptySequent s') /\
     forall (U: Set) (W: relation U) (v: types -> subW U W),
       (forall s', (In s' Γ) -> seqTrue U W v s') -> seqTrue U W v s.

   Notation "Γ ⊨ s" := (semConsequence Γ s) (at level 60, no associativity).

   Inductive Singleton: Set := Sing.
   Definition TotalOnSingleton (_ _:Singleton) := True.
   Definition AllSingleton (_:Wpoint Singleton TotalOnSingleton) := True.
   Definition ValOnSingleton := fun (_:types) => AllSingleton.
   Definition WpointOnSingleton := exist (fun (_: Singleton * Singleton) => True) (Sing, Sing) I.

   Lemma AllEqualOnSingleton: forall (x y: Wpoint Singleton TotalOnSingleton), x = y.
   Proof.
     intros.
     destruct x as [[[] []] []]. destruct y as [[[] []] []]. reflexivity.
   Qed.

   Lemma AllTrueOnSingleton: forall (A: Formula)  (p: Wpoint Singleton TotalOnSingleton),
       formValuation Singleton TotalOnSingleton ValOnSingleton A p.
     intros. induction A as [v| A IHA B IHB | A IHA B IHB | A IHA B IHB].
     - apply I.
     - simpl. intros.
       assert (p = z) as PZ by apply AllEqualOnSingleton.
       rewrite <- PZ. assumption.
     - simpl. intros.
       assert (p = z) as PZ by apply AllEqualOnSingleton.
       rewrite <- PZ. assumption.
     - simpl.
       exists WpointOnSingleton. split.
       + assert (p = WpointOnSingleton) as PP by apply AllEqualOnSingleton.
         rewrite <- PP. assumption.
       + exists WpointOnSingleton. split.
         * assert (p = WpointOnSingleton) as PP by apply AllEqualOnSingleton.
           rewrite <- PP. assumption.
         * unfold C. simpl. destruct p. simpl. destruct x as [[] []]. simpl. auto.
   Qed.

   Lemma conseqNonEmpty:  forall Γ x A, Γ ⊨ x ⇒ A -> x <> [].
   Proof.
     intros. intro XisNull.
     unfold semConsequence in H.  destruct H as [NEmp STrue].
     subst.
     assert (forall s, In s Γ -> seqTrue Singleton TotalOnSingleton ValOnSingleton s). {
       intros. unfold seqTrue. intros.  unfold seqValuation. destruct s.
       assert (nonEmptySequent (s ⇒ f)) as NE by apply NEmp, H. unfold nonEmptySequent in NE.
       destruct s. 1:{ apply NE; reflexivity. }
       left.  apply AllTrueOnSingleton. }
     apply (STrue Singleton TotalOnSingleton ValOnSingleton) in H.
     unfold seqTrue in H.
     assert (seqValuation Singleton TotalOnSingleton ValOnSingleton ([] ⇒ A) WpointOnSingleton) as HH by apply H.
     apply HH.
   Qed.

   Fixpoint pullMultLeft (X: Formula) (x: str) :=
     match x with
     | [] => X
     | X' :: x' => pullMultLeft (X ° X') x'
     end.

   Lemma strValuationRight: forall U W v X x A p,
       strValuation U W v X (x ++ [A]) p = strValuation U W v (pullMultLeft X x) [A] p.
   Proof.
     intros.
     generalize dependent X.
     induction x.
     - simpl. reflexivity.
     - intro. simpl. rewrite (IHx  (X ° a)). reflexivity.
   Qed.

   Lemma strValuationToFormValuation: forall U W v X x p,
       strValuation U W v X x p = formValuation U W v (pullMultLeft X x) p.
   Proof.
     intros.
     generalize dependent X.
     induction x.
     - simpl. reflexivity.
     - intro. simpl. rewrite (IHx  (X ° a)). reflexivity.
   Qed.

   Lemma leftDivSound: forall Γ x A B, Γ ⊨ x ⇒ A -> Γ ⊨ ((x ++ [A \\ B]) ⇒ B).
   Proof.
     intros.
     unfold semConsequence. intros.
     unfold seqTrue. split.
     - unfold semConsequence in H. destruct H. assumption.
     - intros U W v allΓ p.
       assert (x <> []) as XnonEmpty by (apply (conseqNonEmpty Γ x A); assumption).
       unfold seqValuation.
       destruct x as [| X x]. 1:{ exfalso. apply XnonEmpty. reflexivity. }
       simpl. apply or_comm. apply imply_to_or.  intros StrVal. simpl.
       rewrite strValuationRight in StrVal.
       simpl in StrVal.
       destruct StrVal as [p1 [FVpml [p2 [XX1 XX2]]]].
       unfold semConsequence in H.
       destruct H as [_ H]. set (HH := H U W v allΓ p1) . unfold seqTrue in HH.
       unfold seqValuation in HH.  rewrite strValuationToFormValuation in HH.
       apply or_comm in HH. set (HHH:= or_to_imply _ _ HH).
       apply (XX1 p1). 2:assumption.
       apply HHH. assumption.
   Qed.

   Fixpoint pullMultRight (X : Formula) (x : str) :=
     match x with
     | [] => X
     | (X'::x') => X ° (pullMultRight X' x')
     end.

   Lemma strValuationLeft: forall U W v A x p,
       strValuation U W v A x p = formValuation U W v (pullMultRight A x) p.
   Proof.
     intros.
     generalize dependent A.
     induction x as [| X x].
     - simpl. reflexivity.
     - simpl. intros. rewrite (IHx (A ° X)).
!!!! From here !!!!!

       Lemma rightDivSound: forall Γ x A B, Γ ⊨ x ⇒ A -> Γ ⊨ (((A // B) :: x) ⇒ B).
   Proof.
     intros.
     unfold semConsequence. intros.
     unfold seqTrue. split.
     - unfold semConsequence in H. destruct H. assumption.
     - intros U W v allΓ p.
       assert (x <> []) as XnonEmpty by (apply (conseqNonEmpty Γ x A); assumption).
       simpl.
       apply or_comm. apply imply_to_or. intros StrVal.
       destruct x as [| X x]. 1: congruence.
       simpl in StrVal.
       unfold strValuation in StrVal.

     Lemma Soundness: forall Γ s, Γ ⊢ s -> Γ ⊨ s.
   Proof.
   Admitted.

   Lemma Completeness: forall Γ s, Γ ⊨ s -> Γ ⊢ s.
   Admitted.


End LambekCalculus.
