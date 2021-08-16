Require Import List.
Import ListNotations.
From Coq Require Import Relations.

Require Import LambekSyntax.
Require Import SyntaxOps.

Section Semantics.

  Definition frame := {UW : { U : Type & relation U } | transitive (projT1 UW) (projT2 UW) }.

  Context (F: frame).

  Definition U: Type := projT1 (proj1_sig F).
  Definition W: relation U := projT2 (proj1_sig F).
  Definition transitivity: transitive U W := proj2_sig F.

  Definition Wpred (x: U*U) := W (fst x) (snd x).
  Definition Wpoint := sig Wpred.
  Definition Cf (x y: Wpoint) (e: snd (proj1_sig x) = fst (proj1_sig y)) : Wpoint.
  Proof.
    destruct x as [x px]. destruct x as [a b].
    destruct y as [y py]. destruct y as [b' c].
    simpl in e. rewrite <- e in py.
    exists (a,c).
    simpl. simpl in px. simpl in py.
    apply (transitivity _ _ _ px py).
  Defined.

  Definition C (x y z: Wpoint): Prop := fst (proj1_sig x) = fst (proj1_sig z)
                                        /\ snd (proj1_sig x) = fst (proj1_sig y)
                                        /\ snd (proj1_sig y) = snd (proj1_sig z).

  Definition subW := Wpoint -> Prop.

  Definition valuation := elem_cat -> subW.
  Context (v: valuation).

  Fixpoint formValuation (A: formula): subW :=
    match A with
    | var X => v X
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

  Fixpoint strValuation (X: formula) (x: str): subW :=
    match x with
    | [] => formValuation X
    | (A :: x') => strValuation (X ° A) x'
    end.

  Definition seqValuation (s: sequent): subW :=
    match s with
    | (X :: x, A) => fun p => (strValuation X x p) ->  (formValuation A p)
    | ([], A) => fun _ => False
    end.

  Definition seqTrue (s: sequent): Prop :=
    forall p, seqValuation s p.

  Lemma strAssoc: forall X Y Z p,
      formValuation ((X ° Y) ° Z)  p <-> formValuation (X ° (Y ° Z)) p.
  Proof.
    intros. simpl. split; intros H.
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
      set (w' := exist Wpred (u2', u4') (transitivity _ _ _ Wy Wz)).
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
    set (w' := exist Wpred (u1', u3') (transitivity _ _ _ Wx Wy)).
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

  Lemma pullMultRightExtraction (A  X: formula) (x : str):
    forall p,
      formValuation (pullMultRight (A ° X) x) p <-> formValuation (A ° pullMultRight  X x) p.
  Proof.
    generalize dependent A. generalize dependent X.
    induction x as [| X' x].
    - intros. reflexivity.
    - intros.
      set (TG1 := (pullMultRight (A ° X) (X' :: x))).
      set (TG2 := (A ° pullMultRight X (X' :: x))).
      simpl in TG1. simpl in TG2.
      apply strAssoc.
  Qed.

  Lemma pullMultEquiv A x p:
    formValuation (pullMultLeft A x) p <-> formValuation (pullMultRight A x) p.
  Proof.
    generalize dependent A.
    induction x as [| X x].
    - intros A. simpl. apply iff_refl.
    - intros A.
      set (TG := pullMultRight A (X :: x)).
      simpl in TG. subst TG.
      set (TG := pullMultLeft A (X :: x)).
      simpl in TG.
      subst TG.
      rewrite (IHx (A ° X)).
      apply pullMultRightExtraction.
  Qed.

  Lemma strValuationStepBack A X x p:
    strValuation (A ° X) x p = strValuation A (X :: x) p.
  Proof.
    reflexivity.
  Qed.

  Lemma strValuationToFormValuationRight: forall A x p,
      strValuation A x p <-> formValuation (pullMultRight A x) p.
  Proof.
    intros.
    generalize dependent A.
    induction x as [| X x].
    - simpl. reflexivity.
    - intros.
      set (TG := strValuation  A (X :: x) p).
      simpl in TG.
      subst TG.
      rewrite (IHx (A ° X)).
      apply pullMultRightExtraction.
  Qed.
End Semantics.

Definition semConsequence (Γ: list sequent) (s: sequent) :=
  (forall s', In s' Γ -> nonEmptySequent s') /\
  forall (F: frame) (v: valuation F),
    (forall s', (In s' Γ) -> seqTrue F v s') -> seqTrue F v s.

Notation "Γ ⊨ s" := (semConsequence Γ s) (at level 60, no associativity).
