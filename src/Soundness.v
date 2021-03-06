Require Import List.
Import ListNotations.
From Coq Require Import Relations.
Require Import Coq.Logic.Classical_Prop.
Require Import NonEmptyList.
Require Import LambekSyntax.
Require Import SyntaxOps.
Require Import Semantics.
Require Import Singleton.

Lemma conseqNonEmpty:  forall Γ x A, Γ ⊨ x ⇒ A -> x <> [].
Proof.
  intros. intro XisNull.
  unfold semConsequence in H.  destruct H as [NEmp STrue].
  subst.
  assert (forall s, In s Γ -> seqTrue singletonModel s). {
    intros. unfold seqTrue. intros.  unfold seqValuation. destruct s.
    assert (nonEmptySequent (s ⇒ f)) as NE by apply NEmp, H. unfold nonEmptySequent in NE.
    destruct s. 1:{ apply NE; reflexivity. }
    intro.  apply allTrueOnSingleton. }
  apply (STrue singletonModel) in H.
  unfold seqTrue in H.
  assert (seqValuation singletonModel ([] ⇒ A) WpointOnSingleton) as HH by apply H.
  apply HH.
Qed.

Lemma strValuationRight: forall M X x A p,
    strValuation M X (x ++ [A]) p = strValuation M (pullMultLeft X x) [A] p.
Proof.
  intros.
  generalize dependent X.
  induction x.
  - simpl. reflexivity.
  - intro. simpl. rewrite (IHx  (X ° a)). reflexivity.
Qed.

Lemma strValuationToFormValuationLeft: forall M X x p,
    strValuation M X x p <-> formValuation M (pullMultLeft X x) p.
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
  - intros M allΓ p.
    assert (x <> []) as XnonEmpty by (apply (conseqNonEmpty Γ x A); assumption).
    unfold seqValuation.
    destruct x as [| X x]. 1:{ exfalso. apply XnonEmpty. reflexivity. }
    simpl.  intros StrVal. simpl.
    rewrite strValuationRight in StrVal.
    simpl in StrVal.
    destruct StrVal as [p1 [FVpml [p2 [XX1 XX2]]]].
    unfold semConsequence in H.
    destruct H as [_ H]. set (HH := H M allΓ p1) . unfold seqTrue in HH.
    unfold seqValuation in HH.  rewrite strValuationToFormValuationLeft in HH.
    apply (XX1 p1). 2:assumption.
    apply HH. assumption.
Qed.

Lemma rightDivSound: forall Γ x A B, Γ ⊨ x ⇒ A -> Γ ⊨ ((B // A) :: x) ⇒ B.
Proof.
  intros.
  unfold semConsequence. intros.
  unfold seqTrue. split.
  - unfold semConsequence in H. destruct H. assumption.
  - intros M allΓ p.
    assert (x <> []) as XnonEmpty by (apply (conseqNonEmpty Γ x A); assumption).
    simpl. intros StrVal.
    destruct x as [| X x]. 1: congruence.
    simpl in StrVal.
    apply strValuationToFormValuationRight in StrVal.
    apply pullMultRightExtraction in StrVal.
    simpl in StrVal.
    destruct StrVal as [p1 [R1 [p2 [FV2 C12p]]]].
    assert (formValuation M A p2) as AatP2. {
      unfold semConsequence in H.
      destruct H as [AllNonEmpty HH].
      set (HHH := (HH M allΓ)).
      unfold seqTrue in HHH. unfold seqValuation in HHH.
      apply (HHH p2).
      apply strValuationToFormValuationRight.
      apply FV2. }
    apply R1 with (y:=p2). 1:apply AatP2.
    apply C12p.
Qed.

Lemma arrowLeftSound M x A B:
  x <> [] ->
  seqTrue M ((A :: x) ⇒ B) <-> seqTrue M (x ⇒ A \\ B).
Proof.
  intros NE.
  unfold seqTrue.
  split.
  - intros H p.
    unfold seqValuation.
    destruct x as [| X x]. 1: congruence.
    unfold seqValuation in H.
    intros SV.
    simpl.
    intros p1 FVA p2 C1p2.
    set (HH := H p2).
    apply HH.
    apply strValuationToFormValuationRight.
    simpl.
    exists p1. split. 1: assumption.
    exists p. split. 2: assumption.
    apply strValuationToFormValuationRight in SV.
    assumption.
  - intros H p.
    unfold seqValuation.
    destruct x as [|X x]. 1: congruence.
    intros SV.
    simpl in H.
    apply strValuationToFormValuationRight in SV.
    simpl in SV.
    destruct SV as [p1 [FVA [p2 [FVx C12p]]]].
    apply strValuationToFormValuationRight in FVx.
    apply (H p2 FVx p1 FVA p C12p).
Qed.

Lemma arrowRightSound {M} x A B:
  x <> [] ->
  seqTrue M ((x ++ [A]) ⇒ B) <-> seqTrue M (x ⇒ B // A).
Proof.
  intros NE.
  unfold seqTrue.
  split.
  - intros H p.
    unfold seqValuation.
    destruct x as [| X x]. 1: congruence.
    simpl in H.
    intros SV.
    simpl.
    intros p1 FVA p2 Cp12.
    set (HH := H p2).
    apply HH.
    apply (strValuationToFormValuationLeft).
    rewrite pullMultLeftSplit.
    simpl.
    exists p. split.
    1: { apply strValuationToFormValuationLeft in SV. assumption. }
    exists p1. auto.
  - intros H p.
    destruct x as [|X x]. 1: congruence.
    simpl.
    unfold seqValuation.
    intros SV.
    simpl in H.
    apply strValuationToFormValuationLeft in SV.
    rewrite pullMultLeftSplit in SV.
    simpl in SV.
    destruct SV as [p1 [FVXx [p2 [FVA C12p]]]].
    apply strValuationToFormValuationLeft in FVXx.
    apply (H p1 FVXx p2 FVA p C12p).
Qed.

Lemma mulInSeqTrue M x A B z CC:
  seqTrue M ((x ++ (A ° B :: z)) ⇒ CC) <-> seqTrue M ((x ++ A :: B :: z) ⇒ CC).
Proof.
  generalize dependent CC.
  induction x as [| X x].
  - intros CC. simpl.
    unfold seqTrue.
    split.
    + intros H p.
      unfold seqValuation.
      intros SV.
      unfold seqValuation in H.
      simpl in SV.
      apply H.
      assumption.
    + intros H p.
      unfold seqValuation.
      intros SV.
      unfold seqValuation in H.
      set (HH := H p).
      simpl in HH.
      apply (HH SV).
  - intros CC. simpl.
    set (IHXC := IHx (X \\ CC)).
    repeat rewrite (arrowLeftSound M). 1: assumption.
    all: apply not_eq_sym, app_cons_not_nil.
Qed.

Lemma pointwiseMultLeft1 M A B X p
      (AtoB: forall p', formValuation M A p' -> formValuation M B p')
      (H: formValuation M (A ° X) p):
  formValuation M (B ° X) p.
Proof.
  simpl. simpl in H.
  destruct H as [p1 [FVA [p2 [FVX C12p]]]].
  exists p1. split. 1:{ apply AtoB. assumption. }
  exists p2. auto.
Qed.

Lemma pointwiseMultLeft M A B X p
      (ABEq: forall p', formValuation M A p' <-> formValuation M B p'):
  formValuation M (A ° X) p <-> formValuation M (B ° X) p.
Proof.
  split.
  all:(apply pointwiseMultLeft1; intros;  apply ABEq; assumption).
Qed.

Lemma pointwiseMultRight1 M A B X p
      (AtoB: forall p', formValuation M A p' -> formValuation M B p')
      (H: formValuation M (X ° A) p):
  formValuation M (X ° B) p.
Proof.
  simpl. simpl in H.
  destruct H as [p1 [FVX [p2 [FVA C12p]]]].
  exists p1. split. 1:assumption.
  exists p2. split. 1:{ apply AtoB. assumption. }
  assumption.
Qed.

Lemma pointwiseMultRight M A B X p
      (ABEq: forall p', formValuation M A p' <-> formValuation M B p'):
  formValuation M (X ° A) p <-> formValuation M (X ° B) p.
Proof.
  split.
  all:( apply pointwiseMultRight1; intros; apply ABEq; assumption).
Qed.

Lemma leftMultRearrange M A B X p
      (H: formValuation M (A \\ B ° X) p):
  formValuation M (A \\ (B ° X)) p.
Proof.
  simpl. simpl in H.
  intros p1 FVA p2 C1p2.
  destruct H as [p3 [HH [p4 [FVX C34p]]]].
  destruct p1 as [[u1 u2] Wp1].
  destruct p2 as [[u1' u4] Wp2].
  destruct p3 as [[u2' u3] Wp3].
  destruct p4 as [[u3' u4'] Wp4].
  destruct p as [[u2'' u4''] Wp].
  destruct C1p2 as [C1p21 [C1p22 C1p23]].
  destruct C34p as [C34p1 [C34p2 C34p3]].
  simpl in *. subst.
  set (pB := exist Wpred (u1', u3') (transitivity _ _ _ Wp1 Wp3)).
  set (p1 := exist Wpred (u1', u2'') Wp1).
  set (p3 := exist Wpred (u2'', u3') Wp3).
  set (p4 := exist Wpred (u3', u4) Wp4).
  exists pB. split.
  - apply (HH p1 FVA pB).
    repeat (split; auto).
  - exists p4. split.
    1: assumption.
    repeat (split; auto).
Qed.

Lemma rightMultRearrange M X B A p
      (H: formValuation M (X ° (B // A)) p):
  formValuation M ((X ° B) // A) p.
Proof.
  simpl. simpl in H.
  intros p1 FVA p2 Cp12.
  destruct H as [p3 [FVX [p4 [HH C34p]]]].
  destruct p1 as [[u3 u4] Wp1].
  destruct p2 as [[u1 u4'] Wp2].
  destruct p3 as [[u1' u2] Wp3].
  destruct p4 as [[u2' u3'] Wp4].
  destruct p as [[u1'' u3''] Wp].
  destruct Cp12 as [Cp121 [Cp122 Cp123]].
  destruct C34p as [C34p1 [C34p2 C34p3]].
  simpl in *. subst.
  set (p1 := exist Wpred (u3, u4') Wp1).
  set (p2 := exist Wpred (u1, u4') Wp2).
  set (p3 := exist Wpred (u1, u2') Wp3).
  set (p4 := exist Wpred (u2', u3) Wp4).
  set (pB := exist Wpred (u2', u4') (transitivity _ _ _ Wp4 Wp1)).
  exists p3. split. 1: assumption.
  exists pB. split. 1: { apply (HH p1 FVA pB). split; auto. }
  split; auto.
Qed.

Lemma pointwiseReplaceInStrHead1 M A B z p
      (AtoB: forall p', formValuation M A p' -> formValuation M B p'):
  strValuation M A z p -> strValuation M B z p.
Proof.
  generalize dependent A.
  generalize dependent B.
  induction z as [| Z z].
  - intros. simpl. simpl in H. apply AtoB. assumption.
  - intros. simpl. simpl in H.
    apply (IHz (B ° Z) (A ° Z)). 2: assumption.
    intro p'.
    apply pointwiseMultLeft1.
    assumption.
Qed.

Lemma pointwiseReplaceInStrHead M A B z p
      (ABEq: forall p', formValuation M A p' <-> formValuation M B p'):
  strValuation M A z p <-> strValuation M B z p.
Proof.
  split; apply pointwiseReplaceInStrHead1; intros; apply ABEq; assumption.
Qed.

Lemma pointwiseReplaceInStrTail M X x A B z p :
  (forall p', formValuation M A p' -> formValuation M B p') ->
  strValuation M X (x ++ A :: z) p -> strValuation M X (x ++ B :: z) p.
Proof.
  intros H.
  generalize dependent X.
  induction x as [| X' x].
  - intro X. simpl.
    generalize dependent A.
    generalize dependent B.
    induction z as [| Z z].
    + intros B A H.
      simpl.
      intros [p1 [FVX [p2 [FVA CCC]]]].
      exists p1. split. 1: assumption.
      exists p2. split. 1: { apply H. assumption. }
      assumption.
    + intros B A H SVXA.
      simpl. simpl in SVXA.
      set (IHz':= IHz (B ° Z) (A ° Z)).
      assert (forall p', formValuation M (X ° (A ° Z)) p' -> formValuation M (X ° (B ° Z)) p') as XAZeqXBZ. {
        intro p'.
        apply pointwiseMultRight1.
        intro.
        apply pointwiseMultLeft1.
        assumption. }
      rewrite (pointwiseReplaceInStrHead _ (X ° B ° Z) (X ° (B ° Z))).
      2:apply strAssoc.
      apply IHz'.
      1: { intro p'. apply pointwiseMultLeft1. assumption. }
      apply (pointwiseReplaceInStrHead _ (X ° (A ° Z)) (X ° A ° Z)).
      1: { intro p'. rewrite strAssoc. apply iff_refl. }
      assumption.
  - intro X. simpl.
    apply (IHx (X ° X')).
Qed.

Lemma pointwiseReplaceInSeq M x A B z CC p :
  (forall p', formValuation M A p' -> formValuation M B p') ->
  seqValuation M ((x ++ B :: z) ⇒ CC) p ->
  seqValuation M ((x ++ A :: z) ⇒ CC) p.
Proof.
  intros H.
  destruct x as [| X x].
  - simpl. intros HD AtA.
    apply HD. apply (pointwiseReplaceInStrHead1 M A B). all: auto.
  - simpl. intros TL AtA.
    apply TL. apply (pointwiseReplaceInStrTail M X x A B z). all: auto.
Qed.

Lemma strValuationStepInMiddle M X x A B z p:
  strValuation M X (x ++ A :: B :: z) p <->
  strValuation M X (x ++ (A ° B) :: z) p.
Proof.
  generalize dependent X.
  induction x as [| X x].
  - simpl. intro X.
    apply pointwiseReplaceInStrHead.
    intros p'. apply strAssoc.
  - simpl. intros X'.
    apply (IHx (X' ° X)).
Qed.

Lemma seqValuationStepInMiddle M x A B z CC p:
  seqValuation M ((x ++ A :: B :: z) ⇒ CC) p <-> seqValuation M ((x ++ A ° B :: z) ⇒ CC) p.
Proof.
  destruct x as [| X x].
  - simpl. apply iff_refl.
  - simpl. rewrite strValuationStepInMiddle. apply iff_refl.
Qed.

Lemma leftElimSema M A B p1 p2 p
      (FVA: formValuation M A p1)
      (FVDiv: formValuation M (A \\ B) p2)
      (C12p: C p1 p2 p):
  formValuation M B p.
Proof.
  simpl in FVDiv.
  apply (FVDiv p1 FVA p). apply C12p.
Qed.

Lemma pullMultRightI M X x y p:
  formValuation M (pullMultRight (pullMultRight X x) y) p <->
  formValuation M (pullMultRight X (x ++ y)) p.
Proof.
  generalize dependent p.
  generalize dependent X.
  induction x.
  - simpl. reflexivity.
  - intros.
    set (TG := pullMultRight (pullMultRight X (a :: x)) y). simpl in TG. subst TG.
    set (TG := pullMultRight X ((a :: x) ++ y)). simpl in TG. subst TG.
    rewrite pullMultRightExtraction.
    rewrite <- (pointwiseMultRight M _ _ _ p (IHx a)).
    apply iff_refl.
Qed.

Lemma strValuationToFormValuationRightPartial M X x y p:
  strValuation M X (x ++ y) p <-> strValuation M (pullMultRight X x) y p.
Proof.
  repeat rewrite strValuationToFormValuationRight.
  generalize dependent p.
  generalize dependent X.
  induction x as [| X' x].
  - intros X p. simpl.  apply iff_refl.
  - intros X p.
    set (TG := pullMultRight X ((X' :: x) ++ y)). simpl in TG. subst TG.
    set (TG := pullMultRight (pullMultRight X (X' :: x))). simpl in TG. subst TG.
    rewrite <- pullMultRightExtraction.
    rewrite (IHx (X ° X')).
    rewrite pullMultRightExtraction.
    rewrite pullMultRightI.
    rewrite pullMultRightExtraction.
    rewrite (pointwiseMultRight M _ _ _ p (IHx X')).
    apply iff_refl.
Qed.

Lemma strValuationSplit M X x Y y p:
  strValuation M X (x ++  Y :: y) p <-> formValuation M ((pullMultRight X x) ° (pullMultRight Y y)) p.
Proof.
  split.
  - intros H.
    rewrite (strValuationToFormValuationRightPartial M X x (Y::y) p) in H.
    apply strValuationToFormValuationRight in H.
    set (PMR := pullMultRight (pullMultRight X x) (Y :: y)) in H.
    simpl in PMR.
    apply H.
  - intros H.
    rewrite <- pullMultRightExtraction in H.
    rewrite <- strValuationToFormValuationRight in H.
    rewrite strValuationStepBack in H.
    rewrite <- strValuationToFormValuationRightPartial in H.
    apply H.
Qed.

Lemma semConsequenceToValuation {M} {Γ}
      (allΓ: forall s' : sequent, In s' Γ -> seqTrue M s')
      {X} {x} {A} {p}:
  Γ ⊨ (X :: x) ⇒ A -> formValuation M (pullMultRight X x) p -> formValuation M A p.
Proof.
  intros H1 H2.
  rewrite <- strValuationToFormValuationRight in H2.
  unfold semConsequence in H1.
  destruct H1 as [_ H1].
  apply (H1 M allΓ p H2).
Qed.

Lemma soundness: forall Γ s, Γ ⊢ s -> Γ ⊨ s.
Proof.
  intros Γ s [NE HH].
  induction HH as
      [ s inΓ NE2
      | A
      | y X x A B z CC
      | X x A B
      | y B A X x z CC
      | X x B A
      | x A B y CC
      | X x Y y A B ].
  - unfold semConsequence. split. 1:apply NE.
    intros M allΓ.
    apply allΓ, inΓ.
  - unfold semConsequence. split. 1: apply NE.
    intros M allΓ p.
    unfold seqValuation. unfold strValuation.
    intro. assumption.
  - unfold semConsequence. split. 1: apply NE.
    intros M allΓ p.
    rewrite app_assoc.
    unfold seqValuation.
    generalize dependent p.
    generalize dependent CC.
    induction y as [| Y y].
    + intros CC HH2 IHHH2 p.
      simpl. intro strVal.
      generalize dependent B.
      induction z as [| Z z].
      * intros B _ IHHH2 strVal.
        simpl in IHHH2.
        unfold semConsequence in IHHH2.
        destruct IHHH2 as [_ IHHH2].
        set (BtoCC := IHHH2 M allΓ p).
        unfold seqValuation in BtoCC. apply BtoCC.
        unfold strValuation.
        destruct IHHH1 as [_ IHHH1].
        rewrite strValuationRight in strVal.
        unfold strValuation in strVal.
        simpl in strVal.
        destruct strVal as [p1 [FVA [p2 [RR C12p]]]].
        set (IHH1S := IHHH1 M allΓ p1).
        unfold seqValuation in IHH1S.
        rewrite strValuationToFormValuationLeft in IHH1S.
        set (FVAA := IHH1S FVA).
        set (TG := RR p1 FVAA p C12p).
        assumption.
      * intros B HH2 IHHH2 StrVal.
        simpl in IHHH2.
        apply (IHz (B ° Z)).
        **  apply (mulArrow Γ [] B Z z CC). assumption.
        **  unfold semConsequence. split. 1: apply NE.
            intros.
            rewrite mulInSeqTrue.
            simpl.
            unfold semConsequence in IHHH2.
            destruct IHHH2 as [_ IHHH2].
            apply (IHHH2 M0 H).
        ** simpl in StrVal.
           apply strValuationStepInMiddle in StrVal.
           apply pointwiseReplaceInStrTail with (A:=(A \\ B) ° Z).
           { apply leftMultRearrange. }
           assumption.
    + intros CC HH2 IHHH2 p. simpl.
      intros StrVal.
      set (IHy':= IHy (Y \\ CC)).
      assert (genProof Γ ((y ++ B :: z) ⇒ (Y \\ CC))) as HH2'. {
        destruct y as [| Y' y'].
        - simpl.
          apply (arrowLeft Γ B z Y CC HH2).
        - simpl.
          apply (arrowLeft Γ Y' (y' ++ B :: z) Y CC HH2).
      }
      assert (Γ ⊨ (y ++ B :: z) ⇒ Y \\ CC) as IHHH2'. {
        unfold semConsequence.
        split. 1:apply NE.
        intros M0 allΓ0.
        apply arrowLeftSound.
        * apply not_eq_sym. apply app_cons_not_nil.
        * apply IHHH2.
          apply allΓ0.
      }
      set (IHy'' := IHy' HH2' IHHH2').
      destruct (splitTl (y ++ X :: x) (A \\ B) z) as [[R r] E].
      rewrite E in *.
      apply strValuationToFormValuationRight in StrVal.
      simpl in StrVal.
      destruct StrVal as [p1 [FVY [p2 [FVR C12p]]]].
      set (IHy''' := IHy'' p2).
      rewrite strValuationToFormValuationRight in IHy'''.
      apply IHy''' in FVR.
      apply (leftElimSema M Y CC p1 p2 p). all:assumption.
  - unfold semConsequence. unfold semConsequence in IHHH.
    destruct IHHH as [_ IHHH].
    split. 1:assumption.
    intros. rewrite <- arrowLeftSound. 2:congruence.
    apply IHHH. assumption.
  - unfold semConsequence. split. 1: apply NE.
    intros M allΓ.
    generalize dependent CC.
    induction z as [| Z z] using rev_ind.
    + intros. intro p.
      generalize dependent B.
      induction y as [| Y y] using rev_ind.
      * intros B HH2 IHHH2 H.
        rewrite app_nil_r in H.
        apply strValuationToFormValuationRight in H.
        destruct H as [p1 [RR [p2 [FVA C12p]]]].
        set (FVA' := semConsequenceToValuation allΓ IHHH1 FVA).
        set (RR' := RR p2 FVA' p C12p).
        apply (semConsequenceToValuation allΓ IHHH2 RR').
      * intros B  HH2 IHHH2.
        rewrite <- app_assoc in HH2. simpl in HH2.
        set (HH2' := mulArrow Γ y Y B [] CC HH2).
        rewrite <- app_assoc in IHHH2. simpl in IHHH2.
        assert (Γ ⊨ (y ++ [Y ° B]) ⇒ CC) as IHHH2'. {
          unfold semConsequence.
          split. 1:assumption.
          intros M0 allΓ0.
          apply (mulInSeqTrue M0).
          unfold semConsequence in IHHH2.
          destruct IHHH2 as [_ IHHH2].
          apply (IHHH2 M0 allΓ0).
        }
        set (IHy' := IHy (Y ° B) HH2' IHHH2').
        rewrite <- app_assoc.
        set (tmp := [Y] ++ B // A :: X :: x ++ []). simpl in tmp. subst tmp.
        rewrite seqValuationStepInMiddle.
        apply (pointwiseReplaceInSeq _ y (Y ° (B // A)) ((Y ° B) // A) (X :: x ++ []) CC p).
        ** apply rightMultRearrange.
        ** assumption.
    + intros CC HH2 IHHH2.
      rewrite app_comm_cons in HH2. rewrite app_assoc in HH2.
      rewrite app_comm_cons in IHHH2. rewrite app_assoc in IHHH2.
      destruct (splitTl y B z) as [[Hd tl] e]. simpl in e. rewrite e in *.
      set (HH2' := arrowRight Γ Hd tl Z CC HH2).
      assert (Γ ⊨ (Hd :: tl) ⇒ CC // Z) as IHHH2'. {
        unfold semConsequence. unfold semConsequence in IHHH2.
        split. 1:assumption.
        destruct IHHH2 as [_ IHHH2].
        intros.
        apply arrowRightSound. 1:congruence.
        apply IHHH2.
        assumption.
      }
      set (IHz'' := IHz (CC // Z) HH2' IHHH2').
      assert ((y ++ B // A :: X :: x ++ z ++ [Z]) = (y ++ B // A :: X :: x ++ z) ++ [Z]). {
        repeat rewrite app_comm_cons.
        repeat rewrite <- app_assoc.
        reflexivity.
      }
      rewrite H.
      destruct (splitTl y (B // A) (X :: x ++ z)) as [[Hd' tl'] e']. simpl in e'. rewrite e' in *.
      apply arrowRightSound.
      1: congruence.
      assumption.
  - unfold semConsequence. unfold semConsequence in IHHH.
    destruct IHHH as [_ IHHH].
    split. 1:assumption.
    intros. rewrite <- arrowRightSound. 2:congruence.
    apply IHHH. assumption.
  - unfold semConsequence. unfold semConsequence in IHHH.
    split. 1:assumption.
    intros M allΓ.
    destruct IHHH as [_ IHHH].
    rewrite mulInSeqTrue.
    apply IHHH.
    apply allΓ.
  - unfold semConsequence.
    split. 1:assumption.
    intros M allΓ.
    intros p StrVal.
    rewrite (strValuationSplit M X x Y y p) in StrVal.
    simpl in StrVal.
    destruct StrVal as [p1 [FVXx [p2 [FVYy C12p]]]].
    unfold semConsequence in IHHH1. unfold semConsequence in IHHH2.
    destruct IHHH1 as [_ IHHH1]. destruct IHHH2 as [_ IHHH2].
    set (IH1v := IHHH1 M allΓ p1). set (IH2v := IHHH2 M allΓ p2).
    unfold seqValuation in IH1v. unfold seqValuation in IH2v.
    rewrite strValuationToFormValuationRight in IH1v.
    rewrite strValuationToFormValuationRight in IH2v.
    apply IH1v in FVXx. apply IH2v in FVYy.
    simpl.
    exists p1.
    split. 1: assumption.
    exists p2. auto.
Qed.
