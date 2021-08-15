Require Import List.
Import ListNotations.
From Coq Require Import Relations.
Require Import Coq.Logic.Classical_Prop.
Require Import NonEmptyList.
Require Import LambekSyntax.
Require Import Semantics.

Inductive singleton: Set := Sing.
Definition totalOnSingleton (_ _:singleton) := True.
Definition allSingleton (_:Wpoint singleton totalOnSingleton) := True.
Definition valOnSingleton := fun (_:elem_cat) => allSingleton.
Definition WpointOnSingleton := exist (fun (_: singleton * singleton) => True) (Sing, Sing) I.

Lemma transitiveOnSingleton : transitive singleton totalOnSingleton.
Proof.
  unfold transitive.
  intros x y z T1 T2.
  unfold totalOnSingleton.
  exact I.
Qed.

Lemma allEqualOnSingleton: forall (x y: Wpoint singleton totalOnSingleton), x = y.
Proof.
  intros.
  destruct x as [[[] []] []]. destruct y as [[[] []] []]. reflexivity.
Qed.

Lemma allTrueOnSingleton: forall (A: formula)  (p: Wpoint singleton totalOnSingleton),
    formValuation singleton totalOnSingleton valOnSingleton A p.
  intros. induction A as [v| A IHA B IHB | A IHA B IHB | A IHA B IHB].
  - apply I.
  - simpl. intros.
    assert (p = z) as PZ by apply allEqualOnSingleton.
    rewrite <- PZ. assumption.
  - simpl. intros.
    assert (p = z) as PZ by apply allEqualOnSingleton.
    rewrite <- PZ. assumption.
  - simpl.
    exists WpointOnSingleton. split.
    + assert (p = WpointOnSingleton) as PP by apply allEqualOnSingleton.
      rewrite <- PP. assumption.
    + exists WpointOnSingleton. split.
      * assert (p = WpointOnSingleton) as PP by apply allEqualOnSingleton.
        rewrite <- PP. assumption.
      * unfold C. simpl. destruct p. simpl. destruct x as [[] []]. simpl. auto.
Qed.
