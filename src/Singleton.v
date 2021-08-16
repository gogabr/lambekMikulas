Require Import List.
Import ListNotations.
From Coq Require Import Relations.
Require Import Coq.Logic.Classical_Prop.
Require Import NonEmptyList.
Require Import LambekSyntax.
Require Import Semantics.

Inductive singleton: Set := Sing.
Definition totalOnSingleton (_ _:singleton) := True.

Lemma transitiveOnSingleton : transitive singleton totalOnSingleton.
Proof.
  unfold transitive.
  intros x y z T1 T2.
  unfold totalOnSingleton.
  exact I.
Qed.

Definition singletonFrame: frame := exist _ (existT _ _ totalOnSingleton) transitiveOnSingleton.

Definition allSingleton (_:Wpoint singletonFrame) := True.
Definition valOnSingleton := fun (_:elem_cat) => allSingleton.
Definition WpointOnSingleton := exist (fun (_: singleton * singleton) => True) (Sing, Sing) I.

Lemma allEqualOnSingleton: forall (x y: Wpoint singletonFrame), x = y.
Proof.
  intros.
  destruct x as [[[] []] []]. destruct y as [[[] []] []]. reflexivity.
Qed.

Lemma allTrueOnSingleton: forall (A: formula)  (p: Wpoint singletonFrame),
    formValuation singletonFrame valOnSingleton A p.
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
