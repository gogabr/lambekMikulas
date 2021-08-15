Require Import List.
Import ListNotations.
From Coq Require Import Relations.
Require Import Coq.Logic.Classical_Prop.
Require Import NonEmptyList.
Require Import LambekSyntax.
Require Import Semantics.

Inductive Singleton: Set := Sing.
Definition TotalOnSingleton (_ _:Singleton) := True.
Definition AllSingleton (_:Wpoint Singleton TotalOnSingleton) := True.
Definition ValOnSingleton := fun (_:types) => AllSingleton.
Definition WpointOnSingleton := exist (fun (_: Singleton * Singleton) => True) (Sing, Sing) I.

Lemma TransitiveOnSingleton : transitive Singleton TotalOnSingleton.
Proof.
  unfold transitive.
  intros x y z T1 T2.
  unfold TotalOnSingleton.
  exact I.
Qed.

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
