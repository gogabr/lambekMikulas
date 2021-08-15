Require Import List.
Import ListNotations.
From Coq Require Import Relations.
Require Import Coq.Logic.Classical_Prop.
Require Import NonEmptyList.
Require Import LambekSyntax.
Require Import SyntaxOps.
Require Import Semantics.
Require Import Singleton.

Lemma completeness: forall Γ s, Γ ⊨ s -> Γ ⊢ s.
Admitted.
