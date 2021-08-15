Require Import List.
Import ListNotations.

Definition splitNE {T: Type} (l: list T) (p: l <> []):
                             sig (fun s: T * list T => l = fst s :: snd s).
Proof.
  destruct l as [|X x].
  - congruence.
  - exists (X, x).
    reflexivity.
Defined.

Definition splitNEs {T: Type} (l: list T) (p: [] <> l):
                             sig (fun s: T * list T => l = fst s :: snd s).
Proof.
  apply (splitNE l).
  apply not_eq_sym.
  assumption.
Defined.

Definition splitTl {T: Type} (h: list T) (E: T) (z: list T):
                             sig (fun s: T * list T => h ++ E :: z = fst s :: snd s).
Proof.
  apply (splitNEs (h ++ E :: z)).
  apply app_cons_not_nil.
Defined.

Definition rSplitNE {T: Type} (l: list T) (p: l <> []):
                             sig (fun s: list T * T => l = fst s ++ [snd s]).
Proof.
  Search _ (?x ++ ?y::?z).
  destruct (exists_last p) as [x [X a]].
  exists (x,X).
  simpl.
  exact a.
Defined.

Definition rSplitNEs {T: Type} (l: list T) (p: [] <> l):
                             sig (fun s: list T * T => l = fst s ++ [snd s]).
Proof.
  apply (rSplitNE l).
  apply not_eq_sym.
  assumption.
Defined.

Definition rSplitTl {T: Type} (h: list T) (E: T) (z: list T):
                             sig (fun s: list T * T => h ++ E :: z = fst s ++ [snd s]).
Proof.
  apply (rSplitNEs (h ++ E :: z)).
  apply app_cons_not_nil.
Defined.
