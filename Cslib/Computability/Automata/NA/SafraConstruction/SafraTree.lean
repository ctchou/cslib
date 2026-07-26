/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.SafraConstruction.VTree

/-! # Safra tree

-/

@[expose] public section

namespace Cslib

open Finset

structure SafraVal (S : Type*) where
  stable : Bool
  acc : Bool
  set : Finset S

abbrev SafraTree (S : Type*) := VTree (SafraVal S)

namespace SafraTree

variable {S : Type*} [DecidableEq S]

abbrev set (t : SafraTree S) : Finset S :=
  t.val.set

abbrev stable (t : SafraTree S) : Bool :=
  t.val.stable

abbrev acc (t : SafraTree S) : Bool :=
  t.val.acc

abbrev kids (t : SafraTree S) : List (SafraTree S) :=
  VTree.kids t

abbrev mk (stable : Bool) (acc : Bool) (set : Finset S) (kids : List (SafraTree S)) : SafraTree S :=
  {val := ⟨stable, acc, set⟩, kids := kids}

def nodeWellFormed (n : SafraTree S) : Prop :=
  n.kids.foldl (· ∪ set ·) ∅ ⊂ n.set ∧
  n.kids.Pairwise (fun k1 k2 ↦ Disjoint k1.set k2.set) ∧
  (n.acc → n.kids = []) ∧
  (∀ i, (_ : i < n.kids.length) →
    n.kids[i].stable → n.stable ∧ ∀ j, (_ : j < i) → n.kids[j].stable)

def WellFormed (t : SafraTree S) : Prop :=
  t.Forall nodeWellFormed

def nextAux (trans : Finset S → Finset S) (accept : Finset S)
    (stableInp : Bool) (seenInp : Finset S) : SafraTree S → SafraTree S
  | {kids := kidsInp, val := {set := setInp, ..}} =>
    let (stableNew, seenNew, kidsNew) := kidsInp.foldl (fun (stableFold, seenFold, kidsFold) kid ↦
      let kidNew := nextAux trans accept stableFold seenFold kid
      if kidNew.set = ∅
      then (false, seenFold, kidsFold)
      else (stableFold, seenFold ∪ kidNew.set, kidsFold ++ [kidNew])
    ) (stableInp, ∅, [])
    let setOut := trans setInp \ seenInp
    let setAcc := (setOut ∩ accept) \ seenNew
    let kidsOut := if setAcc = ∅ then kidsNew else kidsNew ++ [mk stableNew false setAcc []]
    let accOut := setOut ≠ ∅ ∧ kidsOut.foldl (· ∪ set ·) ∅ = setOut
    mk stableInp accOut setOut (if accOut then [] else kidsOut)

def next (trans : Finset S → Finset S) (accept : Finset S) : SafraTree S → SafraTree S :=
  nextAux trans accept true ∅

theorem next_wellFormed (trans : Finset S → Finset S) (accept : Finset S) {t : SafraTree S}
    (h : t.WellFormed) : (t.next trans accept).WellFormed := by
  sorry

end SafraTree

end Cslib
