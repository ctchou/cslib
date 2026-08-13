/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Computability.Automata.NA.SafraConstruction.DeepLeftOrder
public import Cslib.Computability.Automata.NA.SafraConstruction.Tree

/-! # Safra Tree

-/

@[expose] public section

namespace Cslib.SafraConstruction

variable {State Symbol : Type*}

open Descriptive Set

structure MacroState (State : Type*) where
  states : Set State
  safraMap : states → List ℕ
  stableTree : tree ℕ
  accept : Set (List ℕ)

namespace MacroState

def safraTree (ms : MacroState State) : tree ℕ := treeOf (range ms.safraMap)

def safraSet (ms : MacroState State) (x : List ℕ) := {s | ms.safraMap s = x}

structure WellFormed (ms : MacroState State) : Prop where
  safraTree_orderd : Tree.Ordered ms.safraTree
  stableTree_ordered : Tree.Ordered ms.stableTree
  stableTree_subtree_safraTree : ms.stableTree ≤ ms.safraTree
  safraMap_surjOn_safraTree : SurjOn ms.safraMap univ ms.safraTree.val
  accept_subset_stableTree : ms.accept ⊆ ms.stableTree.val
  accept_leaf_stableTree : ∀ x ∈ ms.accept, Tree.IsLeaf ms.stableTree x

end MacroState

section MacroTrans

open Automata

variable (na : NA.Buchi State Symbol) (mda : DA.Rabin (MacroState State) Symbol)
  {ms ms' : MacroState State} {a : Symbol} (hmda : mda.tr ms a = ms')

def wellFormed_invariant : Prop := ms.WellFormed → ms'.WellFormed

def stable_backward : Prop :=
  ∀ x, x ∈ ms'.stableTree → ∀ s' ∈ ms'.safraSet x, ∃ s ∈ ms.safraSet x, na.Tr s a s'

def safraMap_forward : Prop :=
  ∀ s s', na.Tr s a s' →
    ∀ h : s ∈ ms.states, ∃ h' : s' ∈ ms'.states,
    let x := ms.safraMap ⟨s, h⟩
    let x' := ms'.safraMap ⟨s', h'⟩
    DeepLeft x' x ∧
    (x' ∈ ms'.stableTree → x = x') ∧
    (x' ∈ ms'.accept → s' ∈ na.accept)

end MacroTrans

end Cslib.SafraConstruction
