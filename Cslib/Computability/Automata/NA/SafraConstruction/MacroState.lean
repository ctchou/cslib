/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.SafraConstruction.DeepLeftOrder
public import Cslib.Computability.Automata.NA.SafraConstruction.Tree

/-! # Safra Tree

-/

@[expose] public section

namespace Cslib

open Descriptive

structure MacroState (State : Type*) where
  states : Set State
  branch : states → List ℕ
  accept : Set (List ℕ)

namespace MacroState

variable {State : Type*}

def HasTree (ms : MacroState State) (t : tree ℕ) : Prop :=
  Set.range ms.branch = t.val

def AccAtLeaf (ms : MacroState State) (t : tree ℕ) : Prop :=
  ∀ x ∈ ms.accept, Tree.IsLeaf t x

def WellFormed (ms : MacroState State) : Prop :=
  ∃ t : tree ℕ, Tree.Ordered t ∧ ms.HasTree t ∧ ms.AccAtLeaf t

end MacroState

end Cslib
