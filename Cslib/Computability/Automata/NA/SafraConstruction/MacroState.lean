/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.SafraConstruction.DeepLeftOrder
public import Cslib.Computability.Automata.NA.SafraConstruction.Tree
public import Cslib.Foundations.Semantics.FLTS.Basic
public import Cslib.Foundations.Semantics.LTS.SetImage

/-! # Safra Tree

-/

@[expose] public section

namespace Cslib.SafraConstruction

variable {State Symbol : Type*}

open Descriptive

structure MacroState (State : Type*) where
  states : Set State
  branch : states → List ℕ
  accept : Set (List ℕ)

namespace MacroState

def IsTree (ms : MacroState State) (t : tree ℕ) : Prop :=
  Set.range ms.branch = t.val

def AccAtLeaf (ms : MacroState State) (t : tree ℕ) : Prop :=
  ∀ x ∈ ms.accept, Tree.IsLeaf t x

def WellFormed (ms : MacroState State) : Prop :=
  ∃ t : tree ℕ, Tree.Ordered t ∧ ms.IsTree t ∧ ms.AccAtLeaf t

end MacroState

def macroTransConsistency (lts : LTS State Symbol) (flts : FLTS (MacroState State) Symbol) : Prop :=
  ∀ ms a, (flts.tr ms a).states = lts.setImage ms.states a

end Cslib.SafraConstruction
