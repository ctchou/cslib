/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Relation.Defs

/-! # More definitions and theorems about relation

## References
-/

@[expose] public section

namespace Relation

variable {α : Type*}

/-- The successors of an element `a` is the set of all elements `b` such that `r a b`. -/
abbrev successors (r : α → α → Prop) (a : α) : Set α := {b | r a b}

/-- The predecessors of an element `a` is the set of all elements `b` such that `r b a`. -/
abbrev predecessors (r : α → α → Prop) (a : α) : Set α := {b | r b a}

def restrict (r : α → α → Prop) (s : Set α) : α → α → Prop :=
  fun a b ↦ a ∈ s ∧ b ∈ s ∧ r a b

def IsStrictTotalOrderOn (s : Set α) (r : α → α → Prop) : Prop :=
  IsStrictOrder α r ∧
  ∀ a b, a ∈ s → b ∈ s → a = b ∨ r a b ∨ r b a

def IsIntervalOrder (r : α → α → Prop) : Prop :=
  ∀ a1 b1 a2 b2, r a1 b1 ∧ r a2 b2 → r a1 b2 ∨ r a2 b1

end Relation
