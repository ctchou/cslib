/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.SetTheory.Descriptive.Tree

/-! # Additions to the theory of trees in the sense of descriptive set theory

-/

@[expose] public section

namespace Descriptive.Tree

variable {α : Type*}

def kidsAt (T : tree α) (x : T) : Set α :=
  { a | x ++ [a] ∈ T }

def Ordered [LE α] (T : tree α) : Prop :=
  ∀ x : T, IsLowerSet (kidsAt T x)

end Descriptive.Tree
