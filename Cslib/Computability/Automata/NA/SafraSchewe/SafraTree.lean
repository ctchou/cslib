/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Data.Descriptive.Tree

/-! # History map

-/

@[expose] public section

namespace Cslib

section DeepLeftOrder

def DeepLeft (p1 p2 : List ℕ) : Prop :=
  p2 <+: p1 ∨ (p1 < p2 ∧ ¬ p1 <+: p2)

variable {p1 p2 p3 : List ℕ}

theorem deepLeft_total (p1 p2 : List ℕ) :
    DeepLeft p1 p2 ∨ DeepLeft p2 p1 := by
  grind [DeepLeft]

theorem deepLeft_refl (p : List ℕ) : DeepLeft p p := by
  grind [DeepLeft]

theorem deepLeft_antisymm :
    DeepLeft p1 p2 → DeepLeft p2 p1 → p1 = p2 := by
  grind [DeepLeft, List.IsPrefix.eq_of_length_le]

theorem deepLeft_trans :
    DeepLeft p1 p2 → DeepLeft p2 p3 → DeepLeft p1 p3 := by
  rintro (_ | _) (_ | _)
  · grind [DeepLeft]
  · sorry
  · sorry
  · sorry

end DeepLeftOrder

open Descriptive

structure SafraTree (α : Type*) where
  skel : tree ℕ
  set : skel → Set α
  acc : skel → Prop

namespace SafraTree

variable {α : Type*} {t : SafraTree α}

def SkelOrdered (t : SafraTree α) : Prop :=
  Tree.Ordered t.skel

def SetPairDisj (t : SafraTree α) : Prop :=
  Set.univ.PairwiseDisjoint t.set

def SetNeEmpty (t : SafraTree α) : Prop :=
  ∀ x : t.skel, t.set x ≠ ∅

def AccAtLeaf (t : SafraTree α) : Prop :=
  ∀ x : t.skel, t.acc x → t.set x ≠ ∅

def WellFormed (t : SafraTree α) : Prop :=
  t.SkelOrdered ∧ t.SetPairDisj ∧ t.SetNeEmpty ∧ t.AccAtLeaf

def subtreeUnion (t : SafraTree α) (x : List ℕ) : Set α :=
  let subtree := Tree.pullSub (Tree.subAt t.skel x) x
  ⋃ y, ⋃ hy : y ∈ subtree, t.set ⟨y, Tree.pullSub_subAt t.skel x hy⟩

abbrev treeUnion (t : SafraTree α) := t.subtreeUnion []

def dedup (t : SafraTree α) : SafraTree α where
  skel := t.skel
  acc := t.acc
  set (x : t.skel) := {a | a ∈ t.set x ∧ ∀ y : t.skel, a ∈ t.set y → DeepLeft x.val y.val}

theorem dedup_ensures (t : SafraTree α) :
    t.dedup.treeUnion = t.treeUnion ∧
    t.dedup.SetPairDisj ∧ t.dedup.skel = t.skel ∧ t.dedup.acc = t.acc := by
  sorry

def Continuable (t : SafraTree α) (x : List ℕ) : Prop :=
  ∀ y, y <+: x → ∃ h : y ∈ t.skel, t.set ⟨y, h⟩ ≠ ∅

def Collapsable (t : SafraTree α) (x : List ℕ) : Prop :=
  ∃ h : x ∈ t.skel, t.set ⟨x, h⟩ = ∅ ∧ subtreeUnion t x ≠ ∅ ∧
    ∃ y a, y ++ [a] = x ∧ t.Continuable y

def trimmedSkel (t : SafraTree α) : tree ℕ where
  val := { x | t.Continuable x ∨ t.Collapsable x }
  property := by
    rintro x a (_ | ⟨_, _⟩)
    · grind [Continuable]
    · grind [List.append_singleton_inj]

theorem trimmedSkel_le_skel (t : SafraTree α) : t.trimmedSkel ≤ t.skel := by
  rintro x (h | ⟨_, _⟩)
  · obtain ⟨_, _⟩ := h x (List.prefix_refl x)
    assumption
  · assumption

open Classical in
def trim (t : SafraTree α) : SafraTree α where
  skel := t.trimmedSkel
  set (x : t.trimmedSkel) :=
    if t.Collapsable x.val then t.subtreeUnion x.val
    else t.set ⟨x.val, trimmedSkel_le_skel t x.property⟩
  acc (x : t.trimmedSkel) := t.Collapsable x.val

theorem trim_ensures (t : SafraTree α) (h : t.SetPairDisj) :
    t.trim.treeUnion = t.treeUnion ∧ t.trim.SetPairDisj ∧
    t.trim.SetNeEmpty ∧ t.trim.AccAtLeaf ∧ t.trim.skel ≤ t.skel := by
  sorry

end SafraTree

end Cslib
