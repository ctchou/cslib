/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.SafraConstruction.DeepLeftOrder
public import Cslib.Computability.Automata.NA.SafraConstruction.Tree

/-! # History map

-/

@[expose] public section

namespace Cslib

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
  ∀ x : t.skel, t.acc x → Tree.IsLeaf t.skel x

def WellFormed (t : SafraTree α) : Prop :=
  t.SkelOrdered ∧ t.SetPairDisj ∧ t.SetNeEmpty ∧ t.AccAtLeaf

def subtreeUnion (t : SafraTree α) (x : List ℕ) : Set α :=
  ⋃ y, ⋃ hy : y ∈ Tree.subAt t.skel x, t.set ⟨x ++ y, hy⟩

abbrev treeUnion (t : SafraTree α) := t.subtreeUnion []

theorem mem_subtreeUnion {a : α} {x : List ℕ} :
    a ∈ t.subtreeUnion x ↔ ∃ y : t.skel, x <+: y.val ∧ a ∈ t.set y := by
  simp only [subtreeUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨z, hz, ha⟩
    exact ⟨⟨x ++ z, hz⟩, List.prefix_append x z, ha⟩
  · rintro ⟨⟨_, hy⟩, ⟨z, rfl⟩, ha⟩
    exact ⟨z, hy, ha⟩

theorem mem_treeUnion {a : α} : a ∈ t.treeUnion ↔ ∃ x : t.skel, a ∈ t.set x := by
  simp [mem_subtreeUnion]

def dedup (t : SafraTree α) : SafraTree α where
  skel := t.skel
  acc := t.acc
  set (x : t.skel) := {a | a ∈ t.set x ∧ ∀ y : t.skel, a ∈ t.set y → DeepLeft x.val y.val}

theorem dedup_ensures (t : SafraTree α) (h : Tree.Finite t.skel) :
    t.dedup.treeUnion = t.treeUnion ∧ t.dedup.SetPairDisj ∧
    t.dedup.skel = t.skel ∧ t.dedup.acc = t.acc := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · ext a
    simp only [mem_treeUnion]
    constructor
    · rintro ⟨x, hx, -⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      let S := {y : List ℕ | ∃ hy : y ∈ t.skel, a ∈ t.set ⟨y, hy⟩}
      have hfin : S.Finite := h.subset fun y ⟨hy, _⟩ => hy
      obtain ⟨m, hm, hmin⟩ := deepLeft_finset_min hfin.toFinset ⟨x.val, by simpa [S] using hx⟩
      obtain ⟨hm', ha⟩ : m ∈ S := by simpa using hm
      exact ⟨⟨m, hm'⟩, ha, fun y hy => hmin y.val (by simpa [S] using hy)⟩
  · intro x _ y _ hxy
    refine Set.disjoint_left.mpr fun a ha hb => hxy (Subtype.ext ?_)
    exact deepLeft_antisymm (ha.2 y hb.1) (hb.2 x ha.1)

def Continuable (t : SafraTree α) (x : List ℕ) : Prop :=
  ∀ y, y <+: x → ∃ h : y ∈ t.skel, t.set ⟨y, h⟩ ≠ ∅

def Collapsable (t : SafraTree α) (x : List ℕ) : Prop :=
  ∃ h : x ∈ t.skel, t.set ⟨x, h⟩ = ∅ ∧ subtreeUnion t x ≠ ∅ ∧
    (x = [] ∨ ∃ y a, y ++ [a] = x ∧ t.Continuable y)

def trimmedSkel (t : SafraTree α) : tree ℕ where
  val := { x | t.Continuable x ∨ t.Collapsable x }
  property := by
    rintro x a (_ | ⟨_, _⟩)
    · grind [Continuable]
    · grind [List.append_singleton_inj, List.append_eq_nil_iff]

theorem trimmedSkel_le_skel (t : SafraTree α) : t.trimmedSkel ≤ t.skel := by
  rintro x (h | ⟨_, _⟩)
  · obtain ⟨_, _⟩ := h x (List.prefix_refl x)
    assumption
  · assumption

open Classical in
noncomputable def trim (t : SafraTree α) : SafraTree α where
  skel := t.trimmedSkel
  set (x : t.trimmedSkel) :=
    if t.Collapsable x.val then t.subtreeUnion x.val
    else t.set ⟨x.val, trimmedSkel_le_skel t x.property⟩
  acc (x : t.trimmedSkel) := t.Collapsable x.val

/-- A collapsable node has no proper descendant in the trimmed skeleton. -/
theorem eq_of_collapsable_of_prefix {x y : List ℕ} (hx : t.Collapsable x)
    (hy : y ∈ t.trimmedSkel) (hxy : x <+: y) : y = x := by
  obtain ⟨_, hxe, -, -⟩ := hx
  rcases hy with hy | ⟨-, -, -, rfl | ⟨y', b, rfl, hy'⟩⟩
  · obtain ⟨_, hne⟩ := hy x hxy
    exact absurd hxe hne
  · exact (List.prefix_nil.mp hxy).symm
  · rcases List.prefix_concat_iff.mp hxy with rfl | hxy'
    · rfl
    · obtain ⟨_, hne⟩ := hy' x hxy'
      exact absurd hxe hne

/-- Every node of the skeleton is either continuable or has a prefix with an empty set
all of whose strict prefixes have nonempty sets. -/
theorem continuable_or_empty_prefix (y : List ℕ) (hy : y ∈ t.skel) :
    t.Continuable y ∨ ∃ z, z <+: y ∧ ∃ hz : z ∈ t.skel, t.set ⟨z, hz⟩ = ∅ ∧
      (z = [] ∨ ∃ y' b, y' ++ [b] = z ∧ t.Continuable y') := by
  induction y using List.reverseRecOn with
  | nil =>
    by_cases he : t.set ⟨[], hy⟩ = ∅
    · exact Or.inr ⟨[], List.prefix_refl _, hy, he, Or.inl rfl⟩
    · left
      intro z hz
      obtain rfl := List.prefix_nil.mp hz
      exact ⟨hy, he⟩
  | append_singleton y' b ih =>
    rcases ih (Tree.mem_of_append hy) with hc | ⟨z, hz, rest⟩
    · by_cases he : t.set ⟨y' ++ [b], hy⟩ = ∅
      · exact Or.inr ⟨_, List.prefix_refl _, hy, he, Or.inr ⟨y', b, rfl, hc⟩⟩
      · left
        intro z hz
        rcases List.prefix_concat_iff.mp hz with rfl | hz'
        · exact ⟨hy, he⟩
        · exact hc z hz'
    · exact Or.inr ⟨z, hz.trans (List.prefix_append _ _), rest⟩

theorem trim_ensures (t : SafraTree α) (h : t.SetPairDisj) :
    t.trim.treeUnion = t.treeUnion ∧ t.trim.SetPairDisj ∧
    t.trim.SetNeEmpty ∧ t.trim.AccAtLeaf ∧ t.trim.skel ≤ t.skel := by
  have same : ∀ {a : α} {w1 w2 : t.skel}, a ∈ t.set w1 → a ∈ t.set w2 → w1 = w2 := by
    intro a w1 w2 h1 h2
    by_contra hne
    exact Set.disjoint_left.mp (h (Set.mem_univ _) (Set.mem_univ _) hne) h1 h2
  refine ⟨?_, ?_, ?_, ?_, trimmedSkel_le_skel t⟩
  · ext a
    simp only [mem_treeUnion]
    constructor
    · rintro ⟨x, ha⟩
      simp only [trim] at ha
      split_ifs at ha with hc
      · obtain ⟨w, -, hw⟩ := mem_subtreeUnion.mp ha
        exact ⟨w, hw⟩
      · exact ⟨_, ha⟩
    · rintro ⟨⟨y, hy⟩, ha⟩
      rcases continuable_or_empty_prefix y hy with hc | ⟨z, hz, hzs, hze, hzr⟩
      · have hnc : ¬ t.Collapsable y := by
          rintro ⟨_, he, -⟩
          exact Set.notMem_empty a (he ▸ ha)
        refine ⟨⟨y, Or.inl hc⟩, ?_⟩
        simp only [trim, hnc, ↓reduceIte]
        exact ha
      · have haz : a ∈ t.subtreeUnion z := mem_subtreeUnion.mpr ⟨⟨y, hy⟩, hz, ha⟩
        have hcz : t.Collapsable z :=
          ⟨hzs, hze, Set.nonempty_iff_ne_empty.mp ⟨a, haz⟩, hzr⟩
        refine ⟨⟨z, Or.inr hcz⟩, ?_⟩
        simp only [trim, hcz, ↓reduceIte]
        exact haz
  · rintro ⟨x, hx⟩ - ⟨y, hy⟩ - hxy
    refine Set.disjoint_left.mpr fun a ha hb => hxy ?_
    simp only [trim] at ha hb
    split_ifs at ha hb with hcx hcy hcy
    · obtain ⟨w1, hw1, ha⟩ := mem_subtreeUnion.mp ha
      obtain ⟨w2, hw2, hb⟩ := mem_subtreeUnion.mp hb
      obtain rfl := same ha hb
      rcases List.prefix_or_prefix_of_prefix hw1 hw2 with h' | h'
      · exact Subtype.ext (eq_of_collapsable_of_prefix hcx hy h').symm
      · exact Subtype.ext (eq_of_collapsable_of_prefix hcy hx h')
    · obtain ⟨w1, hw1, ha⟩ := mem_subtreeUnion.mp ha
      obtain rfl := same ha hb
      exact Subtype.ext (eq_of_collapsable_of_prefix hcx hy hw1).symm
    · obtain ⟨w2, hw2, hb⟩ := mem_subtreeUnion.mp hb
      obtain rfl := same ha hb
      exact Subtype.ext (eq_of_collapsable_of_prefix hcy hx hw2)
    · have hxy' := same ha hb
      simp only [Subtype.mk.injEq] at hxy'
      exact Subtype.ext hxy'
  · rintro ⟨x, hx⟩
    simp only [trim]
    split_ifs with hc
    · obtain ⟨_, _, hne, _⟩ := hc
      exact hne
    · rcases hx with hx | hx
      · obtain ⟨_, hne⟩ := hx x (List.prefix_refl x)
        exact hne
      · exact absurd hx hc
  · rintro ⟨x, hx⟩ hacc
    ext b
    simp only [Tree.kidsAt, Set.mem_empty_iff_false, iff_false]
    intro hb
    have := eq_of_collapsable_of_prefix hacc hb (List.prefix_append _ _)
    simp at this

end SafraTree

end Cslib
