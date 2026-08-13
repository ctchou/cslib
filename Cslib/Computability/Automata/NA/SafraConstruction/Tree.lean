/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Descriptive.Tree

/-! # Additions to the theory of trees in the sense of descriptive set theory

-/

@[expose] public section

namespace Descriptive.Tree

variable {α : Type*}

abbrev Finite (T : tree α) : Prop :=
  T.val.Finite

def kidsAt (T : tree α) (x : List α) : Set α :=
  { a | x ++ [a] ∈ T }

abbrev IsLeaf (T : tree α) (x : List α) : Prop :=
  kidsAt T x = ∅

def Ordered [LE α] (T : tree α) : Prop :=
  ∀ x : T, IsLowerSet (kidsAt T x)

noncomputable def packPath (T : tree ℕ) : List ℕ → List ℕ
  | [] => []
  | n :: x => {k | k < n ∧ [k] ∈ T}.ncard :: (packPath (subAt T [n]) x)

theorem length_packPath (T : tree ℕ) (x : List ℕ) : (packPath T x).length = x.length := by
  induction x generalizing T with
  | nil => rfl
  | cons n x ih => simp [packPath, ih]

theorem packPath_append (T : tree ℕ) (x y : List ℕ) :
    ∃ z, packPath T (x ++ y) = packPath T x ++ z := by
  induction x generalizing T with
  | nil => exact ⟨packPath T y, rfl⟩
  | cons n x ih =>
    obtain ⟨z, hz⟩ := ih (subAt T [n])
    exact ⟨z, by simp [packPath, hz]⟩

noncomputable def pack (T : tree ℕ) : tree ℕ where
  val := packPath T '' T.val
  property := by
    rintro x a ⟨y, hy, hxy⟩
    induction y using List.reverseRecOn with
    | nil => simp [packPath] at hxy
    | append_singleton y' b _ =>
      obtain ⟨z, hz⟩ := packPath_append T y' [b]
      refine ⟨y', mem_of_append hy, ?_⟩
      rw [hz] at hxy
      refine (List.append_inj hxy ?_).1
      have h1 := congrArg List.length hxy
      have h2 := congrArg List.length hz
      simp [length_packPath] at h1 h2 ⊢
      lia

theorem packPath_concat (T : tree ℕ) (y : List ℕ) (n : ℕ) :
    packPath T (y ++ [n]) = packPath T y ++ [{k | k < n ∧ y ++ [k] ∈ T}.ncard] := by
  induction y generalizing T with
  | nil => simp [packPath]
  | cons m y ih => simp [packPath, ih]

theorem pack_ordered (T : tree ℕ) : Ordered (pack T) := by
  classical
  rintro ⟨x, hx⟩ a b hba ⟨y, hy, hxy⟩
  induction y using List.reverseRecOn with
  | nil => simp [packPath] at hxy
  | append_singleton y n _ =>
    rw [packPath_concat] at hxy
    obtain ⟨rfl, h2⟩ := List.append_inj' hxy rfl
    obtain rfl := List.singleton_inj.mp h2
    let p := fun k => y ++ [k] ∈ T
    have hcount : ∀ m, {k | k < m ∧ y ++ [k] ∈ T}.ncard = Nat.count p m := by
      intro m
      rw [Nat.count_eq_card_filter_range, ← Set.ncard_coe_finset]
      congr
      ext k
      simp [p]
    rcases hba.lt_or_eq with hlt | rfl
    · rw [hcount] at hlt
      have hcard : ∀ hf : (Set.ofPred p).Finite, b < hf.toFinset.card :=
        fun hf => hlt.trans_le (Nat.count_le_card hf n)
      exact ⟨y ++ [Nat.nth p b], Nat.nth_mem b hcard, by
        rw [packPath_concat, hcount, Nat.count_nth hcard]⟩
    · exact ⟨y ++ [n], hy, by rw [packPath_concat]⟩

end Descriptive.Tree
