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
public import Cslib.Foundations.Semantics.LTS.SetImage

/-! # Safra Tree

-/

@[expose] public section

namespace Cslib.SafraConstruction

variable {State Symbol : Type*}

open Descriptive Set Automata

structure MacroState (State : Type*) where
  states : Set State
  safraHost : states → List ℕ
  stableTree : tree ℕ
  accept : Set (List ℕ)

namespace MacroState

def safraTree (ms : MacroState State) : tree ℕ :=
  treeOf (range ms.safraHost)

theorem leaf_prefix_eq_self (ms : MacroState State) {x : List ℕ} {s : State} (h : s ∈ ms.states)
    (hl : x ∈ Tree.leaves ms.safraTree) (hp : x <+: ms.safraHost ⟨s, h⟩) :
    ms.safraHost ⟨s, h⟩ = x := by
  obtain ⟨r, hr⟩ := hp
  cases r with
  | nil => simpa using hr.symm
  | cons k r =>
    have hk : k ∈ Tree.kidsAt ms.safraTree x :=
      ⟨_, ⟨⟨s, h⟩, rfl⟩, ⟨r, by simp [← hr]⟩⟩
    have hleaf' : Tree.kidsAt ms.safraTree x = ∅ := hl.2
    simp [hleaf'] at hk

structure WellFormed (ms : MacroState State) : Prop where
  safraTree_orderd : Tree.Ordered ms.safraTree
  stableTree_ordered : Tree.Ordered ms.stableTree
  stableTree_sub_safraTree : ms.stableTree ≤ ms.safraTree
  safraHost_surjOn_safraTree : SurjOn ms.safraHost univ ms.safraTree.val
  accept_leaf : ms.accept ⊆ Tree.leaves ms.safraTree

end MacroState

structure SafraSpec (na : NA.Buchi State Symbol) (mda : DA.Rabin (MacroState State) Symbol) :
    Prop where
  start_states : mda.start.states = na.start
  start_wf : mda.start.WellFormed
  --
  wf_inv : ∀ ms a, ms.WellFormed → (mda.tr ms a).WellFormed
  states_image : ∀ ms a, (mda.tr ms a).states = na.setImage ms.states a
  forward : ∀ ms a, let ms' := mda.tr ms a
    ∀ s s' (h : s ∈ ms.states) (h' : s' ∈ ms'.states), na.Tr s a s' →
    let x := ms.safraHost ⟨s, h⟩
    let x' := ms'.safraHost ⟨s', h'⟩
    ( (DeepLeft x' x ∧ (s' ∈ na.accept → x' ≠ x)) ∨
      (x' <+: x ∧ x' ∈ ms'.accept) ) ∧
    (∀ y, y <+: x → y <+: x' → y ∈ ms'.stableTree)
  backward : ∀ ms a, let ms' := mda.tr ms a
    ∀ s' (h' : s' ∈ ms'.states),
    ∀ x, x ∈ ms.safraTree → x ∈ ms'.stableTree → x <+: ms'.safraHost ⟨s', h'⟩ →
      ∃ s, ∃ h : s ∈ ms.states, na.Tr s a s' ∧ x <+: ms.safraHost ⟨s, h⟩ ∧
        ( (x ≠ ms'.safraHost ⟨s', h'⟩ ∨ x ∈ ms'.accept) →
          (x ≠ ms.safraHost ⟨s, h⟩ ∨ s' ∈ na.accept) )
  --
  pairs : mda.pairs =
    range fun x : List ℕ => ({ms | x ∈ ms.accept}, {ms | x ∉ ms.stableTree})

variable {na : NA.Buchi State Symbol} {mda : DA.Rabin (MacroState State) Symbol}

theorem macro_mtr_wellFormed (hs : SafraSpec na mda) (ms : MacroState State) (as : List Symbol)
    (h : ms.WellFormed) : (mda.mtr ms as).WellFormed := by
  induction as generalizing ms with
  | nil => exact h
  | cons a as ih => exact ih (mda.tr ms a) (hs.wf_inv ms a h)

theorem macro_mtr_states (hs : SafraSpec na mda) (ms : MacroState State) (as : List Symbol) :
    (mda.mtr ms as).states = List.foldl na.setImage ms.states as := by
  induction as generalizing ms with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, ← hs.states_image]
    exact ih (ms := mda.tr ms a)

end Cslib.SafraConstruction
