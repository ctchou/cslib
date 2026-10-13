/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Relation.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-! # Encodable
-/

@[expose] public section

open Function Relation Set

namespace Encodable

section ToStrictWellOrder

variable {α : Type*} [en : Encodable α]

abbrev linearOrder : LinearOrder α :=
  LinearOrder.lift' encode encode_injective

attribute [local instance] linearOrder

noncomputable abbrev locallyFiniteOrder : LocallyFiniteOrder α :=
  .ofFiniteIcc fun a b =>
    (Set.finite_Icc (encode a) (encode b)).preimage encode_injective.injOn

attribute [local instance] locallyFiniteOrder

noncomputable abbrev predOrder : PredOrder α :=
  LinearLocallyFiniteOrder.predOrder α

noncomputable abbrev succOrder : SuccOrder α :=
  LinearLocallyFiniteOrder.succOrder α

abbrev lt : α → α → Prop := linearOrder.lt

abbrev le : α → α → Prop := linearOrder.le

noncomputable abbrev pred : α → α := predOrder.pred

noncomputable abbrev succ : α → α := succOrder.succ

theorem lt_isStrictTotalOrder : IsStrictTotalOrder α lt :=
  @instIsStrictTotalOrderLt α linearOrder

theorem lt_finite_predecessors (a : α) : (predecessors lt a).Finite :=
  (finite_lt_nat (encode a)).preimage encode_injective.injOn

theorem lt_wellFounded : WellFounded (α := α) lt :=
  InvImage.wf encode wellFounded_lt

end ToStrictWellOrder

section OfStrictWellOrder

variable {α : Type*} {r : α → α → Prop}

noncomputable def rank (r : α → α → Prop) (x : α) : ℕ := (predecessors r x).ncard

theorem rank_mono (hs : IsStrictTotalOrder α r) (hf : ∀ x, (predecessors r x).Finite)
    {a b : α} (hab : r a b) : rank r a < rank r b := by
  refine ncard_lt_ncard (s := predecessors r a) ⟨fun _ hc ↦ hs.trans _ _ _ hc hab, ?_⟩ (hf b)
  exact fun h ↦ hs.irrefl a (h hab)

theorem rank_inj (hs : IsStrictTotalOrder α r) (hf : ∀ a, (predecessors r a).Finite) :
    Injective (rank r) := by
  intro x y h
  exact hs.trichotomous x y (fun hxy ↦ (rank_mono hs hf hxy).ne h)
    (fun hyx ↦ (rank_mono hs hf hyx).ne' h)

open Classical in
@[instance_reducible]
noncomputable def ofStrictWellOrder
    (hs : IsStrictTotalOrder α r) (hf : ∀ x, (predecessors r x).Finite) :
    Encodable α where
  encode := rank r
  decode := partialInv (rank r)
  encodek := partialInv_left (rank_inj hs hf)

end OfStrictWellOrder

end Encodable
