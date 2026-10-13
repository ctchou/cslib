/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Relation.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-! # Encodable
-/

@[expose] public section

open Relation Set

namespace Encodable

variable {α : Type*} [Encodable α]

abbrev linearOrder : LinearOrder α :=
  LinearOrder.lift' encode encode_injective

section

attribute [local instance] linearOrder

noncomputable abbrev locallyFiniteOrder : LocallyFiniteOrder α :=
  .ofFiniteIcc fun a b =>
    (Set.finite_Icc (encode a) (encode b)).preimage encode_injective.injOn

attribute [local instance] locallyFiniteOrder

noncomputable abbrev predOrder : PredOrder α :=
  LinearLocallyFiniteOrder.predOrder α

noncomputable abbrev succOrder : SuccOrder α :=
  LinearLocallyFiniteOrder.succOrder α

end

abbrev lt : α → α → Prop := linearOrder.lt

noncomputable abbrev pred : α → α := predOrder.pred

noncomputable abbrev succ : α → α := succOrder.succ

theorem lt_isStrictTotalOrder : IsStrictTotalOrder α lt :=
  @instIsStrictTotalOrderLt α linearOrder

theorem lt_finite_predecessors (x : α) : (predecessors lt x).Finite :=
  (finite_lt_nat (encode x)).preimage encode_injective.injOn

end Encodable
