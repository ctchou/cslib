/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.MapHom
public import Mathlib.Data.List.ReduceOption

/-! # Lifting the labels of an LTS to `Option`

`lts.liftOption` reads every label `μ` of `lts` as `some μ` and has a self-loop on every state on
`none`. This is how an `NA` becomes an `εNA` whose ε-transitions are trivial.

## Main definitions

* `LTS.liftOption lts`: the transitions of `lts` on `some μ`, and self-loops on `none`.

## Main statements

* `LTS.isBisimulation_liftOption_mapLabel_some`: reading `lts.liftOption` back through `some`
  gives `lts`, so equality is a bisimulation between the two.
* `LTS.liftOption_mTr_iff`: the runs of `lts.liftOption` are the runs of `lts` with the `none`
  steps dropped.
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label : Type*}

/-- The LTS with the transitions of `lts` on `some μ` for each label `μ`, and a self-loop on every
state on `none`. -/
def liftOption (lts : LTS State Label) : LTS State (Option Label) where
  Tr s μ s' := match μ with
    | some μ => lts.Tr s μ s'
    | none => s = s'

/-- The transitions of `lts.liftOption` on `some μ` are those of `lts` on `μ`. -/
@[simp]
theorem liftOption_tr_some {lts : LTS State Label} {s s' : State} {μ : Label} :
    lts.liftOption.Tr s (some μ) s' ↔ lts.Tr s μ s' := Iff.rfl

/-- The transitions of `lts.liftOption` on `none` are the self-loops. -/
@[simp]
theorem liftOption_tr_none {lts : LTS State Label} {s s' : State} :
    lts.liftOption.Tr s none s' ↔ s = s' := Iff.rfl

/-- Reading the transitions of `lts.liftOption` back through `some` gives those of `lts`, so
equality is a bisimulation between the two. -/
theorem isBisimulation_liftOption_mapLabel_some {lts : LTS State Label} :
    IsBisimulation (lts.liftOption.mapLabel some) lts Eq := by
  rintro s _ rfl μ
  simp

/-- The runs of `lts.liftOption` are the runs of `lts` with the `none` steps dropped. -/
theorem liftOption_mTr_iff {lts : LTS State Label} {s t : State} {μs : List (Option Label)} :
    lts.liftOption.MTr s μs t ↔ lts.MTr s μs.reduceOption t := by
  induction μs generalizing s with
  | nil => simp
  | cons μ μs ih =>
    cases μ with
    | none => simp [MTr.cons_iff, ih]
    | some μ => simp [MTr.cons_iff, ih]

end Cslib.LTS
