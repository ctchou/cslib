/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

module

public import Cslib.Computability.Languages.LanguageHom
public import Cslib.Foundations.Semantics.LTS.Basic


/-!
# Label map operation for LTS.
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label₁ Label₂ : Type*}

open Language
open scoped Hom

section MapHom

def mapHom (lts : LTS State Label₁) (f : Hom Label₂ Label₁) : LTS State Label₂ where
  Tr s μ s' := lts.MTr s (f [μ]) s'

variable {s s' : State} {f : Hom Label₂ Label₁}

@[simp]
theorem mapHom_tr {lts : LTS State Label₁} {μ : Label₂} :
    (lts.mapHom f).Tr s μ s' ↔ lts.MTr s (f [μ]) s' := by rfl

scoped grind_pattern mapHom_tr => (lts.mapHom f).Tr s μ s'

@[simp, scoped grind =]
theorem mapHom_mTr {lts : LTS State Label₁} {μs : List Label₂} :
    (lts.mapHom f).MTr s μs s' ↔ lts.MTr s (f μs) s' := by
  induction μs generalizing s with
  | nil => simp
  | cons μ μs ih =>
    rw [Hom.map_cons]
    apply Iff.intro .. <;> intro h
    · obtain ⟨_, _, _⟩ := MTr.cons_iff.mp h
      grind [MTr.append_iff (lts := lts)]
    · obtain ⟨_, _, _⟩ := (MTr.append_iff (lts := lts)).mp h
      grind [MTr.cons_iff (lts := lts.mapHom f)]

end MapHom

section MapLabel

/-- Constructs an LTS by mapping its labels into those of an existing LTS. -/
def mapLabel (lts : LTS State Label₁) (f : Label₂ → Label₁) : LTS State Label₂ :=
  lts.mapHom (Hom.lift ([f ·]))

@[simp]
theorem mapLabel_tr {lts : LTS State Label₁} :
    (lts.mapLabel f).Tr s μ s' ↔ lts.Tr s (f μ) s' := by
  simp [mapLabel, Hom.lift_eq_flatMap]

scoped grind_pattern mapLabel_tr => (lts.mapLabel f).Tr s μ s'

@[simp, scoped grind =]
theorem mapLabel_mTr {lts : LTS State Label₁} {f : Label₂ → Label₁} :
    (lts.mapLabel f).MTr s μs s' ↔ lts.MTr s (μs.map f) s' := by
  simp [mapLabel, Hom.lift_eq_flatMap, List.map_eq_flatMap]

end MapLabel

end Cslib.LTS
