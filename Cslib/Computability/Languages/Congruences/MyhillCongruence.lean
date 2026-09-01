/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Languages.MyhillNerode

/-! # Myhill congruence
-/

@[expose] public section

variable {α : Type}

namespace Language

open Cslib FLTS Automata DA

@[implicit_reducible]
def MyhillCongruence (l : Language α) : Congruence α where
  r x y := ∀ w z, w ++ x ++ z ∈ l ↔ w ++ y ++ z ∈ l
  iseqv.refl := by grind
  iseqv.symm := by grind
  iseqv.trans := by grind
  right_cov.elim := by grind [Covariant]
  left_cov.elim := by grind [Covariant]

def NerodeMap (l : Language α) (x : List α) : l.NerodeQuotient → l.NerodeQuotient :=
  fun q ↦ l.NerodeCongruenceDA.mtr q x

theorem nerodeMap_append (l : Language α) (x y : List α) :
    l.NerodeMap (x ++ y) = l.NerodeMap y ∘ l.NerodeMap x := by
  ext q
  simp [NerodeMap, FLTS.mtr_append_eq]

theorem nerodeMap_accept (l : Language α) (x : List α) :
    x ∈ l ↔ l.NerodeMap x l.NerodeCongruenceDA.start ∈ l.NerodeCongruenceDA.accept := by
  nth_rewrite 1 [← nerodeCongruenceDA_language_eq l]
  constructor <;> intro <;> assumption

theorem myhillCongruence_iff (l : Language α) (x y : List α) :
    l.MyhillCongruence.r x y ↔ l.NerodeMap x = l.NerodeMap y := by
  constructor <;> intro h
  · ext q
    obtain ⟨w, rfl⟩ := Quotient.mk_surjective q
    simp only [NerodeMap, NerodeCongruenceDA, congr_mtr_append, Quotient.eq_iff_equiv]
    exact h w
  · intro w z
    simp [nerodeMap_accept, nerodeMap_append, h]

end Language
