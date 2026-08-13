/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Lex
public import Mathlib.Order.Lattice

/-! # Deep-left order

-/

@[expose] public section

namespace Cslib

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

/-- When `a < b` but `a` is not a prefix of `b`, the two lists differ at a position inside `a`,
which is therefore also a position at which any extension `d` of `a` differs from `b`. -/
theorem lt_and_not_prefix_of_prefix {a b d : List ℕ} :
    a <+: d → a < b → ¬ a <+: b → d < b ∧ ¬ d <+: b := by
  induction a generalizing b d with
  | nil => intro _ _ hnp; exact absurd List.nil_prefix hnp
  | cons x a ih =>
    intro hpd hlt hnp
    obtain ⟨t, rfl⟩ := hpd
    cases b with
    | nil => cases hlt
    | cons y b =>
      cases hlt with
      | rel h =>
        refine ⟨List.Lex.rel h, fun hc => ?_⟩
        obtain ⟨rfl, -⟩ := List.cons_prefix_cons.mp hc
        exact absurd h (lt_irrefl x)
      | cons h =>
        obtain ⟨h1, h2⟩ := ih (List.prefix_append a t) h
          (fun hc => hnp (List.cons_prefix_cons.mpr ⟨rfl, hc⟩))
        exact ⟨List.Lex.cons h1, fun hc => h2 (List.cons_prefix_cons.mp hc).2⟩

theorem deepLeft_trans :
    DeepLeft p1 p2 → DeepLeft p2 p3 → DeepLeft p1 p3 := by
  rintro (hpf1 | htl1) (hpf2 | hlt2)
  · grind [DeepLeft]
  · exact Or.inr (lt_and_not_prefix_of_prefix hpf1 hlt2.1 hlt2.2)
  · sorry
  · sorry

end Cslib
