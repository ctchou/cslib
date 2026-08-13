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
lemma lt_and_not_prefix_of_prefix {a b d : List ℕ} :
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

/-- When `a < b` but `a` is not a prefix of `b`, any prefix `c` of `b` is either a prefix of `a`
(if it ends before the position where `a` and `b` differ) or else `a` differs from `c` at that
position. -/
lemma prefix_or_lt_and_not_prefix_of_prefix {a b c : List ℕ} :
    c <+: b → a < b → ¬ a <+: b → c <+: a ∨ (a < c ∧ ¬ a <+: c) := by
  induction a generalizing b c with
  | nil => intro _ _ hnp; exact absurd List.nil_prefix hnp
  | cons x a ih =>
    intro hpc hlt hnp
    cases b with
    | nil => cases hlt
    | cons y b =>
      cases c with
      | nil => exact Or.inl List.nil_prefix
      | cons z c =>
        obtain ⟨rfl, hpc'⟩ := List.cons_prefix_cons.mp hpc
        cases hlt with
        | rel h =>
          refine Or.inr ⟨List.Lex.rel h, fun hc => ?_⟩
          obtain ⟨rfl, -⟩ := List.cons_prefix_cons.mp hc
          exact absurd h (lt_irrefl x)
        | cons h =>
          rcases ih hpc' h (fun hc => hnp (List.cons_prefix_cons.mpr ⟨rfl, hc⟩)) with
            h1 | ⟨h1, h2⟩
          · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h1⟩)
          · exact Or.inr ⟨List.Lex.cons h1, fun hc => h2 (List.cons_prefix_cons.mp hc).2⟩

/-- Strict lexicographic order without the prefix relation is transitive. -/
lemma lt_and_not_prefix_trans {a b c : List ℕ} :
    a < b → ¬ a <+: b → b < c → ¬ b <+: c → a < c ∧ ¬ a <+: c := by
  induction a generalizing b c with
  | nil => intro _ hnp; exact absurd List.nil_prefix hnp
  | cons x a ih =>
    intro hab hnab hbc hnbc
    cases b with
    | nil => cases hab
    | cons y b =>
      cases c with
      | nil => cases hbc
      | cons z c =>
        have key : x < z → x :: a < z :: c ∧ ¬ x :: a <+: z :: c := fun h =>
          ⟨List.Lex.rel h, fun hc => by
            obtain ⟨rfl, -⟩ := List.cons_prefix_cons.mp hc
            exact absurd h (lt_irrefl x)⟩
        cases hab with
        | rel h1 =>
          cases hbc with
          | rel h2 => exact key (lt_trans h1 h2)
          | cons _ => exact key h1
        | cons h1 =>
          cases hbc with
          | rel h2 => exact key h2
          | cons h2 =>
            obtain ⟨h3, h4⟩ := ih h1 (fun hc => hnab (List.cons_prefix_cons.mpr ⟨rfl, hc⟩)) h2
              (fun hc => hnbc (List.cons_prefix_cons.mpr ⟨rfl, hc⟩))
            exact ⟨List.Lex.cons h3, fun hc => h4 (List.cons_prefix_cons.mp hc).2⟩

theorem deepLeft_trans :
    DeepLeft p1 p2 → DeepLeft p2 p3 → DeepLeft p1 p3 := by
  rintro (hpf1 | hlt1) (hpf2 | hlt2)
  · grind [DeepLeft]
  · exact Or.inr (lt_and_not_prefix_of_prefix hpf1 hlt2.1 hlt2.2)
  · exact prefix_or_lt_and_not_prefix_of_prefix hpf2 hlt1.1 hlt1.2
  · exact Or.inr (lt_and_not_prefix_trans hlt1.1 hlt1.2 hlt2.1 hlt2.2)

instance : IsLinearOrder (List ℕ) DeepLeft where
  refl := deepLeft_refl
  trans _ _ _ := deepLeft_trans
  antisymm _ _ := deepLeft_antisymm
  total := deepLeft_total

/-- Every finite nonempty set of lists has a least element with respect to `DeepLeft`. -/
theorem deepLeft_finset_min (s : Finset (List ℕ)) (hne : s.Nonempty) :
    ∃ m ∈ s, ∀ y ∈ s, DeepLeft m y := by
  induction s using Finset.induction_on with
  | empty => simp at hne
  | insert x s _ ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨x, by simp, by simp [deepLeft_refl]⟩
    · obtain ⟨m, hm, hmin⟩ := ih hs
      rcases deepLeft_total x m with h | h
      · refine ⟨x, by simp, ?_⟩
        simpa using ⟨deepLeft_refl x, fun y hy => deepLeft_trans h (hmin y hy)⟩
      · exact ⟨m, by simp [hm], by simpa using ⟨h, hmin⟩⟩

end Cslib
