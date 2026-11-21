/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.SafraConstruction.SafraSpec

/-! # Soundness of the Safra construction

-/

@[expose] public section

namespace Cslib.SafraConstruction

open Descriptive Set Automata

variable {State Symbol : Type*}
  {na : NA.Buchi State Symbol} {mda : DA.Rabin (MacroState State) Symbol}
  {ms : MacroState State} {as : List Symbol} {s : State} {x : List ℕ}

theorem backward_start (hs : SafraSpec na mda) (h : s ∈ (mda.mtr mda.start as).states) :
    ∃ s0 ∈ na.start, ∃ ss, na.Execution s0 as s ss := by
  rw [macro_mtr_states hs, hs.start_states, LTS.mem_foldl_setImage] at h
  obtain ⟨s0, hs0, hmtr⟩ := h
  exact ⟨s0, hs0, LTS.Execution.of_mTr hmtr⟩

/-- If `x` is stable throughout the run of `mda` from `ms` on `as`, then every state in the label
of `x` at the end has a predecessor in the label of `x` at the start. -/
theorem backward_stable (hs : SafraSpec na mda) (hwf : ms.WellFormed)
    (hst : ∀ bs, bs <+: as → x ∈ (mda.mtr ms bs).stableTree)
    (h : s ∈ (mda.mtr ms as).states) (hx : x <+: (mda.mtr ms as).host ⟨s, h⟩) :
    ∃ s0, ∃ h0 : s0 ∈ ms.states, x <+: ms.host ⟨s0, h0⟩ ∧
      ∃ ss, na.Execution s0 as s ss := by
  induction as using List.reverseRecOn generalizing s with
  | nil => exact ⟨s, h, hx, _, .refl s⟩
  | append_singleton bs a ih =>
    have hst' : ∀ bs', bs' <+: bs → x ∈ (mda.mtr ms bs').stableTree :=
      fun bs' hbs' => hst bs' (hbs'.trans (List.prefix_append bs [a]))
    have hsafra : x ∈ (mda.mtr ms bs).safraTree :=
      (macro_mtr_wellFormed hs ms bs hwf).stableTree_sub_safraTree
        (hst' bs (List.prefix_refl bs))
    have hst1 : x ∈ (mda.tr (mda.mtr ms bs) a).stableTree := by
      rw [← FLTS.mtr_concat_eq]; exact hst _ (List.prefix_refl _)
    revert h hx
    rw [FLTS.mtr_concat_eq]
    intro h hx
    obtain ⟨s1, h1, htr, hx1, -⟩ := hs.backward (mda.mtr ms bs) a s h x hsafra hst1 hx
    obtain ⟨s0, h0, hx0, ss, hex⟩ := ih hst' h1 hx1
    exact ⟨s0, h0, hx0, _, hex.comp (LTS.Execution.of_tr htr)⟩

/-- One step of the backward analysis: if `x` is stable at the last two macro states of the run of
`mda` from `ms` on `bs ++ [a]`, and `s` is in the label of `x` at the end, with `s` hosted strictly
below `x` or `x` accepting, then `s` has an `a`-predecessor `s1` in the label of `x` after `bs`,
which is hosted strictly below `x` unless `s` is an accepting state of `na`. -/
theorem backward_step (hs : SafraSpec na mda) (hwf : ms.WellFormed)
    {bs : List Symbol} {a : Symbol}
    (hst : ∀ cs, cs <+: bs ++ [a] → x ∈ (mda.mtr ms cs).stableTree)
    (h : s ∈ (mda.mtr ms (bs ++ [a])).states)
    (hx : x <+: (mda.mtr ms (bs ++ [a])).host ⟨s, h⟩)
    (hcond : x ≠ (mda.mtr ms (bs ++ [a])).host ⟨s, h⟩ ∨
      x ∈ (mda.mtr ms (bs ++ [a])).accept) :
    ∃ s1, ∃ h1 : s1 ∈ (mda.mtr ms bs).states, na.Tr s1 a s ∧
      x <+: (mda.mtr ms bs).host ⟨s1, h1⟩ ∧
      (x ≠ (mda.mtr ms bs).host ⟨s1, h1⟩ ∨ s ∈ na.accept) := by
  have hsafra : x ∈ (mda.mtr ms bs).safraTree :=
    (macro_mtr_wellFormed hs ms bs hwf).stableTree_sub_safraTree
      (hst bs (List.prefix_append bs [a]))
  have hst1 : x ∈ (mda.tr (mda.mtr ms bs) a).stableTree := by
    rw [← FLTS.mtr_concat_eq]; exact hst _ (List.prefix_refl _)
  revert h hx hcond
  rw [FLTS.mtr_concat_eq]
  intro h hx hcond
  obtain ⟨s1, h1, htr, hx1, hcase⟩ := hs.backward (mda.mtr ms bs) a s h x hsafra hst1 hx
  exact ⟨s1, h1, htr, hx1, hcase hcond⟩

/-- Appending one transition to an execution preserves visiting an accepting state of `na` after
the first state, and creates such a visit if the new last state is accepting. -/
theorem execution_extend_accept {s0 s1 s : State} {bs : List Symbol} {a : Symbol}
    {ss : List State} (hex : na.Execution s0 bs s1 ss) (htr : na.Tr s1 a s)
    (hacc : ∃ t ∈ na.accept, t ∈ ss.tail ∨ t = s) :
    ∃ ss', na.Execution s0 (bs ++ [a]) s ss' ∧ ∃ t ∈ na.accept, t ∈ ss'.tail := by
  obtain ⟨t, ht, hts⟩ := hacc
  refine ⟨_, hex.comp (LTS.Execution.of_tr htr), t, ht, ?_⟩
  rw [List.tail_append_of_ne_nil hex.ss_ne_nil]
  rcases hts with hts | rfl
  · exact List.mem_append_left _ hts
  · simp

/-- If `x` is accepting (hence a leaf) at `ms` and stable throughout the run of `mda` from `ms` on
`as`, then every state hosted strictly below `x` at the end is reached from the label of `x` at the
start by an execution that visits an accepting state of `na` after its first state. -/
theorem backward_below (hs : SafraSpec na mda) (hwf : ms.WellFormed)
    (hst : ∀ bs, bs <+: as → x ∈ (mda.mtr ms bs).stableTree) (hacc : x ∈ ms.accept)
    (h : s ∈ (mda.mtr ms as).states) (hx : x <+: (mda.mtr ms as).host ⟨s, h⟩)
    (hne : x ≠ (mda.mtr ms as).host ⟨s, h⟩) :
    ∃ s0, ∃ h0 : s0 ∈ ms.states, ms.host ⟨s0, h0⟩ = x ∧
      ∃ ss, na.Execution s0 as s ss ∧ ∃ t ∈ na.accept, t ∈ ss.tail := by
  induction as using List.reverseRecOn generalizing s with
  | nil => exact absurd (ms.leaf_prefix_eq_self h (hwf.accept_leaf hacc) hx).symm hne
  | append_singleton bs a ih =>
    obtain ⟨s1, h1, htr, hx1, hcase⟩ := backward_step hs hwf hst h hx (.inl hne)
    have hst' : ∀ cs, cs <+: bs → x ∈ (mda.mtr ms cs).stableTree :=
      fun cs hcs => hst cs (hcs.trans (List.prefix_append bs [a]))
    rcases hcase with hne1 | hfin
    · obtain ⟨s0, h0, hx0, ss, hex, t, ht, hts⟩ := ih hst' h1 hx1 hne1
      exact ⟨s0, h0, hx0, execution_extend_accept hex htr ⟨t, ht, .inl hts⟩⟩
    · obtain ⟨s0, h0, hx0, ss, hex⟩ := backward_stable hs hwf hst' h1 hx1
      exact ⟨s0, h0, ms.leaf_prefix_eq_self h0 (hwf.accept_leaf hacc) hx0,
        execution_extend_accept hex htr ⟨s, hfin, .inr rfl⟩⟩

/-- If `x` is accepting at `ms` and at the end of a nonempty run of `mda` from `ms` on `as`, and
stable throughout, then every state in the label of `x` at the end is reached from the label of `x`
at the start by an execution that visits an accepting state of `na` after its first state. -/
theorem backward_accept (hs : SafraSpec na mda) (hwf : ms.WellFormed)
    (hst : ∀ bs, bs <+: as → x ∈ (mda.mtr ms bs).stableTree) (hacc : x ∈ ms.accept)
    (h : s ∈ (mda.mtr ms as).states) (hx : x <+: (mda.mtr ms as).host ⟨s, h⟩)
    (hne : as ≠ []) (hacc' : x ∈ (mda.mtr ms as).accept) :
    ∃ s0, ∃ h0 : s0 ∈ ms.states, ms.host ⟨s0, h0⟩ = x ∧
      ∃ ss, na.Execution s0 as s ss ∧ ∃ t ∈ na.accept, t ∈ ss.tail := by
  obtain ⟨bs, a, rfl⟩ : ∃ bs a, as = bs ++ [a] :=
    ⟨as.dropLast, as.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  obtain ⟨s1, h1, htr, hx1, hcase⟩ := backward_step hs hwf hst h hx (.inr hacc')
  have hst' : ∀ cs, cs <+: bs → x ∈ (mda.mtr ms cs).stableTree :=
    fun cs hcs => hst cs (hcs.trans (List.prefix_append bs [a]))
  rcases hcase with hne1 | hfin
  · obtain ⟨s0, h0, hx0, ss, hex, t, ht, hts⟩ := backward_below hs hwf hst' hacc h1 hx1 hne1
    exact ⟨s0, h0, hx0, execution_extend_accept hex htr ⟨t, ht, .inl hts⟩⟩
  · obtain ⟨s0, h0, hx0, ss, hex⟩ := backward_stable hs hwf hst' h1 hx1
    exact ⟨s0, h0, ms.leaf_prefix_eq_self h0 (hwf.accept_leaf hacc) hx0,
      execution_extend_accept hex htr ⟨s, hfin, .inr rfl⟩⟩

end Cslib.SafraConstruction
