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

open Descriptive Set Automata ωAcceptor

variable {State Symbol : Type*}
  {na : NA.Buchi State Symbol} {mda : DA.Rabin (MacroState State) Symbol}

section BetweenAccepts

variable {ms : MacroState State} {as : List Symbol} {s : State} {x : List ℕ}

abbrev IsStableOver (mda : DA.Rabin (MacroState State) Symbol)
    (ms : MacroState State) (as : List Symbol) (x : List ℕ) : Prop :=
  ∀ bs, bs <+: as → x ∈ (mda.mtr ms bs).stableTree

/-- If `x` is stable throughout the run of `mda` from `ms` on `as`, then every state in the label
of `x` at the end has a predecessor in the label of `x` at the start. -/
theorem backward_stable (hs : SafraSpec na mda) (hwf : ms.WellFormed)
    (hst : IsStableOver mda ms as x)
    (h : s ∈ (mda.mtr ms as).states) (hx : x <+: (mda.mtr ms as).host ⟨s, h⟩) :
    ∃ s0, ∃ h0 : s0 ∈ ms.states, x <+: ms.host ⟨s0, h0⟩ ∧
      ∃ ss, na.Execution s0 as s ss := by
  induction as using List.reverseRecOn generalizing s with
  | nil => exact ⟨s, h, hx, _, .refl s⟩
  | append_singleton bs a ih =>
    have hst' : IsStableOver mda ms bs x :=
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
    {bs : List Symbol} {a : Symbol} (hst : IsStableOver mda ms (bs ++ [a]) x)
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
    (hst : IsStableOver mda ms as x) (hacc : x ∈ ms.accept)
    (h : s ∈ (mda.mtr ms as).states) (hx : x <+: (mda.mtr ms as).host ⟨s, h⟩)
    (hne : x ≠ (mda.mtr ms as).host ⟨s, h⟩) :
    ∃ s0, ∃ h0 : s0 ∈ ms.states, ms.host ⟨s0, h0⟩ = x ∧
      ∃ ss, na.Execution s0 as s ss ∧ ∃ t ∈ na.accept, t ∈ ss.tail := by
  induction as using List.reverseRecOn generalizing s with
  | nil => exact absurd (ms.leaf_prefix_eq_self h (hwf.accept_leaf hacc) hx).symm hne
  | append_singleton bs a ih =>
    obtain ⟨s1, h1, htr, hx1, hcase⟩ := backward_step hs hwf hst h hx (.inl hne)
    have hst' : IsStableOver mda ms bs x :=
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
    (hst : IsStableOver mda ms as x) (hacc : x ∈ ms.accept)
    (h : s ∈ (mda.mtr ms as).states) (hx : x <+: (mda.mtr ms as).host ⟨s, h⟩)
    (hne : as ≠ []) (hacc' : x ∈ (mda.mtr ms as).accept) :
    ∃ s0, ∃ h0 : s0 ∈ ms.states, ms.host ⟨s0, h0⟩ = x ∧
      ∃ ss, na.Execution s0 as s ss ∧ ∃ t ∈ na.accept, t ∈ ss.tail := by
  obtain ⟨bs, a, rfl⟩ : ∃ bs a, as = bs ++ [a] :=
    ⟨as.dropLast, as.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  obtain ⟨s1, h1, htr, hx1, hcase⟩ := backward_step hs hwf hst h hx (.inr hacc')
  have hst' : IsStableOver mda ms bs x :=
    fun cs hcs => hst cs (hcs.trans (List.prefix_append bs [a]))
  rcases hcase with hne1 | hfin
  · obtain ⟨s0, h0, hx0, ss, hex, t, ht, hts⟩ := backward_below hs hwf hst' hacc h1 hx1 hne1
    exact ⟨s0, h0, hx0, execution_extend_accept hex htr ⟨t, ht, .inl hts⟩⟩
  · obtain ⟨s0, h0, hx0, ss, hex⟩ := backward_stable hs hwf hst' h1 hx1
    exact ⟨s0, h0, ms.leaf_prefix_eq_self h0 (hwf.accept_leaf hacc) hx0,
      execution_extend_accept hex htr ⟨s, hfin, .inr rfl⟩⟩

end BetweenAccepts

section InfiniteAccepts

variable {as : ωSequence Symbol}

theorem accept_infinitely
    (hs : SafraSpec na mda) (ha : Accepts mda as) :
    ∃ (x : List ℕ) (f : ℕ → ℕ), StrictMono f ∧
      ∀ k, let ms_k := mda.mtr mda.start (as.extract 0 (f k))
        x ∈ ms_k.accept ∧ IsStableOver mda ms_k (as.extract (f k) (f (k + 1))) x := by
  obtain ⟨p, hp, hfreq, hev⟩ := ha
  rw [hs.pairs] at hp
  obtain ⟨x, rfl⟩ := hp
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨f, hmono, hf⟩ :=
    Filter.extraction_of_frequently_atTop (hfreq.and_eventually (Filter.eventually_ge_atTop N))
  refine ⟨x, f, hmono, fun k => ?_⟩
  intro ms_k
  simp only [ms_k, DA.mtr_extract_eq_run]
  refine ⟨(hf k).1, fun bs hbs => ?_⟩
  have hlen : bs.length ≤ f (k + 1) - f k := by simpa using hbs.length_le
  rw [List.prefix_iff_eq_take.1 hbs, ωSequence.take_extract hlen,
    DA.mtr_run_extract_eq_run (Nat.le_add_right _ _)]
  simpa using hN _ ((hf k).2.trans (Nat.le_add_right _ _))

noncomputable def acceptHost (hs : SafraSpec na mda) (ha : Accepts mda as) : List ℕ :=
  Classical.choose (accept_infinitely hs ha)

noncomputable def acceptPos (hs : SafraSpec na mda) (ha : Accepts mda as) : ℕ → ℕ :=
  Classical.choose (Classical.choose_spec (accept_infinitely hs ha))

noncomputable abbrev acceptMS (hs : SafraSpec na mda) (ha : Accepts mda as)
    (k : ℕ) : MacroState State :=
  mda.mtr mda.start (as.extract 0 (acceptPos hs ha k))

theorem accept_spec (hs : SafraSpec na mda) (ha : Accepts mda as) :
    StrictMono (acceptPos hs ha) ∧
      ∀ k, acceptHost hs ha ∈ (acceptMS hs ha k).accept ∧
        IsStableOver mda (acceptMS hs ha k)
          (as.extract (acceptPos hs ha k) (acceptPos hs ha (k + 1))) (acceptHost hs ha) :=
  Classical.choose_spec (Classical.choose_spec (accept_infinitely hs ha))

theorem acceptMS_host_exists (hs : SafraSpec na mda) (ha : Accepts mda as) (k : ℕ) :
    ∃ s, ∃ h : s ∈ (acceptMS hs ha k).states,
      (acceptMS hs ha k).host ⟨s, h⟩ = acceptHost hs ha := by
  have hl := (macro_mtr_wellFormed hs _ _ hs.start_wf).accept_leaf ((accept_spec hs ha).2 k).1
  obtain ⟨_, ⟨⟨s, h⟩, rfl⟩, hp⟩ := hl.1
  exact ⟨s, h, (acceptMS hs ha k).leaf_prefix_eq_self h hl hp⟩

theorem acceptMS_backward (hs : SafraSpec na mda) (ha : Accepts mda as) (k : ℕ) {s : State}
    (h : s ∈ (acceptMS hs ha (k + 1)).states)
    (hx : (acceptMS hs ha (k + 1)).host ⟨s, h⟩ = acceptHost hs ha) :
    ∃ s0, ∃ h0 : s0 ∈ (acceptMS hs ha k).states,
      (acceptMS hs ha k).host ⟨s0, h0⟩ = acceptHost hs ha ∧
      ∃ ss, na.Execution s0 (as.extract (acceptPos hs ha k) (acceptPos hs ha (k + 1))) s ss ∧
        ∃ t ∈ na.accept, t ∈ ss.tail := by
  obtain ⟨hmono, hspec⟩ := accept_spec hs ha
  have hlt := hmono (Nat.lt_succ_self k)
  have heq : mda.mtr (acceptMS hs ha k) (as.extract (acceptPos hs ha k) (acceptPos hs ha (k + 1)))
      = acceptMS hs ha (k + 1) := by
    simp only [acceptMS, DA.mtr_extract_eq_run]
    exact DA.mtr_run_extract_eq_run hlt.le
  have hacc' := (hspec (k + 1)).1
  revert h hx hacc'
  rw [← heq]
  intro h hx hacc'
  exact backward_accept hs (macro_mtr_wellFormed hs _ _ hs.start_wf) (hspec k).2 (hspec k).1 h
    (hx ▸ List.prefix_refl _) (by simpa using hlt) hacc'

theorem acceptMS_start (hs : SafraSpec na mda) (ha : Accepts mda as) {s : State}
    (h : s ∈ (acceptMS hs ha 0).states) :
    ∃ s0 ∈ na.start, ∃ ss, na.Execution s0 (as.extract 0 (acceptPos hs ha 0)) s ss := by
  rw [macro_mtr_states hs, hs.start_states, LTS.mem_foldl_setImage] at h
  obtain ⟨s0, hs0, hmtr⟩ := h
  exact ⟨s0, hs0, LTS.Execution.of_mTr hmtr⟩

end InfiniteAccepts

end Cslib.SafraConstruction
