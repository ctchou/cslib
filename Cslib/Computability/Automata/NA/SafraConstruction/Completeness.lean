/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.SafraConstruction.SafraSpec
public import Mathlib.Data.Set.Finite.List

/-! # Completeness of the Safra construction

-/

@[expose] public section

namespace Cslib.SafraConstruction

open Descriptive Set Automata Filter

variable {State Symbol : Type*}
  {na : NA.Buchi State Symbol} {mda : DA.Rabin (MacroState State) Symbol}
  {as : ωSequence Symbol} {ss : ωSequence State}

theorem state_mem_macro_states (hs : SafraSpec na mda) (hr : na.Run as ss) (n : ℕ) :
    ss n ∈ ((mda.run as) n).states := by
  induction n with
  | zero => simpa [hs.start_states] using hr.start
  | succ n ih =>
    rw [DA.run_succ, hs.states_image]
    exact Set.mem_biUnion ih (hr.trans n)

theorem macro_run_wellFormed (hs : SafraSpec na mda) (as : ωSequence Symbol) (n : ℕ) :
    (mda.run as n).WellFormed := by
  induction n with
  | zero => exact hs.start_wf
  | succ n ih => rw [DA.run_succ]; exact hs.wf_inv _ _ ih

def freqHosts (hs : SafraSpec na mda) (hr : na.Run as ss) : Set (List ℕ) :=
  {x | ∃ᶠ k in atTop, (mda.run as k).host ⟨ss k, state_mem_macro_states hs hr k⟩ = x}

/-- A set of lists of bounded length with bounded entries is finite. -/
lemma finite_bounded_lists (n : ℕ) :
    {x : List ℕ | x.length ≤ n ∧ ∀ i ∈ x, i < n}.Finite := by
  refine ((List.finite_length_le (Fin n) n).image (List.map Fin.val)).subset ?_
  rintro x ⟨hlen, hlt⟩
  exact ⟨x.pmap Fin.mk hlt, by simpa using hlen, by simp [List.map_pmap]⟩

theorem freqHosts_nonempty [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss) :
    (freqHosts hs hr).Nonempty := by
  set N := Nat.card State
  set f : ℕ → List ℕ := fun k => (mda.run as k).host ⟨ss k, state_mem_macro_states hs hr k⟩
  have hfS : ∀ k, f k ∈ {x : List ℕ | x.length ≤ N ∧ ∀ i ∈ x, i < N} := fun k =>
    have hwf := macro_run_wellFormed hs as k
    have hx := (mda.run as k).host_mem_safraTree ⟨ss k, state_mem_macro_states hs hr k⟩
    ⟨((mda.run as k).length_lt_of_mem_safraTree hwf hx).le,
      fun _ hi => (mda.run as k).lt_of_mem_safraTree hwf hx hi⟩
  by_contra hne
  have hall : ∀ x ∈ {x : List ℕ | x.length ≤ N ∧ ∀ i ∈ x, i < N}, ∀ᶠ k in atTop, f k ≠ x :=
    fun x _ => by
      have : x ∉ freqHosts hs hr := fun hx => hne ⟨x, hx⟩
      simpa [freqHosts, Filter.not_frequently, f] using this
  obtain ⟨k, hk⟩ := ((finite_bounded_lists N).eventually_all.2 hall).exists
  exact hk (f k) (hfS k) rfl

open Classical in
/-- The minimal length of the hosts that occur infinitely often along the run `ss`
(the `l` in the "only if" part of the proof of Proposition 1 of Schewe's paper). -/
noncomputable def shortestHostLen [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss) : ℕ :=
  Nat.find (p := fun n => ∃ x ∈ freqHosts hs hr, x.length = n) <| by
    obtain ⟨x, hx⟩ := freqHosts_nonempty hs hr
    exact ⟨x.length, x, hx, rfl⟩

end Cslib.SafraConstruction
