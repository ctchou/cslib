/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.SafraConstruction.SafraSpec
public import Mathlib.Data.ENat.Lattice

/-! # Completeness of the Safra construction

-/

@[expose] public section

namespace Cslib.SafraConstruction

open Descriptive Set Automata Filter

variable {State Symbol : Type*}
  {na : NA.Buchi State Symbol} {mda : DA.Rabin (MacroState State) Symbol}
  {as : ωSequence Symbol} {ss : ωSequence State}

theorem na_state_in_mda_states (hs : SafraSpec na mda) (hr : na.Run as ss) (n : ℕ) :
    ss n ∈ ((mda.run as) n).states := by
  induction n with
  | zero => simpa [hs.start_states] using hr.start
  | succ n ih =>
    rw [DA.run_succ, hs.states_image]
    exact Set.mem_biUnion ih (hr.trans n)

def freqHosts (hs : SafraSpec na mda) (hr : na.Run as ss) : Set (List ℕ) :=
  {x | ∃ᶠ k in atTop, (mda.run as k).host ⟨ss k, na_state_in_mda_states hs hr k⟩ = x}

noncomputable def shortestHostLen (hs : SafraSpec na mda) (hr : na.Run as ss) : ℕ∞ :=
  ⨅ x ∈ freqHosts hs hr, (x.length : ℕ∞)

end Cslib.SafraConstruction
