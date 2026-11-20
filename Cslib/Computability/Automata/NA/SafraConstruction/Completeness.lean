/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.SafraConstruction.SafraSpec

/-! # Completeness of the Safra construction

-/

@[expose] public section

namespace Cslib.SafraConstruction

open Descriptive Set Automata Filter

variable {State Symbol : Type*}
  {na : NA.Buchi State Symbol} {mda : DA.Rabin (MacroState State) Symbol}
  {as : ωSequence Symbol} {ss : ωSequence State}

def freqHosts (as : ωSequence Symbol) (ss : ωSequence State) : Set (List ℕ) :=
  let mss : ωSequence (MacroState State) := mda.run as
  {x | ∃ᶠ k in atTop, ∃ h : (ss k) ∈ (mss k).states, (mss k).safraHost ⟨ss k, h⟩ = x}

end Cslib.SafraConstruction
