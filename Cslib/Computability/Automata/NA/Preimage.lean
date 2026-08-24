/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Semantics.LTS.MapHom

/-!
# Preimage construction on nondeterministic automata

-/


@[expose] public section

namespace Cslib.Automata.NA.FinAcc

open Acceptor Language _root_.Language

variable {State Symbol Symbol' : Type*} (f : Hom Symbol' Symbol)

def preimage (na : FinAcc State Symbol) : FinAcc State Symbol' where
  toLTS := na.toLTS.mapHom f
  start := na.start
  accept := na.accept

/-- The start states of `na.preimage` are the accept states of `na`. -/
@[simp, grind =]
theorem preimage_start (na : FinAcc State Symbol) : (na.preimage f).start = na.start := rfl

/-- The accept states of `na.preimage` are the start states of `na`. -/
@[simp, grind =]
theorem preimage_accept (na : FinAcc State Symbol) : (na.preimage f).accept = na.accept := rfl

/-- The multistep transitions of `na.preimage` are exactly the preimaged multistep transitions
of `na`. -/
@[simp, grind =]
theorem preimage_mTr (na : FinAcc State Symbol) {xs' : List Symbol'} {s t : State} :
    (na.preimage f).MTr s xs' t ↔ na.MTr s (f xs') t :=
  LTS.mapHom_mTr

/-- `na.preimage` accepts a word iff `na` accepts its reversal. -/
@[simp]
theorem accepts_preimage {na : FinAcc State Symbol} {xs' : List Symbol'} :
    Accepts (na.preimage f) xs' ↔ Accepts na (f xs') := by
  simp [Accepts]

/-- `na.preimage` accepts exactly the reversals of the words accepted by `na`. -/
@[simp]
theorem preimage_language_eq (na : FinAcc State Symbol) :
    language (na.preimage f) = (language na).preimage f := by
  ext
  simp

end Cslib.Automata.NA.FinAcc
