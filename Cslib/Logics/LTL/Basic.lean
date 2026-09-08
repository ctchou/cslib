/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Init
public import Cslib.Logics.Modal.Semantics

/-! # Linear-time temporal logic

This is a draft.
-/

@[expose] public section

namespace Cslib.Logic.Modal.LTL

open PFunctor

inductive Operator where
  | next
  | eventually
  | until

def Signature : PFunctor where
  A := Operator
  B (op : Operator) := match op with
    | Operator.next => Fin 1
    | Operator.eventually => Fin 1
    | Operator.until => Fin 2

inductive Atom (S L : Type*) where
  | state : S → Atom S L
  | label : L → Atom S L

abbrev Proposition (S L : Type*) := Modal.Proposition Signature (Atom S L)

end Cslib.Logic.Modal.LTL

namespace Cslib.OmegaSequence

open PFunctor Logic.Modal.LTL

variable {State Label : Type*}

end Cslib.OmegaSequence
