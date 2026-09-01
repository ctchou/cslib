/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Languages.Congruences.MyhillCongruence
public import Mathlib.Algebra.FreeMonoid.Basic

/-! # Myhill congruence
-/

@[expose] public section

variable {α : Type}

namespace Language

open FreeMonoid

def Congruence.toCon [c : Congruence α] : Con (FreeMonoid α) where
  r := c.r
  iseqv := c.iseqv
  mul' {w x y z} h_wx h_yz := by
    have h_wyxy : c.eq (w * y) (x * y) := c.right_cov.elim y h_wx
    have h_xyxz : c.eq (x * y) (x * z) := c.left_cov.elim x h_yz
    exact c.iseqv.trans h_wyxy h_xyxz

def SyntacticMonoid (l : Language α) := l.MyhillCongruence.toCon.Quotient

def SyntacticMonoidParam (l : Language α) : l.SyntacticMonoid :=
  sorry

theorem IsRegular.finite_syntacticMonoid {l : Language α}
    (h : l.IsRegular) : Finite (l.SyntacticMonoid) := by
  sorry

end Language
