/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Group.NatPowAssoc
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Saturation
-/

@[expose] public section

variable {R : Type*} [CommRing R]

@[mk_iff IsPrincipalRoot.iff_def]
structure IsPrincipalRoot (ζ : R) (n : ℕ) : Prop where
  pow_eq_one : ζ ^ n = 1
  sum_pow_eq_zero : ∀ k : ℕ, k ≠ 0 → k < n → ∑ j ∈ Finset.range n, (ζ ^ k) ^ j = 0

@[simps!]
def IsPrincipalRoot.toRootsOfUnity {ζ : R} {n : ℕ} [NeZero n] (h : IsPrincipalRoot ζ n) :
    rootsOfUnity n R :=
  rootsOfUnity.mkOfPowEq ζ h.pow_eq_one

-- #check IsPrincipalRoot.val_inv_toRootsOfUnity_coe
-- #check IsPrincipalRoot.val_toRootsOfUnity_coe

theorem IsPrincipalRoot_of_IsPrimitiveRoot [IsDomain R] {ζ : R} {n : ℕ}
    (h : IsPrimitiveRoot ζ n) : IsPrincipalRoot ζ n where
  pow_eq_one := h.pow_eq_one
  sum_pow_eq_zero := by
    rintro k h0 hk
    have : (ζ ^ k) ^ n - 1 = 0 := by
      rw [← npow_mul, npow_mul', h.pow_eq_one]
      ring
    grind [geom_sum_mul (ζ ^ k) n, IsPrimitiveRoot.pow_ne_one_of_pos_of_lt h h0 hk, mul_eq_zero]

section DFT

open Vector

def dft (ζ : R) (n : ℕ) (v : Vector R n) : Vector R n :=
  (range n).map (fun k ↦ ∑ j : Fin n, v[j] * (ζ ^ k) ^ (j : ℕ))

theorem IsPrincipalRoot.dft_dft {ζ : R} {n : ℕ} (h : IsPrincipalRoot ζ n) (v : Vector R n) :
    dft (ζ ^ (n - 1)) n (dft ζ n v) = n • v := by
  ext k hk
  simp [dft]
  sorry

end DFT
