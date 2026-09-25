/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.DivisionBounds
/-!
# degree bounds for the error factors

This file supplies the degree estimates for the polynomials `f_n` appearing in
the coefficientwise Hensel iteration.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- a natural-degree bound survives reduction of
coefficients. -/
theorem henselFactorization_map_natDegree_le_of_natDegree_le
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    {P : R[X]} {d : ℕ} (hP : P.natDegree ≤ d) :
    (P.map φ).natDegree ≤ d :=
  Polynomial.natDegree_map_le.trans hP

/-- exact degree is recovered from a bounded lift whose
reduction has nonzero leading coefficient in the prescribed degree. -/
theorem henselFactorization_natDegree_eq_of_residue_eq_of_le
    {R : Type*} [CommRing R] [IsLocalRing R]
    {P : R[X]} {gbar : (IsLocalRing.ResidueField R)[X]} {m : ℕ}
    (hP : P.natDegree ≤ m)
    (hmap : P.map (IsLocalRing.residue R) = gbar)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0) :
    P.natDegree = m := by
  refine le_antisymm hP ?_
  have hcoeff_map :=
    congrArg (fun Q : (IsLocalRing.ResidueField R)[X] => Q.coeff m) hmap
  have hcoeff :
      IsLocalRing.residue R (P.coeff m) = gbar.coeff m := by
    simpa [Polynomial.coeff_map] using hcoeff_map
  have hgcoeff : gbar.coeff m ≠ 0 := by
    simpa [Polynomial.leadingCoeff, hgbar_nat] using hglead
  have hPcoeff : P.coeff m ≠ 0 := by
    intro hzero
    apply hgcoeff
    rw [← hcoeff, hzero, map_zero]
  exact Polynomial.le_natDegree_of_ne_zero hPcoeff

/-- the stated degree bound for the second residual factor:
if `fbar = gbar*hbar`, `deg fbar≤d`, and `deg gbar=m` with `gbar≠0`, then
`deg hbar≤d-m`. -/
theorem henselFactorization_residual_right_natDegree_le
    {k : Type*} [Field k] {fbar gbar hbar : k[X]} {m d : ℕ}
    (hfbar : fbar = gbar * hbar)
    (hf : fbar.natDegree ≤ d)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0) :
    hbar.natDegree ≤ d - m := by
  by_cases hh : hbar = 0
  · simp [hh]
  · have hg : gbar ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hglead
    have hprod : (gbar * hbar).natDegree ≤ d := by
      simpa [hfbar] using hf
    have hsum : m + hbar.natDegree ≤ d := by
      simpa [hgbar_nat, Polynomial.natDegree_mul hg hh] using hprod
    exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hsum)

/-- if `deg f ≤ d`, `deg g ≤ m`, and `deg h ≤ d-m`, then
`deg(f-gh)≤d`. -/
theorem henselFactorization_error_natDegree_le
    {R : Type*} [CommRing R] {f g h : R[X]} {d m : ℕ}
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ m)
    (hh : h.natDegree ≤ d - m) (hmd : m ≤ d) :
    (f - g * h).natDegree ≤ d := by
  have hmul : (g * h).natDegree ≤ d := by
    have hmul' : (g * h).natDegree ≤ m + (d - m) :=
      Polynomial.natDegree_mul_le_of_le hg hh
    have hsum : m + (d - m) = d := by
      rw [Nat.add_comm, Nat.sub_add_cancel hmd]
    simpa [hsum] using hmul'
  have hsub := Polynomial.natDegree_sub_le_of_le hf hmul
  simpa using hsub

/-- if `P=C(a)Q` with `a≠0`, then a degree bound on `P`
is a degree bound on `Q`. -/
theorem henselFactorization_factor_natDegree_le_of_constant_mul_eq
    {R : Type*} [CommRing R] [NoZeroDivisors R] {a : R} (ha : a ≠ 0)
    {P Q : R[X]} {d : ℕ}
    (hP : P.natDegree ≤ d) (hfactor : P = Polynomial.C a * Q) :
    Q.natDegree ≤ d := by
  have hCQ : (Polynomial.C a * Q).natDegree ≤ d := by
    simpa [hfactor] using hP
  simpa [Polynomial.natDegree_C_mul (p := Q) (a0 := ha)] using hCQ

/-- degree bound for the next error factor `f_n` from the
current factorization error. -/
theorem henselFactorization_error_factor_natDegree_le
    {R : Type*} [CommRing R] [NoZeroDivisors R] {π : R} {n : ℕ}
    (hπn : π ^ n ≠ 0)
    {f g h fn : R[X]} {d m : ℕ}
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ m)
    (hh : h.natDegree ≤ d - m) (hmd : m ≤ d)
    (hfactor : f - g * h = Polynomial.C (π ^ n) * fn) :
    fn.natDegree ≤ d :=
  henselFactorization_factor_natDegree_le_of_constant_mul_eq
    (a := π ^ n) hπn
    (P := f - g * h) (Q := fn)
    (henselFactorization_error_natDegree_le hf hg hh hmd)
    hfactor

/-- residue-degree bound for the next error factor `f_n`. -/
theorem henselFactorization_error_factor_residue_natDegree_le
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} {n : ℕ} (hπn : π ^ n ≠ 0)
    {f g h fn : R[X]} {d m : ℕ}
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ m)
    (hh : h.natDegree ≤ d - m) (hmd : m ≤ d)
    (hfactor : f - g * h = Polynomial.C (π ^ n) * fn) :
    (fn.map (IsLocalRing.residue R)).natDegree ≤ d :=
  henselFactorization_map_natDegree_le_of_natDegree_le
    (IsLocalRing.residue R)
    (henselFactorization_error_factor_natDegree_le
      (π := π) hπn hf hg hh hmd hfactor)

end Valuations
end AlgebraicNumberTheory

end
