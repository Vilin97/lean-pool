/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Basic
/-!
# degree bounds for the division remainder

This file supplies the degree estimate for the remainder in the coefficientwise Hensel
correction step.  It removes the later need to assume separately that the
residue of the remainder has small degree.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- the remainder estimate before reducing
coefficients. -/
theorem henselFactorization_remainder_natDegree_le_of_degree_lt
    {R : Type*} [CommRing R] {g0 p : R[X]} {m : ℕ}
    (hg0nat : g0.natDegree = m) (hpdeg : p.degree < g0.degree) :
    p.natDegree ≤ m := by
  apply Polynomial.natDegree_le_of_degree_le
  have hlt : p.degree < (m : WithBot ℕ) := by
    calc
      p.degree < g0.degree := hpdeg
      _ ≤ (g0.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ = (m : WithBot ℕ) := by rw [hg0nat]
  exact hlt.le

/-- the remainder estimate in residue-degree form: if
the division remainder has degree strictly smaller than `g0`, and `g0` has
natural degree `m`, then the residue of the remainder has natural degree at
most `m`. -/
theorem henselFactorization_residue_remainder_natDegree_le_of_degree_lt
    {R : Type*} [CommRing R] [IsLocalRing R]
    {g0 p : R[X]} {m : ℕ}
    (hg0nat : g0.natDegree = m) (hpdeg : p.degree < g0.degree) :
    (p.map (IsLocalRing.residue R)).natDegree ≤ m := by
  exact Polynomial.natDegree_map_le.trans
    (henselFactorization_remainder_natDegree_le_of_degree_lt hg0nat hpdeg)


end Valuations
end AlgebraicNumberTheory

end
