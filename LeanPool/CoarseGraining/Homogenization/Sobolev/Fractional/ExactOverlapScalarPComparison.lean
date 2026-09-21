/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Positive.ExactOverlapScalarP
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.BesovLeGagliardo
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.GagliardoLeBesov

/-!
# Exact scalar overlap comparison at arbitrary finite exponent

This module transports the established finite-depth scalar overlap estimates
to the exact diagonal overlap seminorm through its exact `p`-power identity.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

/-- Exact scalar overlap Besov-to-Gagliardo comparison at an arbitrary finite
exponent, with the constant from the finite-depth estimate. -/
theorem exactOverlapScalarPSeminorm_rpow_le_gagliardo {d : ℕ} [NeZero d]
    (s : FractionalOrder) (p : FiniteLpExponent) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) (humeas : Measurable u)
    (hmem : MemLp u p.exponent (normalizedCubeMeasure Q)) :
    (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q u hu) ^
        p.exponent.toReal ≤
      2 * 3 ^ d *
        Gagliardo.cubeGagliardoESeminorm Q s.1 p.exponent u ^
          p.exponent.toReal := by
  rw [exactOverlapScalarPSeminorm_rpow_eq_iSup_partial s p Q u hu hmem]
  refine iSup_le fun N => ?_
  have hpr : 0 ≤ p.exponent.toReal := ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_rpow_of_nonneg
    (cubeBesovOverlapPartialSeminorm_nonneg Q s.1 p.exponent p.exponent N u)
    hpr]
  exact Gagliardo.ofReal_partialSeminorm_rpow_le_gagliardo Q s.2.1.le p.one_lt.le
    p.lt_top.ne humeas hmem N

/-- Gagliardo-to-exact-scalar-overlap comparison at an arbitrary finite
exponent, with the constant from the established shell estimate. -/
theorem gagliardo_rpow_le_exactOverlapScalarPSeminorm {d : ℕ} [NeZero d]
    (s : FractionalOrder) (p : FiniteLpExponent) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) (humeas : Measurable u)
    (hmem : MemLp u p.exponent (normalizedCubeMeasure Q)) :
    Gagliardo.cubeGagliardoESeminorm Q s.1 p.exponent u ^
        p.exponent.toReal ≤
      (Gagliardo.gagliardoBesovLowerConstant d) ^ p.exponent.toReal *
        (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q u hu) ^
          p.exponent.toReal := by
  have hiSup :
      (⨆ N : ℕ, ENNReal.ofReal
        (cubeBesovOverlapPartialSeminorm Q s.1 p.exponent p.exponent N u ^
          p.exponent.toReal)) =
      ⨆ N : ℕ, (ENNReal.ofReal
        (cubeBesovOverlapPartialSeminorm Q s.1 p.exponent p.exponent N u)) ^
          p.exponent.toReal := by
    apply iSup_congr
    intro N
    have hpr : 0 ≤ p.exponent.toReal := ENNReal.toReal_nonneg
    exact (ENNReal.ofReal_rpow_of_nonneg
      (cubeBesovOverlapPartialSeminorm_nonneg Q s.1 p.exponent p.exponent N u)
      hpr).symm
  calc
    Gagliardo.cubeGagliardoESeminorm Q s.1 p.exponent u ^ p.exponent.toReal ≤
        (Gagliardo.gagliardoBesovLowerConstant d) ^ p.exponent.toReal *
          ⨆ N : ℕ, ENNReal.ofReal
            (cubeBesovOverlapPartialSeminorm Q s.1 p.exponent p.exponent N u ^
              p.exponent.toReal) :=
      Gagliardo.gagliardo_rpow_le_iSup_partialSeminorm Q s.2.1.le s.2.2.le
        p.one_lt.le p.lt_top.ne humeas hmem
    _ = (Gagliardo.gagliardoBesovLowerConstant d) ^ p.exponent.toReal *
          ⨆ N : ℕ, (ENNReal.ofReal
            (cubeBesovOverlapPartialSeminorm Q s.1 p.exponent p.exponent N u)) ^
              p.exponent.toReal := by
      rw [hiSup]
    _ = (Gagliardo.gagliardoBesovLowerConstant d) ^ p.exponent.toReal *
        (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q u hu) ^
          p.exponent.toReal := by
      rw [← exactOverlapScalarPSeminorm_rpow_eq_iSup_partial s p Q u hu hmem]

end Homogenization
