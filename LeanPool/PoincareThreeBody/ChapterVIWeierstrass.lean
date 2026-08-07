/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

/-!
# The Weierstrass normal form in Poincaré's Chapter VI, §99

Poincaré applies Weierstrass preparation to the inverse square of the local integrand.  At the
pinch point its specialization in the parameter has a zero of order two in the integration
variable.  He concludes that

`ψ = ((t - h)² + k) ψ₁`,

where `ψ₁` is a unit and the parameter series `h` and `k` vanish at the singular parameter.
This file verifies that formal-power-series step.  It does not identify the analytic germs of
the three-body integrand with these formal series or prove convergence of the prepared factors.
-/

noncomputable section

open scoped Polynomial

namespace LeanPool.PoincareThreeBody

/-- The parameter series in the local coordinate `z - z₀`. -/
abbrev ChapterVIParameterSeries := PowerSeries ℂ

/-- A series in the local integration coordinate `t - t₀`, whose coefficients are parameter
series in `z - z₀`. -/
abbrev ChapterVIBivariateSeries := PowerSeries ChapterVIParameterSeries

/-- Completing the square for a monic quadratic over the parameter-series ring.  Division by
two is performed in the coefficient field and then embedded as a constant parameter series. -/
theorem chapterVI_monicQuadratic_completeSquare
    (polynomial : ChapterVIParameterSeries[X])
    (hmonic : polynomial.Monic)
    (hdegree : polynomial.natDegree = 2) :
    let center := PowerSeries.C (-(1 / 2 : ℂ)) * polynomial.coeff 1
    let kappa := polynomial.coeff 0 - center ^ 2
    polynomial =
      (Polynomial.X - Polynomial.C center) ^ 2 + Polynomial.C kappa := by
  let center := PowerSeries.C (-(1 / 2 : ℂ)) * polynomial.coeff 1
  let kappa := polynomial.coeff 0 - center ^ 2
  change polynomial =
    (Polynomial.X - Polynomial.C center) ^ 2 + Polynomial.C kappa
  have hexpand : polynomial =
      Polynomial.X ^ 2 + Polynomial.C (polynomial.coeff 1) * Polynomial.X +
        Polynomial.C (polynomial.coeff 0) := by
    apply Polynomial.ext
    intro index
    by_cases hzero : index = 0
    · subst index
      simp
    by_cases hone : index = 1
    · subst index
      simp
    by_cases htwo : index = 2
    · subst index
      have hleading : polynomial.coeff 2 = 1 := by
        rw [← hdegree]
        exact hmonic.coeff_natDegree
      simp [hleading]
    have hlarge : 2 < index := by omega
    have hcoefficient : polynomial.coeff index = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      simpa [hdegree] using hlarge
    simp [hcoefficient, hzero, htwo, Ne.symm hone,
      Polynomial.coeff_X, Polynomial.coeff_C]
  have hcenter :
      (2 : ChapterVIParameterSeries) * center = -polynomial.coeff 1 := by
    have hscalar :
        (2 : ChapterVIParameterSeries) * PowerSeries.C (-(1 / 2 : ℂ)) = -1 := by
      have htwo : (2 : ChapterVIParameterSeries) = PowerSeries.C (2 : ℂ) := by
        simpa using
          (map_natCast (PowerSeries.C : ℂ →+* ChapterVIParameterSeries) 2).symm
      rw [htwo, ← map_mul]
      norm_num
    dsimp only [center]
    rw [← mul_assoc, hscalar]
    simp
  have hlinear : polynomial.coeff 1 =
      -2 * center := by
    calc
      polynomial.coeff 1 = -(-polynomial.coeff 1) := by simp
      _ = -(2 * center) := by
        rw [hcenter]
      _ = -2 * center := by ring
  calc
    polynomial =
        Polynomial.X ^ 2 + Polynomial.C (polynomial.coeff 1) * Polynomial.X +
          Polynomial.C (polynomial.coeff 0) := hexpand
    _ = (Polynomial.X - Polynomial.C center) ^ 2 +
        Polynomial.C (polynomial.coeff 0 - center ^ 2) := by
      rw [hlinear]
      simp only [map_neg, map_mul, map_sub]
      have hCtwo : Polynomial.C (2 : ChapterVIParameterSeries) =
          (2 : ChapterVIParameterSeries[X]) := by
        simpa using
          map_natCast (Polynomial.C : ChapterVIParameterSeries →+*
            ChapterVIParameterSeries[X]) 2
      rw [hCtwo, map_pow (Polynomial.C : ChapterVIParameterSeries →+*
        ChapterVIParameterSeries[X]) center 2]
      ring
    _ = (Polynomial.X - Polynomial.C center) ^ 2 + Polynomial.C kappa := by
      rfl

/-- The exact formal-series factorization used in §99.  Specializing the parameter to zero is
the residue map of `ℂ⟦z - z₀⟧`; order two of that specialization produces a monic quadratic in
`t - t₀`.  Completing the square gives Poincaré's `((t - h)² + k) ψ₁`, and distinguishedness
shows that `h` and `k` vanish at the singular parameter. -/
theorem exists_chapterVI_weierstrassNormalForm
    (ψ : ChapterVIBivariateSeries)
    (hψ : ψ.map (IsLocalRing.residue ChapterVIParameterSeries) ≠ 0)
    (horder :
      (ψ.map (IsLocalRing.residue ChapterVIParameterSeries)).order.toNat = 2) :
    ∃ center kappa : ChapterVIParameterSeries,
      ∃ unit : ChapterVIBivariateSeries,
      IsUnit unit ∧
      ψ =
        (↑((Polynomial.X - Polynomial.C center) ^ 2 + Polynomial.C kappa :
          ChapterVIParameterSeries[X]) : ChapterVIBivariateSeries) * unit ∧
      center ∈ IsLocalRing.maximalIdeal ChapterVIParameterSeries ∧
      kappa ∈ IsLocalRing.maximalIdeal ChapterVIParameterSeries := by
  let : IsAdicComplete
      (IsLocalRing.maximalIdeal ChapterVIParameterSeries) ChapterVIParameterSeries := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  rcases ψ.exists_isWeierstrassFactorization hψ with ⟨polynomial, unit, hfactorization⟩
  have hdegree : polynomial.natDegree = 2 := by
    rw [hfactorization.natDegree_eq_toNat_order_map, horder]
  let center := PowerSeries.C (-(1 / 2 : ℂ)) * polynomial.coeff 1
  let kappa := polynomial.coeff 0 - center ^ 2
  have hnormal : polynomial =
      (Polynomial.X - Polynomial.C center) ^ 2 + Polynomial.C kappa := by
    exact chapterVI_monicQuadratic_completeSquare polynomial
      hfactorization.isDistinguishedAt.monic hdegree
  have hcoeffOne : polynomial.coeff 1 ∈
      IsLocalRing.maximalIdeal ChapterVIParameterSeries := by
    exact hfactorization.isDistinguishedAt.mem (by omega)
  have hcenter : center ∈ IsLocalRing.maximalIdeal ChapterVIParameterSeries := by
    exact (IsLocalRing.maximalIdeal ChapterVIParameterSeries).mul_mem_left _ hcoeffOne
  have hkappa : kappa ∈ IsLocalRing.maximalIdeal ChapterVIParameterSeries := by
    exact (IsLocalRing.maximalIdeal ChapterVIParameterSeries).sub_mem
      (hfactorization.isDistinguishedAt.mem (by omega))
      ((IsLocalRing.maximalIdeal ChapterVIParameterSeries).pow_mem_of_mem hcenter 2 (by norm_num))
  refine ⟨center, kappa, unit, hfactorization.isUnit, ?_, hcenter, hkappa⟩
  rw [← hnormal]
  exact hfactorization.eq_mul

end LeanPool.PoincareThreeBody
