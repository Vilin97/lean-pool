/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionBoundaryMeasureAffine
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanCompact
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanOuterApproximation

/-!
# Controlled inflation of smooth Jordan domains

A bounded smooth convex Jordan domain can be enlarged by an arbitrarily small
homothety about an interior point.  Convexity puts the old closed carrier
strictly inside the enlarged open carrier, while boundedness controls the
Hausdorff displacement.  Thus closed smooth Jordan carriers themselves have
the local outer-approximation property used by the terminal exhaustion.
-/

open Complex Metric Set

/-- The closed carrier of a smooth Jordan domain admits arbitrarily tight
smooth Jordan outer approximations. -/
theorem SmoothJordanDomain.hasSmoothJordanOuterApproximation_closure
    (Omega : SmoothJordanDomain) :
    HasSmoothJordanOuterApproximation (closure Omega.carrier) := by
  intro ε hε
  obtain ⟨c, hc⟩ := Omega.carrier_nonempty
  obtain ⟨R, hR, hclosedBall⟩ :=
    Omega.exists_pos_radius_closure_subset_ball c
  let s : ℝ := ε / (2 * R)
  have hs : 0 < s := by
    dsimp only [s]
    exact div_pos hε (mul_pos (by norm_num) hR)
  let t : ℝ := 1 + s
  have ht : 1 < t := by
    dsimp only [t]
    linarith
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have htC : (t : ℂ) ≠ 0 := by
    exact_mod_cast ht0
  let b : ℂ := (1 - (t : ℂ)) * c
  let Psi := Omega.complexAffine (t : ℂ) b htC
  have hhomothety (z : ℂ) :
      (t : ℂ) * z + b = AffineMap.homothety c t z := by
    dsimp only [b]
    rw [AffineMap.homothety_apply]
    change (t : ℂ) * z + (1 - (t : ℂ)) * c =
      (t : ℂ) * (z - c) + c
    ring
  have hcInterior : c ∈ interior Omega.carrier := by
    rw [Omega.isOpen_carrier.interior_eq]
    exact hc
  have hinside : closure Omega.carrier ⊆ Psi.carrier := by
    have hconvex := Omega.strictConvex_carrier.convex
    have hhom :=
      hconvex.closure_subset_image_homothety_interior_of_one_lt
        hcInterior t ht
    change closure Omega.carrier ⊆
      (fun z => (t : ℂ) * z + b) '' Omega.carrier
    rw [show (fun z : ℂ => (t : ℂ) * z + b) =
        AffineMap.homothety c t by
      funext z
      exact hhomothety z]
    simpa only [Omega.isOpen_carrier.interior_eq] using hhom
  refine ⟨Psi, hinside, ?_⟩
  have hclosure : closure Psi.carrier =
      (fun z => (t : ℂ) * z + b) '' closure Omega.carrier := by
    let e : ℂ ≃ₜ ℂ :=
      (Homeomorph.mulLeft₀ (t : ℂ) htC).trans (Homeomorph.addRight b)
    change closure (e '' Omega.carrier) = e '' closure Omega.carrier
    exact (e.image_closure Omega.carrier).symm
  rw [hclosure]
  rintro y ⟨z, hz, rfl⟩
  apply Metric.mem_thickening_iff.mpr
  refine ⟨z, hz, ?_⟩
  change dist ((t : ℂ) * z + b) z < ε
  rw [hhomothety, dist_homothety_self]
  have hnorm : ‖1 - t‖ = s := by
    have hsub : 1 - t = -s := by
      dsimp only [t]
      ring
    rw [hsub, Real.norm_eq_abs, abs_neg, abs_of_pos hs]
  rw [hnorm]
  have hzR : dist c z < R := by
    rw [dist_comm]
    exact hclosedBall hz
  have hsR : s * R = ε / 2 := by
    dsimp only [s]
    field_simp [hR.ne']
  calc
    s * dist c z < s * R := mul_lt_mul_of_pos_left hzR hs
    _ = ε / 2 := hsR
    _ < ε := half_lt_self hε

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- If the closed numerical range is already the closed carrier of a smooth
convex Jordan domain, controlled inflation gives the exact
Crouzeix--Palencia spectral-set bound. -/
theorem crouzeix_palencia_of_closure_numericalRange_eq_smoothJordanClosure
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hW : closure (numericalRange A) = closure Omega.carrier) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply crouzeix_palencia_of_smoothJordanOuterApproximation A
  rw [hW]
  exact Omega.hasSmoothJordanOuterApproximation_closure

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
