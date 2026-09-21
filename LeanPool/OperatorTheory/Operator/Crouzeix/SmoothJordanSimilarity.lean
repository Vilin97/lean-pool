/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanAffine
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanPolytopeReduction

/-!
# Similarity transport and normalization of the planar geometry problem

Smooth Jordan outer approximation is invariant under translations and
nonzero complex similarities.  The metric approximation scale changes by the
similarity ratio, while the smooth Jordan structure itself is transported by
the real-linear and translation constructors.

As a consequence, the remaining full-dimensional polytope problem can be
normalized: it is enough to treat finite convex hulls containing a closed unit
disk.  An interior point supplies a small disk, and a homothety expands it to
unit radius.
-/

open Complex Metric Set
open scoped InnerProductSpace

/-- Multiplication by a nonzero complex number, regarded as an invertible
real-linear map of the complex plane. -/
noncomputable def complexMulRealEquiv (a : ℂ) (ha : a ≠ 0) :
    ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ) (Units.mk0 a ha)

@[simp] theorem complexMulRealEquiv_apply (a : ℂ) (ha : a ≠ 0)
    (z : ℂ) :
    complexMulRealEquiv a ha z = a * z := rfl

/-- The closure of a smooth Jordan carrier transported by a complex
similarity is the similarity image of the original closure. -/
theorem closure_translate_linearImage_complexMulRealEquiv
    (Omega : SmoothJordanDomain) (c a : ℂ) (ha : a ≠ 0) :
    closure
        (((Omega.linearImage (complexMulRealEquiv a ha)).translate c).carrier) =
      (fun z => c + a * z) '' closure Omega.carrier := by
  change closure ((fun z => c + z) ''
      (complexMulRealEquiv a ha '' Omega.carrier)) =
    (fun z => c + a * z) '' closure Omega.carrier
  have hadd :=
    ((Homeomorph.addLeft c).image_closure
      (complexMulRealEquiv a ha '' Omega.carrier)).symm
  change closure ((fun z => c + z) ''
      (complexMulRealEquiv a ha '' Omega.carrier)) =
    (fun z => c + z) '' closure
      (complexMulRealEquiv a ha '' Omega.carrier) at hadd
  rw [hadd]
  have hlinear :=
    ((complexMulRealEquiv a ha).toHomeomorph.image_closure
      Omega.carrier).symm
  change closure (complexMulRealEquiv a ha '' Omega.carrier) =
    complexMulRealEquiv a ha '' closure Omega.carrier at hlinear
  rw [hlinear]
  ext z
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨a * w, ⟨w, hw, rfl⟩, rfl⟩

/-- Smooth Jordan outer approximation is preserved by every nonzero complex
similarity `z ↦ c + a * z`. -/
theorem HasSmoothJordanOuterApproximation.similarity
    {K : Set ℂ} (hK : HasSmoothJordanOuterApproximation K)
    (c a : ℂ) (ha : a ≠ 0) :
    HasSmoothJordanOuterApproximation ((fun z => c + a * z) '' K) := by
  intro ε hε
  let δ : ℝ := ε / ‖a‖
  have haNorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hδ : 0 < δ := by
    exact div_pos hε haNorm
  obtain ⟨Omega, hKOmega, hOmegaK⟩ := hK δ hδ
  let Psi : SmoothJordanDomain :=
    (Omega.linearImage (complexMulRealEquiv a ha)).translate c
  refine ⟨Psi, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨a * z, ⟨z, hKOmega hz, rfl⟩, rfl⟩
  · rw [show closure Psi.carrier =
        (fun z => c + a * z) '' closure Omega.carrier by
      exact closure_translate_linearImage_complexMulRealEquiv Omega c a ha]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hwK, hzw⟩ :=
      Metric.mem_thickening_iff.mp (hOmegaK hz)
    refine Metric.mem_thickening_iff.mpr
      ⟨c + a * w, ⟨w, hwK, rfl⟩, ?_⟩
    have hscale : ‖a‖ * δ = ε := by
      dsimp only [δ]
      exact mul_div_cancel₀ ε haNorm.ne'
    rw [dist_add_left]
    change dist (a • z) (a • w) < ε
    rw [dist_smul₀]
    calc
      ‖a‖ * dist z w < ‖a‖ * δ := mul_lt_mul_of_pos_left hzw haNorm
      _ = ε := hscale

/-- A real homothety written as a translation followed by scalar
multiplication. -/
theorem homothety_apply_eq_const_add_mul (c z : ℂ) (r : ℝ) :
    AffineMap.homothety c r z = (1 - r) • c + (r : ℂ) * z := by
  rw [AffineMap.homothety_apply]
  change (r : ℂ) * (z - c) + c =
    ((1 - r : ℝ) : ℂ) * c + (r : ℂ) * z
  push_cast
  ring

/-- Smooth Jordan outer approximation is preserved by a nontrivial real
homothety about any center. -/
theorem HasSmoothJordanOuterApproximation.homothety
    {K : Set ℂ} (hK : HasSmoothJordanOuterApproximation K)
    (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    HasSmoothJordanOuterApproximation (AffineMap.homothety c r '' K) := by
  let d : ℂ := (1 - r) • c
  have hrComplex : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hsim := hK.similarity d (r : ℂ) hrComplex
  convert hsim using 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, hw, ?_⟩
    rw [homothety_apply_eq_const_add_mul]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, hw, ?_⟩
    rw [homothety_apply_eq_const_add_mul]

/-- The normalized residual geometry problem: smooth outer approximation for
every finite convex hull that contains a closed unit disk. -/
def HasSmoothJordanOuterApproximationForUnitBallPolytopes : Prop :=
  ∀ (u : Finset ℂ) (c : ℂ),
    Metric.closedBall c 1 ⊆ convexHull ℝ (u : Set ℂ) →
      HasSmoothJordanOuterApproximation (convexHull ℝ (u : Set ℂ))

/-- The unit-disk-normalized polytope case implies the unrestricted
full-dimensional polytope case. -/
theorem hasSmoothJordanOuterApproximationForPolytopes_of_unitBall_case
    (hunit : HasSmoothJordanOuterApproximationForUnitBallPolytopes) :
    HasSmoothJordanOuterApproximationForPolytopes := by
  intro u hPinterior
  let P : Set ℂ := convexHull ℝ (u : Set ℂ)
  obtain ⟨c, hcP⟩ := hPinterior
  obtain ⟨r, hr, hballP⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hcP)
  let s : ℝ := r / 2
  have hs : 0 < s := by
    dsimp only [s]
    linarith
  let f : ℂ →ᵃ[ℝ] ℂ := AffineMap.homothety c s⁻¹
  let v : Finset ℂ := u.image f
  let Q : Set ℂ := convexHull ℝ (v : Set ℂ)
  have hQimage : Q = f '' P := by
    dsimp only [Q, v, P]
    rw [Finset.coe_image, ← f.image_convexHull]
  have hunitQ : Metric.closedBall c 1 ⊆ Q := by
    intro z hz
    rw [hQimage]
    let y : ℂ := AffineMap.homothety c s z
    have hyBall : y ∈ Metric.ball c r := by
      dsimp only [y]
      rw [Metric.mem_ball, AffineMap.homothety_apply, dist_eq_norm,
        vadd_eq_add, vsub_eq_sub, add_sub_cancel_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hs]
      have hzdist : dist z c ≤ 1 := by
        simpa only [Metric.mem_closedBall] using hz
      have hzNorm : ‖z - c‖ ≤ 1 := by
        simpa only [dist_eq_norm] using hzdist
      dsimp only [s]
      nlinarith only [hr, hzNorm, norm_nonneg (z - c)]
    refine ⟨y, hballP hyBall, ?_⟩
    dsimp only [f, y]
    rw [← AffineMap.homothety_mul_apply]
    simp only [inv_mul_cancel₀ hs.ne', AffineMap.homothety_one,
      AffineMap.id_apply]
  have hQouter : HasSmoothJordanOuterApproximation Q := hunit v c hunitQ
  have hback : AffineMap.homothety c s '' Q = P := by
    have hcomp :
        (AffineMap.homothety c s : ℂ → ℂ) ∘ f = id := by
      funext z
      dsimp only [f, Function.comp_apply, id_eq]
      rw [← AffineMap.homothety_mul_apply]
      simp only [mul_inv_cancel₀ hs.ne', AffineMap.homothety_one,
        AffineMap.id_apply]
    calc
      AffineMap.homothety c s '' Q =
          AffineMap.homothety c s '' (f '' P) := by rw [hQimage]
      _ = ((AffineMap.homothety c s : ℂ → ℂ) ∘ f) '' P :=
        Set.image_image _ _ P
      _ = P := by rw [hcomp, Set.image_id]
  change HasSmoothJordanOuterApproximation P
  rw [← hback]
  exact hQouter.homothety c s hs.ne'

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]

/-- The exact Crouzeix--Palencia bound follows once smooth outer
approximation is proved for finite convex hulls containing a unit disk. -/
theorem crouzeix_palencia_of_smoothJordanOuterApproximation_unitBallPolytope_case
    (A : E →L[ℂ] E)
    (hunit : HasSmoothJordanOuterApproximationForUnitBallPolytopes) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply crouzeix_palencia_of_smoothJordanOuterApproximation_polytope_case A
  exact hasSmoothJordanOuterApproximationForPolytopes_of_unitBall_case hunit

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
