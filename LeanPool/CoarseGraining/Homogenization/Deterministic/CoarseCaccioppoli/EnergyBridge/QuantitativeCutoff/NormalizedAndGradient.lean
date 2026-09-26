/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.CutoffSizes
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.Basic
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.Geometry
public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.QuantitativeCutoff
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Normalized And Gradient -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

theorem normalized_quantitativeCubeCutoff_canonicalFun_descendant_average_oscillation_controls
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    let η : Vec d → ℝ :=
      QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
    let φ : Vec d → ℝ := fun x => (cubeAverage Q η)⁻¹ * η x
    let B : ℝ := (cubeAverage Q η)⁻¹
    let D : ℝ := B *
      (quantitativeCubeCutoffGradientConst d /
        (((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q))
    (∀ R ∈ descendantsAtDepth Q j, |1 - cubeAverage R φ| ≤ 1 + B) ∧
    (∀ R ∈ descendantsAtDepth Q j,
      ∀ᵐ x ∂ volumeMeasureOn (cubeSet R),
        |cubeAverage R φ - φ x| ≤ cubeScaleFactor R * D) := by
  let η : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
  let A : ℝ := cubeAverage Q η
  let φ : Vec d → ℝ := fun x => A⁻¹ * η x
  let B : ℝ := A⁻¹
  let rawD : ℝ :=
    quantitativeCubeCutoffGradientConst d /
      (((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q)
  let D : ℝ := B * rawD
  let ηq : QuantitativeCubeCutoff Q (1 / 2 : ℝ) (3 / 4 : ℝ) :=
    QuantitativeCubeCutoff.canonical Q (1 / 2 : ℝ) (3 / 4 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hpos : 0 < A := by
    simpa [A, η] using cubeAverage_quantitativeCubeCutoff_canonicalFun_pos Q
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact inv_nonneg.mpr (le_of_lt hpos)
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using
      QuantitativeCubeCutoff.canonicalFun_smooth Q
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
    simpa [φ, B, smul_eq_mul] using hη_smooth.const_smul B
  have hφ_eq : φ = B • η := by
    funext x
    simp [φ, B]
  have hrawD_nonneg : 0 ≤ rawD := by
    exact le_trans (norm_nonneg _) (by
      simpa [rawD, ηq, QuantitativeCubeCutoff.canonical] using
        ηq.gradient_bound (cubeCenter Q))
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg hB_nonneg hrawD_nonneg
  have hpoint_bound : ∀ x, ‖φ x‖ ≤ B := by
    intro x
    have hη_nonneg : 0 ≤ η x := by
      simpa [η] using
        QuantitativeCubeCutoff.canonicalFun_nonneg Q (1 / 2 : ℝ) (3 / 4 : ℝ) x
    have hη_le : η x ≤ 1 := by
      simpa [η] using
        QuantitativeCubeCutoff.canonicalFun_le_one Q (1 / 2 : ℝ) (3 / 4 : ℝ) x
    calc
      ‖φ x‖ = ‖B‖ * ‖η x‖ := by simp [φ, B, norm_mul]
      _ = B * η x := by
            rw [Real.norm_eq_abs, abs_of_nonneg hB_nonneg,
              Real.norm_eq_abs, abs_of_nonneg hη_nonneg]
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hη_le hB_nonneg
      _ = B := by ring
  have hφ_mem_top : ∀ R : TriadicCube d,
      MeasureTheory.MemLp φ ∞ (normalizedCubeMeasure R) := by
    intro R
    exact MeasureTheory.memLp_top_of_bound hφ_smooth.continuous.aestronglyMeasurable B
      (Filter.Eventually.of_forall hpoint_bound)
  have hderiv : ∀ z : Vec d, ‖fderiv ℝ φ z‖ ≤ D := by
    intro z
    have hraw : ‖fderiv ℝ η z‖ ≤ rawD := by
      simpa [η, rawD, ηq, QuantitativeCubeCutoff.canonical] using ηq.gradient_bound z
    rw [hφ_eq]
    rw [fderiv_const_smul_field (𝕜 := ℝ) (f := η) B]
    calc
      ‖B • fderiv ℝ η z‖ = ‖B‖ * ‖fderiv ℝ η z‖ := by rw [norm_smul]
      _ = B * ‖fderiv ℝ η z‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hB_nonneg]
      _ ≤ B * rawD := mul_le_mul_of_nonneg_left hraw hB_nonneg
      _ = D := by rfl
  refine ⟨?_, ?_⟩
  · intro R _hR
    have hlinfty : cubeLpNorm R ∞ φ ≤ B := by
      exact cubeLpNorm_infty_le_of_bound_on_cubeSet R φ hB_nonneg
        (fun x hx => hpoint_bound x)
    have havg_norm : ‖cubeAverage R φ‖ ≤ B := by
      exact (norm_cubeAverage_le_cubeLpNorm_infty R φ (hφ_mem_top R)).trans hlinfty
    have htri : |1 - cubeAverage R φ| ≤ 1 + |cubeAverage R φ| := by
      simpa [Real.norm_eq_abs] using norm_sub_le (1 : ℝ) (cubeAverage R φ)
    have havg_abs : |cubeAverage R φ| ≤ B := by
      simpa [Real.norm_eq_abs] using havg_norm
    have hsum : 1 + |cubeAverage R φ| ≤ 1 + B := by linarith
    exact htri.trans hsum
  · intro R _hR
    have hpoint : ∀ x ∈ cubeSet R,
        |cubeAverage R φ - φ x| ≤ cubeScaleFactor R * D := by
      intro x hx
      have havg :
          ‖φ x - cubeAverage R φ‖ ≤ cubeLpNorm R ∞ (fun y => φ y - φ x) :=
        norm_sub_cubeAverage_le_cubeLpNorm_infty_sub_const R φ x (hφ_mem_top R)
      have hlinfty :
          cubeLpNorm R ∞ (fun y => φ y - φ x) ≤ cubeScaleFactor R * D := by
        apply cubeLpNorm_infty_le_of_bound_on_cubeSet R
        · exact mul_nonneg (cubeScaleFactor_nonneg R) hD_nonneg
        · intro y hy
          simpa [norm_sub_rev] using
            norm_sub_le_cubeScaleFactor_mul_of_contDiff_bound R hφ_smooth hD_nonneg
              (fun z hz => hderiv z) hy hx
      have hnorm : ‖φ x - cubeAverage R φ‖ ≤ cubeScaleFactor R * D := havg.trans hlinfty
      simpa [Real.norm_eq_abs, abs_sub_comm] using hnorm
    simpa [volumeMeasureOn, φ, D, B, rawD, A, η] using
      (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (measurableSet_cubeSet R)).2
        (Filter.Eventually.of_forall hpoint)

theorem cubeBesovDualTestNorm_normalized_quantitativeCubeCutoff_canonicalFun_le
    {d : ℕ} (Q : TriadicCube d) {r : ℝ} (hr_le_one : r ≤ 1) (N : ℕ) :
    let η : Vec d → ℝ :=
      QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
    let φ : Vec d → ℝ := fun x => (cubeAverage Q η)⁻¹ * η x
    let B : ℝ := (cubeAverage Q η)⁻¹
    let D : ℝ := B *
      (quantitativeCubeCutoffGradientConst d /
        (((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q))
    cubeBesovDualTestNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ ≤
      cubeBesovScaleWeight r Q * (cubeScaleFactor Q * D + B) := by
  let η : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
  let A : ℝ := cubeAverage Q η
  let φ : Vec d → ℝ := fun x => A⁻¹ * η x
  let B : ℝ := A⁻¹
  let rawD : ℝ :=
    quantitativeCubeCutoffGradientConst d /
      (((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q)
  let D : ℝ := B * rawD
  let ηq : QuantitativeCubeCutoff Q (1 / 2 : ℝ) (3 / 4 : ℝ) :=
    QuantitativeCubeCutoff.canonical Q (1 / 2 : ℝ) (3 / 4 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hpos : 0 < A := by
    simpa [A, η] using cubeAverage_quantitativeCubeCutoff_canonicalFun_pos Q
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact inv_nonneg.mpr (le_of_lt hpos)
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using
      QuantitativeCubeCutoff.canonicalFun_smooth Q
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
    simpa [φ, B, smul_eq_mul] using hη_smooth.const_smul B
  have hφ_eq : φ = B • η := by
    funext x
    simp [φ, B]
  have hrawD_nonneg : 0 ≤ rawD := by
    exact le_trans (norm_nonneg _) (by
      simpa [rawD, ηq, QuantitativeCubeCutoff.canonical] using
        ηq.gradient_bound (cubeCenter Q))
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg hB_nonneg hrawD_nonneg
  have hpoint_bound : ∀ x, ‖φ x‖ ≤ B := by
    intro x
    have hη_nonneg : 0 ≤ η x := by
      simpa [η] using
        QuantitativeCubeCutoff.canonicalFun_nonneg Q (1 / 2 : ℝ) (3 / 4 : ℝ) x
    have hη_le : η x ≤ 1 := by
      simpa [η] using
        QuantitativeCubeCutoff.canonicalFun_le_one Q (1 / 2 : ℝ) (3 / 4 : ℝ) x
    calc
      ‖φ x‖ = ‖B‖ * ‖η x‖ := by simp [φ, B, norm_mul]
      _ = B * η x := by
            rw [Real.norm_eq_abs, abs_of_nonneg hB_nonneg,
              Real.norm_eq_abs, abs_of_nonneg hη_nonneg]
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hη_le hB_nonneg
      _ = B := by ring
  have hφ_mem_top : MeasureTheory.MemLp φ ∞ (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_top_of_bound hφ_smooth.continuous.aestronglyMeasurable B
      (Filter.Eventually.of_forall hpoint_bound)
  have hlinfty : cubeLpNorm Q ∞ φ ≤ B :=
    cubeLpNorm_infty_le_of_bound_on_cubeSet Q φ hB_nonneg
      (fun x hx => hpoint_bound x)
  have hderiv : ∀ z ∈ cubeSet Q, ‖fderiv ℝ φ z‖ ≤ D := by
    intro z hz
    have hraw : ‖fderiv ℝ η z‖ ≤ rawD := by
      simpa [η, rawD, ηq, QuantitativeCubeCutoff.canonical] using ηq.gradient_bound z
    rw [hφ_eq]
    rw [fderiv_const_smul_field (𝕜 := ℝ) (f := η) B]
    calc
      ‖B • fderiv ℝ η z‖ = ‖B‖ * ‖fderiv ℝ η z‖ := by rw [norm_smul]
      _ = B * ‖fderiv ℝ η z‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hB_nonneg]
      _ ≤ B * rawD := mul_le_mul_of_nonneg_left hraw hB_nonneg
      _ = D := by rfl
  calc
    cubeBesovDualTestNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ
        ≤ cubeBesovScaleWeight r Q * (cubeScaleFactor Q * D + cubeLpNorm Q ∞ φ) := by
          exact cubeBesovDualTestNorm_two_one_le_scaleWeight_mul_of_contDiff_bound_of_le_one
            Q φ N hr_le_one hD_nonneg hφ_mem_top hφ_smooth hderiv
    _ ≤ cubeBesovScaleWeight r Q * (cubeScaleFactor Q * D + B) := by
          have hsum : cubeScaleFactor Q * D + cubeLpNorm Q ∞ φ ≤ cubeScaleFactor Q * D + B := by
            linarith
          exact mul_le_mul_of_nonneg_left hsum (cubeBesovScaleWeight_nonneg r Q)

theorem cubeBesovDualLocalMemLpGlobal_normalized_quantitativeCubeCutoff_canonicalFun
    {d : ℕ} (Q : TriadicCube d) :
    let η : Vec d → ℝ :=
      QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
    let φ : Vec d → ℝ := fun x => (cubeAverage Q η)⁻¹ * η x
    CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) φ := by
  let η : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
  let A : ℝ := cubeAverage Q η
  let φ : Vec d → ℝ := fun x => A⁻¹ * η x
  let B : ℝ := A⁻¹
  have hpos : 0 < A := by
    simpa [A, η] using cubeAverage_quantitativeCubeCutoff_canonicalFun_pos Q
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact inv_nonneg.mpr (le_of_lt hpos)
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using
      QuantitativeCubeCutoff.canonicalFun_smooth Q
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
    simpa [φ, B, smul_eq_mul] using hη_smooth.const_smul B
  have hpoint_bound : ∀ x, ‖φ x‖ ≤ B := by
    intro x
    have hη_nonneg : 0 ≤ η x := by
      simpa [η] using
        QuantitativeCubeCutoff.canonicalFun_nonneg Q (1 / 2 : ℝ) (3 / 4 : ℝ) x
    have hη_le : η x ≤ 1 := by
      simpa [η] using
        QuantitativeCubeCutoff.canonicalFun_le_one Q (1 / 2 : ℝ) (3 / 4 : ℝ) x
    calc
      ‖φ x‖ = ‖B‖ * ‖η x‖ := by simp [φ, B, norm_mul]
      _ = B * η x := by
            rw [Real.norm_eq_abs, abs_of_nonneg hB_nonneg,
              Real.norm_eq_abs, abs_of_nonneg hη_nonneg]
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hη_le hB_nonneg
      _ = B := by ring
  have hφ_mem_top : ∀ R : TriadicCube d,
      MeasureTheory.MemLp φ ∞ (normalizedCubeMeasure R) := by
    intro R
    exact MeasureTheory.memLp_top_of_bound hφ_smooth.continuous.aestronglyMeasurable B
      (Filter.Eventually.of_forall hpoint_bound)
  change CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) φ
  intro j R hR
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  rw [hconj]
  exact ((hφ_mem_top R).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)).sub
    (MeasureTheory.memLp_const (cubeAverage R φ))

theorem fderiv_scalarCutoffGradientField_component_le_of_hessian_bound {d : ℕ}
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (i : Fin d)
    {B : ℝ} {z : Vec d} (hB : ‖iteratedFDeriv ℝ 2 η z‖ ≤ B) :
    ‖fderiv ℝ (fun x => scalarCutoffGradientField η x i) z‖ ≤ B := by
  have hB_nonneg : 0 ≤ B := le_trans (norm_nonneg _) hB
  have hc1 :
      ContDiffAt ℝ (1 : ℕ∞) (fderiv ℝ η) z := by
    exact
      hη.contDiffAt.fderiv_right (m := (1 : ℕ∞))
        (by
          exact_mod_cast (show (1 : ℕ∞) + 1 ≤ (⊤ : ℕ∞) by simp))
  have hc :
      DifferentiableAt ℝ (fderiv ℝ η) z := hc1.differentiableAt (by simp)
  refine ContinuousLinearMap.opNorm_le_bound _ hB_nonneg ?_
  intro v
  have happly :
      (fderiv ℝ (fun x => scalarCutoffGradientField η x i) z) v =
        (fderiv ℝ (fderiv ℝ η) z v) (basisVec i) := by
    have htmp :=
      congrArg (fun L : Vec d →L[ℝ] ℝ => L v)
        (fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ η)
          (u := fun _ : Vec d => basisVec i) hc
          (by simp))
    simpa [scalarCutoffGradientField] using htmp
  calc
    ‖(fderiv ℝ (fun x => scalarCutoffGradientField η x i) z) v‖
        = ‖(fderiv ℝ (fderiv ℝ η) z v) (basisVec i)‖ := by
            rw [happly]
    _ = ‖(fderiv ℝ (fderiv ℝ η) z (![v, basisVec i] 0)) (![v, basisVec i] 1)‖ := by
          simp
    _ = ‖iteratedFDeriv ℝ 2 η z ![v, basisVec i]‖ := by
          rw [iteratedFDeriv_two_apply]
    _ ≤ ‖iteratedFDeriv ℝ 2 η z‖ * ∏ j, ‖![v, basisVec i] j‖ := by
          simpa using ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ 2 η z) ![v, basisVec i]
    _ = ‖iteratedFDeriv ℝ 2 η z‖ * (‖v‖ * ‖basisVec i‖) := by
          simp
    _ = ‖iteratedFDeriv ℝ 2 η z‖ * ‖v‖ := by
          simp [norm_basisVec]
    _ ≤ B * ‖v‖ := by
          exact mul_le_mul_of_nonneg_right hB (norm_nonneg _)

theorem scalarCutoffGradientField_component_fderiv_bound_on_cubeSet_of_hessian_bound
    {d : ℕ} (Q : TriadicCube d) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) {B : ℝ}
    (hB : ∀ z ∈ cubeSet Q, ‖iteratedFDeriv ℝ 2 η z‖ ≤ B) :
    ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => scalarCutoffGradientField η x i) z‖ ≤ B := by
  intro i z hz
  exact fderiv_scalarCutoffGradientField_component_le_of_hessian_bound hη i (hB z hz)

theorem quantitativeCubeCutoff_memLp_top_gradientField {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) :
    MeasureTheory.MemLp (scalarCutoffGradientField η) ∞ (normalizedCubeMeasure Q) := by
  refine
    memLp_top_scalarCutoffGradientField_of_bound_on_cubeSet
      (Q := Q) (η := η) (Xi := quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q))
      η.smooth ?_
  intro z hz
  exact η.gradient_bound z

theorem quantitativeCubeCutoff_cubeLpNorm_infty_gradientField_le {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) :
    cubeLpNorm Q ∞ (scalarCutoffGradientField η) ≤
      quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q) := by
  have hXi_nonneg :
      0 ≤ quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q) := by
    exact le_trans (norm_nonneg _) (η.gradient_bound (cubeCenter Q))
  apply cubeLpNorm_infty_scalarCutoffGradientField_le_of_bound_on_cubeSet Q
  · exact hXi_nonneg
  · intro z hz
    exact η.gradient_bound z

theorem quantitativeCubeCutoff_component_fderiv_bound_on_cubeSet {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) :
    ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => scalarCutoffGradientField η x i) z‖ ≤
        quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2) := by
  exact
    scalarCutoffGradientField_component_fderiv_bound_on_cubeSet_of_hessian_bound
      Q η.smooth (fun z hz => η.hessian_bound z)

theorem normalized_quantitativeCubeCutoff_canonicalFun_gradient_controls
    {d : ℕ} (Q : TriadicCube d) :
    let η : Vec d → ℝ :=
      QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
    let φ : Vec d → ℝ := fun x => (cubeAverage Q η)⁻¹ * η x
    MeasureTheory.MemLp (scalarCutoffGradientField φ) ∞ (normalizedCubeMeasure Q) ∧
    (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => scalarCutoffGradientField φ x i)) ∧
    (∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => scalarCutoffGradientField φ x i) z‖ ≤
        (cubeAverage Q η)⁻¹ *
          (quantitativeCubeCutoffHessianConst d /
            ((((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q) ^ 2))) := by
  let η : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
  let A : ℝ := cubeAverage Q η
  let φ : Vec d → ℝ := fun x => A⁻¹ * η x
  let ηq : QuantitativeCubeCutoff Q (1 / 2 : ℝ) (3 / 4 : ℝ) :=
    QuantitativeCubeCutoff.canonical Q (1 / 2 : ℝ) (3 / 4 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hpos : 0 < A := by
    simpa [A, η] using cubeAverage_quantitativeCubeCutoff_canonicalFun_pos Q
  have hA_nonneg : 0 ≤ A⁻¹ := inv_nonneg.mpr (le_of_lt hpos)
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using
      QuantitativeCubeCutoff.canonicalFun_smooth Q
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
    simpa [φ, smul_eq_mul] using hη_smooth.const_smul A⁻¹
  have hgrad_eq : scalarCutoffGradientField φ = A⁻¹ • scalarCutoffGradientField η := by
    have hφ_eq : φ = A⁻¹ • η := by
      funext x
      simp [φ]
    funext x i
    change (fderiv ℝ φ x) (basisVec i) =
      (A⁻¹ • scalarCutoffGradientField η x) i
    rw [hφ_eq]
    rw [fderiv_const_smul_field (𝕜 := ℝ) (f := η) A⁻¹]
    simp [scalarCutoffGradientField]
  have hraw_mem : MeasureTheory.MemLp (scalarCutoffGradientField η) ∞ (normalizedCubeMeasure Q) := by
    simpa [η, ηq, QuantitativeCubeCutoff.canonical] using
      quantitativeCubeCutoff_memLp_top_gradientField Q ηq
  have hmem : MeasureTheory.MemLp (scalarCutoffGradientField φ) ∞ (normalizedCubeMeasure Q) := by
    rw [hgrad_eq]
    exact hraw_mem.const_smul A⁻¹
  refine ⟨hmem, ?_, ?_⟩
  · intro i
    exact contDiff_scalarCutoffGradientField_component hφ_smooth i
  · intro i z hz
    have hcomponent_eq :
        (fun x => scalarCutoffGradientField φ x i) =
          fun x => A⁻¹ * scalarCutoffGradientField η x i := by
      funext x
      have h := congrFun (congrFun hgrad_eq x) i
      simpa using h
    have hfun_eq :
        (fun x => A⁻¹ * scalarCutoffGradientField η x i) =
          A⁻¹ • (fun x => scalarCutoffGradientField η x i) := by
      funext x
      simp
    have hraw :
        ‖fderiv ℝ (fun x => scalarCutoffGradientField η x i) z‖ ≤
          quantitativeCubeCutoffHessianConst d /
            ((((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q) ^ 2) := by
      simpa [η, ηq, QuantitativeCubeCutoff.canonical] using
        quantitativeCubeCutoff_component_fderiv_bound_on_cubeSet Q ηq i z hz
    rw [hcomponent_eq, hfun_eq]
    rw [fderiv_const_smul_field (𝕜 := ℝ)
      (f := fun x => scalarCutoffGradientField η x i) A⁻¹]
    calc
      ‖A⁻¹ • fderiv ℝ (fun x => scalarCutoffGradientField η x i) z‖
          = ‖A⁻¹‖ * ‖fderiv ℝ (fun x => scalarCutoffGradientField η x i) z‖ := by
            rw [norm_smul]
      _ = A⁻¹ * ‖fderiv ℝ (fun x => scalarCutoffGradientField η x i) z‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hA_nonneg]
      _ ≤ A⁻¹ *
            (quantitativeCubeCutoffHessianConst d /
              ((((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hraw hA_nonneg

/-- `L∞` bound for the scalar-gradient field of the normalized quantitative
cutoff.  This extracts the gradient-size part of
`normalized_quantitativeCubeCutoff_canonicalFun_gradient_controls`; it is used
to bound the Section 5.3 cutoff-product coefficient. -/
theorem cubeLpNorm_infty_scalarCutoffGradientField_normalized_quantitativeCubeCutoff_canonicalFun_le
    {d : ℕ} (Q : TriadicCube d) :
    let η : Vec d → ℝ :=
      QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
    let φ : Vec d → ℝ := fun x => (cubeAverage Q η)⁻¹ * η x
    cubeLpNorm Q ∞ (scalarCutoffGradientField φ) ≤
      (cubeAverage Q η)⁻¹ *
        (quantitativeCubeCutoffGradientConst d /
          (((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q)) := by
  let η : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
  let A : ℝ := cubeAverage Q η
  let φ : Vec d → ℝ := fun x => A⁻¹ * η x
  let ηq : QuantitativeCubeCutoff Q (1 / 2 : ℝ) (3 / 4 : ℝ) :=
    QuantitativeCubeCutoff.canonical Q (1 / 2 : ℝ) (3 / 4 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hpos : 0 < A := by
    simpa [A, η] using cubeAverage_quantitativeCubeCutoff_canonicalFun_pos Q
  have hA_nonneg : 0 ≤ A⁻¹ := inv_nonneg.mpr (le_of_lt hpos)
  have hφ_eq : φ = A⁻¹ • η := by
    funext x
    simp [φ]
  have hG_nonneg : 0 ≤ quantitativeCubeCutoffGradientConst d := by
    unfold quantitativeCubeCutoffGradientConst
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
      smoothTransitionProfile.derivBound_nonneg
  apply cubeLpNorm_infty_scalarCutoffGradientField_le_of_bound_on_cubeSet Q
  · exact mul_nonneg hA_nonneg
      (div_nonneg hG_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (3 / 4 : ℝ) - (1 / 2 : ℝ))
          (cubeRadius_pos Q).le))
  · intro z hz
    change ‖fderiv ℝ φ z‖ ≤
      A⁻¹ *
        (quantitativeCubeCutoffGradientConst d /
          (((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q))
    have hraw :
        ‖fderiv ℝ η z‖ ≤
          quantitativeCubeCutoffGradientConst d /
            (((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q) := by
      simpa [η, ηq, QuantitativeCubeCutoff.canonical] using
        (ηq.gradient_bound z)
    rw [hφ_eq]
    rw [fderiv_const_smul_field (𝕜 := ℝ) (f := η) A⁻¹]
    calc
      ‖A⁻¹ • fderiv ℝ η z‖
          = ‖A⁻¹‖ * ‖fderiv ℝ η z‖ := by
            rw [norm_smul]
      _ = A⁻¹ * ‖fderiv ℝ η z‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hA_nonneg]
      _ ≤ A⁻¹ *
            (quantitativeCubeCutoffGradientConst d /
              (((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q)) := by
            exact mul_le_mul_of_nonneg_left hraw hA_nonneg

/-- The gradient field of a quantitative cutoff built on a parent cube is
`L∞` on every descendant cube.  This is the small-cube version needed by the
Chapter 3 Caccioppoli argument. -/
theorem quantitativeCubeCutoff_memLp_top_gradientField_on_descendant {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (_hR : R ∈ descendantsAtDepth Q j)
    {ρ₁ ρ₂ : ℝ} (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) :
    MeasureTheory.MemLp (scalarCutoffGradientField η) ∞ (normalizedCubeMeasure R) := by
  refine
    memLp_top_scalarCutoffGradientField_of_bound_on_cubeSet
      (Q := R) (η := η)
      (Xi := quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q))
      η.smooth ?_
  intro z hz
  exact η.gradient_bound z

/-- Descendant-local `L∞` bound for the gradient field of a parent-cube
quantitative cutoff. -/
theorem quantitativeCubeCutoff_cubeLpNorm_infty_gradientField_le_on_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (_hR : R ∈ descendantsAtDepth Q j) {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) :
    cubeLpNorm R ∞ (scalarCutoffGradientField η) ≤
      quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q) := by
  have hXi_nonneg :
      0 ≤ quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q) := by
    exact le_trans (norm_nonneg _) (η.gradient_bound (cubeCenter Q))
  apply cubeLpNorm_infty_scalarCutoffGradientField_le_of_bound_on_cubeSet R
  · exact hXi_nonneg
  · intro z hz
    exact η.gradient_bound z

/-- Descendant-local derivative bound for the cutoff-gradient field.  The
bound is still expressed with the parent cube radius, while later small-cube
bookkeeping multiplies it by the descendant scale. -/
theorem quantitativeCubeCutoff_component_fderiv_bound_on_descendant {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    {ρ₁ ρ₂ : ℝ} (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) :
    ∀ i : Fin d, ∀ z ∈ cubeSet R,
      ‖fderiv ℝ (fun x => scalarCutoffGradientField η x i) z‖ ≤
        quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2) := by
  intro i z hz
  exact quantitativeCubeCutoff_component_fderiv_bound_on_cubeSet Q η i z
    (cubeSet_subset_of_mem_descendantsAtDepth hR hz)

theorem CoarseCaccioppoliScalarCutoffControls.of_quantitativeCubeCutoff
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {ρ₁ ρ₂ : ℝ}
    (u g : Vec d → ℝ) (energy : Vec d → ℝ)
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C : ℝ}
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize Q u (scalarCutoffGradientField η)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize Q s (scalarCutoffGradientField η) Acirc1 AcircS
          (Real.sqrt (cubeAverage Q energy))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)) C)
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hgCirc1 : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        Acirc1 * Real.sqrt (cubeAverage Q energy))
    (hgCircS : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        AcircS * Real.sqrt (cubeAverage Q energy)) :
    CoarseCaccioppoliScalarCutoffControls Q s u g (scalarCutoffGradientField η) energy
      Acirc1 AcircS
      (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)) C := by
  refine
    ⟨hB, hBgConst, hBgCent, hC, hproj, ?_, ?_, hgCirc1, hgCircS⟩
  · intro i
    exact contDiff_scalarCutoffGradientField_component η.smooth i
  · intro i z hz
    exact quantitativeCubeCutoff_component_fderiv_bound_on_cubeSet Q η i z hz

/-- Scalar cutoff-control package on a descendant cube, using a quantitative
cutoff constructed on the parent cube. -/
theorem CoarseCaccioppoliScalarCutoffControls.of_quantitativeCubeCutoff_on_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (s : ℝ) {ρ₁ ρ₂ : ℝ}
    (u g : Vec d → ℝ) (energy : Vec d → ℝ)
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C : ℝ}
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u (scalarCutoffGradientField η)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s (scalarCutoffGradientField η) Acirc1 AcircS
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)) C)
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate R C (cubeFluctuation R u) g N)
    (hgCirc1 : ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hgCircS : ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        AcircS * Real.sqrt (cubeAverage R energy)) :
    CoarseCaccioppoliScalarCutoffControls R s u g (scalarCutoffGradientField η) energy
      Acirc1 AcircS
      (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)) C := by
  refine
    ⟨hB, hBgConst, hBgCent, hC, hproj, ?_, ?_, hgCirc1, hgCircS⟩
  · intro i
    exact contDiff_scalarCutoffGradientField_component η.smooth i
  · intro i z hz
    exact quantitativeCubeCutoff_component_fderiv_bound_on_descendant hR η i z hz

/-- Vector projected-Poincare version of
`CoarseCaccioppoliScalarCutoffControls.of_quantitativeCubeCutoff`.

The vector Poincare constant is `C`; the centered exact cutoff size is stated
with the effective scalar-facing constant `(Fintype.card (Fin d) : ℝ) * C`. -/
theorem CoarseCaccioppoliVectorCutoffControls.of_quantitativeCubeCutoff
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {ρ₁ ρ₂ : ℝ}
    (u : Vec d → ℝ) (G : Vec d → Vec d) (energy : Vec d → ℝ)
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C : ℝ}
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize Q u (scalarCutoffGradientField η)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize Q s (scalarCutoffGradientField η) Acirc1 AcircS
          (Real.sqrt (cubeAverage Q energy))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage Q energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage Q energy)) :
    CoarseCaccioppoliVectorCutoffControls Q s u G (scalarCutoffGradientField η) energy
      Acirc1 AcircS
      (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)) C := by
  refine
    ⟨hB, hAcircS, hBgConst, hBgCent, hC, hproj, ?_, ?_, hGcirc1, hGcircS⟩
  · intro i
    exact contDiff_scalarCutoffGradientField_component η.smooth i
  · intro i z hz
    exact quantitativeCubeCutoff_component_fderiv_bound_on_cubeSet Q η i z hz

/-- Vector projected-Poincare cutoff-control package on a descendant cube,
using a quantitative cutoff constructed on the parent cube. -/
theorem CoarseCaccioppoliVectorCutoffControls.of_quantitativeCubeCutoff_on_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (s : ℝ) {ρ₁ ρ₂ : ℝ}
    (u : Vec d → ℝ) (G : Vec d → Vec d) (energy : Vec d → ℝ)
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C : ℝ}
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u (scalarCutoffGradientField η)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s (scalarCutoffGradientField η) Acirc1 AcircS
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    CoarseCaccioppoliVectorCutoffControls R s u G (scalarCutoffGradientField η) energy
      Acirc1 AcircS
      (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)) C := by
  refine
    ⟨hB, hAcircS, hBgConst, hBgCent, hC, hproj, ?_, ?_, hGcirc1, hGcircS⟩
  · intro i
    exact contDiff_scalarCutoffGradientField_component η.smooth i
  · intro i z hz
    exact quantitativeCubeCutoff_component_fderiv_bound_on_descendant hR η i z hz

end

end Homogenization
