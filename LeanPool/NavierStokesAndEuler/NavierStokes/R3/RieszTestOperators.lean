/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszSymbolRegularity
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszL2Bounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.SmoothSobolevL6
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LpNormTools
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierTestDerivatives
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszLinearityDecay

@[expose] public section

/-!
# Differential identities for the Riesz test operators

The operators here are the actual inverse Fourier integrals from
`ComparisonFourierSetup`. Differentiation uses their integrable Fourier moments.
-/


noncomputable section

open MeasureTheory
open scoped ContDiff FourierTransform RealInnerProductSpace BigOperators ENNReal

namespace NavierStokesR3.RieszTestOperators

open ProblemStatement Comparison
open HarmonicTestFunctionals

/-- A coordinate derivative, retained as a Schwartz function. -/
abbrev partialTest (k : Fin 3) (ψ : ComplexTest) : ComplexTest :=
  LineDeriv.lineDerivOpCLM ℂ ComplexTest (NavierStokes.ProblemStatement.coordinateVector k) ψ

@[simp] theorem partialTest_apply (k : Fin 3) (ψ : ComplexTest) (x : Space) :
    partialTest k ψ x = Comparison.partialD k (fun y => ψ y) x := rfl

/-- The Fourier transform of a directional derivative of a Schwartz function. -/
theorem fourier_pderivTest (ψ : ComplexTest) (d ξ : Space) :
    (FourierTransform.fourierCLE ℂ ComplexTest (LineDeriv.lineDerivOpCLM ℂ ComplexTest d ψ)) ξ =
      (2 * Real.pi * Complex.I) * (⟪ξ, d⟫ : ℂ) *
        (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ := by
  have hD : Integrable (fderiv ℝ (fun y => ψ y)) :=
    (SchwartzMap.fderivCLM ℂ Space ℂ ψ).integrable
  change 𝓕 (fun x => fderiv ℝ (fun y => ψ y) x d) ξ = _
  rw [← Real.fourier_continuousLinearMap_apply hD,
    Real.fourier_fderiv ψ.integrable ψ.differentiable hD]
  simp only [VectorFourier.fourierSMulRight_apply, _root_.neg_apply, Complex.real_smul,
    smul_eq_mul, Complex.ofReal_neg,
    FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe]
  erw [innerSL_apply_apply]
  ring

theorem fourier_partialTest (ψ : ComplexTest) (k : Fin 3) (ξ : Space) :
    (FourierTransform.fourierCLE ℂ ComplexTest (partialTest k ψ)) ξ =
      (2 * Real.pi * Complex.I) * (ξ k : ℂ) *
        (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ := by
  simpa only [partialTest, NavierStokes.ProblemStatement.coordinateVector,
    EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] using
    fourier_pderivTest ψ (NavierStokes.ProblemStatement.coordinateVector k) ξ

/-- An integrable first Fourier moment permits differentiation of the inverse
Fourier integral in every direction. -/
theorem fderiv_fourierInv_apply {f : Space → ℂ} (hf : Integrable f)
    (hf1 : Integrable (fun ξ : Space => ‖ξ‖ * ‖f ξ‖)) (x d : Space) :
    fderiv ℝ (𝓕⁻ f) x d =
      𝓕⁻ (fun ξ : Space =>
        (2 * Real.pi * Complex.I) * (⟪ξ, d⟫ : ℂ) * f ξ) x := by
  let L : Space →L[ℝ] Space →L[ℝ] ℝ :=
    -(innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ)
  have hL : L.toLinearMap₁₂ = -innerₗ Space := rfl
  have hR : Integrable (VectorFourier.fourierSMulRight L f) := by
    refine (hf1.const_mul (2 * Real.pi * ‖L‖)).mono'
      hf.aestronglyMeasurable.fourierSMulRight ?_
    filter_upwards with ξ
    exact (VectorFourier.norm_fourierSMulRight_le L f ξ).trans_eq (by ring)
  have hd : fderiv ℝ (𝓕⁻ f) x =
      𝓕⁻ (VectorFourier.fourierSMulRight L f) x := by
    simpa only [FourierTransform.fourierInv, hL] using
      (VectorFourier.hasFDerivAt_fourierIntegral L hf hf1 x).fderiv
  rw [hd]
  have heval : (𝓕⁻ (VectorFourier.fourierSMulRight L f) x) d =
      𝓕⁻ (fun ξ => VectorFourier.fourierSMulRight L f ξ d) x := by
    simpa only [FourierTransform.fourierInv, hL] using
      (Real.fourierIntegral_continuousLinearMap_apply'
        (L := L) (a := d) (w := x) hR)
  rw [heval]
  apply congrArg (fun g : Space → ℂ => 𝓕⁻ g x)
  funext ξ
  simp only [L, VectorFourier.fourierSMulRight_apply, _root_.neg_apply, Complex.real_smul,
    smul_eq_mul, Complex.ofReal_neg]
  erw [innerSL_apply_apply]
  ring

/-- Riesz transforms commute with directional derivatives on Schwartz inputs. -/
theorem pderiv_rieszTest (i j : Fin 3) (ψ : ComplexTest) (d x : Space) :
    fderiv ℝ (rieszTest i j ψ) x d =
      rieszTest i j (LineDeriv.lineDerivOpCLM ℂ ComplexTest d ψ) x := by
  change fderiv ℝ (𝓕⁻ (fun ξ : Space =>
      (rieszSymbol i j ξ : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ)) x d = _
  rw [fderiv_fourierInv_apply (integrable_rieszMultiplier i j ψ)
    (by simpa only [pow_one] using integrable_pow_mul_norm_rieszMultiplier i j ψ 1)]
  unfold rieszTest
  apply congrArg (fun g : Space → ℂ => 𝓕⁻ g x)
  funext ξ
  rw [fourier_pderivTest]
  ring

theorem partial_rieszTest (i j : Fin 3) (ψ : ComplexTest) (k : Fin 3) (x : Space) :
    Comparison.partialD k (rieszTest i j ψ) x = rieszTest i j (partialTest k ψ) x :=
  pderiv_rieszTest i j ψ (NavierStokes.ProblemStatement.coordinateVector k) x

theorem partial_rieszTest_eq (i j : Fin 3) (ψ : ComplexTest) (k : Fin 3) :
    Comparison.partialD k (rieszTest i j ψ) = rieszTest i j (partialTest k ψ) :=
  funext (partial_rieszTest i j ψ k)

theorem memLp_partial_rieszTest (i j : Fin 3) (ψ : ComplexTest) (k : Fin 3) :
    MemLp (Comparison.partialD k (rieszTest i j ψ)) 2 volume := by
  rw [partial_rieszTest_eq]
  exact memLp_rieszTest i j (partialTest k ψ)

theorem integral_norm_sq_partial_rieszTest_le (i j : Fin 3) (ψ : ComplexTest)
    (k : Fin 3) :
    (∫ x : Space, ‖Comparison.partialD k (rieszTest i j ψ) x‖ ^ 2) ≤
      ∫ x : Space, ‖Comparison.partialD k (fun y => ψ y) x‖ ^ 2 := by
  rw [partial_rieszTest_eq]
  simpa only [partialTest_apply] using
    integral_norm_sq_rieszTest_le i j (partialTest k ψ)

theorem lpNorm_two_partial_rieszTest_le (i j : Fin 3) (ψ : ComplexTest)
    (k : Fin 3) :
    comparisonLpNorm 2 (Comparison.partialD k (rieszTest i j ψ)) ≤
      comparisonLpNorm 2 (Comparison.partialD k (fun y => ψ y)) := by
  have hψ : MemLp (Comparison.partialD k (fun y => ψ y)) 2 volume :=
    (partialTest k ψ).memLp 2 volume
  have h := integral_norm_sq_partial_rieszTest_le i j ψ k
  change l2Sq (Comparison.partialD k (rieszTest i j ψ)) ≤
    l2Sq (Comparison.partialD k (fun y => ψ y)) at h
  rw [← LpNormTools.lpNorm_two_sq_eq_l2Sq (memLp_partial_rieszTest i j ψ k),
    ← LpNormTools.lpNorm_two_sq_eq_l2Sq hψ] at h
  exact (sq_le_sq₀ (LpNormTools.lpNorm_nonneg _ _) (LpNormTools.lpNorm_nonneg _ _)).mp h

/-- The three coordinate columns control the operator norm of a real-linear map. -/
theorem norm_clm_le_sum_coordinate_norms {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : Space →L[ℝ] E) :
    ‖A‖ ≤ ∑ k : Fin 3, ‖A (NavierStokes.ProblemStatement.coordinateVector k)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have hsplit : A v = ∑ k : Fin 3,
      v k • A (NavierStokes.ProblemStatement.coordinateVector k) := by
    conv_lhs => rw [← NavierStokes.PeriodicUniqueness.sum_coordinates v]
    simp only [map_sum, map_smul]
  rw [hsplit]
  calc
    ‖∑ k : Fin 3, v k • A (NavierStokes.ProblemStatement.coordinateVector k)‖ ≤
        ∑ k : Fin 3, ‖v k • A (NavierStokes.ProblemStatement.coordinateVector k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k : Fin 3, ‖v‖ * ‖A (NavierStokes.ProblemStatement.coordinateVector k)‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v k) (norm_nonneg _)
    _ = (∑ k : Fin 3, ‖A (NavierStokes.ProblemStatement.coordinateVector k)‖) * ‖v‖ := by
      rw [← Finset.mul_sum, mul_comm]

private theorem memLp_partial_norm_sum (i j : Fin 3) (ψ : ComplexTest) :
    MemLp (fun x : Space => ∑ k : Fin 3,
      ‖Comparison.partialD k (rieszTest i j ψ) x‖) 2 volume := by
  exact MeasureTheory.memLp_finsetSum Finset.univ
    (fun k _ => (memLp_partial_rieszTest i j ψ k).norm)

/-- The complete spatial derivative has a finite `L²` norm. -/
theorem memLp_fderiv_rieszTest (i j : Fin 3) (ψ : ComplexTest) :
    MemLp (fderiv ℝ (rieszTest i j ψ)) 2 volume := by
  have hC1 : ContDiff ℝ 1 (rieszTest i j ψ) :=
    (contDiff_rieszTest i j ψ).of_le (by simp)
  refine (memLp_partial_norm_sum i j ψ).mono'
    (hC1.continuous_fderiv (by simp)).aestronglyMeasurable ?_
  filter_upwards with x
  exact norm_clm_le_sum_coordinate_norms (fderiv ℝ (rieszTest i j ψ) x)

private theorem lpNorm_two_fin3_sum_le {E : Type*} [NormedAddCommGroup E]
    (f : Fin 3 → Space → E) (hf : ∀ k, MemLp (f k) 2 volume) :
    comparisonLpNorm 2 (fun x => ∑ k : Fin 3, f k x) ≤ ∑ k : Fin 3, comparisonLpNorm 2 (f k) := by
  have h := (LpNormTools.lpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((hf 0).add (hf 1)) (hf 2)).trans
      (add_le_add_left (LpNormTools.lpNorm_add_le
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hf 0) (hf 1)) _)
  simpa only [Fin.sum_univ_three, Pi.add_apply, add_assoc] using h

theorem lpNorm_two_fderiv_rieszTest_le (i j : Fin 3) (ψ : ComplexTest) :
    comparisonLpNorm 2 (fderiv ℝ (rieszTest i j ψ)) ≤
      3 * comparisonLpNorm 2 (fderiv ℝ (fun y => ψ y)) := by
  have hDψ : MemLp (fderiv ℝ (fun y => ψ y)) 2 volume :=
    (SchwartzMap.fderivCLM ℂ Space ℂ ψ).memLp 2 volume
  have hcol (k : Fin 3) (x : Space) :
      ‖Comparison.partialD k (fun y => ψ y) x‖ ≤ ‖fderiv ℝ (fun y => ψ y) x‖ := by
    simpa only [Comparison.partialD, NavierStokes.PeriodicIntegration.spatialPartial,
      NavierStokes.ProblemStatement.coordinateVector, PiLp.norm_single,
      norm_one, mul_one] using
      (fderiv ℝ (fun y => ψ y) x).le_opNorm
        (NavierStokes.ProblemStatement.coordinateVector k)
  calc
    comparisonLpNorm 2 (fderiv ℝ (rieszTest i j ψ)) ≤
        comparisonLpNorm 2 (fun x : Space => ∑ k : Fin 3,
          ‖Comparison.partialD k (rieszTest i j ψ) x‖) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (memLp_partial_norm_sum i j ψ)
      intro x
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
      exact norm_clm_le_sum_coordinate_norms (fderiv ℝ (rieszTest i j ψ) x)
    _ ≤ ∑ k : Fin 3, comparisonLpNorm 2 (fun x : Space =>
        ‖Comparison.partialD k (rieszTest i j ψ) x‖) :=
      lpNorm_two_fin3_sum_le _ (fun k => (memLp_partial_rieszTest i j ψ k).norm)
    _ = ∑ k : Fin 3, comparisonLpNorm 2 (Comparison.partialD k (rieszTest i j ψ)) := by
      simp only [comparisonLpNorm, eLpNorm_norm]
    _ ≤ ∑ k : Fin 3, comparisonLpNorm 2 (Comparison.partialD k (fun y => ψ y)) := by
      exact Finset.sum_le_sum fun k _ => lpNorm_two_partial_rieszTest_le i j ψ k
    _ ≤ ∑ _k : Fin 3, comparisonLpNorm 2 (fderiv ℝ (fun y => ψ y)) := by
      exact Finset.sum_le_sum fun k _ =>
        LpNormTools.lpNorm_mono_of_norm_le hDψ (hcol k)
    _ = 3 * comparisonLpNorm 2 (fderiv ℝ (fun y => ψ y)) := by simp

theorem memLp_rieszTest_six (i j : Fin 3) (ψ : ComplexTest) :
    MemLp (rieszTest i j ψ) 6 volume :=
  smooth_memLp_six ((contDiff_rieszTest i j ψ).of_le (by simp))
    (memLp_rieszTest i j ψ) (memLp_fderiv_rieszTest i j ψ)

/-- The homogeneous `L⁶` estimate needed in the pressure flux. Both the output
and its derivative have genuine finite norms by the membership theorems above. -/
theorem lpNorm_six_rieszTest_le (i j : Fin 3) (ψ : ComplexTest) :
    comparisonLpNorm 6 (rieszTest i j ψ) ≤
      3 * (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
        comparisonLpNorm 2 (fderiv ℝ (fun y => ψ y)) := by
  have h := smooth_eLpNorm_six_toReal_le
    ((contDiff_rieszTest i j ψ).of_le (by simp))
    (memLp_rieszTest i j ψ) (memLp_fderiv_rieszTest i j ψ)
  change comparisonLpNorm 6 (rieszTest i j ψ) ≤
    (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
      comparisonLpNorm 2 (fderiv ℝ (rieszTest i j ψ)) at h
  calc
    _ ≤ (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
        comparisonLpNorm 2 (fderiv ℝ (rieszTest i j ψ)) := h
    _ ≤ (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
        (3 * comparisonLpNorm 2 (fderiv ℝ (fun y => ψ y))) :=
      mul_le_mul_of_nonneg_left (lpNorm_two_fderiv_rieszTest_le i j ψ) (by positivity)
    _ = _ := by ring

/-- Applying the test operator to the ordinary Laplacian recovers the negative
mixed derivative. The multiplier identity is valid also at frequency zero. -/
theorem rieszTest_laplacianCLM (i j : Fin 3) (ψ : ComplexTest) (x : Space) :
    rieszTest i j (laplacianCLM ψ) x =
      -(partialCLM i (partialCLM j ψ)) x := by
  have hmult (ξ : Space) :
      (rieszSymbol i j ξ : ℂ) *
          (FourierTransform.fourierCLE ℂ ComplexTest (laplacianCLM ψ)) ξ =
        (FourierTransform.fourierCLE ℂ ComplexTest (-(partialCLM i (partialCLM j ψ)))) ξ := by
    rw [map_neg]
    change (rieszSymbol i j ξ : ℂ) *
        (FourierTransform.fourierCLE ℂ ComplexTest (laplacianCLM ψ)) ξ =
      -((FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i (partialCLM j ψ))) ξ)
    rw [fourier_laplacianCLM_apply, fourier_partialCLM_apply, fourier_partialCLM_apply]
    have hsymbol : (rieszSymbol i j ξ : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ) =
        -((ξ i : ℂ) * (ξ j : ℂ)) := by
      exact_mod_cast rieszSymbol_mul_norm_sq i j ξ
    calc
      _ = -(4 * (Real.pi : ℂ) ^ 2) *
          ((rieszSymbol i j ξ : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ)) *
            (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ := by ring
      _ = _ := by
        rw [hsymbol]
        ring_nf
        simp [Complex.I_sq]
  have hfun : (fun ξ : Space => (rieszSymbol i j ξ : ℂ) *
      (FourierTransform.fourierCLE ℂ ComplexTest (laplacianCLM ψ)) ξ) =
      (FourierTransform.fourierCLE ℂ ComplexTest (-(partialCLM i (partialCLM j ψ))) :
        Space → ℂ) := funext hmult
  unfold rieszTest
  rw [hfun]
  have hinv := congrArg (fun φ : ComplexTest => φ x)
    ((FourierTransform.fourierCLE ℂ ComplexTest).symm_apply_apply
      (-(partialCLM i (partialCLM j ψ))))
  simpa only [FourierTransform.fourierCLE_symm_apply, SchwartzMap.fourierInv_coe] using! hinv

/-- The canonical pressure functional solves the test-function Poisson equation. -/
theorem pressurePair_laplacianCLM (i j : Fin 3) (g : Space → ℝ) (ψ : ComplexTest) :
    pressurePair i j g (laplacianCLM ψ) =
      -(∫ x : Space, (g x : ℂ) * (partialCLM i (partialCLM j ψ)) x) := by
  simp only [pressurePair, rieszTest_laplacianCLM, mul_neg, integral_neg]

/-- The actual smooth Riesz test function satisfies the classical Poisson identity. -/
theorem laplacian_rieszTest (i j : Fin 3) (ψ : ComplexTest) (x : Space) :
    (∑ k : Fin 3, Comparison.partialD k
      (Comparison.partialD k (rieszTest i j ψ)) x) =
      -Comparison.partialD i (Comparison.partialD j (fun y => ψ y)) x := by
  have hLap : laplacianCLM ψ =
      ∑ k : Fin 3, partialTest k (partialTest k ψ) := by
    simp [laplacianCLM, partialCLM, partialTest, Fin.sum_univ_three]
  calc
    _ = ∑ k : Fin 3, rieszTest i j (partialTest k (partialTest k ψ)) x := by
      apply Finset.sum_congr rfl
      intro k _
      rw [partial_rieszTest_eq, partial_rieszTest]
    _ = rieszTest i j (laplacianCLM ψ) x := by
      rw [hLap, rieszTest_sum]
      simp only [Finset.sum_apply]
    _ = _ := by
      rw [rieszTest_laplacianCLM]
      rfl

end NavierStokesR3.RieszTestOperators
