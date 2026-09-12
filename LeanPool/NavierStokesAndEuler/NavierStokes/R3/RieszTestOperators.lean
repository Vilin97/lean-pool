/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierTestDerivatives
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicUniqueness
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LpNormTools
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszLinearityDecay
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszSymbolRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.SmoothSobolevL6
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFourierSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactSchwartz
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszPairing
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.SchwartzParseval
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Differential identities for the Riesz test operators

The operators here are the actual inverse Fourier integrals from
`ComparisonFourierSetup`. Differentiation uses their integrable Fourier moments.
-/

section

/-!
# The `L²` bound for Riesz operators on Schwartz tests

The Fourier pairing and Schwartz Parseval imply a dual bound. Testing it
against a compact smooth cutoff times the output bounds every truncated
energy. Fatou's lemma then proves both square integrability and the global
bound, without extending the Fourier transform to arbitrary `L²` functions.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff FourierTransform ComplexConjugate ENNReal Topology

namespace NavierStokesR3.RieszTestOperators

open ProblemStatement Comparison

/-- Cauchy--Schwarz and the multiplier bound give the test-function dual estimate. -/
theorem norm_rieszTest_pairing_le (i j : Fin 3) (ψ φ : ComplexTest) :
    ‖∫ x : Space, rieszTest i j ψ x * conj (φ x)‖ ≤
      Real.sqrt (∫ x : Space, ‖ψ x‖ ^ 2) *
        Real.sqrt (∫ x : Space, ‖φ x‖ ^ 2) := by
  let Fψ : ComplexTest := FourierTransform.fourierCLE ℂ ComplexTest ψ
  let Fφ : ComplexTest := FourierTransform.fourierCLE ℂ ComplexTest φ
  have hprod : Integrable (fun ξ : Space => ‖Fψ ξ‖ * ‖Fφ ξ‖) :=
    (Fψ.memLp 2).norm.integrable_mul (Fφ.memLp 2).norm
  rw [rieszTest_pairing_fourier_conj]
  change ‖∫ ξ : Space, (rieszSymbol i j ξ : ℂ) * Fψ ξ * conj (Fφ ξ)‖ ≤ _
  calc
    _ ≤ ∫ ξ : Space, ‖(rieszSymbol i j ξ : ℂ) * Fψ ξ * conj (Fφ ξ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ξ : Space, ‖Fψ ξ‖ * ‖Fφ ξ‖ := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hprod
      filter_upwards [] with ξ
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have hm := mul_le_mul_of_nonneg_right
        (norm_rieszSymbol_complex_le i j ξ) (norm_nonneg (Fψ ξ))
      rw [one_mul] at hm
      exact mul_le_mul_of_nonneg_right hm (norm_nonneg (Fφ ξ))
    _ ≤ _ := by
      have h := integral_mul_norm_le_Lp_mul_Lq
        (μ := (volume : Measure Space)) (f := (Fψ : Space → ℂ))
        (g := (Fφ : Space → ℂ)) Real.HolderConjugate.two_two
        (by simpa using Fψ.memLp 2) (by simpa using Fφ.memLp 2)
      have hψ : (∫ ξ : Space, ‖Fψ ξ‖ ^ 2) = ∫ x : Space, ‖ψ x‖ ^ 2 :=
        SchwartzParseval.integral_norm_sq_fourier ψ
      have hφ : (∫ ξ : Space, ‖Fφ ξ‖ ^ 2) = ∫ x : Space, ‖φ x‖ ^ 2 :=
        SchwartzParseval.integral_norm_sq_fourier φ
      simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, hψ, hφ] using h

private noncomputable def l2Cutoff (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := (n : ℝ) + 1
  rOut := (n : ℝ) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

private theorem l2Cutoff_eventually_one (x : Space) :
    ∀ᶠ n : ℕ in atTop, l2Cutoff n x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply (l2Cutoff n).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖x‖ ≤ (n : ℝ) + 1
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

private theorem cutoff_energy_le_of_pairing_bound {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ φ : ComplexTest,
      ‖∫ x : Space, f x * conj (φ x)‖ ≤
        Real.sqrt C * Real.sqrt (∫ x : Space, ‖φ x‖ ^ 2))
    (χ : ContDiffBump (0 : Space)) :
    (∫ x : Space, χ x * ‖f x‖ ^ 2) ≤ C := by
  let φ : ComplexTest := CompactSchwartz.ofCompactSupport
    (fun x => χ x • f x) (χ.contDiff.smul hf) χ.hasCompactSupport.smul_right
  have hYi : Integrable (fun x : Space => χ x * ‖f x‖ ^ 2) :=
    (χ.continuous.mul (hf.continuous.norm.pow 2)).integrable_of_hasCompactSupport
      χ.hasCompactSupport.mul_right
  have hY : 0 ≤ ∫ x : Space, χ x * ‖f x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg χ.nonneg (sq_nonneg _)
  have hφY : (∫ x : Space, ‖φ x‖ ^ 2) ≤ ∫ x : Space, χ x * ‖f x‖ ^ 2 := by
    apply integral_mono (SchwartzParseval.integrable_norm_sq φ) hYi
    intro x
    change ‖χ x • f x‖ ^ 2 ≤ χ x * ‖f x‖ ^ 2
    rw [norm_smul, Real.norm_of_nonneg χ.nonneg, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have h0 := χ.nonneg (x := x)
    have h1 := χ.le_one (x := x)
    nlinarith
  have hpair_eq : (∫ x : Space, f x * conj (φ x)) =
      ((∫ x : Space, χ x * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    calc
      _ = ∫ x : Space, ((χ x * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        change f x * conj (χ x • f x) = ((χ x * ‖f x‖ ^ 2 : ℝ) : ℂ)
        calc
          _ = (χ x : ℂ) * (f x * conj (f x)) := by
            rw [Algebra.smul_def]
            change f x * conj ((χ x : ℂ) * f x) = _
            rw [map_mul, Complex.conj_ofReal]
            ring
          _ = _ := by simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = _ := by simp only [integral_complex_ofReal]
  have hbound : (∫ x : Space, χ x * ‖f x‖ ^ 2) ≤
      Real.sqrt C * Real.sqrt (∫ x : Space, χ x * ‖f x‖ ^ 2) := by
    have hp := hpair φ
    rw [hpair_eq, Complex.norm_real, Real.norm_of_nonneg hY] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hφY)
      (Real.sqrt_nonneg C))
  linarith [sq_nonneg (Real.sqrt C - Real.sqrt (∫ x : Space, χ x * ‖f x‖ ^ 2)),
    Real.sq_sqrt hC, Real.sq_sqrt hY]

/-- A smooth function satisfying the `L²` dual estimate on Schwartz tests is square
integrable with the corresponding bound. -/
theorem memLp_two_and_integral_le_of_pairing_bound {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ φ : ComplexTest,
      ‖∫ x : Space, f x * conj (φ x)‖ ≤
        Real.sqrt C * Real.sqrt (∫ x : Space, ‖φ x‖ ^ 2)) :
    MemLp f 2 volume ∧ (∫ x : Space, ‖f x‖ ^ 2) ≤ C := by
  have hcont (n : ℕ) : Continuous (fun x : Space => l2Cutoff n x * ‖f x‖ ^ 2) :=
    (l2Cutoff n).continuous.mul (hf.continuous.norm.pow 2)
  have hint (n : ℕ) : Integrable (fun x : Space => l2Cutoff n x * ‖f x‖ ^ 2) :=
    (hcont n).integrable_of_hasCompactSupport (l2Cutoff n).hasCompactSupport.mul_right
  have hlin_bound (n : ℕ) :
      (∫⁻ x : Space, ENNReal.ofReal (l2Cutoff n x * ‖f x‖ ^ 2)) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
      (Eventually.of_forall fun x => mul_nonneg (l2Cutoff n).nonneg (sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (cutoff_energy_le_of_pairing_bound hf hC hpair (l2Cutoff n))
  have hlim (x : Space) : Tendsto
      (fun n : ℕ => ENNReal.ofReal (l2Cutoff n x * ‖f x‖ ^ 2))
      atTop (𝓝 (ENNReal.ofReal (‖f x‖ ^ 2))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [l2Cutoff_eventually_one x] with n hn
    simp only [hn, one_mul]
  have hlin : (∫⁻ x : Space, ENNReal.ofReal (‖f x‖ ^ 2)) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x : Space, atTop.liminf
          (fun n : ℕ => ENNReal.ofReal (l2Cutoff n x * ‖f x‖ ^ 2)) := by
        exact lintegral_congr fun x => (hlim x).liminf_eq.symm
      _ ≤ atTop.liminf (fun n : ℕ =>
          ∫⁻ x : Space, ENNReal.ofReal (l2Cutoff n x * ‖f x‖ ^ 2)) :=
        lintegral_liminf_le fun n => (ENNReal.continuous_ofReal.comp (hcont n)).measurable
      _ ≤ ENNReal.ofReal C :=
        liminf_le_of_frequently_le' (Frequently.of_forall hlin_bound)
  have hsq : Integrable (fun x : Space => ‖f x‖ ^ 2) := by
    refine ⟨(hf.continuous.norm.pow 2).aestronglyMeasurable, ?_⟩
    change (∫⁻ x : Space, ‖(‖f x‖ ^ 2 : ℝ)‖ₑ) < (⊤ : ℝ≥0∞)
    simpa only [← ofReal_norm, norm_pow, norm_norm] using
      hlin.trans_lt (ENNReal.ofReal_lt_top : ENNReal.ofReal C < (⊤ : ℝ≥0∞))
  refine ⟨(memLp_two_iff_integrable_sq_norm hf.continuous.aestronglyMeasurable).mpr hsq, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg ‖f x‖)
    hsq.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin).trans_eq (ENNReal.toReal_ofReal hC)

/-- The Riesz test operator is an `L²` contraction, including square integrability. -/
theorem rieszTest_memLp_and_l2_bound (i j : Fin 3) (ψ : ComplexTest) :
    MemLp (rieszTest i j ψ) 2 volume ∧
      (∫ x : Space, ‖rieszTest i j ψ x‖ ^ 2) ≤ ∫ x : Space, ‖ψ x‖ ^ 2 :=
  memLp_two_and_integral_le_of_pairing_bound (contDiff_rieszTest i j ψ)
    (integral_nonneg fun x => sq_nonneg ‖ψ x‖) (norm_rieszTest_pairing_le i j ψ)

theorem memLp_rieszTest (i j : Fin 3) (ψ : ComplexTest) :
    MemLp (rieszTest i j ψ) 2 volume :=
  (rieszTest_memLp_and_l2_bound i j ψ).1

theorem integral_norm_sq_rieszTest_le (i j : Fin 3) (ψ : ComplexTest) :
    (∫ x : Space, ‖rieszTest i j ψ x‖ ^ 2) ≤ ∫ x : Space, ‖ψ x‖ ^ 2 :=
  (rieszTest_memLp_and_l2_bound i j ψ).2

end NavierStokesR3.RieszTestOperators

end
end

end

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff FourierTransform RealInnerProductSpace BigOperators ENNReal

namespace NavierStokesR3.RieszTestOperators

open ProblemStatement Comparison
open HarmonicTestFunctionals

/-- A coordinate derivative, retained as a Schwartz function. -/
abbrev partialTest (k : Fin 3) (ψ : ComplexTest) : ComplexTest :=
  LineDeriv.lineDerivOpCLM ℂ ComplexTest (NavierStokes.ProblemStatement.coordinateVector k) ψ

theorem partialTest_apply (k : Fin 3) (ψ : ComplexTest) (x : Space) :
    partialTest k ψ x = Comparison.partialD k (fun y => ψ y) x := rfl

/-- The Fourier transform of a directional derivative of a Schwartz function. -/
theorem fourier_pderivTest (ψ : ComplexTest) (d ξ : Space) :
    (EulerSobolev.schwartzFourier
      (LineDeriv.lineDerivOpCLM ℂ ComplexTest d ψ)) ξ =
      (2 * Real.pi * Complex.I) * (⟪ξ, d⟫ : ℂ) *
        (EulerSobolev.schwartzFourier ψ) ξ := by
  change (FourierTransform.fourierCLE ℂ ComplexTest
      (LineDeriv.lineDerivOpCLM ℂ ComplexTest d ψ)) ξ =
      (2 * Real.pi * Complex.I) * (⟪ξ, d⟫ : ℂ) *
        (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ
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
    (EulerSobolev.schwartzFourier (partialTest k ψ)) ξ =
      (2 * Real.pi * Complex.I) * (ξ k : ℂ) *
        (EulerSobolev.schwartzFourier ψ) ξ := by
  simpa only [partialTest, NavierStokes.ProblemStatement.coordinateVector,
    EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] using
    fourier_pderivTest ψ (NavierStokes.ProblemStatement.coordinateVector k) ξ

/-- An integrable first Fourier moment permits differentiation of the inverse
Fourier integral in every direction. -/
theorem fderiv_fourierInv_apply {f : Space → ℂ} (hf : Integrable f)
    (hf1 : Integrable (fun ξ : Space => ‖ξ‖ * ‖f ξ‖)) (x d : Space) :
    fderiv ℝ (𝓕⁻ (f : Space → ℂ)) x d =
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
      (rieszSymbol i j ξ : ℂ) * (EulerSobolev.schwartzFourier ψ) ξ)) x d = _
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
  have hpartial (i : Fin 3) (ψ : ComplexTest) (ξ : Space) :
      FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i ψ) ξ =
        (2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) *
          FourierTransform.fourierCLE ℂ ComplexTest ψ ξ := fourier_partialCLM_apply i ψ ξ
  have hlap (ψ : ComplexTest) (ξ : Space) :
      FourierTransform.fourierCLE ℂ ComplexTest (laplacianCLM ψ) ξ =
        (-(4 * (Real.pi : ℂ) ^ 2) * ((‖ξ‖ ^ 2 : ℝ) : ℂ)) *
          FourierTransform.fourierCLE ℂ ComplexTest ψ ξ := fourier_laplacianCLM_apply ψ ξ
  have hmult (ξ : Space) :
      (rieszSymbol i j ξ : ℂ) *
          (FourierTransform.fourierCLE ℂ ComplexTest (laplacianCLM ψ)) ξ =
        (FourierTransform.fourierCLE ℂ ComplexTest (-(partialCLM i (partialCLM j ψ)))) ξ := by
    rw [map_neg]
    change (rieszSymbol i j ξ : ℂ) *
        (FourierTransform.fourierCLE ℂ ComplexTest (laplacianCLM ψ)) ξ =
      -((FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i (partialCLM j ψ))) ξ)
    rw [hlap, hpartial, hpartial]
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
  rw [show EulerSobolev.schwartzFourier (V := Space) (E := ℂ) =
      (FourierTransform.fourierCLE ℂ ComplexTest : ComplexTest → ComplexTest) from rfl]
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
