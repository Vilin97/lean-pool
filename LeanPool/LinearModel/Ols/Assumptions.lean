/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import LeanPool.LinearModel.Ols.Gram
import LeanPool.LinearModel.Ols.Leverage
import LeanPool.LinearModel.Ols.ProjectionCLT

/-!
# The assumption bundle and the OLS projection CLT

The hypothesis structure shared across the OLS development: `AssumptionBundle`
collects all conditions on a triangular array of designs `X` and responses `y` —
the stochastic conditions on `y` (measurability, row-wise independence, uniformly
bounded fourth central moments, lower bound on variance) and the deterministic conditions
on `X` (two-sided eigenvalue bound for `n > 0`, vanishing max leverage) and on
the interaction (bounded mean residuals).

After deriving several consequences of the assumption bundle holding, we establish
that this bundle is sufficient for the Lindeberg condition to hold for the OLS array defined
in `ProjectionCLT.lean`, and consequently for the projection CLT to hold.

The main results are the following:

· `AssumptionBundle.olsArray_LindebergCondition` - under the assumption bundle the
  Lindeberg condition holds for the OLS array.
· `AssumptionBundle.central_limit_charFun_OLS_projection'` - under the assumption bundle
  the characteristic function of `aᵀ(β̂ₙ − β*ₙ) / sₙ` converges pointwise to `exp(-t²/2)`.
· `AssumptionBundle.central_limit_OLS_projection'` - under the assumption bundle
  `aᵀ(β̂ₙ − β*ₙ) / sₙ` converges in distribution to `N(0,1)`

-/

open MeasureTheory ProbabilityTheory Matrix Finset BigOperators Filter
open scoped Topology ENNReal

namespace LeanPool.LinearModel

noncomputable section

variable {n p : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ} {y : (n : ℕ) → Fin n → Ω → ℝ}

section Definitions

/-- The mean residual `r = E[y] − Xβ*`, where `β* = olsEstimand P X y`. -/
def meanResidual (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → Ω → ℝ) : Fin n → ℝ :=
  meanVec y P - X *ᵥ (olsEstimand P X y)

/-- The set of assumptions that we make in order for the CLT to be valid. -/
structure AssumptionBundle (P : Measure Ω) (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
    (y : (n : ℕ) → Fin n → Ω → ℝ) where
  /-- Uniform positive lower bound on the response variances. -/
  α : ℝ
  /-- Uniform square-root upper bound on the fourth central moments. -/
  β : ℝ
  /-- Uniform positive spectral lower bound for the sample Gram matrices. -/
  c : ℝ
  /-- Uniform positive spectral upper bound for the sample Gram matrices. -/
  C : ℝ
  /-- Uniform upper bound on the absolute mean residuals. -/
  Cᵣ : ℝ
  hy_meas : ∀ n i, Measurable (y n i)
  hy_indep : ∀ n, iIndepFun (y n) P
  hy_MemL4 : ∀ n i, MemLp (fun ω => y n i ω - P[y n i]) 4 P
  hy4_ub : ∀ n i, centralMoment (y n i) 4 P ≤ β ^ 2
  hβ_nonneg : 0 ≤ β
  hvar_pos : 0 < α
  hvar_lb : ∀ n i, α ≤ centralMoment (y n i) 2 P
  hc_pos : 0 < c
  hC_pos : 0 < C
  hGram_spectral_lb : ∀ n, 0 < n → isSpectralLb (sampleGram (X n)) c
  hGram_spectral_ub : ∀ n, 0 < n → isSpectralUb (sampleGram (X n)) C
  hlev : Tendsto (fun n => maxLev (X n)) atTop (𝓝 0)
  hres_ub : ∀ n i, |meanResidual P (X n) (y n) i| ≤ Cᵣ

end Definitions


section BundleConsequences

/-- `0 ≤ Cᵣ`, read off from the residual bound at `n = 1`. -/
lemma AssumptionBundle.hCr_nonneg (A1 : AssumptionBundle P X y) : 0 ≤ A1.Cᵣ :=
  le_trans (abs_nonneg _) (A1.hres_ub 1 ⟨0, Nat.one_pos⟩)

/-- Measurability of the centred response `εₙ,ᵢ = yₙ,ᵢ − E[yₙ,ᵢ]`. -/
lemma AssumptionBundle.hε_meas (A1 : AssumptionBundle P X y) (n : ℕ) (i : Fin n) :
    Measurable (fun ω => y n i ω - P[y n i]) :=
  (A1.hy_meas n i).sub measurable_const

/-- Integrability of the fourth central power, recovered from the `L⁴` field. -/
lemma AssumptionBundle.hy4_int (A1 : AssumptionBundle P X y) (n : ℕ) (i : Fin n) :
    Integrable (centralPower (y n i) 4 P) P := by
  have h := (A1.hy_MemL4 n i).integrable_norm_rpow (by simp) ENNReal.ofNat_ne_top
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs]
  exact Even.pow_abs ⟨2, rfl⟩ _

/-- Square-integrability of the centered responses. -/
lemma AssumptionBundle.hy2_int [IsProbabilityMeasure P]
    (A1 : AssumptionBundle P X y) (n : ℕ) (i : Fin n) :
    Integrable (centralPower (y n i) 2 P) P :=
  ((A1.hy_MemL4 n i).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_sq

/-- The responses themselves are in `L²`: shift the centered `L⁴` bound by the mean. -/
lemma AssumptionBundle.hy2_memLp [IsProbabilityMeasure P]
    (A1 : AssumptionBundle P X y) (n : ℕ) (i : Fin n) :
    MemLp (y n i) 2 P := by
  have h := ((A1.hy_MemL4 n i).mono_exponent
    (by norm_num : (2 : ℝ≥0∞) ≤ 4)).add (memLp_const (P[y n i]))
  simpa [Pi.add_def] using h

/-- `Var(y_{n,i}) ≤ β` for all `n` and `i`: nonnegativity of the variance of `ε²`
gives `s² ≤ E[ε⁴] ≤ β²`. -/
lemma AssumptionBundle.hvar_ub [IsProbabilityMeasure P]
    (A1 : AssumptionBundle P X y) :
    ∀ n i, centralMoment (y n i) 2 P ≤ A1.β := by
  intro n i
  set s := centralMoment (y n i) 2 P with hs_def
  have hg2 : MemLp (centralPower (y n i) 2 P) 2 P :=
    (memLp_two_iff_integrable_sq
        ((A1.hε_meas n i).pow_const 2).aestronglyMeasurable).mpr <|
      (A1.hy4_int n i).congr (ae_of_all _ fun ω => by
        simp only [centralPower]
        ring)
  have hsq_eq : centralPower (y n i) 2 P ^ 2 = centralPower (y n i) 4 P := by
    funext ω
    simp only [Pi.pow_apply, centralPower]
    ring
  have h := variance_nonneg (centralPower (y n i) 2 P) P
  rw [variance_eq_sub hg2, hsq_eq, ← centralMoment_eq_integral_centralPower,
    ← centralMoment_eq_integral_centralPower, ← hs_def] at h
  have hs_sq : s ^ 2 ≤ A1.β ^ 2 := by linarith [A1.hy4_ub n i]
  have hs_nonneg : 0 ≤ s := integral_nonneg fun _ => sq_nonneg _
  calc s = Real.sqrt (s ^ 2) := (Real.sqrt_sq hs_nonneg).symm
    _ ≤ Real.sqrt (A1.β ^ 2) := Real.sqrt_le_sqrt hs_sq
    _ = A1.β := Real.sqrt_sq A1.hβ_nonneg

/-- The Gram matrix `XₙᵀXₙ` is invertible for `n > 0`. -/
lemma AssumptionBundle.isUnit_gram_det (A1 : AssumptionBundle P X y)
    (hn : 0 < n) : IsUnit ((X n)ᵀ * X n).det := by
  have hS : IsUnit (sampleGram (X n)).det :=
    inv_of_pos_spectral_lb _ A1.c A1.hc_pos (A1.hGram_spectral_lb n hn)
  rw [sampleGram, Matrix.det_smul] at hS
  rw [isUnit_iff_ne_zero]
  exact right_ne_zero_of_mul (isUnit_iff_ne_zero.mp hS)

/-- A lower bound for the sum of second moments of the OLS array: `α · ∑ₖ wₖ² ≤ sₙ²`. -/
lemma AssumptionBundle.olsArray_momentSum_ge (A1 : AssumptionBundle P X y)
    (a : Fin p → ℝ) (n : ℕ) :
    A1.α * normSq (olsWeights (X n) a)
      ≤ momentSumTriangular (olsArray P X y a) P n := by
  simp only [normSq, dotProduct, ← pow_two]
  rw [momentSum_olsArray_eq X y a, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  calc A1.α * olsWeights (X n) a k ^ 2
      = olsWeights (X n) a k ^ 2 * A1.α := by ring
    _ ≤ olsWeights (X n) a k ^ 2 * centralMoment (y n k) 2 P :=
        mul_le_mul_of_nonneg_left (A1.hvar_lb n k) (sq_nonneg _)

/-- The sum of second moments of the OLS array is eventually positive. -/
lemma AssumptionBundle.olsArray_momentSum_eventually_pos
    (A1 : AssumptionBundle P X y) (a : Fin p → ℝ) (ha_nz : 0 ≠ a) :
    ∀ᶠ n in atTop, 0 < momentSumTriangular (olsArray P X y a) P n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hQ : 0 < normSq (olsWeights (X n) a) :=
    normSq_olsWeights_pos (X n) (A1.isUnit_gram_det hn) a ha_nz
  calc (0 : ℝ) < A1.α * normSq (olsWeights (X n) a) :=
        mul_pos A1.hvar_pos hQ
    _ ≤ momentSumTriangular (olsArray P X y a) P n := A1.olsArray_momentSum_ge a n

end BundleConsequences


section MainResults

open Complex

/-- The OLS array satisfies the Lindeberg condition if the assumption bundle holds,
`P` is a probability measure and the projection direction `a` is nonzero. -/
theorem AssumptionBundle.olsArray_LindebergCondition (A1 : AssumptionBundle P X y)
    [IsProbabilityMeasure P] (a : Fin p → ℝ) (ha_nz : 0 ≠ a) :
    LindebergConditionTriangular (olsArray P X y a) P := by
  intro ε hε
  classical
  set Z : (n : ℕ) → Fin n → Ω → ℝ := olsArray P X y a with hZ_def
  set W : (n : ℕ) → Fin n → ℝ := fun n => olsWeights (X n) a with hW_def
  set Q : ℕ → ℝ := fun n => normSq (W n) with hQ_def
  set s : ℕ → ℝ := fun n => momentSumTriangular Z P n with hs_def
  set Cbd : ℝ := A1.β ^ 2 / (ε ^ 2 * A1.α ^ 2) with hCbd_def
  -- basic integrability of the centred responses
  have hZ_meas : ∀ n (k : Fin n), Measurable (Z n k) := fun n k =>
    (A1.hε_meas n k).const_mul _
  have hZ4_eq : ∀ n (k : Fin n), (fun ω => Z n k ω ^ 4)
      = fun ω => W n k ^ 4 * (centralPower (y n k) 4 P) ω := by
    intro n k
    funext ω
    simp only [hZ_def, olsArray, hW_def, centralPower]
    ring
  have hZ4_int : ∀ n (k : Fin n), Integrable (fun ω => Z n k ω ^ 4) P := by
    intro n k
    rw [hZ4_eq n k]
    exact (A1.hy4_int n k).const_mul _
  have hZ2_int : ∀ n (k : Fin n), Integrable (fun ω => Z n k ω ^ 2) P :=
    fun n k =>
      (((A1.hy_MemL4 n k).const_mul (W n k)).mono_exponent
        (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_sq
  have hZ4_bd : ∀ n (k : Fin n),
      ∫ ω, Z n k ω ^ 4 ∂P ≤ A1.β ^ 2 * W n k ^ 4 := by
    intro n k
    rw [hZ4_eq n k, integral_const_mul, ← centralMoment_eq_integral_centralPower]
    calc W n k ^ 4 * centralMoment (y n k) 4 P
        ≤ W n k ^ 4 * A1.β ^ 2 := by
          gcongr
          exact A1.hy4_ub n k
      _ = A1.β ^ 2 * W n k ^ 4 := by ring
  -- non-negativity of the Lindeberg functional
  have hL_nonneg : ∀ n, 0 ≤ (1 / s n)
      * ∑ k, ∫ ω in LindebergSetTriangular Z P k ε, Z n k ω ^ 2 ∂P := by
    intro n
    refine mul_nonneg ?_ ?_
    · exact one_div_nonneg.mpr
        (Finset.sum_nonneg fun k _ => integral_nonneg fun ω => sq_nonneg _)
    · exact Finset.sum_nonneg fun k _ =>
        integral_nonneg fun ω => sq_nonneg _
  -- the eventual per-`n` upper bound; `Q n > 0` once `n ≥ 1` since `a ≠ 0`
  have hL_le : ∀ᶠ n in atTop, (1 / s n)
      * (∑ k, ∫ ω in LindebergSetTriangular Z P k ε, Z n k ω ^ 2 ∂P)
      ≤ Cbd * maxLev (X n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hQ_pos : 0 < Q n :=
      normSq_olsWeights_pos (X n) (A1.isUnit_gram_det hn) a ha_nz
    have hlev_nn : 0 ≤ maxLev (X n) := maxLev_nonneg (X n)
    have hs_lb : A1.α * Q n ≤ s n := A1.olsArray_momentSum_ge a n
    have hs_pos : 0 < s n :=
      lt_of_lt_of_le (mul_pos A1.hvar_pos hQ_pos) hs_lb
    have hεs : 0 < ε ^ 2 * s n := by positivity
    -- per-`k` truncation bound
    have hterm : ∀ k : Fin n,
        ∫ ω in LindebergSetTriangular Z P k ε, Z n k ω ^ 2 ∂P
          ≤ A1.β ^ 2 * W n k ^ 4 / (ε ^ 2 * s n) := by
      intro k
      have hpt : ∀ ω ∈ LindebergSetTriangular Z P k ε,
          Z n k ω ^ 2 ≤ Z n k ω ^ 4 / (ε ^ 2 * s n) := by
        intro ω hω
        have hmem : ε * Real.sqrt (s n) < |Z n k ω| := hω
        have hsq : ε ^ 2 * s n < Z n k ω ^ 2 := by
          have h0 : 0 ≤ ε * Real.sqrt (s n) :=
            mul_nonneg hε.le (Real.sqrt_nonneg _)
          have h1 : (ε * Real.sqrt (s n)) ^ 2 < |Z n k ω| ^ 2 :=
            pow_lt_pow_left₀ hmem h0 two_ne_zero
          rwa [mul_pow, Real.sq_sqrt hs_pos.le, sq_abs] at h1
        rw [le_div_iff₀ hεs]
        nlinarith [sq_nonneg (Z n k ω), hsq]
      have hmeas_set : MeasurableSet (LindebergSetTriangular Z P k ε) :=
        measurableSet_lt measurable_const (hZ_meas n k).abs
      calc ∫ ω in LindebergSetTriangular Z P k ε, Z n k ω ^ 2 ∂P
          ≤ ∫ ω in LindebergSetTriangular Z P k ε, Z n k ω ^ 4 / (ε ^ 2 * s n) ∂P :=
            setIntegral_mono_on (hZ2_int n k).integrableOn
              ((hZ4_int n k).div_const _).integrableOn hmeas_set hpt
        _ ≤ ∫ ω, Z n k ω ^ 4 / (ε ^ 2 * s n) ∂P :=
            setIntegral_le_integral ((hZ4_int n k).div_const _)
              (ae_of_all _ fun ω => by positivity)
        _ = (∫ ω, Z n k ω ^ 4 ∂P) / (ε ^ 2 * s n) := integral_div _ _
        _ ≤ A1.β ^ 2 * W n k ^ 4 / (ε ^ 2 * s n) :=
            div_le_div_of_nonneg_right (hZ4_bd n k) hεs.le
    -- the weight fourth-power bound `∑ₖ wₖ⁴ ≤ maxLev · Q²`
    have hW4 : ∑ k, W n k ^ 4 ≤ maxLev (X n) * Q n ^ 2 := by
      have hterm4 : ∀ k : Fin n,
          W n k ^ 4 ≤ (maxLev (X n) * Q n) * W n k ^ 2 := by
        intro k
        have h1 : W n k ^ 2 ≤ leverage (X n) k * Q n :=
          olsWeights_sq_le_leverage (X n) a (A1.isUnit_gram_det k.pos) k
        calc W n k ^ 4 = W n k ^ 2 * W n k ^ 2 := by ring
          _ ≤ (leverage (X n) k * Q n) * W n k ^ 2 := by gcongr
          _ ≤ (maxLev (X n) * Q n) * W n k ^ 2 := by
              gcongr
              exact leverage_le_maxLev (X n) k
      calc ∑ k, W n k ^ 4
          ≤ ∑ k, (maxLev (X n) * Q n) * W n k ^ 2 :=
            Finset.sum_le_sum fun k _ => hterm4 k
        _ = (maxLev (X n) * Q n) * Q n := by
            rw [← Finset.mul_sum, ← normSq_eq_sum_sq]
        _ = maxLev (X n) * Q n ^ 2 := by ring
    -- assemble
    have hsum_le : ∑ k, ∫ ω in LindebergSetTriangular Z P k ε, Z n k ω ^ 2 ∂P
        ≤ A1.β ^ 2 * (maxLev (X n) * Q n ^ 2) / (ε ^ 2 * s n) := by
      calc ∑ k, ∫ ω in LindebergSetTriangular Z P k ε, Z n k ω ^ 2 ∂P
          ≤ ∑ k, A1.β ^ 2 * W n k ^ 4 / (ε ^ 2 * s n) :=
            Finset.sum_le_sum fun k _ => hterm k
        _ = A1.β ^ 2 * (∑ k, W n k ^ 4) / (ε ^ 2 * s n) := by
            rw [← Finset.sum_div, ← Finset.mul_sum]
        _ ≤ A1.β ^ 2 * (maxLev (X n) * Q n ^ 2) / (ε ^ 2 * s n) := by gcongr
    have hs_sq : A1.α ^ 2 * Q n ^ 2 ≤ s n ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (mul_pos A1.hvar_pos hQ_pos).le hs_lb 2
    calc (1 / s n) * ∑ k, ∫ ω in LindebergSetTriangular Z P k ε, Z n k ω ^ 2 ∂P
        ≤ (1 / s n) * (A1.β ^ 2 * (maxLev (X n) * Q n ^ 2) / (ε ^ 2 * s n)) :=
          mul_le_mul_of_nonneg_left hsum_le (one_div_nonneg.mpr hs_pos.le)
      _ = (A1.β ^ 2 * maxLev (X n) / ε ^ 2) * (Q n ^ 2 / s n ^ 2) := by
          field_simp
      _ ≤ (A1.β ^ 2 * maxLev (X n) / ε ^ 2) * (1 / A1.α ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · rw [div_le_div_iff₀ (pow_pos hs_pos 2) (pow_pos A1.hvar_pos 2)]
            nlinarith [hs_sq]
          · exact div_nonneg (mul_nonneg (sq_nonneg _) hlev_nn) (sq_nonneg _)
      _ = Cbd * maxLev (X n) := by
          rw [hCbd_def]
          field_simp
  -- squeeze against `Cbd · maxLev → 0`
  have hlim : Tendsto (fun n => Cbd * maxLev (X n)) atTop (𝓝 0) := by
    simpa using A1.hlev.const_mul Cbd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall hL_nonneg) hL_le

/-- The OLS projection CLT (characteristic function version) under the assumption bundle. -/
theorem AssumptionBundle.central_limit_charFun_OLS_projection'
    [IsProbabilityMeasure P] (A1 : AssumptionBundle P X y)
    (a : Fin p → ℝ) (ha_nz : 0 ≠ a) (t : ℝ) :
    Tendsto (fun n ↦ charFun (P.map (LindebergSumTriangular (olsArray P X y a) P n)) t) atTop
      (𝓝 (cexp (-(t ^ 2 / 2)))) :=
  central_limit_charFun_OLS_projection X y a A1.hy_meas A1.hy_indep
    A1.hy2_memLp
    (A1.olsArray_LindebergCondition a ha_nz)
    (A1.olsArray_momentSum_eventually_pos a ha_nz) t

/-- The OLS projection CLT (convergence in distribution version) under the assumption bundle. -/
theorem AssumptionBundle.central_limit_OLS_projection' {P : ProbabilityMeasure Ω}
    (A1 : AssumptionBundle P X y)
    (a : Fin p → ℝ) (ha_nz : 0 ≠ a) :
    Tendsto (fun n : ℕ => P.map (aemeasurable_olsArray X y a A1.hy_meas n))
      atTop (𝓝 stdGaussian) :=
  central_limit_OLS_projection X y a A1.hy_meas A1.hy_indep
    A1.hy2_memLp
    (A1.olsArray_LindebergCondition a ha_nz)
    (A1.olsArray_momentSum_eventually_pos a ha_nz)


end MainResults

end
end LinearModel
end LeanPool
