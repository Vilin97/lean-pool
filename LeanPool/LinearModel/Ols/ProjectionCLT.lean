/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import LeanPool.LinearModel.Clt.LindebergCLT
import LeanPool.LinearModel.Ols.Optimality

/-!
# OLS projection CLT (fixed design, heteroscedastic)

This file establishes that for a sequence of `(n × p)` matrices `Xₙ` and vectors `yₙ ∈ ℝⁿ`, the
normalised scalar projection `aᵀ(β̂ₙ − β*ₙ) / sₙ` for any fixed `a ∈ ℝᵖ` converges in distribution
to `N(0,1)`, where `β̂ₙ = (XₙᵀXₙ)⁻¹Xₙᵀyₙ` and `β*ₙ = (XₙᵀXₙ)⁻¹XₙᵀE[yₙ]` are the OLS estimator and
estimand respectively, and `sₙ² = ∑ₖ w_{n,k}² Var(yₖ)`, with `w_{n,k} = [Xₙ(XₙᵀXₙ)⁻¹a]ₖ`.

The only assumption we make outside of integrability and measurability of the functions
concerned is that the sum `sₙ²` described above is eventually non-zero.

The main results are the following:

· `central_limit_charFun_OLS_projection` - if the Lindeberg condition holds for the OLS
  array then the characteristic function of `aᵀ(β̂ₙ − β*ₙ) / sₙ` converges pointwise
  to `exp(-t²/2)`.
· `central_limit_OLS_projection` - if the Lindeberg condition holds for the OLS array
  then `aᵀ(β̂ₙ − β*ₙ) / sₙ` converges in distribution to `N(0,1)`

-/

open MeasureTheory ProbabilityTheory Matrix Finset BigOperators Filter
open scoped Topology

namespace LeanPool.LinearModel

noncomputable section



variable {n p : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} [IsProbabilityMeasure P]

section Definitions

/-- The `p`-th power of the centred random variable, `ω ↦ (f(ω) − E[f])^p`:
the integrand of `centralMoment f p P`. -/
def centralPower {Ω : Type*} {mΩ : MeasurableSpace Ω} (f : Ω → ℝ) (p : ℕ)
    (P : Measure Ω) : Ω → ℝ :=
  fun ω => (f ω - P[f]) ^ p

lemma centralMoment_eq_integral_centralPower {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (f : Ω → ℝ) (p : ℕ) (P : Measure Ω) :
    centralMoment f p P = P[centralPower f p P] := rfl

/-- The vector of pointwise means `E[yᵢ]` of a family of random variables
`y : ι → Ω → ℝ`. Works at any index type: `Fin n` for a fixed design, `ℕ` for a
triangular array. -/
def meanVec {ι : Type*} (y : ι → Ω → ℝ) (P : Measure Ω) : ι → ℝ :=
  fun i => P[y i]

/-- The estimand `β*ₙ = (XₙᵀXₙ)⁻¹ Xₙᵀ E[yₙ]`. -/
def olsEstimand (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → Ω → ℝ) : Fin p → ℝ :=
  olsEstimator X (meanVec y P)

/-- OLS weights for a linear functional `a`: `w_{n,i} = [Xₙ(XₙᵀXₙ)⁻¹a]ᵢ`. -/
def olsWeights (X : Matrix (Fin n) (Fin p) ℝ) (a : Fin p → ℝ) : Fin n → ℝ :=
  fun i => (X *ᵥ ((Xᵀ * X)⁻¹ *ᵥ a)) i

/-- The OLS triangular array: `Z_{n,i}(ω) = w_{n,i} · (yᵢ(ω) − E[Yᵢ])`. -/
def olsArray (P : Measure Ω) (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
    (y : (n : ℕ) → (Fin n) → Ω → ℝ)
  (a : Fin p → ℝ) : (n : ℕ) → Fin n → Ω → ℝ :=
  fun n i ω => olsWeights (X n) a i * ((y n) i ω - P[(y n) i])

end Definitions


section olsArrayProperties

omit [IsProbabilityMeasure P] in
/-- The OLS array is measurable. -/
lemma olsArray_measurable (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
  (y : (n : ℕ) → (Fin n) → Ω → ℝ) (a : Fin p → ℝ)
  (hy_meas : ∀ n i, Measurable (y n i)) :
    ∀ n k, Measurable ((olsArray P X y a) n k) := by
  intro n k
  exact (measurable_const.mul ((hy_meas n k).sub measurable_const))

/-- The OLS array has mean zero. -/
lemma olsArray_mean_zero (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
  (y : (n : ℕ) → (Fin n) → Ω → ℝ) (a : Fin p → ℝ)
  (hy_int : ∀ n i, MemLp (y n i) 1 P) :
    ∀ n k, ∫ ω, (olsArray P X y a) n k ω ∂P = 0 := by
  intro n k
  simp only [olsArray, olsWeights]
  rw [integral_const_mul]
  have h_zero: ∫ ω, (y n k ω - P[y n k]) ∂P = 0 := by
    rw [integral_sub ((hy_int n k).integrable le_rfl) (integrable_const _)]
    simp
  rw [h_zero, mul_zero]

/-- The OLS array is square-integrable. -/
lemma olsArray_memLp_two (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
  (y : (n : ℕ) → (Fin n) → Ω → ℝ) (a : Fin p → ℝ)
  (hy2 : ∀ n i, MemLp (y n i) 2 P) :
    ∀ n k, MemLp ((olsArray P X y a) n k) 2 P := by
  intro n k
  have h : MemLp (fun ω => y n k ω - P[y n k]) 2 P := by
    have h' := (hy2 n k).sub (memLp_const (P[y n k]))
    simpa [Pi.sub_def] using h'
  exact h.const_mul _

omit [IsProbabilityMeasure P] in
/-- Row-wise independence: for each n, `{olsArray n k}ₖ` are independent. -/
lemma olsArray_row_indep
  (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
  (y : (n : ℕ) → (Fin n) → Ω → ℝ) (a : Fin p → ℝ)
  (hy_indep : ∀ n, iIndepFun (y n) P) :
    ∀ n, iIndepFun ((olsArray P X y a) n) P := by
  intro n
  -- The rows `y n` are already an independent family; compose with the deterministic
  -- affine maps `z ↦ w_{n,k} · (z − E[y n k])`.
  have hg : ∀ k : Fin n,
      Measurable (fun z : ℝ ↦ olsWeights (X n) a k * (z - P[y n k])) :=
    fun _ ↦ measurable_const.mul (measurable_id.sub measurable_const)
  exact (hy_indep n).comp (fun k z ↦ olsWeights (X n) a k * (z - P[y n k])) hg

omit [IsProbabilityMeasure P] in
/-- AE-measurability of the OLS Lindeberg sum `Sₙ/sₙ`. -/
lemma aemeasurable_olsArray (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
    (y : (n : ℕ) → (Fin n) → Ω → ℝ) (a : Fin p → ℝ)
    (hy_meas : ∀ n i, Measurable (y n i)) (n : ℕ) :
    AEMeasurable (LindebergSumTriangular (olsArray P X y a) P n) P :=
  aemeasurable_LindebergSumTriangular n (olsArray_measurable X y a hy_meas)

/-- `Xᵀw = a` for the OLS weight vector `w = X(XᵀX)⁻¹a`. -/
lemma transpose_mulVec_olsWeights (X : Matrix (Fin n) (Fin p) ℝ)
    (hX_inv : IsUnit (Xᵀ * X).det) (a : Fin p → ℝ) :
    Xᵀ *ᵥ (olsWeights X a) = a := by
  change Xᵀ *ᵥ (X *ᵥ ((Xᵀ * X)⁻¹ *ᵥ a)) = a
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hX_inv, Matrix.one_mulVec]

/-- Nondegeneracy of the OLS weights: for `a ≠ 0`, `‖w‖² > 0`. -/
lemma normSq_olsWeights_pos (X : Matrix (Fin n) (Fin p) ℝ)
    (hX_inv : IsUnit (Xᵀ * X).det) (a : Fin p → ℝ) (ha_nz : 0 ≠ a) :
    0 < normSq (olsWeights X a) := by
  have hX_ne : olsWeights X a ≠ 0 := by
    intro h0
    have h := transpose_mulVec_olsWeights X hX_inv a
    rw [h0, Matrix.mulVec_zero] at h
    exact ha_nz h
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hX_ne
  simp only [Pi.zero_apply] at hk
  simp only [normSq, dotProduct, ← pow_two]
  refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨k, Finset.mem_univ k, ?_⟩
  exact (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hk))

omit [IsProbabilityMeasure P] in
/-- The OLS array variance sum factorises: `sₙ² = ∑ₖ wₖ² σₖ²`. -/
lemma momentSum_olsArray_eq (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
  (y : (n : ℕ) → (Fin n) → Ω → ℝ) (a : Fin p → ℝ) :
    momentSumTriangular (olsArray P X y a) P n
      = ∑ k, olsWeights (X n) a k ^ 2 * centralMoment (y n k) 2 P := by
  have hsq : ∀ k : Fin n, P[(olsArray P X y a n k) ^ 2]
      = olsWeights (X n) a k ^ 2 * centralMoment (y n k) 2 P := by
    intro k
    have hcongr : (olsArray P X y a n k) ^ 2
        = fun ω => olsWeights (X n) a k ^ 2 * (y n k ω - P[y n k]) ^ 2 := by
      funext ω
      simp only [Pi.pow_apply, olsArray]
      ring
    rw [hcongr, integral_const_mul]
    rfl
  exact Finset.sum_congr rfl fun k _ => hsq k

end olsArrayProperties


section IntermediateResults

/-- Bias–variance decomposition for a single coordinate: `E[(yᵢ − c)²] = Var(yᵢ) + (μᵢ − c)²`. -/
private lemma expected_sq_eq_variance_plus_bias
    (y : Ω → ℝ) (c : ℝ)
    (hy_MemL2 : MemLp y 2 P) :
    ∫ ω, (y ω - c) ^ 2 ∂P =
      centralMoment y 2 P + (P[y] - c) ^ 2 := by
  have hy_int : Integrable y P := hy_MemL2.integrable one_le_two
  have hy2_int : Integrable (fun ω => (y ω - P[y]) ^ 2) P := by
    simpa [Pi.sub_def] using (hy_MemL2.sub (memLp_const (P[y]))).integrable_sq
  change ∫ ω, (y ω - c) ^ 2 ∂P = ∫ ω, (y ω - P[y]) ^ 2 ∂P + (P[y] - c) ^ 2
  set μ := P[y] with hμ
  have hy_sub_int : Integrable (fun ω => y ω - μ) P := hy_int.sub (integrable_const _)
  have hzero : ∫ ω, (y ω - μ) ∂P = 0 := by rw [integral_sub hy_int (integrable_const _)]; simp [hμ]
  have hexp : (fun ω => (y ω - c) ^ 2) =
      (fun ω => (y ω - μ) ^ 2 + 2 * (μ - c) * (y ω - μ) + (μ - c) ^ 2) := by
    ext ω
    ring
  calc
    ∫ ω, (y ω - c) ^ 2 ∂P =
        ∫ ω, (y ω - μ) ^ 2 + 2 * (μ - c) * (y ω - μ) + (μ - c) ^ 2 ∂P := by
      rw [hexp]
    _= ∫ ω, (y ω - μ) ^ 2 ∂P + 2 * (μ - c) *  ∫ ω, (y ω - μ) ∂P + (μ - c) ^ 2 := by
      rw [integral_add (by fun_prop) (by fun_prop),
        integral_add (by fun_prop) (by fun_prop), integral_const_mul, integral_const]
      simp [probReal_univ]
    _= ∫ ω, (y ω - μ) ^ 2 ∂P + (μ - c) ^ 2 := by simp [hzero]

private lemma vector_expected_sq_eq_variance_plus
    (y : Fin n → Ω → ℝ) (c : Fin n → ℝ)
    (hy_MemL2 : ∀ i, MemLp (y i) 2 P) :
    ∫ ω, normSq ((y · ω) - c) ∂P =
      ∫ ω, normSq ((y · ω) - meanVec y P) ∂P + normSq (meanVec y P - c) := by
  have hy2_int : ∀ i, Integrable (fun ω => (y i ω - P[y i]) ^ 2) P := fun i => by
    simpa [Pi.sub_def] using ((hy_MemL2 i).sub (memLp_const (P[y i]))).integrable_sq
  set μ := meanVec y P with hμ
  simp only [normSq, dotProduct, Pi.sub_apply, ← pow_two, hμ, meanVec]
  have hc : ∀ i, Integrable (fun ω => (y i ω - c i) ^ 2) P := fun i => by
    simpa [Pi.sub_def] using ((hy_MemL2 i).sub (memLp_const (c i))).integrable_sq
  rw [integral_finsetSum _ (fun i _ => hc i)]
  rw [integral_finsetSum _ (fun i _ => hy2_int i)]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => expected_sq_eq_variance_plus_bias (y i) _ (hy_MemL2 i)

/-- `β*` minimises `E[‖y − Xβ‖²]` over all `β ∈ ℝᵖ`. -/
private lemma olsEstimand_minimizes_expected_loss
    (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → Ω → ℝ)
    (hX_inv : IsUnit (Xᵀ * X).det)
    (hy_MemL2 : ∀ i, MemLp (y i) 2 P) :
    ∀ β, ∫ ω, normSq ((y · ω) - (X *ᵥ olsEstimand P X y)) ∂P ≤
     ∫ ω, normSq ((y · ω) - (X *ᵥ β)) ∂P := by
  intro β
  have key : ∀ b : Fin p → ℝ,
      ∫ ω, normSq ((y · ω) - (X *ᵥ b)) ∂P =
          ∫ ω, normSq ((y · ω) - meanVec y P) ∂P + normSq (meanVec y P - (X *ᵥ b)) := by
    intro b
    exact vector_expected_sq_eq_variance_plus y (X *ᵥ b) hy_MemL2
  rw [key β, key (olsEstimand P X y)]
  -- The variance terms cancel; reduce to the algebraic optimality of `β*`.
  have hle : normSq (meanVec y P - (X *ᵥ olsEstimand P X y)) ≤ normSq (meanVec y P - (X *ᵥ β)) := by
    rw [show olsEstimand P X y = olsEstimator X (meanVec y P) from rfl]
    exact olsEstimator_optimal X (meanVec y P) hX_inv β
  linarith [hle]

end IntermediateResults


section MainResults

open Complex

/-- The OLS projection CLT (characteristic function version). -/
theorem central_limit_charFun_OLS_projection
    {P : Measure Ω} [IsProbabilityMeasure P] (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
    (y : (n : ℕ) → (Fin n) → Ω → ℝ) (a : (Fin p) → ℝ)
    (hy_meas : ∀ n i, Measurable (y n i))
    (hy_indep : ∀ n, iIndepFun (y n) P)
    (hy_MemL2 : ∀ n i, MemLp (y n i) 2 P)
    (hLind : LindebergConditionTriangular (olsArray P X y a) P)
    (hsVar_pos : ∀ᶠ n in atTop, 0 < momentSumTriangular (olsArray P X y a) P n)
    (t : ℝ) :
    Tendsto (fun n ↦ charFun (P.map (LindebergSumTriangular (olsArray P X y a) P n)) t) atTop
      (𝓝 (cexp (-(t ^ 2 / 2)))) :=
  central_limit_charFun_Lindeberg_Triangular
    (olsArray_measurable X y a hy_meas)
    (olsArray_row_indep X y a hy_indep)
    (olsArray_mean_zero X y a fun n i => (hy_MemL2 n i).mono_exponent one_le_two)
    (olsArray_memLp_two X y a hy_MemL2)
    hLind hsVar_pos t

/-- The OLS projection CLT (convergence in distribution version). -/
theorem central_limit_OLS_projection
    {P : ProbabilityMeasure Ω}
    (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
    (y : (n : ℕ) → (Fin n) → Ω → ℝ) (a : Fin p → ℝ)
    (hy_meas : ∀ n i, Measurable (y n i))
    (hy_indep : ∀ n, iIndepFun (y n) P)
    (hy_MemL2 : ∀ n i, MemLp (y n i) 2 P)
    (hLind : LindebergConditionTriangular (olsArray P X y a) P)
    (hsVar_pos : ∀ᶠ n in atTop, 0 < momentSumTriangular (olsArray P X y a) P n) :
    Tendsto (fun n : ℕ ↦ P.map (aemeasurable_olsArray X y a hy_meas n)) atTop
      (𝓝 stdGaussian) :=
  central_limit_Lindeberg_Triangular
    (olsArray_measurable X y a hy_meas)
    (olsArray_row_indep X y a hy_indep)
    (olsArray_mean_zero X y a fun n i => (hy_MemL2 n i).mono_exponent one_le_two)
    (olsArray_memLp_two X y a hy_MemL2)
    hLind hsVar_pos


end MainResults

end
end LinearModel
end LeanPool
