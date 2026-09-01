/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import LeanPool.LinearModel.Ols.Assumptions
import LeanPool.LinearModel.Ols.ConvergenceInProbability

/-!
# Consistency of the HC sandwich estimators

This file establishes that the heteroscedasticity-consistent (HC) sandwich estimators
`Sₙ⁻¹ M̂ₙᵈ Sₙ⁻¹` converge in probability entrywise to `Sₙ⁻¹ (Mₙ + Rₙ) Sₙ⁻¹` under the
assumption bundle,
where;
· `Sₙ = (1/n) XₙᵀXₙ` is the sample Gram matrix
· `M̂ₙᵈ = (1/n) ∑ᵢ dᵢ êᵢ² xᵢxᵢᵀ` is the residual-weighted Gram matrix, with residuals `ê = y − Xβ̂`
· `Mₙ = (1/n) ∑ᵢ Var(yᵢ) xᵢxᵢᵀ` is the variance-weighted Gram matrix
· `Rₙ = (1/n) ∑ᵢ rᵢ² xᵢxᵢᵀ` is the misspecification term built from the mean residuals
  `r = E[y] − Xβ*`.

Consistency is proved once for a generic residual-weighted Gram matrix `M̂ₙᵈ` whose
multiplier family `d` is admissible, meaning `⨆ᵢ |d_{n,i} − 1| → 0`; the standard
HC estimators are then obtained
by instantiation, with admissibility of the leverage-based corrections supplied by the
vanishing-leverage assumption.

The main results are the following:

· `hcGram_consistent` - each entry of `M̂ₙᵈ` converges in probability to the entry of
  `Mₙ + Rₙ` for any admissible multiplier family
· `hcGram_sandwich_consistent` - the sandwich form: `Sₙ⁻¹ M̂ₙᵈ Sₙ⁻¹ → Sₙ⁻¹ (Mₙ + Rₙ) Sₙ⁻¹`
  entrywise in probability
· `hc0_sandwich_consistent`, `hc1_sandwich_consistent`, `hc2_sandwich_consistent`,
  `hc3_sandwich_consistent` - instances for the HC0–HC3 multipliers `1`, `n/(n−p)`,
  `1/(1−hᵢ)` and `1/(1−hᵢ)²`.

-/

open MeasureTheory ProbabilityTheory Matrix Finset BigOperators Filter
open scoped Topology

namespace LeanPool.LinearModel

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section Definitions

variable {n p : ℕ} {P : Measure Ω}

/-- The OLS residual vector `ê = y − Xβ̂`. -/
def sampleResidual (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  olsResidual X y (olsEstimator X y)

/-- The residual-weighted Gram matrix of the HC sandwich estimator:
`M̂ₙ = (1/n) ∑ᵢ dᵢ êᵢ² xᵢxᵢᵀ` for a multiplier vector `d`. -/
def hcGram (X : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (y : Fin n → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  weightedGram X (fun i => d i * sampleResidual X y i ^ 2 / (n : ℝ))

/-- Entrywise form of `hcGram`. -/
lemma hcGram_apply (X : Matrix (Fin n) (Fin p) ℝ) (d y : Fin n → ℝ)
    (i j : Fin p) :
    hcGram X d y i j
      = ∑ k, d k * sampleResidual X y k ^ 2 / (n : ℝ) * (X k i * X k j) :=
  weightedGram_apply X _ i j

/-- The HC1 degrees-of-freedom correction `n/(n−p)`. -/
def hc1Correction (n p : ℕ) : ℝ := (n : ℝ) / ((n : ℝ) - (p : ℝ))

/-- The HC2 leverage correction `1/(1−hᵢ)`. -/
def hc2Correction (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) : ℝ :=
  (1 - leverage X i)⁻¹

/-- The HC3 leverage correction `1/(1−hᵢ)²`. -/
def hc3Correction (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) : ℝ :=
  ((1 - leverage X i)⁻¹) ^ 2

/-- The variance-weighted Gram matrix `Mₙ := (1/n) ∑ᵢ Var(yᵢ) xᵢxᵢᵀ`. -/
def varGram (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → Ω → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  weightedGram X (fun i => centralMoment (y i) 2 P / (n : ℝ))

/-- The misspecification Gram matrix `Rₙ := (1/n) ∑ᵢ rᵢ² xᵢxᵢᵀ`
where `r = E[y] − Xβ*`. -/
def misspecGram (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → Ω → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  weightedGram X (fun i => meanResidual P X y i ^ 2 / (n : ℝ))

/-- The finite-sample target `Mₙ + Rₙ` of the HC estimators. -/
def hcTarget (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → Ω → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  varGram P X y + misspecGram P X y

/-- Entrywise form of `hcTarget`. -/
lemma hcTarget_apply (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ)
    (i j : Fin p) :
    hcTarget P X y i j =
      ∑ k, (X k i * X k j) / (n : ℝ)
        * (centralMoment (y k) 2 P + meanResidual P X y k ^ 2) := by
  rw [hcTarget, Matrix.add_apply, varGram, misspecGram,
    weightedGram_apply, weightedGram_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The sandwich form `B M B`. -/
def sandwich (B M : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  B * M * B

/-- The HC sandwich estimator `Sₙ⁻¹ M̂ₙᵈ Sₙ⁻¹`. -/
def hcSandwich (X : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (y : Fin n → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  sandwich (sampleGram X)⁻¹ (hcGram X d y)

/-- The sandwich-form target `Sₙ⁻¹ (Mₙ + Rₙ) Sₙ⁻¹` of the HC sandwich estimators. -/
def sandwichTarget (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → Ω → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  sandwich (sampleGram X)⁻¹ (hcTarget P X y)

end Definitions


section CentredFamilies

variable {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- A centred family: measurable, independent, square-integrable, mean zero. -/
structure CentredFamily (P : Measure Ω) (Z : Fin n → Ω → ℝ) : Prop where
  meas : ∀ i, Measurable (Z i)
  indep : iIndepFun Z P
  memLp_two : ∀ i, MemLp (Z i) 2 P
  mean0 : ∀ i, P[Z i] = 0

omit [IsProbabilityMeasure P] in
/-- A weighted sum of a centered family is measurable. -/
lemma CentredFamily.weighted_sum_measurable {Z : Fin n → Ω → ℝ}
    (hZ : CentredFamily P Z) (w : Fin n → ℝ) :
    Measurable (fun ω => ∑ j, w j * Z j ω) :=
  Finset.measurable_sum Finset.univ fun j _ => (hZ.meas j).const_mul _

omit [IsProbabilityMeasure P] in
/-- A weighted sum of a centred family is in `L2`. -/
lemma CentredFamily.weighted_sum_MemL2 {Z : Fin n → Ω → ℝ}
    (hZ : CentredFamily P Z) (w : Fin n → ℝ) :
    MemLp (fun ω => ∑ j, w j * Z j ω) 2 P :=
  memLp_finsetSum Finset.univ fun j _ => (hZ.memLp_two j).const_mul _

/-- The weighted sum `∑ⱼ wⱼ Zⱼ` has second moment `∑ⱼ wⱼ² E[Zⱼ²]`. -/
lemma CentredFamily.weighted_sum_sq_integral {Z : Fin n → Ω → ℝ}
    (hZ : CentredFamily P Z) (w : Fin n → ℝ) :
    ∫ ω, (∑ j, w j * Z j ω) ^ 2 ∂P = ∑ j, w j ^ 2 * ∫ ω, Z j ω ^ 2 ∂P := by
  classical
  have hg_mean : ∀ j, P[fun ω => w j * Z j ω] = 0 := by
    intro j
    rw [integral_const_mul, hZ.mean0 j, mul_zero]
  have hsum_mean : P[fun ω => ∑ j, w j * Z j ω] = 0 := by
    rw [integral_finsetSum _ fun j _ => ((hZ.memLp_two j).integrable one_le_two).const_mul _]
    exact Finset.sum_eq_zero fun j _ => hg_mean j
  have hsum_eq : (∑ j, fun ω => w j * Z j ω) = fun ω => ∑ j, w j * Z j ω := by
    funext ω
    simp
  calc ∫ ω, (∑ j, w j * Z j ω) ^ 2 ∂P
      = Var[fun ω => ∑ j, w j * Z j ω; P] :=
        (variance_of_integral_eq_zero
          (hZ.weighted_sum_measurable w).aemeasurable hsum_mean).symm
    _ = ∑ j, Var[fun ω => w j * Z j ω; P] := by
        rw [← hsum_eq]
        exact IndepFun.variance_sum (μ := P)
          (fun j _ => (hZ.memLp_two j).const_mul _)
          fun i _ j _ hij =>
            (hZ.indep.comp (fun j z => w j * z)
              (fun j => measurable_const.mul measurable_id)).indepFun hij
    _ = ∑ j, w j ^ 2 * ∫ ω, Z j ω ^ 2 ∂P := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [variance_const_mul]
        congr 1
        exact variance_of_integral_eq_zero (hZ.meas j).aemeasurable (hZ.mean0 j)

/-- Bounded-variance form: if `E[Zⱼ²] ≤ γ` then the second moment of the weighted
sum is at most `γ · ∑ⱼ wⱼ²`. -/
lemma CentredFamily.weighted_sum_sq_integral_le {Z : Fin n → Ω → ℝ}
    (hZ : CentredFamily P Z) (w : Fin n → ℝ) (γ : ℝ)
    (hσ : ∀ j, ∫ ω, Z j ω ^ 2 ∂P ≤ γ) :
    ∫ ω, (∑ j, w j * Z j ω) ^ 2 ∂P ≤ γ * ∑ j, w j ^ 2 := by
  rw [hZ.weighted_sum_sq_integral w, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  calc w j ^ 2 * ∫ ω, Z j ω ^ 2 ∂P
      ≤ w j ^ 2 * γ := mul_le_mul_of_nonneg_left (hσ j) (sq_nonneg _)
    _ = γ * w j ^ 2 := by ring

end CentredFamilies


section ScalarInequalities

/-- `|ab| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq_add_sq (a b : ℝ) :
    |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul, ← sq_abs a, ← sq_abs b]
  linarith [two_mul_le_add_sq |a| |b|]

/-- `(a + b)⁴ ≤ 8a^4 + 8b⁴`. -/
private lemma add_pow_four_le_eight_add (a b : ℝ) :
    (a + b) ^ 4 ≤ 8 * a ^ 4 + 8 * b ^ 4 := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2),
    sq_nonneg (a ^ 2 + b ^ 2)]

/-- `(a - b)² ≤ 2a² + 2b²`. -/
private lemma sub_sq_le_two_add_two (a b : ℝ) :
    (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-- Parameterised Young inequality: `|ab| ≤ (θa² + b²/θ)/2` for `θ > 0`. -/
private lemma abs_mul_le_young {θ : ℝ} (hθ : 0 < θ) (a b : ℝ) :
    |a * b| ≤ (θ * a ^ 2 + b ^ 2 / θ) / 2 := by
  have key : 2 * θ * |a * b| ≤ θ ^ 2 * a ^ 2 + b ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (θ * |a| - |b|), sq_abs a, sq_abs b]
  have h2 : (θ * a ^ 2 + b ^ 2 / θ) / 2 = (θ ^ 2 * a ^ 2 + b ^ 2) / (2 * θ) := by
    field_simp
  rw [h2, le_div_iff₀ (by positivity)]
  linarith [key]

end ScalarInequalities


section ResidualIdentities

variable {n p : ℕ}

/-- `Xβ̂ = Hy`: the fitted values are the projection of `y`. -/
lemma mulVec_olsEstimator (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) :
    X *ᵥ (olsEstimator X y) = (hatMatrix X) *ᵥ y := by
  rw [olsEstimator, hatMatrix, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- The mean residual is the complement projection of the mean vector. -/
lemma meanResidual_eq_complement {P : Measure Ω} (X : Matrix (Fin n) (Fin p) ℝ)
    (v : Fin n → Ω → ℝ) :
    meanResidual P X v = meanVec v P - (hatMatrix X) *ᵥ (meanVec v P) := by
  rw [meanResidual, olsEstimand, mulVec_olsEstimator]

/-- For any `v`, `êᵢ = (v − Hv)ᵢ + (y − v)ᵢ − (H(y − v))ᵢ`. -/
lemma sampleResidual_decomp (X : Matrix (Fin n) (Fin p) ℝ) (y v : Fin n → ℝ)
    (i : Fin n) :
    sampleResidual X y i =
      (v i - ((hatMatrix X) *ᵥ v) i)
      + ((y i - v i) - ∑ j, hatMatrix X i j * (y j - v j)) := by
  have hres : sampleResidual X y i = y i - ((hatMatrix X) *ᵥ y) i := by
    rw [sampleResidual, olsResidual, mulVec_olsEstimator, Pi.sub_apply]
  have hHy : ((hatMatrix X) *ᵥ y) i
      = ∑ j, hatMatrix X i j * y j := by
    simp [Matrix.mulVec, dotProduct]
  have hHμ : ((hatMatrix X) *ᵥ v) i
      = ∑ j, hatMatrix X i j * v j := by
    simp [Matrix.mulVec, dotProduct]
  rw [hres, hHy, hHμ]
  have hsplit : ∑ j, hatMatrix X i j * (y j - v j)
      = (∑ j, hatMatrix X i j * y j) - ∑ j, hatMatrix X i j * v j := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hsplit]
  ring

end ResidualIdentities


section AssumptionBundleConsequences

variable {n p : ℕ} {P : Measure Ω} {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ}
  {y : (n : ℕ) → Fin n → Ω → ℝ}

/-- Degenerate case: over `Fin 0` the sample Gram matrix vanishes. -/
@[simp] lemma sampleGram_fin_zero (X : Matrix (Fin 0) (Fin p) ℝ) :
    sampleGram X = 0 := by
  ext a b
  rw [sampleGram_eq_weightedGram, weightedGram_apply]
  simp

/-- For any `i, j`, `|Sₙ i j| ≤ C`, where `C` is the spectral upper bound
from AssumptionBundle. -/
lemma AssumptionBundle.sampleGram_abs_entry_le (A1 : AssumptionBundle P X y)
    (n : ℕ) (i j : Fin p) : |sampleGram (X n) i j| ≤ A1.C := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simpa using A1.hC_pos.le
  · exact entry_ub_of_spectral_ub _ (sampleGram_transpose _) (sampleGram_is_psd _)
      A1.C (A1.hGram_spectral_ub n hpos) i j

/-- For any `i`, `∑ₖ Xₖᵢ²/n ≤ C`. -/
lemma AssumptionBundle.sum_sq_col_div_le (A1 : AssumptionBundle P X y)
    (n : ℕ) (i : Fin p) : ∑ k, X n k i ^ 2 / (n : ℝ) ≤ A1.C := by
  have hentry : sampleGram (X n) i i = ∑ k, 1 / (n : ℝ) * (X n k i * X n k i) := by
    rw [sampleGram_eq_weightedGram]
    exact weightedGram_apply (X n) _ i i
  have hcongr : ∑ k, X n k i ^ 2 / (n : ℝ)
      = ∑ k, 1 / (n : ℝ) * (X n k i * X n k i) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [hcongr, ← hentry]
  exact le_trans (le_abs_self _) (A1.sampleGram_abs_entry_le n i i)

/-- For any `i, j`, `∑ₖ |Xₖᵢ Xₖⱼ| / n ≤ C`. -/
lemma AssumptionBundle.sum_abs_rowProd_div_le (A1 : AssumptionBundle P X y)
    (n : ℕ) (i j : Fin p) : ∑ k, |X n k i * X n k j| / (n : ℝ) ≤ A1.C := by
  have hterm : ∀ k : Fin n, |X n k i * X n k j|
      ≤ (X n k i ^ 2 + X n k j ^ 2) / 2 := fun k =>
    abs_mul_le_half_sq_add_sq _ _
  calc
    ∑ k, |X n k i * X n k j| / (n : ℝ) =
        (∑ k, |X n k i * X n k j|) / (n : ℝ) := by
      simp only [Finset.sum_div]
    _ ≤ (∑ k, (X n k i ^ 2 + X n k j ^ 2) / 2) / (n : ℝ) :=
      div_le_div_of_nonneg_right
        (by apply Finset.sum_le_sum fun k _ => hterm k) (by positivity)
    _ = (∑ k, (X n k i ^ 2 + X n k j ^ 2) / (n : ℝ)) / 2 := by
      rw [← Finset.sum_div, ← Finset.sum_div, div_right_comm]
    _ = (∑ k, X n k i ^ 2 / (n : ℝ)) / 2 +
        (∑ k, X n k j ^ 2 / (n : ℝ)) / 2 := by
      simp only [add_div, Finset.sum_add_distrib]
    _ ≤ A1.C / 2 + A1.C / 2 := by
      linarith [A1.sum_sq_col_div_le n i, A1.sum_sq_col_div_le n j]
    _ = A1.C := by ring

/-- Scaled maximal squared row norm, `(⨆ᵢ ‖Xᵢ‖²)/n`. -/
def scaledMaxNormSq (X : Matrix (Fin n) (Fin p) ℝ) : ℝ :=
  (⨆ i : Fin n, normSq (X i)) / (n : ℝ)

/-- `scaledMaxNormSq` is non-negative. -/
lemma scaled_max_normSq_nonneg (X : Matrix (Fin n) (Fin p) ℝ) :
    0 ≤ scaledMaxNormSq X :=
  div_nonneg (Real.iSup_nonneg fun _ => normSq_nonneg _) (Nat.cast_nonneg _)

/-- Per-entry form: `Xᵢₖ² ≤ n · scaledMaxNormSq`. -/
lemma sq_entry_le_scaled_max_normSq (X : Matrix (Fin n) (Fin p) ℝ)
    (i : Fin n) (k : Fin p) :
    X i k ^ 2 ≤ (n : ℝ) * scaledMaxNormSq X := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast i.pos
  have h1 : X i k ^ 2 ≤ normSq (X i) := by
    simp only [normSq, dotProduct, ← pow_two]
    apply Finset.single_le_sum (f := fun j => X i j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have h2 : normSq (X i) ≤ ⨆ j : Fin n, normSq (X j) := by
    exact le_ciSup (f := fun j : Fin n => normSq (X j))
      (Set.finite_range _).bddAbove i
  have h3 : (⨆ j : Fin n, normSq (X j)) = (n : ℝ) * scaledMaxNormSq X := by
    rw [scaledMaxNormSq]
    field_simp
  linarith [le_trans h1 h2, h3.le, h3.ge]

/-- Under the assumption bundle: `‖Xₙᵢ‖²/n ≤ C · leverage X i`. -/
lemma AssumptionBundle.rowNormSq_div_le_leverage (A1 : AssumptionBundle P X y)
    (n : ℕ) (i : Fin n) :
    normSq (X n i) / (n : ℝ) ≤ A1.C * leverage (X n) i := by
  have hpos : 0 < n := i.pos
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
  have hdet := A1.isUnit_gram_det hpos
  have hSinv : (sampleGram (X n))⁻¹ = (n : ℝ) • ((X n)ᵀ * X n)⁻¹ := by
    have : Invertible (1 / (n : ℝ)) := invertibleOfNonzero (by positivity)
    rw [sampleGram, Matrix.inv_smul _ _ hdet,
      invOf_eq_right_inv (one_div_mul_cancel hn'.ne')]
  have hlev : normSq' (sampleGram (X n))⁻¹ (X n i) = (n : ℝ) * leverage (X n) i := by
    rw [hSinv, leverage_eq_normSq']
    simp [normSq']
  have h := inv_spectral_lb (sampleGram (X n)) (sampleGram_transpose _)
    (isUnit_sampleGram (X n) hpos hdet) (sampleGram_is_psd _) A1.C A1.hC_pos
    (A1.hGram_spectral_ub n hpos) (X n i)
  rw [hlev] at h
  rw [div_le_iff₀ hn']
  calc normSq (X n i)
      = A1.C * (1 / A1.C * normSq (X n i)) := by
        rw [← mul_assoc, mul_one_div_cancel A1.hC_pos.ne', one_mul]
    _ ≤ A1.C * ((n : ℝ) * leverage (X n) i) :=
        mul_le_mul_of_nonneg_left h A1.hC_pos.le
    _ = A1.C * leverage (X n) i * (n : ℝ) := by ring

/-- Under the assumption bundle, `scaledMaxNormSq (Xₙ) → 0`. -/
lemma AssumptionBundle.scaled_max_normSq_tendsto_zero (A1 : AssumptionBundle P X y) :
    Tendsto (fun n => scaledMaxNormSq (X n)) atTop (𝓝 0) := by
  have hupper : ∀ᶠ n in atTop, scaledMaxNormSq (X n) ≤ A1.C * maxLev (X n) := by
    filter_upwards [eventually_gt_atTop 0] with n hpos
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hpos
    rw [scaledMaxNormSq, div_le_iff₀ hn']
    refine ciSup_le fun i => ?_
    have h := (A1.rowNormSq_div_le_leverage n i).trans
      (mul_le_mul_of_nonneg_left (leverage_le_maxLev (X n) i) A1.hC_pos.le)
    exact (div_le_iff₀ hn').mp h
  have hlim : Tendsto (fun n => A1.C * maxLev (X n)) atTop (𝓝 0) := by
    simpa using A1.hlev.const_mul A1.C
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => scaled_max_normSq_nonneg (X n)) hupper

/-- Under the assumption bundle the centered responses `εₙ,ᵢ = yₙ,ᵢ − E[yₙ,ᵢ]`
form a centred family. -/
lemma AssumptionBundle.CentredFamily {p : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ}
    {y : (n : ℕ) → Fin n → Ω → ℝ} (A1 : AssumptionBundle P X y) (n : ℕ) :
    CentredFamily P (fun (i : Fin n) ω => y n i ω - meanVec (y n) P i) := by
  refine ⟨fun i => A1.hε_meas n i, ?_, ?_, ?_⟩
  · exact (A1.hy_indep n).comp (fun i t => t - meanVec (y n) P i)
      (fun i => measurable_id.sub measurable_const)
  · intro i
    exact (memLp_two_iff_integrable_sq
      (A1.hε_meas n i).aestronglyMeasurable).mpr (A1.hy2_int n i)
  · intro i
    have h1 : Integrable (fun ω => y n i ω - meanVec (y n) P i) P :=
      ((memLp_two_iff_integrable_sq (A1.hε_meas n i).aestronglyMeasurable).mpr
        (A1.hy2_int n i)).integrable one_le_two
    have hy_int : Integrable (y n i) P := by
      have h2 : Integrable
          (fun ω => (y n i ω - meanVec (y n) P i) + meanVec (y n) P i) P :=
        h1.add (integrable_const _)
      refine h2.congr (ae_of_all _ fun ω => ?_)
      simp
    rw [integral_sub hy_int (integrable_const _), integral_const]
    simp [meanVec]

end AssumptionBundleConsequences


section HCConsistency

variable {p : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ} {y : (n : ℕ) → Fin n → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- Decomposition of the error `M̂ₙᵈ - (Mₙ + Rₙ)`.  Writing `rᵢ` for the
mean residual, `εᵢ(ω)` for the centred response and `zᵢ(ω) = (Hε(ω))ᵢ`,
splitting `dₖ = 1 + (dₖ − 1)` makes the entry error split into the four sums
`A + B + C + D` treated below: the multiplier appears only in Term `D`. -/
lemma hcGram_entry_error_decomp (n : ℕ) (d : Fin n → ℝ) (ω : Ω) (i j : Fin p) :
    hcGram (X n) d (fun k => y n k ω) i j
      - hcTarget P (X n) (y n) i j =
      (∑ k, (X n k i * X n k j) / (n : ℝ)
        * ((meanResidual P (X n) (y n) k + (y n k ω - meanVec (y n) P k)) ^ 2
            - (centralMoment (y n k) 2 P + meanResidual P (X n) (y n) k ^ 2)))
      + (∑ k, (X n k i * X n k j) / (n : ℝ)
        * ((-2) * ((meanResidual P (X n) (y n) k + (y n k ω - meanVec (y n) P k))
            * ∑ l, hatMatrix (X n) k l * (y n l ω - meanVec (y n) P l))))
      + (∑ k, (X n k i * X n k j) / (n : ℝ)
        * (∑ l, hatMatrix (X n) k l * (y n l ω - meanVec (y n) P l)) ^ 2)
      + (∑ k, (X n k i * X n k j) / (n : ℝ)
        * ((d k - 1)
          * ((meanResidual P (X n) (y n) k + (y n k ω - meanVec (y n) P k))
              - ∑ l, hatMatrix (X n) k l * (y n l ω - meanVec (y n) P l)) ^ 2)) := by
  rw [hcGram_apply, hcTarget_apply, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpop : meanResidual P (X n) (y n) k
      = meanVec (y n) P k - ((hatMatrix (X n)) *ᵥ (meanVec (y n) P)) k := by
    rw [meanResidual_eq_complement, Pi.sub_apply]
  have hres := sampleResidual_decomp (X n) (fun l => y n l ω) (meanVec (y n) P) k
  rw [← hpop] at hres
  rw [hres]
  ring

/-- The centered response used in the HC consistency decomposition. -/
private abbrev hcCentered (P : Measure Ω) (y : (n : ℕ) → Fin n → Ω → ℝ)
    (n : ℕ) (k : Fin n) (ω : Ω) : ℝ :=
  y n k ω - meanVec (y n) P k

/-- The deterministic mean residual used in the HC consistency decomposition. -/
private abbrev hcResidual (P : Measure Ω) (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
    (y : (n : ℕ) → Fin n → Ω → ℝ) (n : ℕ) (k : Fin n) : ℝ :=
  meanResidual P (X n) (y n) k

/-- The response variance used in the HC consistency decomposition. -/
private abbrev hcVariance (P : Measure Ω) (y : (n : ℕ) → Fin n → Ω → ℝ)
    (n : ℕ) (k : Fin n) : ℝ :=
  centralMoment (y n k) 2 P

/-- The hat-matrix projection of the centered response. -/
private abbrev hcProjectedNoise (P : Measure Ω)
    (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
    (y : (n : ℕ) → Fin n → Ω → ℝ) (n : ℕ) (ω : Ω) (k : Fin n) : ℝ :=
  ∑ l, hatMatrix (X n) k l * hcCentered P y n l ω

omit [IsProbabilityMeasure P] in
private lemma hcResidual_sq_le (A1 : AssumptionBundle P X y) (n : ℕ) (k : Fin n) :
    hcResidual P X y n k ^ 2 ≤ A1.Cᵣ ^ 2 := by
  have habs := abs_le.mp (A1.hres_ub n k)
  exact sq_le_sq' habs.1 habs.2

omit [IsProbabilityMeasure P] in
private lemma hcShift_measurable (A1 : AssumptionBundle P X y) (n : ℕ) (k : Fin n) :
    Measurable (fun ω => hcResidual P X y n k + hcCentered P y n k ω) :=
  measurable_const.add (A1.hε_meas n k)

private lemma hcShift_memLp (A1 : AssumptionBundle P X y) (n : ℕ) (k : Fin n) :
    MemLp (fun ω => hcResidual P X y n k + hcCentered P y n k ω) 2 P := by
  have h := (memLp_const (hcResidual P X y n k) (μ := P) (p := 2)).add
    ((A1.CentredFamily n).memLp_two k)
  simpa [Pi.add_def] using h

private lemma hcShift_fourth_integrable (A1 : AssumptionBundle P X y)
    (n : ℕ) (k : Fin n) :
    Integrable (fun ω => (hcResidual P X y n k + hcCentered P y n k ω) ^ 4) P := by
  have hdom : Integrable (fun ω =>
      8 * hcResidual P X y n k ^ 4 + 8 * hcCentered P y n k ω ^ 4) P :=
    (integrable_const _).add ((A1.hy4_int n k).const_mul 8)
  refine hdom.mono' ((hcShift_measurable A1 n k).pow_const 4).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have hnn : (0 : ℝ) ≤ (hcResidual P X y n k + hcCentered P y n k ω) ^ 4 := by
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact add_pow_four_le_eight_add _ _

private lemma hcShift_fourth_integral_le (A1 : AssumptionBundle P X y)
    (n : ℕ) (k : Fin n) :
    ∫ ω, (hcResidual P X y n k + hcCentered P y n k ω) ^ 4 ∂P
      ≤ 8 * A1.Cᵣ ^ 4 + 8 * A1.β ^ 2 := by
  have hstep : ∫ ω, (hcResidual P X y n k + hcCentered P y n k ω) ^ 4 ∂P
      ≤ ∫ ω, (8 * hcResidual P X y n k ^ 4 +
        8 * hcCentered P y n k ω ^ 4) ∂P := by
    exact integral_mono (hcShift_fourth_integrable A1 n k)
      ((integrable_const _).add ((A1.hy4_int n k).const_mul 8))
      fun ω => add_pow_four_le_eight_add _ _
  have hsplit : ∫ ω, (8 * hcResidual P X y n k ^ 4 +
        8 * hcCentered P y n k ω ^ 4) ∂P =
      8 * hcResidual P X y n k ^ 4 + 8 * ∫ ω, hcCentered P y n k ω ^ 4 ∂P := by
    have hint4 : Integrable (fun ω => 8 * hcCentered P y n k ω ^ 4) P :=
      (A1.hy4_int n k).const_mul 8
    rw [integral_add (integrable_const _) hint4, integral_const, integral_const_mul]
    simp
  have hr4 : hcResidual P X y n k ^ 4 ≤ A1.Cᵣ ^ 4 := by
    have h2 := hcResidual_sq_le A1 n k
    nlinarith [sq_nonneg (hcResidual P X y n k), A1.hCr_nonneg, sq_nonneg A1.Cᵣ]
  have hκi : ∫ ω, hcCentered P y n k ω ^ 4 ∂P ≤ A1.β ^ 2 := A1.hy4_ub n k
  calc
    ∫ ω, (hcResidual P X y n k + hcCentered P y n k ω) ^ 4 ∂P
        ≤ 8 * hcResidual P X y n k ^ 4 +
          8 * ∫ ω, hcCentered P y n k ω ^ 4 ∂P := by
      rw [← hsplit]
      exact hstep
    _ ≤ 8 * A1.Cᵣ ^ 4 + 8 * A1.β ^ 2 := by nlinarith

private lemma hcShift_sq_integrable (A1 : AssumptionBundle P X y)
    (n : ℕ) (k : Fin n) :
    Integrable (fun ω => (hcResidual P X y n k + hcCentered P y n k ω) ^ 2) P :=
  (hcShift_memLp A1 n k).integrable_sq

private lemma hcShift_sq_integral_eq (A1 : AssumptionBundle P X y)
    (n : ℕ) (k : Fin n) :
    ∫ ω, (hcResidual P X y n k + hcCentered P y n k ω) ^ 2 ∂P =
      hcVariance P y n k + hcResidual P X y n k ^ 2 := by
  have hCF := A1.CentredFamily n
  have hint2 : Integrable (fun ω => hcCentered P y n k ω ^ 2) P :=
    (hCF.memLp_two k).integrable_sq
  have hint1 : Integrable (fun ω => hcCentered P y n k ω) P :=
    (hCF.memLp_two k).integrable one_le_two
  have hint12 : Integrable (fun ω => hcCentered P y n k ω ^ 2 +
      (2 * hcResidual P X y n k) * hcCentered P y n k ω) P :=
    hint2.add (hint1.const_mul _)
  have hvar_eq : ∫ ω, hcCentered P y n k ω ^ 2 ∂P = hcVariance P y n k := rfl
  have hexp : (fun ω => (hcResidual P X y n k + hcCentered P y n k ω) ^ 2) =
      fun ω => hcCentered P y n k ω ^ 2 +
        (2 * hcResidual P X y n k) * hcCentered P y n k ω +
        hcResidual P X y n k ^ 2 := by
    funext ω
    ring
  rw [hexp, integral_add hint12 (integrable_const _),
    integral_add hint2 (hint1.const_mul _), integral_const_mul, integral_const,
    hCF.mean0 k, hvar_eq]
  simp

private lemma hcProjected_memLp (A1 : AssumptionBundle P X y)
    (n : ℕ) (k : Fin n) :
    MemLp (fun ω => hcProjectedNoise P X y n ω k) 2 P :=
  (A1.CentredFamily n).weighted_sum_MemL2
    (fun l => hatMatrix (X n) k l)

private lemma hcProjected_sq_integrable (A1 : AssumptionBundle P X y)
    (n : ℕ) (k : Fin n) :
    Integrable (fun ω => hcProjectedNoise P X y n ω k ^ 2) P :=
  (hcProjected_memLp A1 n k).integrable_sq

private lemma hcProjected_sq_integral_le (A1 : AssumptionBundle P X y)
    (n : ℕ) (k : Fin n) :
    ∫ ω, hcProjectedNoise P X y n ω k ^ 2 ∂P ≤ A1.β * maxLev (X n) := by
  have h := (A1.CentredFamily n).weighted_sum_sq_integral_le
    (fun l => hatMatrix (X n) k l) A1.β
    (fun l => le_trans (show ∫ ω, hcCentered P y n l ω ^ 2 ∂P =
      hcVariance P y n l from rfl).le (A1.hvar_ub n l))
  calc
    ∫ ω, hcProjectedNoise P X y n ω k ^ 2 ∂P
        ≤ A1.β * ∑ l, hatMatrix (X n) k l ^ 2 := h
    _ = A1.β * leverage (X n) k := by
      rw [leverage_eq_hatMatrix_normSq (X n) (A1.isUnit_gram_det k.pos) k,
        normSq_eq_sum_sq]
    _ ≤ A1.β * maxLev (X n) :=
      mul_le_mul_of_nonneg_left (leverage_le_maxLev (X n) k) A1.hβ_nonneg

private lemma hcTermA_tendsto (A1 : AssumptionBundle P X y) (i j : Fin p) :
    TendstoInProbability P
      (fun n ω => ∑ k, (X n k i * X n k j) / (n : ℝ) *
        ((hcResidual P X y n k + hcCentered P y n k ω) ^ 2 -
          (hcVariance P y n k + hcResidual P X y n k ^ 2)))
      (fun _ => 0) := by
  let fA : (n : ℕ) → Ω → ℝ := fun n ω =>
    ∑ k, (X n k i * X n k j) / (n : ℝ) *
      ((hcResidual P X y n k + hcCentered P y n k ω) ^ 2 -
        (hcVariance P y n k + hcResidual P X y n k ^ 2))
  change TendstoInProbability P fA (fun _ => 0)
  let g : (n : ℕ) → Fin n → Ω → ℝ := fun n k ω =>
    (X n k i * X n k j) / (n : ℝ) *
      ((hcResidual P X y n k + hcCentered P y n k ω) ^ 2 -
        (hcVariance P y n k + hcResidual P X y n k ^ 2))
  have hg_meas : ∀ n (k : Fin n), Measurable (g n k) := fun n k =>
    (((hcShift_measurable A1 n k).pow_const 2).sub_const _).const_mul _
  have hg_memLp : ∀ n (k : Fin n), MemLp (g n k) 2 P := by
    intro n k
    rw [memLp_two_iff_integrable_sq (hg_meas n k).aestronglyMeasurable]
    have hdom : Integrable (fun ω => ((X n k i * X n k j) / (n : ℝ)) ^ 2 *
        (2 * (hcResidual P X y n k + hcCentered P y n k ω) ^ 4 +
          2 * (hcVariance P y n k + hcResidual P X y n k ^ 2) ^ 2)) P :=
      (((hcShift_fourth_integrable A1 n k).const_mul 2).add
        (integrable_const _)).const_mul _
    refine hdom.mono' ((hg_meas n k).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have hb : ((hcResidual P X y n k + hcCentered P y n k ω) ^ 2 -
        (hcVariance P y n k + hcResidual P X y n k ^ 2)) ^ 2 ≤
        2 * (hcResidual P X y n k + hcCentered P y n k ω) ^ 4 +
          2 * (hcVariance P y n k + hcResidual P X y n k ^ 2) ^ 2 := by
      nlinarith [sub_sq_le_two_add_two
        ((hcResidual P X y n k + hcCentered P y n k ω) ^ 2)
        (hcVariance P y n k + hcResidual P X y n k ^ 2)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ((X n k i * X n k j) / (n : ℝ) *
        ((hcResidual P X y n k + hcCentered P y n k ω) ^ 2 -
          (hcVariance P y n k + hcResidual P X y n k ^ 2))) ^ 2 ≤ _
    calc
      ((X n k i * X n k j) / (n : ℝ) *
          ((hcResidual P X y n k + hcCentered P y n k ω) ^ 2 -
            (hcVariance P y n k + hcResidual P X y n k ^ 2))) ^ 2 =
          ((X n k i * X n k j) / (n : ℝ)) ^ 2 *
            ((hcResidual P X y n k + hcCentered P y n k ω) ^ 2 -
              (hcVariance P y n k + hcResidual P X y n k ^ 2)) ^ 2 := by ring
      _ ≤ ((X n k i * X n k j) / (n : ℝ)) ^ 2 *
          (2 * (hcResidual P X y n k + hcCentered P y n k ω) ^ 4 +
            2 * (hcVariance P y n k + hcResidual P X y n k ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
  have hg_int : ∀ n (k : Fin n), Integrable (g n k) P := fun n k =>
    (hg_memLp n k).integrable one_le_two
  have hg_mean : ∀ n (k : Fin n), P[g n k] = 0 := by
    intro n k
    have h1 : P[g n k] = (X n k i * X n k j) / (n : ℝ) *
        ∫ ω, ((hcResidual P X y n k + hcCentered P y n k ω) ^ 2 -
          (hcVariance P y n k + hcResidual P X y n k ^ 2)) ∂P := by
      exact integral_const_mul _ _
    rw [h1, integral_sub (hcShift_sq_integrable A1 n k) (integrable_const _),
      integral_const, hcShift_sq_integral_eq A1 n k]
    simp
  have hg_pair : ∀ n, Set.Pairwise ↑(Finset.univ : Finset (Fin n))
      fun k l => IndepFun (g n k) (g n l) P := by
    intro n
    have hcomp : iIndepFun (g n) P := by
      refine (A1.hy_indep n).comp (fun k t =>
        (X n k i * X n k j) / (n : ℝ) *
          ((hcResidual P X y n k + (t - meanVec (y n) P k)) ^ 2 -
            (hcVariance P y n k + hcResidual P X y n k ^ 2))) fun k => ?_
      exact (((measurable_const.add (measurable_id.sub
        measurable_const)).pow_const 2).sub_const _).const_mul _
    exact fun k _ l _ hij => hcomp.indepFun hij
  have hsum_eq : ∀ n, fA n = ∑ k, g n k := by
    intro n
    funext ω
    simp [fA, g]
  have hvar_le : ∀ n, Var[fA n; P] ≤
      (8 * A1.Cᵣ ^ 4 + 8 * A1.β ^ 2) * A1.C * scaledMaxNormSq (X n) := by
    intro n
    have hvar_sum : Var[∑ k, g n k; P] = ∑ k, Var[g n k; P] :=
      IndepFun.variance_sum (μ := P) (fun k _ => hg_memLp n k) (hg_pair n)
    have hvar_i : ∀ k : Fin n, Var[g n k; P] ≤
        (X n k i * X n k j) ^ 2 / (n : ℝ) ^ 2 *
          (8 * A1.Cᵣ ^ 4 + 8 * A1.β ^ 2) := by
      intro k
      have h1 : Var[g n k; P] = ((X n k i * X n k j) / (n : ℝ)) ^ 2 *
          Var[fun ω => (hcResidual P X y n k + hcCentered P y n k ω) ^ 2 -
            (hcVariance P y n k + hcResidual P X y n k ^ 2); P] :=
        variance_const_mul _ _ _
      have h2 : Var[fun ω => (hcResidual P X y n k + hcCentered P y n k ω) ^ 2 -
          (hcVariance P y n k + hcResidual P X y n k ^ 2); P] =
          Var[fun ω => (hcResidual P X y n k + hcCentered P y n k ω) ^ 2; P] :=
        variance_sub_const (((hcShift_measurable A1 n k).pow_const 2).aestronglyMeasurable) _
      have h3 : Var[fun ω => (hcResidual P X y n k + hcCentered P y n k ω) ^ 2; P]
          ≤ ∫ ω, (hcResidual P X y n k + hcCentered P y n k ω) ^ 4 ∂P := by
        have hle := variance_le_expectation_sq (μ := P)
          (X := fun ω => (hcResidual P X y n k + hcCentered P y n k ω) ^ 2)
          ((hcShift_measurable A1 n k).pow_const 2).aestronglyMeasurable
        have hcongr : P[(fun ω =>
            (hcResidual P X y n k + hcCentered P y n k ω) ^ 2) ^ 2] =
            ∫ ω, (hcResidual P X y n k + hcCentered P y n k ω) ^ 4 ∂P := by
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          simp only [Pi.pow_apply]
          ring
        rw [hcongr] at hle
        exact hle
      calc
        Var[g n k; P] = ((X n k i * X n k j) / (n : ℝ)) ^ 2 *
            Var[fun ω => (hcResidual P X y n k + hcCentered P y n k ω) ^ 2; P] := by
          rw [h1, h2]
        _ ≤ ((X n k i * X n k j) / (n : ℝ)) ^ 2 *
            (8 * A1.Cᵣ ^ 4 + 8 * A1.β ^ 2) :=
          mul_le_mul_of_nonneg_left (h3.trans (hcShift_fourth_integral_le A1 n k))
            (sq_nonneg _)
        _ = (X n k i * X n k j) ^ 2 / (n : ℝ) ^ 2 *
            (8 * A1.Cᵣ ^ 4 + 8 * A1.β ^ 2) := by rw [div_pow]
    have hsum_le : ∑ k, (X n k i * X n k j) ^ 2 / (n : ℝ) ^ 2 ≤
        A1.C * scaledMaxNormSq (X n) := by
      have hterm : ∀ k : Fin n, (X n k i * X n k j) ^ 2 / (n : ℝ) ^ 2 ≤
          scaledMaxNormSq (X n) * (X n k j ^ 2 / (n : ℝ)) := by
        intro k
        have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast k.pos
        rw [show (X n k i * X n k j) ^ 2 / (n : ℝ) ^ 2 =
          (X n k i ^ 2 / (n : ℝ)) * (X n k j ^ 2 / (n : ℝ)) by field_simp]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ hn']
        simpa [mul_comm] using sq_entry_le_scaled_max_normSq (X n) k i
      calc
        ∑ k, (X n k i * X n k j) ^ 2 / (n : ℝ) ^ 2 ≤
            ∑ k, scaledMaxNormSq (X n) * (X n k j ^ 2 / (n : ℝ)) :=
          Finset.sum_le_sum fun k _ => hterm k
        _ = scaledMaxNormSq (X n) * ∑ k, X n k j ^ 2 / (n : ℝ) := by
          rw [Finset.mul_sum]
        _ ≤ scaledMaxNormSq (X n) * A1.C :=
          mul_le_mul_of_nonneg_left (A1.sum_sq_col_div_le n j)
            (scaled_max_normSq_nonneg (X n))
        _ = A1.C * scaledMaxNormSq (X n) := by ring
    calc
      Var[fA n; P] = ∑ k, Var[g n k; P] := by rw [hsum_eq n]; exact hvar_sum
      _ ≤ ∑ k, (X n k i * X n k j) ^ 2 / (n : ℝ) ^ 2 *
          (8 * A1.Cᵣ ^ 4 + 8 * A1.β ^ 2) := Finset.sum_le_sum fun k _ => hvar_i k
      _ = (∑ k, (X n k i * X n k j) ^ 2 / (n : ℝ) ^ 2) *
          (8 * A1.Cᵣ ^ 4 + 8 * A1.β ^ 2) := by rw [Finset.sum_mul]
      _ ≤ (A1.C * scaledMaxNormSq (X n)) *
          (8 * A1.Cᵣ ^ 4 + 8 * A1.β ^ 2) :=
        mul_le_mul_of_nonneg_right hsum_le (by positivity)
      _ = (8 * A1.Cᵣ ^ 4 + 8 * A1.β ^ 2) * A1.C * scaledMaxNormSq (X n) := by
        ring
  have hfA_memLp : ∀ n, MemLp (fA n) 2 P := fun n =>
    memLp_finsetSum Finset.univ fun k _ => hg_memLp n k
  have hfA_mean : ∀ n, P[fA n] = 0 := by
    intro n
    have h : P[fA n] = ∑ k, P[g n k] := by
      rw [hsum_eq n]
      simpa only [Finset.sum_apply] using
        (integral_finsetSum Finset.univ fun k _ => hg_int n k)
    rw [h]
    exact Finset.sum_eq_zero fun k _ => hg_mean n k
  have hlim : Tendsto (fun n => (8 * A1.Cᵣ ^ 4 + 8 * A1.β ^ 2) * A1.C *
      scaledMaxNormSq (X n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using A1.scaled_max_normSq_tendsto_zero.const_mul
      ((8 * A1.Cᵣ ^ 4 + 8 * A1.β ^ 2) * A1.C)
  have hvar_lim : Tendsto (fun n => Var[fA n; P]) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => variance_nonneg _ _) hvar_le
  exact TendstoInProbability.of_variance hfA_memLp hfA_mean hvar_lim

private lemma hcTermB_tendsto (A1 : AssumptionBundle P X y) (i j : Fin p) :
    TendstoInProbability P
      (fun n ω => ∑ k, (X n k i * X n k j) / (n : ℝ) *
        (-2 * ((hcResidual P X y n k + hcCentered P y n k ω) *
          hcProjectedNoise P X y n ω k)))
      (fun _ => 0) := by
  let fB : (n : ℕ) → Ω → ℝ := fun n ω =>
    ∑ k, (X n k i * X n k j) / (n : ℝ) *
      (-2 * ((hcResidual P X y n k + hcCentered P y n k ω) *
        hcProjectedNoise P X y n ω k))
  change TendstoInProbability P fB (fun _ => 0)
  let θ : ℕ → ℝ := fun n => Real.sqrt (maxLev (X n)) + 1 / ((n : ℝ) + 1)
  have hθ_pos : ∀ n, 0 < θ n := by
    intro n
    simp only [θ]
    positivity
  have hθ_ge : ∀ n, Real.sqrt (maxLev (X n)) ≤ θ n := by
    intro n
    simp only [θ]
    exact le_add_of_nonneg_right (by positivity)
  have hlev_div : ∀ n, maxLev (X n) / θ n ≤ Real.sqrt (maxLev (X n)) := by
    intro n
    have hL_nn : 0 ≤ maxLev (X n) := maxLev_nonneg (X n)
    rw [div_le_iff₀ (hθ_pos n)]
    calc
      maxLev (X n) = Real.sqrt (maxLev (X n)) * Real.sqrt (maxLev (X n)) :=
        (Real.mul_self_sqrt hL_nn).symm
      _ ≤ Real.sqrt (maxLev (X n)) * θ n :=
        mul_le_mul_of_nonneg_left (hθ_ge n) (Real.sqrt_nonneg _)
  have hprod_int : ∀ n (k : Fin n), Integrable (fun ω =>
      (hcResidual P X y n k + hcCentered P y n k ω) *
        hcProjectedNoise P X y n ω k) P := by
    intro n k
    have hmul := MemLp.integrable_mul (hcShift_memLp A1 n k) (hcProjected_memLp A1 n k)
    refine hmul.congr (ae_of_all _ fun ω => ?_)
    simp [Pi.mul_apply]
  have hterm_int : ∀ n (k : Fin n), Integrable (fun ω =>
      (X n k i * X n k j) / (n : ℝ) *
        (-2 * ((hcResidual P X y n k + hcCentered P y n k ω) *
          hcProjectedNoise P X y n ω k))) P := fun n k =>
    ((hprod_int n k).const_mul _).const_mul _
  have hfB_int : ∀ n, Integrable (fB n) P := fun n =>
    integrable_finsetSum _ fun k _ => hterm_int n k
  have hterm_bd : ∀ n (k : Fin n), ∫ ω,
      |(hcResidual P X y n k + hcCentered P y n k ω) *
        hcProjectedNoise P X y n ω k| ∂P ≤
      (θ n * (A1.β + A1.Cᵣ ^ 2) + A1.β * Real.sqrt (maxLev (X n))) / 2 := by
    intro n k
    have hpoint : ∀ ω, |(hcResidual P X y n k + hcCentered P y n k ω) *
        hcProjectedNoise P X y n ω k| ≤
        (θ n * (hcResidual P X y n k + hcCentered P y n k ω) ^ 2 +
          hcProjectedNoise P X y n ω k ^ 2 / θ n) / 2 := fun ω =>
      abs_mul_le_young (hθ_pos n) _ _
    have hint_rhs : Integrable (fun ω =>
        (θ n * (hcResidual P X y n k + hcCentered P y n k ω) ^ 2 +
          hcProjectedNoise P X y n ω k ^ 2 / θ n) / 2) P := by
      refine Integrable.div_const ?_ 2
      exact ((hcShift_sq_integrable A1 n k).const_mul _).add
        ((hcProjected_sq_integrable A1 n k).div_const _)
    have hstep := integral_mono ((hprod_int n k).abs) hint_rhs hpoint
    rw [integral_div, integral_add ((hcShift_sq_integrable A1 n k).const_mul _)
      ((hcProjected_sq_integrable A1 n k).div_const _), integral_const_mul,
      integral_div, hcShift_sq_integral_eq A1 n k] at hstep
    refine hstep.trans ?_
    have h1 : θ n * (hcVariance P y n k + hcResidual P X y n k ^ 2) ≤
        θ n * (A1.β + A1.Cᵣ ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (hθ_pos n).le
      linarith [A1.hvar_ub n k, hcResidual_sq_le A1 n k]
    have h2 : (∫ ω, hcProjectedNoise P X y n ω k ^ 2 ∂P) / θ n ≤
        A1.β * Real.sqrt (maxLev (X n)) := by
      refine (div_le_div_of_nonneg_right (hcProjected_sq_integral_le A1 n k)
        (hθ_pos n).le).trans ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hlev_div n) A1.hβ_nonneg
    linarith
  let δB : ℕ → ℝ := fun n => A1.C *
    (θ n * (A1.β + A1.Cᵣ ^ 2) + A1.β * Real.sqrt (maxLev (X n)))
  have hfB_bd : ∀ n, ∫ ω, |fB n ω| ∂P ≤ δB n := by
    intro n
    have habs_le : ∀ ω, |fB n ω| ≤ ∑ k, |X n k i * X n k j| / (n : ℝ) *
        (2 * |(hcResidual P X y n k + hcCentered P y n k ω) *
          hcProjectedNoise P X y n ω k|) := by
      intro ω
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      simp [abs_mul, abs_div, abs_neg, Nat.abs_cast]
    have hint_dom : Integrable (fun ω => ∑ k, |X n k i * X n k j| / (n : ℝ) *
        (2 * |(hcResidual P X y n k + hcCentered P y n k ω) *
          hcProjectedNoise P X y n ω k|)) P :=
      integrable_finsetSum _ fun k _ => ((hprod_int n k).abs.const_mul 2).const_mul _
    have hstep := integral_mono (hfB_int n).abs hint_dom habs_le
    have hsum_int : ∫ ω, (∑ k, |X n k i * X n k j| / (n : ℝ) *
          (2 * |(hcResidual P X y n k + hcCentered P y n k ω) *
            hcProjectedNoise P X y n ω k|)) ∂P =
        ∑ k, |X n k i * X n k j| / (n : ℝ) *
          (2 * ∫ ω, |(hcResidual P X y n k + hcCentered P y n k ω) *
            hcProjectedNoise P X y n ω k| ∂P) := by
      rw [integral_finsetSum _ fun k _ => ((hprod_int n k).abs.const_mul 2).const_mul _]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul, integral_const_mul]
    rw [hsum_int] at hstep
    refine hstep.trans ?_
    calc
      ∑ k, |X n k i * X n k j| / (n : ℝ) *
          (2 * ∫ ω, |(hcResidual P X y n k + hcCentered P y n k ω) *
            hcProjectedNoise P X y n ω k| ∂P)
          ≤ ∑ k, |X n k i * X n k j| / (n : ℝ) *
            (θ n * (A1.β + A1.Cᵣ ^ 2) + A1.β * Real.sqrt (maxLev (X n))) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (by linarith [hterm_bd n k]) (by positivity)
      _ = (∑ k, |X n k i * X n k j| / (n : ℝ)) *
          (θ n * (A1.β + A1.Cᵣ ^ 2) + A1.β * Real.sqrt (maxLev (X n))) := by
        rw [Finset.sum_mul]
      _ ≤ A1.C * (θ n * (A1.β + A1.Cᵣ ^ 2) +
          A1.β * Real.sqrt (maxLev (X n))) := by
        refine mul_le_mul_of_nonneg_right (A1.sum_abs_rowProd_div_le n i j) ?_
        exact add_nonneg
          (mul_nonneg (hθ_pos n).le (add_nonneg A1.hβ_nonneg (sq_nonneg _)))
          (mul_nonneg A1.hβ_nonneg (Real.sqrt_nonneg _))
      _ = δB n := rfl
  have hδB_lim : Tendsto δB atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n => Real.sqrt (maxLev (X n))) atTop (𝓝 0) := by
      simpa [Real.sqrt_zero] using A1.hlev.sqrt
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hθ_lim : Tendsto θ atTop (𝓝 0) := by
      simpa [θ] using hsqrt.add hinv
    have h := ((hθ_lim.mul_const (A1.β + A1.Cᵣ ^ 2)).add
      (hsqrt.const_mul A1.β)).const_mul A1.C
    simpa [δB] using h
  exact TendstoInProbability.of_integral_abs_le
    (fun n => memLp_one_iff_integrable.mpr (hfB_int n)) hfB_bd hδB_lim

private lemma hcTermC_tendsto (A1 : AssumptionBundle P X y) (i j : Fin p) :
    TendstoInProbability P
      (fun n ω => ∑ k, (X n k i * X n k j) / (n : ℝ) *
        hcProjectedNoise P X y n ω k ^ 2)
      (fun _ => 0) := by
  let fC : (n : ℕ) → Ω → ℝ := fun n ω =>
    ∑ k, (X n k i * X n k j) / (n : ℝ) * hcProjectedNoise P X y n ω k ^ 2
  change TendstoInProbability P fC (fun _ => 0)
  have hterm_int : ∀ n (k : Fin n), Integrable (fun ω =>
      (X n k i * X n k j) / (n : ℝ) * hcProjectedNoise P X y n ω k ^ 2) P :=
    fun n k => (hcProjected_sq_integrable A1 n k).const_mul _
  have hfC_int : ∀ n, Integrable (fC n) P := fun n =>
    integrable_finsetSum _ fun k _ => hterm_int n k
  let δC : ℕ → ℝ := fun n => A1.C * (A1.β * maxLev (X n))
  have hfC_bd : ∀ n, ∫ ω, |fC n ω| ∂P ≤ δC n := by
    intro n
    have habs_le : ∀ ω, |fC n ω| ≤ ∑ k, |X n k i * X n k j| / (n : ℝ) *
        hcProjectedNoise P X y n ω k ^ 2 := by
      intro ω
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, abs_div, Nat.abs_cast,
        abs_of_nonneg (sq_nonneg (hcProjectedNoise P X y n ω k))]
    have hint_dom : Integrable (fun ω => ∑ k, |X n k i * X n k j| / (n : ℝ) *
        hcProjectedNoise P X y n ω k ^ 2) P :=
      integrable_finsetSum _ fun k _ => (hcProjected_sq_integrable A1 n k).const_mul _
    have hstep := integral_mono (hfC_int n).abs hint_dom habs_le
    have hsum_int : ∫ ω, (∑ k, |X n k i * X n k j| / (n : ℝ) *
          hcProjectedNoise P X y n ω k ^ 2) ∂P =
        ∑ k, |X n k i * X n k j| / (n : ℝ) *
          ∫ ω, hcProjectedNoise P X y n ω k ^ 2 ∂P := by
      rw [integral_finsetSum _ fun k _ => (hcProjected_sq_integrable A1 n k).const_mul _]
      exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
    rw [hsum_int] at hstep
    refine hstep.trans ?_
    calc
      ∑ k, |X n k i * X n k j| / (n : ℝ) *
          ∫ ω, hcProjectedNoise P X y n ω k ^ 2 ∂P ≤
          ∑ k, |X n k i * X n k j| / (n : ℝ) *
            (A1.β * maxLev (X n)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (hcProjected_sq_integral_le A1 n k) (by positivity)
      _ = (∑ k, |X n k i * X n k j| / (n : ℝ)) *
          (A1.β * maxLev (X n)) := by rw [Finset.sum_mul]
      _ ≤ A1.C * (A1.β * maxLev (X n)) :=
        mul_le_mul_of_nonneg_right (A1.sum_abs_rowProd_div_le n i j)
          (mul_nonneg A1.hβ_nonneg (maxLev_nonneg (X n)))
      _ = δC n := rfl
  have hδC_lim : Tendsto δC atTop (𝓝 0) := by
    simpa [δC, mul_assoc] using (A1.hlev.const_mul A1.β).const_mul A1.C
  exact TendstoInProbability.of_integral_abs_le
    (fun n => memLp_one_iff_integrable.mpr (hfC_int n)) hfC_bd hδC_lim

private lemma hcTermD_tendsto (A1 : AssumptionBundle P X y)
    (d : (n : ℕ) → Fin n → ℝ)
    (hd : Tendsto (fun n => ⨆ k : Fin n, |d n k - 1|) atTop (𝓝 0))
    (i j : Fin p) :
    TendstoInProbability P
      (fun n ω => ∑ k, (X n k i * X n k j) / (n : ℝ) *
        ((d n k - 1) * ((hcResidual P X y n k + hcCentered P y n k ω) -
          hcProjectedNoise P X y n ω k) ^ 2))
      (fun _ => 0) := by
  let D : ℕ → ℝ := fun n => ⨆ k : Fin n, |d n k - 1|
  have hD_nn : ∀ n, 0 ≤ D n := fun n => Real.iSup_nonneg fun k => abs_nonneg _
  have hDk : ∀ n (k : Fin n), |d n k - 1| ≤ D n := fun n k =>
    le_ciSup (f := fun k : Fin n => |d n k - 1|) (Set.finite_range _).bddAbove k
  let fD : (n : ℕ) → Ω → ℝ := fun n ω =>
    ∑ k, (X n k i * X n k j) / (n : ℝ) *
      ((d n k - 1) * ((hcResidual P X y n k + hcCentered P y n k ω) -
        hcProjectedNoise P X y n ω k) ^ 2)
  change TendstoInProbability P fD (fun _ => 0)
  have hsq_int : ∀ n (k : Fin n), Integrable (fun ω =>
      ((hcResidual P X y n k + hcCentered P y n k ω) -
        hcProjectedNoise P X y n ω k) ^ 2) P := by
    intro n k
    have h := ((hcShift_memLp A1 n k).sub (hcProjected_memLp A1 n k)).integrable_sq
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp [Pi.sub_apply]
  have hsq_bd : ∀ n (k : Fin n), ∫ ω,
      ((hcResidual P X y n k + hcCentered P y n k ω) -
        hcProjectedNoise P X y n ω k) ^ 2 ∂P ≤
      2 * (A1.β + A1.Cᵣ ^ 2) + 2 * (A1.β * maxLev (X n)) := by
    intro n k
    have hstep : ∫ ω, ((hcResidual P X y n k + hcCentered P y n k ω) -
          hcProjectedNoise P X y n ω k) ^ 2 ∂P ≤
        ∫ ω, (2 * (hcResidual P X y n k + hcCentered P y n k ω) ^ 2 +
          2 * hcProjectedNoise P X y n ω k ^ 2) ∂P :=
      integral_mono (hsq_int n k)
        (((hcShift_sq_integrable A1 n k).const_mul 2).add
          ((hcProjected_sq_integrable A1 n k).const_mul 2))
        fun ω => sub_sq_le_two_add_two _ _
    rw [integral_add ((hcShift_sq_integrable A1 n k).const_mul 2)
      ((hcProjected_sq_integrable A1 n k).const_mul 2), integral_const_mul,
      integral_const_mul, hcShift_sq_integral_eq A1 n k] at hstep
    linarith [A1.hvar_ub n k, hcResidual_sq_le A1 n k,
      hcProjected_sq_integral_le A1 n k]
  have hterm_int : ∀ n (k : Fin n), Integrable (fun ω =>
      (X n k i * X n k j) / (n : ℝ) * ((d n k - 1) *
        ((hcResidual P X y n k + hcCentered P y n k ω) -
          hcProjectedNoise P X y n ω k) ^ 2)) P := fun n k =>
    ((hsq_int n k).const_mul _).const_mul _
  have hfD_int : ∀ n, Integrable (fD n) P := fun n =>
    integrable_finsetSum _ fun k _ => hterm_int n k
  let δD : ℕ → ℝ := fun n => A1.C *
    (D n * (2 * (A1.β + A1.Cᵣ ^ 2) + 2 * (A1.β * maxLev (X n))))
  have hfD_bd : ∀ n, ∫ ω, |fD n ω| ∂P ≤ δD n := by
    intro n
    have habs_le : ∀ ω, |fD n ω| ≤ ∑ k, |X n k i * X n k j| / (n : ℝ) *
        (D n * ((hcResidual P X y n k + hcCentered P y n k ω) -
          hcProjectedNoise P X y n ω k) ^ 2) := by
      intro ω
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      calc
        |(X n k i * X n k j) / (n : ℝ) * ((d n k - 1) *
            ((hcResidual P X y n k + hcCentered P y n k ω) -
              hcProjectedNoise P X y n ω k) ^ 2)| =
            |X n k i * X n k j| / (n : ℝ) * (|d n k - 1| *
              ((hcResidual P X y n k + hcCentered P y n k ω) -
                hcProjectedNoise P X y n ω k) ^ 2) := by
          rw [abs_mul, abs_mul, abs_div, Nat.abs_cast,
            abs_of_nonneg (sq_nonneg ((hcResidual P X y n k + hcCentered P y n k ω) -
              hcProjectedNoise P X y n ω k))]
        _ ≤ |X n k i * X n k j| / (n : ℝ) * (D n *
            ((hcResidual P X y n k + hcCentered P y n k ω) -
              hcProjectedNoise P X y n ω k) ^ 2) := by
          gcongr
          exact hDk n k
    have hint_dom : Integrable (fun ω => ∑ k, |X n k i * X n k j| / (n : ℝ) *
        (D n * ((hcResidual P X y n k + hcCentered P y n k ω) -
          hcProjectedNoise P X y n ω k) ^ 2)) P :=
      integrable_finsetSum _ fun k _ => ((hsq_int n k).const_mul _).const_mul _
    have hstep := integral_mono (hfD_int n).abs hint_dom habs_le
    have hsum_int : ∫ ω, (∑ k, |X n k i * X n k j| / (n : ℝ) *
          (D n * ((hcResidual P X y n k + hcCentered P y n k ω) -
            hcProjectedNoise P X y n ω k) ^ 2)) ∂P =
        ∑ k, |X n k i * X n k j| / (n : ℝ) * (D n *
          ∫ ω, ((hcResidual P X y n k + hcCentered P y n k ω) -
            hcProjectedNoise P X y n ω k) ^ 2 ∂P) := by
      rw [integral_finsetSum _ fun k _ => ((hsq_int n k).const_mul _).const_mul _]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul, integral_const_mul]
    rw [hsum_int] at hstep
    refine hstep.trans ?_
    calc
      ∑ k, |X n k i * X n k j| / (n : ℝ) * (D n *
          ∫ ω, ((hcResidual P X y n k + hcCentered P y n k ω) -
            hcProjectedNoise P X y n ω k) ^ 2 ∂P) ≤
          ∑ k, |X n k i * X n k j| / (n : ℝ) *
            (D n * (2 * (A1.β + A1.Cᵣ ^ 2) + 2 * (A1.β * maxLev (X n)))) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hsq_bd n k) (hD_nn n)) (by positivity)
      _ = (∑ k, |X n k i * X n k j| / (n : ℝ)) *
          (D n * (2 * (A1.β + A1.Cᵣ ^ 2) + 2 * (A1.β * maxLev (X n)))) := by
        rw [Finset.sum_mul]
      _ ≤ A1.C * (D n *
          (2 * (A1.β + A1.Cᵣ ^ 2) + 2 * (A1.β * maxLev (X n)))) := by
        refine mul_le_mul_of_nonneg_right (A1.sum_abs_rowProd_div_le n i j) ?_
        refine mul_nonneg (hD_nn n) (add_nonneg ?_ ?_)
        · exact mul_nonneg (by norm_num) (add_nonneg A1.hβ_nonneg (sq_nonneg _))
        · exact mul_nonneg (by norm_num)
            (mul_nonneg A1.hβ_nonneg (maxLev_nonneg (X n)))
      _ = δD n := rfl
  have hδD_lim : Tendsto δD atTop (𝓝 0) := by
    have hbr : Tendsto (fun n => 2 * (A1.β + A1.Cᵣ ^ 2) +
        2 * (A1.β * maxLev (X n))) atTop
        (𝓝 (2 * (A1.β + A1.Cᵣ ^ 2) + 2 * (A1.β * 0))) :=
      tendsto_const_nhds.add ((A1.hlev.const_mul A1.β).const_mul 2)
    have h := (hd.mul hbr).const_mul A1.C
    simpa [δD, D] using h
  exact TendstoInProbability.of_integral_abs_le
    (fun n => memLp_one_iff_integrable.mpr (hfD_int n)) hfD_bd hδD_lim

/-- Under the assumption bundle, each entry of `M̂ₙᵈ` for any multiplier family
with `⨆ₖ |dₙₖ − 1| → 0`  converges in probability to the entry of `Mₙ + Rₙ`. -/
theorem hcGram_consistent
    (A1 : AssumptionBundle P X y)
    (d : (n : ℕ) → Fin n → ℝ)
    (hd : Tendsto (fun n => ⨆ k : Fin n, |d n k - 1|) atTop (𝓝 0))
    (i j : Fin p) :
    TendstoInProbability P
      (fun n ω => hcGram (X n) (d n) (fun k => y n k ω) i j)
      (fun n => hcTarget P (X n) (y n) i j) := by
  rw [tendstoInProbability_iff_sub]
  have hsum := (((hcTermA_tendsto A1 i j).add (hcTermB_tendsto A1 i j)).add
    (hcTermC_tendsto A1 i j)).add (hcTermD_tendsto A1 d hd i j)
  refine hsum.congr fun n ω => ?_
  exact (hcGram_entry_error_decomp (P := P) (X := X) (y := y) n (d n) ω i j).symm

end HCConsistency


section CorrectionTermLimits

variable {p : ℕ} {P : Measure Ω} {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ}
  {y : (n : ℕ) → Fin n → Ω → ℝ}

/-- The constant multiplier family `dᵢ = 1` (HC0) trivially converges to `1`. -/
lemma hc0_multiplier_tendsto :
    Tendsto (fun n => ⨆ _ : Fin n, |(1 : ℝ) - 1|) atTop (𝓝 0) := by
  have hzero : ∀ n : ℕ, (⨆ _ : Fin n, |(1 : ℝ) - 1|) = 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      exact Real.iSup_of_isEmpty _
    · have : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
      simp
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  exact hconst.congr fun n => (hzero n).symm

/-- The HC1 multiplier family converges to `1` uniformly: `⨆ᵢ |n/(n−p) − 1| → 0`. -/
lemma hc1_multiplier_tendsto (p : ℕ) :
    Tendsto (fun n => ⨆ _ : Fin n, |hc1Correction n p - 1|) atTop (𝓝 0) := by
  have hupper : ∀ᶠ n in atTop,
      (⨆ _ : Fin n, |hc1Correction n p - 1|) ≤ (2 * p : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 * p + 1)] with n hn
    have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 (2 * p)) hn
    have hnp : (p : ℝ) < (n : ℝ) := by
      have : p < n := by omega
      exact_mod_cast this
    have hnp' : (0 : ℝ) < (n : ℝ) - (p : ℝ) := by linarith
    have h2p : 2 * (p : ℝ) + 1 ≤ (n : ℝ) := by
      have hcast : ((2 * p + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast at hcast
      linarith
    have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
    rw [ciSup_const]
    have hcorr : hc1Correction n p - 1 = (p : ℝ) / ((n : ℝ) - (p : ℝ)) := by
      rw [hc1Correction, div_sub_one hnp'.ne']
      congr 1
      ring
    rw [hcorr, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hnp'.le)]
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := hn1
      exact_mod_cast this
    rw [div_le_div_iff₀ hnp' hn_pos]
    have hp_nn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
    nlinarith [hp_nn, h2p]
  have hlower : ∀ᶠ (n : ℕ) in atTop,
      (0 : ℝ) ≤ ⨆ _ : Fin n, |hc1Correction n p - 1| :=
    Eventually.of_forall fun n => Real.iSup_nonneg fun _ => abs_nonneg _
  have hlim : Tendsto (fun n : ℕ => (2 * p : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    hlower hupper

/-- Any correction `corr` with `|corr(h) − 1| ≤ K·h` for `0 ≤ h < 1/2`
has multipliers converging to `1` uniformly under the bundle. -/
lemma AssumptionBundle.correction_multiplier_tendsto
    (A1 : AssumptionBundle P X y) (corr : ℝ → ℝ) (K : ℝ) (hK_nonneg : 0 ≤ K)
    (hbd : ∀ h, 0 ≤ h → h < 1 / 2 → |corr h - 1| ≤ K * h) :
    Tendsto (fun n => ⨆ i : Fin n, |corr (leverage (X n) i) - 1|) atTop (𝓝 0) := by
  have hupper : ∀ᶠ n in atTop,
      (⨆ i : Fin n, |corr (leverage (X n) i) - 1|) ≤ K * maxLev (X n) := by
    filter_upwards [A1.hlev.eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 2), eventually_gt_atTop 0] with n hn hpos
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hpos
    refine ciSup_le fun i => ?_
    have hle := leverage_le_maxLev (X n) i
    calc |corr (leverage (X n) i) - 1|
        ≤ K * leverage (X n) i :=
          hbd _ (leverage_nonneg (X n) i)
            (lt_of_le_of_lt hle hn)
      _ ≤ K * maxLev (X n) := mul_le_mul_of_nonneg_left hle hK_nonneg
  have hlower : ∀ᶠ (n : ℕ) in atTop,
      (0 : ℝ) ≤ ⨆ i : Fin n, |corr (leverage (X n) i) - 1| :=
    Eventually.of_forall fun n => Real.iSup_nonneg fun _ => abs_nonneg _
  have hlim : Tendsto (fun n => K * maxLev (X n)) atTop (𝓝 0) := by
    simpa using A1.hlev.const_mul K
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    hlower hupper

/-- The HC2 multiplier family converges to `1` uniformly under the assumption bundle. -/
lemma AssumptionBundle.hc2_multiplier_tendsto (A1 : AssumptionBundle P X y) :
    Tendsto (fun n => ⨆ i : Fin n, |hc2Correction (X n) i - 1|) atTop (𝓝 0) := by
  refine A1.correction_multiplier_tendsto (fun h => (1 - h)⁻¹) 2 (by norm_num)
    fun h hnn hlt => ?_
  have h1h : (0 : ℝ) < 1 - h := by linarith
  have hcorr : (1 - h)⁻¹ - 1 = h / (1 - h) := by
    field_simp
    ring
  rw [hcorr, abs_of_nonneg (div_nonneg hnn h1h.le), div_le_iff₀ h1h]
  nlinarith [mul_nonneg hnn (by linarith : (0 : ℝ) ≤ 1 - 2 * h)]

/-- The HC3 multiplier family converges to `1` uniformly under the assumption bundle. -/
lemma AssumptionBundle.hc3_multiplier_tendsto (A1 : AssumptionBundle P X y) :
    Tendsto (fun n => ⨆ i : Fin n, |hc3Correction (X n) i - 1|) atTop (𝓝 0) := by
  refine A1.correction_multiplier_tendsto (fun h => ((1 - h)⁻¹) ^ 2) 8
    (by norm_num) fun h hnn hlt => ?_
  have h1h : (0 : ℝ) < 1 - h := by linarith
  have hquarter : (1 : ℝ) / 4 ≤ (1 - h) ^ 2 := by nlinarith
  have hcorr : ((1 - h)⁻¹) ^ 2 - 1 = h * (2 - h) / (1 - h) ^ 2 := by
    field_simp [h1h.ne']
    ring
  have hnum_nn : 0 ≤ h * (2 - h) := by nlinarith
  rw [hcorr, abs_of_nonneg (div_nonneg hnum_nn (by positivity)),
    div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hquarter hnn, sq_nonneg h]

end CorrectionTermLimits


section MainResults

variable {p : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ} {y : (n : ℕ) → Fin n → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- If the outer matrix `Bₙ` has uniformly bounded entries and `Vₙ → Tₙ` entrywise in
probability, then `Bₙ Vₙ Bₙ → Bₙ Tₙ Bₙ`. -/
theorem sandwich_entry_tendsto
    (B : (n : ℕ) → Matrix (Fin p) (Fin p) ℝ) (β : ℝ) (hβ_nonneg : 0 ≤ β)
    (hB_ub : ∀ n a b, |B n a b| ≤ β)
    {V : (n : ℕ) → Ω → Matrix (Fin p) (Fin p) ℝ}
    {T : (n : ℕ) → Matrix (Fin p) (Fin p) ℝ}
    (hV_lim : ∀ a b, TendstoInProbability P (fun n ω => V n ω a b)
      (fun n => T n a b))
    (i j : Fin p) :
    TendstoInProbability P (fun n ω => sandwich (B n) (V n ω) i j)
      (fun n => sandwich (B n) (T n) i j) := by
  classical
  rw [tendstoInProbability_iff_sub]
  have hentry : ∀ n ω, sandwich (B n) (V n ω) i j - sandwich (B n) (T n) i j
      = ∑ b, ∑ a, B n i a * (V n ω a b - T n a b) * B n b j := by
    intro n ω
    have hmat : sandwich (B n) (V n ω) - sandwich (B n) (T n)
        = B n * (V n ω - T n) * B n := by
      rw [sandwich, sandwich, Matrix.mul_sub, Matrix.sub_mul]
    have h1 : sandwich (B n) (V n ω) i j - sandwich (B n) (T n) i j
        = (B n * (V n ω - T n) * B n) i j := by
      rw [← Matrix.sub_apply, hmat]
    rw [h1, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.sub_apply]
  have hterm : ∀ b a : Fin p, TendstoInProbability P
      (fun n ω => B n i a * (V n ω a b - T n a b) * B n b j)
      (fun _ => 0) := by
    intro b a
    have hab := tendstoInProbability_iff_sub.mp (hV_lim a b)
    have hscaled := hab.const_mul (β ^ 2 + 1)
    refine TendstoInProbability.of_abs_le (fun n ω => ?_) hscaled
    have h1 : |B n i a * (V n ω a b - T n a b) * B n b j|
        = |B n i a| * |V n ω a b - T n a b| * |B n b j| := by
      rw [abs_mul, abs_mul]
    have h2 : |B n i a| * |V n ω a b - T n a b| * |B n b j|
        ≤ β * |V n ω a b - T n a b| * β := by
      gcongr
      · exact hB_ub n i a
      · exact hB_ub n b j
    have h3 : β * |V n ω a b - T n a b| * β
        ≤ |(β ^ 2 + 1) * (V n ω a b - T n a b)| := by
      rw [abs_mul]
      have hβ2 : |(β ^ 2 + 1 : ℝ)| = β ^ 2 + 1 := by
        rw [abs_of_pos]
        positivity
      rw [hβ2]
      nlinarith [abs_nonneg (V n ω a b - T n a b)]
    rw [h1]
    exact le_trans h2 h3
  have hsum : TendstoInProbability P
      (fun n ω => ∑ b, ∑ a, B n i a * (V n ω a b - T n a b) * B n b j)
      (fun _ => 0) := by
    refine TendstoInProbability.finsetSum Finset.univ fun b _ => ?_
    exact TendstoInProbability.finsetSum Finset.univ fun a _ => hterm b a
  exact hsum.congr fun n ω => (hentry n ω).symm

/-- For any admissible multiplier family, `Sₙ⁻¹ M̂ₙᵈ Sₙ⁻¹ → Sₙ⁻¹ (Mₙ+Rₙ) Sₙ⁻¹`
entrywise in probability. -/
theorem hcGram_sandwich_consistent
    (A1 : AssumptionBundle P X y)
    (d : (n : ℕ) → Fin n → ℝ)
    (hd_lim : Tendsto (fun n => ⨆ k : Fin n, |d n k - 1|) atTop (𝓝 0))
    (i j : Fin p) :
    TendstoInProbability P
      (fun n ω => hcSandwich (X n) (d n) (fun k => y n k ω) i j)
      (fun n => sandwichTarget P (X n) (y n) i j) := by
  refine sandwich_entry_tendsto (fun n => (sampleGram (X n))⁻¹) (1 / A1.c)
    (div_nonneg zero_le_one A1.hc_pos.le) (fun n a b => ?_)
    (fun a b => hcGram_consistent A1 d hd_lim a b) i j
  show |(sampleGram (X n))⁻¹ a b| ≤ 1 / A1.c
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simpa [Matrix.inv_zero] using div_nonneg zero_le_one A1.hc_pos.le
  · exact inv_entry_ub_of_spectral_lb (sampleGram (X n)) A1.c A1.hc_pos
      (sampleGram_transpose _) (A1.hGram_spectral_lb n hpos) a b

/-- HC0 sandwich consistency. -/
theorem hc0_sandwich_consistent
    (A1 : AssumptionBundle P X y)
    (i j : Fin p) :
    TendstoInProbability P
      (fun n ω => hcSandwich (X n) (fun _ => 1) (fun k => y n k ω) i j)
      (fun n => sandwichTarget P (X n) (y n) i j) :=
  hcGram_sandwich_consistent A1 (fun _ _ => (1 : ℝ))
    hc0_multiplier_tendsto i j

/-- HC1 sandwich consistency. -/
theorem hc1_sandwich_consistent
    (A1 : AssumptionBundle P X y)
    (i j : Fin p) :
    TendstoInProbability P
      (fun n ω => hcSandwich (X n) (fun _ => hc1Correction n p)
        (fun k => y n k ω) i j)
      (fun n => sandwichTarget P (X n) (y n) i j) :=
  hcGram_sandwich_consistent A1
    (fun n _ => hc1Correction n p) (hc1_multiplier_tendsto p) i j

/-- HC2 sandwich consistency. -/
theorem hc2_sandwich_consistent
    (A1 : AssumptionBundle P X y)
    (i j : Fin p) :
    TendstoInProbability P
      (fun n ω => hcSandwich (X n) (hc2Correction (X n))
        (fun k => y n k ω) i j)
      (fun n => sandwichTarget P (X n) (y n) i j) :=
  hcGram_sandwich_consistent A1
    (fun n => hc2Correction (X n)) A1.hc2_multiplier_tendsto i j

/-- HC3 sandwich consistency. -/
theorem hc3_sandwich_consistent
    (A1 : AssumptionBundle P X y)
    (i j : Fin p) :
    TendstoInProbability P
      (fun n ω => hcSandwich (X n) (hc3Correction (X n))
        (fun k => y n k ω) i j)
      (fun n => sandwichTarget P (X n) (y n) i j) :=
  hcGram_sandwich_consistent A1
    (fun n => hc3Correction (X n)) A1.hc3_multiplier_tendsto i j

end MainResults


end

end LinearModel
end LeanPool
