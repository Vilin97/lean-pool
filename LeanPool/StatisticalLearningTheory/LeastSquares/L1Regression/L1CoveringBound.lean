/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import LeanPool.StatisticalLearningTheory.LeastSquares.L1Regression.L1DesignMatrix
import LeanPool.StatisticalLearningTheory.LeastSquares.Localization
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Covering Number Bounds for ℓ₁-Constrained Linear Predictors

This file provides covering number bounds for the ℓ₁-constrained linear predictor image
in EmpiricalSpace using Maurey's empirical method.

The main result is:
  N(ε, l1BallImage x R) ≤ (2d + 1)^⌈R²/ε²⌉

where `l1BallImage x R = {Xθ/√n : ‖θ‖₁ ≤ R}`.

## Main Definitions

* `empColumn` - Column j of design matrix as EmpiricalSpace vector
* `scaledSignedColumn` - R · (±1) · X_j / √n
* `maureyVec` - Random variable for Maurey's method
* `maureyAvg` - Empirical average of k samples
* `maureyNet` - The ε-net of all k-averages
* `l1BallImage` - The set {Xθ/√n : ‖θ‖₁ ≤ R}

## Main Results

* `maureyNet_card_le` - Net cardinality bound: |maureyNet| ≤ (2d+1)^k
* `exists_maureyAvg_close` - Maurey's existence lemma
* `l1BallImage_coveringNumber_le` - Main covering number bound
* `l1LocalizedImage_coveringNumber_le` - The corresponding localized-image bound

## References

* Maurey's empirical method for covering numbers of convex hulls
* [Vershynin, High-Dimensional Probability] Chapter 4

-/

noncomputable section

namespace LeanPool.StatisticalLearningTheory

open MeasureTheory Finset BigOperators Real ProbabilityTheory Metric Set
open scoped NNReal ENNReal

namespace LeastSquares

variable {n d : ℕ}

/-! ## Basic Definitions for Maurey's Method -/

/-- Column j of design matrix as EmpiricalSpace vector: (X_j)_i = (x_i)_j -/
noncomputable def empColumn (x : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    EmpiricalSpace n :=
  fun i => (x i) j

/-- Coordinate access for an empirical design column. -/
private lemma empColumn_apply (x : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin d) (i : Fin n) :
    empColumn x j i = (x i) j := rfl

/-- Scaled signed column: R · (±1) · X_j / √n in EmpiricalSpace -/
noncomputable def scaledSignedColumn (x : Fin n → EuclideanSpace ℝ (Fin d))
    (R : ℝ) (j : Fin d) (sign : Bool) : EmpiricalSpace n :=
  fun i => R * (if sign then 1 else -1) / Real.sqrt n * empColumn x j i

/-- Random variable for Maurey's method in EmpiricalSpace -/
noncomputable def maureyVec (x : Fin n → EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    Option (Fin d × Bool) → EmpiricalSpace n
  | none => 0
  | some (j, b) => scaledSignedColumn x R j b

/-- The empty Maurey sample is zero. -/
@[simp]
private lemma maureyVec_none (x : Fin n → EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    maureyVec x R none = 0 := rfl

/-- A nonempty Maurey sample is its scaled signed column. -/
private lemma maureyVec_some (x : Fin n → EuclideanSpace ℝ (Fin d))
    (R : ℝ) (j : Fin d) (b : Bool) :
    maureyVec x R (some (j, b)) = scaledSignedColumn x R j b := rfl

/-- Empirical average of k samples in EmpiricalSpace -/
noncomputable def maureyAvg (x : Fin n → EuclideanSpace ℝ (Fin d)) (R : ℝ) (k : ℕ)
    (f : Fin k → Option (Fin d × Bool)) : EmpiricalSpace n :=
  fun i => (1 / k : ℝ) * ∑ l : Fin k, maureyVec x R (f l) i

/-- The ε-net: all possible k-averages -/
noncomputable def maureyNet (x : Fin n → EuclideanSpace ℝ (Fin d)) (R : ℝ) (k : ℕ) :
    Finset (EmpiricalSpace n) := by
  classical
  exact Finset.univ.image (maureyAvg x R k)

/-- The ℓ₁ ball image in EmpiricalSpace: {Xθ/√n : ‖θ‖₁ ≤ R} -/
def l1BallImage (x : Fin n → EuclideanSpace ℝ (Fin d)) (R : ℝ) : Set (EmpiricalSpace n) :=
  {v | ∃ θ : EuclideanSpace ℝ (Fin d), l1norm θ ≤ R ∧
       v = fun i => (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i)}

/-! ## Net Cardinality Bound -/

/-- Net cardinality bound: |maureyNet| ≤ (2d + 1)^k -/
lemma maureyNet_card_le (x : Fin n → EuclideanSpace ℝ (Fin d)) (R : ℝ) (k : ℕ) :
    (maureyNet x R k).card ≤ (2 * d + 1) ^ k := by
  classical
  have hle : (maureyNet x R k).card ≤
      (Finset.univ : Finset (Fin k → Option (Fin d × Bool))).card := by
    simpa [maureyNet] using (Finset.card_image_le : (Finset.univ.image (maureyAvg x R k)).card ≤ _)
  have hcardS : Fintype.card (Option (Fin d × Bool)) = 2 * d + 1 := by
    simp [Fintype.card_option, Fintype.card_prod, Fintype.card_bool,
      Nat.mul_comm, Nat.add_comm]
  have hcard_univ :
      (Finset.univ : Finset (Fin k → Option (Fin d × Bool))).card = (2 * d + 1) ^ k := by
    simp [hcardS]
  simpa [hcard_univ] using hle

/-! ## Measurable Space for Option (Fin d × Bool) -/

instance instMeasurableSpaceOptionFinProdBool (d : ℕ) : MeasurableSpace (Option (Fin d × Bool)) := ⊤
instance instMeasurableSingletonClassOptionFinProdBool (d : ℕ) :
    MeasurableSingletonClass (Option (Fin d × Bool)) :=
  ⟨fun _ => trivial⟩

/-! ## Probability Distribution for Maurey's Method -/

/-- Probability distribution on Option (Fin d × Bool) based on θ.
For θ with ‖θ‖₁ ≤ R, we assign:
- P(some (j, sign(θ_j))) = |θ_j| / R
- P(none) = 1 - ‖θ‖₁/R -/
noncomputable def maureyPMF (θ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (hθ : l1norm θ ≤ R) :
    PMF (Option (Fin d × Bool)) := by
  classical
  refine PMF.ofFintype (fun o : Option (Fin d × Bool) => ?_) ?_
  · cases o with
    | none => exact ENNReal.ofReal (1 - l1norm θ / R)
    | some jb =>
      let (j, b) := jb
      exact if b = decide (0 ≤ θ j) then ENNReal.ofReal (‖θ j‖ / R) else 0
  · -- sum to 1
    have hl1nonneg : 0 ≤ l1norm θ := Finset.sum_nonneg (fun i _ => norm_nonneg (θ i))
    have hR : 0 ≤ R := le_trans hl1nonneg hθ
    have hpos : 0 ≤ l1norm θ / R := by
      by_cases hR0 : R = 0
      · simp [hR0]
      · have hRpos : 0 < R := lt_of_le_of_ne hR (fun h => hR0 h.symm)
        exact div_nonneg hl1nonneg (le_of_lt hRpos)
    have hle : l1norm θ / R ≤ 1 := by
      by_cases hR0 : R = 0
      · simp [hR0]
      · have hRpos : 0 < R := lt_of_le_of_ne hR (fun h => hR0 h.symm)
        exact (div_le_one hRpos).2 hθ
    have hnonneg : 0 ≤ 1 - l1norm θ / R := by linarith
    rw [Fintype.sum_option]
    by_cases hR0 : R = 0
    · -- R = 0 case: l1norm θ = 0
      have hl1zero : l1norm θ = 0 := by
        have : l1norm θ ≤ 0 := by simp only [hR0] at hθ; exact hθ
        linarith
      have hcoord_zero : ∀ j : Fin d, ‖θ j‖ = 0 := by
        intro j
        have hsum : ∑ i, ‖θ i‖ = 0 := hl1zero
        exact Finset.sum_eq_zero_iff_of_nonneg (fun i _ => norm_nonneg _) |>.1 hsum j (by simp)
      simp only [hR0, div_zero, sub_zero, ENNReal.ofReal_one]
      have hsum_zero' : ∑ jb : Fin d × Bool,
          (if jb.2 = decide (0 ≤ θ jb.1) then ENNReal.ofReal 0 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro jb _
        simp only [ENNReal.ofReal_zero]
        split_ifs <;> rfl
      simp only [hsum_zero', add_zero]
    · -- R > 0 case
      have hRpos : 0 < R := lt_of_le_of_ne hR (fun h => hR0 h.symm)
      have hsum_some : ∑ jb : Fin d × Bool,
          (if jb.2 = decide (0 ≤ θ jb.1) then ENNReal.ofReal (‖θ jb.1‖ / R) else 0) =
          ∑ j : Fin d, ENNReal.ofReal (‖θ j‖ / R) := by
        rw [Fintype.sum_prod_type]
        congr 1
        ext j
        simp only [Fintype.sum_bool, Bool.true_eq, Bool.false_eq]
        by_cases hj : 0 ≤ θ j
        · simp [hj]
        · simp [hj]
      rw [hsum_some]
      have hcoord_le : ∀ j : Fin d, ‖θ j‖ / R ≤ 1 := fun j => by
        have hjle : ‖θ j‖ ≤ l1norm θ := by
          simp only [l1norm]
          exact Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ j)
        exact (div_le_one hRpos).2 (le_trans hjle hθ)
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => div_nonneg (norm_nonneg _) (le_of_lt hRpos))]
      rw [← ENNReal.ofReal_add hnonneg (Finset.sum_nonneg (fun j _ =>
        div_nonneg (norm_nonneg _) (le_of_lt hRpos)))]
      have hsum_real : (1 - l1norm θ / R) + ∑ j, ‖θ j‖ / R = 1 := by
        have : ∑ j : Fin d, ‖θ j‖ / R = l1norm θ / R := by
          simp only [l1norm, Finset.sum_div]
        rw [this]
        ring
      rw [hsum_real, ENNReal.ofReal_one]

/-! ## Mean and Variance Lemmas -/

/-- Helper: the sign function for Maurey's method -/
noncomputable def maureySign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

lemma abs_mul_maureySign (x : ℝ) : |x| * maureySign x = x := by
  by_cases hx : 0 ≤ x
  · simp [maureySign, hx, abs_of_nonneg hx]
  · have hx' : x < 0 := lt_of_not_ge hx
    simp [maureySign, hx, abs_of_neg hx']

/-- Mean of maureyVec at coordinate i equals target_i = (1/√n) * ⟨θ, x_i⟩.
This is the unbiasedness property of Maurey's random variable. -/
lemma maureyPMF_mean_coord (x : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) (hθ : l1norm θ ≤ R) (i : Fin n) :
    ∫ o, maureyVec x R o i ∂(maureyPMF θ R hθ).toMeasure =
      (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i) := by
  classical
  rw [PMF.integral_eq_sum, Fintype.sum_option]
  simp only [maureyVec_none]
  rw [Fintype.sum_prod_type]
  simp only [smul_eq_mul, maureyVec_some, scaledSignedColumn, empColumn_apply]
  have hzero_apply : (0 : EmpiricalSpace n) i = 0 := rfl
  simp only [hzero_apply, mul_zero, zero_add]
  have hsum_eq : ∑ j : Fin d, ∑ b : Bool,
      (maureyPMF θ R hθ (some (j, b))).toReal *
          ((R * (if b then 1 else -1)) / Real.sqrt n * (x i) j) =
      ∑ j : Fin d, (‖θ j‖ / R) * (R / Real.sqrt n * maureySign (θ j) * (x i) j) := by
    congr 1
    ext j
    simp only [Fintype.sum_bool, maureyPMF, PMF.ofFintype_apply]
    by_cases hj : 0 ≤ θ j
    · -- θ j ≥ 0: only (j, true) contributes
      simp only [hj, decide_true, ↓reduceIte, ENNReal.toReal_ofReal
          (div_nonneg (norm_nonneg _) (le_of_lt hR)),
          Bool.false_eq_true, ENNReal.toReal_zero]
      have hsign : maureySign (θ j) = 1 := by simp [maureySign, hj]
      rw [hsign, zero_mul, add_zero]
      ring
    · -- θ j < 0: only (j, false) contributes
      simp only [hj, decide_false, Bool.false_eq_true, ↓reduceIte,
          Bool.true_eq_false, ENNReal.toReal_zero,
          ENNReal.toReal_ofReal (div_nonneg (norm_nonneg _) (le_of_lt hR))]
      have hsign : maureySign (θ j) = -1 := by simp [maureySign, hj]
      rw [hsign, zero_mul, zero_add]
      ring
  rw [hsum_eq]
  have hterm_eq : ∀ j : Fin d,
      (‖θ j‖ / R) * (R / Real.sqrt n * maureySign (θ j) * (x i) j) =
        (1 / Real.sqrt n) * θ j * (x i) j := fun j => by
    have hRne : R ≠ 0 := ne_of_gt hR
    field_simp
    rw [Real.norm_eq_abs, abs_mul_maureySign]
    ring
  simp_rw [hterm_eq, mul_assoc]
  rw [PiLp.inner_apply]
  have h_inner : ∀ a b : ℝ, inner ℝ a b = a * b := by
    intro a b
    change b * star a = a * b
    simp [mul_comm]
  simp only [h_inner]
  rw [← Finset.mul_sum]

/-- Sum of squared coordinates bound for empirical average -/
lemma maureyPMF_variance_bound (x : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) (hθ : l1norm θ ≤ R)
    (hcol : columnNormBound x) (hn : 0 < n) :
    ∫ o, ∑ i : Fin n, (maureyVec x R o i)^2 ∂(maureyPMF θ R hθ).toMeasure ≤ R * l1norm θ := by
  classical
  rw [PMF.integral_eq_sum, Fintype.sum_option]
  simp only [maureyVec_none, sq, smul_eq_mul]
  have hzero_term :
      (maureyPMF θ R hθ none).toReal *
          ∑ i : Fin n, (0 : EmpiricalSpace n) i * (0 : EmpiricalSpace n) i = 0 := by
    have h0 : ∀ i : Fin n, (0 : EmpiricalSpace n) i = 0 := fun _ => rfl
    simp only [h0, mul_zero, Finset.sum_const_zero, mul_zero]
  rw [hzero_term, zero_add]
  rw [Fintype.sum_prod_type]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (le_of_lt hn_pos)
  have hsum_eq : ∑ j : Fin d, ∑ b : Bool,
      (maureyPMF θ R hθ (some (j, b))).toReal *
        (∑ i : Fin n, (maureyVec x R (some (j, b)) i) * (maureyVec x R (some (j, b)) i)) =
      ∑ j : Fin d, (‖θ j‖ / R) * (R^2 / n * ∑ i : Fin n, ((x i) j)^2) := by
    congr 1
    ext j
    simp only [Fintype.sum_bool, maureyPMF, PMF.ofFintype_apply, maureyVec_some,
      scaledSignedColumn, empColumn_apply]
    by_cases hj : 0 ≤ θ j
    · simp only [hj, decide_true, ↓reduceIte, ENNReal.toReal_ofReal
        (div_nonneg (norm_nonneg _) (le_of_lt hR)),
        Bool.false_eq_true, ENNReal.toReal_zero, zero_mul, add_zero]
      congr 1
      have heach : ∀ i : Fin n, R / Real.sqrt n * (x i).ofLp j * (R / Real.sqrt n * (x i).ofLp j) =
                R^2 / n * ((x i).ofLp j)^2 := fun i => by
        rw [← sq, mul_pow, div_pow, hsqrt_sq]
      simp only [mul_one, heach, ← Finset.mul_sum]
    · simp only [hj, decide_false, Bool.false_eq_true, ↓reduceIte,
        Bool.true_eq_false, ENNReal.toReal_zero, zero_mul, zero_add,
        ENNReal.toReal_ofReal (div_nonneg (norm_nonneg _) (le_of_lt hR))]
      congr 1
      have heach : ∀ i : Fin n,
          -(R / Real.sqrt n) * (x i).ofLp j * (-(R / Real.sqrt n) * (x i).ofLp j) =
            R^2 / n * ((x i).ofLp j)^2 := fun i => by
        have hterm :
            -(R / Real.sqrt n) * (x i).ofLp j = -(R / Real.sqrt n * (x i).ofLp j) :=
          neg_mul _ _
        rw [hterm, neg_mul_neg, ← sq, mul_pow, div_pow, hsqrt_sq]
      simp only [mul_neg_one, neg_div]
      simp only [heach, ← Finset.mul_sum]
  rw [hsum_eq]
  have hcol_sq : ∀ j : Fin d, ∑ i : Fin n, ((x i) j)^2 ≤ n := fun j => by
    have h := hcol j
    rw [← designMatrixColumn_norm_sq]
    have hnorm_nonneg : 0 ≤ ‖designMatrixColumn x j‖ := norm_nonneg _
    have hsqrt_nonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
    have hsq_le : ‖designMatrixColumn x j‖^2 ≤ (Real.sqrt n)^2 :=
      sq_le_sq' (by linarith) h
    rw [Real.sq_sqrt (Nat.cast_nonneg n)] at hsq_le
    exact hsq_le
  calc ∑ j : Fin d, (‖θ j‖ / R) * (R^2 / n * ∑ i : Fin n, ((x i) j)^2)
      ≤ ∑ j : Fin d, (‖θ j‖ / R) * (R^2 / n * n) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left (hcol_sq j)
          exact div_nonneg (sq_nonneg R) (Nat.cast_nonneg n)
        · exact div_nonneg (norm_nonneg _) (le_of_lt hR)
    _ = ∑ j : Fin d, ‖θ j‖ * R := by
        congr 1
        ext j
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        have hR_ne : R ≠ 0 := ne_of_gt hR
        field_simp
    _ = R * l1norm θ := by
        rw [l1norm, Finset.mul_sum]
        congr 1
        ext j
        ring

private lemma maureyAvg_coordinate_variance_le
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d))
    {R : ℝ} (hR : 0 < R) (hθ : l1norm θ ≤ R) (k : ℕ) (hk : 0 < k) (i : Fin n) :
    ∫ f : Fin k → Option (Fin d × Bool),
        (maureyAvg x R k f i - (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i)) ^ 2
        ∂Measure.pi (fun _ : Fin k => (maureyPMF θ R hθ).toMeasure) ≤
      (1 / k : ℝ) * ∫ o, (maureyVec x R o i -
        (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i)) ^ 2
        ∂(maureyPMF θ R hθ).toMeasure := by
  classical
  let target_i := (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i)
  let μ : Measure (Option (Fin d × Bool)) := (maureyPMF θ R hθ).toMeasure
  let ν : Measure (Fin k → Option (Fin d × Bool)) := Measure.pi (fun _ : Fin k => μ)
  change ∫ f, (maureyAvg x R k f i - target_i) ^ 2 ∂ν ≤
    (1 / k : ℝ) * ∫ o, (maureyVec x R o i - target_i) ^ 2 ∂μ
  have hμprob : IsProbabilityMeasure μ := by simp only [μ]; infer_instance
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  have hmean_i := maureyPMF_mean_coord x θ hR hθ i
  have hE_single : ∫ o, maureyVec x R o i ∂μ = target_i := by
    simp only [μ, target_i, hmean_i]
  let Y := fun (l : Fin k) (f : Fin k → Option (Fin d × Bool)) =>
    maureyVec x R (f l) i - target_i
  have havg_eq : ∀ f, maureyAvg x R k f i - target_i =
      (k : ℝ)⁻¹ * ∑ l, Y l f := by
    intro f
    simp only [maureyAvg, Y, one_div]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp [hkne]
  simp_rw [havg_eq]
  have hsq_eq : ∀ f, ((k : ℝ)⁻¹ * ∑ l, Y l f) ^ 2 =
      (k : ℝ)⁻¹ ^ 2 * (∑ l, Y l f) ^ 2 := fun f => by ring
  simp_rw [hsq_eq]
  rw [MeasureTheory.integral_const_mul]
  have hexpand : ∀ f, (∑ l, Y l f) ^ 2 = ∑ l₁, ∑ l₂, Y l₁ f * Y l₂ f := by
    intro f
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hexpand]
  rw [MeasureTheory.integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [MeasureTheory.integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  have hindep : ProbabilityTheory.iIndepFun (fun l f => Y l f) ν := by
    simp only [Y]
    have hμprob' : ∀ _ : Fin k, IsProbabilityMeasure μ := fun _ => hμprob
    let g : (l : Fin k) → Option (Fin d × Bool) → ℝ :=
      fun _ o => maureyVec x R o i - target_i
    have hg_meas : ∀ l, Measurable (g l) := fun _ => measurable_of_countable _
    have hid := @ProbabilityTheory.iIndepFun_pi (Fin k) _
      (fun _ => Option (Fin d × Bool)) _ (fun _ => μ) hμprob'
      (fun _ => Option (Fin d × Bool)) _ (fun _ => id)
      (fun _ => measurable_id.aemeasurable)
    simp only [id_eq] at hid
    have hcomp := hid.comp g hg_meas
    simp only [g] at hcomp
    exact hcomp
  have hY_mean_zero : ∀ l, ∫ f, Y l f ∂ν = 0 := by
    intro l
    simp only [Y]
    have hmeas : AEStronglyMeasurable (fun o : Option (Fin d × Bool) =>
        maureyVec x R o i - target_i) μ :=
      Measurable.aestronglyMeasurable (measurable_of_countable _)
    have heq := MeasureTheory.integral_comp_eval (μ := fun _ : Fin k => μ) (i := l) hmeas
    simp only [μ, ν] at heq ⊢
    rw [heq, MeasureTheory.integral_sub Integrable.of_finite Integrable.of_finite]
    rw [hmean_i, MeasureTheory.integral_const]
    simp only [target_i, smul_eq_mul, Measure.real]
    have hprob : ((maureyPMF θ R hθ).toMeasure Set.univ).toReal = 1 := by
      have hμ_prob : IsProbabilityMeasure (maureyPMF θ R hθ).toMeasure := by infer_instance
      rw [hμ_prob.measure_univ, ENNReal.toReal_one]
    rw [hprob, one_mul, sub_self]
  have hcross : ∀ l₁ l₂, l₁ ≠ l₂ → ∫ f, Y l₁ f * Y l₂ f ∂ν = 0 := by
    intro l₁ l₂ hne
    have hpair := hindep.indepFun hne
    have hmeas_1 : AEStronglyMeasurable (Y l₁) ν :=
      Measurable.aestronglyMeasurable (measurable_of_countable _)
    have hmeas_2 : AEStronglyMeasurable (Y l₂) ν :=
      Measurable.aestronglyMeasurable (measurable_of_countable _)
    rw [ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hpair hmeas_1 hmeas_2]
    rw [hY_mean_zero l₁, hY_mean_zero l₂, mul_zero]
  have hdiag : ∀ l, ∫ f, Y l f * Y l f ∂ν =
      ∫ o, (maureyVec x R o i - target_i) ^ 2 ∂μ := by
    intro l
    simp only [Y]
    have hmeas : AEStronglyMeasurable (fun o : Option (Fin d × Bool) =>
        (maureyVec x R o i - target_i) ^ 2) μ :=
      Measurable.aestronglyMeasurable (measurable_of_countable _)
    have heq := MeasureTheory.integral_comp_eval (μ := fun _ : Fin k => μ) (i := l) hmeas
    simp only [μ, ν] at heq ⊢
    convert heq using 2
    ext f
    ring
  have hsum_diag : ∑ l₁ : Fin k, ∑ l₂ : Fin k, ∫ f, Y l₁ f * Y l₂ f ∂ν =
      ∑ l : Fin k, ∫ o, (maureyVec x R o i - target_i) ^ 2 ∂μ := by
    congr 1
    ext l₁
    rw [Finset.sum_eq_single l₁]
    · exact hdiag l₁
    · intro l₂ _ hne
      exact hcross l₁ l₂ (Ne.symm hne)
    · intro h
      exact (h (Finset.mem_univ l₁)).elim
  rw [hsum_diag, Finset.sum_const, Finset.card_fin]
  have halg : ((k : ℝ)⁻¹) ^ 2 *
      (↑k * ∫ o, (maureyVec x R o i - target_i) ^ 2 ∂μ) =
      (1 / k : ℝ) * ∫ o, (maureyVec x R o i - target_i) ^ 2 ∂μ := by
    field_simp
  rw [nsmul_eq_mul, halg]

/-! ## Maurey's Existence Lemma -/

/-- Product PMF weight: the probability of sample configuration f under the product PMF.
This is Π_{l < k} P(f l) where P = maureyPMF θ R. -/
noncomputable def productPMFWeight (θ : EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (hθ : l1norm θ ≤ R) (k : ℕ) :
    (Fin k → Option (Fin d × Bool)) → ℝ≥0∞ :=
  fun f => ∏ l : Fin k, (maureyPMF θ R hθ) (f l)

/-- The product PMF weights sum to 1 (it's a valid PMF). -/
lemma productPMFWeight_sum_eq_one (θ : EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (hθ : l1norm θ ≤ R) (k : ℕ) :
    ∑ f : Fin k → Option (Fin d × Bool), productPMFWeight θ R hθ k f = 1 := by
  unfold productPMFWeight
  rw [← Fintype.sum_pow]
  have hmaureySum : ∑ o, (maureyPMF θ R hθ) o = 1 := by
    have htsum := PMF.tsum_coe (maureyPMF θ R hθ)
    have : ∑' (a : Option (Fin d × Bool)), (maureyPMF θ R hθ) a = ∑ a, (maureyPMF θ R hθ) a := by
      apply tsum_eq_sum
      intro b hb
      exact (hb (Finset.mem_univ b)).elim
    rwa [this] at htsum
  rw [hmaureySum]
  exact one_pow k

private lemma exists_productPMFWeight_toReal_pos
    (θ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) (hθ : l1norm θ ≤ R) (k : ℕ) :
    ∃ f : Fin k → Option (Fin d × Bool),
      (productPMFWeight θ R hθ k f).toReal > 0 := by
  classical
  by_cases hθR : l1norm θ < R
  · use fun _ => none
    have hPnone : 0 < (maureyPMF θ R hθ) none := by
      simp only [maureyPMF, PMF.ofFintype_apply]
      have hdiv : l1norm θ / R < 1 := (div_lt_one hR).mpr hθR
      exact ENNReal.ofReal_pos.mpr (by linarith)
    unfold productPMFWeight
    rw [ENNReal.toReal_prod]
    apply Finset.prod_pos
    intro l _
    rw [ENNReal.toReal_pos_iff]
    constructor
    · exact hPnone
    · exact lt_top_iff_ne_top.mpr (PMF.apply_ne_top (maureyPMF θ R hθ) none)
  · push Not at hθR
    have hθR' : l1norm θ = R := le_antisymm hθ hθR
    have hθ_ne : l1norm θ ≠ 0 := ne_of_gt (hθR' ▸ hR)
    obtain ⟨j, hj⟩ : ∃ j : Fin d, θ j ≠ 0 := by
      by_contra h
      push Not at h
      have : l1norm θ = 0 := by
        unfold l1norm
        apply Finset.sum_eq_zero
        intro j _
        rw [h j]
        exact norm_zero
      exact hθ_ne this
    let s : Option (Fin d × Bool) := some (j, decide (0 ≤ θ j))
    use fun _ => s
    have hPs : 0 < (maureyPMF θ R hθ) s := by
      simp only [maureyPMF, PMF.ofFintype_apply, s, ite_true]
      exact ENNReal.ofReal_pos.mpr (div_pos (norm_pos_iff.mpr hj) hR)
    unfold productPMFWeight
    rw [ENNReal.toReal_prod]
    apply Finset.prod_pos
    intro l _
    rw [ENNReal.toReal_pos_iff]
    constructor
    · exact hPs
    · exact lt_top_iff_ne_top.mpr (PMF.apply_ne_top (maureyPMF θ R hθ) s)

private lemma exists_maureyAvg_sq_dist_le
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d))
    {R : ℝ} (hR : 0 < R) (hθ : l1norm θ ≤ R) (hcol : columnNormBound x)
    (hn : 0 < n) (k : ℕ) (hk : 0 < k) :
    ∃ f : Fin k → Option (Fin d × Bool),
      dist (maureyAvg x R k f)
        (fun i => (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i)) ^ 2 ≤
          R * l1norm θ / k := by
  classical
  let target : EmpiricalSpace n := fun i => (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i)
  let distSq : (Fin k → Option (Fin d × Bool)) → ℝ := fun f =>
    dist (maureyAvg x R k f) target ^ 2
  by_contra h
  push Not at h
  obtain ⟨f_pos, hf_pos⟩ := exists_productPMFWeight_toReal_pos θ hR hθ k
  let E : ℝ := ∑ f : Fin k → Option (Fin d × Bool),
    (productPMFWeight θ R hθ k f).toReal * distSq f
  let μ : Measure (Option (Fin d × Bool)) := (maureyPMF θ R hθ).toMeasure
  let ν : Measure (Fin k → Option (Fin d × Bool)) := Measure.pi (fun _ : Fin k => μ)
  have hμprob : IsProbabilityMeasure μ := by simp only [μ]; infer_instance
  have hνprob : IsProbabilityMeasure ν := by infer_instance
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hn_ge_1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hl1_nonneg : 0 ≤ l1norm θ :=
    Finset.sum_nonneg (s := Finset.univ) (fun i _ => norm_nonneg (θ i))
  have hE_eq : E = ∫ f, distSq f ∂ν := by
    rw [MeasureTheory.integral_fintype (Integrable.of_finite : Integrable distSq ν)]
    simp only [E, smul_eq_mul]
    congr 1
    ext f
    have hν_singleton : ν {f} = productPMFWeight θ R hθ k f := by
      simp only [ν, Measure.pi_singleton, productPMFWeight, μ]
      congr 1
      ext l
      rw [PMF.toMeasure_apply_singleton _ (f l) (measurableSet_singleton _)]
    rw [Measure.real, hν_singleton]
  have hdistSq_eq : ∀ f, distSq f =
      (1 / n : ℝ) * ∑ i : Fin n, (maureyAvg x R k f i - target i) ^ 2 := by
    intro f
    simp only [distSq]
    have hdist : dist (maureyAvg x R k f) target =
        empiricalNorm n (maureyAvg x R k f - target) := rfl
    rw [hdist]
    have hd := empiricalNorm_sq n (maureyAvg x R k f - target)
    rw [hd, one_div]
    congr 1
  have hsum_var_bound :
      ∑ i : Fin n, ∫ f, (maureyAvg x R k f i - target i) ^ 2 ∂ν ≤
        R * l1norm θ / k := by
    have hcoord_sum : ∀ i : Fin n,
        ∫ f, (maureyAvg x R k f i - target i) ^ 2 ∂ν ≤
          (1 / k : ℝ) * ∫ o, (maureyVec x R o i - target i) ^ 2 ∂μ := by
      intro i
      simpa only [target, μ, ν] using maureyAvg_coordinate_variance_le x θ hR hθ k hk i
    calc
      ∑ i : Fin n, ∫ f, (maureyAvg x R k f i - target i) ^ 2 ∂ν ≤
          ∑ i : Fin n, (1 / k : ℝ) * ∫ o, (maureyVec x R o i - target i) ^ 2 ∂μ :=
        Finset.sum_le_sum (fun i _ => hcoord_sum i)
      _ = (1 / k : ℝ) * ∑ i : Fin n, ∫ o, (maureyVec x R o i - target i) ^ 2 ∂μ := by
        rw [← Finset.mul_sum]
      _ ≤ (1 / k : ℝ) * ∑ i : Fin n, ∫ o, (maureyVec x R o i) ^ 2 ∂μ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro i _
        have hmean_i := maureyPMF_mean_coord x θ hR hθ i
        have hE_X : ∫ o, maureyVec x R o i ∂μ = target i := by
          simp only [μ, target, hmean_i]
        have hvar_eq : ∫ o, (maureyVec x R o i - target i) ^ 2 ∂μ =
            ∫ o, (maureyVec x R o i) ^ 2 ∂μ - (target i) ^ 2 := by
          calc
            ∫ o, (maureyVec x R o i - target i) ^ 2 ∂μ =
                ∫ o, (maureyVec x R o i) ^ 2 - 2 * target i * maureyVec x R o i +
                  (target i) ^ 2 ∂μ := by congr 1; ext o; ring
            _ = ∫ o, (maureyVec x R o i) ^ 2 ∂μ -
                2 * target i * ∫ o, maureyVec x R o i ∂μ +
                  ∫ o, (target i) ^ 2 ∂μ := by
              rw [MeasureTheory.integral_add Integrable.of_finite Integrable.of_finite]
              rw [MeasureTheory.integral_sub Integrable.of_finite Integrable.of_finite]
              rw [MeasureTheory.integral_const_mul]
            _ = ∫ o, (maureyVec x R o i) ^ 2 ∂μ -
                2 * target i * target i + (target i) ^ 2 := by
              rw [hE_X, MeasureTheory.integral_const]
              simp only [smul_eq_mul, Measure.real, hμprob.measure_univ,
                ENNReal.toReal_one, one_mul]
            _ = ∫ o, (maureyVec x R o i) ^ 2 ∂μ - (target i) ^ 2 := by ring
        rw [hvar_eq]
        exact sub_le_self _ (sq_nonneg _)
      _ = (1 / k : ℝ) * ∫ o, ∑ i : Fin n, (maureyVec x R o i) ^ 2 ∂μ := by
        congr 1
        rw [MeasureTheory.integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      _ ≤ (1 / k : ℝ) * (R * l1norm θ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [μ] using maureyPMF_variance_bound x θ hR hθ hcol hn
      _ = R * l1norm θ / k := by ring
  have hE_bound : E ≤ R * l1norm θ / k := by
    calc
      E = ∫ f, distSq f ∂ν := hE_eq
      _ = ∫ f, (1 / n : ℝ) * ∑ i : Fin n,
          (maureyAvg x R k f i - target i) ^ 2 ∂ν := by
        congr 1
        ext f
        exact hdistSq_eq f
      _ = (1 / n : ℝ) * ∫ f, ∑ i : Fin n,
          (maureyAvg x R k f i - target i) ^ 2 ∂ν := by
        rw [MeasureTheory.integral_const_mul]
      _ = (1 / n : ℝ) * ∑ i : Fin n, ∫ f,
          (maureyAvg x R k f i - target i) ^ 2 ∂ν := by
        congr 1
        rw [MeasureTheory.integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      _ ≤ (1 / n : ℝ) * (R * l1norm θ / k) := by
        apply mul_le_mul_of_nonneg_left hsum_var_bound (by positivity)
      _ ≤ 1 * (R * l1norm θ / k) := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [one_div] using inv_le_one_of_one_le₀ hn_ge_1)
          (div_nonneg (mul_nonneg hR.le hl1_nonneg) (Nat.cast_nonneg k))
      _ = R * l1norm θ / k := by ring
  have hPMF_sum : ∑ f : Fin k → Option (Fin d × Bool),
      (productPMFWeight θ R hθ k f).toReal = 1 := by
    have hsum := productPMFWeight_sum_eq_one θ R hθ k
    have hne_top : ∀ f, productPMFWeight θ R hθ k f ≠ ⊤ := by
      intro f
      unfold productPMFWeight
      apply ENNReal.prod_ne_top
      intro l _
      exact PMF.apply_ne_top (maureyPMF θ R hθ) (f l)
    rw [← ENNReal.toReal_sum (fun f _ => hne_top f), hsum]
    simp
  have hE_lower : E > R * l1norm θ / k := by
    calc
      E = ∑ f, (productPMFWeight θ R hθ k f).toReal * distSq f := rfl
      _ > ∑ f, (productPMFWeight θ R hθ k f).toReal * (R * l1norm θ / k) := by
        apply Finset.sum_lt_sum
        · intro f _
          by_cases hPf : (productPMFWeight θ R hθ k f).toReal = 0
          · simp only [hPf, zero_mul, le_refl]
          · exact le_of_lt (mul_lt_mul_of_pos_left (h f)
              (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hPf)))
        · use f_pos, Finset.mem_univ f_pos
          exact mul_lt_mul_of_pos_left (h f_pos) hf_pos
      _ = (R * l1norm θ / k) * ∑ f, (productPMFWeight θ R hθ k f).toReal := by
        rw [← Finset.sum_mul, mul_comm]
      _ = R * l1norm θ / k := by rw [hPMF_sum, mul_one]
  linarith

/-- Key Maurey bound: For k samples from the Maurey PMF, the expected distSq is bounded.
Specifically, there exists a sample f with distSq(maureyAvg f, target) ≤ R * l1norm θ / k.
This is because E[distSq] ≤ R * l1norm θ / k, and min ≤ E by pigeonhole. -/
lemma maurey_exists_good_sample (x : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) (hθ : l1norm θ ≤ R)
    (hcol : columnNormBound x) (hn : 0 < n) (k : ℕ) (hk : 0 < k) :
    ∃ f : Fin k → Option (Fin d × Bool),
      dist (maureyAvg x R k f) (fun i => (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i)) ^ 2 ≤
        R * l1norm θ / k := by
  exact exists_maureyAvg_sq_dist_le x θ hR hθ hcol hn k hk
/-- Main bound: existence of close average in EmpiricalSpace.

This is Maurey's empirical method: for any θ with ‖θ‖₁ ≤ R, there exists a k-sample average
from the signed columns that approximates Xθ/√n within distance ε, provided k ≥ R²/ε². -/
lemma exists_maureyAvg_close (x : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hθ : l1norm θ ≤ R) (hcol : columnNormBound x) (hn : 0 < n)
    (k : ℕ) (hk : R ^ 2 ≤ (k : ℝ) * ε ^ 2) :
    ∃ f : Fin k → Option (Fin d × Bool),
      dist (maureyAvg x R k f) (fun i => (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i)) ≤ ε := by
  classical
  by_cases hk0 : k = 0
  · exfalso
    simp only [hk0, Nat.cast_zero, zero_mul] at hk
    linarith [sq_pos_of_pos hR]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  let target : EmpiricalSpace n := fun i => (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i)
  by_cases hθ0 : l1norm θ = 0
  · -- When ‖θ‖₁ = 0, θ = 0, target = 0, and all-none sample gives dist = 0
    have hθ_zero : θ = 0 := by
      ext j
      have : ‖θ j‖ = 0 := Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => norm_nonneg _) |>.1 hθ0 j (Finset.mem_univ j)
      exact norm_eq_zero.1 this
    use fun _ => none
    have havg : maureyAvg x R k (fun _ => none) = 0 := by
      funext i
      simp only [maureyAvg]
      have h0 : maureyVec x R none i = 0 := rfl
      simp only [h0, Finset.sum_const_zero, mul_zero]
      rfl
    change
      dist (maureyAvg x R k (fun _ => none))
        (fun i => (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i)) ≤ ε
    rw [havg]
    have htgt' : (fun i => (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i)) = (0 : EmpiricalSpace n) := by
      funext i
      simp only [hθ_zero, inner_zero_left, mul_zero]
      rfl
    rw [htgt', dist_self]
    exact le_of_lt hε
  have hRsq_k_bound : R ^ 2 / k ≤ ε ^ 2 := by
    have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
    rw [div_le_iff₀ hk_pos]
    calc R ^ 2 ≤ k * ε ^ 2 := hk
      _ = ε ^ 2 * k := by ring
  let α := Fin k → Option (Fin d × Bool)
  let distSq : α → ℝ := fun f => dist (maureyAvg x R k f) target ^ 2
  obtain ⟨f₀, hf₀_min⟩ := Finite.exists_min distSq
  have hdistSq_bound : distSq f₀ ≤ ε ^ 2 := by
    have hdist_none : distSq (fun _ => none) ≤ R ^ 2 := by
      have havg_zero : maureyAvg x R k (fun _ => none) = 0 := by
        funext i
        simp only [maureyAvg]
        have h0 : maureyVec x R none i = 0 := rfl
        simp only [h0, Finset.sum_const_zero, mul_zero]
        rfl
      have hdist_emp : dist (0 : EmpiricalSpace n) target = empiricalNorm n target := by
        change empiricalNorm n ((0 : EmpiricalSpace n) - target) = empiricalNorm n target
        have : (0 : EmpiricalSpace n) - target = -target := by
          funext i; exact zero_sub (target i)
        rw [this]
        exact empiricalNorm_neg n target
      have htarget_le : empiricalNorm n target ≤ l1norm θ := by
        have hinner := empiricalNorm_le_l1norm_of_columnNormBound x θ hcol hn
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
        have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
        have h1 : 0 ≤ 1 / Real.sqrt n := by positivity
        have heq : target = (1 / Real.sqrt n) • (fun i => @inner ℝ _ _ θ (x i)) := by
          funext i
          simp only [target, Pi.smul_apply, smul_eq_mul]
        rw [heq, empiricalNorm_smul_of_nonneg h1]
        calc (1 / Real.sqrt n) * empiricalNorm n (fun i => @inner ℝ _ _ θ (x i))
          _ ≤ (1 / Real.sqrt n) * (Real.sqrt n * l1norm θ) := by
              apply mul_le_mul_of_nonneg_left _ h1
              have h' := empiricalNorm_le_l1norm_of_columnNormBound x θ hcol hn
              calc empiricalNorm n (fun i => @inner ℝ _ _ θ (x i))
                  ≤ l1norm θ := h'
                _ ≤ Real.sqrt n * l1norm θ := by
                    by_cases hl1 : l1norm θ = 0
                    · simp [hl1]
                    · have hl1pos : 0 < l1norm θ := by
                        have hl1nn : 0 ≤ l1norm θ :=
                          Finset.sum_nonneg (s := Finset.univ) (fun i _ => norm_nonneg (θ i))
                        exact lt_of_le_of_ne hl1nn (Ne.symm hl1)
                      have hsqrt_ge_1 : 1 ≤ Real.sqrt n :=
                        Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hn)
                      nlinarith
          _ = l1norm θ := by field_simp
      simp only [distSq, havg_zero, hdist_emp]
      calc (empiricalNorm n target) ^ 2
          ≤ (l1norm θ) ^ 2 := sq_le_sq' (by nlinarith [empiricalNorm_nonneg n target]) htarget_le
        _ ≤ R ^ 2 := by
            have hl1nn : 0 ≤ l1norm θ :=
              Finset.sum_nonneg (s := Finset.univ) (fun i _ => norm_nonneg (θ i))
            nlinarith [sq_nonneg (l1norm θ), sq_nonneg R]
    by_cases hk1 : k = 1
    · -- k = 1: distSq ≤ R² ≤ ε²
      calc distSq f₀ ≤ distSq (fun _ => none) := hf₀_min _
        _ ≤ R ^ 2 := hdist_none
        _ ≤ k * ε ^ 2 := hk
        _ = ε ^ 2 := by simp [hk1]
    · -- k > 1: Use Maurey variance bound. E[distSq] ≤ R²/k, so min ≤ E ≤ R²/k ≤ ε².
      have hk_pos_real : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
      have hvar_bound : R * l1norm θ ≤ R ^ 2 := by
        calc R * l1norm θ ≤ R * R := mul_le_mul_of_nonneg_left hθ (le_of_lt hR)
          _ = R ^ 2 := by ring
      obtain ⟨f_good, hf_good⟩ := maurey_exists_good_sample x θ hR hθ hcol hn k hkpos
      have hdistSq_good : distSq f_good ≤ R * l1norm θ / k := hf_good
      calc distSq f₀
          ≤ distSq f_good := hf₀_min f_good
        _ ≤ R * l1norm θ / k := hdistSq_good
        _ ≤ R ^ 2 / k := by
            apply div_le_div_of_nonneg_right _ (le_of_lt (Nat.cast_pos.mpr hkpos))
            calc R * l1norm θ ≤ R * R := mul_le_mul_of_nonneg_left hθ (le_of_lt hR)
              _ = R ^ 2 := by ring
        _ ≤ ε ^ 2 := hRsq_k_bound
  use f₀
  have hnonneg : 0 ≤ dist (maureyAvg x R k f₀) target := dist_nonneg
  have hε_nonneg : 0 ≤ ε := le_of_lt hε
  nlinarith [sq_nonneg (dist (maureyAvg x R k f₀) target), sq_nonneg ε, hdistSq_bound]

/-- Covering Number Bound for the ℓ1-Convex Hull in EmpiricalSpace -/
theorem l1BallImage_coveringNumber_le {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (hcol : columnNormBound x) (hn : 0 < n) :
    coveringNumber ε (l1BallImage x R) ≤ (2 * d + 1) ^ ⌈R ^ 2 / ε ^ 2⌉₊ := by
  classical
  by_cases hR0 : R = 0
  · subst hR0
    have hsubset : l1BallImage x 0 ⊆ {0} := by
      intro v hv
      obtain ⟨θ, hθ_norm, hv_eq⟩ := hv
      have hθ0 : θ = 0 := by
        have hl1_nonneg : 0 ≤ l1norm θ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
        have hl1_zero : l1norm θ = 0 := le_antisymm hθ_norm hl1_nonneg
        ext j
        have hcoord : ‖θ j‖ = 0 := by
          have hsum : ∑ i, ‖θ i‖ = 0 := hl1_zero
          exact Finset.sum_eq_zero_iff_of_nonneg (fun i _ => norm_nonneg _) |>.1 hsum j (by simp)
        exact norm_eq_zero.1 hcoord
      rw [Set.mem_singleton_iff, hv_eq, hθ0]
      funext i
      simp only [inner_zero_left, mul_zero]
      rfl
    have hnet : IsENet ({0} : Finset (EmpiricalSpace n)) ε (l1BallImage x 0) := by
      intro v hv
      have hv0 : v = 0 := hsubset hv
      rw [hv0]
      exact Set.mem_iUnion₂.mpr ⟨0, by simp, Metric.mem_closedBall_self (le_of_lt hε)⟩
    calc coveringNumber ε (l1BallImage x 0)
        ≤ ({0} : Finset (EmpiricalSpace n)).card := coveringNumber_le_card hnet
      _ = 1 := by simp [Finset.card_singleton]
      _ ≤ (2 * d + 1) ^ ⌈0 ^ 2 / ε ^ 2⌉₊ := by simp
  · have hRpos : 0 < R := lt_of_le_of_ne hR (fun h => hR0 h.symm)
    set k : ℕ := ⌈R ^ 2 / ε ^ 2⌉₊ with hk_def
    let N : Finset (EmpiricalSpace n) := maureyNet x R k
    have hcard : (N.card : WithTop ℕ) ≤ (2 * d + 1) ^ k := by
      exact_mod_cast maureyNet_card_le x R k
    have hnet : IsENet N ε (l1BallImage x R) := by
      intro v hv
      obtain ⟨θ, hθ_norm, hv_eq⟩ := hv
      have hk' : R ^ 2 ≤ (k : ℝ) * ε ^ 2 := by
        have := Nat.le_ceil (R ^ 2 / ε ^ 2)
        have hk'' : (R ^ 2 / ε ^ 2) ≤ k := by simpa [hk_def] using this
        have hε2 : 0 < ε ^ 2 := by nlinarith
        have := (div_le_iff₀ hε2).1 hk''
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      obtain ⟨f, hf⟩ := exists_maureyAvg_close x θ hRpos hε hθ_norm hcol hn k hk'
      have hmem : maureyAvg x R k f ∈ N := by
        have : maureyAvg x R k f ∈ Finset.univ.image (maureyAvg x R k) :=
          Finset.mem_image.mpr ⟨f, Finset.mem_univ f, rfl⟩
        simp only [N, maureyNet, this]
      have hdist : dist v (maureyAvg x R k f) ≤ ε := by
        calc
          dist v (maureyAvg x R k f) = dist (maureyAvg x R k f) v := dist_comm _ _
          _ ≤ ε := hv_eq ▸ hf
      exact Set.mem_iUnion₂.mpr ⟨_, hmem, Metric.mem_closedBall.mpr hdist⟩
    exact (coveringNumber_le_card hnet).trans hcard

/-! ## Localized ℓ₁ Ball Image Covering Bound

The localized ℓ₁ ball image is the set {Xθ/√n : ‖θ‖₁ ≤ R, ‖Xθ‖₂/√n ≤ δ}.
This is a subset of the full ℓ₁ ball image, so its covering number is bounded above
by the covering number of the full ball image.
-/

/-- The localized ℓ₁ ball image in EmpiricalSpace:
    {Xθ/√n : ‖θ‖₁ ≤ R, ‖Xθ‖₂/√n ≤ δ} -/
def l1LocalizedImage (x : Fin n → EuclideanSpace ℝ (Fin d)) (R δ : ℝ) :
    Set (EmpiricalSpace n) :=
  {v | ∃ θ : EuclideanSpace ℝ (Fin d), l1norm θ ≤ R ∧
       empiricalNorm n (fun i => @inner ℝ _ _ θ (x i)) ≤ δ ∧
       v = fun i => (1 / Real.sqrt n) * @inner ℝ _ _ θ (x i)}

/-- The localized ball image is a subset of the full ball image -/
lemma l1LocalizedImage_subset_l1BallImage (x : Fin n → EuclideanSpace ℝ (Fin d)) (R δ : ℝ) :
    l1LocalizedImage x R δ ⊆ l1BallImage x R := by
  intro v ⟨θ, hθ_norm, _, hv⟩
  exact ⟨θ, hθ_norm, hv⟩

/-- Covering number bound for the localized ℓ₁ ball image -/
theorem l1LocalizedImage_coveringNumber_le (x : Fin n → EuclideanSpace ℝ (Fin d))
    {R δ ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hcol : columnNormBound x) (hn : 0 < n) :
    coveringNumber ε (l1LocalizedImage x R δ) ≤ (2 * d + 1) ^ ⌈R ^ 2 / ε ^ 2⌉₊ := by
  calc coveringNumber ε (l1LocalizedImage x R δ)
      ≤ coveringNumber ε (l1BallImage x R) :=
        coveringNumber_mono_set (l1LocalizedImage_subset_l1BallImage x R δ)
    _ ≤ (2 * d + 1) ^ ⌈R ^ 2 / ε ^ 2⌉₊ :=
        l1BallImage_coveringNumber_le hR hε x hcol hn

end LeastSquares

end LeanPool.StatisticalLearningTheory
