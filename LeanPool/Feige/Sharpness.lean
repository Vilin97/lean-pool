/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.Reduction
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform

/-!
# The fixed-dimensional extremal example

This file formalizes the sharpness construction from §1.2 at `δ = 1`.  The
sample space is `(Fin n → Fin (n + 1))`, with its uniform law.  Coordinate
`i` is `n + 1` when the `i`th digit is zero, and is zero otherwise.  Thus
every coordinate has the two-point law used in the proof outline.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace Feige

noncomputable section

/-- The finite product sample space for the sharpness example. -/
abbrev ExtremalSpace (n : ℕ) := Fin n → Fin (n + 1)

/-- The uniform probability measure on the extremal sample space. -/
noncomputable def extremalMarginal (n : ℕ) : Measure (Fin (n + 1)) :=
  (PMF.uniformOfFintype (Fin (n + 1))).toMeasure

/-- The product of the uniform one-coordinate measures. -/
noncomputable def extremalMeasure (n : ℕ) : Measure (ExtremalSpace n) :=
  Measure.pi (fun _ : Fin n ↦ extremalMarginal n)

instance (n : ℕ) : IsProbabilityMeasure (extremalMarginal n) := by
  unfold extremalMarginal
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (extremalMeasure n) := by
  unfold extremalMeasure
  infer_instance

/-- The `i`th coordinate of the `δ = 1` sharpness construction in §1.2. -/
noncomputable def extremalX (n : ℕ) (i : Fin n) (ω : ExtremalSpace n) : ℝ :=
  if ω i = 0 then n + 1 else 0

/-- The sum of all coordinates in the sharpness construction. -/
noncomputable def extremalSum (n : ℕ) (ω : ExtremalSpace n) : ℝ :=
  ∑ i, extremalX n i ω

/-- Embed the `n` nonzero digits into the `n + 1` possible digits. -/
def allLowEmbedding (n : ℕ) : (Fin n → Fin n) → ExtremalSpace n :=
  fun ω i ↦ (ω i).succ

theorem allLowEmbedding_injective (n : ℕ) :
    Function.Injective (allLowEmbedding n) := by
  intro ω τ h
  funext i
  exact Fin.succ_inj.mp (congrFun h i)

/-- The good event consists precisely of choices with no zero digit. -/
def extremalGood (n : ℕ) : Set (ExtremalSpace n) :=
  Set.range (allLowEmbedding n)

instance (n : ℕ) : Fintype (extremalGood n) :=
  Set.fintypeRange (allLowEmbedding n)

theorem mem_extremalGood_iff (n : ℕ) (ω : ExtremalSpace n) :
    ω ∈ extremalGood n ↔ ∀ i, ω i ≠ 0 := by
  constructor
  · rintro ⟨τ, rfl⟩ i
    exact Fin.succ_ne_zero _
  · intro h
    refine ⟨fun i ↦ (ω i).pred (h i), ?_⟩
    funext i
    exact Fin.succ_pred _ _

@[simp] theorem extremalX_eq_zero_iff (n : ℕ) (i : Fin n) (ω : ExtremalSpace n) :
    extremalX n i ω = 0 ↔ ω i ≠ 0 := by
  by_cases h : ω i = 0
  · unfold extremalX
    rw [ite_eq_left h]
    simp only [ne_eq, h, not_true_eq_false, iff_false]
    positivity
  · simp [extremalX, h]

theorem extremalX_nonneg (n : ℕ) (i : Fin n) (ω : ExtremalSpace n) :
    0 ≤ extremalX n i ω := by
  simp only [extremalX]
  split_ifs <;> positivity

theorem extremalX_measurable (n : ℕ) (i : Fin n) :
    Measurable (extremalX n i) := by
  unfold extremalX
  exact Measurable.ite
    ((measurable_pi_apply i) (measurableSet_singleton 0))
    measurable_const measurable_const

theorem extremalX_integrable (n : ℕ) (i : Fin n) :
    Integrable (extremalX n i) (extremalMeasure n) := by
  rw [← integrableOn_univ]
  exact (extremalMeasure n).integrableOn_of_bounded (M := (n : ℝ) + 1) (by finiteness)
    (extremalX_measurable n i).aestronglyMeasurable
    (by
      filter_upwards [] with ω
      simp only [Real.norm_eq_abs, extremalX]
      split_ifs
      · rw [abs_of_nonneg (by positivity)]
      · simp only [abs_zero]
        positivity)

theorem extremalMarginal_mean (n : ℕ) :
    (∫ x : Fin (n + 1), (if x = 0 then (n + 1 : ℝ) else 0)
        ∂(extremalMarginal n)) = 1 := by
  rw [extremalMarginal, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, Nat.cast_add,
    Nat.cast_one, ENNReal.toReal_inv, smul_eq_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have htr : (↑n + 1 : ℝ≥0∞).toReal = (n : ℝ) + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast,
      ENNReal.toReal_one]
  rw [htr]
  field_simp

theorem extremalX_mean (n : ℕ) (i : Fin n) :
    (∫ ω, extremalX n i ω ∂(extremalMeasure n)) = 1 := by
  let f : Fin (n + 1) → ℝ := fun x ↦ if x = 0 then n + 1 else 0
  have hf : Measurable f := Measurable.ite (measurableSet_singleton 0)
    measurable_const measurable_const
  have hmap := (measurePreserving_eval
    (fun _ : Fin n ↦ extremalMarginal n) i).map_eq
  change (∫ ω, f (ω i) ∂(extremalMeasure n)) = 1
  rw [extremalMeasure, ← MeasureTheory.integral_map
    (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable, hmap]
  exact extremalMarginal_mean n

theorem extremalX_iIndepFun (n : ℕ) :
    ProbabilityTheory.iIndepFun (extremalX n) (extremalMeasure n) := by
  let f : Fin n → Fin (n + 1) → ℝ :=
    fun _ x ↦ if x = 0 then n + 1 else 0
  have h := ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : Fin n ↦ extremalMarginal n) (X := f)
    (fun _ ↦ (measurable_const.piecewise
      (measurableSet_singleton 0) measurable_const).aemeasurable)
  simp only [extremalMeasure]
  exact h

/-- Because the threshold is strict, the good event occurs exactly when all
coordinates vanish. -/
theorem extremalSum_lt_iff (n : ℕ) (ω : ExtremalSpace n) :
    extremalSum n ω < n + 1 ↔ ω ∈ extremalGood n := by
  rw [mem_extremalGood_iff]
  constructor
  · intro h i
    by_contra hi
    have hterm : extremalX n i ω = n + 1 := by simp [extremalX, hi]
    have hle : extremalX n i ω ≤ extremalSum n ω := by
      unfold extremalSum
      exact Finset.single_le_sum (fun j _ ↦ extremalX_nonneg n j ω)
        (Finset.mem_univ i)
    linarith
  · intro h
    have hz : ∀ i, extremalX n i ω = 0 := fun i ↦
      (extremalX_eq_zero_iff n i ω).2 (h i)
    unfold extremalSum
    simp only [hz, Finset.sum_const_zero]
    positivity

theorem card_extremalGood (n : ℕ) :
    Fintype.card (extremalGood n) = n ^ n := by
  calc
    Fintype.card (extremalGood n) =
        Fintype.card (Fin n → Fin n) := by
          exact Set.card_range_of_injective (allLowEmbedding_injective n)
    _ = n ^ n := by simp

theorem card_extremalSpace (n : ℕ) :
    Fintype.card (ExtremalSpace n) = (n + 1) ^ n := by
  simp

/-- The probability of the strict good event in the extremal construction is
exactly the fixed-dimensional constant `cₙ`. -/
theorem extremalGood_probability (n : ℕ) :
    (extremalMeasure n).real (extremalGood n) = sharpConstant n := by
  have heq :
      extremalGood n =
        Set.univ.pi (fun _ : Fin n ↦ {x : Fin (n + 1) | x ≠ 0}) := by
    ext ω
    simp [mem_extremalGood_iff]
  rw [heq, extremalMeasure, Measure.real, MeasureTheory.Measure.pi_pi]
  have hm (i : Fin n) :
      extremalMarginal n {x : Fin (n + 1) | x ≠ 0} =
        (n : ℝ≥0∞) / (n + 1) := by
    rw [extremalMarginal,
      PMF.toMeasure_uniformOfFintype_apply _ MeasurableSet.of_discrete]
    rw [Fintype.card_fin]
    push_cast
    congr 1
    norm_cast
    change Fintype.card {x : Fin (n + 1) // ¬x = 0} = n
    rw [Fintype.card_subtype_compl (fun x : Fin (n + 1) ↦ x = 0)]
    simp
  rw [Finset.prod_congr rfl (fun i _ ↦ hm i)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [show (↑n + 1 : ℝ≥0∞).toReal = (n : ℝ) + 1 by
    rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast,
      ENNReal.toReal_one]]
  exact rfl

/-- Under the uniform product model from the sharpness paragraph in §1.2,
the strict threshold event has probability exactly `bₙ,₁`. -/
theorem extremal_strict_event_probability (n : ℕ) :
    (extremalMeasure n).real {ω | extremalSum n ω < n + 1} =
      sharpConstant n := by
  have heq : {ω | extremalSum n ω < n + 1} = extremalGood n := by
    ext ω
    exact extremalSum_lt_iff n ω
  rw [heq, extremalGood_probability]

/-- The threshold in the sharpness example is exactly `E Sₙ + 1 = n + 1`. -/
theorem extremalSum_mean (n : ℕ) :
    (∫ ω, extremalSum n ω ∂(extremalMeasure n)) = n := by
  change (∫ ω, ∑ i, extremalX n i ω ∂(extremalMeasure n)) = n
  rw [integral_finsetSum]
  · simp [extremalX_mean]
  · exact fun i _ ↦ extremalX_integrable n i

/-- The full sharpness statement, with the threshold written in the form used
in Feige's inequality. -/
theorem extremal_mean_threshold_probability (n : ℕ) :
    (extremalMeasure n).real
        {ω | extremalSum n ω <
          (∫ ω', extremalSum n ω' ∂(extremalMeasure n)) + 1} =
      sharpConstant n := by
  rw [extremalSum_mean]
  simpa only [Nat.cast_add, Nat.cast_one] using
    extremal_strict_event_probability n

/-- The sharpness construction in §1.2 proves that no fixed-dimensional
unit-slack lower bound can exceed `sharpConstant n`. -/
theorem fixedDimensionalLowerBound_le_sharpConstant
    {n : ℕ} {c : ℝ} (h : FixedDimensionalFeigeLowerBound n c) :
    c ≤ sharpConstant n := by
  have hbound := h (ExtremalSpace n) inferInstance (extremalMeasure n)
    inferInstance (extremalX n)
    (extremalX_measurable n) (extremalX_integrable n)
    (extremalX_iIndepFun n) (extremalX_nonneg n)
    (fun i ↦ (extremalX_mean n i).le)
  change c ≤ (extremalMeasure n).real
    {ω | extremalSum n ω <
      (∫ ω', extremalSum n ω' ∂(extremalMeasure n)) + 1} at hbound
  rw [extremal_mean_threshold_probability] at hbound
  exact hbound

/-- A lower bound is optimal when every other valid lower bound is no
larger. -/
def IsOptimalFixedDimensionalFeigeBound (n : ℕ) (c : ℝ) : Prop :=
  FixedDimensionalFeigeLowerBound n c ∧
    ∀ d : ℝ, FixedDimensionalFeigeLowerBound n d → d ≤ c

/-- Conditional on exact calibration and the deterministic bridge, the
paper's unit-slack constant is not only valid but optimal; the sharpness
construction in §1.2 supplies the reverse extremal statement. -/
theorem sharpConstant_is_optimal_of_structural_inputs
    {n : ℕ} (hn : 0 < n) (K : (Fin n → ℝ) → ℝ)
    (hcal : UniversalCalibration K) (hbridge : LargeSumBridge K) :
    IsOptimalFixedDimensionalFeigeBound n (sharpConstant n) := by
  constructor
  · exact sharpConstant_is_lowerBound_of_structural_inputs hn K hcal hbridge
  · intro d hd
    exact fixedDimensionalLowerBound_le_sharpConstant hd

end

end Feige
