/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The special Marcinkiewicz interpolation step from `L²` to `L∞`

This file develops the truncation argument used between the two endpoints in
Krause--Lacey Proposition 4.1. It is deliberately stated for an additive
operator on measurable vector-valued functions, rather than postulating a
bounded operator on an `Lp` completion. This is the interface satisfied by
the concrete localized integral operator in the project.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson


section Truncation

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]

/-- The part of a function above the norm threshold `a`. -/
noncomputable def interpolationHigh (f : α → E) (a : ℝ) (x : α) : E :=
  if a < ‖f x‖ then f x else 0

/-- The part of a function at or below the norm threshold `a`. -/
noncomputable def interpolationLow (f : α → E) (a : ℝ) (x : α) : E :=
  if ‖f x‖ ≤ a then f x else 0

omit [MeasurableSpace α] in
lemma interpolationHigh_add_low (f : α → E) (a : ℝ) :
    interpolationHigh f a + interpolationLow f a = f := by
  funext x
  by_cases hx : a < ‖f x‖
  · simp [interpolationHigh, interpolationLow, hx, not_le.mpr hx]
  · simp [interpolationHigh, interpolationLow, hx, le_of_not_gt hx]

omit [MeasurableSpace α] in
lemma norm_interpolationLow_le (f : α → E) {a : ℝ} (ha : 0 ≤ a) (x : α) :
    ‖interpolationLow f a x‖ ≤ a := by
  by_cases hx : ‖f x‖ ≤ a
  · simp [interpolationLow, hx]
  · simp [interpolationLow, hx, ha]

omit [MeasurableSpace α] in
lemma enorm_interpolationHigh (f : α → E) (a : ℝ) (x : α) :
    ‖interpolationHigh f a x‖ₑ =
      if a < ‖f x‖ then ‖f x‖ₑ else 0 := by
  by_cases hx : a < ‖f x‖ <;> simp [interpolationHigh, hx]

lemma stronglyMeasurable_interpolationHigh
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : α → E} (hf : StronglyMeasurable f) (a : ℝ) :
    StronglyMeasurable (interpolationHigh f a) := by
  apply Measurable.stronglyMeasurable
  unfold interpolationHigh
  exact Measurable.ite
    (measurableSet_lt measurable_const hf.norm.measurable) hf.measurable measurable_const

lemma stronglyMeasurable_interpolationLow
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : α → E} (hf : StronglyMeasurable f) (a : ℝ) :
    StronglyMeasurable (interpolationLow f a) := by
  apply Measurable.stronglyMeasurable
  unfold interpolationLow
  exact Measurable.ite
    (measurableSet_le hf.norm.measurable measurable_const) hf.measurable measurable_const

end Truncation

section Distribution

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure α}

/-- The distributional estimate at the heart of the `L²`--`L∞`
Marcinkiewicz interpolation argument. No interpolation result is assumed:
the proof is the source truncation, the `L∞` endpoint on the low part, and
Chebyshev applied to the high part. -/
theorem measure_norm_operator_gt_le_twoInfinity_tail
    (T : (α → E) → (α → E))
    (hadd : ∀ g h, T (g + h) = T g + T h)
    (hTmeas : ∀ g, StronglyMeasurable g → AEStronglyMeasurable (T g) μ)
    {M₂ MTop t : ℝ} (hMTop : 0 < MTop) (ht : 0 < t)
    (hL2 : ∀ g, StronglyMeasurable g →
      (∫⁻ x, ‖T g x‖ₑ ^ (2 : ℕ) ∂μ) ≤
      ENNReal.ofReal (M₂ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) ∂μ)
    (hLinf : ∀ (g : α → E) {a : ℝ}, 0 ≤ a → (∀ x, ‖g x‖ ≤ a) →
      ∀ x, ‖T g x‖ ≤ MTop * a)
    (f : α → E) (hf : StronglyMeasurable f) :
    ENNReal.ofReal ((t / 2) ^ 2) * μ {x | t < ‖T f x‖} ≤
      ENNReal.ofReal (M₂ ^ 2) *
        ∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ := by
  let a : ℝ := t / (2 * MTop)
  let hi : α → E := interpolationHigh f a
  let lo : α → E := interpolationLow f a
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hhi : StronglyMeasurable hi := stronglyMeasurable_interpolationHigh hf a
  have hlo (x : α) : ‖T lo x‖ ≤ t / 2 := by
    have h := hLinf lo ha (norm_interpolationLow_le f ha) x
    dsimp [a] at h
    convert h using 1; field_simp
  have hdecomp : T f = T hi + T lo := by
    rw [← hadd hi lo]
    congr 1
    exact (interpolationHigh_add_low f a).symm
  have hsubset : {x | t < ‖T f x‖} ⊆ {x | t / 2 ≤ ‖T hi x‖} := by
    intro x hx
    rw [hdecomp] at hx
    change t < ‖T hi x + T lo x‖ at hx
    have htri : ‖T hi x + T lo x‖ ≤ ‖T hi x‖ + ‖T lo x‖ := norm_add_le _ _
    have hsum : ‖T hi x‖ + ‖T lo x‖ ≤ ‖T hi x‖ + t / 2 :=
      add_le_add_right (hlo x) _
    have : t < ‖T hi x‖ + t / 2 := lt_of_lt_of_le hx (htri.trans hsum)
    change t / 2 ≤ ‖T hi x‖
    linarith
  have hmarkov := mul_meas_ge_le_lintegral₀
    ((hTmeas hi hhi).enorm.pow_const (2 : ℕ)) (ENNReal.ofReal ((t / 2) ^ 2))
  have hsets : {x | ENNReal.ofReal ((t / 2) ^ 2) ≤ ‖T hi x‖ₑ ^ (2 : ℕ)} =
      {x | t / 2 ≤ ‖T hi x‖} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)]
    exact sq_le_sq₀ (by positivity) (norm_nonneg _)
  rw [hsets] at hmarkov
  calc
    ENNReal.ofReal ((t / 2) ^ 2) * μ {x | t < ‖T f x‖} ≤
        ENNReal.ofReal ((t / 2) ^ 2) * μ {x | t / 2 ≤ ‖T hi x‖} := by
      gcongr
    _ ≤ ∫⁻ x, ‖T hi x‖ₑ ^ (2 : ℕ) ∂μ := hmarkov
    _ ≤ ENNReal.ofReal (M₂ ^ 2) * ∫⁻ x, ‖hi x‖ₑ ^ (2 : ℕ) ∂μ := hL2 hi hhi
    _ = ENNReal.ofReal (M₂ ^ 2) *
        ∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ := rfl

end Distribution

section LayerCake

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α}

/-- Exact evaluation of the integrated high-tail term in the special
`L²`--`L∞` interpolation argument. The proof applies layer cake to the
measure having density `‖f‖²`; this is the Tonelli step in the usual proof. -/
theorem twoInfinity_high_tail_layercake
    (f : α → E) (hf : StronglyMeasurable f)
    {q MTop : ℝ} (hq : 2 < q) (hMTop : 0 < MTop) :
    ENNReal.ofReal (q - 2) *
        ∫⁻ t in Ioi (0 : ℝ),
          (∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ) *
            ENNReal.ofReal (t ^ (q - 3)) =
      ENNReal.ofReal ((2 * MTop) ^ (q - 2)) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ q) ∂μ := by
  let w : α → ℝ≥0∞ := fun x ↦ ‖f x‖ₑ ^ (2 : ℕ)
  let ν : Measure α := μ.withDensity w
  let F : α → ℝ := fun x ↦ (2 * MTop) * ‖f x‖
  have hw : Measurable w := hf.enorm.pow_const _
  have hF : Measurable F := hf.norm.measurable.const_mul _
  have hFnonneg : ∀ x, 0 ≤ F x := fun x ↦ mul_nonneg (by positivity) (norm_nonneg _)
  have htail (t : ℝ) (ht : 0 < t) :
      (∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ) =
        ν {x | t < F x} := by
    have hs : MeasurableSet {x | t < F x} := measurableSet_lt measurable_const hF
    rw [show ν {x | t < F x} = ∫⁻ x in {x | t < F x}, w x ∂μ by
      exact withDensity_apply w hs]
    rw [← lintegral_indicator hs]
    apply lintegral_congr
    intro x
    have hc : 0 < 2 * MTop := by positivity
    have heq : t / (2 * MTop) < ‖f x‖ ↔ t < F x := by
      simpa [F, mul_comm] using
        (div_lt_iff₀ hc : t / (2 * MTop) < ‖f x‖ ↔ t < ‖f x‖ * (2 * MTop))
    rw [enorm_interpolationHigh]
    by_cases hx : t < F x
    · have hx' := heq.mpr hx
      simp [hx, hx', w]
    · have hx' : ¬t / (2 * MTop) < ‖f x‖ := fun h ↦ hx (heq.mp h)
      simp [hx, hx', w]
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul
    ν (Eventually.of_forall hFnonneg) hF.aemeasurable (sub_pos.mpr hq)
  rw [show q - 2 - 1 = q - 3 by ring] at hlayer
  have htailIntegral :
      (∫⁻ t in Ioi (0 : ℝ),
          (∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ) *
            ENNReal.ofReal (t ^ (q - 3))) =
        ∫⁻ t in Ioi (0 : ℝ), ν {x | t < F x} * ENNReal.ofReal (t ^ (q - 3)) := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [htail t (mem_Ioi.mp ht)]
  rw [htailIntegral, ← hlayer]
  rw [lintegral_withDensity_eq_lintegral_mul μ hw]
  · have hqmeas : AEMeasurable (fun x ↦ ENNReal.ofReal (‖f x‖ ^ q)) μ :=
      (hf.norm.measurable.pow measurable_const).ennreal_ofReal.aemeasurable
    rw [← lintegral_const_mul'' _ hqmeas]
    apply lintegral_congr
    intro x
    simp only [Pi.mul_apply, w, F]
    rw [← ofReal_norm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _) 2]
    calc
      ENNReal.ofReal (‖f x‖ ^ 2) *
            ENNReal.ofReal (((2 * MTop) * ‖f x‖) ^ (q - 2)) =
          ENNReal.ofReal
            (‖f x‖ ^ 2 * ((2 * MTop) * ‖f x‖) ^ (q - 2)) :=
        (ENNReal.ofReal_mul (sq_nonneg _)).symm
      _ = ENNReal.ofReal ((2 * MTop) ^ (q - 2) * ‖f x‖ ^ q) := by
        congr 1
        calc
          ‖f x‖ ^ 2 * ((2 * MTop) * ‖f x‖) ^ (q - 2) =
          (2 * MTop) ^ (q - 2) * (‖f x‖ ^ 2 * ‖f x‖ ^ (q - 2)) := by
            rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
            ring
          _ = (2 * MTop) ^ (q - 2) * ‖f x‖ ^ q := by
            congr 1
            rw [← Real.rpow_natCast]
            calc
              ‖f x‖ ^ (2 : ℝ) * ‖f x‖ ^ (q - 2) =
                  ‖f x‖ ^ ((2 : ℝ) + (q - 2)) :=
                (Real.rpow_add_of_nonneg (norm_nonneg _)
                  (by norm_num) (by linarith)).symm
              _ = ‖f x‖ ^ q := by congr 1; ring
      _ = ENNReal.ofReal ((2 * MTop) ^ (q - 2)) *
          ENNReal.ofReal (‖f x‖ ^ q) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)
  · exact (hF.pow measurable_const).ennreal_ofReal

end LayerCake

section Interpolation

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {μ : Measure α}

private lemma twoInfinity_weight_identity {q t : ℝ} (ht : 0 < t) :
    (t / 2) ^ 2 * (4 * t ^ (q - 3)) = t ^ (q - 1) := by
  calc
    (t / 2) ^ 2 * (4 * t ^ (q - 3)) = t ^ 2 * t ^ (q - 3) := by ring
    _ = t ^ (2 : ℝ) * t ^ (q - 3) := by rw [Real.rpow_two]
    _ = t ^ (2 + (q - 3)) := (Real.rpow_add ht 2 (q - 3)).symm
    _ = t ^ (q - 1) := by congr 1; ring

/-- Marcinkiewicz interpolation between strong `L²` and pointwise `L∞`,
specialized to the finite exponents `q > 2`. The conclusion is stated for
the `q`-th power integral, with the explicit constant produced by the direct
layer-cake proof. -/
theorem lintegral_norm_rpow_operator_le_twoInfinity
    (T : (α → E) → (α → E))
    (hadd : ∀ g h, T (g + h) = T g + T h)
    (hTmeas : ∀ g, StronglyMeasurable g → StronglyMeasurable (T g))
    {M₂ MTop q : ℝ} (hMTop : 0 < MTop) (hq : 2 < q)
    (hL2 : ∀ g, StronglyMeasurable g →
      (∫⁻ x, ‖T g x‖ₑ ^ (2 : ℕ) ∂μ) ≤
      ENNReal.ofReal (M₂ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) ∂μ)
    (hLinf : ∀ (g : α → E) {a : ℝ}, 0 ≤ a → (∀ x, ‖g x‖ ≤ a) →
      ∀ x, ‖T g x‖ ≤ MTop * a)
    (f : α → E) (hf : StronglyMeasurable f) :
    (∫⁻ x, ENNReal.ofReal (‖T f x‖ ^ q) ∂μ) ≤
      (ENNReal.ofReal q * ENNReal.ofReal (4 * M₂ ^ 2) *
          ENNReal.ofReal ((2 * MTop) ^ (q - 2)) / ENNReal.ofReal (q - 2)) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ q) ∂μ := by
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have hout := lintegral_rpow_eq_lintegral_meas_lt_mul
    μ (Eventually.of_forall fun x ↦ norm_nonneg (T f x))
      (hTmeas f hf).norm.measurable.aemeasurable hq0
  have hweighted (t : ℝ) (ht : 0 < t) :
      μ {x | t < ‖T f x‖} * ENNReal.ofReal (t ^ (q - 1)) ≤
        ENNReal.ofReal (4 * M₂ ^ 2) *
          (∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ) *
            ENNReal.ofReal (t ^ (q - 3)) := by
    let A : ℝ≥0∞ := ENNReal.ofReal ((t / 2) ^ 2)
    have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hAtop : A ≠ ∞ := ENNReal.ofReal_ne_top
    rw [← ENNReal.mul_le_mul_iff_left hA0 hAtop]
    have htail := measure_norm_operator_gt_le_twoInfinity_tail
      T hadd (fun g hg ↦ (hTmeas g hg).aestronglyMeasurable) hMTop ht hL2 hLinf f hf
    have hcoeff :
        A * ENNReal.ofReal (4 * M₂ ^ 2) * ENNReal.ofReal (t ^ (q - 3)) =
          ENNReal.ofReal (M₂ ^ 2) * ENNReal.ofReal (t ^ (q - 1)) := by
      dsimp [A]
      calc
        ENNReal.ofReal ((t / 2) ^ 2) * ENNReal.ofReal (4 * M₂ ^ 2) *
              ENNReal.ofReal (t ^ (q - 3)) =
            ENNReal.ofReal ((t / 2) ^ 2 * (4 * M₂ ^ 2)) *
              ENNReal.ofReal (t ^ (q - 3)) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _)]
        _ = ENNReal.ofReal (((t / 2) ^ 2 * (4 * M₂ ^ 2)) * t ^ (q - 3)) :=
          (ENNReal.ofReal_mul
            (mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _)))).symm
        _ = ENNReal.ofReal (M₂ ^ 2 * t ^ (q - 1)) := by
          congr 1
          rw [← twoInfinity_weight_identity ht]
          ring
        _ = ENNReal.ofReal (M₂ ^ 2) * ENNReal.ofReal (t ^ (q - 1)) :=
          ENNReal.ofReal_mul (sq_nonneg _)
    calc
      (μ {x | t < ‖T f x‖} * ENNReal.ofReal (t ^ (q - 1))) * A =
          (A * μ {x | t < ‖T f x‖}) * ENNReal.ofReal (t ^ (q - 1)) := by ring
      _ ≤ (ENNReal.ofReal (M₂ ^ 2) *
          ∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ) *
            ENNReal.ofReal (t ^ (q - 1)) := by gcongr
      _ = (ENNReal.ofReal (4 * M₂ ^ 2) *
          (∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ) *
            ENNReal.ofReal (t ^ (q - 3))) * A := by
        calc
          (ENNReal.ofReal (M₂ ^ 2) *
              ∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ) *
                ENNReal.ofReal (t ^ (q - 1)) =
              (ENNReal.ofReal (M₂ ^ 2) * ENNReal.ofReal (t ^ (q - 1))) *
                ∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ := by ring
          _ = (A * ENNReal.ofReal (4 * M₂ ^ 2) * ENNReal.ofReal (t ^ (q - 3))) *
                ∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ := by
              rw [hcoeff]
          _ = (ENNReal.ofReal (4 * M₂ ^ 2) *
              (∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ) *
                ENNReal.ofReal (t ^ (q - 3))) * A := by ring
  rw [hout]
  have hintegral :
      (∫⁻ t in Ioi (0 : ℝ),
          μ {x | t < ‖T f x‖} * ENNReal.ofReal (t ^ (q - 1))) ≤
        ENNReal.ofReal (4 * M₂ ^ 2) *
          ∫⁻ t in Ioi (0 : ℝ),
            (∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ) *
              ENNReal.ofReal (t ^ (q - 3)) := by
    calc
      (∫⁻ t in Ioi (0 : ℝ),
          μ {x | t < ‖T f x‖} * ENNReal.ofReal (t ^ (q - 1))) ≤
          ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (4 * M₂ ^ 2) *
            ((∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ) *
              ENNReal.ofReal (t ^ (q - 3))) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        simpa only [mul_assoc] using hweighted t (mem_Ioi.mp ht)
      _ = ENNReal.ofReal (4 * M₂ ^ 2) *
          ∫⁻ t in Ioi (0 : ℝ),
            (∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ) *
              ENNReal.ofReal (t ^ (q - 3)) := by
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc
    ENNReal.ofReal q *
        ∫⁻ t in Ioi (0 : ℝ), μ {x | t < ‖T f x‖} * ENNReal.ofReal (t ^ (q - 1)) ≤
      ENNReal.ofReal q * (ENNReal.ofReal (4 * M₂ ^ 2) *
        ∫⁻ t in Ioi (0 : ℝ),
          (∫⁻ x, ‖interpolationHigh f (t / (2 * MTop)) x‖ₑ ^ (2 : ℕ) ∂μ) *
            ENNReal.ofReal (t ^ (q - 3))) := by gcongr
    _ = (ENNReal.ofReal q * ENNReal.ofReal (4 * M₂ ^ 2) *
          ENNReal.ofReal ((2 * MTop) ^ (q - 2)) / ENNReal.ofReal (q - 2)) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ q) ∂μ := by
      have hlayer := twoInfinity_high_tail_layercake (μ := μ) f hf hq hMTop
      have hp0 : ENNReal.ofReal (q - 2) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (by linarith)).ne'
      have hptop : ENNReal.ofReal (q - 2) ≠ ∞ := ENNReal.ofReal_ne_top
      have hdiv := (ENNReal.eq_div_iff hp0 hptop).mpr hlayer
      rw [hdiv]
      simp only [div_eq_mul_inv]
      ring

end Interpolation

end QuadraticCarleson
