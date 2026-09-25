/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundBadPart
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The logarithmic low-oscillatory majorant

The low part of the positive theorem is bounded off a Calderón--Zygmund atom
by

`min (1 / d) (D * ℓ / d²)`.

This file proves the exact one-dimensional integral behind the paper's
`O(B)` estimate. The transition occurs at distance `D * ℓ`: the first part
integrates to `log D`, and the inverse-square tail integrates to `1`.
-/

@[expose] public section

open MeasureTheory Set

namespace QuadraticCarleson


/-- The positive-half-line form of the low-oscillatory kernel majorant. -/
noncomputable def positiveLowDecay (D ℓ x : ℝ) : ℝ :=
  min (1 / x) (D * ℓ / x ^ 2)

/-- The low-oscillatory majorant is integrable beyond a positive atom scale. -/
theorem integrableOn_positiveLowDecay_Ioi (D ℓ : ℝ) (hD : 1 ≤ D) (hℓ : 0 < ℓ) :
    IntegrableOn (positiveLowDecay D ℓ) (Ioi ℓ) := by
  have hpow : IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℝ)) (Ioi ℓ) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hℓ
  have hsecond : IntegrableOn (fun x : ℝ ↦ D * ℓ * x ^ (-2 : ℝ)) (Ioi ℓ) :=
    hpow.const_mul (D * ℓ)
  have hmeas : AEStronglyMeasurable (positiveLowDecay D ℓ)
      (volume.restrict (Ioi ℓ)) := by
    exact (((measurable_const.div measurable_id).min
      ((measurable_const.mul measurable_const).div
        (measurable_id.pow_const 2))).aestronglyMeasurable)
  apply hsecond.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hℓ.trans hx
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hsecond0 : 0 ≤ D * ℓ / x ^ 2 :=
    div_nonneg (mul_nonneg hD0 hℓ.le) (sq_nonneg x)
  have hmin0 : 0 ≤ positiveLowDecay D ℓ x :=
    le_min (one_div_nonneg.mpr hx0.le) hsecond0
  rw [Real.norm_eq_abs, abs_of_nonneg hmin0]
  calc
    positiveLowDecay D ℓ x ≤ D * ℓ / x ^ 2 := min_le_right _ _
    _ = D * ℓ * x ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hx0.le, Real.rpow_two]
      ring

/-- Exact evaluation of the positive-half-line logarithmic majorant. -/
theorem integral_positiveLowDecay_Ioi (D ℓ : ℝ) (hD : 1 ≤ D) (hℓ : 0 < ℓ) :
    ∫ x in Ioi ℓ, positiveLowDecay D ℓ x = Real.log D + 1 := by
  have hDℓ : 0 < D * ℓ := mul_pos (zero_lt_one.trans_le hD) hℓ
  have hle : ℓ ≤ D * ℓ := by nlinarith
  have hg := integrableOn_positiveLowDecay_Ioi D ℓ hD hℓ
  have hgD : IntegrableOn (positiveLowDecay D ℓ) (Ioi (D * ℓ)) :=
    hg.mono_set (Ioi_subset_Ioi hle)
  rw [← intervalIntegral.integral_interval_add_Ioi hg hgD]
  have hinterval : (∫ x in ℓ..D * ℓ, positiveLowDecay D ℓ x) = Real.log D := by
    calc
      (∫ x in ℓ..D * ℓ, positiveLowDecay D ℓ x) =
          ∫ x in ℓ..D * ℓ, 1 / x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hle] at hx
        have hx0 : 0 < x := hℓ.trans_le hx.1
        simp only [positiveLowDecay]
        rw [min_eq_left]
        apply (div_le_div_iff₀ hx0 (sq_pos_of_pos hx0)).2
        nlinarith [hx.2]
      _ = Real.log ((D * ℓ) / ℓ) := integral_one_div_of_pos hℓ hDℓ
      _ = Real.log D := by rw [mul_div_cancel_right₀ D hℓ.ne']
  have htail : (∫ x in Ioi (D * ℓ), positiveLowDecay D ℓ x) = 1 := by
    calc
      (∫ x in Ioi (D * ℓ), positiveLowDecay D ℓ x) =
          ∫ x in Ioi (D * ℓ), D * ℓ * x ^ (-2 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hx0 : 0 < x := hDℓ.trans hx
        simp only [positiveLowDecay]
        rw [min_eq_right]
        · rw [Real.rpow_neg hx0.le, Real.rpow_two]
          ring
        · calc
            D * ℓ / x ^ 2 ≤ 1 / x := by
              rw [div_le_iff₀ (sq_pos_of_pos hx0)]
              calc
                D * ℓ ≤ x := le_of_lt hx
                _ = 1 / x * x ^ 2 := by field_simp
            _ = 1 / x := rfl
      _ = D * ℓ * (1 / (D * ℓ)) := by
        rw [integral_const_mul]
        rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hDℓ]
        rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        ring
      _ = 1 := by simpa only [one_div] using mul_inv_cancel₀ hDℓ.ne'
  rw [hinterval, htail]

/-- The translation-invariant radial form of the majorant. -/
noncomputable def lowDecayMajorant (D ℓ z x : ℝ) : ℝ :=
  min (1 / |x - z|) (D * ℓ / |x - z| ^ 2)

/-- On the right of the center, the radial majorant is its positive form. -/
theorem integral_lowDecayMajorant_Ioi (D ℓ z : ℝ) (hD : 1 ≤ D) (hℓ : 0 < ℓ) :
    ∫ x in Ioi (z + ℓ), lowDecayMajorant D ℓ z x = Real.log D + 1 := by
  have hpres := measurePreserving_add_right (volume : Measure ℝ) z
  have hemb := (MeasurableEquiv.addRight z).measurableEmbedding
  have hmap := hpres.setIntegral_preimage_emb hemb
    (lowDecayMajorant D ℓ z) (Ioi (z + ℓ))
  have hset : (fun x : ℝ ↦ x + z) ⁻¹' Ioi (z + ℓ) = Ioi ℓ := by
    ext x
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [hset] at hmap
  calc
    (∫ x in Ioi (z + ℓ), lowDecayMajorant D ℓ z x) =
        ∫ x in Ioi ℓ, lowDecayMajorant D ℓ z (x + z) := hmap.symm
    _ = ∫ x in Ioi ℓ, positiveLowDecay D ℓ x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := hℓ.trans hx
      simp only [lowDecayMajorant, positiveLowDecay, add_sub_cancel_right,
        abs_of_pos hx0]
    _ = Real.log D + 1 := integral_positiveLowDecay_Ioi D ℓ hD hℓ

/-- Reflection gives the same logarithmic mass on the left of the center. -/
theorem integral_lowDecayMajorant_Iio (D ℓ z : ℝ) (hD : 1 ≤ D) (hℓ : 0 < ℓ) :
    ∫ x in Iio (z - ℓ), lowDecayMajorant D ℓ z x = Real.log D + 1 := by
  have hpres := measurePreserving_add_right (volume : Measure ℝ) z
  have hemb := (MeasurableEquiv.addRight z).measurableEmbedding
  have hmap := hpres.setIntegral_preimage_emb hemb
    (lowDecayMajorant D ℓ z) (Iio (z - ℓ))
  have hset : (fun x : ℝ ↦ x + z) ⁻¹' Iio (z - ℓ) = Iio (-ℓ) := by
    ext x
    simp only [mem_preimage, mem_Iio]
    constructor <;> intro h <;> linarith
  rw [hset] at hmap
  calc
    (∫ x in Iio (z - ℓ), lowDecayMajorant D ℓ z x) =
        ∫ x in Iio (-ℓ), lowDecayMajorant D ℓ z (x + z) := hmap.symm
    _ = ∫ x in Iio (-ℓ), min (1 / |x|) (D * ℓ / |x| ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Iio
      intro x hx
      simp only [lowDecayMajorant, add_sub_cancel_right]
    _ = ∫ x in Iic (-ℓ), min (1 / |x|) (D * ℓ / |x| ^ 2) := by
      rw [integral_Iic_eq_integral_Iio]
    _ = ∫ x in Ioi ℓ, min (1 / |-x|) (D * ℓ / |-x| ^ 2) := by
      exact (integral_comp_neg_Ioi ℓ
        (fun x : ℝ ↦ min (1 / |x|) (D * ℓ / |x| ^ 2))).symm
    _ = ∫ x in Ioi ℓ, positiveLowDecay D ℓ x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := hℓ.trans hx
      simp only [abs_neg, abs_of_pos hx0, positiveLowDecay]
    _ = Real.log D + 1 := integral_positiveLowDecay_Ioi D ℓ hD hℓ

/-- The complement of the interval of radius `ℓ` consists of its two open
tails. -/
theorem compl_centeredInterval_radius (z ℓ : ℝ) :
    (Icc (z - ℓ) (z + ℓ))ᶜ = Iio (z - ℓ) ∪ Ioi (z + ℓ) := by
  ext x
  simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi,
    not_and_or, not_le]

/-- Exact logarithmic mass of the low-oscillatory majorant away from an atom.
This is the scalar integral used in the paper's estimate preceding the
lacunary middle-range decomposition. -/
theorem integral_lowDecayMajorant_compl (D ℓ z : ℝ) (hD : 1 ≤ D) (hℓ : 0 < ℓ) :
    ∫ x in (Icc (z - ℓ) (z + ℓ))ᶜ, lowDecayMajorant D ℓ z x =
      2 * (Real.log D + 1) := by
  have hdis : Disjoint (Iio (z - ℓ)) (Ioi (z + ℓ)) := by
    rw [Set.disjoint_left]
    intro x hxl hxr
    simp only [mem_Iio] at hxl
    simp only [mem_Ioi] at hxr
    linarith
  have hpos : 0 < D := zero_lt_one.trans_le hD
  have hmeas : AEStronglyMeasurable (lowDecayMajorant D ℓ z) := by
    have habs : Measurable (fun x : ℝ ↦ |x - z|) :=
      (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
    exact (((measurable_const.div habs).min
      ((measurable_const.mul measurable_const).div (habs.pow_const 2))).aestronglyMeasurable)
  have hbound : ∀ x ∉ Icc (z - ℓ) (z + ℓ),
      ‖lowDecayMajorant D ℓ z x‖ ≤
        D * ℓ * (1 / |x - z| ^ 2) := by
    intro x hx
    have hdist : ℓ < |x - z| := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rw [abs_sub_comm, lt_abs]
      rcases hx with hx | hx
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hmin0 : 0 ≤ lowDecayMajorant D ℓ z x := by
      apply le_min
      · exact one_div_nonneg.mpr (abs_nonneg _)
      · exact div_nonneg (mul_nonneg hpos.le hℓ.le) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hmin0]
    calc
      lowDecayMajorant D ℓ z x ≤ D * ℓ / |x - z| ^ 2 := min_le_right _ _
      _ = D * ℓ * (1 / |x - z| ^ 2) := by ring
  have hinv := integrableOn_inv_abs_sub_sq_compl_tripleCenteredInterval z
    (2 * ℓ / 3) (by positivity)
  have hsetTriple : tripleCenteredInterval z (2 * ℓ / 3) =
      Icc (z - ℓ) (z + ℓ) := by
    ext x
    simp only [tripleCenteredInterval, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [hsetTriple] at hinv
  have hmaj : IntegrableOn (fun x : ℝ ↦ D * ℓ * (1 / |x - z| ^ 2))
      (Icc (z - ℓ) (z + ℓ))ᶜ := hinv.const_mul (D * ℓ)
  have hleft : IntegrableOn (lowDecayMajorant D ℓ z) (Iio (z - ℓ)) := by
    have hmajleft : IntegrableOn (fun x : ℝ ↦ D * ℓ * (1 / |x - z| ^ 2))
        (Iio (z - ℓ)) := hmaj.mono_set (by
      rw [compl_centeredInterval_radius]
      exact subset_union_left)
    apply hmajleft.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    apply hbound x
    simp only [mem_Icc, not_and_or, not_le]
    exact Or.inl hx
  have hright : IntegrableOn (lowDecayMajorant D ℓ z) (Ioi (z + ℓ)) := by
    have hmajright : IntegrableOn (fun x : ℝ ↦ D * ℓ * (1 / |x - z| ^ 2))
        (Ioi (z + ℓ)) := hmaj.mono_set (by
      rw [compl_centeredInterval_radius]
      exact subset_union_right)
    apply hmajright.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply hbound x
    simp only [mem_Icc, not_and_or, not_le]
    exact Or.inr hx
  rw [compl_centeredInterval_radius,
    setIntegral_union hdis measurableSet_Ioi hleft hright,
    integral_lowDecayMajorant_Iio D ℓ z hD hℓ,
    integral_lowDecayMajorant_Ioi D ℓ z hD hℓ]
  ring

/-- Integrability accompanying the exact logarithmic-mass formula. -/
theorem integrableOn_lowDecayMajorant_compl
    (D ℓ z : ℝ) (hD : 1 ≤ D) (hℓ : 0 < ℓ) :
    IntegrableOn (lowDecayMajorant D ℓ z) (Icc (z - ℓ) (z + ℓ))ᶜ := by
  have hpos : 0 < D := zero_lt_one.trans_le hD
  have hmeas : AEStronglyMeasurable (lowDecayMajorant D ℓ z) := by
    have habs : Measurable (fun x : ℝ ↦ |x - z|) :=
      (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
    exact (((measurable_const.div habs).min
      ((measurable_const.mul measurable_const).div (habs.pow_const 2))).aestronglyMeasurable)
  have hinv := integrableOn_inv_abs_sub_sq_compl_tripleCenteredInterval z
    (2 * ℓ / 3) (by positivity)
  have hsetTriple : tripleCenteredInterval z (2 * ℓ / 3) =
      Icc (z - ℓ) (z + ℓ) := by
    ext x
    simp only [tripleCenteredInterval, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [hsetTriple] at hinv
  have hmaj : IntegrableOn (fun x : ℝ ↦ D * ℓ * (1 / |x - z| ^ 2))
      (Icc (z - ℓ) (z + ℓ))ᶜ := hinv.const_mul (D * ℓ)
  apply hmaj.mono' hmeas.restrict
  have hcompl : MeasurableSet (Icc (z - ℓ) (z + ℓ))ᶜ := measurableSet_Icc.compl
  filter_upwards [ae_restrict_mem hcompl] with x hx
  have hdist : ℓ < |x - z| := by
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    rw [abs_sub_comm, lt_abs]
    rcases hx with hx | hx
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hmin0 : 0 ≤ lowDecayMajorant D ℓ z x := by
    apply le_min
    · exact one_div_nonneg.mpr (abs_nonneg _)
    · exact div_nonneg (mul_nonneg hpos.le hℓ.le) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hmin0]
  calc
    lowDecayMajorant D ℓ z x ≤ D * ℓ / |x - z| ^ 2 := min_le_right _ _
    _ = D * ℓ * (1 / |x - z| ^ 2) := by ring

/-- With the paper's choice `D = 2^(2B)`, the logarithmic mass is bounded by
an explicit constant times `B + 1`. This is the precise scalar content of
the displayed `≲ B` estimate (including the harmless `B = 0` case). -/
theorem integral_lowDecayMajorant_two_pow_le (B : ℕ) (ℓ z : ℝ) (hℓ : 0 < ℓ) :
    ∫ x in (Icc (z - ℓ) (z + ℓ))ᶜ,
        lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ℓ z x ≤
      4 * (B + 1 : ℝ) := by
  have hD : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * B) := by
    exact one_le_pow₀ (by norm_num)
  rw [integral_lowDecayMajorant_compl ((2 : ℝ) ^ (2 * B)) ℓ z hD hℓ]
  rw [Real.log_pow]
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hB : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
  push_cast
  nlinarith

/-- A measurable nonnegative function dominated by the paper's dyadic
low-oscillatory majorant has the required `O(B)` integral. This packages the
scalar calculation in the form used for each Calderón--Zygmund bad atom. -/
theorem integral_le_four_mul_succ_of_le_lowDecayMajorant
    (F : ℝ → ℝ) (A ℓ z : ℝ) (B : ℕ)
    (hA : 0 ≤ A) (hℓ : 0 < ℓ)
    (hFmeas : AEStronglyMeasurable F
      (volume.restrict (Icc (z - ℓ) (z + ℓ))ᶜ))
    (hFnonneg : ∀ x ∉ Icc (z - ℓ) (z + ℓ), 0 ≤ F x)
    (hFbound : ∀ x ∉ Icc (z - ℓ) (z + ℓ),
      F x ≤ A * lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ℓ z x) :
    ∫ x in (Icc (z - ℓ) (z + ℓ))ᶜ, F x ≤
      4 * (B + 1 : ℝ) * A := by
  have hD : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * B) := one_le_pow₀ (by norm_num)
  have hdecay := integrableOn_lowDecayMajorant_compl
    ((2 : ℝ) ^ (2 * B)) ℓ z hD hℓ
  have hscaled : IntegrableOn
      (fun x ↦ A * lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ℓ z x)
      (Icc (z - ℓ) (z + ℓ))ᶜ := hdecay.const_mul A
  have hcompl : MeasurableSet (Icc (z - ℓ) (z + ℓ))ᶜ := measurableSet_Icc.compl
  have hFint : IntegrableOn F (Icc (z - ℓ) (z + ℓ))ᶜ := by
    apply hscaled.mono' hFmeas
    filter_upwards [ae_restrict_mem hcompl] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg x hx)]
    exact hFbound x hx
  calc
    (∫ x in (Icc (z - ℓ) (z + ℓ))ᶜ, F x) ≤
        ∫ x in (Icc (z - ℓ) (z + ℓ))ᶜ,
          A * lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ℓ z x := by
      apply integral_mono_ae hFint hscaled
      filter_upwards [ae_restrict_mem hcompl] with x hx
      exact hFbound x hx
    _ = A * ∫ x in (Icc (z - ℓ) (z + ℓ))ᶜ,
          lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ℓ z x := by
      rw [integral_const_mul]
    _ ≤ A * (4 * (B + 1 : ℝ)) := mul_le_mul_of_nonneg_left
      (integral_lowDecayMajorant_two_pow_le B ℓ z hℓ) hA
    _ = 4 * (B + 1 : ℝ) * A := by ring

end QuadraticCarleson
