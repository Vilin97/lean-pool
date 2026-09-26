/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodMaximal
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Strong `L^p` bounds for the centered Hardy--Littlewood maximal operator

This extends the already checked weak `(1,1)` estimate by the layer-cake
argument needed in the sparse finite-maximal lemma.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson


theorem lintegral_rpow_Ioo_zero
    {p t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    (∫⁻ a in Ioo (0 : ℝ) t, ENNReal.ofReal (a ^ (p - 2))) =
      ENNReal.ofReal (t ^ (p - 1) / (p - 1)) := by
  have hexp : -1 < p - 2 := by linarith
  have hint : IntegrableOn (fun a : ℝ ↦ a ^ (p - 2)) (Ioo 0 t) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff ht).2 hexp
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) t)] fun a : ℝ ↦ a ^ (p - 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    exact Real.rpow_nonneg ha.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le ht.le]
  rw [integral_rpow (Or.inl hexp)]
  congr 1
  rw [show p - 2 + 1 = p - 1 by ring,
    Real.zero_rpow (sub_pos.mpr hp).ne']
  ring

/-- The inner scalar integral produced after exchanging the layer-cake
integral with the spatial integral. -/
theorem lintegral_rpow_half_level_indicator
    {p : ℝ} (hp : 1 < p) (v : ℝ≥0∞) (hv : v ≠ ∞) :
    (∫⁻ a in Ioi (0 : ℝ),
        {a | ENNReal.ofReal (a / 2) < v}.indicator
          (fun a ↦ ENNReal.ofReal (a ^ (p - 2))) a) =
      ENNReal.ofReal ((2 * v.toReal) ^ (p - 1) / (p - 1)) := by
  by_cases hv0 : v = 0
  · subst v
    simp [Real.zero_rpow (sub_pos.mpr hp).ne']
  have hvpos : 0 < v.toReal := ENNReal.toReal_pos hv0 hv
  have hset : MeasurableSet {a : ℝ | ENNReal.ofReal (a / 2) < v} :=
    measurableSet_lt (measurable_id.div_const 2).ennreal_ofReal measurable_const
  rw [setLIntegral_indicator hset]
  have heq : {a | ENNReal.ofReal (a / 2) < v} ∩ Ioi (0 : ℝ) =
      Ioo 0 (2 * v.toReal) := by
    ext a
    simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨hav, ha⟩
      have hhalf : a / 2 < v.toReal :=
        (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hv).mp hav
      constructor
      · exact ha
      · linarith
    · rintro ⟨ha, hav⟩
      constructor
      · apply (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hv).mpr
        linarith
      · exact ha
  rw [heq]
  exact lintegral_rpow_Ioo_zero hp (mul_pos (by norm_num) hvpos)

theorem lintegral_rpow_half_level_indicator_mul
    {p : ℝ} (hp : 1 < p) (v : ℝ≥0∞) (hv : v ≠ ∞) :
    (∫⁻ a in Ioi (0 : ℝ),
        {a | ENNReal.ofReal (a / 2) < v}.indicator
          (fun a ↦ ENNReal.ofReal (a ^ (p - 2)) * v) a) =
      ENNReal.ofReal ((2 * v.toReal) ^ (p - 1) / (p - 1)) * v := by
  have hid (a : ℝ) :
      {a | ENNReal.ofReal (a / 2) < v}.indicator
          (fun a ↦ ENNReal.ofReal (a ^ (p - 2)) * v) a =
        {a | ENNReal.ofReal (a / 2) < v}.indicator
          (fun a ↦ ENNReal.ofReal (a ^ (p - 2))) a * v := by
    by_cases ha : ENNReal.ofReal (a / 2) < v <;> simp [ha]
  simp_rw [hid]
  rw [lintegral_mul_const' v _ hv, lintegral_rpow_half_level_indicator hp v hv]

/-- Algebraic normalization of the scalar factor in the strong-type proof. -/
theorem rpow_half_level_factor_mul
    {p : ℝ} (hp : 1 < p) (v : ℝ≥0∞) (hv : v ≠ ∞) :
    ENNReal.ofReal ((2 * v.toReal) ^ (p - 1) / (p - 1)) * v =
      ENNReal.ofReal ((2 : ℝ) ^ (p - 1) / (p - 1)) * v ^ p := by
  by_cases hv0 : v = 0
  · subst v
    have hp0 : 0 < p := lt_trans zero_lt_one hp
    simp [ENNReal.zero_rpow_of_pos hp0]
  have hvpos : 0 < v.toReal := ENNReal.toReal_pos hv0 hv
  rw [← ENNReal.ofReal_toReal hv]
  simp only [ENNReal.toReal_ofReal hvpos.le]
  rw [ENNReal.ofReal_rpow_of_nonneg hvpos.le (lt_trans zero_lt_one hp).le]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hvpos.le]
  have hvpow : v.toReal ^ p = v.toReal ^ (p - 1) * v.toReal := by
    conv_lhs => rw [show p = (p - 1) + 1 by ring]
    rw [Real.rpow_add hvpos, Real.rpow_one]
  rw [hvpow]
  field_simp

/-- Tonelli converts the localized high-value contribution into the exact
`p`th moment. Pointwise finiteness is the only extra condition needed to use
`toReal` in the scalar calculation. -/
theorem lintegral_rpow_high_value_tails
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hfinite : ∀ y, f y ≠ ∞)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ y,
        {y : ℝ | ENNReal.ofReal (a / 2) < f y}.indicator
          (fun y ↦ ENNReal.ofReal (a ^ (p - 2)) * f y) y) =
      ENNReal.ofReal ((2 : ℝ) ^ (p - 1) / (p - 1)) *
        ∫⁻ y, f y ^ p := by
  have hpow : Measurable (fun a : ℝ ↦ ENNReal.ofReal (a ^ (p - 2))) := by
    apply Measurable.ennreal_ofReal
    exact measurable_of_continuousOn_compl_singleton 0
      (continuousOn_id.rpow_const (fun x hx ↦ Or.inl hx))
  have hmset : MeasurableSet
      {z : ℝ × ℝ | ENNReal.ofReal (z.1 / 2) < f z.2} :=
    measurableSet_lt (measurable_fst.div_const 2).ennreal_ofReal
      (hf.comp measurable_snd)
  have hm : Measurable (fun z : ℝ × ℝ ↦
      {z : ℝ × ℝ | ENNReal.ofReal (z.1 / 2) < f z.2}.indicator
        (fun z ↦ ENNReal.ofReal (z.1 ^ (p - 2)) * f z.2) z) :=
    ((hpow.comp measurable_fst).mul (hf.comp measurable_snd)).indicator hmset
  have hswap := lintegral_lintegral_swap
    (f := fun a y : ℝ ↦
      {z : ℝ × ℝ | ENNReal.ofReal (z.1 / 2) < f z.2}.indicator
        (fun z ↦ ENNReal.ofReal (z.1 ^ (p - 2)) * f z.2) (a, y))
    (μ := volume.restrict (Ioi (0 : ℝ))) (ν := (volume : Measure ℝ))
    hm.aemeasurable
  have hid (a y : ℝ) :
      {z : ℝ × ℝ | ENNReal.ofReal (z.1 / 2) < f z.2}.indicator
          (fun z ↦ ENNReal.ofReal (z.1 ^ (p - 2)) * f z.2) (a, y) =
        {y : ℝ | ENNReal.ofReal (a / 2) < f y}.indicator
          (fun y ↦ ENNReal.ofReal (a ^ (p - 2)) * f y) y := rfl
  simp only [hid] at hswap
  rw [hswap]
  have hinner (y : ℝ) :
      (∫⁻ a in Ioi (0 : ℝ),
        {y : ℝ | ENNReal.ofReal (a / 2) < f y}.indicator
          (fun _ ↦ ENNReal.ofReal (a ^ (p - 2)) * f y) y) =
        ENNReal.ofReal ((2 : ℝ) ^ (p - 1) / (p - 1)) * f y ^ p := by
    calc
      _ = (∫⁻ a in Ioi (0 : ℝ),
          {a : ℝ | ENNReal.ofReal (a / 2) < f y}.indicator
            (fun a ↦ ENNReal.ofReal (a ^ (p - 2)) * f y) a) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro a _
        rfl
      _ = ENNReal.ofReal ((2 * (f y).toReal) ^ (p - 1) / (p - 1)) * f y :=
        lintegral_rpow_half_level_indicator_mul hp (f y) (hfinite y)
      _ = _ := rpow_half_level_factor_mul hp (f y) (hfinite y)
  calc
    _ = ∫⁻ y, ENNReal.ofReal ((2 : ℝ) ^ (p - 1) / (p - 1)) * f y ^ p :=
      lintegral_congr hinner
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The explicit constant obtained from the weak `(1,1)` layer-cake proof. -/
noncomputable def centeredHardyLittlewoodRpowConstant (p : ℝ) : ℝ :=
  8 * p * ((2 : ℝ) ^ (p - 1) / (p - 1))

theorem centeredHardyLittlewoodRpowConstant_pos {p : ℝ} (hp : 1 < p) :
    0 < centeredHardyLittlewoodRpowConstant p := by
  unfold centeredHardyLittlewoodRpowConstant
  positivity

/-- Uniform strong `L^p` estimate for each finite-value truncation of the
genuine centered maximal function. -/
theorem centeredHardyLittlewoodMaximal_truncated_rpow_lintegral_le
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hfinite : ∀ y, f y ≠ ∞)
    {p : ℝ} (hp : 1 < p) (n : ℕ) :
    (∫⁻ x, (min (centeredHardyLittlewoodMaximal f x) (n : ℝ≥0∞)) ^ p) ≤
      ENNReal.ofReal (centeredHardyLittlewoodRpowConstant p) *
        ∫⁻ x, f x ^ p := by
  let M := centeredHardyLittlewoodMaximal f
  let g : ℝ → ℝ := fun x ↦ (min (M x) (n : ℝ≥0∞)).toReal
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hM : Measurable M := measurable_centeredHardyLittlewoodMaximal hf
  have hg : Measurable g := (hM.min measurable_const).ennreal_toReal
  have hfin (x : ℝ) : min (M x) (n : ℝ≥0∞) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (ENNReal.natCast_lt_top n))
  have hid (x : ℝ) : ENNReal.ofReal (g x ^ p) =
      (min (M x) (n : ℝ≥0∞)) ^ p := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le,
      ENNReal.ofReal_toReal (hfin x)]
  change (∫⁻ x, (min (M x) (n : ℝ≥0∞)) ^ p) ≤ _
  simp_rw [← hid]
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul volume
    (Filter.Eventually.of_forall fun x ↦ ENNReal.toReal_nonneg)
    hg.aemeasurable hp0]
  have hpoint (a : ℝ) (ha : 0 < a) :
      volume {x | a < g x} * ENNReal.ofReal (a ^ (p - 1)) ≤
        8 * ∫⁻ y,
          {y | ENNReal.ofReal (a / 2) < f y}.indicator
            (fun y ↦ ENNReal.ofReal (a ^ (p - 2)) * f y) y := by
    have hsub : {x | a < g x} ⊆ {x | ENNReal.ofReal a < M x} := by
      intro x hx
      exact lt_of_lt_of_le
        ((ENNReal.ofReal_lt_iff_lt_toReal ha.le (hfin x)).mpr hx)
        (min_le_left _ _)
    have hhalf : 2 * ENNReal.ofReal (a / 2) = ENNReal.ofReal a := by
      rw [← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hw := centeredHardyLittlewoodMaximal_localized_weak_bound
      f (ENNReal.ofReal (a / 2))
    rw [hhalf] at hw
    have hpower : ENNReal.ofReal (a ^ (p - 1)) =
        ENNReal.ofReal a * ENNReal.ofReal (a ^ (p - 2)) := by
      rw [← ENNReal.ofReal_mul ha.le]
      congr 1
      rw [show p - 1 = 1 + (p - 2) by ring, Real.rpow_add ha,
        Real.rpow_one]
    rw [hpower]
    calc
      volume {x | a < g x} *
          (ENNReal.ofReal a * ENNReal.ofReal (a ^ (p - 2))) =
          (ENNReal.ofReal a * volume {x | a < g x}) *
            ENNReal.ofReal (a ^ (p - 2)) := by ac_rfl
      _ ≤ (ENNReal.ofReal a * volume {x | ENNReal.ofReal a < M x}) *
            ENNReal.ofReal (a ^ (p - 2)) := by
        gcongr
      _ ≤ (8 * ∫⁻ y,
            {y | ENNReal.ofReal (a / 2) < f y}.indicator f y) *
            ENNReal.ofReal (a ^ (p - 2)) :=
        mul_le_mul' hw le_rfl
      _ = 8 * ∫⁻ y,
          {y | ENNReal.ofReal (a / 2) < f y}.indicator
            (fun y ↦ ENNReal.ofReal (a ^ (p - 2)) * f y) y := by
        rw [mul_assoc]
        congr 1
        rw [mul_comm]
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro y
        by_cases hy : ENNReal.ofReal (a / 2) < f y <;> simp [hy, mul_comm]
  calc
    ENNReal.ofReal p *
        (∫⁻ a in Ioi (0 : ℝ),
          volume {x | a < g x} * ENNReal.ofReal (a ^ (p - 1))) ≤
      ENNReal.ofReal p *
        (∫⁻ a in Ioi (0 : ℝ), 8 * ∫⁻ y,
          {y | ENNReal.ofReal (a / 2) < f y}.indicator
            (fun y ↦ ENNReal.ofReal (a ^ (p - 2)) * f y) y) := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      exact hpoint a ha
    _ = ENNReal.ofReal p *
        (8 * (ENNReal.ofReal ((2 : ℝ) ^ (p - 1) / (p - 1)) *
          ∫⁻ y, f y ^ p)) := by
      rw [lintegral_const_mul' 8 _ (by norm_num),
        lintegral_rpow_high_value_tails hf hfinite hp]
    _ = ENNReal.ofReal (centeredHardyLittlewoodRpowConstant p) *
          ∫⁻ y, f y ^ p := by
      rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
        ← mul_assoc, ← ENNReal.ofReal_mul hp0.le,
        ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ p * 8)]
      unfold centeredHardyLittlewoodRpowConstant
      congr 2
      ring

/-- Increasing finite truncations recover an extended nonnegative real
power whenever the exponent is positive. -/
theorem iSup_min_nat_rpow (v : ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (⨆ n : ℕ, (min v (n : ℝ≥0∞)) ^ p) = v ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  apply le_antisymm
  · apply iSup_le
    intro n
    exact ENNReal.rpow_le_rpow (min_le_left _ _) hp0.le
  · by_cases hv : v = ∞
    · subst v
      simp only [min_top_left, ENNReal.top_rpow_of_pos hp0]
      rw [← ENNReal.iSup_natCast]
      apply iSup_mono
      intro n
      by_cases hn : n = 0
      · subst n
        simp
      · exact ENNReal.le_rpow_self_of_one_le
          (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)) hp
    · obtain ⟨n, hn⟩ := exists_nat_ge v.toReal
      have hvn : v ≤ (n : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_toReal hv]
        exact_mod_cast ENNReal.ofReal_le_ofReal hn
      calc
        v ^ p = (min v (n : ℝ≥0∞)) ^ p := by rw [min_eq_left hvn]
        _ ≤ ⨆ n : ℕ, (min v (n : ℝ≥0∞)) ^ p :=
          le_iSup (fun n : ℕ ↦ (min v (n : ℝ≥0∞)) ^ p) n

/-- Strong `L^p` estimate for the genuine centered rational-radius maximal
operator, for every real exponent `p > 1`. -/
theorem centeredHardyLittlewoodMaximal_rpow_lintegral_le
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hfinite : ∀ y, f y ≠ ∞)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, centeredHardyLittlewoodMaximal f x ^ p) ≤
      ENNReal.ofReal (centeredHardyLittlewoodRpowConstant p) *
        ∫⁻ x, f x ^ p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hM := measurable_centeredHardyLittlewoodMaximal hf
  have hmeas (n : ℕ) : Measurable (fun x ↦
      (min (centeredHardyLittlewoodMaximal f x) (n : ℝ≥0∞)) ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp (hM.min measurable_const)
  have hmono : Monotone (fun n : ℕ ↦ fun x ↦
      (min (centeredHardyLittlewoodMaximal f x) (n : ℝ≥0∞)) ^ p) := by
    intro m n hmn x
    exact ENNReal.rpow_le_rpow (min_le_min le_rfl (by exact_mod_cast hmn)) hp0.le
  have hid : (fun x ↦ centeredHardyLittlewoodMaximal f x ^ p) =
      (fun x ↦ ⨆ n : ℕ,
        (min (centeredHardyLittlewoodMaximal f x) (n : ℝ≥0∞)) ^ p) := by
    funext x
    exact (iSup_min_nat_rpow _ hp.le).symm
  rw [hid, lintegral_iSup hmeas hmono]
  exact iSup_le (centeredHardyLittlewoodMaximal_truncated_rpow_lintegral_le
    hf hfinite hp)

end QuadraticCarleson
