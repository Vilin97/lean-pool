/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.Definitions

/-!
# One-dimensional centered maximal estimates

The fixed-height quadratic `TT*` argument uses a one-dimensional centered
maximal estimate. The covering argument below proves the needed weak estimate
directly from Mathlib's Vitali theorem, with an explicit constant.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QuadraticCarleson

/-- The weak covering estimate for a bounded family of centered intervals.
Each point of `E` chooses an interval on which the average is at least `a`.
The selected radii need not be measurable, and `E` need not be measurable. -/
theorem centered_average_covering_weak_bound
    (f : ℝ → ℝ≥0∞) (E : Set ℝ) (r : ℝ → ℝ) (R : ℝ)
    (hrpos : ∀ x ∈ E, 0 < r x) (hrbound : ∀ x ∈ E, r x ≤ R)
    (a : ℝ≥0∞)
    (havg : ∀ x ∈ E, a * volume (closedBall x (r x)) ≤
      ∫⁻ y in closedBall x (r x), f y) :
    a * volume E ≤ 4 * ∫⁻ y, f y := by
  obtain ⟨U, hUE, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      E id r R hrbound 4 (by norm_num)
  have hpair : Pairwise (fun i j : U ↦ Disjoint
      (closedBall (i : ℝ) (r i)) (closedBall (j : ℝ) (r j))) := by
    intro i j hij
    exact hdisj i.property j.property (fun h ↦ hij (Subtype.ext h))
  have hpos (i : U) : 0 < volume (closedBall (i : ℝ) (r i)) := by
    rw [Real.volume_closedBall, ENNReal.ofReal_pos]
    exact mul_pos (by norm_num) (hrpos i (hUE i.property))
  have hcount : Countable U := by
    have hh := Measure.countable_meas_pos_of_disjoint_iUnion (μ := (volume : Measure ℝ))
      (fun i : U ↦ measurableSet_closedBall (x := (i : ℝ)) (ε := r i)) hpair
    have hid : {i : U | 0 < volume (closedBall (i : ℝ) (r i))} = univ :=
      Set.eq_univ_of_forall hpos
    rw [hid, Set.countable_univ_iff] at hh
    exact hh
  let : Countable U := hcount
  have hsubset : E ⊆ ⋃ i : U, closedBall (i : ℝ) (4 * r i) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy (mem_closedBall_self (hrpos x hx).le)⟩
  have hvolume (i : U) : volume (closedBall (i : ℝ) (4 * r i)) =
      4 * volume (closedBall (i : ℝ) (r i)) := by
    rw [Real.volume_closedBall, Real.volume_closedBall]
    rw [show 2 * (4 * r i) = 4 * (2 * r i) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  calc
    a * volume E ≤ a * ∑' i : U, volume (closedBall (i : ℝ) (4 * r i)) :=
      mul_le_mul' le_rfl ((measure_mono hsubset).trans (measure_iUnion_le _))
    _ = 4 * ∑' i : U, a * volume (closedBall (i : ℝ) (r i)) := by
      simp_rw [hvolume]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      ring
    _ ≤ 4 * ∑' i : U, ∫⁻ y in closedBall (i : ℝ) (r i), f y := by
      gcongr with i
      exact havg i (hUE i.property)
    _ = 4 * ∫⁻ y in ⋃ i : U, closedBall (i : ℝ) (r i), f y := by
      rw [lintegral_iUnion (fun _ ↦ measurableSet_closedBall) hpair]
    _ ≤ 4 * ∫⁻ y, f y := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/-- The centered interval average, allowing nonnegative extended-valued input. -/
noncomputable def centeredAverage (r : ℝ) (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in closedBall x r, f y) / ENNReal.ofReal (2 * r)

theorem measurable_centeredAverage (r : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (centeredAverage r f) := by
  have hset : MeasurableSet {z : ℝ × ℝ | dist z.2 z.1 ≤ r} :=
    measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  have hm : Measurable (fun z : ℝ × ℝ ↦
      {z : ℝ × ℝ | dist z.2 z.1 ≤ r}.indicator (fun z ↦ f z.2) z) :=
    (hf.comp measurable_snd).indicator hset
  have hint := hm.lintegral_prod_right' (ν := (volume : Measure ℝ))
  have hid (x : ℝ) :
      (∫⁻ y, {z : ℝ × ℝ | dist z.2 z.1 ≤ r}.indicator (fun z ↦ f z.2) (x, y)) =
        ∫⁻ y in closedBall x r, f y := by
    rw [← lintegral_indicator measurableSet_closedBall]
    apply lintegral_congr
    intro y
    by_cases hy : dist y x ≤ r <;> simp [Set.indicator, hy, mem_closedBall]
  change Measurable (fun x ↦ (∫⁻ y in closedBall x r, f y) / ENNReal.ofReal (2 * r))
  simpa only [hid] using hint.div_const (ENNReal.ofReal (2 * r))

theorem le_centeredAverage_iff {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ≥0∞) (x : ℝ)
    (a : ℝ≥0∞) : a ≤ centeredAverage r f x ↔
      a * volume (closedBall x r) ≤ ∫⁻ y in closedBall x r, f y := by
  have hd : ENNReal.ofReal (2 * r) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  rw [centeredAverage, Real.volume_closedBall]
  exact ENNReal.le_div_iff_mul_le (Or.inl hd) (Or.inl ENNReal.ofReal_ne_top)

/-- The centered maximal average over a specified finite family of radii. -/
noncomputable def finiteCenteredMaximal {N : ℕ} (r : Fin N → ℝ)
    (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ i, centeredAverage (r i) f x

theorem measurable_finiteCenteredMaximal {N : ℕ} (r : Fin N → ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) : Measurable (finiteCenteredMaximal r f) :=
  Measurable.iSup (fun i ↦ measurable_centeredAverage (r i) hf)

/-- Uniform weak `(1,1)` control of the finite centered maximal operator.
The constant is independent of the number and sizes of the positive radii. -/
theorem finiteCenteredMaximal_weak_bound {N : ℕ} (r : Fin N → ℝ)
    (hr : ∀ i, 0 < r i) (f : ℝ → ℝ≥0∞) (a : ℝ≥0∞) :
    a * volume {x | a < finiteCenteredMaximal r f x} ≤ 4 * ∫⁻ y, f y := by
  classical
  let E : Set ℝ := {x | a < finiteCenteredMaximal r f x}
  have hex (x : E) : ∃ i, a < centeredAverage (r i) f x :=
    lt_iSup_iff.mp x.property
  choose i hi using hex
  let radii : ℝ → ℝ := fun x ↦ if hx : x ∈ E then r (i ⟨x, hx⟩) else 1
  have hselected (x : ℝ) (hx : x ∈ E) : radii x = r (i ⟨x, hx⟩) := by
    simp [radii, hx]
  have hradius (x : ℝ) (hx : x ∈ E) : 0 < radii x := by
    rw [hselected x hx]
    exact hr _
  have hbound (x : ℝ) (hx : x ∈ E) : radii x ≤ ∑ j, r j := by
    rw [hselected x hx]
    exact Finset.single_le_sum (fun j _ ↦ (hr j).le) (Finset.mem_univ _)
  apply centered_average_covering_weak_bound f E radii (∑ j, r j) hradius hbound a
  intro x hx
  rw [hselected x hx]
  exact (le_centeredAverage_iff (hr _) f x a).mp (hi ⟨x, hx⟩).le

/-- Removing values below a threshold changes any centered average by at
most that threshold. -/
theorem centeredAverage_le_truncate_add {r : ℝ} (hr : 0 < r)
    (f : ℝ → ℝ≥0∞) (b : ℝ≥0∞) (x : ℝ) :
    centeredAverage r f x ≤ centeredAverage r ({y | b < f y}.indicator f) x + b := by
  have hden : ENNReal.ofReal (2 * r) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hpoint (y : ℝ) : f y ≤ {y | b < f y}.indicator f y + b := by
    by_cases hy : b < f y
    · simpa [Set.indicator, hy] using (le_add_right le_rfl : f y ≤ f y + b)
    · simpa [Set.indicator, hy] using le_of_not_gt hy
  unfold centeredAverage
  calc
    _ ≤ (∫⁻ y in closedBall x r, {y | b < f y}.indicator f y + b) /
        ENNReal.ofReal (2 * r) :=
      ENNReal.div_le_div_right (lintegral_mono hpoint) _
    _ = ((∫⁻ y in closedBall x r, {y | b < f y}.indicator f y) +
        b * ENNReal.ofReal (2 * r)) / ENNReal.ofReal (2 * r) := by
      rw [lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ,
        Real.volume_closedBall]
    _ = _ := by
      rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hden ENNReal.ofReal_ne_top]

theorem finiteCenteredMaximal_le_truncate_add {N : ℕ} (r : Fin N → ℝ)
    (hr : ∀ i, 0 < r i) (f : ℝ → ℝ≥0∞) (b : ℝ≥0∞) (x : ℝ) :
    finiteCenteredMaximal r f x ≤
      finiteCenteredMaximal r ({y | b < f y}.indicator f) x + b := by
  apply iSup_le
  intro i
  exact (centeredAverage_le_truncate_add (hr i) f b x).trans
    (add_le_add (le_iSup (fun j ↦ centeredAverage (r j) ({y | b < f y}.indicator f) x) i) le_rfl)

/-- The localized weak estimate needed for the `L²` layer-cake argument.
Only the part of the input exceeding half the level contributes. -/
theorem finiteCenteredMaximal_localized_weak_bound {N : ℕ} (r : Fin N → ℝ)
    (hr : ∀ i, 0 < r i) (f : ℝ → ℝ≥0∞) (b : ℝ≥0∞) :
    (2 * b) * volume {x | 2 * b < finiteCenteredMaximal r f x} ≤
      8 * ∫⁻ y, {y | b < f y}.indicator f y := by
  have hsubset : {x | 2 * b < finiteCenteredMaximal r f x} ⊆
      {x | b < finiteCenteredMaximal r ({y | b < f y}.indicator f) x} := by
    intro x hx
    by_contra hn
    have hh := finiteCenteredMaximal_le_truncate_add r hr f b x
    have hle := add_le_add (le_of_not_gt hn) (le_rfl : b ≤ b)
    have hlast : finiteCenteredMaximal r f x ≤ 2 * b := by
      simpa only [two_mul] using hh.trans hle
    exact (not_lt_of_ge hlast) hx
  have hweak := finiteCenteredMaximal_weak_bound r hr ({y | b < f y}.indicator f) b
  calc
    _ ≤ 2 * (b * volume {x | b < finiteCenteredMaximal r ({y | b < f y}.indicator f) x}) := by
      rw [← mul_assoc]
      exact mul_le_mul' le_rfl (measure_mono hsubset)
    _ ≤ 2 * (4 * ∫⁻ y, {y | b < f y}.indicator f y) := mul_le_mul' le_rfl hweak
    _ = _ := by ring

/-- Integrating the high-value cutoff over all levels gives its exact second
moment. This scalar identity also covers an infinite input value. -/
theorem lintegral_half_level_indicator (v : ℝ≥0∞) :
    (∫⁻ a in Ioi (0 : ℝ), {a : ℝ | ENNReal.ofReal (a / 2) < v}.indicator
      (fun _ ↦ v) a) = 2 * v ^ 2 := by
  have hm : MeasurableSet {a : ℝ | ENNReal.ofReal (a / 2) < v} :=
    measurableSet_lt (measurable_id.div_const 2).ennreal_ofReal measurable_const
  rw [setLIntegral_indicator hm]
  by_cases hv : v = ⊤
  · subst v
    have hs : {a : ℝ | ENNReal.ofReal (a / 2) < ⊤} ∩ Ioi 0 = Ioi 0 := by
      ext a
      simp only [mem_inter_iff, mem_ofPred_eq, ENNReal.ofReal_lt_top, true_and]
    rw [hs]
    simp
  · lift v to ℝ≥0 using hv
    have hs : {a : ℝ | ENNReal.ofReal (a / 2) < (v : ℝ≥0∞)} ∩ Ioi 0 =
        Ioo 0 (2 * (v : ℝ)) := by
      ext a
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨ha, hapos⟩
        have hcmp : a / 2 < (v : ℝ) := by
          rw [← ENNReal.ofReal_coe_nnreal] at ha
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp ha
        exact ⟨hapos, by linarith⟩
      · rintro ⟨hapos, ha⟩
        refine ⟨?_, hapos⟩
        rw [← ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
        linarith
    rw [hs, lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_coe_nnreal]
    norm_num
    ring

/-- Tonelli converts the integrated localized weak bound into a second moment. -/
theorem lintegral_high_value_tails {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ y,
      {y : ℝ | ENNReal.ofReal (a / 2) < f y}.indicator f y) = 2 * ∫⁻ y, f y ^ 2 := by
  have hmset : MeasurableSet {z : ℝ × ℝ | ENNReal.ofReal (z.1 / 2) < f z.2} :=
    measurableSet_lt (measurable_fst.div_const 2).ennreal_ofReal (hf.comp measurable_snd)
  have hm : Measurable (fun z : ℝ × ℝ ↦
      {z : ℝ × ℝ | ENNReal.ofReal (z.1 / 2) < f z.2}.indicator (fun z ↦ f z.2) z) :=
    (hf.comp measurable_snd).indicator hmset
  have hswap := lintegral_lintegral_swap
    (f := fun a y : ℝ ↦
      {z : ℝ × ℝ | ENNReal.ofReal (z.1 / 2) < f z.2}.indicator (fun z ↦ f z.2) (a, y))
    (μ := volume.restrict (Ioi (0 : ℝ))) (ν := (volume : Measure ℝ)) hm.aemeasurable
  have hid (a y : ℝ) :
      {z : ℝ × ℝ | ENNReal.ofReal (z.1 / 2) < f z.2}.indicator (fun z ↦ f z.2) (a, y) =
      {y : ℝ | ENNReal.ofReal (a / 2) < f y}.indicator f y := rfl
  simp only [hid] at hswap
  rw [hswap]
  have hid' (y : ℝ) :
      (∫⁻ a in Ioi (0 : ℝ), {y : ℝ | ENNReal.ofReal (a / 2) < f y}.indicator f y) =
        2 * f y ^ 2 := by
    convert lintegral_half_level_indicator (f y) using 1
    apply lintegral_congr
    intro a
    simp [Set.indicator]
  simp_rw [hid']
  exact lintegral_const_mul _ (hf.pow_const 2)

/-- The second-moment layer-cake formula in the normalization used below. -/
theorem lintegral_ofReal_sq_eq_tail {g : ℝ → ℝ} (hg : Measurable g) (hnn : ∀ x, 0 ≤ g x) :
    (∫⁻ x, ENNReal.ofReal (g x ^ 2)) =
      ∫⁻ a in Ioi (0 : ℝ), volume {x | a < g x} * ENNReal.ofReal (2 * a) := by
  have hint (t : ℝ) (_ht : 0 < t) : IntervalIntegrable (fun a : ℝ ↦ 2 * a) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hnn' : ∀ᵐ a ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ 2 * a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact mul_nonneg (by norm_num) ha.le
  have h := lintegral_comp_eq_lintegral_meas_lt_mul volume
    (Filter.Eventually.of_forall hnn) hg.aemeasurable hint hnn'
  have hid (x : ℝ) : (∫ a in 0..g x, 2 * a) = g x ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  simpa only [hid] using h

/-- Each bounded truncation of the finite centered maximal function has the
uniform second-moment bound. -/
theorem finiteCenteredMaximal_truncated_sq_lintegral_le {N : ℕ}
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) (n : ℕ) :
    (∫⁻ x, (min (finiteCenteredMaximal r f x) (n : ℝ≥0∞)) ^ 2) ≤
      32 * ∫⁻ x, f x ^ 2 := by
  let M := finiteCenteredMaximal r f
  let g : ℝ → ℝ := fun x ↦ (min (M x) (n : ℝ≥0∞)).toReal
  have hM : Measurable M := measurable_finiteCenteredMaximal r hf
  have hg : Measurable g := (hM.min measurable_const).ennreal_toReal
  have hfin (x : ℝ) : min (M x) (n : ℝ≥0∞) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (ENNReal.natCast_lt_top n))
  have hid (x : ℝ) : ENNReal.ofReal (g x ^ 2) = (min (M x) (n : ℝ≥0∞)) ^ 2 := by
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin x)]
  change (∫⁻ x, (min (M x) (n : ℝ≥0∞)) ^ 2) ≤ _
  simp_rw [← hid]
  rw [lintegral_ofReal_sq_eq_tail hg (fun _ ↦ ENNReal.toReal_nonneg)]
  have hpoint (a : ℝ) (ha : 0 < a) :
      volume {x | a < g x} * ENNReal.ofReal (2 * a) ≤
        16 * ∫⁻ y, {y | ENNReal.ofReal (a / 2) < f y}.indicator f y := by
    have hsub : {x | a < g x} ⊆ {x | ENNReal.ofReal a < M x} := by
      intro x hx
      exact lt_of_lt_of_le ((ENNReal.ofReal_lt_iff_lt_toReal ha.le (hfin x)).mpr hx)
        (min_le_left _ _)
    have hhalf : 2 * ENNReal.ofReal (a / 2) = ENNReal.ofReal a := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hw := finiteCenteredMaximal_localized_weak_bound r hr f (ENNReal.ofReal (a / 2))
    rw [hhalf] at hw
    calc
      volume {x | a < g x} * ENNReal.ofReal (2 * a) =
          2 * (ENNReal.ofReal a * volume {x | a < g x}) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
        ring
      _ ≤ 2 * (ENNReal.ofReal a * volume {x | ENNReal.ofReal a < M x}) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (measure_mono hsub))
      _ ≤ 2 * (8 * ∫⁻ y, {y | ENNReal.ofReal (a / 2) < f y}.indicator f y) :=
        mul_le_mul' le_rfl hw
      _ = _ := by ring
  calc
    (∫⁻ a in Ioi (0 : ℝ), volume {x | a < g x} * ENNReal.ofReal (2 * a)) ≤
        ∫⁻ a in Ioi (0 : ℝ),
          16 * ∫⁻ y, {y | ENNReal.ofReal (a / 2) < f y}.indicator f y := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      exact hpoint a ha
    _ = 16 * (∫⁻ a in Ioi (0 : ℝ),
          ∫⁻ y, {y | ENNReal.ofReal (a / 2) < f y}.indicator f y) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ = 32 * ∫⁻ y, f y ^ 2 := by rw [lintegral_high_value_tails hf]; ring

/-- Increasing finite truncations recover an extended nonnegative square. -/
theorem iSup_min_nat_sq (v : ℝ≥0∞) :
    (⨆ n : ℕ, (min v (n : ℝ≥0∞)) ^ 2) = v ^ 2 := by
  apply le_antisymm
  · apply iSup_le
    intro n
    gcongr
    exact min_le_left _ _
  · by_cases hv : v = ⊤
    · subst v
      simp only [min_top_left, ENNReal.top_pow (by decide : (2 : ℕ) ≠ 0)]
      rw [← ENNReal.iSup_natCast]
      apply iSup_mono
      intro n
      exact_mod_cast (show n ≤ n ^ 2 by nlinarith)
    · obtain ⟨n, hn⟩ := exists_nat_ge v.toReal
      have hvn : v ≤ (n : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_toReal hv]
        exact_mod_cast ENNReal.ofReal_le_ofReal hn
      calc
        v ^ 2 = (min v (n : ℝ≥0∞)) ^ 2 := by rw [min_eq_left hvn]
        _ ≤ ⨆ n : ℕ, (min v (n : ℝ≥0∞)) ^ 2 :=
          le_iSup (fun n : ℕ ↦ (min v (n : ℝ≥0∞)) ^ 2) n

/-- The one-dimensional centered maximal `L²` inequality, uniformly for any
finite family of positive radii. No finiteness assumption on the input moment
is needed; all integrals take values in the extended nonnegative reals. -/
theorem finiteCenteredMaximal_sq_lintegral_le {N : ℕ}
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, (finiteCenteredMaximal r f x) ^ 2) ≤ 32 * ∫⁻ x, f x ^ 2 := by
  have hM := measurable_finiteCenteredMaximal r hf
  have hmeas (n : ℕ) : Measurable (fun x ↦
      (min (finiteCenteredMaximal r f x) (n : ℝ≥0∞)) ^ 2) :=
    (hM.min measurable_const).pow_const 2
  have hmono : Monotone (fun n : ℕ ↦ fun x ↦
      (min (finiteCenteredMaximal r f x) (n : ℝ≥0∞)) ^ 2) := by
    intro m n hmn x
    dsimp only
    gcongr
  have hid : (fun x ↦ (finiteCenteredMaximal r f x) ^ 2) =
      (fun x ↦ ⨆ n : ℕ, (min (finiteCenteredMaximal r f x) (n : ℝ≥0∞)) ^ 2) := by
    funext x
    exact (iSup_min_nat_sq _).symm
  rw [hid]
  rw [lintegral_iSup hmeas hmono]
  exact iSup_le (finiteCenteredMaximal_truncated_sq_lintegral_le r hr hf)

end QuadraticCarleson
