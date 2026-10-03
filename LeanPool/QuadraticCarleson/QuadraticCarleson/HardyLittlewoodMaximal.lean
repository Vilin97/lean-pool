/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticCenteredMaximal

/-!
# The centered Hardy--Littlewood maximal operator on the real line

We use positive rational radii. This makes the pointwise supremum measurably
countable while retaining arbitrarily small and arbitrarily large intervals.
The weak `(1,1)` estimate is obtained from the bounded-radius Vitali estimate
in `QuadraticCenteredMaximal` and continuity of measure from below.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QuadraticCarleson

/-- Positive rational radii, used as a countable cofinal family. -/
abbrev PositiveRational := {q : ℚ // 0 < q}

/-- Positive rational radii bounded by `n + 1`. -/
abbrev BoundedPositiveRational (n : ℕ) :=
  {q : ℚ // 0 < q ∧ (q : ℝ) ≤ n + 1}

/-- The centered maximal operator over all positive rational radii. -/
noncomputable def centeredHardyLittlewoodMaximal (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ q : PositiveRational, centeredAverage (q : ℝ) f x

/-- The same maximal operator with radii bounded by `n + 1`. -/
noncomputable def boundedCenteredHardyLittlewoodMaximal (n : ℕ)
    (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ q : BoundedPositiveRational n, centeredAverage (q : ℝ) f x

theorem measurable_centeredHardyLittlewoodMaximal {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) : Measurable (centeredHardyLittlewoodMaximal f) :=
  Measurable.iSup (fun q : PositiveRational ↦ measurable_centeredAverage (q : ℝ) hf)

theorem measurable_boundedCenteredHardyLittlewoodMaximal (n : ℕ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (boundedCenteredHardyLittlewoodMaximal n f) :=
  Measurable.iSup
    (fun q : BoundedPositiveRational n ↦ measurable_centeredAverage (q : ℝ) hf)

theorem boundedCenteredHardyLittlewoodMaximal_le (n : ℕ)
    (f : ℝ → ℝ≥0∞) (x : ℝ) :
    boundedCenteredHardyLittlewoodMaximal n f x ≤ centeredHardyLittlewoodMaximal f x := by
  apply iSup_le
  intro q
  exact le_iSup (fun q : PositiveRational ↦ centeredAverage (q : ℝ) f x)
    ⟨q, q.property.1⟩

theorem boundedCenteredHardyLittlewoodMaximal_mono {n m : ℕ} (hnm : n ≤ m)
    (f : ℝ → ℝ≥0∞) (x : ℝ) :
    boundedCenteredHardyLittlewoodMaximal n f x ≤
      boundedCenteredHardyLittlewoodMaximal m f x := by
  apply iSup_le
  intro q
  change centeredAverage (q : ℝ) f x ≤
    ⨆ q : BoundedPositiveRational m, centeredAverage (q : ℝ) f x
  exact le_iSup (fun q : BoundedPositiveRational m ↦ centeredAverage (q : ℝ) f x)
    ⟨q, q.property.1, q.property.2.trans (by exact_mod_cast Nat.add_le_add_right hnm 1)⟩

/-- The full rational-radius maximal function is the increasing supremum of
its bounded-radius versions. -/
theorem centeredHardyLittlewoodMaximal_eq_iSup_bounded (f : ℝ → ℝ≥0∞) (x : ℝ) :
    centeredHardyLittlewoodMaximal f x =
      ⨆ n : ℕ, boundedCenteredHardyLittlewoodMaximal n f x := by
  apply le_antisymm
  · apply iSup_le
    intro q
    obtain ⟨n, hn⟩ := exists_nat_gt (q : ℝ)
    exact (le_iSup
      (fun q' : BoundedPositiveRational n ↦ centeredAverage (q' : ℝ) f x)
      ⟨q, q.property, hn.le.trans (by norm_num)⟩).trans
      (le_iSup (fun n : ℕ ↦ boundedCenteredHardyLittlewoodMaximal n f x) n)
  · apply iSup_le
    intro n
    exact boundedCenteredHardyLittlewoodMaximal_le n f x

/-- Uniform weak `(1,1)` estimate for the bounded rational-radius maximal
operator. -/
theorem boundedCenteredHardyLittlewoodMaximal_weak_bound (n : ℕ)
    (f : ℝ → ℝ≥0∞) (a : ℝ≥0∞) :
    a * volume {x | a < boundedCenteredHardyLittlewoodMaximal n f x} ≤
      4 * ∫⁻ y, f y := by
  classical
  let E : Set ℝ := {x | a < boundedCenteredHardyLittlewoodMaximal n f x}
  have hex (x : E) : ∃ q : BoundedPositiveRational n,
      a < centeredAverage (q : ℝ) f x :=
    lt_iSup_iff.mp x.property
  choose q hq using hex
  let radii : ℝ → ℝ := fun x ↦ if hx : x ∈ E then (q ⟨x, hx⟩ : ℚ) else 1
  have hselected (x : ℝ) (hx : x ∈ E) : radii x = (q ⟨x, hx⟩ : ℚ) := by
    simp [radii, hx]
  have hradius (x : ℝ) (hx : x ∈ E) : 0 < radii x := by
    rw [hselected x hx]
    exact_mod_cast (q ⟨x, hx⟩).property.1
  have hbound (x : ℝ) (hx : x ∈ E) : radii x ≤ (n : ℝ) + 1 := by
    rw [hselected x hx]
    exact (q ⟨x, hx⟩).property.2
  apply centered_average_covering_weak_bound f E radii ((n : ℝ) + 1)
    hradius hbound a
  intro x hx
  apply (le_centeredAverage_iff (hradius x hx) f x a).mp
  rw [hselected x hx]
  exact (hq ⟨x, hx⟩).le

/-- The strict superlevel set of the full maximal function is the increasing
union of the bounded-radius superlevel sets. -/
theorem centeredHardyLittlewoodMaximal_levelSet_eq_iUnion (f : ℝ → ℝ≥0∞)
    (a : ℝ≥0∞) :
    {x | a < centeredHardyLittlewoodMaximal f x} =
      ⋃ n : ℕ, {x | a < boundedCenteredHardyLittlewoodMaximal n f x} := by
  ext x
  rw [mem_ofPred_eq, centeredHardyLittlewoodMaximal_eq_iSup_bounded]
  simp only [mem_iUnion, mem_ofPred_eq]
  show (a < ⨆ n : ℕ, boundedCenteredHardyLittlewoodMaximal n f x) ↔
    ∃ n : ℕ, a < boundedCenteredHardyLittlewoodMaximal n f x
  exact lt_iSup_iff

/-- The centered Hardy--Littlewood maximal operator on `ℝ` has weak type
`(1,1)` with the explicit Vitali constant `4`. -/
theorem centeredHardyLittlewoodMaximal_weak_bound (f : ℝ → ℝ≥0∞) (a : ℝ≥0∞) :
    a * volume {x | a < centeredHardyLittlewoodMaximal f x} ≤ 4 * ∫⁻ y, f y := by
  rw [centeredHardyLittlewoodMaximal_levelSet_eq_iUnion]
  have hmono : Monotone
      (fun n : ℕ ↦ {x | a < boundedCenteredHardyLittlewoodMaximal n f x}) := by
    intro n m hnm x hx
    exact hx.trans_le (boundedCenteredHardyLittlewoodMaximal_mono hnm f x)
  rw [hmono.measure_iUnion]
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro n
  exact boundedCenteredHardyLittlewoodMaximal_weak_bound n f a

/-- Removing values below `b` changes the full centered maximal function by
at most `b`. -/
theorem centeredHardyLittlewoodMaximal_le_truncate_add
    (f : ℝ → ℝ≥0∞) (b : ℝ≥0∞) (x : ℝ) :
    centeredHardyLittlewoodMaximal f x ≤
      centeredHardyLittlewoodMaximal ({y | b < f y}.indicator f) x + b := by
  apply iSup_le
  intro q
  exact (centeredAverage_le_truncate_add
    (by exact_mod_cast q.property) f b x).trans
    (add_le_add
      (le_iSup (fun q' : PositiveRational ↦
        centeredAverage (q' : ℝ) ({y | b < f y}.indicator f) x) q)
      le_rfl)

/-- Localized weak estimate for the full rational-radius maximal operator. -/
theorem centeredHardyLittlewoodMaximal_localized_weak_bound
    (f : ℝ → ℝ≥0∞) (b : ℝ≥0∞) :
    (2 * b) * volume {x | 2 * b < centeredHardyLittlewoodMaximal f x} ≤
      8 * ∫⁻ y, {y | b < f y}.indicator f y := by
  have hsubset : {x | 2 * b < centeredHardyLittlewoodMaximal f x} ⊆
      {x | b < centeredHardyLittlewoodMaximal
        ({y | b < f y}.indicator f) x} := by
    intro x hx
    by_contra hn
    have hh := centeredHardyLittlewoodMaximal_le_truncate_add f b x
    have hle := add_le_add (le_of_not_gt hn) (le_rfl : b ≤ b)
    have hlast : centeredHardyLittlewoodMaximal f x ≤ 2 * b := by
      simpa only [two_mul] using hh.trans hle
    exact (not_lt_of_ge hlast) hx
  have hweak := centeredHardyLittlewoodMaximal_weak_bound
    ({y | b < f y}.indicator f) b
  calc
    _ ≤ 2 * (b * volume {x | b < centeredHardyLittlewoodMaximal
        ({y | b < f y}.indicator f) x}) := by
      rw [← mul_assoc]
      exact mul_le_mul' le_rfl (measure_mono hsubset)
    _ ≤ 2 * (4 * ∫⁻ y, {y | b < f y}.indicator f y) :=
      mul_le_mul' le_rfl hweak
    _ = _ := by ring

/-- Each finite-value truncation of the genuine centered maximal function has
the same uniform second-moment bound as its finite-radius approximants. -/
theorem centeredHardyLittlewoodMaximal_truncated_sq_lintegral_le
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    (∫⁻ x, (min (centeredHardyLittlewoodMaximal f x) (n : ℝ≥0∞)) ^ 2) ≤
      32 * ∫⁻ x, f x ^ 2 := by
  let M := centeredHardyLittlewoodMaximal f
  let g : ℝ → ℝ := fun x ↦ (min (M x) (n : ℝ≥0∞)).toReal
  have hM : Measurable M := measurable_centeredHardyLittlewoodMaximal hf
  have hg : Measurable g := (hM.min measurable_const).ennreal_toReal
  have hfin (x : ℝ) : min (M x) (n : ℝ≥0∞) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (ENNReal.natCast_lt_top n))
  have hid (x : ℝ) : ENNReal.ofReal (g x ^ 2) =
      (min (M x) (n : ℝ≥0∞)) ^ 2 := by
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin x)]
  change (∫⁻ x, (min (M x) (n : ℝ≥0∞)) ^ 2) ≤ _
  simp_rw [← hid]
  rw [lintegral_ofReal_sq_eq_tail hg (fun _ ↦ ENNReal.toReal_nonneg)]
  have hpoint (a : ℝ) (ha : 0 < a) :
      volume {x | a < g x} * ENNReal.ofReal (2 * a) ≤
        16 * ∫⁻ y, {y | ENNReal.ofReal (a / 2) < f y}.indicator f y := by
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
    calc
      volume {x | a < g x} * ENNReal.ofReal (2 * a) =
          2 * (ENNReal.ofReal a * volume {x | a < g x}) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
        ring
      _ ≤ 2 * (ENNReal.ofReal a * volume {x | ENNReal.ofReal a < M x}) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (measure_mono hsub))
      _ ≤ 2 * (8 * ∫⁻ y,
          {y | ENNReal.ofReal (a / 2) < f y}.indicator f y) :=
        mul_le_mul' le_rfl hw
      _ = _ := by ring
  calc
    (∫⁻ a in Ioi (0 : ℝ),
        volume {x | a < g x} * ENNReal.ofReal (2 * a)) ≤
        ∫⁻ a in Ioi (0 : ℝ),
          16 * ∫⁻ y, {y | ENNReal.ofReal (a / 2) < f y}.indicator f y := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      exact hpoint a ha
    _ = 16 * (∫⁻ a in Ioi (0 : ℝ),
          ∫⁻ y, {y | ENNReal.ofReal (a / 2) < f y}.indicator f y) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ = 32 * ∫⁻ y, f y ^ 2 := by
      rw [lintegral_high_value_tails hf]
      ring

/-- Strong `L²` estimate for the genuine countable centered maximal
operator. -/
theorem centeredHardyLittlewoodMaximal_sq_lintegral_le
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, (centeredHardyLittlewoodMaximal f x) ^ 2) ≤
      32 * ∫⁻ x, f x ^ 2 := by
  have hM := measurable_centeredHardyLittlewoodMaximal hf
  have hmeas (n : ℕ) : Measurable (fun x ↦
      (min (centeredHardyLittlewoodMaximal f x) (n : ℝ≥0∞)) ^ 2) :=
    (hM.min measurable_const).pow_const 2
  have hmono : Monotone (fun n : ℕ ↦ fun x ↦
      (min (centeredHardyLittlewoodMaximal f x) (n : ℝ≥0∞)) ^ 2) := by
    intro m n hmn x
    dsimp only
    gcongr
  have hid : (fun x ↦ (centeredHardyLittlewoodMaximal f x) ^ 2) =
      (fun x ↦ ⨆ n : ℕ,
        (min (centeredHardyLittlewoodMaximal f x) (n : ℝ≥0∞)) ^ 2) := by
    funext x
    exact (iSup_min_nat_sq _).symm
  rw [hid, lintegral_iSup hmeas hmono]
  exact iSup_le (centeredHardyLittlewoodMaximal_truncated_sq_lintegral_le hf)

end QuadraticCarleson
