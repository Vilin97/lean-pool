/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section

/-!
# Interpolation for the comparison cutoff weights

These estimates interpolate the unweighted `L²` norm of a vector field with the
`L⁶` norm after multiplication by the fourth power of a cutoff. They use only
measurability and finite endpoint norms. In fact, the interpolation identities
only require a nonnegative weight; an upper bound of one is unnecessary.
-/


noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NavierStokesR3.WeightedInterpolation

open ProblemStatement Comparison

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

/-- Hölder interpolation for a function dominated by a product of powers.
The arithmetic assumptions are on real exponents, so rational specializations
can be discharged by `norm_num`. -/
theorem eLpNorm_le_rpow_mul
    {f : Space → E} {g : Space → F} {h : Space → G}
    {p q r : ℝ≥0∞} {a b : ℝ}
    (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume)
    (hp : 0 < p.toReal) (hq : 0 < q.toReal) (hr : 0 < r.toReal)
    (ha : 0 < a) (hb : 0 < b)
    (hra : r.toReal < p.toReal / a)
    (hab : 1 / r.toReal = 1 / (p.toReal / a) + 1 / (q.toReal / b))
    (hh : ∀ᵐ x ∂volume, ‖h x‖ ≤ ‖f x‖ ^ a * ‖g x‖ ^ b) :
    eLpNorm h r volume ≤ eLpNorm f p volume ^ a * eLpNorm g q volume ^ b := by
  obtain ⟨hp0, hpt⟩ := ENNReal.toReal_pos_iff.mp hp
  obtain ⟨hq0, hqt⟩ := ENNReal.toReal_pos_iff.mp hq
  obtain ⟨hr0, hrt⟩ := ENNReal.toReal_pos_iff.mp hr
  rw [eLpNorm_eq_eLpNorm' hr0.ne' hrt.ne,
    eLpNorm_eq_eLpNorm' hp0.ne' hpt.ne,
    eLpNorm_eq_eLpNorm' hq0.ne' hqt.ne]
  calc
    eLpNorm' h r.toReal volume ≤
        eLpNorm' (fun x => ‖f x‖ ^ a * ‖g x‖ ^ b) r.toReal volume := by
      apply eLpNorm'_mono_ae hr.le
      filter_upwards [hh] with x hx
      simpa only [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
          (Real.rpow_nonneg (norm_nonneg _) _))] using hx
    _ ≤ eLpNorm' (fun x => ‖f x‖ ^ a) (p.toReal / a) volume *
        eLpNorm' (fun x => ‖g x‖ ^ b) (q.toReal / b) volume := by
      simpa using eLpNorm'_le_eLpNorm'_mul_eLpNorm'
        (hf.norm.aemeasurable.pow_const a).aestronglyMeasurable
        (hg.norm.aemeasurable.pow_const b).aestronglyMeasurable
        (fun x y : ℝ => x * y) 1
        (Filter.Eventually.of_forall fun x => by simp [nnnorm_mul])
        hr hra hab
    _ = eLpNorm' f p.toReal volume ^ a * eLpNorm' g q.toReal volume ^ b := by
      rw [eLpNorm'_norm_rpow _ _ _ ha, eLpNorm'_norm_rpow _ _ _ hb,
        div_mul_cancel₀ _ ha.ne', div_mul_cancel₀ _ hb.ne']

/-- The preceding estimate also proves membership at the interpolated exponent
and permits passage to the real-valued comparison norm. -/
theorem memLp_and_lpNorm_le_rpow_mul
    {f : Space → E} {g : Space → F} {h : Space → G}
    {p q r : ℝ≥0∞} {a b : ℝ}
    (hf : MemLp f p volume) (hg : MemLp g q volume)
    (hhm : AEStronglyMeasurable h volume)
    (hp : 0 < p.toReal) (hq : 0 < q.toReal) (hr : 0 < r.toReal)
    (ha : 0 < a) (hb : 0 < b)
    (hra : r.toReal < p.toReal / a)
    (hab : 1 / r.toReal = 1 / (p.toReal / a) + 1 / (q.toReal / b))
    (hh : ∀ᵐ x ∂volume, ‖h x‖ ≤ ‖f x‖ ^ a * ‖g x‖ ^ b) :
    MemLp h r volume ∧ comparisonLpNorm r h ≤ comparisonLpNorm p f ^ a * comparisonLpNorm q g ^ b
      := by
  have hbound := eLpNorm_le_rpow_mul hf.1 hg.1 hp hq hr ha hb hra hab hh
  have hfinite : eLpNorm f p volume ^ a * eLpNorm g q volume ^ b < ∞ :=
    ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg ha.le hf.eLpNorm_ne_top)
      (ENNReal.rpow_lt_top_of_nonneg hb.le hg.eLpNorm_ne_top)
  refine ⟨⟨hhm, hbound.trans_lt hfinite⟩, ?_⟩
  simpa only [comparisonLpNorm, ENNReal.toReal_mul, ENNReal.toReal_rpow] using
    ENNReal.toReal_mono hfinite.ne hbound

/-- The real-valued seminorm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ≥0∞) (f : Space → E) : 0 ≤ comparisonLpNorm p f :=
  ENNReal.toReal_nonneg

/-- Recover the integral of a norm power from the finite real-valued seminorm. -/
theorem integral_norm_rpow_eq_lpNorm_rpow
    {f : Space → E} {p : ℝ≥0∞} (hp : 0 < p.toReal) (hf : MemLp f p volume) :
    (∫ x : Space, ‖f x‖ ^ p.toReal) = comparisonLpNorm p f ^ p.toReal := by
  obtain ⟨hp0, hpt⟩ := ENNReal.toReal_pos_iff.mp hp
  have hnonneg : 0 ≤ ∫ x : Space, ‖f x‖ ^ p.toReal :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [comparisonLpNorm, hf.eLpNorm_eq_integral_rpow_norm hp0.ne' hpt.ne,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _),
    ← Real.rpow_mul hnonneg, inv_mul_cancel₀ hp.ne', Real.rpow_one]

variable [NormedSpace ℝ E]

/-- The fourth-power cutoff has exactly the required fractional powers. -/
theorem pow_four_rpow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x ^ 4) ^ ((k : ℝ) / 4) = x ^ k := by
  rw [← Real.rpow_natCast x 4, ← Real.rpow_natCast x k, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- Pointwise factorization underlying all three interpolation estimates. -/
theorem norm_weight_pow_eq {φ : ℝ} (hφ : 0 ≤ φ) (w : E) (k : ℕ) :
    ‖(φ ^ k) • w‖ =
      ‖w‖ ^ (1 - (k : ℝ) / 4) * ‖(φ ^ 4) • w‖ ^ ((k : ℝ) / 4) := by
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hφ k), abs_of_nonneg (pow_nonneg hφ 4),
    Real.mul_rpow (pow_nonneg hφ 4) (norm_nonneg w), pow_four_rpow hφ]
  have hw : ‖w‖ ^ (1 - (k : ℝ) / 4) * ‖w‖ ^ ((k : ℝ) / 4) = ‖w‖ := by
    rw [← Real.rpow_add' (norm_nonneg w) (by ring_nf; exact one_ne_zero)]
    simp
  calc
    φ ^ k * ‖w‖ = φ ^ k *
        (‖w‖ ^ (1 - (k : ℝ) / 4) * ‖w‖ ^ ((k : ℝ) / 4)) := by rw [hw]
    _ = _ := by ring

/-- A generic cutoff interpolation theorem with explicit exponent arithmetic. -/
theorem cutoff_interpolation
    {φ : Space → ℝ} {w : Space → E} {k : ℕ} {r : ℝ≥0∞}
    (hφm : AEStronglyMeasurable φ volume) (hφ : ∀ x, 0 ≤ φ x)
    (hw : MemLp w 2 volume)
    (hweighted : MemLp (fun x => (φ x ^ 4) • w x) 6 volume)
    (hr : 0 < r.toReal)
    (ha : 0 < 1 - (k : ℝ) / 4) (hb : 0 < (k : ℝ) / 4)
    (hra : r.toReal < 2 / (1 - (k : ℝ) / 4))
    (hab : 1 / r.toReal =
      1 / (2 / (1 - (k : ℝ) / 4)) + 1 / (6 / ((k : ℝ) / 4))) :
    MemLp (fun x => (φ x ^ k) • w x) r volume ∧
      comparisonLpNorm r (fun x => (φ x ^ k) • w x) ≤
        comparisonLpNorm 2 w ^ (1 - (k : ℝ) / 4) *
          comparisonLpNorm 6 (fun x => (φ x ^ 4) • w x) ^ ((k : ℝ) / 4) := by
  apply memLp_and_lpNorm_le_rpow_mul hw hweighted ((hφm.pow k).smul hw.1)
      (by norm_num) (by norm_num) hr ha hb
  · simpa using hra
  · simpa using hab
  · exact Filter.Eventually.of_forall fun x => (norm_weight_pow_eq (hφ x) (w x) k).le

/-- `φ w` belongs to `L^(12/5)` with the exact endpoint interpolation bound. -/
theorem cutoff_interpolation_twelve_fifths
    {φ : Space → ℝ} {w : Space → E}
    (hφm : AEStronglyMeasurable φ volume) (hφ : ∀ x, 0 ≤ φ x)
    (hw : MemLp w 2 volume)
    (hweighted : MemLp (fun x => (φ x ^ 4) • w x) 6 volume) :
    MemLp (fun x => φ x • w x) (12 / 5) volume ∧
      comparisonLpNorm (12 / 5) (fun x => φ x • w x) ≤
        comparisonLpNorm 2 w ^ (3 / 4 : ℝ) *
          comparisonLpNorm 6 (fun x => (φ x ^ 4) • w x) ^ (1 / 4 : ℝ) := by
  convert! cutoff_interpolation (k := 1) (r := 12 / 5)
    hφm hφ hw hweighted (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) using 1 <;> norm_num

/-- `φ² w` belongs to `L³` with the exact endpoint interpolation bound. -/
theorem cutoff_interpolation_three
    {φ : Space → ℝ} {w : Space → E}
    (hφm : AEStronglyMeasurable φ volume) (hφ : ∀ x, 0 ≤ φ x)
    (hw : MemLp w 2 volume)
    (hweighted : MemLp (fun x => (φ x ^ 4) • w x) 6 volume) :
    MemLp (fun x => (φ x ^ 2) • w x) 3 volume ∧
      comparisonLpNorm 3 (fun x => (φ x ^ 2) • w x) ≤
        comparisonLpNorm 2 w ^ (1 / 2 : ℝ) *
          comparisonLpNorm 6 (fun x => (φ x ^ 4) • w x) ^ (1 / 2 : ℝ) := by
  convert! cutoff_interpolation (k := 2) (r := 3)
    hφm hφ hw hweighted (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) using 1
  norm_num

/-- `φ³ w` belongs to `L⁴` with the exact endpoint interpolation bound. -/
theorem cutoff_interpolation_four
    {φ : Space → ℝ} {w : Space → E}
    (hφm : AEStronglyMeasurable φ volume) (hφ : ∀ x, 0 ≤ φ x)
    (hw : MemLp w 2 volume)
    (hweighted : MemLp (fun x => (φ x ^ 4) • w x) 6 volume) :
    MemLp (fun x => (φ x ^ 3) • w x) 4 volume ∧
      comparisonLpNorm 4 (fun x => (φ x ^ 3) • w x) ≤
        comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
          comparisonLpNorm 6 (fun x => (φ x ^ 4) • w x) ^ (3 / 4 : ℝ) := by
  convert! cutoff_interpolation (k := 3) (r := 4)
    hφm hφ hw hweighted (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) using 1
  norm_num

/-- The weighted cubic transport integrand is integrable and controlled by the
two endpoint norms. -/
theorem cutoff_transport_bound
    {φ : Space → ℝ} {w : Space → E}
    (hφm : AEStronglyMeasurable φ volume) (hφ : ∀ x, 0 ≤ φ x)
    (hw : MemLp w 2 volume)
    (hweighted : MemLp (fun x => (φ x ^ 4) • w x) 6 volume) :
    Integrable (fun x => φ x ^ 6 * ‖w x‖ ^ 3) volume ∧
      (∫ x : Space, φ x ^ 6 * ‖w x‖ ^ 3) ≤
        comparisonLpNorm 2 w ^ (3 / 2 : ℝ) *
          comparisonLpNorm 6 (fun x => (φ x ^ 4) • w x) ^ (3 / 2 : ℝ) := by
  obtain ⟨hmem, hbound⟩ := cutoff_interpolation_three hφm hφ hw hweighted
  have hid (x : Space) :
      ‖(φ x ^ 2) • w x‖ ^ (3 : ℝ) = φ x ^ 6 * ‖w x‖ ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    ring
  have hint : Integrable (fun x => φ x ^ 6 * ‖w x‖ ^ 3) volume := by
    have hi := hmem.integrable_norm_rpow (by norm_num) (by norm_num)
    exact hi.congr (Filter.Eventually.of_forall fun x => by simpa using hid x)
  refine ⟨hint, ?_⟩
  calc
    (∫ x : Space, φ x ^ 6 * ‖w x‖ ^ 3) =
        (∫ x : Space, ‖(φ x ^ 2) • w x‖ ^ (3 : ℝ)) := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hid x).symm)
    _ = comparisonLpNorm 3 (fun x => (φ x ^ 2) • w x) ^ (3 : ℝ) := by
      simpa using integral_norm_rpow_eq_lpNorm_rpow (by norm_num) hmem
    _ ≤ (comparisonLpNorm 2 w ^ (1 / 2 : ℝ) *
        comparisonLpNorm 6 (fun x => (φ x ^ 4) • w x) ^ (1 / 2 : ℝ)) ^ (3 : ℝ) :=
      Real.rpow_le_rpow (lpNorm_nonneg _ _) hbound (by norm_num)
    _ = comparisonLpNorm 2 w ^ (3 / 2 : ℝ) *
        comparisonLpNorm 6 (fun x => (φ x ^ 4) • w x) ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow (Real.rpow_nonneg (lpNorm_nonneg _ _) _)
          (Real.rpow_nonneg (lpNorm_nonneg _ _) _),
        ← Real.rpow_mul (lpNorm_nonneg _ _), ← Real.rpow_mul (lpNorm_nonneg _ _)]
      norm_num

end NavierStokesR3.WeightedInterpolation
