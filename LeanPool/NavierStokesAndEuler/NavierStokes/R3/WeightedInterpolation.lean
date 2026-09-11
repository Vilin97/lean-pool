/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicIntegration
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactEnergy
import Mathlib.Analysis.InnerProductSpace.Calculus
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LpNormTools
import Mathlib.MeasureTheory.Function.L2Space

/-! Related estimates used together by the same construction modules. -/

section

/-!
# Interpolation for the comparison cutoff weights

These estimates interpolate the unweighted `L²` norm of a vector field with the
`L⁶` norm after multiplication by the fourth power of a cutoff. They use only
measurability and finite endpoint norms. In fact, the interpolation identities
only require a nonnegative weight; an upper bound of one is unnecessary.
-/

@[expose] public section

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

end
end

end

section

/-!
# Transport and pressure with a compact spatial weight

Only the scalar weight has compact support. The velocity, transported field,
and pressure may be arbitrary smooth functions on Euclidean three-space.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.LocalizedDifferenceEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

/-- The divergence of a scalar-weighted vector field. -/
theorem divergence_weighted {χ : Space → ℝ} {v : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hv : ContDiff ℝ ∞ v) (x : Space) :
    (∑ i : Fin 3, spatialPartial i (fun y => χ y • v y) x i) =
      fderiv ℝ χ x (v x) + χ x * ∑ i : Fin 3, spatialPartial i v x i := by
  have hpartial (i : Fin 3) :
      spatialPartial i (fun y => χ y • v y) x i =
        χ x * spatialPartial i v x i + spatialPartial i χ x * v x i := by
    change (EuclideanSpace.proj i)
      (fderiv ℝ (fun y => χ y • v y) x (coordinateVector i)) = _
    rw [fderiv_fun_smul (hχ.differentiable (by simp) x)
      (hv.differentiable (by simp) x)]
    simp only [_root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_eq_mul,
      spatialPartial]
    rfl
  simp_rw [hpartial]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, fderiv_apply_eq_sum]
  simp only [spatialPartial]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- A compact scalar weight transfers a directional derivative to the weight
when the vector field is divergence free. -/
theorem integral_weighted_fderiv_apply {χ f : Space → ℝ} {v : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (hcχ : HasCompactSupport χ)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i) = 0) :
    (∫ x, χ x * fderiv ℝ f x (v x)) =
      -(∫ x, f x * fderiv ℝ χ x (v x)) := by
  have h := CompactEnergy.integral_fderiv_apply hf (hχ.smul hv)
    (show HasCompactSupport (fun x => χ x • v x) from hcχ.smul_right)
  change (∫ x, fderiv ℝ f x (χ x • v x)) = -(∫ x, f x * ∑ i : Fin 3, spatialPartial i (fun y => χ y
      • v y) x i) at h
  simpa only [map_smul, smul_eq_mul, divergence_weighted hχ hv, hdiv,
    mul_zero, add_zero] using h

/-- The transport energy becomes a flux through the compact weight. No support
or global integrability assumption is imposed on either vector field. -/
theorem integral_weighted_transport {χ : Space → ℝ} {w v : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v)
    (hcχ : HasCompactSupport χ)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i) = 0) :
    (∫ x, χ x * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) =
      -(1 / 2 : ℝ) * ∫ x, ‖w x‖ ^ 2 * fderiv ℝ χ x (v x) := by
  have h := integral_weighted_fderiv_apply hχ (hw.norm_sq ℝ) hv hcχ hdiv
  have hfun : (fun x => χ x * fderiv ℝ (fun y => ‖w y‖ ^ 2) x (v x)) =
      (fun x => 2 * (χ x * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ)) := by
    funext x
    rw [fderiv_normsq hw]
    ring
  rw [hfun, integral_const_mul] at h
  linarith

/-- The pressure term becomes a flux through the compact weight. The pressure
need not have compact support or satisfy any bound at infinity. -/
theorem integral_weighted_pressure {χ π : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hπ : ContDiff ℝ ∞ π) (hw : ContDiff ℝ ∞ w)
    (hcχ : HasCompactSupport χ)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i w x i) = 0) :
    (∫ x, χ x * fderiv ℝ π x (w x)) =
      -(∫ x, π x * fderiv ℝ χ x (w x)) :=
  integral_weighted_fderiv_apply hχ hπ hw hcχ hdiv

end NavierStokesR3.LocalizedDifferenceEnergy

end
end

end

section

/-!
# Finite-energy bounds for whole-space comparison

The hypotheses in this module concern only square integrability and
measurability. In particular, the comparison field need not have compact
support or any globally bounded derivative.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The explicit square-integrability condition is the usual `MemLp` condition
once measurability of the velocity slice is known. -/
theorem squareIntegrableAtTime_iff_memLp {u : VelocityField} {t : ℝ}
    (hu : AEStronglyMeasurable (fun x : Space => u (t, x)) volume) :
    SquareIntegrableAtTime u t ↔ MemLp (fun x : Space => u (t, x)) 2 volume :=
  (memLp_two_iff_integrable_sq_norm hu).symm

/-- Joint continuity on a time slab gives continuity of every spatial slice,
including a boundary time. -/
theorem continuous_slice_of_continuousOn {times : Set ℝ} {u : VelocityField}
    (hu : ContinuousOn u (times ×ˢ univ)) {t : ℝ} (ht : t ∈ times) :
    Continuous (fun x : Space => u (t, x)) := by
  have hc : ContinuousOn (fun x : Space => u (t, x)) univ :=
    hu.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun x _ => ⟨ht, mem_univ x⟩)
  exact continuous_iff_continuousAt.2 (fun x => (hc x (mem_univ x)).continuousAt
    Filter.univ_mem)

/-- No integrability hypothesis is needed for nonnegativity of the totalized
integral defining the squared norm. -/
theorem l2Sq_nonneg {E : Type*} [NormedAddCommGroup E] (f : Space → E) :
    0 ≤ l2Sq f :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- The elementary pointwise estimate used for the difference energy. -/
theorem norm_sub_sq_le_twice {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := mul_self_le_mul_self (norm_nonneg (a - b)) (norm_sub_le a b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- A difference of square-integrable slices remains square integrable. -/
theorem squareIntegrableAtTime_sub {u v : VelocityField} {t : ℝ}
    (hu_meas : AEStronglyMeasurable (fun x : Space => u (t, x)) volume)
    (hv_meas : AEStronglyMeasurable (fun x : Space => v (t, x)) volume)
    (hu : SquareIntegrableAtTime u t) (hv : SquareIntegrableAtTime v t) :
    SquareIntegrableAtTime (fun z => u z - v z) t := by
  exact (squareIntegrableAtTime_iff_memLp (hu_meas.sub hv_meas)).2
    (((squareIntegrableAtTime_iff_memLp hu_meas).1 hu).sub
      ((squareIntegrableAtTime_iff_memLp hv_meas).1 hv))

/-- The squared `L²` norm of a difference is bounded by the two original
energies. -/
theorem l2Sq_sub_le {E : Type*} [NormedAddCommGroup E] {f g : Space → E}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    l2Sq (fun x => f x - g x) ≤ 2 * (l2Sq f + l2Sq g) := by
  have hf_sq := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hg_sq := (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  have hfg_sq := (memLp_two_iff_integrable_sq_norm (hf.sub hg).1).1 (hf.sub hg)
  calc
    l2Sq (fun x => f x - g x) ≤
        ∫ x : Space, 2 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) :=
      integral_mono hfg_sq ((hf_sq.add hg_sq).const_mul 2)
        (fun x => norm_sub_sq_le_twice (f x) (g x))
    _ = 2 * (l2Sq f + l2Sq g) := by
      rw [integral_const_mul, integral_add hf_sq hg_sq]
      rfl

/-- Uniform finite energy is stable under taking the velocity difference. -/
theorem uniformFiniteEnergy_sub {times : Set ℝ} {u v : VelocityField}
    (hu_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => u (t, x)) volume)
    (hv_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => v (t, x)) volume)
    (hu : UniformFiniteEnergy times u) (hv : UniformFiniteEnergy times v) :
    UniformFiniteEnergy times (fun z => u z - v z) := by
  obtain ⟨Eu, hEu, hu⟩ := hu
  obtain ⟨Ev, hEv, hv⟩ := hv
  refine ⟨2 * (Eu + Ev), by positivity, ?_⟩
  intro t ht
  obtain ⟨hu_sq, hu_bound⟩ := hu t ht
  obtain ⟨hv_sq, hv_bound⟩ := hv t ht
  refine ⟨squareIntegrableAtTime_sub (hu_meas t ht) (hv_meas t ht) hu_sq hv_sq, ?_⟩
  have hdiff := l2Sq_sub_le
    ((squareIntegrableAtTime_iff_memLp (hu_meas t ht)).1 hu_sq)
    ((squareIntegrableAtTime_iff_memLp (hv_meas t ht)).1 hv_sq)
  dsimp [kineticEnergy, l2Sq] at hu_bound hv_bound hdiff ⊢
  linarith

/-- The preceding result applies to fields jointly continuous on the slab. -/
theorem uniformFiniteEnergy_sub_of_continuousOn {times : Set ℝ} {u v : VelocityField}
    (hu_cont : ContinuousOn u (times ×ˢ univ))
    (hv_cont : ContinuousOn v (times ×ˢ univ))
    (hu : UniformFiniteEnergy times u) (hv : UniformFiniteEnergy times v) :
    UniformFiniteEnergy times (fun z => u z - v z) :=
  uniformFiniteEnergy_sub
    (fun _ ht => (continuous_slice_of_continuousOn hu_cont ht).aestronglyMeasurable)
    (fun _ ht => (continuous_slice_of_continuousOn hv_cont ht).aestronglyMeasurable) hu hv

/-- A kinetic-energy bound is also a bound for the squared `L²` norm. -/
theorem uniformFiniteEnergy_l2Sq_bound {times : Set ℝ} {u : VelocityField}
    (hu : UniformFiniteEnergy times u) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ times,
      SquareIntegrableAtTime u t ∧ l2Sq (fun x => u (t, x)) ≤ M := by
  obtain ⟨E, hE, hu⟩ := hu
  refine ⟨2 * E, by positivity, ?_⟩
  intro t ht
  obtain ⟨hint, hbound⟩ := hu t ht
  refine ⟨hint, ?_⟩
  dsimp [kineticEnergy, l2Sq] at hbound ⊢
  linarith

/-- Every component product is dominated by the Euclidean squared norm. -/
theorem norm_component_mul_le_sq (a : Space) (i j : Fin 3) :
    ‖a i * a j‖ ≤ ‖a‖ ^ 2 := by
  rw [norm_mul, pow_two]
  exact mul_le_mul (PiLp.norm_apply_le a i) (PiLp.norm_apply_le a j)
    (norm_nonneg _) (norm_nonneg _)

/-- Pointwise domination of the nonlinear tensor by the two energy densities. -/
theorem tensorDiff_norm_le (u v : VelocityField) (t : ℝ) (i j : Fin 3) (x : Space) :
    ‖tensorDiff u v t i j x‖ ≤ ‖u (t, x)‖ ^ 2 + ‖v (t, x)‖ ^ 2 := by
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_component_mul_le_sq (u (t, x)) i j)
      (norm_component_mul_le_sq (v (t, x)) i j))

/-- The nonlinear tensor has measurable components whenever both velocities
have measurable spatial slices. -/
theorem tensorDiff_aestronglyMeasurable {u v : VelocityField} {t : ℝ}
    (hu : AEStronglyMeasurable (fun x : Space => u (t, x)) volume)
    (hv : AEStronglyMeasurable (fun x : Space => v (t, x)) volume) (i j : Fin 3) :
    AEStronglyMeasurable (tensorDiff u v t i j) volume := by
  have hui := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hu
  have huj := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hu
  have hvi := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hv
  have hvj := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hv
  exact (hui.mul huj).sub (hvi.mul hvj)

/-- Every component of the tensor difference lies in `L¹`. -/
theorem tensorDiff_integrable {u v : VelocityField} {t : ℝ}
    (hu : MemLp (fun x : Space => u (t, x)) 2 volume)
    (hv : MemLp (fun x : Space => v (t, x)) 2 volume) (i j : Fin 3) :
    Integrable (tensorDiff u v t i j) volume := by
  have hu_sq := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have hv_sq := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  exact (hu_sq.add hv_sq).mono' (tensorDiff_aestronglyMeasurable hu.1 hv.1 i j)
    (ae_of_all _ (tensorDiff_norm_le u v t i j))

/-- Its `L¹` norm is bounded using only the two ordinary energies. -/
theorem tensorDiff_norm_integral_le {u v : VelocityField} {t : ℝ}
    (hu : MemLp (fun x : Space => u (t, x)) 2 volume)
    (hv : MemLp (fun x : Space => v (t, x)) 2 volume) (i j : Fin 3) :
    (∫ x : Space, ‖tensorDiff u v t i j x‖) ≤
      l2Sq (fun x => u (t, x)) + l2Sq (fun x => v (t, x)) := by
  have hu_sq := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have hv_sq := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  calc
    (∫ x : Space, ‖tensorDiff u v t i j x‖) ≤
        ∫ x : Space, ‖u (t, x)‖ ^ 2 + ‖v (t, x)‖ ^ 2 :=
      integral_mono (tensorDiff_integrable hu hv i j).norm (hu_sq.add hv_sq)
        (tensorDiff_norm_le u v t i j)
    _ = _ := integral_add hu_sq hv_sq

/-- A single `L¹` bound works for all times and all tensor components. -/
theorem uniformFiniteEnergy_tensorDiff_bound {times : Set ℝ} {u v : VelocityField}
    (hu_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => u (t, x)) volume)
    (hv_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => v (t, x)) volume)
    (hu : UniformFiniteEnergy times u) (hv : UniformFiniteEnergy times v) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ times, ∀ i j : Fin 3,
      Integrable (tensorDiff u v t i j) volume ∧
        (∫ x : Space, ‖tensorDiff u v t i j x‖) ≤ M := by
  obtain ⟨Mu, hMu, hu⟩ := uniformFiniteEnergy_l2Sq_bound hu
  obtain ⟨Mv, hMv, hv⟩ := uniformFiniteEnergy_l2Sq_bound hv
  refine ⟨Mu + Mv, add_nonneg hMu hMv, ?_⟩
  intro t ht i j
  obtain ⟨hu_sq, hu_bound⟩ := hu t ht
  obtain ⟨hv_sq, hv_bound⟩ := hv t ht
  have hu_lp := (squareIntegrableAtTime_iff_memLp (hu_meas t ht)).1 hu_sq
  have hv_lp := (squareIntegrableAtTime_iff_memLp (hv_meas t ht)).1 hv_sq
  exact ⟨tensorDiff_integrable hu_lp hv_lp i j,
    (tensorDiff_norm_integral_le hu_lp hv_lp i j).trans (add_le_add hu_bound hv_bound)⟩

/-- The finite energy hypothesis gives a uniform bound for the ordinary `L²`
norm, with membership in `L²` recorded explicitly. -/
theorem uniformFiniteEnergy_lpNorm_two_bound {times : Set ℝ} {u : VelocityField}
    (hu_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => u (t, x)) volume)
    (hu : UniformFiniteEnergy times u) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ times,
      MemLp (fun x : Space => u (t, x)) 2 volume ∧
        comparisonLpNorm 2 (fun x => u (t, x)) ≤ M := by
  obtain ⟨M, _, hM⟩ := uniformFiniteEnergy_l2Sq_bound hu
  refine ⟨Real.sqrt M, Real.sqrt_nonneg M, ?_⟩
  intro t ht
  obtain ⟨hint, hbound⟩ := hM t ht
  have hLp := (squareIntegrableAtTime_iff_memLp (hu_meas t ht)).1 hint
  refine ⟨hLp, ?_⟩
  rw [LpNormTools.lpNorm_two_eq_sqrt_l2Sq hLp]
  exact Real.sqrt_le_sqrt hbound

/-- The uniform tensor estimate in the common `comparisonLpNorm` notation. -/
theorem uniformFiniteEnergy_tensorDiff_lpNorm_one_bound {times : Set ℝ}
    {u v : VelocityField}
    (hu_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => u (t, x)) volume)
    (hv_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => v (t, x)) volume)
    (hu : UniformFiniteEnergy times u) (hv : UniformFiniteEnergy times v) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ times, ∀ i j : Fin 3,
      Integrable (tensorDiff u v t i j) volume ∧ comparisonLpNorm 1 (tensorDiff u v t i j) ≤ M := by
  obtain ⟨M, hM, hbound⟩ := uniformFiniteEnergy_tensorDiff_bound hu_meas hv_meas hu hv
  refine ⟨M, hM, ?_⟩
  intro t ht i j
  obtain ⟨hint, hle⟩ := hbound t ht i j
  refine ⟨hint, ?_⟩
  rwa [LpNormTools.lpNorm_one_eq_integral_norm hint]

end NavierStokesR3.Comparison

end
end

end
