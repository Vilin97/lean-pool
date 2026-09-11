/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ProblemStatement
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Related estimates used together by the same construction modules. -/

section

/-!
# Cancellation in the heat-kernel commutator

The multiplier is the square of a cutoff valued in `[0, 1]`.  Its difference
is bounded by its Lipschitz variation near the diagonal and by `1` everywhere.
The resulting minimum is the cancellation factor used before interchanging
the heat-time and spatial integrals.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The cancellation factor for the multiplier `φ²`. -/
def cutoffSquareDifference (φ : Space → ℝ) (x y : Space) : ℝ :=
  φ y ^ 2 - φ x ^ 2

theorem abs_sq_sub_sq_le_two_mul_abs_sub {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    |a ^ 2 - b ^ 2| ≤ 2 * |a - b| := by
  have hab : |a + b| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg ha.1 hb.1)]
    linarith [ha.2, hb.2]
  calc
    |a ^ 2 - b ^ 2| = |a - b| * |a + b| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |a - b| * 2 := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
    _ = 2 * |a - b| := mul_comm _ _

theorem abs_sq_sub_sq_le_one {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    |a ^ 2 - b ^ 2| ≤ 1 := by
  rw [abs_le]
  have ha2 : a * a ≤ 1 * 1 := mul_le_mul ha.2 ha.2 ha.1 (by norm_num)
  have hb2 : b * b ≤ 1 * 1 := mul_le_mul hb.2 hb.2 hb.1 (by norm_num)
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

theorem cutoffSquareDifference_abs_le_one {φ : Space → ℝ}
    (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (x y : Space) :
    |cutoffSquareDifference φ x y| ≤ 1 :=
  abs_sq_sub_sq_le_one (hφ y) (hφ x)

theorem cutoffSquareDifference_abs_le_lipschitz {φ : Space → ℝ}
    {L : ℝ≥0} (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : LipschitzWith L φ) (x y : Space) :
    |cutoffSquareDifference φ x y| ≤ 2 * L * ‖x - y‖ := by
  have hxy : |φ y - φ x| ≤ L * ‖x - y‖ := by
    calc
      |φ y - φ x| = dist (φ y) (φ x) := (Real.dist_eq _ _).symm
      _ ≤ L * dist y x := hLip.dist_le_mul y x
      _ = L * ‖x - y‖ := by rw [dist_comm, dist_eq_norm]
  exact (abs_sq_sub_sq_le_two_mul_abs_sub (hφ y) (hφ x)).trans
    (by nlinarith)

theorem cutoffSquareDifference_abs_le_min {φ : Space → ℝ}
    {L : ℝ≥0} (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : LipschitzWith L φ) (x y : Space) :
    |cutoffSquareDifference φ x y| ≤ min (2 * L * ‖x - y‖) 1 :=
  le_min (cutoffSquareDifference_abs_le_lipschitz hφ hLip x y)
    (cutoffSquareDifference_abs_le_one hφ x y)

/-- A form with a real scale parameter, convenient for scaled bump functions. -/
theorem cutoffSquareDifference_abs_le_scaled_min {φ : Space → ℝ}
    {L R : ℝ} (hR : 0 < R)
    (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (x y : Space) :
    |cutoffSquareDifference φ x y| ≤
      max (2 * L) 1 * min (‖x - y‖ / R) 1 := by
  have hsmall : |cutoffSquareDifference φ x y| ≤ 2 * L * (‖x - y‖ / R) := by
    have hxy := hLip y x
    rw [norm_sub_rev] at hxy
    calc
      |cutoffSquareDifference φ x y| ≤ 2 * |φ y - φ x| :=
        abs_sq_sub_sq_le_two_mul_abs_sub (hφ y) (hφ x)
      _ ≤ 2 * ((L / R) * ‖x - y‖) := mul_le_mul_of_nonneg_left hxy (by norm_num)
      _ = 2 * L * (‖x - y‖ / R) := by ring
  have hlarge := cutoffSquareDifference_abs_le_one hφ x y
  have hnonneg : 0 ≤ ‖x - y‖ / R := div_nonneg (norm_nonneg _) hR.le
  by_cases hx : ‖x - y‖ / R ≤ 1
  · rw [min_eq_left hx]
    exact hsmall.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hnonneg)
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hx)), mul_one]
    exact hlarge.trans (le_max_right _ _)

@[simp] theorem cutoffSquareDifference_self (φ : Space → ℝ) (x : Space) :
    cutoffSquareDifference φ x x = 0 := sub_self _

theorem cutoffSquareDifference_swap (φ : Space → ℝ) (x y : Space) :
    cutoffSquareDifference φ y x = -cutoffSquareDifference φ x y := by
  unfold cutoffSquareDifference
  ring

/-- The time-integrated kernel with cancellation already inserted. -/
def cancelledTimeKernel (K : ℝ → Space → ℝ) (φ : Space → ℝ)
    (x y : Space) : ℝ :=
  ∫ s in Ioi (0 : ℝ), K s (x - y) * cutoffSquareDifference φ x y

/-- The absolute time integral is used to justify the subsequent Fubini step. -/
def absoluteCancelledTimeKernel (K : ℝ → Space → ℝ) (φ : Space → ℝ)
    (x y : Space) : ℝ :=
  ∫ s in Ioi (0 : ℝ), |K s (x - y) * cutoffSquareDifference φ x y|

theorem cancelledTimeKernel_abs_le (K : ℝ → Space → ℝ) (φ : Space → ℝ)
    (x y : Space) :
    |cancelledTimeKernel K φ x y| ≤ absoluteCancelledTimeKernel K φ x y :=
  abs_integral_le_integral_abs

theorem absoluteCancelledTimeKernel_nonneg (K : ℝ → Space → ℝ) (φ : Space → ℝ)
    (x y : Space) : 0 ≤ absoluteCancelledTimeKernel K φ x y :=
  integral_nonneg fun _ => abs_nonneg _

theorem cancelledTimeKernel_integrable_time {K : ℝ → Space → ℝ}
    (hK : ∀ z ≠ 0, IntegrableOn (fun s => K s z) (Ioi (0 : ℝ)) volume)
    (φ : Space → ℝ) (x y : Space) :
    IntegrableOn (fun s => K s (x - y) * cutoffSquareDifference φ x y)
      (Ioi (0 : ℝ)) volume := by
  by_cases hxy : x = y
  · simp only [hxy, cutoffSquareDifference_self, mul_zero]
    exact integrable_zero _ _ _
  · exact (hK (x - y) (sub_ne_zero.mpr hxy)).mul_const _

theorem absoluteCancelledTimeKernel_le {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} {C L R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hK : ∀ z ≠ 0, (∫ s in Ioi (0 : ℝ), |K s z|) ≤ C * ‖z‖ ^ (-3 : ℝ))
    (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (x y : Space) :
    absoluteCancelledTimeKernel K φ x y ≤
      (C * max (2 * L) 1) * (‖x - y‖ ^ (-3 : ℝ) * min (‖x - y‖ / R) 1) := by
  by_cases hxy : x = y
  · simp [absoluteCancelledTimeKernel, hxy, cutoffSquareDifference_self]
  have hc : 0 ≤ C * ‖x - y‖ ^ (-3 : ℝ) := by positivity
  calc
    absoluteCancelledTimeKernel K φ x y =
        (∫ s in Ioi (0 : ℝ), |K s (x - y)|) * |cutoffSquareDifference φ x y| := by
      simp only [absoluteCancelledTimeKernel, abs_mul, integral_mul_const]
    _ ≤ (C * ‖x - y‖ ^ (-3 : ℝ)) * |cutoffSquareDifference φ x y| :=
      mul_le_mul_of_nonneg_right (hK _ (sub_ne_zero.mpr hxy)) (abs_nonneg _)
    _ ≤ (C * ‖x - y‖ ^ (-3 : ℝ)) *
        (max (2 * L) 1 * min (‖x - y‖ / R) 1) :=
      mul_le_mul_of_nonneg_left
        (cutoffSquareDifference_abs_le_scaled_min hR hφ hLip x y) hc
    _ = _ := by ring

theorem cancelledTimeKernel_le {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} {C L R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hK : ∀ z ≠ 0, (∫ s in Ioi (0 : ℝ), |K s z|) ≤ C * ‖z‖ ^ (-3 : ℝ))
    (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (x y : Space) :
    |cancelledTimeKernel K φ x y| ≤
      (C * max (2 * L) 1) * (‖x - y‖ ^ (-3 : ℝ) * min (‖x - y‖ / R) 1) :=
  (cancelledTimeKernel_abs_le K φ x y).trans
    (absoluteCancelledTimeKernel_le hC hR hK hφ hLip x y)

theorem cancelledTimeIntegrand_measurable {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} (hK : Measurable (Function.uncurry K))
    (hφ : Measurable φ) :
    Measurable (fun p : (Space × Space) × ℝ =>
      K p.2 (p.1.1 - p.1.2) * cutoffSquareDifference φ p.1.1 p.1.2) := by
  have hmap : Measurable (fun p : (Space × Space) × ℝ =>
      (p.2, p.1.1 - p.1.2)) := by fun_prop
  have hdiff : Measurable (fun p : (Space × Space) × ℝ =>
      cutoffSquareDifference φ p.1.1 p.1.2) := by
    unfold cutoffSquareDifference
    fun_prop
  exact (hK.comp hmap).mul hdiff

theorem cancelledTimeKernel_measurable {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} (hK : Measurable (Function.uncurry K))
    (hφ : Measurable φ) :
    Measurable (Function.uncurry (cancelledTimeKernel K φ)) := by
  exact (cancelledTimeIntegrand_measurable hK hφ).stronglyMeasurable.integral_prod_right'.measurable

theorem absoluteCancelledTimeKernel_measurable {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} (hK : Measurable (Function.uncurry K))
    (hφ : Measurable φ) :
    Measurable (Function.uncurry (absoluteCancelledTimeKernel K φ)) := by
  change Measurable (fun z : Space × Space => ∫ s in Ioi (0 : ℝ), |K s (z.1 - z.2) *
      cutoffSquareDifference φ z.1 z.2|)
  simpa only [Real.norm_eq_abs] using
    ((cancelledTimeIntegrand_measurable hK hφ).norm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

/-- The algebraic cancellation is inserted before either variable is integrated. -/
theorem cutoffSquareDifference_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (k : ℝ) (φ : Space → ℝ) (r : E) (x y : Space) :
    k • (φ y ^ 2 • r) - φ x ^ 2 • (k • r) =
      (k * cutoffSquareDifference φ x y) • r := by
  simp only [cutoffSquareDifference, mul_sub, sub_smul, smul_smul]
  rw [mul_comm (φ x ^ 2) k]

end NavierStokesR3.Comparison

end
end

end

section

/-!
# The three dimensional heat kernel

The definitions in this file are the ordinary Gaussian heat kernel and its
coordinate Hessian.  The latter is proved to agree with the spatial derivatives
used in the comparison argument.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The Euclidean heat kernel in three spatial dimensions. -/
def heatKernel (s : ℝ) (z : Space) : ℝ :=
  (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2) / (4 * s))

/-- The explicit coordinate Hessian of the Euclidean heat kernel. -/
def heatKernelSecond (s : ℝ) (i j : Fin 3) (z : Space) : ℝ :=
  (z i * z j / (4 * s ^ 2) - (if i = j then 1 else 0) / (2 * s)) *
    heatKernel s z

theorem heatKernel_pos {s : ℝ} (hs : 0 < s) (z : Space) : 0 < heatKernel s z := by
  unfold heatKernel
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

theorem heatKernel_nonneg {s : ℝ} (hs : 0 ≤ s) (z : Space) :
    0 ≤ heatKernel s z := by
  unfold heatKernel
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)

theorem hasFDerivAt_heatKernel {s : ℝ} (hs : 0 < s) (z : Space) :
    HasFDerivAt (heatKernel s)
      ((-(heatKernel s z / (2 * s))) • innerSL ℝ z) z := by
  have he : HasFDerivAt (fun x : Space => -(‖x‖ ^ 2) / (4 * s))
      ((4 * s)⁻¹ • (-((2 : ℝ) • innerSL ℝ z))) z := by
    simpa only [Pi.neg_apply, div_eq_mul_inv, mul_comm, two_smul] using
      (hasStrictFDerivAt_norm_sq z).hasFDerivAt.neg.const_mul ((4 * s)⁻¹)
  convert! he.exp.const_mul ((4 * Real.pi * s) ^ (-(3 / 2 : ℝ))) using 1
  ext y
  simp only [_root_.smul_apply, _root_.neg_apply,
    innerSL_apply_apply, smul_eq_mul]
  unfold heatKernel
  field_simp
  ring

theorem partial_heatKernel {s : ℝ} (hs : 0 < s) (i : Fin 3) (z : Space) :
    partialD i (heatKernel s) z = -(z i / (2 * s)) * heatKernel s z := by
  unfold partialD NavierStokes.PeriodicIntegration.spatialPartial
  rw [(hasFDerivAt_heatKernel hs z).fderiv]
  simp [NavierStokes.ProblemStatement.coordinateVector,
    EuclideanSpace.inner_single_right]
  ring

theorem differentiable_heatKernel {s : ℝ} (hs : 0 < s) :
    Differentiable ℝ (heatKernel s) := fun z =>
  (hasFDerivAt_heatKernel hs z).differentiableAt

theorem contDiff_heatKernel (s : ℝ) : ContDiff ℝ ∞ (heatKernel s) := by
  unfold heatKernel
  exact contDiff_const.mul (((contDiff_id.norm_sq ℝ).neg.div_const (4 * s)).exp)

/-- The explicit Gaussian Hessian is the actual iterated coordinate derivative. -/
theorem heatKernelSecond_eq_partial {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    heatKernelSecond s i j z = partialD i (partialD j (heatKernel s)) z := by
  have hfirst : partialD j (heatKernel s) =
      (fun x : Space => -(x j / (2 * s)) * heatKernel s x) :=
    funext (partial_heatKernel hs j)
  have hc : HasFDerivAt (fun x : Space => x j)
      (innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector j)) z := by
    convert! (innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector j)).hasFDerivAt
      (x := z) using 1
    ext x
    simp [NavierStokes.ProblemStatement.coordinateVector,
      EuclideanSpace.inner_single_left]
  have hg : HasFDerivAt (fun x : Space => -(x j / (2 * s)))
      ((-((2 * s)⁻¹)) • innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector j)) z := by
    convert! hc.const_mul (-((2 * s)⁻¹)) using 1
    ext x
    ring
  rw [hfirst]
  unfold partialD NavierStokes.PeriodicIntegration.spatialPartial
  change heatKernelSecond s i j z = fderiv ℝ ((fun x : Space => -(x j / (2 * s))) * heatKernel s) z
      (NavierStokes.ProblemStatement.coordinateVector i)
  rw [(hg.mul (hasFDerivAt_heatKernel hs z)).fderiv]
  by_cases hij : i = j
  · subst i
    simp [heatKernelSecond, NavierStokes.ProblemStatement.coordinateVector,
        EuclideanSpace.inner_single_right]
    field_simp
    ring
  · simp [heatKernelSecond, hij,
      NavierStokes.ProblemStatement.coordinateVector, EuclideanSpace.inner_single_right]
    field_simp
    ring

/-- A radial envelope for every component of the Gaussian Hessian. -/
theorem norm_heatKernelSecond_le {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    ‖heatKernelSecond s i j z‖ ≤
      (‖z‖ ^ 2 / (4 * s ^ 2) + 1 / (2 * s)) * heatKernel s z := by
  have hden₁ : 0 < 4 * s ^ 2 := by positivity
  have hden₂ : 0 < 2 * s := by positivity
  have hcoord : ‖z i * z j‖ ≤ ‖z‖ ^ 2 := by
    rw [norm_mul, pow_two]
    exact mul_le_mul (PiLp.norm_apply_le z i) (PiLp.norm_apply_le z j)
      (norm_nonneg _) (norm_nonneg _)
  have hdiag : ‖(if i = j then (1 : ℝ) else 0)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have hcoeff :
      ‖z i * z j / (4 * s ^ 2) - (if i = j then 1 else 0) / (2 * s)‖ ≤
        ‖z‖ ^ 2 / (4 * s ^ 2) + 1 / (2 * s) := by
    calc
      _ ≤ ‖z i * z j / (4 * s ^ 2)‖ +
          ‖(if i = j then (1 : ℝ) else 0) / (2 * s)‖ := norm_sub_le _ _
      _ = ‖z i * z j‖ / (4 * s ^ 2) +
          ‖(if i = j then (1 : ℝ) else 0)‖ / (2 * s) := by
        simp only [norm_div, Real.norm_eq_abs, abs_of_pos hden₁, abs_of_pos hden₂]
      _ ≤ _ := add_le_add
        (div_le_div_of_nonneg_right hcoord hden₁.le)
        (div_le_div_of_nonneg_right hdiag hden₂.le)
  rw [heatKernelSecond, norm_mul, Real.norm_of_nonneg (heatKernel_nonneg hs.le z)]
  exact mul_le_mul_of_nonneg_right hcoeff (heatKernel_nonneg hs.le z)

end NavierStokesR3.Comparison

end
end

end
