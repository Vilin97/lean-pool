/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernelCancellation
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernelTimeBound
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RadialKernelBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PairedKernelBound

@[expose] public section

/-!
# The paired estimate for the heat commutator kernel

The time-integrated heat Hessian, after cutoff cancellation, is dominated by
the radial `L^(4/3)` kernel. Its exact scaling and the sectionwise Hölder bound
give the factor `R^(-3/4)` in the paired commutator estimate.
-/


noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The actual time-integrated heat Hessian with cutoff cancellation already
inserted into the time integrand. -/
def heatCommutatorKernel (i j : Fin 3) (φ : Space → ℝ) (x y : Space) : ℝ :=
  cancelledTimeKernel (fun s z => heatKernelSecond s i j z) φ x y

/-- A universal positive constant for the paired commutator estimate. -/
def rieszCommutatorConstant : ℝ :=
  heatKernelTimeConstant * (comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) + 1)

theorem rieszCommutatorConstant_pos : 0 < rieszCommutatorConstant := by
  exact mul_pos heatKernelTimeConstant_pos
    (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one)

/-- The explicit heat Hessian is jointly measurable in time and space,
including the totalized formula at time zero. -/
theorem heatKernelSecond_joint_measurable (i j : Fin 3) :
    Measurable (Function.uncurry (fun s z => heatKernelSecond s i j z)) := by
  have hcoord (a : Fin 3) : Measurable (fun p : ℝ × Space => p.2 a) := by
    have hc : Continuous (fun z : Space => z a) := by
      convert! (innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector a)).continuous using 1
      ext z
      simp [NavierStokes.ProblemStatement.coordinateVector, EuclideanSpace.inner_single_left]
    exact hc.measurable.comp measurable_snd
  have hs : Measurable (fun p : ℝ × Space => p.1) := measurable_fst
  have hz : Measurable (fun p : ℝ × Space => p.2) := measurable_snd
  have hs2 : Measurable (fun p : ℝ × Space => p.1 ^ 2) := by
    simpa only [pow_two] using! hs.mul hs
  have hz2 : Measurable (fun p : ℝ × Space => ‖p.2‖ ^ 2) := by
    simpa only [pow_two] using! hz.norm.mul hz.norm
  have hcoeff : Measurable (fun p : ℝ × Space =>
      p.2 i * p.2 j / (4 * p.1 ^ 2) - (if i = j then 1 else 0) / (2 * p.1)) :=
    (((hcoord i).mul (hcoord j)).div (measurable_const.mul hs2)).sub
      (measurable_const.div (measurable_const.mul hs))
  have hbase : Measurable (fun p : ℝ × Space =>
      (4 * Real.pi * p.1) ^ (-(3 / 2 : ℝ))) :=
    (measurable_const.mul hs).pow_const _
  have hexp : Measurable (fun p : ℝ × Space =>
      Real.exp (-(‖p.2‖ ^ 2) / (4 * p.1))) :=
    Real.continuous_exp.measurable.comp (hz2.neg.div (measurable_const.mul hs))
  simpa only [Function.uncurry, heatKernelSecond, heatKernel] using!
    hcoeff.mul (hbase.mul hexp)

/-- The integrated, cancelled heat kernel is jointly measurable in its two
spatial variables. -/
theorem heatCommutatorKernel_measurable (i j : Fin 3) {φ : Space → ℝ}
    (hφ : Measurable φ) :
    Measurable (Function.uncurry (heatCommutatorKernel i j φ)) :=
  cancelledTimeKernel_measurable (heatKernelSecond_joint_measurable i j) hφ

/-- Pointwise domination by the radial commutator kernel. -/
theorem heatCommutatorKernel_bound (i j : Fin 3) {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖) (x y : Space) :
    ‖heatCommutatorKernel i j φ x y‖ ≤
      (heatKernelTimeConstant * max (2 * L) 1) * radialCommutatorKernel R (x - y) := by
  simpa only [heatCommutatorKernel, Real.norm_eq_abs, radialCommutatorKernel] using
    cancelledTimeKernel_le heatKernelTimeConstant_pos.le hR
      (fun z hz => heatKernelSecond_integral_abs_le i j hz) hφ hLip x y

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every heat commutator section acts by an integrable scalar product on
`L⁴` data. -/
theorem heatKernel_commutator_section_integrable (i j : Fin 3)
    {φ : Space → ℝ} {r : Space → E} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (hr : MemLp r 4 volume) (x : Space) :
    Integrable (fun y => heatCommutatorKernel i j φ x y • r y) volume := by
  exact (PairedKernelBound.section_integrable_and_integral_norm_le
    (heatCommutatorKernel_measurable i j hφm)
    ((radialCommutatorKernel_memLp hR).const_mul (heatKernelTimeConstant * max (2 * L) 1))
    hr (heatCommutatorKernel_bound i j hR hφ hLip) x).1

/-- The paired heat kernel is integrable on the product of spatial domains. -/
theorem heatKernel_commutator_product_integrable (i j : Fin 3)
    {φ g : Space → ℝ} {r : Space → E} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (hg : Integrable g volume) (hr : MemLp r 4 volume) :
    Integrable (fun p : Space × Space =>
      g p.1 • (heatCommutatorKernel i j φ p.1 p.2 • r p.2))
      ((volume : Measure Space).prod volume) := by
  exact PairedKernelBound.integrable_paired_kernel
    (heatCommutatorKernel_measurable i j hφm)
    ((radialCommutatorKernel_memLp hR).const_mul (heatKernelTimeConstant * max (2 * L) 1))
    hr hg (heatCommutatorKernel_bound i j hR hφ hLip)

/-- The outer pairing is genuinely integrable for real `L¹` and vector-valued
`L⁴` data. -/
theorem heatKernel_commutator_pair_integrable (i j : Fin 3)
    {φ g : Space → ℝ} {r : Space → E} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (hg : Integrable g volume) (hr : MemLp r 4 volume) :
    Integrable (fun x => g x • ∫ y, heatCommutatorKernel i j φ x y • r y) volume := by
  exact PairedKernelBound.integrable_pairing
    (heatCommutatorKernel_measurable i j hφm)
    ((radialCommutatorKernel_memLp hR).const_mul (heatKernelTimeConstant * max (2 * L) 1))
    hr hg (heatCommutatorKernel_bound i j hR hφ hLip)

/-- The actual heat commutator satisfies the required paired estimate, with
the precise `R^(-3/4)` decay and a universal positive constant. -/
theorem heatKernel_paired_commutator_bound (i j : Fin 3)
    {φ g : Space → ℝ} {r : Space → E} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (hg : Integrable g volume) (hr : MemLp r 4 volume) :
    ‖∫ x, g x • ∫ y, heatCommutatorKernel i j φ x y • r y‖ ≤
      (rieszCommutatorConstant * max (2 * L) 1) * R ^ (-(3 / 4) : ℝ) *
        comparisonLpNorm 1 g * comparisonLpNorm 4 r := by
  have hmax : 0 ≤ max (2 * L) 1 := le_trans zero_le_one (le_max_right _ _)
  have hcoeff : 0 ≤ heatKernelTimeConstant * max (2 * L) 1 :=
    mul_nonneg heatKernelTimeConstant_pos.le hmax
  calc
    ‖∫ x, g x • ∫ y, heatCommutatorKernel i j φ x y • r y‖ ≤
        (heatKernelTimeConstant * max (2 * L) 1) * comparisonLpNorm 1 g *
          comparisonLpNorm (4 / 3) (radialCommutatorKernel R) * comparisonLpNorm 4 r :=
      PairedKernelBound.norm_paired_kernel_le_scaled
        (heatCommutatorKernel_measurable i j hφm) (radialCommutatorKernel_memLp hR)
        hr hg hcoeff (heatCommutatorKernel_bound i j hR hφ hLip)
    _ = (heatKernelTimeConstant * comparisonLpNorm (4 / 3) (radialCommutatorKernel 1)) *
        max (2 * L) 1 * R ^ (-(3 / 4) : ℝ) * comparisonLpNorm 1 g * comparisonLpNorm 4 r := by
      rw [radialCommutatorKernel_lpNorm_scale hR]
      ring
    _ ≤ (rieszCommutatorConstant * max (2 * L) 1) * R ^ (-(3 / 4) : ℝ) *
        comparisonLpNorm 1 g * comparisonLpNorm 4 r := by
      unfold rieszCommutatorConstant
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hR.le _)
      apply mul_le_mul_of_nonneg_right _ hmax
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
        heatKernelTimeConstant_pos.le

end NavierStokesR3.Comparison
