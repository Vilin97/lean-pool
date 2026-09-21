/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.DifferenceQuotientH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph.Preliminaries
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.QuantitativeCutoff
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Order.Filter.Finite

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.EnergyIntegrand

/-! # Diff Quotient Lp -/

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {U V : Set (Vec d)}
variable {u : H1Function U} {f : Vec d → ℝ}

/-- The H¹₀ scalar approximants converge globally whenever both the limit and
the approximants are genuinely supported in the domain. -/
theorem tendsto_eLpNorm_h10_approx_sub_toFun_global_of_support_subset
    (ψ : H10Function U)
    (hψ_support : Function.support ψ.toH1Function.toFun ⊆ U) :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x => ψ.approx n x - ψ.toH1Function.toFun x)
          2 MeasureTheory.volume)
      Filter.atTop (nhds 0) := by
  have hEq :
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x => ψ.approx n x - ψ.toH1Function.toFun x)
          2 MeasureTheory.volume) =
        fun n =>
          MeasureTheory.eLpNorm
            (fun x => ψ.approx n x - ψ.toH1Function.toFun x)
            2 (MeasureTheory.volume.restrict U) := by
    funext n
    have happrox_support : Function.support (ψ.approx n) ⊆ U :=
      (subset_tsupport (ψ.approx n)).trans (ψ.approx_support_subset n)
    have hdiff_support :
        Function.support (fun x => ψ.approx n x - ψ.toH1Function.toFun x) ⊆ U :=
      (Function.support_sub _ _).trans
        (Set.union_subset happrox_support hψ_support)
    exact eLpNorm_eq_restrict_of_support_subset (U := U) hdiff_support
  rw [hEq]
  exact ψ.tendsto_approx

/-- The scalar H¹₀ approximation errors are globally a.e.-strongly-measurable
when their support is genuinely contained in the domain. -/
theorem aestronglyMeasurable_h10_approx_sub_toFun_global_of_support_subset
    (hU_meas : MeasurableSet U) (ψ : H10Function U)
    (hψ_support : Function.support ψ.toH1Function.toFun ⊆ U) (n : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => ψ.approx n x - ψ.toH1Function.toFun x)
      MeasureTheory.volume := by
  have hrestrict :
      MeasureTheory.AEStronglyMeasurable
        (fun x => ψ.approx n x - ψ.toH1Function.toFun x)
        (MeasureTheory.volume.restrict U) :=
    ((ψ.approx_smooth n).continuous.aestronglyMeasurable.restrict).sub
      ψ.toH1Function.memL2.aestronglyMeasurable
  have happrox_support : Function.support (ψ.approx n) ⊆ U :=
    (subset_tsupport (ψ.approx n)).trans (ψ.approx_support_subset n)
  have hdiff_support :
      Function.support (fun x => ψ.approx n x - ψ.toH1Function.toFun x) ⊆ U :=
    (Function.support_sub _ _).trans
      (Set.union_subset happrox_support hψ_support)
  exact aestronglyMeasurable_of_restrict_of_support_subset
    (U := U) hU_meas hrestrict hdiff_support

/-- Global convergence of the backward difference quotients of the H¹₀
approximants to the backward difference quotient of the H¹₀ limit. -/
theorem tendsto_eLpNorm_h10_backwardDifferenceQuotient_approx_sub_toFun_global
    (hU_meas : MeasurableSet U) (ψ : H10Function U)
    (hψ_support : Function.support ψ.toH1Function.toFun ⊆ U)
    (step : ℝ) (i : Fin d) :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x =>
            euclideanBackwardDifferenceQuotient step i (ψ.approx n) x -
              euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun x)
          2 MeasureTheory.volume)
      Filter.atTop (nhds 0) :=
  tendsto_eLpNorm_backwardDifferenceQuotient_sub_zero
    (F := ψ.approx) (G := ψ.toH1Function.toFun)
    (fun n =>
      aestronglyMeasurable_h10_approx_sub_toFun_global_of_support_subset
        (U := U) hU_meas ψ hψ_support n)
    (tendsto_eLpNorm_h10_approx_sub_toFun_global_of_support_subset
      (U := U) ψ hψ_support)
    step i

/-- The smooth whole-space quotient estimate passes to a genuinely supported
`H¹₀(U)` limit.  This is the zero-trace version of
`eLpNorm_euclideanBackwardDifferenceQuotient_le_eLpNorm_coordDeriv`: the
derivative side is the weak gradient coordinate on `U`. -/
theorem eLpNorm_h10_backwardDifferenceQuotient_le_eLpNorm_grad
    (hU_meas : MeasurableSet U) (ψ : H10Function U)
    (hψ_support : Function.support ψ.toH1Function.toFun ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d) :
    MeasureTheory.eLpNorm
        (euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun)
        2 MeasureTheory.volume ≤
      MeasureTheory.eLpNorm (fun x => ψ.toH1Function.grad x i)
        2 (MeasureTheory.volume.restrict U) := by
  let L : ℝ≥0∞ :=
    MeasureTheory.eLpNorm
      (euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun)
      2 MeasureTheory.volume
  let R : ℝ≥0∞ :=
    MeasureTheory.eLpNorm (fun x => ψ.toH1Function.grad x i)
      2 (MeasureTheory.volume.restrict U)
  let A : ℕ → ℝ≥0∞ := fun n =>
    MeasureTheory.eLpNorm
      (fun x =>
        euclideanBackwardDifferenceQuotient step i (ψ.approx n) x -
          euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun x)
      2 MeasureTheory.volume
  let B : ℕ → ℝ≥0∞ := fun n =>
    MeasureTheory.eLpNorm
      (fun x =>
        euclideanCoordDeriv i (ψ.approx n) x - ψ.toH1Function.grad x i)
      2 (MeasureTheory.volume.restrict U)
  have hA :
      Filter.Tendsto A Filter.atTop (nhds 0) := by
    simpa [A] using
      tendsto_eLpNorm_h10_backwardDifferenceQuotient_approx_sub_toFun_global
        (U := U) hU_meas ψ hψ_support step i
  have hB :
      Filter.Tendsto B Filter.atTop (nhds 0) := by
    simpa [B, euclideanCoordDeriv] using ψ.tendsto_approx_grad i
  have hAB :
      Filter.Tendsto (fun n => A n + B n) Filter.atTop (nhds 0) := by
    simpa [zero_add] using hA.add hB
  have hupper_tendsto :
      Filter.Tendsto (fun n => R + (A n + B n)) Filter.atTop (nhds R) := by
    simpa [add_zero] using tendsto_const_nhds.add hAB
  have hle_upper : ∀ n : ℕ, L ≤ R + (A n + B n) := by
    intro n
    let Ln : ℝ≥0∞ :=
      MeasureTheory.eLpNorm
        (euclideanBackwardDifferenceQuotient step i (ψ.approx n))
        2 MeasureTheory.volume
    let Rn : ℝ≥0∞ :=
      MeasureTheory.eLpNorm (euclideanCoordDeriv i (ψ.approx n))
        2 MeasureTheory.volume
    have hdq_approx_meas :
        MeasureTheory.AEStronglyMeasurable
          (euclideanBackwardDifferenceQuotient step i (ψ.approx n))
          MeasureTheory.volume :=
      (contDiff_euclideanBackwardDifferenceQuotient (ψ.approx_smooth n) step i).continuous
        |>.aestronglyMeasurable
    have hdq_diff_meas :
        MeasureTheory.AEStronglyMeasurable
          (fun x =>
            euclideanBackwardDifferenceQuotient step i (ψ.approx n) x -
              euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun x)
          MeasureTheory.volume :=
      aestronglyMeasurable_backwardDifferenceQuotient_sub_of_aestronglyMeasurable
        (F := ψ.approx n) (G := ψ.toH1Function.toFun)
        (aestronglyMeasurable_h10_approx_sub_toFun_global_of_support_subset
          (U := U) hU_meas ψ hψ_support n)
        step i
    have hL_le : L ≤ Ln + A n := by
      have htri :=
        MeasureTheory.eLpNorm_add_le
          (μ := MeasureTheory.volume) (p := (2 : ℝ≥0∞))
          hdq_approx_meas hdq_diff_meas.neg
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hpoint :
          (euclideanBackwardDifferenceQuotient step i (ψ.approx n) +
            - fun x =>
                euclideanBackwardDifferenceQuotient step i (ψ.approx n) x -
                  euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun x) =
            euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun := by
        funext x
        change
          euclideanBackwardDifferenceQuotient step i (ψ.approx n) x -
              (euclideanBackwardDifferenceQuotient step i (ψ.approx n) x -
                euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun x) =
            euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun x
        ring
      calc
        L =
            MeasureTheory.eLpNorm
              (euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun)
              2 MeasureTheory.volume := rfl
        _ =
            MeasureTheory.eLpNorm
              (euclideanBackwardDifferenceQuotient step i (ψ.approx n) +
                - fun x =>
                    euclideanBackwardDifferenceQuotient step i (ψ.approx n) x -
                      euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun x)
              2 MeasureTheory.volume := by
                rw [hpoint]
        _ ≤ Ln + A n := by
          simpa [Ln, A, Pi.add_apply, Pi.neg_apply] using htri
    have hsmooth : Ln ≤ Rn :=
      eLpNorm_euclideanBackwardDifferenceQuotient_le_eLpNorm_coordDeriv
        (ψ.approx_smooth n) (ψ.approx_hasCompactSupport n) hstep i
    have hderiv_approx_mem :
        MeasureTheory.MemLp (euclideanCoordDeriv i (ψ.approx n))
          2 (MeasureTheory.volume.restrict U) := by
      have hglobal :
          MeasureTheory.MemLp (euclideanCoordDeriv i (ψ.approx n))
            2 MeasureTheory.volume :=
        (contDiff_euclideanCoordDeriv (ψ.approx_smooth n) i).continuous.memLp_of_hasCompactSupport
          (hasCompactSupport_euclideanCoordDeriv (ψ.approx_hasCompactSupport n) i)
      exact hglobal.restrict U
    have hderiv_diff_mem :
        MeasureTheory.MemLp
          (fun x =>
            euclideanCoordDeriv i (ψ.approx n) x - ψ.toH1Function.grad x i)
          2 (MeasureTheory.volume.restrict U) :=
      hderiv_approx_mem.sub (ψ.toH1Function.gradMemL2 i)
    have hR_le : Rn ≤ R + B n := by
      have hderiv_support :
          Function.support (euclideanCoordDeriv i (ψ.approx n)) ⊆ U :=
        (support_euclideanCoordDeriv_subset_tsupport i (ψ.approx n)).trans
          (ψ.approx_support_subset n)
      have htri :=
        MeasureTheory.eLpNorm_add_le
          (μ := MeasureTheory.volume.restrict U) (p := (2 : ℝ≥0∞))
          (ψ.toH1Function.gradMemL2 i).aestronglyMeasurable
          hderiv_diff_mem.aestronglyMeasurable
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hderiv_point :
          ((fun x => ψ.toH1Function.grad x i) +
            fun x =>
              euclideanCoordDeriv i (ψ.approx n) x -
                ψ.toH1Function.grad x i) =
            euclideanCoordDeriv i (ψ.approx n) := by
        funext x
        change
          ψ.toH1Function.grad x i +
              (euclideanCoordDeriv i (ψ.approx n) x -
                ψ.toH1Function.grad x i) =
            euclideanCoordDeriv i (ψ.approx n) x
        ring
      calc
        Rn =
            MeasureTheory.eLpNorm (euclideanCoordDeriv i (ψ.approx n))
              2 (MeasureTheory.volume.restrict U) := by
                change
                  MeasureTheory.eLpNorm (euclideanCoordDeriv i (ψ.approx n))
                    2 MeasureTheory.volume =
                  MeasureTheory.eLpNorm (euclideanCoordDeriv i (ψ.approx n))
                    2 (MeasureTheory.volume.restrict U)
                exact eLpNorm_eq_restrict_of_support_subset
                  (U := U) hderiv_support
        _ ≤ R + B n := by
          simpa [R, B, hderiv_point, Pi.add_apply] using htri
    calc
      L ≤ Ln + A n := hL_le
      _ ≤ Rn + A n := by
        simpa [add_comm] using add_le_add_right hsmooth (A n)
      _ ≤ (R + B n) + A n := by
        simpa [add_comm] using add_le_add_right hR_le (A n)
      _ = R + (A n + B n) := by
        rw [add_assoc, add_comm (B n) (A n)]
  exact ge_of_tendsto hupper_tendsto (Filter.Eventually.of_forall hle_upper)

/-- The global backward quotient of a genuinely supported `H¹₀(U)` function is
an `L²(ℝᵈ)` function. -/
theorem memLp_h10_backwardDifferenceQuotient_of_support_subset
    (hU_meas : MeasurableSet U) (ψ : H10Function U)
    (hψ_support : Function.support ψ.toH1Function.toFun ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d) :
    MeasureTheory.MemLp
      (euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun)
      2 MeasureTheory.volume := by
  have hψ_meas : MeasureTheory.AEStronglyMeasurable ψ.toH1Function.toFun
      MeasureTheory.volume :=
    aestronglyMeasurable_of_restrict_of_support_subset
      (U := U) hU_meas ψ.toH1Function.memL2.aestronglyMeasurable hψ_support
  have hdiff_meas : MeasureTheory.AEStronglyMeasurable
      (fun x => ψ.toH1Function.toFun x - (fun _ : Vec d => (0 : ℝ)) x)
      MeasureTheory.volume :=
    hψ_meas.sub MeasureTheory.aestronglyMeasurable_const
  have hquot_meas : MeasureTheory.AEStronglyMeasurable
      (euclideanBackwardDifferenceQuotient step i ψ.toH1Function.toFun)
      MeasureTheory.volume := by
    have hraw :=
      aestronglyMeasurable_backwardDifferenceQuotient_sub_of_aestronglyMeasurable
        (F := ψ.toH1Function.toFun) (G := fun _ : Vec d => (0 : ℝ))
        hdiff_meas step i
    change MeasureTheory.AEStronglyMeasurable
      (fun x =>
        (ψ.toH1Function.toFun x -
          ψ.toH1Function.toFun (euclideanCoordShift (-step) i x)) / step)
      MeasureTheory.volume
    simpa [euclideanBackwardDifferenceQuotient] using hraw
  have hnorm :=
    eLpNorm_h10_backwardDifferenceQuotient_le_eLpNorm_grad
      (U := U) hU_meas ψ hψ_support hstep i
  exact ⟨hquot_meas,
    lt_of_le_of_lt hnorm (ψ.toH1Function.gradMemL2 i).eLpNorm_lt_top⟩

/-- Forward version of the `H¹₀` quotient estimate. -/
theorem eLpNorm_h10_forwardDifferenceQuotient_le_eLpNorm_grad
    (hU_meas : MeasurableSet U) (ψ : H10Function U)
    (hψ_support : Function.support ψ.toH1Function.toFun ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d) :
    MeasureTheory.eLpNorm
        (euclideanForwardDifferenceQuotient step i ψ.toH1Function.toFun)
        2 MeasureTheory.volume ≤
      MeasureTheory.eLpNorm (fun x => ψ.toH1Function.grad x i)
        2 (MeasureTheory.volume.restrict U) := by
  rw [euclideanForwardDifferenceQuotient_eq_backwardDifferenceQuotient_neg]
  exact
    eLpNorm_h10_backwardDifferenceQuotient_le_eLpNorm_grad
      (U := U) hU_meas ψ hψ_support (neg_ne_zero.mpr hstep) i

/-- The global forward quotient of a genuinely supported `H¹₀(U)` function is
an `L²(ℝᵈ)` function. -/
theorem memLp_h10_forwardDifferenceQuotient_of_support_subset
    (hU_meas : MeasurableSet U) (ψ : H10Function U)
    (hψ_support : Function.support ψ.toH1Function.toFun ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d) :
    MeasureTheory.MemLp
      (euclideanForwardDifferenceQuotient step i ψ.toH1Function.toFun)
      2 MeasureTheory.volume := by
  rw [euclideanForwardDifferenceQuotient_eq_backwardDifferenceQuotient_neg]
  exact
    memLp_h10_backwardDifferenceQuotient_of_support_subset
      (U := U) hU_meas ψ hψ_support (neg_ne_zero.mpr hstep) i

/-- Integral-square form of the forward `H¹₀` quotient estimate. -/
theorem integral_forwardDifferenceQuotient_sq_le_integral_h10_grad_sq
    (hU_meas : MeasurableSet U) (ψ : H10Function U)
    (hψ_support : Function.support ψ.toH1Function.toFun ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d) :
    ∫ x, (euclideanForwardDifferenceQuotient step i ψ.toH1Function.toFun x) ^ 2
        ∂MeasureTheory.volume ≤
      ∫ x in U, (ψ.toH1Function.grad x i) ^ 2 ∂MeasureTheory.volume := by
  have hquot_mem :=
    memLp_h10_forwardDifferenceQuotient_of_support_subset
      (U := U) hU_meas ψ hψ_support hstep i
  have hgrad_mem := ψ.toH1Function.gradMemL2 i
  have hnorm :=
    eLpNorm_h10_forwardDifferenceQuotient_le_eLpNorm_grad
      (U := U) hU_meas ψ hψ_support hstep i
  have htoReal_le :
      ENNReal.toReal
          (MeasureTheory.eLpNorm
            (euclideanForwardDifferenceQuotient step i ψ.toH1Function.toFun)
            2 MeasureTheory.volume) ≤
        ENNReal.toReal
          (MeasureTheory.eLpNorm (fun x => ψ.toH1Function.grad x i)
            2 (MeasureTheory.volume.restrict U)) :=
    (ENNReal.toReal_le_toReal hquot_mem.eLpNorm_ne_top hgrad_mem.eLpNorm_ne_top).2 hnorm
  have hsq_le :
      (ENNReal.toReal
          (MeasureTheory.eLpNorm
            (euclideanForwardDifferenceQuotient step i ψ.toH1Function.toFun)
            2 MeasureTheory.volume)) ^ 2 ≤
        (ENNReal.toReal
          (MeasureTheory.eLpNorm (fun x => ψ.toH1Function.grad x i)
            2 (MeasureTheory.volume.restrict U))) ^ 2 :=
    (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).2 htoReal_le
  rw [toReal_eLpNorm_two_sq_eq_integral_sq hquot_mem,
    toReal_eLpNorm_two_sq_eq_integral_sq hgrad_mem] at hsq_le
  exact hsq_le

/-- Set-localized integral-square form of the forward `H¹₀` quotient estimate. -/
theorem integral_set_forwardDifferenceQuotient_sq_le_integral_h10_grad_sq
    (hU_meas : MeasurableSet U) (ψ : H10Function U)
    (hψ_support : Function.support ψ.toH1Function.toFun ⊆ U)
    (S : Set (Vec d)) {step : ℝ} (hstep : step ≠ 0) (i : Fin d) :
    ∫ x in S, (euclideanForwardDifferenceQuotient step i ψ.toH1Function.toFun x) ^ 2
        ∂MeasureTheory.volume ≤
      ∫ x in U, (ψ.toH1Function.grad x i) ^ 2 ∂MeasureTheory.volume := by
  have hquot_mem :=
    memLp_h10_forwardDifferenceQuotient_of_support_subset
      (U := U) hU_meas ψ hψ_support hstep i
  have hset_le :
      ∫ x in S, (euclideanForwardDifferenceQuotient step i ψ.toH1Function.toFun x) ^ 2
          ∂MeasureTheory.volume ≤
        ∫ x, (euclideanForwardDifferenceQuotient step i ψ.toH1Function.toFun x) ^ 2
          ∂MeasureTheory.volume :=
    MeasureTheory.setIntegral_le_integral hquot_mem.integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  exact hset_le.trans
    (integral_forwardDifferenceQuotient_sq_le_integral_h10_grad_sq
      (U := U) hU_meas ψ hψ_support hstep i)

/-- Lower-order quotient control for a function localized by a cutoff which is
one on the set of integration and on its forward coordinate shift. -/
theorem integral_set_forwardDifferenceQuotient_sq_le_integral_localized_h10_grad_sq
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U)
    {S : Set (Vec d)} (hS_meas : MeasurableSet S)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hφ_one : ∀ x ∈ S, φ x = 1)
    (hφ_shift_one : ∀ x ∈ S, φ (euclideanCoordShift step i x) = 1) :
    ∫ x in S, (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2
        ∂MeasureTheory.volume ≤
      ∫ x in U,
        ((u.mulContDiffHasCompactSupportToH10 hU
          hφ hφ_compact hφ_sub).toH1Function.grad x i) ^ 2
        ∂MeasureTheory.volume := by
  let ψ : H10Function U :=
    u.mulContDiffHasCompactSupportToH10 hU hφ hφ_compact hφ_sub
  have hψ_support : Function.support ψ.toH1Function.toFun ⊆ U := by
    have hfun : ψ.toH1Function.toFun = fun x => φ x * u.toFun x := by
      simp [ψ]
    rw [hfun]
    exact (Function.support_mul_subset_left φ u.toFun).trans
      ((subset_tsupport φ).trans hφ_sub)
  have hleft_eq :
      ∫ x in S, (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2
          ∂MeasureTheory.volume =
        ∫ x in S,
          (euclideanForwardDifferenceQuotient step i ψ.toH1Function.toFun x) ^ 2
          ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hS_meas] with x hx
    have hφx : φ x = 1 := hφ_one x hx
    have hφshift : φ (euclideanCoordShift step i x) = 1 :=
      hφ_shift_one x hx
    have hψx : ψ.toH1Function.toFun x = u.toFun x := by
      calc
        ψ.toH1Function.toFun x = φ x * u.toFun x := by simp [ψ]
        _ = u.toFun x := by rw [hφx]; ring
    have hψshift : ψ.toH1Function.toFun (euclideanCoordShift step i x) =
        u.toFun (euclideanCoordShift step i x) := by
      calc
        ψ.toH1Function.toFun (euclideanCoordShift step i x) =
            φ (euclideanCoordShift step i x) *
              u.toFun (euclideanCoordShift step i x) := by
          simp [ψ]
        _ = u.toFun (euclideanCoordShift step i x) := by
          rw [hφshift]
          ring
    have hquot :
        euclideanForwardDifferenceQuotient step i u.toFun x =
          euclideanForwardDifferenceQuotient step i ψ.toH1Function.toFun x := by
      unfold euclideanForwardDifferenceQuotient
      rw [hψshift, hψx]
    rw [hquot]
  rw [hleft_eq]
  exact
    integral_set_forwardDifferenceQuotient_sq_le_integral_h10_grad_sq
      (U := U) hU.isOpen.measurableSet ψ hψ_support S hstep i

/-- A smooth compactly supported cutoff localizes a scalar `L²(V)` function to
an ambient scalar `L²(U)` function when the cutoff support lies in `V`. -/
theorem memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
    {φ F : Vec d → ℝ} (hV_meas : MeasurableSet V)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ V) (hF : MemScalarL2 V F) :
    MemScalarL2 U (fun x => φ x * F x) := by
  have hφ_top :
      MeasureTheory.MemLp φ ⊤ (MeasureTheory.volume.restrict V) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hφ_compact
      (MeasureTheory.volume.restrict V)
  have hprodV :
      MeasureTheory.MemLp (fun x => φ x * F x) 2
        (MeasureTheory.volume.restrict V) := by
    simpa [MemScalarL2, volumeMeasureOn, mul_comm] using hF.mul' hφ_top
  have hsupport : Function.support (fun x => φ x * F x) ⊆ V :=
    (Function.support_mul_subset_left φ F).trans (subset_tsupport φ |>.trans hφ_sub)
  simpa [MemScalarL2, volumeMeasureOn] using
    memLp_restrict_of_support_subset_of_memLp
      (U := U) (V := V) hV_meas hsupport hprodV

end WeakPoissonEquationOn

end

end Homogenization
