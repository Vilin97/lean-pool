/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialCutoffs
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! The compact initial velocity in the manuscript is constructed using
the fixed factorial-bounded outer cutoff and the actual curl potential. -/

@[expose] public section


noncomputable section

namespace EulerBaseDatum

open Set Filter ContinuousLinearMap MeasureTheory EulerSmoothLimit EulerVectorCalculus
  EulerSpatialCutoffs EulerGevrey  EulerLpTranslation EulerMeanSolenoidal
open scoped ContDiff Topology

/-- Potential, given by `outerCutoff x*linearPotential L i x`. -/
def potential (L : Space →L[ℝ] Space) (i : Fin 3) (x : Space) : ℝ :=
  outerCutoff x*linearPotential L i x

theorem potential_smooth (L : Space →L[ℝ] Space) (i : Fin 3) :
    ContDiff ℝ ∞ (potential L i) :=
  outerCutoff_contDiff.mul (contDiff_linearPotential L i)

theorem potential_support (L : Space →L[ℝ] Space) (i : Fin 3) :
    tsupport (potential L i) ⊆ Metric.closedBall (0 : Space) 2 :=
  tsupport_mul_subset_left.trans outerCutoff_support

/-- Velocity, given by `curl (potential L)`. -/
def velocity (L : Space →L[ℝ] Space) : Space → Space := curl (potential L)

theorem velocity_smooth (L : Space →L[ℝ] Space) : ContDiff ℝ ∞ (velocity L) :=
  contDiff_curl (potential L) (potential_smooth L)

theorem velocity_support (L : Space →L[ℝ] Space) :
    tsupport (velocity L) ⊆ Metric.closedBall (0 : Space) 2 :=
  tsupport_curl_subset (potential L) _ Metric.isClosed_closedBall (potential_support L)

theorem velocity_compact (L : Space →L[ℝ] Space) : HasCompactSupport (velocity L) :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset
    (isClosed_tsupport _) (velocity_support L)

theorem velocity_divergence (L : Space →L[ℝ] Space) (x : Space) :
    divergence (velocity L) x=0 := divergence_curl (potential L) (potential_smooth L) x

theorem velocity_odd (L : Space →L[ℝ] Space) (x : Space) : velocity L (-x)= -velocity L x := by
  apply odd_curl_of_even (potential L) (fun i => (potential_smooth L i).differentiable (by simp))
  intro i y
  simp only [potential,outerCutoff_even,linearPotential_even]

theorem velocity_plateau (L : Space →L[ℝ] Space) (hL : LinearMap.trace ℝ Space L.toLinearMap = 0)
    (x : Space) (hx : ‖x‖ < 1) : velocity L x=L x := by
  have he (i : Fin 3) : potential L i =ᶠ[𝓝 x] linearPotential L i := by
    have hx' : x ∈ Metric.ball (0 : Space) 1 := by
        simpa only [Metric.mem_ball,dist_zero_right] using hx
    filter_upwards [Metric.isOpen_ball.mem_nhds hx'] with y hy
    have hy' : ‖y‖ ≤ 1 := (by simpa only [Metric.mem_ball,dist_zero_right] using hy : ‖y‖ < 1).le
    simp only [potential,outerCutoff_one y hy',one_mul]
  exact (curl_congr_nhds _ _ x he).trans (curl_linearPotential_of_trace_zero L hL x)

theorem velocity_fderiv_plateau (L : Space →L[ℝ] Space)
    (hL : LinearMap.trace ℝ Space L.toLinearMap = 0) (x : Space) (hx : ‖x‖ < 1) :
    fderiv ℝ (velocity L) x=L := by
  have he : velocity L =ᶠ[𝓝 x] (L : Space → Space) := by
    have hx' : x ∈ Metric.ball (0 : Space) 1 := by
        simpa only [Metric.mem_ball,dist_zero_right] using hx
    filter_upwards [Metric.isOpen_ball.mem_nhds hx'] with y hy
    exact velocity_plateau L hL y (by simpa only [Metric.mem_ball,dist_zero_right] using hy)
  exact he.fderiv_eq.trans L.fderiv

/-- Field, bundling `field`, `smooth`, `integrable`. -/
def field (L : Space →L[ℝ] Space) : SmoothL2Field Space where
  field := velocity L
  smooth := velocity_smooth L
  integrable n := ((velocity_smooth L).continuous_iteratedFDeriv (m := n) (by
      simp)).memLp_of_hasCompactSupport
    ((velocity_compact L).iteratedFDeriv n)

theorem velocity_memLp (L : Space →L[ℝ] Space) : MemLp (velocity L) 2 volume :=
  (velocity_smooth L).continuous.memLp_of_hasCompactSupport (velocity_compact L)

theorem field_solenoidal (L : Space →L[ℝ] Space) :
    (velocity_memLp L).toLp (velocity L) ∈ solenoidalSpace :=
  smooth_mem_solenoidal (velocity L) (velocity_smooth L) (velocity_memLp L) (velocity_divergence L)

/-- Linear, given by `(EuclideanSpace.proj 1).smulRight (EuclideanSpace.single 0 1+β •
EuclideanSpace.single 2 1)`. -/
def linear (β : ℝ) : Space →L[ℝ] Space :=
  (EuclideanSpace.proj 1).smulRight (EuclideanSpace.single 0 1+β • EuclideanSpace.single 2 1)

@[simp] theorem linear_apply (β : ℝ) (x : Space) :
    linear β x=x 1 • (EuclideanSpace.single 0 1+β • EuclideanSpace.single 2 1) := rfl

theorem linear_trace (β : ℝ) : LinearMap.trace ℝ Space (linear β).toLinearMap=0 := by
  rw [← coordinateTrace_eq_linearTrace]
  simp [coordinateTrace,Fin.sum_univ_three,linear_apply,PiLp.smul_apply]

theorem linear_norm (β : ℝ) : ‖linear β‖ ≤ 1+|β| := by
  apply opNorm_le_bound _ (by positivity)
  intro x
  rw [linear_apply,norm_smul,Real.norm_eq_abs]
  have hv : ‖(EuclideanSpace.single 0 1 : Space)+β • EuclideanSpace.single 2 1‖ ≤ 1+|β| := by
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    simp
  exact (mul_le_mul (PiLp.norm_apply_le x 1) hv (norm_nonneg _) (norm_nonneg x)).trans_eq (mul_comm
      _ _)

theorem linear_q (β : ℝ) :
    linear β (EuclideanSpace.single 1 1)=EuclideanSpace.single 0 1+β • EuclideanSpace.single 2 1 :=
        by
  simp [linear_apply]

end EulerBaseDatum
