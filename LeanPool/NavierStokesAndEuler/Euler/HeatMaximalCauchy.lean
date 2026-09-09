/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.HeatMaximalEstimate
public import LeanPool.NavierStokesAndEuler.Euler.QuadraticCauchy

@[expose] public section

/-! Strong L²-time H² Cauchy convergence from genuine heat energy, avoiding weak compactness. -/

noncomputable section

namespace EulerHeatMaximalCauchy

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevLaplacian
  EulerHeatMaximalEstimate EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A bounded linear observation preserves the difference form of the forced heat right hand side. -/
theorem linear_heat_rhs_sub {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : Y →L[ℝ] Z) (A : X →L[ℝ] Y) (ν : ℝ) (u v : X) (f g : Y) :
    L (ν • A (u-v)+(f-g)) = L (ν • A u+f)-L (ν • A v+g) := by
  rw [map_sub A, smul_sub, sub_add_sub_comm, map_sub L]

/-- The difference of two actual differentiated heat equations is the same linear equation with difference source. -/
theorem first_derivative_difference (T : ℝ) (hT : 0 ≤ T) (ν : ℝ)
    (u v : C(Icc (0 : ℝ) T, SobolevSpace period 3))
    (f g : C(Icc (0 : ℝ) T, SobolevSpace period 1)) (t : ℝ) (i : Fin 4)
    (hu : HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT u s)))
      (value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT u t) + extendPath T hT f t))) t)
    (hv : HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT v s)))
      (value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT v t) + extendPath T hT g t))) t) :
    HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT (u-v) s)))
      (value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT (u-v) t) + extendPath T hT (f-g) t))) t :=
          by
  have h := hu.fun_sub hv
  have he : (fun s => value period (derivativeOperator period 2 i (extendPath T hT (u-v) s))) =
      fun s => value period (derivativeOperator period 2 i (extendPath T hT u s)) -
        value period (derivativeOperator period 2 i (extendPath T hT v s)) := by
    funext s
    exact map_sub ((valueOperator period 2).comp (derivativeOperator period 2 i))
      (u (projIcc 0 T hT s)) (v (projIcc 0 T hT s))
  have hr : value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT (u-v) t) + extendPath T hT (f-g) t)) =
      value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT u t) + extendPath T hT f t)) -
      value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT v t) + extendPath T hT g t)) := by
    exact linear_heat_rhs_sub ((valueOperator period 0).comp (derivativeOperator period 0 i))
      (laplacianOperator period 1) ν (u (projIcc 0 T hT t)) (v (projIcc 0 T hT t))
      (f (projIcc 0 T hT t)) (g (projIcc 0 T hT t))
  rw [he, hr]
  exact h

/-- Restrict a regularized path to its actual H¹ topology. -/
def lowerPath (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period 3)) :
    C(Icc (0 : ℝ) T, SobolevSpace period 1) :=
  (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u

/-- Embed the actual H² restriction of a regularized path into L² time. -/
def higherTime (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, SobolevSpace period 3)) :
    TimeLp T (SobolevSpace period 2) :=
  pathLp T hT ((truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)

/-- Embed the actual undifferentiated forcing into L² time. -/
def sourceTime (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period 1)) :
    TimeLp T (LiftL2 period) :=
  pathLp T hT ((valueOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T) f)

/-- The lower path restriction preserves differences. -/
theorem lowerPath_sub (T : ℝ) (u v : C(Icc (0 : ℝ) T, SobolevSpace period 3)) :
    lowerPath period T (u-v) = lowerPath period T u-lowerPath period T v :=
  map_sub ((restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T)) u v

/-- The actual higher time embedding preserves differences. -/
theorem higherTime_sub (T : ℝ) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, SobolevSpace period 3)) :
    higherTime period T hT (u-v) = higherTime period T hT u-higherTime period T hT v := by
  let A := (truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  exact (congrArg (pathLp T hT) (map_sub A u v)).trans (pathLp_sub T hT (A u) (A v))

/-- The actual source time embedding preserves differences. -/
theorem sourceTime_sub (T : ℝ) (hT : 0 ≤ T) (f g : C(Icc (0 : ℝ) T, SobolevSpace period 1)) :
    sourceTime period T hT (f-g) = sourceTime period T hT f-sourceTime period T hT g := by
  let A := (valueOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  exact (congrArg (pathLp T hT) (map_sub A f g)).trans (pathLp_sub T hT (A f) (A g))

/-- The true linear heat equation controls actual H² time differences by lower path and source differences. -/
theorem heat_H2_difference_bound (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u v : C(Icc (0 : ℝ) T, SobolevSpace period 3))
    (f g : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hd : ∀ t ∈ Ioo 0 T, ∀ i : Fin 4,
      HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT (u-v) s)))
        (value period (derivativeOperator period 0 i
          (ν • laplacianOperator period 1 (extendPath T hT (u-v) t) + extendPath T hT (f-g) t))) t)
            :
    ‖higherTime period T hT u-higherTime period T hT v‖^2 ≤
      (T+4*ν⁻¹)*‖lowerPath period T u-lowerPath period T v‖^2 +
      (ν⁻¹)^2*‖sourceTime period T hT f-sourceTime period T hT g‖^2 := by
  exact EulerQuadraticCauchy.transport_quadratic_bound (T+4*ν⁻¹) ((ν⁻¹)^2)
    (higherTime period T hT (u-v)) (higherTime period T hT u-higherTime period T hT v)
    (lowerPath period T (u-v)) (lowerPath period T u-lowerPath period T v)
    (sourceTime period T hT (f-g)) (sourceTime period T hT f-sourceTime period T hT g)
    (higherTime_sub period T hT u v) (lowerPath_sub period T u v) (sourceTime_sub period T hT f g)
    (heat_time_H2_bound period T hT ν hν (u-v) (f-g) hd)

/-- Actual regularized heat solutions which converge in H¹ and have Cauchy L² sources converge strongly in L² time with two full derivatives. -/
theorem heat_H2_cauchy (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period 3))
    (f : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hd : ∀ n t, t ∈ Ioo 0 T → ∀ i : Fin 4,
      HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT (u n) s)))
        (value period (derivativeOperator period 0 i
          (ν • laplacianOperator period 1 (extendPath T hT (u n) t) + extendPath T hT (f n) t))) t)
    (hu : CauchySeq (fun n => (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (u n)))
    (hf : CauchySeq (fun n => pathLp T hT ((valueOperator period 1).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (f n)))) :
    CauchySeq (fun n => pathLp T hT ((truncateOperator period 2).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (u n))) := by
  change CauchySeq (fun n => higherTime period T hT (u n))
  change CauchySeq (fun n => lowerPath period T (u n)) at hu
  change CauchySeq (fun n => sourceTime period T hT (f n)) at hf
  apply EulerQuadraticCauchy.cauchy_of_quadratic_bound
    (fun n => lowerPath period T (u n)) (fun n => sourceTime period T hT (f n))
    (fun n => higherTime period T hT (u n)) (T+4*ν⁻¹) ((ν⁻¹)^2) hu hf
  intro n m
  apply heat_H2_difference_bound period T hT ν hν (u n) (u m) (f n) (f m)
  intro t ht i
  exact first_derivative_difference period T hT ν (u n) (u m) (f n) (f m) t i
    (hd n t ht i) (hd m t ht i)

/-- Completeness constructs a genuine Bochner L²-time H² limit of the regularized heat solutions. -/
theorem exists_heat_H2_limit (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period 3))
    (f : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hd : ∀ n t, t ∈ Ioo 0 T → ∀ i : Fin 4,
      HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT (u n) s)))
        (value period (derivativeOperator period 0 i
          (ν • laplacianOperator period 1 (extendPath T hT (u n) t) + extendPath T hT (f n) t))) t)
    (hu : CauchySeq (fun n => (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (u n)))
    (hf : CauchySeq (fun n => pathLp T hT ((valueOperator period 1).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (f n)))) :
    ∃ U : TimeLp T (SobolevSpace period 2),
      Filter.Tendsto (fun n => pathLp T hT ((truncateOperator period 2).compLeftContinuous ℝ
        (Icc (0 : ℝ) T) (u n))) Filter.atTop (𝓝 U) :=
  cauchySeq_tendsto_of_complete (heat_H2_cauchy period T hT ν hν u f hd hu hf)

end EulerHeatMaximalCauchy
