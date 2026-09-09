/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryAdvectionLimit
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryRegularizedEnergy
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryRegularizer
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerUniqueness
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryRegularizedCauchy
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryStrongTime
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds

/-! General smooth local Euler existence in ordinary R³. The datum
has all actual spatial L² derivatives; no Gevrey radius is assumed.
The solution is the strong Sobolev limit of genuine symmetric
regularized Euler evolutions on one common positive interval. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral Finset
open scoped ContDiff Topology

namespace RegularizedEvolution

variable {T : ℝ} {hT : 0 ≤ T} {S : SmoothingOperator} (U : RegularizedEvolution S T hT)

/-- Derivative path, given by `fieldPath U.derivative U.derivative_continuous`. -/
def derivativePath : C(Icc (0 : ℝ) T,L2) := fieldPath U.derivative U.derivative_continuous

theorem integral_equation (t : Icc (0 : ℝ) T) :
    (U.velocity t).toLp=(U.velocity ⟨0,le_rfl,hT⟩).toLp +
      integral T hT U.derivativePath t := by
  have h := eq_initial_add_integral T hT U.derivativePath
    (fun r => (U.velocity (projIcc 0 T hT r)).toLp) U.l2_time t
  simpa only [projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)] using h

end RegularizedEvolution

namespace SmoothLimitData

variable {T : ℝ} {hT : 0 ≤ T} {U : ∀ n, RegularizedEvolution (regularizer n) T hT}
  (L : SmoothLimitData (fun n => (U n).velocity) (fun n => (U n).velocity_continuous))

theorem regularized_solenoidal (t : Icc (0 : ℝ) T) : (L.field t).toLp ∈ solenoidalSpace :=
  gradientSpace.isClosed_orthogonal.mem_of_tendsto (L.toLp_convergence t)
    (Eventually.of_forall (fun n => (U n).solenoidal t))

theorem regularized_derivative_convergence (M : ℝ)
    (hM : ∀ n t, WordBound 4 M ((U n).velocity t)) :
    Tendsto (fun n => (U n).derivativePath) atTop
      (𝓝 (projectedRhsPath L.field L.field_continuous)) := by
  have hp := L.projectedRhsPath_convergence hT (40*M)
    (fun n t => tensorNorm_three_le _ M (wordBound_mono (hM n t) (by omega)))
  have he (n : ℕ) :
      ‖(U n).derivativePath-projectedRhsPath (U n).velocity (U n).velocity_continuous‖ ≤
        regularizerError n*regularizationCost M := by
    apply (ContinuousMap.norm_le _ (mul_nonneg (regularizerError_nonneg n)
      (regularizationCost_nonneg M))).mpr
    intro t
    exact regularized_rhs_error n _ ((U n).solenoidal t) M (hM n t)
  have hz : Tendsto (fun n => (U n).derivativePath -
      projectedRhsPath (U n).velocity (U n).velocity_continuous) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) he
    simpa only [zero_mul] using regularizerError_tendsto.mul_const (regularizationCost M)
  have h := hz.add hp
  simpa only [sub_add_cancel,zero_add] using h

theorem regularized_integral_equation (M : ℝ)
    (hM : ∀ n t, WordBound 4 M ((U n).velocity t)) (t : Icc (0 : ℝ) T) :
    (L.field t).toLp=(L.field ⟨0,le_rfl,hT⟩).toLp +
      integral T hT (projectedRhsPath L.field L.field_continuous) t := by
  have hi := (ContinuousMap.evalCLM ℝ t).continuous.tendsto
    (integral T hT (projectedRhsPath L.field L.field_continuous)) |>.comp
      (((integral (E := L2) T hT).continuous.tendsto _).comp
        (L.regularized_derivative_convergence M hM))
  have hs := (L.toLp_convergence ⟨0,le_rfl,hT⟩).add hi
  exact tendsto_nhds_unique (L.toLp_convergence t)
    (hs.congr (fun n => ((U n).integral_equation t).symm))

theorem regularized_time (M : ℝ) (hM : ∀ n t, WordBound 4 M ((U n).velocity t))
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r => (L.field (projIcc 0 T hT r)).toLp)
      (projectedRhs (L.field t)).toLp (Icc (0 : ℝ) T) t := by
  have he : (fun r => (L.field (projIcc 0 T hT r)).toLp) =
      fun r => (L.field ⟨0,le_rfl,hT⟩).toLp +
        extendPath T hT (integral T hT (projectedRhsPath L.field L.field_continuous)) r := by
    funext r
    exact L.regularized_integral_equation M hM (projIcc 0 T hT r)
  rw [he]
  exact (integral_hasDerivWithinAt T hT (projectedRhsPath L.field L.field_continuous) t).const_add _

/-- Regularized evolution, bundling `velocity`, `pressureForce`, `velocity_continuous`,
`pressure_continuous` and the required compatibility proofs. -/
def regularizedEvolution (M : ℝ) (hM : ∀ n t, WordBound 4 M ((U n).velocity t)) :
    Evolution T hT where
  velocity := L.field
  pressureForce t := pressureField (L.field t)
  velocity_continuous := L.field_continuous
  pressure_continuous := pressureField_continuous L.field L.field_continuous
  solenoidal := L.regularized_solenoidal
  gradient t := pressureField_mem_gradient (L.field t)
  time_law t ht x := by
    have hd : ∀ r (hr : r ∈ Ioo 0 T),
        HasDerivAt (fun s => (L.field (projIcc 0 T hT s)).toLp)
          (projectedRhs (L.field ⟨r,hr.1.le,hr.2.le⟩)).toLp r := by
      intro r hr
      exact (L.regularized_time M hM ⟨r,hr.1.le,hr.2.le⟩).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
    have h := pointwise_derivative_of_l2 T hT L.field (fun s => projectedRhs (L.field s))
      L.field_continuous (projectedRhs_continuous L.field L.field_continuous) hd
      ⟨t,ht.1.le,ht.2.le⟩ x
    simpa only [projectedRhs_field] using h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end SmoothLimitData

/-- Regularized solution, given by `Classical.choose ((regularizer n).exists_smooth
(regularizedTime A) (regularizedTime_pos A).le A hA)`. -/
def regularizedSolution (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) (n : ℕ) :
    RegularizedEvolution (regularizer n) (regularizedTime A) (regularizedTime_pos A).le :=
  Classical.choose ((regularizer n).exists_smooth (regularizedTime A) (regularizedTime_pos A).le A
      hA)

theorem regularizedSolution_initial (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) (n :
    ℕ) :
    (regularizedSolution A hA n).velocity ⟨0,le_rfl,(regularizedTime_pos A).le⟩=A :=
  Classical.choose_spec ((regularizer n).exists_smooth (regularizedTime A) (regularizedTime_pos
      A).le A hA)

theorem regularizedSolution_bounds (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    ∀ q, ∃ M : ℝ, ∀ n t, tensorNorm q ((regularizedSolution A hA n).velocity t) ≤ M := by
  intro q
  obtain ⟨M,hM⟩ := regularized_all_order A q
  exact ⟨M,fun n t => hM _ _ (regularizedSolution_initial A hA n) t⟩

theorem regularizedSolution_cauchy (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    CauchySeq (fun n => fieldPath (regularizedSolution A hA n).velocity
      (regularizedSolution A hA n).velocity_continuous) := by
  obtain ⟨M,hM⟩ := regularizedSolution_bounds A hA 4
  apply regularized_cauchy (regularizedSolution A hA) M
    (fun n t k hk w => (wordBound_tensorNorm 4 _ k hk w).trans (hM n t))
  intro j k
  simp only [regularizedSolution_initial]

/-- Local limit, given by `smoothLimitData (regularizedTime_pos A).le _ _
(regularizedSolution_bounds A hA) (regularizedSolution_cauchy A hA)`. -/
def localLimit (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    SmoothLimitData (fun n => (regularizedSolution A hA n).velocity)
      (fun n => (regularizedSolution A hA n).velocity_continuous) :=
  smoothLimitData (regularizedTime_pos A).le _ _
    (regularizedSolution_bounds A hA) (regularizedSolution_cauchy A hA)

/-- Local evolution, choosing the witness provided by `regularizedSolution_bounds`. -/
def localEvolution (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    Evolution (regularizedTime A) (regularizedTime_pos A).le :=
  (localLimit A hA).regularizedEvolution (Classical.choose (regularizedSolution_bounds A hA 4))
    (fun n t k hk w => (wordBound_tensorNorm 4 _ k hk w).trans
      (Classical.choose_spec (regularizedSolution_bounds A hA 4) n t))

theorem localEvolution_initial (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    (localEvolution A hA).velocity ⟨0,le_rfl,(regularizedTime_pos A).le⟩=A := by
  apply smoothField_eq_of_toLp_eq
  have h := (localLimit A hA).toLp_convergence ⟨0,le_rfl,(regularizedTime_pos A).le⟩
  simp only [regularizedSolution_initial] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem exists_local_evolution (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    ∃ (T : ℝ) (hT : 0 < T), ∃ U : Evolution T hT.le,
      U.velocity ⟨0,le_rfl,hT.le⟩=A :=
  ⟨regularizedTime A,regularizedTime_pos A,localEvolution A hA,localEvolution_initial A hA⟩

end EulerOrdinarySobolev
