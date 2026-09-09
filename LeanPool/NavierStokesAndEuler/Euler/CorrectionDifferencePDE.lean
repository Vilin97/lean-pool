/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionDifference
import LeanPool.NavierStokesAndEuler.Euler.CorrectionMildEquation

/-! The exact viscosity-difference equation of two genuine nonlinear mild corrections. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionDifferencePDE

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerQuadraticSource EulerCorrectionContinuation EulerCorrectionDifference EulerSobolevTransport
   EulerSobolevHeatGenerator EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The existing Sobolev normed-group instance, fixed explicitly for difference-equation
elaboration. -/
local instance differenceSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- The existing real Sobolev module instance, fixed explicitly for difference-equation elaboration.
-/
local instance differenceSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
    inferInstance

/-- The literal right side of the viscosity-difference equation, including its genuine pressure
difference. -/
def differenceRhs {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (ν μ : ℝ) (t : T)
    (u v : SobolevSpace period (q + 1)) : LiftL2 period :=
  ν • laplacianEvaluation period (q+1) (by omega) (u-v) +
    (ν-μ) • laplacianEvaluation period (q+1) (by omega) v -
    value period (transportBilinear period hq (velocityComponents D.κ D.direction)
      (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) (D.approximation
          t+u) (u-v)) -
    value period (differenceRemainder period D hq t u v) -
    (D.metric.coefficient t).operator (value period (D.pressure period hq t u)-value period
        (D.pressure period hq t v))

/-- Exact vector subtraction for a bilinear evolution with two viscosities. -/
theorem vector_difference_identity {H : Type*} [AddCommGroup H] [Module ℝ H]
    (ν μ : ℝ) (a b ru rv top rem pu pv : H) (hraw : ru - rv = top + rem) :
    ν • (a-b)+(ν-μ) • b-top-rem-(pu-pv) =
      (ν • a-ru-pu)-(μ • b-rv-pv) := by
  have hr : ru=rv+(top+rem) := (sub_eq_iff_eq_add.mp hraw).trans (add_comm _ _)
  rw [hr,smul_sub,sub_smul]
  abel

/-- The exposed difference equation is exactly the subtraction of the two actual PDE right sides. -/
theorem differenceRhs_eq_sub {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (ν μ : ℝ) (t : T)
    (u v : SobolevSpace period (q + 1)) :
    differenceRhs period D hq ν μ t u v =
      (ν • laplacianEvaluation period (q+1) (by omega) u-value period (D.rawSource period hq t u) -
        (D.metric.coefficient t).operator (value period (D.pressure period hq t u))) -
      (μ • laplacianEvaluation period (q+1) (by omega) v-value period (D.rawSource period hq t v) -
        (D.metric.coefficient t).operator (value period (D.pressure period hq t v))) := by
  have hraw := congrArg (valueOperator period q) (rawSource_sub period D hq t u v)
  change value period (D.rawSource period hq t u)-value period (D.rawSource period hq t v) =
    value period (transportBilinear period hq (velocityComponents D.κ D.direction)
      (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
      (D.approximation t+u) (u-v))+value period (differenceRemainder period D hq t u v) at hraw
  have hlap := (laplacianEvaluation period (q+1) (by omega)).map_sub u v
  have hp := (D.metric.coefficient t).operator.map_sub
    (value period (D.pressure period hq t u)) (value period (D.pressure period hq t v))
  unfold differenceRhs
  rw [hlap,hp]
  exact vector_difference_identity ν μ _ _ _ _ _ _ _ _ hraw

/-- Subtracting two actual mild correction equations gives the literal transport-pressure-heat
difference equation. -/
theorem correction_difference_hasDerivAt {q : ℕ} (hq : 6 ≤ q) (ν μ : ℝ) (hν : 0 < ν) (hμ : 0 < μ)
    (T : ℝ) (hT : 0 ≤ T) (D : CorrectionData period q (Icc (0 : ℝ) T))
    (u v : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hu : ∀ t, u t = quadraticDuhamel period ν hν hT le_rfl (D.coefficients period hq) 0 u t)
    (hv : ∀ t, v t = quadraticDuhamel period μ hμ hT le_rfl (D.coefficients period hq) 0 v t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => value period (extendPath T hT u s)-value period (extendPath T hT v s))
      (differenceRhs period D hq ν μ ⟨t,ht.1.le,ht.2.le⟩ (u ⟨t,ht.1.le,ht.2.le⟩) (v
          ⟨t,ht.1.le,ht.2.le⟩)) t := by
  have hu' := correction_mild_hasDerivAt period hq ν hν hT le_rfl D u hu t ht
  have hv' := correction_mild_hasDerivAt period hq μ hμ hT le_rfl D v hv t ht
  apply (hu'.sub hv').congr_deriv
  exact (differenceRhs_eq_sub period D hq ν μ ⟨t,ht.1.le,ht.2.le⟩ _ _).symm

end EulerCorrectionDifferencePDE
