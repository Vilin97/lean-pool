/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCorrectionCoefficients
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderFullTime

/-! The time derivative of the actual inverse pressure metric, first as
a bounded matrix field and then as its cylinder L² multiplier. -/

@[expose] public section


noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set ContinuousLinearMap EulerSmoothLimit EulerPacketPointJets
  EulerPacketCylinderField EulerLpCylinderRectangular EulerLiftedGradientSpace
  EulerVolterraConvolution EulerTransverseGramPath EulerMeanCoefficients
open scoped BoundedContinuousFunction

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCorrectionMetricTime1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCorrectionMetricTime2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCorrectionMetricTime3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCorrectionMetricTime4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)

/-- Raw inverse metric time, given by `(rawFrameTime D z).adjoint.comp (rawFrame D z) +
(rawFrame D z).adjoint.comp (rawFrameTime D z)`. -/
def rawInverseMetricTime (z : Domain) : Space →L[ℝ] Space :=
  (rawFrameTime D z).adjoint.comp (rawFrame D z) +
    (rawFrame D z).adjoint.comp (rawFrameTime D z)

/-- Inverse metric time coefficient, given by `((frameTimeCoefficient D).adjoint.comp
(frameCoefficient D)).add ((frameCoefficient D).adjoint.comp (frameTimeCoefficient D))`. -/
def inverseMetricTimeCoefficient : MatrixCoefficient D.T (rawInverseMetricTime D) :=
  ((frameTimeCoefficient D).adjoint.comp (frameCoefficient D)).add
    ((frameCoefficient D).adjoint.comp (frameTimeCoefficient D))

@[simp] theorem inverseMetricTimeCoefficient_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (inverseMetricTimeCoefficient D).path t x =
      (D.F₁.field t x).adjoint.comp (D.F.field t x) +
        (D.F.field t x).adjoint.comp (D.F₁.field t x) := rfl

theorem inverseMetric_field_hasDerivWithinAt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T)
    (x : Space) :
    HasDerivWithinAt (fun s => extendPath D.T D.T_pos.le (inverseMetricCoefficient D).path s x)
      (extendPath D.T D.T_pos.le (inverseMetricTimeCoefficient D).path t x)
      (Icc (0 : ℝ) D.T) t := by
  have h := hasDerivWithinAt_gram
    (fun s => extendPath D.T D.T_pos.le D.F.field s x)
    (extendPath D.T D.T_pos.le D.F₁.field t x)
    (Icc (0 : ℝ) D.T) t (D.frame_time t ht x)
  have hvalue : (fun s => extendPath D.T D.T_pos.le (inverseMetricCoefficient D).path s x) =
      fun s => (extendPath D.T D.T_pos.le D.F.field s x).adjoint.comp
        (extendPath D.T D.T_pos.le D.F.field s x) := by
    funext s
    exact inverseMetricCoefficient_apply D (projIcc 0 D.T D.T_pos.le s) x
  have hderivative : extendPath D.T D.T_pos.le (inverseMetricTimeCoefficient D).path t x =
      (extendPath D.T D.T_pos.le D.F₁.field t x).adjoint.comp
          (extendPath D.T D.T_pos.le D.F.field t x) +
        (extendPath D.T D.T_pos.le D.F.field t x).adjoint.comp
          (extendPath D.T D.T_pos.le D.F₁.field t x) :=
    inverseMetricTimeCoefficient_apply D (projIcc 0 D.T D.T_pos.le t) x
  rw [hvalue,hderivative]
  exact h

variable (P : ℝ) [Fact (0 < P)]

/-- Inverse metric derivative path, given by `fullPathMap P (inverseMetricTimeCoefficient
D).path`. -/
def inverseMetricDerivativePath : C(Icc (0 : ℝ) D.T,LiftL2 P →L[ℝ] LiftL2 P) :=
  fullPathMap P (inverseMetricTimeCoefficient D).path

theorem inverseMetric_operator_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le
      (fullPathMap P (inverseMetricCoefficient D).path))
      (inverseMetricDerivativePath D P t) (Icc (0 : ℝ) D.T) t :=
  fullPath_hasDerivWithinAt P D.T D.T_pos.le (inverseMetricCoefficient D).path
    (inverseMetricTimeCoefficient D).path (inverseMetric_field_hasDerivWithinAt D) t

theorem inverseMetricDerivativePath_norm (t : Icc (0 : ℝ) D.T) :
    ‖inverseMetricDerivativePath D P t‖ ≤ ‖(inverseMetricTimeCoefficient D).path‖ := by
  exact ((fullOperatorMap (E := Space) (F := Space) P).le_opNorm ((inverseMetricTimeCoefficient
      D).path t)).trans
    ((mul_le_mul_of_nonneg_right (fullOperatorMap_norm (E := Space) (F := Space) P)
      (norm_nonneg ((inverseMetricTimeCoefficient D).path t))).trans
        (by simpa only [one_mul] using (inverseMetricTimeCoefficient D).path.norm_coe_le_norm t))

end EulerPacketCorrectionCoefficients
