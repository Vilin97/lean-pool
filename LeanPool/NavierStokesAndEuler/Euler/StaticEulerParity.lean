/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.StaticEulerSolution
import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftFieldDecomposition
import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyPressureParity
import LeanPool.NavierStokesAndEuler.Euler.SmallCorrectionParity

/-! Odd initial velocity produces the actual odd local Euler velocity
and odd pressure force. The scalar pressure, normalized at the origin,
is even. These are consequences of correction uniqueness. -/

@[expose] public section


noncomputable section

namespace EulerStaticEuler

open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerPacketCylinderField EulerCorrectionAssembly EulerMetricTransport
  EulerCanonicalGraphPotential EulerGraphPressurePotential

variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)
  (hodd : ∀ x, u.field (-x) = -u.field x)

include hodd

theorem symmetry : ParityData P (inputData P u C R hC hR) :=
  EulerSmallCorrection.parityData (EulerStaticCylinder.field P 1 u)
    (fun _ x _ => hodd x) (amplitude P C R hC hR)

theorem exactPacket_odd (t : Icc (0 : ℝ) 1) :
    -EulerCylinderReflection.reflection P ((exactPacket P u C R hC hR hu hdiv).velocity.field t) =
      (exactPacket P u C R hC hR hu hdiv).velocity.field t :=
  exactPacketOfResidual_velocity_odd P (correctionBudget P u C R hC hR hu hdiv)
    _ (symmetry P u C R hC hR hodd) t

theorem unit_velocity_odd (t : ℝ) (x : Space) :
    EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv) (t,-x) =
      -EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv) (t,x) := by
  let s := projIcc 0 1 zero_le_one t
  have h := continuous_representative_odd P
    ((exactPacket P u C R hC hR hu hdiv).velocity.field s)
    ((exactPacket P u C R hC hR hu hdiv).velocity.pointField s)
    (exactPacket_odd P u C R hC hR hu hdiv hodd s)
    (smoothField_continuous P _ ((exactPacket P u C R hC hR hu hdiv).velocity.pointField_smooth s))
    ((exactPacket P u C R hC hR hu hdiv).velocity.pointField_ae s) (x,(0 : AddCircle P))
  simpa only [Prod.neg_mk,neg_zero,EulerConstantEuler.velocity,ExactLiftedPacket.rawVelocity,
    FieldTower.rawField,coveringMap,AddCircle.coe_zero] using h

omit hodd in
theorem unit_pressure_point (t : Icc (0 : ℝ) 1) (x : LiftDomain P) :
    (exactPacket P u C R hC hR hu hdiv).pressure.pointField t x =
      (correctionBudget P u C R hC hR hu hdiv).pointPressure P t x := by
  erw [exactPacket,exactPacketOfResidual_pressure_pointField]
  have hz : (Field.zero P 1).toFieldTower.pointField t x=0 := by
    change EulerSobolevPointEvaluation.pointEvaluation P x
      ((Field.zero P 1).toFieldTower.realization 3 t)=0
    rw [EulerSmallCorrection.zero_tower,map_zero]
  change (Field.zero P 1).toFieldTower.pointField t x+_=_
  rw [hz,zero_add]

theorem unit_force_odd (t : ℝ) (x : Space) :
    EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) (t,-x) =
      -EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) (t,x) := by
  change (exactPacket P u C R hC hR hu hdiv).pressure.pointField
      (projIcc 0 1 zero_le_one t) (-x,0) =
    -(exactPacket P u C R hC hR hu hdiv).pressure.pointField (projIcc 0 1 zero_le_one t) (x,0)
  rw [unit_pressure_point,unit_pressure_point]
  have h := (correctionBudget P u C R hC hR hu hdiv).pointPressure_odd P
    (symmetry P u C R hC hR hodd) (projIcc 0 1 zero_le_one t) (x,0)
  simpa only [Prod.neg_mk,neg_zero] using h

theorem unit_pressure_even (t : ℝ) (x : Space) :
    EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv) (t,-x) =
      EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv) (t,x) := by
  have h := radialPotential_even
    (fun y => EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) (t,y))
    (unit_force_odd P u C R hC hR hu hdiv hodd t) x
  change radialPotential ((exactPacket P u C R hC hR hu hdiv).graphPressure 1
      (projIcc 0 1 zero_le_one t)) (-x) =
    radialPotential ((exactPacket P u C R hC hR hu hdiv).graphPressure 1
      (projIcc 0 1 zero_le_one t)) x
  have he : (exactPacket P u C R hC hR hu hdiv).graphPressure 1
      (projIcc 0 1 zero_le_one t) =
      fun y => EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) (t,y) := by
    funext y
    simp only [ExactLiftedPacket.graphPressure,EulerConstantEuler.force,
      ExactLiftedPacket.rawPressure,FieldTower.rawField,cylinderGraph,coveringMap,
      inputData,EulerSmallCorrection.input,EulerConstantCorrection.data,
      one_smul,inner_zero_left,mul_zero]
  rw [he]
  exact h

theorem localVelocity_odd (t : ℝ) (x : Space) :
    localVelocity P u C R hC hR hu hdiv (t,-x)= -localVelocity P u C R hC hR hu hdiv (t,x) := by
  unfold localVelocity EulerTimeRescaling.velocity
  rw [EulerTimeRescaling.coordinates_apply,EulerTimeRescaling.coordinates_apply,
    unit_velocity_odd P u C R hC hR hu hdiv hodd,smul_neg]

theorem localPressure_even (t : ℝ) (x : Space) :
    localPressure P u C R hC hR hu hdiv (t,-x)=localPressure P u C R hC hR hu hdiv (t,x) := by
  unfold localPressure EulerTimeRescaling.pressure
  rw [EulerTimeRescaling.coordinates_apply,EulerTimeRescaling.coordinates_apply,
    unit_pressure_even P u C R hC hR hu hdiv hodd]

end EulerStaticEuler
