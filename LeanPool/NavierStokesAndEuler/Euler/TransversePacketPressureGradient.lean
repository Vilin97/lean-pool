/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradient
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketProvider
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureField
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarTime

/-! The actual normalized transverse pressure supplies the literal next-grade pressure gradient. -/

section

/-! The literal pressure integral is the genuine jointly continuous scalar path representative. -/

@[expose] public section

noncomputable section

namespace EulerSourceCylinderClassical

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerSourceCylinderEquation EulerCylinderScalarPrimitive EulerCylinderAngleAverage
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (hSc : IsCompact S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported P Space S hS)) (a₀ : Supported P U S hS)
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (includePath P S hS f)))
  (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a (a₀ : CylinderL2 P U)))
  (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖ ^ 2)
  (hf₀ : ∀ t, average P (f t : CylinderL2 P Space) = 0)
  (ha₀zero : average P (a₀ : CylinderL2 P U) = 0)

theorem pressureField_eq_pointField (t : Icc (0 : ℝ) T) :
    pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t =
      scalarPointField P (pressurePath P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm)
        (pressurePath_contDiff P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm hSc hf ha₀) t :=
  (scalarPointField_eq P _ _ t _
    (pressureField_continuous P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t)
    (pressureField_ae P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t)).symm

theorem pressureField_joint_continuous :
    Continuous (fun z : Icc (0 : ℝ) T × LiftDomain P =>
      pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero z.1 z.2) :=
          by
  simp_rw [pressureField_eq_pointField]
  exact scalarPointField_joint_continuous P _ _

end EulerSourceCylinderClassical

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderScalarPrimitive
  EulerPacketProfileRecursion EulerPacketCylinderField

namespace Forcing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

theorem scalar_eq_pointField (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.scalar I (t,(x,θ)) =
      scalarPointField P (G.pressurePath I) (G.pressurePath_orbit I) t (x,(θ : AddCircle P)) := by
  simpa only [scalar,Data.clamp_coe] using congrFun
    (EulerSourceCylinderClassical.pressureField_eq_pointField P D.support D.support_measurable
      D.support_compact D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos
      D.frame_lower G.path I.value G.path_orbit I.orbit D.M D.normal D.normalLower
      D.normalLower_pos D.normal_lower G.mean_zero I.mean_zero t) (x,(θ : AddCircle P))

/-- The next known-force pressure term comes from the constructed scalar pressure itself. -/
def scalarGradientField : Field P D.T (pressureGradient (G.scalar I)) :=
  EulerPacketCylinderField.scalarGradientField (G.scalar I) (G.pressurePath I)
    (G.pressurePath_orbit I) (G.scalar_eq_pointField I)

end Forcing

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (I : InitialData P D) (raw : VectorField)
  (h : Nonempty (Forcing P D raw))

/-- The total high operator has the required pressure-gradient witness on admissible forcing. -/
def highSolvePressureGradientField : Field P D.T (pressureGradient (highSolve P D I raw).2) :=
  ((Classical.choice h).scalarGradientField I).congr (fun _ _ _ => by
    rw [highSolve_of_admissible D I raw h])

end EulerTransversePacketProvider
