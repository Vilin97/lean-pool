/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedPaths
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradient
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryPressure
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketProvider
import LeanPool.NavierStokesAndEuler.Euler.CylinderSliceRepresentatives
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCylinderFields
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPressureGradient

/-!
# The complete transverse history/forward field as a genuine cylinder path

All raw fields are canonical continuous representatives of the constructed
L² paths. Restriction recovers the actual history and forward solutions.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerCylinderSmoothOrbit EulerCylinderScalarPrimitive EulerPacketProfileRecursion
  EulerTransversePacketProvider EulerPacketCylinderField EulerLpCylinderPaths
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

/-- Vector, defined pointwise by `pointField P (velocityPath τ hτ hτT B G) (velocityPath_orbit τ
hτ hτT B G) (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))`. -/
def vector : VectorField := fun z =>
  pointField P (velocityPath τ hτ hτT B G) (velocityPath_orbit τ hτ hτT B G)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))

/-- Vector derivative, defined pointwise by `pointField P (derivativePath τ hτ hτT B G)
(derivativePath_orbit τ hτ hτT B G) (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))`. -/
def vectorDerivative : VectorField := fun z =>
  pointField P (derivativePath τ hτ hτT B G) (derivativePath_orbit τ hτ hτT B G)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))

/-- Scalar, defined pointwise by `scalarPointField P (pressurePath τ hτ hτT B G)
(pressurePath_orbit τ hτ hτT B G) (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))`. -/
def scalar : ScalarField := fun z =>
  scalarPointField P (pressurePath τ hτ hτT B G) (pressurePath_orbit τ hτ hτT B G)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))

/-- Vector field, bundling `path`, `orbit`, `raw_eq`. -/
def vectorField : Field P D.T (vector τ hτ hτT B G) where
  path := velocityPath τ hτ hτT B G
  orbit := velocityPath_orbit τ hτ hτT B G
  raw_eq t x θ := by simp only [vector,Data.clamp_coe]

/-- Vector derivative field, bundling `path`, `orbit`, `raw_eq`. -/
def vectorDerivativeField : Field P D.T (vectorDerivative τ hτ hτT B G) where
  path := derivativePath τ hτ hτT B G
  orbit := derivativePath_orbit τ hτ hτT B G
  raw_eq t x θ := by simp only [vectorDerivative,Data.clamp_coe]

theorem vectorField_time : TimeDerivative D.T_pos.le (vectorField τ hτ hτT B G)
    (vectorDerivativeField τ hτ hτT B G) := velocityPath_time τ hτ hτT B G

theorem vector_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivWithinAt (fun s => vector τ hτ hτT B G (s,(x,θ)))
      (vectorDerivative τ hτ hτT B G (t,(x,θ))) (Icc (0 : ℝ) D.T) t :=
  (vectorField τ hτ hτT B G).raw_hasDerivWithinAt D.T_pos.le
    (vectorDerivativeField τ hτ hτT B G) (vectorField_time τ hτ hτT B G) t x θ

theorem scalar_eq_pointField (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    scalar τ hτ hτT B G (t,(x,θ)) =
      scalarPointField P (pressurePath τ hτ hτT B G) (pressurePath_orbit τ hτ hτT B G)
        t (x,(θ : AddCircle P)) := by simp only [scalar,Data.clamp_coe]

/-- Scalar gradient field, constructed using `EulerPacketCylinderField.scalarGradientField`. -/
def scalarGradientField : Field P D.T (pressureGradient (scalar τ hτ hτT B G)) :=
  EulerPacketCylinderField.scalarGradientField (scalar τ hτ hτT B G)
    (pressurePath τ hτ hτT B G) (pressurePath_orbit τ hτ hτT B G)
    (scalar_eq_pointField τ hτ hτT B G)

theorem vector_left (t : Icc (0 : ℝ) τ) (x : Space) (θ : ℝ) :
    vector τ hτ hτT B G (t,(x,θ)) =
      B.field (G.initial τ hτ hτT.le) t (x,(θ : AddCircle P)) := by
  let tg : Icc (0 : ℝ) D.T := ⟨t,t.property.1,t.property.2.trans hτT.le⟩
  have he := congrFun (pointField_eq_of_slice_eq P (velocityPath τ hτ hτT B G)
    (pastVelocity τ hτ hτT B G) (velocityPath_orbit τ hτ hτT B G)
    (pastVelocity_orbit τ hτ hτT B G) tg t (velocityPath_left τ hτ hτT B G t)) (x,(θ : AddCircle P))
  change pointField P (velocityPath τ hτ hτT B G) _ (D.clamp tg) _ = _
  rw [Data.clamp_coe]
  exact he

theorem vectorDerivative_left (t : Icc (0 : ℝ) τ) (x : Space) (θ : ℝ) :
    vectorDerivative τ hτ hτT B G (t,(x,θ)) =
      B.derivativeField (G.initial τ hτ hτT.le) t (x,(θ : AddCircle P)) := by
  let tg : Icc (0 : ℝ) D.T := ⟨t,t.property.1,t.property.2.trans hτT.le⟩
  have he := congrFun (pointField_eq_of_slice_eq P (derivativePath τ hτ hτT B G)
    (pastDerivative τ hτ hτT B G) (derivativePath_orbit τ hτ hτT B G)
    (pastDerivative_orbit τ hτ hτT B G) tg t (derivativePath_left τ hτ hτT B G t)) (x,(θ :
        AddCircle P))
  change pointField P (derivativePath τ hτ hτT B G) _ (D.clamp tg) _ = _
  rw [Data.clamp_coe]
  exact he

theorem scalar_left (t : Icc (0 : ℝ) τ) (x : Space) (θ : ℝ) :
    scalar τ hτ hτT B G (t,(x,θ)) =
      B.pressureField (G.initial τ hτ hτT.le) t (x,(θ : AddCircle P)) := by
  let tg : Icc (0 : ℝ) D.T := ⟨t,t.property.1,t.property.2.trans hτT.le⟩
  have he := congrFun (scalarPointField_eq_of_slice_eq P (pressurePath τ hτ hτT B G)
    (pastPressure τ hτ hτT B G) (pressurePath_orbit τ hτ hτT B G)
    (pastPressure_orbit τ hτ hτT B G) tg t (pressurePath_left τ hτ hτT B G t)) (x,(θ : AddCircle P))
  change scalarPointField P (pressurePath τ hτ hτT B G) _ (D.clamp tg) _ = _
  rw [Data.clamp_coe]
  exact he.trans (congrFun (B.pressureField_eq_scalarPointField
    (G.initial τ hτ hτT.le) t) (x,(θ : AddCircle P))).symm

theorem vector_right (t : Icc τ D.T) (x : Space) (θ : ℝ) :
    vector τ hτ hτT B G (t,(x,θ)) =
      (G.tail τ hτ.le hτT).vector (forwardInitial τ hτ hτT B G) ((t : ℝ)-τ,(x,θ)) := by
  let tg : Icc (0 : ℝ) D.T := ⟨t,hτ.le.trans t.property.1,t.property.2⟩
  let tf : Icc (0 : ℝ) (D.T-τ) := ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right
      t.property.2 τ⟩
  have he := congrFun (pointField_eq_of_slice_eq P (velocityPath τ hτ hτT B G)
    (futureVelocity τ hτ hτT B G) (velocityPath_orbit τ hτ hτT B G)
    (futureVelocity_orbit τ hτ hτT B G) tg tf (velocityPath_right τ hτ hτT B G t)) (x,(θ :
        AddCircle P))
  change pointField P (velocityPath τ hτ hτT B G) _ (D.clamp tg) _ = _
  rw [Data.clamp_coe]
  exact he.trans (((G.tail τ hτ.le hτT).vectorField (forwardInitial τ hτ hτT B G)).raw_eq tf x
      θ).symm

theorem vectorDerivative_right (t : Icc τ D.T) (x : Space) (θ : ℝ) :
    vectorDerivative τ hτ hτT B G (t,(x,θ)) =
      (G.tail τ hτ.le hτT).vectorDerivative (forwardInitial τ hτ hτT B G) ((t : ℝ)-τ,(x,θ)) := by
  let tg : Icc (0 : ℝ) D.T := ⟨t,hτ.le.trans t.property.1,t.property.2⟩
  let tf : Icc (0 : ℝ) (D.T-τ) := ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right
      t.property.2 τ⟩
  have he := congrFun (pointField_eq_of_slice_eq P (derivativePath τ hτ hτT B G)
    (futureDerivative τ hτ hτT B G) (derivativePath_orbit τ hτ hτT B G)
    (futureDerivative_orbit τ hτ hτT B G) tg tf (derivativePath_right τ hτ hτT B G t)) (x,(θ :
        AddCircle P))
  change pointField P (derivativePath τ hτ hτT B G) _ (D.clamp tg) _ = _
  rw [Data.clamp_coe]
  exact he.trans (((G.tail τ hτ.le hτT).vectorDerivativeField (forwardInitial τ hτ hτT B G)).raw_eq
      tf x θ).symm

theorem scalar_right (t : Icc τ D.T) (x : Space) (θ : ℝ) :
    scalar τ hτ hτT B G (t,(x,θ)) =
      (G.tail τ hτ.le hτT).scalar (forwardInitial τ hτ hτT B G) ((t : ℝ)-τ,(x,θ)) := by
  let tg : Icc (0 : ℝ) D.T := ⟨t,hτ.le.trans t.property.1,t.property.2⟩
  let tf : Icc (0 : ℝ) (D.T-τ) := ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right
      t.property.2 τ⟩
  have he := congrFun (scalarPointField_eq_of_slice_eq P (pressurePath τ hτ hτT B G)
    (futurePressure τ hτ hτT B G) (pressurePath_orbit τ hτ hτT B G)
    (futurePressure_orbit τ hτ hτT B G) tg tf (pressurePath_right τ hτ hτT B G t)) (x,(θ :
        AddCircle P))
  change scalarPointField P (pressurePath τ hτ hτT B G) _ (D.clamp tg) _ = _
  rw [Data.clamp_coe]
  exact he.trans ((G.tail τ hτ.le hτT).scalar_eq_pointField (forwardInitial τ hτ hτT B G) tf x
      θ).symm

end EulerTransversePacketJoin
