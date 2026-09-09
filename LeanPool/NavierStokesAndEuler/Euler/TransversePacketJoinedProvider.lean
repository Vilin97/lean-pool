/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedParity
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedEquation
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedPressure
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHomogeneity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique

@[expose] public section

/-!
# Total raw-field provider for a positive history time

Every admissible input is sent to the constructed history/forward solution.
Its raw PDE, tangent constraint, parity, actual Field witnesses, true time
derivative, pressure gradient and literal curl corrector are all exported.
-/

noncomputable section

namespace EulerTransversePacketProvider.Forcing

open EulerLpCylinderPaths

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} {raw : EulerPacketProfileRecursion.VectorField}

/-- The genuine cylinder forcing path is determined by its prescribed raw field. -/
theorem path_unique (G H : Forcing P D raw) : G.path = H.path := by
  have he := G.forcingField.path_eq_of_same_raw H.forcingField
  have hp := congrArg (projectPath P D.support D.support_measurable) he
  simpa only [forcingField,project_include] using hp

end EulerTransversePacketProvider.Forcing

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit
  EulerPacketProfileRecursion EulerTransversePacketProvider EulerTimeIntervalRestriction
  EulerPacketCylinderField EulerSourceNormalResidualBounds EulerPacketPointJets

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G H : Forcing P D raw)

theorem vector_independent_of_witness : vector τ hτ hτT B G = vector τ hτ hτT B H := by
  have hv : velocityPath τ hτ hτT B G = velocityPath τ hτ hτT B H := by
    simpa only [one_smul] using velocityPath_eq_smul τ hτ hτT B H G 1
      (by simpa only [one_smul] using G.path_unique H)
  funext z
  exact congrFun (pointField_eq_of_slice_eq P _ _ (velocityPath_orbit τ hτ hτT B G)
    (velocityPath_orbit τ hτ hτT B H) (D.clamp z.1) (D.clamp z.1)
    (congrArg (fun p => p (D.clamp z.1)) hv)) (z.2.1,(z.2.2 : AddCircle P))

theorem scalar_independent_of_witness : scalar τ hτ hτT B G = scalar τ hτ hτT B H := by
  have hv : velocityPath τ hτ hτT B G = velocityPath τ hτ hτT B H := by
    simpa only [one_smul] using velocityPath_eq_smul τ hτ hτT B H G 1
      (by simpa only [one_smul] using G.path_unique H)
  have hp : pressurePath τ hτ hτT B G = pressurePath τ hτ hτT B H := by
    rw [pressurePath_eq_source,pressurePath_eq_source,hv]
    exact congrArg (fun p => sourcePressure P D.M D.normal D.normalLower D.normalLower_pos
      D.normal_lower
      (includePath P D.support D.support_measurable p) (velocityPath τ hτ hτT B H)) (G.path_unique
        H)
  funext z
  exact congrFun (scalarPointField_eq_of_slice_eq P _ _ (pressurePath_orbit τ hτ hτT B G)
    (pressurePath_orbit τ hτ hτT B H) (D.clamp z.1) (D.clamp z.1)
    (congrArg (fun p => p (D.clamp z.1)) hp)) (z.2.1,(z.2.2 : AddCircle P))

theorem vector_tangent (t : Set.Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    ⟪D.normalField (t,(x,θ)),vector τ hτ hτT B G (t,(x,θ))⟫_ℝ = 0 := by
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    rw [vector_left τ hτ hτT B G th x θ]
    simp only [Data.normalField,Data.clamp_coe]
    change ⟪(D.initial τ hτ hτT.le).normal.field th x,
      B.field (G.initial τ hτ hτT.le) th (x,(θ : AddCircle P))⟫_ℝ = 0
    exact B.field_tangent (G.initial τ hτ hτT.le) th (x,(θ : AddCircle P))
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    let tf : Icc (0 : ℝ) (D.tail τ hτ.le hτT).T :=
      ⟨(t : ℝ)-τ,sub_nonneg.mpr tr.property.1,sub_le_sub_right t.property.2 τ⟩
    have he : tailInclusion D.T τ hτ.le tf = t := by
      apply Subtype.ext
      change τ+((t : ℝ)-τ) = t
      ring
    have hm : (D.tail τ hτ.le hτT).normalField (tf,(x,θ)) = D.normalField (t,(x,θ)) := by
      simp only [Data.normalField,Data.clamp_coe]
      change D.normal.field (tailInclusion D.T τ hτ.le tf) x = _
      rw [he]
    rw [vector_right τ hτ hτT B G tr x θ,← hm]
    exact (G.tail τ hτ.le hτT).vector_tangent (forwardInitial τ hτ hτT B G) tf x θ

/-- The total high operator, backed by the unique genuine solution on admissible inputs. -/
def highSolve (raw : VectorField) : VectorField × ScalarField := by
  classical
  exact if h : Nonempty (Forcing P D raw) then
    (vector τ hτ hτT B (Classical.choice h),scalar τ hτ hτT B (Classical.choice h))
  else (0,0)

theorem highSolve_of_admissible (h : Nonempty (Forcing P D raw)) :
    highSolve (P := P) τ hτ hτT B raw =
      (vector τ hτ hτT B (Classical.choice h),scalar τ hτ hτT B (Classical.choice h)) := by
  simp only [highSolve,dite_eq_left h]

theorem highSolve_eq : highSolve (P := P) τ hτ hτT B raw =
    (vector τ hτ hτT B G,scalar τ hτ hτT B G) := by
  rw [highSolve_of_admissible τ hτ hτT B ⟨G⟩]
  exact Prod.ext (vector_independent_of_witness τ hτ hτT B _ G)
    (scalar_independent_of_witness τ hτ hτT B _ G)

variable (h : Nonempty (Forcing P D raw))

def highVectorField : Field P D.T (highSolve (P := P) τ hτ hτT B raw).1 :=
  (vectorField τ hτ hτT B (Classical.choice h)).congr (fun t x θ => by
    rw [highSolve_of_admissible τ hτ hτT B h])

def highDerivativeField : Field P D.T (vectorDerivative τ hτ hτT B (Classical.choice h)) :=
  vectorDerivativeField τ hτ hτT B (Classical.choice h)

theorem highVectorField_time : TimeDerivative D.T_pos.le
    (highVectorField τ hτ hτT B h) (highDerivativeField τ hτ hτT B h) :=
  vectorField_time τ hτ hτT B (Classical.choice h)

def highPressureGradientField : Field P D.T (pressureGradient (highSolve (P := P) τ hτ hτT B
  raw).2) :=
  (scalarGradientField τ hτ hτT B (Classical.choice h)).congr (fun t x θ => by
    rw [highSolve_of_admissible τ hτ hτT B h])

def highCorrectorField : Field P D.T (D.curlCorrector P (highSolve (P := P) τ hτ hτT B raw).1) where
  path := correctorPath τ hτ hτT B (Classical.choice h)
  orbit := correctorPath_orbit τ hτ hτT B (Classical.choice h)
  raw_eq t x θ := by
    rw [highSolve_of_admissible τ hτ hτT B h]
    exact (correctorField τ hτ hτT B (Classical.choice h)).raw_eq t x θ

def highCorrectorDerivativeField : Field P D.T (correctorDerivative τ hτ hτT B (Classical.choice
  h)) where
  path := correctorTimePath τ hτ hτT B (Classical.choice h)
  orbit := correctorTimePath_orbit τ hτ hτT B (Classical.choice h)
  raw_eq t x θ := (correctorDerivativeField τ hτ hτT B (Classical.choice h)).raw_eq t x θ

theorem highCorrectorField_time : TimeDerivative D.T_pos.le
    (highCorrectorField τ hτ hτT B h) (highCorrectorDerivativeField τ hτ hτT B h) := by
  intro t
  exact correctorPath_time τ hτ hτT B (Classical.choice h) t

include h in
theorem highSolve_equation (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    linearPart (D.strain (t,(x,θ)))
        (slicedJet (Icc (0 : ℝ) D.T) (highSolve (P := P) τ hτ hτT B raw).1 (t,(x,θ)))+
      fastPressure (D.normalField (t,(x,θ)))
        (pressureJet (highSolve (P := P) τ hτ hτT B raw).2 (t,(x,θ))) = raw (t,(x,θ)) := by
  rw [highSolve_of_admissible τ hτ hτT B h]
  exact jet_equation τ hτ hτT B (Classical.choice h) t x θ

include h in
theorem highSolve_parity
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
    (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(-x,-θ)) = -raw (t,(x,θ))) :
    (∀ (t : Icc (0 : ℝ) D.T) x θ, (highSolve (P := P) τ hτ hτT B raw).1 (t,(-x,-θ)) =
      -(highSolve (P := P) τ hτ hτT B raw).1 (t,(x,θ))) ∧
    (∀ (t : Icc (0 : ℝ) D.T) x θ, (highSolve (P := P) τ hτ hτT B raw).2 (t,(-x,-θ)) =
      (highSolve (P := P) τ hτ hτT B raw).2 (t,(x,θ))) := by
  rw [highSolve_of_admissible τ hτ hτT B h]
  exact ⟨vector_odd τ hτ hτT B (Classical.choice h) hSym hF hM hH hraw,
    scalar_even τ hτ hτT B (Classical.choice h) hSym hF hM hH hraw⟩

end EulerTransversePacketJoin
