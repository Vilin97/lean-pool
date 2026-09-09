/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketParity
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarParity

@[expose] public section

/-! Even parity of the actual normalized transverse pressure from the odd solved velocity. -/

noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerPacketProfileRecursion EulerCylinderFieldReflection EulerLpCylinderTranslation
  EulerCylinderScalarPrimitive

namespace Forcing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

abbrev normalResidualField := EulerSourceCylinderClassical.normalResidual
  P D.support D.support_measurable D.support_compact D.T D.T_pos.le
  D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
  G.path_orbit I.orbit D.M D.normal

theorem normalResidualField_formula (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.normalResidualField I t (x,(θ : AddCircle P)) =
      (⟪D.normal.field t x,raw (t,(x,θ))⟫_ℝ -
        2*⟪D.normal.field t x,D.M.field t x (G.vector I (t,(x,θ)))⟫_ℝ) / ‖D.normal.field t x‖^2 :=
          by
  simp only [normalResidualField,EulerSourceCylinderClassical.normalResidual,
    vector,Data.clamp_coe,G.raw_eq]

variable (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(-x,-θ)) = -raw (t,(x,θ)))
  (hinit : reflection P (I.value : CylinderL2 P U) = -(I.value : CylinderL2 P U))

include hSym hF hM hraw hinit in
theorem normalResidualField_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.normalResidualField I t (-x,((-θ : ℝ) : AddCircle P)) =
      -G.normalResidualField I t (x,(θ : AddCircle P)) := by
  rw [G.normalResidualField_formula,G.normalResidualField_formula,
    D.normal_even hF,hM,hraw,G.vector_odd I hSym hF hM hraw hinit]
  simp only [map_neg,inner_neg_right]
  ring

include hSym hF hM hraw hinit in
theorem scalar_even (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.scalar I (t,(-x,-θ)) = G.scalar I (t,(x,θ)) := by
  unfold scalar
  simp only [Data.clamp_coe]
  exact classicalPrimitive_joint_even P (G.normalResidualField I t) _ _
    (G.normalResidualField_odd I hSym hF hM hraw hinit t) x θ

end Forcing

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (I : InitialData P D) (raw : VectorField) (h : Nonempty (Forcing P D raw))

include h in
theorem highSolve_parity (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(-x,-θ)) = -raw (t,(x,θ)))
    (hinit : reflection P (I.value : CylinderL2 P U) = -(I.value : CylinderL2 P U)) :
    (∀ (t : Icc (0 : ℝ) D.T) x θ,
      (highSolve P D I raw).1 (t,(-x,-θ)) = -(highSolve P D I raw).1 (t,(x,θ))) ∧
    (∀ (t : Icc (0 : ℝ) D.T) x θ,
      (highSolve P D I raw).2 (t,(-x,-θ)) = (highSolve P D I raw).2 (t,(x,θ))) := by
  rw [highSolve_of_admissible D I raw h]
  exact ⟨(Classical.choice h).vector_odd I hSym hF hM hraw hinit,
    (Classical.choice h).scalar_even I hSym hF hM hraw hinit⟩

end EulerTransversePacketProvider
