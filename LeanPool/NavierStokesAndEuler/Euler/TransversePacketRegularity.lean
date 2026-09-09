/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketProvider

@[expose] public section

/-! Joint continuity and actual spatial support of the concrete forward packet fields. -/

noncomputable section

namespace EulerTransversePacketProvider

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerCylinderSmoothOrbit EulerSourceCylinderClassical
  EulerPacketProfileRecursion EulerMetricTransport

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

namespace Forcing

variable {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

omit [Fact (0 < P)] [CompleteSpace U] in
private theorem continuous_cover :
    Continuous (fun z : Icc (0 : ℝ) D.T × (Space × ℝ) => (z.1,(z.2.1,(z.2.2 : AddCircle P)))) :=
  continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
    ((AddCircle.continuous_mk' P).comp (continuous_snd.comp continuous_snd)))

theorem vector_joint_continuous :
    Continuous (fun z : Icc (0 : ℝ) D.T × (Space × ℝ) => G.vector I (z.1,z.2)) := by
  have h := (field_joint_continuous P D.support D.support_measurable D.support_compact
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    G.path I.value G.path_orbit I.orbit).comp (continuous_cover (P := P) (D := D))
  simpa only [vector,Data.clamp_coe,Function.comp_def] using h

theorem scalar_joint_continuous :
    Continuous (fun z : Icc (0 : ℝ) D.T × (Space × ℝ) => G.scalar I (z.1,z.2)) := by
  have h := (pressureField_joint_continuous P D.support D.support_measurable D.support_compact
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    G.path I.value G.path_orbit I.orbit D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    G.mean_zero I.mean_zero).comp (continuous_cover (P := P) (D := D))
  simpa only [scalar,Data.clamp_coe,Function.comp_def] using h

theorem vectorDerivative_joint_continuous :
    Continuous (fun z : Icc (0 : ℝ) D.T × (Space × ℝ) => G.vectorDerivative I (z.1,z.2)) := by
  have h := (pointField_joint_continuous P
    (includePath P D.support D.support_measurable (G.derivativePath I))
    (G.derivativePath_orbit I)).comp (continuous_cover (P := P) (D := D))
  simpa only [vectorDerivative,derivativeField,Data.clamp_coe,Function.comp_def] using h

theorem vectorDerivative_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    G.vectorDerivative I (t,(x,θ)) = 0 := by
  change pointField P (includePath P D.support D.support_measurable (G.derivativePath I))
    (G.derivativePath_orbit I) (D.clamp t) (x,(θ : AddCircle P)) = 0
  rw [pointField_eq_representative]
  exact representative_zero_outside P D.support D.support_measurable D.support_compact.isClosed
    _ _ (G.derivativePath I (D.clamp t)).property (x,(θ : AddCircle P)) hx

theorem vector_support (t θ : ℝ) :
    tsupport (fun x : Space => G.vector I (t,(x,θ))) ⊆ D.support := by
  apply closure_minimal _ D.support_compact.isClosed
  intro x hx
  by_contra hn
  exact hx (G.vector_zero_outside I t x hn θ)

theorem scalar_support (t θ : ℝ) :
    tsupport (fun x : Space => G.scalar I (t,(x,θ))) ⊆ D.support := by
  apply closure_minimal _ D.support_compact.isClosed
  intro x hx
  by_contra hn
  exact hx (G.scalar_zero_outside I t x hn θ)

theorem vector_compact (t θ : ℝ) : HasCompactSupport (fun x : Space => G.vector I (t,(x,θ))) :=
  D.support_compact.of_isClosed_subset (isClosed_tsupport _) (G.vector_support I t θ)

theorem scalar_compact (t θ : ℝ) : HasCompactSupport (fun x : Space => G.scalar I (t,(x,θ))) :=
  D.support_compact.of_isClosed_subset (isClosed_tsupport _) (G.scalar_support I t θ)

end Forcing

end EulerTransversePacketProvider
