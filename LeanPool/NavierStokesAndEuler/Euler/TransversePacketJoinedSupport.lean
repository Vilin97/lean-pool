/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedField
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketRegularity

@[expose] public section

/-! Actual support and angular normalization of the joined transverse provider. -/

noncomputable section

namespace EulerElapsedTimePathGluing

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem join_mem (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : C(Icc (0 : ℝ) τ,E)) (v : C(Icc (0 : ℝ) (S-τ),E))
    (hm : u ⟨τ,hτ0,le_rfl⟩ = v ⟨0,le_rfl,sub_nonneg.mpr hτS⟩)
    (J : Set E) (hu : ∀ t, u t ∈ J) (hv : ∀ t, v t ∈ J) (t : Icc (0 : ℝ) S) :
    join S τ hτ0 hτS u v hm t ∈ J := by
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    have he : join S τ hτ0 hτS u v hm t = u th := join_left S τ hτ0 hτS u v hm th
    rw [he]
    exact hu th
  · let tr : Icc τ S := ⟨t,(not_le.mp ht).le,t.property.2⟩
    have he := join_right S τ hτ0 hτS u v hm tr
    change join S τ hτ0 hτS u v hm t = _ at he
    rw [he]
    exact hv _

end EulerElapsedTimePathGluing

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerCylinderSmoothOrbit EulerCylinderScalarPrimitive EulerPacketProfileRecursion
  EulerTransversePacketProvider EulerPacketCylinderField EulerLpCylinderPaths
  EulerElapsedTimePathGluing EulerCylinderAngleAverage
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

theorem velocityPath_supported (t : Icc (0 : ℝ) D.T) :
    velocityPath τ hτ hτT B G t ∈ Supported P Space D.support D.support_measurable :=
  join_mem D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B G) _
    (B.velocityPath_supported (G.initial τ hτ hτT.le))
    (fun s => ((G.tail τ hτ.le hτT).velocityPath (forwardInitial τ hτ hτT B G) s).property) t

theorem derivativePath_supported (t : Icc (0 : ℝ) D.T) :
    derivativePath τ hτ hτT B G t ∈ Supported P Space D.support D.support_measurable :=
  join_mem D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B G) _
    (B.derivativePath_supported (G.initial τ hτ hτT.le))
    (fun s => ((G.tail τ hτ.le hτT).derivativePath (forwardInitial τ hτ hτT B G) s).property) t

theorem velocityPath_mean_zero (t : Icc (0 : ℝ) D.T) : average P (velocityPath τ hτ hτT B G t) = 0
  := by
  apply join_mem D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B G)
    {u | average P u = 0} _ _ t
  · exact B.velocityPath_mean_zero (G.initial τ hτ hτT.le)
  · intro s
    exact EulerSourceCylinderEquation.velocity_average_zero P D.support D.support_measurable
      (D.T-τ) (sub_pos.mpr hτT).le (D.tail τ hτ.le hτT).frame (D.tail τ hτ.le hτT).frameDerivative
      (D.tail τ hτ.le hτT).frameLower (D.tail τ hτ.le hτT).frameLower_pos (D.tail τ hτ.le
        hτT).frame_lower
      (G.tail τ hτ.le hτT).path (forwardInitial τ hτ hτT B G).value
      (G.tail τ hτ.le hτT).mean_zero (forwardInitial τ hτ hτT B G).mean_zero s

theorem vector_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    vector τ hτ hτT B G (t,(x,θ)) = 0 := by
  change pointField P (velocityPath τ hτ hτT B G) (velocityPath_orbit τ hτ hτT B G)
    (D.clamp t) (x,(θ : AddCircle P)) = 0
  rw [pointField_eq_representative]
  exact representative_zero_outside P D.support D.support_measurable D.support_compact.isClosed
    _ _ (velocityPath_supported τ hτ hτT B G (D.clamp t)) (x,(θ : AddCircle P)) hx

theorem vectorDerivative_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    vectorDerivative τ hτ hτT B G (t,(x,θ)) = 0 := by
  change pointField P (derivativePath τ hτ hτT B G) (derivativePath_orbit τ hτ hτT B G)
    (D.clamp t) (x,(θ : AddCircle P)) = 0
  rw [pointField_eq_representative]
  exact representative_zero_outside P D.support D.support_measurable D.support_compact.isClosed
    _ _ (derivativePath_supported τ hτ hτT B G (D.clamp t)) (x,(θ : AddCircle P)) hx

theorem vector_mean_zero (t : ℝ) (x : Space) :
    (∫ θ in (0 : ℝ)..P, vector τ hτ hτT B G (t,(x,θ))) = 0 :=
  (pointField_mean_zero_iff P (velocityPath τ hτ hτT B G)
    (velocityPath_orbit τ hτ hτT B G) (D.clamp t)).mp
      (velocityPath_mean_zero τ hτ hτT B G (D.clamp t)) x

theorem scalar_zero_outside (t : Icc (0 : ℝ) D.T) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    scalar τ hτ hτT B G (t,(x,θ)) = 0 := by
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    rw [scalar_left τ hτ hτT B G th x θ]
    exact B.pressureField_zero_outside (G.initial τ hτ hτT.le) th x hx _
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    rw [scalar_right τ hτ hτT B G tr x θ]
    exact (G.tail τ hτ.le hτT).scalar_zero_outside (forwardInitial τ hτ hτT B G) _ x hx θ

theorem scalar_normalized (t : Icc (0 : ℝ) D.T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, scalar τ hτ hτT B G (t,(x,θ))) = 0 := by
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    have he : (fun θ => scalar τ hτ hτT B G (t,(x,θ))) =
        fun θ : ℝ => B.pressureField (G.initial τ hτ hτT.le) th (x,(θ : AddCircle P)) :=
      funext (fun θ => scalar_left τ hτ hτT B G th x θ)
    rw [he]
    exact B.pressureField_mean_zero (G.initial τ hτ hτT.le) th x
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    have he : (fun θ => scalar τ hτ hτT B G (t,(x,θ))) =
        fun θ => (G.tail τ hτ.le hτT).scalar (forwardInitial τ hτ hτT B G) ((t : ℝ)-τ,(x,θ)) :=
      funext (fun θ => scalar_right τ hτ hτT B G tr x θ)
    rw [he]
    exact (G.tail τ hτ.le hτT).scalar_normalized (forwardInitial τ hτ hτT B G) _ x

theorem vector_periodic (t : ℝ) (x : Space) : Function.Periodic (fun θ => vector τ hτ hτT B G
  (t,(x,θ))) P := by
  intro θ
  simp only [vector,AddCircle.coe_add_period]

theorem scalar_periodic (t : ℝ) (x : Space) : Function.Periodic (fun θ => scalar τ hτ hτT B G
  (t,(x,θ))) P := by
  intro θ
  simp only [scalar,AddCircle.coe_add_period]

end EulerTransversePacketJoin
