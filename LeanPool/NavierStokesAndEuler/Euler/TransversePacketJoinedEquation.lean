/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedField
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJets

@[expose] public section

/-! The complete constructed transverse path satisfies the literal packet equation on the whole
  closed interval. -/

noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerCylinderSmoothOrbit EulerCylinderScalarPrimitive EulerPacketProfileRecursion
  EulerTransversePacketProvider EulerPacketCylinderField EulerLpCylinderPaths
  EulerPacketPointJets EulerMetricTransport EulerTimeIntervalRestriction
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

theorem scalar_smooth (t : ℝ) : ContDiff ℝ ∞ (fun y : Space × ℝ => scalar τ hτ hτT B G (t,y)) :=
  coverField_contDiff P _ (scalarPointField_smooth P (pressurePath τ hτ hτT B G)
    (pressurePath_orbit τ hτ hτT B G) (D.clamp t))

/-- The complete actual high field and normalized pressure satisfy (11),
including at the history/forward junction. -/
theorem equation (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    vectorDerivative τ hτ hτT B G (t,(x,θ))+
      D.strain (t,(x,θ)) (vector τ hτ hτT B G (t,(x,θ)))+
      deriv (fun s => scalar τ hτ hτT B G (t,(x,s))) θ • D.normalField (t,(x,θ)) = raw (t,(x,θ)) :=
        by
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    have hs : (fun s => scalar τ hτ hτT B G (t,(x,s))) =
        fun s : ℝ => B.pressureField (G.initial τ hτ hτT.le) th (x,(s : AddCircle P)) :=
      funext (fun s => scalar_left τ hτ hτT B G th x s)
    have hM : D.strain (t,(x,θ)) = (D.initial τ hτ hτT.le).M.field th x := by
      simp only [Data.strain,Data.clamp_coe]
      rfl
    have hm : D.normalField (t,(x,θ)) = (D.initial τ hτ hτT.le).normal.field th x := by
      simp only [Data.normalField,Data.clamp_coe]
      rfl
    rw [vectorDerivative_left τ hτ hτT B G th x θ,vector_left τ hτ hτT B G th x θ,hs,hM,hm]
    exact B.field_pressure_equation (G.initial τ hτ hτT.le) th x θ
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    let tf : Icc (0 : ℝ) (D.T-τ) :=
      ⟨(t : ℝ)-τ,sub_nonneg.mpr tr.property.1,sub_le_sub_right t.property.2 τ⟩
    have heT : tailInclusion D.T τ hτ.le tf = t := by
      apply Subtype.ext
      change τ+((t : ℝ)-τ) = t
      ring
    have htf : (D.tail τ hτ.le hτT).clamp tf = tf :=
      (D.tail τ hτ.le hτT).clamp_coe tf
    have hs : (fun s => scalar τ hτ hτT B G (t,(x,s))) =
        fun s => (G.tail τ hτ.le hτT).scalar (forwardInitial τ hτ hτT B G) (tf,(x,s)) :=
      funext (fun s => scalar_right τ hτ hτT B G tr x s)
    have hM : D.strain (t,(x,θ)) = (D.tail τ hτ.le hτT).strain (tf,(x,θ)) := by
      simp only [Data.strain,Data.clamp_coe,htf]
      change D.M.field t x = D.M.field (tailInclusion D.T τ hτ.le tf) x
      rw [heT]
    have hm : D.normalField (t,(x,θ)) = (D.tail τ hτ.le hτT).normalField (tf,(x,θ)) := by
      simp only [Data.normalField,Data.clamp_coe,htf]
      change D.normal.field t x = D.normal.field (tailInclusion D.T τ hτ.le tf) x
      rw [heT]
    have hr : shiftedRaw τ raw (tf,(x,θ)) = raw (t,(x,θ)) := by
      change raw (τ+((t : ℝ)-τ),(x,θ)) = raw (t,(x,θ))
      rw [show τ+((t : ℝ)-τ) = t by ring]
    rw [vectorDerivative_right τ hτ hτT B G tr x θ,vector_right τ hτ hτT B G tr x θ,hs,hM,hm,← hr]
    exact (G.tail τ hτ.le hτT).equation (forwardInitial τ hτ hτT B G) tf x θ

/-- The literal sliced-jet equation consumed by the packet grade recursion. -/
theorem jet_equation (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    linearPart (D.strain (t,(x,θ)))
        (slicedJet (Icc (0 : ℝ) D.T) (vector τ hτ hτT B G) (t,(x,θ)))+
      fastPressure (D.normalField (t,(x,θ))) (pressureJet (scalar τ hτ hτT B G) (t,(x,θ))) = raw
        (t,(x,θ)) := by
  change (slicedJet (Icc (0 : ℝ) D.T) (vector τ hτ hτT B G) (t,(x,θ))).2 timeDirection+
    D.strain (t,(x,θ)) (vector τ hτ hτT B G (t,(x,θ)))+_ = _
  rw [(vectorField τ hτ hτT B G).slicedJet_temporal D.T_pos (vectorDerivativeField τ hτ hτT B G)
    (vectorField_time τ hτ hτT B G),fastPressure_pressureJet _ (scalar τ hτ hτT B G) t x θ
      ((scalar_smooth τ hτ hτT B G t).differentiable (by simp) (x,θ))]
  exact equation τ hτ hτT B G t x θ

end EulerTransversePacketJoin
