/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryParity
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedCorrectorSupport
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTimeParity

@[expose] public section

/-! Joint parity of the complete constructed high inverse, pressure and actual corrector. -/

noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderFieldReflection
  EulerPacketProfileRecursion EulerTransversePacketProvider EulerTimeIntervalRestriction
  EulerElapsedTimePathGluing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(-x,-θ)) = -raw (t,(x,θ)))

include hF hM hH hraw

theorem forwardInitial_reflection_neg :
    reflection P ((forwardInitial τ hτ hτT B G).value : CylinderL2 P U) =
      -((forwardInitial τ hτ hτT B G).value : CylinderL2 P U) :=
  B.coordinatePath_reflection_neg (G.initial τ hτ hτT.le)
    (fun t x => hF (initialInclusion D.T τ hτT.le t) x)
    (fun t x => hM (initialInclusion D.T τ hτT.le t) x) hH
    (fun t x θ => hraw (initialInclusion D.T τ hτT.le t) x θ) ⟨τ,hτ.le,le_rfl⟩

include hSym

theorem futureVelocity_reflection_neg (t : Icc (0 : ℝ) (D.T-τ)) :
    reflection P (futureVelocity τ hτ hτT B G t) = -futureVelocity τ hτ hτT B G t :=
  (G.tail τ hτ.le hτT).velocityPath_reflection_neg (forwardInitial τ hτ hτT B G) hSym
    (fun s x => hF (tailInclusion D.T τ hτ.le s) x)
    (fun s x => hM (tailInclusion D.T τ hτ.le s) x)
    (fun s x θ => hraw (tailInclusion D.T τ hτ.le s) x θ)
    (forwardInitial_reflection_neg τ hτ hτT B G hF hM hH hraw) t

theorem velocityPath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (velocityPath τ hτ hτT B G t) = -velocityPath τ hτ hτT B G t := by
  apply join_mem D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B G)
    {u | reflection P u = -u} _ _ t
  · exact B.velocityPath_reflection_neg (G.initial τ hτ hτT.le)
      (fun s x => hF (initialInclusion D.T τ hτT.le s) x)
      (fun s x => hM (initialInclusion D.T τ hτT.le s) x) hH
      (fun s x θ => hraw (initialInclusion D.T τ hτT.le s) x θ)
  · exact futureVelocity_reflection_neg τ hτ hτT B G hSym hF hM hH hraw

theorem vector_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    vector τ hτ hτT B G (t,(-x,-θ)) = -vector τ hτ hτT B G (t,(x,θ)) :=
  (vectorField τ hτ hτT B G).raw_odd_of_reflection_neg t
    (velocityPath_reflection_neg τ hτ hτT B G hSym hF hM hH hraw t) x θ

theorem vectorDerivative_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    vectorDerivative τ hτ hτT B G (t,(-x,-θ)) = -vectorDerivative τ hτ hτT B G (t,(x,θ)) :=
  (vectorField τ hτ hτT B G).timeDerivative_odd (vectorDerivativeField τ hτ hτT B G)
    D.T_pos (vectorField_time τ hτ hτT B G) (vector_odd τ hτ hτT B G hSym hF hM hH hraw) t x θ

theorem scalar_even (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    scalar τ hτ hτT B G (t,(-x,-θ)) = scalar τ hτ hτT B G (t,(x,θ)) := by
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    rw [scalar_left τ hτ hτT B G th (-x) (-θ),scalar_left τ hτ hτT B G th x θ]
    exact B.pressureField_even (G.initial τ hτ hτT.le)
      (fun s x => hF (initialInclusion D.T τ hτT.le s) x)
      (fun s x => hM (initialInclusion D.T τ hτT.le s) x) hH
      (fun s x θ => hraw (initialInclusion D.T τ hτT.le s) x θ) th x θ
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    let tf : Icc (0 : ℝ) (D.T-τ) :=
      ⟨(t : ℝ)-τ,sub_nonneg.mpr tr.property.1,sub_le_sub_right t.property.2 τ⟩
    rw [scalar_right τ hτ hτT B G tr (-x) (-θ),scalar_right τ hτ hτT B G tr x θ]
    exact (G.tail τ hτ.le hτT).scalar_even (forwardInitial τ hτ hτT B G) hSym
      (fun s x => hF (tailInclusion D.T τ hτ.le s) x)
      (fun s x => hM (tailInclusion D.T τ hτ.le s) x)
      (fun s x θ => hraw (tailInclusion D.T τ hτ.le s) x θ)
      (forwardInitial_reflection_neg τ hτ hτT B G hF hM hH hraw) tf x θ

theorem curlCorrector_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    D.curlCorrector P (vector τ hτ hτT B G) (t,(-x,-θ)) =
      -D.curlCorrector P (vector τ hτ hτT B G) (t,(x,θ)) := by
  apply D.curlCorrector_odd P (vector τ hτ hτT B G) t
  · simpa only [Data.clamp_coe] using D.inverse_even hF t
  · exact (vectorField τ hτ hτT B G).raw_smooth t
  · exact vector_periodic τ hτ hτT B G t
  · exact vector_mean_zero τ hτ hτT B G t
  · exact vector_odd τ hτ hτT B G hSym hF hM hH hraw t

theorem correctorDerivative_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    correctorDerivative τ hτ hτT B G (t,(-x,-θ)) =
      -correctorDerivative τ hτ hτT B G (t,(x,θ)) :=
  (correctorField τ hτ hτT B G).timeDerivative_odd (correctorDerivativeField τ hτ hτT B G)
    D.T_pos (correctorField_time τ hτ hτT B G) (curlCorrector_odd τ hτ hτT B G hSym hF hM hH hraw)
      t x θ

end EulerTransversePacketJoin
