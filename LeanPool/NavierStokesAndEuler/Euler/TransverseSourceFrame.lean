/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongEquation

@[expose] public section

/-!
# The source frame `Q = F R⊥`

These coefficient lemmas discharge the moving-plane range and lower-frame
hypotheses using the prescribed invertible deformation and orthonormal reference
plane. No inverse solution or acceleration is supplied as input.
-/

noncomputable section

namespace EulerTransverseSourceFrame

open Set InnerProductSpace ContinuousLinearMap MeasureTheory
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution
  EulerTransverseFrameCoordinates EulerTransverseVariationalInverse
  EulerTransverseCoordinateRegularity EulerTransverseStrongEquation
  EulerTransverseGramInverse

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (m₀ : E) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)

/-- The fixed orthonormal reference-plane embedding. -/
def referenceEmbedding : U →L[ℝ] E :=
  (referencePlane m₀).subtypeL.comp R.toContinuousLinearEquiv.toContinuousLinearMap

/-- Applying the source deformation to the fixed orthonormal reference plane. -/
def framePath (T : ℝ) (F : C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    C(Icc (0 : ℝ) T, U →L[ℝ] E) :=
  ⟨fun t => (F t).comp (referenceEmbedding m₀ R), F.continuous.clm_comp continuous_const⟩

omit [CompleteSpace U] [CompleteSpace E] in
/-- The frame is literally the source expression `F R⊥`. -/
theorem framePath_apply (T : ℝ) (F : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (t : Icc (0 : ℝ) T) (x : U) :
    framePath m₀ R T F t x = F t (R x : E) := rfl

omit [CompleteSpace U] in
/-- The source frame maps into the moving tangent plane. -/
theorem framePath_tangent (T : ℝ) (F : Icc (0 : ℝ) T → E ≃L[ℝ] E)
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hA : ∀ t, A t = (F t).toContinuousLinearMap)
    (t : Icc (0 : ℝ) T) (x : U) :
    ⟪movingNormal (F t) m₀, framePath m₀ R T A t x⟫_ℝ = 0 := by
  apply (tangent_iff (F t) m₀ _).2
  rw [framePath_apply, hA]
  change (F t).symm (F t (R x : E)) ∈ referencePlane m₀
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact (R x).property

omit [CompleteSpace U] in
/-- Every moving tangent vector is in the range of the actual source frame. -/
theorem framePath_range (T : ℝ) (F : Icc (0 : ℝ) T → E ≃L[ℝ] E)
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hA : ∀ t, A t = (F t).toContinuousLinearMap)
    (t : Icc (0 : ℝ) T) (η : E) (hη : ⟪movingNormal (F t) m₀, η⟫_ℝ = 0) :
    ∃ x : U, framePath m₀ R T A t x = η := by
  refine ⟨frameCoordinates (F t) m₀ R η, ?_⟩
  rw [framePath_apply, hA]
  exact frame_reconstruct (F t) m₀ η R hη

omit [CompleteSpace U] [CompleteSpace E] in
/-- A bound on `F⁻¹` gives a quantitative lower frame bound, because `R⊥` is isometric. -/
theorem framePath_lower_bound (T : ℝ) (F : Icc (0 : ℝ) T → E ≃L[ℝ] E)
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hA : ∀ t, A t = (F t).toContinuousLinearMap)
    (B : ℝ) (hB : 0 < B) (hinv : ∀ t, ‖(F t).symm.toContinuousLinearMap‖ ≤ B)
    (t : Icc (0 : ℝ) T) (x : U) :
    (B⁻¹)^2 * ‖x‖^2 ≤ ‖framePath m₀ R T A t x‖^2 := by
  have hn : ‖x‖ ≤ B * ‖framePath m₀ R T A t x‖ := by
    calc
      ‖x‖ = ‖(F t).symm (framePath m₀ R T A t x)‖ := by
        rw [framePath_apply, hA]
        change ‖x‖ = ‖(F t).symm (F t (R x : E))‖
        rw [ContinuousLinearEquiv.symm_apply_apply]
        exact (R.norm_map x).symm
      _ ≤ ‖(F t).symm.toContinuousLinearMap‖ * ‖framePath m₀ R T A t x‖ :=
        (F t).symm.toContinuousLinearMap.le_opNorm _
      _ ≤ B * ‖framePath m₀ R T A t x‖ :=
        mul_le_mul_of_nonneg_right (hinv t) (norm_nonneg _)
  have hdiv : ‖x‖ / B ≤ ‖framePath m₀ R T A t x‖ :=
    (div_le_iff₀ hB).2 (by simpa only [mul_comm] using hn)
  have hs := (sq_le_sq₀ (div_nonneg (norm_nonneg x) hB.le) (norm_nonneg _)).2 hdiv
  simpa only [div_eq_mul_inv, mul_pow, mul_comm] using hs

omit [CompleteSpace U] [CompleteSpace E] in
/-- The actual within-interval derivative commutes with a fixed reference frame. -/
theorem framePath_hasDerivWithinAt (T : ℝ) (hT : 0 ≤ T)
    (A A₁ : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A₁ t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (framePath m₀ R T A))
      (framePath m₀ R T A₁ t) (Icc (0 : ℝ) T) t := by
  have h := (hd t).clm_comp (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) (referenceEmbedding m₀
    R))
  convert h using 1
  · rfl
  · simp only [comp_zero, add_zero]
    rfl

omit [CompleteSpace U] [CompleteSpace E] in
/-- The source equation `F_tt = -H F` gives the precise frame equation used in (10). -/
theorem framePath_second_equation (T : ℝ)
    (A A₂ H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hframe : ∀ t, A₂ t = -((H t).comp (A t))) (t : Icc (0 : ℝ) T) :
    framePath m₀ R T A₂ t = -((H t).comp (framePath m₀ R T A t)) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [framePath_apply, hframe, neg_apply, comp_apply]

/-- For the literal source frame `F R⊥`, the actual transverse inverse has
zero-endpoint H² coordinates satisfying equation (10). All range and inverse
bounds used by the strong theorem are discharged from `F` and `R⊥` here. -/
theorem sourceFrame_strong (T : ℝ) (hT : 0 < T)
    (F : Icc (0 : ℝ) T → E ≃L[ℝ] E)
    (A A₁ A₂ H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hA : ∀ t, A t = (F t).toContinuousLinearMap)
    (B : ℝ) (hB : 0 < B) (hinv : ∀ t, ‖(F t).symm.toContinuousLinearMap‖ ≤ B)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT.le A) (A₁ t) (Icc (0 : ℝ) T) t)
    (hd₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT.le A₁) (A₂ t) (Icc (0 : ℝ) T) t)
    (hframe : ∀ t, A₂ t = -((H t).comp (A t)))
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖^2)
    (hsmall : K * (T^2/2) ≤ 1/2) (f : TimeLp T E) :
    let m := fun t => movingNormal (F t) m₀
    let u : TimeLp T E := transverseSolver T hT.le m H K hK hH hsmall f
    ∃ (ξ v : ℝ → U) (a : TimeLp T U),
      AbsolutelyContinuousOnInterval ξ 0 T ∧ AbsolutelyContinuousOnInterval v 0 T ∧
      ξ 0 = 0 ∧ ξ T = 0 ∧
      (∀ t : Icc (0 : ℝ) T, F t (R (ξ t) : E) = realPrimitive T u t) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt ξ (v t) t) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt v (a t) t) ∧
      ∀ᵐ t ∂timeMeasure T,
        gram (extendPath T hT.le (framePath m₀ R T A) t) (a t) =
          (extendPath T hT.le (framePath m₀ R T A) t).adjoint
            (f t - (2 : ℝ) • extendPath T hT.le (framePath m₀ R T A₁) t (v t)) := by
  let Q := framePath m₀ R T A
  let Q₁ := framePath m₀ R T A₁
  let Q₂ := framePath m₀ R T A₂
  let m := fun t => movingNormal (F t) m₀
  let c := (B⁻¹)^2
  have hc : 0 < c := pow_pos (inv_pos.mpr hB) 2
  have hQ : ∀ t x, c * ‖x‖^2 ≤ ‖Q t x‖^2 := framePath_lower_bound m₀ R T F A hA B hB hinv
  have hQd := framePath_hasDerivWithinAt m₀ R T hT.le A A₁ hd
  have hQ₁d := framePath_hasDerivWithinAt m₀ R T hT.le A₁ A₂ hd₁
  let u := transverseSolver T hT.le m H K hK hH hsmall f
  obtain ⟨v, hξAC, hvAC, _, hξder, hvder, heq⟩ :=
    transverseSolver_strong T hT.le Q Q₁ Q₂ c hc hQ hQd hQ₁d hT m
      (framePath_tangent m₀ R T F A hA) (framePath_range m₀ R T F A hA)
      H K hK hH hsmall (framePath_second_equation m₀ R T A A₂ H hframe) f
  refine ⟨coordinatePrimitive T hT.le Q c hc hQ (u : TimeLp T E), v,
    coordinateSecondDerivative T hT.le Q Q₁ Q₂ c hc hQ H (u : TimeLp T E) f,
    hξAC, hvAC, coordinatePrimitive_initial T hT.le Q c hc hQ m u,
    coordinatePrimitive_terminal T hT.le Q c hc hQ (u : TimeLp T E), ?_, hξder, hvder, heq⟩
  intro t
  have hrec := coordinatePrimitive_reconstruct T hT.le Q c hc hQ m
    (framePath_range m₀ R T F A hA) u t
  change A t (R (coordinatePrimitive T hT.le Q c hc hQ (u : TimeLp T E) t) : E) = _ at hrec
  rw [hA t] at hrec
  exact hrec

end EulerTransverseSourceFrame
