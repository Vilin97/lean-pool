/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
public import LeanPool.NavierStokesAndEuler.Euler.TransverseVariationalInverse
import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongEquation

/-!
# Actual source coefficient paths for the transverse inverse

Evaluation of the uniformly smooth spatial coefficient path gives a genuine
smooth map from position to time paths. Restriction to the fixed orthonormal
reference plane is a linear contraction. The pointwise source derivative
bounds therefore imply exactly the time-path coefficient bounds required by
the constructed transverse inverse.
-/

section

/-!
# The source frame `Q = F R⊥`

These coefficient lemmas discharge the moving-plane range and lower-frame
hypotheses using the prescribed invertible deformation and orthonormal reference
plane. No inverse solution or acceleration is supplied as input.
-/

@[expose] public section

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

end
end

end

@[expose] public section

noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace EulerTransverseSourceCoefficientPath

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseFrameCoordinates EulerTransverseSourceFrame
  EulerOperatorGevreyCalculus EulerGevrey

section Evaluation

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cache the standard `NormedAddCommGroup (Space →ᵇ V)` instance to shorten typeclass
synthesis. -/
local instance instTransverseSourceCoefficientPath1 : NormedAddCommGroup (Space →ᵇ V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ V)` instance to shorten typeclass synthesis. -/
local instance instTransverseSourceCoefficientPath2 : NormedSpace ℝ (Space →ᵇ V) := inferInstance

/-- Actual spatial evaluation, performed uniformly along the time path. -/
def pathEvaluation (x : Space) : C(K,Space →ᵇ V) →L[ℝ] C(K,V) :=
  (BoundedContinuousFunction.evalCLM ℝ x).compLeftContinuous ℝ K

/-- Evaluation is a contraction in the genuine uniform path norm. -/
theorem pathEvaluation_norm (x : Space) : ‖pathEvaluation (K := K) (V := V) x‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  exact ((A t).norm_coe_le_norm x).trans (A.norm_coe_le_norm t)

/-- The source coefficient viewed as a time path at a spatial position. -/
def pointPath (A : SmoothCoefficientPath K V) (x : Space) : C(K,V) :=
  pathEvaluation 0 (translateCoefficientPath A.field x)

/-- The coefficient path has the literal prescribed pointwise values. -/
theorem pointPath_apply (A : SmoothCoefficientPath K V) (x : Space) (t : K) :
    pointPath A x t = A.field t x := by
  change A.field t (0+x) = A.field t x
  rw [zero_add]

/-- Genuine smooth position dependence, in the uniform time-path norm. -/
theorem pointPath_contDiff (A : SmoothCoefficientPath K V) : ContDiff ℝ ∞ (pointPath A) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(K,Space →ᵇ V)) (F := C(K,V)) (pathEvaluation 0)).comp A.translation_contDiff

/-- Source pointwise derivative bounds give actual operator-norm derivatives of the time path. -/
theorem pointPath_derivative_bound (A : SmoothCoefficientPath K V)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C) (x : Space) :
    ‖iteratedFDeriv ℝ n (pointPath A) x‖ ≤ C := by
  have h := (pathEvaluation (K := K) (V := V) 0).norm_iteratedFDeriv_comp_left
    (A.translation_contDiff.contDiffAt (x := x)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right (pathEvaluation_norm (K := K) (V := V) 0)
    (norm_nonneg _)).trans (by
        simpa only [one_mul] using A.norm_iteratedFDeriv_translation_le n C hC hb x))

/-- Every prescribed factorial coefficient bound survives the time-path construction. -/
theorem pointPath_gevrey (A : SmoothCoefficientPath K V)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C * majorant Rc d n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (pointPath A) x‖ ≤ C*majorant Rc d n :=
  pointPath_derivative_bound A n _ (mul_nonneg hC (majorant_nonneg Rc hRc d n)) (hb n) x

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Independent angle variables can be added by a fixed spatial projection. -/
theorem pointPath_pullback_contDiff (L : P →L[ℝ] Space) (A : SmoothCoefficientPath K V) :
    ContDiff ℝ ∞ (fun x => pointPath A (L x)) :=
  (pointPath_contDiff A).comp L.contDiff

/-- A spatial projection of norm at most one preserves the literal source derivative bounds. -/
theorem pointPath_pullback_derivative_bound (L : P →L[ℝ] Space) (hL : ‖L‖ ≤ 1)
    (A : SmoothCoefficientPath K V) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => pointPath A (L y)) x‖ ≤ C := by
  change ‖iteratedFDeriv ℝ n ((pointPath A) ∘ L) x‖ ≤ C
  rw [L.iteratedFDeriv_comp_right (pointPath_contDiff A) x (by simp)]
  have h := (iteratedFDeriv ℝ n (pointPath A) (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact h.trans ((mul_le_mul (pointPath_derivative_bound A n C hC hb (L x))
    (pow_le_one₀ (norm_nonneg L) hL) (pow_nonneg (norm_nonneg L) n) hC).trans_eq (mul_one C))

/-- Joint spatial/angle coefficient bounds follow from the source spatial bounds. -/
theorem pointPath_pullback_gevrey (L : P →L[ℝ] Space) (hL : ‖L‖ ≤ 1)
    (A : SmoothCoefficientPath K V)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C * majorant Rc d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => pointPath A (L y)) x‖ ≤ C*majorant Rc d n :=
  pointPath_pullback_derivative_bound L hL A n _
    (mul_nonneg hC (majorant_nonneg Rc hRc d n)) (hb n) x

end Evaluation

section Frame

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransverseSourceCoefficientPath3 : NormedAddCommGroup (U →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] Space)` instance to shorten typeclass synthesis. -/
local instance instTransverseSourceCoefficientPath4 : NormedSpace ℝ (U →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,U →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instTransverseSourceCoefficientPath5 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,U
    →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,U →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instTransverseSourceCoefficientPath6 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,U →L[ℝ]
    Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,Space →L[ℝ] Space)` instance to
shorten typeclass synthesis. -/
local instance instTransverseSourceCoefficientPath7 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ)
    T,Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instTransverseSourceCoefficientPath8 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,Space
    →L[ℝ] Space) := inferInstance

variable (m₀ : Space) (Rperp : U ≃ₗᵢ[ℝ] referencePlane m₀)

/-- The fixed orthonormal reference embedding is a contraction, including a trivial plane. -/
theorem referenceEmbedding_norm : ‖referenceEmbedding m₀ Rperp‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  change ‖Rperp v‖ ≤ 1*‖v‖
  rw [one_mul, Rperp.norm_map]

/-- Restrict an actual coefficient operator to the reference plane. -/
def referenceRestriction : (Space →L[ℝ] Space) →L[ℝ] (U →L[ℝ] Space) :=
  (compL ℝ U Space Space).flip (referenceEmbedding m₀ Rperp)

/-- The time-path reference restriction is a genuine bounded linear map. -/
def framePathMap (T : ℝ) : C(Icc (0 : ℝ) T,Space →L[ℝ] Space) →L[ℝ]
    C(Icc (0 : ℝ) T,U →L[ℝ] Space) :=
  (referenceRestriction m₀ Rperp).compLeftContinuous ℝ (Icc (0 : ℝ) T)

/-- This restriction is exactly the source frame path `F Rperp`. -/
theorem framePathMap_apply (T : ℝ) (A : C(Icc (0 : ℝ) T, Space →L[ℝ] Space)) :
    framePathMap m₀ Rperp T A = framePath m₀ Rperp T A := rfl

/-- Orthogonal reference restriction does not enlarge the coefficient path norm. -/
theorem framePathMap_norm (T : ℝ) : ‖framePathMap m₀ Rperp T‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  calc
    ‖framePathMap m₀ Rperp T A t‖ ≤ ‖A t‖ * ‖referenceEmbedding m₀ Rperp‖ := opNorm_comp_le _ _
    _ ≤ ‖A t‖ * 1 := mul_le_mul_of_nonneg_left (referenceEmbedding_norm m₀ Rperp) (norm_nonneg _)
    _ ≤ ‖A‖ := by simpa only [mul_one] using A.norm_coe_le_norm t

/-- The actual source frame depends smoothly on position in time-path operator norm. -/
theorem sourceFrame_contDiff (T : ℝ)
    (A : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)) :
    ContDiff ℝ ∞ (fun x => framePath m₀ Rperp T (pointPath A x)) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) T,Space →L[ℝ] Space))
    (F := C(Icc (0 : ℝ) T,U →L[ℝ] Space)) (framePathMap m₀ Rperp T)).comp (pointPath_contDiff A)

/-- Source spatial factorial bounds give the exact frame-path bounds used by the inverse. -/
theorem sourceFrame_gevrey (T : ℝ)
    (A : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n t x, ‖iteratedFDeriv ℝ n (A.field t : Space → Space →L[ℝ] Space) x‖ ≤
      C * majorant Rc d n) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => framePath m₀ Rperp T (pointPath A y)) x‖ ≤ C*majorant Rc d n := by
  exact contraction_bound (framePathMap m₀ Rperp T) (framePathMap_norm m₀ Rperp T)
    (pointPath A) (pointPath_contDiff A) Rc C hRc hC d (pointPath_gevrey A Rc C hRc hC d hb) n x

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The literal frame remains smooth after adjoining independent angle coordinates. -/
theorem sourceFrame_pullback_contDiff (T : ℝ) (L : P →L[ℝ] Space)
    (A : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)) :
    ContDiff ℝ ∞ (fun x => framePath m₀ Rperp T (pointPath A (L x))) :=
  (sourceFrame_contDiff m₀ Rperp T A).comp L.contDiff

/-- The actual source `F Rperp` coefficients satisfy the full joint parameter factorial bounds. -/
theorem sourceFrame_pullback_gevrey (T : ℝ) (L : P →L[ℝ] Space) (hL : ‖L‖ ≤ 1)
    (A : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n t x, ‖iteratedFDeriv ℝ n (A.field t : Space → Space →L[ℝ] Space) x‖ ≤
      C * majorant Rc d n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => framePath m₀ Rperp T (pointPath A (L y))) x‖ ≤
      C*majorant Rc d n := by
  exact contraction_bound (framePathMap m₀ Rperp T) (framePathMap_norm m₀ Rperp T)
    (fun y => pointPath A (L y)) (pointPath_pullback_contDiff L A) Rc C hRc hC d
    (pointPath_pullback_gevrey L hL A Rc C hRc hC d hb) n x

end Frame

end EulerTransverseSourceCoefficientPath
