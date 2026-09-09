/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseVariationalOperator

@[expose] public section

/-!
# The genuine transverse Gram inverse

The inverse of `Q*Q`, for `Q = F R⊥`, is constructed from the lower frame
bound.  Its inverse identities and derivative follow from the already proved
coercive operator inverse, not from an assumed matrix inverse.
-/

noncomputable section

namespace EulerTransverseGramInverse

open InnerProductSpace ContinuousLinearMap EulerCoerciveProjection EulerInverseRegularity

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Taking an adjoint is an actual bounded real-linear map. -/
def realAdjoint : (U →L[ℝ] E) →L[ℝ] (E →L[ℝ] U) :=
  ({ toFun := fun Q => Q.adjoint
     map_add' := fun A B => map_add ContinuousLinearMap.adjoint A B
     map_smul' := fun a A => by simp } :
      (U →L[ℝ] E) →ₗ[ℝ] (E →L[ℝ] U)).mkContinuous 1
    (fun Q => by
      change ‖Q.adjoint‖ ≤ (1 : ℝ) * ‖Q‖
      rw [LinearIsometryEquiv.norm_map, one_mul])

/-- The transverse Gram matrix as a genuine bounded operator. -/
def gram (Q : U →L[ℝ] E) : U →L[ℝ] U := Q.adjoint.comp Q

/-- The Gram quadratic form is precisely the squared physical-frame norm. -/
theorem gram_inner (Q : U →L[ℝ] E) (x : U) :
    ⟪gram Q x, x⟫_ℝ = ‖Q x‖ ^ 2 := by
  simp only [gram, comp_apply, adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- A lower frame bound is a coercivity bound for the actual Gram matrix. -/
theorem gram_coercive (Q : U →L[ℝ] E) (c : ℝ)
    (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ ‖Q x‖ ^ 2) (x : U) :
    c * ‖x‖ ^ 2 ≤ ⟪gram Q x, x⟫_ℝ := by
  rw [gram_inner]
  exact hQ x

/-- The Gram inverse is constructed by the actual coercive solver. -/
def gramInverse (Q : U →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ ‖Q x‖ ^ 2) : U →L[ℝ] U :=
  coerciveInverse (gram Q) c hc (gram_coercive Q c hQ)

/-- The constructed Gram inverse is a right inverse. -/
theorem gram_inverse_apply (Q : U →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ ‖Q x‖ ^ 2) (x : U) :
    gram Q (gramInverse Q c hc hQ x) = x :=
  operator_inverse_apply (gram Q) c hc (gram_coercive Q c hQ) x

/-- The constructed Gram inverse is a left inverse. -/
theorem inverse_gram_apply (Q : U →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ ‖Q x‖ ^ 2) (x : U) :
    gramInverse Q c hc hQ (gram Q x) = x :=
  inverse_operator_apply (gram Q) c hc (gram_coercive Q c hQ) x

/-- The inverse norm retains the quantitative lower frame bound. -/
theorem gramInverse_norm (Q : U →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ ‖Q x‖ ^ 2) :
    ‖gramInverse Q c hc hQ‖ ≤ c⁻¹ :=
  coerciveInverse_norm_le (gram Q) c hc (gram_coercive Q c hQ)

/-- A canonical bounded left inverse for the physical transverse frame. -/
def frameLeftInverse (Q : U →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ ‖Q x‖ ^ 2) : E →L[ℝ] U :=
  (gramInverse Q c hc hQ).comp Q.adjoint

/-- The canonical left inverse recovers every transverse coordinate. -/
theorem frameLeftInverse_apply (Q : U →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ ‖Q x‖ ^ 2) (x : U) :
    frameLeftInverse Q c hc hQ (Q x) = x :=
  inverse_gram_apply Q c hc hQ x

/-- Differentiating the actual adjoint commutes with the real derivative. -/
theorem hasDerivAt_adjoint (Q : ℝ → U →L[ℝ] E) (Q₁ : U →L[ℝ] E) (t : ℝ)
    (hQ : HasDerivAt Q Q₁ t) :
    HasDerivAt (fun s => (Q s).adjoint) Q₁.adjoint t := by
  exact ((realAdjoint (U := U) (E := E)).hasFDerivAt).comp_hasDerivAt t hQ

/-- The Gram derivative is the literal product rule. -/
theorem hasDerivAt_gram (Q : ℝ → U →L[ℝ] E) (Q₁ : U →L[ℝ] E) (t : ℝ)
    (hQ : HasDerivAt Q Q₁ t) :
    HasDerivAt (fun s => gram (Q s))
      (Q₁.adjoint.comp (Q t) + (Q t).adjoint.comp Q₁) t :=
  (hasDerivAt_adjoint Q Q₁ t hQ).clm_comp hQ

/-- The constructed Gram inverse has the actual inverse derivative. -/
theorem hasDerivAt_gramInverse (Q : ℝ → U →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ s x, c * ‖x‖ ^ 2 ≤ ‖Q s x‖ ^ 2)
    (Q₁ : U →L[ℝ] E) (t : ℝ) (hd : HasDerivAt Q Q₁ t) :
    HasDerivAt (fun s => gramInverse (Q s) c hc (hQ s))
      (-(gramInverse (Q t) c hc (hQ t)).comp
        ((Q₁.adjoint.comp (Q t) + (Q t).adjoint.comp Q₁).comp
          (gramInverse (Q t) c hc (hQ t)))) t :=
  hasDerivAt_coerciveInverse (fun s => gram (Q s)) c hc
    (fun s => gram_coercive (Q s) c (hQ s)) t _ (hasDerivAt_gram Q Q₁ t hd)

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution

/-- The adjoint of a continuous coefficient path is a continuous coefficient path. -/
def adjointPath (T : ℝ) (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) :
    C(Icc (0 : ℝ) T, E →L[ℝ] U) :=
  ⟨fun t => (Q t).adjoint, (realAdjoint (U := U) (E := E)).continuous.comp Q.continuous⟩

/-- The actual Bochner multiplier adjoint is pointwise transposition of the coefficient. -/
theorem timeMultiplier_adjoint (T : ℝ) (hT : 0 ≤ T)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) :
    (timeMultiplier T hT Q).adjoint = timeMultiplier T hT (adjointPath T Q) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [timeMultiplier_ae T hT Q v,
    timeMultiplier_ae T hT (adjointPath T Q) u] with t hQ hQT
  rw [hQ, hQT]
  exact (adjoint_inner_left (Q (projIcc 0 T hT t)) (v t) (u t)).symm

end EulerTransverseGramInverse
