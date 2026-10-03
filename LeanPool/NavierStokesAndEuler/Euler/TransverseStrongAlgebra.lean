/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramPath
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Coefficient identities in the strong transverse equation

The only cancellation used here is the source frame equation `Q_tt = -H Q`.
The time derivatives of the Gram and mixed coefficients are genuine derivatives
of the prescribed coefficient paths.
-/

@[expose] public section


noncomputable section

namespace EulerTransverseStrongAlgebra

open Set ContinuousLinearMap EulerVolterraConvolution
  EulerTransverseGramInverse EulerTransverseGramPath

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (Q Q₁ Q₂ : C(Icc (0 : ℝ) T, U →L[ℝ] E))

/-- The mixed coefficient `Q* Q_t` in the transverse momentum. -/
def mixedPath : C(Icc (0 : ℝ) T, U →L[ℝ] U) :=
  ⟨fun t => (adjoint (𝕜 := ℝ) (E := U) (F := E) (Q t)).comp (Q₁ t),
    ((realAdjoint (U := U) (E := E)).continuous.comp Q.continuous).clm_comp Q₁.continuous⟩

/-- The actual product-rule derivative `Q_t* Q_t + Q* Q_tt`. -/
def mixedDerivativePath : C(Icc (0 : ℝ) T, U →L[ℝ] U) :=
  ⟨fun t => (adjoint (𝕜 := ℝ) (E := U) (F := E) (Q₁ t)).comp (Q₁ t) +
      (adjoint (𝕜 := ℝ) (E := U) (F := E) (Q t)).comp (Q₂ t),
    (((realAdjoint (U := U) (E := E)).continuous.comp Q₁.continuous).clm_comp
      Q₁.continuous).add
      (((realAdjoint (U := U) (E := E)).continuous.comp Q.continuous).clm_comp
        Q₂.continuous)⟩

variable (hT : 0 ≤ T)
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (hd₁ : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)

include hd in
/-- The actual Gram derivative on the time interval. -/
theorem gramPath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (gramPath T Q))
      (gramDerivativePath T Q Q₁ t) (Icc (0 : ℝ) T) t := by
  have h := hasDerivWithinAt_gram (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t (hd t)
  convert h using 1
  · rfl
  · simp only [extendPath, projIcc_of_mem hT t.property]
    rfl

include hd hd₁ in
/-- The actual mixed-coefficient derivative on the time interval. -/
theorem mixedPath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (mixedPath T Q Q₁))
      (mixedDerivativePath T Q Q₁ Q₂ t) (Icc (0 : ℝ) T) t := by
  have h := (hasDerivWithinAt_adjoint (extendPath T hT Q) (Q₁ t)
    (Icc (0 : ℝ) T) t (hd t)).clm_comp (hd₁ t)
  convert h using 1
  · rfl
  · simp only [extendPath, projIcc_of_mem hT t.property]
    rfl

/-- The genuine Gram inverse recovers the coordinate velocity from momentum. -/
theorem inverse_momentum_identity (Q Q₁ : U →L[ℝ] E)
    (c : ℝ) (hc : 0 < c) (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ ‖Q x‖ ^ 2)
    (ξ v : U) (u : E) (hu : u = Q₁ ξ + Q v) :
    gramInverse Q c hc hQ (adjoint (𝕜 := ℝ) (E := U) (F := E) Q u -
      adjoint (𝕜 := ℝ) (E := U) (F := E) Q (Q₁ ξ)) = v := by
  rw [hu, map_add, add_sub_cancel_left]
  exact inverse_gram_apply Q c hc hQ v

/-- The frame equation cancels the potential term and gives exactly the
projected coordinate equation (10). -/
theorem projected_equation_of_momentum_balance
    (Q Q₁ Q₂ : U →L[ℝ] E) (H : E →L[ℝ] E)
    (ξ v a : U) (u f : E)
    (hu : u = Q₁ ξ + Q v)
    (hframe : Q₂ = -(H.comp Q))
    (hbalance : adjoint (𝕜 := ℝ) (E := U) (F := E) Q₁ u -
        adjoint (𝕜 := ℝ) (E := U) (F := E) Q (H (Q ξ)) +
        adjoint (𝕜 := ℝ) (E := U) (F := E) Q f =
      ((adjoint (𝕜 := ℝ) (E := U) (F := E) Q₁).comp Q +
        (adjoint (𝕜 := ℝ) (E := U) (F := E) Q).comp Q₁) v + gram Q a +
      ((adjoint (𝕜 := ℝ) (E := U) (F := E) Q₁).comp Q₁ +
        (adjoint (𝕜 := ℝ) (E := U) (F := E) Q).comp Q₂) ξ +
      adjoint (𝕜 := ℝ) (E := U) (F := E) Q (Q₁ v)) :
    gram Q a = adjoint (𝕜 := ℝ) (E := U) (F := E) Q (f - (2 : ℝ) • Q₁ v) := by
  simp only [hu, hframe, comp_apply, add_apply, neg_apply, ContinuousLinearMap.map_add,
    ContinuousLinearMap.map_neg] at hbalance
  simp only [ContinuousLinearMap.map_sub, two_smul, ContinuousLinearMap.map_add]
  linear_combination (norm := abel) -hbalance

end EulerTransverseStrongAlgebra
