/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseInitialCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.InitialH1OperatorProduct
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1FrameTransport
import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointBounds
import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongEstimates

/-!
The actual left inverse of initial-zero moving-frame differentiation.  This
gives polynomial coordinate estimates for nonzero-terminal paths, including
differences between frames, without estimating a forward evolution.
-/

@[expose] public section


noncomputable section


namespace EulerTransverseInitialInverse

open Set MeasureTheory ContinuousLinearMap InnerProductSpace
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeH1FrameTransport
  EulerTransverseGramInverse EulerTransverseGramPath EulerTransverseInitialCoordinates
  EulerTransverseStrongEstimates EulerTransverseEndpointBounds

open scoped Topology

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖Q t v‖ ^ 2)
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)

/-- Initial coordinate operator, given by `initialProductDerivative T hT (frameLeftInversePath T
Q c hc hQ) (frameLeftInverseDerivativePath T Q Q₁ c hc hQ)`. -/
def initialCoordinateOperator : TimeLp T E →L[ℝ] TimeLp T U :=
  initialProductDerivative T hT (frameLeftInversePath T Q c hc hQ)
    (frameLeftInverseDerivativePath T Q Q₁ c hc hQ)

theorem initialCoordinateOperator_apply (u : TimeLp T E) :
    initialCoordinateOperator T hT Q Q₁ c hc hQ u =
      initialCoordinateDerivative T hT Q Q₁ c hc hQ u := rfl

include hd in
theorem initialCoordinates_product (u : TimeLp T U) (t : Icc (0 : ℝ) T) :
    initialCoordinates T hT Q c hc hQ (initialProductDerivative T hT Q Q₁ u) t =
      initialRealPrimitive T u t := by
  have he := initialPrimitive_initialProductDerivative T hT Q Q₁ hd u t
  change initialRealPrimitive T (initialProductDerivative T hT Q Q₁ u) t =
    Q t (initialRealPrimitive T u t) at he
  simp only [initialCoordinates, extendPath, projIcc_of_mem hT t.property, he]
  exact frameLeftInverse_apply (Q t) c hc (hQ t) _

include hd in
/-- Differentiating the true initial primitive proves the left-inverse identity. -/
theorem initialCoordinateOperator_product (u : TimeLp T U) :
    initialCoordinateOperator T hT Q Q₁ c hc hQ (initialProductDerivative T hT Q Q₁ u) = u := by
  apply Lp.ext
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), t ∈ Ioo (0 : ℝ) T
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem,
    (initialCoordinates_h1 T hT Q Q₁ c hc hQ hd (initialProductDerivative T hT Q Q₁ u)).2.2,
    initialRealPrimitive_hasDerivAt_ae T u] with t ht hcoord hu
  have he : initialCoordinates T hT Q c hc hQ (initialProductDerivative T hT Q Q₁ u) =ᶠ[𝓝 t]
      initialRealPrimitive T u := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact initialCoordinates_product T hT Q Q₁ c hc hQ hd u ⟨s, hs⟩
  exact hcoord.unique (hu.congr_of_eventuallyEq he)

theorem initialCoordinateOperator_norm_le :
    ‖initialCoordinateOperator T hT Q Q₁ c hc hQ‖ ≤ transportCost T Q Q₁ c := by
  have hb := product_norm_le T hT (initialPrimitiveTimeLp T hT)
    (initialPrimitive_norm_le_time T hT) (frameLeftInversePath T Q c hc hQ)
    (frameLeftInverseDerivativePath T Q Q₁ c hc hQ)
  have hpath := add_le_add
    (mul_le_mul_of_nonneg_left (frameLeftInverseDerivativePath_norm T Q Q₁ c hc hQ) hT)
    (frameLeftInversePath_norm T Q c hc hQ)
  change ‖initialCoordinateOperator T hT Q Q₁ c hc hQ‖ ≤ _ at hb
  apply hb.trans (hpath.trans _)
  unfold transportCost
  linarith

include hd hc hQ in
theorem norm_le_initialProductDerivative (u : TimeLp T U) :
    ‖u‖ ≤ transportCost T Q Q₁ c * ‖initialProductDerivative T hT Q Q₁ u‖ := by
  calc
    ‖u‖ = ‖initialCoordinateOperator T hT Q Q₁ c hc hQ (initialProductDerivative T hT Q Q₁ u)‖ := by
      rw [initialCoordinateOperator_product T hT Q Q₁ c hc hQ hd]
    _ ≤ ‖initialCoordinateOperator T hT Q Q₁ c hc hQ‖ *
        ‖initialProductDerivative T hT Q Q₁ u‖ := le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (initialCoordinateOperator_norm_le T hT Q Q₁ c hc hQ)
      (norm_nonneg _)

include hd hc hQ in
/-- A difference of coordinate derivatives is bounded by the physical
difference and the literal change of the frame coefficients. -/
theorem norm_sub_le_initialProductDerivative
    (P P₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (u v : TimeLp T U) :
    ‖u-v‖ ≤ transportCost T Q Q₁ c *
      (‖initialProductDerivative T hT Q Q₁ u - initialProductDerivative T hT P P₁ v‖ +
        (T * ‖Q₁-P₁‖ + ‖Q-P‖) * ‖v‖) := by
  apply (norm_le_initialProductDerivative T hT Q Q₁ c hc hQ hd (u-v)).trans
  apply mul_le_mul_of_nonneg_left _ (transportCost_pos T hT Q Q₁ c hc).le
  have he : initialProductDerivative T hT Q Q₁ (u-v) =
      (initialProductDerivative T hT Q Q₁ u - initialProductDerivative T hT P P₁ v) -
        (initialProductDerivative T hT Q Q₁ - initialProductDerivative T hT P P₁) v := by
    rw [map_sub, sub_apply]
    abel
  rw [he]
  apply (norm_sub_le _ _).trans (add_le_add (le_refl _) _)
  exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    (product_sub_norm_le T hT _ (initialPrimitive_norm_le_time T hT) Q Q₁ P P₁) (norm_nonneg v))

end EulerTransverseInitialInverse
