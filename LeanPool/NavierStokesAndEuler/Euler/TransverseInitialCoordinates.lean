/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.InitialTimePrimitive
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramPath
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1FieldProduct

/-!
Actual moving-frame coordinates for initial-zero H¹ paths with arbitrary
terminal value.  The coordinate derivative is constructed in Bochner L².
The physical reconstruction and its differentiated identity follow from the
coefficient left inverse, the H¹ product rule and uniqueness of derivatives.
-/

@[expose] public section


noncomputable section


namespace EulerTransverseInitialCoordinates

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution  EulerTimeH1FieldProduct
  EulerTransverseGramInverse EulerTransverseGramPath
open scoped Topology

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)

/-- Initial coordinates, given by `extendPath T hT (frameLeftInversePath T Q c hc hQ) t
(initialRealPrimitive T u t)`. -/
def initialCoordinates (u : TimeLp T E) (t : ℝ) : U :=
  extendPath T hT (frameLeftInversePath T Q c hc hQ) t (initialRealPrimitive T u t)

/-- Initial coordinate field, given by `timeMultiplier T hT (frameLeftInversePath T Q c hc hQ)
(initialPrimitiveTimeLp T hT u)`. -/
def initialCoordinateField (u : TimeLp T E) : TimeLp T U :=
  timeMultiplier T hT (frameLeftInversePath T Q c hc hQ) (initialPrimitiveTimeLp T hT u)

/-- Initial coordinate derivative, constructed using `fieldProductDerivative`. -/
def initialCoordinateDerivative (u : TimeLp T E) : TimeLp T U :=
  fieldProductDerivative T hT (frameLeftInversePath T Q c hc hQ)
    (frameLeftInverseDerivativePath T Q Q₁ c hc hQ) (initialPrimitiveTimeLp T hT u) u

theorem initialCoordinates_initial (u : TimeLp T E) :
    initialCoordinates T hT Q c hc hQ u 0 = 0 := by
  simp only [initialCoordinates, initialRealPrimitive_initial, map_zero]

theorem initialCoordinateField_ae (u : TimeLp T E) :
    (initialCoordinateField T hT Q c hc hQ u : ℝ → U) =ᵐ[timeMeasure T]
      initialCoordinates T hT Q c hc hQ u :=
  fieldProduct_ae T hT (frameLeftInversePath T Q c hc hQ)
    (initialPrimitiveTimeLp T hT u) (initialRealPrimitive T u)
    (initialPrimitiveTimeLp_ae T hT u)

variable (hd : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)

include hd in
theorem initialCoordinates_h1 (u : TimeLp T E) :
    AbsolutelyContinuousOnInterval (initialCoordinates T hT Q c hc hQ u) 0 T ∧
      (initialCoordinateField T hT Q c hc hQ u : ℝ → U) =ᵐ[timeMeasure T]
        initialCoordinates T hT Q c hc hQ u ∧
      ∀ᵐ t ∂timeMeasure T,
        HasDerivAt (initialCoordinates T hT Q c hc hQ u)
          (initialCoordinateDerivative T hT Q Q₁ c hc hQ u t) t :=
  fieldProduct_h1 T hT (frameLeftInversePath T Q c hc hQ)
    (frameLeftInverseDerivativePath T Q Q₁ c hc hQ)
    (frameLeftInversePath_hasDerivWithinAt T Q Q₁ c hc hQ hT hd)
    (initialPrimitiveTimeLp T hT u) u (initialRealPrimitive T u)
    (initialRealPrimitive_absolutelyContinuous T u)
    (initialPrimitiveTimeLp_ae T hT u) (initialRealPrimitive_hasDerivAt_ae T u)

/-- The constructed coordinates reconstruct the actual nonzero-terminal path. -/
theorem initialCoordinates_reconstruct (u : TimeLp T E)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t)
    (t : Icc (0 : ℝ) T) :
    Q t (initialCoordinates T hT Q c hc hQ u t) = initialRealPrimitive T u t := by
  obtain ⟨x, hx⟩ := huRange t
  simp only [initialCoordinates, extendPath, projIcc_of_mem hT t.property]
  rw [← hx]
  change Q t (frameLeftInverse (Q t) c hc (hQ t) (Q t x)) = Q t x
  rw [frameLeftInverse_apply]

include hd in
/-- Differentiating reconstruction gives the literal physical velocity a.e. -/
theorem initialCoordinateDerivative_reconstruct_ae (u : TimeLp T E)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t) :
    ∀ᵐ t ∂timeMeasure T,
      u t = extendPath T hT Q₁ t (initialCoordinates T hT Q c hc hQ u t) +
        extendPath T hT Q t (initialCoordinateDerivative T hT Q Q₁ c hc hQ u t) := by
  let ξ := initialCoordinateField T hT Q c hc hQ u
  let v := initialCoordinateDerivative T hT Q Q₁ c hc hQ u
  have hξ := initialCoordinates_h1 T hT Q Q₁ c hc hQ hd u
  have hprod := fieldProduct_hasDerivAt_ae T hT Q Q₁ hd ξ v
    (initialCoordinates T hT Q c hc hQ u) hξ.2.1 hξ.2.2
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), t ∈ Ioo (0 : ℝ) T
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem, initialRealPrimitive_hasDerivAt_ae T u, hprod,
    fieldProductDerivative_ae T hT Q Q₁ ξ v, hξ.2.1] with t ht hud hpd hp hξt
  have he : initialRealPrimitive T u =ᶠ[𝓝 t]
      (fun s => extendPath T hT Q s (initialCoordinates T hT Q c hc hQ u s)) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    simpa only [extendPath, projIcc_of_mem hT hs] using
      (initialCoordinates_reconstruct T hT Q c hc hQ u huRange ⟨s, hs⟩).symm
  have hu := hud.unique (hpd.congr_of_eventuallyEq he)
  change u t = fieldProductDerivative T hT Q Q₁ ξ v t at hu
  rw [hu, hp]
  exact congrArg (fun a => extendPath T hT Q₁ t a + extendPath T hT Q t (v t)) hξt

end EulerTransverseInitialCoordinates
