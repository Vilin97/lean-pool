/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramPath
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1OperatorProduct
public import LeanPool.NavierStokesAndEuler.Euler.TransverseVariationalInverse

/-!
# Genuine time-H¹ transverse coordinates

The coordinates are obtained by applying the constructed frame left inverse to
the physical displacement. Their time derivative is an actual Bochner L² field,
and differentiating the reconstructed displacement gives the exact kinetic
coordinate identity used in the strong transverse equation.
-/

@[expose] public section


noncomputable section

namespace EulerTransverseCoordinateRegularity

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution
  EulerTimeH1OperatorProduct EulerTransverseVariationalInverse
  EulerTransverseGramInverse EulerTransverseGramPath

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c)
  (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)

/-- Canonical coordinates obtained from the actual inverse Gram coefficient. -/
def coordinatePrimitive (u : TimeLp T E) : ℝ → U :=
  productPrimitive T hT (frameLeftInversePath T Q c hc hQ) u

/-- The actual L² derivative of the canonical coordinates. -/
def coordinateDerivative (u : TimeLp T E) : TimeLp T U :=
  productDerivative T hT (frameLeftInversePath T Q c hc hQ)
    (frameLeftInverseDerivativePath T Q Q₁ c hc hQ) u

variable (hd : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)

include hd in
/-- The canonical coordinates are genuinely absolutely continuous. -/
theorem coordinatePrimitive_absolutelyContinuous (u : TimeLp T E) :
    AbsolutelyContinuousOnInterval (coordinatePrimitive T hT Q c hc hQ u) 0 T :=
  productPrimitive_absolutelyContinuous T hT (frameLeftInversePath T Q c hc hQ)
    (frameLeftInverseDerivativePath T Q Q₁ c hc hQ)
    (frameLeftInversePath_hasDerivWithinAt T Q Q₁ c hc hQ hT hd) u

include hd in
/-- The explicitly constructed L² field is the actual a.e. coordinate derivative. -/
theorem coordinatePrimitive_hasDerivAt_ae (u : TimeLp T E) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (coordinatePrimitive T hT Q c hc hQ u)
        (coordinateDerivative T hT Q Q₁ c hc hQ u t) t :=
  productPrimitive_hasDerivAt_ae T hT (frameLeftInversePath T Q c hc hQ)
    (frameLeftInverseDerivativePath T Q Q₁ c hc hQ)
    (frameLeftInversePath_hasDerivWithinAt T Q Q₁ c hc hQ hT hd) u

include hd in
/-- Integrating the coordinate derivative recovers the canonical coordinates. -/
theorem terminalPrimitive_coordinateDerivative (u : TimeLp T E) (t : Icc (0 : ℝ) T) :
    terminalPrimitive T hT (coordinateDerivative T hT Q Q₁ c hc hQ u) t =
      coordinatePrimitive T hT Q c hc hQ u t := by
  exact (productPrimitive_eq_realPrimitive T hT (frameLeftInversePath T Q c hc hQ)
    (frameLeftInverseDerivativePath T Q Q₁ c hc hQ)
    (frameLeftInversePath_hasDerivWithinAt T Q Q₁ c hc hQ hT hd) u t t.property).symm

/-- The initial coordinate trace vanishes for every admissible displacement. -/
theorem coordinatePrimitive_initial (m : Icc (0 : ℝ) T → E)
    (u : transverseDerivatives T hT m) :
    coordinatePrimitive T hT Q c hc hQ (u : TimeLp T E) 0 = 0 := by
  have hu : realPrimitive T (u : TimeLp T E) 0 = 0 := u.property.1
  simp only [coordinatePrimitive, productPrimitive, hu, map_zero]

/-- The terminal coordinate trace vanishes identically. -/
theorem coordinatePrimitive_terminal (u : TimeLp T E) :
    coordinatePrimitive T hT Q c hc hQ u T = 0 :=
  productPrimitive_terminal T hT (frameLeftInversePath T Q c hc hQ) u

/-- Reconstruction only requires the prescribed physical displacement to lie
in the actual range of the frame. This general statement also applies to
infinite-dimensional spatial constraint spaces. -/
theorem coordinatePrimitive_reconstruct_of_range (u : TimeLp T E)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = realPrimitive T u t)
    (t : Icc (0 : ℝ) T) :
    Q t (coordinatePrimitive T hT Q c hc hQ u t) = realPrimitive T u t := by
  obtain ⟨x, hx⟩ := huRange t
  simp only [coordinatePrimitive, productPrimitive, extendPath, projIcc_of_mem hT t.property]
  rw [← hx]
  change Q t (frameLeftInverse (Q t) c hc (hQ t) (Q t x)) = Q t x
  rw [frameLeftInverse_apply]

include hd in
/-- The kinetic identity follows from injectivity of the genuine time primitive. -/
theorem coordinateDerivative_reconstruct_of_range (u : TimeLp T E)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = realPrimitive T u t) :
    productDerivative T hT Q Q₁ (coordinateDerivative T hT Q Q₁ c hc hQ u) = u := by
  apply terminalPrimitive_injective T hT
  apply ContinuousMap.ext
  intro t
  rw [terminalPrimitive_productDerivative T hT Q Q₁ hd,
    terminalPrimitive_coordinateDerivative T hT Q Q₁ c hc hQ hd]
  exact coordinatePrimitive_reconstruct_of_range T hT Q c hc hQ u huRange t

include hd in
/-- The L² primitive of the coordinate derivative has the actual coordinate
path as its representative. -/
theorem coordinatePrimitive_ae (u : TimeLp T E) :
    (primitiveTimeLp T hT (coordinateDerivative T hT Q Q₁ c hc hQ u) : ℝ → U) =ᵐ[timeMeasure T]
      coordinatePrimitive T hT Q c hc hQ u := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [hmem,
    primitiveTimeLp_ae T hT (coordinateDerivative T hT Q Q₁ c hc hQ u)] with t ht hp
  exact hp.trans (terminalPrimitive_coordinateDerivative T hT Q Q₁ c hc hQ hd u ⟨t, ht⟩)

include hd in
/-- The physical derivative has the literal expression `Q_t ξ + Q ξ_t` a.e. -/
theorem coordinateDerivative_reconstruct_ae_of_range (u : TimeLp T E)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = realPrimitive T u t) :
    ∀ᵐ t ∂timeMeasure T,
      u t = extendPath T hT Q₁ t (coordinatePrimitive T hT Q c hc hQ u t) +
        extendPath T hT Q t (coordinateDerivative T hT Q Q₁ c hc hQ u t) := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hid := coordinateDerivative_reconstruct_of_range T hT Q Q₁ c hc hQ hd u huRange
  have hprod := productDerivative_ae T hT Q Q₁ (coordinateDerivative T hT Q Q₁ c hc hQ u)
  rw [hid] at hprod
  filter_upwards [hmem, hprod] with t ht hprod
  rw [hprod]
  congr 2
  exact terminalPrimitive_coordinateDerivative T hT Q Q₁ c hc hQ hd u ⟨t, ht⟩

omit [CompleteSpace U] [CompleteSpace E] in
/-- A transverse constraint puts the physical displacement in the frame's range. -/
theorem transverse_range (m : Icc (0 : ℝ) T → E)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (u : transverseDerivatives T hT m) (t : Icc (0 : ℝ) T) :
    ∃ x : U, Q t x = realPrimitive T (u : TimeLp T E) t :=
  hRange t _ (u.property.2 t)

/-- Canonical coordinates reconstruct every admissible transverse displacement. -/
theorem coordinatePrimitive_reconstruct (m : Icc (0 : ℝ) T → E)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (u : transverseDerivatives T hT m) (t : Icc (0 : ℝ) T) :
    Q t (coordinatePrimitive T hT Q c hc hQ (u : TimeLp T E) t) =
      realPrimitive T (u : TimeLp T E) t :=
  coordinatePrimitive_reconstruct_of_range T hT Q c hc hQ (u : TimeLp T E)
    (transverse_range T hT Q m hRange u) t

include hd in
/-- The transverse derivative is the derivative of its reconstructed coordinates. -/
theorem coordinateDerivative_reconstruct (m : Icc (0 : ℝ) T → E)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (u : transverseDerivatives T hT m) :
    productDerivative T hT Q Q₁
      (coordinateDerivative T hT Q Q₁ c hc hQ (u : TimeLp T E)) =
      (u : TimeLp T E) :=
  coordinateDerivative_reconstruct_of_range T hT Q Q₁ c hc hQ hd (u : TimeLp T E)
    (transverse_range T hT Q m hRange u)

include hd in
/-- The transverse physical derivative has its actual coordinate expression a.e. -/
theorem coordinateDerivative_reconstruct_ae (m : Icc (0 : ℝ) T → E)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (u : transverseDerivatives T hT m) :
    ∀ᵐ t ∂timeMeasure T,
      (u : TimeLp T E) t =
        extendPath T hT Q₁ t (coordinatePrimitive T hT Q c hc hQ (u : TimeLp T E) t) +
        extendPath T hT Q t (coordinateDerivative T hT Q Q₁ c hc hQ (u : TimeLp T E) t) :=
  coordinateDerivative_reconstruct_ae_of_range T hT Q Q₁ c hc hQ hd (u : TimeLp T E)
    (transverse_range T hT Q m hRange u)

end EulerTransverseCoordinateRegularity
