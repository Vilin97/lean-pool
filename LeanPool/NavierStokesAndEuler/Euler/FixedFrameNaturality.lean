/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedSpaceInverse
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap

/-!
# Naturality of the actual fixed-frame Dirichlet inverse

Bounded spatial maps preserving the coefficients and their adjoint test maps
commute with the constructed coercive solve. This covers translations and
spatial support projections on actual L², not just pointwise model solutions.
-/

@[expose] public section


noncomputable section

namespace EulerFixedFrameNaturality

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerTimeLp
  EulerTerminalTimePrimitive EulerVolterraConvolution EulerTimeH1OperatorProduct
  EulerTimeH1FrameTransport EulerTransverseFixedSpaceInverse EulerTimeLpBoundedMap

variable {U V E F : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (T : ℝ) (hT : 0 ≤ T)

/-- The genuine bounded spatial map on the fixed zero-trace derivative space. -/
def zeroTraceMap (A : U →L[ℝ] V) :
    zeroTraceDerivatives (U := U) T hT →L[ℝ] zeroTraceDerivatives (U := V) T hT :=
  ((timeLift T A).comp (zeroTraceDerivatives (U := U) T hT).subtypeL).codRestrict
    (zeroTraceDerivatives (U := V) T hT) (fun u => by
      change initialTrace T hT (timeLift T A (u : TimeLp T U)) = 0
      have hu : initialTrace T hT (u : TimeLp T U) = 0 := u.property
      rw [initialTrace_timeLift,hu,map_zero])

@[simp] theorem zeroTraceMap_coe (A : U →L[ℝ] V) (u : zeroTraceDerivatives (U := U) T hT) :
    (zeroTraceMap T hT A u : TimeLp T V) = timeLift T A (u : TimeLp T U) := rfl

theorem zeroTraceMap_norm (A : U →L[ℝ] V) : ‖zeroTraceMap T hT A‖ ≤ ‖A‖ := by
  apply opNorm_le_bound _ (norm_nonneg A)
  intro u
  exact timeLift_apply_norm_le T A (u : TimeLp T U)

omit [CompleteSpace U] [CompleteSpace V] [CompleteSpace E] [CompleteSpace F] in
theorem timeMultiplier_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (hQR : ∀ t u, R t (A u) = B (Q t u)) (u : TimeLp T U) :
    timeMultiplier T hT R (timeLift T A u) = timeLift T B (timeMultiplier T hT Q u) := by
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT R (timeLift T A u),timeLift_ae T A u,
    timeLift_ae T B (timeMultiplier T hT Q u),timeMultiplier_ae T hT Q u] with t hr ha hb hq
  rw [hr,ha,hb,hq]
  exact hQR (projIcc 0 T hT t) (u t)

omit [CompleteSpace E] [CompleteSpace F] in
theorem productDerivative_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R R₁ : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (hQR : ∀ t u, R t (A u) = B (Q t u))
    (hQR₁ : ∀ t u, R₁ t (A u) = B (Q₁ t u)) (u : TimeLp T U) :
    productDerivative T hT R R₁ (timeLift T A u) = timeLift T B (productDerivative T hT Q Q₁ u) :=
        by
  change timeMultiplier T hT R₁ (primitiveTimeLp T hT (timeLift T A u)) +
      timeMultiplier T hT R (timeLift T A u) =
    timeLift T B (timeMultiplier T hT Q₁ (primitiveTimeLp T hT u)+timeMultiplier T hT Q u)
  rw [primitiveTimeLp_timeLift,timeMultiplier_intertwines T hT A B Q₁ R₁ hQR₁,
    timeMultiplier_intertwines T hT A B Q R hQR,map_add]

omit [CompleteSpace E] [CompleteSpace F] in
theorem fixedDerivative_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R R₁ : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (hQR : ∀ t u, R t (A u) = B (Q t u))
    (hQR₁ : ∀ t u, R₁ t (A u) = B (Q₁ t u)) (u : zeroTraceDerivatives (U := U) T hT) :
    fixedFrameDerivative T hT R R₁ (zeroTraceMap T hT A u) =
      timeLift T B (fixedFrameDerivative T hT Q Q₁ u) :=
  productDerivative_intertwines T hT A B Q Q₁ R R₁ hQR hQR₁ (u : TimeLp T U)

theorem fixedPrimitive_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R R₁ : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (hQR : ∀ t u, R t (A u) = B (Q t u))
    (hQR₁ : ∀ t u, R₁ t (A u) = B (Q₁ t u)) (u : zeroTraceDerivatives (U := U) T hT) :
    fixedFramePrimitive T hT R R₁ (zeroTraceMap T hT A u) =
      timeLift T B (fixedFramePrimitive T hT Q Q₁ u) := by
  change primitiveTimeLp T hT (fixedFrameDerivative T hT R R₁ (zeroTraceMap T hT A u)) = _
  rw [fixedDerivative_intertwines T hT A B Q Q₁ R R₁ hQR hQR₁,
    primitiveTimeLp_timeLift]
  rfl

/-- A coefficient intertwiner and its adjoint preserve the actual variational
solve, as follows by testing against the genuine pulled-back test field. -/
theorem fixedFrameSolver_intertwines
    (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R R₁ : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (J : C(Icc (0 : ℝ) T, F →L[ℝ] F))
    (c : ℝ) (hc : 0 < c) (hQ : ∀ t u, c * ‖u‖ ^ 2 ≤ ‖Q t u‖ ^ 2)
    (d : ℝ) (hd : 0 < d) (hR : ∀ t v, d * ‖v‖ ^ 2 ≤ ‖R t v‖ ^ 2)
    (hQtime : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (hRtime : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT R) (R₁ t) (Icc (0 : ℝ) T) t)
    (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hH : ∀ t u, ⟪H t u,u⟫_ℝ ≤ K*‖u‖^2) (hJ : ∀ t v, ⟪J t v,v⟫_ℝ ≤ L*‖v‖^2)
    (hsmall : K*(T^2/2) ≤ 1/2) (hsmall' : L*(T^2/2) ≤ 1/2)
    (hQR : ∀ t u, R t (A u) = B (Q t u))
    (hQR₁ : ∀ t u, R₁ t (A u) = B (Q₁ t u))
    (hRQ : ∀ t v, Q t (A.adjoint v) = B.adjoint (R t v))
    (hRQ₁ : ∀ t v, Q₁ t (A.adjoint v) = B.adjoint (R₁ t v))
    (hHJ : ∀ t u, J t (B u) = B (H t u)) (f : TimeLp T E) :
    zeroTraceMap T hT A (fixedFrameSolver T hT Q Q₁ H c hc hQ hQtime K hK hH hsmall f) =
      fixedFrameSolver T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f) := by
  apply fixedFrameSolver_unique T hT R R₁ J d hd hR hRtime L hL hJ hsmall'
  intro v
  have hw := fixedFrameSolver_weak T hT Q Q₁ H c hc hQ hQtime K hK hH hsmall f
    (zeroTraceMap T hT A.adjoint v)
  rw [fixedDerivative_intertwines T hT A.adjoint B.adjoint R R₁ Q Q₁ hRQ hRQ₁,
    fixedPrimitive_intertwines T hT A.adjoint B.adjoint R R₁ Q Q₁ hRQ hRQ₁] at hw
  simp only [← timeLift_adjoint,adjoint_inner_right] at hw
  rw [fixedDerivative_intertwines T hT A B Q Q₁ R R₁ hQR hQR₁,
    fixedPrimitive_intertwines T hT A B Q Q₁ R R₁ hQR hQR₁,
    timeMultiplier_intertwines T hT B B H J hHJ]
  exact hw

end EulerFixedFrameNaturality
