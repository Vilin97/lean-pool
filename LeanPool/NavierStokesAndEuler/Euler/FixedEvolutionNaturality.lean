/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FixedFrameNaturality
public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedEvolution
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1ReconstructionNaturality

@[expose] public section

/-!
# Naturality of the genuine continuous Dirichlet velocity

The constructed coordinate acceleration and its bounded H¹ reconstruction
commute with the same spatial intertwiners as the variational inverse. This
transports the actual continuous history path, including its endpoint values.
-/

noncomputable section

namespace EulerFixedFrameNaturality

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerTimeLp
  EulerVolterraConvolution EulerTimeLpBoundedMap EulerTimeLpGramInverse
  EulerCoerciveProjection EulerTransverseFixedEvolution EulerTimeH1Reconstruction
  EulerTimeH1FrameTransport

variable {U V E F : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (T : ℝ) (hT : 0 ≤ T)

/-- The backward test intertwiner gives the actual adjoint-multiplier identity. -/
theorem adjointMultiplier_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : C(Icc (0 : ℝ) T,U →L[ℝ] E)) (R : C(Icc (0 : ℝ) T,V →L[ℝ] F))
    (hRQ : ∀ t v, Q t (A.adjoint v) = B.adjoint (R t v)) (f : TimeLp T E) :
    (timeMultiplier T hT R).adjoint (timeLift T B f) =
      timeLift T A ((timeMultiplier T hT Q).adjoint f) := by
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left,← adjoint_inner_right, timeLift_adjoint,
    ← timeMultiplier_intertwines T hT A.adjoint B.adjoint R Q hRQ,
    ← adjoint_inner_left,← timeLift_adjoint,adjoint_inner_right]

/-- The true Gram operator commutes with compatible rectangular intertwiners. -/
theorem gramOperator_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : C(Icc (0 : ℝ) T,U →L[ℝ] E)) (R : C(Icc (0 : ℝ) T,V →L[ℝ] F))
    (hQR : ∀ t u, R t (A u) = B (Q t u))
    (hRQ : ∀ t v, Q t (A.adjoint v) = B.adjoint (R t v)) (u : TimeLp T U) :
    gramOperator T hT R (timeLift T A u) = timeLift T A (gramOperator T hT Q u) := by
  change (timeMultiplier T hT R).adjoint (timeMultiplier T hT R (timeLift T A u)) = _
  rw [timeMultiplier_intertwines T hT A B Q R hQR,
    adjointMultiplier_intertwines T hT A B Q R hRQ]
  rfl

/-- The constructed Gram inverse inherits the intertwining identity by its
two-sided inverse property. -/
theorem gramSolver_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : C(Icc (0 : ℝ) T,U →L[ℝ] E)) (R : C(Icc (0 : ℝ) T,V →L[ℝ] F))
    (c : ℝ) (hc : 0 < c) (hQ : ∀ t u, c*‖u‖^2 ≤ ‖Q t u‖^2)
    (d : ℝ) (hd : 0 < d) (hR : ∀ t v, d*‖v‖^2 ≤ ‖R t v‖^2)
    (hQR : ∀ t u, R t (A u) = B (Q t u))
    (hRQ : ∀ t v, Q t (A.adjoint v) = B.adjoint (R t v)) (f : TimeLp T U) :
    gramSolver T hT R d hd hR (timeLift T A f) =
      timeLift T A (gramSolver T hT Q c hc hQ f) := by
  have he := gramOperator_intertwines T hT A B Q R hQR hRQ
    (gramSolver T hT Q c hc hQ f)
  change gramOperator T hT R (timeLift T A (gramSolver T hT Q c hc hQ f)) =
    timeLift T A (gramOperator T hT Q (coerciveInverse (gramOperator T hT Q) c hc
      (gramOperator_coercive T hT Q c hQ) f)) at he
  rw [operator_inverse_apply] at he
  have hi := inverse_operator_apply (gramOperator T hT R) d hd
    (gramOperator_coercive T hT R d hR) (timeLift T A (gramSolver T hT Q c hc hQ f))
  rw [he] at hi
  exact hi

variable (A : U →L[ℝ] V) (B : E →L[ℝ] F)
  (Q Q₁ : C(Icc (0 : ℝ) T,U →L[ℝ] E)) (R R₁ : C(Icc (0 : ℝ) T,V →L[ℝ] F))
  (H : C(Icc (0 : ℝ) T,E →L[ℝ] E)) (J : C(Icc (0 : ℝ) T,F →L[ℝ] F))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t u, c*‖u‖^2 ≤ ‖Q t u‖^2)
  (d : ℝ) (hd : 0 < d) (hR : ∀ t v, d*‖v‖^2 ≤ ‖R t v‖^2)
  (hQtime : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (hRtime : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT R) (R₁ t) (Icc (0 : ℝ) T) t)
  (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
  (hH : ∀ t u, ⟪H t u,u⟫_ℝ ≤ K*‖u‖^2) (hJ : ∀ t v, ⟪J t v,v⟫_ℝ ≤ L*‖v‖^2)
  (hsmall : K*(T^2/2) ≤ 1/2) (hsmall' : L*(T^2/2) ≤ 1/2)
  (hQR : ∀ t u, R t (A u) = B (Q t u))
  (hQR₁ : ∀ t u, R₁ t (A u) = B (Q₁ t u))
  (hRQ : ∀ t v, Q t (A.adjoint v) = B.adjoint (R t v))
  (hRQ₁ : ∀ t v, Q₁ t (A.adjoint v) = B.adjoint (R₁ t v))
  (hHJ : ∀ t u, J t (B u) = B (H t u))

include hQR hQR₁ hRQ hRQ₁ hHJ in
theorem velocityLp_intertwines (f : TimeLp T E) :
    velocityLp T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f) =
      timeLift T A (velocityLp T hT Q Q₁ H c hc hQ hQtime K hK hH hsmall f) := by
  have he := fixedFrameSolver_intertwines T hT A B Q Q₁ R R₁ H J
    c hc hQ d hd hR hQtime hRtime K L hK hL hH hJ hsmall hsmall'
    hQR hQR₁ hRQ hRQ₁ hHJ f
  have he' := congrArg (fun z : zeroTraceDerivatives (U := V) T hT => (z : TimeLp T V)) he
  exact he'.symm

include hQR hQR₁ hRQ hRQ₁ hHJ in
theorem accelerationLp_intertwines (f : TimeLp T E) :
    accelerationLp T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f) =
      timeLift T A (accelerationLp T hT Q Q₁ H c hc hQ hQtime K hK hH hsmall f) := by
  change gramSolver T hT R d hd hR ((timeMultiplier T hT R).adjoint
    (timeLift T B f-(2 : ℝ) • timeMultiplier T hT R₁
      (velocityLp T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f)))) = _
  rw [velocityLp_intertwines T hT A B Q Q₁ R R₁ H J c hc hQ d hd hR hQtime hRtime
    K L hK hL hH hJ hsmall hsmall' hQR hQR₁ hRQ hRQ₁ hHJ,
    timeMultiplier_intertwines T hT A B Q₁ R₁ hQR₁,
    ← map_smul,← map_sub,adjointMultiplier_intertwines T hT A B Q R hRQ,
    gramSolver_intertwines T hT A B Q R c hc hQ d hd hR hQR hRQ]
  rfl

include hQR hQR₁ hRQ hRQ₁ hHJ in
/-- The identity holds at every time, including the endpoint used by the
subsequent forward solve. -/
theorem velocityPath_intertwines (f : TimeLp T E) (t : Icc (0 : ℝ) T) :
    velocityPath T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f) t =
      A (velocityPath T hT Q Q₁ H c hc hQ hQtime K hK hH hsmall f t) := by
  change reconstruction T hT
    (velocityLp T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f),
      accelerationLp T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f)) t = _
  rw [velocityLp_intertwines T hT A B Q Q₁ R R₁ H J c hc hQ d hd hR hQtime hRtime
    K L hK hL hH hJ hsmall hsmall' hQR hQR₁ hRQ hRQ₁ hHJ,
    accelerationLp_intertwines T hT A B Q Q₁ R R₁ H J c hc hQ d hd hR hQtime hRtime
    K L hK hL hH hJ hsmall hsmall' hQR hQR₁ hRQ hRQ₁ hHJ,
    reconstruction_timeLift]
  rfl

end EulerFixedFrameNaturality
