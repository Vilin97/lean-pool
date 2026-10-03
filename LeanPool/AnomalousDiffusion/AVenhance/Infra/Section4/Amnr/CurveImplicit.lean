/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CurveIntegral

/-! Local smoothness of actual solution curves from their integral equation. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Filter
open scoped Topology
namespace AVenhance.Infra.Section4

/-- A continuous family solving a smooth equation with invertible derivative
is smooth. Only continuity of the solution family is assumed; its derivatives
are obtained from the inverse function theorem and the actual equation. -/
theorem amnr_contDiffAt_of_invertible_left_equation {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {P : F → F} {Q R : E → F} {x : E}
    (hQ : ContinuousAt Q x) (hP : ContDiffAt ℝ (⊤ : ℕ∞) P (Q x))
    (e : F ≃L[ℝ] F) (hD : HasFDerivAt P (e : F →L[ℝ] F) (Q x))
    (hR : ContDiffAt ℝ (⊤ : ℕ∞) R x) (heq : ∀ y, P (Q y) = R y) :
    ContDiffAt ℝ (⊤ : ℕ∞) Q x := by
  have hn : (⊤ : ℕ∞) ≠ (0 : WithTop ℕ∞) := by simp
  let G := hP.localInverse hD hn
  have hG : ContDiffAt ℝ (⊤ : ℕ∞) G (R x) := by
    rw [← heq x]
    exact hP.to_localInverse hD hn
  have hleft : ∀ᶠ z in 𝓝 (Q x), G (P z) = z :=
    (hP.hasStrictFDerivAt' hD hn).eventually_left_inverse
  have hnear : ∀ᶠ y in 𝓝 x, G (R y) = Q y := by
    have hh := hQ.eventually hleft
    exact hh.mono fun y hy => by rw [← heq y]; exact hy
  exact (hG.comp x hR).congr_of_eventuallyEq (hnear.mono fun _ hy => hy.symm)

/-- The actual nonlinear Volterra residual whose zero equation determines
an ODE curve from its constant initial data. -/
def amnrCurveResidual {K E : Type} [TopologicalSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × E → E) (hf : Continuous f) (η : C(K, ℝ))
    (V : C(K, E) →L[ℝ] C(K, E)) (u : C(K, E)) : C(K, E) :=
  u - V (amnrCurveJointCompose f hf η u)

/-- The actual residual inherits all-order smoothness from proved primitive
field bounds and the actual bounded time-integration operator. -/
theorem amnrCurveResidual_contDiff_infty {K E : Type}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤ C)
    (η : C(K, ℝ)) (V : C(K, E) →L[ℝ] C(K, E)) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrCurveResidual f hf.continuous η V) := by
  convert contDiff_id.sub (V.contDiff.comp (amnrCurveJointCompose_contDiff_infty hf hbound η))
      using 1
  rfl

/-- Differentiating the residual gives identity minus the linear Volterra
operator along the actual trajectory. -/
theorem amnrCurveResidual_hasFDerivAt {K E : Type}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ C)
    (η : C(K, ℝ)) (V : C(K, E) →L[ℝ] C(K, E)) (u : C(K, E)) :
    HasFDerivAt (amnrCurveResidual f hf.continuous η V)
      ((1 : C(K, E) →L[ℝ] C(K, E)) - V.comp (amnrCurveOperator (amnrCurveJointCompose
          (amnrStateDerivative f)
        (amnrStateDerivative_contDiff hf).continuous η u))) u := by
  exact (hasFDerivAt_id u).sub
    (V.hasFDerivAt.comp u (amnrCurveJointCompose_hasFDerivAt hf hC hbound η u))

/-- A continuous family solving the actual Volterra equation is smooth in
its initial datum on a short interval. Only the primitive field derivative
and integration length are used to prove invertibility. -/
theorem amnrCurveResidual_solution_contDiffAt {K E : Type}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ × E → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤ C)
    (η : C(K, ℝ)) (V : C(K, E) →L[ℝ] C(K, E)) {M : ℝ} (hM : 0 ≤ M)
    (hstate : ∀ z, ‖amnrStateDerivative f z‖ ≤ M) (hsmall : ‖V‖ * M < 1)
    {Q : E → C(K, E)} {x : E} (hQ : ContinuousAt Q x)
    (heq : ∀ y, amnrCurveResidual f hf.continuous η V (Q y) = ContinuousMap.const K y) :
    ContDiffAt ℝ (⊤ : ℕ∞) Q x := by
  let A := amnrCurveJointCompose (amnrStateDerivative f)
    (amnrStateDerivative_contDiff hf).continuous η (Q x)
  let W := V.comp (amnrCurveOperator A)
  have hA : ‖A‖ ≤ M := by
    apply (ContinuousMap.norm_le A hM).mpr
    intro t
    exact hstate (η t, Q x t)
  have hW : ‖W‖ < 1 := by
    calc
      ‖W‖ ≤ ‖V‖ * ‖amnrCurveOperator A‖ := V.opNorm_comp_le _
      _ ≤ ‖V‖ * M := mul_le_mul_of_nonneg_left ((amnrCurveOperator_norm_le A).trans hA)
          (norm_nonneg V)
      _ < 1 := hsmall
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hW
  let e := ContinuousLinearEquiv.ofUnit u
  have he : (e : C(K, E) →L[ℝ] C(K, E)) = 1 - W := hu
  obtain ⟨C, hC, hCb⟩ := hbound 2
  have hderiv := amnrCurveResidual_hasFDerivAt hf hC hCb η V (Q x)
  change HasFDerivAt (amnrCurveResidual f hf.continuous η V) (1 - W) (Q x) at hderiv
  rw [← he] at hderiv
  exact amnr_contDiffAt_of_invertible_left_equation hQ
    (amnrCurveResidual_contDiff_infty hf hbound η V).contDiffAt e hderiv
    (ContinuousLinearMap.const ℝ K).contDiff.contDiffAt heq

end AVenhance.Infra.Section4
