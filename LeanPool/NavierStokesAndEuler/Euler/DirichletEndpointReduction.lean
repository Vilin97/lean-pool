/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

/-!
The endpoint Schur complement of a coercive quadratic form.  The stationary
extension is constructed by the inverse of the form on the closed zero-trace
space.  No stationary extension or Dirichlet-to-Neumann map is an input.
-/

noncomputable section

namespace EulerDirichletEndpointReduction

open InnerProductSpace ContinuousLinearMap EulerCoerciveProjection

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

variable (S : Submodule ℝ E) [CompleteSpace S]
  (A : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
  (hA : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)

/-- The zero-trace correction obtained by a genuine coercive inverse. -/
def correction : E →L[ℝ] S :=
  (projectedInverse S A c hc hA).comp (S.orthogonalProjectionOnto.comp A)

/-- Subtract the solved zero-trace correction from any trial extension. -/
def stationaryPart : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - S.subtypeL.comp (correction S A c hc hA)

theorem stationaryPart_eq (x : E) :
    stationaryPart S A c hc hA x = x - (correction S A c hc hA x : E) := rfl

theorem correction_equation (x : E) (v : S) :
    ⟪A (correction S A c hc hA x : E), (v : E)⟫_ℝ = ⟪A x, (v : E)⟫_ℝ := by
  rw [← projectedOperator_inner S A]
  change ⟪projectedOperator S A
    (projectedInverse S A c hc hA (S.orthogonalProjectionOnto (A x))), v⟫_ℝ = _
  rw [projectedOperator_inverse_apply]
  exact S.inner_orthogonalProjectionOnto_eq_of_mem_right v (A x)

/-- The constructed extension satisfies all zero-trace stationary equations. -/
theorem stationaryPart_orthogonal (x : E) (v : S) :
    ⟪A (stationaryPart S A c hc hA x), (v : E)⟫_ℝ = 0 := by
  rw [stationaryPart_eq, map_sub, inner_sub_left, correction_equation, sub_self]

theorem stationaryPart_sub_mem (x : E) : stationaryPart S A c hc hA x - x ∈ S := by
  rw [stationaryPart_eq]
  have he : x - (correction S A c hc hA x : E) - x =
      -(correction S A c hc hA x : E) := by abel
  rw [he]
  exact S.neg_mem (correction S A c hc hA x).property

theorem stationaryPart_subspace (v : S) : stationaryPart S A c hc hA (v : E) = 0 := by
  have hcorr : correction S A c hc hA (v : E) = v := by
    change coerciveInverse (projectedOperator S A) c hc
      (projectedOperator_coercive S A c hA) (projectedOperator S A v) = v
    exact inverse_operator_apply _ _ _ _ v
  rw [stationaryPart_eq, hcorr, sub_self]

/-- The actual extension depends only on the terminal class of the trial. -/
theorem stationaryPart_eq_of_sub_mem (x y : E) (hxy : x - y ∈ S) :
    stationaryPart S A c hc hA x = stationaryPart S A c hc hA y := by
  have he := stationaryPart_subspace S A c hc hA ⟨x - y, hxy⟩
  change stationaryPart S A c hc hA (x - y) = 0 at he
  rw [map_sub] at he
  exact sub_eq_zero.mp he

/-- Energy splits orthogonally along the stationary extension and zero-trace variations. -/
theorem energy_split (hAs : A.IsSymmetric) (x : E) (v : S) :
    ⟪A (stationaryPart S A c hc hA x + (v : E)),
      stationaryPart S A c hc hA x + (v : E)⟫_ℝ =
        ⟪A (stationaryPart S A c hc hA x), stationaryPart S A c hc hA x⟫_ℝ +
          ⟪A (v : E), (v : E)⟫_ℝ := by
  have hz := stationaryPart_orthogonal S A c hc hA x v
  have hz' : ⟪A (v : E), stationaryPart S A c hc hA x⟫_ℝ = 0 := by
    have hs := hAs (v : E) (stationaryPart S A c hc hA x)
    change ⟪A (v : E), stationaryPart S A c hc hA x⟫_ℝ =
      ⟪(v : E), A (stationaryPart S A c hc hA x)⟫_ℝ at hs
    rw [hs, real_inner_comm]
    exact hz
  simp only [map_add, inner_add_left, inner_add_right, hz, hz', add_zero, zero_add]

/-- The solved extension minimizes the actual quadratic form in its trace class. -/
theorem stationaryPart_minimizes (hAs : A.IsSymmetric) (x : E) :
    ⟪A (stationaryPart S A c hc hA x), stationaryPart S A c hc hA x⟫_ℝ ≤
      ⟪A x, x⟫_ℝ := by
  have he := energy_split S A c hc hA hAs x (correction S A c hc hA x)
  rw [stationaryPart_eq, sub_add_cancel] at he
  have hp := hA (correction S A c hc hA x : E)
  have hc0 := mul_nonneg hc.le (sq_nonneg ‖(correction S A c hc hA x : E)‖)
  rw [stationaryPart_eq]
  linarith

variable [CompleteSpace E]

/-- A prescribed bounded trial lift followed by the actual stationary projection. -/
def endpointExtension (L : U →L[ℝ] E) : U →L[ℝ] E :=
  (stationaryPart S A c hc hA).comp L

/-- The operator representing the actual stationary endpoint energy. -/
def endpointOperator (L : U →L[ℝ] E) : U →L[ℝ] U :=
  (endpointExtension S A c hc hA L).adjoint.comp
    (A.comp (endpointExtension S A c hc hA L))

theorem endpointOperator_inner (L : U →L[ℝ] E) (x y : U) :
    ⟪endpointOperator S A c hc hA L x, y⟫_ℝ =
      ⟪A (endpointExtension S A c hc hA L x), endpointExtension S A c hc hA L y⟫_ℝ := by
  simp only [endpointOperator, comp_apply, adjoint_inner_left]

/-- Positivity is inherited from the actual displacement form. -/
theorem endpointOperator_positive (hAs : A.IsSymmetric) (L : U →L[ℝ] E) :
    (endpointOperator S A c hc hA L).IsPositive := by
  have hp : A.IsPositive := (ContinuousLinearMap.isPositive_iff A).2
    ⟨hAs, fun x => (mul_nonneg hc.le (sq_nonneg ‖x‖)).trans (hA x)⟩
  exact hp.adjoint_conj (endpointExtension S A c hc hA L)

/-- Any explicit admissible trial controls the endpoint quadratic form. -/
theorem endpointOperator_trial_bound (hAs : A.IsSymmetric) (L : U →L[ℝ] E) (x : U) :
    ⟪endpointOperator S A c hc hA L x, x⟫_ℝ ≤ ⟪A (L x), L x⟫_ℝ := by
  rw [endpointOperator_inner]
  exact stationaryPart_minimizes S A c hc hA hAs (L x)

omit [CompleteSpace E] in
/-- A nonnegative quadratic-form bound gives the same operator-norm bound. -/
theorem positive_norm_le_of_quadratic (B : E →L[ℝ] E) (hB : B.IsPositive)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ⟪B x, x⟫_ℝ ≤ C * ‖x‖ ^ 2) : ‖B‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro x y hx hy
  have hx' : ⟪B x, x⟫_ℝ ≤ C := by simpa only [hx, one_pow, mul_one] using hb x
  have hy' : ⟪B y, y⟫_ℝ ≤ C := by simpa only [hy, one_pow, mul_one] using hb y
  have hcross := EulerDNSelection.positive_cross_sq_le B hB x y
  have hprod := mul_le_mul hx' hy' (hB.inner_nonneg_left y) hC
  have hs : |⟪B x, y⟫_ℝ| ^ 2 ≤ C ^ 2 := by
    rw [sq_abs]
    nlinarith only [hcross, hprod]
  have habs := (sq_le_sq₀ (abs_nonneg _) hC).1 hs
  exact (le_abs_self _).trans habs

/-- The endpoint norm is controlled by the energy of the trial, without an inverse norm loss. -/
theorem endpointOperator_norm_le (hAs : A.IsSymmetric) (L : U →L[ℝ] E)
    (C : ℝ) (hC : 0 ≤ C) (hL : ∀ x, ⟪A (L x), L x⟫_ℝ ≤ C * ‖x‖ ^ 2) :
    ‖endpointOperator S A c hc hA L‖ ≤ C := by
  apply positive_norm_le_of_quadratic _ (endpointOperator_positive S A c hc hA hAs L) C hC
  intro x
  exact (endpointOperator_trial_bound S A c hc hA hAs L x).trans (hL x)

end EulerDirichletEndpointReduction
