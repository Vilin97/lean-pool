/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
The Hilbert-space inverse used for the packet pressure equation.
Invertibility is constructed from Lax--Milgram, not assumed.  The coercivity
hypothesis is an explicit quadratic inequality on the given bounded operator.
This does not assert the Fourier or Sobolev realization of the pressure space.
-/

@[expose] public section

noncomputable section

namespace EulerCoerciveProjection

open InnerProductSpace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bounded bilinear form associated with an operator and the real inner product. -/
def operatorBilinear (T : E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ).comp T

lemma operatorBilinear_coercive (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) :
    IsCoercive (operatorBilinear T) := by
  refine ⟨c, hc, fun x => ?_⟩
  change c * ‖x‖ * ‖x‖ ≤ ⟪T x, x⟫_ℝ
  simpa only [pow_two, mul_assoc] using hT x

section Complete

variable [CompleteSpace E]

/-- Lax--Milgram constructs an equivalence from the operator's coercivity. -/
def coerciveEquiv (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) : E ≃L[ℝ] E :=
  (operatorBilinear_coercive T c hc hT).continuousLinearEquivOfBilin

@[simp]
theorem coerciveEquiv_apply (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (x : E) :
    coerciveEquiv T c hc hT x = T x := by
  apply ext_inner_right ℝ
  intro y
  exact (operatorBilinear_coercive T c hc hT).continuousLinearEquivOfBilin_apply x y

/-- The inverse operator constructed from the coercive Lax–Milgram equivalence. -/
def coerciveInverse (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) : E →L[ℝ] E :=
  (coerciveEquiv T c hc hT).symm.toContinuousLinearMap

@[simp]
theorem operator_inverse_apply (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (y : E) :
    T (coerciveInverse T c hc hT y) = y := by
  change T ((coerciveEquiv T c hc hT).symm y) = y
  rw [← coerciveEquiv_apply T c hc hT]
  exact (coerciveEquiv T c hc hT).apply_symm_apply y

@[simp]
theorem inverse_operator_apply (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (x : E) :
    coerciveInverse T c hc hT (T x) = x := by
  change (coerciveEquiv T c hc hT).symm (T x) = x
  rw [← coerciveEquiv_apply T c hc hT]
  exact (coerciveEquiv T c hc hT).symm_apply_apply x

theorem coerciveInverse_apply_norm_le (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (y : E) :
    ‖coerciveInverse T c hc hT y‖ ≤ c⁻¹ * ‖y‖ := by
  let x := coerciveInverse T c hc hT y
  change ‖x‖ ≤ c⁻¹ * ‖y‖
  by_cases hx : x = 0
  · simp only [hx, norm_zero]
    positivity
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb : c * ‖x‖ ≤ ‖y‖ := by
    apply (mul_le_mul_iff_left₀ hn).mp
    calc
      c * ‖x‖ * ‖x‖ = c * ‖x‖ ^ 2 := by ring
      _ ≤ ⟪T x, x⟫_ℝ := hT x
      _ = ⟪y, x⟫_ℝ := by rw [show T x = y from operator_inverse_apply T c hc hT y]
      _ ≤ ‖y‖ * ‖x‖ := real_inner_le_norm y x
  have := (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hb)
  simpa only [div_eq_mul_inv, mul_comm] using this

theorem coerciveInverse_norm_le (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) :
    ‖coerciveInverse T c hc hT‖ ≤ c⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hc.le)
  exact coerciveInverse_apply_norm_le T c hc hT

/-- The exact resolvent identity for the inverses constructed by Lax--Milgram. -/
theorem coerciveInverse_resolvent (T U : E →L[ℝ] E) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ)
    (hU : ∀ x, d * ‖x‖ ^ 2 ≤ ⟪U x, x⟫_ℝ) :
    coerciveInverse T c hc hT - coerciveInverse U d hd hU =
      (coerciveInverse T c hc hT).comp
        ((U - T).comp (coerciveInverse U d hd hU)) := by
  ext y
  apply (coerciveEquiv T c hc hT).injective
  simp only [coerciveEquiv_apply, sub_apply,
    ContinuousLinearMap.comp_apply, map_sub, operator_inverse_apply]

theorem coerciveInverse_norm_sub_le (T U : E →L[ℝ] E) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ)
    (hU : ∀ x, d * ‖x‖ ^ 2 ≤ ⟪U x, x⟫_ℝ) :
    ‖coerciveInverse T c hc hT - coerciveInverse U d hd hU‖ ≤
      c⁻¹ * d⁻¹ * ‖U - T‖ := by
  rw [coerciveInverse_resolvent T U c d hc hd hT hU]
  calc
    ‖(coerciveInverse T c hc hT).comp
        ((U - T).comp (coerciveInverse U d hd hU))‖ ≤
        ‖coerciveInverse T c hc hT‖ *
          ‖(U - T).comp (coerciveInverse U d hd hU)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖coerciveInverse T c hc hT‖ *
        (‖U - T‖ * ‖coerciveInverse U d hd hU‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ c⁻¹ * (‖U - T‖ * d⁻¹) :=
      mul_le_mul (coerciveInverse_norm_le T c hc hT)
        (mul_le_mul_of_nonneg_left (coerciveInverse_norm_le U d hd hU) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (inv_nonneg.2 hc.le)
    _ = c⁻¹ * d⁻¹ * ‖U - T‖ := by ring

end Complete

section Subspace

variable (S : Submodule ℝ E) [CompleteSpace S]

/-- Orthogonal projection of the given ambient operator, restricted to the subspace. -/
def projectedOperator (G : E →L[ℝ] E) : S →L[ℝ] S :=
  S.orthogonalProjectionOnto.comp (G.comp S.subtypeL)

theorem projectedOperator_inner (G : E →L[ℝ] E) (x y : S) :
    ⟪projectedOperator S G x, y⟫_ℝ = ⟪G (x : E), (y : E)⟫_ℝ := by
  exact S.inner_orthogonalProjectionOnto_eq_of_mem_right y (G x)

theorem projectedOperator_coercive (G : E →L[ℝ] E) (c : ℝ)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (x : S) :
    c * ‖x‖ ^ 2 ≤ ⟪projectedOperator S G x, x⟫_ℝ := by
  rw [projectedOperator_inner]
  exact hG x

/-- The projected-pressure inverse, constructed by applying Lax--Milgram on `S`. -/
def projectedInverse (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) : S →L[ℝ] S :=
  coerciveInverse (projectedOperator S G) c hc (projectedOperator_coercive S G c hG)

@[simp]
theorem projectedOperator_inverse_apply (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (f : S) :
    projectedOperator S G (projectedInverse S G c hc hG f) = f :=
  operator_inverse_apply (projectedOperator S G) c hc (projectedOperator_coercive S G c hG) f

theorem projectedInverse_norm_le (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) :
    ‖projectedInverse S G c hc hG‖ ≤ c⁻¹ :=
  coerciveInverse_norm_le (projectedOperator S G) c hc (projectedOperator_coercive S G c hG)

@[simp]
theorem projectedOperator_sub (G H : E →L[ℝ] E) :
    projectedOperator S (G - H) = projectedOperator S G - projectedOperator S H := by
  ext x
  simp [projectedOperator]

theorem projectedOperator_norm_le (G : E →L[ℝ] E) :
    ‖projectedOperator S G‖ ≤ ‖G‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    ‖projectedOperator S G x‖ ≤ ‖G (x : E)‖ :=
      S.norm_orthogonalProjectionOnto_apply_le (G x)
    _ ≤ ‖G‖ * ‖x‖ := G.le_opNorm x

theorem projectedInverse_norm_sub_le (G H : E →L[ℝ] E) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ)
    (hH : ∀ x, d * ‖x‖ ^ 2 ≤ ⟪H x, x⟫_ℝ) :
    ‖projectedInverse S G c hc hG - projectedInverse S H d hd hH‖ ≤
      c⁻¹ * d⁻¹ * ‖H - G‖ := by
  calc
    ‖projectedInverse S G c hc hG - projectedInverse S H d hd hH‖ ≤
        c⁻¹ * d⁻¹ * ‖projectedOperator S H - projectedOperator S G‖ :=
      coerciveInverse_norm_sub_le (projectedOperator S G) (projectedOperator S H)
        c d hc hd (projectedOperator_coercive S G c hG)
        (projectedOperator_coercive S H d hH)
    _ = c⁻¹ * d⁻¹ * ‖projectedOperator S (H - G)‖ := by rw [projectedOperator_sub]
    _ ≤ c⁻¹ * d⁻¹ * ‖H - G‖ :=
      mul_le_mul_of_nonneg_left (projectedOperator_norm_le S (H - G))
        (mul_nonneg (inv_nonneg.2 hc.le) (inv_nonneg.2 hd.le))

/-- Solves the projected equation with an ambient forcing vector. -/
def pressureSolver (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) : E →L[ℝ] S :=
  (projectedInverse S G c hc hG).comp S.orthogonalProjectionOnto

theorem pressureSolver_equation (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (f : E) :
    S.orthogonalProjectionOnto (G (pressureSolver S G c hc hG f : E)) =
      S.orthogonalProjectionOnto f :=
  projectedOperator_inverse_apply S G c hc hG (S.orthogonalProjectionOnto f)

theorem pressureSolver_apply_norm_le (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (f : E) :
    ‖pressureSolver S G c hc hG f‖ ≤ c⁻¹ * ‖f‖ := by
  calc
    ‖pressureSolver S G c hc hG f‖ ≤ c⁻¹ * ‖S.orthogonalProjectionOnto f‖ :=
      coerciveInverse_apply_norm_le (projectedOperator S G) c hc
        (projectedOperator_coercive S G c hG) (S.orthogonalProjectionOnto f)
    _ ≤ c⁻¹ * ‖f‖ :=
      mul_le_mul_of_nonneg_left (S.norm_orthogonalProjectionOnto_apply_le f)
        (inv_nonneg.2 hc.le)

/-- Existence and uniqueness of the pressure variable in the closed subspace. -/
theorem existsUnique_projected_solution (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (f : E) :
    ∃! p : S, S.orthogonalProjectionOnto (G (p : E)) =
      S.orthogonalProjectionOnto f := by
  refine ⟨pressureSolver S G c hc hG f, pressureSolver_equation S G c hc hG f, ?_⟩
  intro p hp
  apply (coerciveEquiv (projectedOperator S G) c hc
    (projectedOperator_coercive S G c hG)).injective
  simp only [coerciveEquiv_apply]
  change S.orthogonalProjectionOnto (G (p : E)) =
    S.orthogonalProjectionOnto (G (pressureSolver S G c hc hG f : E))
  rw [hp, pressureSolver_equation]

end Subspace

/-- Closedness supplies completeness; no inverse or existence hypothesis is assumed. -/
theorem closed_subspace_inverse [CompleteSpace E] (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) :
    ∃ I : S →L[ℝ] S,
      (∀ f y : S, ⟪G (I f : E), (y : E)⟫_ℝ = ⟪(f : E), (y : E)⟫_ℝ) ∧
      ‖I‖ ≤ c⁻¹ := by
  let : CompleteSpace S := hS.completeSpace_coe
  refine ⟨projectedInverse S G c hc hG, ?_, projectedInverse_norm_le S G c hc hG⟩
  intro f y
  rw [← projectedOperator_inner S G (projectedInverse S G c hc hG f) y,
    projectedOperator_inverse_apply]
  rfl

end EulerCoerciveProjection
