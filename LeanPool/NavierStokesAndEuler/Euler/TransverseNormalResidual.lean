/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
import Mathlib.Tactic.Positivity.Finset

/-!
# Recovering the transverse normal residual

A residual annihilated by the adjoint of a frame spanning `m⊥` is exactly its
normal component. Applying this elementary Hilbert-space fact to the proved
projected coordinate equation gives the pressure coefficient in equation (11).
-/

@[expose] public section


noncomputable section

namespace EulerTransverseNormalResidual

open InnerProductSpace ContinuousLinearMap EulerTransverseGramInverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal scalar normal component, with the source denominator `D_m`. -/
def normalCoefficient (m r : E) : ℝ := ⟪m, r⟫_ℝ / ‖m‖^2

/-- Orthogonality to the tangent hyperplane determines the normal component. -/
theorem eq_normal_of_tangent_orthogonal (m r : E) (hm : m ≠ 0)
    (hr : ∀ x : E, ⟪m, x⟫_ℝ = 0 → ⟪r, x⟫_ℝ = 0) :
    r = normalCoefficient m r • m := by
  let w := r - normalCoefficient m r • m
  have hn : ‖m‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hm)
  have hw : ⟪m, w⟫_ℝ = 0 := by
    simp only [w, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, normalCoefficient]
    field_simp
    ring
  have hz : w = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    change ⟪r - normalCoefficient m r • m, w⟫_ℝ = 0
    rw [inner_sub_left, real_inner_smul_left, hr w hw, hw, mul_zero, sub_self]
  exact sub_eq_zero.mp hz

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [CompleteSpace U] [CompleteSpace E]

/-- A frame spanning the tangent hyperplane detects exactly the normal residual. -/
theorem eq_normal_of_adjoint_zero (Q : U →L[ℝ] E) (m r : E) (hm : m ≠ 0)
    (hRange : ∀ η, ⟪m, η⟫_ℝ = 0 → ∃ x : U, Q x = η)
    (hr : Q.adjoint r = 0) : r = normalCoefficient m r • m := by
  apply eq_normal_of_tangent_orthogonal m r hm
  intro η hη
  obtain ⟨x, rfl⟩ := hRange η hη
  rw [← adjoint_inner_left, hr, inner_zero_left]

/-- Equation (10), together with `Q_t = M Q`, gives the exact source pressure
coefficient and velocity equation (11). No pressure residual is assumed. -/
theorem physical_velocity_balance (Q Q₁ : U →L[ℝ] E) (M : E →L[ℝ] E)
    (m : E) (hm : m ≠ 0)
    (hTangent : ∀ x, ⟪m, Q x⟫_ℝ = 0)
    (hRange : ∀ η, ⟪m, η⟫_ℝ = 0 → ∃ x : U, Q x = η)
    (hflow : Q₁ = M.comp Q) (v a : U) (f : E)
    (heq : gram Q a = Q.adjoint (f - (2 : ℝ) • Q₁ v)) :
    (Q₁ v + Q a) + M (Q v) +
      ((⟪m, f⟫_ℝ - 2 * ⟪m, M (Q v)⟫_ℝ) / ‖m‖^2) • m = f := by
  let r := f - (Q₁ v + Q a) - M (Q v)
  have hQr : Q.adjoint r = 0 := by
    dsimp only [r]
    rw [hflow] at heq ⊢
    simp only [gram, comp_apply, map_sub, map_add, map_smul] at heq ⊢
    linear_combination (norm := module) -heq
  have hr := eq_normal_of_adjoint_zero Q m r hm hRange hQr
  have hco : normalCoefficient m r = (⟪m, f⟫_ℝ - 2 * ⟪m, M (Q v)⟫_ℝ) / ‖m‖^2 := by
    simp only [normalCoefficient, r, inner_sub_right, inner_add_right, hTangent,
      add_zero, hflow, comp_apply]
    ring
  rw [hco] at hr
  calc
    (Q₁ v + Q a) + M (Q v) +
        ((⟪m, f⟫_ℝ - 2 * ⟪m, M (Q v)⟫_ℝ) / ‖m‖^2) • m =
        (Q₁ v + Q a) + M (Q v) + r := by rw [hr]
    _ = f := by dsimp only [r]; abel

end EulerTransverseNormalResidual
