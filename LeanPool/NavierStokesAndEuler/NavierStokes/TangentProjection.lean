/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Tangent projection and pressure cancellation

This file checks the algebra in manuscript Lemma 8.4, equation (27), and
Appendix A.3.  The vectors are in an arbitrary real inner-product space;
`Kt` denotes the value of the matrix `K` on `t`.  No assertion about the
existence, size, or differentiated estimates of a pulse is made here.
-/

namespace NavierStokes.TangentProjection

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped InnerProductSpace

/-- Orthogonal projection onto the hyperplane perpendicular to `n`, for `n ≠ 0`. -/
def tangentProj (n f : E) : E := f - (⟪n, f⟫_ℝ / ⟪n, n⟫_ℝ) • n

/-- The right-hand side of equation (27), with the viscous coefficient `δ`. -/
def projectedRhs (n n' t Kt f : E) (δ : ℝ) : E :=
  -Kt + ((⟪n, Kt⟫_ℝ - ⟪n', t⟫_ℝ) / ⟪n, n⟫_ℝ) • n - δ • t - tangentProj n f

/-- The real coefficient of the normal vector canceled by pressure. -/
def pressureCoefficient (n n' t Kt f : E) : ℝ :=
  (⟪n, Kt⟫_ℝ - ⟪n', t⟫_ℝ + ⟪n, f⟫_ℝ) / ⟪n, n⟫_ℝ

theorem tangentProj_normal {n : E} (hn : n ≠ 0) (f : E) :
    ⟪n, tangentProj n f⟫_ℝ = 0 := by
  have hn2 : ⟪n, n⟫_ℝ ≠ 0 := inner_self_ne_zero.mpr hn
  simp only [tangentProj, inner_sub_right, inner_smul_right]
  rw [div_mul_cancel₀ _ hn2, sub_self]

theorem tangentProj_of_tangent (n f : E) (hf : ⟪n, f⟫_ℝ = 0) :
    tangentProj n f = f := by
  simp [tangentProj, hf]

theorem tangentProj_idempotent {n : E} (hn : n ≠ 0) (f : E) :
    tangentProj n (tangentProj n f) = tangentProj n f :=
  tangentProj_of_tangent n _ (tangentProj_normal hn f)

/-- The full normal identity includes the damping of an existing tangency defect. -/
theorem normal_projectedRhs {n : E} (hn : n ≠ 0) (n' t Kt f : E) (δ : ℝ) :
    ⟪n, projectedRhs n n' t Kt f δ⟫_ℝ = -⟪n', t⟫_ℝ - δ * ⟪n, t⟫_ℝ := by
  have hn2 : ⟪n, n⟫_ℝ ≠ 0 := inner_self_ne_zero.mpr hn
  simp only [projectedRhs, inner_sub_right, inner_add_right, inner_neg_right,
    inner_smul_right, tangentProj_normal hn, div_mul_cancel₀ _ hn2]
  ring

/-- In particular the projected vector field has the normal derivative required by tangency. -/
theorem normal_projectedRhs_of_tangent {n : E} (hn : n ≠ 0)
    (n' t Kt f : E) (δ : ℝ) (ht : ⟪n, t⟫_ℝ = 0) :
    ⟪n, projectedRhs n n' t Kt f δ⟫_ℝ = -⟪n', t⟫_ℝ := by
  rw [normal_projectedRhs hn, ht]
  ring

/-- Rearranging the projected equation leaves exactly this normal vector. -/
theorem projected_balance (n n' t Kt f : E) (δ : ℝ) :
    projectedRhs n n' t Kt f δ + Kt + δ • t + f =
      pressureCoefficient n n' t Kt f • n := by
  unfold projectedRhs tangentProj pressureCoefficient
  module

/-- A pressure force with the opposite normal coefficient cancels the residual exactly. -/
theorem pressure_cancellation (n n' t Kt f : E) (δ : ℝ) :
    projectedRhs n n' t Kt f δ + Kt + δ • t -
      pressureCoefficient n n' t Kt f • n = -f := by
  have h := projected_balance n n' t Kt f δ
  rw [← h]
  abel

/-- Actual differentiation of tangency gives the normal derivative in Appendix A.3. -/
theorem differentiated_tangency {n t : ℝ → E} {n' t' : E} {x : ℝ}
    (hn : HasDerivAt n n' x) (ht : HasDerivAt t t' x)
    (htangent : ∀ y, ⟪n y, t y⟫_ℝ = 0) :
    ⟪n x, t'⟫_ℝ = -⟪n', t x⟫_ℝ := by
  have hp := hn.inner ℝ ht
  have heq : (fun y => ⟪n y, t y⟫_ℝ) = fun _ => (0 : ℝ) := funext htangent
  rw [heq] at hp
  have hz := hp.unique (hasDerivAt_const x (0 : ℝ))
  linarith

/-- Along any differentiable solution of (27), the tangency defect solves `h' = -δ h`. -/
theorem tangency_defect_derivative {n t : ℝ → E} {n' : E} {x : ℝ}
    {Kt f : E} {δ : ℝ} (hn0 : n x ≠ 0)
    (hn : HasDerivAt n n' x)
    (ht : HasDerivAt t (projectedRhs (n x) n' (t x) Kt f δ) x) :
    HasDerivAt (fun y => ⟪n y, t y⟫_ℝ) (-δ * ⟪n x, t x⟫_ℝ) x := by
  convert! hn.inner ℝ ht using 1
  rw [normal_projectedRhs hn0]
  ring

/-- Integrating-factor proof of zero-data uniqueness for the scalar defect equation.
The primitive `D` is explicit, so no existence assumption is hidden in this statement. -/
theorem scalar_defect_zero (h δ D : ℝ → ℝ)
    (hD : ∀ x, HasDerivAt D (δ x) x)
    (hh : ∀ x, HasDerivAt h (-δ x * h x) x)
    (x₀ : ℝ) (hzero : h x₀ = 0) : ∀ x, h x = 0 := by
  have hp : ∀ x, HasDerivAt (fun y => Real.exp (D y) * h y) 0 x := by
    intro x
    convert! (hD x).exp.mul (hh x) using 1
    ring
  intro x
  have heq := is_const_of_deriv_eq_zero (fun y => (hp y).differentiableAt)
    (fun y => (hp y).deriv) x x₀
  have hz : Real.exp (D x) * h x = 0 := by
    simpa only [hzero, mul_zero] using heq
  exact (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)

/-- Initial tangency persists for a differentiable solution of the projected equation.
This version is global in slot time and assumes an explicit primitive of the damping. -/
theorem tangency_preserved (n n' t Kt f : ℝ → E) (δ D : ℝ → ℝ)
    (hn0 : ∀ x, n x ≠ 0)
    (hn : ∀ x, HasDerivAt n (n' x) x)
    (ht : ∀ x, HasDerivAt t (projectedRhs (n x) (n' x) (t x) (Kt x) (f x) (δ x)) x)
    (hD : ∀ x, HasDerivAt D (δ x) x)
    (x₀ : ℝ) (hzero : ⟪n x₀, t x₀⟫_ℝ = 0) : ∀ x, ⟪n x, t x⟫_ℝ = 0 := by
  exact scalar_defect_zero (fun x => ⟪n x, t x⟫_ℝ) δ D hD
    (fun x => tangency_defect_derivative (hn0 x) (hn x) (ht x)) x₀ hzero

/-- Nonnegative viscosity gives a nonnegative scalar damping coefficient. -/
theorem viscous_coefficient_nonneg (ε k j : ℝ) (n : E) (hε : 0 ≤ ε) :
    0 ≤ ε * k ^ 2 * j ^ 2 * ⟪n, n⟫_ℝ := by
  exact mul_nonneg (mul_nonneg (mul_nonneg hε (sq_nonneg k)) (sq_nonneg j))
    (real_inner_self_nonneg)

/-- The damping term has nonpositive contribution to the energy derivative. -/
theorem damping_dissipative (δ : ℝ) (t : E) (hδ : 0 ≤ δ) :
    ⟪t, -δ • t⟫_ℝ ≤ 0 := by
  rw [inner_smul_right]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) real_inner_self_nonneg

/-- With `c = k j' ≠ 0`, the manuscript's pressure is `i A / c`.
Multiplication by the Fourier gradient `i c` yields `-A`, fixing the sign. -/
theorem complex_pressure_sign (A c : ℂ) (hc : c ≠ 0) :
    (Complex.I * c) * (Complex.I * A / c) = -A := by
  calc
    (Complex.I * c) * (Complex.I * A / c) =
        (Complex.I * Complex.I) * A * (c / c) := by ring
    _ = -A := by rw [Complex.I_mul_I, div_self hc]; ring

end

end NavierStokes.TangentProjection
