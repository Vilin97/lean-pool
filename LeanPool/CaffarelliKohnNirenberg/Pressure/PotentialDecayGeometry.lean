/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Far-field geometry for potential decay

Elementary normed-space inequalities used in the far-field estimates for the
Newtonian potentials of compactly supported data.  Nothing measure-theoretic is
involved: each statement is a triangle-inequality estimate on `Vec3`.
-/

public section

open CKN.Foundation.Parabolic
noncomputable section
namespace CKN

/-- On the support of data carried by the closed ball of radius `R` about `x₀`, a far point
`x` with `2 * R ≤ ‖x - x₀‖` stays at distance at least `‖x - x₀‖ / 2`. -/
theorem far_field_norm_sub_ge {x₀ x y : Vec3} {R : ℝ}
    (hx : 2 * R ≤ ‖x - x₀‖) (hy : ‖y - x₀‖ ≤ R) :
    ‖x - x₀‖ / 2 ≤ ‖x - y‖ := by
  have htri : ‖x - x₀‖ ≤ ‖x - y‖ + ‖y - x₀‖ := by
    calc
      ‖x - x₀‖ = ‖(x - y) + (y - x₀)‖ := by congr 1; abel
      _ ≤ ‖x - y‖ + ‖y - x₀‖ := norm_add_le _ _
  nlinarith only [htri, hy, hx]

/-- On the support of data carried by the closed ball of radius `R` about `x₀`, a far point
`x` with `2 * R ≤ ‖x - x₀‖` is distinct from every such `y`, so the kernel `‖x - y‖⁻¹`
is finite there. -/
theorem far_field_sub_ne_zero {x₀ x y : Vec3} {R : ℝ} (hR : 0 < R)
    (hx : 2 * R ≤ ‖x - x₀‖) (hy : ‖y - x₀‖ ≤ R) :
    x - y ≠ 0 := by
  intro hzero
  have heq : x = y := sub_eq_zero.mp hzero
  have hxy : ‖x - x₀‖ = ‖y - x₀‖ := by rw [heq]
  linarith only [hx, hy, hxy, hR]

/-- A decay estimate centred at `x₀` becomes a decay estimate centred at the origin,
at the cost of doubling the constant and the radius. -/
theorem inv_norm_decay_recentre {h : Vec3 → ℝ} {x₀ : Vec3} {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hdecay : ∀ z : Vec3, 2 * R ≤ ‖z - x₀‖ → |h z| ≤ M * ‖z - x₀‖⁻¹)
    {x : Vec3} (hx : 2 * (2 * R + 2 * ‖x₀‖) ≤ ‖x‖) :
    |h x| ≤ (2 * M) * ‖x‖⁻¹ := by
  have hx' : 4 * R + 4 * ‖x₀‖ ≤ ‖x‖ := by linarith only [hx]
  have h4R : 0 < 4 * R := by positivity
  have h4x₀ : 0 ≤ 4 * ‖x₀‖ := by positivity
  have hxR : 4 * R ≤ ‖x‖ := by linarith only [hx', h4x₀]
  have hx0 : 4 * ‖x₀‖ ≤ ‖x‖ := by linarith only [hx', h4R]
  have hxpos : 0 < ‖x‖ := by linarith only [hxR, hR]
  have hhalf : (3 / 4) * ‖x‖ ≤ ‖x - x₀‖ := by
    have hrev : ‖x‖ - ‖x₀‖ ≤ ‖x - x₀‖ := norm_sub_norm_le x x₀
    have hquarter : ‖x₀‖ ≤ ‖x‖ / 4 := by linarith only [hx0]
    linarith only [hrev, hquarter]
  have hfar : 2 * R ≤ ‖x - x₀‖ := by
    have htwo : 2 * R ≤ (3 / 4) * ‖x‖ := by linarith only [hxR, norm_nonneg x]
    linarith only [htwo, hhalf]
  have hinv : ‖x - x₀‖⁻¹ ≤ ((3 / 4) * ‖x‖)⁻¹ := by
    exact (inv_le_inv₀ (lt_of_lt_of_le (by positivity) hhalf)
      (by positivity : 0 < (3 / 4) * ‖x‖)).2 hhalf
  calc
    |h x| ≤ M * ‖x - x₀‖⁻¹ := hdecay x hfar
    _ ≤ M * ((3 / 4) * ‖x‖)⁻¹ := mul_le_mul_of_nonneg_left hinv hM
    _ = (4 * M / 3) * ‖x‖⁻¹ := by
      rw [mul_inv]
      field_simp [ne_of_gt hxpos]
    _ ≤ (2 * M) * ‖x‖⁻¹ := by
      have hcoef : 4 * M / 3 ≤ 2 * M := by linarith only [hM]
      exact mul_le_mul_of_nonneg_right hcoef (inv_nonneg.mpr (norm_nonneg x))

end CKN
