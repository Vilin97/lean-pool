/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.FstarDefs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! the proof notes, 5.4 (Lemma 12), the weight `W`:
`W = W2` on `[0, ∞)` (Lean's `arctan (1/0) = 0` convention included), `W2 0 = 0`, and
`W2′(x) = (2/3)(2·atan x + π/4 − atan(x/5)/2) ≥ 0` for `x ≥ 0`, which is the addendum's
`W′ = (2/3)(π − 2 atan(1/x) + atan(5/x)/2)` after `atan(1/x) = π/2 − atan x`. Written from
scratch. -/

public section

open Real
namespace Zeta32.Fstar
noncomputable section

/-- Closed expression for the potential weight on the nonnegative real axis. -/
def W2 (x : ℝ) : ℝ :=
  (2/3) * (2 * x * arctan x - log (1 + x^2) + π/4 * x - x/2 * arctan (x/5) + 5/4 * log (1 + x^2/25))

theorem Wt_eq_W2 {x : ℝ} (hx : 0 ≤ x) : Wt x = W2 x := by
  rcases hx.lt_or_eq with hx | hx
  · have h1 : arctan (1/x) = π/2 - arctan x := by
      rw [one_div]; exact arctan_inv_of_pos hx
    have h5 : arctan (5/x) = π/2 - arctan (x/5) := by
      rw [show 5/x = (x/5)⁻¹ by field_simp]; exact arctan_inv_of_pos (by positivity)
    unfold Wt W2; rw [h1, h5]; ring
  · subst hx; simp [Wt, W2]

theorem hasDerivAt_W2 (x : ℝ) :
    HasDerivAt W2 ((2/3) * (2 * arctan x + π/4 - arctan (x/5) / 2)) x := by
  have hq1 : (0:ℝ) < 1 + x^2 := by positivity
  have hq5 : (0:ℝ) < 1 + x^2/25 := by positivity
  have d1 : HasDerivAt (fun y : ℝ => 2 * y * arctan y) (2 * arctan x + 2 * x * (1 / (1 + x^2)))
    x := by
    have := ((hasDerivAt_id x).const_mul 2).mul (hasDerivAt_arctan x)
    convert this using 1
    · funext y; simp
    · simp
  have d2 : HasDerivAt (fun y : ℝ => log (1 + y^2)) ((2 * x) / (1 + x^2)) x := by
    have := ((hasDerivAt_pow 2 x).const_add 1).log hq1.ne'
    convert this using 1; ring
  have d3 : HasDerivAt (fun y : ℝ => π/4 * y) (π/4) x := by
    simpa using (hasDerivAt_id x).const_mul (π/4)
  have d4 : HasDerivAt (fun y : ℝ => y/2 * arctan (y/5))
      (1/2 * arctan (x/5) + x/2 * (1 / (1 + (x/5)^2) * (1/5))) x := by
    have := ((hasDerivAt_id x).div_const 2).mul (((hasDerivAt_id x).div_const 5).arctan)
    convert this using 1
    · funext y; simp
    · simp
  have d5 : HasDerivAt (fun y : ℝ => 5/4 * log (1 + y^2/25)) (5/4 * ((2 * x / 25) / (1 +
    x^2/25))) x := by
    have := ((((hasDerivAt_pow 2 x).div_const 25).const_add 1).log hq5.ne').const_mul (5/4)
    convert this using 1; ring
  have := ((((d1.sub d2).add d3).sub d4).add d5).const_mul (2/3)
  convert this using 1
  · funext y; simp [W2]
  · field_simp
    ring

theorem continuous_W2 : Continuous W2 := by
  unfold W2
  have h1 : ∀ y : ℝ, 1 + y^2 ≠ 0 := fun y => by positivity
  have h5 : ∀ y : ℝ, 1 + y^2/25 ≠ 0 := fun y => by positivity
  fun_prop (disch := assumption)

theorem W2_monotoneOn : MonotoneOn W2 (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) continuous_W2.continuousOn
    (fun x _ => (hasDerivAt_W2 x).hasDerivWithinAt)
  intro x hx
  rw [interior_Ici] at hx
  have h1 : 0 ≤ arctan x := arctan_nonneg.mpr hx.le
  have h2 := arctan_lt_pi_div_two (x/5)
  nlinarith

theorem Wt_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : Wt x ≤ Wt y := by
  rw [Wt_eq_W2 hx, Wt_eq_W2 (hx.trans hxy)]
  exact W2_monotoneOn hx (hx.trans hxy) hxy

theorem Wt_zero : Wt 0 = 0 := by simp [Wt]

theorem Wt_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Wt x := by
  simpa [Wt_zero] using Wt_mono le_rfl hx

end
end Zeta32.Fstar
