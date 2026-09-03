/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import LeanPool.ZetaZeros.MontgomeryTaylor.Evaluation
public import LeanPool.ZetaZeros.MontgomeryTaylor.Reduction

/-!
# The Montgomery--Taylor computation

`A(Q_0) = C_MT`: the pair-correlation functional at the self-convolution of the extremal test
function is the Montgomery--Taylor constant. It is proved here rather than assumed.

The three preceding files supply the pieces: the functional is the integral of `f_0` against `G`
(`Reduction`), `G` is constant (`AffineKernel`), and that constant is `C_MT` (`Evaluation`). With
`f_0` of total mass one, the integral collapses to the constant.
-/

@[expose] public section

open MeasureTheory

namespace ZetaZeros

/-- **The Montgomery--Taylor computation** (`lem_montgomery_taylor`). See Montgomery,
*Distribution of the zeros of the Riemann zeta function*, Proc. ICM (Vancouver, 1974), Vol. 1,
379--381. -/
@[zz_tag "lem_montgomery_taylor"]
theorem montgomeryTaylor :
    extremalSelfConv 0 + 2 * ∫ α in (0:ℝ)..1, α * extremalSelfConv α = montgomeryTaylorConst := by
  -- Step 1: reduce the LHS to a single interval integral of f₀·G.
  rw [montgomeryTaylor_step1]
  -- Step 2: G is constant on [-1/2,1/2], equal to G 0, so we may pull it out of the integral:
  --   ∫_{-1/2}^{1/2} f₀(u) G(u) du = ∫_{-1/2}^{1/2} f₀(u) G(0) du = G(0) · ∫_{-1/2}^{1/2} f₀.
  -- Since f₀ vanishes off [-1/2,1/2], ∫_{-1/2}^{1/2} f₀ = ∫_ℝ f₀ = 1 (integral_extremalTest).
  -- Step 3: G(0) = montgomeryTaylorConst (extremalG_zero).
  have hpull :
      (∫ u in (-(1:ℝ)/2)..(1/2), extremalTest u * extremalG u)
        = extremalG 0 * ∫ u in (-(1:ℝ)/2)..(1/2), extremalTest u := by
    -- Rewrite the integrand using extremalG_const on [-1/2,1/2], then factor the constant out.
    rw [show (fun u => extremalTest u * extremalG u)
        = (fun u => extremalTest u * extremalG u) from rfl]
    rw [intervalIntegral.integral_congr
      (g := fun u => extremalG 0 * extremalTest u)
      (f := fun u => extremalTest u * extremalG u) ?_]
    · rw [intervalIntegral.integral_const_mul]
    · intro u hu
      rw [Set.uIcc_of_le (by norm_num : (-(1:ℝ)/2) ≤ 1/2), Set.mem_Icc] at hu
      have : |u| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
      simp only
      rw [extremalG_const this, mul_comm]
  have hmass : (∫ u in (-(1:ℝ)/2)..(1/2), extremalTest u) = 1 := by
    -- Off `[-1/2,1/2]` the integrand vanishes, so the interval integral equals the line
    -- integral, which is one.
    rw [intervalIntegral.integral_of_le (by norm_num : (-(1:ℝ)/2) ≤ 1/2),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero,
      integral_extremalTest]
    intro x hx
    apply extremalTest_eq_zero
    rw [Set.mem_Icc, not_and_or] at hx
    rw [lt_abs]
    rcases hx with h | h
    · right; push Not at h; linarith
    · left; push Not at h; linarith
  rw [hpull, hmass, mul_one, extremalG_zero]

end ZetaZeros
