/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# Elementary facts on scalar actions and continuous linear functionals

## Main results

* `Complex.smul_eq_re_smul_add_im_smul`: A complex scalar acts on a vector of a complex module
  through its real and imaginary parts.
* `ContinuousLinearMap.exists_apply_eq_one_of_ne_zero`: A nonzero continuous linear functional
  attains the value `1` on a nonzero vector.
* `ContinuousLinearMap.exists_pos_smul_eq_of_neg_imp_nonpos`: Inclusion of negative half-spaces
  forces two nonzero real continuous linear functionals to be positively proportional.
-/

public section

/-- A complex scalar acts on a vector through its real and imaginary parts. -/
theorem Complex.smul_eq_re_smul_add_im_smul {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ζ : ℂ) (c : E) : ζ • c = ζ.re • c + ζ.im • (Complex.I • c) := by
  conv_lhs => rw [← Complex.re_add_im ζ]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

/-- A nonzero continuous linear functional attains the value `1` on a nonzero vector. -/
theorem ContinuousLinearMap.exists_apply_eq_one_of_ne_zero {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {ℓ : E →L[𝕜] 𝕜}
    (hℓ : ℓ ≠ 0) : ∃ ν, ℓ ν = 1 ∧ 0 < ‖ν‖ := by
  have hℓ' : (ℓ : E →ₗ[𝕜] 𝕜) ≠ 0 := fun h => hℓ (ContinuousLinearMap.coe_injective h)
  obtain ⟨ν, hν⟩ := LinearMap.surjective hℓ' 1
  refine ⟨ν, hν, norm_pos_iff.mpr fun h0 => ?_⟩
  rw [h0, map_zero] at hν
  exact zero_ne_one hν

/-- A nonzero functional whose closed negative half-space contains the open negative half-space of
another nonzero functional is a positive multiple of it. -/
theorem ContinuousLinearMap.exists_pos_smul_eq_of_neg_imp_nonpos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ℓ₁ ℓ₂ : E →L[ℝ] ℝ}
    (h₁ : ℓ₁ ≠ 0) (h₂ : ℓ₂ ≠ 0)
    (h : ∀ v, ℓ₂ v < 0 → ℓ₁ v ≤ 0) : ∃ c : ℝ, 0 < c ∧ ℓ₁ = c • ℓ₂ := by
  obtain ⟨u, hu⟩ : ∃ u, ℓ₂ u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h₂ (ContinuousLinearMap.ext hcon)
  set u₀ : E := (1 / ℓ₂ u) • u with hu₀
  have hℓu₀ : ℓ₂ u₀ = 1 := by rw [hu₀, map_smul, smul_eq_mul, one_div, inv_mul_cancel₀ hu]
  set c := ℓ₁ u₀ with hc
  -- the kernel of `ℓ₂` is contained in the kernel of `ℓ₁`
  have hker : ∀ v, ℓ₂ v = 0 → ℓ₁ v = 0 := by
    intro v hv
    have hle : ∀ ε : ℝ, 0 < ε → ℓ₁ v ≤ ε * c := by
      intro ε hε
      have := h (v - ε • u₀) (by rw [map_sub, map_smul, hv, hℓu₀, smul_eq_mul]; linarith)
      rw [map_sub, map_smul, smul_eq_mul] at this
      linarith
    have hge : ∀ ε : ℝ, 0 < ε → -(ε * c) ≤ ℓ₁ v := by
      intro ε hε
      have := h (-v - ε • u₀) (by rw [map_sub, map_neg, map_smul, hv, hℓu₀, smul_eq_mul]; linarith)
      rw [map_sub, map_neg, map_smul, smul_eq_mul] at this
      linarith
    have h1 : ℓ₁ v ≤ 0 := le_of_forall_pos_le_add fun ε hε => by
      have := hle (ε / (|c| + 1)) (by positivity)
      have hcb : ε / (|c| + 1) * c ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [le_abs_self c, abs_nonneg c]
      linarith
    have h2 : 0 ≤ ℓ₁ v := by
      by_contra hneg
      push Not at hneg
      have := hge (-ℓ₁ v / (2 * (|c| + 1))) (div_pos (by linarith) (by positivity))
      have hcb : -ℓ₁ v / (2 * (|c| + 1)) * c ≤ -ℓ₁ v / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [le_abs_self c, abs_nonneg c]
      linarith
    exact le_antisymm h1 h2
  have heq : ℓ₁ = c • ℓ₂ := by
    ext v
    have hv : ℓ₂ (v - ℓ₂ v • u₀) = 0 := by rw [map_sub, map_smul, hℓu₀, smul_eq_mul, mul_one,
      sub_self]
    have := hker _ hv
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
    rw [this, smul_apply, smul_eq_mul, hc, mul_comm]
  have hc0 : 0 ≤ c := by
    have := h (-u₀) (by rw [map_neg, hℓu₀]; norm_num)
    rw [map_neg] at this
    linarith
  refine ⟨c, lt_of_le_of_ne hc0 fun hzero => h₁ ?_, heq⟩
  rw [heq, ← hzero, zero_smul]

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
