/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Abstract-real facts for the `cutoff1` source contract

The exponential decay of the corrector after the support of `ξ'_{m,k}` beats every power of
`ε_m⁻¹`.  Pure real-variable lemmas: no objects appear here. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

/-- `y^n e^{-cy} ≤ n!/c^n`. -/
theorem sb_pow_mul_exp_neg_le (n : ℕ) {c : ℝ} (hc : 0 < c) {y : ℝ} (hy : 0 ≤ y) :
    y ^ n * Real.exp (-(c * y)) ≤ (n.factorial : ℝ) / c ^ n := by
  have h := Real.pow_div_factorial_le_exp (c * y) (by positivity) n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 : (c * y) ^ n ≤ n.factorial * Real.exp (c * y) := by
    rw [div_le_iff₀ hfac] at h
    linarith
  have h2 : (c * y) ^ n * Real.exp (-(c * y)) ≤ n.factorial := by
    calc (c * y) ^ n * Real.exp (-(c * y))
        ≤ (n.factorial * Real.exp (c * y)) * Real.exp (-(c * y)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = n.factorial := by
          rw [mul_assoc, ← Real.exp_add]; simp
  rw [le_div_iff₀ (pow_pos hc n)]
  calc y ^ n * Real.exp (-(c * y)) * c ^ n = (c * y) ^ n * Real.exp (-(c * y)) := by
        rw [mul_pow]; ring
    _ ≤ n.factorial := h2

/-- A real power times a decaying exponential is bounded. -/
theorem sb_rpow_mul_exp_neg_le {p c : ℝ} (hp : 0 ≤ p) (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 ≤ y → y ^ p * Real.exp (-(c * y)) ≤ M := by
  refine ⟨1 + (⌈p⌉₊.factorial : ℝ) / c ^ ⌈p⌉₊, by positivity, ?_⟩
  intro y hy
  have hexp1 : Real.exp (-(c * y)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hexp0 : 0 ≤ Real.exp (-(c * y)) := Real.exp_nonneg _
  have hyp : y ^ p ≤ 1 + y ^ ⌈p⌉₊ := by
    by_cases hy1 : y ≤ 1
    · have := Real.rpow_le_one hy hy1 hp
      have : 0 ≤ y ^ ⌈p⌉₊ := by positivity
      linarith
    · rw [not_le] at hy1
      have h := Real.rpow_le_rpow_of_exponent_le hy1.le (Nat.le_ceil p)
      rw [Real.rpow_natCast] at h
      linarith
  calc y ^ p * Real.exp (-(c * y)) ≤ (1 + y ^ ⌈p⌉₊) * Real.exp (-(c * y)) :=
        mul_le_mul_of_nonneg_right hyp hexp0
    _ = Real.exp (-(c * y)) + y ^ ⌈p⌉₊ * Real.exp (-(c * y)) := by ring
    _ ≤ 1 + (⌈p⌉₊.factorial : ℝ) / c ^ ⌈p⌉₊ :=
        add_le_add hexp1 (sb_pow_mul_exp_neg_le _ hc hy)

/-- Exponential decay at the scale `x^{-2δ}` beats `x^{-q}` up to `x^δ`. -/
theorem sb_exp_decay_le {q δ c : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x Z : ℝ, 0 < x → c * x ^ (-(2 * δ)) ≤ Z →
      Real.exp (-Z) * (x ^ q)⁻¹ ≤ M * x ^ δ := by
  obtain ⟨M, hM0, hM⟩ := sb_rpow_mul_exp_neg_le (p := (q + δ) / (2 * δ)) (c := c)
    (by positivity) hc
  refine ⟨M, hM0, ?_⟩
  intro x Z hx hZ
  set y : ℝ := x ^ (-(2 * δ)) with hy
  have hy0 : 0 ≤ y := (Real.rpow_pos_of_pos hx _).le
  have hyp : y ^ ((q + δ) / (2 * δ)) = x ^ (-(q + δ)) := by
    rw [hy, ← Real.rpow_mul hx.le]
    congr 1
    field_simp
  have hexp : Real.exp (-Z) ≤ Real.exp (-(c * y)) := Real.exp_le_exp.2 (by linarith)
  have hxq : (x ^ q)⁻¹ = x ^ (-(q + δ)) * x ^ δ := by
    rw [← Real.rpow_add hx, ← Real.rpow_neg hx.le]
    congr 1
    ring
  have h := hM y hy0
  rw [hyp] at h
  calc Real.exp (-Z) * (x ^ q)⁻¹ ≤ Real.exp (-(c * y)) * (x ^ (-(q + δ)) * x ^ δ) := by
        rw [hxq]
        exact mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = (x ^ (-(q + δ)) * Real.exp (-(c * y))) * x ^ δ := by ring
    _ ≤ M * x ^ δ := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hx.le _)

end AVenhance.Infra.Section5.Contracts
end
