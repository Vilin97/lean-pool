/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Fast geometric-decay iteration lemma

A standalone real-analysis prelude for a De Giorgi / Stampacchia iteration.  If a
nonnegative sequence `Y` starting below `1` satisfies a superlinear recursion
`Y (n+1) ≤ A · Bⁿ · (Y n)^{1+β}` with the compatibility bound
`A ≤ B^{-1/β}`, then `Y n ≤ B^{-n/β}` for every `n`, and (when `1 < B`) `Y → 0`.

All exponents are real (`Real.rpow`).  No `sorry`, no axioms, no heartbeat
overrides.
-/

@[expose] public section

namespace Homogenization

open Filter Topology

/-- **Fast geometric decay.**  A nonnegative sequence obeying a
superlinear recursion with a compatible leading constant decays at least like the
geometric rate `B^{-n/β}`. -/
theorem iteration_geometric_decay
    {Y : ℕ → ℝ} {A B β : ℝ}
    (hY0 : Y 0 ≤ 1) (hYnn : ∀ n, 0 ≤ Y n) (hβ : 0 < β)
    (hB : 1 ≤ B) (hA : 0 ≤ A) (hAB : A ≤ B ^ (-(1 / β)))
    (hrec : ∀ n, Y (n + 1) ≤ A * B ^ (n : ℝ) * Y n ^ (1 + β)) :
    ∀ n, Y n ≤ B ^ (-(n : ℝ) / β) := by
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB
  have hB0' : (0 : ℝ) ≤ B := hB0.le
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  intro n
  induction n with
  | zero =>
      simp only [Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero]
      exact hY0
  | succ n ih =>
      have h1β : (0 : ℝ) ≤ 1 + β := by linarith
      -- monotonicity of `t ↦ t^{1+β}` applied to the inductive hypothesis
      have hstep : Y n ^ (1 + β) ≤ (B ^ (-(n : ℝ) / β)) ^ (1 + β) :=
        Real.rpow_le_rpow (hYnn n) ih h1β
      have hpow : (B ^ (-(n : ℝ) / β)) ^ (1 + β) = B ^ ((-(n : ℝ) / β) * (1 + β)) :=
        (Real.rpow_mul hB0' _ _).symm
      have hfac : 0 ≤ A * B ^ (n : ℝ) := mul_nonneg hA (Real.rpow_nonneg hB0' _)
      have hexp : (n : ℝ) + (-(n : ℝ) / β) * (1 + β) = -(n : ℝ) / β := by
        field_simp
        ring
      calc
        Y (n + 1) ≤ A * B ^ (n : ℝ) * Y n ^ (1 + β) := hrec n
        _ ≤ A * B ^ (n : ℝ) * (B ^ (-(n : ℝ) / β)) ^ (1 + β) :=
              mul_le_mul_of_nonneg_left hstep hfac
        _ = A * B ^ (-(n : ℝ) / β) := by
              rw [hpow, mul_assoc, ← Real.rpow_add hB0, hexp]
        _ ≤ B ^ (-(1 / β)) * B ^ (-(n : ℝ) / β) :=
              mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hB0' _)
        _ = B ^ (-((n + 1 : ℕ) : ℝ) / β) := by
              rw [← Real.rpow_add hB0]
              congr 1
              push_cast
              ring

/-- **Fast geometric decay (corollary).**  Under the same recursion with a genuine
contraction rate `1 < B`, the sequence tends to `0`. -/
theorem iteration_geometric_decay_tendsto_zero
    {Y : ℕ → ℝ} {A B β : ℝ}
    (hY0 : Y 0 ≤ 1) (hYnn : ∀ n, 0 ≤ Y n) (hβ : 0 < β)
    (hB : 1 < B) (hA : 0 ≤ A) (hAB : A ≤ B ^ (-(1 / β)))
    (hrec : ∀ n, Y (n + 1) ≤ A * B ^ (n : ℝ) * Y n ^ (1 + β)) :
    Tendsto Y atTop (𝓝 0) := by
  have hbound := iteration_geometric_decay hY0 hYnn hβ hB.le hA hAB hrec
  have hB0' : (0 : ℝ) ≤ B := (lt_trans one_pos hB).le
  set r : ℝ := B ^ (-(1 / β)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hB0' _
  have hr1 : r < 1 := by
    rw [hr]
    refine Real.rpow_lt_one_of_one_lt_of_neg hB ?_
    have : (0 : ℝ) < 1 / β := by positivity
    linarith
  have hgeom : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hEq : ∀ n : ℕ, B ^ (-(n : ℝ) / β) = r ^ n := by
    intro n
    rw [hr, ← Real.rpow_natCast (B ^ (-(1 / β))) n, ← Real.rpow_mul hB0']
    congr 1
    ring
  refine squeeze_zero hYnn (fun n => ?_) hgeom
  rw [← hEq n]
  exact hbound n

end Homogenization
