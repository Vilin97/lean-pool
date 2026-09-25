/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Cylinders

/-!
# Decay

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-! Discrete form of the scale iteration used for a rate strictly below three. -/

theorem geometric_decay_iteration
    {θ σ A B : ℝ} (hθ : 0 ≤ θ) (hσ : 0 ≤ σ) (hθσ : θ < σ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) {a : ℕ → ℝ}
    (_ : 0 ≤ a 0) (haA : a 0 ≤ A)
    (hrec : ∀ n, a (n + 1) ≤ θ * a n + B * σ ^ n) :
    ∀ n, a n ≤ (A + B / (σ - θ)) * σ ^ n := by
  have hgap : 0 < σ - θ := by linarith only [hθσ]
  have hK : 0 ≤ A + B / (σ - θ) := by positivity
  have hB' : B ≤ (σ - θ) * (A + B / (σ - θ)) := by
    rw [mul_add, mul_div_cancel₀ B hgap.ne']
    nlinarith only [hA, hB, hθσ]
  have hAK : A ≤ A + B / (σ - θ) :=
    le_add_of_nonneg_right (div_nonneg hB hgap.le)
  intro n
  induction n with
  | zero =>
      simpa only [pow_zero, mul_one] using haA.trans hAK
  | succ n ih =>
      have hpow : σ ^ (n + 1) = σ ^ n * σ := by
        rw [pow_succ]
      calc
        a (n + 1) ≤ θ * ((A + B / (σ - θ)) * σ ^ n) + B * σ ^ n := by
          exact (hrec n).trans (add_le_add
            (mul_le_mul_of_nonneg_left ih hθ) (le_refl _))
        _ = (θ * (A + B / (σ - θ)) + B) * σ ^ n := by ring
        _ ≤ (σ * (A + B / (σ - θ))) * σ ^ n := by
          have hcoef : θ * (A + B / (σ - θ)) + B ≤
              σ * (A + B / (σ - θ)) := by
            nlinarith only [hB']
          exact mul_le_mul_of_nonneg_right hcoef (pow_nonneg hσ n)
        _ = (A + B / (σ - θ)) * σ ^ (n + 1) := by
          rw [hpow]
          ring

theorem morrey_exponent_from_decay
    {κ β : ℝ} (hκ : 0 < κ) (_ : 0 ≤ β) (hβ5 : β < 5)
    (hβκ : β = 5 - 5 * (6 / 5 : ℝ) / κ) :
    κ = (6 : ℝ) / (5 - β) := by
  have hden : 5 - β ≠ 0 := by linarith only [hβ5]
  apply (eq_div_iff hden).2
  rw [hβκ]
  field_simp [ne_of_gt hκ]
  ring

theorem gradientMorreyExponent
    {τ τ₃ q : ℝ} (_ : 0 < τ) (_ : 0 < τ₃) (hq : 0 < q)
    (hτcond : 1 / τ + 1 / τ₃ > 0) :
    0 < min ((1 / τ + 1 / τ₃)⁻¹) q := by
  have hsum : 0 < 1 / τ + 1 / τ₃ := hτcond
  exact lt_min (inv_pos.mpr hsum) hq

theorem morreyNorm_le_of_cell_bound
    {p q : ℝ} {g : ParabolicPoint → ℝ} {C : ℝ≥0∞}
    (hcell : ∀ z : ParabolicPoint, ∀ r : {r : ℝ // 0 < r},
      morreyCell p q g z r.1 ≤ C) :
    morreyNorm p q g ≤ C := by
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  exact hcell z r

/-! A scale recurrence is the discrete form of the two-scale estimate used for
the pressure gradient.  The parameters are deliberately exposed: the
conversion from a continuous scale to the geometric sequence belongs to the
caller, while this lemma contains the complete iteration. -/
theorem decay_iteration
    {θ σ A B : ℝ} {a : ℕ → ℝ}
    (hθ : 0 ≤ θ) (hσ : 0 ≤ σ) (hθσ : θ < σ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 ≤ a 0) (haA : a 0 ≤ A)
    (hrec : ∀ n, a (n + 1) ≤ θ * a n + B * σ ^ n) :
    ∀ n, a n ≤ (A + B / (σ - θ)) * σ ^ n := by
  exact geometric_decay_iteration hθ hσ hθσ hA hB ha haA hrec

end CKN.Core.Step4
