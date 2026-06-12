/-
Copyright (c) 2026 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import Mathlib.Analysis.Calculus.Deriv.ZPow
import LeanPool.LeanLJ.Function

/-!
# Analytic properties of the Lennard-Jones potential

This file proves continuity and differentiability of the truncated Lennard-Jones pair
potential on its interaction domain, computes its derivative explicitly on the open
interaction region (`ljp_hasDerivAt`, `ljp_deriv`), and shows that two algebraic
formulations of the potential agree.
-/

namespace LeanLJ

lemma lj_pow_12' (σ r : ℝ) (h : r ≠ 0) :
    deriv (fun r => σ ^ 12 * r ^ (-12 : ℤ)) r = σ ^ 12 * (-12 : ℤ) * r ^ (-13 : ℤ) := by
  have hd : DifferentiableAt ℝ (fun r : ℝ => r ^ (-12 : ℤ)) r :=
    (differentiableAt_id).zpow (Or.inl h)
  rw [deriv_const_mul _ hd, deriv_zpow, show (-12 - 1) = (-13 : ℤ) by ring]
  ring

lemma lj_pow_6' (σ r : ℝ) (h : r ≠ 0) :
    deriv (fun r => σ ^ 6 * r ^ (-6 : ℤ)) r = σ ^ 6 * (-6 : ℤ) * r ^ (-7 : ℤ) := by
  have hd : DifferentiableAt ℝ (fun r : ℝ => r ^ (-6 : ℤ)) r :=
    (differentiableAt_id).zpow (Or.inl h)
  rw [deriv_const_mul _ hd, deriv_zpow, show (-6 - 1) = (-7 : ℤ) by ring]
  ring

lemma scale_continuous (ε σ : ℝ) :
  ContinuousOn (fun r => 4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6)) {r | r > 0} := by
  apply ContinuousOn.mul
  · exact continuous_const.continuousOn
  · apply ContinuousOn.sub <;>
    · apply ContinuousOn.pow
      apply ContinuousOn.div
      · exact continuous_const.continuousOn
      · exact continuous_id.continuousOn
      · exact fun x a => Ne.symm (ne_of_lt a)

theorem Lj_eq (r r_c ε σ : ℝ) : Ljp r r_c ε σ = LJ r r_c ε σ := by
  unfold Ljp
  unfold LJ
  simp
  ring_nf

theorem cutoff_behavior (r r_c ε σ : ℝ)
    (h : r > r_c) : ljReal r r_c ε σ = 0 := by
  unfold ljReal
  simp [if_neg (not_le_of_gt h)]


theorem ljp_zero_on_tail (r_c ε σ : ℝ) :
  ∀ r, r > r_c → ljReal r r_c ε σ = 0 := by
  intro r h
  unfold ljReal
  simp only [if_neg (not_le_of_gt h)]


theorem ljp_eq_le {r_c ε σ : ℝ} :
  ∀ r ∈ {r | r > 0 ∧ r ≤ r_c }, ljReal r r_c ε σ = 4 * ε * ((σ / r)^12 - (σ / r)^6) := by
  intro r hr
  have h_r_le_rc : r ≤ r_c := hr.2
  unfold ljReal
  rw [if_pos h_r_le_rc]
  ring

theorem ljp_eq_gt (r_c ε σ : ℝ) : ∀ r ∈ {r | r > r_c ∧ r > 0}, ljReal r r_c ε σ = 0 := by
  intro r hr
  have h_r_gt_rc : r > r_c := hr.1
  unfold ljReal
  rw [if_neg (not_le_of_gt h_r_gt_rc)]


theorem ljp_continuous_closed_domain (r_c ε σ : ℝ) :
  ContinuousOn (fun r => Ljp r r_c ε σ) {r | 0 < r ∧ r ≤ r_c} := by
  have subset_pos : {r | 0 < r ∧ r ≤ r_c} ⊆ {r | r > 0} := by
    intro r hr
    exact hr.1
  have base := (scale_continuous ε σ).mono subset_pos
  apply ContinuousOn.congr base
  intro r hr
  simp only [Ljp, if_pos hr.2]
  ring

theorem ljp_continuous_piecewise (r_c ε σ : ℝ) :
  ContinuousOn (fun r => Ljp r r_c ε σ) {r | 0 < r ∧ r < r_c} := by
  have subset_pos : {r | 0 < r ∧ r < r_c} ⊆ {r | r > 0} := by
    intro r hr
    exact hr.1
  have base := (scale_continuous ε σ).mono subset_pos
  apply ContinuousOn.congr base
  intro r hr
  simp only [Ljp, if_pos (le_of_lt hr.2)]
  ring

theorem ljp_differentiable (r_c ε σ : ℝ) :
  DifferentiableOn ℝ (fun r => Ljp r r_c ε σ) {r | 0 < r ∧ r ≤ r_c} := by
  have subset_pos : {r | 0 < r ∧ r ≤ r_c} ⊆ {r | r > 0} := by
    intro r hr
    exact hr.1
  have base : DifferentiableOn ℝ
      (fun r => 4 * ε * (((σ / r) ^ 6) ^ 2 - (σ / r) ^ 6)) {r | r > 0} := by
    apply DifferentiableOn.mul
    · intro r hr
      simp only [gt_iff_lt]
      apply differentiableOn_const
      exact hr
    · apply DifferentiableOn.sub
      · apply DifferentiableOn.pow
        · apply DifferentiableOn.pow
          · apply DifferentiableOn.div
            · exact (differentiable_const σ).differentiableOn
            · exact differentiable_id.differentiableOn
            · intro x hx
              exact ne_of_gt hx
      · apply DifferentiableOn.pow
        apply DifferentiableOn.div
        · exact (differentiable_const σ).differentiableOn
        · exact differentiable_id.differentiableOn
        · intro x hx
          exact ne_of_gt hx
  apply DifferentiableOn.congr (base.mono subset_pos)
  · intro r hr
    simp [Ljp, if_pos hr.2]

/-- On the open interaction region `0 < r < r_c`, the truncated Lennard-Jones potential
has the explicit derivative `24 * ε * (σ ^ 6 / r ^ 7 - 2 * σ ^ 12 / r ^ 13)`. -/
theorem ljp_hasDerivAt (r_c ε σ : ℝ) {r : ℝ} (h0 : 0 < r) (hc : r < r_c) :
    HasDerivAt (fun r => Ljp r r_c ε σ)
      (24 * ε * (σ ^ 6 / r ^ 7 - 2 * σ ^ 12 / r ^ 13)) r := by
  have hne : r ≠ 0 := ne_of_gt h0
  have h12 : HasDerivAt (fun x : ℝ => x ^ (-12 : ℤ)) ((-12 : ℤ) * r ^ ((-12 : ℤ) - 1)) r :=
    hasDerivAt_zpow (-12) r (Or.inl hne)
  have h6 : HasDerivAt (fun x : ℝ => x ^ (-6 : ℤ)) ((-6 : ℤ) * r ^ ((-6 : ℤ) - 1)) r :=
    hasDerivAt_zpow (-6) r (Or.inl hne)
  have hg : HasDerivAt
      (fun x : ℝ => 4 * ε * (σ ^ 12 * x ^ (-12 : ℤ) - σ ^ 6 * x ^ (-6 : ℤ)))
      (4 * ε * (σ ^ 12 * ((-12 : ℤ) * r ^ ((-12 : ℤ) - 1))
        - σ ^ 6 * ((-6 : ℤ) * r ^ ((-6 : ℤ) - 1)))) r :=
    ((h12.const_mul (σ ^ 12)).sub (h6.const_mul (σ ^ 6))).const_mul (4 * ε)
  have heq : (fun x : ℝ => Ljp x r_c ε σ)
      =ᶠ[nhds r] fun x : ℝ => 4 * ε * (σ ^ 12 * x ^ (-12 : ℤ) - σ ^ 6 * x ^ (-6 : ℤ)) := by
    filter_upwards [Ioo_mem_nhds h0 hc] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx.1
    simp only [Ljp, if_pos hx.2.le]
    field_simp
  have hval : 4 * ε * (σ ^ 12 * ((-12 : ℤ) * r ^ ((-12 : ℤ) - 1))
      - σ ^ 6 * ((-6 : ℤ) * r ^ ((-6 : ℤ) - 1)))
      = 24 * ε * (σ ^ 6 / r ^ 7 - 2 * σ ^ 12 / r ^ 13) := by
    norm_num
    field_simp
    ring
  exact hval ▸ hg.congr_of_eventuallyEq heq

/-- The derivative of the truncated Lennard-Jones potential on the open interaction
region, as a `deriv` equality. -/
theorem ljp_deriv (r_c ε σ : ℝ) {r : ℝ} (h0 : 0 < r) (hc : r < r_c) :
    deriv (fun r => Ljp r r_c ε σ) r = 24 * ε * (σ ^ 6 / r ^ 7 - 2 * σ ^ 12 / r ^ 13) :=
  (ljp_hasDerivAt r_c ε σ h0 hc).deriv

theorem ljp_second_derivative (r_c ε σ : ℝ) :
    DifferentiableOn ℝ
      (fun r => 4 * ε * (156 * σ ^ 12 * r ^ (-14 : ℤ) - 42 * σ ^ 6 * r ^ (-8 : ℤ)))
      {r | 0 < r ∧ r ≤ r_c} := by
  apply DifferentiableOn.mul
  · exact (differentiable_const (4 * ε)).differentiableOn
  · apply DifferentiableOn.sub
    · apply DifferentiableOn.const_mul
      apply DifferentiableOn.zpow
      · exact differentiable_id.differentiableOn
      · apply Or.inl
        intro x hx
        exact ne_of_gt hx.1
    · apply DifferentiableOn.const_mul
      apply DifferentiableOn.zpow
      · exact differentiable_id.differentiableOn
      · apply Or.inl
        intro x hx
        exact ne_of_gt hx.1

end LeanLJ
