/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# The defect lemma

For points `w₁, …, w_N` in the closed unit disk,

  `(∏ ‖wⱼ‖) · ∑ⱼ ‖wⱼ⁻¹ - conj wⱼ‖ ≤ 1 - (∏ ‖wⱼ‖)²`.

The origin argument uses this to replace the inversion identities `1/zⱼ = conj zⱼ`, which hold
only when the points lie *on* the unit circle, by inequalities valid throughout the disk, at a
cost proportional to `1 - |J|²` where `J` is the product.

The blog post proves it by writing `‖wⱼ‖ = e^{-aⱼ}`, computing `‖wⱼ⁻¹ - conj wⱼ‖ = 2 sinh aⱼ`,
and reducing to superadditivity of `sinh`.  None of that is needed.  Splitting off one point,

  `D (w ::ₘ t) = P · (r · δ_w) + r · D t`,   `r = ‖w‖`,  `P = ∏ over t`,

the pointwise fact `r · δ_w ≤ 1 - r²` and the inductive hypothesis `D t ≤ 1 - P²` leave

  `1 - r²P² - [P(1-r²) + r(1-P²)] = (1-r)(1-P)(1-rP) ≥ 0`,

which is immediate for `r, P ∈ [0,1]`.

Points *at* the origin need no separate treatment.  There `wⱼ⁻¹` is Lean's junk value `0`, but
the pointwise fact is still true — as an inequality rather than an equality — because the
left-hand side carries a factor `‖wⱼ‖`.  A limiting argument, which the informal proof needs,
is therefore avoided.

## Main statements

* `Sendov.norm_mul_norm_inv_sub_conj_le`: the pointwise fact;
* `Sendov.defect`: the lemma.
-/

public section

namespace Sendov

open Multiset

/-! ### Products of norms -/

lemma prod_norm_nonneg (s : Multiset ℂ) : 0 ≤ (s.map (fun z => ‖z‖)).prod := by
  refine Multiset.prod_nonneg ?_
  intro y hy
  obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 hy
  exact norm_nonneg z

lemma prod_norm_le_one : ∀ (s : Multiset ℂ), (∀ z ∈ s, ‖z‖ ≤ 1) →
    (s.map (fun z => ‖z‖)).prod ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons w t ih =>
    intro hs
    have hw : ‖w‖ ≤ 1 := hs w (mem_cons_self w t)
    have ht : ∀ z ∈ t, ‖z‖ ≤ 1 := fun z hz => hs z (mem_cons_of_mem hz)
    have hIH := ih ht
    have hP0 : 0 ≤ (t.map (fun z => ‖z‖)).prod := prod_norm_nonneg t
    simp only [Multiset.map_cons, Multiset.prod_cons]
    nlinarith [norm_nonneg w]

/-! ### The pointwise fact -/

/-- `‖w‖ · ‖w⁻¹ - conj w‖ ≤ 1 - ‖w‖²` for `‖w‖ ≤ 1`, with equality unless `w = 0`.  The
factor `‖w‖` on the left is what makes the origin harmless. -/
lemma norm_mul_norm_inv_sub_conj_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖w‖ * ‖w⁻¹ - (starRingEnd ℂ) w‖ ≤ 1 - ‖w‖ ^ 2 := by
  rcases eq_or_ne w 0 with rfl | hne
  · simp
  · have hkey : w * (w⁻¹ - (starRingEnd ℂ) w) = 1 - ((‖w‖ : ℝ) : ℂ) ^ 2 := by
      rw [mul_sub, mul_inv_cancel₀ hne, Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq]
    have h1 : ‖w‖ * ‖w⁻¹ - (starRingEnd ℂ) w‖ = ‖(1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2‖ := by
      rw [← norm_mul, hkey]
    rw [h1]
    have h2 : ((1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith [norm_nonneg w])]

/-! ### The lemma -/

/-- **The defect lemma.** -/
theorem defect : ∀ (s : Multiset ℂ), (∀ z ∈ s, ‖z‖ ≤ 1) →
    (s.map (fun z => ‖z‖)).prod * (s.map (fun z => ‖z⁻¹ - (starRingEnd ℂ) z‖)).sum
      ≤ 1 - ((s.map (fun z => ‖z‖)).prod) ^ 2 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons w t ih =>
    intro hs
    have hw : ‖w‖ ≤ 1 := hs w (mem_cons_self w t)
    have ht : ∀ z ∈ t, ‖z‖ ≤ 1 := fun z hz => hs z (mem_cons_of_mem hz)
    have hIH := ih ht
    have hP0 : 0 ≤ (t.map (fun z => ‖z‖)).prod := prod_norm_nonneg t
    have hP1 : (t.map (fun z => ‖z‖)).prod ≤ 1 := prod_norm_le_one t ht
    have hT0 : 0 ≤ (t.map (fun z => ‖z⁻¹ - (starRingEnd ℂ) z‖)).sum := by
      refine Multiset.sum_nonneg ?_
      intro y hy
      obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 hy
      exact norm_nonneg _
    have hr0 : 0 ≤ ‖w‖ := norm_nonneg w
    have hpt := norm_mul_norm_inv_sub_conj_le hw
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    -- `r P (δ + T) = P (r δ) + r (P T) ≤ P(1-r²) + r(1-P²) ≤ 1 - r²P²`
    have hstep1 := mul_le_mul_of_nonneg_left hpt hP0
    have hstep2 := mul_le_mul_of_nonneg_left hIH hr0
    have hfac : 0 ≤ (1 - ‖w‖) * (1 - (t.map (fun z => ‖z‖)).prod)
        * (1 - ‖w‖ * (t.map (fun z => ‖z‖)).prod) := by
      have h3 : ‖w‖ * (t.map (fun z => ‖z‖)).prod ≤ 1 := by nlinarith
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith [hstep1, hstep2, hfac]

end Sendov
