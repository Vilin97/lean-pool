/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Counterexample.Identities
public import LeanPool.Sendov.Analytic.Defect
public import LeanPool.Sendov.Analytic.Polar

/-!
# Estimating `J ∑ⱼ 1/zⱼ`

The origin argument needs `∑ⱼ 1/zⱼ`, which the centroid identity supplies only after the
inversions `1/zⱼ = conj zⱼ` and `1/qⱼ = conj qⱼ` are used.  Those hold exactly when the points
lie on the unit circle, i.e. when `|J| = 1`, and the **defect lemma** measures the failure by
`1 - |J|²`.  Conjugating the centroid identity and paying that defect gives

  `J ∑ⱼ 1/zⱼ = a (n-1) J - n J (x+iy) + O_≤( (n/(n-1)) (1 - |J|²) )`,

which is `Sendov.Jsum_estimate` below.  A single application of the defect lemma, to the
`2(n-1)` points `z₁,…,z_{n-1}, conj q₁,…,conj q_{n-1}`, pays for both substitutions at once.

Everything is division-free on the `z` side: `J ∑ⱼ 1/zⱼ` is written as `(∏ qⱼ) · sumEraseProd z`,
which is well defined even when some `zⱼ` vanishes.  That case is not excluded by hypothesis but
handled: if `∏ zⱼ = 0` then at most one term of `sumEraseProd z` survives, so the left side is at
most `1` while the right side is at least `n/(n-1) > 1`.  On the `q` side no such care is needed,
since the `qⱼ` are reciprocals and never vanish.

## Main statements

* `Sendov.Jsum_estimate`: the estimate above;
* `Sendov.sumEraseProd_norm_le_one`: the degenerate case `∏ zⱼ = 0`;
* `Sendov.prod_mul_sum_inv`: `(∏ s) ∑ⱼ 1/sⱼ = sumEraseProd s` when no `sⱼ` vanishes.
-/

public section

namespace Sendov

/-! ### Multiset odds and ends -/

lemma sum_map_sub (s : Multiset ℂ) (f g : ℂ → ℂ) :
    (s.map (fun v => f v - g v)).sum = (s.map f).sum - (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    ring

lemma sum_map_const_sub (s : Multiset ℂ) (c : ℂ) (g : ℂ → ℂ) :
    (s.map (fun v => c - g v)).sum = (s.card : ℂ) * c - (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring

lemma sum_map_re (s : Multiset ℂ) : (s.map (fun v => v.re)).sum = s.sum.re := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih => simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_re, ih]

lemma norm_sum_map_le (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).sum‖ ≤ (s.map (fun w => ‖f w‖)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    linarith [norm_add_le (f v) ((t.map f).sum), ih]

lemma norm_prod_le_one : ∀ (s : Multiset ℂ), (∀ w ∈ s, ‖w‖ ≤ 1) → ‖s.prod‖ ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro hs
    have hv := hs v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rw [Multiset.prod_cons, norm_mul]
    nlinarith [ih ht, norm_nonneg v, norm_nonneg t.prod]

/-- `(∏ s) ∑ⱼ 1/sⱼ = ∑ⱼ ∏_{k≠j} sₖ`, the clearing of denominators that is valid exactly when
no `sⱼ` vanishes. -/
lemma prod_mul_sum_inv : ∀ (s : Multiset ℂ), (∀ w ∈ s, w ≠ 0) →
    s.prod * (s.map (fun w => w⁻¹)).sum = sumEraseProd s := by
  intro s
  induction s using Multiset.induction_on with
  | empty => simp [sumEraseProd]
  | cons v t ih =>
    intro hs
    have hv := hs v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, u ≠ 0 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, sumEraseProd_cons, ← ih ht]
    field_simp

/-- The degenerate case.  If `∏ sⱼ = 0` then some `sⱼ` vanishes, so at most one term of
`∑ⱼ ∏_{k≠j} sₖ` is nonzero — and that term is a product of points of the closed unit disk. -/
lemma sumEraseProd_norm_le_one : ∀ (s : Multiset ℂ), (∀ w ∈ s, ‖w‖ ≤ 1) → s.prod = 0 →
    ‖sumEraseProd s‖ ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; simp at h
  | cons v t ih =>
    intro hs hp
    have hv := hs v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rw [sumEraseProd_cons]
    rcases eq_or_ne t.prod 0 with ht0 | ht0
    · rw [ht0, zero_add, norm_mul]
      nlinarith [ih ht ht0, norm_nonneg v, norm_nonneg (sumEraseProd t), hv]
    · have hv0 : v = 0 := by
        rw [Multiset.prod_cons] at hp
        rcases mul_eq_zero.1 hp with h | h
        · exact h
        · exact absurd h ht0
      rw [hv0, zero_mul, add_zero]
      exact norm_prod_le_one t ht

/-! ### The estimate -/

/-- **The estimate for `J ∑ⱼ 1/zⱼ`.**  Conjugating the centroid identity replaces `1/zⱼ` by
`conj zⱼ` and `qⱼ` by `1/conj qⱼ`; the defect lemma pays for both substitutions at once. -/
theorem Jsum_estimate {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {z q : Multiset ℂ}
    (hqcard : q.card = n - 1)
    (hz1 : ∀ w ∈ z, ‖w‖ ≤ 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hcent : ((n : ℂ) - 1) * ((a : ℂ) + z.sum) = (n : ℂ) * (q.map (fun v => (a : ℂ) - v⁻¹)).sum)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    ‖q.prod * sumEraseProd z
        - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
            * (q.prod * z.prod)‖
      ≤ ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hratio : (1 : ℝ) ≤ (n : ℝ) / ((n : ℝ) - 1) := by
    rw [le_div_iff₀ hn1]; linarith
  have hqpnorm : ‖q.prod‖ ≤ 1 := norm_prod_le_one q hq1
  rcases eq_or_ne z.prod 0 with hz0 | hz0
  · -- degenerate: `J = 0`, and `sumEraseProd z` has at most one surviving term
    rw [hz0, mul_zero, mul_zero, sub_zero, norm_zero, mul_zero, norm_mul]
    have h2 : ‖sumEraseProd z‖ ≤ 1 := sumEraseProd_norm_le_one z hz1 hz0
    nlinarith [norm_nonneg q.prod, norm_nonneg (sumEraseProd z)]
  · -- the main case: every `zⱼ` is nonzero, so denominators may be cleared
    have hzne : ∀ w ∈ z, w ≠ 0 := by
      intro w hw hw0
      exact hz0 (Multiset.prod_eq_zero (hw0 ▸ hw))
    set qc : Multiset ℂ := q.map (fun v => (starRingEnd ℂ) v) with hqc
    have hqcnorm : ∀ w ∈ qc, ‖w‖ ≤ 1 := by
      intro w hw
      rw [hqc] at hw
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hw
      simpa using hq1 v hv
    have hqsum : q.sum = (qc.map (fun w => (starRingEnd ℂ) w)).sum := by
      rw [hqc, Multiset.map_map]
      simp
    -- the conjugated centroid identity
    have hconj : ((n : ℂ) - 1) * ((a : ℂ) + (z.map (fun w => (starRingEnd ℂ) w)).sum)
        = (n : ℂ) * (((n : ℂ) - 1) * (a : ℂ) - (qc.map (fun w => w⁻¹)).sum) := by
      have h := congrArg (starRingEnd ℂ) hcent
      simp only [map_mul, map_sub, map_add, map_one, map_inv₀, map_natCast,
        Complex.conj_ofReal, map_multiset_sum, Multiset.map_map, Function.comp_def] at h
      rw [sum_map_const_sub, hqcard] at h
      have hcard : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
        push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
        ring
      rw [hcard] at h
      rw [hqc, Multiset.map_map]
      simp only [Function.comp_def]
      exact h
    -- `J ∑ⱼ 1/zⱼ` in division-free form
    have hSz : q.prod * sumEraseProd z = (q.prod * z.prod) * (z.map (fun w => w⁻¹)).sum := by
      rw [← prod_mul_sum_inv z hzne]; ring
    -- name the error and the bracket
    obtain ⟨E, hEdef⟩ : ∃ w : ℂ, w = q.prod * sumEraseProd z
        - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
            * (q.prod * z.prod) := ⟨_, rfl⟩
    obtain ⟨X, hXdef⟩ : ∃ w : ℂ, w = ((n : ℂ) - 1)
          * ((z.map (fun w => w⁻¹)).sum - (z.map (fun w => (starRingEnd ℂ) w)).sum)
        + (n : ℂ) * (q.sum - (qc.map (fun w => w⁻¹)).sum) := ⟨_, rfl⟩
    rw [← hEdef]
    -- the exact rearrangement
    have hE : ((n : ℂ) - 1) * E = (q.prod * z.prod) * X := by
      rw [hEdef, hXdef, hSz, hxy]
      linear_combination (q.prod * z.prod) * hconj
    -- the defect lemma, applied to `z` together with the conjugates of `q`
    have hdefect := defect (z + qc) (by
      intro w hw
      rcases Multiset.mem_add.1 hw with h | h
      · exact hz1 w h
      · exact hqcnorm w h)
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_add, Multiset.sum_add] at hdefect
    have hzp : (z.map (fun w => ‖w‖)).prod = ‖z.prod‖ := (norm_multiset_prod z).symm
    have hqp : (qc.map (fun w => ‖w‖)).prod = ‖q.prod‖ := by
      rw [hqc, Multiset.map_map]
      simp only [Function.comp_def, RCLike.norm_conj]
      exact (norm_multiset_prod q).symm
    rw [hzp, hqp] at hdefect
    obtain ⟨Dz, hDz⟩ : ∃ r : ℝ, r = (z.map (fun w => ‖w⁻¹ - (starRingEnd ℂ) w‖)).sum := ⟨_, rfl⟩
    obtain ⟨Dq, hDq⟩ : ∃ r : ℝ, r = (qc.map (fun w => ‖w⁻¹ - (starRingEnd ℂ) w‖)).sum := ⟨_, rfl⟩
    rw [← hDz, ← hDq] at hdefect
    have hDz0 : 0 ≤ Dz := by
      rw [hDz]
      exact Multiset.sum_nonneg (by
        intro r hr
        obtain ⟨w, _, rfl⟩ := Multiset.mem_map.1 hr
        exact norm_nonneg _)
    have hDq0 : 0 ≤ Dq := by
      rw [hDq]
      exact Multiset.sum_nonneg (by
        intro r hr
        obtain ⟨w, _, rfl⟩ := Multiset.mem_map.1 hr
        exact norm_nonneg _)
    -- the two substitution errors
    have hbz : ‖(z.map (fun w => w⁻¹)).sum - (z.map (fun w => (starRingEnd ℂ) w)).sum‖ ≤ Dz := by
      rw [← sum_map_sub, hDz]
      exact norm_sum_map_le z _
    have hbq : ‖q.sum - (qc.map (fun w => w⁻¹)).sum‖ ≤ Dq := by
      have hneg : q.sum - (qc.map (fun w => w⁻¹)).sum
          = -((qc.map (fun w => w⁻¹ - (starRingEnd ℂ) w)).sum) := by
        rw [hqsum, sum_map_sub]
        ring
      rw [hneg, norm_neg, hDq]
      exact norm_sum_map_le qc _
    -- assemble
    have hnorm : ‖((n : ℂ) - 1)‖ = (n : ℝ) - 1 := by
      have hc : ((n : ℂ) - 1) = (((n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hn1)]
    have hnn : ‖(n : ℂ)‖ = (n : ℝ) := by simp
    have hXle : ‖X‖ ≤ ((n : ℝ) - 1) * Dz + (n : ℝ) * Dq := by
      rw [hXdef]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, hnorm, hnn]
      exact add_le_add (mul_le_mul_of_nonneg_left hbz (by linarith))
        (mul_le_mul_of_nonneg_left hbq (by positivity))
    have hkey : ((n : ℝ) - 1) * ‖E‖ = ‖q.prod‖ * ‖z.prod‖ * ‖X‖ := by
      have h := congrArg norm hE
      rw [norm_mul, norm_mul, norm_mul, hnorm] at h
      exact h
    have hP0 : (0 : ℝ) ≤ ‖q.prod‖ * ‖z.prod‖ := by positivity
    have hstep : ((n : ℝ) - 1) * ‖E‖ ≤ (n : ℝ) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by
      rw [hkey]
      calc ‖q.prod‖ * ‖z.prod‖ * ‖X‖
          ≤ ‖q.prod‖ * ‖z.prod‖ * (((n : ℝ) - 1) * Dz + (n : ℝ) * Dq) :=
            mul_le_mul_of_nonneg_left hXle hP0
        _ ≤ ‖q.prod‖ * ‖z.prod‖ * ((n : ℝ) * (Dz + Dq)) := by nlinarith [hDz0, hP0]
        _ = (n : ℝ) * (‖z.prod‖ * ‖q.prod‖ * (Dz + Dq)) := by ring
        _ ≤ (n : ℝ) * (1 - (‖z.prod‖ * ‖q.prod‖) ^ 2) := by
            have hnpos : (0 : ℝ) ≤ (n : ℝ) := by linarith
            exact mul_le_mul_of_nonneg_left hdefect hnpos
        _ = (n : ℝ) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hn1]
    linarith [hstep]

end Sendov
