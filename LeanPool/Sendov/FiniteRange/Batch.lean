/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Common.Rpow

/-!
# Batching adjacent degrees

Every term of `Sendov.R` is monotone in `n`, and the directions cooperate: the elementary
part decreases, the prefactor increases, and the moment decreases.  So for a whole range of
degrees `n₀ ≤ n ≤ n₁` one bound suffices,

  `R n α ≤ base n₀ α + pref n₁ α * I n₀ α`,

needing one moment and one certificate for the batch rather than one per degree.

The key identity is

  `Q (n+1) α t = Q n α t - (2α / (n(n-1))) * t * (1-t)`,

so `Q` decreases with `n` on `[0,1]`; combined with `Q ≤ 1` and the exponent `(n-4)/2`
increasing, the moment decreases too.

This pays most where it costs most.  Batch sizes track the slack in `R n α`, which is
smallest near its maximum at `n = 53` and grows away from it, so the expensive high degrees
batch into the largest groups: measured, `n ∈ [62,97]` costs 12.5× less batched, against 2.8×
in the tight middle.  Note also that the certificate's degree is set by `n₀`, the *smallest*
member, so a batch is cheaper than any single degree it covers except the first.

## Main statements

* `Sendov.Q_succ_sub`: the identity above;
* `Sendov.Q_anti`: `Q` decreases with `n` on `[0,1]`;
* `Sendov.A_mono`: `A` increases with `n`.
-/

public section

namespace Sendov

variable {α t : ℝ}

lemma M_mono {m n : ℕ} (h : m ≤ n) : M m ≤ M n := by
  simp only [M]
  have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  linarith

/-- `A` increases with `n`: raising the degree moves `a²` towards `1`. -/
lemma A_mono {m n : ℕ} (hm : 2 ≤ m) (h : m ≤ n) (hα : 0 ≤ α) : A m α ≤ A n α := by
  have hMm : 0 < M m := M_pos hm
  have hMn : 0 < M n := lt_of_lt_of_le hMm (M_mono h)
  simp only [A]
  have : 2 * α / M n ≤ 2 * α / M m :=
    div_le_div_of_nonneg_left (by linarith) hMm (M_mono h)
  linarith

/-- **The degree step.**  Raising `n` by one lowers `Q` by a multiple of `t(1-t)`. -/
lemma Q_succ_sub (n : ℕ) (hn : 2 ≤ n) (hα : 0 ≤ α) (t : ℝ) :
    Q (n + 1) α t = Q n α t - (2 * α / ((n : ℝ) * ((n : ℝ) - 1))) * t * (1 - t) := by
  have h1 : ((n : ℝ) - 1) ≠ 0 := by
    have := M_pos hn; simp only [M] at this; linarith
  have h2 : (n : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hM1 : M (n + 1) = (n : ℝ) := by simp only [M]; push_cast; ring
  have hMn : M n = (n : ℝ) - 1 := by simp only [M]
  simp only [Q, c, A, hM1, hMn]
  field_simp
  ring

/-- `Q` decreases with `n` on `[0,1]`. -/
lemma Q_anti {m n : ℕ} (hm : 2 ≤ m) (h : m ≤ n) (hα : 0 ≤ α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Q n α t ≤ Q m α t := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · have hmn : m ≤ n := by omega
      have hn2 : 2 ≤ n := le_trans hm hmn
      have hstep : Q (n + 1) α t ≤ Q n α t := by
        rw [Q_succ_sub n hn2 hα t]
        have hnn : (0 : ℝ) ≤ 2 * α / ((n : ℝ) * ((n : ℝ) - 1)) := by
          have h1 : (0 : ℝ) < (n : ℝ) - 1 := by
            have := M_pos hn2; simp only [M] at this; linarith
          have h2 : (0 : ℝ) < (n : ℝ) := by linarith
          positivity
        nlinarith [mul_nonneg (mul_nonneg hnn ht0) (by linarith : (0 : ℝ) ≤ 1 - t)]
      exact le_trans hstep (ih hmn)
    · have : m = n + 1 := by omega
      subst this
      exact le_rfl

/-! ### The batch bound -/

open MeasureTheory

/-- `x ^ y ≤ x ^ z` for `0 ≤ x ≤ 1` and `0 < z ≤ y`, allowing `x = 0`. -/
lemma rpow_le_rpow_exponent_ge' {x y z : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 < z)
    (hzy : z ≤ y) : x ^ y ≤ x ^ z := by
  rcases eq_or_lt_of_le hx0 with h | h
  · rw [← h, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
  · exact Real.rpow_le_rpow_of_exponent_ge h hx1 hzy

/-- The moment decreases with the degree: `Q` falls and the exponent rises. -/
theorem integral_anti {m n : ℕ} (hm : 5 ≤ m) (h : m ≤ n) (hα : 0 ≤ α)
    (hcm : 0 ≤ c m α) (hfn : c n α ^ 2 ≤ A n α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2))
      ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * Q m α t ^ (((m : ℝ) - 4) / 2) := by
  have hm2 : 2 ≤ m := by omega
  have hn2 : 2 ≤ n := by omega
  have hmR : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  have hem : (0 : ℝ) < ((m : ℝ) - 4) / 2 := by linarith
  have hen : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by linarith
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_integrand n α hen).intervalIntegrable _ _)
    ((continuous_integrand m α hem.le).intervalIntegrable _ _) ?_
  intro t ht
  obtain ⟨ht0, ht1⟩ := ht
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht0 3)
  have hQn : 0 ≤ Q n α t := Q_nonneg hfn t
  have hmono : Q n α t ≤ Q m α t := Q_anti hm2 h hα ht0 ht1
  -- nonnegativity at `m` comes free from monotonicity, so feasibility at `m` is not needed
  have hQm0 : 0 ≤ Q m α t := le_trans hQn hmono
  have hQm1 : Q m α t ≤ 1 := Q_le_one hm2 hα hcm ht0 ht1
  have hstep1 : Q n α t ^ (((n : ℝ) - 4) / 2) ≤ Q m α t ^ (((n : ℝ) - 4) / 2) :=
    Real.rpow_le_rpow hQn hmono hen
  have hstep2 : Q m α t ^ (((n : ℝ) - 4) / 2) ≤ Q m α t ^ (((m : ℝ) - 4) / 2) :=
    rpow_le_rpow_exponent_ge' hQm0 hQm1 hem (by linarith)
  linarith

/-- **The batch bound.**  One evaluation covers every degree in `[n₀, n₁]`: the elementary
part and the moment at `n₀`, the prefactor at `n₁`.

Only `0 ≤ c n₀ α` is required at `n₀`, not feasibility.  That matters: feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`, and for `n₀ < 36` it
does not follow from `α ≤ 17` either.  Nonnegativity of `Q` at `n₀` instead comes free from
`Q_anti`, since `Q n₀ ≥ Q n ≥ 0`. -/
theorem R_le_batch {n₀ n n₁ : ℕ} (h0 : 5 ≤ n₀) (h1 : n₀ ≤ n) (h2 : n ≤ n₁) (hα : 0 ≤ α)
    (hc0 : 0 ≤ c n₀ α) (hfn : c n α ^ 2 ≤ A n α) :
    R n α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n₀) + 1 / (4 * M n₀ * (3 + α))
      + A n₁ α ^ 2 * n₁ * M n₁ * ((n₁ : ℝ) - 2) / (4 * (3 + α))
        * ∫ t in (0 : ℝ)..1, t ^ 3 * Q n₀ α t ^ (((n₀ : ℝ) - 4) / 2) := by
  have hn2 : 2 ≤ n := by omega
  have h02 : 2 ≤ n₀ := by omega
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hM0 : 0 < M n₀ := M_pos h02
  have hMn : 0 < M n := M_pos hn2
  have hMn1 : 0 < M n₁ := lt_of_lt_of_le hMn (M_mono h2)
  -- the elementary part decreases
  have hbase : 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
      ≤ 1 / (2 * M n₀) + 1 / (4 * M n₀ * (3 + α)) := by
    have hMM : M n₀ ≤ M n := M_mono h1
    have e1 : 1 / (2 * M n) ≤ 1 / (2 * M n₀) := by
      apply one_div_le_one_div_of_le (by linarith); linarith
    have e2 : 1 / (4 * M n * (3 + α)) ≤ 1 / (4 * M n₀ * (3 + α)) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    linarith
  -- the prefactor increases
  have hAn : 0 ≤ A n α := A_nonneg hfn
  have hApre : A n α ≤ A n₁ α := A_mono hn2 h2 hα
  have hnn1 : (n : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast h2
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn12 : (2 : ℝ) ≤ (n₁ : ℝ) := le_trans hn2R hnn1
  have hA2 : A n α ^ 2 ≤ A n₁ α ^ 2 := by nlinarith [hAn, hApre]
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hMle : M n ≤ M n₁ := M_mono h2
  have hA1nn : (0 : ℝ) ≤ A n₁ α ^ 2 := sq_nonneg _
  have e1 : A n α ^ 2 * n ≤ A n₁ α ^ 2 * n₁ := mul_le_mul hA2 hnn1 hnn hA1nn
  have e2 : A n α ^ 2 * n * M n ≤ A n₁ α ^ 2 * n₁ * M n₁ :=
    mul_le_mul e1 hMle hMn.le (by positivity)
  have e3 : A n α ^ 2 * n * M n * ((n : ℝ) - 2) ≤ A n₁ α ^ 2 * n₁ * M n₁ * ((n₁ : ℝ) - 2) :=
    mul_le_mul e2 (by linarith) (by linarith) (by positivity)
  have hc : (0 : ℝ) < 4 * (3 + α) := by positivity
  have hpref : A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
      ≤ A n₁ α ^ 2 * n₁ * M n₁ * ((n₁ : ℝ) - 2) / (4 * (3 + α)) := by
    rw [div_le_div_iff_of_pos_right hc]
    exact e3
  -- the moment decreases
  have hI := integral_anti (m := n₀) (n := n) h0 h1 hα hc0 hfn
  have hInn : 0 ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    exact mul_nonneg (pow_nonneg hu.1 3) (Real.rpow_nonneg (Q_nonneg hfn u) _)
  have hprefnn : 0 ≤ A n₁ α ^ 2 * n₁ * M n₁ * ((n₁ : ℝ) - 2) / (4 * (3 + α)) := by
    have h4 : (0 : ℝ) ≤ (n₁ : ℝ) - 2 := by linarith
    have h5 : (0 : ℝ) ≤ M n₁ := hMn1.le
    positivity
  rw [R]
  nlinarith [hbase, hpref, hI, hInn, hprefnn]

end Sendov
