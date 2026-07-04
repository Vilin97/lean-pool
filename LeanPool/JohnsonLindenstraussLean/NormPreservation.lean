import JL.ChiSquared

/-!
# Distributional Johnson–Lindenstrauss norm preservation

Combining the two one-sided chi-squared tail bounds of `JL.ChiSquared` via a union
bound gives the **two-sided distributional JL guarantee**, stated here in its core
chi-squared form: with `S = ∑ gᵢ²` a sum of `k` i.i.d. squared standard Gaussians,

`P( S ∉ ((1-ε)k, (1+ε)k) ) ≤ 2·exp(-(ε² - ε³) k / 4)`.

Since `‖f x‖² / ‖x‖² = S / k` for the Gaussian random projection `f` (Gaussian
rotation invariance), this is exactly the statement that `f` preserves the squared
norm of any fixed vector to within a factor `1 ± ε`, except with the stated failure
probability.
-/

open MeasureTheory ProbabilityTheory Real

namespace JL

/-- **Two-sided chi-squared concentration / JL norm preservation.**
The probability that the chi-squared sum leaves the window `((1-ε)k, (1+ε)k)` is at
most `2·exp(-(ε² - ε³) k / 4)`. -/
theorem chiSq_concentration (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (gaussianVec k).real
        {ω | (1 + ε) * (k : ℝ) ≤ chiSq k ω ∨ chiSq k ω ≤ (1 - ε) * (k : ℝ)}
      ≤ 2 * rexp (-(ε ^ 2 - ε ^ 3) * (k : ℝ) / 4) := by
  rw [Set.setOf_or]
  refine (measureReal_union_le _ _).trans ?_
  have hu := chiSq_upper_tail k h0
  have hl := chiSq_lower_tail k h0 h1
  linarith

/-- The same guarantee phrased through the normalised squared norm `S / k`: the
relative deviation `|S/k - 1|` reaches `ε` with probability at most
`2·exp(-(ε² - ε³) k / 4)`. -/
theorem jl_norm_preservation (k : ℕ) (hk : 0 < k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (gaussianVec k).real {ω | ε ≤ |chiSq k ω / (k : ℝ) - 1|}
      ≤ 2 * rexp (-(ε ^ 2 - ε ^ 3) * (k : ℝ) / 4) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have hset : {ω : Fin k → ℝ | ε ≤ |chiSq k ω / (k : ℝ) - 1|}
      = {ω | (1 + ε) * (k : ℝ) ≤ chiSq k ω ∨ chiSq k ω ≤ (1 - ε) * (k : ℝ)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have hrw : chiSq k ω / (k : ℝ) - 1 = (chiSq k ω - (k : ℝ)) / (k : ℝ) := by
      rw [sub_div, div_self hkne]
    rw [hrw, abs_div, abs_of_pos hkR, le_div_iff₀ hkR, le_abs]
    constructor
    · rintro (h | h)
      · exact Or.inl (by nlinarith)
      · exact Or.inr (by nlinarith)
    · rintro (h | h)
      · exact Or.inl (by nlinarith)
      · exact Or.inr (by nlinarith)
  rw [hset]
  exact chiSq_concentration k h0 h1

end JL
