/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.JTPKeyIdentity

/-!
# Core lemmas for the Jacobi triple product proof

The proof strategy: Show $(q;q)_∞ (-z;q)_∞ (-q/z;q)_∞ = g(z)$ by:
1. Dividing both sides by $(-q/z;q)_∞$ (nonzero for ‖q/z‖ < 1)
2. Showing $g(z) / (-q/z;q)_∞ = (q;q)_∞ (-z;q)_∞$
3. This follows from the Cauchy product and the Euler 2nd identity

Key identity: $(q;q)_∞ / (q;q)_n = (q^{n+1};q)_∞$ (telescoping)
-/

open Finset Filter
open scoped Topology

namespace QSeries

noncomputable section

/-- Telescoping factorisation: $(q;q)_\infty = (q;q)_n \cdot (q \cdot q^n; q)_\infty$. -/
theorem qPochhammerInf_self_eq_qPochhammer_mul {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInf q q = qPochhammer q q n * qPochhammerInf (q * q ^ n) q := by
  rw [qPochhammerInf_mul_pow_eq_div hq n, mul_div_cancel₀ _ (qPochhammer_self_ne_zero hq n)]

/-- Euler's second identity evaluated at $z = -q^{n+1}$, giving $(q^{n+1}; q)_\infty$. -/
theorem euler_second_identity_neg_pow {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    HasSum (fun m : ℕ => q ^ m.choose 2 * (-q ^ (n + 1)) ^ m / qPochhammer q q m)
      (qPochhammerInf (q ^ (n + 1)) q) := by
  convert euler_second_identity hq ?_ using 1
  · norm_num
  · simpa using pow_lt_one₀ (norm_nonneg q) hq (by omega)

/-- The product $(q;q)_\infty (-z;q)_\infty$ equals
$\sum_n q^{\binom{n}{2}} z^n (q^{n+1};q)_\infty$, via Euler's second identity. -/
theorem hasSum_pow_choose_two_mul_pow_mul_qPochhammerInf {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q)
      (qPochhammerInf q q * qPochhammerInf (-z) q) := by
  refine ((euler_second_identity hq hz).mul_left (qPochhammerInf q q)).congr_fun fun n => ?_
  rw [qPochhammerInf_mul_pow_eq_div hq n]
  ring

/-- Key identity: the n-th coefficient of the product (q;q)_∞ (-z;q)_∞
expanded using Euler 2nd, multiplied by (q;q)_∞, gives the JTP coefficient.
Specifically: qPochhammerInf (q * q^n) q = qPochhammerInf (q^(n+1)) q. -/
theorem qPochhammerInf_mul_pow {q : ℂ} (n : ℕ) :
    qPochhammerInf (q * q ^ n) q = qPochhammerInf (q ^ (n + 1)) q := by
  congr 1; ring

/-- The Jacobi triple product identity at $q = 0$, verified directly. -/
theorem jacobiTripleProduct_zero {z : ℂ} (hz' : z ≠ 0) :
    qPochhammerInf 0 0 * qPochhammerInf (-z) 0 * qPochhammerInf (-0 / z) 0 =
    (∑' k : ℕ, z ^ k * (0 : ℂ) ^ k.choose 2) +
    (∑' m : ℕ, z⁻¹ ^ (m + 1) * (0 : ℂ) ^ (m + 2).choose 2) := by
  norm_num [qPochhammerInf]
  rw [tprod_eq_prod]
  any_goals exact {0}
  · rw [tsum_eq_sum, tsum_eq_single 0] <;> norm_num
    any_goals exact {0, 1}
    · norm_num [Finset.sum_pair]
    · exact fun n hn => Or.inr <| Nat.ne_of_gt <| Nat.choose_pos <| by omega
    · intro b hb; rcases b with (_ | _ | b) <;> simp_all [Nat.choose]
  · aesop

/-- Euler's second identity evaluated at $z = -q/z$, giving $(-q/z; q)_\infty$. -/
theorem euler_second_identity_div {q z : ℂ} (hq : ‖q‖ < 1) (hzq : ‖q‖ < ‖z‖)
    (hz' : z ≠ 0) :
    HasSum (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m)
      (qPochhammerInf (-q / z) q) := by
  have hnorm : ‖q / z‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hz')).2 hzq
  rw [neg_div]
  exact (euler_second_identity hq hnorm).congr_fun fun n => by ring

/-! ### The diagonal splitting of a double series over `ℕ × ℕ` -/

/-- The diagonal splitting equivalence `(ℕ × ℕ) ⊕ (ℕ × ℕ) ≃ ℕ × ℕ`: the left summand
enumerates the pairs on or below the diagonal as `(m + k, m)`, the right summand
enumerates the pairs strictly above it as `(n, n + l + 1)`. -/
private def diagonalEquiv : (ℕ × ℕ) ⊕ (ℕ × ℕ) ≃ ℕ × ℕ where
  toFun s := match s with
    | .inl p => (p.2 + p.1, p.2)
    | .inr p => (p.2, p.2 + (p.1 + 1))
  invFun p := if p.2 ≤ p.1 then .inl (p.1 - p.2, p.2) else .inr (p.2 - p.1 - 1, p.1)
  left_inv := by rintro (⟨k, m⟩ | ⟨l, n⟩) <;> simp
  right_inv := by rintro ⟨a, b⟩; dsimp only; split_ifs with h <;> simp <;> omega

/-- `HasSum` form of the diagonal splitting of a family indexed by `ℕ × ℕ`. -/
private theorem hasSum_split_diagonal {f : ℕ × ℕ → ℂ} {a b : ℂ}
    (h1 : HasSum (fun p : ℕ × ℕ => f (p.2 + p.1, p.2)) a)
    (h2 : HasSum (fun p : ℕ × ℕ => f (p.2, p.2 + (p.1 + 1))) b) :
    HasSum f (a + b) :=
  diagonalEquiv.hasSum_iff.mp (HasSum.sum (f := f ∘ diagonalEquiv) h1 h2)

/-- Splitting a summable family over `ℕ × ℕ` along the diagonal:
$\sum_p f(p) = \sum_k \sum_m f(m+k, m) + \sum_l \sum_n f(n, n+l+1)$. -/
theorem tsum_split_diagonal {f : ℕ × ℕ → ℂ} (hf : Summable f) :
    ∑' p : ℕ × ℕ, f p =
      (∑' k : ℕ, ∑' m : ℕ, f (m + k, m)) + ∑' l : ℕ, ∑' n : ℕ, f (n, n + (l + 1)) := by
  have hc : Summable (f ∘ diagonalEquiv) := diagonalEquiv.summable_iff.mpr hf
  have hl : Summable fun p : ℕ × ℕ => f (p.2 + p.1, p.2) := hc.comp_injective Sum.inl_injective
  have hr : Summable fun p : ℕ × ℕ => f (p.2, p.2 + (p.1 + 1)) :=
    hc.comp_injective Sum.inr_injective
  rw [(hasSum_split_diagonal hl.hasSum hr.hasSum).tsum_eq, hl.tsum_prod, hr.tsum_prod]

/-! ### The Jacobi triple product from two `HasSum` inputs -/

/-- Cancellation `z ^ (m + k) * (z⁻¹) ^ m = z ^ k` for `z ≠ 0`. -/
private theorem pow_add_mul_inv_pow {z : ℂ} (hz : z ≠ 0) (m k : ℕ) :
    z ^ (m + k) * z⁻¹ ^ m = z ^ k := by
  rw [pow_add, mul_right_comm, ← mul_pow, mul_inv_cancel₀ hz, one_pow, one_mul]

/-- Cancellation `z ^ n * (z⁻¹) ^ (n + j) = (z⁻¹) ^ j` for `z ≠ 0`. -/
private theorem pow_mul_inv_pow_add {z : ℂ} (hz : z ≠ 0) (n j : ℕ) :
    z ^ n * z⁻¹ ^ (n + j) = z⁻¹ ^ j := by
  rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hz, one_pow, one_mul]

/-- The `z ^ k` diagonal of the Jacobi triple product double series sums to
`z ^ k * q ^ (k choose 2)`. -/
theorem hasSum_diagonal_nonneg {q z : ℂ} (hq : ‖q‖ < 1) (hz' : z ≠ 0) (k : ℕ) :
    HasSum (fun m : ℕ =>
      q ^ (m + k).choose 2 * z ^ (m + k) * qPochhammerInf (q * q ^ (m + k)) q *
        (q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m)) (z ^ k * q ^ k.choose 2) := by
  refine ((hasSum_pow_choose_two_nonneg hq k).mul_left (z ^ k)).congr_fun fun m => ?_
  rw [div_eq_mul_inv, div_eq_mul_inv, ← pow_add_mul_inv_pow hz' m k]
  ring

/-- The `z⁻¹ ^ (l + 1)` diagonal of the Jacobi triple product double series sums to
`z⁻¹ ^ (l + 1) * q ^ (l + 2 choose 2)`. -/
theorem hasSum_diagonal_neg {q z : ℂ} (hq : ‖q‖ < 1) (hz' : z ≠ 0) (l : ℕ) :
    HasSum (fun n : ℕ =>
      q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q *
        (q ^ (n + (l + 1)).choose 2 * q ^ (n + (l + 1)) * z⁻¹ ^ (n + (l + 1)) /
          qPochhammer q q (n + (l + 1)))) (z⁻¹ ^ (l + 1) * q ^ (l + 2).choose 2) := by
  refine ((hasSum_pow_choose_two_neg hq l).mul_left (z⁻¹ ^ (l + 1))).congr_fun fun n => ?_
  rw [div_eq_mul_inv, div_eq_mul_inv, ← pow_mul_inv_pow_add hz' n (l + 1)]
  ring

/-- The Jacobi triple product identity, given Euler's second identity in the two shapes
needed: `hA` expands $(q;q)_\infty(-z;q)_\infty$ and `hB` expands $(-q/z;q)_\infty$.
Multiplying the two series, applying Fubini and splitting the resulting double series
along the diagonal reduces everything to `hasSum_diagonal_nonneg` / `hasSum_diagonal_neg`. -/
theorem jacobiTripleProduct_of_hasSum {q z : ℂ} (hq : ‖q‖ < 1) (hz' : z ≠ 0)
    (hA : HasSum (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q)
      (qPochhammerInf q q * qPochhammerInf (-z) q))
    (hB : HasSum (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m)
      (qPochhammerInf (-q / z) q)) :
    qPochhammerInf q q * qPochhammerInf (-z) q * qPochhammerInf (-q / z) q =
    (∑' k : ℕ, z ^ k * q ^ k.choose 2) +
    (∑' m : ℕ, z⁻¹ ^ (m + 1) * q ^ (m + 2).choose 2) := by
  have hprod : Summable fun p : ℕ × ℕ =>
      q ^ p.1.choose 2 * z ^ p.1 * qPochhammerInf (q * q ^ p.1) q *
        (q ^ p.2.choose 2 * q ^ p.2 * z⁻¹ ^ p.2 / qPochhammer q q p.2) :=
    .of_norm (by simpa using Summable.mul_norm hA.summable.norm hB.summable.norm)
  have hfubini : qPochhammerInf q q * qPochhammerInf (-z) q * qPochhammerInf (-q / z) q =
      ∑' p : ℕ × ℕ, q ^ p.1.choose 2 * z ^ p.1 * qPochhammerInf (q * q ^ p.1) q *
        (q ^ p.2.choose 2 * q ^ p.2 * z⁻¹ ^ p.2 / qPochhammer q q p.2) := by
    rw [← hA.tsum_eq, ← hB.tsum_eq, hprod.tsum_prod]
    simp only [tsum_mul_left, tsum_mul_right]
  rw [hfubini, tsum_split_diagonal hprod]
  congr 1
  · exact tsum_congr fun k => (hasSum_diagonal_nonneg hq hz' k).tsum_eq
  · exact tsum_congr fun l => (hasSum_diagonal_neg hq hz' l).tsum_eq

/-- The Jacobi triple product identity in the annulus $\|q\| < \|z\| < 1$. -/
theorem jacobiTripleProduct_annulus {q z : ℂ} (hq : ‖q‖ < 1)
    (hzq : ‖q‖ < ‖z‖) (hz : ‖z‖ < 1) (hz' : z ≠ 0) :
    qPochhammerInf q q * qPochhammerInf (-z) q * qPochhammerInf (-q / z) q =
    (∑' k : ℕ, z ^ k * q ^ k.choose 2) +
    (∑' m : ℕ, z⁻¹ ^ (m + 1) * q ^ (m + 2).choose 2) :=
  jacobiTripleProduct_of_hasSum hq hz' (hasSum_pow_choose_two_mul_pow_mul_qPochhammerInf hq hz)
    (euler_second_identity_div hq hzq hz')

end

end QSeries
