/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Common.Rpow

/-!
# The quadratic `1 - 2ct + At²`

Two quadratics drive the whole development, and they are the same object with different
parameters:

* `β(t) = 1 - 2axt + a²t²`, the quantity the blog post's inequalities are stated in;
* `Q n α t = 1 - 2c(α)t + a²t²`, what `β` becomes after `β(1)` is replaced by `α/(3+α)`.

So the facts about them — nonnegativity under feasibility, the chord bound below the vertex,
monotonicity above it — are proved once here for

  `QQ c A t = 1 - 2ct + At²`,

and `Sendov.Q n α t = QQ (c n α) (A n α) t` holds by `rfl`.

Note which hypothesis each fact needs.  Nonnegativity is exactly feasibility `c² ≤ A`, since
`QQ = (1-ct)² + (A-c²)t²`.  The bound `QQ ≤ 1` on `[0,1]` needs only `0 ≤ c` together with
`QQ 1 ≤ 1`: writing `QQ t - 1 = t(At - 2c)`, the value at `t = 1` already gives `A ≤ 2c`, and
then `At ≤ 2c` whether `A` is nonnegative (as `At ≤ A`) or negative (as `At ≤ 0 ≤ 2c`).  That
matters, because `A` is genuinely negative in parts of the range.

## Main statements

* `Sendov.QQ_nonneg`, `Sendov.QQ_le_one`;
* `Sendov.QQ_le_chord`: `QQ t ≤ 1 - ct` below the vertex;
* `Sendov.QQ_le_at_one`: `QQ t ≤ QQ 1` above it.
-/

public section

namespace Sendov

/-- The quadratic `1 - 2ct + At²`. -/
@[expose]
noncomputable def QQ (c A t : ℝ) : ℝ := 1 - 2 * c * t + A * t ^ 2

/-- `Sendov.Q` is an instance of `Sendov.QQ`.  Stated before the section variables below,
which deliberately shadow `Sendov.c` and `Sendov.A`. -/
lemma Q_eq_QQ (n : ℕ) (α t : ℝ) : Q n α t = QQ (c n α) (A n α) t := rfl

variable {c A t : ℝ}

/-- `QQ` as a sum of squares. -/
lemma QQ_eq (c A t : ℝ) : QQ c A t = (1 - c * t) ^ 2 + (A - c ^ 2) * t ^ 2 := by
  simp only [QQ]; ring

lemma QQ_zero (c A : ℝ) : QQ c A 0 = 1 := by simp [QQ]

lemma QQ_one (c A : ℝ) : QQ c A 1 = 1 - 2 * c + A := by simp [QQ]

/-- Feasibility `c² ≤ A` says exactly that `QQ` is a sum of squares. -/
lemma QQ_nonneg (hfeas : c ^ 2 ≤ A) (t : ℝ) : 0 ≤ QQ c A t := by
  rw [QQ_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))

/-- `QQ ≤ 1` on `[0,1]`, from `QQ 1 ≤ 1` and `0 ≤ c` alone. -/
lemma QQ_le_one (hc : 0 ≤ c) (hB : QQ c A 1 ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    QQ c A t ≤ 1 := by
  have hAc : A - 2 * c ≤ 0 := by rw [QQ_one] at hB; linarith
  have h5 : A * t - 2 * c ≤ 0 := by
    rcases le_total 0 A with h | h
    · nlinarith [mul_le_of_le_one_right h ht1]
    · nlinarith [mul_nonneg ht0 (neg_nonneg.2 h)]
  simp only [QQ]
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 h5)]

/-- Below the vertex, `QQ` lies under the chord `1 - ct`. -/
lemma QQ_le_chord (ht0 : 0 ≤ t) (ht : A * t ≤ c) : QQ c A t ≤ 1 - c * t := by
  simp only [QQ]
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht)]

/-- Above the vertex, `QQ` is increasing, so it is at most its value at `t = 1`. -/
lemma QQ_le_at_one (hA : 0 ≤ A) (ht : c ≤ A * t) (ht1 : t ≤ 1) : QQ c A t ≤ QQ c A 1 := by
  have hkey : 0 ≤ A * (1 + t) - 2 * c := by nlinarith [ht, hA, ht1]
  simp only [QQ]
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) hkey]

/-- `t ^ k * QQ ^ e` is continuous, hence interval integrable: needed wherever an integral of
this shape is split or compared. -/
lemma continuous_pow_mul_QQ (c A : ℝ) (k : ℕ) {e : ℝ} (he : 0 ≤ e) :
    Continuous fun t : ℝ => t ^ k * QQ c A t ^ e := by
  have hQ : Continuous fun t : ℝ => QQ c A t := by simp only [QQ]; fun_prop
  have hk : Continuous fun t : ℝ => t ^ k := by fun_prop
  exact hk.mul ((continuous_rpow_const he).comp hQ)

end Sendov
