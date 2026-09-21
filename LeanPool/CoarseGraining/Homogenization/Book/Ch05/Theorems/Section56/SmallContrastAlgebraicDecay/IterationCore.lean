/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAlgebraicDecay.Recurrence

/-! # Iteration Core -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open scoped BigOperators

noncomputable section

namespace SmallContrastAlgebraicDecay

/-!
# Pure induction core for the small-contrast algebraic iteration

This file contains no probability or homogenization assumptions.  It is the
strong-induction step used after the scalar recurrence has been reduced to
explicit decay, shift, and quadratic absorption estimates.
-/

/-- Strong-induction core for a one-step contraction with a quadratic
lower-scale error. -/
theorem algebraic_decay_induction_core
    {F : ℕ → ℝ} {decay source : ℕ → ℝ} {q : ℕ → ℕ}
    {L N : ℕ} {K θ lam ε : ℝ}
    (hK_nonneg : 0 ≤ K) (hθ_nonneg : 0 ≤ θ)
    (hdecay_nonneg : ∀ m, 0 ≤ decay m)
    (hF_nonneg : ∀ m, 0 ≤ F m)
    (hbase : ∀ m, m < N → F m ≤ K * decay m)
    (hq_lt : ∀ m, N ≤ m → q m < m)
    (hshift_lt : ∀ m, N ≤ m → m - L < m)
    (hrec :
      ∀ m, N ≤ m →
        F m ≤ θ * F (m - L) + (F (q m)) ^ (2 : ℕ) + source m)
    (hshift :
      ∀ m, N ≤ m →
        θ * (K * decay (m - L)) ≤ lam * (K * decay m))
    (hquad :
      ∀ m, N ≤ m →
        (K * decay (q m)) ^ (2 : ℕ) ≤ ε * (K * decay m))
    (hsource :
      ∀ m, N ≤ m →
        source m ≤ ε * (K * decay m))
    (hbudget : lam + ε + ε ≤ 1) :
    ∀ m, F m ≤ K * decay m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hmN : m < N
      · exact hbase m hmN
      · have hNm : N ≤ m := Nat.le_of_not_gt hmN
        have hm_shift : m - L < m := hshift_lt m hNm
        have hq : q m < m := hq_lt m hNm
        have hF_shift := ih (m - L) hm_shift
        have hF_q := ih (q m) hq
        have hshift_bound :
            θ * F (m - L) ≤ lam * (K * decay m) := by
          exact (mul_le_mul_of_nonneg_left hF_shift hθ_nonneg).trans (hshift m hNm)
        have hquad_bound :
              (F (q m)) ^ (2 : ℕ) ≤ ε * (K * decay m) := by
          have hFq_nonneg : 0 ≤ F (q m) := hF_nonneg (q m)
          exact
            (pow_le_pow_left₀ hFq_nonneg hF_q 2).trans (hquad m hNm)
        have hsource_bound := hsource m hNm
        have hrec_m := hrec m hNm
        have htarget_nonneg : 0 ≤ K * decay m :=
          mul_nonneg hK_nonneg (hdecay_nonneg m)
        calc
          F m ≤ θ * F (m - L) + (F (q m)) ^ (2 : ℕ) + source m :=
            hrec_m
          _ ≤ lam * (K * decay m) + ε * (K * decay m) +
                ε * (K * decay m) := by
              gcongr
          _ = (lam + ε + ε) * (K * decay m) := by ring
          _ ≤ 1 * (K * decay m) :=
              mul_le_mul_of_nonneg_right hbudget htarget_nonneg
          _ = K * decay m := by ring

end SmallContrastAlgebraicDecay

end

end Section56
end Ch05
end Book
end Homogenization
