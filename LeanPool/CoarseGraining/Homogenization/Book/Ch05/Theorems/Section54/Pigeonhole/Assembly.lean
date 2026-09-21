/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Pigeonhole.ScalarChain
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Pigeonhole.RealAlgebra

/-! # Assembly -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace Pigeonhole

noncomputable section

/-!
# Assembly staging for the Section 5.4 pigeonhole lemma

The manuscript-facing theorem will live here.  Its scalar-chain input is now
available from `(P4)`; the remaining work is the finite pigeonhole and
telescoping argument over the arithmetic progression of scales.
-/

/-- If one of the two good-scale inequalities fails while both scalar chains
are monotone, then the product contracts by `(1 + δ)⁻¹`. -/
theorem product_step_le_inv_mul_of_not_good
    {delta aPrev aNow bPrev bNow : ℝ} (hdelta_pos : 0 < delta)
    (haNow_nonneg : 0 ≤ aNow) (hbNow_nonneg : 0 ≤ bNow)
    (ha_mono : aNow ≤ aPrev) (hb_mono : bNow ≤ bPrev)
    (hbad : ¬ (aPrev ≤ (1 + delta) * aNow ∧
        bPrev ≤ (1 + delta) * bNow)) :
    aNow * bNow ≤ (1 + delta)⁻¹ * (aPrev * bPrev) := by
  let c : ℝ := 1 + delta
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hc_inv_nonneg : 0 ≤ c⁻¹ := (inv_pos.mpr hc_pos).le
  have haPrev_nonneg : 0 ≤ aPrev := le_trans haNow_nonneg ha_mono
  have hbPrev_nonneg : 0 ≤ bPrev := le_trans hbNow_nonneg hb_mono
  by_cases ha_good : aPrev ≤ c * aNow
  · have hb_bad : ¬ bPrev ≤ c * bNow := by
      intro hb_good
      exact hbad ⟨by simpa [c] using ha_good, by simpa [c] using hb_good⟩
    have hb_contract : bNow ≤ c⁻¹ * bPrev :=
      (le_inv_mul_iff₀ hc_pos).2 (not_le.mp hb_bad).le
    have hmul : aNow * bNow ≤ aPrev * (c⁻¹ * bPrev) :=
      mul_le_mul ha_mono hb_contract hbNow_nonneg haPrev_nonneg
    calc
      aNow * bNow ≤ aPrev * (c⁻¹ * bPrev) := hmul
      _ = c⁻¹ * (aPrev * bPrev) := by ring
      _ = (1 + delta)⁻¹ * (aPrev * bPrev) := by simp [c]
  · have ha_contract : aNow ≤ c⁻¹ * aPrev :=
      (le_inv_mul_iff₀ hc_pos).2 (not_le.mp ha_good).le
    have hright_nonneg : 0 ≤ c⁻¹ * aPrev :=
      mul_nonneg hc_inv_nonneg haPrev_nonneg
    have hmul : aNow * bNow ≤ (c⁻¹ * aPrev) * bPrev :=
      mul_le_mul ha_contract hb_mono hbNow_nonneg hright_nonneg
    calc
      aNow * bNow ≤ (c⁻¹ * aPrev) * bPrev := hmul
      _ = c⁻¹ * (aPrev * bPrev) := by ring
      _ = (1 + delta)⁻¹ * (aPrev * bPrev) := by simp [c]

/-- A one-sided finite Gronwall estimate for a sequence whose consecutive
steps are bounded by multiplication by `r`. -/
theorem iterate_le_geometric_of_step
    {A : ℕ → ℝ} {r : ℝ} (hr_nonneg : 0 ≤ r) :
    ∀ k : ℕ,
      (∀ j : ℕ, 1 ≤ j → j ≤ k → A j ≤ r * A (j - 1)) →
        A k ≤ r ^ k * A 0
  | 0, _ => by simp
  | k + 1, hstep => by
      have hprev : A k ≤ r ^ k * A 0 :=
        iterate_le_geometric_of_step hr_nonneg k (by
          intro j hj_pos hj_le
          exact hstep j hj_pos (Nat.le_trans hj_le (Nat.le_succ k)))
      have hlast : A (k + 1) ≤ r * A ((k + 1) - 1) :=
        hstep (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) le_rfl
      have hlast' : A (k + 1) ≤ r * A k := by
        simpa using hlast
      calc
        A (k + 1) ≤ r * A k := hlast'
        _ ≤ r * (r ^ k * A 0) := mul_le_mul_of_nonneg_left hprev hr_nonneg
        _ = r ^ (k + 1) * A 0 := by ring

end

end Pigeonhole
end Section54
end Ch05
end Book
end Homogenization
