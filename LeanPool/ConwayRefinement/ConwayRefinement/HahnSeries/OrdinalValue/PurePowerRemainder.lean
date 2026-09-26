/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PowerRemainder

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ConvolutionRemainder

/-!
# The remainder estimate for pure powers

Berarducci's induction computes the value of a pure power `b ^ k` by applying Lemma 8.2 with
`c = 1`. That reading is not available: Definition 6.4 defines `v_J^p` only for value above one,
so the hypothesis `v_J^p(b) ≤ v_J^p(c)` of Lemma 8.2 is undefined at `c = 1`. Nor can the case be
absorbed by choosing some other factor for `c`, since the doubling in Lemma 9.5 then raises the
exponent of `b` instead of lowering it. The pure-power case is therefore developed on its own.

It is strictly easier than the general one. The term carrying the truncation of `c` disappears,
and with it the only use of that hypothesis. At a positive exponent the remainder for `b ^ (m + 1)`
is literally the two-factor remainder for the pair `(b, b)` one step down, so Lemma 7.7 transfers
with no new analysis; at exponent zero the remainder vanishes.
-/

universe v

public noncomputable section

open HahnSeries Ordinal

namespace Berarducci

variable {K : Type v} [Field K]

/-- The remainder in the product rule for `b ^ (m + 1)`. -/
def powerRemainderOne (b : SeriesWithOrdinalValueAboveOne K) (m : ℕ) (γ : ℝ) : Germ K :=
  germAt ((b.1 ^ (m + 1) : Series K) : K⟦ℝ⟧) γ
    - (m + 1) • (germAt (b.1 : K⟦ℝ⟧) γ * toGerm (b.1 ^ m))

/-- The bound on that remainder. -/
def powerRemainderBoundOne (b : SeriesWithOrdinalValueAboveOne K) (m : ℕ) : NatOrdinal :=
  ordinalValue b.1 ^ m * b.residualValue

theorem powerRemainderBoundOne_eq (b : SeriesWithOrdinalValueAboveOne K) (m : ℕ) :
    powerRemainderBoundOne b m = ordinalValue b.1 ^ m * b.residualValue := (rfl)

/-- The defining decomposition, read as an expansion of the germ. -/
theorem germAt_purePower_decomp (b : SeriesWithOrdinalValueAboveOne K) (m : ℕ) (ξ : ℝ) :
    germAt ((b.1 ^ (m + 1) : Series K) : K⟦ℝ⟧) ξ =
      (m + 1) • (germAt (b.1 : K⟦ℝ⟧) ξ * toGerm (b.1 ^ m)) + powerRemainderOne b m ξ := by
  rw [powerRemainderOne]
  abel

/-- Taking both factors equal shifts the two-factor bound by one exponent. -/
theorem powerRemainderBound_self (b : SeriesWithOrdinalValueAboveOne K) (m : ℕ) :
    powerRemainderBound b b m = powerRemainderBoundOne b (m + 1) := by
  rw [powerRemainderBound_eq, powerRemainderBoundOne_eq, pow_succ]
  ring

/-- Taking both factors equal shifts the two-factor remainder by one exponent. -/
theorem powerRemainderOne_succ (b : SeriesWithOrdinalValueAboveOne K) (m : ℕ) (γ : ℝ) :
    powerRemainderOne b (m + 1) γ = powerRemainder b b m γ := by
  rw [powerRemainderOne, powerRemainder_eq]
  simp only [← pow_succ]
  rw [mul_comm (toGerm (b.1 ^ (m + 1))) (germAt (b.1 : K⟦ℝ⟧) γ), succ_nsmul]
  abel

/-- Berarducci, Lemma 7.7 for a pure power. -/
theorem exists_powerRemainderOne_lt (b : SeriesWithOrdinalValueAboveOne K) (m : ℕ) :
    ∃ η < (0 : ℝ), ∀ γ : ℝ, η < γ → γ < 0 →
      germOrdinalValue (powerRemainderOne b m γ) < powerRemainderBoundOne b m := by
  cases m with
  | zero =>
    refine ⟨-1, by norm_num, fun γ _ _ ↦ ?_⟩
    have hzero : powerRemainderOne b 0 γ = 0 := by
      rw [powerRemainderOne]
      simp
    rw [hzero, germOrdinalValue_zero, powerRemainderBoundOne_eq, pow_zero, one_mul]
    exact pos_iff_ne_zero.mpr b.residualValue_ne_zero
  | succ n =>
    obtain ⟨η, hη, h⟩ := exists_powerRemainder_lt b b le_rfl n
    refine ⟨η, hη, fun γ hlow hhigh ↦ ?_⟩
    rw [powerRemainderOne_succ, ← powerRemainderBound_self]
    exact h γ hlow hhigh

end Berarducci
