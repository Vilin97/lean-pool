/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadEventSummability
public import Mathlib.Data.Nat.Pairing

/-! # Bad Scale Union -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped BigOperators ENNReal

/-!
# Union bound for quantitative bad scales

This file contains only the countable union bound which passes from the
bad-scale event to its fixed-pair components.  It is part of the quantitative
tail proof and does not introduce a last-bad-scale construction.
-/

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measureReal_iUnion_nat_le_tsum
    {μ : Measure Ω} [IsFiniteMeasure μ] {E : ℕ → Set Ω}
    (hE : Summable fun k : ℕ => μ.real (E k)) :
    μ.real (⋃ k : ℕ, E k) ≤ ∑' k : ℕ, μ.real (E k) := by
  let ν : FiniteMeasure Ω := ⟨μ, inferInstance⟩
  have hE_nn : Summable fun k : ℕ => ν (E k) := by
    rw [← NNReal.summable_coe]
    simpa [ν, Measure.real] using! hE
  have hν := MeasureTheory.FiniteMeasure.apply_iUnion_le
    (μ := ν) (f := E) hE_nn
  have hν_real : (ν (⋃ k : ℕ, E k) : ℝ) ≤ ∑' k : ℕ, (ν (E k) : ℝ) := by
    exact_mod_cast hν
  simpa [ν, Measure.real] using! hν_real

/-- The bad-scale event is bounded by the sum of the fixed-pair bad events. -/
theorem measureReal_badScaleEvent_le_tsum_unpair_badPairEvent
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {t α : ℝ} {N : ℕ}
    (hE : Summable fun k : ℕ =>
      μ.real (badPairEvent H t α N (Nat.unpair k).1 (Nat.unpair k).2)) :
    μ.real (badScaleEvent H t α N) ≤
      ∑' k : ℕ,
        μ.real (badPairEvent H t α N (Nat.unpair k).1 (Nat.unpair k).2) := by
  have hbad :
      badScaleEvent H t α N =
        ⋃ k : ℕ, badPairEvent H t α N (Nat.unpair k).1 (Nat.unpair k).2 := by
    ext ω
    constructor
    · rintro ⟨m, n, hnm, hNm, hbad⟩
      refine Set.mem_iUnion.2 ⟨Nat.pair m n, ?_⟩
      have hbad' :
          (3 : ℝ) ^ (-(α * ((m - N : ℕ) : ℝ))) <
            (3 : ℝ) ^ (-(t * ((m - n : ℕ) : ℝ))) * H m n ω := by
        simpa [neg_mul] using hbad
      simpa [badPairEvent, Nat.unpair_pair] using ⟨hnm, hNm, hbad'⟩
    · rintro hω
      rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
      rcases hk with ⟨hnm, hNm, hbad⟩
      have hbad' :
          (3 : ℝ) ^ (-t * (((Nat.unpair k).1 - (Nat.unpair k).2 : ℕ) : ℝ)) *
              H (Nat.unpair k).1 (Nat.unpair k).2 ω >
            (3 : ℝ) ^ (-α * (((Nat.unpair k).1 - N : ℕ) : ℝ)) := by
        simpa [neg_mul] using hbad
      exact ⟨(Nat.unpair k).1, (Nat.unpair k).2, hnm, hNm, hbad'⟩
  rw [hbad]
  exact measureReal_iUnion_nat_le_tsum (μ := μ) hE

end

end Section57
end Ch05
end Book
end Homogenization
