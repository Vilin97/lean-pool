/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.HarmonicPhaseSum
import LeanPool.QuadraticCarleson.QuadraticCarleson.TranslatedBohrUnion

/-!
# Phase witnesses on the counterexample's translated Bohr set

This file joins the measure-theoretic construction of the paper's set `E_N`
to the almost-constant finite harmonic sum. Every point of `E_N` supplies an
integer translate, a dyadic modulation, and the explicit logarithmic lower
bound needed in the negative endpoint argument.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson


/-- Every point of the paper's translated Bohr set carries a dyadic phase-sum
witness. The exponent inequalities record exactly the logarithmic window in
which that modulation was selected. -/
theorem paperTranslatedBohrSet_phase_witness {N : ℕ} {L x : ℝ}
    (hN : 100 ≤ N) (hx : x ∈ paperTranslatedBohrSet N L) :
    ∃ (k : ℤ) (n : ℕ),
      k ∈ paperBohrIndices N ∧
      (N : ℝ) * k + L ≤ (n : ℝ) ∧
      (n : ℝ) < (N : ℝ) * k + L + N ∧
      x - k ∈ bohrSet (2 ^ n) (1 / ((2 : ℝ) ^ 100 * N)) ∧
      Real.log N / (4 * N) ≤
        ‖harmonicPhaseSum N k.toNat ((2 ^ n : ℕ) : ℤ) (x - k)‖ := by
  unfold paperTranslatedBohrSet translatedDyadicBohrUnion at hx
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
  unfold integerTranslate at hxk
  obtain ⟨n, hn, hbohr⟩ := mem_iUnion₂.mp hxk
  have hkpos : 0 < k := paperBohrIndices_pos (by omega) hk
  have hkcastZ : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hkpos.le
  have hkcastR : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast hkcastZ
  have hkupper : ((k.toNat : ℕ) : ℝ) ≤ 7 * (N : ℝ) / 10 := by
    rw [hkcastR]
    exact (mem_paperBohrIndices.mp hk).2
  refine ⟨k, n, hk, hn.1, hn.2, hbohr, ?_⟩
  apply harmonicPhaseSum_norm_ge_of_mem_bohrSet hN hkupper
  simpa only [hkcastR] using hbohr

/-- The dyadic phase-sum lower-level set contains the full translated Bohr
set. This packages the preceding witness in the exact set-theoretic form
used to transfer the already proved `|E_N| ≳ N` estimate. -/
def paperPhaseWitnessSet (N : ℕ) (L : ℝ) : Set ℝ :=
  {x | ∃ (k : ℤ) (n : ℕ),
    k ∈ paperBohrIndices N ∧
    (N : ℝ) * k + L ≤ (n : ℝ) ∧
    (n : ℝ) < (N : ℝ) * k + L + N ∧
    x - k ∈ bohrSet (2 ^ n) (1 / ((2 : ℝ) ^ 100 * N)) ∧
    Real.log N / (4 * N) ≤
      ‖harmonicPhaseSum N k.toNat ((2 ^ n : ℕ) : ℤ) (x - k)‖}

theorem paperTranslatedBohrSet_subset_phaseWitnessSet {N : ℕ} {L : ℝ}
    (hN : 100 ≤ N) :
    paperTranslatedBohrSet N L ⊆ paperPhaseWitnessSet N L := by
  intro x hx
  exact paperTranslatedBohrSet_phase_witness hN hx

/-- Consequently the model phase-sum level set has measure bounded below by
an explicit positive multiple of `N`. -/
theorem paperPhaseWitnessSet_volume_real_ge {N : ℕ} {L : ℝ}
    (hN : 100 ≤ N) (hL : 2 ≤ 3 * (N : ℝ) ^ 2 / 5 + L) :
    (N : ℝ) / (30720 * ((2 : ℝ) ^ 100 + 1)) ≤
      volume.real (paperPhaseWitnessSet N L) := by
  have hfinite : volume (paperPhaseWitnessSet N L) ≠ ∞ := by
    apply measure_ne_top_of_subset (s := Icc (0 : ℝ) ((N : ℝ) + 1))
    · intro x hx
      obtain ⟨k, n, hk, hnlow, hnup, hbohr, hphase⟩ := hx
      have hkpos : (0 : ℝ) < k := by
        exact_mod_cast paperBohrIndices_pos (by omega) hk
      have hkupper := (mem_paperBohrIndices.mp hk).2
      exact ⟨by linarith [hbohr.1.1], by linarith [hbohr.1.2]⟩
    · simp
  calc
    (N : ℝ) / (30720 * ((2 : ℝ) ^ 100 + 1)) ≤
        volume.real (paperTranslatedBohrSet N L) :=
      paperTranslatedBohrSet_volume_real_ge (by omega) hL
    _ ≤ volume.real (paperPhaseWitnessSet N L) :=
      measureReal_mono (paperTranslatedBohrSet_subset_phaseWitnessSet hN) hfinite

end QuadraticCarleson
