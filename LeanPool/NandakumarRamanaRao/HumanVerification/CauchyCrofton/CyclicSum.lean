/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib

/-!
# Total variation of a cyclically unimodal sequence

A purely one-dimensional lemma used for the Cauchy perimeter of a convex polygon.

If `a : ℤ → ℝ` is `m`-periodic and, for every level `t ≠ 0`, there is at most one up-crossing
of the level `t` per period, then the cyclic total variation of `a` equals twice its range.

The proof is a layer-cake computation: the intervals `[a j, a (j+1))` attached to the ascending
steps are pairwise disjoint (two of them would produce two up-crossings of a common level) and
they cover the range interval `[N, M)` up to the single point `0`.
-/

open MeasureTheory Set

noncomputable section

namespace HumanVerification.CauchyCrofton

/-- **Cyclic total variation of a unimodal sequence.** -/
theorem cyclic_sum_abs_sub {m : ℕ} (hm : 0 < m) (a : ℤ → ℝ)
    (hper : ∀ j : ℤ, a (j + m) = a j)
    (hcross : ∀ t : ℝ, t ≠ 0 → ∀ j k : ℤ, a j ≤ t → t < a (j + 1) → a k ≤ t → t < a (k + 1) →
      ∃ q : ℤ, k = j + q * m)
    {M N : ℝ} (hMle : ∀ j : ℤ, a j ≤ M) (hMex : ∃ j : ℤ, a j = M)
    (hNle : ∀ j : ℤ, N ≤ a j) (hNex : ∃ j : ℤ, a j = N) :
    ∑ j ∈ Finset.range m, |a ((j : ℤ) + 1) - a (j : ℤ)| = 2 * (M - N) := by
  classical
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  -- periodicity under arbitrary integer multiples of the period
  have hperz : ∀ (j k : ℤ), a (j + k * m) = a j := by
    intro j k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
        have e : j + ((n : ℤ) + 1) * m = (j + (n : ℤ) * m) + m := by ring
        rw [e, hper, ih]
    | pred n ih =>
        have e : (j + (-(n : ℤ) - 1) * m) + m = j + (-(n : ℤ)) * m := by ring
        have := hper (j + (-(n : ℤ) - 1) * m)
        rw [e, ih] at this
        exact this.symm
  -- every index is equivalent to one in `[0, m)`
  have hred : ∀ j : ℤ, ∃ i : ℕ, i < m ∧ a (i : ℤ) = a j ∧ a ((i : ℤ) + 1) = a (j + 1) := by
    intro j
    have hmod1 : 0 ≤ j % (m : ℤ) := Int.emod_nonneg j (by omega)
    have hmod2 : j % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos j hmZ
    refine ⟨(j % m).toNat, by omega, ?_, ?_⟩
    · have hsplit : j = j % m + (j / m) * m := by
        have := Int.emod_add_ediv_mul j (m : ℤ); omega
      have h1 : ((j % m).toNat : ℤ) = j % m := Int.toNat_of_nonneg (by omega)
      rw [h1]
      conv_rhs => rw [hsplit]
      rw [hperz]
    · have hsplit : j + 1 = (j % m + 1) + (j / m) * m := by
        have := Int.emod_add_ediv_mul j (m : ℤ); omega
      have h1 : ((j % m).toNat : ℤ) = j % m := Int.toNat_of_nonneg (by omega)
      rw [h1]
      conv_rhs => rw [hsplit]
      rw [hperz]
  have hNM : N ≤ M := le_trans (hNle 0) (hMle 0)
  -- Step 1 : the telescoping sum vanishes
  have htel : ∑ j ∈ Finset.range m, (a ((j : ℤ) + 1) - a (j : ℤ)) = 0 := by
    have h := Finset.sum_range_sub (f := fun i : ℕ => a (i : ℤ)) m
    have hcast : ∀ i : ℕ, a (((i + 1 : ℕ) : ℤ)) = a ((i : ℤ) + 1) := by
      intro i; norm_cast
    simp only [hcast] at h
    rw [h]
    have hm0 : a ((m : ℕ) : ℤ) = a 0 := by
      have := hperz 0 1
      simpa using this
    rw [hm0]
    simp
  -- Step 2 : the sum of the ascents is the range
  have hascent : ∑ j ∈ Finset.range m, max (a ((j : ℤ) + 1) - a (j : ℤ)) 0 = M - N := by
    have hvol : ∀ j : ℕ, ENNReal.ofReal (max (a ((j : ℤ) + 1) - a (j : ℤ)) 0)
        = volume (Set.Ico (a (j : ℤ)) (a ((j : ℤ) + 1))) := by
      intro j
      rw [Real.volume_Ico]
      rcases le_or_gt (a ((j : ℤ) + 1)) (a (j : ℤ)) with h | h
      · rw [max_eq_right (by linarith), ENNReal.ofReal_zero,
          ENNReal.ofReal_eq_zero.2 (by linarith)]
      · rw [max_eq_left (by linarith)]
    have hdisj : (↑(Finset.range m) : Set ℕ).PairwiseDisjoint
        (fun j : ℕ => Set.Ico (a (j : ℤ)) (a ((j : ℤ) + 1))) := by
      intro j hj k hk hjk
      simp only [Finset.coe_range, Set.mem_Iio] at hj hk
      rw [Function.onFun, Set.disjoint_left]
      intro t htj htk
      -- find a nonzero level in the intersection
      have hL : max (a (j : ℤ)) (a (k : ℤ)) ≤ t := by
        simp only [max_le_iff]
        exact ⟨htj.1, htk.1⟩
      have hU : t < min (a ((j : ℤ) + 1)) (a ((k : ℤ) + 1)) := by
        simp only [lt_min_iff]
        exact ⟨htj.2, htk.2⟩
      have hLU : max (a (j : ℤ)) (a (k : ℤ)) < min (a ((j : ℤ) + 1)) (a ((k : ℤ) + 1)) :=
        lt_of_le_of_lt hL hU
      obtain ⟨s, hs1, hs2, hs0⟩ : ∃ s : ℝ, max (a (j : ℤ)) (a (k : ℤ)) ≤ s ∧
          s < min (a ((j : ℤ) + 1)) (a ((k : ℤ) + 1)) ∧ s ≠ 0 := by
        rcases eq_or_ne (max (a (j : ℤ)) (a (k : ℤ))) 0 with h0 | h0
        · have hUpos : 0 < min (a ((j : ℤ) + 1)) (a ((k : ℤ) + 1)) := by
            rw [h0] at hLU; exact hLU
          exact ⟨min (a ((j : ℤ) + 1)) (a ((k : ℤ) + 1)) / 2, by rw [h0]; linarith,
            by linarith, by intro hcon; rw [div_eq_zero_iff] at hcon; rcases hcon with h | h
                            · linarith
                            · norm_num at h⟩
        · exact ⟨max (a (j : ℤ)) (a (k : ℤ)), le_refl _, hLU, h0⟩
      have hsj : a (j : ℤ) ≤ s ∧ s < a ((j : ℤ) + 1) :=
        ⟨le_trans (le_max_left _ _) hs1, lt_of_lt_of_le hs2 (min_le_left _ _)⟩
      have hsk : a (k : ℤ) ≤ s ∧ s < a ((k : ℤ) + 1) :=
        ⟨le_trans (le_max_right _ _) hs1, lt_of_lt_of_le hs2 (min_le_right _ _)⟩
      obtain ⟨q, hq⟩ := hcross s hs0 (j : ℤ) (k : ℤ) hsj.1 hsj.2 hsk.1 hsk.2
      apply hjk
      have hjZ : (j : ℤ) < (m : ℤ) := by exact_mod_cast hj
      have hkZ : (k : ℤ) < (m : ℤ) := by exact_mod_cast hk
      have hj0' : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
      have hk0' : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
      have hq0 : q = 0 := by
        rcases lt_trichotomy q 0 with h | h | h
        · exfalso
          have hle : q * (m : ℤ) ≤ -(m : ℤ) := by nlinarith
          omega
        · exact h
        · exfalso
          have hle : (m : ℤ) ≤ q * (m : ℤ) := by nlinarith
          omega
      have hZ : (j : ℤ) = (k : ℤ) := by rw [hq0] at hq; omega
      exact_mod_cast hZ
    have hsub : (⋃ j ∈ Finset.range m, Set.Ico (a (j : ℤ)) (a ((j : ℤ) + 1)))
        ⊆ Set.Ico N M := by
      intro t ht
      simp only [Set.mem_iUnion, Finset.mem_range] at ht
      obtain ⟨j, _, hj⟩ := ht
      exact ⟨le_trans (hNle _) hj.1, lt_of_lt_of_le hj.2 (hMle _)⟩
    have hcover : Set.Ico N M
        ⊆ (⋃ j ∈ Finset.range m, Set.Ico (a (j : ℤ)) (a ((j : ℤ) + 1))) ∪ {(0 : ℝ)} := by
      intro t ht
      rcases eq_or_ne t 0 with rfl | ht0
      · exact Or.inr rfl
      refine Or.inl ?_
      obtain ⟨j0, hj0⟩ := hNex
      obtain ⟨l, hl⟩ := hMex
      -- there is an index within one period whose value exceeds `t`
      have hex : ∃ n : ℕ, t < a (j0 + n) := by
        obtain ⟨i, _, hi1, _⟩ := hred l
        -- shift `i` into the window `[j0, j0 + m)`
        obtain ⟨i2, hi2lt, hi2, _⟩ := hred (j0 + ((i : ℤ) - j0) % m)
        refine ⟨(((i : ℤ) - j0) % m).toNat, ?_⟩
        have hmodnn : (0 : ℤ) ≤ ((i : ℤ) - j0) % (m : ℤ) := Int.emod_nonneg _ (by omega)
        have hmod : ((((i : ℤ) - j0) % m).toNat : ℤ) = ((i : ℤ) - j0) % m :=
          Int.toNat_of_nonneg hmodnn
        rw [hmod]
        have hval : a (j0 + ((i : ℤ) - j0) % m) = a (i : ℤ) := by
          have hsplit : (i : ℤ) = (j0 + ((i : ℤ) - j0) % m) + (((i : ℤ) - j0) / m) * m := by
            have := Int.emod_add_ediv_mul ((i : ℤ) - j0) (m : ℤ); omega
          conv_rhs => rw [hsplit]
          rw [hperz]
        rw [hval, hi1, hl]
        exact ht.2
      classical
      have hzero : ¬ (t < a (j0 + ((0 : ℕ) : ℤ))) := by
        have hz : a (j0 + ((0 : ℕ) : ℤ)) = N := by simpa using hj0
        rw [hz]
        exact not_lt.2 ht.1
      have hfind := Nat.find_spec hex
      set n := Nat.find hex with hn
      have hnpos : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · exfalso; apply hzero; rw [h] at hfind; exact_mod_cast hfind
        · exact h
      have hprev : ¬ (t < a (j0 + ((n - 1 : ℕ) : ℤ))) := Nat.find_min hex (by omega)
      have hstep : (j0 + ((n - 1 : ℕ) : ℤ)) + 1 = j0 + (n : ℤ) := by
        have : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by omega
        omega
      obtain ⟨i, hilt, hi1, hi2⟩ := hred (j0 + ((n - 1 : ℕ) : ℤ))
      refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hilt, ?_⟩⟩
      constructor
      · rw [hi1]; exact not_lt.1 hprev
      · rw [hi2, hstep]; exact hfind
    have hmeasure : volume (⋃ j ∈ Finset.range m, Set.Ico (a (j : ℤ)) (a ((j : ℤ) + 1)))
        = ENNReal.ofReal (M - N) := by
      apply le_antisymm
      · have hmono := measure_mono (μ := (volume : Measure ℝ)) hsub
        rwa [Real.volume_Ico] at hmono
      · have h1 : volume (Set.Ico N M)
            ≤ volume ((⋃ j ∈ Finset.range m, Set.Ico (a (j : ℤ)) (a ((j : ℤ) + 1)))
              ∪ {(0 : ℝ)}) := measure_mono (μ := (volume : Measure ℝ)) hcover
        have h3 : volume ((⋃ j ∈ Finset.range m, Set.Ico (a (j : ℤ)) (a ((j : ℤ) + 1)))
              ∪ {(0 : ℝ)})
            ≤ volume (⋃ j ∈ Finset.range m, Set.Ico (a (j : ℤ)) (a ((j : ℤ) + 1)))
              + volume ({(0 : ℝ)}) := measure_union_le _ _
        rw [measure_singleton, add_zero] at h3
        rw [Real.volume_Ico] at h1
        exact le_trans h1 h3
    have hsum : ∑ j ∈ Finset.range m, volume (Set.Ico (a (j : ℤ)) (a ((j : ℤ) + 1)))
        = ENNReal.ofReal (M - N) := by
      rw [← measure_biUnion_finset hdisj (fun j _ => measurableSet_Ico)]
      exact hmeasure
    have hsum2 : ENNReal.ofReal (∑ j ∈ Finset.range m, max (a ((j : ℤ) + 1) - a (j : ℤ)) 0)
        = ENNReal.ofReal (M - N) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => le_max_right _ _)]
      rw [Finset.sum_congr rfl (fun j _ => hvol j)]
      exact hsum
    have hnn : 0 ≤ ∑ j ∈ Finset.range m, max (a ((j : ℤ) + 1) - a (j : ℤ)) 0 :=
      Finset.sum_nonneg fun _ _ => le_max_right _ _
    exact (ENNReal.ofReal_eq_ofReal_iff hnn (by linarith)).1 hsum2
  -- Step 3 : combine
  have habs : ∀ x : ℝ, |x| = 2 * max x 0 - x := by
    intro x
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_neg h, max_eq_right h.le]; ring
  calc ∑ j ∈ Finset.range m, |a ((j : ℤ) + 1) - a (j : ℤ)|
      = ∑ j ∈ Finset.range m,
          (2 * max (a ((j : ℤ) + 1) - a (j : ℤ)) 0 - (a ((j : ℤ) + 1) - a (j : ℤ))) := by
        exact Finset.sum_congr rfl fun j _ => habs _
    _ = 2 * (∑ j ∈ Finset.range m, max (a ((j : ℤ) + 1) - a (j : ℤ)) 0)
          - ∑ j ∈ Finset.range m, (a ((j : ℤ) + 1) - a (j : ℤ)) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 2 * (M - N) := by rw [hascent, htel]; ring

end HumanVerification.CauchyCrofton
