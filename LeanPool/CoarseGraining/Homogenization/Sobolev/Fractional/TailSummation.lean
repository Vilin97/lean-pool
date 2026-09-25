/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.Constants

/-!
# Backwards geometric tail summation

The per-pair scale accounting of the Besov-to-Gagliardo direction: summing the
coefficients `q^j` over any finite set of depths on which `q^j` is bounded by
`M` costs at most `2 * M`, provided the ratio `q` is at least `3`.  Applied
with `q = 3^{s p + d}` and `M = (dist x y)^{-(s p + d)}-ish` this is the
geometric tail that makes the comparison constant dimensional.
-/

@[expose] public section

namespace Homogenization
namespace Gagliardo

open scoped ENNReal BigOperators

/-- Backwards geometric summation: if every term `q^j`, `j ∈ F`, is bounded by
`M` and the ratio satisfies `3 ≤ q < ∞`, then the total is at most `2 * M`. -/
theorem sum_pow_le_two_mul_of_forall_le {q : ℝ≥0∞} (hq3 : 3 ≤ q) (hqt : q ≠ ∞)
    {M : ℝ≥0∞} {F : Finset ℕ} (hF : ∀ j ∈ F, q ^ j ≤ M) :
    (∑ j ∈ F, q ^ j) ≤ 2 * M := by
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · simp [hFe]
  · have hq0 : q ≠ 0 := by
      intro h
      rw [h] at hq3
      exact (by norm_num : ¬ (3 : ℝ≥0∞) ≤ 0) hq3
    obtain ⟨n, hnF, hnmax⟩ := F.exists_max_image id hFne
    have hsub : F ⊆ Finset.range (n + 1) := by
      intro j hj
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (hnmax j hj))
    have hstep : (∑ j ∈ F, q ^ j) ≤ ∑ j ∈ Finset.range (n + 1), q ^ j :=
      Finset.sum_le_sum_of_subset hsub
    refine hstep.trans ?_
    -- reflect the range sum and compare with the geometric series in `q⁻¹`
    have hreflect : (∑ j ∈ Finset.range (n + 1), q ^ j)
        = ∑ k ∈ Finset.range (n + 1), q ^ (n - k) := by
      exact (Finset.sum_range_reflect (fun j => q ^ j) (n + 1)).symm
    have hterm : ∀ k ∈ Finset.range (n + 1), q ^ (n - k) ≤ q ^ n * (q⁻¹) ^ k := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hpow : q ^ (n - k) * q ^ k = q ^ n := by
        rw [← pow_add, Nat.sub_add_cancel hkn]
      have hqk0 : q ^ k ≠ 0 := pow_ne_zero k hq0
      have hqkt : q ^ k ≠ ∞ := ENNReal.pow_ne_top hqt
      have : q ^ (n - k) = q ^ n * (q ^ k)⁻¹ := by
        rw [← hpow, mul_assoc, ENNReal.mul_inv_cancel hqk0 hqkt, mul_one]
      rw [this, ENNReal.inv_pow]
    have hgeom : (∑ k ∈ Finset.range (n + 1), (q⁻¹) ^ k) ≤ 2 := by
      refine sum_range_pow_le_two_of_le_third ?_ (n + 1)
      exact ENNReal.inv_le_inv.2 hq3
    calc (∑ j ∈ Finset.range (n + 1), q ^ j)
        = ∑ k ∈ Finset.range (n + 1), q ^ (n - k) := hreflect
      _ ≤ ∑ k ∈ Finset.range (n + 1), q ^ n * (q⁻¹) ^ k :=
          Finset.sum_le_sum hterm
      _ = q ^ n * ∑ k ∈ Finset.range (n + 1), (q⁻¹) ^ k := by
          rw [Finset.mul_sum]
      _ ≤ q ^ n * 2 := mul_le_mul_right hgeom _
      _ ≤ M * 2 := mul_le_mul_left (hF n hnF) _
      _ = 2 * M := mul_comm _ _

end Gagliardo
end Homogenization
