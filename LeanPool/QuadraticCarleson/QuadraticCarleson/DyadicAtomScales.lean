/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Order.CompletePartialOrder

/-!
# Exact dyadic scale classes for Calderón--Zygmund atoms

We use the following half-open convention:

`I ∈ 𝓘_j ↔ 2^j ≤ ℓ_I ∧ ℓ_I < 2^(j+1)`.

In particular, the classes are half-open: the lower endpoint belongs to the
class and the upper endpoint belongs to the next class. This file develops
that convention for an abstract atom type equipped with a positive real
length.
-/

@[expose] public section

open Set

namespace QuadraticCarleson


/-- The exact half-open dyadic scale class fixed by the author. -/
def dyadicAtomScaleClass {ι : Type*} (length : ι → ℝ) (j : ℤ) : Set ι :=
  {I | (2 : ℝ) ^ j ≤ length I ∧ length I < (2 : ℝ) ^ (j + 1)}

@[simp]
theorem mem_dyadicAtomScaleClass_iff {ι : Type*} {length : ι → ℝ}
    {I : ι} {j : ℤ} :
    I ∈ dyadicAtomScaleClass length j ↔
      (2 : ℝ) ^ j ≤ length I ∧ length I < (2 : ℝ) ^ (j + 1) :=
  Iff.rfl

/-- Every positive real number has a unique half-open dyadic scale. -/
theorem existsUnique_dyadicScale (ell : ℝ) (hell : 0 < ell) :
    ∃! j : ℤ, (2 : ℝ) ^ j ≤ ell ∧ ell < (2 : ℝ) ^ (j + 1) := by
  obtain ⟨j, hj⟩ := exists_mem_Ico_zpow hell (by norm_num : (1 : ℝ) < 2)
  refine ⟨j, hj, fun k hk ↦ ?_⟩
  apply le_antisymm
  · by_contra hnot
    have hjk : j + 1 ≤ k := by omega
    have hp : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ k :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2 hjk
    exact (not_lt_of_ge (hp.trans hk.1)) hj.2
  · by_contra hnot
    have hkj : k + 1 ≤ j := by omega
    have hp : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ j :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2 hkj
    exact (not_lt_of_ge (hp.trans hj.1)) hk.2

/-- Every positive-length atom belongs to a unique scale class. -/
theorem existsUnique_mem_dyadicAtomScaleClass
    {ι : Type*} (length : ι → ℝ) (hlength : ∀ I, 0 < length I) (I : ι) :
    ∃! j : ℤ, I ∈ dyadicAtomScaleClass length j := by
  simpa [dyadicAtomScaleClass] using existsUnique_dyadicScale (length I) (hlength I)

/-- The unique scale index of a positive-length atom. -/
noncomputable def dyadicAtomScaleIndex
    {ι : Type*} (length : ι → ℝ) (hlength : ∀ I, 0 < length I) (I : ι) : ℤ :=
  Classical.choose (existsUnique_mem_dyadicAtomScaleClass length hlength I)

theorem dyadicAtomScaleIndex_mem
    {ι : Type*} (length : ι → ℝ) (hlength : ∀ I, 0 < length I) (I : ι) :
    I ∈ dyadicAtomScaleClass length (dyadicAtomScaleIndex length hlength I) :=
  (Classical.choose_spec (existsUnique_mem_dyadicAtomScaleClass length hlength I)).1

theorem dyadicAtomScaleIndex_unique
    {ι : Type*} (length : ι → ℝ) (hlength : ∀ I, 0 < length I)
    {I : ι} {j : ℤ} (hI : I ∈ dyadicAtomScaleClass length j) :
    j = dyadicAtomScaleIndex length hlength I :=
  (Classical.choose_spec (existsUnique_mem_dyadicAtomScaleClass length hlength I)).2 j hI

theorem mem_dyadicAtomScaleClass_iff_index_eq
    {ι : Type*} (length : ι → ℝ) (hlength : ∀ I, 0 < length I)
    {I : ι} {j : ℤ} :
    I ∈ dyadicAtomScaleClass length j ↔
      dyadicAtomScaleIndex length hlength I = j := by
  constructor
  · intro hI
    exact (dyadicAtomScaleIndex_unique length hlength hI).symm
  · intro h
    rw [← h]
    exact dyadicAtomScaleIndex_mem length hlength I

/-- The dyadic classes cover all atoms. -/
theorem iUnion_dyadicAtomScaleClass_eq_univ
    {ι : Type*} (length : ι → ℝ) (hlength : ∀ I, 0 < length I) :
    ⋃ j : ℤ, dyadicAtomScaleClass length j = (Set.univ : Set ι) := by
  ext I
  simp only [mem_iUnion, mem_univ, iff_true]
  exact (existsUnique_mem_dyadicAtomScaleClass length hlength I).exists

/-- Distinct dyadic scale classes are disjoint. -/
theorem disjoint_dyadicAtomScaleClass
    {ι : Type*} (length : ι → ℝ) (hlength : ∀ I, 0 < length I)
    {j k : ℤ} (hjk : j ≠ k) :
    Disjoint (dyadicAtomScaleClass length j) (dyadicAtomScaleClass length k) := by
  rw [Set.disjoint_left]
  intro I hIj hIk
  exact hjk ((existsUnique_mem_dyadicAtomScaleClass length hlength I).unique hIj hIk)

/-- Pairwise-disjoint formulation of the partition. -/
theorem pairwiseDisjoint_dyadicAtomScaleClass
    {ι : Type*} (length : ι → ℝ) (hlength : ∀ I, 0 < length I) :
    Pairwise fun j k : ℤ ↦
      Disjoint (dyadicAtomScaleClass length j) (dyadicAtomScaleClass length k) := by
  intro j k hjk
  exact disjoint_dyadicAtomScaleClass length hlength hjk

theorem dyadicAtomScaleClass_length_lower
    {ι : Type*} {length : ι → ℝ} {I : ι} {j : ℤ}
    (hI : I ∈ dyadicAtomScaleClass length j) :
    (2 : ℝ) ^ j ≤ length I :=
  hI.1

theorem dyadicAtomScaleClass_length_upper
    {ι : Type*} {length : ι → ℝ} {I : ι} {j : ℤ}
    (hI : I ∈ dyadicAtomScaleClass length j) :
    length I < (2 : ℝ) ^ (j + 1) :=
  hI.2

/-- Equivalent normalized-length formulation: `1 ≤ ℓ_I / 2^j < 2`. -/
theorem mem_dyadicAtomScaleClass_iff_normalized
    {ι : Type*} {length : ι → ℝ} {I : ι} {j : ℤ} :
    I ∈ dyadicAtomScaleClass length j ↔
      1 ≤ length I / (2 : ℝ) ^ j ∧ length I / (2 : ℝ) ^ j < 2 := by
  have hj : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  rw [mem_dyadicAtomScaleClass_iff]
  constructor
  · intro h
    constructor
    · exact (le_div_iff₀ hj).2 (by simpa using h.1)
    · apply (div_lt_iff₀ hj).2
      rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at h
      nlinarith
  · intro h
    constructor
    · simpa using (le_div_iff₀ hj).1 h.1
    · rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      simpa [mul_comm] using (div_lt_iff₀ hj).1 h.2

/-- Equality at a lower endpoint belongs to that class. -/
theorem mem_dyadicAtomScaleClass_of_length_eq_lower
    {ι : Type*} {length : ι → ℝ} {I : ι} {j : ℤ}
    (hI : length I = (2 : ℝ) ^ j) :
    I ∈ dyadicAtomScaleClass length j := by
  rw [mem_dyadicAtomScaleClass_iff, hI]
  exact ⟨le_rfl, (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2 (by omega)⟩

/-- Equality at an upper endpoint belongs to the next class, not the current
one. -/
theorem mem_dyadicAtomScaleClass_succ_of_length_eq_upper
    {ι : Type*} {length : ι → ℝ} {I : ι} {j : ℤ}
    (hI : length I = (2 : ℝ) ^ (j + 1)) :
    I ∈ dyadicAtomScaleClass length (j + 1) :=
  mem_dyadicAtomScaleClass_of_length_eq_lower hI

theorem not_mem_dyadicAtomScaleClass_of_length_eq_upper
    {ι : Type*} {length : ι → ℝ} {I : ι} {j : ℤ}
    (hI : length I = (2 : ℝ) ^ (j + 1)) :
    I ∉ dyadicAtomScaleClass length j := by
  intro hmem
  exact (lt_irrefl _ : ¬(2 : ℝ) ^ (j + 1) < (2 : ℝ) ^ (j + 1)) (hI ▸ hmem.2)

/-- Atom length is strictly less than twice its lower dyadic scale. -/
theorem dyadicAtomScaleClass_length_lt_two_mul
    {ι : Type*} {length : ι → ℝ} {I : ι} {j : ℤ}
    (hI : I ∈ dyadicAtomScaleClass length j) :
    length I < 2 * (2 : ℝ) ^ j := by
  have hu := hI.2
  rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at hu
  simpa [mul_comm] using hu

/-- Lengths in one scale class differ by a factor strictly smaller than two. -/
theorem dyadicAtomScaleClass_lengths_comparable
    {ι : Type*} {length : ι → ℝ} {I J : ι} {j : ℤ}
    (hI : I ∈ dyadicAtomScaleClass length j)
    (hJ : J ∈ dyadicAtomScaleClass length j) :
    length I < 2 * length J ∧ length J < 2 * length I := by
  constructor
  · exact (dyadicAtomScaleClass_length_lt_two_mul hI).trans_le
      (mul_le_mul_of_nonneg_left hJ.1 (by norm_num))
  · exact (dyadicAtomScaleClass_length_lt_two_mul hJ).trans_le
      (mul_le_mul_of_nonneg_left hI.1 (by norm_num))

/-- Reciprocal bounds corresponding exactly to the half-open length bounds. -/
theorem dyadicAtomScaleClass_reciprocal_bounds
    {ι : Type*} {length : ι → ℝ} (hlength : ∀ I, 0 < length I)
    {I : ι} {j : ℤ} (hI : I ∈ dyadicAtomScaleClass length j) :
    ((2 : ℝ) ^ (j + 1))⁻¹ < (length I)⁻¹ ∧
      (length I)⁻¹ ≤ ((2 : ℝ) ^ j)⁻¹ := by
  constructor
  · exact (inv_lt_inv₀ (zpow_pos (by norm_num) _) (hlength I)).2 hI.2
  · exact (inv_le_inv₀ (hlength I) (zpow_pos (by norm_num) _)).2 hI.1

/-- Squared scale bounds used for quadratic oscillation. -/
theorem dyadicAtomScaleClass_sq_bounds
    {ι : Type*} {length : ι → ℝ} (hlength : ∀ I, 0 < length I)
    {I : ι} {j : ℤ} (hI : I ∈ dyadicAtomScaleClass length j) :
    (2 : ℝ) ^ (2 * j) ≤ (length I) ^ 2 ∧
      (length I) ^ 2 < (2 : ℝ) ^ (2 * (j + 1)) := by
  constructor
  · rw [show (2 : ℝ) ^ (2 * j) = ((2 : ℝ) ^ j) ^ 2 by
      rw [show 2 * j = j + j by ring, zpow_add₀ (by norm_num)]; ring]
    exact pow_le_pow_left₀ (zpow_nonneg (by norm_num) _) hI.1 2
  · rw [show (2 : ℝ) ^ (2 * (j + 1)) = ((2 : ℝ) ^ (j + 1)) ^ 2 by
      rw [show 2 * (j + 1) = (j + 1) + (j + 1) by ring,
        zpow_add₀ (by norm_num)]; ring]
    exact (sq_lt_sq₀ (hlength I).le
      (zpow_pos (by norm_num : (0 : ℝ) < 2) (j + 1)).le).2 hI.2

/-- Ordering atom lengths orders their dyadic scale indices. -/
theorem dyadicAtomScale_mono_of_length_le
    {ι : Type*} {length : ι → ℝ} {I J : ι} {j k : ℤ}
    (hI : I ∈ dyadicAtomScaleClass length j)
    (hJ : J ∈ dyadicAtomScaleClass length k)
    (hIJ : length I ≤ length J) : j ≤ k := by
  by_contra hnot
  have hkj : k + 1 ≤ j := by omega
  have hp : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ j :=
    (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2 hkj
  have hJI : length J < length I := hJ.2.trans_le (hp.trans hI.1)
  exact (not_lt_of_ge hIJ) hJI

theorem dyadicAtomScaleIndex_mono_of_length_le
    {ι : Type*} (length : ι → ℝ) (hlength : ∀ I, 0 < length I)
    {I J : ι} (hIJ : length I ≤ length J) :
    dyadicAtomScaleIndex length hlength I ≤
      dyadicAtomScaleIndex length hlength J :=
  dyadicAtomScale_mono_of_length_le
    (dyadicAtomScaleIndex_mem length hlength I)
    (dyadicAtomScaleIndex_mem length hlength J) hIJ

/-- Strictly separated scale classes have strictly separated lengths. -/
theorem length_lt_of_dyadicAtomScale_lt
    {ι : Type*} {length : ι → ℝ} {I J : ι} {j k : ℤ}
    (hI : I ∈ dyadicAtomScaleClass length j)
    (hJ : J ∈ dyadicAtomScaleClass length k) (hjk : j < k) :
    length I < length J := by
  have hp : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ k :=
    (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2 (by omega)
  exact hI.2.trans_le (hp.trans hJ.1)

/-- A gap of `d+1` dyadic generations gives the geometric separation
`2^d ℓ_I < ℓ_J`. -/
theorem pow_mul_length_lt_of_dyadicAtomScale_gap
    {ι : Type*} {length : ι → ℝ} {I J : ι} {j k : ℤ} (d : ℕ)
    (hI : I ∈ dyadicAtomScaleClass length j)
    (hJ : J ∈ dyadicAtomScaleClass length k)
    (hgap : j + (d : ℤ) + 1 ≤ k) :
    (2 : ℝ) ^ d * length I < length J := by
  have hmul := mul_lt_mul_of_pos_left hI.2
    (pow_pos (by norm_num : (0 : ℝ) < 2) d)
  have heq : (2 : ℝ) ^ d * (2 : ℝ) ^ (j + 1) =
      (2 : ℝ) ^ (j + (d : ℤ) + 1) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [heq] at hmul
  have hp : (2 : ℝ) ^ (j + (d : ℤ) + 1) ≤ (2 : ℝ) ^ k :=
    (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2 hgap
  exact hmul.trans_le (hp.trans hJ.1)

end QuadraticCarleson
