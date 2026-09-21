/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.BohrUnion

/-!
# Size of an arbitrary large-frequency localized Bohr set

The size observation preceding Lemma `l:bohrintersection` in the paper is
proved for every natural frequency at least one hundred. No divisibility
condition is imposed. The radius range here includes the paper's range.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson


private def bohrRightCell (k a : ℕ) (ρ : ℝ) : Set ℝ :=
  Ico ((a : ℝ) / k) (((a : ℝ) + ρ) / k)

private theorem bohrRightCell_subset {k a : ℕ} {ρ : ℝ}
    (hk : 0 < k) (ha₁ : k ≤ 4 * a) (ha₂ : 2 * (a + 1) ≤ k) (hρ : ρ ≤ 1) :
    bohrRightCell k a ρ ⊆ bohrSet k ρ := by
  intro x hx
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have ha₁' : (k : ℝ) ≤ 4 * a := by exact_mod_cast ha₁
  have ha₂' : 2 * ((a : ℝ) + 1) ≤ k := by exact_mod_cast ha₂
  have hx₁ := (div_le_iff₀ hk').mp hx.1
  have hx₂ := (lt_div_iff₀ hk').mp hx.2
  constructor
  · constructor <;> nlinarith
  · have hfract : Int.fract ((k : ℝ) * x) = (k : ℝ) * x - a := by
      apply Int.fract_eq_iff.mpr
      refine ⟨by nlinarith, by nlinarith, ⟨(a : ℤ), ?_⟩⟩
      push_cast
      ring
    change min (Int.fract ((k : ℝ) * x)) (1 - Int.fract ((k : ℝ) * x)) ≤ ρ
    rw [hfract]
    exact (min_le_left _ _).trans (by nlinarith)

/-- A lower size bound at every sufficiently large frequency, obtained from
disjoint right halves of the interior integer cells. -/
theorem bohrSet_volume_real_ge {k : ℕ} {ρ : ℝ}
    (hk : 100 ≤ k) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1) :
    ρ / 8 ≤ volume.real (bohrSet k ρ) := by
  classical
  let n := k / 4 - 1
  let a : ℕ → ℕ := fun j ↦ k / 4 + 1 + j
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcount : k ≤ 8 * n := by dsimp [n]; omega
  have hcount' : (k : ℝ) ≤ 8 * n := by exact_mod_cast hcount
  have hdisj : PairwiseDisjoint (↑(Finset.range n) : Set ℕ)
      (fun j ↦ bohrRightCell k (a j) ρ) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi₁ := (div_le_iff₀ hk').mp hxi.1
    have hi₂ := (lt_div_iff₀ hk').mp hxi.2
    have hj₁ := (div_le_iff₀ hk').mp hxj.1
    have hj₂ := (lt_div_iff₀ hk').mp hxj.2
    dsimp [a] at hi₁ hi₂ hj₁ hj₂
    push_cast at hi₁ hi₂ hj₁ hj₂
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      linarith
    · have hji' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
      linarith
  have hcell : ∀ j, volume.real (bohrRightCell k (a j) ρ) = ρ / k := by
    intro j
    dsimp [bohrRightCell]
    rw [Real.volume_real_Ico_of_le]
    · ring
    · exact div_le_div_of_nonneg_right (by linarith) hk'.le
  have hsub : (⋃ j ∈ Finset.range n, bohrRightCell k (a j) ρ) ⊆ bohrSet k ρ := by
    apply iUnion₂_subset
    intro j hj
    have hj' := Finset.mem_range.mp hj
    apply bohrRightCell_subset (by omega) _ _ hρ
    · dsimp [a]; omega
    · dsimp [a, n] at *; omega
  calc
    ρ / 8 ≤ (n : ℝ) * (ρ / k) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hk').mpr
      nlinarith [mul_le_mul_of_nonneg_left hcount' hρ0]
    _ = ∑ j ∈ Finset.range n, volume.real (bohrRightCell k (a j) ρ) := by
      simp [hcell]
    _ = volume.real (⋃ j ∈ Finset.range n, bohrRightCell k (a j) ρ) := by
      symm
      exact measureReal_biUnion_finset hdisj (fun _ _ ↦ measurableSet_Ico)
        (fun _ _ ↦ by simp [bohrRightCell])
    _ ≤ volume.real (bohrSet k ρ) :=
      measureReal_mono hsub
        (measure_ne_top_of_subset (bohrSet_subset_Ico k ρ) (by simp))

private theorem bohrSet_subset_integerCover {k : ℕ} {ρ : ℝ}
    (hk : 0 < k) (hρ : ρ < 1 / 10) :
    bohrSet k ρ ⊆ ⋃ a ∈ Finset.range (k + 1),
      Icc (((a : ℝ) - ρ) / k) (((a : ℝ) + ρ) / k) := by
  intro x hx
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨a, ha0, hak, ha⟩ := exists_int_near_of_mem_bohrSet hρ hx
  have hato : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
  have hato' : (a.toNat : ℝ) = (a : ℝ) := by exact_mod_cast hato
  have hak' : a.toNat ≤ k := by exact_mod_cast (hato ▸ hak)
  refine mem_iUnion₂.mpr ⟨a.toNat, Finset.mem_range.mpr (by omega), ?_⟩
  rw [hato']
  have ha' := abs_le.mp ha
  constructor
  · apply (div_le_iff₀ hk').mpr
    nlinarith
  · apply (le_div_iff₀ hk').mpr
    nlinarith

/-- Covering by the `k + 1` nearby-integer intervals gives a uniform upper
bound at every positive natural frequency. -/
theorem bohrSet_volume_real_le {k : ℕ} {ρ : ℝ}
    (hk : 0 < k) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 10) :
    volume.real (bohrSet k ρ) ≤ 4 * ρ := by
  classical
  let J : ℕ → Set ℝ := fun a ↦
    Icc (((a : ℝ) - ρ) / k) (((a : ℝ) + ρ) / k)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcover : bohrSet k ρ ⊆ ⋃ a ∈ Finset.range (k + 1), J a :=
    bohrSet_subset_integerCover hk hρ
  have hfinite : volume (⋃ a ∈ Finset.range (k + 1), J a) ≠ ∞ := by
    apply ne_of_lt
    exact (measure_biUnion_finset_le _ _).trans_lt
      (ENNReal.sum_lt_top.mpr fun a _ ↦ by simp [J])
  have hJ : ∀ a, volume.real (J a) = 2 * ρ / k := by
    intro a
    dsimp [J]
    rw [Real.volume_real_Icc_of_le]
    · ring
    · exact div_le_div_of_nonneg_right (by linarith) hk'.le
  calc
    volume.real (bohrSet k ρ) ≤ volume.real (⋃ a ∈ Finset.range (k + 1), J a) :=
      measureReal_mono hcover hfinite
    _ ≤ ∑ a ∈ Finset.range (k + 1), volume.real (J a) :=
      measureReal_biUnion_finset_le _ _
    _ = ((k : ℝ) + 1) * (2 * ρ / k) := by simp [hJ]
    _ ≤ 4 * ρ := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hk').mpr
      nlinarith [mul_le_mul_of_nonneg_left hk1 hρ0]

/-- The comparability stated immediately after the paper's Bohr-set
definition, with explicit absolute constants. The paper's radius range
`0 < ρ < 1/100` is contained in the range proved here. -/
theorem bohrSet_volume_real_comparable {k : ℕ} {ρ : ℝ}
    (hk : 100 ≤ k) (hρ0 : 0 < ρ) (hρ : ρ < 1 / 10) :
    ρ / 8 ≤ volume.real (bohrSet k ρ) ∧ volume.real (bohrSet k ρ) ≤ 4 * ρ :=
  ⟨bohrSet_volume_real_ge hk hρ0.le (by linarith),
    bohrSet_volume_real_le (by omega) hρ0.le hρ⟩


end QuadraticCarleson
