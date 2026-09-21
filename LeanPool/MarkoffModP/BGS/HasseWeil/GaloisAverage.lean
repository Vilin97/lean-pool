/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FixedPointAverage
import Mathlib

/-!
# The finite averaging step in the Corvaja--Zannier Hasse--Weil argument

The Galois-closure argument produces finitely many twisted fixed-point error
terms.  Every twist has the same upper bound, while their sum is small.  The
elementary lemma below converts those facts into a two-sided bound for each
individual twist.
-/

namespace BGS.HasseWeil

open scoped BigOperators
open Filter Asymptotics

/-- If every term in a nonempty finite family is at most `B` and the total
sum has absolute value at most `A`, then every term has a two-sided bound.
This is the numerical core of the Galois-twist averaging step. -/
theorem abs_le_of_uniform_upper_and_abs_sum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (i : ι) (A B : ℝ)
    (hB : 0 ≤ B) (hupper : ∀ j, E j ≤ B)
    (hsum : |∑ j, E j| ≤ A) :
    |E i| ≤ A + (Fintype.card ι - 1 : ℕ) * B := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hsum
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have heraseCard : (Finset.univ.erase i).card = Fintype.card ι - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hrest : ∑ j ∈ Finset.univ.erase i, E j ≤
      (Fintype.card ι - 1 : ℕ) * B := by
    calc
      ∑ j ∈ Finset.univ.erase i, E j ≤
          ∑ _j ∈ Finset.univ.erase i, B := by
            exact Finset.sum_le_sum fun j _ => hupper j
      _ = (Fintype.card ι - 1 : ℕ) * B := by
        simp [heraseCard]
  have hsumSplit : ∑ j, E j = E i + ∑ j ∈ Finset.univ.erase i, E j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    ring
  have hlowerSum : -A ≤ ∑ j, E j := (abs_le.mp hsum).1
  have hlower : -(A + (Fintype.card ι - 1 : ℕ) * B) ≤ E i := by
    rw [hsumSplit] at hlowerSum
    linarith
  have hupper' : E i ≤ A + (Fintype.card ι - 1 : ℕ) * B := by
    by_cases hsingleton : Fintype.card ι = 1
    · have huniv : (Finset.univ : Finset ι) = {i} :=
        univ_eq_singleton_of_card_one i hsingleton
      have hEi : |E i| ≤ A := by simpa [huniv] using hsum
      simpa [hsingleton] using (le_trans (le_abs_self (E i)) hEi)
    · have htwo : 2 ≤ Fintype.card ι := by omega
      have hcoefficientNat : 1 ≤ Fintype.card ι - 1 := by omega
      have hcoefficient : (1 : ℝ) ≤ (Fintype.card ι - 1 : ℕ) := by
        exact_mod_cast hcoefficientNat
      calc
        E i ≤ B := hupper i
        _ ≤ (Fintype.card ι - 1 : ℕ) * B := by
          exact le_mul_of_one_le_left hB hcoefficient
        _ ≤ A + (Fintype.card ι - 1 : ℕ) * B := le_add_of_nonneg_left hA
  exact abs_le.mpr ⟨hlower, hupper'⟩

/-- Sequence form of Galois averaging. A uniform `B * rho ^ n` upper bound
for all twists, together with a bounded total error, gives the same geometric
growth rate as a two-sided bound for every twist. -/
theorem abs_twistError_le_geometric_of_uniform_upper_and_abs_sum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ℕ → ι → ℝ) (i : ι) (A B rho : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hrho : 1 ≤ rho)
    (hupper : ∀ n j, E n j ≤ B * rho ^ n)
    (hsum : ∀ n, |∑ j, E n j| ≤ A) (n : ℕ) :
    |E n i| ≤ (A + (Fintype.card ι - 1 : ℕ) * B) * rho ^ n := by
  have hrhoPow : 1 ≤ rho ^ n := one_le_pow₀ hrho
  have hgeometricNonneg : 0 ≤ B * rho ^ n := by positivity
  have hraw := abs_le_of_uniform_upper_and_abs_sum_le
    (E n) i A (B * rho ^ n) hgeometricNonneg (hupper n) (hsum n)
  calc
    |E n i| ≤ A + (Fintype.card ι - 1 : ℕ) * (B * rho ^ n) := hraw
    _ ≤ A * rho ^ n + (Fintype.card ι - 1 : ℕ) * (B * rho ^ n) := by
      gcongr
      simpa using (mul_le_mul_of_nonneg_left hrhoPow hA)
    _ = (A + (Fintype.card ι - 1 : ℕ) * B) * rho ^ n := by ring

/-- The finite averaging estimate gives the geometric `O(rho ^ n)` bound
needed by the zeta-function power-sum argument. -/
theorem twistError_isBigO_geometric_of_uniform_upper_and_abs_sum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ℕ → ι → ℝ) (i : ι) (A B rho : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hrho : 1 ≤ rho)
    (hupper : ∀ n j, E n j ≤ B * rho ^ n)
    (hsum : ∀ n, |∑ j, E n j| ≤ A) :
    (fun n : ℕ ↦ E n i) =O[atTop] fun n : ℕ ↦ rho ^ n := by
  let C : ℝ := A + ((Fintype.card ι - 1 : ℕ) : ℝ) * B
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  apply IsBigO.of_bound C
  filter_upwards [] with n
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (le_trans zero_le_one hrho) n)]
  simpa only [C] using
    abs_twistError_le_geometric_of_uniform_upper_and_abs_sum_le
      E i A B rho hA hB hrho hupper hsum n

/-- If a nonempty finite family is uniformly close to `center` and its sum
is close to `card · base`, then `base` is close to `center`.  The deliberately
division-free bound is convenient for integral point counts and is uniform
when the family cardinality is fixed. -/
theorem abs_base_sub_center_le_of_average_and_pointwise
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x : ι → ℝ) (base center A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haverage : |∑ i, x i - (Fintype.card ι : ℝ) * base| ≤ A)
    (hpointwise : ∀ i, |x i - center| ≤ B) :
    |base - center| ≤ A + (Fintype.card ι : ℝ) * B := by
  have hcardNat : 1 ≤ Fintype.card ι :=
    Fintype.card_pos_iff.mpr inferInstance
  have hcard : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast hcardNat
  have hsum : |∑ i, (x i - center)| ≤
      (Fintype.card ι : ℝ) * B := by
    calc
      |∑ i, (x i - center)| ≤ ∑ i, |x i - center| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, B := Finset.sum_le_sum fun i _ => hpointwise i
      _ = (Fintype.card ι : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hscaled : |(Fintype.card ι : ℝ) * (base - center)| ≤
      A + (Fintype.card ι : ℝ) * B := by
    have hid : (Fintype.card ι : ℝ) * (base - center) =
        -(∑ i, x i - (Fintype.card ι : ℝ) * base) +
          ∑ i, (x i - center) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring
    rw [hid]
    calc
      |-(∑ i, x i - (Fintype.card ι : ℝ) * base) +
          ∑ i, (x i - center)| ≤
          |-(∑ i, x i - (Fintype.card ι : ℝ) * base)| +
            |∑ i, (x i - center)| := abs_add_le _ _
      _ ≤ A + (Fintype.card ι : ℝ) * B := by
        gcongr
        simpa only [abs_neg] using haverage
  have hnonneg : 0 ≤ |base - center| := abs_nonneg _
  calc
    |base - center| ≤
        (Fintype.card ι : ℝ) * |base - center| := by
      nlinarith
    _ = |(Fintype.card ι : ℝ) * (base - center)| := by
      rw [abs_mul, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ Fintype.card ι)]
    _ ≤ A + (Fintype.card ι : ℝ) * B := hscaled

end BGS.HasseWeil
