/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.BalancedCombination
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LatticeCoordinates

/-!
# Integer approximation with an exact affine barycenter

A rational affine combination and an integer affine combination of weight
one produce integer combinations of every sufficiently large weight. The
integer correction depends only on the remainder modulo one common
denominator, and therefore has uniformly bounded error.
-/

open scoped BigOperators

namespace EGZ.BalancedCombination

/-- A common denominator for any finite rational family, expressed using
real casts for later quantitative estimates. -/
theorem exists_common_denominator {I : Type*} [Fintype I] (β : I → ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : I → ℤ,
      ∀ i, (b i : ℝ) = (m : ℝ) * (β i : ℝ) := by
  classical
  let m : ℕ := ∏ i, (β i).den
  let b : I → ℤ := fun i ↦ (β i).num *
    (∏ j ∈ ({i} : Finset I)ᶜ, (β j).den : ℕ)
  refine ⟨m, Finset.prod_pos (fun i _ ↦ (β i).den_pos), b, ?_⟩
  intro i
  have hm : m = (β i).den * ∏ j ∈ ({i} : Finset I)ᶜ, (β j).den := by
    simpa only [m] using Fintype.prod_eq_mul_prod_compl i (fun j ↦ (β j).den)
  rw [hm]
  simp only [b, Rat.cast_def]
  push_cast
  field_simp

theorem Data.exists_integer_affine_coefficients {d : ℕ} (D : Data d) :
    ∃ z : D.support → ℤ, (∑ q, z q) = 1 ∧ (∑ q, z q • q.val) = D.center := by
  classical
  obtain ⟨z, hzS, hsum, hvec⟩ :=
    exists_finsupp_affineCombination_of_mem_affineSpan D.center_mem_span
  refine ⟨fun q ↦ z q, ?_, ?_⟩
  · rw [Finset.sum_coe_sort]
    rw [← hsum]
    exact (Finset.sum_subset hzS (fun q _ hq ↦ Finsupp.notMem_support_iff.mp hq)).symm
  · change (∑ q : D.support, (fun v : IntCoord d ↦ z v • v) q) = D.center
    have hcoe := Finset.sum_coe_sort D.support (fun v : IntCoord d ↦ z v • v)
    rw [hcoe, ← hvec]
    exact (Finset.sum_subset hzS (fun q _ hq ↦ by
      rw [Finsupp.notMem_support_iff.mp hq, zero_smul])).symm

/-- Exact integer affine combinations approximate `n * β` with a bounded
error independent of `n`. Positivity is not needed for this algebraic step. -/
theorem Data.exists_integer_approximation {d : ℕ} (D : Data d)
    (β : D.support → ℚ) (hsum : (∑ q, β q) = 1)
    (hvec : ∀ i, (∑ q, β q * (q.val i : ℚ)) = (D.center i : ℚ)) :
    ∃ (A : ℕ → D.support → ℤ) (E : ℝ), 0 ≤ E ∧
      ∀ n : ℕ, (∑ q, A n q) = (n : ℤ) ∧
        (∑ q, A n q • q.val) = (n : ℤ) • D.center ∧
        ∀ q, |(A n q : ℝ) - n * (β q : ℝ)| ≤ E := by
  classical
  obtain ⟨m, hm, b, hb⟩ := exists_common_denominator β
  obtain ⟨z, hzsum, hzvec⟩ := D.exists_integer_affine_coefficients
  have hsumR : (∑ q, (β q : ℝ)) = 1 := by exact_mod_cast hsum
  have hvecR (i : Fin d) : (∑ q, (β q : ℝ) * (q.val i : ℝ)) = (D.center i : ℝ) := by
    exact_mod_cast hvec i
  have hbsum : (∑ q, b q) = (m : ℤ) := by
    have h : (∑ q, (b q : ℝ)) = (m : ℝ) := by
      simp_rw [hb]
      rw [← Finset.mul_sum, hsumR, mul_one]
    exact_mod_cast h
  have hbvec : (∑ q, b q • q.val) = (m : ℤ) • D.center := by
    ext i
    have h : (∑ q, (b q : ℝ) * (q.val i : ℝ)) = (m : ℝ) * (D.center i : ℝ) := by
      simp_rw [hb]
      simpa only [Finset.mul_sum, mul_assoc] using congrArg (fun x : ℝ ↦ (m : ℝ) * x) (hvecR i)
    simpa [Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul] using
      (show (∑ q, b q * q.val i) = (m : ℤ) * D.center i by exact_mod_cast h)
  let A : ℕ → D.support → ℤ := fun n q ↦
    (n / m : ℕ) * b q + (n % m : ℕ) * z q
  let E : ℝ := (m : ℝ) * ∑ q, |(z q : ℝ) - (β q : ℝ)|
  have hE : 0 ≤ E := mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun q _ ↦ abs_nonneg _))
  refine ⟨A, E, hE, ?_⟩
  intro n
  have hnZ : ((n / m : ℕ) : ℤ) * m + ((n % m : ℕ) : ℤ) = n := by
    exact_mod_cast (show n / m * m + n % m = n by simpa [Nat.mul_comm] using Nat.div_add_mod n m)
  have hnR : (n / m : ℕ) * (m : ℝ) + (n % m : ℕ) = (n : ℝ) := by
    exact_mod_cast (show n / m * m + n % m = n by simpa [Nat.mul_comm] using Nat.div_add_mod n m)
  refine ⟨?_, ?_, ?_⟩
  · simp only [A, Finset.sum_add_distrib, ← Finset.mul_sum, hbsum, hzsum, mul_one]
    exact hnZ
  · calc
      (∑ q, A n q • q.val) =
          ((n / m : ℕ) : ℤ) • (∑ q, b q • q.val) + ((n % m : ℕ) : ℤ) • (∑ q, z q • q.val) := by
        simp only [A, add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]
      _ = (n : ℤ) • D.center := by
        rw [hbvec, hzvec, ← mul_smul, ← add_smul, hnZ]
  · intro q
    have heq : (A n q : ℝ) - n * (β q : ℝ) =
        (n % m : ℕ) * ((z q : ℝ) - (β q : ℝ)) := by
      simp only [A, Int.cast_add, Int.cast_mul, Int.cast_natCast, hb]
      rw [← hnR]
      ring
    rw [heq, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n % m))]
    have hr : ((n % m : ℕ) : ℝ) ≤ m := by exact_mod_cast (Nat.mod_lt n hm).le
    calc
      ((n % m : ℕ) : ℝ) * |(z q : ℝ) - (β q : ℝ)| ≤
          (m : ℝ) * |(z q : ℝ) - (β q : ℝ)| :=
        mul_le_mul_of_nonneg_right hr (abs_nonneg _)
      _ ≤ E := mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun q _ ↦ abs_nonneg ((z q : ℝ) - (β q : ℝ))) (Finset.mem_univ q))
        (Nat.cast_nonneg m)

/-- A single positive rational affine combination satisfying all the relaxed
caps yields the balanced integer combinations, with constants independent
of the centrality parameter. -/
theorem Data.exists_coefficients_of_rational {d : ℕ} (D : Data d)
    (ε : ℝ) (hε : 0 < ε) (β : D.support → ℚ)
    (hβ : ∀ q, 0 < β q) (hsum : (∑ q, β q) = 1)
    (hvec : ∀ i, (∑ q, β q * (q.val i : ℚ)) = (D.center i : ℚ))
    (hcap : ∀ θ : ℝ, 0 < θ → IsCentral D.support D.weight θ D.center.real →
      ∀ q, (β q : ℝ) ≤ (1 + ε / 2) * D.weight q / (θ * ∑ r, D.weight r)) :
    ∃ μ : ℝ, ∃ N : ℕ, 0 < μ ∧
      ∀ θ : ℝ, 0 < θ → IsCentral D.support D.weight θ D.center.real →
        ∀ n : ℕ, N < n → Nonempty (Coefficients D ε θ μ n) := by
  classical
  let : Nonempty D.support := D.support_nonempty.to_subtype
  obtain ⟨A, E, hE, hA⟩ := D.exists_integer_approximation β hsum hvec
  let M : ℝ := ∑ q, D.weight q
  have hM : 0 < M := D.totalWeight_pos
  let margin : D.support → ℝ := fun q ↦ min ((β q : ℝ) / 2) (ε / 2 * D.weight q / M)
  let μ : ℝ := Finset.univ.inf' Finset.univ_nonempty margin
  have hμ : 0 < μ := (Finset.lt_inf'_iff _).2 (fun q _ ↦ by
    exact lt_min (div_pos (by exact_mod_cast hβ q) (by norm_num))
      (div_pos (mul_pos (by positivity) (D.weight_pos q)) hM))
  have hμ₁ (q : D.support) : μ ≤ (β q : ℝ) / 2 :=
    (Finset.inf'_le margin (Finset.mem_univ q)).trans (min_le_left _ _)
  have hμ₂ (q : D.support) : μ ≤ ε / 2 * D.weight q / M :=
    (Finset.inf'_le margin (Finset.mem_univ q)).trans (min_le_right _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt (E / μ)
  refine ⟨μ, N, hμ, ?_⟩
  intro θ hθ hcentral n hn
  have hnR : (N : ℝ) < n := by exact_mod_cast hn
  have hEn : E ≤ μ * n := by
    have := (div_lt_iff₀ hμ).mp (hN.trans hnR)
    nlinarith
  have hθone := D.centrality_le_one hcentral
  have hAlo (q : D.support) : μ * n ≤ (A n q : ℝ) := by
    have habs := (abs_le.mp ((hA n).2.2 q)).1
    have hprod := mul_le_mul_of_nonneg_right (hμ₁ q) (Nat.cast_nonneg n)
    nlinarith
  have hAnonneg (q : D.support) : 0 ≤ A n q := by
    have : (0 : ℝ) ≤ A n q := (mul_nonneg hμ.le (Nat.cast_nonneg n)).trans (hAlo q)
    exact_mod_cast this
  let a : D.support → ℕ := fun q ↦ (A n q).toNat
  have haZ (q : D.support) : (a q : ℤ) = A n q := Int.toNat_of_nonneg (hAnonneg q)
  have haR (q : D.support) : (a q : ℝ) = (A n q : ℝ) := by exact_mod_cast haZ q
  refine ⟨{ coeff := a, sum_eq := ?_, weighted_sum_eq := ?_, lower := ?_, upper := ?_ }⟩
  · have : (∑ q, (a q : ℤ)) = (n : ℤ) := by simpa only [haZ] using (hA n).1
    exact_mod_cast this
  · simpa only [← haZ, natCast_zsmul] using (hA n).2.1
  · intro q
    simpa only [haR] using hAlo q
  · intro q
    rw [haR]
    let B : ℝ := D.weight q / (θ * M)
    have hB : 0 < B := div_pos (D.weight_pos q) (mul_pos hθ hM)
    have hbase : D.weight q / M ≤ B :=
      div_le_div_of_nonneg_left (D.weight_pos q).le (mul_pos hθ hM)
        (by nlinarith)
    have hμB : μ ≤ ε / 2 * B := (hμ₂ q).trans (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ ε / 2))
    have hβB : (β q : ℝ) ≤ (1 + ε / 2) * B := by
      simpa only [B, M, mul_div_assoc] using hcap θ hθ hcentral q
    have herror := (abs_le.mp ((hA n).2.2 q)).2
    have hprod₁ := mul_le_mul_of_nonneg_right hμB (Nat.cast_nonneg n)
    have hprod₂ := mul_le_mul_of_nonneg_right hβB (Nat.cast_nonneg n)
    have hupper : (A n q : ℝ) ≤ (1 + ε) * n * B := by nlinarith
    simpa only [B, M, mul_div_assoc] using hupper

end EGZ.BalancedCombination
