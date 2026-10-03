/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyRademacherMenshov

/-!
# Ordered finite energy bookkeeping

An exact finite double-sum decomposition separates diagonal energy from
strictly lower-rank cross rows. The result applies to arbitrary coefficients
of absolute value at most one, without assuming a signed-sum estimate.
-/

@[expose] public section

namespace QuadraticCarleson.KrauseLaceyOrderedEnergy


theorem sum_abs_inner_eq_diagonal_add_crossRows
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset ι) (v : ι → E) (rank : ι → ℤ)
    (heq : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → rank i = rank j → inner ℝ (v i) (v j) = 0) :
    (∑ i ∈ S, ∑ j ∈ S, |inner ℝ (v i) (v j)|) =
      (∑ i ∈ S, ‖v i‖ ^ 2) +
        2 * ∑ i ∈ S, ∑ j ∈ S.filter (fun j ↦ rank j < rank i),
          |inner ℝ (v i) (v j)| := by
  classical
  have hpair (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      |inner ℝ (v i) (v j)| =
        (if rank j < rank i then |inner ℝ (v i) (v j)| else 0) +
        (if rank i < rank j then |inner ℝ (v i) (v j)| else 0) +
        (if i = j then ‖v i‖ ^ 2 else 0) := by
    by_cases hij : i = j
    · subst j
      simp []
    · by_cases hlt : rank j < rank i
      · simp [hij, hlt, not_lt_of_ge hlt.le]
      · by_cases hgt : rank i < rank j
        · simp [hij, hlt, hgt]
        · have hr : rank i = rank j := by omega
          simp [hij, hlt, hgt, heq i hi j hj hij hr]
  have hswap :
      (∑ i ∈ S, ∑ j ∈ S, if rank i < rank j then |inner ℝ (v i) (v j)| else 0) =
      ∑ i ∈ S, ∑ j ∈ S, if rank j < rank i then |inner ℝ (v i) (v j)| else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm (v i) (v j)]
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S,
        ((if rank j < rank i then |inner ℝ (v i) (v j)| else 0) +
        (if rank i < rank j then |inner ℝ (v i) (v j)| else 0) +
        (if i = j then ‖v i‖ ^ 2 else 0)) := by
      exact Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ hpair i hi j hj
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [hswap]
      simp_rw [Finset.sum_ite_eq, Finset.sum_filter]
      have hdiag : (∑ i ∈ S, if i ∈ S then ‖v i‖ ^ 2 else 0) =
          ∑ i ∈ S, ‖v i‖ ^ 2 := Finset.sum_congr rfl fun i hi ↦ ite_eq_left hi
      rw [hdiag]
      ring

theorem signed_sum_sq_le_diagonal_add_crossRows
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset ι) (v : ι → E) (rank : ι → ℤ)
    (heq : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → rank i = rank j → inner ℝ (v i) (v j) = 0)
    (c : ι → ℝ) (hc : ∀ i ∈ S, |c i| ≤ 1) :
    ‖∑ i ∈ S, c i • v i‖ ^ 2 ≤
      (∑ i ∈ S, ‖v i‖ ^ 2) +
        2 * ∑ i ∈ S, ∑ j ∈ S.filter (fun j ↦ rank j < rank i),
          |inner ℝ (v i) (v j)| := by
  rw [← sum_abs_inner_eq_diagonal_add_crossRows S v rank heq,
    ← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  calc
    c i * (c j * inner ℝ (v i) (v j)) ≤ |c i * (c j * inner ℝ (v i) (v j))| :=
      le_abs_self _
    _ = (|c i| * |c j|) * |inner ℝ (v i) (v j)| := by rw [abs_mul, abs_mul]; ring
    _ ≤ 1 * |inner ℝ (v i) (v j)| := mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right (hc i hi) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hc j hj)) (abs_nonneg _)
    _ = _ := one_mul _


/-- Assemble residue-class energy from diagonal, separated-row and orthogonality bounds. -/
theorem signed_sum_sq_le_mass_of_residue_bounds
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset ι) (v : ι → E) (rank : ι → ℤ) (mass : ι → ℝ)
    (diagonalCoefficient rowCoefficient : ℝ)
    (hmod : ∀ i ∈ S, ∀ j ∈ S, rank i % 3 = rank j % 3)
    (heq : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → rank i = rank j → inner ℝ (v i) (v j) = 0)
    (hdiag : (∑ i ∈ S, ‖v i‖ ^ 2) ≤ diagonalCoefficient * ∑ i ∈ S, mass i)
    (hrow : ∀ i ∈ S,
      (∑ j ∈ S.filter (fun j ↦ rank j + 3 ≤ rank i), |inner ℝ (v i) (v j)|) ≤
        rowCoefficient * mass i)
    (c : ι → ℝ) (hc : ∀ i ∈ S, |c i| ≤ 1) :
    ‖∑ i ∈ S, c i • v i‖ ^ 2 ≤
      (diagonalCoefficient + 2 * rowCoefficient) * ∑ i ∈ S, mass i := by
  classical
  have hfilter (i : ι) (hi : i ∈ S) :
      S.filter (fun j ↦ rank j < rank i) = S.filter (fun j ↦ rank j + 3 ≤ rank i) := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · intro hj
      have hm := hmod i hi j hj.1
      exact ⟨hj.1, by omega⟩
    · intro hj
      exact ⟨hj.1, by omega⟩
  have hrows :
      (∑ i ∈ S, ∑ j ∈ S.filter (fun j ↦ rank j < rank i), |inner ℝ (v i) (v j)|) ≤
        rowCoefficient * ∑ i ∈ S, mass i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [hfilter i hi]
    exact hrow i hi
  calc
    _ ≤ (∑ i ∈ S, ‖v i‖ ^ 2) +
        2 * ∑ i ∈ S, ∑ j ∈ S.filter (fun j ↦ rank j < rank i),
          |inner ℝ (v i) (v j)| := signed_sum_sq_le_diagonal_add_crossRows S v rank heq c hc
    _ ≤ diagonalCoefficient * (∑ i ∈ S, mass i) +
        2 * (rowCoefficient * ∑ i ∈ S, mass i) :=
      add_le_add hdiag (mul_le_mul_of_nonneg_left hrows (by norm_num))
    _ = _ := by ring


/-- Combine finite colour-class energy bounds without repeating the analytic argument. -/
theorem norm_sum_sq_le_of_finite_partition
    {ι E : Type*} [NormedAddCommGroup E]
    (S : Finset ι) (v : ι → E) (mass : ι → ℝ) (colour : ι → Fin 3) (C : ℝ)
    (hbound : ∀ r : Fin 3,
      ‖∑ i ∈ S.filter (fun i => colour i = r), v i‖ ^ 2 ≤
        C * ∑ i ∈ S.filter (fun i => colour i = r), mass i) :
    ‖∑ i ∈ S, v i‖ ^ 2 ≤ (3 * C) * ∑ i ∈ S, mass i := by
  classical
  let R (r : Fin 3) := S.filter fun i => colour i = r
  let w (r : Fin 3) := ∑ i ∈ R r, v i
  have hsum : (∑ i ∈ S, v i) = ∑ r : Fin 3, w r :=
    (Finset.sum_fiberwise_of_maps_to (fun i (_ : i ∈ S) =>
      Finset.mem_univ (colour i)) _).symm
  rw [hsum]
  calc
    _ ≤ (∑ r : Fin 3, ‖w r‖) ^ 2 := by gcongr; exact norm_sum_le _ _
    _ ≤ 3 * ∑ r : Fin 3, ‖w r‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun r : Fin 3 => ‖w r‖)
    _ ≤ 3 * ∑ r : Fin 3, C * ∑ i ∈ R r, mass i := by
      gcongr with r
      exact hbound r
    _ = _ := by
      rw [← Finset.mul_sum]
      have hm : (∑ r : Fin 3, ∑ i ∈ R r, mass i) = ∑ i ∈ S, mass i :=
        Finset.sum_fiberwise_of_maps_to (fun i (_ : i ∈ S) =>
          Finset.mem_univ (colour i)) _
      rw [hm]
      ring

end QuadraticCarleson.KrauseLaceyOrderedEnergy
