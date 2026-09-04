/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.QuantumParallelRepetition.Part01
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Quantum parallel repetition, part 02 -/

noncomputable section

namespace QuantumParallelRepetition

/-- The local matrix norm instance used while elaborating part two. -/
noncomputable local instance matrixComplexContinuousENormPartTwo
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open scoped BigOperators

theorem harmonicNumber_eq_harmonic (n : ℕ) :
    harmonicNumber n = (harmonic n : ℝ) := by
  unfold harmonicNumber harmonic
  rw [Finset.sum_fin_eq_sum_range]
  simp only [Rat.cast_sum, Rat.cast_inv, Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range.mp hi, ↓reduceDIte, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]

theorem harmonicNumber_log_lower (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ harmonicNumber n := by
  rw [harmonicNumber_eq_harmonic]
  simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic n

theorem harmonicNumber_log_upper (n : ℕ) :
    harmonicNumber n ≤ 1 + Real.log (n : ℝ) := by
  rw [harmonicNumber_eq_harmonic]
  exact harmonic_le_one_add_log n

theorem harmonicNumber_pos {n : ℕ} (hn : 0 < n) :
    0 < harmonicNumber n := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (Real.log_pos (by linarith : (1 : ℝ) < (n : ℝ) + 1)).trans_le
    (harmonicNumber_log_lower n)

theorem harmonicNumber_mul_le_add
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    harmonicNumber (d * n) ≤
      harmonicNumber n + (1 + Real.log (d : ℝ)) := by
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log (n : ℝ) ≤ harmonicNumber n := by
    exact (Real.log_le_log hnreal (by linarith :
      (n : ℝ) ≤ (n : ℝ) + 1)).trans
      (harmonicNumber_log_lower n)
  calc
    harmonicNumber (d * n) ≤
        1 + Real.log ((d * n : ℕ) : ℝ) :=
          harmonicNumber_log_upper (d * n)
    _ = 1 + (Real.log (d : ℝ) + Real.log (n : ℝ)) := by
      rw [Nat.cast_mul, Real.log_mul hdreal.ne' hnreal.ne']
    _ ≤ harmonicNumber n + (1 + Real.log (d : ℝ)) := by
      linarith

theorem exists_proofHarmonicNumber_gt (bound : ℝ) :
    ∃ n : ℕ, bound < harmonicNumber n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp bound)
  have hpositive : 0 < (n : ℝ) + 1 := by positivity
  have hlog : bound < Real.log ((n : ℝ) + 1) := by
    apply (Real.lt_log_iff_exp_lt hpositive).mpr
    exact lt_trans hn (by linarith)
  exact ⟨n, hlog.trans_le (harmonicNumber_log_lower n)⟩

theorem exists_proofHarmonicNumber_ratio_ge
    (d : ℕ) (hd : 0 < d)
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ n : ℕ, 0 < n ∧
      1 - ε ≤ harmonicNumber n /
        harmonicNumber (d * n) := by
  let C : ℝ := 1 + Real.log (d : ℝ)
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hd
  have hC : 0 < C := by
    dsimp [C]
    linarith
  obtain ⟨n, hnlarge⟩ :=
    exists_proofHarmonicNumber_gt (C / ε)
  have hn : 0 < n := by
    have hzero : harmonicNumber 0 = 0 := by
      rw [harmonicNumber_eq_harmonic]
      simp only [harmonic_zero, Rat.cast_zero]
    by_contra hnot
    have hnzero : n = 0 := by omega
    rw [hnzero, hzero] at hnlarge
    have hpositive : 0 < C / ε := div_pos hC hε
    linarith
  have hden : 0 < harmonicNumber (d * n) :=
    harmonicNumber_pos (Nat.mul_pos hd hn)
  have hupper := harmonicNumber_mul_le_add hd hn
  have hbudget : C < ε * harmonicNumber n := by
    have h := (div_lt_iff₀ hε).mp hnlarge
    linarith
  refine ⟨n, hn, (le_div_iff₀ hden).mpr ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left
    hupper (sub_nonneg.mpr hεone)
  have hproduct : 0 ≤ ε * C := mul_nonneg hε.le hC.le
  change (1 - ε) * harmonicNumber (d * n) ≤
    harmonicNumber n
  change harmonicNumber (d * n) ≤
    harmonicNumber n + C at hupper
  change (1 - ε) * harmonicNumber (d * n) ≤
    (1 - ε) * (harmonicNumber n + C) at hscaled
  linarith

end

section

open WithLp
open scoped BigOperators Kronecker

/-- The quantum state representing e pr. -/
def ePRState (m : ℕ) :
    EuclideanSpace ℂ (Fin m × Fin m) :=
  toLp 2 fun q : Fin m × Fin m =>
    if q.1 = q.2 then
      (↑((Real.sqrt (m : ℝ))⁻¹) : ℂ)
    else
      0

theorem ePRState_norm (m : ℕ) (hm : 0 < m) :
    ‖ePRState m‖ = 1 := by
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hamp :
      ‖(↑((Real.sqrt (m : ℝ))⁻¹) : ℂ)‖ ^ 2 =
        (m : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
      inv_pow, Real.sq_sqrt hmreal.le]
  have hsquare : ‖ePRState m‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    have hterm (i j : Fin m) :
        ‖if i = j then
          (↑((Real.sqrt (m : ℝ))⁻¹) : ℂ)
        else
          0‖ ^ 2 =
          if i = j then (m : ℝ)⁻¹ else 0 := by
      split_ifs with h
      · exact hamp
      · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    change
      (∑ i : Fin m, ∑ j : Fin m,
        ‖if i = j then
          (↑((Real.sqrt (m : ℝ))⁻¹) : ℂ)
        else
          0‖ ^ 2) = 1
    simp_rw [hterm]
    simp only [sum_ite_eq, mem_univ, ↓reduceIte, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, ne_eq, hmreal.ne', not_false_eq_true, mul_inv_cancel₀]
  nlinarith [norm_nonneg (ePRState m)]

theorem permutationMatrix_mem_unitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) :
    σ.permMatrix ℂ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp only [inv_mul_cancel, permMatrix_one]

/-- The unitary operator implementing permutation. -/
def permutationUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : Matrix.unitaryGroup ι ℂ :=
  ⟨σ.permMatrix ℂ, permutationMatrix_mem_unitary σ⟩

@[simp] theorem permutationUnitary_val
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) :
    (permutationUnitary σ : Matrix ι ι ℂ) =
      σ.permMatrix ℂ := rfl

theorem localPermutationUnitaryAction_apply
    {n : ℕ} (σ : Equiv.Perm (Fin n))
    (ψ : EuclideanSpace ℂ (Fin n × Fin n))
    (i j : Fin n) :
    localUnitaryAction
      (permutationUnitary σ)
      (permutationUnitary σ) ψ (i, j) =
        ψ (σ i, σ j) := by
  let X : Matrix (Fin n) (Fin n) ℂ :=
    fun a b => ψ (b, a)
  have hx : ofLp ψ = Matrix.vec X := by
    funext q
    rcases q with ⟨a, b⟩
    rfl
  change
    (((σ.permMatrix ℂ) ⊗ₖ (σ.permMatrix ℂ)).mulVec
      (ofLp ψ)) (i, j) = ψ (σ i, σ j)
  rw [hx, Matrix.kronecker_mulVec_vec]
  change
    ((σ.permMatrix ℂ) * X *
      (σ.permMatrix ℂ).transpose) j i = ψ (σ i, σ j)
  rw [Matrix.transpose_permMatrix,
    PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem diagonalInner_real_eq_sum
    {N : ℕ}
    (z w : EuclideanSpace ℂ (Fin N × Fin N))
    (hz : ∀ i j : Fin N, i ≠ j → z (i, j) = 0) :
    (inner ℂ z w).re =
      ∑ i : Fin N, (inner ℂ (z (i, i)) (w (i, i))).re := by
  rw [PiLp.inner_apply, Complex.re_sum,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [hz i j (Ne.symm hji)]
    simp only [RCLike.inner_apply, map_zero, mul_zero, zero_re]
  · simp only [mem_univ, not_true_eq_false, RCLike.inner_apply, mul_re, conj_re, conj_im, mul_neg,
      sub_neg_eq_add, IsEmpty.forall_iff]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem harmonicSchmidtFiber_count_sq_le
    {n : ℕ} (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    (((Finset.univ.filter fun j : Fin n =>
      x ≤ a * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ) * x ^ 2 ≤
      a ^ 2 := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun j : Fin n =>
    x ≤ a * (Real.sqrt ((j.val : ℝ) + 1))⁻¹
  change (S.card : ℝ) * x ^ 2 ≤ a ^ 2
  by_cases hs : S.Nonempty
  · let j : Fin n := S.max' hs
    have hjmem : j ∈ S := S.max'_mem hs
    have hjthreshold :
        x ≤ a * (Real.sqrt ((j.val : ℝ) + 1))⁻¹ :=
      (Finset.mem_filter.mp hjmem).2
    have hcard : S.card ≤ j.val + 1 := by
      calc
        S.card ≤ (Finset.Iic j).card := by
          apply Finset.card_le_card
          intro k hk
          exact Finset.mem_Iic.mpr (S.le_max' k hk)
        _ = j.val + 1 := by simp only [Fin.card_Iic]
    have hjpositive : 0 < (j.val : ℝ) + 1 := by positivity
    have hsqrtpositive : 0 < Real.sqrt ((j.val : ℝ) + 1) :=
      Real.sqrt_pos.2 hjpositive
    have hscaled :
        x * Real.sqrt ((j.val : ℝ) + 1) ≤ a := by
      apply (le_div_iff₀ hsqrtpositive).mp
      simpa only [div_eq_mul_inv] using hjthreshold
    have hsquares :
        ((j.val : ℝ) + 1) * x ^ 2 ≤ a ^ 2 := by
      have hnonneg : 0 ≤ x * Real.sqrt ((j.val : ℝ) + 1) :=
        mul_nonneg hx (Real.sqrt_nonneg _)
      have hs :
          (x * Real.sqrt ((j.val : ℝ) + 1)) ^ 2 ≤ a ^ 2 := by
        linarith [mul_nonneg (sub_nonneg.mpr hscaled)
          (add_nonneg ha hnonneg)]
      rw [mul_pow, Real.sq_sqrt hjpositive.le] at hs
      linarith
    have hcardreal : (S.card : ℝ) ≤ (j.val : ℝ) + 1 := by
      exact_mod_cast hcard
    exact (mul_le_mul_of_nonneg_right hcardreal (sq_nonneg x)).trans
      hsquares
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hempty]
    simp only [card_empty, CharP.cast_eq_zero, zero_mul, sq_nonneg a]

private def harmonicTensorSchmidtAmplitude
    {d n : ℕ} (σ : Fin d → ℝ) (q : Fin (d * n)) : ℝ :=
  let p : Fin d × Fin n := finProdFinEquiv.symm q
  σ p.1 * (Real.sqrt ((p.2.val : ℝ) + 1))⁻¹

private def descendingHarmonicSchmidtPermutation
    {d n : ℕ} (σ : Fin d → ℝ) : Equiv.Perm (Fin (d * n)) :=
  Tuple.sort (fun q : Fin (d * n) =>
    -harmonicTensorSchmidtAmplitude (n := n) σ q)

theorem descendingHarmonicSchmidtPermutation_antitone
    {d n : ℕ} (σ : Fin d → ℝ) :
    Antitone (fun q : Fin (d * n) =>
      harmonicTensorSchmidtAmplitude (n := n) σ
        (descendingHarmonicSchmidtPermutation
          (n := n) σ q)) := by
  intro i j hij
  have h := Tuple.monotone_sort
    (fun q : Fin (d * n) =>
      -harmonicTensorSchmidtAmplitude (n := n) σ q)
    hij
  exact neg_le_neg_iff.mp h

theorem harmonicSchmidtThreshold_card_eq
    {d n : ℕ} (σ : Fin d → ℝ) (x : ℝ) :
    (((Finset.univ.filter fun q : Fin (d * n) =>
      x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q).card : ℕ) : ℝ) =
      ∑ i : Fin d,
        (((Finset.univ.filter fun j : Fin n =>
          x ≤ σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ) := by
  classical
  calc
    (((Finset.univ.filter fun q : Fin (d * n) =>
      x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q).card : ℕ) : ℝ) =
      ∑ q : Fin (d * n),
        if x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q
          then (1 : ℝ) else 0 := by
            simp only [sum_boole]
    _ = ∑ p : Fin d × Fin n,
      if x ≤ harmonicTensorSchmidtAmplitude (n := n) σ
          (finProdFinEquiv p)
        then (1 : ℝ) else 0 := by
          exact (Equiv.sum_comp finProdFinEquiv
            (fun q : Fin (d * n) =>
              if x ≤ harmonicTensorSchmidtAmplitude
                (n := n) σ q then (1 : ℝ) else 0)).symm
    _ = ∑ i : Fin d,
        (((Finset.univ.filter fun j : Fin n =>
          x ≤ σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro i _
          simp only [harmonicTensorSchmidtAmplitude, Equiv.symm_apply_apply, sum_boole]

theorem harmonicSchmidtThreshold_count_sq_le_one
    {d n : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (x : ℝ) (hx : 0 ≤ x) :
    (((Finset.univ.filter fun q : Fin (d * n) =>
      x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q).card : ℕ) : ℝ) *
        x ^ 2 ≤ 1 := by
  rw [harmonicSchmidtThreshold_card_eq]
  calc
    (∑ i : Fin d,
      (((Finset.univ.filter fun j : Fin n =>
        x ≤ σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ)) *
          x ^ 2 =
        ∑ i : Fin d,
          (((Finset.univ.filter fun j : Fin n =>
            x ≤ σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ) *
              x ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ∑ i : Fin d, σ i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact harmonicSchmidtFiber_count_sq_le
        (σ i) x (hσ i) hx
    _ = 1 := hunit

theorem descendingHarmonicSchmidtAmplitude_rank_sq_le_one
    {d n : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (k : Fin (d * n)) :
    (((k.val : ℝ) + 1) *
      harmonicTensorSchmidtAmplitude (n := n) σ
        (descendingHarmonicSchmidtPermutation
          (n := n) σ k) ^ 2) ≤ 1 := by
  classical
  let π := descendingHarmonicSchmidtPermutation
    (n := n) σ
  let x := harmonicTensorSchmidtAmplitude
    (n := n) σ (π k)
  let S : Finset (Fin (d * n)) :=
    Finset.univ.filter fun q : Fin (d * n) =>
      x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q
  have hx : 0 ≤ x := by
    dsimp [x, harmonicTensorSchmidtAmplitude]
    exact mul_nonneg (hσ _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hanti :=
    descendingHarmonicSchmidtPermutation_antitone
      (n := n) σ
  have hcard : k.val + 1 ≤ S.card := by
    calc
      k.val + 1 = (Finset.Iic k).card := by simp only [Fin.card_Iic]
      _ = ((Finset.Iic k).map π.toEmbedding).card := by simp only [Fin.card_Iic, card_map]
      _ ≤ S.card := by
        apply Finset.card_le_card
        intro q hq
        obtain ⟨l, hl, hleq⟩ := Finset.mem_map.mp hq
        subst q
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact hanti (Finset.mem_Iic.mp hl)
  have hcardreal : (k.val : ℝ) + 1 ≤ (S.card : ℝ) := by
    exact_mod_cast hcard
  have htotal := harmonicSchmidtThreshold_count_sq_le_one
    (n := n) σ hσ hunit x hx
  change ((k.val : ℝ) + 1) * x ^ 2 ≤ 1
  change (S.card : ℝ) * x ^ 2 ≤ 1 at htotal
  exact (mul_le_mul_of_nonneg_right hcardreal
    (sq_nonneg x)).trans htotal

theorem descendingHarmonicSchmidtAmplitude_le_harmonic
    {d n : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (k : Fin (d * n)) :
    harmonicTensorSchmidtAmplitude (n := n) σ
      (descendingHarmonicSchmidtPermutation
        (n := n) σ k) ≤
      (Real.sqrt ((k.val : ℝ) + 1))⁻¹ := by
  let x := harmonicTensorSchmidtAmplitude (n := n) σ
    (descendingHarmonicSchmidtPermutation
      (n := n) σ k)
  have hx : 0 ≤ x := by
    dsimp [x, harmonicTensorSchmidtAmplitude]
    exact mul_nonneg (hσ _)
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hrank : 0 < (k.val : ℝ) + 1 := by positivity
  have hsqrt : 0 < Real.sqrt ((k.val : ℝ) + 1) :=
    Real.sqrt_pos.mpr hrank
  have hrankbound :=
    descendingHarmonicSchmidtAmplitude_rank_sq_le_one
      (n := n) σ hσ hunit k
  change x ≤ (Real.sqrt ((k.val : ℝ) + 1))⁻¹
  rw [← one_div]
  apply (le_div_iff₀ hsqrt).2
  have hsquare :
      (x * Real.sqrt ((k.val : ℝ) + 1)) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt hrank.le]
    linarith
  have hnonneg :
      0 ≤ x * Real.sqrt ((k.val : ℝ) + 1) :=
    mul_nonneg hx hsqrt.le
  nlinarith [sq_nonneg
    (x * Real.sqrt ((k.val : ℝ) + 1) + 1)]

private def diagonalSchmidtUnitVector
    {d : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    BipartiteUnitVector d := by
  refine ⟨diagonalSchmidtState σ, ?_⟩
  have hsquare := diagonalSchmidtState_norm_sq σ
  rw [hunit] at hsquare
  nlinarith [norm_nonneg (diagonalSchmidtState σ)]

theorem diagonalSchmidtTensorTarget_diagonal
    {d n : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (q : Fin (d * n)) :
    tensorEmbezzlementTarget (n := n)
      (diagonalSchmidtUnitVector σ hunit) (q, q) =
        (‖rawEmbezzlementState n‖⁻¹ : ℝ) •
          (harmonicTensorSchmidtAmplitude
            (n := n) σ q : ℂ) := by
  simp only [tensorEmbezzlementTarget, diagonalSchmidtUnitVector, diagonalSchmidtState,
    finProdFinEquiv_symm_apply, embezzlementState_apply, Fin.coe_modNat, ofReal_inv, smul_ite,
    real_smul, mul_comm, smul_zero, mul_ite, ite_mul, zero_mul, mul_zero, ite_self, ↓reduceIte,
    harmonicTensorSchmidtAmplitude, ofReal_mul, mul_assoc]

private def harmonicSchmidtPermutationUnitary
    {d n : ℕ} (σ : Fin d → ℝ) :
    Matrix.unitaryGroup (Fin (d * n)) ℂ :=
  permutationUnitary
    (descendingHarmonicSchmidtPermutation
      (n := n) σ).symm

theorem harmonicSchmidtPermutationAction_off_diagonal
    {d n : ℕ} (σ : Fin d → ℝ)
    (i j : Fin (d * n)) (hij : i ≠ j) :
    localUnitaryAction
      (harmonicSchmidtPermutationUnitary (n := n) σ)
      (harmonicSchmidtPermutationUnitary (n := n) σ)
      (embezzlementState (d * n)) (i, j) = 0 := by
  rw [harmonicSchmidtPermutationUnitary,
    localPermutationUnitaryAction_apply,
    embezzlementState_apply]
  have hperm :
      (descendingHarmonicSchmidtPermutation
        (n := n) σ).symm i ≠
      (descendingHarmonicSchmidtPermutation
        (n := n) σ).symm j :=
    (descendingHarmonicSchmidtPermutation
      (n := n) σ).symm.injective.ne hij
  simp only [hperm, ↓reduceIte, smul_zero]

theorem harmonicSchmidtPermutationAction_diagonal
    {d n : ℕ} (σ : Fin d → ℝ)
    (k : Fin (d * n)) :
    localUnitaryAction
      (harmonicSchmidtPermutationUnitary (n := n) σ)
      (harmonicSchmidtPermutationUnitary (n := n) σ)
      (embezzlementState (d * n))
        (descendingHarmonicSchmidtPermutation
          (n := n) σ k,
          descendingHarmonicSchmidtPermutation
            (n := n) σ k) =
      (‖rawEmbezzlementState (d * n)‖⁻¹ : ℝ) •
        (↑((Real.sqrt ((k.val : ℝ) + 1))⁻¹) : ℂ) := by
  rw [harmonicSchmidtPermutationUnitary,
    localPermutationUnitaryAction_apply,
    embezzlementState_apply]
  simp only [Equiv.symm_apply_apply, ↓reduceIte, ofReal_inv, real_smul]

theorem harmonicTensorSchmidtAmplitude_sq_sum
    {d n : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    (∑ q : Fin (d * n),
      harmonicTensorSchmidtAmplitude
        (n := n) σ q ^ 2) =
      harmonicNumber n := by
  have hterm (i : Fin d) (j : Fin n) :
      (σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹) ^ 2 =
        σ i ^ 2 * ((j.val : ℝ) + 1)⁻¹ := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
  calc
    (∑ q : Fin (d * n),
      harmonicTensorSchmidtAmplitude
        (n := n) σ q ^ 2) =
      ∑ p : Fin d × Fin n,
        harmonicTensorSchmidtAmplitude
          (n := n) σ (finProdFinEquiv p) ^ 2 := by
            exact (Equiv.sum_comp finProdFinEquiv
              (fun q : Fin (d * n) =>
                harmonicTensorSchmidtAmplitude
                  (n := n) σ q ^ 2)).symm
    _ = ∑ i : Fin d,
      σ i ^ 2 * harmonicNumber n := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        simp_rw [harmonicTensorSchmidtAmplitude,
          Equiv.symm_apply_apply]
        simp_rw [hterm]
        rw [← Finset.mul_sum]
        rfl
    _ = (∑ i : Fin d, σ i ^ 2) *
      harmonicNumber n := by
        rw [Finset.sum_mul]
    _ = harmonicNumber n := by rw [hunit, one_mul]

theorem descendingHarmonicSchmidtAmplitude_sq_sum
    {d n : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    (∑ k : Fin (d * n),
      harmonicTensorSchmidtAmplitude
        (n := n) σ
          (descendingHarmonicSchmidtPermutation
            (n := n) σ k) ^ 2) =
      harmonicNumber n := by
  calc
    (∑ k : Fin (d * n),
      harmonicTensorSchmidtAmplitude
        (n := n) σ
          (descendingHarmonicSchmidtPermutation
            (n := n) σ k) ^ 2) =
        ∑ q : Fin (d * n),
          harmonicTensorSchmidtAmplitude
            (n := n) σ q ^ 2 :=
          Equiv.sum_comp
            (descendingHarmonicSchmidtPermutation
              (n := n) σ)
            (fun q : Fin (d * n) =>
              harmonicTensorSchmidtAmplitude
                (n := n) σ q ^ 2)
    _ = harmonicNumber n :=
      harmonicTensorSchmidtAmplitude_sq_sum
        (n := n) σ hunit

private def universalCatalystOverlapTerm
    {d n : ℕ} (σ : Fin d → ℝ)
    (k : Fin (d * n)) : ℝ :=
  ‖rawEmbezzlementState (d * n)‖⁻¹ *
    (Real.sqrt ((k.val : ℝ) + 1))⁻¹ *
    ‖rawEmbezzlementState n‖⁻¹ *
    harmonicTensorSchmidtAmplitude
      (n := n) σ
        (descendingHarmonicSchmidtPermutation
          (n := n) σ k)

theorem universalCatalystOverlap_eq_sum
    {d n : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    (inner ℂ
      (localUnitaryAction
        (harmonicSchmidtPermutationUnitary (n := n) σ)
        (harmonicSchmidtPermutationUnitary (n := n) σ)
        (embezzlementState (d * n)))
      (tensorEmbezzlementTarget (n := n)
        (diagonalSchmidtUnitVector σ hunit))).re =
      ∑ k : Fin (d * n),
        universalCatalystOverlapTerm
          (n := n) σ k := by
  rw [diagonalInner_real_eq_sum _ _
    (harmonicSchmidtPermutationAction_off_diagonal
      (n := n) σ)]
  calc
    (∑ q : Fin (d * n),
      (inner ℂ
        (localUnitaryAction
          (harmonicSchmidtPermutationUnitary (n := n) σ)
          (harmonicSchmidtPermutationUnitary (n := n) σ)
          (embezzlementState (d * n)) (q, q))
        (tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit)
          (q, q))).re) =
      ∑ k : Fin (d * n),
        (inner ℂ
          (localUnitaryAction
            (harmonicSchmidtPermutationUnitary (n := n) σ)
            (harmonicSchmidtPermutationUnitary (n := n) σ)
            (embezzlementState (d * n))
            (descendingHarmonicSchmidtPermutation
              (n := n) σ k,
              descendingHarmonicSchmidtPermutation
                (n := n) σ k))
          (tensorEmbezzlementTarget (n := n)
            (diagonalSchmidtUnitVector σ hunit)
            (descendingHarmonicSchmidtPermutation
              (n := n) σ k,
              descendingHarmonicSchmidtPermutation
                (n := n) σ k))).re := by
          exact (Equiv.sum_comp
            (descendingHarmonicSchmidtPermutation
              (n := n) σ)
            (fun q : Fin (d * n) =>
              (inner ℂ
                (localUnitaryAction
                  (harmonicSchmidtPermutationUnitary
                    (n := n) σ)
                  (harmonicSchmidtPermutationUnitary
                    (n := n) σ)
                  (embezzlementState (d * n)) (q, q))
                (tensorEmbezzlementTarget (n := n)
                  (diagonalSchmidtUnitVector σ hunit)
                  (q, q))).re)).symm
    _ = ∑ k : Fin (d * n),
        universalCatalystOverlapTerm
          (n := n) σ k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [harmonicSchmidtPermutationAction_diagonal,
            diagonalSchmidtTensorTarget_diagonal]
          simp only [ofReal_inv, real_smul, mul_comm, RCLike.inner_apply, map_mul, map_inv₀,
            conj_ofReal, mul_left_comm, mul_assoc, mul_re, inv_re, ofReal_re, normSq_ofReal,
            div_self_mul_self', inv_im, ofReal_im, neg_zero, zero_div, mul_zero, sub_zero, mul_im,
            zero_mul, add_zero, universalCatalystOverlapTerm]

theorem universalCatalystOverlapTerm_lower
    {d n : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (k : Fin (d * n)) :
    ‖rawEmbezzlementState (d * n)‖⁻¹ *
      ‖rawEmbezzlementState n‖⁻¹ *
        harmonicTensorSchmidtAmplitude
          (n := n) σ
            (descendingHarmonicSchmidtPermutation
              (n := n) σ k) ^ 2 ≤
      universalCatalystOverlapTerm
        (n := n) σ k := by
  let a := harmonicTensorSchmidtAmplitude
    (n := n) σ
      (descendingHarmonicSchmidtPermutation
        (n := n) σ k)
  let h := (Real.sqrt ((k.val : ℝ) + 1))⁻¹
  let c := ‖rawEmbezzlementState (d * n)‖⁻¹ *
    ‖rawEmbezzlementState n‖⁻¹
  have ha : 0 ≤ a := by
    dsimp [a, harmonicTensorSchmidtAmplitude]
    exact mul_nonneg (hσ _)
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hah : a ≤ h :=
    descendingHarmonicSchmidtAmplitude_le_harmonic
      (n := n) σ hσ hunit k
  change c * a ^ 2 ≤ _
  calc
    c * a ^ 2 = (c * a) * a := by ring
    _ ≤ (c * a) * h :=
      mul_le_mul_of_nonneg_left hah (mul_nonneg hc ha)
    _ = universalCatalystOverlapTerm
      (n := n) σ k := by
        dsimp [c, a, h, universalCatalystOverlapTerm]
        ring

theorem universalDiagonalCatalystOverlap_lower
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    ‖rawEmbezzlementState n‖ /
      ‖rawEmbezzlementState (d * n)‖ ≤
        (inner ℂ
          (localUnitaryAction
            (harmonicSchmidtPermutationUnitary
              (n := n) σ)
            (harmonicSchmidtPermutationUnitary
              (n := n) σ)
            (embezzlementState (d * n)))
          (tensorEmbezzlementTarget (n := n)
            (diagonalSchmidtUnitVector σ hunit))).re := by
  have hnraw : ‖rawEmbezzlementState n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (rawEmbezzlementState_ne_zero n hn)
  have hdnraw :
      ‖rawEmbezzlementState (d * n)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (rawEmbezzlementState_ne_zero
        (d * n) (Nat.mul_pos hd hn))
  calc
    ‖rawEmbezzlementState n‖ /
      ‖rawEmbezzlementState (d * n)‖ =
        ‖rawEmbezzlementState (d * n)‖⁻¹ *
          ‖rawEmbezzlementState n‖⁻¹ *
            harmonicNumber n := by
              rw [← rawEmbezzlementState_norm_sq n]
              field_simp
    _ = ∑ k : Fin (d * n),
      ‖rawEmbezzlementState (d * n)‖⁻¹ *
        ‖rawEmbezzlementState n‖⁻¹ *
          harmonicTensorSchmidtAmplitude
            (n := n) σ
              (descendingHarmonicSchmidtPermutation
                (n := n) σ k) ^ 2 := by
          rw [← descendingHarmonicSchmidtAmplitude_sq_sum
            (n := n) σ hunit, Finset.mul_sum]
    _ ≤ ∑ k : Fin (d * n),
      universalCatalystOverlapTerm
        (n := n) σ k := by
          apply Finset.sum_le_sum
          intro k _
          exact universalCatalystOverlapTerm_lower
            (n := n) σ hσ hunit k
    _ = (inner ℂ
      (localUnitaryAction
        (harmonicSchmidtPermutationUnitary
          (n := n) σ)
        (harmonicSchmidtPermutationUnitary
          (n := n) σ)
        (embezzlementState (d * n)))
      (tensorEmbezzlementTarget (n := n)
        (diagonalSchmidtUnitVector σ hunit))).re :=
      (universalCatalystOverlap_eq_sum
        (n := n) σ hunit).symm

private def harmonicTargetLiftUnitary
    {d n : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin (d * n)) ℂ := by
  let e : (Fin d × Fin n) ≃ Fin (d * n) :=
    finProdFinEquiv
  let M : Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ :=
    (U.val ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
  have hM : M ∈ Matrix.unitaryGroup (Fin d × Fin n) ℂ := by
    exact Matrix.kronecker_mem_unitary U.property
      (show (1 : Matrix (Fin n) (Fin n) ℂ) ∈
        Matrix.unitaryGroup (Fin n) ℂ from
          (Matrix.unitaryGroup (Fin n) ℂ).one_mem)
  refine ⟨(Matrix.reindex e e) M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have hstar :
      star ((Matrix.reindex e e) M) =
        (Matrix.reindex e e) (star M) := by
    ext i j
    simp only [reindex_apply, star_apply, submatrix_apply, RCLike.star_def, star_eq_conjTranspose,
      conjTranspose_apply]
  rw [hstar]
  change (Matrix.reindexRingEquiv ℂ e) (star M) *
    (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp hM]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

@[simp] theorem harmonicTargetLiftUnitary_apply
    {d n : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d) (i j : Fin n) :
    harmonicTargetLiftUnitary (n := n) U
      (finProdFinEquiv (a, i))
      (finProdFinEquiv (b, j)) =
        if i = j then U a b else 0 := by
  change
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (U.val ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)))
        (finProdFinEquiv (a, i))
        (finProdFinEquiv (b, j)) = _
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero]

theorem localUnitaryAction_comp
    {m : ℕ}
    (U₁ V₁ U₂ V₂ : Matrix.unitaryGroup (Fin m) ℂ)
    (ψ : EuclideanSpace ℂ (Fin m × Fin m)) :
    localUnitaryAction U₁ V₁
      (localUnitaryAction U₂ V₂ ψ) =
        localUnitaryAction (U₁ * U₂) (V₁ * V₂) ψ := by
  apply WithLp.ofLp_injective
  change
    ((U₁.val ⊗ₖ V₁.val).mulVec
      ((U₂.val ⊗ₖ V₂.val).mulVec (ofLp ψ))) =
      ((U₁ * U₂).val ⊗ₖ (V₁ * V₂).val).mulVec (ofLp ψ)
  rw [Matrix.mulVec_mulVec,
    ← Matrix.mul_kronecker_mul]
  rfl

theorem targetCatalystDoubleSum_reindex
    {d n : ℕ}
    (F : Fin (d * n) → Fin (d * n) → ℂ) :
    (∑ i : Fin (d * n), ∑ j : Fin (d * n), F i j) =
      ∑ p : Fin d × Fin n,
        ∑ q : Fin d × Fin n,
          F (finProdFinEquiv p) (finProdFinEquiv q) := by
  calc
    (∑ i : Fin (d * n), ∑ j : Fin (d * n), F i j) =
        ∑ p : Fin d × Fin n,
          ∑ j : Fin (d * n), F (finProdFinEquiv p) j := by
            exact (Equiv.sum_comp finProdFinEquiv
              (fun i : Fin (d * n) =>
                ∑ j : Fin (d * n), F i j)).symm
    _ = ∑ p : Fin d × Fin n,
        ∑ q : Fin d × Fin n,
          F (finProdFinEquiv p) (finProdFinEquiv q) := by
            apply Finset.sum_congr rfl
            intro p _
            exact (Equiv.sum_comp finProdFinEquiv
              (fun j : Fin (d * n) =>
                F (finProdFinEquiv p) j)).symm

theorem harmonicTargetLift_diagonal_action_apply
    {d n : ℕ}
    (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d) (i j : Fin n) :
    localUnitaryAction
      (harmonicTargetLiftUnitary (n := n) U)
      (harmonicTargetLiftUnitary (n := n) V)
      (tensorEmbezzlementTarget (n := n)
        (diagonalSchmidtUnitVector σ hunit))
        (finProdFinEquiv (a, i),
          finProdFinEquiv (b, j)) =
      schmidtVector σ U V (a, b) *
        embezzlementState n (i, j) := by
  classical
  let LU := harmonicTargetLiftUnitary (n := n) U
  let LV := harmonicTargetLiftUnitary (n := n) V
  let T := tensorEmbezzlementTarget (n := n)
    (diagonalSchmidtUnitVector σ hunit)
  have hT (p q : Fin d × Fin n) :
      T (finProdFinEquiv p, finProdFinEquiv q) =
        (if p.1 = q.1 then (σ p.1 : ℂ) else 0) *
          embezzlementState n (p.2, q.2) := by
    change
      (if (finProdFinEquiv.symm (finProdFinEquiv p)).1 =
          (finProdFinEquiv.symm (finProdFinEquiv q)).1 then
        (σ (finProdFinEquiv.symm (finProdFinEquiv p)).1 : ℂ)
      else 0) *
        embezzlementState n
          ((finProdFinEquiv.symm (finProdFinEquiv p)).2,
            (finProdFinEquiv.symm (finProdFinEquiv q)).2) = _
    simp only [Equiv.symm_apply_apply]
  change
    ((LU.val ⊗ₖ LV.val).mulVec
      (ofLp T))
      (finProdFinEquiv (a, i), finProdFinEquiv (b, j)) = _
  calc
    ((LU.val ⊗ₖ LV.val).mulVec
      (ofLp T))
      (finProdFinEquiv (a, i), finProdFinEquiv (b, j)) =
      ∑ r : Fin (d * n), ∑ s : Fin (d * n),
        LU (finProdFinEquiv (a, i)) r *
          LV (finProdFinEquiv (b, j)) s * T (r, s) := by
            simp only [mulVec, dotProduct, kroneckerMap_apply, mul_assoc, Fintype.sum_prod_type]
    _ = ∑ p : Fin d × Fin n,
        ∑ q : Fin d × Fin n,
          LU (finProdFinEquiv (a, i)) (finProdFinEquiv p) *
            LV (finProdFinEquiv (b, j)) (finProdFinEquiv q) *
            T (finProdFinEquiv p, finProdFinEquiv q) :=
          targetCatalystDoubleSum_reindex
            (fun r s =>
              LU (finProdFinEquiv (a, i)) r *
                LV (finProdFinEquiv (b, j)) s * T (r, s))
    _ = schmidtVector σ U V (a, b) *
      embezzlementState n (i, j) := by
        simp_rw [hT]
        simp only [ite_mul, zero_mul, mul_comm, mul_assoc, Fintype.sum_prod_type,
          harmonicTargetLiftUnitary_apply, mul_ite, mul_left_comm, mul_zero, sum_ite_irrel,
          sum_ite_eq, mem_univ, ↓reduceIte, sum_const_zero, schmidtVector_apply, LU, LV]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring

theorem harmonicTargetLift_diagonal_action
    {d n : ℕ}
    (ξ : BipartiteUnitVector d)
    (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (hξ : ξ.val = schmidtVector σ U V) :
    localUnitaryAction
      (harmonicTargetLiftUnitary (n := n) U)
      (harmonicTargetLiftUnitary (n := n) V)
      (tensorEmbezzlementTarget (n := n)
        (diagonalSchmidtUnitVector σ hunit)) =
      tensorEmbezzlementTarget (n := n) ξ := by
  ext ⟨r, s⟩
  let p : Fin d × Fin n := finProdFinEquiv.symm r
  let q : Fin d × Fin n := finProdFinEquiv.symm s
  have hr : finProdFinEquiv p = r :=
    Equiv.apply_symm_apply finProdFinEquiv r
  have hs : finProdFinEquiv q = s :=
    Equiv.apply_symm_apply finProdFinEquiv s
  calc
    localUnitaryAction
      (harmonicTargetLiftUnitary (n := n) U)
      (harmonicTargetLiftUnitary (n := n) V)
      (tensorEmbezzlementTarget (n := n)
        (diagonalSchmidtUnitVector σ hunit)) (r, s) =
      localUnitaryAction
        (harmonicTargetLiftUnitary (n := n) U)
        (harmonicTargetLiftUnitary (n := n) V)
        (tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit))
          (finProdFinEquiv (p.1, p.2),
            finProdFinEquiv (q.1, q.2)) := by
          simp only [Prod.mk.eta, hr, hs]
    _ = schmidtVector σ U V (p.1, q.1) *
      embezzlementState n (p.2, q.2) :=
        harmonicTargetLift_diagonal_action_apply
          σ hunit U V p.1 q.1 p.2 q.2
    _ = ξ.val (p.1, q.1) *
      embezzlementState n (p.2, q.2) := by rw [hξ]
    _ = tensorEmbezzlementTarget (n := n) ξ
      (finProdFinEquiv (p.1, p.2),
        finProdFinEquiv (q.1, q.2)) := by
          change _ =
            ξ.val
              ((finProdFinEquiv.symm
                (finProdFinEquiv (p.1, p.2))).1,
                (finProdFinEquiv.symm
                  (finProdFinEquiv (q.1, q.2))).1) *
              embezzlementState n
                ((finProdFinEquiv.symm
                  (finProdFinEquiv (p.1, p.2))).2,
                  (finProdFinEquiv.symm
                    (finProdFinEquiv (q.1, q.2))).2)
          simp only [Equiv.symm_apply_apply]
    _ = tensorEmbezzlementTarget (n := n) ξ (r, s) := by
      simp only [Prod.mk.eta, hr, hs]

theorem localUnitaryAction_sub
    {m : ℕ}
    (U V : Matrix.unitaryGroup (Fin m) ℂ)
    (z w : EuclideanSpace ℂ (Fin m × Fin m)) :
    localUnitaryAction U V (z - w) =
      localUnitaryAction U V z -
        localUnitaryAction U V w := by
  apply WithLp.ofLp_injective
  change
    ((U.val ⊗ₖ V.val).mulVec
      ((ofLp z) - (ofLp w))) =
        ((U.val ⊗ₖ V.val).mulVec (ofLp z)) -
          ((U.val ⊗ₖ V.val).mulVec (ofLp w))
  exact Matrix.mulVec_sub _ _ _

theorem universalDiagonalCatalystOverlap_of_harmonic_ratio
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hratio : 1 - δ ≤
      harmonicNumber n /
        harmonicNumber (d * n)) :
    1 - δ ≤
      (inner ℂ
        (localUnitaryAction
          (harmonicSchmidtPermutationUnitary
            (n := n) σ)
          (harmonicSchmidtPermutationUnitary
            (n := n) σ)
          (embezzlementState (d * n)))
        (tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit))).re := by
  let q : ℝ :=
    ‖rawEmbezzlementState n‖ /
      ‖rawEmbezzlementState (d * n)‖
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hqsquare :
      q ^ 2 = harmonicNumber n /
        harmonicNumber (d * n) := by
    dsimp [q]
    rw [div_pow,
      rawEmbezzlementState_norm_sq,
      rawEmbezzlementState_norm_sq]
  have hgoalnonneg : 0 ≤ 1 - δ := sub_nonneg.mpr hδone
  have hgoalsquare : (1 - δ) ^ 2 ≤ 1 - δ := by
    linarith [mul_nonneg hδ hgoalnonneg]
  have hqbound : 1 - δ ≤ q := by
    rw [← hqsquare] at hratio
    nlinarith [sq_nonneg (q + (1 - δ))]
  exact hqbound.trans
    (universalDiagonalCatalystOverlap_lower
      hd hn σ hσ hunit)

theorem universalDiagonalCatalyst_distance
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hratio : 1 - δ ≤
      harmonicNumber n /
        harmonicNumber (d * n)) :
    ‖localUnitaryAction
      (harmonicSchmidtPermutationUnitary
        (n := n) σ)
      (harmonicSchmidtPermutationUnitary
        (n := n) σ)
      (embezzlementState (d * n)) -
        tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit)‖ ≤
      Real.sqrt (2 * δ) := by
  apply unitVector_distance_of_real_overlap
    (localUnitaryAction
      (harmonicSchmidtPermutationUnitary
        (n := n) σ)
      (harmonicSchmidtPermutationUnitary
        (n := n) σ)
      (embezzlementState (d * n)))
    (tensorEmbezzlementTarget (n := n)
      (diagonalSchmidtUnitVector σ hunit))
    (by rw [localUnitaryAction_norm,
      embezzlementState_norm (d * n)
        (Nat.mul_pos hd hn)])
    (tensorEmbezzlementTarget_norm hn
      (diagonalSchmidtUnitVector σ hunit))
    δ hδ
  exact universalDiagonalCatalystOverlap_of_harmonic_ratio
    hd hn σ hσ hunit δ hδ hδone hratio

theorem exists_proofUniversalHarmonicCatalyst
    (d : ℕ) (hd : 0 < d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∀ ξ : BipartiteUnitVector d,
        ∃ U V : Matrix.unitaryGroup (Fin (d * n)) ℂ,
          ‖localUnitaryAction U V
            (embezzlementState (d * n)) -
              tensorEmbezzlementTarget (n := n) ξ‖ ≤ ε := by
  let δ : ℝ := min (ε ^ 2 / 2) 1
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity) zero_lt_one
  have hδone : δ ≤ 1 := min_le_right _ _
  obtain ⟨n, hn, hratio⟩ :=
    exists_proofHarmonicNumber_ratio_ge d hd hδ hδone
  refine ⟨n, hn, ?_⟩
  intro ξ
  obtain ⟨σ, U, V, hσ, hunit, hξ⟩ :=
    exists_proofUnitSchmidtDecomposition ξ
  let LU := harmonicTargetLiftUnitary (n := n) U
  let LV := harmonicTargetLiftUnitary (n := n) V
  let P := harmonicSchmidtPermutationUnitary
    (n := n) σ
  refine ⟨LU * P, LV * P, ?_⟩
  have hdiagonal := universalDiagonalCatalyst_distance
    hd hn σ hσ hunit δ hδ.le hδone hratio
  have htarget := harmonicTargetLift_diagonal_action
    (n := n) ξ σ hunit U V hξ
  have hdeltaeps : 2 * δ ≤ ε ^ 2 := by
    have hmin : δ ≤ ε ^ 2 / 2 := min_le_left _ _
    linarith
  have hsqrt : Real.sqrt (2 * δ) ≤ ε := by
    have hsq : (Real.sqrt (2 * δ)) ^ 2 = 2 * δ :=
      Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (2 * δ)]
  calc
    ‖localUnitaryAction (LU * P) (LV * P)
      (embezzlementState (d * n)) -
        tensorEmbezzlementTarget (n := n) ξ‖ =
      ‖localUnitaryAction LU LV
        (localUnitaryAction P P
          (embezzlementState (d * n)) -
            tensorEmbezzlementTarget (n := n)
              (diagonalSchmidtUnitVector σ hunit))‖ := by
        rw [localUnitaryAction_sub,
          localUnitaryAction_comp]
        rw [htarget]
    _ = ‖localUnitaryAction P P
      (embezzlementState (d * n)) -
        tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit)‖ :=
        localUnitaryAction_norm LU LV _
    _ ≤ Real.sqrt (2 * δ) := hdiagonal
    _ ≤ ε := hsqrt

/-- The unitary operator implementing coherent shared random controlled. -/
def coherentSharedRandomControlledUnitary
    {Ω d : Type*}
    [Fintype Ω] [Fintype d]
    [DecidableEq Ω] [DecidableEq d]
    (U : Ω → Matrix.unitaryGroup d ℂ) :
    Matrix.unitaryGroup (Σ _ : Ω, d) ℂ := by
  refine ⟨Matrix.blockDiagonal' fun ω : Ω =>
    (U ω : Matrix d d ℂ), ?_⟩
  rw [Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul]
  have hblock (ω : Ω) :
      (U ω : Matrix d d ℂ).conjTranspose *
        (U ω : Matrix d d ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff').mp (U ω).property
  simp_rw [hblock]
  ext ⟨ω, i⟩ ⟨ν, j⟩
  by_cases hων : ω = ν <;>
    by_cases hij : i = j <;>
      simp [Matrix.blockDiagonal'_apply,
        Matrix.one_apply, hων, hij]

/-- The positive operator-valued measurement implementing spectral partition. -/
def spectralPartitionPOVM
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (bin : d → κ) : POVM κ d where
  effect k :=
    ∑ i ∈ Finset.univ.filter (fun i : d => bin i = k),
      positiveMatrixSpectralAtom F hF i
  positive k := by
    apply Matrix.posSemidef_sum
    intro i _
    exact positiveMatrixSpectralAtom_posSemidef F hF i
  complete := by
    classical
    calc
      (∑ k : κ,
        ∑ i ∈ Finset.univ.filter (fun i : d => bin i = k),
          positiveMatrixSpectralAtom F hF i) =
        ∑ i : d, positiveMatrixSpectralAtom F hF i := by
          simp only [sum_filter, sum_comm, sum_ite_eq, mem_univ, ↓reduceIte]
      _ = 1 := positiveMatrixSpectralAtom_sum F hF

theorem spectralPartitionPOVM_projective
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (bin : d → κ) (k : κ) :
    (spectralPartitionPOVM F hF bin).effect k *
      (spectralPartitionPOVM F hF bin).effect k =
        (spectralPartitionPOVM F hF bin).effect k := by
  exact spectralAtomSum_mul_self F hF
    (Finset.univ.filter (fun i : d => bin i = k))

private def bilateralWorkPairEquiv
    {ι d e : Type*} :
    ((ι → d) × (ι → e)) ≃ (ι → d × e) where
  toFun x i := (x.1 i, x.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv x := by
    rcases x with ⟨a, b⟩
    rfl
  right_inv x := by
    funext i
    exact Prod.eta (x i)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


theorem spectralPartitionPOVM_trace_eq_atom_count
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (bin : d → κ) (k : κ) :
    (Matrix.trace
      ((spectralPartitionPOVM F hF bin).effect k)).re =
      ∑ i : d, if bin i = k then (1 : ℝ) else 0 := by
  classical
  simp only [spectralPartitionPOVM, trace_sum, spectralAtom_trace, sum_const, nsmul_eq_mul,
    mul_one, natCast_re, sum_boole]

theorem spectralPartitionPOVM_trace_mul_eq_atom_overlap
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (binF binG : d → κ) (k : κ) :
    (Matrix.trace
      ((spectralPartitionPOVM F hF binF).effect k *
        (spectralPartitionPOVM G hG binG).effect k)).re =
      ∑ i ∈ (Finset.univ.filter fun i : d => binF i = k),
        ∑ j ∈ (Finset.univ.filter fun j : d => binG j = k),
          spectralAtomOverlap F G hF hG i j := by
  classical
  simp only [spectralPartitionPOVM, Matrix.mul_sum, Matrix.sum_mul, trace_sum, re_sum,
    spectralAtomOverlap]
  rw [Finset.sum_comm]

theorem spectralPartitionPOVM_weighted_trace_deficit_eq_mismatch
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (binF binG : d → κ)
    (τ : κ → ℝ) :
    (∑ k : κ, τ k ^ 2 *
        (Matrix.trace
          ((spectralPartitionPOVM G hG binG).effect k)).re) -
      (∑ k : κ, τ k ^ 2 *
        (Matrix.trace
          ((spectralPartitionPOVM F hF binF).effect k *
            (spectralPartitionPOVM G hG binG).effect k)).re) =
      ∑ i : d, ∑ j : d,
        if binF i = binG j then 0
        else τ (binG j) ^ 2 *
          spectralAtomOverlap F G hF hG i j := by
  classical
  let w : d → d → ℝ :=
    spectralAtomOverlap F G hF hG
  have hQ :
      (∑ k : κ, τ k ^ 2 *
        (Matrix.trace
          ((spectralPartitionPOVM G hG binG).effect k)).re) =
        ∑ j : d, τ (binG j) ^ 2 := by
    simp_rw [spectralPartitionPOVM_trace_eq_atom_count]
    calc
      (∑ k : κ, τ k ^ 2 *
        (∑ j : d, if binG j = k then (1 : ℝ) else 0)) =
          ∑ k : κ, ∑ j : d,
            if binG j = k then τ k ^ 2 else 0 := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              split_ifs <;> simp
      _ = ∑ j : d, ∑ k : κ,
          if binG j = k then τ k ^ 2 else 0 :=
            Finset.sum_comm
      _ = ∑ j : d, τ (binG j) ^ 2 := by
            simp only [sum_ite_eq, mem_univ, ↓reduceIte]
  have hPQ :
      (∑ k : κ, τ k ^ 2 *
        (Matrix.trace
          ((spectralPartitionPOVM F hF binF).effect k *
            (spectralPartitionPOVM G hG binG).effect k)).re) =
        ∑ i : d, ∑ j : d,
          if binF i = binG j then
            τ (binG j) ^ 2 * w i j
          else 0 := by
    have hsingle (k : κ) :
        τ k ^ 2 *
          (Matrix.trace
            ((spectralPartitionPOVM F hF binF).effect k *
              (spectralPartitionPOVM G hG binG).effect k)).re =
          ∑ i : d, ∑ j : d,
            if binF i = k ∧ binG j = k then
              τ k ^ 2 * w i j
            else 0 := by
      rw [spectralPartitionPOVM_trace_mul_eq_atom_overlap]
      dsimp [w]
      simp only [Finset.sum_filter, Finset.mul_sum,
        mul_ite, mul_zero]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : binF i = k
      · simp only [hi, ↓reduceIte, true_and]
      · simp only [hi, ↓reduceIte, false_and, sum_const_zero]
    simp_rw [hsingle]
    calc
      (∑ k : κ, ∑ i : d, ∑ j : d,
        if binF i = k ∧ binG j = k then
          τ k ^ 2 * w i j
        else 0) =
          ∑ i : d, ∑ j : d, ∑ k : κ,
            if binF i = k ∧ binG j = k then
              τ k ^ 2 * w i j
            else 0 := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_comm]
      _ = ∑ i : d, ∑ j : d,
          if binF i = binG j then
            τ (binG j) ^ 2 * w i j
          else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            have reindex (k : κ) :
                (if binF i = k ∧ binG j = k then
                  τ k ^ 2 * w i j
                else 0) =
                  if binG j = k then
                    if binF i = binG j then
                      τ (binG j) ^ 2 * w i j
                    else 0
                  else 0 := by
              by_cases hk : binG j = k
              · subst k
                simp only [and_true, ↓reduceIte]
              · simp only [hk, and_false, ↓reduceIte]
            simp_rw [reindex]
            simp only [sum_ite_eq, mem_univ, ↓reduceIte]
  rw [hQ, hPQ]
  have hcolumn : ∀ j : d, (∑ i : d, w i j) = 1 :=
    spectralAtomOverlap_sum_left F G hF hG
  have hfirst :
      (∑ j : d, τ (binG j) ^ 2) =
        ∑ i : d, ∑ j : d,
          τ (binG j) ^ 2 * w i j := by
    calc
      (∑ j : d, τ (binG j) ^ 2) =
          ∑ j : d,
            τ (binG j) ^ 2 * (∑ i : d, w i j) := by
              simp_rw [hcolumn]
              simp only [mul_one]
      _ = ∑ i : d, ∑ j : d,
          τ (binG j) ^ 2 * w i j := by
            simp_rw [Finset.mul_sum]
            exact Finset.sum_comm
  rw [hfirst, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [w]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


private def finiteUniformThresholdGrid
    (lower upper : ℝ) (N : ℕ) (k : Fin N) : ℝ :=
  lower + (k.val : ℝ) * ((upper - lower) / (N : ℝ))

private def finiteUniformThresholdCrossing
    (lower upper a b : ℝ) (N : ℕ) : ℝ :=
  ((Finset.univ.filter fun k : Fin N =>
      min a b ≤ finiteUniformThresholdGrid lower upper N k ∧
        finiteUniformThresholdGrid lower upper N k ≤ max a b).card : ℝ) /
    (N : ℝ)

theorem finiteUniformGrid_interval_card_le
    (N : ℕ) (offset step lo hi : ℝ)
    (positive : 0 < step)
    (ordered : lo ≤ hi) :
    (((Finset.univ.filter fun k : Fin N =>
      lo ≤ offset + (k.val : ℝ) * step ∧
        offset + (k.val : ℝ) * step ≤ hi).card : ℕ) : ℝ) ≤
      (hi - lo) / step + 1 := by
  classical
  let selected : Finset (Fin N) :=
    Finset.univ.filter fun k : Fin N =>
      lo ≤ offset + (k.val : ℝ) * step ∧
        offset + (k.val : ℝ) * step ≤ hi
  change (selected.card : ℝ) ≤ (hi - lo) / step + 1
  by_cases present : selected.Nonempty
  · let first : Fin N := selected.min' present
    let last : Fin N := selected.max' present
    have first_mem : first ∈ selected :=
      Finset.min'_mem selected present
    have last_mem : last ∈ selected :=
      Finset.max'_mem selected present
    have interval : selected ⊆ Finset.Icc first last := by
      intro k hk
      apply Finset.mem_Icc.mpr
      constructor
      · exact Finset.min'_le selected k hk
      · exact Finset.le_max' selected k hk
    have cardinal : selected.card ≤
        last.val + 1 - first.val := by
      have h := Finset.card_le_card interval
      simpa only [ge_iff_le, Fin.card_Icc] using h
    have ordered_indices : first.val ≤ last.val := by
      change (selected.min' present).val ≤ (selected.max' present).val
      exact Finset.min'_le_max' selected present
    have nat_bound : first.val ≤ last.val + 1 := by omega
    have real_cardinal :
        (selected.card : ℝ) ≤
          (last.val : ℝ) + 1 - (first.val : ℝ) := by
      exact_mod_cast cardinal
    have first_lower : lo ≤ offset + (first.val : ℝ) * step :=
      (Finset.mem_filter.mp first_mem).2.1
    have last_upper : offset + (last.val : ℝ) * step ≤ hi :=
      (Finset.mem_filter.mp last_mem).2.2
    have spread :
        ((last.val : ℝ) - (first.val : ℝ)) * step ≤ hi - lo := by
      linarith
    have scaled :
        (last.val : ℝ) - (first.val : ℝ) ≤
          (hi - lo) / step :=
      (le_div_iff₀ positive).2 spread
    linarith
  · have empty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp present
    rw [empty, Finset.card_empty, Nat.cast_zero]
    have difference : 0 ≤ hi - lo := sub_nonneg.mpr ordered
    exact add_nonneg (div_nonneg difference positive.le)
      (by norm_num)

theorem finiteUniformThresholdCrossing_le
    {lower upper : ℝ}
    (window : lower < upper)
    (a b : ℝ)
    (N : ℕ) (nonempty : 0 < N) :
    finiteUniformThresholdCrossing lower upper a b N ≤
      |a - b| / (upper - lower) + 1 / (N : ℝ) := by
  have realN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast nonempty
  have width : 0 < upper - lower := sub_pos.mpr window
  have step : 0 < (upper - lower) / (N : ℝ) :=
    div_pos width realN
  have count := finiteUniformGrid_interval_card_le
    N lower ((upper - lower) / (N : ℝ))
    (min a b) (max a b) step min_le_max
  change
    ((Finset.univ.filter fun k : Fin N =>
      min a b ≤ finiteUniformThresholdGrid lower upper N k ∧
        finiteUniformThresholdGrid lower upper N k ≤ max a b).card : ℝ) /
      (N : ℝ) ≤ _
  have same_count :
      ((Finset.univ.filter fun k : Fin N =>
        min a b ≤ finiteUniformThresholdGrid lower upper N k ∧
          finiteUniformThresholdGrid lower upper N k ≤
            max a b).card : ℝ) ≤
        (max a b - min a b) /
          ((upper - lower) / (N : ℝ)) + 1 := by
    simpa only [finiteUniformThresholdGrid, inf_le_iff, le_sup_iff] using count
  calc
    ((Finset.univ.filter fun k : Fin N =>
      min a b ≤ finiteUniformThresholdGrid lower upper N k ∧
        finiteUniformThresholdGrid lower upper N k ≤ max a b).card : ℝ) /
      (N : ℝ) ≤
        ((max a b - min a b) /
          ((upper - lower) / (N : ℝ)) + 1) / (N : ℝ) :=
      div_le_div_of_nonneg_right same_count realN.le
    _ = |a - b| / (upper - lower) + 1 / (N : ℝ) := by
      rw [max_sub_min_eq_abs]
      have habs : |b - a| = |a - b| := abs_sub_comm b a
      rw [habs]
      field_simp [realN.ne', width.ne']

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem localUnitaryPureResidual_targetLocalInverse_reset
    {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n × Fin n)) :
    localUnitaryAction U⁻¹ V⁻¹
        (localUnitaryAction U V x) = x := by
  rw [localUnitaryAction_comp,
    inv_mul_cancel, inv_mul_cancel]
  simp only [localUnitaryAction, OneMemClass.coe_one, zero_mul, implies_true, mul_zero, mul_one,
    kroneckerMap_one_one, one_mulVec, toLp_ofLp]

private def targetCoefficientMatrix
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun b a => ξ.val (a, b)

theorem targetCoefficientMatrix_vec
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    toLp 2 (Matrix.vec (targetCoefficientMatrix ξ)) = ξ.val := by
  ext ⟨a, b⟩
  rfl

private def targetReducedDensity
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (targetCoefficientMatrix ξ).conjTranspose *
    targetCoefficientMatrix ξ

theorem targetReducedDensity_posSemidef
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    (targetReducedDensity ξ).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self
    (targetCoefficientMatrix ξ)

theorem targetReducedDensity_trace
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix.trace (targetReducedDensity ξ) = 1 := by
  have vectorized := matrixVectorization_inner
    (targetCoefficientMatrix ξ)
    (targetCoefficientMatrix ξ)
  rw [targetCoefficientMatrix_vec,
    inner_self_eq_one_of_norm_eq_one ξ.property] at vectorized
  exact vectorized.symm

theorem targetSpectralAtom_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (i a b : d) :
    positiveMatrixSpectralAtom F hF i a b =
      (hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ) a i *
        star ((hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ) b i) := by
  classical
  simp only [positiveMatrixSpectralAtom, spectralConjugationCLM_apply, Matrix.mul_apply,
    IsHermitian.eigenvectorUnitary_apply, diagonal_apply, Pi.single_apply, mul_ite, mul_one,
    mul_zero, sum_ite_eq', mem_univ, ↓reduceIte, star_apply, RCLike.star_def, ite_mul, zero_mul]

theorem targetSpectralAtomOverlap_eq_basis_norm_sq
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (i j : d) :
    spectralAtomOverlap F G hF hG i j =
      ‖unitaryBasisOverlap
        hF.isHermitian.eigenvectorUnitary
        hG.isHermitian.eigenvectorUnitary i j‖ ^ 2 := by
  classical
  let U : Matrix d d ℂ := hF.isHermitian.eigenvectorUnitary
  let V : Matrix d d ℂ := hG.isHermitian.eigenvectorUnitary
  let z : ℂ := ∑ a : d, star (U a i) * V a j
  have cross :
      Matrix.trace
        (positiveMatrixSpectralAtom F hF i *
          positiveMatrixSpectralAtom G hG j) = star z * z := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      targetSpectralAtom_apply]
    change
      (∑ a : d, ∑ b : d,
        (U a i * star (U b i)) *
          (V b j * star (V a j))) = star z * z
    dsimp [z]
    rw [map_sum, Finset.sum_mul]
    simp only [map_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [starRingEnd_apply, star_star]
    ring
  unfold spectralAtomOverlap
  rw [cross]
  have coeff :
      unitaryBasisOverlap
        hF.isHermitian.eigenvectorUnitary
        hG.isHermitian.eigenvectorUnitary i j = z := by
    simp only [unitaryBasisOverlap_apply, Matrix.mul_apply, conjTranspose_apply,
      IsHermitian.eigenvectorUnitary_apply, RCLike.star_def, z, U, V]
  rw [coeff, ← Complex.normSq_eq_norm_sq]
  change (star z * z).re = Complex.normSq z
  simpa only [RCLike.star_def, mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add, ofReal_re] using
    (congrArg Complex.re
      (@Complex.normSq_eq_conj_mul_self z)).symm

end

section

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp


private def targetCanonicalSchmidtCoefficient
    {d : ℕ} (ξ : BipartiteUnitVector d)
    (i : Fin d) : ℝ :=
  Real.sqrt
    ((targetReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)

theorem targetCanonicalSchmidtCoefficient_nonneg
    {d : ℕ} (ξ : BipartiteUnitVector d) (i : Fin d) :
    0 ≤ targetCanonicalSchmidtCoefficient ξ i :=
  Real.sqrt_nonneg _

theorem targetCanonicalSchmidtCoefficient_sq_sum
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    (∑ i : Fin d, targetCanonicalSchmidtCoefficient ξ i ^ 2) = 1 := by
  unfold targetCanonicalSchmidtCoefficient
  simp_rw [Real.sq_sqrt
    ((targetReducedDensity_posSemidef ξ).eigenvalues_nonneg _)]
  exact positiveDensity_eigenvalues_sum
    (targetReducedDensity ξ)
    (targetReducedDensity_posSemidef ξ)
    (targetReducedDensity_trace ξ)

theorem exists_proofTargetCanonicalSpectralSchmidtDecomposition
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    ∃ (V : Matrix.unitaryGroup (Fin d) ℂ),
      ξ.val = schmidtVector
        (targetCanonicalSchmidtCoefficient ξ)
        (conjugateUnitary
          (targetReducedDensity_posSemidef ξ).isHermitian.eigenvectorUnitary)
        V := by
  classical
  let C : Matrix (Fin d) (Fin d) ℂ := targetCoefficientMatrix ξ
  let T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin d) := Matrix.toEuclideanLin C
  let hF := targetReducedDensity_posSemidef ξ
  let v : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d)) := hF.isHermitian.eigenvectorBasis
  let σ : Fin d → ℝ := targetCanonicalSchmidtCoefficient ξ
  have hσ (i : Fin d) : 0 ≤ σ i :=
    targetCanonicalSchmidtCoefficient_nonneg ξ i
  have hσsq (i : Fin d) :
      σ i ^ 2 = hF.isHermitian.eigenvalues i := by
    exact Real.sq_sqrt (hF.eigenvalues_nonneg i)
  have heigen (i : Fin d) :
      (T.adjoint ∘ₗ T) (v i) = ((σ i ^ 2 : ℝ) : ℂ) • v i := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change
      toLp 2
        (C.conjTranspose.mulVec
          (C.mulVec (ofLp (v i)))) =
        ((σ i ^ 2 : ℝ) : ℂ) • v i
    rw [Matrix.mulVec_mulVec]
    have spectral := hF.isHermitian.mulVec_eigenvectorBasis i
    change
      (C.conjTranspose * C).mulVec
        (ofLp (v i)) =
        (hF.isHermitian.eigenvalues i) • (ofLp (v i)) at spectral
    rw [spectral, ← hσsq]
    rfl
  let s : Set (Fin d) := {i | σ i ≠ 0}
  let f : Fin d → EuclideanSpace ℂ (Fin d) :=
    fun i => ((σ i : ℂ)⁻¹) • T (v i)
  have hGram (i j : Fin d) :
      inner ℂ (T (v i)) (T (v j)) =
        ((σ j ^ 2 : ℝ) : ℂ) * inner ℂ (v i) (v j) := by
    calc
      inner ℂ (T (v i)) (T (v j)) =
          inner ℂ (v i) (T.adjoint (T (v j))) :=
        (T.adjoint_inner_right (v i) (T (v j))).symm
      _ = inner ℂ (v i) (((σ j ^ 2 : ℝ) : ℂ) • v j) := by
        rw [← heigen j]
        rfl
      _ = _ := by rw [inner_smul_right]
  have hf : Orthonormal ℂ (s.domRestrict f) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (σ (i : Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast i.property
    have hj : (σ (j : Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast j.property
    change inner ℂ
      (((σ (i : Fin d) : ℂ)⁻¹) • T (v i))
      (((σ (j : Fin d) : ℂ)⁻¹) • T (v j)) = _
    rw [inner_smul_left, inner_smul_right, hGram,
      v.inner_eq_ite]
    by_cases same : i = j
    · subst j
      simp only [ite_true, mul_one]
      have real_star :
          starRingEnd ℂ ((σ (i : Fin d) : ℂ)⁻¹) =
            ((σ (i : Fin d) : ℂ)⁻¹) := by simp only [map_inv₀, conj_ofReal]
      rw [real_star]
      push_cast
      field_simp
    · have unequal : (i : Fin d) ≠ (j : Fin d) := by
        intro equal
        exact same (Subtype.ext equal)
      simp only [map_inv₀, conj_ofReal, ofReal_pow, unequal, ↓reduceIte, mul_zero, same]
  obtain ⟨u, hu⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (by
        rw [Fintype.card_fin]
        exact finrank_euclideanSpace_fin) hf
  have singular (i : Fin d) :
      T (v i) = (σ i : ℂ) • u i := by
    by_cases zero : σ i = 0
    · have kernel : (T.adjoint ∘ₗ T) (v i) = 0 := by
        rw [heigen i, zero]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ofReal_zero,
          zero_smul]
      have image : T (v i) = 0 := by
        apply LinearMap.mem_ker.mp
        rw [← T.ker_adjoint_comp_self]
        exact LinearMap.mem_ker.mpr kernel
      simp only [image, zero, ofReal_zero, zero_smul]
    · have chosen : u i = f i := hu i zero
      rw [chosen]
      change T (v i) =
        (σ i : ℂ) • (((σ i : ℂ)⁻¹) • T (v i))
      rw [smul_smul, mul_inv_cancel₀]
      · simp only [one_smul]
      · exact_mod_cast zero
  refine ⟨orthonormalBasisUnitary u, ?_⟩
  have eigen_unitary :
      orthonormalBasisUnitary v =
        hF.isHermitian.eigenvectorUnitary := rfl
  ext ⟨a, b⟩
  rw [schmidtVector_apply]
  have repr :
      T ((EuclideanSpace.basisFun (Fin d) ℂ) a) =
        ∑ i : Fin d,
          inner ℂ (v i) ((EuclideanSpace.basisFun (Fin d) ℂ) a) •
            T (v i) := by
    calc
      T ((EuclideanSpace.basisFun (Fin d) ℂ) a) =
          T (∑ i : Fin d,
            inner ℂ (v i) ((EuclideanSpace.basisFun (Fin d) ℂ) a) •
              v i) := by rw [v.sum_repr']
      _ = _ := by simp only [EuclideanSpace.basisFun_apply, map_sum, map_smul]
  have coordinate := congrArg
    (fun z : EuclideanSpace ℂ (Fin d) => z b) repr
  have replace :
      conjugateUnitary
          hF.isHermitian.eigenvectorUnitary =
        conjugateUnitary
          (orthonormalBasisUnitary v) := by
    rw [eigen_unitary]
  rw [replace]
  simpa [T, C, σ, targetCoefficientMatrix, Matrix.toLpLin_apply,
    EuclideanSpace.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, EuclideanSpace.inner_single_right,
    conjugateUnitary_apply,
    orthonormalBasisUnitary_apply, singular,
    mul_assoc, mul_left_comm, mul_comm] using coordinate

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem conjugateUnitaryBasisOverlap_norm_sq
    {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (i j : Fin d) :
    ‖unitaryBasisOverlap
      (conjugateUnitary U)
      (conjugateUnitary V) i j‖ ^ 2 =
      ‖unitaryBasisOverlap U V i j‖ ^ 2 := by
  have hconj :
      unitaryBasisOverlap
        (conjugateUnitary U)
        (conjugateUnitary V) i j =
        star (unitaryBasisOverlap U V i j) := by
    simp only [unitaryBasisOverlap_apply, Matrix.mul_apply, conjTranspose_apply,
      conjugateUnitary_apply, RCLike.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply,
      star_sum, star_mul']
  rw [hconj, norm_star]

private def targetCanonicalSpectralEnergy
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  let F := targetReducedDensity ξ
  let G := targetReducedDensity ζ
  let hF := targetReducedDensity_posSemidef ξ
  let hG := targetReducedDensity_posSemidef ζ
  ∑ i : Fin d, ∑ j : Fin d,
    (Real.sqrt (hF.isHermitian.eigenvalues i) -
      Real.sqrt (hG.isHermitian.eigenvalues j)) ^ 2 *
      spectralAtomOverlap F G hF hG i j

theorem targetCanonicalSpectralEnergy_le_of_canonicalSchmidt
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (V W : Matrix.unitaryGroup (Fin d) ℂ)
    (hξ :
      ξ.val = schmidtVector
        (fun i => Real.sqrt
          ((targetReducedDensity_posSemidef ξ).isHermitian.eigenvalues i))
        (conjugateUnitary
          (targetReducedDensity_posSemidef ξ).isHermitian.eigenvectorUnitary)
        V)
    (hζ :
      ζ.val = schmidtVector
        (fun j => Real.sqrt
          ((targetReducedDensity_posSemidef ζ).isHermitian.eigenvalues j))
        (conjugateUnitary
          (targetReducedDensity_posSemidef ζ).isHermitian.eigenvectorUnitary)
        W) :
    targetCanonicalSpectralEnergy ξ ζ ≤
      2 * ‖ξ.val - ζ.val‖ ^ 2 := by
  let F := targetReducedDensity ξ
  let G := targetReducedDensity ζ
  let hF : F.PosSemidef := targetReducedDensity_posSemidef ξ
  let hG : G.PosSemidef := targetReducedDensity_posSemidef ζ
  have hFtrace : Matrix.trace F = 1 :=
    targetReducedDensity_trace ξ
  have hGtrace : Matrix.trace G = 1 :=
    targetReducedDensity_trace ζ
  have hσunit :
      (∑ i : Fin d, (Real.sqrt (hF.isHermitian.eigenvalues i)) ^ 2) = 1 := by
    simp_rw [Real.sq_sqrt (hF.eigenvalues_nonneg _)]
    exact positiveDensity_eigenvalues_sum F hF hFtrace
  have hμunit :
      (∑ j : Fin d, (Real.sqrt (hG.isHermitian.eigenvalues j)) ^ 2) = 1 := by
    simp_rw [Real.sq_sqrt (hG.eigenvalues_nonneg _)]
    exact positiveDensity_eigenvalues_sum G hG hGtrace
  have henergy := schmidtVector_spectralEnergy_le
    (fun i => Real.sqrt (hF.isHermitian.eigenvalues i))
    (fun j => Real.sqrt (hG.isHermitian.eigenvalues j))
    (fun i => Real.sqrt_nonneg _)
    (fun j => Real.sqrt_nonneg _)
    hσunit hμunit
    (conjugateUnitary hF.isHermitian.eigenvectorUnitary) V
    (conjugateUnitary hG.isHermitian.eigenvectorUnitary) W
  simp_rw [conjugateUnitaryBasisOverlap_norm_sq,
    ← targetSpectralAtomOverlap_eq_basis_norm_sq F G hF hG] at henergy
  change targetCanonicalSpectralEnergy ξ ζ ≤
    2 * ‖ξ.val - ζ.val‖ ^ 2
  simpa only [targetCanonicalSpectralEnergy, hξ, hζ]
    using henergy

theorem targetCanonicalSpectralEnergy_le
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    targetCanonicalSpectralEnergy ξ ζ ≤
      2 * ‖ξ.val - ζ.val‖ ^ 2 := by
  obtain ⟨V, hξ⟩ :=
    exists_proofTargetCanonicalSpectralSchmidtDecomposition ξ
  obtain ⟨W, hζ⟩ :=
    exists_proofTargetCanonicalSpectralSchmidtDecomposition ζ
  apply targetCanonicalSpectralEnergy_le_of_canonicalSchmidt
    ξ ζ V W
  · exact hξ
  · exact hζ

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


theorem harmonicCoherentSharedResource_inverseAbsorption_distance
    {d n : ℕ}
    (U V : Matrix.unitaryGroup (Fin (d * n)) ℂ)
    (resource : BipartiteUnitVector d) :
    ‖localUnitaryAction U⁻¹ V⁻¹
        (tensorEmbezzlementTarget (n := n) resource) -
      embezzlementState (d * n)‖ =
      ‖localUnitaryAction U V
          (embezzlementState (d * n)) -
        tensorEmbezzlementTarget (n := n) resource‖ := by
  have reset :
      localUnitaryAction U V
        (localUnitaryAction U⁻¹ V⁻¹
          (tensorEmbezzlementTarget (n := n) resource)) =
        tensorEmbezzlementTarget (n := n) resource := by
    simpa only [inv_inv] using
      (localUnitaryPureResidual_targetLocalInverse_reset
        U⁻¹ V⁻¹
        (tensorEmbezzlementTarget (n := n) resource))
  calc
    _ = ‖localUnitaryAction U V
        (localUnitaryAction U⁻¹ V⁻¹
          (tensorEmbezzlementTarget (n := n) resource) -
          embezzlementState (d * n))‖ :=
      (localUnitaryAction_norm U V _).symm
    _ = ‖tensorEmbezzlementTarget (n := n) resource -
          localUnitaryAction U V
            (embezzlementState (d * n))‖ := by
      rw [localUnitaryAction_sub, reset]
    _ = _ := norm_sub_rev _ _

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


theorem dSVProjectorSquaredDifference_trace
    {d : Type*} [Fintype d]
    (P Q : Matrix d d ℂ)
    (hP : P * P = P) (hQ : Q * Q = Q) :
    (Matrix.trace ((P - Q) * (P - Q))).re =
      (Matrix.trace P).re + (Matrix.trace Q).re -
        2 * (Matrix.trace (P * Q)).re := by
  classical
  have complex :
      Matrix.trace ((P - Q) * (P - Q)) =
        Matrix.trace P + Matrix.trace Q -
          2 * Matrix.trace (P * Q) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
      hP, hQ, Matrix.trace_mul_comm Q P]
    ring
  rw [complex]
  simp only [sub_re, add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


theorem dSVCanonicalFailurePrefix_card
    {d : ℕ} (r : Fin (d + 1)) :
    (Finset.univ.filter
      (fun i : Fin d => i.val < r.val)).card = r.val := by
  classical
  calc
    (Finset.univ.filter
      (fun i : Fin d => i.val < r.val)).card =
        (Finset.range r.val).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i member
        exact Finset.mem_range.mpr (Finset.mem_filter.mp member).2
      · intro i _ j _ equal
        exact Fin.ext equal
      · intro j member
        have before : j < r.val := Finset.mem_range.mp member
        have bounded : j < d := by
          have endpoint : r.val ≤ d := by omega
          omega
        refine ⟨⟨j, bounded⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, before⟩
    _ = r.val := Finset.card_range _

/--
The DSV canonical failure prefix construction used in the quantum parallel-repetition argument.
-/
def dSVCanonicalFailurePrefix
    {d : ℕ} (r : Fin (d + 1)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 fun q : Fin d × Fin d =>
    if q.1 = q.2 ∧ q.1.val < r.val then 1 else 0

theorem dSVCanonicalFailurePrefix_norm_sq
    {d : ℕ} (r : Fin (d + 1)) :
    ‖dSVCanonicalFailurePrefix r‖ ^ 2 = (r.val : ℝ) := by
  classical
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  change
    (∑ i : Fin d, ∑ j : Fin d,
      ‖if i = j ∧ i.val < r.val then (1 : ℂ) else 0‖ ^ 2) =
      (r.val : ℝ)
  have atom (i j : Fin d) :
      ‖if i = j ∧ i.val < r.val then (1 : ℂ) else 0‖ ^ 2 =
        if i = j then if i.val < r.val then (1 : ℝ) else 0
        else 0 := by
    by_cases same : i = j
    · subst j
      by_cases before : i.val < r.val <;> simp [before]
    · simp only [same, false_and, ↓reduceIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
  simp_rw [atom]
  have count := dSVCanonicalFailurePrefix_card r
  simpa only [sum_ite_eq, mem_univ, ↓reduceIte, sum_boole, Nat.cast_inj] using congrArg
    (fun n : ℕ => (n : ℝ)) count

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


theorem dSVProjectorComplement_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Matrix d d ℂ) (positive : P.PosSemidef)
    (projective : P * P = P) :
    (1 - P).PosSemidef := by
  have gram :
      (1 - P).conjTranspose * (1 - P) = (1 - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      positive.isHermitian.eq]
    simp only [Matrix.mul_sub, mul_one, Matrix.sub_mul, one_mul, projective, sub_self, sub_zero]
  rw [← gram]
  exact Matrix.posSemidef_conjTranspose_mul_self (1 - P)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


theorem dSVCanonicalFailurePrefix_inner
    {d : ℕ} (r s : Fin (d + 1)) :
    inner ℂ (dSVCanonicalFailurePrefix r)
        (dSVCanonicalFailurePrefix s) =
      (min r.val s.val : ℕ) := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change
    (∑ q : Fin d × Fin d,
      (if q.1 = q.2 ∧ q.1.val < s.val then (1 : ℂ) else 0) *
        star (if q.1 = q.2 ∧ q.1.val < r.val
          then (1 : ℂ) else 0)) =
      (min r.val s.val : ℕ)
  rw [Fintype.sum_prod_type]
  change
    (∑ i : Fin d, ∑ j : Fin d,
      (if i = j ∧ i.val < s.val then (1 : ℂ) else 0) *
        star (if i = j ∧ i.val < r.val then (1 : ℂ) else 0)) =
      (min r.val s.val : ℕ)
  have atom (i j : Fin d) :
      (if i = j ∧ i.val < s.val then (1 : ℂ) else 0) *
        star (if i = j ∧ i.val < r.val then (1 : ℂ) else 0) =
        if i = j then
          if i.val < min r.val s.val then (1 : ℂ) else 0
        else 0 := by
    by_cases same : i = j
    · subst j
      by_cases belowr : i.val < r.val
      · by_cases belows : i.val < s.val
        · simp only [belows, and_self, ↓reduceIte, belowr, star_one, mul_one, lt_inf_iff]
        · simp only [belows, and_false, ↓reduceIte, belowr, and_self, star_one, mul_one,
            lt_inf_iff]
      · by_cases belows : i.val < s.val
        · simp only [belows, and_self, ↓reduceIte, belowr, and_false, star_zero, mul_zero,
            lt_inf_iff, and_true]
        · simp only [belows, and_false, ↓reduceIte, belowr, star_zero, mul_zero, lt_inf_iff,
            and_self]
    · simp only [same, false_and, ↓reduceIte, star_zero, mul_zero]
  simp_rw [atom]
  let t : Fin (d + 1) := ⟨min r.val s.val, by
    have hr : r.val ≤ d := by omega
    have hs : s.val ≤ d := by omega
    omega⟩
  have counted := dSVCanonicalFailurePrefix_card t
  have cast_counted := congrArg (fun n : ℕ => (n : ℂ)) counted
  simpa [t, Finset.sum_boole] using cast_counted

theorem dSVCanonicalFailurePrefix_sub_norm_sq
    {d : ℕ} (r s : Fin (d + 1)) :
    ‖dSVCanonicalFailurePrefix r -
        dSVCanonicalFailurePrefix s‖ ^ 2 =
      |(r.val : ℝ) - (s.val : ℝ)| := by
  rw [@norm_sub_sq ℂ,
    dSVCanonicalFailurePrefix_norm_sq,
    dSVCanonicalFailurePrefix_norm_sq,
    dSVCanonicalFailurePrefix_inner]
  change
    (r.val : ℝ) - 2 * (min r.val s.val : ℕ) + (s.val : ℝ) =
      |(r.val : ℝ) - (s.val : ℝ)|
  by_cases order : r.val ≤ s.val
  · rw [min_eq_left order, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (by exact_mod_cast order)
  · have opposite : s.val ≤ r.val := Nat.le_of_not_ge order
    rw [min_eq_right opposite, abs_of_nonneg]
    · ring
    · exact sub_nonneg.mpr (by exact_mod_cast opposite)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The finite equivalence encoding DSV rank controlled target catalyst index. -/
def dSVRankControlledTargetCatalystIndexEquiv
    {ι : Type*} [Fintype ι]
    (d n : ℕ) :
    ((Fin d × ι) × Fin n) ≃
      Fin (d * (Fintype.card ι * n)) :=
  (Equiv.prodAssoc (Fin d) ι (Fin n)).trans
    ((Equiv.prodCongr (Equiv.refl (Fin d))
      ((Equiv.prodCongr (Fintype.equivFin ι)
        (Equiv.refl (Fin n))).trans finProdFinEquiv)).trans
      finProdFinEquiv)

end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem dSVMixedProjectorSuccessLoss_le_square
    {d : Type*} [Fintype d] [DecidableEq d]
    (P R : Matrix d d ℂ)
    (hcomplement : (1 - P).PosSemidef)
    (hR : R.PosSemidef)
    (hPP : P * P = P) (hRR : R * R = R) :
    (Matrix.trace P).re - (Matrix.trace (P * R)).re ≤
      (Matrix.trace ((P - R) * (P - R))).re := by
  have remainder := trace_mul_posSemidef_nonneg hcomplement hR
  have square :
      (Matrix.trace ((P - R) * (P - R))).re =
        (Matrix.trace P).re + (Matrix.trace R).re -
          2 * (Matrix.trace (P * R)).re := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      hPP, hRR, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_sub, Matrix.trace_mul_comm R P]
    simp only [sub_re]
    ring
  have rest :
      0 ≤ (Matrix.trace R).re - (Matrix.trace (P * R)).re := by
    simpa only [sub_nonneg, Matrix.sub_mul, one_mul, trace_sub, sub_re] using remainder
  rw [square]
  linarith

theorem dSVWeightedMixedProjectorSuccessLoss_le_square
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq d]
    (w : κ → ℝ) (nonnegative : ∀ k, 0 ≤ w k)
    (P R : κ → Matrix d d ℂ)
    (hcomplement : ∀ k, (1 - P k).PosSemidef)
    (hR : ∀ k, (R k).PosSemidef)
    (hPP : ∀ k, P k * P k = P k)
    (hRR : ∀ k, R k * R k = R k) :
    (∑ k : κ, w k * (Matrix.trace (P k)).re) -
        (∑ k : κ, w k * (Matrix.trace (P k * R k)).re) ≤
      ∑ k : κ, w k *
        (Matrix.trace ((P k - R k) * (P k - R k))).re := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k _
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_left
    (dSVMixedProjectorSuccessLoss_le_square
      (P k) (R k) (hcomplement k) (hR k) (hPP k) (hRR k))
    (nonnegative k)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The positive operator-valued measurement implementing DSV global projector binary. -/
def dSVGlobalProjectorBinaryPOVM
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (P : κ → Matrix d d ℂ)
    (positive : ∀ k, (P k).PosSemidef)
    (complement : ∀ k, (1 - P k).PosSemidef) :
    POVM Bool (Σ _ : κ, d) where
  effect b := Matrix.blockDiagonal' fun k =>
    if b then P k else 1 - P k
  positive b := by
    apply posSemidef_blockDiagonal'
    intro k
    cases b
    · exact complement k
    · exact positive k
  complete := by
    classical
    rw [Fintype.sum_bool]
    ext ⟨k, i⟩ ⟨l, j⟩
    by_cases same : k = l
    · subst l
      simp only [↓reduceIte, Bool.false_eq_true, Matrix.add_apply, blockDiagonal'_apply,
        ↓reduceDIte, cast_eq, Matrix.sub_apply, Matrix.one_apply, add_sub_cancel, Sigma.mk.injEq,
        heq_eq_eq, true_and]
    · simp only [↓reduceIte, Bool.false_eq_true, Matrix.add_apply, blockDiagonal'_apply, same,
        ↓reduceDIte, add_zero, ne_eq, Sigma.mk.injEq, heq_eq_eq, false_and, not_false_eq_true,
        one_apply_ne]

theorem dSVGlobalProjectorBinaryPOVM_projective
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (P : κ → Matrix d d ℂ)
    (positive : ∀ k, (P k).PosSemidef)
    (complement : ∀ k, (1 - P k).PosSemidef)
    (projective : ∀ k, P k * P k = P k)
    (b : Bool) :
    (dSVGlobalProjectorBinaryPOVM
      P positive complement).effect b *
      (dSVGlobalProjectorBinaryPOVM
        P positive complement).effect b =
      (dSVGlobalProjectorBinaryPOVM
        P positive complement).effect b := by
  change
    Matrix.blockDiagonal' (fun k => if b then P k else 1 - P k) *
      Matrix.blockDiagonal' (fun k => if b then P k else 1 - P k) =
      Matrix.blockDiagonal' (fun k => if b then P k else 1 - P k)
  rw [← Matrix.blockDiagonal'_mul]
  apply congrArg (fun A : κ → Matrix d d ℂ => Matrix.blockDiagonal' A)
  funext k
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_sub, mul_one, Matrix.sub_mul, one_mul,
      projective k, sub_self, sub_zero]
  · exact projective k

theorem dSVActualGlobalMixedBornSuccess_eq
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (k₀ : κ) (i₀ : d) (nonzero : τ k₀ ≠ 0)
    (P R : κ → Matrix d d ℂ)
    (hP : ∀ k, (P k).PosSemidef)
    (hPc : ∀ k, (1 - P k).PosSemidef)
    (hR : ∀ k, (R k).PosSemidef)
    (hRc : ∀ k, (1 - R k).PosSemidef)
    (hPP : ∀ k, P k * P k = P k)
    (hRR : ∀ k, R k * R k = R k) :
    binaryJointSuccessProbability
      (pureDensityMatrix
        (sharedThresholdResource (d := d) τ)
        (sharedThresholdResource_norm τ k₀ i₀ nonzero))
      (dSVGlobalProjectorBinaryPOVM P hP hPc)
      (transposePOVM
        (dSVGlobalProjectorBinaryPOVM R hR hRc)) =
      (∑ k : κ, τ k ^ 2 * (Matrix.trace (P k * R k)).re) /
        ((Fintype.card d : ℝ) * ∑ k : κ, τ k ^ 2) := by
  let A := dSVGlobalProjectorBinaryPOVM P hP hPc
  let B := transposePOVM
    (dSVGlobalProjectorBinaryPOVM R hR hRc)
  let z := sharedThresholdResource (d := d) τ
  have hz : ‖z‖ = 1 :=
    sharedThresholdResource_norm τ k₀ i₀ nonzero
  have hA : ∀ b : Bool, A.effect b * A.effect b = A.effect b :=
    dSVGlobalProjectorBinaryPOVM_projective
      P hP hPc hPP
  have hB : ∀ b : Bool, B.effect b * B.effect b = B.effect b :=
    transposePOVM_projective
      (dSVGlobalProjectorBinaryPOVM R hR hRc)
      (dSVGlobalProjectorBinaryPOVM_projective
        R hR hRc hRR)
  change binaryJointSuccessProbability
    (pureDensityMatrix z hz) A B = _
  unfold binaryJointSuccessProbability
    binaryBornProbability
  rw [← coherentBinaryJointOutcome_norm_sq
    A B hA hB z hz true true]
  change
    ‖toLp 2
      ((Matrix.blockDiagonal' P ⊗ₖ
        (Matrix.blockDiagonal' R).transpose).mulVec
          (ofLp (sharedThresholdResource (d := d) τ)))‖ ^ 2 = _
  exact sharedThresholdResource_block_action_norm_sq
    τ P R hP hR hPP hRR

end

section

open scoped BigOperators

/-- The DSV rational soft pass construction used in the quantum parallel-repetition argument. -/
def dSVRationalSoftPass (t x : ℝ) : ℝ :=
  x / (x + t)

theorem dSVRationalSoftPass_mem_unit
    {t x : ℝ} (positive : 0 < t) (nonnegative : 0 ≤ x) :
    0 ≤ dSVRationalSoftPass t x ∧
      dSVRationalSoftPass t x ≤ 1 := by
  unfold dSVRationalSoftPass
  have denominator : 0 < x + t := by linarith
  constructor
  · exact div_nonneg nonnegative denominator.le
  · apply (div_le_iff₀ denominator).mpr
    linarith

theorem dSVRationalSoftPass_sub
    {t a b : ℝ} (positive : 0 < t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    dSVRationalSoftPass t a -
        dSVRationalSoftPass t b =
      t * (a - b) / ((a + t) * (b + t)) := by
  unfold dSVRationalSoftPass
  have da : a + t ≠ 0 := by linarith
  have db : b + t ≠ 0 := by linarith
  field_simp
  ring

theorem dSVRationalSoftPass_lipschitz
    {t a b : ℝ} (positive : 0 < t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |dSVRationalSoftPass t a -
        dSVRationalSoftPass t b| ≤ |a - b| / t := by
  have denominator : 0 < (a + t) * (b + t) :=
    mul_pos (by linarith) (by linarith)
  rw [dSVRationalSoftPass_sub positive ha hb,
    abs_div, abs_mul, abs_of_pos positive, abs_of_pos denominator]
  apply (div_le_iff₀ denominator).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ positive).mpr
  have wide : t ^ 2 ≤ (a + t) * (b + t) := by
    nlinarith [mul_nonneg ha hb]
  linarith [mul_le_mul_of_nonneg_left wide (abs_nonneg (a - b))]

end

section

open scoped BigOperators ComplexOrder MatrixOrder


theorem dSVAdaptiveSoft_sqrt_sub_sq_le_abs
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have sa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have sb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have square_a : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have square_b : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  rcases le_total a b with ordered | ordered
  · rw [abs_of_nonpos (sub_nonpos.mpr ordered)]
    have roots := Real.sqrt_le_sqrt ordered
    linarith [mul_nonneg sa (sub_nonneg.mpr roots)]
  · rw [abs_of_nonneg (sub_nonneg.mpr ordered)]
    have roots := Real.sqrt_le_sqrt ordered
    linarith [mul_nonneg sb (sub_nonneg.mpr roots)]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The DSV soft bob left reduced density construction used in the quantum parallel-repetition
argument.
-/
def dSVSoftBobLeftReducedDensity
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix (Fin d) (Fin d) ℂ :=
  targetCoefficientMatrix ζ *
    (targetCoefficientMatrix ζ).conjTranspose

theorem dSVSoftBobLeftReducedDensity_posSemidef
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    (dSVSoftBobLeftReducedDensity ζ).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose
    (targetCoefficientMatrix ζ)

theorem dSVSoftBobLeftReducedDensity_trace
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix.trace (dSVSoftBobLeftReducedDensity ζ) = 1 := by
  unfold dSVSoftBobLeftReducedDensity
  calc
    Matrix.trace
        (targetCoefficientMatrix ζ *
          (targetCoefficientMatrix ζ).conjTranspose) =
        Matrix.trace
          ((targetCoefficientMatrix ζ).conjTranspose *
            targetCoefficientMatrix ζ) :=
      Matrix.trace_mul_comm _ _
    _ = 1 := targetReducedDensity_trace ζ

/-- The unitary operator implementing DSV original computational reindexed. -/
def dSVOriginalComputationalReindexedUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ℕ} (e : ι ≃ Fin D)
    (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup (Fin D) ℂ := by
  classical
  let M : Matrix ι ι ℂ := U.val
  refine ⟨(Matrix.reindex e e) M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star ((Matrix.reindex e e) M) =
        (Matrix.reindex e e) (star M) := by
    ext i j
    simp only [reindex_apply, star_apply, submatrix_apply, RCLike.star_def, star_eq_conjTranspose,
      conjTranspose_apply]
  rw [compatible]
  change (Matrix.reindexRingEquiv ℂ e) (star M) *
    (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp U.property]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

end

section

open scoped BigOperators ComplexOrder

/--
The DSV heterogeneous real prefix construction used in the quantum parallel-repetition argument.
-/
def dSVHeterogeneousRealPrefix
    (continuation : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, continuation i

theorem dSVHeterogeneousRealPrefix_succ
    (continuation : ℕ → ℝ) (k : ℕ) :
    dSVHeterogeneousRealPrefix continuation (k + 1) =
      dSVHeterogeneousRealPrefix continuation k *
        continuation k := by
  simp only [dSVHeterogeneousRealPrefix, prod_range_succ]

theorem dSVHeterogeneousRealStopping_escape_identity
    (continuation : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      dSVHeterogeneousRealPrefix continuation k *
        (1 - continuation k)) =
      1 - dSVHeterogeneousRealPrefix continuation N := by
  induction N with
  | zero =>
      simp only [range_zero, dSVHeterogeneousRealPrefix, sum_empty, prod_empty, sub_self]
  | succ N ih =>
      simp only [Finset.sum_range_succ,
        dSVHeterogeneousRealPrefix_succ]
      linear_combination ih

theorem dSVHeterogeneousRealPrefix_nonneg
    (continuation : ℕ → ℝ)
    (nonnegative : ∀ k, 0 ≤ continuation k) (k : ℕ) :
    0 ≤ dSVHeterogeneousRealPrefix continuation k := by
  unfold dSVHeterogeneousRealPrefix
  exact Finset.prod_nonneg (fun i _ => nonnegative i)

theorem dSVHeterogeneousRealStopping_escape_budget
    (continuation escape : ℕ → ℝ)
    (continuation_nonnegative : ∀ k, 0 ≤ continuation k)
    (escape_bound : ∀ k, continuation k + escape k ≤ 1)
    (N : ℕ) :
    (∑ k ∈ Finset.range N,
      dSVHeterogeneousRealPrefix continuation k * escape k)
      ≤ 1 := by
  have each (k : ℕ) :
      dSVHeterogeneousRealPrefix continuation k * escape k ≤
        dSVHeterogeneousRealPrefix continuation k *
          (1 - continuation k) := by
    apply mul_le_mul_of_nonneg_left
    · linarith [escape_bound k]
    · exact dSVHeterogeneousRealPrefix_nonneg
        continuation continuation_nonnegative k
  calc
    (∑ k ∈ Finset.range N,
      dSVHeterogeneousRealPrefix continuation k * escape k)
        ≤ ∑ k ∈ Finset.range N,
          dSVHeterogeneousRealPrefix continuation k *
            (1 - continuation k) := by
              exact Finset.sum_le_sum (fun k _ => each k)
    _ = 1 - dSVHeterogeneousRealPrefix continuation N :=
      dSVHeterogeneousRealStopping_escape_identity
        continuation N
    _ ≤ 1 := by
      have := dSVHeterogeneousRealPrefix_nonneg
        continuation continuation_nonnegative N
      linarith

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The type used to represent DSV uniform density threshold local index in the exact sampling
construction.
-/
abbrev DSVUniformDensityThresholdLocalIndex
    (N d : ℕ) :=
  Σ _ : Fin N, Fin d

/-- The quantum state representing DSV uniform density threshold shared. -/
def dSVUniformDensityThresholdSharedState
    (N d : ℕ) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  sharedThresholdResource (d := Fin d)
    (fun _ : Fin N => (1 : ℝ))

theorem dSVUniformDensityThresholdRaw_norm_sq
    (N d : ℕ) :
    ‖sharedThresholdResourceRaw (d := Fin d)
      (fun _ : Fin N => (1 : ℝ))‖ ^ 2 =
      (d : ℝ) * (N : ℝ) := by
  simpa only [Fintype.card_fin, one_pow, sum_const, card_univ, nsmul_eq_mul,
    mul_one] using sharedThresholdResourceRaw_norm_sq
    (d := Fin d) (fun _ : Fin N => (1 : ℝ))

theorem dSVUniformDensityThresholdSharedState_norm
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d) :
    ‖dSVUniformDensityThresholdSharedState N d‖ = 1 := by
  exact sharedThresholdResource_norm
    (fun _ : Fin N => (1 : ℝ))
    ⟨0, grid⟩ ⟨0, dimension⟩ (by norm_num)

theorem dSVUniformDensityThresholdSharedState_mismatchedFlag
    (N d : ℕ) (k l : Fin N) (i j : Fin d)
    (different : k ≠ l) :
    dSVUniformDensityThresholdSharedState N d
      (⟨k, i⟩, ⟨l, j⟩) = 0 := by
  simp only [dSVUniformDensityThresholdSharedState, sharedThresholdResource,
    sharedThresholdResourceRaw, ofReal_one, PiLp.smul_apply, different, false_and, ↓reduceIte,
    smul_zero]

theorem dSVUniformDensityThresholdSharedState_mismatchedWork
    (N d : ℕ) (k l : Fin N) (i j : Fin d)
    (different : i ≠ j) :
    dSVUniformDensityThresholdSharedState N d
      (⟨k, i⟩, ⟨l, j⟩) = 0 := by
  simp only [dSVUniformDensityThresholdSharedState, sharedThresholdResource,
    sharedThresholdResourceRaw, ofReal_one, PiLp.smul_apply, different, and_false, ↓reduceIte,
    smul_zero]

/--
The DSV uniform density threshold shared density construction used in the quantum parallel-
repetition argument.
-/
def dSVUniformDensityThresholdSharedDensity
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d) :
    DensityMatrix
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  pureDensityMatrix
    (dSVUniformDensityThresholdSharedState N d)
    (dSVUniformDensityThresholdSharedState_norm
      grid dimension)

theorem dSVUniformDensityThresholdShared_mixedBorn_eq
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (P R : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ k, (P k).PosSemidef)
    (hPc : ∀ k, (1 - P k).PosSemidef)
    (hR : ∀ k, (R k).PosSemidef)
    (hRc : ∀ k, (1 - R k).PosSemidef)
    (hPP : ∀ k, P k * P k = P k)
    (hRR : ∀ k, R k * R k = R k) :
    binaryJointSuccessProbability
      (dSVUniformDensityThresholdSharedDensity
        grid dimension)
      (dSVGlobalProjectorBinaryPOVM P hP hPc)
      (transposePOVM
        (dSVGlobalProjectorBinaryPOVM R hR hRc)) =
      (∑ k : Fin N, (Matrix.trace (P k * R k)).re) /
        ((d : ℝ) * (N : ℝ)) := by
  simpa only [dSVUniformDensityThresholdSharedDensity, dSVUniformDensityThresholdSharedState,
    one_pow, one_mul, Fintype.card_fin, sum_const, card_univ, nsmul_eq_mul, mul_one] using
    dSVActualGlobalMixedBornSuccess_eq
      (fun _ : Fin N => (1 : ℝ))
      ⟨0, grid⟩ ⟨0, dimension⟩ (by norm_num)
      P R hP hPc hR hRc hPP hRR

theorem dSVUniformDensityThresholdShared_diagonalBorn_eq
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (P : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ k, (P k).PosSemidef)
    (hPc : ∀ k, (1 - P k).PosSemidef)
    (hPP : ∀ k, P k * P k = P k) :
    binaryJointSuccessProbability
      (dSVUniformDensityThresholdSharedDensity
        grid dimension)
      (dSVGlobalProjectorBinaryPOVM P hP hPc)
      (transposePOVM
        (dSVGlobalProjectorBinaryPOVM P hP hPc)) =
      (∑ k : Fin N, (Matrix.trace (P k)).re) /
        ((d : ℝ) * (N : ℝ)) := by
  rw [dSVUniformDensityThresholdShared_mixedBorn_eq
    grid dimension P P hP hPc hP hPc hPP hPP]
  simp_rw [hPP]

/--
The type used to represent DSV uniform density independent history local index in the exact
sampling construction.
-/
abbrev DSVUniformDensityIndependentHistoryLocalIndex
    (L N d : ℕ) :=
  Fin L → DSVUniformDensityThresholdLocalIndex N d

private def dSVUniformDensityIndependentHistoryPairReindex
    (L N d : ℕ) :
    EuclideanSpace ℂ
      (Fin L →
        (DSVUniformDensityThresholdLocalIndex N d ×
          DSVUniformDensityThresholdLocalIndex N d)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (DSVUniformDensityIndependentHistoryLocalIndex
            L N d ×
          DSVUniformDensityIndependentHistoryLocalIndex
            L N d) := by
  classical
  exact LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    bilateralWorkPairEquiv.symm

/-- The quantum state representing DSV uniform density independent shared. -/
def dSVUniformDensityIndependentSharedState
    (L N d : ℕ) :
    EuclideanSpace ℂ
      (DSVUniformDensityIndependentHistoryLocalIndex L N d ×
        DSVUniformDensityIndependentHistoryLocalIndex L N d) :=
  dSVUniformDensityIndependentHistoryPairReindex L N d
    (finiteTensorVector
      (fun _ : Fin L =>
        dSVUniformDensityThresholdSharedState N d))

theorem dSVUniformDensityIndependentSharedState_apply
    (L N d : ℕ)
    (alice bob :
      DSVUniformDensityIndependentHistoryLocalIndex L N d) :
    dSVUniformDensityIndependentSharedState L N d
        (alice, bob) =
      ∏ j : Fin L,
        dSVUniformDensityThresholdSharedState N d
          (alice j, bob j) := by
  simp only [dSVUniformDensityIndependentSharedState,
    dSVUniformDensityIndependentHistoryPairReindex, bilateralWorkPairEquiv, Equiv.symm_mk,
    finiteTensorVector, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    Equiv.coe_fn_mk]

theorem dSVUniformDensityIndependentSharedState_norm
    (L : ℕ) {N d : ℕ}
    (grid : 0 < N) (dimension : 0 < d) :
    ‖dSVUniformDensityIndependentSharedState L N d‖ = 1 := by
  unfold dSVUniformDensityIndependentSharedState
  rw [LinearIsometryEquiv.norm_map]
  exact finiteTensorVector_norm
    (fun _ : Fin L =>
      dSVUniformDensityThresholdSharedState N d)
    (fun _ =>
      dSVUniformDensityThresholdSharedState_norm
        grid dimension)

end

section

open scoped BigOperators ComplexOrder MatrixOrder


private def dSVUniformDensitySpectralAtomDiscrepancy
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    |targetCanonicalSchmidtCoefficient ξ i ^ 2 -
      targetCanonicalSchmidtCoefficient ζ j ^ 2| *
      spectralAtomOverlap
        (targetReducedDensity ξ)
        (targetReducedDensity ζ)
        (targetReducedDensity_posSemidef ξ)
        (targetReducedDensity_posSemidef ζ) i j

private def dSVUniformDensitySchmidtSumMass
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    (targetCanonicalSchmidtCoefficient ξ i +
      targetCanonicalSchmidtCoefficient ζ j) ^ 2 *
      spectralAtomOverlap
        (targetReducedDensity ξ)
        (targetReducedDensity ζ)
        (targetReducedDensity_posSemidef ξ)
        (targetReducedDensity_posSemidef ζ) i j

theorem dSVUniformDensitySchmidtSumMass_le_four
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    dSVUniformDensitySchmidtSumMass ξ ζ ≤ 4 := by
  let F := targetReducedDensity ξ
  let G := targetReducedDensity ζ
  let hF : F.PosSemidef := targetReducedDensity_posSemidef ξ
  let hG : G.PosSemidef := targetReducedDensity_posSemidef ζ
  let σ := targetCanonicalSchmidtCoefficient ξ
  let μ := targetCanonicalSchmidtCoefficient ζ
  let overlap := spectralAtomOverlap F G hF hG
  have left :
      (∑ i : Fin d, ∑ j : Fin d,
        σ i ^ 2 * overlap i j) = 1 := by
    calc
      _ = ∑ i : Fin d, σ i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum,
          spectralAtomOverlap_sum_right F G hF hG i]
        simp only [mul_one]
      _ = 1 := targetCanonicalSchmidtCoefficient_sq_sum ξ
  have right :
      (∑ i : Fin d, ∑ j : Fin d,
        μ j ^ 2 * overlap i j) = 1 := by
    rw [Finset.sum_comm]
    calc
      (∑ j : Fin d, ∑ i : Fin d,
        μ j ^ 2 * overlap i j) =
          ∑ j : Fin d, μ j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.mul_sum,
              spectralAtomOverlap_sum_left F G hF hG j]
            simp only [mul_one]
      _ = 1 := targetCanonicalSchmidtCoefficient_sq_sum ζ
  have cross :
      (∑ i : Fin d, ∑ j : Fin d,
        σ i * μ j * overlap i j) ≤ 1 := by
    exact spectralAtomOverlap_schmidtMass_le_one
      F G hF hG (targetReducedDensity_trace ξ)
      (targetReducedDensity_trace ζ)
  have split :
      dSVUniformDensitySchmidtSumMass ξ ζ =
        (∑ i : Fin d, ∑ j : Fin d,
          σ i ^ 2 * overlap i j) +
        (∑ i : Fin d, ∑ j : Fin d,
          μ j ^ 2 * overlap i j) +
        2 * (∑ i : Fin d, ∑ j : Fin d,
          σ i * μ j * overlap i j) := by
    unfold dSVUniformDensitySchmidtSumMass
    change
      (∑ i : Fin d, ∑ j : Fin d,
        (σ i + μ j) ^ 2 * overlap i j) = _
    simp_rw [Finset.mul_sum]
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [split, left, right]
  linarith

theorem dSVUniformDensitySpectralAtomDiscrepancy_le
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    dSVUniformDensitySpectralAtomDiscrepancy ξ ζ ≤
      2 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ := by
  let F := targetReducedDensity ξ
  let G := targetReducedDensity ζ
  let hF : F.PosSemidef := targetReducedDensity_posSemidef ξ
  let hG : G.PosSemidef := targetReducedDensity_posSemidef ζ
  let σ := targetCanonicalSchmidtCoefficient ξ
  let μ := targetCanonicalSchmidtCoefficient ζ
  let weight : Fin d × Fin d → ℝ := fun ij =>
    spectralAtomOverlap F G hF hG ij.1 ij.2
  let f : Fin d × Fin d → ℝ := fun ij =>
    |σ ij.1 - μ ij.2|
  let g : Fin d × Fin d → ℝ := fun ij =>
    σ ij.1 + μ ij.2
  have hweight : ∀ ij, 0 ≤ weight ij := fun ij =>
    spectralAtomOverlap_nonneg F G hF hG ij.1 ij.2
  have cauchy := weighted_real_cauchy weight f g hweight
  have exact_l1 :
      (∑ ij : Fin d × Fin d, weight ij * f ij * g ij) =
        dSVUniformDensitySpectralAtomDiscrepancy ξ ζ := by
    rw [Fintype.sum_prod_type]
    unfold dSVUniformDensitySpectralAtomDiscrepancy
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have sum_nonnegative : 0 ≤ σ i + μ j :=
      add_nonneg
        (targetCanonicalSchmidtCoefficient_nonneg ξ i)
        (targetCanonicalSchmidtCoefficient_nonneg ζ j)
    have factor : σ i ^ 2 - μ j ^ 2 =
        (σ i - μ j) * (σ i + μ j) := by ring
    rw [factor, abs_mul, abs_of_nonneg sum_nonnegative]
    dsimp [weight, f, g, F, G, hF, hG, σ, μ]
    ring
  have exact_energy :
      (∑ ij : Fin d × Fin d, weight ij * f ij ^ 2) =
        targetCanonicalSpectralEnergy ξ ζ := by
    rw [Fintype.sum_prod_type]
    unfold targetCanonicalSpectralEnergy
    dsimp [weight, f, F, G, hF, hG, σ, μ,
      targetCanonicalSchmidtCoefficient]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [sq_abs]
    ring
  have exact_mass :
      (∑ ij : Fin d × Fin d, weight ij * g ij ^ 2) =
        dSVUniformDensitySchmidtSumMass ξ ζ := by
    rw [Fintype.sum_prod_type]
    unfold dSVUniformDensitySchmidtSumMass
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [weight, g, F, G, hF, hG, σ, μ]
    ring
  rw [exact_l1, exact_energy, exact_mass] at cauchy
  have target_energy := targetCanonicalSpectralEnergy_le ξ ζ
  have sum_mass := dSVUniformDensitySchmidtSumMass_le_four ξ ζ
  have first :
      Real.sqrt (targetCanonicalSpectralEnergy ξ ζ) ≤
        Real.sqrt 2 * ‖ξ.val - ζ.val‖ := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have square_two : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num)
      nlinarith [sq_nonneg ‖ξ.val - ζ.val‖]
  have second :
      Real.sqrt (dSVUniformDensitySchmidtSumMass ξ ζ) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · linarith
  calc
    _ ≤ Real.sqrt (targetCanonicalSpectralEnergy ξ ζ) *
        Real.sqrt (dSVUniformDensitySchmidtSumMass ξ ζ) :=
      cauchy
    _ ≤ (Real.sqrt 2 * ‖ξ.val - ζ.val‖) * 2 :=
      mul_le_mul first second
        (Real.sqrt_nonneg _) (by positivity)
    _ = 2 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ := by ring

end

section

open scoped BigOperators

namespace ClassicalSampling

variable {α : Type*} [Fintype α] [DecidableEq α]

private def markedFirst (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) : α :=
  permutation.symm
    (rank.symm
      ((marked.image (fun a => rank (permutation a))).min'
        (nonempty.image (fun a => rank (permutation a)))))

omit [DecidableEq α] in
theorem markedFirst_mem (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) :
    markedFirst rank marked nonempty permutation ∈ marked := by
  have hmin := (marked.image (fun a => rank (permutation a))).min'_mem
    (nonempty.image (fun a => rank (permutation a)))
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hmin
  simpa only [markedFirst, ← heq, Equiv.symm_apply_apply] using ha

omit [DecidableEq α] in
theorem markedFirst_rank (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) :
    rank (permutation (markedFirst rank marked nonempty permutation)) =
      (marked.image (fun a => rank (permutation a))).min'
        (nonempty.image (fun a => rank (permutation a))) := by
  simp only [markedFirst, Equiv.apply_symm_apply]

omit [DecidableEq α] in
theorem markedFirst_rank_le (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) {a : α} (ha : a ∈ marked) :
    rank (permutation (markedFirst rank marked nonempty permutation)) ≤
      rank (permutation a) := by
  rw [markedFirst_rank]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

omit [DecidableEq α] in
theorem markedFirst_eq_of_mem_of_rank_le
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) {a : α} (ha : a ∈ marked)
    (hle : ∀ b ∈ marked, rank (permutation a) ≤ rank (permutation b)) :
    markedFirst rank marked nonempty permutation = a := by
  apply permutation.injective
  apply rank.injective
  exact le_antisymm
    (markedFirst_rank_le rank marked nonempty permutation ha)
    (hle _ (markedFirst_mem rank marked nonempty permutation))

omit [DecidableEq α] in
theorem markedFirst_subset_eq_of_mem
    (rank : α ≃ Fin (Fintype.card α))
    {small large : Finset α}
    (hsmall : small.Nonempty) (hlarge : large.Nonempty)
    (permutation : Equiv.Perm α)
    (hsub : small ⊆ large)
    (hmem : markedFirst rank large hlarge permutation ∈ small) :
    markedFirst rank small hsmall permutation =
      markedFirst rank large hlarge permutation := by
  apply markedFirst_eq_of_mem_of_rank_le rank small hsmall permutation hmem
  intro a ha
  exact markedFirst_rank_le rank large hlarge permutation (hsub ha)

theorem markedFirst_eq_iff_union_first_mem_inter
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (permutation : Equiv.Perm α) :
    markedFirst rank left hleft permutation =
        markedFirst rank right hright permutation ↔
      markedFirst rank (left ∪ right) (hleft.mono Finset.subset_union_left)
          permutation ∈ left ∩ right := by
  let hunion : (left ∪ right).Nonempty :=
    hleft.mono Finset.subset_union_left
  constructor
  · intro hagree
    have hfirst :
        markedFirst rank (left ∪ right) hunion permutation =
          markedFirst rank left hleft permutation := by
      apply markedFirst_eq_of_mem_of_rank_le
        rank (left ∪ right) hunion permutation
      · exact Finset.mem_union_left right
          (markedFirst_mem rank left hleft permutation)
      · intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact markedFirst_rank_le rank left hleft permutation ha
        · rw [hagree]
          exact markedFirst_rank_le rank right hright permutation ha
    apply Finset.mem_inter.mpr
    constructor
    · rw [hfirst]
      exact markedFirst_mem rank left hleft permutation
    · rw [hfirst, hagree]
      exact markedFirst_mem rank right hright permutation
  · intro hcommon
    have hleft' := markedFirst_subset_eq_of_mem
      rank hleft hunion permutation Finset.subset_union_left
      (Finset.mem_inter.mp hcommon).1
    have hright' := markedFirst_subset_eq_of_mem
      rank hright hunion permutation Finset.subset_union_right
      (Finset.mem_inter.mp hcommon).2
    exact hleft'.trans hright'.symm

theorem markedFirst_ne_iff_union_first_mem_symmDiff
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (permutation : Equiv.Perm α) :
    markedFirst rank left hleft permutation ≠
        markedFirst rank right hright permutation ↔
      markedFirst rank (left ∪ right) (hleft.mono Finset.subset_union_left)
          permutation ∈ (left \ right) ∪ (right \ left) := by
  let hunion : (left ∪ right).Nonempty :=
    hleft.mono Finset.subset_union_left
  let a := markedFirst rank (left ∪ right) hunion permutation
  have ha : a ∈ left ∪ right :=
    markedFirst_mem rank (left ∪ right) hunion permutation
  have hagree := markedFirst_eq_iff_union_first_mem_inter
    rank left right hleft hright permutation
  change markedFirst rank left hleft permutation ≠
      markedFirst rank right hright permutation ↔
    a ∈ (left \ right) ∪ (right \ left)
  constructor
  · intro hne
    have hninter : a ∉ left ∩ right := by
      intro hinter
      exact hne (hagree.mpr hinter)
    rcases Finset.mem_union.mp ha with hla | hra
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr
        ⟨hla, fun hright' => hninter (Finset.mem_inter.mpr ⟨hla, hright'⟩)⟩
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr
        ⟨hra, fun hleft' => hninter (Finset.mem_inter.mpr ⟨hleft', hra⟩)⟩
  · intro hdiff heq
    have hinter : a ∈ left ∩ right := hagree.mp heq
    rcases Finset.mem_union.mp hdiff with hdiff | hdiff
    · exact (Finset.mem_sdiff.mp hdiff).2 (Finset.mem_inter.mp hinter).2
    · exact (Finset.mem_sdiff.mp hdiff).2 (Finset.mem_inter.mp hinter).1

omit [Fintype α] in
theorem swap_mem_iff_of_mem {marked : Finset α} {x y : α}
    (hx : x ∈ marked) (hy : y ∈ marked) (a : α) :
    Equiv.swap x y a ∈ marked ↔ a ∈ marked := by
  by_cases hax : a = x
  · subst a
    simp only [Equiv.swap_apply_left, hy, hx]
  · by_cases hay : a = y
    · subst a
      simp only [Equiv.swap_apply_right, hx, hy]
    · rw [Equiv.swap_apply_of_ne_of_ne hax hay]

theorem markedFirst_swap_trans
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    {x y : α} (hx : x ∈ marked) (hy : y ∈ marked)
    (permutation : Equiv.Perm α) :
    markedFirst rank marked nonempty ((Equiv.swap x y).trans permutation) =
      Equiv.swap x y (markedFirst rank marked nonempty permutation) := by
  apply markedFirst_eq_of_mem_of_rank_le
    rank marked nonempty ((Equiv.swap x y).trans permutation)
  · exact (swap_mem_iff_of_mem hx hy _).mpr
      (markedFirst_mem rank marked nonempty permutation)
  · intro a ha
    have hminimal := markedFirst_rank_le rank marked nonempty permutation
      ((swap_mem_iff_of_mem hx hy a).mpr ha)
    simpa only [Equiv.trans_apply, Equiv.swap_apply_self, ge_iff_le] using hminimal

private def firstFiber (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (a : α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun permutation =>
    markedFirst rank marked nonempty permutation = a

theorem firstFiber_card_eq
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    {x y : α} (hx : x ∈ marked) (hy : y ∈ marked) :
    (firstFiber rank marked nonempty x).card =
      (firstFiber rank marked nonempty y).card := by
  classical
  refine Finset.card_bij'
    (fun permutation _ => (Equiv.swap x y).trans permutation)
    (fun permutation _ => (Equiv.swap x y).trans permutation)
    ?_ ?_ ?_ ?_
  · intro permutation hpermutation
    have hfirst : markedFirst rank marked nonempty permutation = x :=
      (Finset.mem_filter.mp hpermutation).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [markedFirst_swap_trans rank marked nonempty hx hy permutation,
      hfirst, Equiv.swap_apply_left]
  · intro permutation hpermutation
    have hfirst : markedFirst rank marked nonempty permutation = y :=
      (Finset.mem_filter.mp hpermutation).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [markedFirst_swap_trans rank marked nonempty hx hy permutation,
      hfirst, Equiv.swap_apply_right]
  · intro permutation _
    ext a
    simp only [Equiv.trans_apply, Equiv.swap_apply_self]
  · intro permutation _
    ext a
    simp only [Equiv.trans_apply, Equiv.swap_apply_self]

theorem markedFirst_event_card_mul
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (event : Finset α) (hevent : event ⊆ marked) :
    (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank marked nonempty permutation ∈ event).card *
        marked.card =
      event.card * Fintype.card (Equiv.Perm α) := by
  classical
  obtain ⟨base, hbase⟩ := nonempty
  have hevent_card :
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
          markedFirst rank marked ⟨base, hbase⟩ permutation ∈ event).card =
        event.card * (firstFiber rank marked ⟨base, hbase⟩ base).card := by
    calc
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
          markedFirst rank marked ⟨base, hbase⟩ permutation ∈ event).card =
          ∑ a ∈ event,
            (firstFiber rank marked ⟨base, hbase⟩ a).card := by
              symm
              simpa only [firstFiber] using
                (Finset.sum_card_fiberwise_eq_card_filter
                  (Finset.univ : Finset (Equiv.Perm α)) event
                  (markedFirst rank marked ⟨base, hbase⟩))
      _ = event.card * (firstFiber rank marked ⟨base, hbase⟩ base).card :=
        Finset.sum_const_nat fun a ha =>
          firstFiber_card_eq rank marked ⟨base, hbase⟩ (hevent ha) hbase
  have htotal_card :
      Fintype.card (Equiv.Perm α) =
        marked.card * (firstFiber rank marked ⟨base, hbase⟩ base).card := by
    calc
      Fintype.card (Equiv.Perm α) =
          (Finset.univ : Finset (Equiv.Perm α)).card := by simp only [card_univ]
      _ = ∑ a ∈ marked,
            (firstFiber rank marked ⟨base, hbase⟩ a).card := by
              simpa only [card_univ, firstFiber] using
                (Finset.card_eq_sum_card_fiberwise
                  (f := markedFirst rank marked ⟨base, hbase⟩)
                  (s := (Finset.univ : Finset (Equiv.Perm α)))
                  (t := marked)
                  (fun permutation _ =>
                    markedFirst_mem rank marked ⟨base, hbase⟩ permutation))
      _ = marked.card * (firstFiber rank marked ⟨base, hbase⟩ base).card :=
        Finset.sum_const_nat fun a ha =>
          firstFiber_card_eq rank marked ⟨base, hbase⟩ ha hbase
  change
    (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank marked ⟨base, hbase⟩ permutation ∈ event).card *
        marked.card =
      event.card * Fintype.card (Equiv.Perm α)
  rw [hevent_card, htotal_card]
  ac_rfl

theorem sharedPermutation_disagreement_card_mul
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation).card *
        (left ∪ right).card =
      ((left \ right) ∪ (right \ left)).card *
        Fintype.card (Equiv.Perm α) := by
  classical
  let hunion : (left ∪ right).Nonempty :=
    hleft.mono Finset.subset_union_left
  have hsubset : (left \ right) ∪ (right \ left) ⊆ left ∪ right := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Finset.mem_union_left right (Finset.mem_sdiff.mp ha).1
    · exact Finset.mem_union_right left (Finset.mem_sdiff.mp ha).1
  have hfilter :
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) =
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank (left ∪ right) hunion permutation ∈
          (left \ right) ∪ (right \ left)) := by
    ext permutation
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact markedFirst_ne_iff_union_first_mem_symmDiff
      rank left right hleft hright permutation
  rw [hfilter]
  exact markedFirst_event_card_mul rank (left ∪ right) hunion
    ((left \ right) ∪ (right \ left)) hsubset

/-- The probability of uniform permutation. -/
def uniformPermutationProbability (event : Equiv.Perm α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter fun permutation : Equiv.Perm α =>
      event permutation).card : ℝ) / Fintype.card (Equiv.Perm α)

theorem markedFirst_event_probability
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (event : Finset α) (hevent : event ⊆ marked) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank marked nonempty permutation ∈ event) =
      (event.card : ℝ) / marked.card := by
  classical
  have hpermutation : 0 < (Fintype.card (Equiv.Perm α) : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨Equiv.refl α⟩ :
        0 < Fintype.card (Equiv.Perm α))
  have hmarked : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr nonempty : 0 < marked.card)
  unfold uniformPermutationProbability
  apply (div_eq_div_iff hpermutation.ne' hmarked.ne').mpr
  have hcount := markedFirst_event_card_mul
    rank marked nonempty event hevent
  have hreal :
      ((Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank marked nonempty permutation ∈ event).card : ℝ) *
          (marked.card : ℝ) =
        (event.card : ℝ) * (Fintype.card (Equiv.Perm α) : ℝ) := by
    exact_mod_cast hcount
  simpa only [] using hreal

theorem sharedPermutation_disagreement_probability
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) =
      (((left \ right) ∪ (right \ left)).card : ℝ) /
        (left ∪ right).card := by
  classical
  have hpermutation : 0 < (Fintype.card (Equiv.Perm α) : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨Equiv.refl α⟩ :
        0 < Fintype.card (Equiv.Perm α))
  have hunion : 0 < ((left ∪ right).card : ℝ) := by
    exact_mod_cast
      (Finset.card_pos.mpr
        (hleft.mono Finset.subset_union_left) :
        0 < (left ∪ right).card)
  unfold uniformPermutationProbability
  apply (div_eq_div_iff hpermutation.ne' hunion.ne').mpr
  exact_mod_cast
    sharedPermutation_disagreement_card_mul rank left right hleft hright

theorem sharedPermutation_disagreement_probability_le
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) ≤
      (((left \ right) ∪ (right \ left)).card : ℝ) / left.card := by
  rw [sharedPermutation_disagreement_probability
    rank left right hleft hright]
  apply div_le_div_of_nonneg_left
  · positivity
  · exact_mod_cast (Finset.card_pos.mpr hleft : 0 < left.card)
  · exact_mod_cast (Finset.card_le_card Finset.subset_union_left :
      left.card ≤ (left ∪ right).card)

private def markedTotalVariation (left right : Finset α) : ℝ :=
  (((left \ right) ∪ (right \ left)).card : ℝ) /
    (2 * (left.card : ℝ))

theorem sharedPermutation_disagreement_probability_le_two_mul_tv
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (_equal_card : left.card = right.card) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) ≤
      2 * markedTotalVariation left right := by
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm α =>
          markedFirst rank left hleft permutation ≠
            markedFirst rank right hright permutation) ≤
        (((left \ right) ∪ (right \ left)).card : ℝ) / left.card :=
      sharedPermutation_disagreement_probability_le
        rank left right hleft hright
    _ = 2 * markedTotalVariation left right := by
      unfold markedTotalVariation
      have hcard : (left.card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr hleft)
      field_simp

section RationalMarks

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The rational marked construction used in the quantum parallel-repetition argument. -/
def rationalMarked (denominator : ℕ) (numerator : β → ℕ) :
    Finset (β × Fin denominator) := by
  classical
  exact Finset.univ.filter fun point =>
    point.2.val < numerator point.1

theorem rationalMarked_fiber_card
    (denominator : ℕ) (numerator : β → ℕ) (letter : β) :
    ((rationalMarked denominator numerator).filter
      fun point => point.1 = letter).card =
        min denominator (numerator letter) := by
  classical
  calc
    ((rationalMarked denominator numerator).filter
      fun point => point.1 = letter).card =
        (Finset.univ.filter fun copy : Fin denominator =>
          copy.val < numerator letter).card := by
      refine Finset.card_bij'
        (fun point _ => point.2)
        (fun copy _ => (letter, copy))
        ?_ ?_ ?_ ?_
      · intro point hpoint
        have hpoint' :
            point.2.val < numerator point.1 ∧ point.1 = letter := by
          simpa only [rationalMarked, mem_filter, mem_univ, true_and] using hpoint
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by simpa only [hpoint'.2] using hpoint'.1⟩
      · intro copy hcopy
        have hcopy' : copy.val < numerator letter :=
          (Finset.mem_filter.mp hcopy).2
        simp only [rationalMarked, mem_filter, mem_univ, hcopy', and_self]
      · intro point hpoint
        have hletter : point.1 = letter :=
          (Finset.mem_filter.mp hpoint).2
        apply Prod.ext
        · exact hletter.symm
        · rfl
      · intro copy _
        rfl
    _ = min denominator (numerator letter) := by
      simpa only using
        (Fin.card_filter_val_lt (n := denominator)
          (m := numerator letter))

omit [DecidableEq β] in
theorem rationalNumerator_le_denominator
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator)
    (letter : β) : numerator letter ≤ denominator := by
  rw [← normalized]
  exact Finset.single_le_sum
    (fun a _ => Nat.zero_le (numerator a)) (Finset.mem_univ letter)

omit [DecidableEq β] in
theorem rationalMarked_card
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator) :
    (rationalMarked denominator numerator).card = denominator := by
  classical
  calc
    (rationalMarked denominator numerator).card =
        ∑ letter : β,
          ((rationalMarked denominator numerator).filter
            fun point => point.1 = letter).card := by
      simpa only using
        (Finset.card_eq_sum_card_fiberwise
          (f := fun point : β × Fin denominator => point.1)
          (s := rationalMarked denominator numerator)
          (t := (Finset.univ : Finset β))
          (fun _ _ => Finset.mem_univ _))
    _ = ∑ letter : β, numerator letter := by
      apply Finset.sum_congr rfl
      intro letter _
      calc
        ((rationalMarked denominator numerator).filter
              fun point => point.1 = letter).card =
            min denominator (numerator letter) := by
          exact rationalMarked_fiber_card denominator numerator letter
        _ = numerator letter := min_eq_right
          (rationalNumerator_le_denominator denominator numerator normalized letter)
    _ = denominator := normalized

omit [DecidableEq β] in
theorem rationalMarked_nonempty
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator)
    (positive : 0 < denominator) :
    (rationalMarked denominator numerator).Nonempty := by
  apply Finset.card_pos.mp
  rw [rationalMarked_card denominator numerator normalized]
  exact positive

theorem rationalMarked_letter_probability
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (rank : (β × Fin denominator) ≃
      Fin (Fintype.card (β × Fin denominator)))
    (letter : β) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm (β × Fin denominator) =>
        (markedFirst rank (rationalMarked denominator numerator)
          nonempty permutation).1 = letter) =
      (numerator letter : ℝ) / denominator := by
  classical
  let marked := rationalMarked denominator numerator
  let event := marked.filter fun point => point.1 = letter
  have hsub : event ⊆ marked := Finset.filter_subset _ _
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (β × Fin denominator) =>
          (markedFirst rank marked nonempty permutation).1 = letter) =
        uniformPermutationProbability
          (fun permutation : Equiv.Perm (β × Fin denominator) =>
            markedFirst rank marked nonempty permutation ∈ event) := by
      congr 1
      funext permutation
      apply propext
      simp only [mem_filter, markedFirst_mem rank marked nonempty permutation, true_and, event]
    _ = (event.card : ℝ) / marked.card :=
      markedFirst_event_probability rank marked nonempty event hsub
    _ = (numerator letter : ℝ) / denominator := by
      change
        (((rationalMarked denominator numerator).filter
          fun point => point.1 = letter).card : ℝ) /
          (rationalMarked denominator numerator).card =
        (numerator letter : ℝ) / denominator
      rw [rationalMarked_fiber_card,
        min_eq_right
          (rationalNumerator_le_denominator
            denominator numerator normalized letter),
        rationalMarked_card denominator numerator normalized]

end RationalMarks

end ClassicalSampling

namespace Pinsker

theorem centered_log_lower_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  have hden : 0 < x + 1 := by linarith
  let t : ℝ := (x - 1) / (x + 1)
  have ht0 : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hx) hden.le
  have ht1 : t < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have hratio : (1 + t) / (1 - t) = x := by
    dsimp [t]
    field_simp
    ring
  have hseries :
      t ≤ (1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t)) := by
    simpa only [one_div, range_one, sum_singleton, mul_zero, zero_add, pow_one,
      CharP.cast_eq_zero, div_one] using (Real.sum_range_le_log_div ht0 ht1 1)
  rw [hratio] at hseries
  dsimp [t] at hseries
  calc
    2 * (x - 1) / (x + 1) = 2 * ((x - 1) / (x + 1)) := by ring
    _ ≤ Real.log x := by linarith

theorem centered_log_upper_of_le_one
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ 2 * (x - 1) / (x + 1) := by
  have hinv : 1 ≤ (1 : ℝ) / x := by
    apply (le_div_iff₀ hx0).mpr
    simpa only [one_mul] using hx1
  have h := centered_log_lower_of_one_le hinv
  have hratio :
      2 * ((1 : ℝ) / x - 1) / ((1 : ℝ) / x + 1) =
        -(2 * (x - 1) / (x + 1)) := by
    field_simp
    ring
  rw [hratio, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hx0.ne',
    Real.log_one] at h
  linarith

private def pinskerScalarGap (x : ℝ) : ℝ :=
  InformationTheory.klFun x - 3 * (x - 1) ^ 2 / (2 * (x + 2))

theorem hasDerivAt_pinskerScalarGap {x : ℝ} (hx : 0 < x) :
    HasDerivAt pinskerScalarGap
      (Real.log x - 3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2)) x := by
  have hden : 2 * (x + 2) ≠ 0 := by positivity
  have hnumerator :=
    (((hasDerivAt_id x).sub_const 1).pow 2).const_mul 3
  have hdenominator :=
    ((hasDerivAt_id x).add_const 2).const_mul 2
  have hquotient := hnumerator.div hdenominator hden
  have hgap := (InformationTheory.hasDerivAt_klFun hx.ne').sub hquotient
  have hfunction :
      (InformationTheory.klFun -
        (fun y => 3 * ((fun z => id z - 1) ^ 2) y) /
          (fun y => 2 * (id y + 2))) = pinskerScalarGap := by
    funext y
    change
      InformationTheory.klFun y - 3 * (y - 1) ^ 2 / (2 * (y + 2)) =
        InformationTheory.klFun y - 3 * (y - 1) ^ 2 / (2 * (y + 2))
    rfl
  rw [hfunction] at hgap
  apply hgap.congr_deriv
  dsimp
  field_simp
  ring

theorem pinsker_rational_coefficient_le {x : ℝ} (hx : 0 < x) :
    3 * (x + 5) / (2 * (x + 2) ^ 2) ≤ 2 / (x + 1) := by
  have hleft : 0 < 2 * (x + 2) ^ 2 := by positivity
  have hright : 0 < x + 1 := by linarith
  apply (div_le_div_iff₀ hleft hright).mpr
  linarith [sq_nonneg (x - 1)]

theorem pinskerScalarGap_derivative_nonneg
    {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ Real.log x -
      3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hcoefficient := pinsker_rational_coefficient_le hx0
  have hscaled := mul_le_mul_of_nonneg_left
    hcoefficient (sub_nonneg.mpr hx)
  have hrational :
      3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) ≤
        2 * (x - 1) / (x + 1) := by
    calc
      3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) =
          (x - 1) * (3 * (x + 5) / (2 * (x + 2) ^ 2)) := by ring
      _ ≤ (x - 1) * (2 / (x + 1)) := hscaled
      _ = 2 * (x - 1) / (x + 1) := by ring
  have hlog := centered_log_lower_of_one_le hx
  linarith

theorem pinskerScalarGap_derivative_nonpos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.log x -
      3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) ≤ 0 := by
  have hcoefficient := pinsker_rational_coefficient_le hx0
  have hscaled := mul_le_mul_of_nonpos_left
    hcoefficient (sub_nonpos.mpr hx1)
  have hrational :
      2 * (x - 1) / (x + 1) ≤
        3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) := by
    calc
      2 * (x - 1) / (x + 1) = (x - 1) * (2 / (x + 1)) := by ring
      _ ≤ (x - 1) * (3 * (x + 5) / (2 * (x + 2) ^ 2)) := hscaled
      _ = 3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) := by ring
  have hlog := centered_log_upper_of_le_one hx0 hx1
  linarith

theorem pinskerScalarGap_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ pinskerScalarGap x := by
  by_cases hzero : x = 0
  · subst x
    norm_num [pinskerScalarGap, InformationTheory.klFun]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
  by_cases hone : 1 ≤ x
  · let derivative : ℝ → ℝ := fun y =>
      Real.log y - 3 * (y - 1) * (y + 5) / (2 * (y + 2) ^ 2)
    have hcontinuous : ContinuousOn pinskerScalarGap (Set.Icc 1 x) := by
      intro y hy
      have hypos : 0 < y := by
        have hyone := (Set.mem_Icc.mp hy).1
        linarith
      exact (hasDerivAt_pinskerScalarGap hypos).continuousAt.continuousWithinAt
    have hmonotone : MonotoneOn pinskerScalarGap (Set.Icc 1 x) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg
        (f' := derivative) (convex_Icc 1 x) hcontinuous
      · intro y hy
        have hymem : y ∈ Set.Icc (1 : ℝ) x := interior_subset hy
        have hypos : 0 < y := by
          have hyone := (Set.mem_Icc.mp hymem).1
          linarith
        exact (hasDerivAt_pinskerScalarGap hypos).hasDerivWithinAt
      · intro y hy
        have hymem : y ∈ Set.Icc (1 : ℝ) x := interior_subset hy
        exact pinskerScalarGap_derivative_nonneg (Set.mem_Icc.mp hymem).1
    have hbound := hmonotone
      (show (1 : ℝ) ∈ Set.Icc 1 x from ⟨le_rfl, hone⟩)
      (show x ∈ Set.Icc (1 : ℝ) x from ⟨hone, le_rfl⟩) hone
    simpa only [pinskerScalarGap, InformationTheory.klFun, sub_nonneg, ge_iff_le, Real.log_one,
      mul_zero, zero_add, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div] using hbound
  · have hxone : x ≤ 1 := le_of_not_ge hone
    let derivative : ℝ → ℝ := fun y =>
      Real.log y - 3 * (y - 1) * (y + 5) / (2 * (y + 2) ^ 2)
    have hcontinuous : ContinuousOn pinskerScalarGap (Set.Icc x 1) := by
      intro y hy
      have hypos : 0 < y :=
        hxpos.trans_le (Set.mem_Icc.mp hy).1
      exact (hasDerivAt_pinskerScalarGap hypos).continuousAt.continuousWithinAt
    have hantitone : AntitoneOn pinskerScalarGap (Set.Icc x 1) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos
        (f' := derivative) (convex_Icc x 1) hcontinuous
      · intro y hy
        have hymem : y ∈ Set.Icc x (1 : ℝ) := interior_subset hy
        have hypos : 0 < y := hxpos.trans_le (Set.mem_Icc.mp hymem).1
        exact (hasDerivAt_pinskerScalarGap hypos).hasDerivWithinAt
      · intro y hy
        have hymem : y ∈ Set.Icc x (1 : ℝ) := interior_subset hy
        have hypos : 0 < y := hxpos.trans_le (Set.mem_Icc.mp hymem).1
        exact pinskerScalarGap_derivative_nonpos
          hypos (Set.mem_Icc.mp hymem).2
    have hbound := hantitone
      (show x ∈ Set.Icc x (1 : ℝ) from ⟨le_rfl, hxone⟩)
      (show (1 : ℝ) ∈ Set.Icc x 1 from ⟨hxone, le_rfl⟩) hxone
    simpa only [pinskerScalarGap, InformationTheory.klFun, sub_nonneg, ge_iff_le, Real.log_one,
      mul_zero, zero_add, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div] using hbound

theorem quadratic_le_klFun {x : ℝ} (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 / (2 * (x + 2)) ≤ InformationTheory.klFun x := by
  have h := pinskerScalarGap_nonneg hx
  dsimp [pinskerScalarGap] at h
  linarith

/-- The entropy quantity for finite relative. -/
def finiteRelativeEntropy {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  ∑ i, q i * InformationTheory.klFun (p i / q i)

/-- The finite total variation construction used in the quantum parallel-repetition argument. -/
def finiteTotalVariation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  (∑ i, |p i - q i|) / 2

theorem quadratic_density_le_weighted_kl
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    3 * (p - q) ^ 2 / (2 * (p + 2 * q)) ≤
      q * InformationTheory.klFun (p / q) := by
  have hscalar := quadratic_le_klFun (div_nonneg hp hq.le)
  have hweighted := mul_le_mul_of_nonneg_left hscalar hq.le
  calc
    3 * (p - q) ^ 2 / (2 * (p + 2 * q)) =
        q * (3 * (p / q - 1) ^ 2 / (2 * (p / q + 2))) := by
      field_simp [hq.ne']
    _ ≤ q * InformationTheory.klFun (p / q) := hweighted

theorem finiteRelativeEntropy_eq_log_sum
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hq : ∀ i, 0 < q i)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    finiteRelativeEntropy p q =
      ∑ i, p i * Real.log (p i / q i) := by
  unfold finiteRelativeEntropy
  calc
    (∑ i, q i * InformationTheory.klFun (p i / q i)) =
        ∑ i, (p i * Real.log (p i / q i) + q i - p i) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold InformationTheory.klFun
      field_simp [(hq i).ne']
    _ = ∑ i, p i * Real.log (p i / q i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        hp_normalized, hq_normalized]
      ring

theorem finite_pinsker
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 < q i)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    2 * (finiteTotalVariation p q) ^ 2 ≤ finiteRelativeEntropy p q := by
  classical
  let weight : ι → ℝ := fun i => (p i + 2 * q i) / 3
  have hweight : ∀ i, 0 < weight i := by
    intro i
    dsimp [weight]
    have hpi := hp i
    have hqi := hq i
    positivity
  have hweight_sum : (∑ i, weight i) = 1 := by
    dsimp [weight]
    calc
      (∑ i, (p i + 2 * q i) / 3) =
          ((∑ i, p i) + 2 * (∑ i, q i)) / 3 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 1 := by rw [hp_normalized, hq_normalized]; norm_num
  have hcauchy :
      (∑ i, |p i - q i|) ^ 2 ≤
        ∑ i, |p i - q i| ^ 2 / weight i := by
    have h := Finset.sq_sum_div_le_sum_sq_div
      (Finset.univ : Finset ι)
      (fun i => |p i - q i|)
      (g := weight)
      (fun i _ => hweight i)
    simpa only [sq_abs, ge_iff_le, hweight_sum, div_one] using h
  have hpoint : ∀ i,
      |p i - q i| ^ 2 / weight i ≤
        2 * (q i * InformationTheory.klFun (p i / q i)) := by
    intro i
    have hdensity := quadratic_density_le_weighted_kl (hp i) (hq i)
    calc
      |p i - q i| ^ 2 / weight i =
          2 * (3 * (p i - q i) ^ 2 /
            (2 * (p i + 2 * q i))) := by
        dsimp [weight]
        rw [sq_abs]
        have hden : p i + 2 * q i ≠ 0 := by
          have hpi := hp i
          have hqi := hq i
          positivity
        field_simp [hden]
      _ ≤ 2 * (q i * InformationTheory.klFun (p i / q i)) :=
        mul_le_mul_of_nonneg_left hdensity (by norm_num)
  have hsum :
      (∑ i, |p i - q i| ^ 2 / weight i) ≤
        2 * finiteRelativeEntropy p q := by
    calc
      (∑ i, |p i - q i| ^ 2 / weight i) ≤
          ∑ i, 2 * (q i * InformationTheory.klFun (p i / q i)) :=
        Finset.sum_le_sum fun i _ => hpoint i
      _ = 2 * finiteRelativeEntropy p q := by
        unfold finiteRelativeEntropy
        rw [Finset.mul_sum]
  have hmain :
      (∑ i, |p i - q i|) ^ 2 ≤ 2 * finiteRelativeEntropy p q :=
    hcauchy.trans hsum
  unfold finiteTotalVariation
  linarith

theorem sum_over_positive_reference_support
    {ι : Type*} [Fintype ι]
    (q f : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i)
    (hzero : ∀ i, q i = 0 → f i = 0) :
    (∑ i : {i : ι // 0 < q i}, f i) = ∑ i, f i := by
  classical
  calc
    (∑ i : {i : ι // 0 < q i}, f i) =
        ∑ i ∈ (Finset.univ.filter fun i : ι => 0 < q i), f i := by
      simpa only [subtype_univ] using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset ι))
          (p := fun i : ι => 0 < q i) f)
    _ = ∑ i, f i := by
      apply Finset.sum_filter_of_ne
      intro i _ hfi
      have hqi : q i ≠ 0 := by
        intro hqi
        exact hfi (hzero i hqi)
      exact lt_of_le_of_ne (hq i) hqi.symm

theorem finite_pinsker_of_absolute_continuity
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    2 * (finiteTotalVariation p q) ^ 2 ≤ finiteRelativeEntropy p q := by
  classical
  let p' : {i : ι // 0 < q i} → ℝ := fun i => p i
  let q' : {i : ι // 0 < q i} → ℝ := fun i => q i
  have hp'_nonnegative : ∀ i, 0 ≤ p' i := fun i => hp i
  have hq'_positive : ∀ i, 0 < q' i := fun i => i.property
  have hp'_normalized : (∑ i, p' i) = 1 := by
    change (∑ i : {i : ι // 0 < q i}, p i) = 1
    rw [sum_over_positive_reference_support q p hq absolute_continuity,
      hp_normalized]
  have hq'_normalized : (∑ i, q' i) = 1 := by
    change (∑ i : {i : ι // 0 < q i}, q i) = 1
    rw [sum_over_positive_reference_support q q hq (fun _ h => h),
      hq_normalized]
  have htv : finiteTotalVariation p' q' = finiteTotalVariation p q := by
    unfold finiteTotalVariation
    change
      (∑ i : {i : ι // 0 < q i}, |p i - q i|) / 2 =
        (∑ i, |p i - q i|) / 2
    rw [sum_over_positive_reference_support
      q (fun i => |p i - q i|) hq]
    intro i hqi
    simp only [absolute_continuity i hqi, hqi, sub_self, abs_zero]
  have hkl : finiteRelativeEntropy p' q' = finiteRelativeEntropy p q := by
    unfold finiteRelativeEntropy
    change
      (∑ i : {i : ι // 0 < q i},
        q i * InformationTheory.klFun (p i / q i)) =
      ∑ i, q i * InformationTheory.klFun (p i / q i)
    apply sum_over_positive_reference_support
      q (fun i => q i * InformationTheory.klFun (p i / q i)) hq
    intro i hqi
    simp only [hqi, div_zero, zero_mul]
  have h := finite_pinsker p' q'
    hp'_nonnegative hq'_positive hp'_normalized hq'_normalized
  rwa [htv, hkl] at h

theorem finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    finiteRelativeEntropy p q =
      ∑ i, p i * Real.log (p i / q i) := by
  unfold finiteRelativeEntropy
  calc
    (∑ i, q i * InformationTheory.klFun (p i / q i)) =
        ∑ i, (p i * Real.log (p i / q i) + q i - p i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hqi : q i = 0
      · simp only [hqi, absolute_continuity i hqi, div_zero, zero_mul, Real.log_zero, mul_zero,
          add_zero, sub_self]
      · unfold InformationTheory.klFun
        have hqpos : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hqi)
        field_simp [hqpos.ne']
    _ = ∑ i, p i * Real.log (p i / q i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        hp_normalized, hq_normalized]
      ring

theorem finite_pinsker_sqrt_of_absolute_continuity
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    finiteTotalVariation p q ≤
      Real.sqrt (finiteRelativeEntropy p q / 2) := by
  apply Real.le_sqrt_of_sq_le
  have h := finite_pinsker_of_absolute_continuity
    p q hp hq absolute_continuity hp_normalized hq_normalized
  linarith

end Pinsker

namespace ClassicalInformation

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
The distribution floor numerator construction used in the quantum parallel-repetition argument.
-/
def distributionFloorNumerator (denominator : ℕ) (p : ι → ℝ) : ι → ℕ :=
  fun i => Nat.floor (p i * (denominator : ℝ))

/--
The distribution floor residual construction used in the quantum parallel-repetition argument.
-/
def distributionFloorResidual (denominator : ℕ) (p : ι → ℝ) : ℕ :=
  denominator - ∑ i, distributionFloorNumerator denominator p i

/--
The distribution rounded numerator construction used in the quantum parallel-repetition
argument.
-/
def distributionRoundedNumerator
    (base : ι) (denominator : ℕ) (p : ι → ℝ) : ι → ℕ :=
  fun i => distributionFloorNumerator denominator p i +
    if i = base then distributionFloorResidual denominator p else 0

private def distributionFloorProbability
    (denominator : ℕ) (p : ι → ℝ) : ι → ℝ :=
  fun i => (distributionFloorNumerator denominator p i : ℝ) / denominator

/-- The probability of distribution rounded. -/
def distributionRoundedProbability
    (base : ι) (denominator : ℕ) (p : ι → ℝ) : ι → ℝ :=
  fun i =>
    (distributionRoundedNumerator base denominator p i : ℝ) / denominator

omit [Fintype ι] [DecidableEq ι] in
theorem distributionFloorNumerator_cast_le
    (denominator : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (i : ι) :
    (distributionFloorNumerator denominator p i : ℝ) ≤
      p i * denominator := by
  unfold distributionFloorNumerator
  exact Nat.floor_le (mul_nonneg (hp i) (Nat.cast_nonneg _))

omit [Fintype ι] [DecidableEq ι] in
theorem distributionFloorProbability_le
    (denominator : ℕ) (positive : 0 < denominator)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (i : ι) :
    distributionFloorProbability denominator p i ≤ p i := by
  have hden : 0 < (denominator : ℝ) := by exact_mod_cast positive
  unfold distributionFloorProbability
  apply (div_le_iff₀ hden).mpr
  exact distributionFloorNumerator_cast_le denominator p hp i

omit [Fintype ι] [DecidableEq ι] in
theorem distributionFloorProbability_error_lt
    (denominator : ℕ) (positive : 0 < denominator)
    (p : ι → ℝ) (i : ι) :
    p i - distributionFloorProbability denominator p i <
      (1 : ℝ) / denominator := by
  have hden : 0 < (denominator : ℝ) := by exact_mod_cast positive
  apply (lt_div_iff₀ hden).mpr
  have hupper := Nat.lt_floor_add_one (p i * (denominator : ℝ))
  unfold distributionFloorProbability distributionFloorNumerator
  calc
    (p i - (Nat.floor (p i * (denominator : ℝ)) : ℝ) /
        (denominator : ℝ)) * (denominator : ℝ) =
      p i * (denominator : ℝ) - Nat.floor (p i * (denominator : ℝ)) := by
        field_simp
    _ < 1 := by linarith

omit [DecidableEq ι] in
theorem distributionFloorNumerator_sum_le
    (denominator : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (normalized : (∑ i, p i) = 1) :
    (∑ i, distributionFloorNumerator denominator p i) ≤ denominator := by
  have hreal :
      ((∑ i, distributionFloorNumerator denominator p i) : ℝ) ≤
        (denominator : ℝ) := by
    calc
      ((∑ i, distributionFloorNumerator denominator p i) : ℝ) =
          ∑ i, (distributionFloorNumerator denominator p i : ℝ) := by
        simp only
      _ ≤ ∑ i, p i * (denominator : ℝ) :=
        Finset.sum_le_sum fun i _ =>
          distributionFloorNumerator_cast_le denominator p hp i
      _ = (denominator : ℝ) := by
        rw [← Finset.sum_mul, normalized]
        simp only [one_mul]
  exact_mod_cast hreal

theorem distributionRoundedNumerator_sum
    (base : ι) (denominator : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (normalized : (∑ i, p i) = 1) :
    (∑ i, distributionRoundedNumerator base denominator p i) =
      denominator := by
  have hfloor := distributionFloorNumerator_sum_le
    denominator p hp normalized
  unfold distributionRoundedNumerator
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  unfold distributionFloorResidual
  omega

omit [DecidableEq ι] in
theorem distributionFloorResidual_probability_eq_sum
    (denominator : ℕ) (positive : 0 < denominator)
    (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (normalized : (∑ i, p i) = 1) :
    (distributionFloorResidual denominator p : ℝ) / denominator =
      ∑ i, (p i - distributionFloorProbability denominator p i) := by
  have hfloor := distributionFloorNumerator_sum_le
    denominator p hp normalized
  have hden : (denominator : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  unfold distributionFloorResidual distributionFloorProbability
  rw [Nat.cast_sub hfloor, Nat.cast_sum, Finset.sum_sub_distrib,
    normalized, ← Finset.sum_div]
  field_simp

theorem distributionRoundedProbability_eq_floor_add
    (base : ι) (denominator : ℕ) (p : ι → ℝ) (i : ι) :
    distributionRoundedProbability base denominator p i =
      distributionFloorProbability denominator p i +
        if i = base then
          (distributionFloorResidual denominator p : ℝ) / denominator
        else 0 := by
  by_cases hbase : i = base
  · simp only [distributionRoundedProbability, distributionRoundedNumerator, hbase, ↓reduceIte,
      Nat.cast_add, distributionFloorProbability]
    ring
  · simp only [distributionRoundedProbability, distributionRoundedNumerator, hbase, ↓reduceIte,
      add_zero, distributionFloorProbability]

theorem distributionRoundedProbability_totalVariation_le
    (base : ι) (denominator : ℕ) (positive : 0 < denominator)
    (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (normalized : (∑ i, p i) = 1) :
    finiteTotalVariation p
        (distributionRoundedProbability base denominator p) ≤
      (Fintype.card ι : ℝ) / denominator := by
  have hden : 0 < (denominator : ℝ) := by exact_mod_cast positive
  have hres :
      0 ≤ (distributionFloorResidual denominator p : ℝ) / denominator :=
    div_nonneg (Nat.cast_nonneg _) hden.le
  have hpoint : ∀ i,
      |p i - distributionRoundedProbability base denominator p i| ≤
        (p i - distributionFloorProbability denominator p i) +
          if i = base then
            (distributionFloorResidual denominator p : ℝ) / denominator
          else 0 := by
    intro i
    have hdefect :
        0 ≤ p i - distributionFloorProbability denominator p i :=
      sub_nonneg.mpr
        (distributionFloorProbability_le denominator positive p hp i)
    have htriangle := abs_sub_le (p i)
      (distributionFloorProbability denominator p i)
      (distributionRoundedProbability base denominator p i)
    rw [abs_of_nonneg hdefect] at htriangle
    have hcorrection :
        |distributionFloorProbability denominator p i -
            distributionRoundedProbability base denominator p i| =
          if i = base then
            (distributionFloorResidual denominator p : ℝ) / denominator
          else 0 := by
      rw [distributionRoundedProbability_eq_floor_add]
      by_cases hbase : i = base
      · simp only [hbase, ↓reduceIte, sub_add_cancel_left, abs_neg, abs_of_nonneg hres]
      · simp only [hbase, ↓reduceIte, add_zero, sub_self, abs_zero]
    rw [hcorrection] at htriangle
    exact htriangle
  have htv_defect :
      finiteTotalVariation p
          (distributionRoundedProbability base denominator p) ≤
        ∑ i, (p i - distributionFloorProbability denominator p i) := by
    calc
      finiteTotalVariation p
          (distributionRoundedProbability base denominator p) =
        (∑ i, |p i - distributionRoundedProbability
          base denominator p i|) / 2 := rfl
      _ ≤ (∑ i,
          ((p i - distributionFloorProbability denominator p i) +
            if i = base then
              (distributionFloorResidual denominator p : ℝ) / denominator
            else 0)) / 2 := by
        apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
        exact Finset.sum_le_sum fun i _ => hpoint i
      _ = ∑ i, (p i - distributionFloorProbability denominator p i) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rw [distributionFloorResidual_probability_eq_sum
          denominator positive p hp normalized]
        ring
  calc
    finiteTotalVariation p
        (distributionRoundedProbability base denominator p) ≤
      ∑ i, (p i - distributionFloorProbability denominator p i) :=
        htv_defect
    _ ≤ ∑ _i : ι, (1 : ℝ) / denominator :=
      Finset.sum_le_sum fun i _ =>
        (distributionFloorProbability_error_lt denominator positive p i).le
    _ = (Fintype.card ι : ℝ) / denominator := by
      simp only [div_eq_mul_inv, one_mul, sum_const, card_univ, nsmul_eq_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem finite_log_sum_inequality
    (indices : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0)
    (positive_mass : 0 < ∑ i ∈ indices, q i) :
    (∑ i ∈ indices, q i) *
        InformationTheory.klFun
          ((∑ i ∈ indices, p i) / (∑ i ∈ indices, q i)) ≤
      ∑ i ∈ indices,
        q i * InformationTheory.klFun (p i / q i) := by
  let total : ℝ := ∑ i ∈ indices, q i
  have htotal : 0 < total := positive_mass
  have hnormalized :
      (∑ i ∈ indices, q i / total) = 1 := by
    rw [← Finset.sum_div]
    exact div_self htotal.ne'
  have hmean :
      (∑ i ∈ indices, (q i / total) * (p i / q i)) =
        (∑ i ∈ indices, p i) / total := by
    calc
      (∑ i ∈ indices, (q i / total) * (p i / q i)) =
          ∑ i ∈ indices, p i / total := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hqi : q i = 0
        · simp only [hqi, zero_div, absolute_continuity i hqi, div_zero, mul_zero]
        · field_simp [hqi, htotal.ne']
      _ = (∑ i ∈ indices, p i) / total := by
        rw [Finset.sum_div]
  have hjensen :
      InformationTheory.klFun ((∑ i ∈ indices, p i) / total) ≤
        ∑ i ∈ indices,
          (q i / total) * InformationTheory.klFun (p i / q i) := by
    have h := InformationTheory.convexOn_klFun.map_sum_le
      (t := indices)
      (w := fun i => q i / total)
      (p := fun i => p i / q i)
      (fun i _ => div_nonneg (hq i) htotal.le)
      hnormalized
      (fun i _ => show p i / q i ∈ Set.Ici (0 : ℝ) from
        div_nonneg (hp i) (hq i))
    simpa only [smul_eq_mul, hmean] using h
  change
    total * InformationTheory.klFun
      ((∑ i ∈ indices, p i) / total) ≤
      ∑ i ∈ indices, q i * InformationTheory.klFun (p i / q i)
  calc
    total * InformationTheory.klFun
        ((∑ i ∈ indices, p i) / total) ≤
      total * (∑ i ∈ indices,
        (q i / total) * InformationTheory.klFun (p i / q i)) :=
      mul_le_mul_of_nonneg_left hjensen htotal.le
    _ = ∑ i ∈ indices,
        q i * InformationTheory.klFun (p i / q i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [htotal.ne']

section CoarseGraining

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The total probability mass of grouped. -/
def groupedMass (map : ι → κ) (p : ι → ℝ) (j : κ) : ℝ :=
  ∑ i ∈ (Finset.univ.filter fun i => map i = j), p i

omit [DecidableEq ι] [Fintype κ] in
/-- Express a grouped mass as an indicator-weighted sum over its source. -/
theorem groupedMass_eq_sum_ite (map : ι → κ) (p : ι → ℝ) (j : κ) :
    groupedMass map p j = ∑ i, if map i = j then p i else 0 := by
  classical
  rw [groupedMass, Finset.sum_filter]

omit [DecidableEq ι] in
theorem finite_relative_entropy_data_processing
    (map : ι → κ) (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0) :
    finiteRelativeEntropy (groupedMass map p) (groupedMass map q) ≤
      finiteRelativeEntropy p q := by
  change
    (∑ j : κ, groupedMass map q j *
      InformationTheory.klFun
        (groupedMass map p j / groupedMass map q j)) ≤
      ∑ i : ι, q i * InformationTheory.klFun (p i / q i)
  calc
    (∑ j : κ, groupedMass map q j *
        InformationTheory.klFun
          (groupedMass map p j / groupedMass map q j)) ≤
      ∑ j : κ,
        ∑ i ∈ (Finset.univ.filter fun i => map i = j),
          q i * InformationTheory.klFun (p i / q i) := by
        apply Finset.sum_le_sum
        intro j _
        let indices : Finset ι :=
          Finset.univ.filter fun i => map i = j
        change
          (∑ i ∈ indices, q i) *
              InformationTheory.klFun
                ((∑ i ∈ indices, p i) / (∑ i ∈ indices, q i)) ≤
            ∑ i ∈ indices,
              q i * InformationTheory.klFun (p i / q i)
        have hreference : 0 ≤ ∑ i ∈ indices, q i :=
          Finset.sum_nonneg (fun i _ => hq i)
        by_cases hzero : (∑ i ∈ indices, q i) = 0
        · rw [hzero, zero_mul]
          apply Finset.sum_nonneg
          intro i _
          exact mul_nonneg (hq i)
            (InformationTheory.klFun_nonneg
              (div_nonneg (hp i) (hq i)))
        · exact finite_log_sum_inequality indices p q hp hq
            absolute_continuity (lt_of_le_of_ne hreference (Ne.symm hzero))
    _ = ∑ i : ι,
        q i * InformationTheory.klFun (p i / q i) := by
      simpa only [] using
        (Finset.sum_fiberwise (Finset.univ : Finset ι) map
          (fun i => q i * InformationTheory.klFun (p i / q i)))

end CoarseGraining

section JointChainRule

variable {κ : Type*} [Fintype κ]

/-- The marginal distribution of joint first. -/
def jointFirstMarginal (joint : ι × κ → ℝ) : ι → ℝ :=
  fun i => ∑ j : κ, joint (i, j)

/-- The joint conditional construction used in the quantum parallel-repetition argument. -/
def jointConditional (joint : ι × κ → ℝ) (i : ι) : κ → ℝ :=
  fun j => joint (i, j) / jointFirstMarginal joint i

omit [Fintype ι] [DecidableEq ι] in
theorem jointFirstMarginal_nonneg
    (joint : ι × κ → ℝ)
    (nonnegative : ∀ point, 0 ≤ joint point) (i : ι) :
    0 ≤ jointFirstMarginal joint i := by
  exact Finset.sum_nonneg (fun j _ => nonnegative (i, j))

omit [DecidableEq ι] in
theorem jointFirstMarginal_sum (joint : ι × κ → ℝ) :
    (∑ i : ι, jointFirstMarginal joint i) =
      ∑ point : ι × κ, joint point := by
  exact (Fintype.sum_prod_type joint).symm

omit [Fintype ι] [DecidableEq ι] in
theorem jointFirstMarginal_absolute_continuity
    (p q : ι × κ → ℝ)
    (hq : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (i : ι) :
    jointFirstMarginal q i = 0 → jointFirstMarginal p i = 0 := by
  intro hzero
  change (∑ j : κ, q (i, j)) = 0 at hzero
  have hcoordinates : ∀ j : κ, q (i, j) = 0 := by
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hq (i, j))).mp hzero j (Finset.mem_univ j)
  change (∑ j : κ, p (i, j)) = 0
  exact Finset.sum_eq_zero
    (fun j _ => absolute_continuity (i, j) (hcoordinates j))

omit [Fintype ι] [DecidableEq ι] in
theorem jointConditional_sum
    (joint : ι × κ → ℝ) (i : ι)
    (nonzero : jointFirstMarginal joint i ≠ 0) :
    (∑ j : κ, jointConditional joint i j) = 1 := by
  unfold jointConditional
  rw [← Finset.sum_div]
  exact div_self nonzero

omit [DecidableEq ι] in
theorem finite_relative_entropy_joint_chain_rule
    (p q : ι × κ → ℝ)
    (hp : ∀ point, 0 ≤ p point)
    (hq : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (hp_normalized : (∑ point, p point) = 1)
    (hq_normalized : (∑ point, q point) = 1) :
    finiteRelativeEntropy p q =
      finiteRelativeEntropy (jointFirstMarginal p)
        (jointFirstMarginal q) +
      ∑ i : ι, jointFirstMarginal p i *
        finiteRelativeEntropy (jointConditional p i)
          (jointConditional q i) := by
  have hp_marginal : (∑ i : ι, jointFirstMarginal p i) = 1 :=
    (jointFirstMarginal_sum p).trans hp_normalized
  have hq_marginal : (∑ i : ι, jointFirstMarginal q i) = 1 :=
    (jointFirstMarginal_sum q).trans hq_normalized
  have h_marginal_absolute :
      ∀ i : ι, jointFirstMarginal q i = 0 →
        jointFirstMarginal p i = 0 :=
    jointFirstMarginal_absolute_continuity p q hq absolute_continuity
  have h_joint_log :
      finiteRelativeEntropy p q =
        ∑ point : ι × κ,
          p point * Real.log (p point / q point) :=
    finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
      p q hq absolute_continuity hp_normalized hq_normalized
  have h_marginal_log :
      finiteRelativeEntropy (jointFirstMarginal p)
        (jointFirstMarginal q) =
        ∑ i : ι, jointFirstMarginal p i *
          Real.log (jointFirstMarginal p i /
            jointFirstMarginal q i) :=
    finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
      (jointFirstMarginal p) (jointFirstMarginal q)
      (jointFirstMarginal_nonneg q hq)
      h_marginal_absolute hp_marginal hq_marginal
  calc
    finiteRelativeEntropy p q =
      ∑ point : ι × κ,
        p point * Real.log (p point / q point) := h_joint_log
    _ = ∑ i : ι, ∑ j : κ,
        p (i, j) * Real.log (p (i, j) / q (i, j)) :=
          Fintype.sum_prod_type _
    _ = ∑ i : ι,
        (jointFirstMarginal p i *
          Real.log (jointFirstMarginal p i /
            jointFirstMarginal q i) +
          jointFirstMarginal p i *
            finiteRelativeEntropy (jointConditional p i)
              (jointConditional q i)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hpzero : jointFirstMarginal p i = 0
      · have hcoordinates : ∀ j : κ, p (i, j) = 0 := by
          intro j
          apply (Finset.sum_eq_zero_iff_of_nonneg
            (fun j _ => hp (i, j))).mp
              (show (∑ j : κ, p (i, j)) = 0 from hpzero)
              j (Finset.mem_univ j)
        simp only [hcoordinates, zero_div, Real.log_zero, mul_zero, sum_const_zero, hpzero,
          zero_mul, add_zero]
      · have hqzero : jointFirstMarginal q i ≠ 0 := by
          intro hzero
          exact hpzero (h_marginal_absolute i hzero)
        have hconditional_absolute :
            ∀ j : κ, jointConditional q i j = 0 →
              jointConditional p i j = 0 := by
          intro j hzero
          change q (i, j) / jointFirstMarginal q i = 0 at hzero
          have hpoint : q (i, j) = 0 := by
            rcases (div_eq_zero_iff.mp hzero) with hpoint | hmarginal
            · exact hpoint
            · exact (hqzero hmarginal).elim
          simp only [jointConditional, absolute_continuity (i, j) hpoint, zero_div]
        have hconditional_log :
            finiteRelativeEntropy (jointConditional p i)
              (jointConditional q i) =
              ∑ j : κ,
                jointConditional p i j *
                  Real.log (jointConditional p i j /
                    jointConditional q i j) := by
          apply finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
          · intro j
            exact div_nonneg (hq (i, j))
              (jointFirstMarginal_nonneg q hq i)
          · exact hconditional_absolute
          · exact jointConditional_sum p i hpzero
          · exact jointConditional_sum q i hqzero
        rw [hconditional_log]
        calc
          (∑ j : κ,
            p (i, j) * Real.log (p (i, j) / q (i, j))) =
            ∑ j : κ,
              (p (i, j) *
                Real.log (jointFirstMarginal p i /
                  jointFirstMarginal q i) +
                jointFirstMarginal p i *
                  (jointConditional p i j *
                    Real.log (jointConditional p i j /
                      jointConditional q i j))) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hpj : p (i, j) = 0
              · simp only [hpj, zero_div, Real.log_zero, mul_zero, zero_mul, jointConditional,
                  add_zero]
              · have hqj : q (i, j) ≠ 0 := by
                  intro hzero
                  exact hpj (absolute_continuity (i, j) hzero)
                have hfactorization :
                    p (i, j) / q (i, j) =
                      (jointFirstMarginal p i /
                        jointFirstMarginal q i) *
                        (jointConditional p i j /
                          jointConditional q i j) := by
                  unfold jointConditional
                  field_simp [hpzero, hqzero, hqj]
                have hfirst :
                    jointFirstMarginal p i /
                      jointFirstMarginal q i ≠ 0 :=
                  div_ne_zero hpzero hqzero
                have hsecond :
                    jointConditional p i j /
                      jointConditional q i j ≠ 0 := by
                  unfold jointConditional
                  exact div_ne_zero
                    (div_ne_zero hpj hpzero)
                    (div_ne_zero hqj hqzero)
                rw [hfactorization, Real.log_mul hfirst hsecond]
                unfold jointConditional
                field_simp [hpzero]
          _ = jointFirstMarginal p i *
              Real.log (jointFirstMarginal p i /
                jointFirstMarginal q i) +
              jointFirstMarginal p i *
                (∑ j : κ,
                  jointConditional p i j *
                    Real.log (jointConditional p i j /
                      jointConditional q i j)) := by
                rw [Finset.sum_add_distrib, ← Finset.sum_mul,
                  ← Finset.mul_sum]
                rfl
    _ = (∑ i : ι,
          jointFirstMarginal p i *
            Real.log (jointFirstMarginal p i /
              jointFirstMarginal q i)) +
        ∑ i : ι, jointFirstMarginal p i *
          finiteRelativeEntropy (jointConditional p i)
            (jointConditional q i) := by
      rw [Finset.sum_add_distrib]
    _ = finiteRelativeEntropy (jointFirstMarginal p)
          (jointFirstMarginal q) +
        ∑ i : ι, jointFirstMarginal p i *
          finiteRelativeEntropy (jointConditional p i)
            (jointConditional q i) := by
      rw [h_marginal_log]

end JointChainRule

section SharedPermutationSampling

/--
The rational permutation output construction used in the quantum parallel-repetition argument.
-/
def rationalPermutationOutput
    (denominator : ℕ) (numerator : ι → ℕ)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (permutation : Equiv.Perm (ι × Fin denominator)) : ι :=
  (markedFirst (Fintype.equivFin (ι × Fin denominator))
    (rationalMarked denominator numerator) nonempty permutation).1

theorem rationalPermutationOutput_probability
    (denominator : ℕ) (numerator : ι → ℕ)
    (normalized : (∑ i, numerator i) = denominator)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (letter : ι) :
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator numerator
            nonempty permutation = letter) =
      (numerator letter : ℝ) / denominator := by
  exact rationalMarked_letter_probability denominator numerator normalized
    nonempty (Fintype.equivFin (ι × Fin denominator)) letter

theorem rationalMarked_inter
    (denominator : ℕ) (left right : ι → ℕ) :
    rationalMarked denominator left ∩ rationalMarked denominator right =
      rationalMarked denominator (fun i => min (left i) (right i)) := by
  ext point
  simp only [rationalMarked, mem_inter, mem_filter, mem_univ, true_and, lt_inf_iff]

theorem rationalMarked_inter_card
    (denominator : ℕ) (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (_hright : (∑ i, right i) = denominator) :
    (rationalMarked denominator left ∩
      rationalMarked denominator right).card =
        ∑ i : ι, min (left i) (right i) := by
  rw [rationalMarked_inter]
  calc
    (rationalMarked denominator
        (fun i => min (left i) (right i))).card =
      ∑ i : ι,
        ((rationalMarked denominator
          (fun i => min (left i) (right i))).filter
            fun point => point.1 = i).card := by
      simpa only using
        (Finset.card_eq_sum_card_fiberwise
          (f := fun point : ι × Fin denominator => point.1)
          (s := rationalMarked denominator
            (fun i => min (left i) (right i)))
          (t := (Finset.univ : Finset ι))
          (fun _ _ => Finset.mem_univ _))
    _ = ∑ i : ι, min (left i) (right i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rationalMarked_fiber_card, min_eq_right]
      exact (min_le_left (left i) (right i)).trans
        (rationalNumerator_le_denominator
          denominator left hleft i)

theorem rationalMarked_markedTotalVariation_eq
    (denominator : ℕ) (positive : 0 < denominator)
    (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (hright : (∑ i, right i) = denominator) :
    markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) =
      finiteTotalVariation
        (fun i => (left i : ℝ) / denominator)
        (fun i => (right i : ℝ) / denominator) := by
  let L := rationalMarked denominator left
  let R := rationalMarked denominator right
  have hL : L.card = denominator :=
    rationalMarked_card denominator left hleft
  have hR : R.card = denominator :=
    rationalMarked_card denominator right hright
  have hI :
      ((L ∩ R).card : ℝ) =
        ∑ i : ι, (min (left i) (right i) : ℝ) := by
    change
      (((rationalMarked denominator left ∩
        rationalMarked denominator right).card : ℕ) : ℝ) =
        ∑ i : ι, (min (left i) (right i) : ℝ)
    rw [rationalMarked_inter_card denominator left right hleft hright,
      Nat.cast_sum]
    simp only [Nat.cast_min]
  have hdisjoint : Disjoint (L \ R) (R \ L) := by
    apply Finset.disjoint_left.mpr
    intro point hpoint_left hpoint_right
    exact (Finset.mem_sdiff.mp hpoint_left).2
      (Finset.mem_sdiff.mp hpoint_right).1
  have hunion :
      (((L \ R) ∪ (R \ L)).card : ℝ) =
        ((L \ R).card : ℝ) + ((R \ L).card : ℝ) := by
    exact_mod_cast (Finset.card_union_of_disjoint hdisjoint)
  have hleft_difference :
      ((L \ R).card : ℝ) + ((L ∩ R).card : ℝ) =
        (L.card : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_inter L R)
  have hright_difference :
      ((R \ L).card : ℝ) + ((L ∩ R).card : ℝ) =
        (R.card : ℝ) := by
    have h := Finset.card_sdiff_add_card_inter R L
    rw [Finset.inter_comm R L] at h
    exact_mod_cast h
  have hsymmetric :
      (((L \ R) ∪ (R \ L)).card : ℝ) =
        (denominator : ℝ) + denominator -
          2 * ∑ i : ι, (min (left i) (right i) : ℝ) := by
    have hLreal : (L.card : ℝ) = denominator := by exact_mod_cast hL
    have hRreal : (R.card : ℝ) = denominator := by exact_mod_cast hR
    linarith
  have hpointwise : ∀ i : ι,
      |(left i : ℝ) / denominator -
        (right i : ℝ) / denominator| =
        ((left i : ℝ) + right i -
          2 * (min (left i) (right i) : ℝ)) / denominator := by
    intro i
    rw [← sub_div, abs_div]
    have hdenominator_abs : |(denominator : ℝ)| = denominator :=
      abs_of_nonneg (Nat.cast_nonneg denominator)
    rw [hdenominator_abs]
    by_cases horder : left i ≤ right i
    · have hreal : (left i : ℝ) ≤ right i := by
        exact_mod_cast horder
      rw [min_eq_left hreal, abs_of_nonpos (sub_nonpos.mpr hreal)]
      ring
    · have horder' : right i ≤ left i :=
        (Nat.le_of_lt (Nat.lt_of_not_ge horder))
      have hreal : (right i : ℝ) ≤ left i := by
        exact_mod_cast horder'
      rw [min_eq_right hreal, abs_of_nonneg (sub_nonneg.mpr hreal)]
      ring
  have hleft_real : (∑ i : ι, (left i : ℝ)) = denominator := by
    exact_mod_cast hleft
  have hright_real : (∑ i : ι, (right i : ℝ)) = denominator := by
    exact_mod_cast hright
  have hdenominator : (denominator : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  change
    (((L \ R) ∪ (R \ L)).card : ℝ) /
        (2 * (L.card : ℝ)) =
      (∑ i : ι,
        |(left i : ℝ) / denominator -
          (right i : ℝ) / denominator|) / 2
  rw [hsymmetric, hL]
  simp_rw [hpointwise]
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum,
    hleft_real, hright_real]
  field_simp [hdenominator]

theorem uniformPermutationProbability_mono
    {α : Type*} [Fintype α] [DecidableEq α]
    (small large : Equiv.Perm α → Prop)
    (hinclusion : ∀ permutation, small permutation → large permutation) :
    uniformPermutationProbability small ≤
      uniformPermutationProbability large := by
  classical
  unfold uniformPermutationProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (show
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        small permutation) ⊆
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        large permutation) from by
        intro permutation hpermutation
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hinclusion permutation
            (Finset.mem_filter.mp hpermutation).2⟩)
  · exact_mod_cast (Nat.zero_le (Fintype.card (Equiv.Perm α)))

theorem rationalPermutationOutput_disagreement_le_two_mul_tv
    (denominator : ℕ) (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (hright : (∑ i, right i) = denominator)
    (nonempty_left : (rationalMarked denominator left).Nonempty)
    (nonempty_right : (rationalMarked denominator right).Nonempty) :
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      2 * markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) := by
  let rank := Fintype.equivFin (ι × Fin denominator)
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          markedFirst rank (rationalMarked denominator left)
            nonempty_left permutation ≠
          markedFirst rank (rationalMarked denominator right)
            nonempty_right permutation) := by
        apply uniformPermutationProbability_mono
        intro permutation hdifferent hequal
        apply hdifferent
        exact congrArg Prod.fst hequal
    _ ≤ 2 * markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) := by
      apply sharedPermutation_disagreement_probability_le_two_mul_tv
      calc
        (rationalMarked denominator left).card = denominator :=
          rationalMarked_card denominator left hleft
        _ = (rationalMarked denominator right).card :=
          (rationalMarked_card denominator right hright).symm

theorem rationalPermutationOutput_disagreement_le_two_mul_finiteTotalVariation
    (denominator : ℕ) (positive : 0 < denominator)
    (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (hright : (∑ i, right i) = denominator)
    (nonempty_left : (rationalMarked denominator left).Nonempty)
    (nonempty_right : (rationalMarked denominator right).Nonempty) :
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      2 * finiteTotalVariation
        (fun i => (left i : ℝ) / denominator)
        (fun i => (right i : ℝ) / denominator) := by
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      2 * markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) :=
          rationalPermutationOutput_disagreement_le_two_mul_tv
            denominator left right hleft hright
            nonempty_left nonempty_right
    _ = 2 * finiteTotalVariation
        (fun i => (left i : ℝ) / denominator)
        (fun i => (right i : ℝ) / denominator) := by
      rw [rationalMarked_markedTotalVariation_eq
        denominator positive left right hleft hright]

end SharedPermutationSampling

end ClassicalInformation

end

section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder


private def dSVUniformLeftDensityConjugateSwapVector
    {d : ℕ} (z : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 (fun ij : Fin d × Fin d => star (z (ij.2, ij.1)))

theorem dSVUniformLeftDensityConjugateSwapVector_norm
    {d : ℕ} (z : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖dSVUniformLeftDensityConjugateSwapVector z‖ = ‖z‖ := by
  have squares :
      ‖dSVUniformLeftDensityConjugateSwapVector z‖ ^ 2 =
        ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    change
      (∑ i : Fin d, ∑ j : Fin d,
        ‖star (z (j, i))‖ ^ 2) =
        ∑ i : Fin d, ∑ j : Fin d, ‖z (i, j)‖ ^ 2
    simp_rw [norm_star]
    rw [Finset.sum_comm]
  nlinarith [norm_nonneg
    (dSVUniformLeftDensityConjugateSwapVector z),
    norm_nonneg z]

theorem dSVUniformLeftDensityConjugateSwapVector_distance
    {d : ℕ} (z w : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖dSVUniformLeftDensityConjugateSwapVector z -
        dSVUniformLeftDensityConjugateSwapVector w‖ =
      ‖z - w‖ := by
  have difference :
      dSVUniformLeftDensityConjugateSwapVector z -
        dSVUniformLeftDensityConjugateSwapVector w =
      dSVUniformLeftDensityConjugateSwapVector (z - w) := by
    ext ij
    change star (z (ij.2, ij.1)) - star (w (ij.2, ij.1)) =
      star ((z - w) (ij.2, ij.1))
    simp only [RCLike.star_def, PiLp.sub_apply, star_sub]
  rw [difference,
    dSVUniformLeftDensityConjugateSwapVector_norm]

private def dSVUniformLeftDensityConjugateSwap
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    BipartiteUnitVector d :=
  ⟨dSVUniformLeftDensityConjugateSwapVector ξ.val,
    (dSVUniformLeftDensityConjugateSwapVector_norm ξ.val).trans
      ξ.property⟩

theorem dSVUniformLeftDensityConjugateSwap_coefficient
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetCoefficientMatrix
        (dSVUniformLeftDensityConjugateSwap ξ) =
      (targetCoefficientMatrix ξ).conjTranspose := by
  ext b a
  rfl

theorem dSVUniformLeftDensityConjugateSwap_density
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetReducedDensity
        (dSVUniformLeftDensityConjugateSwap ξ) =
      dSVSoftBobLeftReducedDensity ξ := by
  unfold targetReducedDensity
    dSVSoftBobLeftReducedDensity
  rw [dSVUniformLeftDensityConjugateSwap_coefficient,
    Matrix.conjTranspose_conjTranspose]

theorem dSVUniformLeftDensityConjugateSwap_distance
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    ‖(dSVUniformLeftDensityConjugateSwap ξ).val -
        (dSVUniformLeftDensityConjugateSwap ζ).val‖ =
      ‖ξ.val - ζ.val‖ :=
  dSVUniformLeftDensityConjugateSwapVector_distance
    ξ.val ζ.val

/--
The DSV uniform left density schmidt coefficient construction used in the quantum parallel-
repetition argument.
-/
def dSVUniformLeftDensitySchmidtCoefficient
    {d : ℕ} (ξ : BipartiteUnitVector d)
    (i : Fin d) : ℝ :=
  Real.sqrt
    ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)

/--
The DSV uniform left density spectral atom discrepancy construction used in the quantum
parallel-repetition argument.
-/
def dSVUniformLeftDensitySpectralAtomDiscrepancy
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    |dSVUniformLeftDensitySchmidtCoefficient ξ i ^ 2 -
      dSVUniformLeftDensitySchmidtCoefficient ζ j ^ 2| *
      spectralAtomOverlap
        (dSVSoftBobLeftReducedDensity ξ)
        (dSVSoftBobLeftReducedDensity ζ)
        (dSVSoftBobLeftReducedDensity_posSemidef ξ)
        (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j

theorem dSVUniformLeftDensitySpectralAtomDiscrepancy_eq_swap
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ =
      dSVUniformDensitySpectralAtomDiscrepancy
        (dSVUniformLeftDensityConjugateSwap ξ)
        (dSVUniformLeftDensityConjugateSwap ζ) := by
  unfold dSVUniformLeftDensitySpectralAtomDiscrepancy
    dSVUniformDensitySpectralAtomDiscrepancy
    dSVUniformLeftDensitySchmidtCoefficient
    targetCanonicalSchmidtCoefficient
  simp only [dSVUniformLeftDensityConjugateSwap_density]

theorem dSVUniformLeftDensitySpectralAtomDiscrepancy_le
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ ≤
      2 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ := by
  rw [dSVUniformLeftDensitySpectralAtomDiscrepancy_eq_swap]
  have bound := dSVUniformDensitySpectralAtomDiscrepancy_le
    (dSVUniformLeftDensityConjugateSwap ξ)
    (dSVUniformLeftDensityConjugateSwap ζ)
  rwa [dSVUniformLeftDensityConjugateSwap_distance] at bound

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The DSV uniform density threshold grid construction used in the quantum parallel-repetition
argument.
-/
def dSVUniformDensityThresholdGrid
    (N : ℕ) (k : Fin N) : ℝ :=
  finiteUniformThresholdGrid
    (1 / (N : ℝ)) (1 + 1 / (N : ℝ)) N k

theorem dSVUniformDensityThresholdGrid_apply
    {N : ℕ} (positive : 0 < N) (k : Fin N) :
    dSVUniformDensityThresholdGrid N k =
      ((k.val : ℝ) + 1) / (N : ℝ) := by
  have nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  unfold dSVUniformDensityThresholdGrid
    finiteUniformThresholdGrid
  field_simp
  ring

/-- The probability weight for DSV uniform density threshold. -/
def dSVUniformDensityThresholdWeight
    (N : ℕ) (_k : Fin N) : ℝ :=
  1 / (N : ℝ)

theorem dSVUniformDensityThresholdWeight_nonneg
    (N : ℕ) (k : Fin N) :
    0 ≤ dSVUniformDensityThresholdWeight N k := by
  unfold dSVUniformDensityThresholdWeight
  positivity

/--
The DSV uniform density grid prefix construction used in the quantum parallel-repetition
argument.
-/
def dSVUniformDensityGridPrefix
    (N : ℕ) (density : ℝ) : ℝ :=
  ∑ k : Fin N,
    dSVUniformDensityThresholdWeight N k *
      if dSVUniformDensityThresholdGrid N k ≤ density
      then 1 else 0

theorem dSVUniformDensityGridPrefix_eq_count
    (N : ℕ) (density : ℝ) :
    dSVUniformDensityGridPrefix N density =
      ((Finset.univ.filter fun k : Fin N =>
        dSVUniformDensityThresholdGrid N k ≤ density).card : ℝ) /
        (N : ℝ) := by
  classical
  unfold dSVUniformDensityGridPrefix
    dSVUniformDensityThresholdWeight
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [div_eq_mul_inv, mul_comm, mul_one, sum_const, nsmul_eq_mul]

/--
The DSV uniform density threshold mismatch construction used in the quantum parallel-repetition
argument.
-/
def dSVUniformDensityThresholdMismatch
    (N : ℕ) (alice bob : ℝ) : ℝ :=
  ∑ k : Fin N,
    dSVUniformDensityThresholdWeight N k *
      if ((dSVUniformDensityThresholdGrid N k ≤ alice) ↔
        (dSVUniformDensityThresholdGrid N k ≤ bob))
      then 0 else 1

theorem dSVUniformDensityThresholdMismatch_indicator_le_crossing
    {N : ℕ} (k : Fin N) (alice bob : ℝ) :
    (if ((dSVUniformDensityThresholdGrid N k ≤ alice) ↔
        (dSVUniformDensityThresholdGrid N k ≤ bob))
      then (0 : ℝ) else 1) ≤
      if min alice bob ≤ dSVUniformDensityThresholdGrid N k ∧
        dSVUniformDensityThresholdGrid N k ≤ max alice bob
      then 1 else 0 := by
  classical
  by_cases left : dSVUniformDensityThresholdGrid N k ≤ alice
  · by_cases right : dSVUniformDensityThresholdGrid N k ≤ bob
    · simp only [left, right, iff_self, ↓reduceIte]
      split <;> norm_num
    · have lower : bob < dSVUniformDensityThresholdGrid N k :=
        lt_of_not_ge right
      have interval :
          min alice bob ≤ dSVUniformDensityThresholdGrid N k ∧
            dSVUniformDensityThresholdGrid N k ≤ max alice bob :=
        ⟨(min_le_right alice bob).trans lower.le,
          left.trans (le_max_left alice bob)⟩
      simp only [left, right, iff_false, not_true_eq_false, ↓reduceIte, interval, and_self,
        Std.le_refl]
  · by_cases right : dSVUniformDensityThresholdGrid N k ≤ bob
    · have lower : alice < dSVUniformDensityThresholdGrid N k :=
        lt_of_not_ge left
      have interval :
          min alice bob ≤ dSVUniformDensityThresholdGrid N k ∧
            dSVUniformDensityThresholdGrid N k ≤ max alice bob :=
        ⟨(min_le_left alice bob).trans lower.le,
          right.trans (le_max_right alice bob)⟩
      simp only [left, right, iff_true, ↓reduceIte, interval, and_self, Std.le_refl]
    · simp only [left, right, ↓reduceIte, inf_le_iff, le_sup_iff, or_self, and_false, Std.le_refl]

theorem dSVUniformDensityThresholdMismatch_le
    {N : ℕ} (positive : 0 < N) (alice bob : ℝ) :
    dSVUniformDensityThresholdMismatch N alice bob ≤
      |alice - bob| + 1 / (N : ℝ) := by
  classical
  have window :
      (1 / (N : ℝ)) < 1 + 1 / (N : ℝ) := by linarith
  calc
    dSVUniformDensityThresholdMismatch N alice bob ≤
      finiteUniformThresholdCrossing
        (1 / (N : ℝ)) (1 + 1 / (N : ℝ)) alice bob N := by
      unfold dSVUniformDensityThresholdMismatch
        finiteUniformThresholdCrossing
      calc
        (∑ k : Fin N,
          dSVUniformDensityThresholdWeight N k *
            if ((dSVUniformDensityThresholdGrid N k ≤ alice) ↔
              (dSVUniformDensityThresholdGrid N k ≤ bob))
            then 0 else 1) ≤
          ∑ k : Fin N,
            dSVUniformDensityThresholdWeight N k *
              if min alice bob ≤
                  dSVUniformDensityThresholdGrid N k ∧
                dSVUniformDensityThresholdGrid N k ≤ max alice bob
              then 1 else 0 := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left
              (dSVUniformDensityThresholdMismatch_indicator_le_crossing
                k alice bob)
              (dSVUniformDensityThresholdWeight_nonneg N k)
        _ = _ := by
          unfold dSVUniformDensityThresholdWeight
            dSVUniformDensityThresholdGrid
          simp_rw [mul_ite, mul_one, mul_zero]
          rw [← Finset.sum_filter]
          simp only [div_eq_mul_inv, mul_comm, mul_one, inf_le_iff, le_sup_iff, sum_const,
            nsmul_eq_mul]
    _ ≤ |alice - bob| /
        ((1 + 1 / (N : ℝ)) - (1 / (N : ℝ))) +
          1 / (N : ℝ) :=
      finiteUniformThresholdCrossing_le
        window alice bob N positive
    _ = |alice - bob| + 1 / (N : ℝ) := by
      ring

theorem dSVUniformDensityThresholdGrid_count_eq_floor
    {N : ℕ} (positive : 0 < N)
    (density : ℝ) (nonnegative : 0 ≤ density) (bounded : density ≤ 1) :
    (Finset.univ.filter fun k : Fin N =>
      dSVUniformDensityThresholdGrid N k ≤ density).card =
        Nat.floor (density * (N : ℝ)) := by
  classical
  have gridpositive : (0 : ℝ) < N := by exact_mod_cast positive
  have densitypositive : 0 ≤ density * (N : ℝ) :=
    mul_nonneg nonnegative gridpositive.le
  have floor_bound : Nat.floor (density * (N : ℝ)) ≤ N := by
    have product : density * (N : ℝ) ≤ (N : ℝ) := by
      nlinarith
    have floor := Nat.floor_mono product
    simpa only [ge_iff_le, Nat.floor_natCast] using floor
  have same :
      (Finset.univ.filter fun k : Fin N =>
        dSVUniformDensityThresholdGrid N k ≤ density) =
      (Finset.univ.filter fun k : Fin N =>
        k.val < Nat.floor (density * (N : ℝ))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dSVUniformDensityThresholdGrid_apply positive,
      div_le_iff₀ gridpositive]
    constructor
    · intro threshold
      have cast : ((k.val + 1 : ℕ) : ℝ) ≤ density * (N : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using threshold
      have below := (Nat.le_floor_iff densitypositive).2 cast
      omega
    · intro below
      have integer : k.val + 1 ≤ Nat.floor (density * (N : ℝ)) := by
        omega
      have cast := (Nat.le_floor_iff densitypositive).1 integer
      simpa only [ge_iff_le, Nat.cast_add, Nat.cast_one] using cast
  rw [same, Fin.card_filter_val_lt, min_eq_right floor_bound]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


theorem dSVUniformDensityBinarySpectral_false_eq_complement
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (bin : d → Bool) :
    (spectralPartitionPOVM F hF bin).effect false =
      1 - (spectralPartitionPOVM F hF bin).effect true := by
  have complete := (spectralPartitionPOVM F hF bin).complete
  rw [Fintype.sum_bool] at complete
  rw [add_comm] at complete
  exact eq_sub_of_add_eq complete

end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem dSVUniformDensitySchmidtVector_sub
    {d : ℕ} (σ τ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    schmidtVector σ U V -
        schmidtVector τ U V =
      schmidtVector (fun i => σ i - τ i) U V := by
  unfold schmidtVector
  rw [← localUnitaryAction_sub]
  congr 1
  ext ⟨i, j⟩
  by_cases equal : i = j
  · subst j
    simp only [diagonalSchmidtState, PiLp.sub_apply, ↓reduceIte, ofReal_sub]
  · simp only [diagonalSchmidtState, PiLp.sub_apply, equal, ↓reduceIte, sub_self, ofReal_sub]

theorem dSVUniformDensity_normalize_sub_self_norm
    {d : ℕ} (v : EuclideanSpace ℂ (Fin d × Fin d))
    (nonzero : v ≠ 0) :
    ‖NormedSpace.normalize v - v‖ = |1 - ‖v‖| := by
  have positive : 0 < ‖v‖ := norm_pos_iff.mpr nonzero
  calc
    ‖NormedSpace.normalize v - v‖ =
        ‖((‖v‖⁻¹ - 1 : ℝ) • v)‖ := by
          unfold NormedSpace.normalize
          congr 1
          rw [sub_smul, one_smul]
    _ = |‖v‖⁻¹ - 1| * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs]
    _ = |(‖v‖⁻¹ - 1) * ‖v‖| := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg v)]
    _ = |1 - ‖v‖| := by
          congr 1
          field_simp [positive.ne']

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] Classical.propDecidable

/-- The normalize or default construction used in the quantum parallel-repetition argument. -/
def normalizeOrDefault (fallback z : E) : E :=
  if z = 0 then fallback else NormedSpace.normalize z

theorem normalizeOrDefault_norm
    (fallback z : E) (hfallback : ‖fallback‖ = 1) :
    ‖normalizeOrDefault fallback z‖ = 1 := by
  classical
  by_cases hz : z = 0
  · simp only [normalizeOrDefault, hz, ↓reduceIte, hfallback]
  · simp only [normalizeOrDefault, hz, ↓reduceIte, NormedSpace.norm_normalize hz]

theorem normalizeOrDefault_sub_le
    (fallback u v : E)
    (hfallback : ‖fallback‖ = 1)
    (hu : u ≠ 0) :
    ‖normalizeOrDefault fallback u - normalizeOrDefault fallback v‖ ≤
      2 * ‖u - v‖ / ‖u‖ := by
  classical
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  by_cases hv : v = 0
  · simp only [normalizeOrDefault, hu, ↓reduceIte, hv, sub_zero]
    calc
      ‖NormedSpace.normalize u - fallback‖ ≤
          ‖NormedSpace.normalize u‖ + ‖fallback‖ := norm_sub_le _ _
      _ = 2 := by rw [NormedSpace.norm_normalize hu, hfallback]; norm_num
      _ = 2 * ‖u‖ / ‖u‖ := by field_simp
  · simp only [normalizeOrDefault, hu, hv, ↓reduceIte]
    let u₀ := NormedSpace.normalize u
    let v₀ := NormedSpace.normalize v
    have hv₀ : ‖v₀‖ = 1 := NormedSpace.norm_normalize hv
    have hrevu : ‖u‖ • u₀ = u :=
      NormedSpace.norm_smul_normalize u
    have hrevv : ‖v‖ • v₀ = v :=
      NormedSpace.norm_smul_normalize v
    have hreverse : |‖v‖ - ‖u‖| ≤ ‖u - v‖ := by
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le v u
    have hscaled :
        ‖u‖ * ‖u₀ - v₀‖ = ‖u - ‖u‖ • v₀‖ := by
      calc
        ‖u‖ * ‖u₀ - v₀‖ = ‖‖u‖ • (u₀ - v₀)‖ := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg u)]
        _ = ‖u - ‖u‖ • v₀‖ := by rw [smul_sub, hrevu]
    have hsecond : ‖v - ‖u‖ • v₀‖ = |‖v‖ - ‖u‖| := by
      calc
        ‖v - ‖u‖ • v₀‖ = ‖‖v‖ • v₀ - ‖u‖ • v₀‖ := by
          rw [hrevv]
        _ = ‖(‖v‖ - ‖u‖) • v₀‖ := by rw [sub_smul]
        _ = |‖v‖ - ‖u‖| := by
          rw [norm_smul, Real.norm_eq_abs, hv₀, mul_one]
    have hbound : ‖u‖ * ‖u₀ - v₀‖ ≤ 2 * ‖u - v‖ := by
      rw [hscaled]
      calc
        ‖u - ‖u‖ • v₀‖ ≤
            ‖u - v‖ + ‖v - ‖u‖ • v₀‖ := by
              have hsplit :
                  u - ‖u‖ • v₀ = (u - v) + (v - ‖u‖ • v₀) := by
                abel
              rw [hsplit]
              exact norm_add_le _ _
        _ = ‖u - v‖ + |‖v‖ - ‖u‖| := by rw [hsecond]
        _ ≤ 2 * ‖u - v‖ := by linarith
    change ‖u₀ - v₀‖ ≤ 2 * ‖u - v‖ / ‖u‖
    exact (le_div_iff₀ hupos).mpr (by linarith)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


/--
The DSV canonical failure unit rank family construction used in the quantum parallel-repetition
argument.
-/
def dSVCanonicalFailureUnitRankFamily
    (d : ℕ) (positive : 0 < d) (rank : Fin (d + 1)) :
    BipartiteUnitVector d :=
  ⟨normalizeOrDefault
      (embezzlementState d)
      (dSVCanonicalFailurePrefix rank),
    normalizeOrDefault_norm
      (embezzlementState d)
      (dSVCanonicalFailurePrefix rank)
      (embezzlementState_norm d positive)⟩

theorem dSVCanonicalFailurePrefix_eq_zero_of_rank_zero
    {d : ℕ} (rank : Fin (d + 1))
    (zero : rank.val = 0) :
    dSVCanonicalFailurePrefix rank = 0 := by
  have squared :
      ‖dSVCanonicalFailurePrefix rank‖ ^ 2 = 0 := by
    simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero,
      zero, CharP.cast_eq_zero] using dSVCanonicalFailurePrefix_norm_sq rank
  have normzero : ‖dSVCanonicalFailurePrefix rank‖ = 0 := by
    nlinarith [norm_nonneg (dSVCanonicalFailurePrefix rank)]
  exact norm_eq_zero.mp normzero

theorem dSVCanonicalFailurePrefix_norm_eq_sqrt
    {d : ℕ} (rank : Fin (d + 1)) :
    ‖dSVCanonicalFailurePrefix rank‖ =
      Real.sqrt (rank.val : ℝ) := by
  have squared := dSVCanonicalFailurePrefix_norm_sq rank
  have root := Real.sq_sqrt (by positivity : 0 ≤ (rank.val : ℝ))
  nlinarith [norm_nonneg (dSVCanonicalFailurePrefix rank),
    Real.sqrt_nonneg (rank.val : ℝ)]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The DSV uniform density threshold left bob basis construction used in the quantum parallel-
repetition argument.
-/
def dSVUniformDensityThresholdLeftBobBasis
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  (dSVSoftBobLeftReducedDensity_posSemidef ζ).isHermitian.eigenvectorUnitary

end

section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

private def dSVUniformDensityPolarConjugateSwap
    {d : ℕ} (v : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 (fun q : Fin d × Fin d => star (v (q.2, q.1)))

theorem dSVUniformDensityPolarConjugateSwap_norm
    {d : ℕ} (v : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖dSVUniformDensityPolarConjugateSwap v‖ = ‖v‖ := by
  have squares :
      ‖dSVUniformDensityPolarConjugateSwap v‖ ^ 2 =
        ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [dSVUniformDensityPolarConjugateSwap,
      norm_star]
    exact Finset.sum_comm
  nlinarith [norm_nonneg
    (dSVUniformDensityPolarConjugateSwap v), norm_nonneg v]

private def dSVUniformDensityPolarConjugateSwapTarget
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    BipartiteUnitVector d :=
  ⟨dSVUniformDensityPolarConjugateSwap ξ.val, by
    rw [dSVUniformDensityPolarConjugateSwap_norm]
    exact ξ.property⟩

theorem dSVUniformDensityPolarConjugateSwap_coefficient
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetCoefficientMatrix
        (dSVUniformDensityPolarConjugateSwapTarget ξ) =
      (targetCoefficientMatrix ξ).conjTranspose := by
  ext b a
  rfl

theorem dSVUniformDensityPolarConjugateSwap_reducedDensity
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetReducedDensity
        (dSVUniformDensityPolarConjugateSwapTarget ξ) =
      dSVSoftBobLeftReducedDensity ξ := by
  unfold targetReducedDensity
    dSVSoftBobLeftReducedDensity
  rw [dSVUniformDensityPolarConjugateSwap_coefficient]
  simp only [conjTranspose_conjTranspose]

/--
The DSV uniform density polar left schmidt coefficient construction used in the quantum
parallel-repetition argument.
-/
def dSVUniformDensityPolarLeftSchmidtCoefficient
    {d : ℕ} (ξ : BipartiteUnitVector d)
    (i : Fin d) : ℝ :=
  Real.sqrt
    ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)

theorem exists_proofDSVUniformDensityPolarLeftCanonicalSchmidt
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    ∃ A : Matrix.unitaryGroup (Fin d) ℂ,
      ξ.val = schmidtVector
        (dSVUniformDensityPolarLeftSchmidtCoefficient ξ)
        A (dSVUniformDensityThresholdLeftBobBasis ξ) := by
  let χ := dSVUniformDensityPolarConjugateSwapTarget ξ
  have density : targetReducedDensity χ =
      dSVSoftBobLeftReducedDensity ξ :=
    dSVUniformDensityPolarConjugateSwap_reducedDensity ξ
  obtain ⟨V, decomposition⟩ :=
    exists_proofTargetCanonicalSpectralSchmidtDecomposition χ
  have canonical_basis :
      (targetReducedDensity_posSemidef χ).isHermitian.eigenvectorUnitary =
        dSVUniformDensityThresholdLeftBobBasis ξ := by
    unfold dSVUniformDensityThresholdLeftBobBasis
    simp only [density]
  have canonical_coefficient :
      targetCanonicalSchmidtCoefficient χ =
        dSVUniformDensityPolarLeftSchmidtCoefficient ξ := by
    funext i
    unfold targetCanonicalSchmidtCoefficient
      dSVUniformDensityPolarLeftSchmidtCoefficient
    simp only [density]
  rw [canonical_basis, canonical_coefficient] at decomposition
  refine ⟨conjugateUnitary V, ?_⟩
  ext ⟨a, b⟩
  have coordinate := congrArg
    (fun v : EuclideanSpace ℂ (Fin d × Fin d) => v (b, a))
    decomposition
  change star (ξ.val (a, b)) = _ at coordinate
  rw [schmidtVector_apply] at coordinate
  have unconjugated := congrArg star coordinate
  rw [schmidtVector_apply]
  simpa only [conjugateUnitary_apply, RCLike.star_def, mul_comm, mul_left_comm,
    RingHomCompTriple.comp_apply, RingHom.id_apply, star_sum, star_mul',
    conj_ofReal] using unconjugated

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def finiteTensorLocalUnitaryMatrix
    {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    (U : ι → Matrix.unitaryGroup β ℂ) :
    Matrix (ι → β) (ι → β) ℂ :=
  fun q r => ∏ i : ι, (U i : Matrix β β ℂ) (q i) (r i)

theorem finiteTensorLocalUnitaryMatrix_gram
    {ι β : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : ι → Matrix.unitaryGroup β ℂ) :
    (finiteTensorLocalUnitaryMatrix U).conjTranspose *
        finiteTensorLocalUnitaryMatrix U = 1 := by
  classical
  ext p q
  change
    (∑ r : ι → β,
      star (∏ i : ι, (U i : Matrix β β ℂ) (r i) (p i)) *
        (∏ i : ι, (U i : Matrix β β ℂ) (r i) (q i))) =
      (1 : Matrix (ι → β) (ι → β) ℂ) p q
  have factor :
      (∑ r : ι → β,
        star (∏ i : ι, (U i : Matrix β β ℂ) (r i) (p i)) *
          (∏ i : ι, (U i : Matrix β β ℂ) (r i) (q i))) =
        ∏ i : ι, ∑ x : β,
          star ((U i : Matrix β β ℂ) x (p i)) *
            (U i : Matrix β β ℂ) x (q i) := by
    calc
      _ = ∑ r : ι → β, ∏ i : ι,
          (star ((U i : Matrix β β ℂ) (r i) (p i)) *
            (U i : Matrix β β ℂ) (r i) (q i)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [star_prod, ← Finset.prod_mul_distrib]
      _ = _ :=
        (Fintype.prod_sum fun i : ι => fun x : β =>
          star ((U i : Matrix β β ℂ) x (p i)) *
            (U i : Matrix β β ℂ) x (q i)).symm
  rw [factor]
  have single (i : ι) :
      (∑ x : β,
        star ((U i : Matrix β β ℂ) x (p i)) *
          (U i : Matrix β β ℂ) x (q i)) =
        (1 : Matrix β β ℂ) (p i) (q i) := by
    have gram := (Matrix.mem_unitaryGroup_iff').mp
      (U i).property
    have entry := congrArg
      (fun M : Matrix β β ℂ => M (p i) (q i)) gram
    simpa only [RCLike.star_def, star_eq_conjTranspose, Matrix.mul_apply,
      conjTranspose_apply] using entry
  simp_rw [single]
  by_cases equal : p = q
  · subst q
    simp only [one_apply_eq, prod_const_one]
  · have different : ∃ i : ι, p i ≠ q i := by
      by_contra h
      push Not at h
      exact equal (funext h)
    obtain ⟨i, hi⟩ := different
    have zero :
        (∏ j : ι, (1 : Matrix β β ℂ) (p j) (q j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [ne_eq, hi, not_false_eq_true, one_apply_ne]
    rw [zero]
    simp only [ne_eq, equal, not_false_eq_true, one_apply_ne]

private def finiteTensorLocalUnitary
    {ι β : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : ι → Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (ι → β) ℂ := by
  refine ⟨finiteTensorLocalUnitaryMatrix U, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose]
  exact finiteTensorLocalUnitaryMatrix_gram U

/-- The unitary operator implementing controlled finite tensor local. -/
def controlledFiniteTensorLocalUnitary
    {Ω ι β : Type*}
    [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : Ω → ι → Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Ω, (ι → β)) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun ω => finiteTensorLocalUnitary (U ω))

end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem controlledFiniteTensorLocalUnitary_apply
    {Ω ι β : Type*}
    [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : Ω → ι → Matrix.unitaryGroup β ℂ)
    (ω ν : Ω) (q r : ι → β) :
    (controlledFiniteTensorLocalUnitary U :
      Matrix (Σ _ : Ω, (ι → β)) (Σ _ : Ω, (ι → β)) ℂ)
        ⟨ω, q⟩ ⟨ν, r⟩ =
      if ω = ν then
        ∏ i : ι, (U ω i : Matrix β β ℂ) (q i) (r i)
      else 0 := by
  classical
  by_cases equal : ω = ν
  · subst ν
    simp only [controlledFiniteTensorLocalUnitary, coherentSharedRandomControlledUnitary,
      finiteTensorLocalUnitary, blockDiagonal'_apply, ↓reduceDIte, finiteTensorLocalUnitaryMatrix,
      cast_eq, ↓reduceIte]
  · simp only [controlledFiniteTensorLocalUnitary, coherentSharedRandomControlledUnitary,
      blockDiagonal'_apply, equal, ↓reduceDIte, ↓reduceIte]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The type used to represent DSV uniform density threshold whole history local index in the exact
sampling construction.
-/
abbrev DSVUniformDensityThresholdWholeHistoryLocalIndex
    (N d L : ℕ) :=
  Σ _ : Fin (L + 1),
    Fin (L + 1) → DSVUniformDensityThresholdLocalIndex N d

/--
The type used to represent DSV uniform density threshold whole history catalyst index in the
exact sampling construction.
-/
abbrev DSVUniformDensityThresholdWholeHistoryCatalystIndex
    (N d L : ℕ) :=
  Fin N × (Fin (L + 1) ×
    (Fin L → DSVUniformDensityThresholdLocalIndex N d))

/-- The quantum state representing DSV uniform density threshold whole history shared. -/
def dSVUniformDensityThresholdWholeHistorySharedState
    (N d L : ℕ) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ×
        DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) :=
  sharedThresholdResource
    (d := Fin (L + 1) →
      DSVUniformDensityThresholdLocalIndex N d)
    (fun flag : Fin (L + 1) =>
      if flag.val = 0 then (1 : ℝ) else 0)

theorem dSVUniformDensityThresholdWholeHistorySharedState_norm
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (L : ℕ) :
    ‖dSVUniformDensityThresholdWholeHistorySharedState
      N d L‖ = 1 := by
  let k : Fin (L + 1) := ⟨0, by omega⟩
  let i : Fin (L + 1) →
      DSVUniformDensityThresholdLocalIndex N d :=
    fun _ => ⟨⟨0, grid⟩, ⟨0, dimension⟩⟩
  apply sharedThresholdResource_norm
    (fun flag : Fin (L + 1) =>
      if flag.val = 0 then (1 : ℝ) else 0) k i
  simp only [↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true, k]

/-- The finite equivalence encoding DSV uniform density threshold whole history target split. -/
def dSVUniformDensityThresholdWholeHistoryTargetSplitEquiv
    (N d L : ℕ) :
    DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ≃
      (Fin d ×
        DSVUniformDensityThresholdWholeHistoryCatalystIndex
          N d L) where
  toFun q :=
    ((q.2 0).2,
      ((q.2 0).1, (q.1, fun j => q.2 j.succ)))
  invFun q :=
    ⟨q.2.2.1,
      Fin.cons (⟨q.2.1, q.1⟩ :
        DSVUniformDensityThresholdLocalIndex N d)
        q.2.2.2⟩
  left_inv := by
    rintro ⟨flag, history⟩
    change
      (⟨flag, Fin.cons (history 0) (fun j => history j.succ)⟩ :
        DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L) = ⟨flag, history⟩
    congr 1
    exact Fin.cons_self_tail history
  right_inv := by
    rintro ⟨target, threshold, flag, history⟩
    simp only [Fin.cons_zero, Fin.cons_succ]

/--
The DSV uniform density alice history spectral copy construction used in the quantum parallel-
repetition argument.
-/
def dSVUniformDensityAliceHistorySpectralCopy
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun _ : Fin N =>
      (dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹)

/--
The DSV uniform density bob history copy basis construction used in the quantum parallel-
repetition argument.
-/
def dSVUniformDensityBobHistoryCopyBasis
    {N d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun _ : Fin N =>
      conjugateUnitary
        (dSVUniformDensityThresholdLeftBobBasis ζ))

theorem dSVUniformDensityCompletePureHistory_raw_norm
    (N d L : ℕ) :
    ‖sharedThresholdResourceRaw
      (d := Fin (L + 1) →
        DSVUniformDensityThresholdLocalIndex N d)
      (fun flag : Fin (L + 1) =>
        if flag.val = 0 then (1 : ℝ) else 0)‖ =
      ‖sharedThresholdResourceRaw (d := Fin d)
        (fun _ : Fin N => (1 : ℝ))‖ ^ (L + 1) := by
  let single := sharedThresholdResourceRaw (d := Fin d)
    (fun _ : Fin N => (1 : ℝ))
  let whole := sharedThresholdResourceRaw
    (d := Fin (L + 1) →
      DSVUniformDensityThresholdLocalIndex N d)
    (fun flag : Fin (L + 1) =>
      if flag.val = 0 then (1 : ℝ) else 0)
  have hsquare : ‖single‖ ^ 2 = (d : ℝ) * (N : ℝ) :=
    dSVUniformDensityThresholdRaw_norm_sq N d
  have hwhole :
      ‖whole‖ ^ 2 = (((N * d) ^ (L + 1) : ℕ) : ℝ) := by
    have original := sharedThresholdResourceRaw_norm_sq
      (d := Fin (L + 1) →
        DSVUniformDensityThresholdLocalIndex N d)
      (fun flag : Fin (L + 1) =>
        if flag.val = 0 then (1 : ℝ) else 0)
    simpa [DSVUniformDensityThresholdLocalIndex,
      whole] using original
  have hpower :
      (‖single‖ ^ (L + 1)) ^ 2 =
        (((N * d) ^ (L + 1) : ℕ) : ℝ) := by
    calc
      (‖single‖ ^ (L + 1)) ^ 2 =
        (‖single‖ ^ 2) ^ (L + 1) := by
          simp only [← pow_mul, Nat.mul_comm]
      _ = (((N * d) ^ (L + 1) : ℕ) : ℝ) := by
          rw [hsquare]
          push_cast
          ring
  change ‖whole‖ = ‖single‖ ^ (L + 1)
  nlinarith [norm_nonneg whole,
    pow_nonneg (norm_nonneg single) (L + 1)]

theorem dSVUniformDensityCompletePureHistory_zeroFlag_apply
    (N d L : ℕ)
    (flag other : Fin (L + 1))
    (alice bob :
      DSVUniformDensityIndependentHistoryLocalIndex
        (L + 1) N d) :
    dSVUniformDensityThresholdWholeHistorySharedState N d L
      (⟨flag, alice⟩, ⟨other, bob⟩) =
      if flag.val = 0 ∧ other.val = 0 then
        dSVUniformDensityIndependentSharedState
          (L + 1) N d (alice, bob)
      else 0 := by
  classical
  let single := sharedThresholdResourceRaw (d := Fin d)
    (fun _ : Fin N => (1 : ℝ))
  let whole := sharedThresholdResourceRaw
    (d := Fin (L + 1) →
      DSVUniformDensityThresholdLocalIndex N d)
    (fun k : Fin (L + 1) =>
      if k.val = 0 then (1 : ℝ) else 0)
  have normalization :
      ‖whole‖ = ‖single‖ ^ (L + 1) :=
    dSVUniformDensityCompletePureHistory_raw_norm N d L
  have scalar :
      ‖whole‖⁻¹ = (‖single‖⁻¹) ^ (L + 1) := by
    rw [normalization, inv_pow]
  by_cases first_zero : flag = 0
  · subst flag
    by_cases second_zero : other = 0
    · subst other
      simp only [and_self]
      rw [dSVUniformDensityIndependentSharedState_apply]
      by_cases histories : alice = bob
      · subst bob
        have complex_scalar :
            ((‖whole‖⁻¹ : ℝ) : ℂ) =
              (((‖single‖⁻¹) ^ (L + 1) : ℝ) : ℂ) := by
          exact_mod_cast scalar
        have whole_amplitude :
            dSVUniformDensityThresholdWholeHistorySharedState
                N d L (⟨0, alice⟩, ⟨0, alice⟩) =
              ((‖whole‖⁻¹ : ℝ) : ℂ) := by
          simp only [dSVUniformDensityThresholdWholeHistorySharedState, sharedThresholdResource,
            sharedThresholdResourceRaw, Fin.val_eq_zero_iff, PiLp.smul_apply, and_self,
            ↓reduceIte, ofReal_one, real_smul, ofReal_inv, mul_one, whole]
        have single_amplitude
            (q : DSVUniformDensityThresholdLocalIndex N d) :
            dSVUniformDensityThresholdSharedState N d (q, q) =
              ((‖single‖⁻¹ : ℝ) : ℂ) := by
          simp only [dSVUniformDensityThresholdSharedState, sharedThresholdResource,
            sharedThresholdResourceRaw, ofReal_one, PiLp.smul_apply, and_self, ↓reduceIte,
            real_smul, ofReal_inv, mul_one, single]
        rw [whole_amplitude]
        simp_rw [single_amplitude]
        simpa only [ofReal_inv, Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceIte, prod_inv_distrib,
          prod_const, card_univ, Fintype.card_fin, _root_.inv_inj, inv_pow,
          ofReal_pow] using complex_scalar
      · obtain ⟨j, different⟩ :
          ∃ j : Fin (L + 1), alice j ≠ bob j := by
          by_contra absent
          push Not at absent
          exact histories (funext absent)
        have zero :
            dSVUniformDensityThresholdSharedState N d
              (alice j, bob j) = 0 := by
          by_cases labels : (alice j).1 = (bob j).1
          · have works : (alice j).2 ≠ (bob j).2 := by
              intro same
              apply different
              exact Sigma.ext labels (by simpa only [heq_eq_eq] using same)
            exact
              dSVUniformDensityThresholdSharedState_mismatchedWork
                N d (alice j).1 (bob j).1
                (alice j).2 (bob j).2 works
          · exact
              dSVUniformDensityThresholdSharedState_mismatchedFlag
                N d (alice j).1 (bob j).1
                (alice j).2 (bob j).2 labels
        have product_zero :
            (∏ i : Fin (L + 1),
              dSVUniformDensityThresholdSharedState N d
                (alice i, bob i)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) zero
        rw [product_zero]
        simp only [dSVUniformDensityThresholdWholeHistorySharedState, sharedThresholdResource,
          sharedThresholdResourceRaw, Fin.val_eq_zero_iff, PiLp.smul_apply, histories, and_false,
          ↓reduceIte, smul_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
    · have nonzero : other.val ≠ 0 := by
        simpa only [ne_eq, Fin.val_eq_zero_iff] using second_zero
      have different : (0 : Fin (L + 1)) ≠ other := by
        exact Ne.symm second_zero
      simp only [dSVUniformDensityThresholdWholeHistorySharedState, sharedThresholdResource,
        sharedThresholdResourceRaw, Fin.val_eq_zero_iff, PiLp.smul_apply, different, false_and,
        ↓reduceIte, smul_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod, nonzero, and_false]
  · have nonzero : flag.val ≠ 0 := by
      simpa only [ne_eq, Fin.val_eq_zero_iff] using first_zero
    simp only [dSVUniformDensityThresholdWholeHistorySharedState, sharedThresholdResource,
      sharedThresholdResourceRaw, Fin.val_eq_zero_iff, PiLp.smul_apply, first_zero, ↓reduceIte,
      ofReal_zero, ite_self, smul_zero, nonzero, false_and]

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def scalarPurificationLp (z : ℝ) (hz : 0 ≤ z) :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  ((scalarResolventFilter_memLp_two hz).ofReal (K := ℂ)).toLp
    (fun s : ℝ => ((z / (z + s) : ℝ) : ℂ))

theorem scalarPurificationLp_coeFn
    (z : ℝ) (hz : 0 ≤ z) :
    (scalarPurificationLp z hz : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      (fun s : ℝ => ((z / (z + s) : ℝ) : ℂ)) :=
  ((scalarResolventFilter_memLp_two hz).ofReal
    (K := ℂ)).coeFn_toLp

private def commonPurificationGenerator
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    Sum (ι × d) d → Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
  | .inl (i, k) =>
      scalarPurificationLp
        ((positive i).isHermitian.eigenvalues k)
        ((positive i).eigenvalues_nonneg k)
  | .inr k =>
      scalarPurificationLp
        (hM.isHermitian.eigenvalues k)
        (hM.eigenvalues_nonneg k)

/--
The common purification subspace construction used in the quantum parallel-repetition argument.
-/
def commonPurificationSubspace
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    Submodule ℂ (Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :=
  Submodule.span ℂ
    (Set.range (commonPurificationGenerator F M positive hM))

theorem commonPurificationSubspace_finiteDimensional
    {ι d : Type*} [Finite ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    FiniteDimensional ℂ (commonPurificationSubspace F M positive hM) := by
  unfold commonPurificationSubspace
  exact FiniteDimensional.span_of_finite ℂ
    (Set.finite_range (commonPurificationGenerator F M positive hM))

theorem ensemble_scalarPurificationLp_mem_common
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (i : ι) (k : d) :
    scalarPurificationLp
        ((positive i).isHermitian.eigenvalues k)
        ((positive i).eigenvalues_nonneg k) ∈
      commonPurificationSubspace F M positive hM := by
  apply Submodule.subset_span
  exact ⟨Sum.inl (i, k), rfl⟩

theorem mean_scalarPurificationLp_mem_common
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (k : d) :
    scalarPurificationLp
        (hM.isHermitian.eigenvalues k)
        (hM.eigenvalues_nonneg k) ∈
      commonPurificationSubspace F M positive hM := by
  apply Submodule.subset_span
  exact ⟨Sum.inr k, rfl⟩

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/--
The spectral purification filter entry lp construction used in the quantum parallel-repetition
argument.
-/
def spectralPurificationFilterEntryLp
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i j : d) :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (((spectralPurificationFilter_memLp_two F hF).eval i).eval j).toLp
    (fun s : ℝ => spectralPurificationFilter F hF s i j)

theorem spectralPurificationFilterEntryLp_coeFn
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i j : d) :
    (spectralPurificationFilterEntryLp F hF i j : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi 0)]
        (fun s : ℝ => spectralPurificationFilter F hF s i j) :=
  (((spectralPurificationFilter_memLp_two F hF).eval i).eval j).coeFn_toLp

theorem spectralPurificationFilterEntryLp_eq_eigen_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i j : d) :
    spectralPurificationFilterEntryLp F hF i j =
      ∑ k : d,
        (((hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ) i k) *
          (star (hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ)) k j) •
        scalarPurificationLp
          (hF.isHermitian.eigenvalues k)
          (hF.eigenvalues_nonneg k) := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let coefficient : d → ℂ := fun k =>
    (U : Matrix d d ℂ) i k *
      star (U : Matrix d d ℂ) k j
  let generator : d → Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
    fun k => scalarPurificationLp
      (eigenvalue k) (hF.eigenvalues_nonneg k)
  apply Lp.ext
  have hentry := spectralPurificationFilterEntryLp_coeFn F hF i j
  have hsum := Lp.coeFn_fun_finsetSum
    Finset.univ (fun k : d => coefficient k • generator k)
  have hgenerator :
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ k : d,
          (coefficient k • generator k :
            Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) s =
            coefficient k *
              ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ) := by
    apply ae_all_iff.mpr
    intro k
    have hsmul := Lp.coeFn_smul (coefficient k) (generator k)
    have hscalar := scalarPurificationLp_coeFn
      (eigenvalue k) (hF.eigenvalues_nonneg k)
    filter_upwards [hsmul, hscalar] with s hs ht
    rw [hs]
    change
      coefficient k *
        (scalarPurificationLp (eigenvalue k)
          (hF.eigenvalues_nonneg k) : ℝ → ℂ) s = _
    rw [ht]
  filter_upwards [hentry, hsum, hgenerator] with s he hs hg
  rw [he, hs]
  change
    ((U : Matrix d d ℂ) *
      Matrix.diagonal (fun k =>
        ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ)) *
      star (U : Matrix d d ℂ)) i j =
      ∑ k : d, (coefficient k • generator k :
        Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) s
  simp_rw [hg]
  simp only [Matrix.diagonal, ofReal_div, ofReal_add, Matrix.mul_apply, of_apply, mul_comm,
    ite_mul, zero_mul, sum_ite_eq', Finset.mem_univ, ↓reduceIte, star_apply, RCLike.star_def,
    mul_assoc, coefficient]

theorem ensemble_spectralPurificationFilterEntryLp_mem_common
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (a : ι) (i j : d) :
    spectralPurificationFilterEntryLp (F a) (positive a) i j ∈
      commonPurificationSubspace F M positive hM := by
  rw [spectralPurificationFilterEntryLp_eq_eigen_sum]
  apply (commonPurificationSubspace F M positive hM).sum_mem
  intro k _
  apply (commonPurificationSubspace F M positive hM).smul_mem
  exact ensemble_scalarPurificationLp_mem_common
    F M positive hM a k

theorem mean_spectralPurificationFilterEntryLp_mem_common
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (i j : d) :
    spectralPurificationFilterEntryLp M hM i j ∈
      commonPurificationSubspace F M positive hM := by
  rw [spectralPurificationFilterEntryLp_eq_eigen_sum]
  apply (commonPurificationSubspace F M positive hM).sum_mem
  intro k _
  apply (commonPurificationSubspace F M positive hM).smul_mem
  exact mean_scalarPurificationLp_mem_common
    F M positive hM k

/--
The ensemble purification subspace entry construction used in the quantum parallel-repetition
argument.
-/
def ensemblePurificationSubspaceEntry
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (a : ι) (i j : d) :
    commonPurificationSubspace F M positive hM :=
  ⟨spectralPurificationFilterEntryLp (F a) (positive a) i j,
    ensemble_spectralPurificationFilterEntryLp_mem_common
      F M positive hM a i j⟩

private def meanPurificationSubspaceEntry
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (i j : d) :
    commonPurificationSubspace F M positive hM :=
  ⟨spectralPurificationFilterEntryLp M hM i j,
    mean_spectralPurificationFilterEntryLp_mem_common
      F M positive hM i j⟩

/--
The common purification orthonormal basis construction used in the quantum parallel-repetition
argument.
-/
noncomputable def commonPurificationOrthonormalBasis
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ
        (commonPurificationSubspace F M positive hM)))
      ℂ (commonPurificationSubspace F M positive hM) := by
  letI : FiniteDimensional ℂ
      (commonPurificationSubspace F M positive hM) :=
    commonPurificationSubspace_finiteDimensional F M positive hM
  exact stdOrthonormalBasis ℂ
    (commonPurificationSubspace F M positive hM)

/-- The matrix representation of finite purification. -/
noncomputable def finitePurificationMatrix
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) :
    Matrix
      (d × Fin (Module.finrank ℂ
        (commonPurificationSubspace F M positive hM))) d ℂ :=
  fun ik j =>
    (commonPurificationOrthonormalBasis F M positive hM).repr
      (ensemblePurificationSubspaceEntry F M positive hM a ik.1 j)
      ik.2

/-- The matrix representation of mean finite purification. -/
noncomputable def meanFinitePurificationMatrix
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    Matrix
      (d × Fin (Module.finrank ℂ
        (commonPurificationSubspace F M positive hM))) d ℂ :=
  fun ik j =>
    (commonPurificationOrthonormalBasis F M positive hM).repr
      (meanPurificationSubspaceEntry F M positive hM ik.1 j)
      ik.2

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem finitePurificationMatrix_gram_apply
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) (i j : d) :
    ((finitePurificationMatrix F M positive hM a).conjTranspose *
      finitePurificationMatrix F M positive hM a) i j =
      ∑ r : d,
        inner ℂ
          (ensemblePurificationSubspaceEntry F M positive hM a r i)
          (ensemblePurificationSubspaceEntry F M positive hM a r j) := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    finitePurificationMatrix, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  let b := commonPurificationOrthonormalBasis F M positive hM
  let u := ensemblePurificationSubspaceEntry
    F M positive hM a r i
  let v := ensemblePurificationSubspaceEntry
    F M positive hM a r j
  have hisometry := b.repr.inner_map_map u v
  change (∑ k, star (b.repr u k) * b.repr v k) =
    inner ℂ u v
  rw [← hisometry, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [RCLike.star_def, mul_comm, dotProduct, Pi.star_apply]

theorem ensemblePurificationSubspaceEntry_inner_eq_integral
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (a : ι) (r i j : d) :
    inner ℂ
        (ensemblePurificationSubspaceEntry F M positive hM a r i)
        (ensemblePurificationSubspaceEntry F M positive hM a r j) =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s r i) *
          spectralPurificationFilter (F a) (positive a) s r j := by
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hi := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r i
  have hj := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r j
  filter_upwards [hi, hj] with s hs ht
  change
    inner ℂ
      (spectralPurificationFilterEntryLp
        (F a) (positive a) r i s)
      (spectralPurificationFilterEntryLp
        (F a) (positive a) r j s) = _
  rw [hs, ht]
  simp only [RCLike.inner_apply, RCLike.star_def, mul_comm]

theorem finitePurificationMatrix_gram_eq_integral
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) :
    (finitePurificationMatrix F M positive hM a).conjTranspose *
        finitePurificationMatrix F M positive hM a =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s) *
          spectralPurificationFilter (F a) (positive a) s := by
  classical
  have hfilter := spectralPurificationFilter_memLp_two
    (F a) (positive a)
  have hmatrix := spectralPurificationFilter_gram_integrable
    (F a) (positive a)
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ =>
            (star (spectralPurificationFilter (F a) (positive a) s) *
              spectralPurificationFilter (F a) (positive a) s) i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  ext i j
  rw [finitePurificationMatrix_gram_apply]
  rw [show
    (∫ s in Ioi (0 : ℝ),
      star (spectralPurificationFilter (F a) (positive a) s) *
        spectralPurificationFilter (F a) (positive a) s) i j =
      (∫ s in Ioi (0 : ℝ),
        (star (spectralPurificationFilter (F a) (positive a) s) *
          spectralPurificationFilter (F a) (positive a) s) i) j from
        congrArg (fun row : d → ℂ => row j)
          (MeasureTheory.eval_integral hrows i)]
  rw [show
    (∫ s in Ioi (0 : ℝ),
      (star (spectralPurificationFilter (F a) (positive a) s) *
        spectralPurificationFilter (F a) (positive a) s) i) j =
      ∫ s in Ioi (0 : ℝ),
        (star (spectralPurificationFilter (F a) (positive a) s) *
          spectralPurificationFilter (F a) (positive a) s) i j from
        MeasureTheory.eval_integral (fun k => (hrows i).eval k) j]
  simp_rw [ensemblePurificationSubspaceEntry_inner_eq_integral]
  have hproduct (r : d) :
      Integrable
        (fun s : ℝ =>
          star (spectralPurificationFilter (F a) (positive a) s r i) *
            spectralPurificationFilter (F a) (positive a) s r j)
        (volume.restrict (Ioi 0)) :=
    (((hfilter.eval r).eval i).star).integrable_mul
      ((hfilter.eval r).eval j)
  rw [← integral_finsetSum Finset.univ (fun r _ => hproduct r)]
  apply integral_congr_ae
  filter_upwards with s
  simp only [RCLike.star_def, Matrix.mul_apply, star_apply]

theorem finitePurificationMatrix_gram
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) :
    (finitePurificationMatrix F M positive hM a).conjTranspose *
      finitePurificationMatrix F M positive hM a = F a := by
  rw [finitePurificationMatrix_gram_eq_integral]
  exact integral_spectralPurificationFilter_gram (F a) (positive a)

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem finitePurificationMatrix_difference_gram_apply
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) (i j : d) :
    ((finitePurificationMatrix F M positive hM a -
          meanFinitePurificationMatrix F M positive hM).conjTranspose *
        (finitePurificationMatrix F M positive hM a -
          meanFinitePurificationMatrix F M positive hM)) i j =
      ∑ r : d,
        inner ℂ
          (ensemblePurificationSubspaceEntry F M positive hM a r i -
            meanPurificationSubspaceEntry F M positive hM r i)
          (ensemblePurificationSubspaceEntry F M positive hM a r j -
            meanPurificationSubspaceEntry F M positive hM r j) := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sub_apply, finitePurificationMatrix,
    meanFinitePurificationMatrix, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  let b := commonPurificationOrthonormalBasis F M positive hM
  let u := ensemblePurificationSubspaceEntry
    F M positive hM a r i
  let u₀ := meanPurificationSubspaceEntry
    F M positive hM r i
  let v := ensemblePurificationSubspaceEntry
    F M positive hM a r j
  let v₀ := meanPurificationSubspaceEntry
    F M positive hM r j
  have hisometry := b.repr.inner_map_map (u - u₀) (v - v₀)
  change
    (∑ k, star (b.repr u k - b.repr u₀ k) *
      (b.repr v k - b.repr v₀ k)) =
      inner ℂ (u - u₀) (v - v₀)
  rw [← hisometry, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_sub, RCLike.star_def, mul_comm, dotProduct, map_sub, PiLp.sub_apply,
    WithLp.ofLp_sub, Pi.star_apply, Pi.sub_apply]

theorem purificationSubspaceEntry_difference_inner_eq_integral
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) (r i j : d) :
    inner ℂ
      (ensemblePurificationSubspaceEntry F M positive hM a r i -
        meanPurificationSubspaceEntry F M positive hM r i)
      (ensemblePurificationSubspaceEntry F M positive hM a r j -
        meanPurificationSubspaceEntry F M positive hM r j) =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s r i -
          spectralPurificationFilter M hM s r i) *
        (spectralPurificationFilter (F a) (positive a) s r j -
          spectralPurificationFilter M hM s r j) := by
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  let fi := spectralPurificationFilterEntryLp
    (F a) (positive a) r i
  let mi := spectralPurificationFilterEntryLp M hM r i
  let fj := spectralPurificationFilterEntryLp
    (F a) (positive a) r j
  let mj := spectralPurificationFilterEntryLp M hM r j
  have hsubi := Lp.coeFn_sub fi mi
  have hsubj := Lp.coeFn_sub fj mj
  have hfi := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r i
  have hmi := spectralPurificationFilterEntryLp_coeFn M hM r i
  have hfj := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r j
  have hmj := spectralPurificationFilterEntryLp_coeFn M hM r j
  filter_upwards [hsubi, hsubj, hfi, hmi, hfj, hmj]
    with s hi hj hfi' hmi' hfj' hmj'
  change inner ℂ ((fi - mi) s) ((fj - mj) s) = _
  rw [hi, hj]
  change inner ℂ (fi s - mi s) (fj s - mj s) = _
  change
    inner ℂ
      ((spectralPurificationFilterEntryLp
        (F a) (positive a) r i : ℝ → ℂ) s -
        (spectralPurificationFilterEntryLp M hM r i : ℝ → ℂ) s)
      ((spectralPurificationFilterEntryLp
        (F a) (positive a) r j : ℝ → ℂ) s -
        (spectralPurificationFilterEntryLp M hM r j : ℝ → ℂ) s) = _
  rw [hfi', hmi', hfj', hmj']
  simp only [RCLike.inner_apply, map_sub, star_sub, RCLike.star_def, mul_comm]

theorem finitePurificationMatrix_difference_gram_eq_integral
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) :
    (finitePurificationMatrix F M positive hM a -
        meanFinitePurificationMatrix F M positive hM).conjTranspose *
      (finitePurificationMatrix F M positive hM a -
        meanFinitePurificationMatrix F M positive hM) =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter M hM s) *
        (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter M hM s) := by
  classical
  have hdelta :
      MemLp (fun s : ℝ =>
        spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter M hM s)
        2 (volume.restrict (Ioi 0)) :=
    (spectralPurificationFilter_memLp_two (F a) (positive a)).sub
      (spectralPurificationFilter_memLp_two M hM)
  have hmatrix := spectralPurificationFilter_difference_gram_integrable
    (F a) M (positive a) hM
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ =>
            (star (spectralPurificationFilter (F a) (positive a) s -
                spectralPurificationFilter M hM s) *
              (spectralPurificationFilter (F a) (positive a) s -
                spectralPurificationFilter M hM s)) i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  ext i j
  rw [finitePurificationMatrix_difference_gram_apply]
  rw [show
    (∫ s in Ioi (0 : ℝ),
      star (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter M hM s) *
        (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter M hM s)) i j =
      (∫ s in Ioi (0 : ℝ),
        (star (spectralPurificationFilter (F a) (positive a) s -
            spectralPurificationFilter M hM s) *
          (spectralPurificationFilter (F a) (positive a) s -
            spectralPurificationFilter M hM s)) i) j from
        congrArg (fun row : d → ℂ => row j)
          (MeasureTheory.eval_integral hrows i)]
  rw [show
    (∫ s in Ioi (0 : ℝ),
      (star (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter M hM s) *
        (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter M hM s)) i) j =
      ∫ s in Ioi (0 : ℝ),
        (star (spectralPurificationFilter (F a) (positive a) s -
            spectralPurificationFilter M hM s) *
          (spectralPurificationFilter (F a) (positive a) s -
            spectralPurificationFilter M hM s)) i j from
        MeasureTheory.eval_integral (fun k => (hrows i).eval k) j]
  simp_rw [purificationSubspaceEntry_difference_inner_eq_integral]
  have hproduct (r : d) :
      Integrable
        (fun s : ℝ =>
          star (spectralPurificationFilter (F a) (positive a) s r i -
            spectralPurificationFilter M hM s r i) *
            (spectralPurificationFilter (F a) (positive a) s r j -
              spectralPurificationFilter M hM s r j))
        (volume.restrict (Ioi 0)) :=
    (((hdelta.eval r).eval i).star).integrable_mul
      ((hdelta.eval r).eval j)
  rw [← integral_finsetSum Finset.univ (fun r _ => hproduct r)]
  apply integral_congr_ae
  filter_upwards with s
  simp only [star_sub, RCLike.star_def, Matrix.mul_apply, Matrix.sub_apply, star_apply]

theorem weighted_finitePurificationMatrix_difference_gram
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ)
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    (∑ a : ι, weight a •
      ((finitePurificationMatrix F M positive hM a -
          meanFinitePurificationMatrix F M positive hM).conjTranspose *
        (finitePurificationMatrix F M positive hM a -
          meanFinitePurificationMatrix F M positive hM))) =
      ∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s := by
  classical
  have hterm (a : ι) :
      Integrable
        (fun s : ℝ => weight a •
          (star (spectralPurificationFilter (F a) (positive a) s -
              spectralPurificationFilter M hM s) *
            (spectralPurificationFilter (F a) (positive a) s -
              spectralPurificationFilter M hM s)))
        (volume.restrict (Ioi 0)) :=
    (spectralPurificationFilter_difference_gram_integrable
      (F a) M (positive a) hM).smul (weight a)
  simp_rw [finitePurificationMatrix_difference_gram_eq_integral]
  unfold weightedSpectralFilterVariance
  rw [integral_finsetSum Finset.univ (fun a _ => hterm a)]
  simp_rw [integral_smul]

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem finite_purification_log_entropy_jensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef) :
    let hM : M.PosSemidef := by
      rw [← mean]
      exact weighted_positive_matrix_mean weight F nonnegative positive
    ((∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∑ i : ι, weight i •
        ((finitePurificationMatrix F M positive hM i -
            meanFinitePurificationMatrix F M positive hM).conjTranspose *
          (finitePurificationMatrix F M positive hM i -
            meanFinitePurificationMatrix F M positive hM)))).PosSemidef := by
  dsimp
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  have h := exact_matrix_log_entropy_filter_jensen
    weight F M nonnegative normalized mean positive
  change
    ((∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s)).PosSemidef at h
  rw [← weighted_finitePurificationMatrix_difference_gram
    weight F M positive hM] at h
  exact h

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

private def matrixPurificationVector
    {d : Type*}
    (K : Matrix d d ℂ) : EuclideanSpace ℂ (d × d) :=
  toLp 2 (Matrix.vec K)

theorem matrixPurificationVector_norm_sq
    {d : Type*} [Fintype d]
    (K : Matrix d d ℂ) :
    ‖matrixPurificationVector K‖ ^ 2 =
      (Matrix.trace (Matrix.conjTranspose K * K)).re := by
  calc
    ‖matrixPurificationVector K‖ ^ 2 =
        (⟪matrixPurificationVector K,
          matrixPurificationVector K⟫_ℂ).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) (matrixPurificationVector K)
    _ = (star (Matrix.vec K) ⬝ᵥ Matrix.vec K).re := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (Matrix.vec K ⬝ᵥ star (Matrix.vec K)).re =
          (star (Matrix.vec K) ⬝ᵥ Matrix.vec K).re
      rw [dotProduct_comm]
    _ = (Matrix.trace (Matrix.conjTranspose K * K)).re := by
      rw [Matrix.star_vec_dotProduct_vec]

private def strategyPurificationShuffle
    (dA dB : Type) :
    ((dA × (dA × dB)) × dB) ≃ ((dA × dB) × (dA × dB)) where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv := by
    rintro ⟨⟨a, k⟩, b⟩
    rfl
  right_inv := by
    rintro ⟨k, ⟨a, b⟩⟩
    rfl

/-- The state vector representing strategy purification. -/
def strategyPurificationVector
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) :
    EuclideanSpace ℂ ((S.Alice × (S.Alice × S.Bob)) × S.Bob) :=
  toLp 2
    (fun q =>
      Matrix.vec (spectralSupportSqrt S.state.matrix S.state.positive)
        (strategyPurificationShuffle S.Alice S.Bob q))

theorem strategyPurificationVector_norm_sq
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) :
    ‖strategyPurificationVector S‖ ^ 2 =
      ‖matrixPurificationVector
          (spectralSupportSqrt S.state.matrix S.state.positive)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa only [strategyPurificationVector, vec, matrixPurificationVector] using
    Equiv.sum_comp (strategyPurificationShuffle S.Alice S.Bob)
      (fun q : (S.Alice × S.Bob) × (S.Alice × S.Bob) =>
        ‖Matrix.vec
          (spectralSupportSqrt S.state.matrix S.state.positive) q‖ ^ 2)

theorem strategyPurificationVector_norm
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) :
    ‖strategyPurificationVector S‖ = 1 := by
  let K := spectralSupportSqrt S.state.matrix S.state.positive
  have h_hermitian : (Matrix.conjTranspose K) = K :=
    (spectralSupportFunctional_isHermitian
      S.state.matrix S.state.positive Real.sqrt).eq
  have h_sq : ‖strategyPurificationVector S‖ ^ 2 = 1 := by
    calc
      ‖strategyPurificationVector S‖ ^ 2 =
          ‖matrixPurificationVector K‖ ^ 2 :=
            strategyPurificationVector_norm_sq S
      _ = (Matrix.trace (Matrix.conjTranspose K * K)).re :=
            matrixPurificationVector_norm_sq K
      _ = (Matrix.trace S.state.matrix).re := by
            rw [h_hermitian]
            change
              (Matrix.trace
                (spectralSupportSqrt S.state.matrix S.state.positive *
                  spectralSupportSqrt S.state.matrix S.state.positive)).re =
                (Matrix.trace S.state.matrix).re
            rw [spectralSupportSqrt_sq]
      _ = 1 := by rw [S.state.trace_one]; norm_num
  nlinarith [norm_nonneg (strategyPurificationVector S)]

theorem reindexedMatrixQuadratic
    {d e : Type*} [Fintype d] [Fintype e]
    [DecidableEq e]
    (φ : e ≃ d) (M : Matrix d d ℂ) (v : d → ℂ) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := e) (𝕜 := ℂ)
        (M.submatrix φ φ))
      (toLp 2 (v ∘ φ)) =
      (star v ⬝ᵥ M.mulVec v).re := by
  classical
  unfold quadraticExpectation
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change
    (((M.submatrix φ φ).mulVec (v ∘ φ)) ⬝ᵥ
      star (v ∘ φ)).re = (star v ⬝ᵥ M.mulVec v).re
  have h_mul :
      (M.submatrix φ φ).mulVec (v ∘ φ) =
        M.mulVec v ∘ φ := by
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using
      Matrix.submatrix_mulVec_equiv M (v ∘ φ) φ φ
  have h_star : star (v ∘ φ) = star v ∘ φ := by
    rfl
  rw [h_mul, h_star, comp_equiv_dotProduct_comp_equiv]
  rw [dotProduct_comm]

/-- The positive operator-valued measurement implementing purification alice. -/
def purificationAlicePOVM
    {ι d k : Type*} [Fintype ι]
    [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k]
    (P : POVM ι d) : POVM ι (d × k) where
  effect a := P.effect a ⊗ₖ (1 : Matrix k k ℂ)
  positive a := (P.positive a).kronecker Matrix.PosSemidef.one
  complete := by
    classical
    calc
      (∑ a : ι, P.effect a ⊗ₖ (1 : Matrix k k ℂ)) =
          (∑ a : ι, P.effect a) ⊗ₖ (1 : Matrix k k ℂ) := by
            ext ⟨i, u⟩ ⟨j, v⟩
            simp only [Matrix.sum_apply, kroneckerMap_apply, sum_mul]
      _ = 1 := by
        rw [P.complete]
        exact Matrix.one_kronecker_one

theorem purificationJointEffect_submatrix
    {dA dB : Type}
    [DecidableEq dA] [DecidableEq dB]
    (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    (A ⊗ₖ (1 : Matrix (dA × dB) (dA × dB) ℂ)) ⊗ₖ B =
      ((1 : Matrix (dA × dB) (dA × dB) ℂ) ⊗ₖ
        (A ⊗ₖ B)).submatrix
          (strategyPurificationShuffle dA dB)
          (strategyPurificationShuffle dA dB) := by
  classical
  ext ⟨⟨a, k⟩, b⟩ ⟨⟨a', k'⟩, b'⟩
  simp only [kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    strategyPurificationShuffle, Equiv.coe_fn_mk, submatrix_apply, one_mul]

theorem strategyPurificationVector_quadratic
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G)
    (EA : Matrix S.Alice S.Alice ℂ)
    (EB : Matrix S.Bob S.Bob ℂ) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (S.Alice × (S.Alice × S.Bob)) × S.Bob) (𝕜 := ℂ)
        ((EA ⊗ₖ (1 : Matrix (S.Alice × S.Bob)
          (S.Alice × S.Bob) ℂ)) ⊗ₖ EB))
      (strategyPurificationVector S) =
      (Matrix.trace
        (S.state.matrix * (EA ⊗ₖ EB))).re := by
  let K := spectralSupportSqrt S.state.matrix S.state.positive
  let E := EA ⊗ₖ EB
  let φ := strategyPurificationShuffle S.Alice S.Bob
  have h_hermitian : (Matrix.conjTranspose K) = K :=
    (spectralSupportFunctional_isHermitian
      S.state.matrix S.state.positive Real.sqrt).eq
  have h_lift := purificationJointEffect_submatrix EA EB
  change
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (S.Alice × (S.Alice × S.Bob)) × S.Bob) (𝕜 := ℂ)
        ((EA ⊗ₖ (1 : Matrix (S.Alice × S.Bob)
          (S.Alice × S.Bob) ℂ)) ⊗ₖ EB))
      (toLp 2 (Matrix.vec K ∘ φ)) =
      (Matrix.trace (S.state.matrix * E)).re
  rw [h_lift]
  rw [reindexedMatrixQuadratic φ
    ((1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ) ⊗ₖ E)
    (Matrix.vec K)]
  have h_vec :
      Matrix.mulVec
        ((1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ) ⊗ₖ E)
        (Matrix.vec K) =
        Matrix.vec (E * K) := by
    exact (Matrix.vec_mul_eq_mulVec E K).symm
  rw [h_vec, Matrix.star_vec_dotProduct_vec]
  rw [h_hermitian]
  congr 1
  calc
    Matrix.trace (K * (E * K)) =
      Matrix.trace (K * E * K) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (K * K * E) := by
      rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (S.state.matrix * E) := by
      change
        Matrix.trace
          (spectralSupportSqrt S.state.matrix S.state.positive *
            spectralSupportSqrt S.state.matrix S.state.positive * E) = _
      rw [spectralSupportSqrt_sq]

/-- The strategy implementing purified. -/
def purifiedStrategy
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) : Strategy G :=
  pureVectorStrategy G (strategyPurificationVector S)
    (strategyPurificationVector_norm S)
    (fun x => purificationAlicePOVM (S.aliceMeasurement x))
    S.bobMeasurement

theorem purifiedStrategy_outcomeProbability
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G)
    (x : X) (y : Y) (a : A) (b : B) :
    (purifiedStrategy S).outcomeProbability x y a b =
      S.outcomeProbability x y a b := by
  unfold purifiedStrategy
  rw [pureVectorStrategy_outcomeProbability]
  exact strategyPurificationVector_quadratic S
    ((S.aliceMeasurement x).effect a)
    ((S.bobMeasurement y).effect b)

theorem purifiedStrategy_winProbability
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) :
    (purifiedStrategy S).winProbability = S.winProbability := by
  unfold Strategy.winProbability
  simp_rw [purifiedStrategy_outcomeProbability]

theorem rectangular_matrix_mulVec_norm_sq
    {d e : Type*} [Fintype d] [Fintype e] [DecidableEq d]
    (K : Matrix e d ℂ) (z : EuclideanSpace ℂ d) :
    ‖toLp 2 (K.mulVec (ofLp z))‖ ^ 2 =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
          (K.conjTranspose * K)) z := by
  calc
    ‖toLp 2 (K.mulVec (ofLp z))‖ ^ 2 =
        (⟪toLp 2 (K.mulVec (ofLp z)),
          toLp 2 (K.mulVec (ofLp z))⟫_ℂ).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ)
        (toLp 2 (K.mulVec (ofLp z)))
    _ = (star (K.mulVec (ofLp z)) ⬝ᵥ
          K.mulVec (ofLp z)).re := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (K.mulVec (ofLp z) ⬝ᵥ star (K.mulVec (ofLp z))).re = _
      rw [dotProduct_comm]
    _ = (star (ofLp z) ⬝ᵥ
          (K.conjTranspose * K).mulVec (ofLp z)).re := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
        Matrix.mulVec_mulVec]
    _ = quadraticExpectation
          (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
            (K.conjTranspose * K)) z := by
      unfold quadraticExpectation
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (star (ofLp z) ⬝ᵥ
            (K.conjTranspose * K).mulVec (ofLp z)).re =
          ((K.conjTranspose * K).mulVec (ofLp z) ⬝ᵥ
            star (ofLp z)).re
      rw [dotProduct_comm]

/-- The matrix representation of finite local purification joint. -/
def finiteLocalPurificationJointMatrix
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    Matrix ((eA × (S.Alice × S.Bob)) × eB)
      ((S.Alice × (S.Alice × S.Bob)) × S.Bob) ℂ :=
  (KA ⊗ₖ
    (1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ)) ⊗ₖ KB

/-- The state vector representing finite local purification. -/
def finiteLocalPurificationVector
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    EuclideanSpace ℂ ((eA × (S.Alice × S.Bob)) × eB) :=
  toLp 2
    ((finiteLocalPurificationJointMatrix S KA KB).mulVec
      (ofLp (strategyPurificationVector S)))

theorem finiteLocalPurificationJointMatrix_gram
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    (finiteLocalPurificationJointMatrix S KA KB).conjTranspose *
        finiteLocalPurificationJointMatrix S KA KB =
      ((KA.conjTranspose * KA) ⊗ₖ
        (1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ)) ⊗ₖ
        (KB.conjTranspose * KB) := by
  unfold finiteLocalPurificationJointMatrix
  rw [Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  simp only [conjTranspose_one, mul_one]

theorem finiteLocalPurificationVector_norm_sq
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    ‖finiteLocalPurificationVector S KA KB‖ ^ 2 =
      (Matrix.trace
        (S.state.matrix *
          ((KA.conjTranspose * KA) ⊗ₖ
            (KB.conjTranspose * KB)))).re := by
  unfold finiteLocalPurificationVector
  rw [rectangular_matrix_mulVec_norm_sq,
    finiteLocalPurificationJointMatrix_gram]
  exact strategyPurificationVector_quadratic S
    (KA.conjTranspose * KA) (KB.conjTranspose * KB)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder InnerProductSpace

theorem dSVUniformDensityMixedProtocolLocalAction_norm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ (ι × ι)) :
    ‖toLp 2
        (((U : Matrix ι ι ℂ) ⊗ₖ
          (V : Matrix ι ι ℂ)).mulVec (ofLp z))‖ = ‖z‖ := by
  classical
  let M : Matrix (ι × ι) (ι × ι) ℂ :=
    (U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix ι ι ℂ)
  have unitary : M ∈ Matrix.unitaryGroup (ι × ι) ℂ :=
    Matrix.kronecker_mem_unitary U.property V.property
  have gram : M.conjTranspose * M = 1 := by
    simpa only [star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp unitary)
  have squared :
      ‖toLp 2 (M.mulVec (ofLp z))‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [rectangular_matrix_mulVec_norm_sq, gram]
    simp only [quadraticExpectation, map_one, one_apply_eq_self, inner_self_eq_norm_sq_to_K,
      coe_algebraMap, ← ofReal_pow, ofReal_re]
  change ‖toLp 2 (M.mulVec (ofLp z))‖ = ‖z‖
  nlinarith [norm_nonneg (toLp 2 (M.mulVec (ofLp z))),
    norm_nonneg z]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The DSV uniform density physical async sigma continuation construction used in the quantum
parallel-repetition argument.
-/
def dSVUniformDensityPhysicalAsyncSigmaContinuation
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U V : ι → Matrix.unitaryGroup κ ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : ι, κ) × (Σ _ : ι, κ))) :
    EuclideanSpace ℂ ((Σ _ : ι, κ) × (Σ _ : ι, κ)) := by
  classical
  let A := coherentSharedRandomControlledUnitary U
  let B := coherentSharedRandomControlledUnitary V
  exact toLp 2 ((A.val ⊗ₖ B.val).mulVec (ofLp z))

theorem dSVUniformDensityPhysicalAsyncSigmaContinuation_norm
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U V : ι → Matrix.unitaryGroup κ ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : ι, κ) × (Σ _ : ι, κ))) :
    ‖dSVUniformDensityPhysicalAsyncSigmaContinuation U V z‖ =
      ‖z‖ := by
  simpa only [dSVUniformDensityPhysicalAsyncSigmaContinuation]
    using dSVUniformDensityMixedProtocolLocalAction_norm
      (coherentSharedRandomControlledUnitary U)
      (coherentSharedRandomControlledUnitary V) z

theorem dSVUniformDensityFirstAcceptFinitePrefix
    {L : ℕ} (s : Finset (Fin L)) (j : Fin L) :
    (if h : s.Nonempty then (s.min' h).succ else
      (0 : Fin (L + 1))) = j.succ ↔
      j ∈ s ∧ ∀ i : Fin L, i < j → i ∉ s := by
  classical
  constructor
  · intro selected
    by_cases nonempty : s.Nonempty
    · have minimum : s.min' nonempty = j := by
        have equal : (s.min' nonempty).succ = j.succ := by
          simpa only [Fin.succ_inj, nonempty, ↓reduceDIte] using selected
        exact Fin.succ_injective L equal
      constructor
      · rw [← minimum]
        exact Finset.min'_mem s nonempty
      · intro i before contained
        have least : s.min' nonempty ≤ i := Finset.min'_le s i contained
        rw [minimum] at least
        exact (not_le_of_gt before) least
    · have impossible : (0 : Fin (L + 1)) = j.succ := by
        simpa only [nonempty, ↓reduceDIte] using selected
      exact False.elim (Fin.succ_ne_zero j impossible.symm)
  · rintro ⟨accepted, prior⟩
    have nonempty : s.Nonempty := ⟨j, accepted⟩
    have minimum : s.min' nonempty = j := by
      apply (Finset.min'_eq_iff s nonempty j).mpr
      refine ⟨accepted, ?_⟩
      intro i contained
      exact le_of_not_gt (fun before => prior i before contained)
    simp only [nonempty, ↓reduceDIte, minimum]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


theorem dSVUniformDensityFirstAcceptControlledTensor_inv_apply
    {Ω ι β : Type*}
    [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : Ω → ι → Matrix.unitaryGroup β ℂ)
    (ω ν : Ω) (q r : ι → β) :
    (((controlledFiniteTensorLocalUnitary U)⁻¹ :
      Matrix.unitaryGroup (Σ _ : Ω, (ι → β)) ℂ) :
      Matrix (Σ _ : Ω, (ι → β)) (Σ _ : Ω, (ι → β)) ℂ)
      ⟨ω, q⟩ ⟨ν, r⟩ =
      if ω = ν then
        ∏ i : ι, star ((U ω i : Matrix β β ℂ) (r i) (q i))
      else 0 := by
  classical
  change
    star ((controlledFiniteTensorLocalUnitary U :
      Matrix (Σ _ : Ω, (ι → β)) (Σ _ : Ω, (ι → β)) ℂ)
      ⟨ν, r⟩ ⟨ω, q⟩) = _
  rw [controlledFiniteTensorLocalUnitary_apply]
  by_cases same : ω = ν
  · subst ν
    simp only [↓reduceIte, star_prod, RCLike.star_def]
  · have reversed : ν ≠ ω := Ne.symm same
    simp only [reversed, ↓reduceIte, star_zero, same]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem coherentSharedRandomControlledUnitary_inv
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : ι → Matrix.unitaryGroup κ ℂ) :
    (coherentSharedRandomControlledUnitary U)⁻¹ =
      coherentSharedRandomControlledUnitary
        (fun i => (U i)⁻¹) := by
  classical
  apply Subtype.ext
  ext ⟨i, x⟩ ⟨j, y⟩
  change
    star ((coherentSharedRandomControlledUnitary U :
      Matrix (Σ _ : ι, κ) (Σ _ : ι, κ) ℂ) ⟨j, y⟩ ⟨i, x⟩) =
      (coherentSharedRandomControlledUnitary
        (fun i => (U i)⁻¹) :
        Matrix (Σ _ : ι, κ) (Σ _ : ι, κ) ℂ) ⟨i, x⟩ ⟨j, y⟩
  by_cases same : i = j
  · subst j
    simp only [coherentSharedRandomControlledUnitary, blockDiagonal'_apply, ↓reduceDIte, cast_eq,
      RCLike.star_def, UnitaryGroup.inv_val, star_apply]
  · have reversed : j ≠ i := Ne.symm same
    simp only [coherentSharedRandomControlledUnitary, blockDiagonal'_apply, reversed, ↓reduceDIte,
      star_zero, UnitaryGroup.inv_val, same]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

theorem dSVUniformDensityPhysicalAsync_doubleProductSum
    {ι β γ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [Fintype γ]
    (f : ι → β → γ → ℝ) :
    (∑ x : ι → β, ∑ y : ι → γ,
      ∏ i : ι, f i (x i) (y i)) =
      ∏ i : ι, ∑ a : β, ∑ b : γ, f i a b := by
  classical
  calc
    (∑ x : ι → β, ∑ y : ι → γ,
      ∏ i : ι, f i (x i) (y i)) =
        ∑ x : ι → β,
          ∏ i : ι, ∑ b : γ, f i (x i) b := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum
        (fun i : ι => fun b : γ => f i (x i) b)).symm
    _ = ∏ i : ι, ∑ a : β, ∑ b : γ, f i a b :=
      (Fintype.prod_sum
        (fun i : ι => fun a : β => ∑ b : γ, f i a b)).symm

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem spectralPartitionPOVM_effect_eq_spectralDiagonal
    {κ ι : Type*}
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (F : Matrix ι ι ℂ) (positive : F.PosSemidef)
    (bin : ι → κ) (outcome : κ) :
    (spectralPartitionPOVM F positive bin).effect outcome =
      spectralConjugationCLM positive.isHermitian.eigenvectorUnitary
        (Matrix.diagonal fun i : ι =>
          if bin i = outcome then (1 : ℂ) else 0) := by
  classical
  let selected : Finset ι :=
    Finset.univ.filter fun i : ι => bin i = outcome
  have diagonal :
      (∑ i ∈ selected,
        Matrix.diagonal (Pi.single i (1 : ℂ))) =
        Matrix.diagonal fun i : ι =>
          if bin i = outcome then (1 : ℂ) else 0 := by
    ext i j
    by_cases same : i = j
    · subst j
      simp only [Matrix.sum_apply, diagonal_apply_eq, Pi.single_apply, sum_ite_eq, mem_filter,
        mem_univ, true_and, selected]
    · simp only [Matrix.sum_apply, ne_eq, same, not_false_eq_true, diagonal_apply_ne,
        sum_const_zero]
  change
    (∑ i ∈ selected,
      spectralConjugationCLM positive.isHermitian.eigenvectorUnitary
        (Matrix.diagonal (Pi.single i (1 : ℂ)))) = _
  rw [← map_sum, diagonal]

theorem dSVUniformDensityPhysicalSpectralAliceCopy_inv
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    (dSVUniformDensityAliceHistorySpectralCopy
      (N := N) ξ)⁻¹ =
      coherentSharedRandomControlledUnitary
        (fun _ : Fin N =>
          dSVUniformDensityThresholdLeftBobBasis ξ) := by
  unfold dSVUniformDensityAliceHistorySpectralCopy
  rw [coherentSharedRandomControlledUnitary_inv]
  simp only [inv_inv]

theorem dSVUniformDensityPhysicalSpectralAliceCopy_transpose
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    (dSVUniformDensityAliceHistorySpectralCopy
      (N := N) ξ : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
      (dSVUniformDensityBobHistoryCopyBasis
        (N := N) ξ : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  classical
  change
    (Matrix.blockDiagonal'
      (fun _ : Fin N =>
        (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
          Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ))).transpose =
      Matrix.blockDiagonal'
        (fun _ : Fin N =>
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis ξ) :
            Matrix (Fin d) (Fin d) ℂ))
  rw [Matrix.blockDiagonal'_transpose]
  apply congrArg Matrix.blockDiagonal'
  funext k
  ext i j
  rfl

theorem dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    ((((dSVUniformDensityAliceHistorySpectralCopy
      (N := N) ξ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).transpose =
      (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ξ)⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  calc
    _ = (dSVUniformDensityAliceHistorySpectralCopy
      (N := N) ξ : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose.conjTranspose := by
          ext i j
          rfl
    _ = (dSVUniformDensityBobHistoryCopyBasis
      (N := N) ξ : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).conjTranspose := by
          rw [dSVUniformDensityPhysicalSpectralAliceCopy_transpose]
    _ = _ := by
          rfl

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


attribute [local instance] Classical.propDecidable

theorem dSVUniformDensityPhysicalMatched_doubleTensorSourceFactor
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β]
    (A B : ι → Matrix β β ℂ)
    (source : β × β → ℂ)
    (a b : ι → β) :
    (∑ x : ι → β, ∑ y : ι → β,
      (∏ i : ι, A i (a i) (x i)) *
      (∏ i : ι, B i (b i) (y i)) *
      (∏ i : ι, source (x i, y i))) =
      ∏ i : ι, ∑ x : β, ∑ y : β,
        A i (a i) x * B i (b i) y * source (x, y) := by
  classical
  calc
    _ = ∑ x : ι → β, ∑ y : ι → β,
        ∏ i : ι,
          (A i (a i) (x i) * B i (b i) (y i) * source (x i, y i)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ = ∑ x : ι → β,
        ∏ i : ι, ∑ y : β,
          (A i (a i) (x i) * B i (b i) y * source (x i, y)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum fun i : ι => fun y : β =>
        A i (a i) (x i) * B i (b i) y * source (x i, y)).symm
    _ = _ :=
      (Fintype.prod_sum fun i : ι => fun x : β =>
        ∑ y : β, A i (a i) x * B i (b i) y * source (x, y)).symm

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The DSV uniform density corrected matched sigma weighted residual construction used in the
quantum parallel-repetition argument.
-/
def dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
    {H : Type*} {n : ℕ}
    (history : EuclideanSpace ℂ (H × H))
    (work : H → H → EuclideanSpace ℂ (Fin n × Fin n)) :
    EuclideanSpace ℂ
      ((Σ _ : H, Fin n) × (Σ _ : H, Fin n)) :=
  toLp 2 fun q : (Σ _ : H, Fin n) × (Σ _ : H, Fin n) =>
    history (q.1.1, q.2.1) * work q.1.1 q.2.1 (q.1.2, q.2.2)

theorem dSVUniformDensityCorrectedMatchedSigmaWeightedResidual_distance_sq
    {H : Type*} [Fintype H] {n : ℕ}
    (history : EuclideanSpace ℂ (H × H))
    (work target : H → H → EuclideanSpace ℂ (Fin n × Fin n)) :
    ‖dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history work -
      dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history target‖ ^ 2 =
      ∑ a : H, ∑ b : H,
        ‖history (a, b)‖ ^ 2 * ‖work a b - target a b‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_sigma]
  change
    (∑ a : H, ∑ i : Fin n,
      ∑ b : H, ∑ j : Fin n,
        ‖history (a, b) * work a b (i, j) -
          history (a, b) * target a b (i, j)‖ ^ 2) = _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change
    ‖history (a, b) * work a b (i, j) -
      history (a, b) * target a b (i, j)‖ ^ 2 =
      ‖history (a, b)‖ ^ 2 *
        ‖work a b (i, j) - target a b (i, j)‖ ^ 2
  rw [← mul_sub, norm_mul, mul_pow]

theorem dSVUniformDensityCorrectedMatchedSigmaWeightedResidual_controlled
    {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}
    (history : EuclideanSpace ℂ (H × H))
    (work : H → H → EuclideanSpace ℂ (Fin n × Fin n))
    (U V : H → Matrix.unitaryGroup (Fin n) ℂ) :
    dSVUniformDensityPhysicalAsyncSigmaContinuation
        U V
        (dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
          history work) =
      dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history (fun a b =>
          localUnitaryAction (U a) (V b) (work a b)) := by
  classical
  ext ⟨⟨a, i⟩, ⟨b, j⟩⟩
  simp only [dSVUniformDensityPhysicalAsyncSigmaContinuation,
    coherentSharedRandomControlledUnitary, dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    mulVec, dotProduct, kroneckerMap_apply, blockDiagonal'_apply, cast_eq, dite_eq_ite, mul_ite,
    ite_mul, zero_mul, mul_comm, mul_zero, ite_self, mul_assoc, Fintype.sum_prod_type,
    Fintype.sum_sigma, sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, ↓reduceIte,
    localUnitaryAction]
  simp_rw [Finset.mul_sum]

theorem
    dSVUniformDensityCorrectedMatchedSigmaControlledReset_distance_sq
    {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}
    (history : EuclideanSpace ℂ (H × H))
    (work target : H → H → EuclideanSpace ℂ (Fin n × Fin n))
    (U V : H → Matrix.unitaryGroup (Fin n) ℂ) :
    ‖dSVUniformDensityPhysicalAsyncSigmaContinuation U V
        (dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
          history work) -
      dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history target‖ ^ 2 =
      ∑ a : H, ∑ b : H,
        ‖history (a, b)‖ ^ 2 *
          ‖localUnitaryAction
              (U a) (V b) (work a b) - target a b‖ ^ 2 := by
  rw [dSVUniformDensityCorrectedMatchedSigmaWeightedResidual_controlled,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual_distance_sq]

end

section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The DSV density rational projective threshold bin construction used in the quantum parallel-
repetition argument.
-/
def dSVDensityRationalProjectiveThresholdBin
    (w : ℝ) (N : ℕ) (k : Fin N) (a : ℝ) : Bool :=
  decide (dSVUniformDensityThresholdGrid N k ≤
    dSVRationalSoftPass w a)

/--
The positive operator-valued measurement implementing DSV density rational projective threshold.
-/
def dSVDensityRationalProjectiveThresholdPOVM
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℝ) (N : ℕ) (k : Fin N)
    (F : Matrix ι ι ℂ) (positive : F.PosSemidef) : POVM Bool ι :=
  spectralPartitionPOVM F positive
    (fun i : ι => dSVDensityRationalProjectiveThresholdBin
      w N k (positive.isHermitian.eigenvalues i))

theorem dSVDensityRationalProjectiveThresholdPOVM_projective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℝ) (N : ℕ) (k : Fin N)
    (F : Matrix ι ι ℂ) (positive : F.PosSemidef) (outcome : Bool) :
    (dSVDensityRationalProjectiveThresholdPOVM
      w N k F positive).effect outcome *
      (dSVDensityRationalProjectiveThresholdPOVM
        w N k F positive).effect outcome =
      (dSVDensityRationalProjectiveThresholdPOVM
        w N k F positive).effect outcome := by
  exact spectralPartitionPOVM_projective F positive
    (fun i : ι => dSVDensityRationalProjectiveThresholdBin
      w N k (positive.isHermitian.eigenvalues i)) outcome

/--
The positive operator-valued measurement implementing DSV density rational left projective
threshold.
-/
def dSVDensityRationalLeftProjectiveThresholdPOVM
    {d : ℕ} (w : ℝ) (N : ℕ) (k : Fin N)
    (ξ : BipartiteUnitVector d) : POVM Bool (Fin d) :=
  dSVDensityRationalProjectiveThresholdPOVM w N k
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ)

/--
The DSV density rational left projective threshold atom mismatch construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalLeftProjectiveThresholdAtomMismatch
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG := dSVSoftBobLeftReducedDensity_posSemidef ζ
  ∑ i : Fin d, ∑ j : Fin d,
    spectralAtomOverlap F G hF hG i j *
      dSVUniformDensityThresholdMismatch N
        (dSVRationalSoftPass w
          (hF.isHermitian.eigenvalues i))
        (dSVRationalSoftPass w
          (hG.isHermitian.eigenvalues j))

theorem
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch_le_discrepancy
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ ≤
      dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ / w +
        (d : ℝ) / N := by
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF : F.PosSemidef :=
    dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG : G.PosSemidef :=
    dSVSoftBobLeftReducedDensity_posSemidef ζ
  have overlap_mass :
      (∑ i : Fin d, ∑ j : Fin d,
        spectralAtomOverlap F G hF hG i j) = (d : ℝ) := by
    simp_rw [spectralAtomOverlap_sum_right]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have discrepancy :
      (∑ i : Fin d, ∑ j : Fin d,
        |hF.isHermitian.eigenvalues i -
          hG.isHermitian.eigenvalues j| *
            spectralAtomOverlap F G hF hG i j) =
        dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ := by
    unfold dSVUniformLeftDensitySpectralAtomDiscrepancy
      dSVUniformLeftDensitySchmidtCoefficient
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Real.sq_sqrt ((dSVSoftBobLeftReducedDensity_posSemidef ξ).eigenvalues_nonneg i),
      Real.sq_sqrt ((dSVSoftBobLeftReducedDensity_posSemidef ζ).eigenvalues_nonneg j), F, G]
  calc
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ ≤
      ∑ i : Fin d, ∑ j : Fin d,
        spectralAtomOverlap F G hF hG i j *
          (|hF.isHermitian.eigenvalues i -
            hG.isHermitian.eigenvalues j| / w + 1 / (N : ℝ)) := by
      unfold dSVDensityRationalLeftProjectiveThresholdAtomMismatch
      change
        (∑ i : Fin d, ∑ j : Fin d,
          spectralAtomOverlap F G hF hG i j *
            dSVUniformDensityThresholdMismatch N
              (dSVRationalSoftPass w
                (hF.isHermitian.eigenvalues i))
              (dSVRationalSoftPass w
                (hG.isHermitian.eigenvalues j))) ≤ _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _
        (spectralAtomOverlap_nonneg F G hF hG i j)
      exact (dSVUniformDensityThresholdMismatch_le grid _ _).trans
        (by simpa only [one_div, add_comm, add_le_add_iff_left] using
          (add_le_add_right
            (dSVRationalSoftPass_lipschitz width
              (hF.eigenvalues_nonneg i) (hG.eigenvalues_nonneg j))
            (1 / (N : ℝ))))
    _ = (∑ i : Fin d, ∑ j : Fin d,
          |hF.isHermitian.eigenvalues i -
            hG.isHermitian.eigenvalues j| *
              spectralAtomOverlap F G hF hG i j) / w +
        (1 / (N : ℝ)) *
          (∑ i : Fin d, ∑ j : Fin d,
            spectralAtomOverlap F G hF hG i j) := by
      calc
        (∑ i : Fin d, ∑ j : Fin d,
          spectralAtomOverlap F G hF hG i j *
            (|hF.isHermitian.eigenvalues i -
              hG.isHermitian.eigenvalues j| / w + 1 / (N : ℝ))) =
          ∑ i : Fin d, ∑ j : Fin d,
            ((|hF.isHermitian.eigenvalues i -
                hG.isHermitian.eigenvalues j| *
                spectralAtomOverlap F G hF hG i j) / w +
              (1 / (N : ℝ)) *
                spectralAtomOverlap F G hF hG i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by
          simp_rw [Finset.sum_add_distrib, Finset.sum_div,
            Finset.mul_sum]
    _ = dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ / w +
          (d : ℝ) / N := by
      rw [discrepancy, overlap_mass]
      ring

theorem dSVUniformDensityGridPrefix_le_density
    {N : ℕ} (positive : 0 < N)
    {a : ℝ} (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    dSVUniformDensityGridPrefix N a ≤ a := by
  have cast : (0 : ℝ) < N := by exact_mod_cast positive
  rw [dSVUniformDensityGridPrefix_eq_count,
    dSVUniformDensityThresholdGrid_count_eq_floor
      positive a nonnegative bounded]
  apply (div_le_iff₀ cast).mpr
  exact Nat.floor_le (mul_nonneg nonnegative cast.le)

theorem dSVUniformDensityGridPrefix_density_sub_lt
    {N : ℕ} (positive : 0 < N)
    {a : ℝ} (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a - dSVUniformDensityGridPrefix N a < 1 / (N : ℝ) := by
  have cast : (0 : ℝ) < N := by exact_mod_cast positive
  rw [dSVUniformDensityGridPrefix_eq_count,
    dSVUniformDensityThresholdGrid_count_eq_floor
      positive a nonnegative bounded]
  apply (lt_div_iff₀ cast).mpr
  have floor := Nat.lt_floor_add_one (a * (N : ℝ))
  calc
    (a - (Nat.floor (a * (N : ℝ)) : ℝ) / (N : ℝ)) *
        (N : ℝ) =
      a * (N : ℝ) - (Nat.floor (a * (N : ℝ)) : ℝ) := by
        field_simp
    _ < 1 := by linarith

theorem dSVUniformDensityGridPrefix_density_sub_le
    {N : ℕ} (positive : 0 < N)
    {a : ℝ} (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a - 1 / (N : ℝ) ≤ dSVUniformDensityGridPrefix N a := by
  linarith [dSVUniformDensityGridPrefix_density_sub_lt
    positive nonnegative bounded]

/-- The total probability mass of DSV density rational left projective diagonal. -/
def dSVDensityRationalLeftProjectiveDiagonalMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) : ℝ :=
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  ∑ i : Fin d,
    dSVUniformDensityGridPrefix N
      (dSVRationalSoftPass w
        (hF.isHermitian.eigenvalues i))

theorem dSVSoftBobLeftReducedDensity_eigenvalue_le_one
    {d : ℕ} (ξ : BipartiteUnitVector d) (i : Fin d) :
    (dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i
      ≤ 1 := by
  let F := dSVSoftBobLeftReducedDensity ξ
  let hF : F.PosSemidef :=
    dSVSoftBobLeftReducedDensity_posSemidef ξ
  change hF.isHermitian.eigenvalues i ≤ 1
  calc
    hF.isHermitian.eigenvalues i ≤
        ∑ j : Fin d, hF.isHermitian.eigenvalues j :=
      Finset.single_le_sum
        (fun j _ => hF.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = 1 := positiveDensity_eigenvalues_sum F hF
      (dSVSoftBobLeftReducedDensity_trace ξ)

theorem dSVRationalSoftPass_ge_density_div_width_add_one
    {w a : ℝ} (width : 0 < w)
    (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a / (w + 1) ≤ dSVRationalSoftPass w a := by
  unfold dSVRationalSoftPass
  have denominator : 0 < a + w := by linarith
  have wider : 0 < w + 1 := by linarith
  apply (div_le_div_iff₀ wider denominator).mpr
  nlinarith

theorem dSVDensityRationalLeftProjectiveDiagonalMass_lower
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) :
    1 / (w + 1) - (d : ℝ) / N ≤
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  let F := dSVSoftBobLeftReducedDensity ξ
  let hF : F.PosSemidef :=
    dSVSoftBobLeftReducedDensity_posSemidef ξ
  have density_sum :
      (∑ i : Fin d, hF.isHermitian.eigenvalues i) = 1 :=
    positiveDensity_eigenvalues_sum F hF
      (dSVSoftBobLeftReducedDensity_trace ξ)
  have rational_sum :
      1 / (w + 1) ≤
        ∑ i : Fin d,
          dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i) := by
    calc
      1 / (w + 1) =
          ∑ i : Fin d, hF.isHermitian.eigenvalues i / (w + 1) := by
        rw [← Finset.sum_div, density_sum]
      _ ≤ ∑ i : Fin d,
          dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i) := by
        apply Finset.sum_le_sum
        intro i _
        exact dSVRationalSoftPass_ge_density_div_width_add_one
          width (hF.eigenvalues_nonneg i)
          (dSVSoftBobLeftReducedDensity_eigenvalue_le_one ξ i)
  calc
    1 / (w + 1) - (d : ℝ) / N ≤
        (∑ i : Fin d,
          dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i)) - (d : ℝ) / N :=
      sub_le_sub_right rational_sum _
    _ = ∑ i : Fin d,
        (dSVRationalSoftPass w
          (hF.isHermitian.eigenvalues i) - 1 / (N : ℝ)) := by
      simp only [one_div, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        sub_right_inj]
      ring
    _ ≤ dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
      unfold dSVDensityRationalLeftProjectiveDiagonalMass
      change
        (∑ i : Fin d,
          (dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i) - 1 / (N : ℝ))) ≤
          ∑ i : Fin d,
            dSVUniformDensityGridPrefix N
              (dSVRationalSoftPass w
                (hF.isHermitian.eigenvalues i))
      apply Finset.sum_le_sum
      intro i _
      exact dSVUniformDensityGridPrefix_density_sub_le grid
        (dSVRationalSoftPass_mem_unit width
          (hF.eigenvalues_nonneg i)).1
        (dSVRationalSoftPass_mem_unit width
          (hF.eigenvalues_nonneg i)).2

end

end QuantumParallelRepetition

end
