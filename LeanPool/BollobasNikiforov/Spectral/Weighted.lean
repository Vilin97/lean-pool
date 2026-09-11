/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.BollobasNikiforov.Spectral.Perron
import LeanPool.BollobasNikiforov.Basic.Spectrum
import LeanPool.BollobasNikiforov.Basic.Inner
import LeanPool.BollobasNikiforov.Basic.Graph
import LeanPool.BollobasNikiforov.M.Main
import LeanPool.BollobasNikiforov.MS.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank-at-most-two spectral slice of a symmetric nonnegative matrix

A symmetric entrywise-nonnegative matrix `B` has a rank-at-most-two PSD slice
`X = a uuᵀ + b vvᵀ` built from a nonnegative Perron vector for `λ_max` and,
when `λ₂ > 0`, a unit eigenvector for `λ₂` orthogonal to it. This slice
satisfies `⟨B, X⟩ = ⟨X, X⟩ = F B` and is a Gram matrix of planar vectors in
the closed right half-plane. If `B` is zero-diagonal and supported on `E(G)`,
the Motzkin–Straus bound on `M X` yields `F B ≤ turanFactor G * ⟨B, B⟩`.
-/

namespace BollobasNikiforov

open Matrix Module WithLp Submodule
open scoped InnerProductSpace Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]
variable {B : Matrix n n ℝ}

omit [DecidableEq n] in
lemma sum_sq_eq_dotProduct (x : n → ℝ) : ∑ i, x i ^ 2 = x ⬝ᵥ x := by
  simp [dotProduct, pow_two]

omit [DecidableEq n] in
lemma isHermitian_dotProduct_mulVec (hB : B.IsHermitian) (x y : n → ℝ) :
    x ⬝ᵥ B *ᵥ y = (B *ᵥ x) ⬝ᵥ y := by
  have hBT : Bᵀ = B := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hB.eq
  rw [dotProduct_mulVec, ← vecMul_transpose, hBT]

omit [DecidableEq n] in
lemma inner_smul_vecMulVec (r : ℝ) (C : Matrix n n ℝ) (u : n → ℝ) :
    inner C (r • vecMulVec u u) = r * (u ⬝ᵥ C *ᵥ u) := by
  rw [inner_smul_right, inner_vecMulVec]

omit [DecidableEq n] in
lemma vecMulVec_mulVec (u v x : n → ℝ) :
    vecMulVec u v *ᵥ x = (v ⬝ᵥ x) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  trans u i * ∑ j, v j * x j
  · simp_rw [mul_assoc]
    exact (Finset.mul_sum (Finset.univ) (fun j => v j * x j) (u i)).symm
  · ring

omit [DecidableEq n] in
lemma inner_vecMulVec_vecMulVec (u v : n → ℝ) :
    inner (vecMulVec u u) (vecMulVec v v) = (u ⬝ᵥ v) ^ 2 := by
  rw [inner_vecMulVec, vecMulVec_mulVec, dotProduct_smul, smul_eq_mul, mul_comm,
    dotProduct_comm, pow_two]

variable [Nontrivial n]

/-- Index of `λ_max` among `eigenvalues`. -/
noncomputable def lambdaMaxIndex : n :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))) ⟨0, Fintype.card_pos⟩

/-- Index of `λ₂` among `eigenvalues`. -/
noncomputable def lambdaSecondIndex : n :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))) ⟨1, Fintype.one_lt_card⟩

omit [DecidableEq n] in
lemma lambdaMaxIndex_ne_lambdaSecondIndex : lambdaMaxIndex (n := n) ≠ lambdaSecondIndex := by
  intro h
  have := congrArg Fin.val
    ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).injective h)
  exact Nat.zero_ne_one this

lemma eigenvalues_lambdaMaxIndex (hB : B.IsHermitian) :
    hB.eigenvalues lambdaMaxIndex = lambdaMax hB := by
  simp [lambdaMaxIndex, IsHermitian.eigenvalues, lambdaMax, eigs₀]

lemma eigenvalues_lambdaSecondIndex (hB : B.IsHermitian) :
    hB.eigenvalues lambdaSecondIndex = lambdaSecond hB := by
  simp [lambdaSecondIndex, IsHermitian.eigenvalues, lambdaSecond, eigs₀]

omit [Nontrivial n] in
lemma eigenvectorBasis_sum_sq (hB : B.IsHermitian) (i : n) :
    ∑ k, (hB.eigenvectorBasis i : n → ℝ) k ^ 2 = 1 := by
  have hn : ‖hB.eigenvectorBasis i‖ = 1 := (hB.eigenvectorBasis).orthonormal.1 i
  rw [← EuclideanSpace.real_norm_sq_eq, hn, one_pow]

omit [Nontrivial n] in
lemma eigenvectorBasis_dotProduct (hB : B.IsHermitian) {i j : n} (hij : i ≠ j) :
    (hB.eigenvectorBasis i : n → ℝ) ⬝ᵥ (hB.eigenvectorBasis j : n → ℝ) = 0 := by
  have h0 : ⟪hB.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℝ = 0 :=
    (hB.eigenvectorBasis).orthonormal.inner_eq_zero hij
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h0
  simpa [dotProduct_comm] using h0

/-- A unit eigenvector for `λ₂` orthogonal to a unit `λ_max`-eigenvector, when `λ₂ > 0`. -/
lemma exists_second_eigenvec (hB : B.IsHermitian)
    {u : n → ℝ} (hu : B *ᵥ u = lambdaMax hB • u) (hu1 : ∑ i, u i ^ 2 = 1)
    (_hb : 0 < lambdaSecond hB) :
    ∃ v : n → ℝ, ∑ i, v i ^ 2 = 1 ∧ u ⬝ᵥ v = 0 ∧
      B *ᵥ v = lambdaSecond hB • v := by
  let e0 : n → ℝ := hB.eigenvectorBasis lambdaMaxIndex
  let e1 : n → ℝ := hB.eigenvectorBasis lambdaSecondIndex
  have he0 : B *ᵥ e0 = lambdaMax hB • e0 := by
    simpa [e0, eigenvalues_lambdaMaxIndex] using hB.mulVec_eigenvectorBasis lambdaMaxIndex
  have he1 : B *ᵥ e1 = lambdaSecond hB • e1 := by
    simpa [e1, eigenvalues_lambdaSecondIndex] using
      hB.mulVec_eigenvectorBasis lambdaSecondIndex
  have he0_sq : ∑ k, e0 k ^ 2 = 1 := eigenvectorBasis_sum_sq hB _
  have he1_sq : ∑ k, e1 k ^ 2 = 1 := eigenvectorBasis_sum_sq hB _
  have he01 : e0 ⬝ᵥ e1 = 0 :=
    eigenvectorBasis_dotProduct hB lambdaMaxIndex_ne_lambdaSecondIndex
  have hu1' : u ⬝ᵥ u = 1 := by simpa [sum_sq_eq_dotProduct] using hu1
  have hpair : lambdaMax hB * (e1 ⬝ᵥ u) = lambdaSecond hB * (e1 ⬝ᵥ u) := by
    have hsa := isHermitian_dotProduct_mulVec hB u e1
    rw [hu, he1, dotProduct_smul, smul_dotProduct] at hsa
    simp only [smul_eq_mul] at hsa
    rw [dotProduct_comm u e1] at hsa
    exact hsa.symm
  let w : n → ℝ := e1 - (e1 ⬝ᵥ u) • u
  have hw_ortho : u ⬝ᵥ w = 0 := by
    simp only [dotProduct_sub, dotProduct_smul, hu1', smul_eq_mul, mul_one, w]
    rw [dotProduct_comm u e1]
    ring
  have hw_eigen : B *ᵥ w = lambdaSecond hB • w := by
    simp only [w, mulVec_sub, mulVec_smul, he1, hu, smul_smul]
    rw [smul_sub, smul_smul]
    congr 1
    rw [mul_comm, hpair, mul_comm]
  by_cases hw : w = 0
  · set c := e1 ⬝ᵥ u
    have hpar : e1 = c • u := by
      simpa [w, c, sub_eq_zero] using hw
    have hab : lambdaMax hB = lambdaSecond hB := by
      have : lambdaMax hB • e1 = lambdaSecond hB • e1 := by
        calc
          lambdaMax hB • e1 = lambdaMax hB • (c • u) := by rw [hpar]
          _ = c • (lambdaMax hB • u) := by
            rw [smul_smul, mul_comm, ← smul_smul]
          _ = c • (B *ᵥ u) := by rw [hu]
          _ = B *ᵥ (c • u) := by rw [mulVec_smul]
          _ = B *ᵥ e1 := by rw [hpar]
          _ = lambdaSecond hB • e1 := he1
      have he1_ne : e1 ≠ 0 := by
        intro h
        simp [h] at he1_sq
      exact smul_left_injective ℝ he1_ne this
    refine ⟨e0, he0_sq, ?_, ?_⟩
    · have hc0 : c ≠ 0 := by
        intro hc
        have : e1 = 0 := by simpa [hc] using hpar
        have : ∑ k, e1 k ^ 2 = 0 := by simp [this]
        simp [this] at he1_sq
      have : c * (u ⬝ᵥ e0) = 0 := by
        calc
          c * (u ⬝ᵥ e0) = (c • u) ⬝ᵥ e0 := by
            rw [smul_dotProduct, smul_eq_mul]
          _ = e1 ⬝ᵥ e0 := by rw [← hpar]
          _ = 0 := by rw [dotProduct_comm, he01]
      exact (mul_eq_zero.mp this).resolve_left hc0
    · rw [he0, hab]
  · have hwsq_pos : 0 < ∑ i, w i ^ 2 := by
      have hnn : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      refine lt_of_le_of_ne hnn ?_
      intro h0
      apply hw
      rw [sum_sq_eq_dotProduct] at h0
      exact dotProduct_self_eq_zero.mp h0.symm
    set s := Real.sqrt (∑ i, w i ^ 2)
    have hspos : 0 < s := Real.sqrt_pos.mpr hwsq_pos
    refine ⟨s⁻¹ • w, ?_, ?_, ?_⟩
    · have hs2 : s ^ 2 = ∑ i, w i ^ 2 := Real.sq_sqrt (le_of_lt hwsq_pos)
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
      rw [← Finset.mul_sum, ← hs2, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hspos.ne')]
    · simp [dotProduct_smul, hw_ortho]
    · simp [mulVec_smul, hw_eigen, smul_comm s⁻¹]

/-- Data of the rank-at-most-two spectral slice of a symmetric nonnegative matrix. -/
structure SpectralSlice (hB : B.IsHermitian) (hnn : ∀ i j, 0 ≤ B i j) where
  /-- The largest eigenvalue `λ₁(B)`. -/
  a : ℝ
  /-- The positive part `max (λ₂(B)) 0` of the second eigenvalue. -/
  b : ℝ
  /-- A nonnegative unit eigenvector for `a`. -/
  u : n → ℝ
  /-- An eigenvector for `b`, orthogonal to `u`, of unit mass when `0 < b` and zero otherwise. -/
  v : n → ℝ
  /-- The rank-at-most-two matrix `a • u uᵀ + b • v vᵀ`. -/
  X : Matrix n n ℝ
  ha : a = lambdaMax hB
  hb : b = max (lambdaSecond hB) 0
  hu_nonneg : ∀ i, 0 ≤ u i
  hu_unit : ∑ i, u i ^ 2 = 1
  hu_eigen : B *ᵥ u = a • u
  hv_sq : ∑ i, v i ^ 2 = if 0 < b then 1 else 0
  hv_ortho : u ⬝ᵥ v = 0
  hv_eigen : B *ᵥ v = b • v
  hX : X = a • vecMulVec u u + b • vecMulVec v v

/-- **SP04.** Existence of the spectral slice. -/
noncomputable def spectralSlice (hB : B.IsHermitian) (hnn : ∀ i j, 0 ≤ B i j) :
    SpectralSlice hB hnn :=
  let hu := exists_nonneg_eigenvector_lambdaMax (n := n) hB hnn
  let u := hu.choose
  let hu0 := hu.choose_spec.1
  let hu1 := hu.choose_spec.2.1
  let hue := hu.choose_spec.2.2
  if hb : 0 < lambdaSecond hB then
    let hv := exists_second_eigenvec hB hue hu1 hb
    let v := hv.choose
    { a := lambdaMax hB
      b := lambdaSecond hB
      u := u
      v := v
      X := lambdaMax hB • vecMulVec u u + lambdaSecond hB • vecMulVec v v
      ha := rfl
      hb := (max_eq_left hb.le).symm
      hu_nonneg := hu0
      hu_unit := hu1
      hu_eigen := hue
      hv_sq := by
        have hv1 := hv.choose_spec.1
        simpa [hb] using hv1
      hv_ortho := hv.choose_spec.2.1
      hv_eigen := hv.choose_spec.2.2
      hX := rfl }
  else
    { a := lambdaMax hB
      b := 0
      u := u
      v := 0
      X := lambdaMax hB • vecMulVec u u
      ha := rfl
      hb := (max_eq_right (not_lt.mp hb)).symm
      hu_nonneg := hu0
      hu_unit := hu1
      hu_eigen := hue
      hv_sq := by simp
      hv_ortho := by simp
      hv_eigen := by simp
      hX := by simp }

namespace SpectralSlice

variable {hB : B.IsHermitian} {hnn : ∀ i j, 0 ≤ B i j}
variable (s : SpectralSlice hB hnn)

lemma a_nonneg : 0 ≤ s.a := by
  have huu : s.u ⬝ᵥ s.u = 1 := by simpa [sum_sq_eq_dotProduct] using s.hu_unit
  have : s.a = s.u ⬝ᵥ B *ᵥ s.u := by
    rw [s.hu_eigen, dotProduct_smul, smul_eq_mul, huu, mul_one]
  rw [this, dot_mulVec_eq_sum_sum]
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => ?_
  exact mul_nonneg (mul_nonneg (s.hu_nonneg i) (hnn i j)) (s.hu_nonneg j)

lemma b_nonneg : 0 ≤ s.b := by
  rw [s.hb]
  exact le_max_right _ _

lemma hv_dot : s.v ⬝ᵥ s.v = if 0 < s.b then 1 else 0 := by
  simpa [sum_sq_eq_dotProduct] using s.hv_sq

/-- **SP04.** The spectral slice is positive semidefinite. -/
lemma posSemidef : s.X.PosSemidef := by
  have huu : (vecMulVec s.u s.u).PosSemidef := by
    simpa using posSemidef_vecMulVec_self_star (R := ℝ) s.u
  have hvv : (vecMulVec s.v s.v).PosSemidef := by
    simpa using posSemidef_vecMulVec_self_star (R := ℝ) s.v
  rw [s.hX]
  exact (huu.smul s.a_nonneg).add (hvv.smul s.b_nonneg)

lemma col_eq (j : n) :
    s.X.col j = (s.a * s.u j) • s.u + (s.b * s.v j) • s.v := by
  ext i
  simp [s.hX, col_apply, vecMulVec_apply, smul_eq_mul]
  ring

/-- **SP04.** The spectral slice has rank at most two. -/
lemma rank_le_two : s.X.rank ≤ 2 := by
  classical
  rw [rank_eq_finrank_span_cols]
  let W := span ℝ ({s.u, s.v} : Set (n → ℝ))
  have hle : span ℝ (Set.range s.X.col) ≤ W := by
    refine span_le.mpr ?_
    intro x hx
    obtain ⟨j, rfl⟩ := Set.mem_range.mp hx
    rw [s.col_eq]
    exact W.add_mem (W.smul_mem _ (subset_span (by simp)))
      (W.smul_mem _ (subset_span (by simp : s.v ∈ ({s.u, s.v} : Set _))))
  refine (finrank_mono hle).trans ?_
  refine (finrank_span_le_card (R := ℝ) ({s.u, s.v} : Set (n → ℝ))).trans ?_
  have : ({s.u, s.v} : Set (n → ℝ)).toFinset.card ≤ 2 := by
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  exact this

lemma inner_B_X_eq_sq : inner B s.X = s.a ^ 2 + s.b ^ 2 := by
  have huu : s.u ⬝ᵥ s.u = 1 := by simpa [sum_sq_eq_dotProduct] using s.hu_unit
  rw [s.hX, inner_add_right, inner_smul_vecMulVec, inner_smul_vecMulVec, s.hu_eigen, s.hv_eigen,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, huu, s.hv_dot]
  split_ifs with hb
  · ring
  · have hb0 : s.b = 0 := le_antisymm (le_of_not_gt hb) s.b_nonneg
    simp [hb0, pow_two]

lemma inner_X_X_eq_sq : inner s.X s.X = s.a ^ 2 + s.b ^ 2 := by
  have huu : s.u ⬝ᵥ s.u = 1 := by simpa [sum_sq_eq_dotProduct] using s.hu_unit
  have hAA : inner (vecMulVec s.u s.u) (vecMulVec s.u s.u) = 1 := by
    rw [inner_vecMulVec_vecMulVec, huu, one_pow]
  have hAC : inner (vecMulVec s.u s.u) (vecMulVec s.v s.v) = 0 := by
    rw [inner_vecMulVec_vecMulVec, s.hv_ortho, zero_pow (by decide)]
  have hCA : inner (vecMulVec s.v s.v) (vecMulVec s.u s.u) = 0 := by
    rw [inner_comm, hAC]
  have hCC : inner (vecMulVec s.v s.v) (vecMulVec s.v s.v) = (s.v ⬝ᵥ s.v) ^ 2 :=
    inner_vecMulVec_vecMulVec _ _
  rw [s.hX, inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_right,
    inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right, inner_smul_left,
    inner_smul_right, hAA, hAC, hCA, hCC, s.hv_dot]
  split_ifs with hb
  · ring
  · have hb0 : s.b = 0 := le_antisymm (le_of_not_gt hb) s.b_nonneg
    simp [hb0, pow_two]

/-- **SP05.** `⟨B, X⟩ = ⟨X, X⟩ = F B`. -/
lemma inner_B_X : inner B s.X = F hB := by
  have ha' : 0 ≤ lambdaMax hB := by simpa [s.ha] using s.a_nonneg
  rw [s.inner_B_X_eq_sq, F_eq, s.ha, s.hb, max_eq_left ha']

lemma inner_X_X : inner s.X s.X = F hB := by
  have ha' : 0 ≤ lambdaMax hB := by simpa [s.ha] using s.a_nonneg
  rw [s.inner_X_X_eq_sq, F_eq, s.ha, s.hb, max_eq_left ha']

lemma inner_B_X_eq_inner_X_X : inner B s.X = inner s.X s.X :=
  s.inner_B_X.trans s.inner_X_X.symm

lemma lambdaMax_pos_of_ne_zero (hB0 : B ≠ 0) : 0 < s.a := by
  refine lt_of_le_of_ne s.a_nonneg ?_
  intro ha0
  have hlam0 : lambdaMax hB = 0 := by simp [← s.ha, ha0]
  have hle (i : n) : hB.eigenvalues i ≤ 0 := by
    have : hB.eigenvalues i = hB.eigenvalues₀
        ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i) := rfl
    rw [this]
    have h0 : (⟨0, Fintype.card_pos⟩ : Fin (Fintype.card n)) ≤
        (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i := Fin.zero_le _
    have hmono := hB.eigenvalues₀_antitone h0
    have hmax0 : hB.eigenvalues₀ ⟨0, Fintype.card_pos⟩ = 0 := by
      simpa [lambdaMax, eigs₀] using hlam0
    rwa [hmax0] at hmono
  have htr : B.trace = ∑ i, hB.eigenvalues i := by
    simpa using hB.trace_eq_sum_eigenvalues
  have hsum_nonpos : ∑ i, hB.eigenvalues i ≤ 0 :=
    Finset.sum_nonpos fun i _ => hle i
  have hdiag : 0 ≤ B.trace :=
    Finset.sum_nonneg fun i _ => hnn i i
  have hsum0 : ∑ i, hB.eigenvalues i = 0 :=
    le_antisymm hsum_nonpos (by simpa [htr] using hdiag)
  have hz : hB.eigenvalues = 0 := by
    ext i
    have hneg : ∑ j, -hB.eigenvalues j = 0 := by simp [hsum0]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => neg_nonneg.mpr (hle j))).1 hneg
    simpa using this i (Finset.mem_univ _)
  exact hB0 ((IsHermitian.eigenvalues_eq_zero_iff hB).mp hz)

/-- **SP05.** If `B ≠ 0` then the common Frobenius mass is positive. -/
lemma inner_pos (hB0 : B ≠ 0) : 0 < inner s.X s.X := by
  rw [s.inner_X_X_eq_sq]
  have ha : 0 < s.a := s.lambdaMax_pos_of_ne_zero hB0
  nlinarith [s.b_nonneg]

/-- Planar Gram embedding of the spectral slice. -/
noncomputable def embed (i : n) : Fin 2 → ℝ :=
  ![Real.sqrt s.a * s.u i, Real.sqrt s.b * s.v i]

/-- **SP06.** The first coordinate is nonnegative. -/
lemma embed_nonneg_fst (i : n) : 0 ≤ s.embed i 0 := by
  simp only [embed, Fin.isValue, cons_val_zero]
  exact mul_nonneg (Real.sqrt_nonneg _) (s.hu_nonneg i)

/-- **SP06.** `X` is the Gram matrix of the planar embedding. -/
lemma gram (i j : n) : s.X i j = s.embed i ⬝ᵥ s.embed j := by
  have ha : Real.sqrt s.a * Real.sqrt s.a = s.a := Real.mul_self_sqrt s.a_nonneg
  have hb : Real.sqrt s.b * Real.sqrt s.b = s.b := Real.mul_self_sqrt s.b_nonneg
  have hXij : s.X i j = s.a * (s.u i * s.u j) + s.b * (s.v i * s.v j) := by
    simp [s.hX, vecMulVec_apply]
  have hz : s.embed i ⬝ᵥ s.embed j =
      (Real.sqrt s.a * s.u i) * (Real.sqrt s.a * s.u j) +
        (Real.sqrt s.b * s.v i) * (Real.sqrt s.b * s.v j) := by
    simp [embed, dotProduct, Fin.sum_univ_two]
  calc
    s.X i j = s.a * (s.u i * s.u j) + s.b * (s.v i * s.v j) := hXij
    _ = (Real.sqrt s.a * Real.sqrt s.a) * (s.u i * s.u j) +
          (Real.sqrt s.b * Real.sqrt s.b) * (s.v i * s.v j) := by rw [ha, hb]
    _ = (Real.sqrt s.a * s.u i) * (Real.sqrt s.a * s.u j) +
          (Real.sqrt s.b * s.v i) * (Real.sqrt s.b * s.v j) := by ring
    _ = s.embed i ⬝ᵥ s.embed j := hz.symm

/-- **SP07.** `M` of the spectral slice is completely positive. -/
lemma isCompletelyPositive_M [LinearOrder n] : IsCompletelyPositive (M s.X) := by
  have hX : BollobasNikiforov.gram s.embed = s.X := by
    ext i j
    rw [s.gram]
    rfl
  have hw : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  have hwz : ∀ i, 0 ≤ (![1, 0] : Fin 2 → ℝ) ⬝ᵥ s.embed i := by
    intro i
    have hdot : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ s.embed i = s.embed i 0 := by
      simp [dotProduct, Fin.sum_univ_two]
    rw [hdot]
    exact s.embed_nonneg_fst i
  rw [← hX]
  exact matrix_theorem s.embed hw hwz

/-- **SP08.** Completely positive Motzkin–Straus on `M s.X`. -/
lemma sum_adjMatrix_posPart_sq_le_turanFactor {G : SimpleGraph n} [DecidableRel G.Adj] :
    ∑ i, ∑ j, G.adjMatrix ℝ i j * (posPart s.X i j) ^ 2 ≤ turanFactor G * F hB := by
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  have hXsymm : s.X.IsSymm := isHermitian_iff_isSymm.mp s.posSemidef.isHermitian
  have hsum : inner (G.adjMatrix ℝ) (M s.X) =
      ∑ i, ∑ j, G.adjMatrix ℝ i j * (posPart s.X i j) ^ 2 := by
    rw [inner_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      simp [SimpleGraph.adjMatrix_apply]
    · rw [M_apply_of_ne s.X hXsymm hij]
  have hMS : inner (G.adjMatrix ℝ) (M s.X) ≤
      turanFactor G * inner (of fun _ _ => (1 : ℝ)) (M s.X) :=
    inner_adjMatrix_le_turanFactor_inner s.isCompletelyPositive_M
  have hJ : inner (of fun _ _ => (1 : ℝ)) (M s.X) = F hB := by
    rw [show (of fun _ _ => (1 : ℝ)) = ones from rfl, inner_ones_M, s.inner_X_X]
  rw [← hsum]
  exact hMS.trans_eq (by rw [hJ])

end SpectralSlice

/-! ### SP09–SP10 — support bound and Frobenius Cauchy–Schwarz -/

section Support

variable {G : SimpleGraph n} [DecidableRel G.Adj]

omit [Nontrivial n] [DecidableEq n] in
/-- **SP09.** If `B` is supported on the edges of `G` and entrywise nonnegative,
then pairing against `X` is dominated by pairing against `A_G ⊙ X₊`. -/
lemma inner_le_inner_hadamard_posPart {X : Matrix n n ℝ}
    (hnn : ∀ i j, 0 ≤ B i j) (hdiag : ∀ i, B i i = 0)
    (hsupp : ∀ i j, ¬ G.Adj i j → B i j = 0) :
    inner B X ≤ inner B (G.adjMatrix ℝ ⊙ posPart X) := by
  rw [inner_eq_sum, inner_eq_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  simp only [hadamard_apply, posPart_apply]
  by_cases hij : G.Adj i j
  · have hA : G.adjMatrix ℝ i j = 1 := by simp [SimpleGraph.adjMatrix_apply, hij]
    rw [hA, one_mul]
    exact mul_le_mul_of_nonneg_left (le_max_left (X i j) 0) (hnn i j)
  · by_cases hii : i = j
    · subst hii
      simp [hdiag i, SimpleGraph.adjMatrix_apply]
    · simp [hsupp i j hij, SimpleGraph.adjMatrix_apply, hij]

omit [Nontrivial n] [DecidableEq n] in
/-- **SP10.** Cauchy–Schwarz for the Frobenius pairing against `A_G ⊙ X₊`. -/
lemma inner_hadamard_posPart_le_sqrt (X : Matrix n n ℝ) :
    inner B (G.adjMatrix ℝ ⊙ posPart X) ≤
      Real.sqrt (inner B B) *
        Real.sqrt (∑ i, ∑ j, G.adjMatrix ℝ i j * (posPart X i j) ^ 2) := by
  set A := G.adjMatrix ℝ
  set P := posPart X
  have hAsq (i j : n) : A i j ^ 2 = A i j := by
    simp only [A, SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hab :
      inner B (A ⊙ P) =
        ∑ p ∈ Finset.univ ×ˢ Finset.univ, B p.1 p.2 * (A p.1 p.2 * P p.1 p.2) := by
    rw [inner_eq_sum]
    simp_rw [hadamard_apply]
    exact (Finset.sum_product' (s := Finset.univ) (t := Finset.univ)
      (f := fun i j => B i j * (A i j * P i j))).symm
  have hBB :
      inner B B = ∑ p ∈ Finset.univ ×ˢ Finset.univ, B p.1 p.2 ^ 2 := by
    rw [inner_self]
    exact (Finset.sum_product' (s := Finset.univ) (t := Finset.univ)
      (f := fun i j => B i j ^ 2)).symm
  have hP2 :
      ∑ i, ∑ j, A i j * P i j ^ 2 =
        ∑ p ∈ Finset.univ ×ˢ Finset.univ, (A p.1 p.2 * P p.1 p.2) ^ 2 := by
    rw [← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mul_pow, hAsq]
  have hcs :
      (∑ p ∈ Finset.univ ×ˢ Finset.univ, B p.1 p.2 * (A p.1 p.2 * P p.1 p.2)) ^ 2 ≤
        (∑ p ∈ Finset.univ ×ˢ Finset.univ, B p.1 p.2 ^ 2) *
          ∑ p ∈ Finset.univ ×ˢ Finset.univ, (A p.1 p.2 * P p.1 p.2) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hb : 0 ≤ inner B B := by
    rw [inner_self]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq :
      inner B (A ⊙ P) ^ 2 ≤
        inner B B * ∑ i, ∑ j, A i j * P i j ^ 2 := by
    rwa [← hab, ← hBB, ← hP2] at hcs
  rw [← Real.sqrt_mul hb]
  exact Real.le_sqrt_of_sq_le hsq

end Support

/-! ### SP11–SP12 — algebra of the weighted inequality -/

namespace SpectralSlice

variable {hB : B.IsHermitian} {hnn : ∀ i j, 0 ≤ B i j}
variable (s : SpectralSlice hB hnn)
variable {G : SimpleGraph n} [DecidableRel G.Adj]

include s hnn

omit [DecidableRel G.Adj] in
/-- **SP11.** Combining the support bound, Cauchy–Schwarz, and SP08. -/
lemma F_le_turanFactor_mul_inner
    (hdiag : ∀ i, B i i = 0)
    (hsupp : ∀ i j, ¬ G.Adj i j → B i j = 0) :
    F hB ≤ turanFactor G * inner B B := by
  classical
  have : Nonempty n := inferInstance
  by_cases hB0 : B = 0
  · have hF : F hB = 0 := by
      have hin : inner B s.X = 0 := by
        rw [inner_eq_sum]
        exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
          have hij : B i j = 0 := by rw [hB0]; rfl
          simp [hij]
      exact (s.inner_B_X.symm.trans hin).trans
        ((F_zero (n := n)).symm.trans F_zero)
    have hBB : inner B B = 0 := by
      rw [inner_eq_sum]
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        have hij : B i j = 0 := by rw [hB0]; rfl
        simp [hij]
    rw [hF, hBB, mul_zero]
  · have hpos : 0 < F hB := by
      rw [← s.inner_X_X]
      exact s.inner_pos hB0
    obtain ⟨i, j, hijB⟩ : ∃ (i : n) (j : n), B i j ≠ 0 := by
      have h : ¬ ∀ (a b : n), B a b = 0 := fun h => hB0 (Matrix.ext h)
      rw [not_forall] at h
      obtain ⟨i, hi⟩ := h
      rw [not_forall] at hi
      obtain ⟨j, hj⟩ := hi
      exact ⟨i, j, hj⟩
    have hijpos : 0 < B i j := lt_of_le_of_ne (hnn i j) hijB.symm
    have hne : i ≠ j := by
      intro hij
      subst hij
      exact hijB (hdiag i)
    have hadj : G.Adj i j := by
      have := hne
      exact Decidable.not_not.mp (mt (hsupp i j) (ne_of_gt hijpos))
    have hω : 2 ≤ G.cliqueNum := SimpleGraph.two_le_cliqueNum_of_adj G hadj
    have ht : 0 ≤ turanFactor G ∧ 0 < turanFactor G :=
      ⟨turanFactor_nonneg G, turanFactor_pos G hω⟩
    have hFnn : 0 ≤ F hB := hpos.le
    have hBB : 0 ≤ inner B B := by
      rw [inner_self]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h1 : inner B s.X ≤ inner B (G.adjMatrix ℝ ⊙ posPart s.X) :=
      inner_le_inner_hadamard_posPart hnn hdiag hsupp
    have h2 : inner B (G.adjMatrix ℝ ⊙ posPart s.X) ≤
        Real.sqrt (inner B B) *
          Real.sqrt (∑ i, ∑ j, G.adjMatrix ℝ i j * (posPart s.X i j) ^ 2) :=
      inner_hadamard_posPart_le_sqrt s.X
    have h3 := s.sum_adjMatrix_posPart_sq_le_turanFactor (G := G)
    have hchain : F hB ≤ Real.sqrt (inner B B) *
        Real.sqrt (∑ i, ∑ j, G.adjMatrix ℝ i j * (posPart s.X i j) ^ 2) := by
      rw [← s.inner_B_X]
      exact h1.trans h2
    have hchain2 : F hB ≤ Real.sqrt (inner B B) * Real.sqrt (turanFactor G * F hB) :=
      hchain.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h3) (Real.sqrt_nonneg _))
    have hprod : 0 ≤ inner B B * (turanFactor G * F hB) :=
      mul_nonneg hBB (mul_nonneg ht.1 hFnn)
    rw [← Real.sqrt_mul hBB] at hchain2
    have hsq : F hB ^ 2 ≤ inner B B * (turanFactor G * F hB) :=
      (Real.le_sqrt hFnn hprod).mp hchain2
    have hrearr : F hB * F hB ≤ (turanFactor G * inner B B) * F hB := by
      convert hsq using 1
      · rw [pow_two]
      · ring
    exact (mul_le_mul_iff_of_pos_right hpos).mp hrearr

end SpectralSlice

/-- **SP12.** Theorem `thm:weighted`. -/
theorem weighted {G : SimpleGraph n}
    (hB : B.IsHermitian) (hnn : ∀ i j, 0 ≤ B i j)
    (hdiag : ∀ i, B i i = 0)
    (hsupp : ∀ i j, ¬ G.Adj i j → B i j = 0) :
    F hB ≤ turanFactor G * inner B B :=
  (spectralSlice hB hnn).F_le_turanFactor_mul_inner hdiag hsupp

end BollobasNikiforov
