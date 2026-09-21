/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientField
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Signed Permutation -/

namespace Homogenization

/-- The real-vector representation of an integer lattice vector. -/
def intVecToRealVec {d : ℕ} (z : Fin d → ℤ) : Vec d :=
  fun i => (z i : ℝ)

/-- A coordinate permutation with independent sign changes. -/
def IsSignedPermutationMatrix {d : ℕ} (R : Mat d) : Prop :=
  ∃ σ : Equiv.Perm (Fin d), ∃ s : Fin d → ℝ,
    (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ i j, R i j = if i = σ j then s j else 0

private theorem matVecMul_one {d : ℕ} (x : Vec d) :
    matVecMul (1 : Mat d) x = x := by
  ext i
  unfold matVecMul
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hij : i ≠ j := fun h => hji h.symm
    simp [hij]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem IsSignedPermutationMatrix.transpose_mul_self {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    matTranspose R * R = 1 := by
  classical
  rcases hR with ⟨σ, s, hs, hR⟩
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.mul_apply]
    calc
      ∑ k, matTranspose R i k * R k i =
          matTranspose R i (σ i) * R (σ i) i := by
        refine Finset.sum_eq_single (a := σ i)
          (f := fun k : Fin d => matTranspose R i k * R k i) ?_ ?_
        · intro k _ hk
          change R k i * R k i = 0
          rw [hR k i]
          simp [hk]
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = s i * s i := by
        change R (σ i) i * R (σ i) i = s i * s i
        rw [hR (σ i) i]
        simp
      _ = 1 := by
        rcases hs i with hsi | hsi <;> simp [hsi]
      _ = (1 : Mat d) i i := by simp
  · rw [Matrix.mul_apply]
    calc
      ∑ k, matTranspose R i k * R k j = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [matTranspose, Matrix.transpose_apply, hR k i, hR k j]
        have hσij : σ i ≠ σ j := fun h => hij (σ.injective h)
        by_cases hki : k = σ i
        · have hkj : k ≠ σ j := by
            intro h
            apply hij
            exact σ.injective (hki.symm.trans h)
          simp [hki, hσij]
        · simp [hki]
      _ = (1 : Mat d) i j := by simp [hij]

theorem IsSignedPermutationMatrix.mul_transpose_self {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    R * matTranspose R = 1 := by
  classical
  rcases hR with ⟨σ, s, hs, hR⟩
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.mul_apply]
    calc
      ∑ k, R i k * matTranspose R k i =
          R i (σ.symm i) * matTranspose R (σ.symm i) i := by
        refine Finset.sum_eq_single (a := σ.symm i)
          (f := fun k : Fin d => R i k * matTranspose R k i) ?_ ?_
        · intro k _ hk
          change R i k * R i k = 0
          rw [hR i k]
          have hik : i ≠ σ k := by
            intro h
            apply hk
            have hsymm : σ.symm i = k := by
              rw [h]
              simp
            exact hsymm.symm
          rw [if_neg hik]
          simp
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = s (σ.symm i) * s (σ.symm i) := by
        change R i (σ.symm i) * R i (σ.symm i) =
          s (σ.symm i) * s (σ.symm i)
        rw [hR i (σ.symm i)]
        have hi : i = σ (σ.symm i) := by simp
        rw [if_pos hi]
      _ = 1 := by
        rcases hs (σ.symm i) with hsi | hsi <;> simp [hsi]
      _ = (1 : Mat d) i i := by simp
  · rw [Matrix.mul_apply]
    calc
      ∑ k, R i k * matTranspose R k j = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [matTranspose, Matrix.transpose_apply, hR i k, hR j k]
        by_cases hik : i = σ k
        · have hjk : j ≠ σ k := by
            intro h
            exact hij (hik.trans h.symm)
          simp [hik, hjk]
        · simp [hik]
      _ = (1 : Mat d) i j := by simp [hij]

theorem IsSignedPermutationMatrix.transpose {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    IsSignedPermutationMatrix (matTranspose R) := by
  classical
  rcases hR with ⟨σ, s, hs, hRdef⟩
  refine ⟨σ.symm, fun i => s (σ.symm i), ?_, ?_⟩
  · intro i
    exact hs (σ.symm i)
  · intro i j
    rw [matTranspose, Matrix.transpose_apply, hRdef j i]
    by_cases h : i = σ.symm j
    · subst i
      simp
    · have hji : j ≠ σ i := by
        intro hji
        apply h
        rw [hji]
        simp
      rw [if_neg hji, if_neg h]

theorem IsSignedPermutationMatrix.det_ne_zero {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    Matrix.det R ≠ 0 := by
  have hdet := congrArg Matrix.det hR.transpose_mul_self
  have hprod : Matrix.det R * Matrix.det R = 1 := by
    simpa [matTranspose, Matrix.det_mul, Matrix.det_transpose] using hdet
  intro hzero
  simp [hzero] at hprod

theorem IsSignedPermutationMatrix.abs_det_eq_one {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    |Matrix.det R| = 1 := by
  have hdet := congrArg Matrix.det hR.transpose_mul_self
  have hsquare : Matrix.det R * Matrix.det R = 1 := by
    simpa [matTranspose, Matrix.det_mul, Matrix.det_transpose] using hdet
  have hnonneg : 0 ≤ |Matrix.det R| := abs_nonneg _
  have habs_square : |Matrix.det R| * |Matrix.det R| = 1 := by
    rw [← abs_mul, hsquare, abs_one]
  nlinarith

private theorem continuous_matVecMul {d : ℕ} (R : Mat d) :
    Continuous (fun x : Vec d => matVecMul R x) := by
  change Continuous fun x : Fin d → ℝ => fun i => ∑ j, R i j * x j
  exact continuous_pi fun i =>
    continuous_finsetSum Finset.univ fun j _ => continuous_const.mul (continuous_apply j)

noncomputable def signedPermutationHomeomorph {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) : Vec d ≃ₜ Vec d where
  toEquiv :=
    { toFun := matVecMul R
      invFun := matVecMul (matTranspose R)
      left_inv := by
        intro x
        rw [matVecMul_mul, hR.transpose_mul_self, matVecMul_one]
      right_inv := by
        intro x
        rw [matVecMul_mul, hR.mul_transpose_self, matVecMul_one] }
  continuous_toFun := continuous_matVecMul R
  continuous_invFun := continuous_matVecMul (matTranspose R)

theorem measurePreserving_matVecMul_signedPermutation {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    MeasureTheory.MeasurePreserving (fun x : Vec d => matVecMul R x)
      MeasureTheory.volume MeasureTheory.volume := by
  refine ⟨(continuous_matVecMul R).measurable, ?_⟩
  have hscale :
      ENNReal.ofReal |(Matrix.det R)⁻¹| = 1 := by
    rw [abs_inv, hR.abs_det_eq_one]
    norm_num
  change MeasureTheory.Measure.map (Matrix.toLin' R) MeasureTheory.volume = MeasureTheory.volume
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hR.det_ne_zero, hscale, one_smul]

end Homogenization
