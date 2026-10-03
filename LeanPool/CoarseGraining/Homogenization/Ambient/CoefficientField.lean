/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.BlockMatrix
public import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # Coefficient Field -/

@[expose] public section

namespace Homogenization

abbrev CoeffField (d : ℕ) := Vec d → Mat d

def IsEllipticMatrix {d : ℕ} (lam Lam : ℝ) (A : Mat d) : Prop :=
  0 < lam ∧
    lam ≤ Lam ∧
    (∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ)) ∧
    (∀ ξ : Vec d, Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ))

namespace IsEllipticMatrix

theorem mono {d : ℕ} {lam Lam lam' Lam' : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (hlam'_pos : 0 < lam') (hlam'_le : lam' ≤ lam)
    (hLam_le : Lam ≤ Lam') :
    IsEllipticMatrix lam' Lam' A := by
  rcases hA with ⟨hlam_pos, hlam_le_Lam, hlower, hinv⟩
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlam_le_Lam
  have hLam'_pos : 0 < Lam' := lt_of_lt_of_le hLam_pos hLam_le
  refine ⟨hlam'_pos, hlam'_le.trans (hlam_le_Lam.trans hLam_le), ?_, ?_⟩
  · intro ξ
    calc
      lam' * vecNormSq ξ ≤ lam * vecNormSq ξ :=
        mul_le_mul_of_nonneg_right hlam'_le (vecNormSq_nonneg ξ)
      _ ≤ vecDot ξ (matVecMul A ξ) := hlower ξ
  · intro ξ
    have hInv_le : Lam'⁻¹ ≤ Lam⁻¹ := (inv_le_inv₀ hLam'_pos hLam_pos).2 hLam_le
    calc
      Lam'⁻¹ * vecNormSq ξ ≤ Lam⁻¹ * vecNormSq ξ :=
        mul_le_mul_of_nonneg_right hInv_le (vecNormSq_nonneg ξ)
      _ ≤ vecDot ξ (matVecMul A⁻¹ ξ) := hinv ξ

end IsEllipticMatrix

theorem isUnit_det_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) : IsUnit A.det := by
  classical
  by_cases hdet : IsUnit A.det
  · exact hdet
  · rcases hA with ⟨hlam_pos, hlamLam, -, hInv⟩
    have hInvZero : A⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit A hdet
    by_cases hd : d = 0
    · subst hd
      simp
    · let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
      have hbasis := hInv (Pi.single i 1)
      have hnorm : vecNormSq (Pi.single i 1 : Vec d) = 1 := by
        rw [vecNormSq, vecDot, Finset.sum_eq_single i]
        · simp
        · intro j _ hij
          simp [Pi.single_eq_of_ne hij]
        · simp
      have hzero :
          vecDot (Pi.single i 1 : Vec d) (matVecMul A⁻¹ (Pi.single i 1)) = 0 := by
        rw [hInvZero]
        simp [matVecMul, vecDot]
      have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlamLam
      have hLamInv_nonpos : Lam⁻¹ ≤ 0 := by
        rw [hnorm, hzero] at hbasis
        simpa using hbasis
      have hLamInv_pos : 0 < Lam⁻¹ := by positivity
      linarith

theorem vecNormSq_matVecMul_le_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    vecNormSq (matVecMul A ξ) ≤ Lam ^ 2 * vecNormSq ξ := by
  have hdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix hA
  rcases hA with ⟨hlam_pos, hlamLam, -, hInv⟩
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlamLam
  have hInvMul : matVecMul A⁻¹ (matVecMul A ξ) = ξ := by
    rw [matVecMul_mul, Matrix.nonsing_inv_mul A hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hInvA :
      Lam⁻¹ * vecNormSq (matVecMul A ξ) ≤ vecDot (matVecMul A ξ) ξ := by
    simpa [hInvMul] using hInv (matVecMul A ξ)
  have hCS :
      vecDot (matVecMul A ξ) ξ ^ 2 ≤
        vecNormSq (matVecMul A ξ) * vecNormSq ξ :=
    sq_vecDot_le_vecNormSq_mul_vecNormSq (matVecMul A ξ) ξ
  have hnonneg : 0 ≤ vecNormSq (matVecMul A ξ) :=
    vecNormSq_nonneg (matVecMul A ξ)
  have hdot_nonneg : 0 ≤ vecDot (matVecMul A ξ) ξ := by
    have hLamInv_nonneg : 0 ≤ Lam⁻¹ := by positivity
    exact (mul_nonneg hLamInv_nonneg hnonneg).trans hInvA
  have hInvA' :
      vecNormSq (matVecMul A ξ) ≤ Lam * vecDot (matVecMul A ξ) ξ := by
    have hmul := mul_le_mul_of_nonneg_left hInvA (le_of_lt hLam_pos)
    have hLamInv : Lam * Lam⁻¹ = 1 := by
      field_simp [hLam_pos.ne']
    calc
      vecNormSq (matVecMul A ξ) = (Lam * Lam⁻¹) * vecNormSq (matVecMul A ξ) := by
        rw [hLamInv, one_mul]
      _ = Lam * (Lam⁻¹ * vecNormSq (matVecMul A ξ)) := by ring
      _ ≤ Lam * vecDot (matVecMul A ξ) ξ := hmul
  have hsq :
      vecNormSq (matVecMul A ξ) ^ 2 ≤
        Lam ^ 2 * vecDot (matVecMul A ξ) ξ ^ 2 := by
    calc
      vecNormSq (matVecMul A ξ) ^ 2 ≤
          (Lam * vecDot (matVecMul A ξ) ξ) ^ (2 : ℕ) :=
            pow_le_pow_left₀ hnonneg hInvA' 2
      _ = Lam ^ (2 : ℕ) * vecDot (matVecMul A ξ) ξ ^ (2 : ℕ) := by ring
  have hmain :
      vecNormSq (matVecMul A ξ) ^ 2 ≤
        Lam ^ 2 * (vecNormSq (matVecMul A ξ) * vecNormSq ξ) := by
    exact hsq.trans (mul_le_mul_of_nonneg_left hCS (sq_nonneg Lam))
  by_cases hzero : vecNormSq (matVecMul A ξ) = 0
  · rw [hzero]
    exact mul_nonneg (sq_nonneg Lam) (vecNormSq_nonneg ξ)
  · have hpos : 0 < vecNormSq (matVecMul A ξ) := by
      exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hzero)
    have hmain' :
        vecNormSq (matVecMul A ξ) * vecNormSq (matVecMul A ξ) ≤
          vecNormSq (matVecMul A ξ) * (Lam ^ (2 : ℕ) * vecNormSq ξ) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmain
    nlinarith

theorem abs_apply_le_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (i j : Fin d) :
    |A i j| ≤ Lam := by
  let e : Vec d := Pi.single j 1
  have he_norm : vecNormSq e = 1 := by
    rw [vecNormSq, vecDot, Finset.sum_eq_single j]
    · simp [e]
    · intro k _ hkj
      simp [e, Pi.single_eq_of_ne hkj]
    · simp [e]
  have hentry : matVecMul A e i = A i j := by
    rw [matVecMul, Finset.sum_eq_single j]
    · simp [e]
    · intro k _ hkj
      simp [e, Pi.single_eq_of_ne hkj]
    · simp [e]
  have hcoord_sq : (A i j) ^ 2 ≤ vecNormSq (matVecMul A e) := by
    calc
      (A i j) ^ 2 = (matVecMul A e i) ^ 2 := by rw [hentry]
      _ ≤ ∑ k, (matVecMul A e k) ^ 2 := by
            exact Finset.single_le_sum
              (fun k _ => sq_nonneg (matVecMul A e k))
              (Finset.mem_univ i)
      _ = vecNormSq (matVecMul A e) := by
            simp [vecNormSq, vecDot, pow_two]
  have hupper : vecNormSq (matVecMul A e) ≤ Lam ^ 2 := by
    simpa [he_norm] using vecNormSq_matVecMul_le_of_isEllipticMatrix hA e
  have hLam_nonneg : 0 ≤ Lam := le_trans (le_of_lt hA.1) hA.2.1
  have hsq : (A i j) ^ 2 ≤ Lam ^ 2 := le_trans hcoord_sq hupper
  have habs_sq : |A i j| ^ 2 ≤ Lam ^ 2 := by
    simpa [sq_abs] using hsq
  nlinarith [sq_nonneg (Lam - |A i j|), habs_sq]

theorem isEllipticMatrix_transpose {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix lam Lam (matTranspose A) := by
  rcases hA with ⟨hlam_pos, hlamLam, hlower, hInv⟩
  refine ⟨hlam_pos, hlamLam, ?_, ?_⟩
  · intro ξ
    calc
      lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ) := hlower ξ
      _ = vecDot ξ (matVecMul (matTranspose A) ξ) := by
        rw [vecDot_matVecMul_transpose, vecDot_comm]
  · intro ξ
    have htransinv : matTranspose A⁻¹ = (matTranspose A)⁻¹ := by
      simpa [matTranspose] using (Matrix.transpose_nonsing_inv (A := A))
    calc
      Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ) := hInv ξ
      _ = vecDot ξ (matVecMul ((matTranspose A)⁻¹) ξ) := by
        rw [vecDot_comm, ← vecDot_matVecMul_transpose ξ ξ A⁻¹, htransinv]

theorem vecNormSq_matVecMul_symmPart_le_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ}
    {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    vecNormSq (matVecMul (symmPart A) ξ) ≤ Lam ^ 2 * vecNormSq ξ := by
  have hAT : IsEllipticMatrix lam Lam (matTranspose A) := isEllipticMatrix_transpose hA
  have hAupper := vecNormSq_matVecMul_le_of_isEllipticMatrix hA ξ
  have hATupper := vecNormSq_matVecMul_le_of_isEllipticMatrix hAT ξ
  calc
    vecNormSq (matVecMul (symmPart A) ξ)
      = (1 / 2 : ℝ) ^ 2 *
          vecNormSq (matVecMul A ξ + matVecMul (matTranspose A) ξ) := by
            rw [symmPart_eq_smul_add_transpose, smul_matVecMul, add_matVecMul, vecNormSq_smul]
    _ ≤ (1 / 2 : ℝ) ^ 2 *
          (2 * (vecNormSq (matVecMul A ξ) + vecNormSq (matVecMul (matTranspose A) ξ))) := by
            gcongr
            exact vecNormSq_add_le (matVecMul A ξ) (matVecMul (matTranspose A) ξ)
    _ ≤ Lam ^ 2 * vecNormSq ξ := by
            nlinarith

theorem vecNormSq_matVecMul_skewPart_le_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ}
    {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    vecNormSq (matVecMul (skewPart A) ξ) ≤ Lam ^ 2 * vecNormSq ξ := by
  have hAT : IsEllipticMatrix lam Lam (matTranspose A) := isEllipticMatrix_transpose hA
  have hAupper := vecNormSq_matVecMul_le_of_isEllipticMatrix hA ξ
  have hATupper := vecNormSq_matVecMul_le_of_isEllipticMatrix hAT ξ
  calc
    vecNormSq (matVecMul (skewPart A) ξ)
      = (1 / 2 : ℝ) ^ 2 *
          vecNormSq (matVecMul A ξ - matVecMul (matTranspose A) ξ) := by
            rw [skewPart_eq_smul_sub_transpose, smul_matVecMul, vecNormSq_smul]
            congr 1
            rw [sub_eq_add_neg, add_matVecMul, neg_matVecMul]
            simp [sub_eq_add_neg]
    _ ≤ (1 / 2 : ℝ) ^ 2 *
          (2 * (vecNormSq (matVecMul A ξ) + vecNormSq (matVecMul (matTranspose A) ξ))) := by
            gcongr
            exact vecNormSq_sub_le (matVecMul A ξ) (matVecMul (matTranspose A) ξ)
    _ ≤ Lam ^ 2 * vecNormSq ξ := by
            nlinarith

theorem vecDot_matVecMul_comm_of_isSymm {d : ℕ} {A : Mat d}
    (hA : A.IsSymm) (ξ η : Vec d) :
    vecDot ξ (matVecMul A η) = vecDot η (matVecMul A ξ) := by
  calc
    vecDot ξ (matVecMul A η) = vecDot ξ (matVecMul (matTranspose A) η) := by
      rw [show matTranspose A = A by simpa [matTranspose] using hA.eq]
    _ = vecDot (matVecMul A ξ) η := by
      rw [vecDot_matVecMul_transpose]
    _ = vecDot η (matVecMul A ξ) := by
      rw [vecDot_comm]

theorem isSymm_nonsingInv {d : ℕ} {A : Mat d} (hA : A.IsSymm) :
    A⁻¹.IsSymm := by
  rw [Matrix.IsSymm] at hA ⊢
  rw [Matrix.transpose_nonsing_inv, hA]

theorem vecDot_matVecMul_symmPart {d : ℕ} (A : Mat d) (ξ : Vec d) :
    vecDot ξ (matVecMul (symmPart A) ξ) = vecDot ξ (matVecMul A ξ) := by
  rw [symmPart_eq_smul_add_transpose, smul_matVecMul, add_matVecMul, vecDot_smul_right,
    vecDot_add_right, vecDot_matVecMul_transpose, vecDot_comm]
  ring

theorem sq_le_mul_of_quadratic_nonneg {a b c : ℝ} (hc : 0 ≤ c)
    (hquad : ∀ t : ℝ, 0 ≤ a - 2 * t * b + t ^ 2 * c) :
    b ^ 2 ≤ a * c := by
  by_cases hc0 : c = 0
  · by_cases hb0 : b = 0
    · simp [hb0, hc0]
    · have htest := hquad ((a + 1) / (2 * b))
      rw [hc0] at htest
      have hEq : a - 2 * (((a + 1) / (2 * b)) * b) = -1 := by
        field_simp [hb0]
        ring
      nlinarith [htest, hEq]
  · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have htest := hquad (b / c)
    field_simp [hc_pos.ne'] at htest
    nlinarith

theorem sq_vecDot_matVecMul_le_of_isSymm_of_nonneg {d : ℕ} {A : Mat d}
    (hA : A.IsSymm) (hA_nonneg : ∀ ξ : Vec d, 0 ≤ vecDot ξ (matVecMul A ξ)) (ξ η : Vec d) :
    vecDot ξ (matVecMul A η) ^ 2 ≤
      vecDot ξ (matVecMul A ξ) * vecDot η (matVecMul A η) := by
  have hcomm := vecDot_matVecMul_comm_of_isSymm hA ξ η
  have hc : 0 ≤ vecDot η (matVecMul A η) := hA_nonneg η
  refine sq_le_mul_of_quadratic_nonneg hc ?_
  intro t
  have hnonneg := hA_nonneg (ξ - t • η)
  have hquad :
      vecDot (ξ - t • η) (matVecMul A (ξ - t • η)) =
        vecDot ξ (matVecMul A ξ) - 2 * t * vecDot ξ (matVecMul A η) +
          t ^ 2 * vecDot η (matVecMul A η) := by
    rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, matVecMul_smul]
    simp [vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right,
      vecDot_smul_left, vecDot_smul_right, hcomm]
    ring
  rw [hquad] at hnonneg
  exact hnonneg

theorem sq_vecDot_matVecMul_symmPart_le_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ η : Vec d) :
    vecDot ξ (matVecMul (symmPart A) η) ^ 2 ≤
      vecDot ξ (matVecMul (symmPart A) ξ) * vecDot η (matVecMul (symmPart A) η) := by
  refine sq_vecDot_matVecMul_le_of_isSymm_of_nonneg ?_ ?_ ξ η
  · rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp [symmPart]
    ring
  · intro z
    rcases hA with ⟨hlam_pos, -, hlower, -⟩
    have hlower' :
        lam * vecNormSq z ≤ vecDot z (matVecMul (symmPart A) z) := by
      rw [vecDot_matVecMul_symmPart]
      exact hlower z
    have hnorm_nonneg : 0 ≤ vecNormSq z := vecNormSq_nonneg z
    nlinarith

theorem lowerBound_symmPart_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    lam * vecNormSq ξ ≤ vecDot ξ (matVecMul (symmPart A) ξ) := by
  rcases hA with ⟨_, _, hlower, _⟩
  rw [vecDot_matVecMul_symmPart]
  exact hlower ξ

theorem upperBound_symmPart_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    vecDot ξ (matVecMul (symmPart A) ξ) ≤ Lam * vecNormSq ξ := by
  rw [vecDot_matVecMul_symmPart]
  have hAupper : vecNormSq (matVecMul A ξ) ≤ Lam ^ 2 * vecNormSq ξ :=
    vecNormSq_matVecMul_le_of_isEllipticMatrix hA ξ
  rcases hA with ⟨hlam_pos, hlamLam, hlower, _⟩
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlamLam
  have hCS :
      vecDot ξ (matVecMul A ξ) ^ 2 ≤ vecNormSq ξ * vecNormSq (matVecMul A ξ) :=
    sq_vecDot_le_vecNormSq_mul_vecNormSq ξ (matVecMul A ξ)
  have hq_nonneg : 0 ≤ vecDot ξ (matVecMul A ξ) := by
    have hnorm_nonneg : 0 ≤ vecNormSq ξ := vecNormSq_nonneg ξ
    nlinarith [hlower ξ]
  have hmain' :
      vecDot ξ (matVecMul A ξ) ^ 2 ≤ vecNormSq ξ * (Lam ^ 2 * vecNormSq ξ) := by
    have hmul :
        vecNormSq ξ * vecNormSq (matVecMul A ξ) ≤
          vecNormSq ξ * (Lam ^ 2 * vecNormSq ξ) := by
      exact mul_le_mul_of_nonneg_left hAupper (vecNormSq_nonneg ξ)
    exact le_trans hCS hmul
  have hmain : vecDot ξ (matVecMul A ξ) ^ 2 ≤ (Lam * vecNormSq ξ) ^ 2 := by
    nlinarith [hmain']
  by_cases hzero : vecNormSq ξ = 0
  · rw [hzero]
    have hAnorm_zero : vecNormSq (matVecMul A ξ) = 0 := by
      have hAnorm_nonneg : 0 ≤ vecNormSq (matVecMul A ξ) := vecNormSq_nonneg (matVecMul A ξ)
      nlinarith [hAupper]
    have hq_zero : vecDot ξ (matVecMul A ξ) = 0 := by
      nlinarith [hCS, hAnorm_zero]
    nlinarith [hq_zero]
  · have hpos : 0 < vecNormSq ξ := by
      exact lt_of_le_of_ne (vecNormSq_nonneg ξ) (by simpa [eq_comm] using hzero)
    have hLamNorm_nonneg : 0 ≤ Lam * vecNormSq ξ := by positivity
    have habs : |vecDot ξ (matVecMul A ξ)| ≤ |Lam * vecNormSq ξ| := by
      exact sq_le_sq.mp hmain
    have hq_abs : |vecDot ξ (matVecMul A ξ)| = vecDot ξ (matVecMul A ξ) := abs_of_nonneg hq_nonneg
    have hLamNorm_abs : |Lam * vecNormSq ξ| = Lam * vecNormSq ξ :=
      abs_of_nonneg hLamNorm_nonneg
    nlinarith [habs, hq_abs, hLamNorm_abs]

theorem isUnit_det_symmPart_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) : IsUnit (symmPart A).det := by
  have hinj : Function.Injective (matVecMul (symmPart A)) := by
    intro ξ η hξη
    have hzero : matVecMul (symmPart A) (ξ - η) = 0 := by
      rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg]
      simp [hξη]
    have hlower := lowerBound_symmPart_of_isEllipticMatrix hA (ξ - η)
    rw [hzero, vecDot_zero_right] at hlower
    rcases hA with ⟨hlam_pos, -, -, -⟩
    have hnorm_zero : vecNormSq (ξ - η) = 0 := by
      nlinarith [vecNormSq_nonneg (ξ - η)]
    exact sub_eq_zero.mp (vecNormSq_eq_zero hnorm_zero)
  have hinj' : Function.Injective ((symmPart A).mulVec) := by
    simpa [matVecMul] using! hinj
  exact ((symmPart A).isUnit_iff_isUnit_det).mp
    ((Matrix.mulVec_injective_iff_isUnit (A := symmPart A)).mp hinj')

private theorem isUnit_symmPart_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) : IsUnit (symmPart A) := by
  exact ((symmPart A).isUnit_iff_isUnit_det).mpr
    (isUnit_det_symmPart_of_isEllipticMatrix hA)

private theorem symmPart_inv_nonneg_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    0 ≤ vecDot ξ (matVecMul ((symmPart A)⁻¹) ξ) := by
  let s := symmPart A
  let η := matVecMul s⁻¹ ξ
  have hs : IsUnit s := isUnit_symmPart_of_isEllipticMatrix hA
  have hsdet : IsUnit s.det := (Matrix.isUnit_iff_isUnit_det (A := s)).mp hs
  have hsη : matVecMul s η = ξ := by
    dsimp [η]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv s hsdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hlower := lowerBound_symmPart_of_isEllipticMatrix hA η
  have hmain : lam * vecNormSq η ≤ vecDot ξ η := by
    simpa [s, η, hsη, vecDot_comm] using hlower
  rcases hA with ⟨hlam_pos, -, -, -⟩
  have hηnonneg : 0 ≤ vecNormSq η := vecNormSq_nonneg η
  have hξη_nonneg : 0 ≤ vecDot ξ η := by
    nlinarith
  simpa [η] using hξη_nonneg

private theorem vecNormSq_matVecMul_symmPartInv_le_of_isEllipticMatrix_aux
    {d : ℕ} {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    vecNormSq (matVecMul ((symmPart A)⁻¹) ξ) ≤
      (lam⁻¹ * lam⁻¹) * vecNormSq ξ := by
  let s := symmPart A
  let η := matVecMul s⁻¹ ξ
  have hs : IsUnit s := isUnit_symmPart_of_isEllipticMatrix hA
  have hsdet : IsUnit s.det := (Matrix.isUnit_iff_isUnit_det (A := s)).mp hs
  have hsη : matVecMul s η = ξ := by
    dsimp [η]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv s hsdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hlower := lowerBound_symmPart_of_isEllipticMatrix hA η
  have hmain : lam * vecNormSq η ≤ vecDot ξ η := by
    simpa [s, η, hsη, vecDot_comm] using hlower
  have hCS :
      vecDot ξ η ^ 2 ≤ vecNormSq ξ * vecNormSq η :=
    sq_vecDot_le_vecNormSq_mul_vecNormSq ξ η
  have hξη_nonneg : 0 ≤ vecDot ξ η := symmPart_inv_nonneg_of_isEllipticMatrix hA ξ
  rcases hA with ⟨hlam_pos, -, -, -⟩
  by_cases hη0 : vecNormSq η = 0
  · rw [hη0]
    have hlam_inv_sq_nonneg : 0 ≤ lam⁻¹ * lam⁻¹ := by
      positivity
    nlinarith [hlam_inv_sq_nonneg, vecNormSq_nonneg ξ]
  · have hηpos : 0 < vecNormSq η := by
      exact lt_of_le_of_ne (vecNormSq_nonneg η) (by simpa [eq_comm] using hη0)
    have hsq : (lam * vecNormSq η) ^ 2 ≤ vecNormSq ξ * vecNormSq η := by
      have hsq' : (lam * vecNormSq η) ^ 2 ≤ vecDot ξ η ^ 2 := by
        have hlam_nonneg : 0 ≤ lam := le_of_lt hlam_pos
        have hlamη_nonneg : 0 ≤ lam * vecNormSq η := mul_nonneg hlam_nonneg (vecNormSq_nonneg η)
        nlinarith [hmain, hξη_nonneg, hlamη_nonneg]
      exact le_trans hsq' hCS
    have hlam_sq_bound : lam ^ 2 * vecNormSq η ≤ vecNormSq ξ := by
      nlinarith [hsq, hηpos, le_of_lt hlam_pos]
    have hlam_inv_sq_nonneg : 0 ≤ lam⁻¹ * lam⁻¹ := by
      positivity
    have hmul :
        (lam⁻¹ * lam⁻¹) * (lam ^ 2 * vecNormSq η) ≤
          (lam⁻¹ * lam⁻¹) * vecNormSq ξ := by
      exact mul_le_mul_of_nonneg_left hlam_sq_bound hlam_inv_sq_nonneg
    have hcancel : (lam⁻¹ * lam⁻¹) * (lam ^ 2 * vecNormSq η) = vecNormSq η := by
      field_simp [hlam_pos.ne']
    calc
      vecNormSq (matVecMul ((symmPart A)⁻¹) ξ) = vecNormSq η := by
        rfl
      _ = (lam⁻¹ * lam⁻¹) * (lam ^ 2 * vecNormSq η) := by
        exact hcancel.symm
      _ ≤ (lam⁻¹ * lam⁻¹) * vecNormSq ξ := hmul

theorem abs_apply_symmPartInv_le_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (i j : Fin d) :
    |((symmPart A)⁻¹ : Mat d) i j| ≤ lam⁻¹ := by
  let e : Vec d := Pi.single j 1
  have he_norm : vecNormSq e = 1 := by
    rw [vecNormSq, vecDot, Finset.sum_eq_single j]
    · simp [e]
    · intro k _ hkj
      simp [e, Pi.single_eq_of_ne hkj]
    · simp [e]
  have hentry : matVecMul ((symmPart A)⁻¹) e i = ((symmPart A)⁻¹ : Mat d) i j := by
    rw [matVecMul, Finset.sum_eq_single j]
    · simp [e]
    · intro k _ hkj
      simp [e, Pi.single_eq_of_ne hkj]
    · simp [e]
  have hcoord_sq : (((symmPart A)⁻¹ : Mat d) i j) ^ 2 ≤ vecNormSq (matVecMul ((symmPart A)⁻¹) e) := by
    calc
      (((symmPart A)⁻¹ : Mat d) i j) ^ 2 = (matVecMul ((symmPart A)⁻¹) e i) ^ 2 := by
        rw [hentry]
      _ ≤ ∑ k, (matVecMul ((symmPart A)⁻¹) e k) ^ 2 := by
            exact Finset.single_le_sum
              (fun k _ => sq_nonneg (matVecMul ((symmPart A)⁻¹) e k))
              (Finset.mem_univ i)
      _ = vecNormSq (matVecMul ((symmPart A)⁻¹) e) := by
            simp [vecNormSq, vecDot, pow_two]
  have hupper : vecNormSq (matVecMul ((symmPart A)⁻¹) e) ≤ (lam⁻¹ * lam⁻¹) := by
    simpa [he_norm] using vecNormSq_matVecMul_symmPartInv_le_of_isEllipticMatrix_aux hA e
  have hlam_inv_nonneg : 0 ≤ lam⁻¹ := by
    rcases hA with ⟨hlam_pos, -, -, -⟩
    positivity
  have hsq : (((symmPart A)⁻¹ : Mat d) i j) ^ 2 ≤ (lam⁻¹) ^ 2 := by
    simpa [pow_two] using le_trans hcoord_sq hupper
  have habs_sq : |((symmPart A)⁻¹ : Mat d) i j| ^ 2 ≤ (lam⁻¹) ^ 2 := by
    simpa [sq_abs] using hsq
  nlinarith [sq_nonneg (lam⁻¹ - |((symmPart A)⁻¹ : Mat d) i j|), habs_sq]

def IsEllipticFieldOn {d : ℕ} (lam Lam : ℝ) (U : Set (Vec d)) (a : CoeffField d) : Prop :=
  by
    classical
    exact
      Measurable (fun x i j => if x ∈ U then a x i j else 0) ∧
        ∀ x ∈ U, IsEllipticMatrix lam Lam (a x)

theorem abs_apply_le_of_isEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    {x : Vec d} (hx : x ∈ U) (i j : Fin d) :
    |a x i j| ≤ Lam :=
  abs_apply_le_of_isEllipticMatrix (hEll.2 x hx) i j

theorem measurableSet_of_isEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) :
    MeasurableSet U := by
  classical
  rcases hEll with ⟨hmeas, hell⟩
  by_cases hd : d = 0
  · subst hd
    simpa using (Subsingleton.measurableSet : MeasurableSet U)
  · let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    have hrow : Measurable (fun x => fun j => if x ∈ U then a x i j else 0) :=
      (measurable_pi_iff.mp hmeas) i
    have hdiag : Measurable (fun x => if x ∈ U then a x i i else 0) :=
      (measurable_pi_iff.mp hrow) i
    have hU :
        U = {x | 0 < if x ∈ U then a x i i else 0} := by
      ext x
      constructor
      · intro hx
        rcases hell x hx with ⟨hlam_pos, -, hlower, -⟩
        have hnorm : vecNormSq (Pi.single i 1 : Vec d) = 1 := by
          rw [vecNormSq, vecDot, Finset.sum_eq_single i]
          · simp
          · intro j _ hij
            simp [Pi.single_eq_of_ne hij]
          · simp
        have hpair :
            vecDot (Pi.single i 1 : Vec d) (matVecMul (a x) (Pi.single i 1)) = a x i i := by
          rw [vecDot, Finset.sum_eq_single i]
          · rw [matVecMul, Finset.sum_eq_single i]
            · simp
            · intro j _ hij
              simp [Pi.single_eq_of_ne hij]
            · simp
          · intro j _ hij
            simp [Pi.single_eq_of_ne hij]
          · simp
        have hdiag_lower : lam ≤ a x i i := by
          have hsingle := hlower (Pi.single i 1)
          rw [hnorm, hpair] at hsingle
          simpa using hsingle
        have hdiag_pos : 0 < a x i i := lt_of_lt_of_le hlam_pos hdiag_lower
        simp [hx, hdiag_pos]
      · intro hx
        by_contra hxU
        simp [hxU] at hx
    rw [hU]
    exact measurableSet_Ioi.preimage hdiag

namespace IsEllipticFieldOn

theorem mono {d : ℕ} {lam Lam : ℝ} {U V : Set (Vec d)} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (hV : MeasurableSet V) (hVU : V ⊆ U) :
    IsEllipticFieldOn lam Lam V a := by
  classical
  refine ⟨?_, ?_⟩
  · refine (measurable_pi_iff).2 ?_
    intro i
    refine (measurable_pi_iff).2 ?_
    intro j
    have hmeasUij : Measurable (fun x : Vec d => if x ∈ U then a x i j else 0) := by
      simpa using (measurable_pi_iff.mp (measurable_pi_iff.mp hEll.1 i) j)
    have hmeasVij :
        Measurable (V.piecewise (fun x : Vec d => if x ∈ U then a x i j else 0) (fun _ => 0)) :=
      hmeasUij.piecewise hV measurable_const
    have hEq :
        V.piecewise (fun x : Vec d => if x ∈ U then a x i j else 0) (fun _ => 0) =
          (fun x : Vec d => if x ∈ V then a x i j else 0) := by
      funext x
      by_cases hxV : x ∈ V
      · simp [Set.piecewise, hxV, hVU hxV]
      · simp [Set.piecewise, hxV]
    rw [hEq] at hmeasVij
    simpa using hmeasVij
  · intro x hx
    exact hEll.2 x (hVU hx)

theorem mono_constants {d : ℕ} {lam Lam lam' Lam' : ℝ} {U : Set (Vec d)}
    {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) (hlam'_pos : 0 < lam')
    (hlam'_le : lam' ≤ lam) (hLam_le : Lam ≤ Lam') :
    IsEllipticFieldOn lam' Lam' U a := by
  exact ⟨hEll.1, fun x hx => (hEll.2 x hx).mono hlam'_pos hlam'_le hLam_le⟩

end IsEllipticFieldOn

theorem abs_apply_symmPartInv_le_of_isEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    {x : Vec d} (hx : x ∈ U) (i j : Fin d) :
    |(((symmPart (a x))⁻¹ : Mat d) i j)| ≤ lam⁻¹ :=
  abs_apply_symmPartInv_le_of_isEllipticMatrix (hEll.2 x hx) i j

private theorem measurable_symmPart_entry {d : ℕ} {α : Type*} [MeasurableSpace α]
    {A : α → Fin d → Fin d → ℝ} (hA : Measurable A) (i j : Fin d) :
    Measurable (fun x => symmPart (A x) i j) := by
  have hij : Measurable (fun x => A x i j) :=
    measurable_pi_iff.1 (measurable_pi_iff.1 hA i) j
  have hji : Measurable (fun x => A x j i) :=
    measurable_pi_iff.1 (measurable_pi_iff.1 hA j) i
  simpa [symmPart, div_eq_mul_inv] using (hij.add hji).mul_const ((2 : ℝ)⁻¹)

private theorem measurable_matrix_inv_entry {d : ℕ} {α : Type*} [MeasurableSpace α]
    {A : α → Fin d → Fin d → ℝ} (hA : Measurable A) (i j : Fin d) :
    Measurable (fun x => (((A x : Mat d)⁻¹ : Mat d) i j)) := by
  have hdetMap : Measurable (fun M : Fin d → Fin d → ℝ => Matrix.det M) := by
    let f : (Fin d → Fin d → ℝ) → ℝ := fun M => Matrix.det M
    have hf : Continuous f := by
      simpa [f] using! (continuous_id.matrix_det : Continuous f)
    exact hf.measurable
  have hdet : Measurable (fun x => Matrix.det (A x)) := hdetMap.comp hA
  have hadjMap : Measurable (fun M : Fin d → Fin d → ℝ => Matrix.adjugate M i j) := by
    let g : (Fin d → Fin d → ℝ) → ℝ := fun M => Matrix.adjugate M i j
    have hg : Continuous g := by
      simpa [g] using! (((continuous_id.matrix_adjugate).matrix_elem i j) : Continuous g)
    exact hg.measurable
  have hadj : Measurable (fun x => Matrix.adjugate (A x) i j) := hadjMap.comp hA
  change Measurable (fun x => Ring.inverse (Matrix.det (A x)) * Matrix.adjugate (A x) i j)
  simpa [Matrix.inv_def] using! hdet.inv.mul hadj

theorem memVectorL2_matVecMul_of_isEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 U (fun x => matVecMul (a x) (f x)) := by
  classical
  rw [MemVectorL2] at hf ⊢
  refine (MeasureTheory.memLp_pi_iff).2 ?_
  intro i
  refine MeasureTheory.memLp_finsetSum
    (s := Finset.univ)
    (f := fun j : Fin d => fun x : Vec d => a x i j * f x j) ?_
  intro j hj
  have hfj : MeasureTheory.MemLp (fun x => f x j) 2 (volumeMeasureOn U) :=
    (MeasureTheory.memLp_pi_iff.mp hf) j
  let coeff : Vec d → ℝ := fun x => if x ∈ U then a x i j else 0
  have hcoeff_meas : Measurable coeff := by
    simpa [coeff] using (measurable_pi_iff.1 (measurable_pi_iff.1 hEll.1 i) j)
  have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  have hcoeff_ae : AEMeasurable (fun x => a x i j) (volumeMeasureOn U) := by
    refine (Measurable.aemeasurable hcoeff_meas).congr ?_
    filter_upwards [hmem] with x hx
    simp [coeff, hx]
  have hterm_meas :
      MeasureTheory.AEStronglyMeasurable (fun x => a x i j * f x j) (volumeMeasureOn U) :=
    hcoeff_ae.aestronglyMeasurable.mul hfj.aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂ volumeMeasureOn U, ‖a x i j * f x j‖ ≤ Lam * ‖f x j‖ := by
    filter_upwards [hmem] with x hx
    have hcoeff_le : |a x i j| ≤ Lam := abs_apply_le_of_isEllipticFieldOn hEll hx i j
    calc
      ‖a x i j * f x j‖ = |a x i j| * ‖f x j‖ := by
        rw [norm_mul, Real.norm_eq_abs]
      _ ≤ Lam * ‖f x j‖ := mul_le_mul_of_nonneg_right hcoeff_le (norm_nonneg _)
  simpa using MeasureTheory.MemLp.of_le_mul hfj hterm_meas hbound

theorem memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 U (fun x => matVecMul (symmPart (a x)) (f x)) := by
  classical
  rw [MemVectorL2] at hf ⊢
  refine (MeasureTheory.memLp_pi_iff).2 ?_
  intro i
  refine MeasureTheory.memLp_finsetSum
    (s := Finset.univ)
    (f := fun j : Fin d => fun x : Vec d => symmPart (a x) i j * f x j) ?_
  intro j hj
  have hfj : MeasureTheory.MemLp (fun x => f x j) 2 (volumeMeasureOn U) :=
    (MeasureTheory.memLp_pi_iff.mp hf) j
  let coeff : Vec d → ℝ := fun x => if x ∈ U then symmPart (a x) i j else 0
  have hij : Measurable (fun x : Vec d => if x ∈ U then a x i j else 0) := by
    simpa using (measurable_pi_iff.1 (measurable_pi_iff.1 hEll.1 i) j)
  have hji : Measurable (fun x : Vec d => if x ∈ U then a x j i else 0) := by
    simpa using (measurable_pi_iff.1 (measurable_pi_iff.1 hEll.1 j) i)
  have hcoeff_meas : Measurable coeff := by
    let s : Vec d → ℝ :=
      fun x => (if x ∈ U then a x i j else 0) + (if x ∈ U then a x j i else 0)
    have hs : Measurable s := hij.add hji
    have hscaled : Measurable (fun x : Vec d => (1 / 2 : ℝ) * s x) := measurable_const.mul hs
    convert hscaled using 1
    funext x
    by_cases hx : x ∈ U
    · simp [coeff, s, symmPart, hx, div_eq_mul_inv]
      ring
    · simp [coeff, s, symmPart, hx, div_eq_mul_inv]
  have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  have hcoeff_ae : AEMeasurable (fun x => symmPart (a x) i j) (volumeMeasureOn U) := by
    refine (Measurable.aemeasurable hcoeff_meas).congr ?_
    filter_upwards [hmem] with x hx
    simp [coeff, hx]
  have hterm_meas :
      MeasureTheory.AEStronglyMeasurable (fun x => symmPart (a x) i j * f x j)
        (volumeMeasureOn U) :=
    hcoeff_ae.aestronglyMeasurable.mul hfj.aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂ volumeMeasureOn U, ‖symmPart (a x) i j * f x j‖ ≤ Lam * ‖f x j‖ := by
    filter_upwards [hmem] with x hx
    have hcoeff_ij : |a x i j| ≤ Lam := abs_apply_le_of_isEllipticFieldOn hEll hx i j
    have hcoeff_ji : |a x j i| ≤ Lam := abs_apply_le_of_isEllipticFieldOn hEll hx j i
    have hsymm : |symmPart (a x) i j| ≤ Lam := by
      calc
        |symmPart (a x) i j|
            = |a x i j + a x j i| * (1 / 2 : ℝ) := by
                simp [symmPart, div_eq_mul_inv, abs_mul]
        _ = (1 / 2 : ℝ) * |a x i j + a x j i| := by ring
        _ ≤ (1 / 2 : ℝ) * (|a x i j| + |a x j i|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ Lam := by
              nlinarith
    calc
      ‖symmPart (a x) i j * f x j‖ = |symmPart (a x) i j| * ‖f x j‖ := by
        rw [norm_mul, Real.norm_eq_abs]
      _ ≤ Lam * ‖f x j‖ := mul_le_mul_of_nonneg_right hsymm (norm_nonneg _)
  simpa using MeasureTheory.MemLp.of_le_mul hfj hterm_meas hbound

theorem memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 U (fun x => matVecMul ((symmPart (a x))⁻¹) (f x)) := by
  classical
  rw [MemVectorL2] at hf ⊢
  refine (MeasureTheory.memLp_pi_iff).2 ?_
  intro i
  refine MeasureTheory.memLp_finsetSum
    (s := Finset.univ)
    (f := fun j : Fin d => fun x : Vec d => (((symmPart (a x))⁻¹ : Mat d) i j) * f x j) ?_
  intro j hj
  have hfj : MeasureTheory.MemLp (fun x => f x j) 2 (volumeMeasureOn U) :=
    (MeasureTheory.memLp_pi_iff.mp hf) j
  let aExt : Vec d → Fin d → Fin d → ℝ := fun x => if x ∈ U then a x else 0
  have haExt : Measurable aExt := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    convert (measurable_pi_iff.1 (measurable_pi_iff.1 hEll.1 i) j) using 1
    funext x
    by_cases hx : x ∈ U <;> simp [aExt, hx]
  let sExt : Vec d → Fin d → Fin d → ℝ := fun x => symmPart (aExt x)
  let coeff : Vec d → ℝ := fun x => (((sExt x : Mat d)⁻¹ : Mat d) i j)
  have hsymmExt : Measurable sExt := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    simpa [sExt] using measurable_symmPart_entry haExt i j
  have hcoeff_meas : Measurable coeff := by
    simpa [coeff] using measurable_matrix_inv_entry hsymmExt i j
  have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  have hcoeff_ae :
      AEMeasurable (fun x => (((symmPart (a x))⁻¹ : Mat d) i j)) (volumeMeasureOn U) := by
    refine (Measurable.aemeasurable hcoeff_meas).congr ?_
    filter_upwards [hmem] with x hx
    simp [coeff, sExt, aExt, hx]
  have hterm_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun x => (((symmPart (a x))⁻¹ : Mat d) i j) * f x j) (volumeMeasureOn U) :=
    hcoeff_ae.aestronglyMeasurable.mul hfj.aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂ volumeMeasureOn U,
        ‖(((symmPart (a x))⁻¹ : Mat d) i j) * f x j‖ ≤ lam⁻¹ * ‖f x j‖ := by
    filter_upwards [hmem] with x hx
    have hcoeff_le :
        |(((symmPart (a x))⁻¹ : Mat d) i j)| ≤ lam⁻¹ :=
      abs_apply_symmPartInv_le_of_isEllipticFieldOn hEll hx i j
    calc
      ‖(((symmPart (a x))⁻¹ : Mat d) i j) * f x j‖
          = |(((symmPart (a x))⁻¹ : Mat d) i j)| * ‖f x j‖ := by
              rw [norm_mul, Real.norm_eq_abs]
      _ ≤ lam⁻¹ * ‖f x j‖ := mul_le_mul_of_nonneg_right hcoeff_le (norm_nonneg _)
  simpa using MeasureTheory.MemLp.of_le_mul hfj hterm_meas hbound

theorem memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 U (fun x => matVecMul (skewPart (a x)) (f x)) := by
  classical
  rw [MemVectorL2] at hf ⊢
  refine (MeasureTheory.memLp_pi_iff).2 ?_
  intro i
  refine MeasureTheory.memLp_finsetSum
    (s := Finset.univ)
    (f := fun j : Fin d => fun x : Vec d => skewPart (a x) i j * f x j) ?_
  intro j hj
  have hfj : MeasureTheory.MemLp (fun x => f x j) 2 (volumeMeasureOn U) :=
    (MeasureTheory.memLp_pi_iff.mp hf) j
  let coeff : Vec d → ℝ := fun x => if x ∈ U then skewPart (a x) i j else 0
  have hij : Measurable (fun x : Vec d => if x ∈ U then a x i j else 0) := by
    simpa using (measurable_pi_iff.1 (measurable_pi_iff.1 hEll.1 i) j)
  have hji : Measurable (fun x : Vec d => if x ∈ U then a x j i else 0) := by
    simpa using (measurable_pi_iff.1 (measurable_pi_iff.1 hEll.1 j) i)
  have hcoeff_meas : Measurable coeff := by
    let s : Vec d → ℝ :=
      fun x => (if x ∈ U then a x i j else 0) - (if x ∈ U then a x j i else 0)
    have hs : Measurable s := hij.sub hji
    have hscaled : Measurable (fun x : Vec d => (1 / 2 : ℝ) * s x) := measurable_const.mul hs
    convert hscaled using 1
    funext x
    by_cases hx : x ∈ U
    · simp [coeff, s, skewPart, hx, sub_eq_add_neg, div_eq_mul_inv]
      ring
    · simp [coeff, s, skewPart, hx, sub_eq_add_neg, div_eq_mul_inv]
  have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  have hcoeff_ae : AEMeasurable (fun x => skewPart (a x) i j) (volumeMeasureOn U) := by
    refine (Measurable.aemeasurable hcoeff_meas).congr ?_
    filter_upwards [hmem] with x hx
    simp [coeff, hx]
  have hterm_meas :
      MeasureTheory.AEStronglyMeasurable (fun x => skewPart (a x) i j * f x j)
        (volumeMeasureOn U) :=
    hcoeff_ae.aestronglyMeasurable.mul hfj.aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂ volumeMeasureOn U, ‖skewPart (a x) i j * f x j‖ ≤ Lam * ‖f x j‖ := by
    filter_upwards [hmem] with x hx
    have hcoeff_ij : |a x i j| ≤ Lam := abs_apply_le_of_isEllipticFieldOn hEll hx i j
    have hcoeff_ji : |a x j i| ≤ Lam := abs_apply_le_of_isEllipticFieldOn hEll hx j i
    have hskew : |skewPart (a x) i j| ≤ Lam := by
      have hsub :
          |a x i j - a x j i| ≤ |a x i j| + |a x j i| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (a x i j) (-a x j i)
      calc
        |skewPart (a x) i j|
            = |a x i j - a x j i| * (1 / 2 : ℝ) := by
                simp [skewPart, div_eq_mul_inv, abs_mul]
        _ = (1 / 2 : ℝ) * |a x i j - a x j i| := by ring
        _ ≤ (1 / 2 : ℝ) * (|a x i j| + |a x j i|) := by
              gcongr
        _ ≤ Lam := by
              nlinarith
    calc
      ‖skewPart (a x) i j * f x j‖ = |skewPart (a x) i j| * ‖f x j‖ := by
        rw [norm_mul, Real.norm_eq_abs]
      _ ≤ Lam * ‖f x j‖ := mul_le_mul_of_nonneg_right hskew (norm_nonneg _)
  simpa using MeasureTheory.MemLp.of_le_mul hfj hterm_meas hbound

noncomputable def restrictCoeffField {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) : CoeffField d := by
  classical
  exact fun x => if x ∈ U then a x else 0

@[simp] theorem restrictCoeffField_apply_of_mem {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {x : Vec d} (hx : x ∈ U) :
    restrictCoeffField U a x = a x := by
  simp [restrictCoeffField, hx]

@[simp] theorem restrictCoeffField_apply_of_not_mem {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {x : Vec d} (hx : x ∉ U) :
    restrictCoeffField U a x = 0 := by
  simp [restrictCoeffField, hx]

@[simp] theorem restrictCoeffField_univ {d : ℕ} (a : CoeffField d) :
    restrictCoeffField Set.univ a = a := by
  funext x
  simp [restrictCoeffField]

@[simp] theorem restrictCoeffField_empty {d : ℕ} (a : CoeffField d) :
    restrictCoeffField (∅ : Set (Vec d)) a = 0 := by
  funext x
  simp [restrictCoeffField]

/-- Extension companion to `restrictCoeffField`: outside `U` we insert the
identity matrix, matching the Chapter-2 note convention. -/
noncomputable def extendByIdCoeffField {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) :
    CoeffField d := by
  classical
  exact fun x => if x ∈ U then a x else 1

@[simp] theorem extendByIdCoeffField_apply_of_mem {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {x : Vec d} (hx : x ∈ U) :
    extendByIdCoeffField U a x = a x := by
  simp [extendByIdCoeffField, hx]

@[simp] theorem extendByIdCoeffField_apply_of_not_mem {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {x : Vec d} (hx : x ∉ U) :
    extendByIdCoeffField U a x = 1 := by
  simp [extendByIdCoeffField, hx]

@[simp] theorem extendByIdCoeffField_univ {d : ℕ} (a : CoeffField d) :
    extendByIdCoeffField Set.univ a = a := by
  funext x
  simp [extendByIdCoeffField]

@[simp] theorem extendByIdCoeffField_empty {d : ℕ} (a : CoeffField d) :
    extendByIdCoeffField (∅ : Set (Vec d)) a = 1 := by
  funext x
  simp [extendByIdCoeffField]

@[simp] theorem restrictCoeffField_extendByIdCoeffField {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) :
    restrictCoeffField U (extendByIdCoeffField U a) = restrictCoeffField U a := by
  funext x
  by_cases hx : x ∈ U <;> simp [restrictCoeffField, extendByIdCoeffField, hx]

def translateCoeffField {d : ℕ} (z : Vec d) (a : CoeffField d) : CoeffField d :=
  fun x => a (fun i => x i + z i)

noncomputable def symmCoeffField {d : ℕ} (a : CoeffField d) : CoeffField d :=
  fun x => symmPart (a x)

noncomputable def skewCoeffField {d : ℕ} (a : CoeffField d) : CoeffField d :=
  fun x => skewPart (a x)

end Homogenization
