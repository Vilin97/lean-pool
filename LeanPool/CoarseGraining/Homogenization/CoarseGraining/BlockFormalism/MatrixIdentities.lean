/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockFormalism.Structures

/-! # Matrix Identities -/

namespace Homogenization

/-!
# Block formalism -- matrix identities and conjugation

blockMatrixOfCoeff matTranspose / primal / adjoint identities,
blockVecDot / blockMatVecMul conj-by-involution lemmas, signFlip and swap
conjugation identities, and the blockMatrixOfCoeff_quadratic_eq /
matTranspose_flipFlux identities.
-/

@[simp] theorem blockMatrixOfCoeff_matTranspose_lowerRight {d : ℕ} (A : Mat d) :
    (blockMatrixOfCoeff (matTranspose A)).lowerRight = (blockMatrixOfCoeff A).lowerRight := by
  simp [blockMatrixOfCoeff, symmPart_matTranspose, skewPart_matTranspose]

theorem blockMatrixOfCoeff_matTranspose {d : ℕ} (A : Mat d) :
    blockMatrixOfCoeff (matTranspose A) =
      { upperLeft := (blockMatrixOfCoeff A).upperLeft
        upperRight := -(blockMatrixOfCoeff A).upperRight
        lowerLeft := -(blockMatrixOfCoeff A).lowerLeft
        lowerRight := (blockMatrixOfCoeff A).lowerRight } := by
  apply blockMat_ext <;> simp

theorem blockMatVecMul_blockMatrixOfCoeff_snd {d : ℕ} (A : Mat d) (p q : Vec d) :
    (blockMatVecMul (blockMatrixOfCoeff A) (p, q)).2 =
      matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p) := by
  rw [blockMatVecMul, blockMatrixOfCoeff]
  simp [sub_eq_add_neg, matVecMul_add, add_comm]
  rw [neg_matVecMul, matVecMul_neg, matVecMul_mul]

theorem blockMatVecMul_blockMatrixOfCoeff_fst {d : ℕ} (A : Mat d) (p q : Vec d) :
    (blockMatVecMul (blockMatrixOfCoeff A) (p, q)).1 =
      matVecMul (symmPart A) p +
        matVecMul (skewPart A)
          (matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p)) := by
  let lower := matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p)
  have hsnd : (blockMatVecMul (blockMatrixOfCoeff A) (p, q)).2 = lower := by
    simpa [lower] using blockMatVecMul_blockMatrixOfCoeff_snd A p q
  have hfst :
      (blockMatVecMul (blockMatrixOfCoeff A) (p, q)).1 =
        matVecMul (symmPart A) p + matVecMul (skewPart A) lower := by
    rw [← hsnd]
    rw [blockMatVecMul, blockMatrixOfCoeff]
    simp [matTranspose_skewPart]
    rw [add_matVecMul, matVecMul_add]
    have hneg :
        matVecMul (skewPart A) (matVecMul (-((symmPart A)⁻¹ * skewPart A)) p) =
          -matVecMul (skewPart A * ((symmPart A)⁻¹ * skewPart A)) p := by
      rw [neg_matVecMul, matVecMul_neg, matVecMul_mul]
    have hpos :
        matVecMul (skewPart A) (matVecMul (symmPart A)⁻¹ q) =
          matVecMul (skewPart A * (symmPart A)⁻¹) q := by
      rw [matVecMul_mul]
    rw [hneg, hpos]
    rw [neg_matVecMul]
    simp [Matrix.mul_assoc, add_left_comm, add_comm]
  simpa [lower] using hfst

theorem blockMatVecMul_blockMatrixOfCoeff_primal_of_isUnit_det_symmPart {d : ℕ}
    (A : Mat d) (hdet : IsUnit (symmPart A).det) (ξ : Vec d) :
    blockMatVecMul (blockMatrixOfCoeff A) (ξ, matVecMul A ξ) =
      (matVecMul A ξ, ξ) := by
  let s := symmPart A
  let k := skewPart A
  have hA : A = s + k := by
    ext i j
    simp [s, k, symmPart, skewPart, sub_eq_add_neg]
    ring
  have hsInvMul : matVecMul s⁻¹ (matVecMul s ξ) = ξ := by
    rw [matVecMul_mul, Matrix.nonsing_inv_mul s hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hkT : matTranspose k = -k := by
    ext i j
    simp [k, skewPart, matTranspose]
    ring
  apply Prod.ext
  · calc
      (blockMatVecMul (blockMatrixOfCoeff A) (ξ, matVecMul A ξ)).1 =
          matVecMul s ξ +
            matVecMul (matTranspose k) (matVecMul s⁻¹ (matVecMul k ξ)) -
            matVecMul (matTranspose k) (matVecMul s⁻¹ (matVecMul A ξ)) := by
              simp [blockMatVecMul, blockMatrixOfCoeff, s, k, hkT, add_matVecMul, matVecMul_mul,
                sub_eq_add_neg, neg_matVecMul, Matrix.mul_assoc]
      _ = matVecMul s ξ +
            matVecMul (matTranspose k) (matVecMul s⁻¹ (matVecMul k ξ)) -
            matVecMul (matTranspose k) (ξ + matVecMul s⁻¹ (matVecMul k ξ)) := by
              rw [hA, add_matVecMul, matVecMul_add, hsInvMul]
      _ = matVecMul s ξ - matVecMul (matTranspose k) ξ := by
            rw [matVecMul_add]
            simp [sub_eq_add_neg, add_assoc, add_comm]
      _ = matVecMul s ξ + matVecMul k ξ := by
            rw [hkT, neg_matVecMul]
            simp [sub_eq_add_neg]
      _ = matVecMul A ξ := by
            rw [hA, add_matVecMul]
  · calc
      (blockMatVecMul (blockMatrixOfCoeff A) (ξ, matVecMul A ξ)).2 =
          -(matVecMul s⁻¹ (matVecMul k ξ)) + matVecMul s⁻¹ (matVecMul A ξ) := by
            simp [blockMatVecMul, blockMatrixOfCoeff, s, k, matVecMul_mul, neg_matVecMul]
      _ = -(matVecMul s⁻¹ (matVecMul k ξ)) + (ξ + matVecMul s⁻¹ (matVecMul k ξ)) := by
            rw [hA, add_matVecMul, matVecMul_add, hsInvMul]
      _ = ξ := by
            simp [add_assoc, add_comm]

theorem blockMatVecMul_blockMatrixOfCoeff_adjoint_of_isUnit_det_symmPart {d : ℕ}
    (A : Mat d) (hdet : IsUnit (symmPart A).det) (η : Vec d) :
    blockMatVecMul (blockMatrixOfCoeff A) (η, -matVecMul (matTranspose A) η) =
      (matVecMul (matTranspose A) η, -η) := by
  have hdetT : IsUnit (symmPart (matTranspose A)).det := by
    simpa [symmPart_matTranspose] using hdet
  have hprimal :=
    blockMatVecMul_blockMatrixOfCoeff_primal_of_isUnit_det_symmPart
      (A := matTranspose A) hdetT η
  apply Prod.ext
  · simpa [blockMatrixOfCoeff_matTranspose, blockMatVecMul, matVecMul_neg, neg_matVecMul] using
      congrArg Prod.fst hprimal
  · have hsnd :
        -matVecMul (blockMatrixOfCoeff A).lowerRight (matVecMul (matTranspose A) η) +
            matVecMul (blockMatrixOfCoeff A).lowerLeft η =
          -η := by
        simpa [blockMatrixOfCoeff_matTranspose, blockMatVecMul, matVecMul_neg, neg_matVecMul] using
          congrArg Neg.neg (congrArg Prod.snd hprimal)
    calc
      (blockMatVecMul (blockMatrixOfCoeff A) (η, -matVecMul (matTranspose A) η)).2 =
          matVecMul (blockMatrixOfCoeff A).lowerLeft η +
            -matVecMul (blockMatrixOfCoeff A).lowerRight (matVecMul (matTranspose A) η) := by
              simp [blockMatVecMul, matVecMul_neg]
      _ = -matVecMul (blockMatrixOfCoeff A).lowerRight (matVecMul (matTranspose A) η) +
            matVecMul (blockMatrixOfCoeff A).lowerLeft η := by
              simp [add_comm]
      _ = -η := hsnd

theorem blockMatVecMul_blockMatrixOfCoeff_primal_of_isEllipticMatrix {d : ℕ}
    {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    blockMatVecMul (blockMatrixOfCoeff A) (ξ, matVecMul A ξ) =
      (matVecMul A ξ, ξ) :=
  blockMatVecMul_blockMatrixOfCoeff_primal_of_isUnit_det_symmPart A
    (isUnit_det_symmPart_of_isEllipticMatrix hA) ξ

theorem blockMatVecMul_blockMatrixOfCoeff_adjoint_of_isEllipticMatrix {d : ℕ}
    {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (η : Vec d) :
    blockMatVecMul (blockMatrixOfCoeff A) (η, -matVecMul (matTranspose A) η) =
      (matVecMul (matTranspose A) η, -η) :=
  blockMatVecMul_blockMatrixOfCoeff_adjoint_of_isUnit_det_symmPart A
    (isUnit_det_symmPart_of_isEllipticMatrix hA) η

theorem blockVecDot_blockVecConj_of_transpose_eq_self_of_mul_self_eq_one {d : ℕ}
    {R : Mat d} (hR : matTranspose R = R) (hR2 : R * R = 1) (X Y : BlockVec d) :
    blockVecDot (blockVecConj R X) (blockVecConj R Y) = blockVecDot X Y := by
  rcases X with ⟨p, q⟩
  rcases Y with ⟨u, v⟩
  simp [blockVecConj, blockVecDot,
    vecDot_matVecMul_conj_of_transpose_eq_self_of_mul_self_eq_one (hR := hR) (hR2 := hR2)]

theorem blockMatVecMul_blockMatConj_of_mul_self_eq_one {d : ℕ} {R : Mat d}
    (hR2 : R * R = 1) (B : BlockMat d) (X : BlockVec d) :
    blockMatVecMul (blockMatConj R B) (blockVecConj R X) =
      blockVecConj R (blockMatVecMul B X) := by
  rcases X with ⟨p, q⟩
  apply Prod.ext
  · calc
      (blockMatVecMul (blockMatConj R B) (blockVecConj R (p, q))).1
          = matVecMul (R * B.upperLeft * R) (matVecMul R p) +
              matVecMul (R * B.upperRight * R) (matVecMul R q) := by
                rfl
      _ = matVecMul R (matVecMul B.upperLeft p) +
            matVecMul R (matVecMul B.upperRight q) := by
                rw [matVecMul_mul_mul_cancel_of_mul_self_eq_one (R := R) (A := B.upperLeft)
                      (x := p) hR2,
                  matVecMul_mul_mul_cancel_of_mul_self_eq_one (R := R) (A := B.upperRight)
                    (x := q) hR2]
      _ = matVecMul R (matVecMul B.upperLeft p + matVecMul B.upperRight q) := by
            rw [matVecMul_add]
      _ = (blockVecConj R (blockMatVecMul B (p, q))).1 := by
            rfl
  · calc
      (blockMatVecMul (blockMatConj R B) (blockVecConj R (p, q))).2
          = matVecMul (R * B.lowerLeft * R) (matVecMul R p) +
              matVecMul (R * B.lowerRight * R) (matVecMul R q) := by
                rfl
      _ = matVecMul R (matVecMul B.lowerLeft p) +
            matVecMul R (matVecMul B.lowerRight q) := by
                rw [matVecMul_mul_mul_cancel_of_mul_self_eq_one (R := R) (A := B.lowerLeft)
                      (x := p) hR2,
                  matVecMul_mul_mul_cancel_of_mul_self_eq_one (R := R) (A := B.lowerRight)
                    (x := q) hR2]
      _ = matVecMul R (matVecMul B.lowerLeft p + matVecMul B.lowerRight q) := by
            rw [matVecMul_add]
      _ = (blockVecConj R (blockMatVecMul B (p, q))).2 := by
            rfl

theorem blockMatrixOfCoeff_conj_of_transpose_eq_self_of_mul_self_eq_one {d : ℕ}
    {R A : Mat d} (hR : matTranspose R = R) (hR2 : R * R = 1) :
    blockMatrixOfCoeff (R * A * R) = blockMatConj R (blockMatrixOfCoeff A) := by
  apply blockMat_ext
  · calc
      (blockMatrixOfCoeff (R * A * R)).upperLeft
          = R * symmPart A * R +
              (R * matTranspose (skewPart A) * R) * (R * (symmPart A)⁻¹ * R) *
                (R * skewPart A * R) := by
                  simp [blockMatrixOfCoeff, symmPart_mul_mul_of_transpose_eq_self hR,
                    skewPart_mul_mul_of_transpose_eq_self hR,
                    matTranspose_mul_mul_of_transpose_eq_self hR,
                    nonsing_inv_mul_mul_of_mul_self_eq_one (R := R) (A := symmPart A) hR2]
      _ = R * symmPart A * R +
            (R * (matTranspose (skewPart A) * (symmPart A)⁻¹) * R) *
              (R * skewPart A * R) := by
              rw [mul_mul_mul_conj_of_mul_self_eq_one (R := R)
                (B := matTranspose (skewPart A)) (C := (symmPart A)⁻¹) hR2]
      _ = R * symmPart A * R +
            R * (matTranspose (skewPart A) * (symmPart A)⁻¹ * skewPart A) * R := by
              rw [mul_mul_mul_conj_of_mul_self_eq_one (R := R)
                (B := matTranspose (skewPart A) * (symmPart A)⁻¹) (C := skewPart A) hR2]
      _ = (blockMatConj R (blockMatrixOfCoeff A)).upperLeft := by
              simp [blockMatConj, blockMatrixOfCoeff, Matrix.mul_assoc, Matrix.mul_add, add_mul]
  · calc
      (blockMatrixOfCoeff (R * A * R)).upperRight
          = -((R * matTranspose (skewPart A) * R) * (R * (symmPart A)⁻¹ * R)) := by
              simp [blockMatrixOfCoeff, symmPart_mul_mul_of_transpose_eq_self hR,
                skewPart_mul_mul_of_transpose_eq_self hR,
                matTranspose_mul_mul_of_transpose_eq_self hR,
                nonsing_inv_mul_mul_of_mul_self_eq_one (R := R) (A := symmPart A) hR2]
      _ = -(R * (matTranspose (skewPart A) * (symmPart A)⁻¹) * R) := by
              rw [mul_mul_mul_conj_of_mul_self_eq_one (R := R)
                (B := matTranspose (skewPart A)) (C := (symmPart A)⁻¹) hR2]
      _ = (blockMatConj R (blockMatrixOfCoeff A)).upperRight := by
              simp [blockMatConj, blockMatrixOfCoeff, Matrix.mul_assoc]
  · calc
      (blockMatrixOfCoeff (R * A * R)).lowerLeft
          = -((R * (symmPart A)⁻¹ * R) * (R * skewPart A * R)) := by
              simp [blockMatrixOfCoeff, symmPart_mul_mul_of_transpose_eq_self hR,
                skewPart_mul_mul_of_transpose_eq_self hR,
                nonsing_inv_mul_mul_of_mul_self_eq_one (R := R) (A := symmPart A) hR2]
      _ = -(R * ((symmPart A)⁻¹ * skewPart A) * R) := by
              rw [mul_mul_mul_conj_of_mul_self_eq_one (R := R)
                (B := (symmPart A)⁻¹) (C := skewPart A) hR2]
      _ = (blockMatConj R (blockMatrixOfCoeff A)).lowerLeft := by
              simp [blockMatConj, blockMatrixOfCoeff, Matrix.mul_assoc]
  · simp [blockMatConj, blockMatrixOfCoeff, symmPart_mul_mul_of_transpose_eq_self hR,
      nonsing_inv_mul_mul_of_mul_self_eq_one (R := R) (A := symmPart A) hR2]

theorem matTranspose_signFlipMatrix {d : ℕ} (i : Fin d) :
    matTranspose (signFlipMatrix i) = signFlipMatrix i := by
  ext r c
  by_cases h : r = c
  · subst c
    simp [signFlipMatrix, matTranspose]
  · simp [signFlipMatrix, matTranspose, h, eq_comm]

theorem signFlipMatrix_mul_self {d : ℕ} (i : Fin d) :
    signFlipMatrix i * signFlipMatrix i = 1 := by
  ext r c
  by_cases h : r = c
  · subst c
    by_cases hr : r = i <;> simp [signFlipMatrix, hr]
  · simp [signFlipMatrix, h]

theorem blockMatrixOfCoeff_signFlipMatrix_conj {d : ℕ} (i : Fin d) (A : Mat d) :
    blockMatrixOfCoeff (signFlipMatrix i * A * signFlipMatrix i) =
      blockMatConj (signFlipMatrix i) (blockMatrixOfCoeff A) := by
  exact blockMatrixOfCoeff_conj_of_transpose_eq_self_of_mul_self_eq_one
    (R := signFlipMatrix i) (A := A)
    (matTranspose_signFlipMatrix i) (signFlipMatrix_mul_self i)

theorem blockMatrixOfCoeff_swap_conj {d : ℕ} (i j : Fin d) (A : Mat d) :
    blockMatrixOfCoeff (Matrix.swap ℝ i j * A * Matrix.swap ℝ i j) =
      blockMatConj (Matrix.swap ℝ i j) (blockMatrixOfCoeff A) := by
  exact blockMatrixOfCoeff_conj_of_transpose_eq_self_of_mul_self_eq_one
    (R := Matrix.swap ℝ i j) (A := A)
    (by simp [matTranspose])
    (Matrix.swap_mul_self (R := ℝ) i j)

theorem blockMatrixOfCoeff_quadratic_eq {d : ℕ} (A : Mat d) (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) =
      vecDot p (matVecMul (symmPart A) p) +
        vecDot (q - matVecMul (skewPart A) p)
          (matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p)) := by
  let s := symmPart A
  let k := skewPart A
  let sInv := s⁻¹
  let kp := matVecMul k p
  calc
    blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q))
      = vecDot p (matVecMul s p)
          + vecDot p (matVecMul (matTranspose k) (matVecMul sInv kp))
          - vecDot p (matVecMul (matTranspose k) (matVecMul sInv q))
          - vecDot q (matVecMul sInv kp)
          + vecDot q (matVecMul sInv q) := by
            simp [blockVecDot, blockMatVecMul, blockMatrixOfCoeff, s, k, sInv, kp,
              add_matVecMul, matVecMul_mul, vecDot_add_right, sub_eq_add_neg, Matrix.mul_assoc]
            rw [neg_matVecMul, neg_matVecMul, neg_matVecMul,
              vecDot_neg_right, vecDot_neg_right, vecDot_neg_right]
            simp
            ring
    _ = vecDot p (matVecMul s p)
          + vecDot kp (matVecMul sInv kp)
          - vecDot kp (matVecMul sInv q)
          - vecDot q (matVecMul sInv kp)
          + vecDot q (matVecMul sInv q) := by
            rw [vecDot_matVecMul_transpose p (matVecMul sInv kp) k,
              vecDot_matVecMul_transpose p (matVecMul sInv q) k]
    _ = vecDot p (matVecMul s p) +
          vecDot (q - kp) (matVecMul sInv (q - kp)) := by
            simp [kp, sub_eq_add_neg, matVecMul_add, matVecMul_neg,
              vecDot_add_left, vecDot_add_right,
              vecDot_neg_left, vecDot_neg_right]
            ring
    _ = vecDot p (matVecMul (symmPart A) p) +
          vecDot (q - matVecMul (skewPart A) p)
            (matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p)) := by
              simp [s, k, sInv, kp]

theorem blockMatrixOfCoeff_quadratic_matTranspose_flipFlux {d : ℕ} (A : Mat d) (p q : Vec d) :
    blockVecDot (p, -q) (blockMatVecMul (blockMatrixOfCoeff (matTranspose A)) (p, -q)) =
      blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) := by
  let r := q - matVecMul (skewPart A) p
  rw [blockMatrixOfCoeff_quadratic_eq, blockMatrixOfCoeff_quadratic_eq, symmPart_matTranspose]
  have hr : -q - matVecMul (skewPart (matTranspose A)) p = -r := by
    funext i
    rw [skewPart_matTranspose, neg_matVecMul]
    simp [r, sub_eq_add_neg]
    ring
  rw [hr]
  have hneg :
      vecDot (-r) (matVecMul ((symmPart A)⁻¹) (-r)) =
        vecDot r (matVecMul ((symmPart A)⁻¹) r) := by
    simp [matVecMul_neg, vecDot_neg_left, vecDot_neg_right]
  simpa [r] using hneg

theorem blockVecDot_blockMatVecMul_blockMatrixOfCoeff_conj_of_transpose_eq_self_of_mul_self_eq_one
    {d : ℕ} {R A : Mat d} (hR : matTranspose R = R) (hR2 : R * R = 1) (X : BlockVec d) :
    blockVecDot (blockVecConj R X)
      (blockMatVecMul (blockMatrixOfCoeff (R * A * R)) (blockVecConj R X)) =
        blockVecDot X (blockMatVecMul (blockMatrixOfCoeff A) X) := by
  rw [blockMatrixOfCoeff_conj_of_transpose_eq_self_of_mul_self_eq_one hR hR2,
    blockMatVecMul_blockMatConj_of_mul_self_eq_one hR2,
    blockVecDot_blockVecConj_of_transpose_eq_self_of_mul_self_eq_one hR hR2]

end Homogenization
