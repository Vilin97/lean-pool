/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ThetaEllipticity

/-! # Basic -/

namespace Homogenization

/-!
# Pointwise block algebra (items A4–A9)

Sharp-constant pointwise block-matrix algebra of Proposition 2.1 of the
high-moment paper (Armstrong–Kuusi–Loher, to appear).  Items A4–A8-upper
live here; the diagonal-sandwich lower bound A8 and the two-field comparison A9
(which need the block Fenchel/inverse machinery) live in
`SharpBlockBounds/DiagonalSandwich.lean`.

Notation throughout: `A : Mat d`, `s := symmPart A`, `k := skewPart A`, and
`bfA := blockMatrixOfCoeff A` is the doubled block matrix
`[[s + kᵀ s⁻¹ k, −kᵀ s⁻¹], [−s⁻¹ k, s⁻¹]]`.
-/

open Homogenization.Book.Ch02

variable {d : ℕ}

/-! ## Elementary matrix/vector helpers -/

/-- The zero matrix annihilates every vector. -/
theorem zero_matVecMul (x : Vec d) : matVecMul (0 : Mat d) x = 0 := by
  funext i; simp [matVecMul]

/-- `A = symmPart A + skewPart A` at the level of the vector action. -/
theorem matVecMul_eq_symmPart_add_skewPart (A : Mat d) (w : Vec d) :
    matVecMul A w = matVecMul (symmPart A) w + matVecMul (skewPart A) w := by
  have hAsk : (symmPart A + skewPart A : Mat d) = A := by
    ext i j; simp [symmPart, skewPart]; ring
  rw [← add_matVecMul, hAsk]

/-! ## A7 — the block quadratic identity

`(p,q) · bfA (p,q) = p · s p + (q − k p) · s⁻¹ (q − k p)`.  This is the
identity `blockMatrixOfCoeff_quadratic_eq`, re-exported under the item-A7 name. -/

/-- **A7.**  The doubled quadratic form of `bfA` in Schur-complement form. -/
theorem blockMatrixOfCoeff_quadratic (A : Mat d) (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) =
      vecDot p (matVecMul (symmPart A) p) +
        vecDot (q - matVecMul (skewPart A) p)
          (matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p)) :=
  blockMatrixOfCoeff_quadratic_eq A p q

/-! ## The image identity and the sharp flux/coercivity bound

`s + kᵀ s⁻¹ k` is the quadratic form `w ↦ (A w) · s⁻¹ (A w)`; combined with the
flux inequality `(★)` this gives the sharp nonsymmetric coercivity `A4`. -/

/-- Quadratic-form identity `w · s w + (k w) · s⁻¹ (k w) = (A w) · s⁻¹ (A w)`. -/
theorem image_symmPartInv_quadratic_eq {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (w : Vec d) :
    vecDot w (matVecMul (symmPart A) w) +
        vecDot (matVecMul (skewPart A) w)
          (matVecMul ((symmPart A)⁻¹) (matVecMul (skewPart A) w)) =
      vecDot (matVecMul A w) (matVecMul ((symmPart A)⁻¹) (matVecMul A w)) := by
  have hsdet : IsUnit (symmPart A).det :=
    (Matrix.isUnit_iff_isUnit_det (A := symmPart A)).mp
      (isUnit_symmPart_of_isEllipticMatrix hA)
  have hsInv : symmPart A * (symmPart A)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hsdet
  have hInvs : (symmPart A)⁻¹ * symmPart A = 1 := Matrix.nonsing_inv_mul _ hsdet
  have hsSymm : matTranspose (symmPart A) = symmPart A := by
    simpa [matTranspose] using matTranspose_symmPart A
  have hAw : matVecMul A w = matVecMul (symmPart A) w + matVecMul (skewPart A) w :=
    matVecMul_eq_symmPart_add_skewPart A w
  have key :
      vecDot (matVecMul A w) (matVecMul ((symmPart A)⁻¹) (matVecMul A w)) =
        vecDot (matVecMul (symmPart A) w)
            (matVecMul ((symmPart A)⁻¹) (matVecMul (symmPart A) w))
          + vecDot (matVecMul (symmPart A) w)
              (matVecMul ((symmPart A)⁻¹) (matVecMul (skewPart A) w))
          + vecDot (matVecMul (skewPart A) w)
              (matVecMul ((symmPart A)⁻¹) (matVecMul (symmPart A) w))
          + vecDot (matVecMul (skewPart A) w)
              (matVecMul ((symmPart A)⁻¹) (matVecMul (skewPart A) w)) := by
    rw [hAw, matVecMul_add, vecDot_add_left, vecDot_add_right, vecDot_add_right]
    ring
  have e1 :
      vecDot (matVecMul (symmPart A) w)
          (matVecMul ((symmPart A)⁻¹) (matVecMul (symmPart A) w)) =
        vecDot w (matVecMul (symmPart A) w) := by
    rw [matVecMul_mul, hInvs, matVecMul_one, vecDot_comm]
  have e2 :
      vecDot (matVecMul (symmPart A) w)
          (matVecMul ((symmPart A)⁻¹) (matVecMul (skewPart A) w)) = 0 := by
    rw [← vecDot_matVecMul_transpose w
          (matVecMul ((symmPart A)⁻¹) (matVecMul (skewPart A) w)) (symmPart A),
      hsSymm, matVecMul_mul, hsInv, matVecMul_one]
    exact vecDot_matVecMul_skewPart_self_eq_zero A w
  have e3 :
      vecDot (matVecMul (skewPart A) w)
          (matVecMul ((symmPart A)⁻¹) (matVecMul (symmPart A) w)) = 0 := by
    rw [matVecMul_mul, hInvs, matVecMul_one, vecDot_comm]
    exact vecDot_matVecMul_skewPart_self_eq_zero A w
  rw [key, e1, e2, e3]; ring

/-- The sharp flux/coercivity bound `(A w) · s⁻¹ (A w) ≤ Lam · ‖w‖²`, proved by
Cauchy–Schwarz against the flux inequality `(★)` for `Aᵀ`. -/
theorem image_symmPartInv_le {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (w : Vec d) :
    vecDot (matVecMul A w) (matVecMul ((symmPart A)⁻¹) (matVecMul A w)) ≤
      Lam * vecNormSq w := by
  set u := matVecMul A w with hu
  set z := matVecMul ((symmPart A)⁻¹) u with hz
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hA.1 hA.2.1
  have hsdet : IsUnit (symmPart A).det :=
    (Matrix.isUnit_iff_isUnit_det (A := symmPart A)).mp
      (isUnit_symmPart_of_isEllipticMatrix hA)
  -- s z = u, hence T = u·z = z·s z
  have hsz : matVecMul (symmPart A) z = u := by
    rw [hz, matVecMul_mul, Matrix.mul_nonsing_inv _ hsdet, matVecMul_one]
  set T := vecDot u z with hT
  have hT_nonneg : 0 ≤ T := by
    rw [hT, hz]; exact symmPart_inv_nonneg_of_isEllipticMatrix hA u
  have hTeq : T = vecDot z (matVecMul (symmPart A) z) := by
    rw [hsz, hT, vecDot_comm]
  -- T = w · Aᵀ z
  have hTw : T = vecDot w (matVecMul (matTranspose A) z) := by
    rw [vecDot_matVecMul_transpose, ← hu, hT]
  -- Cauchy–Schwarz
  have hCS : T ^ 2 ≤ vecNormSq w * vecNormSq (matVecMul (matTranspose A) z) := by
    rw [hTw]; exact sq_vecDot_le_vecNormSq_mul_vecNormSq w (matVecMul (matTranspose A) z)
  -- (★) for Aᵀ
  have hAT : IsEllipticMatrix lam Lam (matTranspose A) := isEllipticMatrix_transpose hA
  have hstar :
      vecNormSq (matVecMul (matTranspose A) z) ≤
        Lam * vecDot z (matVecMul (symmPart (matTranspose A)) z) :=
    vecNormSq_matVecMul_le_mul_vecDot_symmPart_of_isEllipticMatrix hAT z
  rw [symmPart_matTranspose, ← hTeq] at hstar
  -- combine: T² ≤ ‖w‖² · Lam · T
  have hcomb : T ^ 2 ≤ vecNormSq w * (Lam * T) :=
    le_trans hCS (mul_le_mul_of_nonneg_left hstar (vecNormSq_nonneg w))
  by_cases hT0 : T = 0
  · rw [hT0]; exact mul_nonneg hLam_pos.le (vecNormSq_nonneg w)
  · have hTpos : 0 < T := lt_of_le_of_ne hT_nonneg (Ne.symm hT0)
    nlinarith [hcomb, hTpos]

/-- The skew Schur term is controlled by `A4`'s budget:
`(k w) · s⁻¹ (k w) ≤ Lam ‖w‖² − w · s w`. -/
theorem skew_symmPartInv_le {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (w : Vec d) :
    vecDot (matVecMul (skewPart A) w)
        (matVecMul ((symmPart A)⁻¹) (matVecMul (skewPart A) w)) ≤
      Lam * vecNormSq w - vecDot w (matVecMul (symmPart A) w) := by
  have hid := image_symmPartInv_quadratic_eq hA w
  have hle := image_symmPartInv_le hA w
  linarith [hid, hle]

/-! ## A4 — nonsymmetric coercivity -/

/-- **A4.**  `s + kᵀ s⁻¹ k ≤ Θ • 1` in the Loewner order. -/
theorem upperLeft_matLoewnerLE_smul_one_of_isThetaElliptic
    {Θ : ℝ} {A : Mat d} (hA : IsThetaElliptic Θ A) :
    MatLoewnerLE
      (symmPart A + matTranspose (skewPart A) * (symmPart A)⁻¹ * skewPart A)
      (Θ • (1 : Mat d)) := by
  refine matLoewnerLE_of_forall (fun w => ?_)
  rw [vecDot_matVecMul_smul_one]
  -- expand the quadratic form of `s + kᵀ s⁻¹ k`
  have hexp :
      vecDot w
          (matVecMul
            (symmPart A + matTranspose (skewPart A) * (symmPart A)⁻¹ * skewPart A) w) =
        vecDot w (matVecMul (symmPart A) w) +
          vecDot (matVecMul (skewPart A) w)
            (matVecMul ((symmPart A)⁻¹) (matVecMul (skewPart A) w)) := by
    rw [add_matVecMul, vecDot_add_right]
    congr 1
    rw [← matVecMul_mul, ← matVecMul_mul, vecDot_matVecMul_transpose]
  rw [hexp, image_symmPartInv_quadratic_eq hA w]
  exact image_symmPartInv_le hA w

/-! ## A5 — sharp flux bounds -/

/-- Quadratic form of `Aᵀ A` is the squared image norm `‖A x‖²`. -/
theorem vecDot_matVecMul_transpose_mul_self (A : Mat d) (x : Vec d) :
    vecDot x (matVecMul (matTranspose A * A) x) = vecNormSq (matVecMul A x) := by
  rw [← matVecMul_mul, vecDot_matVecMul_transpose]; rfl

/-- Quadratic form of `A Aᵀ` is the squared adjoint image norm `‖Aᵀ x‖²`. -/
theorem vecDot_matVecMul_self_mul_transpose (A : Mat d) (x : Vec d) :
    vecDot x (matVecMul (A * matTranspose A) x) =
      vecNormSq (matVecMul (matTranspose A) x) := by
  rw [← matVecMul_mul, vecDot_comm]
  exact (vecDot_matVecMul_transpose (matVecMul (matTranspose A) x) x A).symm

/-- **A5a.**  `Aᵀ A ≤ Θ • s` in the Loewner order. -/
theorem transpose_mul_self_matLoewnerLE_smul_symmPart_of_isThetaElliptic
    {Θ : ℝ} {A : Mat d} (hA : IsThetaElliptic Θ A) :
    MatLoewnerLE (matTranspose A * A) (Θ • symmPart A) := by
  refine matLoewnerLE_of_forall (fun x => ?_)
  rw [vecDot_matVecMul_transpose_mul_self, smul_matVecMul, vecDot_smul_right]
  exact vecNormSq_matVecMul_le_mul_vecDot_symmPart_of_isEllipticMatrix hA x

/-- **A5b.**  `A Aᵀ ≤ Θ • s` in the Loewner order. -/
theorem self_mul_transpose_matLoewnerLE_smul_symmPart_of_isThetaElliptic
    {Θ : ℝ} {A : Mat d} (hA : IsThetaElliptic Θ A) :
    MatLoewnerLE (A * matTranspose A) (Θ • symmPart A) := by
  refine matLoewnerLE_of_forall (fun x => ?_)
  rw [vecDot_matVecMul_self_mul_transpose, smul_matVecMul, vecDot_smul_right]
  have hAT : IsThetaElliptic Θ (matTranspose A) := isEllipticMatrix_transpose hA
  have := vecNormSq_matVecMul_le_mul_vecDot_symmPart_of_isEllipticMatrix hAT x
  rwa [symmPart_matTranspose] at this

/-- **A5 (corollary).**  `‖A e‖² + ‖Aᵀ e‖² ≤ 2 Θ (e · s e)`. -/
theorem vecNormSq_image_add_transpose_le_of_isThetaElliptic
    {Θ : ℝ} {A : Mat d} (hA : IsThetaElliptic Θ A) (e : Vec d) :
    vecNormSq (matVecMul A e) + vecNormSq (matVecMul (matTranspose A) e) ≤
      2 * Θ * vecDot e (matVecMul (symmPart A) e) := by
  have h1 := vecNormSq_matVecMul_le_mul_vecDot_symmPart_of_isEllipticMatrix hA e
  have hAT : IsThetaElliptic Θ (matTranspose A) := isEllipticMatrix_transpose hA
  have h2 := vecNormSq_matVecMul_le_mul_vecDot_symmPart_of_isEllipticMatrix hAT e
  rw [symmPart_matTranspose] at h2
  linarith

/-! ## A6 — skew bound -/

/-- **A6.**  `‖k e‖² ≤ Θ² ‖e‖²`. -/
theorem vecNormSq_matVecMul_skewPart_le_of_isThetaElliptic
    {Θ : ℝ} {A : Mat d} (hA : IsThetaElliptic Θ A) (e : Vec d) :
    vecNormSq (matVecMul (skewPart A) e) ≤ Θ ^ 2 * vecNormSq e :=
  vecNormSq_matVecMul_skewPart_le_of_isEllipticMatrix hA e

/-! ## A8 (upper) — diagonal sandwich, upper half -/

/-- A block-diagonal matrix with scalar-multiple-of-identity blocks acts
diagonally on doubled vectors. -/
theorem blockVecDot_blockMatVecMul_blockDiag_smul_one (a b : ℝ) (p q : Vec d) :
    blockVecDot (p, q)
        (blockMatVecMul (blockDiag (a • (1 : Mat d)) (b • (1 : Mat d))) (p, q)) =
      a * vecNormSq p + b * vecNormSq q := by
  simp only [blockVecDot, blockMatVecMul_fst, blockMatVecMul_snd, blockDiag,
    zero_matVecMul, matVecMul_smul_one, add_zero, zero_add, vecDot_smul_right]
  rfl

/-- Cauchy-type parallelogram bound for a p.s.d. quadratic form:
`(a − b) · N (a − b) ≤ 2 (a · N a + b · N b)`. -/
theorem vecDot_matVecMul_sub_le_two {N : Mat d}
    (hN : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul N x)) (a b : Vec d) :
    vecDot (a - b) (matVecMul N (a - b)) ≤
      2 * (vecDot a (matVecMul N a) + vecDot b (matVecMul N b)) := by
  have key :
      vecDot (a - b) (matVecMul N (a - b)) +
          vecDot (a + b) (matVecMul N (a + b)) =
        2 * (vecDot a (matVecMul N a) + vecDot b (matVecMul N b)) := by
    simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left,
      vecDot_add_right, vecDot_neg_left, vecDot_neg_right]
    ring
  have hpos := hN (a + b)
  linarith

/-- **A8 (upper).**  `bfA ≤ blockDiag (2Θ • 1) (2 • 1)` in the block Loewner
order. -/
theorem blockMatrixOfCoeff_blockMatLoewnerLE_blockDiag_of_isThetaElliptic
    {Θ : ℝ} {A : Mat d} (hA : IsThetaElliptic Θ A) :
    BlockMatLoewnerLE (blockMatrixOfCoeff A)
      (blockDiag ((2 * Θ) • (1 : Mat d)) ((2 : ℝ) • (1 : Mat d))) := by
  intro X
  rcases X with ⟨p, q⟩
  have hquad := blockMatrixOfCoeff_quadratic A p q
  have hdiag := blockVecDot_blockMatVecMul_blockDiag_smul_one (2 * Θ) 2 p q
  have hp := upperBound_symmPart_of_isEllipticMatrix hA p
  have hp0 : 0 ≤ vecDot p (matVecMul (symmPart A) p) := by
    have := lowerBound_symmPart_of_isEllipticMatrix hA p
    nlinarith [vecNormSq_nonneg p, this]
  have hNpsd : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul ((symmPart A)⁻¹) x) :=
    fun x => symmPart_inv_nonneg_of_isEllipticMatrix hA x
  have hsub := vecDot_matVecMul_sub_le_two hNpsd q (matVecMul (skewPart A) p)
  have hq := symmPart_inv_upperBound_of_isEllipticMatrix hA q
  have hkp := skew_symmPartInv_le hA p
  rw [hquad, hdiag]
  simp only [inv_one, one_mul] at hq
  nlinarith [hp, hp0, hsub, hq, hkp]

end Homogenization
