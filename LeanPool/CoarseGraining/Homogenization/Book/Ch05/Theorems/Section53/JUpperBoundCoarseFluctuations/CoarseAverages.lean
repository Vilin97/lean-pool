/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.WeakNormInput

/-! # Coarse Averages -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

/-!
# Coarse-average terms in the third Section 5.3 lemma

This file starts the bridge from the high-scale average terms in
`WeakNormsMaximizer` to the manuscript coarse block-matrix fluctuation.  The
first step is deterministic: on the a.e.-elliptic support, the Ch4 measurable
scalar-response average over a cube agrees with the corresponding coarse-block
formula from Chapter 2.
-/

noncomputable section

private theorem canonicalScalarResponseGradientAverageCubeSet_self_eq_blockMatrix
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (p q : Vec d) :
    Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q a.toFun =
      -p + matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight q -
        matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft p := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  let v :=
    (Ch02.canonicalMaximizer
      (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ) p q).toSolution
  have hself : Q ∈ descendantsAtDepth Q 0 := by
    simp [descendantsAtDepth_zero]
  have hAverage :=
    Ch04.canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer
      a ha (Q := Q) (R := Q) (j := 0) hself p q
  have hCubeAverage :
      cubeAverageVec Q (fun x => v.toH1.grad x) =
        Ch02.averageGradient (Ch02.cubeDomain Q) aQ v := by
    ext i
    rw [Ch02.averageGradient, Ch02.averageVec,
      JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
    rfl
  have hCh02 :=
    Ch02.averageGradient_canonicalMaximizer_eq_blockMatrix
      (Ch02.cubeDomain Q) aQ p q
  have hCoarse :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) aQ := by
    simpa [F, aQ] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  calc
    Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q a.toFun =
        cubeAverageVec Q (fun x => v.toH1.grad x) := by
          simpa [F, aQ, v] using hAverage
    _ = Ch02.averageGradient (Ch02.cubeDomain Q) aQ v := hCubeAverage
    _ =
        -p + matVecMul (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) aQ).lowerRight q -
          matVecMul (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) aQ).lowerLeft p := by
          simpa [aQ, v] using hCh02
    _ =
        -p + matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight q -
          matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft p := by
          rw [hCoarse]

private theorem canonicalScalarResponseFluxAverageCubeSet_self_eq_blockMatrix
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (p q : Vec d) :
    Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun =
      q + matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperRight q -
        matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft p := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  let v :=
    (Ch02.canonicalMaximizer
      (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ) p q).toSolution
  have hself : Q ∈ descendantsAtDepth Q 0 := by
    simp [descendantsAtDepth_zero]
  have hAverage :=
    Ch04.canonicalScalarResponseFluxAverageCubeSet_eq_cubeAverageVec_canonicalMaximizerFlux
      a ha (Q := Q) (R := Q) (j := 0) hself p q
  have hCubeAverage :
      cubeAverageVec Q (fun x => matVecMul (aQ.toCoeffField x) (v.toH1.grad x)) =
        Ch02.averageFlux (Ch02.cubeDomain Q) aQ v := by
    ext i
    rw [Ch02.averageFlux, Ch02.averageVec,
      JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
    rfl
  have hCh02 :=
    Ch02.averageFlux_canonicalMaximizer_eq_blockMatrix
      (Ch02.cubeDomain Q) aQ p q
  have hCoarse :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) aQ := by
    simpa [F, aQ] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  calc
    Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun =
        cubeAverageVec Q (fun x => matVecMul (aQ.toCoeffField x) (v.toH1.grad x)) := by
          simpa [F, aQ, v] using hAverage
    _ = Ch02.averageFlux (Ch02.cubeDomain Q) aQ v := hCubeAverage
    _ =
        q + matVecMul (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) aQ).upperRight q -
          matVecMul (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) aQ).upperLeft p := by
          simpa [aQ, v] using hCh02
    _ =
        q + matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperRight q -
          matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft p := by
          rw [hCoarse]

private theorem matVecMul_smul_one {d : ℕ} (c : ℝ) (x : Vec d) :
    matVecMul (c • (1 : Mat d)) x = c • x := by
  rw [smul_matVecMul]
  change c • (Matrix.mulVec (1 : Matrix (Fin d) (Fin d) ℝ) x) = c • x
  rw [Matrix.one_mulVec]

private theorem zero_matVecMul {d : ℕ} (x : Vec d) :
    matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

private noncomputable def scalarAnnealedBlockMatrixAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ) :
    BlockMat d :=
  Ch02.blockDiag
    (hP.barSigmaAtScale hStruct m • (1 : Mat d))
    ((hP.barSigmaStarAtScale hStruct m)⁻¹ • (1 : Mat d))

private theorem special_average_mismatch_eq_reflected_block_fluctuation
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m : ℕ) (R : TriadicCube d) (e : Vec d) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    let A := coarseBlockMatrix (cubeSet R) a.toFun
    let Abar := scalarAnnealedBlockMatrixAtScale hP hStruct (m : ℤ)
    let P_e : BlockVec d := (-q_e, p_e)
    (-(Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e),
      -(Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e)) =
        blockMatVecMul
          (ofFullBlockMat (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)))
          P_e := by
  dsimp only
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let A := coarseBlockMatrix (cubeSet R) a.toFun
  let Abar := scalarAnnealedBlockMatrixAtScale hP hStruct (m : ℤ)
  let P_e : BlockVec d := (-q_e, p_e)
  have hgrad :=
    canonicalScalarResponseGradientAverageCubeSet_self_eq_blockMatrix a ha R p_e q_e
  have hflux :=
    canonicalScalarResponseFluxAverageCubeSet_self_eq_blockMatrix a ha R p_e q_e
  have hblock :
      blockMatVecMul
          (ofFullBlockMat (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)))
          P_e =
        blockMatVecMul (blockReflect A) P_e - blockMatVecMul (blockReflect Abar) P_e :=
    blockMatVecMul_ofFullBlockMat_sub (blockReflect A) (blockReflect Abar) P_e
  rw [hblock]
  rw [hgrad, hflux]
  ext i <;>
    simp [p_e, q_e, P_e, A, Abar, scalarAnnealedBlockMatrixAtScale,
      Ch02.blockDiag, blockReflect, blockMatVecMul, matVecMul_smul_one,
      matVecMul_neg, matVecMul_smul, zero_matVecMul, sub_eq_add_neg] <;>
    ring

private theorem vecNormSq_neg {d : ℕ} (x : Vec d) :
    vecNormSq (-x) = vecNormSq x := by
  simp [vecNormSq, vecDot]

private theorem vecNormSq_sub_comm {d : ℕ} (x y : Vec d) :
    vecNormSq (x - y) = vecNormSq (y - x) := by
  have h : x - y = -(y - x) := by
    ext i
    simp [sub_eq_add_neg]
  rw [h, vecNormSq_neg]

private noncomputable def reflectedBlockFluctuationOperatorNormSqAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m : ℤ) (R : TriadicCube d) (a : RegCoeffField d) : ℝ :=
  let A := coarseBlockMatrix (cubeSet R) a.toFun
  let Abar := scalarAnnealedBlockMatrixAtScale hP hStruct m
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar))‖ ^ 2

private noncomputable def starInvSqrtDiag {d : ℕ} (b c : ℝ) : BlockCoord d → ℝ
  | Sum.inl _ => Real.sqrt c
  | Sum.inr _ => (Real.sqrt b)⁻¹

private noncomputable def starSqrtDiag {d : ℕ} (b c : ℝ) : BlockCoord d → ℝ
  | Sum.inl _ => (Real.sqrt c)⁻¹
  | Sum.inr _ => Real.sqrt b

private def blockCoordSwapEquiv (d : ℕ) : BlockCoord d ≃ BlockCoord d where
  toFun
    | Sum.inl i => Sum.inr i
    | Sum.inr i => Sum.inl i
  invFun
    | Sum.inl i => Sum.inr i
    | Sum.inr i => Sum.inl i
  left_inv := by
    intro α
    cases α <;> rfl
  right_inv := by
    intro α
    cases α <;> rfl

private noncomputable def fullBlockInvSqrtDiag {d : ℕ} (b c : ℝ) : BlockCoord d → ℝ
  | Sum.inl _ => (Real.sqrt b)⁻¹
  | Sum.inr _ => Real.sqrt c

private theorem toFullBlockMat_blockReflect_eq_reindex_swap {d : ℕ} (A : BlockMat d) :
    toFullBlockMat (blockReflect A) =
      Matrix.reindex (blockCoordSwapEquiv d) (blockCoordSwapEquiv d) (toFullBlockMat A) := by
  ext α β
  cases α <;> cases β <;> rfl

private theorem diagonal_starInvSqrtDiag_eq_reindex_fullBlockInvSqrtDiag
    {d : ℕ} (b c : ℝ) :
    Matrix.diagonal (starInvSqrtDiag (d := d) b c) =
      Matrix.reindex (blockCoordSwapEquiv d) (blockCoordSwapEquiv d)
        (Matrix.diagonal (fullBlockInvSqrtDiag b c)) := by
  ext α β
  cases α <;> cases β <;>
    simp [Matrix.diagonal, blockCoordSwapEquiv, starInvSqrtDiag, fullBlockInvSqrtDiag]

private theorem reindex_swap_mul {d : ℕ} (M N : FullBlockMat d) :
      Matrix.reindex (blockCoordSwapEquiv d) (blockCoordSwapEquiv d) (M * N) =
        Matrix.reindex (blockCoordSwapEquiv d) (blockCoordSwapEquiv d) M *
          Matrix.reindex (blockCoordSwapEquiv d) (blockCoordSwapEquiv d) N := by
  exact map_mul (Matrix.reindexAlgEquiv ℝ ℝ (blockCoordSwapEquiv d)) M N

private theorem reflectedNormalizedBlockFluctuationMatrix_eq_reindex_full
    {d : ℕ} (b c : ℝ) (A Abar : BlockMat d) :
    let Dstar : FullBlockMat d := Matrix.diagonal (starInvSqrtDiag b c)
    let D : FullBlockMat d := Matrix.diagonal (fullBlockInvSqrtDiag b c)
    Dstar * (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)) * Dstar =
      Matrix.reindex (blockCoordSwapEquiv d) (blockCoordSwapEquiv d)
        (D * (toFullBlockMat A - toFullBlockMat Abar) * D) := by
  dsimp only
  let e := blockCoordSwapEquiv d
  let Dstar : FullBlockMat d := Matrix.diagonal (starInvSqrtDiag b c)
  let D : FullBlockMat d := Matrix.diagonal (fullBlockInvSqrtDiag b c)
  let M : FullBlockMat d := toFullBlockMat A - toFullBlockMat Abar
  have hD : Dstar = Matrix.reindex e e D := by
    simpa [Dstar, D, e] using
      diagonal_starInvSqrtDiag_eq_reindex_fullBlockInvSqrtDiag (d := d) b c
  have hM :
      toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar) =
        Matrix.reindex e e M := by
    rw [toFullBlockMat_blockReflect_eq_reindex_swap A,
      toFullBlockMat_blockReflect_eq_reindex_swap Abar]
    ext α β
    rfl
  calc
    Dstar * (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)) * Dstar =
        Matrix.reindex e e D * Matrix.reindex e e M * Matrix.reindex e e D := by
          rw [hD, hM]
    _ = Matrix.reindex e e (D * M) * Matrix.reindex e e D := by
          rw [← reindex_swap_mul]
    _ = Matrix.reindex e e ((D * M) * D) := by
          rw [← reindex_swap_mul]
    _ = Matrix.reindex e e (D * (toFullBlockMat A - toFullBlockMat Abar) * D) := by
          rfl

private theorem starInvSqrtDiag_mul_starSqrtDiag {d : ℕ} {b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) :
    Matrix.diagonal (starInvSqrtDiag (d := d) b c) *
      Matrix.diagonal (starSqrtDiag b c) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext α β
  by_cases h : α = β
  · subst β
    cases α
    · simp [starInvSqrtDiag, starSqrtDiag, ne_of_gt (Real.sqrt_pos_of_pos hc)]
    · simp [starInvSqrtDiag, starSqrtDiag, ne_of_gt (Real.sqrt_pos_of_pos hb)]
  · simp [Matrix.diagonal, h]

private theorem norm_sq_starInvSqrtDiag_mulVec_toFullBlockVec
    {d : ℕ} {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (X : BlockVec d) :
    ‖(WithLp.toLp 2
        (Matrix.mulVec (Matrix.diagonal (starInvSqrtDiag (d := d) b c)) (toFullBlockVec X)) :
        PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
      c * vecNormSq X.1 + b⁻¹ * vecNormSq X.2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  rcases X with ⟨x, y⟩
  simp [starInvSqrtDiag, toFullBlockVec, Matrix.mulVec, vecNormSq, vecDot,
    abs_of_nonneg (Real.sqrt_nonneg c), abs_of_nonneg (Real.sqrt_nonneg b)]
  simp_rw [mul_pow, sq_abs, inv_pow]
  rw [Real.sq_sqrt hc.le]
  have hs : (√b) ^ 2 = b := Real.sq_sqrt hb.le
  rw [hs]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  field_simp [ne_of_gt hb]

private theorem norm_sq_starSqrtDiag_mulVec_toFullBlockVec
    {d : ℕ} {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (X : BlockVec d) :
    ‖(WithLp.toLp 2
        (Matrix.mulVec (Matrix.diagonal (starSqrtDiag (d := d) b c)) (toFullBlockVec X)) :
        PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
      c⁻¹ * vecNormSq X.1 + b * vecNormSq X.2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  rcases X with ⟨x, y⟩
  simp [starSqrtDiag, toFullBlockVec, Matrix.mulVec, vecNormSq, vecDot,
    abs_of_nonneg (Real.sqrt_nonneg c), abs_of_nonneg (Real.sqrt_nonneg b)]
  simp_rw [mul_pow, sq_abs, inv_pow]
  have hc_sq : (√c) ^ 2 = c := Real.sq_sqrt hc.le
  rw [hc_sq, Real.sq_sqrt hb.le]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  field_simp [ne_of_gt hc]

private theorem normalized_mulVec_norm_sq_le
    {d : ℕ} [NeZero d] {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (M : FullBlockMat d) (P : FullBlockVec d) :
    ‖(WithLp.toLp 2
        (Matrix.mulVec (Matrix.diagonal (starInvSqrtDiag (d := d) b c)) (Matrix.mulVec M P)) :
        PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 ≤
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (Matrix.diagonal (starInvSqrtDiag (d := d) b c) * M *
            Matrix.diagonal (starInvSqrtDiag b c))‖ ^ 2 *
        ‖(WithLp.toLp 2
          (Matrix.mulVec (Matrix.diagonal (starSqrtDiag (d := d) b c)) P) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 := by
  let D : FullBlockMat d := Matrix.diagonal (starInvSqrtDiag (d := d) b c)
  let E : FullBlockMat d := Matrix.diagonal (starSqrtDiag (d := d) b c)
  let x : PiLp 2 (fun _ : BlockCoord d => ℝ) := WithLp.toLp 2 (Matrix.mulVec E P)
  let y : PiLp 2 (fun _ : BlockCoord d => ℝ) := WithLp.toLp 2 (Matrix.mulVec D (Matrix.mulVec M P))
  have hDE : D * E = 1 := starInvSqrtDiag_mul_starSqrtDiag (d := d) hb hc
  have hmulVec : Matrix.mulVec D (Matrix.mulVec M P) =
      Matrix.mulVec (D * M * D) (Matrix.mulVec E P) := by
    symm
    calc
      Matrix.mulVec (D * M * D) (Matrix.mulVec E P) =
          Matrix.mulVec ((D * M * D) * E) P := by
            rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec (D * M * (D * E)) P := by
            rw [Matrix.mul_assoc]
      _ = Matrix.mulVec (D * M * 1) P := by
            rw [hDE]
      _ = Matrix.mulVec (D * M) P := by
            rw [mul_one]
      _ = Matrix.mulVec D (Matrix.mulVec M P) := by
            rw [Matrix.mulVec_mulVec]
  have hy : (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (D * M * D)) x = y := by
    change WithLp.toLp 2 (Matrix.mulVec (D * M * D) (Matrix.mulVec E P)) =
      WithLp.toLp 2 (Matrix.mulVec D (Matrix.mulVec M P))
    rw [← hmulVec]
  have hnorm0 := (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (D * M * D)).le_opNorm x
  rw [hy] at hnorm0
  have hsq := pow_le_pow_left₀ (norm_nonneg y) hnorm0 2
  simpa [D, E, x, y, mul_pow] using hsq

private theorem sigma_mul_inv_star_sq_eq_theta {b c σ θ : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hσ : σ = Real.sqrt (b * c)) (hθ : θ = b * c⁻¹) :
    (σ * c⁻¹) ^ 2 = θ := by
  have hprod_pos : 0 < b * c := mul_pos hb hc
  rw [hσ, hθ]
  rw [mul_pow, Real.sq_sqrt hprod_pos.le]
  field_simp [ne_of_gt hc]

private theorem barSigma_mul_sigma_inv_eq_sigma_mul_inv_star {b c σ : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hσ : σ = Real.sqrt (b * c)) :
    b * σ⁻¹ = σ * c⁻¹ := by
  have hprod_pos : 0 < b * c := mul_pos hb hc
  have hσpos : 0 < σ := by
    rw [hσ]
    exact Real.sqrt_pos_of_pos hprod_pos
  rw [hσ]
  have hsqrt_ne : Real.sqrt (b * c) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hprod_pos)
  field_simp [hsqrt_ne, ne_of_gt hc]
  rw [Real.sq_sqrt hprod_pos.le]

private theorem norm_sq_starSqrtDiag_mulVec_specialBlockVec
    {d : ℕ} {b c σ : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hσ : σ = Real.sqrt (b * c)) (e : Vec d) :
    ‖(WithLp.toLp 2
        (Matrix.mulVec (Matrix.diagonal (starSqrtDiag (d := d) b c))
          (toFullBlockVec (-(σ ^ (1 / 2 : ℝ) • e), σ ^ (-(1 / 2 : ℝ)) • e))) :
        PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
      2 * (σ * c⁻¹) * vecNormSq e := by
  have hprod_pos : 0 < b * c := mul_pos hb hc
  have hσpos : 0 < σ := by
    rw [hσ]
    exact Real.sqrt_pos_of_pos hprod_pos
  have hpos_sq : (σ ^ (1 / 2 : ℝ)) ^ 2 = σ := by
    calc
      (σ ^ (1 / 2 : ℝ)) ^ 2 =
          (σ ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (σ ^ (1 / 2 : ℝ)) 2).symm
      _ = σ ^ ((1 / 2 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul hσpos.le (1 / 2 : ℝ) (2 : ℝ)).symm
      _ = σ ^ (1 : ℝ) := by
        norm_num
      _ = σ := by
        rw [Real.rpow_one]
  have hneg_sq : (σ ^ (-(1 / 2 : ℝ))) ^ 2 = σ⁻¹ := by
    calc
      (σ ^ (-(1 / 2 : ℝ))) ^ 2 =
          (σ ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (σ ^ (-(1 / 2 : ℝ))) 2).symm
      _ = σ ^ ((-(1 / 2 : ℝ)) * (2 : ℝ)) :=
        (Real.rpow_mul hσpos.le (-(1 / 2 : ℝ)) (2 : ℝ)).symm
      _ = σ ^ (-1 : ℝ) := by
        norm_num
      _ = (σ ^ (1 : ℝ))⁻¹ :=
        Real.rpow_neg hσpos.le 1
      _ = σ⁻¹ := by
        rw [Real.rpow_one]
  have hnorm :=
    norm_sq_starSqrtDiag_mulVec_toFullBlockVec (d := d) hb hc
      (-(σ ^ (1 / 2 : ℝ) • e), σ ^ (-(1 / 2 : ℝ)) • e)
  have hq_norm : vecNormSq (-(σ ^ (1 / 2 : ℝ) • e)) = σ * vecNormSq e := by
    have hneg :
        -(σ ^ (1 / 2 : ℝ) • e) = (-(σ ^ (1 / 2 : ℝ))) • e := by
      ext i
      simp
    rw [hneg, vecNormSq_smul]
    rw [show (-(σ ^ (1 / 2 : ℝ))) ^ 2 = (σ ^ (1 / 2 : ℝ)) ^ 2 by ring]
    rw [hpos_sq]
  have hp_norm : vecNormSq (σ ^ (-(1 / 2 : ℝ)) • e) = σ⁻¹ * vecNormSq e := by
    rw [vecNormSq_smul, hneg_sq]
  calc
    ‖(WithLp.toLp 2
        (Matrix.mulVec (Matrix.diagonal (starSqrtDiag (d := d) b c))
          (toFullBlockVec (-(σ ^ (1 / 2 : ℝ) • e), σ ^ (-(1 / 2 : ℝ)) • e))) :
        PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
        c⁻¹ * vecNormSq (-(σ ^ (1 / 2 : ℝ) • e)) +
          b * vecNormSq (σ ^ (-(1 / 2 : ℝ)) • e) := hnorm
    _ = c⁻¹ * (σ * vecNormSq e) + b * (σ⁻¹ * vecNormSq e) := by
          rw [hq_norm, hp_norm]
    _ = 2 * (σ * c⁻¹) * vecNormSq e := by
          have hbar := barSigma_mul_sigma_inv_eq_sigma_mul_inv_star hb hc hσ
          calc
            c⁻¹ * (σ * vecNormSq e) + b * (σ⁻¹ * vecNormSq e) =
                (c⁻¹ * σ + b * σ⁻¹) * vecNormSq e := by ring
            _ = (σ * c⁻¹ + σ * c⁻¹) * vecNormSq e := by
                  rw [hbar]
                  ring
            _ = 2 * (σ * c⁻¹) * vecNormSq e := by ring

private theorem weighted_blockVec_norm_sq_eq_sigma_inv_star_mul_normalized_norm_sq
    {d : ℕ} {b c σ : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hσ : σ = Real.sqrt (b * c)) (X : BlockVec d) :
    σ * vecNormSq X.1 + σ⁻¹ * vecNormSq X.2 =
      (σ * c⁻¹) *
        ‖(WithLp.toLp 2
          (Matrix.mulVec (Matrix.diagonal (starInvSqrtDiag (d := d) b c)) (toFullBlockVec X)) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 := by
  have hprod_pos : 0 < b * c := mul_pos hb hc
  have hσpos : 0 < σ := by
    rw [hσ]
    exact Real.sqrt_pos_of_pos hprod_pos
  have hsigma_sq : σ ^ 2 = b * c := by
    rw [hσ]
    exact Real.sq_sqrt hprod_pos.le
  rw [norm_sq_starInvSqrtDiag_mulVec_toFullBlockVec (d := d) hb hc X]
  have hcoeff : σ * c⁻¹ * b⁻¹ = σ⁻¹ := by
    have hbne : b ≠ 0 := ne_of_gt hb
    have hcne : c ≠ 0 := ne_of_gt hc
    have hσne : σ ≠ 0 := ne_of_gt hσpos
    field_simp [hbne, hcne, hσne]
    nlinarith [hsigma_sq]
  calc
    σ * vecNormSq X.1 + σ⁻¹ * vecNormSq X.2 =
        σ * vecNormSq X.1 + (σ * c⁻¹ * b⁻¹) * vecNormSq X.2 := by
          rw [hcoeff]
    _ = (σ * c⁻¹) * (c * vecNormSq X.1 + b⁻¹ * vecNormSq X.2) := by
          field_simp [ne_of_gt hc]

private noncomputable def reflectedNormalizedBlockFluctuationOperatorNormSqAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m : ℤ) (R : TriadicCube d) (a : RegCoeffField d) : ℝ :=
  let b := hP.barSigmaAtScale hStruct m
  let c := hP.barSigmaStarAtScale hStruct m
  let D : FullBlockMat d := Matrix.diagonal (starInvSqrtDiag b c)
  let A := coarseBlockMatrix (cubeSet R) a.toFun
  let Abar := scalarAnnealedBlockMatrixAtScale hP hStruct m
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (D * (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)) * D)‖ ^ 2

/-- Proof-internal manuscript normalized full-block fluctuation, using the
Euclidean operator norm of the full block matrix.  This is exposed inside the
third-lemma proof namespace so the assembly file can state the variance term
without introducing a public Ch5 wrapper. -/
noncomputable def fullBlockNormalizedFluctuationOperatorNormSqAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m : ℤ) (R : TriadicCube d) (a : RegCoeffField d) : ℝ :=
  Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct m R a

private theorem reflectedNormalizedBlockFluctuationOperatorNormSqAtScale_eq_fullBlock
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m : ℤ) (R : TriadicCube d) (a : RegCoeffField d) :
    reflectedNormalizedBlockFluctuationOperatorNormSqAtScale hP hStruct m R a =
      fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct m R a := by
  let b := hP.barSigmaAtScale hStruct m
  let c := hP.barSigmaStarAtScale hStruct m
  let D : FullBlockMat d := Matrix.diagonal (fullBlockInvSqrtDiag b c)
  let A := coarseBlockMatrix (cubeSet R) a.toFun
  let Abar := scalarAnnealedBlockMatrixAtScale hP hStruct m
  let e := blockCoordSwapEquiv d
  have hmat :
      Matrix.diagonal (starInvSqrtDiag (d := d) b c) *
          (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)) *
          Matrix.diagonal (starInvSqrtDiag b c) =
        Matrix.reindex e e (D * (toFullBlockMat A - toFullBlockMat Abar) * D) := by
    simpa [D, e] using
      reflectedNormalizedBlockFluctuationMatrix_eq_reindex_full (d := d) b c A Abar
  have hnorm :
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (Matrix.reindex e e (D * (toFullBlockMat A - toFullBlockMat Abar) * D))‖ =
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (D * (toFullBlockMat A - toFullBlockMat Abar) * D)‖ :=
    Ch02.norm_toEuclideanCLM_reindex_self e _
  unfold reflectedNormalizedBlockFluctuationOperatorNormSqAtScale
  unfold fullBlockNormalizedFluctuationOperatorNormSqAtScale
  dsimp only
  calc
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
        (Matrix.diagonal (starInvSqrtDiag (d := d) b c) *
          (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)) *
          Matrix.diagonal (starInvSqrtDiag b c))‖ ^ 2 =
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (Matrix.reindex e e (D * (toFullBlockMat A - toFullBlockMat Abar) * D))‖ ^ 2 := by
          rw [hmat]
    _ =
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (D * (toFullBlockMat A - toFullBlockMat Abar) * D)‖ ^ 2 := by
          rw [hnorm]

private theorem weighted_special_average_mismatch_le_reflected_normalized_block_fluctuation
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m : ℕ) (R : TriadicCube d) (e : Vec d)
    (hb : 0 < hP.barSigmaAtScale hStruct (m : ℤ))
    (hc : 0 < hP.barSigmaStarAtScale hStruct (m : ℤ)) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    sigmaHatAtScale hP hStruct (m : ℤ) *
        vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e) +
      (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
        vecNormSq (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e) ≤
      2 * thetaAtScale hP hStruct (m : ℤ) *
        reflectedNormalizedBlockFluctuationOperatorNormSqAtScale hP hStruct (m : ℤ) R a *
          vecNormSq e := by
  dsimp only
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := c⁻¹ • q_e - p_e
  let q0_e := q_e - b • p_e
  let A := coarseBlockMatrix (cubeSet R) a.toFun
  let Abar := scalarAnnealedBlockMatrixAtScale hP hStruct (m : ℤ)
  let M : FullBlockMat d := toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)
  let P_e : BlockVec d := (-q_e, p_e)
  let X : BlockVec d :=
    (-(Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e),
      -(Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e))
  have hσ : σ = Real.sqrt (b * c) := by
    rfl
  have hθ : θ = b * c⁻¹ := by
    rfl
  have hid : X = blockMatVecMul (ofFullBlockMat M) P_e := by
    simpa [X, M, P_e, p_e, q_e, p0_e, q0_e, A, Abar, b, c, σ] using
      special_average_mismatch_eq_reflected_block_fluctuation hP hStruct a ha m R e
  have hmulVec : Matrix.mulVec M (toFullBlockVec P_e) = toFullBlockVec X := by
    calc
      Matrix.mulVec M (toFullBlockVec P_e) =
          toFullBlockVec (blockMatVecMul (ofFullBlockMat M) P_e) := by
            rw [toFullBlockVec_blockMatVecMul]
            simp [M]
      _ = toFullBlockVec X := by
            rw [← hid]
  have hnorm_le :=
    normalized_mulVec_norm_sq_le (d := d) (b := b) (c := c) hb hc M (toFullBlockVec P_e)
  have hnorm_le' :
      ‖(WithLp.toLp 2
          (Matrix.mulVec (Matrix.diagonal (starInvSqrtDiag (d := d) b c)) (toFullBlockVec X)) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 ≤
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
            (Matrix.diagonal (starInvSqrtDiag (d := d) b c) * M *
              Matrix.diagonal (starInvSqrtDiag b c))‖ ^ 2 *
          ‖(WithLp.toLp 2
            (Matrix.mulVec (Matrix.diagonal (starSqrtDiag (d := d) b c)) (toFullBlockVec P_e)) :
            PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 := by
    simpa [hmulVec] using hnorm_le
  have hP_norm :
      ‖(WithLp.toLp 2
          (Matrix.mulVec (Matrix.diagonal (starSqrtDiag (d := d) b c)) (toFullBlockVec P_e)) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
        2 * (σ * c⁻¹) * vecNormSq e := by
    have h :=
      norm_sq_starSqrtDiag_mulVec_specialBlockVec (d := d) hb hc hσ e
    simpa [P_e, p_e, q_e, specialPAtScale, specialQAtScale, σ, mul_assoc] using h
  have hweight :=
    weighted_blockVec_norm_sq_eq_sigma_inv_star_mul_normalized_norm_sq
      (d := d) hb hc hσ X
  have hα_nonneg : 0 ≤ σ * c⁻¹ := by
    have hσpos : 0 < σ := by
      rw [hσ]
      exact Real.sqrt_pos_of_pos (mul_pos hb hc)
    exact mul_nonneg hσpos.le (inv_pos.mpr hc).le
  have hmul_le := mul_le_mul_of_nonneg_left hnorm_le' hα_nonneg
  have hscalar :
      (σ * c⁻¹) *
          (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (starInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (starInvSqrtDiag b c))‖ ^ 2 *
            (2 * (σ * c⁻¹) * vecNormSq e)) =
        2 * θ *
          ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (starInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (starInvSqrtDiag b c))‖ ^ 2 *
            vecNormSq e := by
    have hsq := sigma_mul_inv_star_sq_eq_theta hb hc hσ hθ
    calc
      (σ * c⁻¹) *
          (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (starInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (starInvSqrtDiag b c))‖ ^ 2 *
            (2 * (σ * c⁻¹) * vecNormSq e)) =
          2 * (σ * c⁻¹) ^ 2 *
            ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (starInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (starInvSqrtDiag b c))‖ ^ 2 *
            vecNormSq e := by
            ring
      _ = 2 * θ *
          ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (starInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (starInvSqrtDiag b c))‖ ^ 2 *
            vecNormSq e := by
            rw [hsq]
  calc
    σ *
        vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e) +
      σ⁻¹ *
        vecNormSq (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e)
      = σ * vecNormSq X.1 + σ⁻¹ * vecNormSq X.2 := by
          simp [X]
          rw [vecNormSq_sub_comm
              (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun) p0_e,
            vecNormSq_sub_comm
              (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun) q0_e]
    _ = (σ * c⁻¹) *
        ‖(WithLp.toLp 2
          (Matrix.mulVec (Matrix.diagonal (starInvSqrtDiag (d := d) b c)) (toFullBlockVec X)) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 := hweight
    _ ≤ (σ * c⁻¹) *
        (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
            (Matrix.diagonal (starInvSqrtDiag (d := d) b c) * M *
              Matrix.diagonal (starInvSqrtDiag b c))‖ ^ 2 *
          ‖(WithLp.toLp 2
            (Matrix.mulVec (Matrix.diagonal (starSqrtDiag (d := d) b c)) (toFullBlockVec P_e)) :
            PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2) := hmul_le
    _ = (σ * c⁻¹) *
        (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
            (Matrix.diagonal (starInvSqrtDiag (d := d) b c) * M *
              Matrix.diagonal (starInvSqrtDiag b c))‖ ^ 2 *
          (2 * (σ * c⁻¹) * vecNormSq e)) := by
          rw [hP_norm]
    _ = 2 * θ *
          ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (starInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (starInvSqrtDiag b c))‖ ^ 2 *
            vecNormSq e := hscalar
    _ = 2 * thetaAtScale hP hStruct (m : ℤ) *
        reflectedNormalizedBlockFluctuationOperatorNormSqAtScale hP hStruct (m : ℤ) R a *
          vecNormSq e := by
          simp [reflectedNormalizedBlockFluctuationOperatorNormSqAtScale, M, A, Abar, b, c, θ,
            mul_assoc]

/-- Pointwise special-vector average mismatch controlled by the manuscript
normalized full-block fluctuation, with the Euclidean size of the special
direction left explicit.  This is the robust internal form; the unit-vector
corollary below is the one currently consumed by the high-scale assembly. -/
theorem weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation_mul_vecNormSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m : ℕ) (R : TriadicCube d) (e : Vec d)
    (hb : 0 < hP.barSigmaAtScale hStruct (m : ℤ))
    (hc : 0 < hP.barSigmaStarAtScale hStruct (m : ℤ)) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    sigmaHatAtScale hP hStruct (m : ℤ) *
        vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e) +
      (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
        vecNormSq (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e) ≤
      2 * thetaAtScale hP hStruct (m : ℤ) *
        fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct (m : ℤ) R a *
          vecNormSq e := by
  simpa [reflectedNormalizedBlockFluctuationOperatorNormSqAtScale_eq_fullBlock hP hStruct
      (m : ℤ) R a, mul_assoc] using
    weighted_special_average_mismatch_le_reflected_normalized_block_fluctuation
      hP hStruct a ha m R e hb hc

/-- Pointwise special-vector average mismatch controlled by the manuscript
normalized full-block fluctuation for Euclidean-unit directions.  This remains
a theorem in the coarse-fluctuation proof namespace, not a new public theorem
package. -/
theorem weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m : ℕ) (R : TriadicCube d) (e : Vec d)
    (hb : 0 < hP.barSigmaAtScale hStruct (m : ℤ))
    (hc : 0 < hP.barSigmaStarAtScale hStruct (m : ℤ))
    (he : vecNormSq e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    sigmaHatAtScale hP hStruct (m : ℤ) *
        vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e) +
      (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
        vecNormSq (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e) ≤
      2 * thetaAtScale hP hStruct (m : ℤ) *
        fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct (m : ℤ) R a := by
  simpa [reflectedNormalizedBlockFluctuationOperatorNormSqAtScale_eq_fullBlock hP hStruct
      (m : ℤ) R a, he, mul_assoc] using
    weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation_mul_vecNormSq
      hP hStruct a ha m R e hb hc

/-- Descendant-averaged special-vector average mismatch controlled by the
manuscript normalized full-block fluctuation, with the Euclidean direction
size explicit. -/
theorem descendantsAverage_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation_mul_vecNormSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m : ℕ) (Q : TriadicCube d) (j : ℕ) (e : Vec d)
    (hb : 0 < hP.barSigmaAtScale hStruct (m : ℤ))
    (hc : 0 < hP.barSigmaStarAtScale hStruct (m : ℤ)) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    descendantsAverage Q j
        (fun R =>
          sigmaHatAtScale hP hStruct (m : ℤ) *
              vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e) +
            (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
              vecNormSq (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e)) ≤
      descendantsAverage Q j
        (fun R =>
          2 * thetaAtScale hP hStruct (m : ℤ) *
            fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct (m : ℤ) R a *
              vecNormSq e) := by
  dsimp only
  refine descendantsAverage_le_descendantsAverage Q j ?_
  intro R hR
  exact
    weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation_mul_vecNormSq
      hP hStruct a ha m R e hb hc

/-- Descendant-averaged special-vector average mismatch controlled by the
manuscript normalized full-block fluctuation. -/
theorem descendantsAverage_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m : ℕ) (Q : TriadicCube d) (j : ℕ) (e : Vec d)
    (hb : 0 < hP.barSigmaAtScale hStruct (m : ℤ))
    (hc : 0 < hP.barSigmaStarAtScale hStruct (m : ℤ))
    (he : vecNormSq e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    descendantsAverage Q j
        (fun R =>
          sigmaHatAtScale hP hStruct (m : ℤ) *
              vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e) +
            (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
              vecNormSq (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e)) ≤
      descendantsAverage Q j
        (fun R =>
          2 * thetaAtScale hP hStruct (m : ℤ) *
            fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct (m : ℤ) R a) := by
  dsimp only
  refine descendantsAverage_le_descendantsAverage Q j ?_
  intro R hR
  exact
    weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation
      hP hStruct a ha m R e hb hc he

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
