/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.ScalarBounds
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.FiniteNet

/-!
# Per-probe second moments of the normalized fluctuation matrix

The observable is controlled a.s. by finitely many quadratic probes of the
normalized fluctuation matrix `H = D·(A_m − Ā_m)·D`
(`fullBlock_operatorNorm_sq_le_probeSqBudget`).  Here we bound the *second moment*
of each such probe by the centered-second-moment estimate
(`centered_quadratic_second_moment`).

* `fluctuation_probe_eq_centered_blockQuadratic` — the deterministic identity
  turning a probe of `H` into the centered block quadratic form of the
  diagonally rescaled probe vector.
* `probe_sq_integral_le` — for any probe `q` with `⟪q,q⟫ ≤ 2`, the second moment
  of `fullBlockQuadratic H q` is at most `16·Cd·Θ⁶·(3^m)^{-β}`.
-/

@[expose] public section

namespace Homogenization

open Homogenization MeasureTheory
open Homogenization.Book.Ch04
  (RestrictionCoeffLaw RestrictionLawCarrier RestrictionStructuralLaw annealedBlockMatrixAtScale
    scalarAnnealedBlockMatrixAtScale scalarFullBlockInvSqrtDiag)
open Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale
  (annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale
    fullBlockNormalizedFluctuationMatrix fullBlockQuadratic fullBlockQuadratic_sub
    fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot)

variable {d : ℕ}

/-- **Probe → centered block quadratic.**  A quadratic probe of the normalized
fluctuation matrix `H = D·(A_m − Ā_m)·D` equals the centered block quadratic
form of the diagonally rescaled probe vector `w = ofFullBlockVec (D q)`. -/
theorem fluctuation_probe_eq_centered_blockQuadratic [NeZero d] {L : RestrictionCoeffLaw d}
    (hP : RestrictionLawCarrier L) (hStruct : RestrictionStructuralLaw L) (m : ℤ) (q : FullBlockVec d)
    (a : RegCoeffField d) :
    fullBlockQuadratic
        (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a) q
      = blockVecDot
          (ofFullBlockVec (Matrix.mulVec (Matrix.diagonal
            (scalarFullBlockInvSqrtDiag (hP.barSigmaAtScale hStruct m)
              (hP.barSigmaStarAtScale hStruct m))) q))
          (blockMatVecMul
            (ofFullBlockMat
              (toFullBlockMat (coarseBlockMatrix (cubeSet (originCube d m)) a)
                - toFullBlockMat (annealedBlockMatrixAtScale L m)))
            (ofFullBlockVec (Matrix.mulVec (Matrix.diagonal
              (scalarFullBlockInvSqrtDiag (hP.barSigmaAtScale hStruct m)
                (hP.barSigmaStarAtScale hStruct m))) q))) := by
  classical
  set b := hP.barSigmaAtScale hStruct m with hb
  set c := hP.barSigmaStarAtScale hStruct m with hc
  set r := scalarFullBlockInvSqrtDiag b c with hr
  set A := coarseBlockMatrix (cubeSet (originCube d m)) a with hA
  set Abar := scalarAnnealedBlockMatrixAtScale hP hStruct m with hAbar
  have hunfold :
      fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a
        = Matrix.diagonal r * (toFullBlockMat A - toFullBlockMat Abar) * Matrix.diagonal r :=
    rfl
  rw [hunfold, Matrix.mul_sub, Matrix.sub_mul, fullBlockQuadratic_sub,
    fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot r A q,
    fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot r Abar q,
    show Abar = annealedBlockMatrixAtScale L m from
      (annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale hP hStruct m).symm,
    blockVecDot_blockMatVecMul_sub_eq_ofFullBlockMat_sub]

/-- **M-factor bound.**  With `½ ≤ b`, `0 ≤ c ≤ 2Θ`, the centered weight of the
diagonally rescaled probe is at most `2Θ·⟪q,q⟫`. -/
private theorem mfactor_le [NeZero d] {b c Θ : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hc0 : 0 ≤ c) (hc : c ≤ 2 * Θ) (hΘ : 1 ≤ Θ)
    (q : FullBlockVec d) :
    Θ * vecNormSq (ofFullBlockVec (Matrix.mulVec
          (Matrix.diagonal (scalarFullBlockInvSqrtDiag b c)) q)).1
      + vecNormSq (ofFullBlockVec (Matrix.mulVec
          (Matrix.diagonal (scalarFullBlockInvSqrtDiag b c)) q)).2
      ≤ 2 * Θ * dotProduct q q := by
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hb
  have hΘ0 : (0 : ℝ) ≤ Θ := le_trans (by norm_num) hΘ
  have hw1 : (ofFullBlockVec (Matrix.mulVec
        (Matrix.diagonal (scalarFullBlockInvSqrtDiag b c)) q)).1
      = (Real.sqrt b)⁻¹ • (fun i => q (Sum.inl i)) := by
    funext i
    simp [ofFullBlockVec, Matrix.mulVec_diagonal, scalarFullBlockInvSqrtDiag]
  have hw2 : (ofFullBlockVec (Matrix.mulVec
        (Matrix.diagonal (scalarFullBlockInvSqrtDiag b c)) q)).2
      = (Real.sqrt c) • (fun i => q (Sum.inr i)) := by
    funext i
    simp [ofFullBlockVec, Matrix.mulVec_diagonal, scalarFullBlockInvSqrtDiag]
  rw [hw1, hw2, vecNormSq_smul, vecNormSq_smul]
  have hsqb : (Real.sqrt b)⁻¹ ^ 2 = b⁻¹ := by rw [inv_pow, Real.sq_sqrt hb0.le]
  have hsqc : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc0
  rw [hsqb, hsqc]
  have hbinv : b⁻¹ ≤ 2 := by
    have h := (inv_le_inv₀ hb0 (show (0 : ℝ) < 1 / 2 by norm_num)).mpr hb
    norm_num at h; exact h
  have hqU : (0 : ℝ) ≤ vecNormSq (fun i => q (Sum.inl i)) := vecNormSq_nonneg _
  have hqL : (0 : ℝ) ≤ vecNormSq (fun i => q (Sum.inr i)) := vecNormSq_nonneg _
  have hdqq : dotProduct q q
      = vecNormSq (fun i => q (Sum.inl i)) + vecNormSq (fun i => q (Sum.inr i)) := by
    rw [dotProduct, Fintype.sum_sum_type]
    simp [vecNormSq, vecDot]
  rw [hdqq]
  have t1 : (0 : ℝ) ≤ (2 - b⁻¹) * (Θ * vecNormSq (fun i => q (Sum.inl i))) :=
    mul_nonneg (by linarith) (mul_nonneg hΘ0 hqU)
  have t2 : (0 : ℝ) ≤ (2 * Θ - c) * vecNormSq (fun i => q (Sum.inr i)) :=
    mul_nonneg (by linarith) hqL
  nlinarith [t1, t2]

/-- **Per-probe second moment.**  For any full-block probe `q` with
`⟪q,q⟫ ≤ 4`, the second moment of `fullBlockQuadratic H q` is at most
`64·Cd·Θ⁶·(3^m)^{-β}`, with `Cd` the dimension-only centered-moment constant. -/
theorem probe_sq_integral_le [NeZero d] (hd : 3 ≤ d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ {m : ℤ} (_hm : 0 ≤ m) {Θ : ℝ} (_hΘ : 1 ≤ Θ) {L : RestrictionCoeffLaw d}
        [IsProbabilityMeasure L] (hP : RestrictionLawCarrier L) (hStruct : RestrictionStructuralLaw L)
        (_hLaw : ThetaEllipticLaw Θ L) (q : FullBlockVec d) (_hq2 : dotProduct q q ≤ 4),
      (∫ a, (fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a) q)
            ^ 2 ∂L)
        ≤ 64 * Cd * Θ ^ 6 * ((3 : ℝ) ^ m) ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1)) := by
  obtain ⟨Cd, hCd0, hN2⟩ := centered_quadratic_second_moment (d := d) hd
  refine ⟨Cd, hCd0, ?_⟩
  intro m hm Θ hΘ L _ hP hStruct hLaw q hq2
  have hΘ0 : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  set t : ℝ := ((3 : ℝ) ^ m) ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1)) with htdef
  have ht : (0 : ℝ) ≤ t := Real.rpow_nonneg (by positivity) _
  -- rewrite the integrand into the centered block quadratic form
  have hcongr :
      (∫ a, (fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a) q)
            ^ 2 ∂L)
        = ∫ a, (blockVecDot
            (ofFullBlockVec (Matrix.mulVec (Matrix.diagonal
              (scalarFullBlockInvSqrtDiag (hP.barSigmaAtScale hStruct m)
                (hP.barSigmaStarAtScale hStruct m))) q))
            (blockMatVecMul
              (ofFullBlockMat
                (toFullBlockMat (coarseBlockMatrix (cubeSet (originCube d m)) a)
                  - toFullBlockMat (annealedBlockMatrixAtScale L m)))
              (ofFullBlockVec (Matrix.mulVec (Matrix.diagonal
                (scalarFullBlockInvSqrtDiag (hP.barSigmaAtScale hStruct m)
                  (hP.barSigmaStarAtScale hStruct m))) q)))) ^ 2 ∂L := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
    dsimp only
    rw [fluctuation_probe_eq_centered_blockQuadratic hP hStruct m q a]
  rw [hcongr]
  have key := hN2 hm hΘ hP hStruct.unit_range hLaw
    (ofFullBlockVec (Matrix.mulVec (Matrix.diagonal
      (scalarFullBlockInvSqrtDiag (hP.barSigmaAtScale hStruct m)
        (hP.barSigmaStarAtScale hStruct m))) q))
  refine le_trans key ?_
  -- arithmetic
  set w : BlockVec d := ofFullBlockVec (Matrix.mulVec (Matrix.diagonal
    (scalarFullBlockInvSqrtDiag (hP.barSigmaAtScale hStruct m)
      (hP.barSigmaStarAtScale hStruct m))) q) with hwdef
  have hMnn : 0 ≤ Θ * vecNormSq w.1 + vecNormSq w.2 :=
    add_nonneg (mul_nonneg hΘ0.le (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  have hM : Θ * vecNormSq w.1 + vecNormSq w.2 ≤ 2 * Θ * dotProduct q q := by
    rw [hwdef]
    exact mfactor_le (half_le_barSigmaAtScale hΘ hP hStruct hLaw m)
      (le_of_lt (barSigmaStarAtScale_pos hΘ hP hStruct hLaw m))
      (barSigmaStarAtScale_le_two_mul_Theta hΘ hP hStruct hLaw m) hΘ q
  have hM4 : Θ * vecNormSq w.1 + vecNormSq w.2 ≤ 8 * Θ := by
    have h : 2 * Θ * dotProduct q q ≤ 2 * Θ * 4 :=
      mul_le_mul_of_nonneg_left hq2 (by linarith [hΘ0])
    linarith [hM]
  have hMsq : (Θ * vecNormSq w.1 + vecNormSq w.2) ^ 2 ≤ 64 * Θ ^ 2 := by
    nlinarith [mul_le_mul hM4 hM4 hMnn (show (0 : ℝ) ≤ 8 * Θ by linarith [hΘ0])]
  have hmin : min 1 (Θ ^ 2 * t) ≤ Θ ^ 2 * t := min_le_right _ _
  have hCdM : 0 ≤ Cd * (Θ * vecNormSq w.1 + vecNormSq w.2) ^ 2 :=
    mul_nonneg hCd0 (sq_nonneg _)
  have hΘ4le6 : Θ ^ 4 ≤ Θ ^ 6 := by
    have h2 : (1 : ℝ) ≤ Θ ^ 2 := by nlinarith [hΘ]
    have : Θ ^ 4 * 1 ≤ Θ ^ 4 * Θ ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (pow_nonneg hΘ0.le 4)
    nlinarith [this]
  have hfac : (0 : ℝ) ≤ 64 * Cd * t := mul_nonneg (mul_nonneg (by norm_num) hCd0) ht
  calc Cd * (Θ * vecNormSq w.1 + vecNormSq w.2) ^ 2 * min 1 (Θ ^ 2 * t)
      ≤ Cd * (Θ * vecNormSq w.1 + vecNormSq w.2) ^ 2 * (Θ ^ 2 * t) :=
        mul_le_mul_of_nonneg_left hmin hCdM
    _ ≤ Cd * (64 * Θ ^ 2) * (Θ ^ 2 * t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMsq hCd0)
          (mul_nonneg (sq_nonneg _) ht)
    _ = 64 * Cd * Θ ^ 4 * t := by ring
    _ ≤ 64 * Cd * Θ ^ 6 * t := by nlinarith [mul_nonneg hfac (by linarith [hΘ4le6] :
          (0 : ℝ) ≤ Θ ^ 6 - Θ ^ 4)]

/-- **Probe second-moment integrability.**  Each squared probe of the normalized
fluctuation matrix is integrable: it is `(X − c₀)²` for the a.s.-bounded coarse
block quadratic `X` and a constant `c₀`. -/
theorem integrable_fluctuation_probe_sq [NeZero d] {L : RestrictionCoeffLaw d} {Θ : ℝ}
    (hΘ : 1 ≤ Θ) (hP : RestrictionLawCarrier L) (hStruct : RestrictionStructuralLaw L)
    (hLaw : ThetaEllipticLaw Θ L) (m : ℤ) (q : FullBlockVec d) :
    Integrable
      (fun a : RegCoeffField d => (fullBlockQuadratic
        (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a) q)
          ^ 2) L := by
  have : IsProbabilityMeasure L := hP.isProbability
  have hΘ0 : (0 : ℝ) ≤ Θ := le_trans (by norm_num) hΘ
  set w : BlockVec d := ofFullBlockVec (Matrix.mulVec (Matrix.diagonal
    (scalarFullBlockInvSqrtDiag (hP.barSigmaAtScale hStruct m)
      (hP.barSigmaStarAtScale hStruct m))) q) with hwdef
  set c₀ : ℝ := blockVecDot w (blockMatVecMul (annealedBlockMatrixAtScale L m) w) with hc0def
  have hpt : ∀ a : RegCoeffField d, fullBlockQuadratic
        (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a) q
      = blockVecDot w
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a) w) - c₀ := by
    intro a
    rw [fluctuation_probe_eq_centered_blockQuadratic hP hStruct m q a,
      blockVecDot_blockMatVecMul_ofFullBlockMat_sub]
  have hXint := integrable_coarseBlockQuadratic_of_thetaEllipticLaw hΘ hP hLaw m w
  set Mub : ℝ := 2 * (Θ * vecNormSq w.1 + vecNormSq w.2) with hMubdef
  have hMub0 : 0 ≤ Mub := by
    rw [hMubdef]
    exact mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg hΘ0 (vecNormSq_nonneg _)) (vecNormSq_nonneg _))
  have hsqint : Integrable
      (fun a : RegCoeffField d => (blockVecDot w
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a) w) - c₀) ^ 2) L := by
    refine (integrable_const ((Mub + |c₀|) ^ 2)).mono' ?_ ?_
    · exact (hXint.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2
    · filter_upwards [ae_coarseBlockQuadratic_bounds_of_thetaEllipticLaw hΘ hLaw m w] with a ha
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [le_abs_self c₀, neg_abs_le c₀, ha.1, ha.2, hMub0, abs_nonneg c₀]
  exact hsqint.congr (Filter.Eventually.of_forall (fun a => by dsimp only; rw [hpt a]))

end Homogenization
