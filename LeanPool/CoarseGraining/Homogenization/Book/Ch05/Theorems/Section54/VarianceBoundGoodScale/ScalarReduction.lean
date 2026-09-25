/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Pigeonhole.ScalarChain
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.NormalizedBlocks

/-! # Scalar Reduction -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open MeasureTheory
open scoped BigOperators
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Scalar form of the variance-bound left-hand side

This file packages the exact beta-weighted scalar expression appearing in the
variance bound at a good scale and records the basic order facts needed by the
later reduction steps.
-/

/-- The beta-weighted full-block fluctuation sum appearing in
`l.variance.bound.good.scale.homogenization.scale`. -/
noncomputable def varianceGoodScaleFullBlockSumAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 m,
    varianceWeight (section54VarianceBeta hP4) m j *
      ∫ a,
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P

/-- The variance-bound left-hand side is nonnegative. -/
theorem varianceGoodScaleFullBlockSumAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 ≤ varianceGoodScaleFullBlockSumAtScale hP hStruct hP4 m := by
  unfold varianceGoodScaleFullBlockSumAtScale
  refine sum_Icc_varianceWeight_mul_nonneg ?_
  intro j _hj
  exact integral_nonneg fun a =>
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg
      hP hStruct (m : ℤ) (originCube d (j : ℤ)) a

/-- Sumwise comparison principle for the variance-bound left-hand side. -/
theorem varianceGoodScaleFullBlockSumAtScale_le_weighted_sum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ)
    {F : ℕ → ℝ}
    (hF :
      ∀ j, j ∈ Finset.Icc 1 m →
        (∫ a,
          Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P) ≤ F j) :
    varianceGoodScaleFullBlockSumAtScale hP hStruct hP4 m ≤
      ∑ j ∈ Finset.Icc 1 m,
        varianceWeight (section54VarianceBeta hP4) m j * F j := by
  unfold varianceGoodScaleFullBlockSumAtScale
  exact sum_Icc_varianceWeight_mul_le_mul hF

/-- Constant comparison principle for the variance-bound left-hand side. -/
theorem varianceGoodScaleFullBlockSumAtScale_le_weighted_const
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) {C : ℝ}
    (hC :
      ∀ j, j ∈ Finset.Icc 1 m →
        (∫ a,
          Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P) ≤ C) :
    varianceGoodScaleFullBlockSumAtScale hP hStruct hP4 m ≤
      (∑ j ∈ Finset.Icc 1 m,
        varianceWeight (section54VarianceBeta hP4) m j) * C := by
  unfold varianceGoodScaleFullBlockSumAtScale
  exact sum_Icc_varianceWeight_mul_le_const_mul hC

/-- Block-matrix subadditivity, after scalar normalization and testing against
a fixed full-block vector.  This is the deterministic bridge from the Ch4
Löwner comparison to the scalar partition average used in the good-scale
variance proof. -/
theorem fullBlockNormalizedQuadraticObservable_le_restrictionDescendantAverageOnCube_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) :
    (fun a : RegCoeffField d =>
      fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet Q) a.toFun)
      ≤ᵐ[P]
    fun a : RegCoeffField d =>
      Ch04.restrictionDescendantAverageOnCube Q k
        (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a := by
  filter_upwards [hP.coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_ae Q hk]
    with a hSub
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let X : BlockVec d := ofFullBlockVec (Matrix.mulVec D q)
  have hParent :
      fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet Q) a.toFun =
        blockVecDot X (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a.toFun) X) := by
    dsimp [fullBlockNormalizedQuadraticObservable, fullBlockQuadratic, b, c, D, X]
    simpa [D] using!
      fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot
        (Ch04.scalarFullBlockInvSqrtDiag (d := d) b c)
        (coarseBlockMatrix (cubeSet Q) a.toFun) q
  have hAvg :
      blockVecDot X
          (blockMatVecMul
            (descendantsAverageBlockMat Q (Int.toNat (Q.scale - k))
              (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) X) =
        Ch04.restrictionDescendantAverageOnCube Q k
          (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a := by
    rw [blockVecDot_blockMatVecMul_descendantsAverageBlockMat]
    simp [Ch04.restrictionDescendantAverageOnCube, descendantsAtScale_eq_descendantsAtDepth Q hk,
      fullBlockNormalizedQuadraticObservableR,
      fullBlockNormalizedQuadraticObservable, b, c, D,
      fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot, descendantsAverage, X]
  calc
    fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet Q) a.toFun
        = blockVecDot X (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a.toFun) X) := hParent
    _ ≤ blockVecDot X
          (blockMatVecMul
            (descendantsAverageBlockMat Q (Int.toNat (Q.scale - k))
              (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) X) := by
        nlinarith [hSub X]
    _ = Ch04.restrictionDescendantAverageOnCube Q k
          (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a := hAvg

/-- Positive-part control for a normalized quadratic probe.  Once the origin
scale-`k` annealed value is at most `1 + delta`, the pointwise positive excess
over `1` is bounded by `delta` plus the centered descendant average. -/
theorem fullBlockNormalizedQuadraticObservable_positivePart_le_delta_add_centeredAverageOnCube_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (hmean_le :
      (∫ b,
        fullBlockNormalizedQuadraticObservable hP hStruct center q
          (cubeSet (originCube d k)) b.toFun ∂P) ≤ 1 + delta) :
    (fun a : RegCoeffField d =>
      max (fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet Q) a.toFun -
        1) 0) ≤ᵐ[P]
    fun a : RegCoeffField d =>
      delta +
        |Ch04.restrictionCenteredDescendantAverageOnCube P Q k
          (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a| := by
  filter_upwards
    [fullBlockNormalizedQuadraticObservable_le_restrictionDescendantAverageOnCube_ae
      hP hStruct center q Q hk] with a hsub
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fullBlockNormalizedQuadraticObservableR hP hStruct center q
  let f := X (cubeSet Q) a
  let avg := Ch04.restrictionDescendantAverageOnCube Q k X a
  let μ := ∫ b, X (cubeSet (originCube d k)) b ∂P
  have hcenter :
      Ch04.restrictionCenteredDescendantAverageOnCube P Q k X a = avg - μ := by
    exact congrFun
      (Ch04.restrictionCenteredDescendantAverageOnCube_eq_restrictionDescendantAverageOnCube_sub
        (P := P) (Q := Q) (n := k) hk X) a
  have hsub' : f ≤ avg := by simpa [X, f, avg] using! hsub
  have hμ : μ ≤ 1 + delta := by simpa [X, μ] using! hmean_le
  have hfirst : f - 1 ≤ delta + (avg - μ) := by linarith
  have hmax : max (f - 1) 0 ≤ delta + max (avg - μ) 0 := by
    refine max_le ?_ ?_
    · have hmono : delta + (avg - μ) ≤ delta + max (avg - μ) 0 := by
        nlinarith [le_max_left (avg - μ) 0]
      exact hfirst.trans hmono
    · exact add_nonneg hdelta_nonneg (le_max_right _ _)
  have hmax_abs : max (avg - μ) 0 ≤ |avg - μ| :=
    max_le (le_abs_self _) (abs_nonneg _)
  calc
    max (fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet Q) a.toFun -
        1) 0 = max (f - 1) 0 := rfl
    _ ≤ delta + max (avg - μ) 0 := hmax
    _ ≤ delta + |avg - μ| := by nlinarith [hmax_abs]
    _ =
        delta + |Ch04.restrictionCenteredDescendantAverageOnCube P Q k X a| := by
          rw [hcenter]

/-- Base-parameter version of
`fullBlockNormalizedQuadraticObservable_positivePart_le_delta_add_centeredAverageOnCube_ae`.
It is used for the non-unit plus/minus probes in the finite-dimensional
upgrade. -/
theorem fullBlockNormalizedQuadraticObservable_positivePart_base_le_error_add_centeredAverageOnCube_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) {base err : ℝ} (herr_nonneg : 0 ≤ err)
    (hmean_le :
      (∫ b,
        fullBlockNormalizedQuadraticObservable hP hStruct center q
          (cubeSet (originCube d k)) b.toFun ∂P) ≤ base + err) :
    (fun a : RegCoeffField d =>
      max (fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet Q) a.toFun -
        base) 0) ≤ᵐ[P]
    fun a : RegCoeffField d =>
      err +
        |Ch04.restrictionCenteredDescendantAverageOnCube P Q k
          (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a| := by
  filter_upwards
    [fullBlockNormalizedQuadraticObservable_le_restrictionDescendantAverageOnCube_ae
      hP hStruct center q Q hk] with a hsub
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fullBlockNormalizedQuadraticObservableR hP hStruct center q
  let f := X (cubeSet Q) a
  let avg := Ch04.restrictionDescendantAverageOnCube Q k X a
  let μ := ∫ b, X (cubeSet (originCube d k)) b ∂P
  have hcenter :
      Ch04.restrictionCenteredDescendantAverageOnCube P Q k X a = avg - μ := by
    exact congrFun
      (Ch04.restrictionCenteredDescendantAverageOnCube_eq_restrictionDescendantAverageOnCube_sub
        (P := P) (Q := Q) (n := k) hk X) a
  have hsub' : f ≤ avg := by simpa [X, f, avg] using! hsub
  have hμ : μ ≤ base + err := by simpa [X, μ] using! hmean_le
  have hfirst : f - base ≤ err + (avg - μ) := by linarith
  have hmax : max (f - base) 0 ≤ err + max (avg - μ) 0 := by
    refine max_le ?_ ?_
    · have hmono : err + (avg - μ) ≤ err + max (avg - μ) 0 := by
        nlinarith [le_max_left (avg - μ) 0]
      exact hfirst.trans hmono
    · exact add_nonneg herr_nonneg (le_max_right _ _)
  have hmax_abs : max (avg - μ) 0 ≤ |avg - μ| :=
    max_le (le_abs_self _) (abs_nonneg _)
  calc
    max (fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet Q) a.toFun -
        base) 0 = max (f - base) 0 := rfl
    _ ≤ err + max (avg - μ) 0 := hmax
    _ ≤ err + |avg - μ| := by nlinarith [hmax_abs]
    _ =
        err + |Ch04.restrictionCenteredDescendantAverageOnCube P Q k X a| := by
          rw [hcenter]

/-- The mean of a normalized quadratic probe on an origin cube is the same
quadratic form applied to the corresponding annealed full-block matrix. -/
theorem integral_origin_fullBlockNormalizedQuadraticObservable_eq_annealedBlockMatrixAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center n : ℤ) (q : FullBlockVec d)
    (hBlock : Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P) :
    let b := hP.barSigmaAtScale hStruct center
    let c := hP.barSigmaStarAtScale hStruct center
    let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
    (∫ a,
      fullBlockNormalizedQuadraticObservable hP hStruct center q
        (cubeSet (originCube d n)) a.toFun ∂P) =
      fullBlockQuadratic (D * toFullBlockMat (Ch04.annealedBlockMatrixAtScale P n) * D) q := by
  classical
  dsimp only
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let X : BlockVec d := ofFullBlockVec (Matrix.mulVec D q)
  let B : RegCoeffField d → BlockMat d :=
    fun a => coarseBlockMatrix (cubeSet (originCube d n)) a.toFun
  have hEntry : ∀ α β,
      Integrable (fun a : RegCoeffField d => blockMatEntry (B a) α β) P := by
    intro α β
    simpa [B] using
      Ch04.RestrictionLawCarrier.integrable_blockMatEntry_coarseBlockMatrix_cubeSet_of_integrable_coarseFullBlockMatrixAtCube
        (Q := originCube d n) hBlock α β
  have hIntEq :=
    Ch04.integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries
      (P := P) (B := B) hEntry X X
  have hObs :
      (fun a : RegCoeffField d =>
        fullBlockNormalizedQuadraticObservable hP hStruct center q
          (cubeSet (originCube d n)) a.toFun) =
      fun a : RegCoeffField d => blockVecDot X (blockMatVecMul (B a) X) := by
    funext a
    dsimp [fullBlockNormalizedQuadraticObservable, fullBlockQuadratic, b, c, D, X, B]
    simpa [D] using!
      fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot
        (Ch04.scalarFullBlockInvSqrtDiag (d := d) b c)
        (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) q
  rw [hObs]
  rw [hIntEq]
  have hAnnealed :
      { upperLeft := fun i j => ∫ a, (B a).upperLeft i j ∂P
        upperRight := fun i j => ∫ a, (B a).upperRight i j ∂P
        lowerLeft := fun i j => ∫ a, (B a).lowerLeft i j ∂P
        lowerRight := fun i j => ∫ a, (B a).lowerRight i j ∂P } =
      Ch04.annealedBlockMatrixAtScale P n := by
    rw [Ch04.annealedBlockMatrixAtScale, Ch04.annealedBlockMatrix]
  rw [hAnnealed]
  symm
  simpa [D, X] using
    fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot
      (Ch04.scalarFullBlockInvSqrtDiag (d := d) b c)
      (Ch04.annealedBlockMatrixAtScale P n) q

/-- `(P4)` supplies the integrability in
`integral_origin_fullBlockNormalizedQuadraticObservable_eq_annealedBlockMatrixAtScale`
for nonnegative origin scales. -/
theorem integral_origin_fullBlockNormalizedQuadraticObservable_eq_annealedBlockMatrixAtScale_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center n : ℤ) (hn : 0 ≤ n) (q : FullBlockVec d) :
    let b := hP.barSigmaAtScale hStruct center
    let c := hP.barSigmaStarAtScale hStruct center
    let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
    (∫ a,
      fullBlockNormalizedQuadraticObservable hP hStruct center q
        (cubeSet (originCube d n)) a.toFun ∂P) =
      fullBlockQuadratic (D * toFullBlockMat (Ch04.annealedBlockMatrixAtScale P n) * D) q := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P := by
    have hnat :=
      Section52.originBlockIntegrableAtScale_from_P4
        hP hStruct hP4 (Int.toNat n)
    simpa [Int.toNat_of_nonneg hn] using hnat
  exact
    integral_origin_fullBlockNormalizedQuadraticObservable_eq_annealedBlockMatrixAtScale
      hP hStruct center n q hBlock

private theorem inv_sqrt_mul_le_of_le_mul {b x A : ℝ} (hb : 0 < b)
    (hx : x ≤ A * b) :
    (Real.sqrt b)⁻¹ * x * (Real.sqrt b)⁻¹ ≤ A := by
  have hsqrt_pos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
  have hmul : x / b ≤ A :=
    (div_le_iff₀ hb).mpr (by simpa [mul_comm] using hx)
  calc
    (Real.sqrt b)⁻¹ * x * (Real.sqrt b)⁻¹ = x / b := by
      calc
        (Real.sqrt b)⁻¹ * x * (Real.sqrt b)⁻¹ =
            x * ((Real.sqrt b) ^ 2)⁻¹ := by
              field_simp [hsqrt_pos.ne']
        _ = x * b⁻¹ := by rw [hsq]
        _ = x / b := by rw [div_eq_mul_inv]
    _ ≤ A := hmul

private theorem sqrt_mul_inv_le_of_mul_le {c x A : ℝ} (hc : 0 < c)
    (hx : c * x ≤ A) :
    Real.sqrt c * x * Real.sqrt c ≤ A := by
  have hsq : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc.le
  calc
    Real.sqrt c * x * Real.sqrt c = c * x := by
      calc
        Real.sqrt c * x * Real.sqrt c = (Real.sqrt c) ^ 2 * x := by ring
        _ = c * x := by rw [hsq]
    _ ≤ A := hx

private theorem one_le_inv_sqrt_mul_of_le {b x : ℝ} (hb : 0 < b)
    (hbx : b ≤ x) :
    1 ≤ (Real.sqrt b)⁻¹ * x * (Real.sqrt b)⁻¹ := by
  have hxdiv : 1 ≤ x / b :=
    (le_div_iff₀ hb).mpr (by simpa using hbx)
  have hsqrt_pos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
  calc
    1 ≤ x / b := hxdiv
    _ = (Real.sqrt b)⁻¹ * x * (Real.sqrt b)⁻¹ := by
      symm
      calc
        (Real.sqrt b)⁻¹ * x * (Real.sqrt b)⁻¹ =
            x * ((Real.sqrt b) ^ 2)⁻¹ := by
              field_simp [hsqrt_pos.ne']
        _ = x * b⁻¹ := by rw [hsq]
        _ = x / b := by rw [div_eq_mul_inv]

private theorem one_le_sqrt_mul_inv_of_inv_le {c x : ℝ} (hc : 0 < c)
    (hinv : c⁻¹ ≤ x) :
    1 ≤ Real.sqrt c * x * Real.sqrt c := by
  have hmul : 1 ≤ c * x := by
    calc
      1 = c * c⁻¹ := by field_simp [hc.ne']
      _ ≤ c * x := mul_le_mul_of_nonneg_left hinv hc.le
  have hsq : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc.le
  calc
    1 ≤ c * x := hmul
    _ = Real.sqrt c * x * Real.sqrt c := by
      symm
      calc
        Real.sqrt c * x * Real.sqrt c = (Real.sqrt c) ^ 2 * x := by ring
        _ = c * x := by rw [hsq]

/-- At a good scale, each intermediate annealed block is at most `(1+delta)`
after normalization by the top scale. -/
theorem normalizedAnnealedQuadratic_le_one_add_delta_mul_dotProduct_of_good
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (m k : ℕ) (_hk : k ≤ m)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (q : FullBlockVec d) :
    let bm := hP.barSigmaAtScale hStruct (m : ℤ)
    let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
    let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bm cm)
    fullBlockQuadratic (D * toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (k : ℤ)) * D) q ≤
      (1 + delta) * dotProduct q q := by
  classical
  dsimp only
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let bk := hP.barSigmaAtScale hStruct (k : ℤ)
  let ck := hP.barSigmaStarAtScale hStruct (k : ℤ)
  let r : BlockCoord d → ℝ := fun α =>
    match α with
    | Sum.inl _ => (Real.sqrt bm)⁻¹ * bk * (Real.sqrt bm)⁻¹
    | Sum.inr _ => Real.sqrt cm * ck⁻¹ * Real.sqrt cm
  have hbm_pos : 0 < bm := by
    simpa [bm] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hcm_pos : 0 < cm := by
    simpa [cm] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hchain_k0 := Pigeonhole.scalarChain_of_P4 hP hStruct hP4 (Nat.zero_le k)
  have hbk_le_good : bk ≤ (1 + delta) * bm := by
    have hbk_le_zero : bk ≤ hP.barSigmaAtScale hStruct 0 := by
      simpa [bk] using hchain_k0.2.2
    exact hbk_le_zero.trans (by simpa [bm] using hgood_upper)
  have hck_inv_le_good : ck⁻¹ ≤ (1 + delta) * cm⁻¹ := by
    have hck_le_zero : ck⁻¹ ≤ (hP.barSigmaStarAtScale hStruct 0)⁻¹ := by
      simpa [ck] using hchain_k0.2.1
    exact hck_le_zero.trans (by simpa [cm] using hgood_lower)
  have hcm_mul_ck : cm * ck⁻¹ ≤ 1 + delta := by
    calc
      cm * ck⁻¹ ≤ cm * ((1 + delta) * cm⁻¹) :=
        mul_le_mul_of_nonneg_left hck_inv_le_good hcm_pos.le
      _ = 1 + delta := by field_simp [hcm_pos.ne']
  have hmat :
      Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bm cm) *
          toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (k : ℤ)) *
            Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bm cm) =
        Matrix.diagonal r := by
    rw [annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale hP hStruct (k : ℤ)]
    simpa [bm, cm, bk, ck, r] using!
      normalizedScalarAnnealedBlockMatrix_eq_diagonal hP hStruct (m : ℤ) (k : ℤ)
  rw [hmat]
  exact fullBlockQuadratic_diagonal_le_mul_dotProduct q (fun α => by
    cases α with
    | inl i =>
        simpa [r, bm, bk] using
          inv_sqrt_mul_le_of_le_mul hbm_pos hbk_le_good
    | inr i =>
        simpa [r, cm, ck] using
          sqrt_mul_inv_le_of_mul_le hcm_pos hcm_mul_ck)

/-- Scalar-chain monotonicity gives the lower normalized annealed bound. -/
theorem dotProduct_le_normalizedAnnealedQuadratic_of_scalarChain
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m k : ℕ) (hk : k ≤ m) (q : FullBlockVec d) :
    let bm := hP.barSigmaAtScale hStruct (m : ℤ)
    let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
    let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bm cm)
    dotProduct q q ≤
      fullBlockQuadratic (D * toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (k : ℤ)) * D) q := by
  classical
  dsimp only
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let bk := hP.barSigmaAtScale hStruct (k : ℤ)
  let ck := hP.barSigmaStarAtScale hStruct (k : ℤ)
  let r : BlockCoord d → ℝ := fun α =>
    match α with
    | Sum.inl _ => (Real.sqrt bm)⁻¹ * bk * (Real.sqrt bm)⁻¹
    | Sum.inr _ => Real.sqrt cm * ck⁻¹ * Real.sqrt cm
  have hbm_pos : 0 < bm := by
    simpa [bm] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hcm_pos : 0 < cm := by
    simpa [cm] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hchain_km := Pigeonhole.scalarChain_of_P4 hP hStruct hP4 hk
  have hbm_le_bk : bm ≤ bk := by
    simpa [bm, bk] using hchain_km.2.2
  have hcm_inv_le_ck_inv : cm⁻¹ ≤ ck⁻¹ := by
    simpa [cm, ck] using hchain_km.2.1
  have hmat :
      Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bm cm) *
          toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (k : ℤ)) *
            Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bm cm) =
        Matrix.diagonal r := by
    rw [annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale hP hStruct (k : ℤ)]
    simpa [bm, cm, bk, ck, r] using!
      normalizedScalarAnnealedBlockMatrix_eq_diagonal hP hStruct (m : ℤ) (k : ℤ)
  rw [hmat]
  calc
    dotProduct q q = 1 * dotProduct q q := by ring
    _ ≤ fullBlockQuadratic (Matrix.diagonal r) q :=
      mul_dotProduct_le_fullBlockQuadratic_diagonal q (fun α => by
        cases α with
        | inl i =>
            simpa [r, bm, bk] using
              one_le_inv_sqrt_mul_of_le hbm_pos hbm_le_bk
        | inr i =>
            simpa [r, cm, ck] using
              one_le_sqrt_mul_inv_of_inv_le hcm_pos hcm_inv_le_ck_inv)

/-- Good-scale upper bound for the mean of a normalized quadratic probe. -/
theorem integral_origin_fullBlockNormalizedQuadraticObservable_le_base_add_delta_mul_dotProduct_of_good
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (m k : ℕ) (hk : k ≤ m)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (q : FullBlockVec d) :
    (∫ a,
      fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
        (cubeSet (originCube d (k : ℤ))) a.toFun ∂P) ≤
      dotProduct q q + delta * dotProduct q q := by
  have hmean :=
    integral_origin_fullBlockNormalizedQuadraticObservable_eq_annealedBlockMatrixAtScale_from_P4
      hP hStruct hP4 (m : ℤ) (k : ℤ) (by exact_mod_cast Nat.zero_le k) q
  rw [hmean]
  have hquad :=
    normalizedAnnealedQuadratic_le_one_add_delta_mul_dotProduct_of_good
      hP hStruct hP4 (m := m) (k := k) hk hgood_upper hgood_lower q
  calc
    fullBlockQuadratic
        ((Matrix.diagonal
            (Ch04.scalarFullBlockInvSqrtDiag (hP.barSigmaAtScale hStruct (m : ℤ))
              (hP.barSigmaStarAtScale hStruct (m : ℤ)))) *
          toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (k : ℤ)) *
            Matrix.diagonal
              (Ch04.scalarFullBlockInvSqrtDiag (hP.barSigmaAtScale hStruct (m : ℤ))
                (hP.barSigmaStarAtScale hStruct (m : ℤ)))) q
        ≤ (1 + delta) * dotProduct q q := by
          simpa using hquad
    _ = dotProduct q q + delta * dotProduct q q := by ring

/-- Scalar-chain lower bound for the mean of a normalized quadratic probe. -/
theorem dotProduct_le_integral_origin_fullBlockNormalizedQuadraticObservable_of_scalarChain
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m k : ℕ) (hk : k ≤ m) (q : FullBlockVec d) :
    dotProduct q q ≤
      ∫ a,
        fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
          (cubeSet (originCube d (k : ℤ))) a.toFun ∂P := by
  have hmean :=
    integral_origin_fullBlockNormalizedQuadraticObservable_eq_annealedBlockMatrixAtScale_from_P4
      hP hStruct hP4 (m : ℤ) (k : ℤ) (by exact_mod_cast Nat.zero_le k) q
  rw [hmean]
  exact
    dotProduct_le_normalizedAnnealedQuadratic_of_scalarChain
      hP hStruct hP4 m k hk q

/-- Good-scale positive-part control for a normalized quadratic probe on an
origin cube. -/
theorem fullBlockNormalizedQuadraticObservable_positivePart_good_origin_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (m j : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (q : FullBlockVec d) :
    (fun a : RegCoeffField d =>
      max (fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
        (cubeSet (originCube d (j : ℤ))) a.toFun - dotProduct q q) 0)
      ≤ᵐ[P]
    fun a : RegCoeffField d =>
      delta * dotProduct q q +
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ) q) a| := by
  have hmean_le :=
    integral_origin_fullBlockNormalizedQuadraticObservable_le_base_add_delta_mul_dotProduct_of_good
      hP hStruct hP4 (m := m) (k := 0) (by omega) hgood_upper hgood_lower q
  have herr : 0 ≤ delta * dotProduct q q :=
    mul_nonneg hdelta_nonneg (dotProduct_self_nonneg q)
  have hpos :=
    fullBlockNormalizedQuadraticObservable_positivePart_base_le_error_add_centeredAverageOnCube_ae
      hP hStruct (m : ℤ) q (originCube d (j : ℤ)) (k := 0)
      (base := dotProduct q q) (err := delta * dotProduct q q)
      (by change (0 : ℤ) ≤ (j : ℤ); exact_mod_cast Nat.zero_le j)
      herr (by simpa [zero_add] using hmean_le)
  simpa [Ch04.restrictionCenteredDescendantAverageOnCube, Ch04.restrictionCenteredDescendantAverage] using hpos

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
