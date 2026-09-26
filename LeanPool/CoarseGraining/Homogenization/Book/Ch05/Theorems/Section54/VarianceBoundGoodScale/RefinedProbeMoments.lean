/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ProbeMomentCompression
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.MomentFactorBounds.FactorBounds

/-! # Refined Probe Moments -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open MeasureTheory

noncomputable section

/-!
# Refined probe moments at a good scale

The coarse probe moment bounds in `QuadraticProbeBounds` dominate every probe
by one scalar times `Λ + λ⁻¹`.  For the final good-scale variance estimate we
need the matched form: upper coordinates cost only the upper unit-scale factor
and lower coordinates cost only the lower inverse factor.  This file supplies
that local refinement and compresses it to `\widetilde\Theta_0` using the two
good-scale scalar hypotheses.
-/

/-- Upper unit-scale coefficient carried by a coordinate probe after
normalization at scale `m`.  It is nonzero only on the upper block. -/
noncomputable def coordinateProbeUpperCoeffAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m : ℕ) : BlockCoord d → ℝ
  | Sum.inl _ => (hP.barSigmaAtScale hStruct (m : ℤ))⁻¹
  | Sum.inr _ => 0

/-- Lower unit-scale coefficient carried by a coordinate probe after
normalization at scale `m`.  It is nonzero only on the lower block. -/
noncomputable def coordinateProbeLowerCoeffAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m : ℕ) : BlockCoord d → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => hP.barSigmaStarAtScale hStruct (m : ℤ)

theorem coordinateProbeUpperCoeffAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (α : BlockCoord d) :
    0 ≤ coordinateProbeUpperCoeffAtScale hP hStruct m α := by
  cases α with
  | inl i =>
      exact (inv_pos.mpr
        (Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m)).le
  | inr i =>
      simp [coordinateProbeUpperCoeffAtScale]

theorem coordinateProbeLowerCoeffAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (α : BlockCoord d) :
    0 ≤ coordinateProbeLowerCoeffAtScale hP hStruct m α := by
  cases α with
  | inl i =>
      simp [coordinateProbeLowerCoeffAtScale]
  | inr i =>
      exact (Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m).le

private theorem scalarFullBlockInvSqrtDiag_upper_abs_mul_self
    {d : ℕ} {b c : ℝ} (hb : 0 < b) (i : Fin d) :
    |Ch04.scalarFullBlockInvSqrtDiag (d := d) b c (Sum.inl i)| *
        |Ch04.scalarFullBlockInvSqrtDiag (d := d) b c (Sum.inl i)| =
      b⁻¹ := by
  have hsqrt_pos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsqrt_ne : Real.sqrt b ≠ 0 := hsqrt_pos.ne'
  simp [Ch04.scalarFullBlockInvSqrtDiag,
    abs_of_pos (inv_pos.mpr hsqrt_pos)]
  field_simp [hsqrt_ne]
  rw [Real.sq_sqrt hb.le]

private theorem scalarFullBlockInvSqrtDiag_lower_abs_mul_self
    {d : ℕ} {b c : ℝ} (hc : 0 < c) (i : Fin d) :
    |Ch04.scalarFullBlockInvSqrtDiag (d := d) b c (Sum.inr i)| *
        |Ch04.scalarFullBlockInvSqrtDiag (d := d) b c (Sum.inr i)| =
      c := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  simp [Ch04.scalarFullBlockInvSqrtDiag, abs_of_nonneg hsqrt_nonneg]
  rw [← sq, Real.sq_sqrt hc.le]

/-- Matched pointwise domination for coordinate probes: upper coordinates see
only the upper unit-scale factor, lower coordinates only the lower inverse
factor. -/
theorem fullBlockNormalizedQuadraticObservable_coordinateProbe_abs_le_weighted_factors_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (α : BlockCoord d) :
    (fun a : RegCoeffField d =>
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
          (fullBlockCoordinateProbe α) (cubeSet (originCube d 0)) a|)
      ≤ᵐ[P]
        fun a =>
          coordinateProbeUpperCoeffAtScale hP hStruct m α *
              Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a +
            coordinateProbeLowerCoeffAtScale hP hStruct m α *
              (Ch04.lambdaSqCoeffField
                (originCube d 0) hP4.sLower (.finite 1) a)⁻¹ := by
  cases α with
  | inl i =>
      filter_upwards
        [Ch04.RestrictionLawCarrier.upperLeft_abs_entry_le_LambdaSqCoeffField_ae
          hP (originCube d 0) hP4.sUpper_pos i i] with a hentry
      let b := hP.barSigmaAtScale hStruct (m : ℤ)
      let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
      let r := Ch04.scalarFullBlockInvSqrtDiag (d := d) b c
      let L := Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a
      have hb : 0 < b := by
        simpa [b] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
      have hcoeff :
          |r (Sum.inl i)| * |r (Sum.inl i)| = b⁻¹ := by
        simpa [r] using
          scalarFullBlockInvSqrtDiag_upper_abs_mul_self (d := d) (b := b) (c := c) hb i
      have hquad :
          fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
              (fullBlockCoordinateProbe (Sum.inl i)) (cubeSet (originCube d 0)) a =
            r (Sum.inl i) *
              blockMatEntry (coarseBlockMatrix (cubeSet (originCube d 0)) a)
                (Sum.inl i) (Sum.inl i) *
              r (Sum.inl i) := by
        simpa [fullBlockNormalizedQuadraticObservable, b, c, r] using
          fullBlockQuadratic_diagonal_coordinateProbe r
            (coarseBlockMatrix (cubeSet (originCube d 0)) a) (Sum.inl i)
      calc
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
            (fullBlockCoordinateProbe (Sum.inl i)) (cubeSet (originCube d 0)) a|
            =
              |r (Sum.inl i) *
                blockMatEntry (coarseBlockMatrix (cubeSet (originCube d 0)) a)
                  (Sum.inl i) (Sum.inl i) *
                r (Sum.inl i)| := by rw [hquad]
        _ ≤ |r (Sum.inl i)| * |r (Sum.inl i)| * L := by
          simpa [L, blockMatEntry] using
            abs_mul_entry_mul_le_factor
              (x := r (Sum.inl i)) (y := r (Sum.inl i))
              (e := (coarseBlockMatrix (cubeSet (originCube d 0)) a).upperLeft i i)
              hentry
        _ =
            coordinateProbeUpperCoeffAtScale hP hStruct m (Sum.inl i) *
                Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a +
              coordinateProbeLowerCoeffAtScale hP hStruct m (Sum.inl i) *
                (Ch04.lambdaSqCoeffField
                  (originCube d 0) hP4.sLower (.finite 1) a)⁻¹ := by
          simp [coordinateProbeUpperCoeffAtScale, coordinateProbeLowerCoeffAtScale,
            b, L, hcoeff]
  | inr i =>
      filter_upwards
        [Ch04.RestrictionLawCarrier.lowerRight_abs_entry_le_lambdaSqCoeffField_inv_ae
          hP (originCube d 0) hP4.sLower_pos i i] with a hentry
      let b := hP.barSigmaAtScale hStruct (m : ℤ)
      let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
      let r := Ch04.scalarFullBlockInvSqrtDiag (d := d) b c
      let I :=
        (Ch04.lambdaSqCoeffField (originCube d 0) hP4.sLower (.finite 1) a)⁻¹
      have hc : 0 < c := by
        simpa [c] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
      have hcoeff :
          |r (Sum.inr i)| * |r (Sum.inr i)| = c := by
        simpa [r] using
          scalarFullBlockInvSqrtDiag_lower_abs_mul_self (d := d) (b := b) (c := c) hc i
      have hquad :
          fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
              (fullBlockCoordinateProbe (Sum.inr i)) (cubeSet (originCube d 0)) a =
            r (Sum.inr i) *
              blockMatEntry (coarseBlockMatrix (cubeSet (originCube d 0)) a)
                (Sum.inr i) (Sum.inr i) *
              r (Sum.inr i) := by
        simpa [fullBlockNormalizedQuadraticObservable, b, c, r] using
          fullBlockQuadratic_diagonal_coordinateProbe r
            (coarseBlockMatrix (cubeSet (originCube d 0)) a) (Sum.inr i)
      calc
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
            (fullBlockCoordinateProbe (Sum.inr i)) (cubeSet (originCube d 0)) a|
            =
              |r (Sum.inr i) *
                blockMatEntry (coarseBlockMatrix (cubeSet (originCube d 0)) a)
                  (Sum.inr i) (Sum.inr i) *
                r (Sum.inr i)| := by rw [hquad]
        _ ≤ |r (Sum.inr i)| * |r (Sum.inr i)| * I := by
          simpa [I, blockMatEntry] using
            abs_mul_entry_mul_le_factor
              (x := r (Sum.inr i)) (y := r (Sum.inr i))
              (e := (coarseBlockMatrix (cubeSet (originCube d 0)) a).lowerRight i i)
              hentry
        _ =
            coordinateProbeUpperCoeffAtScale hP hStruct m (Sum.inr i) *
                Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a +
              coordinateProbeLowerCoeffAtScale hP hStruct m (Sum.inr i) *
                (Ch04.lambdaSqCoeffField
                  (originCube d 0) hP4.sLower (.finite 1) a)⁻¹ := by
          simp [coordinateProbeUpperCoeffAtScale, coordinateProbeLowerCoeffAtScale,
            c, I, hcoeff]

private theorem isSymmetricBlockMat_coarseBlockMatrix_origin_of_ae
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a) :
    IsSymmetricBlockMat (coarseBlockMatrix (cubeSet (originCube d 0)) a) := by
  let Q : TriadicCube d := originCube d 0
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  rw [show originCube d 0 = Q from rfl, hEq]
  exact Ch02.isSymmetricBlockMat_coarseBlockMatrix
    (Ch02.cubeDomain Q) (F.coeffOn Q)

private theorem fullBlockNormalizedQuadraticObservable_plus_add_minus_eq_two_coord_sum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m : ℕ) {α β : BlockCoord d} (hαβ : α ≠ β)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a) :
    fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
        (fullBlockPlusProbe α β) (cubeSet (originCube d 0)) a +
      fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
        (fullBlockMinusProbe α β) (cubeSet (originCube d 0)) a =
      2 *
        (fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
            (fullBlockCoordinateProbe α) (cubeSet (originCube d 0)) a +
          fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
            (fullBlockCoordinateProbe β) (cubeSet (originCube d 0)) a) := by
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let r := Ch04.scalarFullBlockInvSqrtDiag (d := d) b c
  let A := coarseBlockMatrix (cubeSet (originCube d 0)) a
  have hSymm : IsSymmetricBlockMat A := by
    simpa [A] using isSymmetricBlockMat_coarseBlockMatrix_origin_of_ae ha
  have hplus :=
    fullBlockQuadratic_diagonal_plusProbe_of_ne
      (d := d) r (A := A) hSymm hαβ
  have hminus :=
    fullBlockQuadratic_diagonal_minusProbe_of_ne
      (d := d) r (A := A) hSymm hαβ
  have hcoordα :=
    fullBlockQuadratic_diagonal_coordinateProbe
      (d := d) r A α
  have hcoordβ :=
    fullBlockQuadratic_diagonal_coordinateProbe
      (d := d) r A β
  simpa [fullBlockNormalizedQuadraticObservable, b, c, r, A,
    hplus, hminus, hcoordα, hcoordβ] using
    (by ring :
      (r α * blockMatEntry A α α * r α +
            2 * (r α * blockMatEntry A α β * r β) +
            r β * blockMatEntry A β β * r β) +
          (r α * blockMatEntry A α α * r α -
            2 * (r α * blockMatEntry A α β * r β) +
            r β * blockMatEntry A β β * r β) =
        2 *
          ((r α * blockMatEntry A α α * r α) +
            (r β * blockMatEntry A β β * r β)))

private theorem fullBlockNormalizedQuadraticObservable_pairProbe_abs_le_weighted_factors_ae_aux
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) {α β : BlockCoord d} (_hαβ : α ≠ β)
    (probe otherProbe : FullBlockVec d)
    (hsum :
      ∀ {a : RegCoeffField d}, Ch04.AELocallyUniformlyEllipticField a →
        fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
            probe (cubeSet (originCube d 0)) a +
          fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
            otherProbe (cubeSet (originCube d 0)) a =
        2 *
          (fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
              (fullBlockCoordinateProbe α) (cubeSet (originCube d 0)) a +
            fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
              (fullBlockCoordinateProbe β) (cubeSet (originCube d 0)) a)) :
    (fun a : RegCoeffField d =>
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
          probe (cubeSet (originCube d 0)) a|)
      ≤ᵐ[P]
        fun a =>
          (2 *
              (coordinateProbeUpperCoeffAtScale hP hStruct m α +
                coordinateProbeUpperCoeffAtScale hP hStruct m β)) *
              Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a +
            (2 *
              (coordinateProbeLowerCoeffAtScale hP hStruct m α +
                coordinateProbeLowerCoeffAtScale hP hStruct m β)) *
              (Ch04.lambdaSqCoeffField
                (originCube d 0) hP4.sLower (.finite 1) a)⁻¹ := by
  have hcoordα :=
    fullBlockNormalizedQuadraticObservable_coordinateProbe_abs_le_weighted_factors_ae
      hP hStruct hP4 m α
  have hcoordβ :=
    fullBlockNormalizedQuadraticObservable_coordinateProbe_abs_le_weighted_factors_ae
      hP hStruct hP4 m β
  filter_upwards
    [hcoordα, hcoordβ, hP.ae_locallyUniformlyEllipticField,
      fullBlockNormalizedQuadraticObservable_nonneg_ae
        hP hStruct (m : ℤ) probe (originCube d 0),
      fullBlockNormalizedQuadraticObservable_nonneg_ae
        hP hStruct (m : ℤ) otherProbe (originCube d 0)]
    with a hα hβ hae hprobe_nonneg hother_nonneg
  let X :=
    fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
      probe (cubeSet (originCube d 0)) a
  let Y :=
    fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
      otherProbe (cubeSet (originCube d 0)) a
  let A :=
    fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
      (fullBlockCoordinateProbe α) (cubeSet (originCube d 0)) a
  let B :=
    fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
      (fullBlockCoordinateProbe β) (cubeSet (originCube d 0)) a
  let L := Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a
  let I :=
    (Ch04.lambdaSqCoeffField (originCube d 0) hP4.sLower (.finite 1) a)⁻¹
  let Cuα := coordinateProbeUpperCoeffAtScale hP hStruct m α
  let Cuβ := coordinateProbeUpperCoeffAtScale hP hStruct m β
  let Clα := coordinateProbeLowerCoeffAtScale hP hStruct m α
  let Clβ := coordinateProbeLowerCoeffAtScale hP hStruct m β
  have hX_nonneg : 0 ≤ X := by simpa [X] using hprobe_nonneg
  have hY_nonneg : 0 ≤ Y := by simpa [Y] using hother_nonneg
  have hsum_point : X + Y = 2 * (A + B) := by
    simpa [X, Y, A, B] using hsum (a := a) hae
  have hX_le_two :
      X ≤ 2 * (A + B) := by
    calc
      X ≤ X + Y := by linarith
      _ = 2 * (A + B) := hsum_point
  have hA_le : A ≤ Cuα * L + Clα * I := by
    calc
      A ≤ |A| := le_abs_self A
      _ ≤ Cuα * L + Clα * I := by simpa [A, L, I, Cuα, Clα] using hα
  have hB_le : B ≤ Cuβ * L + Clβ * I := by
    calc
      B ≤ |B| := le_abs_self B
      _ ≤ Cuβ * L + Clβ * I := by simpa [B, L, I, Cuβ, Clβ] using hβ
  have htwo :
      2 * (A + B) ≤
        (2 * (Cuα + Cuβ)) * L + (2 * (Clα + Clβ)) * I := by
    nlinarith
  calc
    |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
        probe (cubeSet (originCube d 0)) a|
        = X := by simp [X, abs_of_nonneg hX_nonneg]
    _ ≤ 2 * (A + B) := hX_le_two
    _ ≤ (2 * (Cuα + Cuβ)) * L + (2 * (Clα + Clβ)) * I := htwo
    _ =
        (2 *
            (coordinateProbeUpperCoeffAtScale hP hStruct m α +
              coordinateProbeUpperCoeffAtScale hP hStruct m β)) *
            Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a +
          (2 *
            (coordinateProbeLowerCoeffAtScale hP hStruct m α +
              coordinateProbeLowerCoeffAtScale hP hStruct m β)) *
            (Ch04.lambdaSqCoeffField
              (originCube d 0) hP4.sLower (.finite 1) a)⁻¹ := by
      simp [Cuα, Cuβ, Clα, Clβ, L, I]

/-- Matched pointwise domination for plus probes. -/
theorem fullBlockNormalizedQuadraticObservable_plusProbe_abs_le_weighted_factors_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) {α β : BlockCoord d} (hαβ : α ≠ β) :
    (fun a : RegCoeffField d =>
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
          (fullBlockPlusProbe α β) (cubeSet (originCube d 0)) a|)
      ≤ᵐ[P]
        fun a =>
          (2 *
              (coordinateProbeUpperCoeffAtScale hP hStruct m α +
                coordinateProbeUpperCoeffAtScale hP hStruct m β)) *
              Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a +
            (2 *
              (coordinateProbeLowerCoeffAtScale hP hStruct m α +
                coordinateProbeLowerCoeffAtScale hP hStruct m β)) *
              (Ch04.lambdaSqCoeffField
                (originCube d 0) hP4.sLower (.finite 1) a)⁻¹ := by
  refine
    fullBlockNormalizedQuadraticObservable_pairProbe_abs_le_weighted_factors_ae_aux
      hP hStruct hP4 m hαβ
      (fullBlockPlusProbe α β) (fullBlockMinusProbe α β) ?_
  intro a ha
  exact
    fullBlockNormalizedQuadraticObservable_plus_add_minus_eq_two_coord_sum
      hP hStruct m hαβ ha

/-- Matched pointwise domination for minus probes. -/
theorem fullBlockNormalizedQuadraticObservable_minusProbe_abs_le_weighted_factors_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) {α β : BlockCoord d} (hαβ : α ≠ β) :
    (fun a : RegCoeffField d =>
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
          (fullBlockMinusProbe α β) (cubeSet (originCube d 0)) a|)
      ≤ᵐ[P]
        fun a =>
          (2 *
              (coordinateProbeUpperCoeffAtScale hP hStruct m α +
                coordinateProbeUpperCoeffAtScale hP hStruct m β)) *
              Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a +
            (2 *
              (coordinateProbeLowerCoeffAtScale hP hStruct m α +
                coordinateProbeLowerCoeffAtScale hP hStruct m β)) *
              (Ch04.lambdaSqCoeffField
                (originCube d 0) hP4.sLower (.finite 1) a)⁻¹ := by
  refine
    fullBlockNormalizedQuadraticObservable_pairProbe_abs_le_weighted_factors_ae_aux
      hP hStruct hP4 m hαβ
      (fullBlockMinusProbe α β) (fullBlockPlusProbe α β) ?_
  intro a ha
  have h :=
    fullBlockNormalizedQuadraticObservable_plus_add_minus_eq_two_coord_sum
      hP hStruct m hαβ ha
  linarith

private theorem fullBlockNormalizedQuadraticObservable_origin_regular'
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        fullBlockNormalizedQuadraticObservable hP hStruct center q
          (cubeSet (originCube d 0)) a) P := by
  rcases exists_isRestrictionLocalRandomVariable_ae_eq_fullBlockNormalizedQuadraticObservable_cubeSet
      hP hStruct center q (originCube d 0) with ⟨Y, hY_local, hY_eq⟩
  exact (hP.aemeasurable_of_isLocalRandomVariable hY_local).congr hY_eq.symm

private theorem coordinateProbe_weighted_moments_le_one_add_delta_mul_widetildeTheta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (m : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (α : BlockCoord d) :
    coordinateProbeUpperCoeffAtScale hP hStruct m α *
        Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
      coordinateProbeLowerCoeffAtScale hP hStruct m α *
        Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi ≤
      (1 + delta) * widetildeThetaAtScale P 0 hP4 := by
  let L0 := Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  let l0 := Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  have hL0_nonneg : 0 ≤ L0 := by
    simpa [L0] using Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos
  have hl0_nonneg : 0 ≤ l0 := by
    simpa [l0] using Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos
  cases α with
  | inl i =>
      have hcoeff :
          (hP.barSigmaAtScale hStruct (m : ℤ))⁻¹ ≤ (1 + delta) * l0 := by
        simpa [l0] using
          barSigmaAtScale_inv_le_one_add_delta_mul_lambdaInvMomentAtScale_zero_of_good
            hP hStruct hP4 hdelta_nonneg m hgood_upper
      calc
        coordinateProbeUpperCoeffAtScale hP hStruct m (Sum.inl i) * L0 +
            coordinateProbeLowerCoeffAtScale hP hStruct m (Sum.inl i) * l0
            = (hP.barSigmaAtScale hStruct (m : ℤ))⁻¹ * L0 := by
              simp [coordinateProbeUpperCoeffAtScale, coordinateProbeLowerCoeffAtScale, L0, l0]
        _ ≤ ((1 + delta) * l0) * L0 :=
              mul_le_mul_of_nonneg_right hcoeff hL0_nonneg
        _ = (1 + delta) * widetildeThetaAtScale P 0 hP4 := by
              simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale, L0, l0]
              ring
  | inr i =>
      have hcoeff :
          hP.barSigmaStarAtScale hStruct (m : ℤ) ≤ (1 + delta) * L0 := by
        simpa [L0] using
          barSigmaStarAtScale_le_one_add_delta_mul_LambdaMomentAtScale_zero_of_good
            hP hStruct hP4 hdelta_nonneg m hgood_lower
      calc
        coordinateProbeUpperCoeffAtScale hP hStruct m (Sum.inr i) * L0 +
            coordinateProbeLowerCoeffAtScale hP hStruct m (Sum.inr i) * l0
            = hP.barSigmaStarAtScale hStruct (m : ℤ) * l0 := by
              simp [coordinateProbeUpperCoeffAtScale, coordinateProbeLowerCoeffAtScale, L0, l0]
        _ ≤ ((1 + delta) * L0) * l0 :=
              mul_le_mul_of_nonneg_right hcoeff hl0_nonneg
        _ = (1 + delta) * widetildeThetaAtScale P 0 hP4 := by
              simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale, L0, l0]
              ring

private theorem pairProbe_weighted_moments_le_four_mul_one_add_delta_mul_widetildeTheta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (m : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (α β : BlockCoord d) :
    (2 *
        (coordinateProbeUpperCoeffAtScale hP hStruct m α +
          coordinateProbeUpperCoeffAtScale hP hStruct m β)) *
        Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
      (2 *
        (coordinateProbeLowerCoeffAtScale hP hStruct m α +
          coordinateProbeLowerCoeffAtScale hP hStruct m β)) *
        Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi ≤
      4 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) := by
  let L0 := Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  let l0 := Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  let Θ0 := widetildeThetaAtScale P 0 hP4
  have hα :
      coordinateProbeUpperCoeffAtScale hP hStruct m α * L0 +
        coordinateProbeLowerCoeffAtScale hP hStruct m α * l0 ≤
      (1 + delta) * Θ0 := by
    simpa [L0, l0, Θ0] using
      coordinateProbe_weighted_moments_le_one_add_delta_mul_widetildeTheta
        hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower α
  have hβ :
      coordinateProbeUpperCoeffAtScale hP hStruct m β * L0 +
        coordinateProbeLowerCoeffAtScale hP hStruct m β * l0 ≤
      (1 + delta) * Θ0 := by
    simpa [L0, l0, Θ0] using
      coordinateProbe_weighted_moments_le_one_add_delta_mul_widetildeTheta
        hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower β
  nlinarith

/-- Centered origin moment for coordinate probes, compressed to
`\widetilde\Theta_0` by the good-scale hypotheses. -/
theorem coordinateProbe_centeredOrigin_momentRoot_le_widetildeTheta_of_good
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (m : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (α : BlockCoord d) :
    Integrable
        (fun a =>
          |Ch04.restrictionCenteredOriginObservable P 0
            (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
              (fullBlockCoordinateProbe α)) a| ^ hP4.xi) P ∧
      Ch04.annealedMomentRoot P hP4.xi
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
                (fullBlockCoordinateProbe α)) a|)
        ≤
          2 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) := by
  let X : RegCoeffField d → ℝ :=
    fun a =>
      fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
        (fullBlockCoordinateProbe α) (cubeSet (originCube d 0)) a
  let Cu := coordinateProbeUpperCoeffAtScale hP hStruct m α
  let Cl := coordinateProbeLowerCoeffAtScale hP hStruct m α
  have hX_meas : AEMeasurable X P := by
    simpa [X] using
      fullBlockNormalizedQuadraticObservable_origin_regular'
        hP hStruct (m : ℤ) (fullBlockCoordinateProbe α)
  have hbridge :=
    section54_centeredOrigin_momentRoot_le_weighted_factor_sum_of_abs_le
      hP hStruct hP4
      (CUpper := Cu) (CLower := Cl)
      (by simpa [Cu] using
        coordinateProbeUpperCoeffAtScale_nonneg hP hStruct hP4 m α)
      (by simpa [Cl] using
        coordinateProbeLowerCoeffAtScale_nonneg hP hStruct hP4 m α)
      (X := X) hX_meas
      (by
        simpa [X, Cu, Cl] using
          fullBlockNormalizedQuadraticObservable_coordinateProbe_abs_le_weighted_factors_ae
            hP hStruct hP4 m α)
  refine ⟨?_, ?_⟩
  · simpa [X, Ch04.restrictionCenteredOriginObservable] using! hbridge.1
  · have hweighted :=
      coordinateProbe_weighted_moments_le_one_add_delta_mul_widetildeTheta
        hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower α
    calc
      Ch04.annealedMomentRoot P hP4.xi
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
                (fullBlockCoordinateProbe α)) a|)
          ≤ 2 *
              (Cu * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                Cl * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) := by
            simpa [X, Ch04.restrictionCenteredOriginObservable, Cu, Cl] using! hbridge.2
      _ ≤ 2 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) :=
            mul_le_mul_of_nonneg_left hweighted (by norm_num)

private theorem pairProbe_centeredOrigin_momentRoot_le_widetildeTheta_of_good_aux
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (m : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    {α β : BlockCoord d} (_hαβ : α ≠ β) (probe : FullBlockVec d)
    (hbound :
      (fun a : RegCoeffField d =>
          |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
            probe (cubeSet (originCube d 0)) a|)
        ≤ᵐ[P]
          fun a =>
            (2 *
                (coordinateProbeUpperCoeffAtScale hP hStruct m α +
                  coordinateProbeUpperCoeffAtScale hP hStruct m β)) *
                Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a +
              (2 *
                (coordinateProbeLowerCoeffAtScale hP hStruct m α +
                  coordinateProbeLowerCoeffAtScale hP hStruct m β)) *
                (Ch04.lambdaSqCoeffField
                  (originCube d 0) hP4.sLower (.finite 1) a)⁻¹) :
    Integrable
        (fun a =>
          |Ch04.restrictionCenteredOriginObservable P 0
            (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
              probe) a| ^ hP4.xi) P ∧
      Ch04.annealedMomentRoot P hP4.xi
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
                probe) a|)
        ≤
          8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) := by
  let X : RegCoeffField d → ℝ :=
    fun a =>
      fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
        probe (cubeSet (originCube d 0)) a
  let Cu := 2 *
    (coordinateProbeUpperCoeffAtScale hP hStruct m α +
      coordinateProbeUpperCoeffAtScale hP hStruct m β)
  let Cl := 2 *
    (coordinateProbeLowerCoeffAtScale hP hStruct m α +
      coordinateProbeLowerCoeffAtScale hP hStruct m β)
  have hCu_nonneg : 0 ≤ Cu := by
    dsimp [Cu]
    nlinarith
      [coordinateProbeUpperCoeffAtScale_nonneg hP hStruct hP4 m α,
        coordinateProbeUpperCoeffAtScale_nonneg hP hStruct hP4 m β]
  have hCl_nonneg : 0 ≤ Cl := by
    dsimp [Cl]
    nlinarith
      [coordinateProbeLowerCoeffAtScale_nonneg hP hStruct hP4 m α,
        coordinateProbeLowerCoeffAtScale_nonneg hP hStruct hP4 m β]
  have hX_meas : AEMeasurable X P := by
    simpa [X] using
      fullBlockNormalizedQuadraticObservable_origin_regular'
        hP hStruct (m : ℤ) probe
  have hbridge :=
    section54_centeredOrigin_momentRoot_le_weighted_factor_sum_of_abs_le
      hP hStruct hP4
      (CUpper := Cu) (CLower := Cl)
      hCu_nonneg hCl_nonneg
      (X := X) hX_meas
      (by simpa [X, Cu, Cl] using hbound)
  refine ⟨?_, ?_⟩
  · simpa [X, Ch04.restrictionCenteredOriginObservable] using! hbridge.1
  · have hweighted :=
      pairProbe_weighted_moments_le_four_mul_one_add_delta_mul_widetildeTheta
        hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower α β
    calc
      Ch04.annealedMomentRoot P hP4.xi
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
                probe) a|)
          ≤ 2 *
              (Cu * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                Cl * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) := by
            simpa [X, Ch04.restrictionCenteredOriginObservable, Cu, Cl] using! hbridge.2
      _ ≤ 2 * (4 * ((1 + delta) * widetildeThetaAtScale P 0 hP4)) :=
            mul_le_mul_of_nonneg_left hweighted (by norm_num)
      _ = 8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) := by ring

/-- Centered origin moment for plus probes, compressed to
`\widetilde\Theta_0` by the good-scale hypotheses. -/
theorem plusProbe_centeredOrigin_momentRoot_le_widetildeTheta_of_good
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (m : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    {α β : BlockCoord d} (hαβ : α ≠ β) :
    Integrable
        (fun a =>
          |Ch04.restrictionCenteredOriginObservable P 0
            (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
              (fullBlockPlusProbe α β)) a| ^ hP4.xi) P ∧
      Ch04.annealedMomentRoot P hP4.xi
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
                (fullBlockPlusProbe α β)) a|)
        ≤
          8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) :=
  pairProbe_centeredOrigin_momentRoot_le_widetildeTheta_of_good_aux
    hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower hαβ
    (fullBlockPlusProbe α β)
    (fullBlockNormalizedQuadraticObservable_plusProbe_abs_le_weighted_factors_ae
      hP hStruct hP4 m hαβ)

/-- Centered origin moment for minus probes, compressed to
`\widetilde\Theta_0` by the good-scale hypotheses. -/
theorem minusProbe_centeredOrigin_momentRoot_le_widetildeTheta_of_good
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (m : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    {α β : BlockCoord d} (hαβ : α ≠ β) :
    Integrable
        (fun a =>
          |Ch04.restrictionCenteredOriginObservable P 0
            (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
              (fullBlockMinusProbe α β)) a| ^ hP4.xi) P ∧
      Ch04.annealedMomentRoot P hP4.xi
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
                (fullBlockMinusProbe α β)) a|)
        ≤
          8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) :=
  pairProbe_centeredOrigin_momentRoot_le_widetildeTheta_of_good_aux
    hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower hαβ
    (fullBlockMinusProbe α β)
    (fullBlockNormalizedQuadraticObservable_minusProbe_abs_le_weighted_factors_ae
      hP hStruct hP4 m hαβ)

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
