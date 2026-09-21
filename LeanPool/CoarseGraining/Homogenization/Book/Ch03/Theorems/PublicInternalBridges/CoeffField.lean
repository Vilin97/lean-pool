/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHS
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.ForceLocalization
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.TerminalBounds
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.GlobalIteration
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.WeakSolutionBridge
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise
import LeanPool.CoarseGraining.Homogenization.PDE.EnergyIdentities
import LeanPool.CoarseGraining.Homogenization.PDE.NeumannRHS
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalCubeBridge

/-! # Coeff Field -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public coefficient-field bridges for Chapter 3

This file contains the pointwise coefficient representative, descendant-data
bridges, Ch2 multiscale translations, and homogenization-error translations
used by the broader Chapter 3 public/internal bridge layer.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- Pointwise representative of the public coefficient family on `Q`.

It is a.e. equal to the public `CoeffOn` field on the open cube, but is
pointwise elliptic on every descendant cube, making it suitable for the
deterministic coarse-graining APIs. -/
abbrev publicCoeffField {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d) :
    CoeffField d :=
  Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (a.coeffOn Q)

theorem publicCoeffField_ae_eq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) :
    publicCoeffField Q a =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
      (a.coeffOn Q).toCoeffField := by
  simpa [publicCoeffField] using
    Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
      (Ch02.cubeDomain Q) (a.coeffOn Q)

theorem publicCoeffField_ae_eq_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) :
    publicCoeffField Q a =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (a.coeffOn Q).toCoeffField := by
  simpa [Ch02.cubeDomain_coe] using publicCoeffField_ae_eq Q a

theorem publicCoeffField_ae_eq_cubeSet {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) :
    publicCoeffField Q a =ᵐ[volumeMeasureOn (cubeSet Q)]
      (a.coeffOn Q).toCoeffField := by
  simpa [volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    using publicCoeffField_ae_eq_openCubeSet Q a

theorem publicCoeffField_isEllipticFieldOn {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) :
    IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
      (Ch02.cubeDomain Q : Set (Vec d)) (publicCoeffField Q a) := by
  simpa [publicCoeffField] using
    Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
      (Ch02.cubeDomain Q) (a.coeffOn Q)

theorem publicCoeffField_isEllipticFieldOn_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) :
    IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
      (openCubeSet Q) (publicCoeffField Q a) := by
  simpa [Ch02.cubeDomain_coe] using publicCoeffField_isEllipticFieldOn Q a

theorem publicCoeffField_isEllipticFieldOn_cubeSet {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) :
    IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
      (cubeSet Q) (publicCoeffField Q a) := by
  simpa [publicCoeffField] using
    Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn_cubeSet
      Q (a.coeffOn Q)

theorem publicCoeffField_isEllipticFieldOn_descendant_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) :
    IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
      (openCubeSet R) (publicCoeffField Q a) :=
  (publicCoeffField_isEllipticFieldOn_openCubeSet Q a).mono
    (measurableSet_openCubeSet R)
    (openCubeSet_subset_of_mem_descendantsAtDepth hR)

theorem publicCoeffField_isEllipticFieldOn_descendant_cubeSet {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) :
    IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
      (cubeSet R) (publicCoeffField Q a) :=
  (publicCoeffField_isEllipticFieldOn_cubeSet Q a).mono
    (measurableSet_cubeSet R)
    (cubeSet_subset_of_mem_descendantsAtDepth hR)

theorem publicCoeffField_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d) :
    OpenCubeDescendantDeterministicCoarseData Q (publicCoeffField Q a) := by
  simpa [publicCoeffField] using
    Ch02.pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)

theorem publicCoeffField_openCubeDeterministicCoarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d) :
    OpenCubeDeterministicCoarseData Q (publicCoeffField Q a) :=
  (publicCoeffField_openCubeDescendantDeterministicCoarseData Q a).self

theorem publicCoeffField_openCubeDescendantDeterministicCoarseData_descendant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) :
    OpenCubeDescendantDeterministicCoarseData R (publicCoeffField Q a) := by
  have hscale : Q.scale - (j : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  exact OpenCubeDescendantDeterministicCoarseData.of_mem_descendantsAtScale
    (publicCoeffField_openCubeDescendantDeterministicCoarseData Q a)
    hscale (mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR)

theorem publicCoeffField_openCubeDeterministicCoarseData_descendant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) :
    OpenCubeDeterministicCoarseData R (publicCoeffField Q a) :=
  (publicCoeffField_openCubeDescendantDeterministicCoarseData_descendant
    Q a hR).self

noncomputable def h1CoerciveEstimateCubeSet
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    H1CoerciveEstimate (cubeSet Q) :=
  _root_.Homogenization.h1CoerciveEstimate_cubeSet Q

theorem publicCoeffField_summable_qtwo_maxDescendantBBlockNormAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ =>
      geometricWeight s 2 n *
        maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ))
          (publicCoeffField Q a)) :=
  _root_.Homogenization.summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
    (Q := Q) (a := publicCoeffField Q a) s hs
    (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
    (publicCoeffField_openCubeDescendantDeterministicCoarseData Q a)

theorem publicCoeffField_summable_qtwo_maxDescendantBBlockNormAtScale_rpow_one
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ =>
      geometricWeight s 2 n *
        Real.rpow
          (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ))
            (publicCoeffField Q a)) 1) := by
  simpa [Real.rpow_one] using
    publicCoeffField_summable_qtwo_maxDescendantBBlockNormAtScale
      (Q := Q) (a := a) hs

theorem publicCoeffField_summable_qtwo_maxDescendantBBlockNormAtScale_descendant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ =>
      geometricWeight s 2 n *
        maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ))
          (publicCoeffField Q a)) :=
  _root_.Homogenization.summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
    (Q := R) (a := publicCoeffField Q a) s hs
    (publicCoeffField_isEllipticFieldOn_descendant_cubeSet Q a hR)
    (publicCoeffField_openCubeDescendantDeterministicCoarseData_descendant Q a hR)

theorem publicCoeffField_summable_qtwo_maxDescendantBBlockNormAtScale_descendant_rpow_one
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ =>
      geometricWeight s 2 n *
        Real.rpow
          (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ))
            (publicCoeffField Q a)) 1) := by
  simpa [Real.rpow_one] using
    publicCoeffField_summable_qtwo_maxDescendantBBlockNormAtScale_descendant
      (Q := Q) (a := a) hR hs

theorem publicCoeffField_ae_eq_descendant_openCubeSet
    {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) :
    publicCoeffField Q a =ᵐ[volumeMeasureOn (openCubeSet R)]
      (a.coeffOn R).toCoeffField := by
  have hsubset : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hle :
      volumeMeasureOn (openCubeSet R) ≤ volumeMeasureOn (openCubeSet Q) := by
    simpa [volumeMeasureOn] using
      MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hsubset
  have hparent :
      publicCoeffField Q a =ᵐ[volumeMeasureOn (openCubeSet R)]
        (a.coeffOn Q).toCoeffField :=
    (publicCoeffField_ae_eq_openCubeSet Q a).filter_mono
      (MeasureTheory.ae_mono hle)
  have hrestrict :
      (a.coeffOn R).toCoeffField =ᵐ[volumeMeasureOn (openCubeSet R)]
        (a.coeffOn Q).toCoeffField :=
    a.restrictsTo_of_subset hsubset
  exact hparent.trans hrestrict.symm

theorem publicCoeffField_ae_eq_descendant_cubeSet
    {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) :
    publicCoeffField Q a =ᵐ[volumeMeasureOn (cubeSet R)]
      (a.coeffOn R).toCoeffField := by
  simpa [volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
    using publicCoeffField_ae_eq_descendant_openCubeSet Q a hR

theorem publicCoeffField_ae_eq_publicCoeffField_descendant_cubeSet
    {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) :
    publicCoeffField Q a =ᵐ[volumeMeasureOn (cubeSet R)]
      publicCoeffField R a := by
  exact (publicCoeffField_ae_eq_descendant_cubeSet Q a hR).trans
    (publicCoeffField_ae_eq_cubeSet R a).symm

theorem memVectorL2_cubeSet_of_forceBesovRegularity
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q s g) :
    MemVectorL2 (cubeSet Q) g :=
  memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hg.memLp

theorem memVectorL2_descendant_cubeSet_of_forceBesovRegularity
    {d : ℕ} {Q R : TriadicCube d} {s : ℝ} {j : ℕ}
    {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q s g)
    (hR : R ∈ descendantsAtDepth Q j) :
    MemVectorL2 (cubeSet R) g := by
  have hmono :
      volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
    simpa [volumeMeasureOn] using
      MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
        (cubeSet_subset_of_mem_descendantsAtDepth hR)
  exact (memVectorL2_cubeSet_of_forceBesovRegularity hg).mono_measure hmono

theorem forceBesovRegularity_descendant_memLp_normalizedCubeMeasure
    {d : ℕ} {Q R : TriadicCube d} {s : ℝ} {j : ℕ}
    {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q s g)
    (hR : R ∈ descendantsAtDepth Q j) :
    MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure R) :=
  memLp_on_descendant_of_memLp_generic (E := Vec d) hR hg.memLp

theorem forceBesovRegularity_descendant_partialSeminorms_bddAbove
    {d : ℕ} {Q R : TriadicCube d} {s : ℝ} {j : ℕ}
    {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q s g)
    (hR : R ∈ descendantsAtDepth Q j) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo R s N g) :=
  cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_parent_bddAbove
    s g hR hg.partialSeminorms_bddAbove

theorem forceBesovRegularity_descendant_centered_partialSeminorms_bddAbove
    {d : ℕ} {Q R : TriadicCube d} {s : ℝ} {j : ℕ}
    {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q s g)
    (hR : R ∈ descendantsAtDepth Q j) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo R s N
        (fun x => g x - cubeAverageVec R g)) := by
  rcases forceBesovRegularity_descendant_partialSeminorms_bddAbove hg hR with
    ⟨B, hB⟩
  refine ⟨B, ?_⟩
  rintro _ ⟨N, rfl⟩
  have hmem :
      ∀ k ∈ Finset.range (N + 1), ∀ S ∈ descendantsAtDepth R k,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S) := by
    intro k _ S hS
    exact forceBesovRegularity_descendant_memLp_normalizedCubeMeasure hg
      (mem_descendantsAtDepth_add hR hS)
  change cubeBesovPositiveVectorPartialSeminormTwo R s N
      (fun x => g x - cubeAverageVec R g) ≤ B
  rw [cubeBesovPositiveVectorPartialSeminormTwo_sub_const R s N g
    (cubeAverageVec R g) hmem]
  exact hB ⟨N, rfl⟩

theorem forceBesovRegularity_descendant
    {d : ℕ} {Q R : TriadicCube d} {s : ℝ} {j : ℕ}
    {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q s g)
    (hR : R ∈ descendantsAtDepth Q j) :
    ForceBesovRegularity R s g :=
  ⟨forceBesovRegularity_descendant_memLp_normalizedCubeMeasure hg hR,
    forceBesovRegularity_descendant_partialSeminorms_bddAbove hg hR⟩

theorem forceBesovRegularity_negativeBesovPartialSeminormTwo_bddAbove
    {d : ℕ} {Q : TriadicCube d} {s t : ℝ} {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q t g) (hs : 0 < s) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N g) :=
  cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs g hg.memLp

theorem forceBesovRegularity_descendant_negativeBesovPartialSeminormTwo_bddAbove
    {d : ℕ} {Q R : TriadicCube d} {s t : ℝ} {j : ℕ}
    {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q t g)
    (hR : R ∈ descendantsAtDepth Q j) (hs : 0 < s) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo R s N g) :=
  cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs g
    (forceBesovRegularity_descendant_memLp_normalizedCubeMeasure hg hR)

theorem constantCoeffMatrix_isEllipticFieldOn_constantCoeffField
    {d : ℕ} {U : Set (Vec d)}
    (a0 : ConstantCoeffMatrix d) (hU : MeasurableSet U) :
    IsEllipticFieldOn a0.lam a0.Lam U (constantCoeffField a0.matrix) :=
  isEllipticFieldOn_constantCoeffField hU a0.elliptic

theorem matNorm_le_dim_mul_constantCoeffMatrixNorm
    {d : ℕ} (a0 : ConstantCoeffMatrix d) :
    matNorm a0.matrix ≤ (d : ℝ) * constantCoeffMatrixNorm a0 := by
  simpa [constantCoeffMatrixNorm] using
    Ch02.matNorm_le_dim_mul_matrixNorm a0.matrix

theorem sqrt_matNorm_le_dim_mul_constantCoeffMatrixNormHalf
    {d : ℕ} [NeZero d] (a0 : ConstantCoeffMatrix d) :
    Real.sqrt (matNorm a0.matrix) ≤
      (d : ℝ) * constantCoeffMatrixNormHalf a0 := by
  have hop_nonneg : 0 ≤ Ch02.matrixNorm a0.matrix :=
    Ch02.matrixNorm_nonneg a0.matrix
  have hmat_le :
      matNorm a0.matrix ≤ (d : ℝ) * Ch02.matrixNorm a0.matrix :=
    Ch02.matNorm_le_dim_mul_matrixNorm a0.matrix
  have hsqrts :
      Real.sqrt (matNorm a0.matrix) ≤
        Real.sqrt ((d : ℝ) * Ch02.matrixNorm a0.matrix) :=
    Real.sqrt_le_sqrt hmat_le
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd_one : 1 ≤ (d : ℝ) := by
    norm_num [Nat.one_le_iff_ne_zero, NeZero.ne d]
  have hM_sq :
      constantCoeffMatrixNormHalf a0 ^ 2 = Ch02.matrixNorm a0.matrix := by
    simpa [constantCoeffMatrixNormHalf, Real.sqrt_eq_rpow] using
      Real.sq_sqrt hop_nonneg
  have hright_nonneg :
      0 ≤ (d : ℝ) * constantCoeffMatrixNormHalf a0 :=
    mul_nonneg hd_nonneg (Real.rpow_nonneg hop_nonneg _)
  have hsq :
      Real.sqrt ((d : ℝ) * Ch02.matrixNorm a0.matrix) ^ 2 ≤
        ((d : ℝ) * constantCoeffMatrixNormHalf a0) ^ 2 := by
    rw [Real.sq_sqrt (mul_nonneg hd_nonneg hop_nonneg), mul_pow, hM_sq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd_one) hop_nonneg]
  exact hsqrts.trans
    ((sq_le_sq₀ (Real.sqrt_nonneg _) hright_nonneg).mp hsq)

theorem sqrt_LambdaSq_publicCoeffField_finite_one_le_dim_mul_poincareUpperEllipticityFactor
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Real.sqrt (LambdaSq Q s (MultiscaleExponent.finite 1)
        (publicCoeffField Q a)) ≤
      (d : ℝ) *
        poincareUpperEllipticityFactor Q a s
          (Ch02.MultiscaleExponent.finite 1) := by
  have h := Ch02.old_LambdaSq_one_rpow_half_le_dim_mul_pointwiseCoeffField
    Q a hs
  simpa [publicCoeffField, LambdaSq, Ch02.LambdaSq,
    poincareUpperEllipticityFactor, Real.sqrt_eq_rpow] using h

theorem sqrt_lambdaSq_publicCoeffField_finite_one_inv_le_dim_mul_poincareLowerEllipticityFactor
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Real.sqrt ((lambdaSq Q s (MultiscaleExponent.finite 1)
        (publicCoeffField Q a))⁻¹) ≤
      (d : ℝ) *
        poincareLowerEllipticityFactor Q a s
          (Ch02.MultiscaleExponent.finite 1) := by
  have h := Ch02.old_lambdaSq_one_rpow_neg_half_le_dim_mul_pointwiseCoeffField
    Q a hs
  have hleft :
      Real.sqrt ((lambdaSq Q s (MultiscaleExponent.finite 1)
          (publicCoeffField Q a))⁻¹) =
        Real.rpow
          (lambdaSq Q s (MultiscaleExponent.finite 1)
            (publicCoeffField Q a)) (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow]
    rw [← Real.rpow_eq_pow]
    ring_nf
  calc
    Real.sqrt ((lambdaSq Q s (MultiscaleExponent.finite 1)
        (publicCoeffField Q a))⁻¹) =
        Real.rpow
          (lambdaSq Q s (MultiscaleExponent.finite 1)
            (publicCoeffField Q a)) (-1 / 2 : ℝ) := hleft
    _ ≤
        (d : ℝ) *
          poincareLowerEllipticityFactor Q a s
            (Ch02.MultiscaleExponent.finite 1) := by
          have hExp : (-1 / 2 : ℝ) = (-(1 / 2 : ℝ)) := by ring
          simpa [publicCoeffField, lambdaSq, Ch02.lambdaSq,
            poincareLowerEllipticityFactor, hExp] using h

theorem sqrt_LambdaSq_publicCoeffField_finite_two_le_dim_mul_poincareUpperEllipticityFactor
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Real.sqrt (LambdaSq Q s (MultiscaleExponent.finite 2)
        (publicCoeffField Q a)) ≤
      (d : ℝ) *
        poincareUpperEllipticityFactor Q a s
          (Ch02.MultiscaleExponent.finite 2) := by
  have h := Ch02.old_LambdaSq_two_rpow_half_le_dim_mul_pointwiseCoeffField
    Q a hs
  simpa [publicCoeffField, LambdaSq, Ch02.LambdaSq,
    poincareUpperEllipticityFactor, Real.sqrt_eq_rpow] using h

theorem sqrt_lambdaSq_publicCoeffField_finite_two_inv_le_dim_mul_poincareLowerEllipticityFactor
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Real.sqrt ((lambdaSq Q s (MultiscaleExponent.finite 2)
        (publicCoeffField Q a))⁻¹) ≤
      (d : ℝ) *
        poincareLowerEllipticityFactor Q a s
          (Ch02.MultiscaleExponent.finite 2) := by
  have h := Ch02.old_lambdaSq_two_rpow_neg_half_le_dim_mul_pointwiseCoeffField
    Q a hs
  have hleft :
      Real.sqrt ((lambdaSq Q s (MultiscaleExponent.finite 2)
          (publicCoeffField Q a))⁻¹) =
        Real.rpow
          (lambdaSq Q s (MultiscaleExponent.finite 2)
            (publicCoeffField Q a)) (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow]
    rw [← Real.rpow_eq_pow]
    ring_nf
  calc
    Real.sqrt ((lambdaSq Q s (MultiscaleExponent.finite 2)
        (publicCoeffField Q a))⁻¹) =
        Real.rpow
          (lambdaSq Q s (MultiscaleExponent.finite 2)
            (publicCoeffField Q a)) (-1 / 2 : ℝ) := hleft
    _ ≤
        (d : ℝ) *
          poincareLowerEllipticityFactor Q a s
            (Ch02.MultiscaleExponent.finite 2) := by
          have hExp : (-1 / 2 : ℝ) = (-(1 / 2 : ℝ)) := by ring
          simpa [publicCoeffField, lambdaSq, Ch02.lambdaSq,
            poincareLowerEllipticityFactor, hExp] using h

theorem lambdaSq_publicCoeffField_finite_two_inv_le_dim_mul_public_rpow_neg_one
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    (lambdaSq Q s (MultiscaleExponent.finite 2)
        (publicCoeffField Q a))⁻¹ ≤
      (d : ℝ) *
        Real.rpow (Ch02.lambdaSq Q s (Ch02.MultiscaleExponent.finite 2) a)
          (-1 : ℝ) := by
  have h := Ch02.old_lambdaSq_two_inv_le_dim_mul_pointwiseCoeffField Q a hs
  calc
    (lambdaSq Q s (MultiscaleExponent.finite 2)
        (publicCoeffField Q a))⁻¹ ≤
        (d : ℝ) * (Ch02.lambdaSq Q s (Ch02.MultiscaleExponent.finite 2) a)⁻¹ := by
          simpa [publicCoeffField, lambdaSq, Ch02.lambdaSq] using h
    _ =
        (d : ℝ) *
          Real.rpow (Ch02.lambdaSq Q s (Ch02.MultiscaleExponent.finite 2) a)
            (-1 : ℝ) := by
          congr 1
          exact (Real.rpow_neg_one _).symm

theorem blockJ_cubeSet_publicCoeffField_eq_ch02_doubledResponseJ
    {d : ℕ} [NeZero d] (a : CoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k)
    (P Q' : BlockVec d) :
    BlockJ (cubeSet R) P Q' (publicCoeffField Q a) =
      Ch02.doubledResponseJ (Ch02.cubeDomain R) (a.coeffOn R) P Q' := by
  let A : CoeffField d := publicCoeffField Q a
  let := isFiniteMeasureVolumeMeasureOnCubeSet R
  have hsubOpen : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtScale hk hR
  let aRpw : Ch02.CoeffOn (Ch02.cubeDomain R) :=
    Ch02.pointwiseCoeffOnRestrict (a.coeffOn Q) hsubOpen
  have haeeq : Ch02.CoeffOn.AEEq (a.coeffOn R) aRpw := by
    simpa [aRpw] using
      Ch02.coeffOn_descendant_aeeq_pointwiseCoeffOnRestrict (a := a) hk hR
  have hEllQ : IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam (cubeSet Q) A := by
    simpa [A] using publicCoeffField_isEllipticFieldOn_cubeSet Q a
  have hEllR : IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam (cubeSet R) A :=
    hEllQ.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtScale hk hR)
  have hvolR : (MeasureTheory.volume (cubeSet R)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos R).ne'
  have hbook_scalar_pw :=
    (Ch02.doubledResponseTheory (Ch02.cubeDomain R) aRpw).doubledResponseJ_eq_scalar
      P.1 Q'.2 P.2 Q'.1
  calc
    BlockJ (cubeSet R) P Q' (publicCoeffField Q a) =
        (1 / 2 : ℝ) * ResponseJ (cubeSet R) (P.1 - Q'.2) (Q'.1 - P.2) A +
          (1 / 2 : ℝ) * ResponseJ (cubeSet R) (Q'.2 + P.1) (Q'.1 + P.2)
            (adjointCoeffField A) := by
          simpa [A] using
            blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
              (a := A) (U := cubeSet R) (measurableSet_cubeSet R) hEllR
              hvolR (p := P.1) (pStar := Q'.2) (q := P.2) (qStar := Q'.1)
    _ = (1 / 2 : ℝ) * ResponseJ (openCubeSet R) (P.1 - Q'.2) (Q'.1 - P.2) A +
          (1 / 2 : ℝ) * ResponseJ (openCubeSet R) (Q'.2 + P.1) (Q'.1 + P.2)
            (adjointCoeffField A) := by
          rw [ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube R,
            ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube R]
    _ = (1 / 2 : ℝ) * Ch02.responseJ (Ch02.cubeDomain R) aRpw
            (P.1 - Q'.2) (Q'.1 - P.2) +
          (1 / 2 : ℝ) * Ch02.responseJ (Ch02.cubeDomain R) aRpw.transpose
            (Q'.2 + P.1) (Q'.1 + P.2) := by
          rw [Internal.Ch02.book_responseJ_eq_ResponseJ,
            Internal.Ch02.book_responseJ_eq_ResponseJ]
          rfl
    _ = Ch02.doubledResponseJ (Ch02.cubeDomain R) aRpw P Q' := by
          exact hbook_scalar_pw.symm
    _ = Ch02.doubledResponseJ (Ch02.cubeDomain R) (a.coeffOn R) P Q' := by
          rw [Ch02.doubledResponseJ_eq_ofAEEq haeeq P Q']

theorem normalizedBlockResponseValueSet_publicCoeffField_eq_ch02
    {d : ℕ} [NeZero d] (a : CoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) (a0 : Mat d) :
    normalizedBlockResponseValueSet R (publicCoeffField Q a) a0 =
      Ch02.normalizedBlockResponseValueSet R a a0 := by
  ext m
  constructor
  · rintro ⟨e, he, hm⟩
    refine ⟨e, ?_, ?_⟩
    · simpa [Ch02.fullBlockVecNormSq, Homogenization.fullBlockVecNormSq] using he
    · have hbridge :=
        blockJ_cubeSet_publicCoeffField_eq_ch02_doubledResponseJ
          (a := a) (Q := Q) (R := R) (k := k) hk hR
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))
      simpa [Ch02.constantFullBlockMatrixInvSqrt, constantFullBlockMatrixInvSqrt,
        Ch02.constantFullBlockMatrixSqrt, constantFullBlockMatrixSqrt,
        Ch02.constantFullBlockMatrix, constantFullBlockMatrix,
        Ch02.constantBlockMatrix, blockMatrixOfCoeff] using hm.trans hbridge
  · rintro ⟨e, he, hm⟩
    refine ⟨e, ?_, ?_⟩
    · simpa [Ch02.fullBlockVecNormSq, Homogenization.fullBlockVecNormSq] using he
    · have hbridge :=
        blockJ_cubeSet_publicCoeffField_eq_ch02_doubledResponseJ
          (a := a) (Q := Q) (R := R) (k := k) hk hR
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))
      simpa [Ch02.constantFullBlockMatrixInvSqrt, constantFullBlockMatrixInvSqrt,
        Ch02.constantFullBlockMatrixSqrt, constantFullBlockMatrixSqrt,
        Ch02.constantFullBlockMatrix, constantFullBlockMatrix,
        Ch02.constantBlockMatrix, blockMatrixOfCoeff] using hm.trans hbridge.symm

theorem normalizedBlockResponseMax_publicCoeffField_eq_ch02
    {d : ℕ} [NeZero d] (a : CoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) (a0 : Mat d) :
    normalizedBlockResponseMax R (publicCoeffField Q a) a0 =
      Ch02.normalizedBlockResponseMax R a a0 := by
  unfold normalizedBlockResponseMax Ch02.normalizedBlockResponseMax
  rw [normalizedBlockResponseValueSet_publicCoeffField_eq_ch02
    (a := a) (Q := Q) (R := R) (k := k) hk hR a0]

theorem maxDescendantNormalizedBlockResponseAtScale_publicCoeffField_eq_ch02
    {d : ℕ} [NeZero d] (a : CoeffFamily d) (Q : TriadicCube d)
    {k : ℤ} (hk : k ≤ Q.scale) (a0 : Mat d) :
    maxDescendantNormalizedBlockResponseAtScale Q k (publicCoeffField Q a) a0 =
      Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale
    Ch02.maxDescendantNormalizedBlockResponseAtScale
  rw [Ch02.finsetSupReal_eq_finsetSsup]
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨R, hR, rfl⟩
    exact ⟨R, hR,
      (normalizedBlockResponseMax_publicCoeffField_eq_ch02
        (a := a) (Q := Q) (R := R) (k := k) hk hR a0).symm⟩
  · rintro ⟨R, hR, rfl⟩
    exact ⟨R, hR,
      normalizedBlockResponseMax_publicCoeffField_eq_ch02
        (a := a) (Q := Q) (R := R) (k := k) hk hR a0⟩

theorem scaleResponseAtScale_publicCoeffField_infinity_eq_ch02
    {d : ℕ} [NeZero d] (a : CoeffFamily d) (Q : TriadicCube d)
    {k : ℤ} (hk : k ≤ Q.scale) (a0 : Mat d) :
    scaleResponseAtScale Q k MultiscaleExponent.infinity
        (publicCoeffField Q a) a0 =
      Ch02.scaleResponseAtScale Q k Ch02.MultiscaleExponent.infinity a a0 := by
  rw [scaleResponseAtScale_infinity_eq, Ch02.scaleResponseAtScale_infinity_eq,
    maxDescendantNormalizedBlockResponseAtScale_publicCoeffField_eq_ch02
      (a := a) Q hk a0]

theorem maxDescendantNormalizedBlockResponseAtScale_parent_publicCoeffField_descendant_eq_ch02
    {d : ℕ} [NeZero d] (a : CoeffFamily d)
    {Q R : TriadicCube d} {k l : ℤ}
    (hR : R ∈ descendantsAtScale Q k) (hl : l ≤ R.scale) (a0 : Mat d) :
    maxDescendantNormalizedBlockResponseAtScale R l (publicCoeffField Q a) a0 =
      Ch02.maxDescendantNormalizedBlockResponseAtScale R l a a0 := by
  have hk : k ≤ Q.scale := Homogenization.descendant_scale_le_of_mem_descendantsAtScale hR
  have hRscale : R.scale = k := Homogenization.descendant_scale_eq_of_mem_descendantsAtScale hR
  have hlQ : l ≤ Q.scale := by
    exact le_trans (by simpa [hRscale] using hl) hk
  unfold maxDescendantNormalizedBlockResponseAtScale
    Ch02.maxDescendantNormalizedBlockResponseAtScale
  rw [Ch02.finsetSupReal_eq_finsetSsup]
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S, hS,
      (normalizedBlockResponseMax_publicCoeffField_eq_ch02
        (a := a) (Q := Q) (R := S) (k := l) hlQ
        (Homogenization.mem_descendantsAtScale_trans hR hS) a0).symm⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S, hS,
      normalizedBlockResponseMax_publicCoeffField_eq_ch02
        (a := a) (Q := Q) (R := S) (k := l) hlQ
        (Homogenization.mem_descendantsAtScale_trans hR hS) a0⟩

theorem scaleResponseAtScale_parent_publicCoeffField_descendant_infinity_eq_ch02
    {d : ℕ} [NeZero d] (a : CoeffFamily d)
    {Q R : TriadicCube d} {k l : ℤ}
    (hR : R ∈ descendantsAtScale Q k) (hl : l ≤ R.scale) (a0 : Mat d) :
    scaleResponseAtScale R l MultiscaleExponent.infinity
        (publicCoeffField Q a) a0 =
      Ch02.scaleResponseAtScale R l Ch02.MultiscaleExponent.infinity a a0 := by
  rw [scaleResponseAtScale_infinity_eq, Ch02.scaleResponseAtScale_infinity_eq,
    maxDescendantNormalizedBlockResponseAtScale_parent_publicCoeffField_descendant_eq_ch02
      (a := a) hR hl a0]

theorem homogenizationErrorOnCube_parent_publicCoeffField_descendant_infinity_one_eq_ch02
    {d : ℕ} [NeZero d] (a : CoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ}
    (hR : R ∈ descendantsAtScale Q k) (s : ℝ) (a0 : Mat d) :
    HomogenizationErrorOnCube R s MultiscaleExponent.infinity
        (MultiscaleExponent.finite 1) (publicCoeffField Q a) a0 =
      Ch02.HomogenizationErrorOnCube R s Ch02.MultiscaleExponent.infinity
        (Ch02.MultiscaleExponent.finite 1) a a0 := by
  rw [homogenizationErrorOnCube_infinity_one_eq_tsum,
    Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum]
  apply tsum_congr
  intro n
  have hl : R.scale - (n : ℤ) ≤ R.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  rw [← Ch02.geometricWeight_eq_old]
  rw [scaleResponseAtScale_parent_publicCoeffField_descendant_infinity_eq_ch02
    (a := a) hR hl a0]

theorem homogenizationErrorOnCube_parent_publicCoeffField_descendant_infinity_one_terms_summable
    {d : ℕ} [NeZero d] (a : CoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ}
    (hR : R ∈ descendantsAtScale Q k) (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    Summable fun n : ℕ =>
      geometricWeight s 1 n *
        scaleResponseAtScale R (R.scale - (n : ℤ))
          MultiscaleExponent.infinity (publicCoeffField Q a) a0 := by
  have hbook := Ch02.summable_homogenizationErrorOnCube_infinity_one_terms
    R a a0 hs
  refine hbook.congr ?_
  intro n
  have hl : R.scale - (n : ℤ) ≤ R.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  rw [Ch02.geometricWeight_eq_old]
  rw [scaleResponseAtScale_parent_publicCoeffField_descendant_infinity_eq_ch02
    (a := a) hR hl a0]

theorem homogenizationErrorOnCube_publicCoeffField_infinity_one_eq_ch02
    {d : ℕ} [NeZero d] (a : CoeffFamily d) (Q : TriadicCube d)
    (s : ℝ) (a0 : Mat d) :
    HomogenizationErrorOnCube Q s MultiscaleExponent.infinity
        (MultiscaleExponent.finite 1) (publicCoeffField Q a) a0 =
      Ch02.HomogenizationErrorOnCube Q s Ch02.MultiscaleExponent.infinity
        (Ch02.MultiscaleExponent.finite 1) a a0 := by
  rw [homogenizationErrorOnCube_infinity_one_eq_tsum,
    Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum]
  apply tsum_congr
  intro n
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  rw [← Ch02.geometricWeight_eq_old]
  rw [scaleResponseAtScale_publicCoeffField_infinity_eq_ch02
    (a := a) Q hk a0]

theorem homogenizationErrorOnCube_publicCoeffField_infinity_one_terms_summable
    {d : ℕ} [NeZero d] (a : CoeffFamily d) (Q : TriadicCube d)
    (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    Summable fun n : ℕ =>
      geometricWeight s 1 n *
        scaleResponseAtScale Q (Q.scale - (n : ℤ))
          MultiscaleExponent.infinity (publicCoeffField Q a) a0 := by
  have hbook := Ch02.summable_homogenizationErrorOnCube_infinity_one_terms
    Q a a0 hs
  refine hbook.congr ?_
  intro n
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  rw [Ch02.geometricWeight_eq_old]
  rw [scaleResponseAtScale_publicCoeffField_infinity_eq_ch02
    (a := a) Q hk a0]


end

end Ch03
end Book
end Homogenization
