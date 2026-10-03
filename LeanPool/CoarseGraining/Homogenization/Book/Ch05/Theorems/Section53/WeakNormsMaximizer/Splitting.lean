/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.RawIdentities
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.Bounds

/-! # Splitting -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace WeakNormsMaximizer

/-!
# Splitting for the weak-norm maximizer lemma

Finite-depth high/low Besov splits for the raw scalar-response maximizer
fields.  The high-depth terms are still deterministic analytic terms; later
files bound them by the energy defect and multiscale ellipticity factors.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Finite-depth gradient split for the second Section 5.3 lemma.  Depths
`j < L` are split into the child maximizer average and the parent-child
mismatch.  Depths `L ≤ j` are left as the raw parent-gradient low-scale term
plus the affine `p0` tail. -/
theorem canonicalScalarResponseGradientWeakNormPartialCubeSet_le_highLowSplit
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (s : ℝ) (N L : ℕ) (hs : 0 < s)
    (p q p0 : Vec d) :
    Ch04.canonicalScalarResponseGradientWeakNormPartialCubeSet Q s N p q p0 a.toFun ≤
      (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
          2 *
            (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R =>
                    vecNormSq
                      (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R =>
                    vecNormSq
                      (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
                        Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt (descendantsAverage Q j fun _R => vecNormSq (0 : Vec d)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.sqrt (descendantsAverage Q j fun _R => vecNormSq (0 : Vec d)))) +
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ j < L),
              cubeBesovNegativeVectorDepthSeminorm Q s
                (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q
                  ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
                  p q) j) +
            (Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
                (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
              Real.sqrt (vecNormSq (-p0))) := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  let grad := JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q aQ p q
  let gradDefect :=
    JUpperBoundWeakNorms.canonicalMaximizerGradientDefectOnCube Q aQ p q p0
  have hraw :
      cubeBesovNegativeVectorPartialSeminorm Q s N gradDefect ≤
        (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
            2 *
              (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                  Real.sqrt
                    (descendantsAverage Q j fun R =>
                      vecNormSq
                        (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0)) +
                Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                  Real.sqrt
                    (descendantsAverage Q j fun R =>
                      vecNormSq
                        (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
                          Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun)) +
                Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                  Real.sqrt (descendantsAverage Q j fun _R => vecNormSq (0 : Vec d)) +
                Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                  Real.sqrt (descendantsAverage Q j fun _R => vecNormSq (0 : Vec d)))) +
          2 *
            ((∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ j < L),
                cubeBesovNegativeVectorDepthSeminorm Q s grad j) +
              (Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
                  (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
                Real.sqrt (vecNormSq (-p0))) := by
    refine
      cubeBesovNegativeVectorPartialSeminorm_le_cubeTerms_below_cutoff_add_low_self_add_geometric_const
        Q s N L gradDefect grad (-p0)
        (fun _j R =>
          Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0)
        (fun _j R =>
          Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
            Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun)
        (fun _j _R => (0 : Vec d)) (fun _j _R => (0 : Vec d))
        hs ?_ ?_
    · intro j hj hjL R hR
      have hparent :
          cubeAverageVec R gradDefect =
            Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun - p0 := by
        simpa [F, aQ, gradDefect] using
          JUpperBoundWeakNorms.cubeAverageVec_canonicalMaximizerGradientDefectOnDependentFamily_eq_ch04
            a ha hR p q p0
      rw [hparent]
      ext i
      simp [sub_eq_add_neg]
      ring
    · intro j hj hjL R hR
      have hgrad :
          MemLp grad (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
        simpa [F, aQ, grad] using
          JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube_memLp_descendant
            Q R aQ hR p q
      simpa [gradDefect, grad, add_comm, sub_eq_add_neg] using!
        cubeAverageVec_sub_const R grad p0 hgrad
  rw [← JUpperBoundWeakNorms.cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerGradientDefectOnDependentFamily_eq_ch04
    a ha Q s N p q p0]
  exact hraw

/-- Finite-depth flux split for the second Section 5.3 lemma.  This is the
flux analogue of
`canonicalScalarResponseGradientWeakNormPartialCubeSet_le_highLowSplit`. -/
theorem canonicalScalarResponseFluxWeakNormPartialCubeSet_le_highLowSplit
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (t : ℝ) (N L : ℕ) (ht : 0 < t)
    (p q q0 : Vec d) :
    Ch04.canonicalScalarResponseFluxWeakNormPartialCubeSet Q t N p q q0 a.toFun ≤
      (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
          2 *
            (Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R =>
                    vecNormSq
                      (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0)) +
              Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
                Real.sqrt
                  (descendantsAverage Q j fun R =>
                    vecNormSq
                      (Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
                        Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun)) +
              Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
                Real.sqrt (descendantsAverage Q j fun _R => vecNormSq (0 : Vec d)) +
              Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
                Real.sqrt (descendantsAverage Q j fun _R => vecNormSq (0 : Vec d)))) +
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ j < L),
              cubeBesovNegativeVectorDepthSeminorm Q t
                (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q
                  ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
                  p q) j) +
            (Real.rpow (3 : ℝ) (-t * (L : ℝ)) *
                (1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
              Real.sqrt (vecNormSq (-q0))) := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  let flux := JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q aQ p q
  let fluxDefect :=
    JUpperBoundWeakNorms.canonicalMaximizerFluxDefectOnCube Q aQ p q q0
  have hraw :
      cubeBesovNegativeVectorPartialSeminorm Q t N fluxDefect ≤
        (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
            2 *
              (Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
                  Real.sqrt
                    (descendantsAverage Q j fun R =>
                      vecNormSq
                        (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0)) +
                Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
                  Real.sqrt
                    (descendantsAverage Q j fun R =>
                      vecNormSq
                        (Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
                          Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun)) +
                Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
                  Real.sqrt (descendantsAverage Q j fun _R => vecNormSq (0 : Vec d)) +
                Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
                  Real.sqrt (descendantsAverage Q j fun _R => vecNormSq (0 : Vec d)))) +
          2 *
            ((∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ j < L),
                cubeBesovNegativeVectorDepthSeminorm Q t flux j) +
              (Real.rpow (3 : ℝ) (-t * (L : ℝ)) *
                  (1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
                Real.sqrt (vecNormSq (-q0))) := by
    refine
      cubeBesovNegativeVectorPartialSeminorm_le_cubeTerms_below_cutoff_add_low_self_add_geometric_const
        Q t N L fluxDefect flux (-q0)
        (fun _j R =>
          Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0)
        (fun _j R =>
          Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
            Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun)
        (fun _j _R => (0 : Vec d)) (fun _j _R => (0 : Vec d))
        ht ?_ ?_
    · intro j hj hjL R hR
      have hparent :
          cubeAverageVec R fluxDefect =
            Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun - q0 := by
        simpa [F, aQ, fluxDefect] using
          JUpperBoundWeakNorms.cubeAverageVec_canonicalMaximizerFluxDefectOnDependentFamily_eq_ch04
            a ha hR p q q0
      rw [hparent]
      ext i
      simp [sub_eq_add_neg]
      ring
    · intro j hj hjL R hR
      have hflux :
          MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
        simpa [F, aQ, flux] using
          JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube_memLp_descendant
            Q R aQ hR p q
      simpa [fluxDefect, flux, add_comm, sub_eq_add_neg] using!
        cubeAverageVec_sub_const R flux q0 hflux
  rw [← JUpperBoundWeakNorms.cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_eq_ch04
    a ha Q t N p q q0]
  exact hraw

end

end WeakNormsMaximizer
end Section53
end Ch05
end Book
end Homogenization
