/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CoarseObservables

/-! # Canonical Averages -/

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# Canonical averaged response observables

This file owns the Chapter 4 measurable representatives of the whole-cube
averaged gradient and flux of the canonical response maximizer.

The definitions are finite coarse-block formulas.  Chapter 2 proves that these
formulas are the corresponding averages of the public canonical maximizer.  We
do not expose measurability of the full chosen maximizer field here.
-/

/-- Ch4 measurable representative of the whole-cube canonical averaged
gradient on a deterministic triadic cube.

This is the lower-row coarse-block formula from Chapter 2. -/
noncomputable def canonicalAverageGradientCubeSet {d : ℕ}
    (Q : TriadicCube d) (p q : Vec d) (a : RegCoeffField d) : Vec d :=
  -p + matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight q -
    matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft p

/-- Ch4 measurable representative of the whole-cube canonical averaged flux on
a deterministic triadic cube.

This is the upper-row coarse-block formula from Chapter 2. -/
noncomputable def canonicalAverageFluxCubeSet {d : ℕ}
    (Q : TriadicCube d) (p q : Vec d) (a : RegCoeffField d) : Vec d :=
  q + matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperRight q -
    matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft p

private theorem aemeasurable_matVecMul_const
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {M : α → Mat d} (hM : AEMeasurable M μ) (x : Vec d) :
    AEMeasurable (fun a : α => matVecMul (M a) x) μ := by
  rw [aemeasurable_pi_iff]
  intro i
  have hM_entry : ∀ j : Fin d, AEMeasurable (fun a : α => M a i j) μ := by
    intro j
    exact (aemeasurable_pi_iff.mp ((aemeasurable_pi_iff.mp hM) i)) j
  simpa [matVecMul] using
    (Finset.univ.aemeasurable_fun_sum
      (μ := μ) (f := fun j a => M a i j * x j)
      (fun j _hj => (hM_entry j).mul aemeasurable_const))

namespace RestrictionLawCarrier

/-- The whole-cube canonical averaged gradient is a.e.-measurable under the
single Chapter 4 law carrier. -/
theorem aemeasurable_canonicalAverageGradientCubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    AEMeasurable (canonicalAverageGradientCubeSet Q p q) P := by
  have hLowerRight :
      AEMeasurable
        (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight) P :=
    hP.aemeasurable_coarseSigmaStarInv_cubeSet Q
  have hLowerLeft :
      AEMeasurable
        (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft) P :=
    hP.aemeasurable_coarseBlockMatrix_lowerLeft_cubeSet Q
  have hRight := aemeasurable_matVecMul_const hLowerRight q
  have hLeft := aemeasurable_matVecMul_const hLowerLeft p
  simpa [canonicalAverageGradientCubeSet] using!
    ((aemeasurable_const.add hRight).sub hLeft)

/-- The whole-cube canonical averaged flux is a.e.-measurable under the single
Chapter 4 law carrier. -/
theorem aemeasurable_canonicalAverageFluxCubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    AEMeasurable (canonicalAverageFluxCubeSet Q p q) P := by
  have hUpperRight :
      AEMeasurable
        (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet Q) a.toFun).upperRight) P :=
    hP.aemeasurable_coarseBlockMatrix_upperRight_cubeSet Q
  have hUpperLeft :
      AEMeasurable
        (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft) P :=
    hP.aemeasurable_coarseB_cubeSet Q
  have hRight := aemeasurable_matVecMul_const hUpperRight q
  have hLeft := aemeasurable_matVecMul_const hUpperLeft p
  simpa [canonicalAverageFluxCubeSet] using!
    ((aemeasurable_const.add hRight).sub hLeft)

/-- Finite descendant averages of canonical averaged-gradient components are
a.e.-measurable. -/
theorem aemeasurable_descendantsAverage_canonicalAverageGradientCubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        fun i : Fin d =>
          descendantsAverage Q j
            (fun R => canonicalAverageGradientCubeSet R p q a i)) P := by
  rw [aemeasurable_pi_iff]
  intro i
  exact
    aemeasurable_descendantsAverage
      (P := P) (Q := Q) (j := j)
      (F := fun R a => canonicalAverageGradientCubeSet R p q a i)
      (fun R _hR =>
        (aemeasurable_pi_iff.mp
          (hP.aemeasurable_canonicalAverageGradientCubeSet R p q)) i)

/-- Finite descendant averages of canonical averaged-flux components are
a.e.-measurable. -/
theorem aemeasurable_descendantsAverage_canonicalAverageFluxCubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        fun i : Fin d =>
          descendantsAverage Q j
            (fun R => canonicalAverageFluxCubeSet R p q a i)) P := by
  rw [aemeasurable_pi_iff]
  intro i
  exact
    aemeasurable_descendantsAverage
      (P := P) (Q := Q) (j := j)
      (F := fun R a => canonicalAverageFluxCubeSet R p q a i)
      (fun R _hR =>
        (aemeasurable_pi_iff.mp
          (hP.aemeasurable_canonicalAverageFluxCubeSet R p q)) i)

end RestrictionLawCarrier

end Ch04
end Book
end Homogenization
