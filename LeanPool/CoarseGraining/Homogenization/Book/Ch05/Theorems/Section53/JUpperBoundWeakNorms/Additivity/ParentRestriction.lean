/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.Densities

/-! # Parent Restriction -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# AdditivityParentRestriction

Parent-restricted response identities and the partition defect.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

noncomputable def castAHarmonicCoeff {d : ℕ} {U : Set (Vec d)}
    {a b : CoeffField d} (h : a = b) (u : AHarmonicFunction a U) :
    AHarmonicFunction b U :=
  h ▸ u

@[simp] theorem castAHarmonicCoeff_grad {d : ℕ} {U : Set (Vec d)}
    {a b : CoeffField d} (h : a = b) (u : AHarmonicFunction a U) :
    (castAHarmonicCoeff h u).toH1.grad = u.toH1.grad := by
  subst b
  rfl

/--
The parent canonical response solution, restricted to a descendant child cube
and viewed with the child coefficient representative.  For the Chapter 4
dependent family the parent and child coefficient representatives are the same
sampled coefficient field, so this needs no representative-identification
layer.
-/
noncomputable def parentResponseSolutionOnDependentFamilyRestrictedToCube
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    Ch02.Solution (Ch02.cubeDomain R)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
  have hCoeff : (F.coeffOn Q).toCoeffField = (F.coeffOn R).toCoeffField := by
    simp [F]
  let uParent : AHarmonicFunction (F.coeffOn R).toCoeffField (openCubeSet Q) :=
    castAHarmonicCoeff hCoeff
      (canonicalMaximizerSolutionOnCube Q (F.coeffOn Q) p q)
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hGradR : MemVectorL2 (openCubeSet R) uParent.toH1.grad := by
    simpa using
      (uParent.toH1.restrict (isOpen_openCubeSet R) hsub).grad_memVectorL2
  have hEllOpen :
      IsAEEllipticFieldOn (F.coeffOn R).lam (F.coeffOn R).Lam
        (openCubeSet R) (F.coeffOn R).toCoeffField := by
    simpa [Ch02.cubeDomain_coe] using
      (ch02_coeffOn_isAEEllipticFieldOn (F.coeffOn R))
  have hFluxR :
      MemVectorL2 (openCubeSet R)
        (fun x => matVecMul ((F.coeffOn R).toCoeffField x) (uParent.toH1.grad x)) :=
    hEllOpen.memVectorL2_matVecMul hGradR
  exact uParent.restrictOfMemVectorL2
    (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hsub hFluxR

/-- The restricted parent solution has the parent canonical gradient. -/
theorem parentResponseSolutionOnDependentFamilyRestrictedToCube_grad
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    (parentResponseSolutionOnDependentFamilyRestrictedToCube a ha Q hR p q).toH1.grad =
      canonicalMaximizerGradientOnCube Q
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
        p q := by
  funext x
  rfl

/--
One-child diff-energy identity with the restricted parent solution supplied by
the Chapter 4 dependent coefficient family.
-/
theorem cubeAverage_additivityDiffHalfEnergyDensityOnDependentFamilyOnCube_eq_responseJOnCube_sub_parentRestrictedResponseValue
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q) =
      Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q -
        Ch02.responseValue (Ch02.cubeDomain R) (F.coeffOn R) p q
          (parentResponseSolutionOnDependentFamilyRestrictedToCube a ha Q hR p q) := by
  intro F
  exact
    cubeAverage_additivityDiffHalfEnergyDensityOnFamilyOnCube_eq_responseJOnCube_sub_responseValue_of_grad_eq
      (a := F) (Q := Q) (R := R) (p := p) (q := q)
      (w := parentResponseSolutionOnDependentFamilyRestrictedToCube a ha Q hR p q)
      (by
        simpa [F] using
          parentResponseSolutionOnDependentFamilyRestrictedToCube_grad a ha Q hR p q)

/--
The response value of the restricted parent solution on one child cube is the
child cube average of the parent response integrand.
-/
theorem parentRestrictedResponseValueOnDependentFamily_eq_cubeAverage_parentResponseIntegrand
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    Ch02.responseValue (Ch02.cubeDomain R) (F.coeffOn R) p q
        (parentResponseSolutionOnDependentFamilyRestrictedToCube a ha Q hR p q) =
      cubeAverage R
        (Ch02.responseIntegrand (Ch02.cubeDomain Q) (F.coeffOn Q) p q
          (canonicalMaximizerSolutionOnCube Q (F.coeffOn Q) p q)) := by
  intro F
  unfold Ch02.responseValue
  rw [ch02_average_cubeDomain_eq_cubeAverage]
  congr 1

/-- The descendant-indexed restricted-parent response value. -/
noncomputable def parentRestrictedResponseValueOnDependentFamilyAtDepth
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    TriadicCube d → ℝ :=
  fun R =>
    if hR : R ∈ descendantsAtDepth Q j then
      let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
      Ch02.responseValue (Ch02.cubeDomain R) (F.coeffOn R) p q
        (parentResponseSolutionOnDependentFamilyRestrictedToCube a ha Q hR p q)
    else
      0

/--
The descendant average of restricted-parent response values is the parent
response.
-/
theorem descendantsAverage_parentRestrictedResponseValueOnDependentFamilyAtDepth_eq_responseJOnCube
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    descendantsAverage Q j
        (parentRestrictedResponseValueOnDependentFamilyAtDepth a ha Q j p q) =
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q := by
  intro F
  let G : Vec d → ℝ :=
    Ch02.responseIntegrand (Ch02.cubeDomain Q) (F.coeffOn Q) p q
      (canonicalMaximizerSolutionOnCube Q (F.coeffOn Q) p q)
  have hG_int_open :
      IntegrableOn G (openCubeSet Q) volume := by
    simpa [G, Ch02.cubeDomain_coe] using
      ch02_responseIntegrand_integrableOn
        (Ch02.cubeDomain Q) (F.coeffOn Q) p q
        (canonicalMaximizerSolutionOnCube Q (F.coeffOn Q) p q)
  have hG_int : IntegrableOn G (cubeSet Q) volume := by
    rw [integrableOn_cubeSet_iff_integrableOn_openCubeSet]
    exact hG_int_open
  have hcongr :
      descendantsAverage Q j
          (parentRestrictedResponseValueOnDependentFamilyAtDepth a ha Q j p q) =
        descendantsAverage Q j (fun R => cubeAverage R G) := by
    apply descendantsAverage_congr_of_eq_on_descendants
    intro R hR
    simp [parentRestrictedResponseValueOnDependentFamilyAtDepth, hR, F, G,
      parentRestrictedResponseValueOnDependentFamily_eq_cubeAverage_parentResponseIntegrand]
  calc
    descendantsAverage Q j
        (parentRestrictedResponseValueOnDependentFamilyAtDepth a ha Q j p q)
        = descendantsAverage Q j (fun R => cubeAverage R G) := hcongr
    _ = cubeAverage Q G := by
          rw [← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
            (Q := Q) (j := j) (f := G) hG_int]
    _ = Ch02.responseValue (Ch02.cubeDomain Q) (F.coeffOn Q) p q
          (canonicalMaximizerSolutionOnCube Q (F.coeffOn Q) p q) := by
          rw [Ch02.responseValue, ch02_average_cubeDomain_eq_cubeAverage]
    _ = Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q := by
          symm
          exact
            Ch02.responseJ_eq_responseValue_of_isResponseMaximizer
              (by
                simpa [canonicalMaximizerSolutionOnCube] using
                  Ch02.canonicalMaximizer_isMaximizer
                    (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) (F.coeffOn Q))
                    p q)

/--
The descendant average of the local difference half-energy is exactly the
response partition defect for the Chapter 4 dependent coefficient family.
-/
theorem descendantsAverage_additivityDiffHalfEnergyOnDependentFamily_eq_responseJPartitionDefectOnFamilyAtDepth
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    descendantsAverage Q j
        (fun R =>
          cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q)) =
      responseJPartitionDefectOnFamilyAtDepth F Q j p q := by
  intro F
  let D : TriadicCube d → ℝ := fun R =>
    cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q)
  let Child : TriadicCube d → ℝ := fun R =>
    Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q
  let Parent : TriadicCube d → ℝ :=
    parentRestrictedResponseValueOnDependentFamilyAtDepth a ha Q j p q
  have hlocal :
      descendantsAverage Q j D =
        descendantsAverage Q j (fun R => Child R - Parent R) := by
    apply descendantsAverage_congr_of_eq_on_descendants
    intro R hR
    have hdiff :=
      cubeAverage_additivityDiffHalfEnergyDensityOnDependentFamilyOnCube_eq_responseJOnCube_sub_parentRestrictedResponseValue
        (a := a) (ha := ha) (Q := Q) (R := R) hR p q
    have hParent :
        Parent R =
          Ch02.responseValue (Ch02.cubeDomain R) (F.coeffOn R) p q
            (parentResponseSolutionOnDependentFamilyRestrictedToCube a ha Q hR p q) := by
      simp [Parent, parentRestrictedResponseValueOnDependentFamilyAtDepth, hR, F]
    calc
      D R =
          Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q -
            Ch02.responseValue (Ch02.cubeDomain R) (F.coeffOn R) p q
              (parentResponseSolutionOnDependentFamilyRestrictedToCube a ha Q hR p q) := by
            simpa [D, F] using hdiff
      _ = Child R - Parent R := by
            rw [hParent]
  have hlinear :
      descendantsAverage Q j (fun R => Child R - Parent R) =
        descendantsAverage Q j Child - descendantsAverage Q j Parent := by
    calc
      descendantsAverage Q j (fun R => Child R - Parent R)
          =
            descendantsAverage Q j (fun R => Child R + (-1 : ℝ) * Parent R) := by
              congr 1
              funext R
              ring
      _ =
          descendantsAverage Q j Child +
            descendantsAverage Q j (fun R => (-1 : ℝ) * Parent R) := by
            rw [descendantsAverage_add]
      _ =
          descendantsAverage Q j Child + (-1 : ℝ) * descendantsAverage Q j Parent := by
            rw [descendantsAverage_smul]
      _ =
          descendantsAverage Q j Child - descendantsAverage Q j Parent := by
            ring
  calc
    descendantsAverage Q j D
        = descendantsAverage Q j (fun R => Child R - Parent R) := hlocal
    _ = descendantsAverage Q j Child - descendantsAverage Q j Parent := hlinear
    _ =
        childResponseJAverageOnFamilyAtDepth F Q j p q -
          Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q := by
          rw [descendantsAverage_parentRestrictedResponseValueOnDependentFamilyAtDepth_eq_responseJOnCube]
          rfl
    _ = responseJPartitionDefectOnFamilyAtDepth F Q j p q := by
          rfl

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
