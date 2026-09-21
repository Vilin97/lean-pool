/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Averages

/-! # Canonical Fields -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# CanonicalFields

Canonical scalar maximizer fields and Ch4 extraction identities.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- A Chapter 2 coefficient object is a spatially a.e. elliptic field on its
public domain. -/
theorem ch02_coeffOn_isAEEllipticFieldOn {d : ℕ} {U : Ch02.Domain d}
    (a : Ch02.CoeffOn U) :
    IsAEEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField :=
  ⟨U.measurableSet, a.aeStronglyMeasurable, a.aeElliptic⟩

/-- Private raw Chapter 2 canonical maximizer on a cube.  This is a local
Section 5.3 adapter for deterministic estimates; the measurable selected
observables remain the Ch4 Hilbert-field definitions. -/
noncomputable def canonicalMaximizerSolutionOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q : Vec d) :
    Ch02.Solution (Ch02.cubeDomain Q) a :=
  (Ch02.canonicalMaximizer
    (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) a) p q).toSolution

/-- The affine comparison function `ell_p0(x) = p0 dot x`, used only inside
the private product-term reduction. -/
noncomputable def linearPotential {d : ℕ} (p0 : Vec d) : Vec d → ℝ :=
  fun x => vecDot p0 x

/-- Continuous-linear version of `linearPotential`, used to compute its
Fréchet derivative without exposing another public definition. -/
noncomputable def linearPotentialCLM {d : ℕ} (p0 : Vec d) :
    Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, (p0 i) • (ContinuousLinearMap.proj (R := ℝ) i)

theorem linearPotential_eq_linearPotentialCLM {d : ℕ}
    (p0 : Vec d) :
    linearPotential p0 = fun x => linearPotentialCLM p0 x := by
  funext x
  simp [linearPotential, linearPotentialCLM, vecDot]

theorem linearPotentialCLM_apply_basisVec {d : ℕ}
    (p0 : Vec d) (i : Fin d) :
    linearPotentialCLM p0 (basisVec i) = p0 i := by
  rw [linearPotentialCLM]
  simp only [_root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp [basisVec]
  · intro j _hj hji
    simp [basisVec, hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem fderiv_linearPotential_apply_basisVec {d : ℕ}
    (p0 x : Vec d) (i : Fin d) :
    (fderiv ℝ (linearPotential p0) x) (basisVec i) = p0 i := by
  rw [linearPotential_eq_linearPotentialCLM p0]
  have hfd :
      fderiv ℝ (fun x => linearPotentialCLM p0 x) x =
        linearPotentialCLM p0 := by
    exact ContinuousLinearMap.fderiv (linearPotentialCLM p0)
  rw [hfd]
  exact linearPotentialCLM_apply_basisVec p0 i

/-- `ell_p0` as an `H¹` function on the parent open cube. -/
noncomputable def linearPotentialH1OnCube {d : ℕ}
    (Q : TriadicCube d) (p0 : Vec d) :
    H1Function ((Ch02.cubeDomain Q : Ch02.Domain d) : Set (Vec d)) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (U := ((Ch02.cubeDomain Q : Ch02.Domain d) : Set (Vec d)))
    (f := linearPotential p0) (Ch02.cubeDomain Q).isDomain (by
      unfold linearPotential vecDot
      fun_prop)

@[simp] theorem linearPotentialH1OnCube_toFun {d : ℕ}
    (Q : TriadicCube d) (p0 : Vec d) :
    (linearPotentialH1OnCube Q p0).toFun = linearPotential p0 :=
  rfl

@[simp] theorem linearPotentialH1OnCube_grad {d : ℕ}
    (Q : TriadicCube d) (p0 : Vec d) :
    (linearPotentialH1OnCube Q p0).grad = fun _ => p0 := by
  funext x i
  simp [linearPotentialH1OnCube, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain,
    fderiv_linearPotential_apply_basisVec]

/-- Private potential defect `v_m - ell_p0` for the raw canonical maximizer. -/
noncomputable def canonicalMaximizerPotentialDefectOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 : Vec d) : Vec d → ℝ :=
  fun x => (canonicalMaximizerSolutionOnCube Q a p q).toH1.toFun x -
    linearPotential p0 x

/-- Raw gradient field of the canonical maximizer on a cube. -/
noncomputable def canonicalMaximizerGradientOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q : Vec d) : Vec d → Vec d :=
  fun x => (canonicalMaximizerSolutionOnCube Q a p q).toH1.grad x

/-- Private gradient defect `grad v_m - p0` for the raw canonical maximizer. -/
noncomputable def canonicalMaximizerGradientDefectOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 : Vec d) : Vec d → Vec d :=
  fun x => canonicalMaximizerGradientOnCube Q a p q x - p0

/-- Raw flux field of the canonical maximizer on a cube. -/
noncomputable def canonicalMaximizerFluxOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q : Vec d) : Vec d → Vec d :=
  fun x => matVecMul (a.toCoeffField x)
    (canonicalMaximizerGradientOnCube Q a p q x)

/-- Private flux defect `a grad v_m - q0` for the raw canonical maximizer. -/
noncomputable def canonicalMaximizerFluxDefectOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q q0 : Vec d) : Vec d → Vec d :=
  fun x => canonicalMaximizerFluxOnCube Q a p q x - q0

/-- `v_m - ell_p0` as an `H¹` function on the parent open cube. -/
noncomputable def canonicalMaximizerPotentialDefectH1OnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 : Vec d) :
    H1Function ((Ch02.cubeDomain Q : Ch02.Domain d) : Set (Vec d)) :=
  (canonicalMaximizerSolutionOnCube Q a p q).toH1 -
    linearPotentialH1OnCube Q p0

@[simp] theorem canonicalMaximizerPotentialDefectH1OnCube_toFun {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 : Vec d) :
    (canonicalMaximizerPotentialDefectH1OnCube Q a p q p0).toFun =
      canonicalMaximizerPotentialDefectOnCube Q a p q p0 := by
  funext x
  show ((canonicalMaximizerSolutionOnCube Q a p q).toH1 - linearPotentialH1OnCube Q p0) x =
    canonicalMaximizerPotentialDefectOnCube Q a p q p0 x
  rw [congrFun (H1Function.sub_toFun _ _) x]
  simp [canonicalMaximizerPotentialDefectOnCube]

@[simp] theorem canonicalMaximizerPotentialDefectH1OnCube_grad {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 : Vec d) :
    (canonicalMaximizerPotentialDefectH1OnCube Q a p q p0).grad =
      fun x => canonicalMaximizerGradientOnCube Q a p q x - p0 := by
  funext x i
  show ((canonicalMaximizerSolutionOnCube Q a p q).toH1 - linearPotentialH1OnCube Q p0).grad x i =
    canonicalMaximizerGradientOnCube Q a p q x i - p0 i
  rw [congrFun (congrFun (H1Function.sub_grad _ _) x) i]
  simp [canonicalMaximizerGradientOnCube]

/-- The raw canonical maximizer potential defect is `L²` on the normalized
cube.  This is deterministic `H¹` membership plus the smooth affine comparison,
not a law/measurability fact. -/
theorem canonicalMaximizerPotentialDefectOnCube_memLp {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 : Vec d) :
    MemLp (canonicalMaximizerPotentialDefectOnCube Q a p q p0)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have hv :
      MemLp (fun x => (canonicalMaximizerSolutionOnCube Q a p q).toH1.toFun x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [Ch02.cubeDomain_coe] using
      (canonicalMaximizerSolutionOnCube Q a p q).toH1.memL2_normalizedCubeMeasure
  have hlin : MemLp (linearPotential p0) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    let u : H1Function (openCubeSet Q) :=
      H1Function.ofContDiffOnIsOpenBoundedConvexDomain
        (U := openCubeSet Q) (f := linearPotential p0)
      (isOpenBoundedConvexDomain_openCubeSet Q) (by
          unfold linearPotential vecDot
          fun_prop)
    simpa [u] using! u.memL2_normalizedCubeMeasure
  simpa [canonicalMaximizerPotentialDefectOnCube] using! hv.sub hlin

/-- The raw canonical maximizer gradient defect is `L²` on the normalized cube. -/
theorem canonicalMaximizerGradientDefectOnCube_memLp {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 : Vec d) :
    MemLp (canonicalMaximizerGradientDefectOnCube Q a p q p0)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have hgradOpen :
      MemVectorL2 (openCubeSet Q) (canonicalMaximizerGradientOnCube Q a p q) := by
    simpa [canonicalMaximizerGradientOnCube, canonicalMaximizerSolutionOnCube,
      Ch02.cubeDomain_coe] using!
      (canonicalMaximizerSolutionOnCube Q a p q).toH1.grad_memVectorL2
  have hgrad :
      MemLp (canonicalMaximizerGradientOnCube Q a p q)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q hgradOpen
  have hconst :
      MemLp (fun _ : Vec d => p0) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa using
      (MeasureTheory.memLp_const
        (μ := normalizedCubeMeasure Q) (p := (2 : ℝ≥0∞)) (c := p0))
  simpa [canonicalMaximizerGradientDefectOnCube] using! hgrad.sub hconst

/-- The raw canonical maximizer flux defect is `L²` on the normalized cube.

The coefficient object is only a.e.-elliptic, so the flux bound is delegated to
the public Ch2 source theorem `Solution.flux_memVectorL2`, which hides the
pointwise-good representative used in its proof. -/
theorem canonicalMaximizerFluxDefectOnCube_memLp {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q q0 : Vec d) :
    MemLp (canonicalMaximizerFluxDefectOnCube Q a p q q0)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have hfluxOpen :
      MemVectorL2 (openCubeSet Q)
        (fun x => matVecMul (a.toCoeffField x)
          ((canonicalMaximizerSolutionOnCube Q a p q).toH1.grad x)) := by
    simpa [Ch02.cubeDomain_coe] using!
      Ch02.Solution.flux_memVectorL2 (canonicalMaximizerSolutionOnCube Q a p q)
  have hflux :
      MemLp
        (fun x => matVecMul (a.toCoeffField x)
          ((canonicalMaximizerSolutionOnCube Q a p q).toH1.grad x))
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q hfluxOpen
  have hconst :
      MemLp (fun _ : Vec d => q0) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa using
      (MeasureTheory.memLp_const
        (μ := normalizedCubeMeasure Q) (p := (2 : ℝ≥0∞)) (c := q0))
  simpa [canonicalMaximizerFluxDefectOnCube] using! hflux.sub hconst

theorem canonicalMaximizerGradientOnCube_memLp_descendant {d : ℕ}
    (Q R : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    MemLp (canonicalMaximizerGradientOnCube Q a p q)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
  have hgradOpen :
      MemVectorL2 (openCubeSet Q)
        (canonicalMaximizerGradientOnCube Q a p q) := by
    simpa [canonicalMaximizerGradientOnCube, canonicalMaximizerSolutionOnCube,
      Ch02.cubeDomain_coe] using!
      (canonicalMaximizerSolutionOnCube Q a p q).toH1.grad_memVectorL2
  have hgradOpenR :
      MemVectorL2 (openCubeSet R)
        (canonicalMaximizerGradientOnCube Q a p q) := by
    exact hgradOpen.mono_measure (by
      simpa [volumeMeasureOn] using
        MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
          (openCubeSet_subset_of_mem_descendantsAtDepth hR))
  exact memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet R hgradOpenR

theorem cubeAverageVec_canonicalMaximizerGradientDefectOnDependentFamily_eq_ch04
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q p0 : Vec d) :
    cubeAverageVec R
        (canonicalMaximizerGradientDefectOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q p0) =
      Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun - p0 := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  have hgrad :
      MemLp (canonicalMaximizerGradientOnCube Q aQ p q)
        (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    canonicalMaximizerGradientOnCube_memLp_descendant Q R aQ hR p q
  have hch04 :
      Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun =
        cubeAverageVec R (canonicalMaximizerGradientOnCube Q aQ p q) := by
    simpa [F, aQ, canonicalMaximizerGradientOnCube, canonicalMaximizerSolutionOnCube]
      using!
      Ch04.canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer
        a ha hR p q
  calc
    cubeAverageVec R
        (canonicalMaximizerGradientDefectOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q p0) =
        cubeAverageVec R (fun x => canonicalMaximizerGradientOnCube Q aQ p q x - p0) := by
          rfl
    _ = cubeAverageVec R (canonicalMaximizerGradientOnCube Q aQ p q) - p0 := by
          simpa using cubeAverageVec_sub_const R (canonicalMaximizerGradientOnCube Q aQ p q) p0 hgrad
    _ = Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun - p0 := by
          rw [hch04]

theorem cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerGradientDefectOnDependentFamily_eq_ch04
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (p q p0 : Vec d) :
    cubeBesovNegativeVectorPartialSeminorm Q s N
        (canonicalMaximizerGradientDefectOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q p0) =
      Ch04.canonicalScalarResponseGradientWeakNormPartialCubeSet Q s N p q p0 a.toFun := by
  unfold cubeBesovNegativeVectorPartialSeminorm
    cubeBesovNegativeVectorDepthSeminorm cubeBesovNegativeVectorDepthAverage
    Ch04.canonicalScalarResponseGradientWeakNormPartialCubeSet
  refine Finset.sum_congr rfl ?_
  intro j hj
  apply congrArg (fun z : ℝ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt z)
  unfold descendantsAverage
  apply congrArg (fun z : ℝ => (((descendantsAtDepth Q j).card : ℝ)⁻¹) * z)
  refine Finset.sum_congr rfl ?_
  intro R hR
  rw [cubeAverageVec_canonicalMaximizerGradientDefectOnDependentFamily_eq_ch04
    a ha hR p q p0]

theorem cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerGradientDefectOnDependentFamily_le_ch04WeakNorm
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (N : ℕ) (p q p0 : Vec d) :
    cubeBesovNegativeVectorPartialSeminorm Q s N
        (canonicalMaximizerGradientDefectOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q p0) ≤
      Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  have hRawBdd :
      BddAbove (Set.range fun M : ℕ =>
        cubeBesovNegativeVectorPartialSeminorm Q s M
          (canonicalMaximizerGradientDefectOnCube Q aQ p q p0)) :=
    cubeBesovNegativeVectorPartialSeminorm_bddAbove_of_memLp Q hs
      (canonicalMaximizerGradientDefectOnCube Q aQ p q p0)
      (canonicalMaximizerGradientDefectOnCube_memLp Q aQ p q p0)
  rcases hRawBdd with ⟨B, hB⟩
  have hCh4Bdd :
      BddAbove (Set.range fun M : ℕ =>
        Ch04.canonicalScalarResponseGradientWeakNormPartialCubeSet Q s M p q p0 a.toFun) := by
    refine ⟨B, ?_⟩
    rintro x ⟨M, rfl⟩
    have hRaw :
        cubeBesovNegativeVectorPartialSeminorm Q s M
            (canonicalMaximizerGradientDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0) ≤ B := by
      simpa [F, aQ] using hB ⟨M, rfl⟩
    simpa [cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerGradientDefectOnDependentFamily_eq_ch04
      a ha Q s M p q p0] using hRaw
  rw [cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerGradientDefectOnDependentFamily_eq_ch04
    a ha Q s N p q p0]
  exact le_csSup hCh4Bdd ⟨N, rfl⟩

theorem canonicalMaximizerFluxOnCube_memLp_descendant {d : ℕ}
    (Q R : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    MemLp (canonicalMaximizerFluxOnCube Q a p q)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
  have hfluxOpen :
      MemVectorL2 (openCubeSet Q)
        (canonicalMaximizerFluxOnCube Q a p q) := by
    simpa [canonicalMaximizerFluxOnCube, canonicalMaximizerGradientOnCube,
      canonicalMaximizerSolutionOnCube, Ch02.cubeDomain_coe] using!
      Ch02.Solution.flux_memVectorL2 (canonicalMaximizerSolutionOnCube Q a p q)
  have hfluxOpenR :
      MemVectorL2 (openCubeSet R)
        (canonicalMaximizerFluxOnCube Q a p q) := by
    exact hfluxOpen.mono_measure (by
      simpa [volumeMeasureOn] using
        MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
          (openCubeSet_subset_of_mem_descendantsAtDepth hR))
  exact memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet R hfluxOpenR

theorem cubeAverageVec_canonicalMaximizerFluxDefectOnDependentFamily_eq_ch04
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q q0 : Vec d) :
    cubeAverageVec R
        (canonicalMaximizerFluxDefectOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q q0) =
      Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun - q0 := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  have hflux :
      MemLp (canonicalMaximizerFluxOnCube Q aQ p q)
        (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    canonicalMaximizerFluxOnCube_memLp_descendant Q R aQ hR p q
  have hch04 :
      Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun =
        cubeAverageVec R (canonicalMaximizerFluxOnCube Q aQ p q) := by
    simpa [F, aQ, canonicalMaximizerFluxOnCube, canonicalMaximizerGradientOnCube,
      canonicalMaximizerSolutionOnCube] using!
      Ch04.canonicalScalarResponseFluxAverageCubeSet_eq_cubeAverageVec_canonicalMaximizerFlux
        a ha hR p q
  calc
    cubeAverageVec R
        (canonicalMaximizerFluxDefectOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q q0) =
        cubeAverageVec R (fun x => canonicalMaximizerFluxOnCube Q aQ p q x - q0) := by
          rfl
    _ = cubeAverageVec R (canonicalMaximizerFluxOnCube Q aQ p q) - q0 := by
          simpa using cubeAverageVec_sub_const R (canonicalMaximizerFluxOnCube Q aQ p q) q0 hflux
    _ = Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun - q0 := by
          rw [hch04]

theorem cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_eq_ch04
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (p q q0 : Vec d) :
    cubeBesovNegativeVectorPartialSeminorm Q s N
        (canonicalMaximizerFluxDefectOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q q0) =
      Ch04.canonicalScalarResponseFluxWeakNormPartialCubeSet Q s N p q q0 a.toFun := by
  unfold cubeBesovNegativeVectorPartialSeminorm
    cubeBesovNegativeVectorDepthSeminorm cubeBesovNegativeVectorDepthAverage
    Ch04.canonicalScalarResponseFluxWeakNormPartialCubeSet
  refine Finset.sum_congr rfl ?_
  intro j hj
  apply congrArg (fun z : ℝ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt z)
  unfold descendantsAverage
  apply congrArg (fun z : ℝ => (((descendantsAtDepth Q j).card : ℝ)⁻¹) * z)
  refine Finset.sum_congr rfl ?_
  intro R hR
  rw [cubeAverageVec_canonicalMaximizerFluxDefectOnDependentFamily_eq_ch04
    a ha hR p q q0]

theorem cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_le_ch04WeakNorm
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (N : ℕ) (p q q0 : Vec d) :
    cubeBesovNegativeVectorPartialSeminorm Q s N
        (canonicalMaximizerFluxDefectOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q q0) ≤
      Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  have hRawBdd :
      BddAbove (Set.range fun M : ℕ =>
        cubeBesovNegativeVectorPartialSeminorm Q s M
          (canonicalMaximizerFluxDefectOnCube Q aQ p q q0)) :=
    cubeBesovNegativeVectorPartialSeminorm_bddAbove_of_memLp Q hs
      (canonicalMaximizerFluxDefectOnCube Q aQ p q q0)
      (canonicalMaximizerFluxDefectOnCube_memLp Q aQ p q q0)
  rcases hRawBdd with ⟨B, hB⟩
  have hCh4Bdd :
      BddAbove (Set.range fun M : ℕ =>
        Ch04.canonicalScalarResponseFluxWeakNormPartialCubeSet Q s M p q q0 a.toFun) := by
    refine ⟨B, ?_⟩
    rintro x ⟨M, rfl⟩
    have hRaw :
        cubeBesovNegativeVectorPartialSeminorm Q s M
            (canonicalMaximizerFluxDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q q0) ≤ B := by
      simpa [F, aQ] using hB ⟨M, rfl⟩
    simpa [cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_eq_ch04
      a ha Q s M p q q0] using hRaw
  rw [cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_eq_ch04
    a ha Q s N p q q0]
  exact le_csSup hCh4Bdd ⟨N, rfl⟩

theorem norm_cubeAverageVec_canonicalMaximizerFluxDefectOnDependentFamily_le_ch04
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (p q q0 : Vec d) :
    ‖cubeAverageVec Q
        (canonicalMaximizerFluxDefectOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q q0)‖ ≤
      ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖ := by
  rw [cubeAverageVec_canonicalMaximizerFluxDefectOnDependentFamily_eq_ch04
    (a := a) (ha := ha) (Q := Q) (R := Q) (j := 0) (by simp) p q q0]

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
