/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHS
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletCorrectedWeakFluxAveraged
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

/-! # Weak Solutions -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public weak-solution bridges for Chapter 3

This file contains forced-solution, flux-field, weak-solution, and comparison-pair
bridges from the public Chapter 3 data to the deterministic cube APIs.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal
open ZeroTraceDirichletCorrectorData

theorem forcedSolutionGradientField_memVectorL2_cubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g) :
    MemVectorL2 (cubeSet Q) (forcedSolutionGradientField u) := by
  simpa [forcedSolutionGradientField] using
    (publicH1ToCubeSet u.toH1).grad_memVectorL2

theorem forcedSolutionGradientField_memVectorL2_descendant_cubeSet
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {j : ℕ}
    (u : ForcedCubeSolution Q a g) (hR : R ∈ descendantsAtDepth Q j) :
    MemVectorL2 (cubeSet R) (forcedSolutionGradientField u) := by
  have hmono :
      volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
    simpa [volumeMeasureOn] using
      MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
        (cubeSet_subset_of_mem_descendantsAtDepth hR)
  exact (forcedSolutionGradientField_memVectorL2_cubeSet u).mono_measure hmono

theorem forcedSolutionGradientField_negativeBesovPartialSeminormTwo_bddAbove
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {s : ℝ}
    (u : ForcedCubeSolution Q a g) (hs : 0 < s) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (forcedSolutionGradientField u)) :=
  cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs
    (forcedSolutionGradientField u)
    (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q
      (forcedSolutionGradientField_memVectorL2_cubeSet u))

theorem forcedSolutionGradientField_descendant_negativeBesovPartialSeminormTwo_bddAbove
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {j : ℕ} {s : ℝ}
    (u : ForcedCubeSolution Q a g) (hR : R ∈ descendantsAtDepth Q j)
    (hs : 0 < s) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo R s N
        (forcedSolutionGradientField u)) :=
  cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs
    (forcedSolutionGradientField u)
    (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R
      (forcedSolutionGradientField_memVectorL2_descendant_cubeSet u hR))

/-- Harmonic `H¹` gradients automatically have bounded finite negative-Besov
partials on their cube. -/
theorem AHarmonicFunction.grad_negativeBesovPartialSeminormTwo_bddAbove
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {s : ℝ}
    (w : AHarmonicFunction a (cubeSet Q)) (hs : 0 < s) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => w.toH1.grad x)) :=
  cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs
    (fun x => w.toH1.grad x)
    (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q
      w.toH1.grad_memVectorL2)

theorem forcedSolutionPublicFlux_memVectorL2_descendant_cubeSet
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {j : ℕ}
    (u : ForcedCubeSolution Q a g) (hR : R ∈ descendantsAtDepth Q j) :
    MemVectorL2 (cubeSet R)
      (fun x => matVecMul (publicCoeffField Q a x)
        (forcedSolutionGradientField u x)) :=
  memVectorL2_matVecMul_of_isEllipticFieldOn
    (publicCoeffField_isEllipticFieldOn_descendant_cubeSet Q a hR)
    (forcedSolutionGradientField_memVectorL2_descendant_cubeSet u hR)

theorem forcedSolutionPublicFlux_memLp_normalizedCubeMeasure_descendant
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {j : ℕ}
    (u : ForcedCubeSolution Q a g) (hR : R ∈ descendantsAtDepth Q j) :
    MeasureTheory.MemLp
      (fun x => matVecMul (publicCoeffField Q a x)
        (forcedSolutionGradientField u x))
      (2 : ENNReal) (normalizedCubeMeasure R) :=
  memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R
    (forcedSolutionPublicFlux_memVectorL2_descendant_cubeSet u hR)

theorem forcedSolutionPublicFlux_negativeBesovPartialSeminormTwo_bddAbove_descendant
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {j : ℕ} {s : ℝ}
    (u : ForcedCubeSolution Q a g) (hR : R ∈ descendantsAtDepth Q j)
    (hs : 0 < s) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo R s N
        (fun x => matVecMul (publicCoeffField Q a x)
          (forcedSolutionGradientField u x))) :=
  cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs
    (fun x => matVecMul (publicCoeffField Q a x)
      (forcedSolutionGradientField u x))
    (forcedSolutionPublicFlux_memLp_normalizedCubeMeasure_descendant u hR)

theorem forcedSolutionPublicFlux_negativeBesovPartialSeminormTwo_bddAbove_child
    {d : ℕ} [NeZero d] {Q R S : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {j : ℕ} {s : ℝ}
    (u : ForcedCubeSolution Q a g) (hR : R ∈ descendantsAtDepth Q j)
    (hS : S ∈ descendantsAtDepth R 1) (hs : 0 < s) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo S s N
        (fun x => matVecMul (publicCoeffField Q a x)
          (forcedSolutionGradientField u x))) :=
  forcedSolutionPublicFlux_negativeBesovPartialSeminormTwo_bddAbove_descendant
    (Q := Q) (R := S) (a := a) (g := g) u
    (mem_descendantsAtDepth_add hR hS) hs

theorem publicH1_fluxDefect_memVectorL2_descendant_cubeSet
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d} {j : ℕ}
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
    (hR : R ∈ descendantsAtDepth Q j) :
    MemVectorL2 (cubeSet R)
      (fluxDefect (publicCoeffField Q a) a0.matrix u.grad) := by
  have hgrad : MemVectorL2 (cubeSet R) u.grad :=
    publicH1ToCubeSet_grad_memVectorL2_descendant_cubeSet u hR
  have hA :
      MemVectorL2 (cubeSet R)
        (fun x => matVecMul (publicCoeffField Q a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_descendant_cubeSet Q a hR) hgrad
  have hEll0 :
      IsEllipticFieldOn a0.lam a0.Lam (cubeSet R)
        (constantCoeffField a0.matrix) :=
    constantCoeffMatrix_isEllipticFieldOn_constantCoeffField a0
      (measurableSet_cubeSet R)
  have hA0 :
      MemVectorL2 (cubeSet R) (fun x => matVecMul a0.matrix (u.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 hgrad
  simpa [fluxDefect] using! hA.sub hA0

theorem publicH1_fluxDefect_negativeBesovPartialSeminormTwo_bddAbove_descendant
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d} {j : ℕ} {s : ℝ}
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
    (hR : R ∈ descendantsAtDepth Q j) (hs : 0 < s) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo R s N
        (fluxDefect (publicCoeffField Q a) a0.matrix u.grad)) :=
  cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs
    (fluxDefect (publicCoeffField Q a) a0.matrix u.grad)
    (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R
      (publicH1_fluxDefect_memVectorL2_descendant_cubeSet
        (Q := Q) (a := a) (a0 := a0) u hR))

theorem CoarseGrainingComparisonDatum.fluxDefect_negativeBesovPartialSeminormTwo_bddAbove_descendant
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d} {g : Vec d → Vec d} {j : ℕ} {s : ℝ}
    (w : CoarseGrainingComparisonDatum Q a a0 g)
    (hR : R ∈ descendantsAtDepth Q j) (hs : 0 < s) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo R s N
        (fluxDefect (publicCoeffField Q a) a0.matrix w.u.grad)) :=
  publicH1_fluxDefect_negativeBesovPartialSeminormTwo_bddAbove_descendant
    (Q := Q) (a := a) (a0 := a0) w.u hR hs

namespace IsH1DirichletRhsWeakSolutionOn

theorem of_residual_solenoidal
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {u : H1Function U} {g : Vec d → Vec d}
    (hflux : MemVectorL2 U (fun x => matVecMul (a x) (u.grad x)))
    (hg : MemVectorL2 U g)
    (hsol : IsSolenoidalOn U (fun x => matVecMul (a x) (u.grad x) - g x)) :
    IsH1DirichletRhsWeakSolutionOn a U u g := by
  intro φ
  have hflux_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hflux φ.toH1Function.grad_memVectorL2
  have hg_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (g x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hg φ.toH1Function.grad_memVectorL2
  have hfun :
      (fun x => vecDot (matVecMul (a x) (u.grad x) - g x)
          (φ.toH1Function.grad x)) =
        fun x =>
          vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) -
            vecDot (g x) (φ.toH1Function.grad x) := by
    funext x
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  have h := hsol φ
  rw [hfun, MeasureTheory.integral_sub hflux_int hg_int] at h
  exact sub_eq_zero.mp h

theorem restrict_cubeSet_of_mem_descendantsAtDepth
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    {a : CoeffField d} {u : H1Function (cubeSet Q)} {g : Vec d → Vec d}
    {lam Lam : ℝ}
    (h : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MemVectorL2 (cubeSet Q) g)
    (hR : R ∈ descendantsAtDepth Q j) :
    IsH1DirichletRhsWeakSolutionOn a (cubeSet R)
      ((u.toOpenCubeSet.restrictToOpenSubcube hR).toCubeSet) g := by
  let uR : H1Function (cubeSet R) :=
    (u.toOpenCubeSet.restrictToOpenSubcube hR).toCubeSet
  change IsH1DirichletRhsWeakSolutionOn a (cubeSet R) uR g
  have hsubset : cubeSet R ⊆ cubeSet Q :=
    cubeSet_subset_of_mem_descendantsAtDepth hR
  have hu_grad_memR : MemVectorL2 (cubeSet R) u.grad := by
    simpa [MemVectorL2, volumeMeasureOn] using
      u.grad_memVectorL2.mono_measure
        (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hsubset)
  have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEll.mono (measurableSet_cubeSet R) hsubset
  have hfluxR :
      MemVectorL2 (cubeSet R) (fun x => matVecMul (a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEllR hu_grad_memR
  have hgR : MemVectorL2 (cubeSet R) g :=
    hg.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hsubset)
  have hresQ :
      IsSolenoidalOn (cubeSet Q)
        (fun x => matVecMul (a x) (u.grad x) - g x) :=
    h.residual_solenoidal hEll hg
  have hresMemR :
      MemVectorL2 (cubeSet R) (fun x => matVecMul (a x) (u.grad x) - g x) :=
    hfluxR.sub hgR
  have hresR :
      IsSolenoidalOn (cubeSet R)
        (fun x => matVecMul (a x) (u.grad x) - g x) :=
    IsSolenoidalOn.restrict_cubeSet_of_mem_descendantsAtDepth hresQ hR hresMemR
  exact of_residual_solenoidal
    (by simpa [uR] using hfluxR) hgR
    (by simpa [uR] using hresR)

end IsH1DirichletRhsWeakSolutionOn

theorem weakFluxRHSScaledAveragedSeminormSq_bddAbove_publicCoeffField_forcedSolution
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {s : ℝ}
    (u : ForcedCubeSolution Q a g) (hs : 0 < s) :
    BddAbove (Set.range fun n : ℕ =>
      weakFluxRHSScaledAveragedSeminormSq Q (publicCoeffField Q a) s
        (forcedSolutionGradientField u) n) := by
  have hQ : Q ∈ descendantsAtDepth Q 0 := by
    simp [descendantsAtDepth_zero]
  have hflux :
      MeasureTheory.MemLp
        (fun x => matVecMul (publicCoeffField Q a x)
          (forcedSolutionGradientField u x))
        (2 : ENNReal) (normalizedCubeMeasure Q) :=
    forcedSolutionPublicFlux_memLp_normalizedCubeMeasure_descendant
      (Q := Q) (R := Q) u hQ
  simpa [weakFluxRHSScaledAveragedSeminormSq, weakFluxRHSAveragedSeminormSq,
    coarsePoincareRHSSn, coarsePoincareRHSRn] using
      coarsePoincareRHSSn_bddAbove_of_memLp Q hs
        (fun x => matVecMul (publicCoeffField Q a x)
          (forcedSolutionGradientField u x)) hflux

theorem forcedSolutionFluxField_ae_eq_publicCoeffField_cubeSet
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g) :
    forcedSolutionFluxField Q a u =ᵐ[volumeMeasureOn (cubeSet Q)]
      fun x => matVecMul (publicCoeffField Q a x) (u.toH1.grad x) := by
  filter_upwards [(publicCoeffField_ae_eq_cubeSet Q a).symm] with x hx
  ext i
  simp [forcedSolutionFluxField, hx]

theorem forcedSolutionFluxDefectField_ae_eq_fluxDefect_publicCoeffField_cubeSet
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d} {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) :
    forcedSolutionFluxDefectField Q a a0 u
      =ᵐ[volumeMeasureOn (cubeSet Q)]
    fluxDefect (publicCoeffField Q a) a0.matrix u.toH1.grad := by
  filter_upwards [(publicCoeffField_ae_eq_cubeSet Q a).symm] with x hx
  ext i
  simp [forcedSolutionFluxDefectField, fluxDefect, hx, sub_eq_add_neg,
    add_matVecMul, neg_matVecMul]

theorem homogenizationComparisonFluxDefectFromGradient_ae_eq_fluxDefect_publicCoeffField_cubeSet
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d} (G : Vec d → Vec d) :
    homogenizationComparisonFluxDefectFromGradient Q a a0 G
      =ᵐ[volumeMeasureOn (cubeSet Q)]
    fluxDefect (publicCoeffField Q a) a0.matrix G := by
  filter_upwards [(publicCoeffField_ae_eq_cubeSet Q a).symm] with x hx
  ext i
  simp [homogenizationComparisonFluxDefectFromGradient, fluxDefect, hx,
    sub_eq_add_neg, add_matVecMul, neg_matVecMul]

theorem homogenizationComparisonFluxDefectFromGradient_ae_eq_fluxDefect_parent_publicCoeffField_descendant_cubeSet
    {d : ℕ} {Q R : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (G : Vec d → Vec d) :
    homogenizationComparisonFluxDefectFromGradient R a a0 G
      =ᵐ[volumeMeasureOn (cubeSet R)]
    fluxDefect (publicCoeffField Q a) a0.matrix G := by
  filter_upwards [(publicCoeffField_ae_eq_descendant_cubeSet Q a hR).symm]
    with x hx
  ext i
  simp [homogenizationComparisonFluxDefectFromGradient, fluxDefect, hx,
    sub_eq_add_neg, add_matVecMul, neg_matVecMul]

theorem homogenizationComparisonFluxField_ae_eq_fluxComparison_publicCoeffField_cubeSet
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d}
    (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    homogenizationComparisonFluxField Q a a0 u v
      =ᵐ[volumeMeasureOn (cubeSet Q)]
    fluxComparison (publicCoeffField Q a) a0.matrix u.grad v.grad := by
  filter_upwards [(publicCoeffField_ae_eq_cubeSet Q a).symm] with x hx
  ext i
  simp [homogenizationComparisonFluxField, fluxComparison, hx]

theorem homogenizationComparisonConstantGradientField_eq_constantGradientComparison
    {d : ℕ} {Q : TriadicCube d} {a0 : ConstantCoeffMatrix d}
    (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    homogenizationComparisonConstantGradientField a0 u v =
      constantGradientComparison a0.matrix u.grad v.grad := by
  rfl

/-- A zero-trace potential on the public open cube can be moved to `cubeSet`
after changing representatives a.e. on the open cube. -/
theorem isPotentialZeroTraceOn_cubeSet_of_openCubeSet_ae
    {d : ℕ} [NeZero d] {Q : TriadicCube d}
    {f g : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn (openCubeSet Q) f)
    (hfg : f =ᵐ[volumeMeasureOn (openCubeSet Q)] g) :
    IsPotentialZeroTraceOn (cubeSet Q) g :=
  isPotentialZeroTraceOn_cubeSet_triadicCube_of_openCubeSet
    (IsPotentialZeroTraceOn.congr_ae hfg hf)

namespace IsSolenoidalOn

/-- The solenoidal predicate is insensitive to a.e. changes of the vector field
on the test domain. -/
theorem congr_ae {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → Vec d}
    (hfg : f =ᵐ[volumeMeasureOn U] g)
    (hf : IsSolenoidalOn U f) :
    IsSolenoidalOn U g := by
  intro φ
  calc
    ∫ x in U, vecDot (g x) (φ.toH1Function.grad x)
        ∂MeasureTheory.volume =
      ∫ x in U, vecDot (f x) (φ.toH1Function.grad x)
        ∂MeasureTheory.volume := by
        exact MeasureTheory.integral_congr_ae <|
          hfg.mono fun x hx => by simp [hx]
    _ = 0 := hf φ

end IsSolenoidalOn

theorem isH1DirichletRhsWeakSolutionOn_coeffOn_of_isForcedEquation
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {u : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    {g : Vec d → Vec d}
    (h : IsForcedEquation Q a u g) :
    IsH1DirichletRhsWeakSolutionOn (a.coeffOn Q).toCoeffField
      (Ch02.cubeDomain Q : Set (Vec d)) u g :=
  h

theorem isH1DirichletRhsWeakSolutionOn_publicCoeffField_of_isForcedEquation
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {u : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    {g : Vec d → Vec d}
    (h : IsForcedEquation Q a u g) :
    IsH1DirichletRhsWeakSolutionOn (publicCoeffField Q a)
      (Ch02.cubeDomain Q : Set (Vec d)) u g := by
  intro φ
  have hcoeff := publicCoeffField_ae_eq Q a
  have hintegrand :
      (fun x =>
        vecDot (matVecMul (publicCoeffField Q a x) (u.grad x))
          (φ.toH1Function.grad x))
        =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
      fun x =>
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (φ.toH1Function.grad x) := by
    filter_upwards [hcoeff] with x hx
    simp [hx]
  calc
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul (publicCoeffField Q a x) (u.grad x))
          (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
        exact MeasureTheory.integral_congr_ae hintegrand
    _ =
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := h φ

theorem isZeroTraceDirichletRhsWeakSolution_coeffOn_of_zeroTraceForcedCubeSolution
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d}
    (u : ZeroTraceForcedCubeSolution Q a g) :
    IsZeroTraceDirichletRhsWeakSolution (a.coeffOn Q).toCoeffField
      (Ch02.cubeDomain Q : Set (Vec d)) u.toH10 g :=
  u.weakSolution

theorem isZeroTraceDirichletRhsWeakSolution_publicCoeffField_of_zeroTraceForcedCubeSolution
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d}
    (u : ZeroTraceForcedCubeSolution Q a g) :
    IsZeroTraceDirichletRhsWeakSolution (publicCoeffField Q a)
      (Ch02.cubeDomain Q : Set (Vec d)) u.toH10 g := by
  intro φ
  have hcoeff := publicCoeffField_ae_eq Q a
  have hintegrand :
      (fun x =>
        vecDot (matVecMul (publicCoeffField Q a x)
          (u.toH10.toH1Function.grad x)) (φ.toH1Function.grad x))
        =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
      fun x =>
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x)
          (u.toH10.toH1Function.grad x)) (φ.toH1Function.grad x) := by
    filter_upwards [hcoeff] with x hx
    simp [hx]
  calc
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul (publicCoeffField Q a x)
          (u.toH10.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x)
          (u.toH10.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
        exact MeasureTheory.integral_congr_ae hintegrand
    _ =
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume :=
        u.weakSolution φ

theorem isMeanZeroNeumannRhsWeakSolution_coeffOn_of_isMeanZeroNeumannForcedEquation
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {w : H1MeanZeroFunction (Ch02.cubeDomain Q : Set (Vec d))}
    {g : Vec d → Vec d}
    (h : IsMeanZeroNeumannForcedEquation Q a w g) :
    IsMeanZeroNeumannRhsWeakSolution (a.coeffOn Q).toCoeffField
      (Ch02.cubeDomain Q : Set (Vec d)) w g :=
  h

theorem isMeanZeroNeumannRhsWeakSolution_publicCoeffField_of_isMeanZeroNeumannForcedEquation
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {w : H1MeanZeroFunction (Ch02.cubeDomain Q : Set (Vec d))}
    {g : Vec d → Vec d}
    (h : IsMeanZeroNeumannForcedEquation Q a w g) :
    IsMeanZeroNeumannRhsWeakSolution (publicCoeffField Q a)
      (Ch02.cubeDomain Q : Set (Vec d)) w g := by
  intro φ
  have hcoeff := publicCoeffField_ae_eq Q a
  have hintegrand :
      (fun x =>
        vecDot (matVecMul (publicCoeffField Q a x)
          (w.toH1Function.grad x)) (φ.toH1Function.grad x))
        =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
      fun x =>
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x)
          (w.toH1Function.grad x)) (φ.toH1Function.grad x) := by
    filter_upwards [hcoeff] with x hx
    simp [hx]
  calc
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul (publicCoeffField Q a x)
          (w.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x)
          (w.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
        exact MeasureTheory.integral_congr_ae hintegrand
    _ =
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume :=
        h φ

theorem isMeanZeroNeumannRhsWeakSolution_publicCoeffField_of_neumannForcedCubeSolution
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d}
    (w : NeumannForcedCubeSolution Q a g) :
    IsMeanZeroNeumannRhsWeakSolution (publicCoeffField Q a)
      (Ch02.cubeDomain Q : Set (Vec d)) w.toH1MeanZero
      (fun x => g x - cubeAverageVec Q g) :=
  isMeanZeroNeumannRhsWeakSolution_publicCoeffField_of_isMeanZeroNeumannForcedEquation
    (Q := Q) (a := a) (w := w.toH1MeanZero)
    (g := fun x => g x - cubeAverageVec Q g) w.weakSolution

theorem isH1DirichletRhsWeakSolutionOn_constantCoeff_of_isConstantCoeffForcedEquation
    {d : ℕ} {Q : TriadicCube d} {a0 : ConstantCoeffMatrix d}
    {u : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    {g : Vec d → Vec d}
    (h : IsConstantCoeffForcedEquation Q a0 u g) :
    IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0.matrix)
      (Ch02.cubeDomain Q : Set (Vec d)) u g := by
  intro φ
  simpa [constantCoeffField] using h φ

/-- Open-cube weak equations transport to the half-open triadic cube because
the two realizations differ by a null boundary. -/
theorem isH1DirichletRhsWeakSolutionOn_cubeSet_of_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d}
    {a : CoeffField d} {u : H1Function (openCubeSet Q)}
    {g : Vec d → Vec d}
    (h : IsH1DirichletRhsWeakSolutionOn a (openCubeSet Q) u g) :
    IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u.toCubeSet g := by
  intro φ
  have hopen := h φ.toOpenCubeSet
  have hleft :
      ∫ x in cubeSet Q,
          vecDot (matVecMul (a x) (u.toCubeSet.grad x))
            (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (matVecMul (a x) (u.grad x))
            (φ.toOpenCubeSet.toH1Function.grad x) ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q)
        (f := fun x =>
          vecDot (matVecMul (a x) (u.toCubeSet.grad x))
            (φ.toH1Function.grad x)))
  have hright :
      ∫ x in cubeSet Q,
          vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (g x) (φ.toOpenCubeSet.toH1Function.grad x)
            ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q) (f := fun x => vecDot (g x) (φ.toH1Function.grad x)))
  rw [hleft, hright]
  exact hopen

theorem isZeroTraceDirichletRhsWeakSolution_cubeSet_of_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d}
    {a : CoeffField d} {u : H10Function (openCubeSet Q)}
    {g : Vec d → Vec d}
    (h : IsZeroTraceDirichletRhsWeakSolution a (openCubeSet Q) u g) :
    IsZeroTraceDirichletRhsWeakSolution a (cubeSet Q) u.toCubeSet g := by
  intro φ
  have hopen := h φ.toOpenCubeSet
  have hleft :
      ∫ x in cubeSet Q,
          vecDot (matVecMul (a x) (u.toCubeSet.toH1Function.grad x))
            (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (matVecMul (a x) (u.toH1Function.grad x))
            (φ.toOpenCubeSet.toH1Function.grad x) ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q)
        (f := fun x =>
          vecDot (matVecMul (a x) (u.toCubeSet.toH1Function.grad x))
            (φ.toH1Function.grad x)))
  have hright :
      ∫ x in cubeSet Q,
          vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (g x) (φ.toOpenCubeSet.toH1Function.grad x)
            ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q) (f := fun x => vecDot (g x) (φ.toH1Function.grad x)))
  calc
    ∫ x in cubeSet Q,
        vecDot (matVecMul (a x) (u.toCubeSet.toH1Function.grad x))
          (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        vecDot (matVecMul (a x) (u.toH1Function.grad x))
          (φ.toOpenCubeSet.toH1Function.grad x) ∂MeasureTheory.volume := hleft
    _ =
      ∫ x in openCubeSet Q,
        vecDot (g x) (φ.toOpenCubeSet.toH1Function.grad x)
          ∂MeasureTheory.volume := hopen
    _ =
      ∫ x in cubeSet Q,
        vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := hright.symm

theorem isMeanZeroNeumannRhsWeakSolution_cubeSet_of_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d}
    {a : CoeffField d} {u : H1MeanZeroFunction (openCubeSet Q)}
    {g : Vec d → Vec d}
    (h : IsMeanZeroNeumannRhsWeakSolution a (openCubeSet Q) u g) :
    IsMeanZeroNeumannRhsWeakSolution a (cubeSet Q)
      (H1MeanZeroFunction.toCubeSet u) g := by
  intro φ
  have hopen := h (H1MeanZeroFunction.toOpenCubeSet φ)
  have hleft :
      ∫ x in cubeSet Q,
          vecDot (matVecMul (a x)
            ((H1MeanZeroFunction.toCubeSet u).toH1Function.grad x))
            (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (matVecMul (a x) (u.toH1Function.grad x))
            ((H1MeanZeroFunction.toOpenCubeSet φ).toH1Function.grad x)
            ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q)
        (f := fun x =>
          vecDot (matVecMul (a x)
            ((H1MeanZeroFunction.toCubeSet u).toH1Function.grad x))
            (φ.toH1Function.grad x)))
  have hright :
      ∫ x in cubeSet Q,
          vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (g x)
            ((H1MeanZeroFunction.toOpenCubeSet φ).toH1Function.grad x)
            ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q) (f := fun x => vecDot (g x) (φ.toH1Function.grad x)))
  calc
    ∫ x in cubeSet Q,
        vecDot (matVecMul (a x)
          ((H1MeanZeroFunction.toCubeSet u).toH1Function.grad x))
          (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        vecDot (matVecMul (a x) (u.toH1Function.grad x))
          ((H1MeanZeroFunction.toOpenCubeSet φ).toH1Function.grad x)
          ∂MeasureTheory.volume := hleft
    _ =
      ∫ x in openCubeSet Q,
        vecDot (g x)
          ((H1MeanZeroFunction.toOpenCubeSet φ).toH1Function.grad x)
          ∂MeasureTheory.volume := hopen
    _ =
      ∫ x in cubeSet Q,
        vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := hright.symm

theorem isH1DirichletRhsWeakSolutionOn_publicCoeffField_cubeSet_of_isForcedEquation
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {u : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    {g : Vec d → Vec d}
    (h : IsForcedEquation Q a u g) :
    IsH1DirichletRhsWeakSolutionOn (publicCoeffField Q a) (cubeSet Q)
      (publicH1ToCubeSet u) g := by
  have hopen :
      IsH1DirichletRhsWeakSolutionOn (publicCoeffField Q a) (openCubeSet Q)
        (castH1Domain (Ch02.cubeDomain_coe Q) u) g := by
    simpa [Ch02.cubeDomain_coe] using!
      isH1DirichletRhsWeakSolutionOn_publicCoeffField_of_isForcedEquation
        (Q := Q) (a := a) (u := u) (g := g) h
  simpa [publicH1ToCubeSet] using
    isH1DirichletRhsWeakSolutionOn_cubeSet_of_openCubeSet
      (Q := Q) (a := publicCoeffField Q a)
      (u := castH1Domain (Ch02.cubeDomain_coe Q) u) (g := g) hopen

theorem CoarseGrainingComparisonDatum.cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_const_mul_coarseFluxResponseRHSBound_descendant
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d} {g : Vec d → Vec d} {j : ℕ} {s : ℝ}
    (w : CoarseGrainingComparisonDatum Q a a0 g)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeBesovNegativeVectorSeminormTwo R s
        (fluxDefect (publicCoeffField Q a) a0.matrix w.u.grad) ≤
      (2 * zeroTraceDirichletCorrectedWeakFluxApexConstant d 1) *
        coarseFluxResponseRHSBound R
          (publicCoeffField Q a) a0.matrix s w.u.grad g := by
  let uR : H1Function (cubeSet R) :=
    ((publicH1ToCubeSet w.u).toOpenCubeSet.restrictToOpenSubcube hR).toCubeSet
  have hs_le : s ≤ 1 := hs_lt.le
  have hweakQ :
      IsH1DirichletRhsWeakSolutionOn (publicCoeffField Q a) (cubeSet Q)
        (publicH1ToCubeSet w.u) g :=
    isH1DirichletRhsWeakSolutionOn_publicCoeffField_cubeSet_of_isForcedEquation
      (Q := Q) (a := a) (u := w.u) (g := g) w.uWeakSolution
  have hweakR :
      IsH1DirichletRhsWeakSolutionOn (publicCoeffField Q a) (cubeSet R) uR g := by
    dsimp [uR]
    exact
      IsH1DirichletRhsWeakSolutionOn.restrict_cubeSet_of_mem_descendantsAtDepth
        hweakQ (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (memVectorL2_cubeSet_of_forceBesovRegularity hg) hR
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
    mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR
  have hresponseSum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity
            (publicCoeffField Q a) a0.matrix) :=
    homogenizationErrorOnCube_parent_publicCoeffField_descendant_infinity_one_terms_summable
      (a := a) hRscale a0.matrix hs
  have hdet :
      cubeBesovNegativeVectorSeminormTwo R s
          (fluxDefect (publicCoeffField Q a) a0.matrix uR.grad) ≤
        2 * zeroTraceDirichletCorrectedWeakFluxApexConstant d s *
          coarseFluxResponseRHSBound R
            (publicCoeffField Q a) a0.matrix s uR.grad g :=
    ZeroTraceDirichletCorrectorData.cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_h1DirichletRhsWeakSolutionOn_correctedWeakFlux_averagedCorrectorEnergy
      (Q := R) (a := publicCoeffField Q a) (a0 := a0.matrix) (s := s)
      (g := g) (v := uR)
      (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
      (lam0 := a0.lam) (Lam0 := a0.Lam)
      hs hs_le (publicCoeffField_isEllipticFieldOn_descendant_cubeSet Q a hR)
      a0.elliptic a0.isSymm hweakR (forceBesovRegularity_descendant hg hR)
      hresponseSum
  let B : ℝ :=
    coarseFluxResponseRHSBound R
      (publicCoeffField Q a) a0.matrix s w.u.grad g
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact coarseFluxResponseRHSBound_nonneg_of_bddAbove
      R (publicCoeffField Q a) a0.matrix w.u.grad g hs
      (forceBesovRegularity_descendant_partialSeminorms_bddAbove hg hR)
  have hM_le :
      zeroTraceDirichletCorrectedWeakFluxApexConstant d s ≤
        zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 := by
    have hdisplay :
        zeroTraceDirichletCorrectedWeakFluxApexDisplayScale d s ≤
          zeroTraceDirichletCorrectedWeakFluxApexDisplayScale d 1 := by
      unfold zeroTraceDirichletCorrectedWeakFluxApexDisplayScale
      have hpow :
          (3 : ℝ) ^ ((d : ℝ) + s) ≤
            (3 : ℝ) ^ ((d : ℝ) + 1) :=
        Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
      have hinner :
          (3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2 ≤
            (3 : ℝ) ^ ((d : ℝ) + 1) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg 2)
      exact mul_le_mul_of_nonneg_left hinner (by exact_mod_cast Nat.zero_le d)
    unfold zeroTraceDirichletCorrectedWeakFluxApexConstant
    nlinarith
  have hfactor :
      2 * zeroTraceDirichletCorrectedWeakFluxApexConstant d s ≤
        2 * zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 := by
    nlinarith
  calc
    cubeBesovNegativeVectorSeminormTwo R s
        (fluxDefect (publicCoeffField Q a) a0.matrix w.u.grad)
        ≤ 2 * zeroTraceDirichletCorrectedWeakFluxApexConstant d s * B := by
          simpa [uR, B, publicH1ToCubeSet_grad] using hdet
    _ ≤ (2 * zeroTraceDirichletCorrectedWeakFluxApexConstant d 1) * B :=
          mul_le_mul_of_nonneg_right hfactor hB_nonneg

theorem isMeanZeroNeumannRhsWeakSolution_publicCoeffField_cubeSet_of_isMeanZeroNeumannForcedEquation
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {w : H1MeanZeroFunction (Ch02.cubeDomain Q : Set (Vec d))}
    {g : Vec d → Vec d}
    (h : IsMeanZeroNeumannForcedEquation Q a w g) :
    IsMeanZeroNeumannRhsWeakSolution (publicCoeffField Q a) (cubeSet Q)
      (publicH1MeanZeroToCubeSet w) g := by
  have hopen :
      IsMeanZeroNeumannRhsWeakSolution (publicCoeffField Q a)
        (openCubeSet Q) (castH1MeanZeroDomain (Ch02.cubeDomain_coe Q) w) g := by
    simpa [Ch02.cubeDomain_coe] using!
      isMeanZeroNeumannRhsWeakSolution_publicCoeffField_of_isMeanZeroNeumannForcedEquation
        (Q := Q) (a := a) (w := w) (g := g) h
  simpa [publicH1MeanZeroToCubeSet] using
    isMeanZeroNeumannRhsWeakSolution_cubeSet_of_openCubeSet
      (Q := Q) (a := publicCoeffField Q a)
      (u := castH1MeanZeroDomain (Ch02.cubeDomain_coe Q) w) (g := g) hopen

theorem isMeanZeroNeumannRhsWeakSolution_publicCoeffField_cubeSet_of_neumannForcedCubeSolution
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d}
    (w : NeumannForcedCubeSolution Q a g) :
    IsMeanZeroNeumannRhsWeakSolution (publicCoeffField Q a) (cubeSet Q)
      (publicH1MeanZeroToCubeSet w.toH1MeanZero)
      (fun x => g x - cubeAverageVec Q g) :=
  isMeanZeroNeumannRhsWeakSolution_publicCoeffField_cubeSet_of_isMeanZeroNeumannForcedEquation
    (Q := Q) (a := a) (w := w.toH1MeanZero)
    (g := fun x => g x - cubeAverageVec Q g) w.weakSolution



end

end Ch03
end Book
end Homogenization
