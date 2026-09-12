/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SpecialPeriods9
public import LeanPool.HopfProblem.Foundations.SplitGroupExtension
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldGluing1
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology1
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Threefold.SpecialPeriods9
import all LeanPool.HopfProblem.Foundations.SplitGroupExtension

/-!
# Hopf problem: homology of x · threefold homology 2

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem ThreefoldHomologyCuspFibre.specialFibreToPiece_eq :
    ThreefoldOverlapMappingTorus.Cusp.specialFibreToPiece =
      fibreToFull ThreefoldOverlapMappingTorus.Cusp.specialData
        ThreefoldOverlapMappingTorus.Cusp.specialHeight :=
  rfl

private theorem ThreefoldHomologyCuspFibre.fibreToFilling_eq :
    ThreefoldOverlapMappingTorus.fibreToFilling Option.none =
      ThreefoldOverlapMappingTorus.Cusp.specialFibreToPiece := by
  rw [ThreefoldOverlapMappingTorus.fibreToFilling,
    ThreefoldOverlapMappingTorus.boundaryToFilling_cusp]
  rfl

private theorem ThreefoldHomologyCuspFibre.fibreToFilling_homology_surjective (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.fibreToFilling Option.none) n) := by
  rw [fibreToFilling_eq, specialFibreToPiece_eq]
  exact
    fibreToFull_homology_surjective ThreefoldOverlapMappingTorus.Cusp.specialData
      ThreefoldOverlapMappingTorus.Cusp.specialHeight n

private theorem ThreefoldHomologyCuspFibre.boundaryFillingHomologyMap_surjective (n : ℕ) :
    Function.Surjective (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none n) :=
  by
  intro a
  obtain ⟨b, hb⟩ := fibreToFilling_homology_surjective n a
  refine
    ⟨SingularMayerVietoris.singularHomologyMap
        (MappingTorus.HomologyCover.fibreInclusion
          (ThreefoldOverlapMappingTorus.monodromy Option.none))
        n b,
      ?_⟩
  exact
    (LinearMap.congr_fun
          (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_fibre Option.none n) b).trans
      hb

private def ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv (j : Elliptic.Kind)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some (Option.some j))) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.EllipticFilling.SpecialCentralSurface j) n :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
      (SpecialPeriods.Threefold.EllipticGeometry.pieceSurfaceHomotopyEquiv j) n).symm

private def ThreefoldHomology.Finiteness.ellipticPieceHomologyEquiv (j : Elliptic.Kind) (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some (Option.some j))) n ≃ₗ[ℤ]
      (Fin (Elliptic.HigherHomology.ellipticBettiNumber n) → ℤ) :=
  (ellipticPieceRetractionHomologyEquiv j n).trans
    (SpecialPeriods.EllipticFilling.specialCentralSurfaceHomologyCoordinates j n)

private theorem
    ThreefoldHomology.Finiteness.ellipticPieceHomology_free (j : Elliptic.Kind) (n : ℕ) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some (Option.some j))) n) :=
  Module.Free.of_equiv (ellipticPieceHomologyEquiv j n).symm

private theorem
    ThreefoldHomology.Finiteness.ellipticPieceHomology_finite (j : Elliptic.Kind) (n : ℕ) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some (Option.some j))) n) :=
  Module.Finite.of_surjective (ellipticPieceHomologyEquiv j n).symm.toLinearMap
    (ellipticPieceHomologyEquiv j n).symm.surjective

private theorem
    ThreefoldHomology.Finiteness.ellipticPieceHomology_finrank (j : Elliptic.Kind) (n : ℕ) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some (Option.some j))) n) =
      Elliptic.HigherHomology.ellipticBettiNumber n := by
  rw [(ellipticPieceHomologyEquiv j n).finrank_eq]
  simp

private theorem ThreefoldHomology.Finiteness.ellipticPieceHomology_subsingleton (j : Elliptic.Kind)
    {n : ℕ} (hn : 4 < n) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some (Option.some j))) n) := by
  have : Subsingleton (Fin (Elliptic.HigherHomology.ellipticBettiNumber n) → ℤ) := by
    rw [Elliptic.HigherHomology.ellipticBettiNumber_eq_zero_of_lt hn]
    infer_instance
  exact (ellipticPieceHomologyEquiv j n).injective.subsingleton

private def ThreefoldHomology.BoundaryFirst.latticeMonodromy : Option Elliptic.Kind → LatticeMatrix
  | none => M₀
  | some j => j.matrix

private def ThreefoldHomology.BoundaryFirst.latticeDifference (i : Option Elliptic.Kind) :
    Lattice →ₗ[ℤ] Lattice :=
  -((latticeMonodromy i - 1).mulVecLin)

private theorem ThreefoldHomology.BoundaryFirst.latticeDifference_apply (i : Option Elliptic.Kind)
    (w : Lattice) : latticeDifference i w = w - latticeMonodromy i *ᵥ w := by
  simp [latticeDifference]

private def ThreefoldHomology.BoundaryFirst.cuspCoinvariantMap : Lattice →ₗ[ℤ] (Fin 2 → ℤ)
    where
  toFun w := ![w 0, w 1]
  map_add' w z := by ext k; fin_cases k <;> rfl
  map_smul' a w := by ext k; fin_cases k <;> rfl

/-- The lattice coinvariant map for a cusp or elliptic boundary component. -/
public
def ThreefoldHomology.BoundaryFirst.latticeCoinvariantMap :
    Option Elliptic.Kind → Lattice →ₗ[ℤ] (Fin 2 → ℤ)
  | none => cuspCoinvariantMap
  | some j => Elliptic.coinvariantMap j

public
theorem ThreefoldHomology.BoundaryFirst.latticeCoinvariantMap_surjective
    (i : Option Elliptic.Kind) : Function.Surjective (latticeCoinvariantMap i) := by
  cases i with
  | none =>
    intro c
    refine ⟨![c 0, c 1, 0, 0], ?_⟩
    ext k
    fin_cases k <;> rfl
  | some j => exact Elliptic.coinvariantMap_surjective j

private theorem ThreefoldHomology.BoundaryFirst.latticeDifference_range (i : Option Elliptic.Kind) :
    LinearMap.range (latticeDifference i) = LinearMap.ker (latticeCoinvariantMap i) := by
  rw [latticeDifference, LinearMap.range_neg]
  cases i with
  | none =>
    ext w
    change (∃ v : Lattice, (M₀ - 1) *ᵥ v = w) ↔ cuspCoinvariantMap w = 0
    rw [M₀_sub_one_range]
    constructor
    · rintro ⟨h0, h1⟩
      ext k
      fin_cases k <;> assumption
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
  | some j => exact (Elliptic.coinvariantMap_ker_eq_range j).symm

private def ThreefoldHomology.BoundaryFirst.latticeCokernelEquiv (i : Option Elliptic.Kind) :
    (Lattice ⧸ LinearMap.range (latticeDifference i)) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (Submodule.quotEquivOfEq _ _ (latticeDifference_range i)).trans
    ((latticeCoinvariantMap i).quotKerEquivOfSurjective (latticeCoinvariantMap_surjective i))

end Mathoverflow1973

end
