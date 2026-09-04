/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyOfX.ThreefoldHomologyStarCoproduct
public import LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology5
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.CuspFibre.CuspSpecialization
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.HomologyOfX.CuspCoinvariants
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology1
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Threefold.SpecialPeriods9
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology2
import all LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus2
import all LeanPool.HopfProblem.PeriodFamily.Core3
import all LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyAlgebra
import all LeanPool.HopfProblem.PeriodFamily.Core4
import all LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyLattice
import all LeanPool.HopfProblem.PeriodFamily.Core5
import all LeanPool.HopfProblem.Elliptic.Core7
import all LeanPool.HopfProblem.PeriodFamily.Core6
import all LeanPool.HopfProblem.PeriodFamily.Core7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods11
import all LeanPool.HopfProblem.Elliptic.Core8
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology5
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomologyStarCoproduct

/-!
# Hopf problem: homology of x · threefold homology 3

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

private theorem ThreefoldHomology.Finiteness.regularHomology_free (n : ℕ) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n) :=
  PeriodFamily.Canonical.specialRegularHomology_free n

private theorem ThreefoldHomology.Finiteness.regularHomology_finite (n : ℕ) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n) :=
  PeriodFamily.Canonical.specialRegularHomology_finite n

private theorem ThreefoldHomology.Finiteness.regularHomology_finrank (n : ℕ) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n) =
      PeriodFamily.Homology.familyBetti n :=
  PeriodFamily.Canonical.specialRegularHomology_finrank n

private theorem ThreefoldHomology.Finiteness.regularHomology_isZero {n : ℕ} (hn : 5 < n) :
    CategoryTheory.Limits.IsZero
      (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n) :=
  PeriodFamily.Canonical.specialRegularHomology_isZero_of_lt hn

private theorem ThreefoldHomology.Finiteness.regularHomology_subsingleton {n : ℕ} (hn : 5 < n) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n) :=
  ModuleCat.isZero_iff_subsingleton.mp (regularHomology_isZero hn)

private theorem
    ThreefoldHomologyFinitenessAlgebra.noetherian_of_exact {B H C : Type u} [AddCommGroup B]
    [AddCommGroup H] [AddCommGroup C] [Module ℤ B] [Module ℤ H] [Module ℤ C] (f : B →ₗ[ℤ] H)
    (g : H →ₗ[ℤ] C) (h : Function.Exact f g) [Module.Finite ℤ B] [Module.Finite ℤ C] :
    IsNoetherian ℤ H :=
  isNoetherian_of_range_eq_ker f g h.linearMap_ker_eq.symm

private theorem ThreefoldHomologyFinitenessAlgebra.finite_of_exact {B H C : Type u} [AddCommGroup B]
    [AddCommGroup H] [AddCommGroup C] [Module ℤ B] [Module ℤ H] [Module ℤ C] (f : B →ₗ[ℤ] H)
    (g : H →ₗ[ℤ] C) (h : Function.Exact f g) [Module.Finite ℤ B] [Module.Finite ℤ C] :
    Module.Finite ℤ H := by
  have := noetherian_of_exact f g h
  infer_instance

private theorem
    ThreefoldHomologyFinitenessAlgebra.eq_zero_of_exact {B H C : Type u} [AddCommGroup B]
    [AddCommGroup H] [AddCommGroup C] [Module ℤ B] [Module ℤ H] [Module ℤ C] (f : B →ₗ[ℤ] H)
    (g : H →ₗ[ℤ] C) (h : Function.Exact f g) [Subsingleton B] [Subsingleton C] (a : H) : a = 0 := by
  obtain ⟨b, hb⟩ := (h a).mp (Subsingleton.elim (g a) 0)
  exact hb.symm.trans ((congrArg f (Subsingleton.elim b 0)).trans (map_zero f))

public
theorem
    ThreefoldHomologyFinitenessAlgebra.subsingleton_of_exact {B H C : Type u} [AddCommGroup B]
    [AddCommGroup H] [AddCommGroup C] [Module ℤ B] [Module ℤ H] [Module ℤ C] (f : B →ₗ[ℤ] H)
    (g : H →ₗ[ℤ] C) (h : Function.Exact f g) [Subsingleton B] [Subsingleton C] : Subsingleton H :=
  ⟨fun a b => (eq_zero_of_exact f g h a).trans (eq_zero_of_exact f g h b).symm⟩

private theorem
    ThreefoldHomologyFinitenessMappingTorus.fibre_wang_exact (f : RealTorus₄ ≃ₜ RealTorus₄)
    (n : ℕ) :
    Function.Exact (MappingTorusHomology.fibreHomologyMap f (n + 1))
      (MappingTorusHomology.wangBoundary f n) :=
  LinearMap.exact_iff.mpr (MappingTorusHomology.wang_exact_at_mappingTorus f n).symm

private theorem
    ThreefoldHomologyFinitenessMappingTorus.homology_finite (f : RealTorus₄ ≃ₜ RealTorus₄)
    (n : ℕ) : Module.Finite ℤ (SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) n) :=
  by
  cases n with
  | zero =>
    let := PeriodTorusHigherHomology.realTorus_homology_finite 0
    exact
      Module.Finite.of_surjective (MappingTorusHomology.fibreHomologyMap f 0)
        (MappingTorusHomology.fibreHomologyMap_zero_surjective f)
  | succ n =>
    let := PeriodTorusHigherHomology.realTorus_homology_finite (n + 1)
    let := PeriodTorusHigherHomology.realTorus_homology_finite n
    exact
      ThreefoldHomologyFinitenessAlgebra.finite_of_exact
        (MappingTorusHomology.fibreHomologyMap f (n + 1)) (MappingTorusHomology.wangBoundary f n)
        (fibre_wang_exact f n)

private theorem ThreefoldHomologyFinitenessMappingTorus.homology_subsingleton_of_lt
    (f : RealTorus₄ ≃ₜ RealTorus₄) {n : ℕ} (hn : 5 < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) n) := by
  cases n with
  | zero => omega
  | succ
    n =>
    let := PeriodTorusHigherHomology.realTorus_homology_subsingleton_of_lt (n := n + 1) (by omega)
    let := PeriodTorusHigherHomology.realTorus_homology_subsingleton_of_lt (n := n) (by omega)
    exact
      ThreefoldHomologyFinitenessAlgebra.subsingleton_of_exact
        (MappingTorusHomology.fibreHomologyMap f (n + 1)) (MappingTorusHomology.wangBoundary f n)
        (fibre_wang_exact f n)

private abbrev ThreefoldHomology.StarOverlapHomology (n : ℕ) :=
  ∀ i : SpecialPeriods.Threefold.Puncture,
    SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n

private abbrev ThreefoldHomology.StarFillingHomology (n : ℕ) :=
  ∀ i : SpecialPeriods.Threefold.Puncture,
    SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.localPiece (Option.some i)) n

private abbrev ThreefoldHomology.StarPairHomology (n : ℕ) :=
  SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n ×
    StarFillingHomology n

private def ThreefoldHomology.starOverlapToRegularHomologyMap (n : ℕ) :
    StarOverlapHomology n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n
    where
  toFun
    a :=
    ∑ i : SpecialPeriods.Threefold.Puncture,
      SingularMayerVietoris.singularHomologyMap (overlapToRegularFamily i) n (a i)
  map_add' a b := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r
    a := by
    simp only [Pi.smul_apply, map_zsmul, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (int_smul_eq_zsmul ..).symm

private def ThreefoldHomology.starOverlapToFillingsHomologyMap (n : ℕ) :
    StarOverlapHomology n →ₗ[ℤ] StarFillingHomology n
    where
  toFun a i := SingularMayerVietoris.singularHomologyMap (overlapToFilling i) n (a i)
  map_add' a b := by ext i; exact map_add _ _ _
  map_smul' r
    a := by
    ext i
    simp only [Pi.smul_apply, map_zsmul, RingHom.id_apply]

private def ThreefoldHomology.starLeftHomologyMap (n : ℕ) :
    StarOverlapHomology n →ₗ[ℤ] StarPairHomology n :=
  ((starOverlapToRegularHomologyMap n).toAddMonoidHom.prod
      (-(starOverlapToFillingsHomologyMap n).toAddMonoidHom)).toIntLinearMap

private def ThreefoldHomology.starFillingsToSpaceHomologyMap (n : ℕ) :
    StarFillingHomology n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space n
    where
  toFun
    a :=
    ∑ i : SpecialPeriods.Threefold.Puncture,
      SingularMayerVietoris.singularHomologyMap (originalPieceInclusion (Option.some i)) n (a i)
  map_add' a b := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r
    a := by
    simp only [Pi.smul_apply, map_zsmul, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (int_smul_eq_zsmul ..).symm

private def ThreefoldHomology.starRightHomologyMap (n : ℕ) :
    StarPairHomology n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space n := by
  let f :=
    (SingularMayerVietoris.singularHomologyMap originalRegularInclusion n).toAddMonoidHom.coprod
      (starFillingsToSpaceHomologyMap n).toAddMonoidHom
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' r
        a := by
        convert! f.map_zsmul r a using 1
        exact int_smul_eq_zsmul .. }

@[simp]
private theorem ThreefoldHomology.starOverlapToRegularHomologyMap_apply (n : ℕ)
    (a : StarOverlapHomology n) :
    starOverlapToRegularHomologyMap n a =
      ∑ i : SpecialPeriods.Threefold.Puncture,
        SingularMayerVietoris.singularHomologyMap (overlapToRegularFamily i) n (a i) :=
  rfl

@[simp]
private theorem ThreefoldHomology.starLeftHomologyMap_apply (n : ℕ) (a : StarOverlapHomology n) :
    starLeftHomologyMap n a =
      (∑ i : SpecialPeriods.Threefold.Puncture,
          SingularMayerVietoris.singularHomologyMap (overlapToRegularFamily i) n (a i),
        fun i => -SingularMayerVietoris.singularHomologyMap (overlapToFilling i) n (a i)) :=
  rfl

@[simp]
private theorem ThreefoldHomology.starFillingsToSpaceHomologyMap_apply (n : ℕ)
    (a : StarFillingHomology n) :
    starFillingsToSpaceHomologyMap n a =
      ∑ i : SpecialPeriods.Threefold.Puncture,
        SingularMayerVietoris.singularHomologyMap (originalPieceInclusion (Option.some i)) n
          (a i) :=
  rfl

private theorem ThreefoldHomology.starLeftHomologyMap_single (n : ℕ)
    (i : SpecialPeriods.Threefold.Puncture)
    (a : SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n) :
    starLeftHomologyMap n (Pi.single i a) =
      (SingularMayerVietoris.singularHomologyMap (overlapToRegularFamily i) n a,
        Pi.single i (-SingularMayerVietoris.singularHomologyMap (overlapToFilling i) n a)) := by
  rw [starLeftHomologyMap_apply]
  apply Prod.ext
  · rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, map_zero]
    · simp
  · funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne h]

private theorem ThreefoldHomology.starRightHomologyMap_single (n : ℕ)
    (i : SpecialPeriods.Threefold.Puncture)
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n)
    (b :
      SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.localPiece (Option.some i))
        n) :
    starRightHomologyMap n (a, Pi.single i b) =
      SingularMayerVietoris.singularHomologyMap originalRegularInclusion n a +
        SingularMayerVietoris.singularHomologyMap (originalPieceInclusion (Option.some i)) n b := by
  change
    SingularMayerVietoris.singularHomologyMap originalRegularInclusion n a +
        starFillingsToSpaceHomologyMap n (Pi.single i b) =
      _
  rw [starFillingsToSpaceHomologyMap_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

private def ThreefoldHomology.Finiteness.cuspPieceHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) n ≃ₗ[ℤ]
      (Fin (CuspCentralHomology.centralBetti n) → ℤ) :=
  ThreefoldHomologyFinitenessCusp.fullHomologyCoordinates
    ThreefoldOverlapMappingTorus.Cusp.specialData n

private theorem ThreefoldHomology.Finiteness.cuspPieceHomology_free (n : ℕ) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) n) :=
  Module.Free.of_equiv (cuspPieceHomologyEquiv n).symm

private theorem ThreefoldHomology.Finiteness.cuspPieceHomology_finite (n : ℕ) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) n) :=
  Module.Finite.of_surjective (cuspPieceHomologyEquiv n).symm.toLinearMap
    (cuspPieceHomologyEquiv n).symm.surjective

private theorem ThreefoldHomology.Finiteness.cuspPieceHomology_finrank (n : ℕ) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) n) =
      CuspCentralHomology.centralBetti n := by
  rw [(cuspPieceHomologyEquiv n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

private theorem ThreefoldHomology.Finiteness.cuspPieceHomology_subsingleton {n : ℕ} (hn : 4 < n) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) n) :=
  ThreefoldHomologyFinitenessCusp.fullHomology_subsingleton_of_four_lt
    ThreefoldOverlapMappingTorus.Cusp.specialData hn

private theorem ThreefoldHomology.Finiteness.fillingHomology_finite
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some i)) n) := by
  cases i with
  | none => exact cuspPieceHomology_finite n
  | some j => exact ellipticPieceHomology_finite j n

private theorem ThreefoldHomology.Finiteness.fillingHomology_subsingleton
    (i : SpecialPeriods.Threefold.Puncture) {n : ℕ} (hn : 4 < n) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some i)) n) := by
  cases i with
  | none => exact cuspPieceHomology_subsingleton hn
  | some j => exact ellipticPieceHomology_subsingleton j hn

private theorem ThreefoldHomology.Finiteness.overlapHomology_finite
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n) := by
  have :=
    ThreefoldHomologyFinitenessMappingTorus.homology_finite
      (ThreefoldOverlapMappingTorus.monodromy i) n
  exact
    Module.Finite.of_surjective
      (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).symm.toLinearMap
      (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).symm.surjective

private theorem ThreefoldHomology.Finiteness.overlapHomology_subsingleton
    (i : SpecialPeriods.Threefold.Puncture) {n : ℕ} (hn : 5 < n) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n) := by
  have :=
    ThreefoldHomologyFinitenessMappingTorus.homology_subsingleton_of_lt
      (ThreefoldOverlapMappingTorus.monodromy i) hn
  refine ⟨fun a b => (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).injective ?_⟩
  exact Subsingleton.elim _ _

private theorem ThreefoldHomology.Finiteness.starFillingHomology_finite (n : ℕ) :
    Module.Finite ℤ (ThreefoldHomology.StarFillingHomology n) := by
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Module.Finite ℤ
        (SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some i)) n) :=
    fun i => fillingHomology_finite i n
  exact
    finite_pi_int
      (fun i : SpecialPeriods.Threefold.Puncture =>
        SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some i)) n)

private theorem ThreefoldHomology.Finiteness.starOverlapHomology_finite (n : ℕ) :
    Module.Finite ℤ (ThreefoldHomology.StarOverlapHomology n) := by
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Module.Finite ℤ
        (SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n) :=
    fun i => overlapHomology_finite i n
  exact
    finite_pi_int
      (fun i : SpecialPeriods.Threefold.Puncture =>
        SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n)

private theorem ThreefoldHomology.Finiteness.starPairHomology_finite (n : ℕ) :
    Module.Finite ℤ (ThreefoldHomology.StarPairHomology n) := by
  have := regularHomology_finite n
  have := starFillingHomology_finite n
  exact
    finite_prod_int
      (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n)
      (ThreefoldHomology.StarFillingHomology n)

private theorem ThreefoldHomology.Finiteness.starFillingHomology_subsingleton {n : ℕ} (hn : 4 < n) :
    Subsingleton (ThreefoldHomology.StarFillingHomology n) := by
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Subsingleton
        (SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some i)) n) :=
    fun i => fillingHomology_subsingleton i hn
  infer_instance

private theorem ThreefoldHomology.Finiteness.starOverlapHomology_subsingleton {n : ℕ} (hn : 5 < n) :
    Subsingleton (ThreefoldHomology.StarOverlapHomology n) := by
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Subsingleton
        (SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n) :=
    fun i => overlapHomology_subsingleton i hn
  infer_instance

private theorem ThreefoldHomology.Finiteness.starPairHomology_subsingleton {n : ℕ} (hn : 5 < n) :
    Subsingleton (ThreefoldHomology.StarPairHomology n) := by
  have := regularHomology_subsingleton hn
  have := starFillingHomology_subsingleton (by omega : 4 < n)
  infer_instance

private def ThreefoldHomology.disjointOpenUnionHomeomorph {ι X : Type*} [TopologicalSpace X]
    (U : ι → TopologicalSpace.Opens X)
    (h : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X))) :
    (Σ i, U i) ≃ₜ (⋃ i, (U i : Set X)) := by
  refine
    (Equiv.ofBijective _
          (Set.sigmaToiUnion_bijective (fun i => (U i : Set X)) h)).toHomeomorphOfContinuousOpen
      ?_ ?_
  · exact continuous_sigma (fun i => continuous_subtype_val.subtype_mk _)
  · exact isOpenMap_sigma.mpr (fun i => (U i).isOpen.isOpenMap_subtype_val.subtype_mk _)

private def
    ThreefoldHomology.starFillings : TopologicalSpace.Opens SpecialPeriods.Threefold.Space :=
  ⟨⋃ i : SpecialPeriods.Threefold.Puncture,
      (SpecialPeriods.Threefold.liftedPatch (Option.some i) : Set SpecialPeriods.Threefold.Space),
    isOpen_iUnion (fun i => (SpecialPeriods.Threefold.liftedPatch (Option.some i)).isOpen)⟩

private def ThreefoldHomology.starOverlap : TopologicalSpace.Opens SpecialPeriods.Threefold.Space :=
  SpecialPeriods.Threefold.liftedPatch Option.none ⊓ starFillings

@[simp]
private theorem ThreefoldHomology.mem_starFillings (x : SpecialPeriods.Threefold.Space) :
    x ∈ starFillings ↔
      ∃ i : SpecialPeriods.Threefold.Puncture,
        x ∈ SpecialPeriods.Threefold.liftedPatch (Option.some i) :=
  Set.mem_iUnion

private theorem ThreefoldHomology.filling_le_starFillings (i : SpecialPeriods.Threefold.Puncture) :
    (SpecialPeriods.Threefold.liftedPatch (Option.some i) : Set SpecialPeriods.Threefold.Space) ⊆
      starFillings := by
  intro x hx
  exact (mem_starFillings x).mpr ⟨i, hx⟩

private theorem ThreefoldHomology.star_cover :
    (SpecialPeriods.Threefold.liftedPatch Option.none : Set SpecialPeriods.Threefold.Space) ∪
        starFillings =
      Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x _
  have hx :
    x ∈
      ⋃ i : SpecialPeriods.Threefold.Index,
        (SpecialPeriods.Threefold.liftedPatch i : Set SpecialPeriods.Threefold.Space) := by
    rw [SpecialPeriods.Threefold.liftedPatch_iUnion]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  cases i with
  | none => exact Or.inl hi
  | some i => exact Or.inr (filling_le_starFillings i hi)

private theorem ThreefoldHomology.starOverlap_eq_iUnion :
    (starOverlap : Set SpecialPeriods.Threefold.Space) =
      ⋃ i : SpecialPeriods.Threefold.Puncture,
        (SpecialPeriods.Threefold.RegularOverlap i : Set SpecialPeriods.Threefold.Space) := by
  change
    (SpecialPeriods.Threefold.liftedPatch Option.none : Set SpecialPeriods.Threefold.Space) ∩
        (⋃ i : SpecialPeriods.Threefold.Puncture,
          (SpecialPeriods.Threefold.liftedPatch (Option.some i) :
            Set SpecialPeriods.Threefold.Space)) =
      ⋃ i : SpecialPeriods.Threefold.Puncture,
        (SpecialPeriods.Threefold.liftedPatch Option.none : Set SpecialPeriods.Threefold.Space) ∩
          SpecialPeriods.Threefold.liftedPatch (Option.some i)
  exact Set.inter_iUnion _ _

private theorem ThreefoldHomology.regularOverlap_pairwise_disjoint :
    Pairwise
      (fun i j : SpecialPeriods.Threefold.Puncture =>
        Disjoint (SpecialPeriods.Threefold.RegularOverlap i : Set SpecialPeriods.Threefold.Space)
          (SpecialPeriods.Threefold.RegularOverlap j : Set SpecialPeriods.Threefold.Space)) := by
  intro i j hij
  exact
    (SpecialPeriods.Threefold.liftedFilling_disjoint hij).mono Set.inter_subset_right
      Set.inter_subset_right

private def ThreefoldHomology.sigmaOriginalFillingHomeomorph :
    (Σ i : SpecialPeriods.Threefold.Puncture,
        SpecialPeriods.Threefold.localPiece (Option.some i)) ≃ₜ
      (Σ i : SpecialPeriods.Threefold.Puncture,
        SpecialPeriods.Threefold.liftedPatch (Option.some i))
    where
  toEquiv := Equiv.sigmaCongrRight (fun i => (originalPatchHomeomorph (Option.some i)).toEquiv)
  continuous_toFun :=
    continuous_sigma
      (fun i => continuous_sigmaMk.comp (originalPatchHomeomorph (Option.some i)).continuous)
  continuous_invFun :=
    continuous_sigma
      (fun i => continuous_sigmaMk.comp (originalPatchHomeomorph (Option.some i)).symm.continuous)

private def ThreefoldHomology.starFillingsHomeomorph :
    (Σ i : SpecialPeriods.Threefold.Puncture,
        SpecialPeriods.Threefold.localPiece (Option.some i)) ≃ₜ
      starFillings :=
  sigmaOriginalFillingHomeomorph.trans
    (disjointOpenUnionHomeomorph
      (fun i : SpecialPeriods.Threefold.Puncture =>
        SpecialPeriods.Threefold.liftedPatch (Option.some i))
      (fun _ _ hij => SpecialPeriods.Threefold.liftedFilling_disjoint hij))

private def ThreefoldHomology.starOverlapHomeomorph :
    (Σ i : SpecialPeriods.Threefold.Puncture, SpecialPeriods.Threefold.RegularOverlap i) ≃ₜ
      starOverlap :=
  (disjointOpenUnionHomeomorph
        (fun i : SpecialPeriods.Threefold.Puncture =>
          SpecialPeriods.Threefold.liftedPatch Option.none ⊓
            SpecialPeriods.Threefold.liftedPatch (Option.some i))
        regularOverlap_pairwise_disjoint).trans
    (Homeomorph.setCongr starOverlap_eq_iUnion.symm)

private def ThreefoldHomology.fillingToStar (i : SpecialPeriods.Threefold.Puncture) :
    C(SpecialPeriods.Threefold.localPiece (Option.some i), starFillings) :=
  (ContinuousMap.inclusion (filling_le_starFillings i)).comp
    (originalPatchHomeomorph (Option.some i) :
      C(SpecialPeriods.Threefold.localPiece (Option.some i),
        SpecialPeriods.Threefold.liftedPatch (Option.some i)))

private def ThreefoldHomology.overlapToStar (i : SpecialPeriods.Threefold.Puncture) :
    C(SpecialPeriods.Threefold.RegularOverlap i, starOverlap) :=
  ⟨fun x => ⟨x.val, x.property.1, filling_le_starFillings i x.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩

private def ThreefoldHomology.starOverlapToRegularPatch :
    C(starOverlap, SpecialPeriods.Threefold.liftedPatch Option.none) :=
  ContinuousMap.inclusion Set.inter_subset_left

private def ThreefoldHomology.starOverlapToFillings : C(starOverlap, starFillings) :=
  ContinuousMap.inclusion Set.inter_subset_right

private def ThreefoldHomology.starOverlapToRegular :
    C(starOverlap, SpecialPeriods.Threefold.SpecialRegularFamily) :=
  (originalRegularPatchHomeomorph.symm :
        C(SpecialPeriods.Threefold.liftedPatch Option.none,
          SpecialPeriods.Threefold.SpecialRegularFamily)).comp
    starOverlapToRegularPatch

private theorem ThreefoldHomology.starOverlapToRegular_overlapToStar
    (i : SpecialPeriods.Threefold.Puncture) :
    starOverlapToRegular.comp (overlapToStar i) = overlapToRegularFamily i :=
  rfl

private theorem ThreefoldHomology.starOverlapToFillings_overlapToStar
    (i : SpecialPeriods.Threefold.Puncture) :
    starOverlapToFillings.comp (overlapToStar i) = (fillingToStar i).comp (overlapToFilling i) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact (inclusion_overlapToFilling i x).symm

private theorem ThreefoldHomology.fillingToStar_ambient (i : SpecialPeriods.Threefold.Puncture) :
    (SingularMayerVietoris.subtypeInclusion
            (starFillings : Set SpecialPeriods.Threefold.Space)).comp
        (fillingToStar i) =
      originalPieceInclusion (Option.some i) :=
  rfl

private theorem
    ThreefoldHomology.starFillingsHomeomorph_sigmaMk (i : SpecialPeriods.Threefold.Puncture) :
    (starFillingsHomeomorph :
            C((Σ j : SpecialPeriods.Threefold.Puncture,
                SpecialPeriods.Threefold.localPiece (Option.some j)),
              starFillings)).comp
        (ContinuousMap.sigmaMk i) =
      fillingToStar i := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

private theorem
    ThreefoldHomology.starOverlapHomeomorph_sigmaMk (i : SpecialPeriods.Threefold.Puncture) :
    (starOverlapHomeomorph :
            C((Σ j : SpecialPeriods.Threefold.Puncture,
                SpecialPeriods.Threefold.RegularOverlap j),
              starOverlap)).comp
        (ContinuousMap.sigmaMk i) =
      overlapToStar i := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

private def ThreefoldHomology.starRegularHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.liftedPatch Option.none)
        n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n :=
  PeriodTorusHigherHomology.homeomorphHomologyEquiv originalRegularPatchHomeomorph.symm n

private def ThreefoldHomology.starFillingsHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology starFillings n ≃ₗ[ℤ] StarFillingHomology n :=
  ((PeriodTorusHigherHomology.homeomorphHomologyEquiv starFillingsHomeomorph.symm
          n).toAddEquiv.trans
      (ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv
          (fun i : SpecialPeriods.Threefold.Puncture =>
            SpecialPeriods.Threefold.localPiece (Option.some i))
          n).toAddEquiv).toIntLinearEquiv

private def ThreefoldHomology.starOverlapHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology starOverlap n ≃ₗ[ℤ] StarOverlapHomology n :=
  ((PeriodTorusHigherHomology.homeomorphHomologyEquiv starOverlapHomeomorph.symm
          n).toAddEquiv.trans
      (ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv
          (fun i : SpecialPeriods.Threefold.Puncture => SpecialPeriods.Threefold.RegularOverlap i)
          n).toAddEquiv).toIntLinearEquiv

private def ThreefoldHomology.starPairHomologyEquiv (n : ℕ) :
    (SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.liftedPatch Option.none) n ×
        SingularMayerVietoris.SingularHomology starFillings n) ≃ₗ[ℤ]
      StarPairHomology n :=
  ((starRegularHomologyEquiv n).toAddEquiv.prodCongr
      (starFillingsHomologyEquiv n).toAddEquiv).toIntLinearEquiv

@[simp]
private theorem ThreefoldHomology.starRegularHomologyEquiv_apply (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.liftedPatch Option.none)
        n) :
    starRegularHomologyEquiv n a =
      SingularMayerVietoris.singularHomologyMap
        (originalRegularPatchHomeomorph.symm :
          C(SpecialPeriods.Threefold.liftedPatch Option.none,
            SpecialPeriods.Threefold.SpecialRegularFamily))
        n a :=
  rfl

@[simp]
private theorem ThreefoldHomology.starFillingsHomologyEquiv_symm_apply (n : ℕ)
    (a : StarFillingHomology n) :
    (starFillingsHomologyEquiv n).symm a =
      SingularMayerVietoris.singularHomologyMap
        (starFillingsHomeomorph :
          C((Σ i : SpecialPeriods.Threefold.Puncture,
              SpecialPeriods.Threefold.localPiece (Option.some i)),
            starFillings))
        n
        ((ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv
              (fun i : SpecialPeriods.Threefold.Puncture =>
                SpecialPeriods.Threefold.localPiece (Option.some i))
              n).symm
          a) :=
  rfl

@[simp]
private theorem ThreefoldHomology.starOverlapHomologyEquiv_symm_apply (n : ℕ)
    (a : StarOverlapHomology n) :
    (starOverlapHomologyEquiv n).symm a =
      SingularMayerVietoris.singularHomologyMap
        (starOverlapHomeomorph :
          C((Σ i : SpecialPeriods.Threefold.Puncture, SpecialPeriods.Threefold.RegularOverlap i),
            starOverlap))
        n
        ((ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv
              (fun i : SpecialPeriods.Threefold.Puncture =>
                SpecialPeriods.Threefold.RegularOverlap i)
              n).symm
          a) :=
  rfl

private theorem ThreefoldHomology.starFillingsHomologyEquiv_symm_single (n : ℕ)
    (i : SpecialPeriods.Threefold.Puncture)
    (a :
      SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.localPiece (Option.some i))
        n) :
    (starFillingsHomologyEquiv n).symm (Pi.single i a) =
      SingularMayerVietoris.singularHomologyMap (fillingToStar i) n a := by
  rw [starFillingsHomologyEquiv_symm_apply,
    ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv_symm_single]
  change
    SingularMayerVietoris.singularHomologyMap
        (starFillingsHomeomorph :
          C((Σ i : SpecialPeriods.Threefold.Puncture,
              SpecialPeriods.Threefold.localPiece (Option.some i)),
            starFillings))
        n (SingularMayerVietoris.singularHomologyMap (ContinuousMap.sigmaMk i) n a) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    starFillingsHomeomorph_sigmaMk]

private theorem ThreefoldHomology.starOverlapHomologyEquiv_symm_single (n : ℕ)
    (i : SpecialPeriods.Threefold.Puncture)
    (a : SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n) :
    (starOverlapHomologyEquiv n).symm (Pi.single i a) =
      SingularMayerVietoris.singularHomologyMap (overlapToStar i) n a := by
  rw [starOverlapHomologyEquiv_symm_apply,
    ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv_symm_single]
  change
    SingularMayerVietoris.singularHomologyMap
        (starOverlapHomeomorph :
          C((Σ i : SpecialPeriods.Threefold.Puncture, SpecialPeriods.Threefold.RegularOverlap i),
            starOverlap))
        n (SingularMayerVietoris.singularHomologyMap (ContinuousMap.sigmaMk i) n a) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    starOverlapHomeomorph_sigmaMk]

@[simp]
private theorem ThreefoldHomology.starFillingsHomologyEquiv_inclusion (n : ℕ)
    (i : SpecialPeriods.Threefold.Puncture)
    (a :
      SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.localPiece (Option.some i))
        n) :
    starFillingsHomologyEquiv n
        (SingularMayerVietoris.singularHomologyMap (fillingToStar i) n a) =
      Pi.single i a := by
  apply (starFillingsHomologyEquiv n).symm.injective
  rw [LinearEquiv.symm_apply_apply, starFillingsHomologyEquiv_symm_single]

@[simp]
private theorem ThreefoldHomology.starOverlapHomologyEquiv_inclusion (n : ℕ)
    (i : SpecialPeriods.Threefold.Puncture)
    (a : SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n) :
    starOverlapHomologyEquiv n (SingularMayerVietoris.singularHomologyMap (overlapToStar i) n a) =
      Pi.single i a := by
  apply (starOverlapHomologyEquiv n).symm.injective
  rw [LinearEquiv.symm_apply_apply, starOverlapHomologyEquiv_symm_single]

private theorem
    ThreefoldHomology.starFillingsHomologyEquiv_symm_sum (n : ℕ) (a : StarFillingHomology n) :
    (starFillingsHomologyEquiv n).symm a =
      ∑ i : SpecialPeriods.Threefold.Puncture,
        SingularMayerVietoris.singularHomologyMap (fillingToStar i) n (a i) := by
  conv_lhs => rw [← Finset.univ_sum_single a]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact starFillingsHomologyEquiv_symm_single n i (a i)

private theorem
    ThreefoldHomology.starOverlapHomologyEquiv_symm_sum (n : ℕ) (a : StarOverlapHomology n) :
    (starOverlapHomologyEquiv n).symm a =
      ∑ i : SpecialPeriods.Threefold.Puncture,
        SingularMayerVietoris.singularHomologyMap (overlapToStar i) n (a i) := by
  conv_lhs => rw [← Finset.univ_sum_single a]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact starOverlapHomologyEquiv_symm_single n i (a i)

private theorem ThreefoldHomology.starFillingsHomologyEquiv_decomposition (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology starFillings n) :
    a =
      ∑ i : SpecialPeriods.Threefold.Puncture,
        SingularMayerVietoris.singularHomologyMap (fillingToStar i) n
          (starFillingsHomologyEquiv n a i) := by
  have h := starFillingsHomologyEquiv_symm_sum n (starFillingsHomologyEquiv n a)
  rwa [LinearEquiv.symm_apply_apply] at h

private theorem ThreefoldHomology.starOverlapHomologyEquiv_decomposition (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology starOverlap n) :
    a =
      ∑ i : SpecialPeriods.Threefold.Puncture,
        SingularMayerVietoris.singularHomologyMap (overlapToStar i) n
          (starOverlapHomologyEquiv n a i) := by
  have h := starOverlapHomologyEquiv_symm_sum n (starOverlapHomologyEquiv n a)
  rwa [LinearEquiv.symm_apply_apply] at h

private theorem ThreefoldHomology.starFillingsHomology_hom_ext (n : ℕ) {M : Type} [AddCommGroup M]
    [Module ℤ M] (f g : SingularMayerVietoris.SingularHomology starFillings n →ₗ[ℤ] M)
    (h :
      ∀ (i : SpecialPeriods.Threefold.Puncture)
        (a :
          SingularMayerVietoris.SingularHomology
            (SpecialPeriods.Threefold.localPiece (Option.some i)) n),
        f (SingularMayerVietoris.singularHomologyMap (fillingToStar i) n a) =
          g (SingularMayerVietoris.singularHomologyMap (fillingToStar i) n a)) :
    f = g := by
  apply LinearMap.ext
  intro a
  rw [starFillingsHomologyEquiv_decomposition n a, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun i _ => h i _)

private theorem ThreefoldHomology.starOverlapHomology_hom_ext (n : ℕ) {M : Type} [AddCommGroup M]
    [Module ℤ M] (f g : SingularMayerVietoris.SingularHomology starOverlap n →ₗ[ℤ] M)
    (h :
      ∀ (i : SpecialPeriods.Threefold.Puncture)
        (a :
          SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n),
        f (SingularMayerVietoris.singularHomologyMap (overlapToStar i) n a) =
          g (SingularMayerVietoris.singularHomologyMap (overlapToStar i) n a)) :
    f = g := by
  apply LinearMap.ext
  intro a
  rw [starOverlapHomologyEquiv_decomposition n a, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun i _ => h i _)

private theorem ThreefoldHomology.starRegularHomologyEquiv_ambient (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap originalRegularInclusion n).comp
        (starRegularHomologyEquiv n).toLinearMap =
      SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion
          (SpecialPeriods.Threefold.liftedPatch Option.none : Set SpecialPeriods.Threefold.Space))
        n := by
  change
    (SingularMayerVietoris.singularHomologyMap originalRegularInclusion n).comp
        (SingularMayerVietoris.singularHomologyMap
          (originalRegularPatchHomeomorph.symm :
            C(SpecialPeriods.Threefold.liftedPatch Option.none,
              SpecialPeriods.Threefold.SpecialRegularFamily))
          n) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  apply
    congrArg
      (fun f :
          C(SpecialPeriods.Threefold.liftedPatch Option.none, SpecialPeriods.Threefold.Space) =>
        SingularMayerVietoris.singularHomologyMap f n)
  apply ContinuousMap.ext
  intro x
  exact congrArg Subtype.val (originalRegularPatchHomeomorph.apply_symm_apply x)

private theorem ThreefoldHomology.starFillingsToSpaceHomologyMap_single (n : ℕ)
    (i : SpecialPeriods.Threefold.Puncture)
    (a :
      SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.localPiece (Option.some i))
        n) :
    starFillingsToSpaceHomologyMap n (Pi.single i a) =
      SingularMayerVietoris.singularHomologyMap (originalPieceInclusion (Option.some i)) n a := by
  have h :=
    starRightHomologyMap_single n i
      (0 : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n)
      a
  change
    SingularMayerVietoris.singularHomologyMap originalRegularInclusion n 0 +
        starFillingsToSpaceHomologyMap n (Pi.single i a) =
      SingularMayerVietoris.singularHomologyMap originalRegularInclusion n 0 +
        SingularMayerVietoris.singularHomologyMap (originalPieceInclusion (Option.some i)) n
          a at h
  simpa only [map_zero, zero_add] using h

private theorem ThreefoldHomology.starFillingsHomologyEquiv_ambient (n : ℕ) :
    (starFillingsToSpaceHomologyMap n).comp (starFillingsHomologyEquiv n).toLinearMap =
      SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion
          (starFillings : Set SpecialPeriods.Threefold.Space))
        n := by
  apply starFillingsHomology_hom_ext n
  intro i a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, starFillingsHomologyEquiv_inclusion,
    starFillingsToSpaceHomologyMap_single]
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    fillingToStar_ambient]

private theorem ThreefoldHomology.starRegularHomologyEquiv_overlapToStar (n : ℕ)
    (i : SpecialPeriods.Threefold.Puncture)
    (a : SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n) :
    starRegularHomologyEquiv n
        (SingularMayerVietoris.singularHomologyMap starOverlapToRegularPatch n
          (SingularMayerVietoris.singularHomologyMap (overlapToStar i) n a)) =
      SingularMayerVietoris.singularHomologyMap (overlapToRegularFamily i) n a := by
  rw [starRegularHomologyEquiv_apply, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  change
    SingularMayerVietoris.singularHomologyMap starOverlapToRegular n
        (SingularMayerVietoris.singularHomologyMap (overlapToStar i) n a) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    starOverlapToRegular_overlapToStar]

private theorem ThreefoldHomology.starFillingsHomologyEquiv_overlapToStar (n : ℕ)
    (i : SpecialPeriods.Threefold.Puncture)
    (a : SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n) :
    starFillingsHomologyEquiv n
        (SingularMayerVietoris.singularHomologyMap starOverlapToFillings n
          (SingularMayerVietoris.singularHomologyMap (overlapToStar i) n a)) =
      Pi.single i (SingularMayerVietoris.singularHomologyMap (overlapToFilling i) n a) := by
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    starOverlapToFillings_overlapToStar, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, starFillingsHomologyEquiv_inclusion]

private theorem ThreefoldHomology.starLeftHomologyMap_comparison (n : ℕ) :
    (starLeftHomologyMap n).comp (starOverlapHomologyEquiv n).toLinearMap =
      (starPairHomologyEquiv n).toLinearMap.comp
        (SingularMayerVietoris.leftHomologyMap
          (SpecialPeriods.Threefold.liftedPatch Option.none : Set SpecialPeriods.Threefold.Space)
          (starFillings : Set SpecialPeriods.Threefold.Space) n) := by
  apply starOverlapHomology_hom_ext n
  intro i a
  have hr :
    starPairHomologyEquiv n
        (SingularMayerVietoris.leftHomologyMap
          (SpecialPeriods.Threefold.liftedPatch Option.none : Set SpecialPeriods.Threefold.Space)
          (starFillings : Set SpecialPeriods.Threefold.Space) n
          (SingularMayerVietoris.singularHomologyMap (overlapToStar i) n a)) =
      (SingularMayerVietoris.singularHomologyMap (overlapToRegularFamily i) n a,
        Pi.single i (-SingularMayerVietoris.singularHomologyMap (overlapToFilling i) n a)) := by
    have hraw :=
      SingularMayerVietoris.leftHomologyMap_apply
        (SpecialPeriods.Threefold.liftedPatch Option.none : Set SpecialPeriods.Threefold.Space)
        (starFillings : Set SpecialPeriods.Threefold.Space) n
        (SingularMayerVietoris.singularHomologyMap (overlapToStar i) n a)
    refine (congrArg (starPairHomologyEquiv n) hraw).trans ?_
    change
      (starRegularHomologyEquiv n
            (SingularMayerVietoris.singularHomologyMap starOverlapToRegularPatch n
              (SingularMayerVietoris.singularHomologyMap (overlapToStar i) n a)),
          starFillingsHomologyEquiv n
            (-SingularMayerVietoris.singularHomologyMap starOverlapToFillings n
                (SingularMayerVietoris.singularHomologyMap (overlapToStar i) n a))) =
        _
    rw [map_neg, starRegularHomologyEquiv_overlapToStar, starFillingsHomologyEquiv_overlapToStar,
      Pi.single_neg]
  exact
    (congrArg (starLeftHomologyMap n) (starOverlapHomologyEquiv_inclusion n i a)).trans
      ((starLeftHomologyMap_single n i a).trans hr.symm)

private theorem ThreefoldHomology.starRightHomologyMap_comparison (n : ℕ) :
    (starRightHomologyMap n).comp (starPairHomologyEquiv n).toLinearMap =
      SingularMayerVietoris.rightHomologyMap
        (SpecialPeriods.Threefold.liftedPatch Option.none : Set SpecialPeriods.Threefold.Space)
        (starFillings : Set SpecialPeriods.Threefold.Space) n := by
  apply LinearMap.ext
  intro a
  change
    SingularMayerVietoris.singularHomologyMap originalRegularInclusion n
          (starRegularHomologyEquiv n a.1) +
        starFillingsToSpaceHomologyMap n (starFillingsHomologyEquiv n a.2) =
      _
  rw [SingularMayerVietoris.rightHomologyMap_apply]
  exact
    congrArg₂ (· + ·) (LinearMap.congr_fun (starRegularHomologyEquiv_ambient n) a.1)
      (LinearMap.congr_fun (starFillingsHomologyEquiv_ambient n) a.2)

private def ThreefoldHomology.rawStarConnectingHomomorphism (n : ℕ) :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology starOverlap n :=
  SingularMayerVietoris.connectingHomomorphism
    ((SpecialPeriods.Threefold.liftedPatch none : Set SpecialPeriods.Threefold.Space))
    ((ThreefoldHomology.starFillings : Set SpecialPeriods.Threefold.Space))
    (SpecialPeriods.Threefold.liftedPatch Option.none).isOpen starFillings.isOpen star_cover n

private def ThreefoldHomology.starConnectingHomomorphism (n : ℕ) :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space (n + 1) →ₗ[ℤ]
      StarOverlapHomology n :=
  (starOverlapHomologyEquiv n).toLinearMap.comp (rawStarConnectingHomomorphism n)

private theorem ThreefoldHomology.star_exact_at_pair (n : ℕ) :
    Function.Exact (starLeftHomologyMap n) (starRightHomologyMap n) := by
  have hraw :
    Function.Exact
      (SingularMayerVietoris.leftHomologyMap
        ((SpecialPeriods.Threefold.liftedPatch none : Set SpecialPeriods.Threefold.Space))
        ((ThreefoldHomology.starFillings : Set SpecialPeriods.Threefold.Space)) n)
      (SingularMayerVietoris.rightHomologyMap
        ((SpecialPeriods.Threefold.liftedPatch none : Set SpecialPeriods.Threefold.Space))
        ((ThreefoldHomology.starFillings : Set SpecialPeriods.Threefold.Space)) n) :=
    LinearMap.exact_iff.mpr
      (SingularMayerVietoris.exact_at_pair
          ((SpecialPeriods.Threefold.liftedPatch none : Set SpecialPeriods.Threefold.Space))
          ((ThreefoldHomology.starFillings : Set SpecialPeriods.Threefold.Space))
          (SpecialPeriods.Threefold.liftedPatch Option.none).isOpen starFillings.isOpen star_cover
          n).symm
  apply
    exact_of_linearEquiv_squares _ _ _ _ (starOverlapHomologyEquiv n) (starPairHomologyEquiv n)
      (LinearEquiv.refl ℤ _) (starLeftHomologyMap_comparison n) _ hraw
  simpa only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp] using
    starRightHomologyMap_comparison n

private theorem ThreefoldHomology.star_exact_at_intersection (n : ℕ) :
    Function.Exact (starConnectingHomomorphism n) (starLeftHomologyMap n) := by
  have hraw :
    Function.Exact (rawStarConnectingHomomorphism n)
      (SingularMayerVietoris.leftHomologyMap
        ((SpecialPeriods.Threefold.liftedPatch none : Set SpecialPeriods.Threefold.Space))
        ((ThreefoldHomology.starFillings : Set SpecialPeriods.Threefold.Space)) n) :=
    LinearMap.exact_iff.mpr
      (SingularMayerVietoris.exact_at_intersection
          ((SpecialPeriods.Threefold.liftedPatch none : Set SpecialPeriods.Threefold.Space))
          ((ThreefoldHomology.starFillings : Set SpecialPeriods.Threefold.Space))
          (SpecialPeriods.Threefold.liftedPatch Option.none).isOpen starFillings.isOpen star_cover
          n).symm
  apply
    exact_of_linearEquiv_squares _ _ _ _ (LinearEquiv.refl ℤ _) (starOverlapHomologyEquiv n)
      (starPairHomologyEquiv n) _ (starLeftHomologyMap_comparison n) hraw
  simp only [LinearEquiv.refl_toLinearMap, LinearMap.comp_id, starConnectingHomomorphism]

private theorem ThreefoldHomology.star_exact_at_ambient (n : ℕ) :
    Function.Exact (starRightHomologyMap (n + 1)) (starConnectingHomomorphism n) := by
  have hraw :
    Function.Exact
      (SingularMayerVietoris.rightHomologyMap
        ((SpecialPeriods.Threefold.liftedPatch none : Set SpecialPeriods.Threefold.Space))
        ((ThreefoldHomology.starFillings : Set SpecialPeriods.Threefold.Space)) (n + 1))
      (rawStarConnectingHomomorphism n) :=
    LinearMap.exact_iff.mpr
      (SingularMayerVietoris.exact_at_ambient
          ((SpecialPeriods.Threefold.liftedPatch none : Set SpecialPeriods.Threefold.Space))
          ((ThreefoldHomology.starFillings : Set SpecialPeriods.Threefold.Space))
          (SpecialPeriods.Threefold.liftedPatch Option.none).isOpen starFillings.isOpen star_cover
          n).symm
  apply
    exact_of_linearEquiv_squares _ _ _ _ (starPairHomologyEquiv (n + 1)) (LinearEquiv.refl ℤ _)
      (starOverlapHomologyEquiv n) _ _ hraw
  · simpa only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp] using
      starRightHomologyMap_comparison (n + 1)
  · simp only [LinearEquiv.refl_toLinearMap, LinearMap.comp_id, starConnectingHomomorphism]

private theorem ThreefoldHomology.starLeftHomologyMap_one_surjective :
    Function.Surjective (starLeftHomologyMap 1) := by
  intro a
  apply (star_exact_at_pair 1 a).mp
  exact SpecialPeriods.Threefold.LowDegrees.singularH1_eq_zero _

private theorem ThreefoldHomology.SecondDegree.puncture_card :
    Fintype.card SpecialPeriods.Threefold.Puncture = 3 := by decide

private theorem ThreefoldHomology.SecondDegree.overlapFirst_free :
    Module.Free ℤ (ThreefoldHomology.StarOverlapHomology 1) := by
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Module.Free ℤ
        (SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) 1) :=
    ThreefoldHomology.BoundaryFirst.overlapH1_free
  exact
    ThreefoldHomologyFreeProducts.free_pi_int
      (fun i : SpecialPeriods.Threefold.Puncture =>
        SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) 1)

private theorem ThreefoldHomology.SecondDegree.overlapFirst_finrank :
    Module.finrank ℤ (ThreefoldHomology.StarOverlapHomology 1) = 9 := by
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Module.Free ℤ
        (SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) 1) :=
    ThreefoldHomology.BoundaryFirst.overlapH1_free
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Module.Finite ℤ
        (SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) 1) :=
    ThreefoldHomology.BoundaryFirst.overlapH1_finite
  rw [ThreefoldHomologyFreeProducts.finrank_pi_int
      (fun i : SpecialPeriods.Threefold.Puncture =>
        SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) 1)]
  simp only [ThreefoldHomology.BoundaryFirst.overlapH1_finrank, Finset.sum_const,
    Finset.card_univ, puncture_card]
  decide

private theorem
    ThreefoldHomology.SecondDegree.fillingFirst_free (i : SpecialPeriods.Threefold.Puncture) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some i)) 1) := by
  cases i with
  | none => exact ThreefoldHomology.Finiteness.cuspPieceHomology_free 1
  | some j => exact ThreefoldHomology.Finiteness.ellipticPieceHomology_free j 1

private theorem ThreefoldHomology.SecondDegree.fillingFirst_finrank
    (i : SpecialPeriods.Threefold.Puncture) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some i)) 1) =
      2 := by
  cases i with
  | none => exact ThreefoldHomology.Finiteness.cuspPieceHomology_finrank 1
  | some j => exact ThreefoldHomology.Finiteness.ellipticPieceHomology_finrank j 1

private theorem ThreefoldHomology.SecondDegree.fillingsFirst_free :
    Module.Free ℤ (ThreefoldHomology.StarFillingHomology 1) := by
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Module.Free ℤ
        (SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some i)) 1) :=
    fillingFirst_free
  exact
    ThreefoldHomologyFreeProducts.free_pi_int
      (fun i : SpecialPeriods.Threefold.Puncture =>
        SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some i)) 1)

private theorem ThreefoldHomology.SecondDegree.fillingsFirst_finrank :
    Module.finrank ℤ (ThreefoldHomology.StarFillingHomology 1) = 6 := by
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Module.Free ℤ
        (SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some i)) 1) :=
    fillingFirst_free
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Module.Finite ℤ
        (SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some i)) 1) :=
    fun i => ThreefoldHomology.Finiteness.fillingHomology_finite i 1
  rw [ThreefoldHomologyFreeProducts.finrank_pi_int
      (fun i : SpecialPeriods.Threefold.Puncture =>
        SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some i)) 1)]
  simp only [fillingFirst_finrank, Finset.sum_const, Finset.card_univ, puncture_card]
  decide

private theorem ThreefoldHomology.SecondDegree.pairFirst_free :
    Module.Free ℤ (ThreefoldHomology.StarPairHomology 1) := by
  have := ThreefoldHomology.Finiteness.regularHomology_free 1
  have := fillingsFirst_free
  exact
    ThreefoldHomologyFreeProducts.free_prod_int
      (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily 1)
      (ThreefoldHomology.StarFillingHomology 1)

private theorem ThreefoldHomology.SecondDegree.pairFirst_finrank :
    Module.finrank ℤ (ThreefoldHomology.StarPairHomology 1) = 9 := by
  have := ThreefoldHomology.Finiteness.regularHomology_free 1
  have := ThreefoldHomology.Finiteness.regularHomology_finite 1
  have := fillingsFirst_free
  have := ThreefoldHomology.Finiteness.starFillingHomology_finite 1
  rw [ThreefoldHomologyFreeProducts.finrank_prod_int
      (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily 1)
      (ThreefoldHomology.StarFillingHomology 1),
    ThreefoldHomology.Finiteness.regularHomology_finrank, fillingsFirst_finrank]
  rfl

private theorem ThreefoldHomology.SecondDegree.starLeft_one_bijective :
    Function.Bijective (ThreefoldHomology.starLeftHomologyMap 1) := by
  have := overlapFirst_free
  have := pairFirst_free
  have := ThreefoldHomology.Finiteness.starOverlapHomology_finite 1
  have := ThreefoldHomology.Finiteness.starPairHomology_finite 1
  apply
    OrzechProperty.bijective_of_surjective_of_finrank_le (ThreefoldHomology.starLeftHomologyMap 1)
      ThreefoldHomology.starLeftHomologyMap_one_surjective
  rw [overlapFirst_finrank, pairFirst_finrank]

private theorem ThreefoldHomology.SecondDegree.connecting_one_eq_zero :
    ThreefoldHomology.starConnectingHomomorphism 1 = 0 := by
  apply LinearMap.ext
  intro a
  change ThreefoldHomology.starConnectingHomomorphism 1 a = 0
  apply starLeft_one_bijective.injective
  simpa only [map_zero] using
    (ThreefoldHomology.star_exact_at_intersection 1).apply_apply_eq_zero a

private theorem ThreefoldHomology.SecondDegree.starRight_two_surjective :
    Function.Surjective (ThreefoldHomology.starRightHomologyMap 2) := by
  intro a
  apply (ThreefoldHomology.star_exact_at_ambient 1 a).mp
  rw [connecting_one_eq_zero, LinearMap.zero_apply]

private theorem ThreefoldHomology.CapElimination.boundaryFillingHomologyMap_surjective
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    Function.Surjective (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap i n) := by
  cases i with
  | none => exact ThreefoldHomologyCuspFibre.boundaryFillingHomologyMap_surjective n
  | some j =>
    exact PeriodFamily.Boundary.EllipticCapProduct.boundaryFillingHomologyMap_surjective j n

private theorem ThreefoldHomology.CapElimination.overlapToFilling_homology_surjective
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (ThreefoldHomology.overlapToFilling i) n) := by
  intro a
  obtain ⟨b, hb⟩ := boundaryFillingHomologyMap_surjective i n a
  refine ⟨(ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).symm b, ?_⟩
  exact
    (LinearMap.congr_fun (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_eq i n)
          b).symm.trans
      hb

private theorem
    ThreefoldHomology.CapElimination.starOverlapToFillingsHomologyMap_surjective (n : ℕ) :
    Function.Surjective (ThreefoldHomology.starOverlapToFillingsHomologyMap n) := by
  classical
  intro a
  choose b hb using fun i : SpecialPeriods.Threefold.Puncture =>
    overlapToFilling_homology_surjective i n (a i)
  refine ⟨b, ?_⟩
  funext i
  exact hb i

private def ThreefoldHomology.CapElimination.capKernelRegularMap (n : ℕ) :
    LinearMap.ker (ThreefoldHomology.starOverlapToFillingsHomologyMap n) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun a := ThreefoldHomology.starOverlapToRegularHomologyMap n a.val
      map_zero' := (ThreefoldHomology.starOverlapToRegularHomologyMap n).map_zero
      map_add' a b := (ThreefoldHomology.starOverlapToRegularHomologyMap n).map_add a.val b.val }

private def ThreefoldHomology.CapElimination.capKernelRegularImage (n : ℕ) :
    Submodule ℤ
      (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n) :=
  LinearMap.range (capKernelRegularMap n)

private theorem ThreefoldHomology.CapElimination.starLeft_regular_fillings (n : ℕ)
    (a : ThreefoldHomology.StarOverlapHomology n) :
    ThreefoldHomology.starLeftHomologyMap n a =
      (ThreefoldHomology.starOverlapToRegularHomologyMap n a,
        -ThreefoldHomology.starOverlapToFillingsHomologyMap n a) :=
  rfl

@[simp]
private theorem ThreefoldHomology.CapElimination.starRight_regular (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n) :
    ThreefoldHomology.starRightHomologyMap n (a, 0) =
      SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion n a := by
  change
    SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion n a +
        ThreefoldHomology.starFillingsToSpaceHomologyMap n 0 =
      _
  rw [map_zero, add_zero]

private theorem ThreefoldHomology.CapElimination.regularInclusion_kernel (n : ℕ) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion n) =
      capKernelRegularImage n := by
  ext a
  change
    SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion n a = 0 ↔
      ∃ b : LinearMap.ker (ThreefoldHomology.starOverlapToFillingsHomologyMap n),
        capKernelRegularMap n b = a
  constructor
  · intro ha
    have hright : ThreefoldHomology.starRightHomologyMap n (a, 0) = 0 :=
      (starRight_regular n a).trans ha
    obtain ⟨b, hb⟩ := (ThreefoldHomology.star_exact_at_pair n (a, 0)).mp hright
    have hreg : ThreefoldHomology.starOverlapToRegularHomologyMap n b = a := congrArg Prod.fst hb
    have hcap : ThreefoldHomology.starOverlapToFillingsHomologyMap n b = 0 := by
      have hneg : -ThreefoldHomology.starOverlapToFillingsHomologyMap n b = 0 :=
        congrArg Prod.snd hb
      exact neg_eq_zero.mp hneg
    exact ⟨⟨b, hcap⟩, hreg⟩
  · rintro ⟨b, hb⟩
    have hcap : ThreefoldHomology.starOverlapToFillingsHomologyMap n b.val = 0 := b.property
    have hleft : ThreefoldHomology.starLeftHomologyMap n b.val = (a, 0) := by
      rw [starLeft_regular_fillings, hcap, neg_zero]
      exact Prod.ext hb rfl
    have hright := (ThreefoldHomology.star_exact_at_pair n).apply_apply_eq_zero b.val
    rw [hleft, starRight_regular] at hright
    exact hright

private theorem ThreefoldHomology.CapElimination.regularInclusion_two_surjective :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion 2) := by
  intro x
  obtain ⟨p, hp⟩ := ThreefoldHomology.SecondDegree.starRight_two_surjective x
  obtain ⟨a, ha⟩ := starOverlapToFillingsHomologyMap_surjective 2 (-p.2)
  have hshape :
    p - ThreefoldHomology.starLeftHomologyMap 2 a =
      (p.1 - ThreefoldHomology.starOverlapToRegularHomologyMap 2 a, 0) := by
    rw [starLeft_regular_fillings]
    apply Prod.ext
    · rfl
    · change p.2 - -ThreefoldHomology.starOverlapToFillingsHomologyMap 2 a = 0
      rw [ha, neg_neg, sub_self]
  refine ⟨p.1 - ThreefoldHomology.starOverlapToRegularHomologyMap 2 a, ?_⟩
  calc
    SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion 2
          (p.1 - ThreefoldHomology.starOverlapToRegularHomologyMap 2 a) =
        ThreefoldHomology.starRightHomologyMap 2
          (p.1 - ThreefoldHomology.starOverlapToRegularHomologyMap 2 a, 0) :=
      (starRight_regular 2 _).symm
    _ =
        ThreefoldHomology.starRightHomologyMap 2
          (p - ThreefoldHomology.starLeftHomologyMap 2 a) :=
      (congrArg (ThreefoldHomology.starRightHomologyMap 2) hshape.symm)
    _ =
        ThreefoldHomology.starRightHomologyMap 2 p -
          ThreefoldHomology.starRightHomologyMap 2 (ThreefoldHomology.starLeftHomologyMap 2 a) :=
      (map_sub _ _ _)
    _ = x := by rw [hp, (ThreefoldHomology.star_exact_at_pair 2).apply_apply_eq_zero a, sub_zero]

private abbrev
    ThreefoldHomology.CapElimination.NativeCapKernel (i : SpecialPeriods.Threefold.Puncture)
    (n : ℕ) :=
  LinearMap.ker (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap i n)

private def ThreefoldHomology.CapElimination.nativeCapKernelRegularMap (n : ℕ) :
    (∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i n) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun
        a :=
        ∑ i : SpecialPeriods.Threefold.Puncture,
          ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i n (a i).val
      map_zero' := by
        simp only [Pi.zero_apply, Submodule.coe_zero, map_zero, Finset.sum_const_zero]
      map_add' a
        b := by simp only [Pi.add_apply, Submodule.coe_add, map_add, Finset.sum_add_distrib] }

@[simp]
private theorem ThreefoldHomology.CapElimination.nativeCapKernelRegularMap_apply (n : ℕ)
    (a : ∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i n) :
    nativeCapKernelRegularMap n a =
      ∑ i : SpecialPeriods.Threefold.Puncture,
        ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i n (a i).val :=
  rfl

private def ThreefoldHomology.CapElimination.nativeCapKernelEquiv (n : ℕ) :
    LinearMap.ker (ThreefoldHomology.starOverlapToFillingsHomologyMap n) ≃ₗ[ℤ]
      (∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i n) :=
  ({    toFun a
          i :=
          ⟨ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n (a.val i),
            by
            have h :=
              LinearMap.congr_fun
                (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_retraction i n) (a.val i)
            exact h.trans (congrFun a.property i)⟩
        invFun
          a :=
          ⟨fun i => (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).symm (a i).val,
            by
            funext i
            have h :=
              LinearMap.congr_fun
                (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_retraction i n)
                ((ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).symm (a i).val)
            have hz :=
              (congrArg (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap i n)
                    ((ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).apply_symm_apply
                      (a i).val)).trans
                (a i).property
            exact h.symm.trans hz⟩
        left_inv
          a := by
          apply Subtype.ext
          funext i
          exact (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).symm_apply_apply (a.val i)
        right_inv
          a := by
          funext i
          apply Subtype.ext
          exact (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).apply_symm_apply (a i).val
        map_add' a
          b := by
          funext i
          apply Subtype.ext
          exact
            (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).map_add (a.val i)
              (b.val i) } :
      LinearMap.ker (ThreefoldHomology.starOverlapToFillingsHomologyMap n) ≃+
        (∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i n)).toIntLinearEquiv

private theorem ThreefoldHomology.CapElimination.nativeCapKernelRegularMap_equiv (n : ℕ)
    (a : LinearMap.ker (ThreefoldHomology.starOverlapToFillingsHomologyMap n)) :
    nativeCapKernelRegularMap n (nativeCapKernelEquiv n a) = capKernelRegularMap n a := by
  change
    (∑ i : SpecialPeriods.Threefold.Puncture,
        ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i n
          (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n (a.val i))) =
      ∑ i : SpecialPeriods.Threefold.Puncture,
        SingularMayerVietoris.singularHomologyMap (ThreefoldHomology.overlapToRegularFamily i) n
          (a.val i)
  apply Finset.sum_congr rfl
  intro i _
  exact
    LinearMap.congr_fun (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap_retraction i n)
      (a.val i)

private theorem ThreefoldHomology.CapElimination.nativeCapKernelRegularMap_range (n : ℕ) :
    LinearMap.range (nativeCapKernelRegularMap n) = capKernelRegularImage n := by
  ext r
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(nativeCapKernelEquiv n).symm a, ?_⟩
    rw [← nativeCapKernelRegularMap_equiv, LinearEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨a, ha⟩
    exact ⟨nativeCapKernelEquiv n a, (nativeCapKernelRegularMap_equiv n a).trans ha⟩

private theorem ThreefoldHomology.CapElimination.regularInclusion_native_kernel (n : ℕ) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion n) =
      LinearMap.range (nativeCapKernelRegularMap n) :=
  (regularInclusion_kernel n).trans (nativeCapKernelRegularMap_range n).symm

private theorem ThreefoldHomology.CapElimination.regularInclusion_eq_zero_iff_native (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n) :
    SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion n a = 0 ↔
      ∃ b : ∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i n,
        nativeCapKernelRegularMap n b = a := by
  change
    a ∈
        LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion
            n) ↔
      _
  rw [regularInclusion_native_kernel]
  rfl

private theorem
    ThreefoldHomology.CapElimination.homologyTwo_subsingleton_iff_nativeCapKernel_surjective :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 2) ↔
      Function.Surjective (nativeCapKernelRegularMap 2) := by
  constructor
  · intro h a
    exact (regularInclusion_eq_zero_iff_native 2 a).mp (h.elim _ _)
  · intro h
    have hz (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 2) :
      a = 0 := by
      obtain ⟨b, rfl⟩ := regularInclusion_two_surjective a
      exact (regularInclusion_eq_zero_iff_native 2 b).mpr (h b)
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩

private theorem ThreefoldHomology.FourthWang.commonCubeInvariant_iff (v : Fin 4 → ℤ) :
    (PeriodTorusHigherHomologyExterior.cubeA₁ *ᵥ v = v ∧
        PeriodTorusHigherHomologyExterior.cubeA₂ *ᵥ v = v) ↔
      v = Pi.single 3 (v 3) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have h11 := congrFun h₁ 1
    have h13 := congrFun h₁ 3
    have h21 := congrFun h₂ 1
    simp [PeriodTorusHigherHomologyExterior.cubeA₁_eq,
      PeriodTorusHigherHomologyExterior.cubeA₂_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] at h11 h13 h21
    have hz : v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 := by omega
    ext i
    fin_cases i <;> simp [hz.1, hz.2.1, hz.2.2]
  · intro h
    rw [h]
    constructor <;> ext i <;> fin_cases i <;>
      simp [PeriodTorusHigherHomologyExterior.cubeA₁_eq,
        PeriodTorusHigherHomologyExterior.cubeA₂_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem ThreefoldHomology.FourthWang.commonThirdInvariant_iff
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    (PeriodFamily.Homology.generatorHomologyEquiv Bool.false 3 a = a ∧
        PeriodFamily.Homology.generatorHomologyEquiv Bool.true 3 a = a) ↔
      PeriodFamily.FlatTorus.singularH3Coordinates a =
        Pi.single 3 (PeriodFamily.FlatTorus.singularH3Coordinates a 3) := by
  rw [← commonCubeInvariant_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · have h := congrArg PeriodFamily.FlatTorus.singularH3Coordinates h₁
      simpa only [PeriodFamily.HomologyDifference.generatorHomologyThree_coordinates,
        Bool.false_eq_true, ite_false] using h
    · have h := congrArg PeriodFamily.FlatTorus.singularH3Coordinates h₂
      simpa only [PeriodFamily.HomologyDifference.generatorHomologyThree_coordinates,
        ite_true] using h
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply PeriodFamily.FlatTorus.singularH3Coordinates.injective
      simpa only [PeriodFamily.HomologyDifference.generatorHomologyThree_coordinates,
        Bool.false_eq_true, ite_false] using h₁
    · apply PeriodFamily.FlatTorus.singularH3Coordinates.injective
      simpa only [PeriodFamily.HomologyDifference.generatorHomologyThree_coordinates,
        ite_true] using h₂

private def ThreefoldHomology.FourthWang.regularSourcePair (n : ℕ) :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily
        (n + 1) →ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        SingularMayerVietoris.SingularHomology RealTorus₄ n) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun := fun a =>
        (PeriodFamily.Homology.sourceKernelProjection
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            n a).val
      map_zero' :=
        congrArg Subtype.val
          (map_zero
            (PeriodFamily.Homology.sourceKernelProjection
              (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)
              n))
      map_add' := fun a b =>
        congrArg Subtype.val
          (map_add
            (PeriodFamily.Homology.sourceKernelProjection
              (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)
              n)
            a b) }

@[simp]
private theorem ThreefoldHomology.FourthWang.regularSourcePair_apply (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily
        (n + 1)) :
    regularSourcePair n a =
      (PeriodFamily.Homology.sourceKernelProjection
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          n a).val :=
  rfl

private def
    ThreefoldHomology.FourthWang.overlapWangHomologyMap (i : SpecialPeriods.Threefold.Puncture)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i)
        (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy i) n).comp
    (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i (n + 1)).toLinearMap

private def
    ThreefoldHomology.FourthWang.sourceColumn (i : SpecialPeriods.Threefold.Puncture) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.SingularHomology RealTorus₄ n ×
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  match i with
  | none =>
    (-PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n a, -a)
  | some .three => (a, 0)
  | some .four => (0, a)

private theorem ThreefoldHomology.FourthWang.regularSourcePair_boundary
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary i) (n + 1)) :
    regularSourcePair n (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i (n + 1) a) =
      sourceColumn i n
        (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy i) n a) := by
  rw [regularSourcePair_apply]
  cases i with
  | none =>
    simpa only [sourceColumn, ThreefoldOverlapMappingTorus.monodromy] using!
      (PeriodFamily.Boundary.Cusp.boundary_sourceKernelProjection n a)
  | some j =>
    cases j with
    | three =>
      simpa only [sourceColumn, ThreefoldOverlapMappingTorus.monodromy] using!
        (PeriodFamily.Boundary.ellipticThreeBoundary_sourceKernelProjection n a)
    | four =>
      simpa only [sourceColumn, ThreefoldOverlapMappingTorus.monodromy] using!
        (PeriodFamily.Boundary.ellipticFourBoundary_sourceKernelProjection n a)

private theorem ThreefoldHomology.FourthWang.regularSourcePair_overlap
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i)
        (n + 1)) :
    regularSourcePair n
        (SingularMayerVietoris.singularHomologyMap (ThreefoldHomology.overlapToRegularFamily i)
          (n + 1) a) =
      sourceColumn i n (overlapWangHomologyMap i n a) := by
  have h :=
    LinearMap.congr_fun
      (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap_retraction i (n + 1)) a
  change
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i (n + 1)
        (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap (ThreefoldHomology.overlapToRegularFamily i)
        (n + 1) a at h
  rw [← h]
  exact regularSourcePair_boundary i n _

private theorem ThreefoldHomology.FourthWang.regularSourcePair_star (n : ℕ)
    (a : ThreefoldHomology.StarOverlapHomology (n + 1)) :
    regularSourcePair n (ThreefoldHomology.starOverlapToRegularHomologyMap (n + 1) a) =
      (overlapWangHomologyMap (Option.some .three) n (a (Option.some .three)) -
          PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n
            (overlapWangHomologyMap Option.none n (a Option.none)),
        overlapWangHomologyMap (Option.some .four) n (a (Option.some .four)) -
          overlapWangHomologyMap Option.none n (a Option.none)) := by
  classical
  rw [ThreefoldHomology.starOverlapToRegularHomologyMap_apply, map_sum]
  simp only [regularSourcePair_overlap]
  rw [Fintype.sum_option]
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four)]
  simp only [sourceColumn, Prod.mk_add_mk, add_zero, zero_add, sub_eq_add_neg]
  exact Prod.ext (add_comm _ _) (add_comm _ _)

private theorem ThreefoldHomology.FourthWang.wang_cancellation (n : ℕ)
    (a : ThreefoldHomology.StarOverlapHomology (n + 1))
    (ha : ThreefoldHomology.starOverlapToRegularHomologyMap (n + 1) a = 0) :
    overlapWangHomologyMap (Option.some .three) n (a (Option.some .three)) =
        overlapWangHomologyMap Option.none n (a Option.none) ∧
      overlapWangHomologyMap (Option.some .four) n (a (Option.some .four)) =
          overlapWangHomologyMap Option.none n (a Option.none) ∧
        PeriodFamily.Homology.generatorHomologyEquiv Bool.false n
              (overlapWangHomologyMap Option.none n (a Option.none)) =
            overlapWangHomologyMap Option.none n (a Option.none) ∧
          PeriodFamily.Homology.generatorHomologyEquiv Bool.true n
              (overlapWangHomologyMap Option.none n (a Option.none)) =
            overlapWangHomologyMap Option.none n (a Option.none) := by
  let w₀ := overlapWangHomologyMap Option.none n (a Option.none)
  let w₃ := overlapWangHomologyMap (Option.some .three) n (a (Option.some .three))
  let w₄ := overlapWangHomologyMap (Option.some .four) n (a (Option.some .four))
  have h := regularSourcePair_star n a
  rw [ha, map_zero] at h
  have h₃ :
    w₃ = PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n w₀ :=
    sub_eq_zero.mp (congrArg Prod.fst h).symm
  have h₄ : w₄ = w₀ := sub_eq_zero.mp (congrArg Prod.snd h).symm
  have hf₃ : PeriodFamily.Homology.generatorHomologyEquiv Bool.false n w₃ = w₃ :=
    PeriodFamily.Boundary.ellipticWangBoundary_generator_fixed .three Elliptic.Kind.three.twist n
      (ThreefoldOverlapMappingTorus.overlapHomologyEquiv (Option.some .three) (n + 1) _)
  have hf₄ : PeriodFamily.Homology.generatorHomologyEquiv Bool.true n w₄ = w₄ :=
    PeriodFamily.Boundary.ellipticWangBoundary_generator_fixed .four Elliptic.Kind.four.twist n
      (ThreefoldOverlapMappingTorus.overlapHomologyEquiv (Option.some .four) (n + 1) _)
  have he₃ : w₃ = w₀ := by
    rw [PeriodFamily.Homology.triangleHomologyEquiv_inv] at h₃
    calc
      w₃ = PeriodFamily.Homology.generatorHomologyEquiv Bool.false n w₃ := hf₃.symm
      _ =
          PeriodFamily.Homology.generatorHomologyEquiv Bool.false n
            ((PeriodFamily.Homology.generatorHomologyEquiv Bool.false n).symm w₀) :=
        (congrArg (PeriodFamily.Homology.generatorHomologyEquiv Bool.false n) h₃)
      _ = w₀ := LinearEquiv.apply_symm_apply _ _
  refine ⟨he₃, h₄, ?_, ?_⟩
  · simpa only [he₃] using hf₃
  · simpa only [h₄] using hf₄

private def ThreefoldHomology.CapElimination.nativeCapKernelSourceMap (n : ℕ) :
    (∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i (n + 1)) →ₗ[ℤ]
      LinearMap.ker (PeriodFamily.Homology.sourceDifference n) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun
        a :=
        PeriodFamily.Homology.sourceKernelProjection
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          n (nativeCapKernelRegularMap (n + 1) a)
      map_zero' := by rw [map_zero, map_zero]
      map_add' a b := by rw [map_add, map_add] }

@[simp]
private theorem ThreefoldHomology.CapElimination.nativeCapKernelSourceMap_apply (n : ℕ)
    (a : ∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i (n + 1)) :
    nativeCapKernelSourceMap n a =
      PeriodFamily.Homology.sourceKernelProjection
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        n (nativeCapKernelRegularMap (n + 1) a) :=
  rfl

private def ThreefoldHomology.CapElimination.nativeCapKernelWangValue (n : ℕ)
    (a : ∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i (n + 1))
    (i : SpecialPeriods.Threefold.Puncture) :
    SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy i) n (a i).val

private theorem ThreefoldHomology.CapElimination.nativeCapKernelSourceMap_val (n : ℕ)
    (a : ∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i (n + 1)) :
    (nativeCapKernelSourceMap n a).val =
      (nativeCapKernelWangValue n a (Option.some .three) -
          PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n
            (nativeCapKernelWangValue n a Option.none),
        nativeCapKernelWangValue n a (Option.some .four) -
          nativeCapKernelWangValue n a Option.none) := by
  classical
  change
    ThreefoldHomology.FourthWang.regularSourcePair n (nativeCapKernelRegularMap (n + 1) a) = _
  rw [nativeCapKernelRegularMap_apply, map_sum]
  simp only [ThreefoldHomology.FourthWang.regularSourcePair_boundary]
  rw [Fintype.sum_option]
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four)]
  simp only [ThreefoldHomology.FourthWang.sourceColumn, nativeCapKernelWangValue, Prod.mk_add_mk,
    add_zero, zero_add, sub_eq_add_neg]
  exact Prod.ext (add_comm _ _) (add_comm _ _)

private theorem ThreefoldHomology.CapElimination.nativeCapKernelWangValue_first_inv (n : ℕ)
    (a : ∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i (n + 1)) :
    PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n
        (nativeCapKernelWangValue n a Option.none) =
      PeriodFamily.Homology.generatorHomologyEquiv Bool.true n
        (nativeCapKernelWangValue n a Option.none) := by
  have h :=
    congrArg (PeriodFamily.Homology.generatorHomologyEquiv Bool.true n)
      (PeriodFamily.Boundary.Cusp.wangBoundary_inverse_word n (a Option.none).val)
  simpa only [LinearEquiv.apply_symm_apply, nativeCapKernelWangValue] using! h

private theorem ThreefoldHomology.CapElimination.nativeCapKernelSourceMap_val_second (n : ℕ)
    (a : ∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i (n + 1)) :
    (nativeCapKernelSourceMap n a).val =
      (nativeCapKernelWangValue n a (Option.some .three) -
          PeriodFamily.Homology.generatorHomologyEquiv Bool.true n
            (nativeCapKernelWangValue n a Option.none),
        nativeCapKernelWangValue n a (Option.some .four) -
          nativeCapKernelWangValue n a Option.none) := by
  rw [nativeCapKernelSourceMap_val, nativeCapKernelWangValue_first_inv]

private theorem ThreefoldHomology.CapElimination.nativeCapKernelSourceMap_one_coordinates
    (a : ∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i 2) :
    (PeriodFamily.FlatTorus.singularH1Equiv (nativeCapKernelSourceMap 1 a).val.1,
        PeriodFamily.FlatTorus.singularH1Equiv (nativeCapKernelSourceMap 1 a).val.2) =
      (PeriodFamily.FlatTorus.singularH1Equiv
            (nativeCapKernelWangValue 1 a (Option.some .three)) -
          A₂ *ᵥ PeriodFamily.FlatTorus.singularH1Equiv (nativeCapKernelWangValue 1 a Option.none),
        PeriodFamily.FlatTorus.singularH1Equiv
            (nativeCapKernelWangValue 1 a (Option.some .four)) -
          PeriodFamily.FlatTorus.singularH1Equiv (nativeCapKernelWangValue 1 a Option.none)) := by
  rw [nativeCapKernelSourceMap_val_second]
  simp only [map_sub, PeriodFamily.HomologyDifference.generatorHomologyOne_true_coordinates]

private theorem ThreefoldHomology.CapElimination.nativeCapKernelSourceMap_three_coordinates
    (a : ∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i 4) :
    (PeriodFamily.FlatTorus.singularH3Coordinates (nativeCapKernelSourceMap 3 a).val.1,
        PeriodFamily.FlatTorus.singularH3Coordinates (nativeCapKernelSourceMap 3 a).val.2) =
      (PeriodFamily.FlatTorus.singularH3Coordinates
            (nativeCapKernelWangValue 3 a (Option.some .three)) -
          PeriodTorusHigherHomologyExterior.cubeA₂ *ᵥ
            PeriodFamily.FlatTorus.singularH3Coordinates
              (nativeCapKernelWangValue 3 a Option.none),
        PeriodFamily.FlatTorus.singularH3Coordinates
            (nativeCapKernelWangValue 3 a (Option.some .four)) -
          PeriodFamily.FlatTorus.singularH3Coordinates
            (nativeCapKernelWangValue 3 a Option.none)) := by
  rw [nativeCapKernelSourceMap_val_second]
  simp only [map_sub, PeriodFamily.HomologyDifference.generatorHomologyThree_coordinates, ite_true]

private def ThreefoldHomologyCuspFibre.cuspFibreCoinvariantMap (n : ℕ) :
    (SingularMayerVietoris.SingularHomology RealTorus₄ n ⧸
        LinearMap.range
          (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none)
            n)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) n :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun
        a :=
        ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none n
          (MappingTorusHomology.cokernelInclusion (ThreefoldOverlapMappingTorus.monodromy none) n
            a)
      map_zero' := by rw [map_zero, map_zero]
      map_add' a b := by rw [map_add, map_add] }

@[simp]
private theorem ThreefoldHomologyCuspFibre.cuspFibreCoinvariantMap_apply (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology RealTorus₄ n ⧸
        LinearMap.range
          (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n)) :
    cuspFibreCoinvariantMap n a =
      ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none n
        (MappingTorusHomology.cokernelInclusion (ThreefoldOverlapMappingTorus.monodromy none) n
          a) :=
  rfl

private theorem ThreefoldHomologyCuspFibre.cuspFibreCoinvariantMap_mk (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    cuspFibreCoinvariantMap n (Submodule.Quotient.mk a) =
      SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.fibreToFilling Option.none) n a := by
  rw [cuspFibreCoinvariantMap_apply, MappingTorusHomology.cokernelInclusion_mk]
  exact
    LinearMap.congr_fun
      (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_fibre Option.none n) a

private theorem ThreefoldHomologyCuspFibre.cuspFibreCoinvariantMap_surjective (n : ℕ) :
    Function.Surjective (cuspFibreCoinvariantMap n) := by
  intro a
  obtain ⟨b, hb⟩ := fibreToFilling_homology_surjective n a
  exact ⟨Submodule.Quotient.mk b, (cuspFibreCoinvariantMap_mk n b).trans hb⟩

private theorem ThreefoldHomologyCuspFibre.cuspWangDifference_le_fibreCap_kernel (n : ℕ) :
    LinearMap.range
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n) ≤
      LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.fibreToFilling Option.none) n) := by
  intro a ha
  have hq :
    (Submodule.Quotient.mk a :
        SingularMayerVietoris.SingularHomology RealTorus₄ n ⧸
          LinearMap.range
            (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none)
              n)) =
      0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ha
  change
    SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.fibreToFilling Option.none) n a =
      0
  rw [← cuspFibreCoinvariantMap_mk, hq, map_zero]

private abbrev ThreefoldHomologyCuspFibre.CuspWangCokernel (n : ℕ) :=
  SingularMayerVietoris.SingularHomology RealTorus₄ n ⧸
    LinearMap.range
      (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n)

private def ThreefoldHomologyCuspFibre.cuspTorusHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology RealTorus₄ n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n :=
  PeriodTorusHigherHomology.homeomorphHomologyEquiv
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph n

private theorem ThreefoldHomologyCuspFibre.cuspTorusHomologyEquiv_monodromy (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    cuspTorusHomologyEquiv n
        (MappingTorusHomology.monodromyHomologyMap (ThreefoldOverlapMappingTorus.monodromy none) n
          a) =
      SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) n
        (cuspTorusHomologyEquiv n a) := by
  have h :=
    PeriodFamily.FlatTorus.flatTorusCircleHomology_triangle_apply
      SpecialPeriods.triangleCuspGenerator n a
  rw [SpecialPeriods.triangleDualRepresentation_cusp_matrix] at h
  have hm := LinearMap.congr_fun (PeriodFamily.Boundary.Cusp.monodromyHomology_triangle n) a
  exact (congrArg (cuspTorusHomologyEquiv n) hm).trans h

private theorem ThreefoldHomologyCuspFibre.cuspWangDifference_conjugacy (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    cuspTorusHomologyEquiv n
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n a) =
      (-CuspCoinvariants.torusDifference n) (cuspTorusHomologyEquiv n a) := by
  change
    cuspTorusHomologyEquiv n
        (a -
          MappingTorusHomology.monodromyHomologyMap (ThreefoldOverlapMappingTorus.monodromy none)
            n a) =
      _
  rw [map_sub, cuspTorusHomologyEquiv_monodromy, LinearMap.neg_apply,
    CuspCoinvariants.torusDifference_apply]
  abel

private theorem ThreefoldHomologyCuspFibre.cuspWangDifference_range_map (n : ℕ) :
    (LinearMap.range
            (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none)
              n)).map
        (cuspTorusHomologyEquiv n).toLinearMap =
      LinearMap.range (CuspCoinvariants.torusDifference n) := by
  have h :=
    CuspCoinvariants.map_range_of_intertwines (cuspTorusHomologyEquiv n)
      (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n)
      (-CuspCoinvariants.torusDifference n) (cuspWangDifference_conjugacy n)
  rw [LinearMap.range_neg] at h
  exact h

private def ThreefoldHomologyCuspFibre.cuspWangCokernelTorusAddEquiv_mo1973_27172 (n : ℕ) :
    CuspWangCokernel n ≃+ CuspCoinvariants.TorusCoinvariants n := by
  letI :=
    Submodule.Quotient.module
      (LinearMap.range
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n))
  letI := Submodule.Quotient.module (LinearMap.range (CuspCoinvariants.torusDifference n))
  exact
    (Submodule.Quotient.equiv
        (LinearMap.range
          (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n))
        (LinearMap.range (CuspCoinvariants.torusDifference n)) (cuspTorusHomologyEquiv n)
        (cuspWangDifference_range_map n)).toAddEquiv

private def ThreefoldHomologyCuspFibre.cuspWangCokernelTorusEquiv (n : ℕ) :
    CuspWangCokernel n ≃ₗ[ℤ] CuspCoinvariants.TorusCoinvariants n :=
  (cuspWangCokernelTorusAddEquiv_mo1973_27172 n).toIntLinearEquiv

private def
    ThreefoldHomologyCuspFibre.cuspWangCokernelTwoEquiv : CuspWangCokernel 2 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ((cuspWangCokernelTorusEquiv 2).toAddEquiv.trans
      CuspCoinvariants.torusTwoCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

private def ThreefoldHomologyCuspFibre.cuspWangCokernelThreeEquiv :
    CuspWangCokernel 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((cuspWangCokernelTorusEquiv 3).toAddEquiv.trans
      CuspCoinvariants.torusThreeCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

private theorem ThreefoldHomologyCuspFibre.cuspWangDifference_zero :
    MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) 0 = 0 :=
  ThreefoldHomology.BoundaryFirst.boundaryWangDifference_zero Option.none

private theorem ThreefoldHomologyCuspFibre.cuspWangDifference_four :
    MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) 4 = 0 := by
  apply LinearMap.ext
  intro a
  apply (cuspTorusHomologyEquiv 4).injective
  rw [LinearMap.zero_apply, map_zero, cuspWangDifference_conjugacy, LinearMap.neg_apply,
    CuspCoinvariants.torusDifference_apply, PeriodFamily.Homology.torusMatrixMap_M₀_homologyFour,
    LinearMap.id_apply, sub_self, neg_zero]

private def ThreefoldHomologyCuspFibre.cuspWangCokernelOfZeroAddEquiv_mo1973_27182 (n : ℕ)
    (h :
      MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n = 0) :
    CuspWangCokernel n ≃+ SingularMayerVietoris.SingularHomology RealTorus₄ n := by
  letI :=
    Submodule.Quotient.module
      (LinearMap.range
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n))
  exact
    ((LinearMap.range
            (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none)
              n)).quotEquivOfEqBot
        (by rw [h, LinearMap.range_zero])).toAddEquiv

private def ThreefoldHomologyCuspFibre.cuspWangCokernelZeroEquiv : CuspWangCokernel 0 ≃ₗ[ℤ] ℤ :=
  ((cuspWangCokernelOfZeroAddEquiv_mo1973_27182 0 cuspWangDifference_zero).trans
      (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
          RealTorus₄).toAddEquiv).toIntLinearEquiv

private def
    ThreefoldHomologyCuspFibre.cuspWangCokernelOneEquiv : CuspWangCokernel 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (ThreefoldHomology.BoundaryFirst.boundaryCokernelOneEquiv
      Option.none).toAddEquiv.toIntLinearEquiv

private def ThreefoldHomologyCuspFibre.cuspWangCokernelFourEquiv : CuspWangCokernel 4 ≃ₗ[ℤ] ℤ :=
  ((cuspWangCokernelOfZeroAddEquiv_mo1973_27182 4 cuspWangDifference_four).trans
      PeriodTorusHigherHomology.realTorusH4Equiv.toAddEquiv).toIntLinearEquiv

private theorem
    ThreefoldHomologyCuspFibre.cuspWangCokernel_subsingleton_of_four_lt {n : ℕ} (hn : 4 < n) :
    Subsingleton (CuspWangCokernel n) := by
  have := PeriodTorusHigherHomology.realTorus_homology_subsingleton_of_lt hn
  infer_instance

private def ThreefoldHomologyCuspFibre.cuspWangCokernelEquiv (n : ℕ) :
    CuspWangCokernel n ≃ₗ[ℤ] (Fin (CuspCentralHomology.centralBetti n) → ℤ) :=
  match n with
  | 0 => cuspWangCokernelZeroEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | 1 => cuspWangCokernelOneEquiv
  | 2 => cuspWangCokernelTwoEquiv
  | 3 => cuspWangCokernelThreeEquiv
  | 4 => cuspWangCokernelFourEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | n + 5 =>
    by
    have := cuspWangCokernel_subsingleton_of_four_lt (show 4 < n + 5 by omega)
    change CuspWangCokernel (n + 5) ≃ₗ[ℤ] (Fin 0 → ℤ)
    exact LinearEquiv.ofSubsingleton _ _

private theorem ThreefoldHomologyCuspFibre.cuspWangCokernel_free (n : ℕ) :
    Module.Free ℤ (CuspWangCokernel n) :=
  Module.Free.of_equiv (cuspWangCokernelEquiv n).symm

private theorem ThreefoldHomologyCuspFibre.cuspWangCokernel_finite (n : ℕ) :
    Module.Finite ℤ (CuspWangCokernel n) :=
  Module.Finite.of_surjective (cuspWangCokernelEquiv n).symm.toLinearMap
    (cuspWangCokernelEquiv n).symm.surjective

private theorem ThreefoldHomologyCuspFibre.cuspWangCokernel_finrank (n : ℕ) :
    Module.finrank ℤ (CuspWangCokernel n) = CuspCentralHomology.centralBetti n := by
  rw [(cuspWangCokernelEquiv n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

private theorem ThreefoldHomologyCuspFibre.cuspFibreCoinvariantMap_bijective (n : ℕ) :
    Function.Bijective (cuspFibreCoinvariantMap n) := by
  have := cuspWangCokernel_free n
  have := cuspWangCokernel_finite n
  have :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) n) :=
    ThreefoldHomologyFinitenessCusp.fullHomology_free
      ThreefoldOverlapMappingTorus.Cusp.specialData n
  have :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) n) :=
    ThreefoldHomologyFinitenessCusp.fullHomology_finite
      ThreefoldOverlapMappingTorus.Cusp.specialData n
  have hr :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) n) =
      CuspCentralHomology.centralBetti n :=
    ThreefoldHomologyFinitenessCusp.fullHomology_finrank
      ThreefoldOverlapMappingTorus.Cusp.specialData n
  apply
    OrzechProperty.bijective_of_surjective_of_finrank_le (cuspFibreCoinvariantMap n)
      (cuspFibreCoinvariantMap_surjective n)
  rw [cuspWangCokernel_finrank, hr]

private def ThreefoldHomologyCuspFibre.cuspFibreCoinvariantEquiv (n : ℕ) :
    CuspWangCokernel n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) n :=
  LinearEquiv.ofBijective (cuspFibreCoinvariantMap n) (cuspFibreCoinvariantMap_bijective n)

private theorem
    ThreefoldHomologyCuspFibre.fibreToFilling_cusp_kernel_eq_wangDifference_range (n : ℕ) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.fibreToFilling Option.none) n) =
      LinearMap.range
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n) := by
  apply le_antisymm ?_ (cuspWangDifference_le_fibreCap_kernel n)
  intro a ha
  apply (Submodule.Quotient.mk_eq_zero _).mp
  apply (cuspFibreCoinvariantMap_bijective n).injective
  rw [cuspFibreCoinvariantMap_mk, map_zero]
  exact ha

private theorem ThreefoldHomologyCuspFibre.fibreToFilling_cusp_eq_zero_iff_fibreHomologyMap_eq_zero
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.fibreToFilling Option.none) n a =
        0 ↔
      MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy none) n a =
        0 := by
  change
    a ∈
        LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap
            (ThreefoldOverlapMappingTorus.fibreToFilling Option.none) n) ↔
      a ∈
        LinearMap.ker
          (MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy none) n)
  rw [fibreToFilling_cusp_kernel_eq_wangDifference_range,
    MappingTorusHomology.wang_exact_at_fibre]

private theorem ThreefoldHomologyCuspFibre.cuspCap_wang_eq_zero (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary Option.none)
        (n + 1))
    (hcap : ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none (n + 1) a = 0)
    (hwang :
      MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy none) n a = 0) :
    a = 0 := by
  have ha :
    a ∈
      LinearMap.range
        (MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy none)
          (n + 1)) := by
    rw [MappingTorusHomology.wang_exact_at_mappingTorus
        (ThreefoldOverlapMappingTorus.monodromy none) n]
    exact hwang
  obtain ⟨b, rfl⟩ := ha
  apply (fibreToFilling_cusp_eq_zero_iff_fibreHomologyMap_eq_zero (n + 1) b).mp
  exact
    (LinearMap.congr_fun
          (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_fibre Option.none (n + 1))
          b).symm.trans
      hcap

private theorem ThreefoldHomologyCuspFibre.cuspCap_wang_ext (n : ℕ)
    (a b :
      SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary Option.none)
        (n + 1))
    (hcap :
      ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none (n + 1) a =
        ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none (n + 1) b)
    (hwang :
      MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy none) n a =
        MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy none) n b) :
    a = b := by
  apply sub_eq_zero.mp
  apply cuspCap_wang_eq_zero n (a - b)
  · rw [map_sub, hcap, sub_self]
  · rw [map_sub, hwang, sub_self]

private def ThreefoldHomologyCuspFibre.cuspCapKernelWangDegreeMap (n : ℕ) :
    LinearMap.ker
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none (n + 1)) →ₗ[ℤ]
      LinearMap.ker
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun
        a :=
        MappingTorusHomology.kernelBoundary (ThreefoldOverlapMappingTorus.monodromy none) n a.val
      map_zero' :=
        (MappingTorusHomology.kernelBoundary (ThreefoldOverlapMappingTorus.monodromy none)
            n).map_zero
      map_add' a
        b :=
        (MappingTorusHomology.kernelBoundary (ThreefoldOverlapMappingTorus.monodromy none)
              n).map_add
          a.val b.val }

private theorem ThreefoldHomologyCuspFibre.cuspCapKernelWangDegreeMap_injective (n : ℕ) :
    Function.Injective (cuspCapKernelWangDegreeMap n) := by
  intro a b hab
  apply Subtype.ext
  apply cuspCap_wang_ext n a.val b.val
  · exact a.property.trans b.property.symm
  · exact congrArg Subtype.val hab

private theorem ThreefoldHomologyCuspFibre.cuspWang_cokernelInclusion_zero (n : ℕ)
    (a : CuspWangCokernel (n + 1)) :
    MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy none) n
        (MappingTorusHomology.cokernelInclusion (ThreefoldOverlapMappingTorus.monodromy none)
          (n + 1) a) =
      0 := by
  have ha :
    MappingTorusHomology.cokernelInclusion (ThreefoldOverlapMappingTorus.monodromy none) (n + 1)
        a ∈
      LinearMap.range
        (MappingTorusHomology.cokernelInclusion (ThreefoldOverlapMappingTorus.monodromy none)
          (n + 1)) :=
    ⟨a, rfl⟩
  rw [MappingTorusHomology.cokernelInclusion_range_eq_ker_kernelBoundary
      (ThreefoldOverlapMappingTorus.monodromy none) n] at ha
  exact congrArg Subtype.val ha

private def ThreefoldHomologyCuspFibre.cuspCapCorrectionDegree (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary Option.none)
        (n + 1)) :
    LinearMap.ker (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none (n + 1)) :=
  ⟨a -
      MappingTorusHomology.cokernelInclusion (ThreefoldOverlapMappingTorus.monodromy none) (n + 1)
        ((cuspFibreCoinvariantEquiv (n + 1)).symm
          (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none (n + 1) a)),
    by
    change ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none (n + 1) (a - _) = 0
    rw [map_sub]
    exact
      sub_eq_zero.mpr
        ((cuspFibreCoinvariantEquiv (n + 1)).apply_symm_apply
            (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none (n + 1) a)).symm⟩

private theorem ThreefoldHomologyCuspFibre.cuspCapCorrectionDegree_wang (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary Option.none)
        (n + 1)) :
    cuspCapKernelWangDegreeMap n (cuspCapCorrectionDegree n a) =
      MappingTorusHomology.kernelBoundary (ThreefoldOverlapMappingTorus.monodromy none) n a := by
  apply Subtype.ext
  change
    MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy none) n
        (a -
          MappingTorusHomology.cokernelInclusion (ThreefoldOverlapMappingTorus.monodromy none)
            (n + 1) _) =
      MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy none) n a
  rw [map_sub, cuspWang_cokernelInclusion_zero, sub_zero]

private theorem ThreefoldHomologyCuspFibre.cuspCapKernelWangDegreeMap_surjective (n : ℕ) :
    Function.Surjective (cuspCapKernelWangDegreeMap n) := by
  intro a
  obtain ⟨b, hb⟩ :=
    MappingTorusHomology.kernelBoundary_surjective (ThreefoldOverlapMappingTorus.monodromy none) n
      a
  exact ⟨cuspCapCorrectionDegree n b, (cuspCapCorrectionDegree_wang n b).trans hb⟩

private def ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree (n : ℕ) :
    LinearMap.ker
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none (n + 1)) ≃ₗ[ℤ]
      LinearMap.ker
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n) :=
  LinearEquiv.ofBijective (cuspCapKernelWangDegreeMap n)
    ⟨cuspCapKernelWangDegreeMap_injective n, cuspCapKernelWangDegreeMap_surjective n⟩

private theorem ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree_symm_wang (n : ℕ)
    (a :
      LinearMap.ker
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy none) n)) :
    MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy none) n
        ((cuspCapKernelWangEquivDegree n).symm a).val =
      a.val :=
  congrArg Subtype.val ((cuspCapKernelWangEquivDegree n).apply_symm_apply a)

private def ThreefoldHomology.CapElimination.ellipticOneClass (j : Elliptic.Kind) (a : Fin 2 → ℤ) :
    NativeCapKernel (Option.some j) 2 :=
  (PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv j 1).symm
    ((Elliptic.HigherHomology.surfaceH1Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
      a)

private theorem ThreefoldHomology.CapElimination.ellipticOneClass_wang (j : Elliptic.Kind)
    (a : Fin 2 → ℤ) :
    PeriodFamily.FlatTorus.singularH1Equiv
        (MappingTorusHomology.wangBoundary
          (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 1 (ellipticOneClass j a).val) =
      a 1 • j.twist +
        ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) * a 0 -
            PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection j * a 1) •
          PeriodFamily.Boundary.EllipticCapKernelWang.deltaVector := by
  have h :=
    PeriodFamily.Boundary.EllipticCapKernelWang.capKernel_wang_h1_coordinates j
      ((Elliptic.HigherHomology.surfaceH1Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
        a)
  simpa only [LinearEquiv.apply_symm_apply, ellipticOneClass] using! h

private def
    ThreefoldHomology.CapElimination.ellipticThreeClass (j : Elliptic.Kind) (a : Fin 2 → ℤ) :
    NativeCapKernel (Option.some j) 4 :=
  (PeriodFamily.Boundary.EllipticCapProduct.boundaryCapH4KernelEquiv j).symm a

private theorem ThreefoldHomology.CapElimination.ellipticThreeClass_wang (j : Elliptic.Kind)
    (a : Fin 2 → ℤ) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (MappingTorusHomology.wangBoundary
          (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 3
          (ellipticThreeClass j a).val) =
      PeriodFamily.Boundary.EllipticCapKernelWang.topWangMatrix j
          (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree j) *ᵥ
        a :=
  PeriodFamily.Boundary.EllipticCapKernelWang.capKernelWangH4Coordinates_symm j a

private theorem ThreefoldHomology.CapElimination.cuspMonodromy_three_coordinates
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (MappingTorusHomology.monodromyHomologyMap
          (ThreefoldOverlapMappingTorus.monodromy Option.none) 3 a) =
      PeriodTorusHigherHomologyExterior.cubeM₀ *ᵥ
        PeriodFamily.FlatTorus.singularH3Coordinates a := by
  have h := LinearMap.congr_fun (PeriodFamily.Boundary.Cusp.monodromyHomology_triangle 3) a
  have h' :
    MappingTorusHomology.monodromyHomologyMap (ThreefoldOverlapMappingTorus.monodromy Option.none)
        3 a =
      PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleCuspGenerator 3 a :=
    h
  rw [h']
  change
    PeriodFamily.FlatTorus.singularH3Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph SpecialPeriods.triangleCuspGenerator :
            C(RealTorus₄, RealTorus₄))
          3 a) =
      _
  rw [PeriodFamily.FlatTorus.singularH3Coordinates_inducedHomology_triangle,
    SpecialPeriods.triangleDualRepresentation_cusp_matrix]
  rfl

private def ThreefoldHomology.CapElimination.cuspOneInvariant (v : Lattice) (hv : M₀ *ᵥ v = v) :
    LinearMap.ker
      (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy Option.none)
        1) :=
  ⟨PeriodFamily.FlatTorus.singularH1Equiv.symm v,
    by
    apply PeriodFamily.FlatTorus.singularH1Equiv.injective
    change
      PeriodFamily.FlatTorus.singularH1Equiv
          (PeriodFamily.FlatTorus.singularH1Equiv.symm v -
            MappingTorusHomology.monodromyHomologyMap
              (ThreefoldOverlapMappingTorus.monodromy Option.none) 1
              (PeriodFamily.FlatTorus.singularH1Equiv.symm v)) =
        _
    rw [map_sub, ThreefoldHomology.BoundaryFirst.boundaryMonodromy_one_coordinates,
      LinearEquiv.apply_symm_apply, map_zero]
    exact sub_eq_zero.mpr hv.symm⟩

private def ThreefoldHomology.CapElimination.cuspThreeInvariant (v : Lattice)
    (hv : PeriodTorusHigherHomologyExterior.cubeM₀ *ᵥ v = v) :
    LinearMap.ker
      (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy Option.none)
        3) :=
  ⟨PeriodFamily.FlatTorus.singularH3Coordinates.symm v,
    by
    apply PeriodFamily.FlatTorus.singularH3Coordinates.injective
    change
      PeriodFamily.FlatTorus.singularH3Coordinates
          (PeriodFamily.FlatTorus.singularH3Coordinates.symm v -
            MappingTorusHomology.monodromyHomologyMap
              (ThreefoldOverlapMappingTorus.monodromy Option.none) 3
              (PeriodFamily.FlatTorus.singularH3Coordinates.symm v)) =
        _
    rw [map_sub, cuspMonodromy_three_coordinates, LinearEquiv.apply_symm_apply, map_zero]
    exact sub_eq_zero.mpr hv.symm⟩

private def ThreefoldHomology.CapElimination.cuspOneClass (v : Lattice) (hv : M₀ *ᵥ v = v) :
    NativeCapKernel Option.none 2 :=
  (ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree 1).symm (cuspOneInvariant v hv)

private theorem
    ThreefoldHomology.CapElimination.cuspOneClass_wang (v : Lattice) (hv : M₀ *ᵥ v = v) :
    PeriodFamily.FlatTorus.singularH1Equiv
        (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy Option.none) 1
          (cuspOneClass v hv).val) =
      v := by
  change
    PeriodFamily.FlatTorus.singularH1Equiv
        (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy Option.none) 1
          ((ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree 1).symm
              (cuspOneInvariant v hv)).val) =
      v
  rw [ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree_symm_wang]
  exact LinearEquiv.apply_symm_apply _ _

private def ThreefoldHomology.CapElimination.cuspThreeClass (v : Lattice)
    (hv : PeriodTorusHigherHomologyExterior.cubeM₀ *ᵥ v = v) : NativeCapKernel Option.none 4 :=
  (ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree 3).symm (cuspThreeInvariant v hv)

private theorem ThreefoldHomology.CapElimination.cuspThreeClass_wang (v : Lattice)
    (hv : PeriodTorusHigherHomologyExterior.cubeM₀ *ᵥ v = v) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy Option.none) 3
          (cuspThreeClass v hv).val) =
      v := by
  change
    PeriodFamily.FlatTorus.singularH3Coordinates
        (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy Option.none) 3
          ((ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree 3).symm
              (cuspThreeInvariant v hv)).val) =
      v
  rw [ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree_symm_wang]
  exact LinearEquiv.apply_symm_apply _ _

private def ThreefoldHomology.SecondSource.nativeSourceClasses (x y : Lattice) :
    ∀ i : SpecialPeriods.Threefold.Puncture, ThreefoldHomology.CapElimination.NativeCapKernel i 2
  | none =>
    ThreefoldHomology.CapElimination.cuspOneClass
      (cuspCoordinates
        (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.four) x y)
      (cuspCoordinates_fixed
        (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.four) x y)
  | some .three =>
    ThreefoldHomology.CapElimination.ellipticOneClass .three
      (threeCoordinates
        (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.three)
        (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.four) x y)
  | some .four => ThreefoldHomology.CapElimination.ellipticOneClass .four (fourCoordinates x y)

private theorem ThreefoldHomology.SecondSource.nativeSourceClasses_wang_three (x y : Lattice) :
    PeriodFamily.FlatTorus.singularH1Equiv
        (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 1 (nativeSourceClasses x y)
          (Option.some .three)) =
      threeWangVector
        (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.three)
        (threeCoordinates
          (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.three)
          (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.four) x
          y) := by
  have h :=
    ThreefoldHomology.CapElimination.ellipticOneClass_wang .three
      (threeCoordinates
        (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.three)
        (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.four) x y)
  simpa only [Elliptic.HigherHomology.fibreNormIndex_three, Nat.cast_one, one_mul,
    Elliptic.Kind.twist, threeWangVector] using! h

private theorem ThreefoldHomology.SecondSource.nativeSourceClasses_wang_four (x y : Lattice) :
    PeriodFamily.FlatTorus.singularH1Equiv
        (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 1 (nativeSourceClasses x y)
          (Option.some .four)) =
      fourWangVector
        (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.four)
        (fourCoordinates x y) := by
  have h := ThreefoldHomology.CapElimination.ellipticOneClass_wang .four (fourCoordinates x y)
  simpa only [Elliptic.HigherHomology.fibreNormIndex_four, Nat.cast_ofNat, Elliptic.Kind.twist,
    fourWangVector] using! h

private theorem ThreefoldHomology.SecondSource.nativeSourceClasses_wang_cusp (x y : Lattice) :
    PeriodFamily.FlatTorus.singularH1Equiv
        (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 1 (nativeSourceClasses x y)
          Option.none) =
      cuspCoordinates
        (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.four) x y :=
  ThreefoldHomology.CapElimination.cuspOneClass_wang _ _

private theorem
    ThreefoldHomology.SecondSource.nativeSourceClasses_source_coordinates (x y : Lattice)
    (hxy : TrianglePeriodFamilyHomologyLattice.deltaOne (x, y) = 0) :
    (PeriodFamily.FlatTorus.singularH1Equiv
          (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 1
                (nativeSourceClasses x y)).val.1,
        PeriodFamily.FlatTorus.singularH1Equiv
          (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 1
                (nativeSourceClasses x y)).val.2) =
      (x, y) := by
  rw [ThreefoldHomology.CapElimination.nativeCapKernelSourceMap_one_coordinates]
  simp only [nativeSourceClasses_wang_three, nativeSourceClasses_wang_four,
    nativeSourceClasses_wang_cusp]
  exact
    Prod.ext
      (threeCoordinates_reconstruct
        (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.three)
        (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.four) x y
        hxy)
      (fourCoordinates_reconstruct
        (PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection Elliptic.Kind.four) x y
        hxy)

private theorem ThreefoldHomology.SecondSource.nativeCapKernelSourceMap_one_surjective :
    Function.Surjective (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 1) := by
  intro a
  have hxy :
    TrianglePeriodFamilyHomologyLattice.deltaOne
        (PeriodFamily.FlatTorus.singularH1Equiv a.val.1,
          PeriodFamily.FlatTorus.singularH1Equiv a.val.2) =
      0 := by
    have h := PeriodFamily.HomologyDifference.sourceDifferenceOne_coordinates a.val
    rw [show PeriodFamily.Homology.sourceDifference 1 a.val = 0 from a.property, map_zero] at h
    exact h.symm
  have h :=
    nativeSourceClasses_source_coordinates (PeriodFamily.FlatTorus.singularH1Equiv a.val.1)
      (PeriodFamily.FlatTorus.singularH1Equiv a.val.2) hxy
  refine
    ⟨nativeSourceClasses (PeriodFamily.FlatTorus.singularH1Equiv a.val.1)
        (PeriodFamily.FlatTorus.singularH1Equiv a.val.2),
      ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact PeriodFamily.FlatTorus.singularH1Equiv.injective (congrArg Prod.fst h)
  · exact PeriodFamily.FlatTorus.singularH1Equiv.injective (congrArg Prod.snd h)

private theorem ThreefoldHomology.CapElimination.exists_fibre_capKernel_decomposition (n : ℕ)
    (hs : Function.Surjective (nativeCapKernelSourceMap n))
    (r :
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily
        (n + 1)) :
    ∃ b : SingularMayerVietoris.SingularHomology RealTorus₄ (n + 1),
      ∃ a : ∀ i : SpecialPeriods.Threefold.Puncture, NativeCapKernel i (n + 1),
        SingularMayerVietoris.singularHomologyMap
              (PeriodFamily.Homology.familyFibreInclusion
                (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                  SpecialPeriods.specialPeriodMap_generator₁
                  SpecialPeriods.specialPeriodMap_generator₂)
                PeriodFamily.Homology.normalizedSlitBaseLift)
              (n + 1) b +
            nativeCapKernelRegularMap (n + 1) a =
          r := by
  obtain ⟨a, ha⟩ :=
    hs
      (PeriodFamily.Homology.sourceKernelProjection
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        n r)
  have hr :
    r - nativeCapKernelRegularMap (n + 1) a ∈
      LinearMap.ker
        (PeriodFamily.Homology.sourceKernelProjection
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          n) := by
    change
      PeriodFamily.Homology.sourceKernelProjection
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          n (r - nativeCapKernelRegularMap (n + 1) a) =
        0
    rw [map_sub, ← nativeCapKernelSourceMap_apply, ha, sub_self]
  rw [PeriodFamily.Homology.sourceKernelProjection_kernel] at hr
  obtain ⟨b, hb⟩ := hr
  exact ⟨b, a, hb ▸ sub_add_cancel r (nativeCapKernelRegularMap (n + 1) a)⟩

private theorem ThreefoldHomology.CapElimination.nativeCapKernelRegularMap_surjective_of_fibre_range
    (n : ℕ) (hs : Function.Surjective (nativeCapKernelSourceMap n))
    (hf :
      LinearMap.range
          (SingularMayerVietoris.singularHomologyMap
            (PeriodFamily.Homology.familyFibreInclusion
              (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)
              PeriodFamily.Homology.normalizedSlitBaseLift)
            (n + 1)) ≤
        LinearMap.range (nativeCapKernelRegularMap (n + 1))) :
    Function.Surjective (nativeCapKernelRegularMap (n + 1)) := by
  intro r
  obtain ⟨b, a, hr⟩ := exists_fibre_capKernel_decomposition n hs r
  obtain ⟨c, hc⟩ := hf ⟨b, rfl⟩
  refine ⟨c + a, ?_⟩
  rw [map_add, hc]
  exact hr

private def ThreefoldHomology.CapElimination.regularFibreIntoSpace :
    C(RealTorus₄, SpecialPeriods.Threefold.Space) :=
  ThreefoldHomology.originalRegularInclusion.comp
    (PeriodFamily.Homology.familyFibreInclusion
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
      PeriodFamily.Homology.normalizedSlitBaseLift)

private theorem ThreefoldHomology.CapElimination.regularFibreIntoSpace_homology (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap regularFibreIntoSpace n =
      (SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion
            n).comp
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            PeriodFamily.Homology.normalizedSlitBaseLift)
          n) :=
  PeriodTorusHigherHomology.singularHomologyMap_comp _ _ _

private theorem ThreefoldHomology.CapElimination.regularFibreIntoSpace_homology_surjective (n : ℕ)
    (hs : Function.Surjective (nativeCapKernelSourceMap n))
    (hr :
      Function.Surjective
        (SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion
          (n + 1))) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap regularFibreIntoSpace (n + 1)) := by
  intro x
  obtain ⟨r, hr⟩ := hr x
  obtain ⟨b, a, hb⟩ := exists_fibre_capKernel_decomposition n hs r
  have hz :
    SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion (n + 1)
        (nativeCapKernelRegularMap (n + 1) a) =
      0 :=
    (regularInclusion_eq_zero_iff_native (n + 1) _).mpr ⟨a, rfl⟩
  refine ⟨b, ?_⟩
  rw [regularFibreIntoSpace_homology, LinearMap.comp_apply]
  have h :=
    congrArg
      (SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion
        (n + 1))
      hb
  rw [map_add, hz, add_zero, hr] at h
  exact h

private theorem ThreefoldHomology.CapElimination.starLeft_surjective_of_nativeCapKernel (n : ℕ)
    (h : Function.Surjective (nativeCapKernelRegularMap n)) :
    Function.Surjective (ThreefoldHomology.starLeftHomologyMap n) := by
  intro p
  obtain ⟨b, hb⟩ := starOverlapToFillingsHomologyMap_surjective n (-p.2)
  have hrel :
    p.1 - ThreefoldHomology.starOverlapToRegularHomologyMap n b ∈
      LinearMap.range (nativeCapKernelRegularMap n) :=
    h (p.1 - ThreefoldHomology.starOverlapToRegularHomologyMap n b)
  rw [nativeCapKernelRegularMap_range] at hrel
  obtain ⟨c, hc⟩ := hrel
  have hc' :
    ThreefoldHomology.starOverlapToRegularHomologyMap n c.val =
      p.1 - ThreefoldHomology.starOverlapToRegularHomologyMap n b :=
    hc
  refine ⟨c.val + b, ?_⟩
  rw [starLeft_regular_fillings]
  apply Prod.ext
  · change ThreefoldHomology.starOverlapToRegularHomologyMap n (c.val + b) = p.1
    rw [map_add, hc', sub_add_cancel]
  · change -ThreefoldHomology.starOverlapToFillingsHomologyMap n (c.val + b) = p.2
    rw [map_add, c.property, zero_add, hb, neg_neg]

private theorem ThreefoldHomology.SecondDegree.regularFibre_homologyTwo_surjective :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap
        ThreefoldHomology.CapElimination.regularFibreIntoSpace 2) :=
  ThreefoldHomology.CapElimination.regularFibreIntoSpace_homology_surjective 1
    ThreefoldHomology.SecondSource.nativeCapKernelSourceMap_one_surjective
    ThreefoldHomology.CapElimination.regularInclusion_two_surjective

private def ThreefoldHomology.SecondDegree.homologyTwoCyclicMap :
    ℤ →ₗ[ℤ] SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 2 :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun
        z :=
        SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion 2
          (PeriodFamily.Homology.sourceCoinvariantInclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            2 (PeriodFamily.HomologyDifference.cokernelTwoEquiv.symm z))
      map_zero' := by rw [map_zero, map_zero, map_zero]
      map_add' a b := by rw [map_add, map_add, map_add] }

private theorem ThreefoldHomology.SecondDegree.homologyTwoCyclicMap_quotient
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    homologyTwoCyclicMap
        (PeriodFamily.HomologyDifference.cokernelTwoEquiv (Submodule.Quotient.mk a)) =
      SingularMayerVietoris.singularHomologyMap
        ThreefoldHomology.CapElimination.regularFibreIntoSpace 2 a := by
  change
    SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion 2
        (PeriodFamily.Homology.sourceCoinvariantInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          2
          (PeriodFamily.HomologyDifference.cokernelTwoEquiv.symm
            (PeriodFamily.HomologyDifference.cokernelTwoEquiv (Submodule.Quotient.mk a)))) =
      _
  rw [LinearEquiv.symm_apply_apply, PeriodFamily.Homology.sourceCoinvariantInclusion_mk,
    ThreefoldHomology.CapElimination.regularFibreIntoSpace_homology, LinearMap.comp_apply]

private theorem ThreefoldHomology.SecondDegree.homologyTwoCyclicMap_surjective :
    Function.Surjective homologyTwoCyclicMap := by
  intro x
  obtain ⟨a, ha⟩ := regularFibre_homologyTwo_surjective x
  exact
    ⟨PeriodFamily.HomologyDifference.cokernelTwoEquiv (Submodule.Quotient.mk a),
      (homologyTwoCyclicMap_quotient a).trans ha⟩

private theorem ThreefoldHomology.SecondDegree.regularFibre_homologyTwo_coordinates
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    SingularMayerVietoris.singularHomologyMap
        ThreefoldHomology.CapElimination.regularFibreIntoSpace 2 a =
      homologyTwoCyclicMap
        (6 * PeriodFamily.FlatTorus.singularH2Coordinates a 2 +
          PeriodFamily.FlatTorus.singularH2Coordinates a 3) := by
  rw [← PeriodFamily.HomologyDifference.cokernelTwoEquiv_mk]
  exact (homologyTwoCyclicMap_quotient a).symm

private def ThreefoldHomology.SecondDegree.homologyTwoGenerator :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 2 :=
  homologyTwoCyclicMap 1

private theorem ThreefoldHomology.SecondDegree.homologyTwoCyclicMap_eq_smul (z : ℤ) :
    homologyTwoCyclicMap z = z • homologyTwoGenerator := by
  simpa [homologyTwoGenerator] using map_zsmul homologyTwoCyclicMap z (1 : ℤ)

private theorem ThreefoldHomology.SecondDegree.homologyTwo_subsingleton_iff_generator_eq_zero :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 2) ↔
      homologyTwoGenerator = 0 := by
  constructor
  · intro h
    exact h.elim _ _
  · intro h
    have hz (x : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 2) :
      x = 0 := by
      obtain ⟨z, rfl⟩ := homologyTwoCyclicMap_surjective x
      rw [homologyTwoCyclicMap_eq_smul, h]
      exact
        @zsmul_zero (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 2) _ z
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩

private def ThreefoldHomology.EllipticFibre.centralRealCover (j : Elliptic.Kind) :
    C(RealTorus₄, ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) :=
  (Elliptic.HigherHomology.periodCover j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j)).comp
    ⟨Elliptic.flatTorusPeriodHomeomorph
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val,
      (Elliptic.flatTorusPeriodHomeomorph
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val).continuous⟩

private theorem ThreefoldHomology.EllipticFibre.centralBoundary_fibre (j : Elliptic.Kind) :
    (ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j).comp
        (MappingTorus.HomologyCover.fibreInclusion
          (ThreefoldOverlapMappingTorus.monodromy (Option.some j))) =
      centralRealCover j := by
  apply ContinuousMap.ext
  intro x
  exact ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_mk j 0 x

private theorem
    ThreefoldHomology.EllipticFibre.fibreToFilling_centralRetraction (j : Elliptic.Kind) :
    (SpecialPeriods.Threefold.EllipticGeometry.pieceSurfaceRetraction j).comp
        (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) =
      centralRealCover j := by
  rw [ThreefoldOverlapMappingTorus.fibreToFilling,
    ThreefoldOverlapMappingTorus.boundaryToFilling_elliptic]
  exact centralBoundary_fibre j

private def ThreefoldHomology.EllipticFibre.centralPeriodHomologyEquiv (j : Elliptic.Kind) (n : ℕ) :
    SingularMayerVietoris.SingularHomology RealTorus₄ n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val.Torus n :=
  PeriodTorusHigherHomology.homeomorphHomologyEquiv
    (Elliptic.flatTorusPeriodHomeomorph
      (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val)
    n

private theorem
    ThreefoldHomology.EllipticFibre.fibreToFilling_homology_retraction (j : Elliptic.Kind)
    (n : ℕ) :
    (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j n).toLinearMap.comp
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) n) =
      (SingularMayerVietoris.singularHomologyMap
            (Elliptic.HigherHomology.periodCover j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
              (Elliptic.mainTwist_admissible j))
            n).comp
        (centralPeriodHomologyEquiv j n).toLinearMap := by
  have h₁ :=
    PeriodTorusHigherHomology.singularHomologyMap_comp
      (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j))
      (SpecialPeriods.Threefold.EllipticGeometry.pieceSurfaceRetraction j) n
  have h₀ :=
    congrArg
      (fun f : C(RealTorus₄, SpecialPeriods.EllipticFilling.SpecialCentralSurface j) =>
        SingularMayerVietoris.singularHomologyMap f n)
      (fibreToFilling_centralRetraction j)
  have h₂ :=
    PeriodTorusHigherHomology.singularHomologyMap_comp
      (⟨Elliptic.flatTorusPeriodHomeomorph
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val,
          (Elliptic.flatTorusPeriodHomeomorph
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val).continuous⟩ :
        C(RealTorus₄,
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val.Torus))
      (Elliptic.HigherHomology.periodCover j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j))
      n
  exact h₁.symm.trans (h₀.trans h₂)

private theorem
    ThreefoldHomology.EllipticFibre.fibreToFilling_homology_eq_zero_iff (j : Elliptic.Kind)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) n a =
        0 ↔
      SingularMayerVietoris.singularHomologyMap
          (Elliptic.HigherHomology.periodCover j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
            (Elliptic.mainTwist_admissible j))
          n (centralPeriodHomologyEquiv j n a) =
        0 := by
  have h := LinearMap.congr_fun (fibreToFilling_homology_retraction j n) a
  change
    ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j n
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) n a) =
      SingularMayerVietoris.singularHomologyMap
        (Elliptic.HigherHomology.periodCover j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
          (Elliptic.mainTwist_admissible j))
        n (centralPeriodHomologyEquiv j n a) at h
  rw [← h]
  exact
    (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j n).map_eq_zero_iff.symm

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private def ThreefoldHomology.DeltaSweep.realParameterAddHom : ℝ →+ Additive ℂˣ
    where
  toFun
    t :=
    Additive.ofMul
      (SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential (t : ℂ))
  map_zero' := by
    change
      SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential ((0 : ℝ) : ℂ) = 1
    exact SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_zero
  map_add' s
    t := by
    change
      SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential
          ((s + t : ℝ) : ℂ) =
        SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential (s : ℂ) *
          SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential (t : ℂ)
    rw [Complex.ofReal_add,
      SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_add]

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private def ThreefoldHomology.DeltaSweep.circleParameterAddHom :
    (PeriodTorusHigherHomology.CircleTopology.Circle) →+ Additive ℂˣ :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℝ)) realParameterAddHom
    (by
      intro t ht
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
      have he : t = (k : ℝ) := by simpa only [zsmul_one] using hk.symm
      change SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential (t : ℂ) = 1
      rw [he]
      simpa only [Complex.ofReal_intCast] using
        SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_int k)

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private def ThreefoldHomology.DeltaSweep.circleParameter
    (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) : ℂˣ :=
  Additive.toMul (circleParameterAddHom t)

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
@[simp]
private theorem ThreefoldHomology.DeltaSweep.circleParameter_real (t : ℝ) :
    circleParameter (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential (t : ℂ) :=
  rfl

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private theorem
    ThreefoldHomology.DeltaSweep.circleParameter_continuous : Continuous circleParameter := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  exact
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_continuous.comp
      Complex.continuous_ofReal

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private def ThreefoldHomology.DeltaSweep.actionMap :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) × SpecialPeriods.Threefold.Space,
      SpecialPeriods.Threefold.Space) :=
  ⟨fun p => SpecialPeriods.Threefold.VerticalAction.actionBiholomorph (circleParameter p.1) p.2,
    by
    let := SpecialPeriods.Threefold.VerticalAction.action
    exact
      SpecialPeriods.Threefold.VerticalAction.action_holomorphic.continuous.comp
        ((circleParameter_continuous.comp continuous_fst).prodMk continuous_snd)⟩

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
@[simp]
private theorem ThreefoldHomology.DeltaSweep.actionMap_apply
    (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) (x : SpecialPeriods.Threefold.Space) :
    actionMap (t, x) =
      SpecialPeriods.Threefold.VerticalAction.actionBiholomorph (circleParameter t) x :=
  rfl

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private theorem
    ThreefoldHomology.DeltaSweep.actionMap_real (t : ℝ) (x : SpecialPeriods.Threefold.Space) :
    actionMap ((t : (PeriodTorusHigherHomology.CircleTopology.Circle)), x) =
      SpecialPeriods.Threefold.VerticalAction.flow (t : ℂ) x := by
  rw [actionMap_apply, circleParameter_real,
    SpecialPeriods.Threefold.VerticalAction.actionBiholomorph_exponential]

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private def ThreefoldHomology.DeltaSweep.centralInclusionMap (j : Elliptic.Kind) :
    C(SpecialPeriods.EllipticFilling.SpecialCentralSurface j, SpecialPeriods.Threefold.Space) :=
  ⟨SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceInclusion j,
    SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceInclusion_continuous j⟩

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private theorem ThreefoldHomology.DeltaSweep.actionMap_central_mem_fibre (j : Elliptic.Kind)
    (t : (PeriodTorusHigherHomology.CircleTopology.Circle))
    (x : SpecialPeriods.EllipticFilling.SpecialCentralSurface j) :
    actionMap (t, centralInclusionMap j x) ∈
      SpecialPeriods.Threefold.projectionSphere ⁻¹'
        {SpecialPeriods.Threefold.EllipticGeometry.sphereValue j} := by
  let := SpecialPeriods.Threefold.VerticalAction.action
  change
    SpecialPeriods.Threefold.projectionSphere (actionMap (t, centralInclusionMap j x)) =
      SpecialPeriods.Threefold.EllipticGeometry.sphereValue j
  exact
    (SpecialPeriods.Threefold.VerticalAction.projectionSphere_action (circleParameter t)
          (centralInclusionMap j x)).trans
      (SpecialPeriods.Threefold.EllipticGeometry.projectionSphere_centralSurfaceInclusion j x)

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private def ThreefoldHomology.DeltaSweep.centralActionMap (j : Elliptic.Kind) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
        SpecialPeriods.EllipticFilling.SpecialCentralSurface j,
      SpecialPeriods.EllipticFilling.SpecialCentralSurface j)
    where
  toFun
    p :=
    (SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceFibreHomeomorph j).symm
      ⟨actionMap (p.1, centralInclusionMap j p.2), actionMap_central_mem_fibre j p.1 p.2⟩
  continuous_toFun :=
    (SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceFibreHomeomorph
          j).symm.continuous.comp
      ((actionMap.continuous.comp
            (continuous_fst.prodMk
              ((centralInclusionMap j).continuous.comp continuous_snd))).subtype_mk
        _)

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private theorem ThreefoldHomology.DeltaSweep.centralInclusionMap_actionMap (j : Elliptic.Kind)
    (t : (PeriodTorusHigherHomology.CircleTopology.Circle))
    (x : SpecialPeriods.EllipticFilling.SpecialCentralSurface j) :
    centralInclusionMap j (centralActionMap j (t, x)) = actionMap (t, centralInclusionMap j x) :=
  SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceFibreHomeomorph_symm_inclusion j _

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private theorem ThreefoldHomology.DeltaSweep.actionMap_centralInclusion (j : Elliptic.Kind)
    (t : (PeriodTorusHigherHomology.CircleTopology.Circle))
    (x : SpecialPeriods.EllipticFilling.SpecialCentralSurface j) :
    actionMap (t, centralInclusionMap j x) = centralInclusionMap j (centralActionMap j (t, x)) :=
  (centralInclusionMap_actionMap j t x).symm

private def ThreefoldHomology.DeltaSweep.deltaLattice : Lattice :=
  ![0, 0, 0, 1]

@[simp]
private theorem ThreefoldHomology.DeltaSweep.realCast_deltaLattice :
    Elliptic.realCast deltaLattice = Pi.basisFun ℝ (Fin 4) 3 := by
  ext i
  fin_cases i <;> simp [Elliptic.realCast, deltaLattice, Pi.basisFun_apply]

private def ThreefoldHomology.DeltaSweep.deltaCircle :
    C((PeriodTorusHigherHomology.CircleTopology.Circle), RealTorus₄) :=
  (PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm :
        C(PeriodTorusHigherHomology.ProductTorus 4, RealTorus₄)).comp
    (PeriodTorusHigherHomology.coordinateCircleMap deltaLattice)

@[simp]
private theorem ThreefoldHomology.DeltaSweep.flatTorusCircleHomeomorph_deltaCircle
    (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph (deltaCircle t) =
      PeriodTorusHigherHomology.coordinateCircleMap deltaLattice t :=
  PeriodTorusHigherHomology.flatTorusCircleHomeomorph.apply_symm_apply _

private theorem ThreefoldHomology.DeltaSweep.deltaCircle_real_apply (t : ℝ) :
    deltaCircle (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      standardLattice.mkQ (t • Pi.basisFun ℝ (Fin 4) 3) := by
  apply PeriodTorusHigherHomology.flatTorusCircleHomeomorph.injective
  rw [flatTorusCircleHomeomorph_deltaCircle,
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph_mkQ]
  ext i
  fin_cases i <;>
    simp [PeriodTorusHigherHomology.coordinateCircleMap_apply, deltaLattice,
      PeriodTorusHigherHomology.coordinateProjection_apply, Pi.basisFun_apply]

@[simp]
private theorem ThreefoldHomology.DeltaSweep.deltaCircle_zero : deltaCircle 0 = 0 := by
  apply PeriodTorusHigherHomology.flatTorusCircleHomeomorph.injective
  rw [flatTorusCircleHomeomorph_deltaCircle, PeriodTorusHigherHomology.coordinateCircleMap_zero,
    PeriodFamily.FlatTorus.flatTorusCircleHomeomorph_zero]

private theorem ThreefoldHomology.DeltaSweep.deltaCircle_positiveLoop :
    PeriodTorusHigherHomology.CirclePaths.positiveLoop.map deltaCircle.continuous =
      (PeriodFamily.FlatTorus.periodLoop deltaLattice).cast deltaCircle_zero deltaCircle_zero := by
  apply Path.ext
  funext t
  change
    deltaCircle (PeriodTorusHigherHomology.CirclePaths.positiveLoop t) =
      PeriodFamily.FlatTorus.periodLoop deltaLattice t
  rw [PeriodTorusHigherHomology.CirclePaths.positiveLoop_apply, deltaCircle_real_apply,
    PeriodFamily.FlatTorus.periodLoop_apply, realCast_deltaLattice]

private theorem ThreefoldHomology.DeltaSweep.deltaCircle_positiveLoop_homology :
    FirstHurewicz.inducedHomology deltaCircle
        (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) =
      PeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice := by
  rw [FirstHurewicz.inducedHomology_loopHomologyClass, deltaCircle_positiveLoop,
    PeriodFamily.FlatTorus.singularH1Equiv_symm_apply]
  rfl

private theorem ThreefoldHomology.DeltaSweep.deltaCircle_positiveLoop_singularHomology :
    SingularMayerVietoris.singularHomologyMap deltaCircle 1
        (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) =
      PeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice :=
  deltaCircle_positiveLoop_homology

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private def ThreefoldHomology.DeltaSweep.centralPeriodCoordinateHomeomorph (j : Elliptic.Kind) :
    RealTorus₄ ≃ₜ SpecialPeriods.EllipticFilling.SpecialCentralPeriodTorus j :=
  Elliptic.flatTorusPeriodHomeomorph
    (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private def ThreefoldHomology.DeltaSweep.centralFlatPeriodCover (j : Elliptic.Kind) :
    C(RealTorus₄, SpecialPeriods.EllipticFilling.SpecialCentralSurface j) :=
  (SpecialPeriods.EllipticFilling.specialCentralPeriodCover j).comp
    (centralPeriodCoordinateHomeomorph j :
      C(RealTorus₄, SpecialPeriods.EllipticFilling.SpecialCentralPeriodTorus j))

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private theorem
    ThreefoldHomology.DeltaSweep.specialCentralInclusion_flatPeriodCover (j : Elliptic.Kind)
    (y : RealTorus₄) :
    SpecialPeriods.EllipticFilling.specialCentralInclusion j (centralFlatPeriodCover j y) =
      (SpecialPeriods.EllipticFilling.specialLocalData j).quotient j.twist
        (Elliptic.mainTwist_admissible j) (SpecialPeriods.discZero, y) := by
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective y
  change
    (SpecialPeriods.EllipticFilling.specialLocalData j).centralFibreInclusion j.twist
        (Elliptic.mainTwist_admissible j)
        (Elliptic.surfaceProjection j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
          (Elliptic.mainTwist_admissible j)
          (Elliptic.flatProjection
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val x)) =
      _
  rw [Elliptic.Equivariant.Data.centralFibreInclusion_surfaceProjection,
    Elliptic.Equivariant.Data.centralInclusion_flatProjection]

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private theorem
    ThreefoldHomology.DeltaSweep.specialFlow_flatPeriodCover_real (j : Elliptic.Kind) (t : ℝ)
    (y : RealTorus₄) :
    SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFlow j (t : ℂ)
        (SpecialPeriods.Threefold.EllipticGeometry.pieceCentralInclusion j
          (centralFlatPeriodCover j y)) =
      SpecialPeriods.Threefold.EllipticGeometry.pieceCentralInclusion j
        (centralFlatPeriodCover j
          (deltaCircle (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) + y)) := by
  have hp :
    SpecialPeriods.Threefold.VerticalAction.Period.flow
        (SpecialPeriods.EllipticFilling.specialLocalData j).periods (t : ℂ)
        (SpecialPeriods.discZero, y) =
      (SpecialPeriods.discZero,
        deltaCircle (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) + y) := by
    rw [deltaCircle_real_apply]
    simp only [SpecialPeriods.Threefold.VerticalAction.Period.flow,
      SpecialPeriods.Threefold.FiniteActionFixed.Period.inverse_vector_real]
    exact Prod.ext rfl (add_comm _ _)
  apply Subtype.ext
  change
    SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFullFlow j (t : ℂ)
        (SpecialPeriods.EllipticFilling.specialCentralInclusion j (centralFlatPeriodCover j y)) =
      SpecialPeriods.EllipticFilling.specialCentralInclusion j
        (centralFlatPeriodCover j
          (deltaCircle (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) + y))
  rw [specialCentralInclusion_flatPeriodCover,
    SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFullFlow_quotient, hp,
    specialCentralInclusion_flatPeriodCover]

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private theorem
    ThreefoldHomology.DeltaSweep.actionMap_real_centralFlatPeriodCover (j : Elliptic.Kind)
    (t : ℝ) (y : RealTorus₄) :
    actionMap
        ((t : (PeriodTorusHigherHomology.CircleTopology.Circle)),
          centralInclusionMap j (centralFlatPeriodCover j y)) =
      centralInclusionMap j
        (centralFlatPeriodCover j
          (deltaCircle (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) + y)) := by
  rw [actionMap_real]
  change
    SpecialPeriods.Threefold.VerticalAction.flow (t : ℂ)
        (SpecialPeriods.Threefold.EllipticGeometry.inclusion j
          (SpecialPeriods.Threefold.EllipticGeometry.pieceCentralInclusion j
            (centralFlatPeriodCover j y))) =
      _
  rw [SpecialPeriods.Threefold.VerticalAction.flow_elliptic, specialFlow_flatPeriodCover_real]
  rfl

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private theorem ThreefoldHomology.DeltaSweep.actionMap_centralFlatPeriodCover (j : Elliptic.Kind)
    (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) (y : RealTorus₄) :
    actionMap (t, centralInclusionMap j (centralFlatPeriodCover j y)) =
      centralInclusionMap j (centralFlatPeriodCover j (deltaCircle t + y)) := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact actionMap_real_centralFlatPeriodCover j s y

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold in
private theorem ThreefoldHomology.DeltaSweep.centralActionMap_flatPeriodCover (j : Elliptic.Kind)
    (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) (y : RealTorus₄) :
    centralActionMap j (t, centralFlatPeriodCover j y) =
      centralFlatPeriodCover j (deltaCircle t + y) := by
  apply SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceInclusion_injective j
  change
    centralInclusionMap j (centralActionMap j (t, centralFlatPeriodCover j y)) =
      centralInclusionMap j (centralFlatPeriodCover j (deltaCircle t + y))
  rw [centralInclusionMap_actionMap]
  exact actionMap_centralFlatPeriodCover j t y

private theorem ThreefoldHomology.CentralFibreCompatibility.globalFibre_maps_agree
    (i : SpecialPeriods.Threefold.Puncture) :
    ThreefoldHomology.originalRegularInclusion.comp
        (ThreefoldOverlapMappingTorus.fibreToRegularFamily i) =
      (ThreefoldHomology.originalPieceInclusion (Option.some i)).comp
        (ThreefoldOverlapMappingTorus.fibreToFilling i) := by
  have h :=
    congrArg
      (fun f : C(ThreefoldOverlapMappingTorus.Boundary i, SpecialPeriods.Threefold.Space) =>
        f.comp
          (MappingTorus.HomologyCover.fibreInclusion (ThreefoldOverlapMappingTorus.monodromy i)))
      (ThreefoldOverlapMappingTorus.boundary_maps_agree i)
  simpa only [ThreefoldOverlapMappingTorus.fibreToRegularFamily,
    ThreefoldOverlapMappingTorus.fibreToFilling, ContinuousMap.comp_assoc] using h

private theorem ThreefoldHomology.CentralFibreCompatibility.regularFibreIntoSpace_homology_filling
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap
        ThreefoldHomology.CapElimination.regularFibreIntoSpace n =
      (SingularMayerVietoris.singularHomologyMap
            (ThreefoldHomology.originalPieceInclusion (Option.some i)) n).comp
        (SingularMayerVietoris.singularHomologyMap (ThreefoldOverlapMappingTorus.fibreToFilling i)
          n) := by
  rw [ThreefoldHomology.CapElimination.regularFibreIntoSpace_homology, ←
    PeriodFamily.Boundary.fibreToRegularFamily_homology_common i n, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, globalFibre_maps_agree,
    PeriodTorusHigherHomology.singularHomologyMap_comp]

private theorem
    ThreefoldHomology.CentralFibreCompatibility.fibreToFilling_homology_centralRetraction
    (j : Elliptic.Kind) (n : ℕ) :
    (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j n).toLinearMap.comp
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) n) =
      SingularMayerVietoris.singularHomologyMap
        (ThreefoldHomology.EllipticFibre.centralRealCover j) n := by
  have h :=
    congrArg
      (fun f : C(RealTorus₄, SpecialPeriods.EllipticFilling.SpecialCentralSurface j) =>
        SingularMayerVietoris.singularHomologyMap f n)
      (ThreefoldHomology.EllipticFibre.fibreToFilling_centralRetraction j)
  exact
    (PeriodTorusHigherHomology.singularHomologyMap_comp
          (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j))
          (SpecialPeriods.Threefold.EllipticGeometry.pieceSurfaceRetraction j) n).symm.trans
      h

private theorem ThreefoldHomology.CentralFibreCompatibility.fibreToFilling_homology_central
    (j : Elliptic.Kind) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) n =
      (SingularMayerVietoris.singularHomologyMap
            (SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceIntoPiece j) n).comp
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.EllipticFibre.centralRealCover j) n) := by
  apply LinearMap.ext
  intro a
  have h :=
    congrArg (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j n).symm
      (LinearMap.congr_fun (fibreToFilling_homology_centralRetraction j n) a)
  change
    SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) n a =
      (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j n).symm
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.EllipticFibre.centralRealCover j) n a)
  exact
    ((ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j n).symm_apply_apply
          _).symm.trans
      h

private theorem
    ThreefoldHomology.CentralFibreCompatibility.regularFibreIntoSpace_homology_eq_central
    (j : Elliptic.Kind) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap
        ThreefoldHomology.CapElimination.regularFibreIntoSpace n =
      (SingularMayerVietoris.singularHomologyMap
            (ThreefoldHomology.DeltaSweep.centralInclusionMap j) n).comp
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.DeltaSweep.centralFlatPeriodCover j) n) := by
  have hi :
    SingularMayerVietoris.singularHomologyMap (ThreefoldHomology.DeltaSweep.centralInclusionMap j)
        n =
      (SingularMayerVietoris.singularHomologyMap
            (ThreefoldHomology.originalPieceInclusion (Option.some (Option.some j))) n).comp
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceIntoPiece j) n) :=
    PeriodTorusHigherHomology.singularHomologyMap_comp
      (SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceIntoPiece j)
      (ThreefoldHomology.originalPieceInclusion (Option.some (Option.some j))) n
  apply LinearMap.ext
  intro a
  calc
    SingularMayerVietoris.singularHomologyMap
          ThreefoldHomology.CapElimination.regularFibreIntoSpace n a =
        SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.originalPieceInclusion (Option.some (Option.some j))) n
          (SingularMayerVietoris.singularHomologyMap
            (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) n a) :=
      LinearMap.congr_fun (regularFibreIntoSpace_homology_filling (Option.some j) n) a
    _ =
        SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.originalPieceInclusion (Option.some (Option.some j))) n
          (SingularMayerVietoris.singularHomologyMap
            (SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceIntoPiece j) n
            (SingularMayerVietoris.singularHomologyMap
              (ThreefoldHomology.EllipticFibre.centralRealCover j) n a)) :=
      (congrArg
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.originalPieceInclusion (Option.some (Option.some j))) n)
        (LinearMap.congr_fun (fibreToFilling_homology_central j n) a))
    _ =
        SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.DeltaSweep.centralInclusionMap j) n
          (SingularMayerVietoris.singularHomologyMap
            (ThreefoldHomology.DeltaSweep.centralFlatPeriodCover j) n a) :=
      (LinearMap.congr_fun hi
          (SingularMayerVietoris.singularHomologyMap
            (ThreefoldHomology.EllipticFibre.centralRealCover j) n a)).symm

private theorem
  ThreefoldHomology.CentralFibreCompatibility.regularFibreIntoSpace_homology_eq_central_apply
    (j : Elliptic.Kind) (n : ℕ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap
        ThreefoldHomology.CapElimination.regularFibreIntoSpace n a =
      SingularMayerVietoris.singularHomologyMap
        (ThreefoldHomology.DeltaSweep.centralInclusionMap j) n
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.DeltaSweep.centralFlatPeriodCover j) n a) :=
  LinearMap.congr_fun (regularFibreIntoSpace_homology_eq_central j n) a

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def ThreefoldHomology.DeltaSweep.sweep {X : Type} [TopologicalSpace X]
    (a : C((PeriodTorusHigherHomology.CircleTopology.Circle) × X, X)) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X (n + 1) :=
  (SingularMayerVietoris.singularHomologyMap a (n + 1)).comp
    (PeriodTorusHigherHomology.positiveCircleCross X n)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem ThreefoldHomology.DeltaSweep.sweep_apply {X : Type} [TopologicalSpace X]
    (a : C((PeriodTorusHigherHomology.CircleTopology.Circle) × X, X)) (n : ℕ)
    (v : SingularMayerVietoris.SingularHomology X n) :
    sweep a n v =
      SingularMayerVietoris.singularHomologyMap a (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross X n v) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    ThreefoldHomology.DeltaSweep.positiveCircleCross_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) (v : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap
        ((ContinuousMap.id (PeriodTorusHigherHomology.CircleTopology.Circle)).prodMap f) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross X n v) =
      PeriodTorusHigherHomology.positiveCircleCross Y n
        (SingularMayerVietoris.singularHomologyMap f n v) := by
  have h :=
    PeriodTorusHigherHomology.crossProductHomology_natural
      (ContinuousMap.id (PeriodTorusHigherHomology.CircleTopology.Circle)) f n
      (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) v
  change
    SingularMayerVietoris.singularHomologyMap
        ((ContinuousMap.id (PeriodTorusHigherHomology.CircleTopology.Circle)).prodMap f) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross X n v) =
      PeriodTorusHigherHomology.crossProductHomology
        (PeriodTorusHigherHomology.CircleTopology.Circle) Y n
        (SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.id (PeriodTorusHigherHomology.CircleTopology.Circle)) 1
          (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop))
        (SingularMayerVietoris.singularHomologyMap f n v) at h
  simpa only [PeriodTorusHigherHomology.positiveCircleCross,
    PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] using h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThreefoldHomology.DeltaSweep.sweep_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (aX : C((PeriodTorusHigherHomology.CircleTopology.Circle) × X, X))
    (aY : C((PeriodTorusHigherHomology.CircleTopology.Circle) × Y, Y)) (f : C(X, Y))
    (h :
      aY.comp ((ContinuousMap.id (PeriodTorusHigherHomology.CircleTopology.Circle)).prodMap f) =
        f.comp aX)
    (n : ℕ) (v : SingularMayerVietoris.SingularHomology X n) :
    sweep aY n (SingularMayerVietoris.singularHomologyMap f n v) =
      SingularMayerVietoris.singularHomologyMap f (n + 1) (sweep aX n v) := by
  calc
    _ =
        SingularMayerVietoris.singularHomologyMap aY (n + 1)
          (SingularMayerVietoris.singularHomologyMap
            ((ContinuousMap.id (PeriodTorusHigherHomology.CircleTopology.Circle)).prodMap f)
            (n + 1) (PeriodTorusHigherHomology.positiveCircleCross X n v)) := by
      rw [sweep_apply, positiveCircleCross_natural]
    _ =
        SingularMayerVietoris.singularHomologyMap
          (aY.comp
            ((ContinuousMap.id (PeriodTorusHigherHomology.CircleTopology.Circle)).prodMap f))
          (n + 1) (PeriodTorusHigherHomology.positiveCircleCross X n v) := by
      rw [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply]
    _ =
        SingularMayerVietoris.singularHomologyMap (f.comp aX) (n + 1)
          (PeriodTorusHigherHomology.positiveCircleCross X n v) := by rw [h]
    _ = _ := by
      rw [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply, sweep_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThreefoldHomology.DeltaSweep.sweep_natural_of_equivariant {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (aX : C((PeriodTorusHigherHomology.CircleTopology.Circle) × X, X))
    (aY : C((PeriodTorusHigherHomology.CircleTopology.Circle) × Y, Y)) (f : C(X, Y))
    (h : ∀ t x, aY (t, f x) = f (aX (t, x))) (n : ℕ)
    (v : SingularMayerVietoris.SingularHomology X n) :
    sweep aY n (SingularMayerVietoris.singularHomologyMap f n v) =
      SingularMayerVietoris.singularHomologyMap f (n + 1) (sweep aX n v) := by
  apply sweep_natural aX aY f ?_ n v
  apply ContinuousMap.ext
  intro p
  exact h p.1 p.2

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    ThreefoldHomology.DeltaSweep.additionSweepMap {G : Type} [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G] (b : C((PeriodTorusHigherHomology.CircleTopology.Circle), G)) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) × G, G) :=
  (PeriodTorusHigherHomologyPontryagin.additionMap G).comp (b.prodMap (ContinuousMap.id G))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThreefoldHomology.DeltaSweep.sweep_addition {G : Type} [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (b : C((PeriodTorusHigherHomology.CircleTopology.Circle), G)) (n : ℕ)
    (v : SingularMayerVietoris.SingularHomology G n) :
    sweep (additionSweepMap b) n v =
      PeriodTorusHigherHomologyPontryagin.product G n
        (SingularMayerVietoris.singularHomologyMap b 1
          (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop))
        v := by
  have h :=
    PeriodTorusHigherHomology.crossProductHomology_natural b (ContinuousMap.id G) n
      (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) v
  change
    SingularMayerVietoris.singularHomologyMap (b.prodMap (ContinuousMap.id G)) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross G n v) =
      PeriodTorusHigherHomology.crossProductHomology G G n
        (SingularMayerVietoris.singularHomologyMap b 1
          (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop))
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id G) n v) at h
  rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] at h
  rw [sweep_apply, additionSweepMap, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, h, PeriodTorusHigherHomologyPontryagin.product_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThreefoldHomology.DeltaSweep.sweep_equivariant_addition_of_comp_eq {X : Type}
    [TopologicalSpace X] {G : Type} [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G] (a : C((PeriodTorusHigherHomology.CircleTopology.Circle) × X, X))
    (b : C((PeriodTorusHigherHomology.CircleTopology.Circle), G)) (i : C(G, X))
    (h :
      a.comp ((ContinuousMap.id (PeriodTorusHigherHomology.CircleTopology.Circle)).prodMap i) =
        i.comp (additionSweepMap b))
    (n : ℕ) (v : SingularMayerVietoris.SingularHomology G n) :
    sweep a n (SingularMayerVietoris.singularHomologyMap i n v) =
      SingularMayerVietoris.singularHomologyMap i (n + 1)
        (PeriodTorusHigherHomologyPontryagin.product G n
          (SingularMayerVietoris.singularHomologyMap b 1
            (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop))
          v) := by rw [sweep_natural (additionSweepMap b) a i h, sweep_addition]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    ThreefoldHomology.DeltaSweep.sweep_equivariant_addition {X : Type} [TopologicalSpace X]
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (a : C((PeriodTorusHigherHomology.CircleTopology.Circle) × X, X))
    (b : C((PeriodTorusHigherHomology.CircleTopology.Circle), G)) (i : C(G, X))
    (h : ∀ t y, a (t, i y) = i (b t + y)) (n : ℕ)
    (v : SingularMayerVietoris.SingularHomology G n) :
    sweep a n (SingularMayerVietoris.singularHomologyMap i n v) =
      SingularMayerVietoris.singularHomologyMap i (n + 1)
        (PeriodTorusHigherHomologyPontryagin.product G n
          (SingularMayerVietoris.singularHomologyMap b 1
            (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop))
          v) := by
  apply sweep_equivariant_addition_of_comp_eq a b i ?_ n v
  apply ContinuousMap.ext
  intro p
  exact h p.1 p.2

private def ThreefoldHomology.DeltaSweep.globalSweep (n : ℕ) :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space (n + 1) :=
  sweep actionMap n

private theorem ThreefoldHomology.DeltaSweep.globalSweep_one_apply_eq_zero
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 1) :
    globalSweep 1 a = 0 := by
  rw [SpecialPeriods.Threefold.LowDegrees.singularH1_eq_zero a, map_zero]

private def ThreefoldHomology.DeltaSweep.centralSweep (j : Elliptic.Kind) (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        (SpecialPeriods.EllipticFilling.SpecialCentralSurface j) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.EllipticFilling.SpecialCentralSurface j) (n + 1) :=
  sweep (centralActionMap j) n

private theorem
    ThreefoldHomology.DeltaSweep.globalSweep_centralInclusion (j : Elliptic.Kind) (n : ℕ)
    (v :
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.EllipticFilling.SpecialCentralSurface j) n) :
    globalSweep n (SingularMayerVietoris.singularHomologyMap (centralInclusionMap j) n v) =
      SingularMayerVietoris.singularHomologyMap (centralInclusionMap j) (n + 1)
        (centralSweep j n v) :=
  sweep_natural_of_equivariant (centralActionMap j) actionMap (centralInclusionMap j)
    (actionMap_centralInclusion j) n v

private theorem ThreefoldHomology.DeltaSweep.centralSweep_global_eq_zero (j : Elliptic.Kind)
    (v :
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.EllipticFilling.SpecialCentralSurface j) 1) :
    SingularMayerVietoris.singularHomologyMap (centralInclusionMap j) 2 (centralSweep j 1 v) =
      0 := by
  rw [← globalSweep_centralInclusion j 1 v]
  exact globalSweep_one_apply_eq_zero _

private theorem
    ThreefoldHomology.DeltaSweep.centralSweep_flatPeriodCover (j : Elliptic.Kind) (n : ℕ)
    (v : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    centralSweep j n (SingularMayerVietoris.singularHomologyMap (centralFlatPeriodCover j) n v) =
      SingularMayerVietoris.singularHomologyMap (centralFlatPeriodCover j) (n + 1)
        (PeriodTorusHigherHomologyPontryagin.product RealTorus₄ n
          (PeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice) v) := by
  have h :=
    sweep_equivariant_addition (centralActionMap j) deltaCircle (centralFlatPeriodCover j)
      (centralActionMap_flatPeriodCover j) n v
  rw [deltaCircle_positiveLoop_singularHomology] at h
  exact h

private theorem ThreefoldHomology.DeltaSweep.flat_product11_exterior (a b : Lattice) :
    PeriodFamily.FlatTorus.singularH2Equiv
        (PeriodTorusHigherHomologyPontryagin.product11 RealTorus₄
          (PeriodFamily.FlatTorus.singularH1Equiv.symm a)
          (PeriodFamily.FlatTorus.singularH1Equiv.symm b)) =
      exteriorPower.ιMulti ℤ 2 ![a, b] := by
  rw [PeriodFamily.FlatTorus.singularH2Equiv_apply,
    PeriodTorusHigherHomologyPontryagin.product_natural _
      PeriodTorusHigherHomology.flatTorusCircleHomeomorph_add 1,
    PeriodFamily.FlatTorus.coordinateH1_flatMarking,
    PeriodFamily.FlatTorus.coordinateH1_flatMarking]
  calc
    _ =
        PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
          (PeriodTorusHigherHomology.coordinateTorusWedgeTwo
            (exteriorPower.ιMulti ℤ 2 ![a, b])) :=
      congrArg PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
        (PeriodTorusHigherHomology.coordinateTorusWedgeTwo_apply_ιMulti ![a, b]).symm
    _ = _ := PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv_wedge _

private theorem ThreefoldHomology.DeltaSweep.flat_product11_coordinates (a b : Lattice) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (PeriodTorusHigherHomologyPontryagin.product11 RealTorus₄
          (PeriodFamily.FlatTorus.singularH1Equiv.symm a)
          (PeriodFamily.FlatTorus.singularH1Equiv.symm b)) =
      ![a 0 * b 1 - a 1 * b 0, a 0 * b 2 - a 2 * b 0, a 0 * b 3 - a 3 * b 0,
        a 1 * b 2 - a 2 * b 1, a 1 * b 3 - a 3 * b 1, a 2 * b 3 - a 3 * b 2] := by
  rw [PeriodFamily.FlatTorus.singularH2Coordinates_apply, flat_product11_exterior]
  funext i
  rw [PeriodTorusHigherHomologyExterior.squareCoordinates_apply,
    PeriodTorusHigherHomologyExterior.squareBasis, Module.Basis.repr_reindex_apply]
  change
    ((Pi.basisFun ℤ (Fin 4)).exteriorPower 2).repr (exteriorPower.ιMulti ℤ 2 ![a, b])
        (PeriodTorusHigherHomologyExterior.pairSubset i) =
      _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [PeriodTorusHigherHomologyExterior.pairSubset_ordered, Module.Basis.coord_apply,
    Pi.basisFun_repr]
  fin_cases i <;> simp [LocalSystemMatrices.pairIndices, Matrix.det_fin_two, mul_comm]

private theorem ThreefoldHomology.DeltaSweep.flat_delta_product11_coordinates (v : Lattice) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (PeriodTorusHigherHomologyPontryagin.product11 RealTorus₄
          (PeriodFamily.FlatTorus.singularH1Equiv.symm ![0, 0, 0, 1])
          (PeriodFamily.FlatTorus.singularH1Equiv.symm v)) =
      ![0, 0, -v 0, 0, -v 1, -v 2] := by
  rw [flat_product11_coordinates]
  simp

private theorem
    ThreefoldHomology.DeltaSweep.centralFlatPeriodCover_eq_surfaceCover (j : Elliptic.Kind) :
    centralFlatPeriodCover j = PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover j := by
  rw [PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_eq_periodCover]
  rfl

private theorem ThreefoldHomology.DeltaSweep.originalAffineNorm_delta_splitFibreClassOne
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm j 2
          (PeriodTorusHigherHomologyPontryagin.product11 RealTorus₄
            (PeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice)
            (PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassOne j))) =
      0 := by
  have hf :
    PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassOne j =
      PeriodFamily.FlatTorus.singularH1Equiv.symm ![0, 0, 1, 0] := by
    apply PeriodFamily.FlatTorus.singularH1Equiv.injective
    rw [PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassOne_coordinates,
      LinearEquiv.apply_symm_apply]
  rw [hf, PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_h2_coordinates,
    deltaLattice, flat_delta_product11_coordinates]
  cases j
  · rw [PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixTwo_three]
    decide
  · rw [PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixTwo_four]
    decide

private theorem ThreefoldHomology.DeltaSweep.originalAffineNorm_delta_splitCircleClassOne
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm j 2
          (PeriodTorusHigherHomologyPontryagin.product11 RealTorus₄
            (PeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice)
            (PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassOne j))) =
      -(j.order : ℤ) • PeriodFamily.Boundary.EllipticCapKernelWang.twistDeltaVector j := by
  have hc :
    PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassOne j =
      PeriodFamily.FlatTorus.singularH1Equiv.symm j.twist := by
    apply PeriodFamily.FlatTorus.singularH1Equiv.injective
    rw [PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassOne_coordinates,
      LinearEquiv.apply_symm_apply]
  rw [hc, PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_h2_coordinates,
    deltaLattice, flat_delta_product11_coordinates]
  cases j
  · rw [PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixTwo_three]
    decide
  · rw [PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixTwo_four]
    decide

private theorem
    ThreefoldHomology.DeltaSweep.centralSweep_h2Coordinates_surfaceCover (j : Elliptic.Kind)
    (v : SingularMayerVietoris.SingularHomology RealTorus₄ 1) :
    PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates j
        (centralSweep j 1
          (SingularMayerVietoris.singularHomologyMap
            (PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover j) 1 v)) =
      PeriodFamily.FlatTorus.singularH2Coordinates
        (PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm j 2
          (PeriodTorusHigherHomologyPontryagin.product11 RealTorus₄
            (PeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice) v)) := by
  rw [← centralFlatPeriodCover_eq_surfaceCover, centralSweep_flatPeriodCover,
    centralFlatPeriodCover_eq_surfaceCover,
    PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates_surfaceCover]

private theorem ThreefoldHomology.DeltaSweep.centralSweep_h2Coordinates (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.EllipticFilling.SpecialCentralSurface j) 1) :
    PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates j (centralSweep j 1 a) =
      -Elliptic.HigherHomology.surfaceH1Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 •
        PeriodFamily.Boundary.EllipticCapKernelWang.twistDeltaVector j := by
  have h :=
    PeriodFamily.Boundary.EllipticCapKernelWang.map_cover_columns
      (Elliptic.HigherHomology.surfaceH1Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod)
      ((PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates j).comp (centralSweep j 1))
      (SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover j) 1
        (PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassOne j))
      (SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover j) 1
        (PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassOne j))
      a (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearOne j) (j.order : ℤ)
      (PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitFibreClassOne j)
      (PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitCircleClassOne j)
  simp only [LinearMap.comp_apply, centralSweep_h2Coordinates_surfaceCover,
    originalAffineNorm_delta_splitFibreClassOne, originalAffineNorm_delta_splitCircleClassOne,
    smul_zero, zero_add] at h
  ext i
  apply mul_left_cancel₀ (show (j.order : ℤ) ≠ 0 by cases j <;> decide)
  have hi := congrFun h i
  change
    (j.order : ℤ) *
        PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates j (centralSweep j 1 a) i =
      Elliptic.HigherHomology.surfaceH1Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 *
        (-(j.order : ℤ) * PeriodFamily.Boundary.EllipticCapKernelWang.twistDeltaVector j i) at hi
  change
    (j.order : ℤ) *
        PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates j (centralSweep j 1 a) i =
      (j.order : ℤ) *
        (-Elliptic.HigherHomology.surfaceH1Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 *
          PeriodFamily.Boundary.EllipticCapKernelWang.twistDeltaVector j i)
  rw [hi]
  ring

private theorem ThreefoldHomology.DeltaSweep.centralSweep_secondCoordinate (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.EllipticFilling.SpecialCentralSurface j) 1) :
    Elliptic.HigherHomology.surfaceH2Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod (centralSweep j 1 a) 1 =
      -Elliptic.HigherHomology.surfaceH1Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 := by
  apply mul_right_cancel₀ (show j.twist 0 ≠ 0 by cases j <;> decide)
  have h := congrFun (centralSweep_h2Coordinates j a) (2 : Fin 6)
  rw [PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates_formula] at h
  simpa [PeriodFamily.Boundary.EllipticCapKernelWang.fibreInvariantPairVector,
    PeriodFamily.Boundary.EllipticCapKernelWang.twistDeltaVector] using h

private theorem
    ThreefoldHomology.DeltaSweep.centralSweep_firstCoordinate_mul_index (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.EllipticFilling.SpecialCentralSurface j) 1) :
    (Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
        Elliptic.HigherHomology.surfaceH2Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod (centralSweep j 1 a)
          0 =
      -PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo j *
        Elliptic.HigherHomology.surfaceH1Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 := by
  have h := congrFun (centralSweep_h2Coordinates j a) (3 : Fin 6)
  rw [PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates_formula] at h
  have hzero :
    ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
            Elliptic.HigherHomology.surfaceH2Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
              (centralSweep j 1 a) 0 -
          PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo j *
            Elliptic.HigherHomology.surfaceH2Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
              (centralSweep j 1 a) 1) *
        Elliptic.HigherHomology.fibreSquareKernelVector j 0 =
      0 := by
    simpa [PeriodFamily.Boundary.EllipticCapKernelWang.fibreInvariantPairVector,
      PeriodFamily.Boundary.EllipticCapKernelWang.twistDeltaVector] using h
  have hcoef :=
    (mul_eq_zero.mp hzero).resolve_right
      (show Elliptic.HigherHomology.fibreSquareKernelVector j 0 ≠ 0 by cases j <;> decide)
  rw [centralSweep_secondCoordinate] at hcoef
  linarith only [hcoef]

private theorem ThreefoldHomology.DeltaSweep.fibreNormIndex_dvd_sourceShearTwo (j : Elliptic.Kind) :
    (Elliptic.HigherHomology.fibreNormIndex j : ℤ) ∣
      PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo j := by
  let a :=
    (Elliptic.HigherHomology.surfaceH1Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
      ![0, 1]
  have h := centralSweep_firstCoordinate_mul_index j a
  have ha :
    Elliptic.HigherHomology.surfaceH1Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 =
      1 := by simp [a]
  rw [ha, mul_one] at h
  refine
    ⟨-Elliptic.HigherHomology.surfaceH2Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod (centralSweep j 1 a)
          0,
      ?_⟩
  rw [mul_neg, h, neg_neg]

private def ThreefoldHomology.DeltaSweep.centralSweepShearCorrection (j : Elliptic.Kind) : ℤ :=
  PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo j /
    (Elliptic.HigherHomology.fibreNormIndex j : ℤ)

private theorem ThreefoldHomology.DeltaSweep.fibreNormIndex_mul_centralSweepShearCorrection
    (j : Elliptic.Kind) :
    (Elliptic.HigherHomology.fibreNormIndex j : ℤ) * centralSweepShearCorrection j =
      PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo j := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel (fibreNormIndex_dvd_sourceShearTwo j)

private theorem ThreefoldHomology.DeltaSweep.centralSweep_firstCoordinate (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.EllipticFilling.SpecialCentralSurface j) 1) :
    Elliptic.HigherHomology.surfaceH2Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod (centralSweep j 1 a) 0 =
      -centralSweepShearCorrection j *
        Elliptic.HigherHomology.surfaceH1Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 := by
  apply mul_left_cancel₀ (Elliptic.HigherHomology.fibreNormIndex_int_ne_zero j)
  rw [centralSweep_firstCoordinate_mul_index, ← fibreNormIndex_mul_centralSweepShearCorrection]
  ring

private theorem ThreefoldHomology.DeltaSweep.centralSweep_coordinates (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.EllipticFilling.SpecialCentralSurface j) 1) :
    Elliptic.HigherHomology.surfaceH2Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod (centralSweep j 1 a) =
      ![-centralSweepShearCorrection j *
          Elliptic.HigherHomology.surfaceH1Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1,
        -Elliptic.HigherHomology.surfaceH1Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1] := by
  ext i
  fin_cases i
  · exact centralSweep_firstCoordinate j a
  · exact centralSweep_secondCoordinate j a

private theorem ThreefoldHomology.DeltaSweep.neg_centralSweep_second_axis_coordinates
    (j : Elliptic.Kind) :
    Elliptic.HigherHomology.surfaceH2Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (-centralSweep j 1
            ((Elliptic.HigherHomology.surfaceH1Equiv j
                  (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
              ![0, 1])) =
      ![centralSweepShearCorrection j, 1] := by
  rw [map_neg, centralSweep_coordinates, LinearEquiv.apply_symm_apply]
  ext i
  fin_cases i <;> simp

private theorem ThreefoldHomology.DeltaSweep.neg_centralSweep_second_axis_global_eq_zero
    (j : Elliptic.Kind) :
    SingularMayerVietoris.singularHomologyMap (centralInclusionMap j) 2
        (-centralSweep j 1
            ((Elliptic.HigherHomology.surfaceH1Equiv j
                  (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
              ![0, 1])) =
      0 := by rw [map_neg, centralSweep_global_eq_zero, neg_zero]

private theorem ThreefoldHomology.DeltaSweep.exists_centralKernelClass_unit_secondCoordinate
    (j : Elliptic.Kind) :
    ∃ a :
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.EllipticFilling.SpecialCentralSurface j) 2,
      Elliptic.HigherHomology.surfaceH2Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a =
          ![centralSweepShearCorrection j, 1] ∧
        SingularMayerVietoris.singularHomologyMap (centralInclusionMap j) 2 a = 0 :=
  ⟨-centralSweep j 1
        ((Elliptic.HigherHomology.surfaceH1Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
          ![0, 1]),
    neg_centralSweep_second_axis_coordinates j, neg_centralSweep_second_axis_global_eq_zero j⟩

private theorem ThreefoldHomology.Finiteness.homology_subsingleton_of_lt {n : ℕ} (hn : 6 < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space n) := by
  cases n with
  | zero => omega
  | succ n =>
    have := starPairHomology_subsingleton (by omega : 5 < n + 1)
    have := starOverlapHomology_subsingleton (by omega : 5 < n)
    exact
      ThreefoldHomologyFinitenessAlgebra.subsingleton_of_exact
        (ThreefoldHomology.starRightHomologyMap (n + 1))
        (ThreefoldHomology.starConnectingHomomorphism n)
        (ThreefoldHomology.star_exact_at_ambient n)

private theorem ThreefoldHomology.SecondDegree.centralCover_splitCircle_global_eq_zero
    (j : Elliptic.Kind) :
    SingularMayerVietoris.singularHomologyMap (ThreefoldHomology.DeltaSweep.centralInclusionMap j)
        2
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover j) 2
          (PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo j)) =
      0 := by
  obtain ⟨a, ha, hz⟩ :=
    ThreefoldHomology.DeltaSweep.exists_centralKernelClass_unit_secondCoordinate j
  have hclass :
    SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover j) 2
        (PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo j) =
      (Elliptic.HigherHomology.fibreNormIndex j : ℤ) • a := by
    apply
      (Elliptic.HigherHomology.surfaceH2Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).injective
    rw [PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitCircleClassTwo]
    have hm :=
      map_zsmul
        (Elliptic.HigherHomology.surfaceH2Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod)
        (Elliptic.HigherHomology.fibreNormIndex j : ℤ) a
    rw [ha] at hm
    rw [hm]
    ext i
    fin_cases i
    · simpa using
        (ThreefoldHomology.DeltaSweep.fibreNormIndex_mul_centralSweepShearCorrection j).symm
    · simp
  rw [hclass]
  have hm :=
    map_zsmul
      (SingularMayerVietoris.singularHomologyMap
        (ThreefoldHomology.DeltaSweep.centralInclusionMap j) 2)
      (Elliptic.HigherHomology.fibreNormIndex j : ℤ) a
  rw [hz] at hm
  exact
    hm.trans
      (@zsmul_zero (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 2) _
        (Elliptic.HigherHomology.fibreNormIndex j : ℤ))

private theorem ThreefoldHomology.SecondDegree.regularFibre_splitCircle_global_eq_zero
    (j : Elliptic.Kind) :
    SingularMayerVietoris.singularHomologyMap
        ThreefoldHomology.CapElimination.regularFibreIntoSpace 2
        (PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo j) =
      0 := by
  rw [ThreefoldHomology.CentralFibreCompatibility.regularFibreIntoSpace_homology_eq_central_apply,
    ThreefoldHomology.DeltaSweep.centralFlatPeriodCover_eq_surfaceCover]
  exact centralCover_splitCircle_global_eq_zero j

private theorem
    ThreefoldHomology.SecondDegree.homologyTwoCyclicMap_twist_u_eq_zero (j : Elliptic.Kind) :
    homologyTwoCyclicMap (j.twist 1) = 0 := by
  have h :=
    (regularFibre_homologyTwo_coordinates
          (PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo j)).symm.trans
      (regularFibre_splitCircle_global_eq_zero j)
  have hc :
    6 *
          PeriodFamily.FlatTorus.singularH2Coordinates
            (PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo j) 2 +
        PeriodFamily.FlatTorus.singularH2Coordinates
          (PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo j) 3 =
      j.twist 1 := by
    rw [PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo_coordinates]
    simp
  exact (congrArg homologyTwoCyclicMap hc).symm.trans h

private theorem ThreefoldHomology.SecondDegree.homologyTwoCyclicMap_two_eq_zero :
    homologyTwoCyclicMap 2 = 0 := by
  simpa [Elliptic.Kind.twist, ε] using homologyTwoCyclicMap_twist_u_eq_zero Elliptic.Kind.three

private theorem ThreefoldHomology.SecondDegree.homologyTwoCyclicMap_neg_three_eq_zero :
    homologyTwoCyclicMap (-3) = 0 := by
  simpa [Elliptic.Kind.twist, ε'] using homologyTwoCyclicMap_twist_u_eq_zero Elliptic.Kind.four

private theorem
    ThreefoldHomology.SecondDegree.homologyTwoGenerator_eq_zero : homologyTwoGenerator = 0 := by
  change homologyTwoCyclicMap 1 = 0
  rw [show (1 : ℤ) = 2 + 2 + -3 by decide, map_add, map_add, homologyTwoCyclicMap_two_eq_zero,
    homologyTwoCyclicMap_neg_three_eq_zero]
  simp only [add_zero]

private theorem ThreefoldHomology.SecondDegree.homologyTwo_subsingleton :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 2) :=
  homologyTwo_subsingleton_iff_generator_eq_zero.mpr homologyTwoGenerator_eq_zero

private theorem ThreefoldHomology.SecondDegree.nativeCapKernelRegularMap_two_surjective :
    Function.Surjective (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 2) :=
  ThreefoldHomology.CapElimination.homologyTwo_subsingleton_iff_nativeCapKernel_surjective.mp
    homologyTwo_subsingleton

private theorem ThreefoldHomology.SecondDegree.cuspWangOne_first_two_zero
    (a :
      LinearMap.ker
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy Option.none)
          1)) :
    PeriodFamily.FlatTorus.singularH1Equiv a.val 0 = 0 ∧
      PeriodFamily.FlatTorus.singularH1Equiv a.val 1 = 0 := by
  have ha :
    MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy Option.none) 1
        a.val =
      0 :=
    a.property
  have h :=
    (ThreefoldHomology.BoundaryFirst.boundaryWangDifference_one_coordinates Option.none
          a.val).symm.trans
      ((congrArg PeriodFamily.FlatTorus.singularH1Equiv ha).trans
        PeriodFamily.FlatTorus.singularH1Equiv.map_zero)
  change -((M₀ - 1) *ᵥ PeriodFamily.FlatTorus.singularH1Equiv a.val) = 0 at h
  exact (M₀_sub_one_kernel _).mp (neg_eq_zero.mp h)

private theorem ThreefoldHomology.SecondDegree.cuspPlane_fixed_mo1973_29384 (a : Fin 2 → ℤ) :
    M₀ *ᵥ ![0, 0, a 0, a 1] = ![0, 0, a 0, a 1] := by
  ext i
  fin_cases i <;> simp [M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private def ThreefoldHomology.SecondDegree.cuspWangOneEquiv :
    LinearMap.ker
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy Option.none)
          1) ≃ₗ[ℤ]
      (Fin 2 → ℤ) :=
  ({    toFun
          a :=
          ![PeriodFamily.FlatTorus.singularH1Equiv a.val 2,
            PeriodFamily.FlatTorus.singularH1Equiv a.val 3]
        invFun
          a :=
          ThreefoldHomology.CapElimination.cuspOneInvariant ![0, 0, a 0, a 1]
            (cuspPlane_fixed_mo1973_29384 a)
        left_inv
          a := by
          apply Subtype.ext
          apply PeriodFamily.FlatTorus.singularH1Equiv.injective
          change
            PeriodFamily.FlatTorus.singularH1Equiv
                (PeriodFamily.FlatTorus.singularH1Equiv.symm
                  ![0, 0, PeriodFamily.FlatTorus.singularH1Equiv a.val 2,
                    PeriodFamily.FlatTorus.singularH1Equiv a.val 3]) =
              PeriodFamily.FlatTorus.singularH1Equiv a.val
          rw [LinearEquiv.apply_symm_apply]
          obtain ⟨h₀, h₁⟩ := cuspWangOne_first_two_zero a
          ext i
          fin_cases i <;> simp [h₀, h₁]
        right_inv
          a := by
          change
            ![PeriodFamily.FlatTorus.singularH1Equiv
                  (PeriodFamily.FlatTorus.singularH1Equiv.symm ![0, 0, a 0, a 1]) 2,
                PeriodFamily.FlatTorus.singularH1Equiv
                  (PeriodFamily.FlatTorus.singularH1Equiv.symm ![0, 0, a 0, a 1]) 3] =
              a
          rw [LinearEquiv.apply_symm_apply]
          ext i
          fin_cases i <;> rfl
        map_add' a
          b := by
          ext i
          fin_cases i <;> simp [map_add] } :
      LinearMap.ker
          (MappingTorusHomology.wangDifference
            (ThreefoldOverlapMappingTorus.monodromy Option.none) 1) ≃+
        (Fin 2 → ℤ)).toIntLinearEquiv

private def ThreefoldHomology.SecondDegree.nativeCapKernelTwoEquiv
    (i : SpecialPeriods.Threefold.Puncture) :
    ThreefoldHomology.CapElimination.NativeCapKernel i 2 ≃ₗ[ℤ] (Fin 2 → ℤ) := by
  cases i with
  | none =>
    exact
      ((ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree 1).toAddEquiv.trans
          cuspWangOneEquiv.toAddEquiv).toIntLinearEquiv
  | some j =>
    exact
      ((PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv j 1).toAddEquiv.trans
          (Elliptic.HigherHomology.surfaceH1Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData
                  j).centralPeriod).toAddEquiv).toIntLinearEquiv

private theorem ThreefoldHomology.SecondDegree.nativeCapKernelTwo_free
    (i : SpecialPeriods.Threefold.Puncture) :
    Module.Free ℤ (ThreefoldHomology.CapElimination.NativeCapKernel i 2) :=
  Module.Free.of_equiv (nativeCapKernelTwoEquiv i).symm

private theorem ThreefoldHomology.SecondDegree.nativeCapKernelTwo_finite
    (i : SpecialPeriods.Threefold.Puncture) :
    Module.Finite ℤ (ThreefoldHomology.CapElimination.NativeCapKernel i 2) :=
  Module.Finite.of_surjective (nativeCapKernelTwoEquiv i).symm.toLinearMap
    (nativeCapKernelTwoEquiv i).symm.surjective

private theorem ThreefoldHomology.SecondDegree.nativeCapKernelTwo_finrank
    (i : SpecialPeriods.Threefold.Puncture) :
    Module.finrank ℤ (ThreefoldHomology.CapElimination.NativeCapKernel i 2) = 2 := by
  rw [(nativeCapKernelTwoEquiv i).finrank_eq]
  simp

private theorem ThreefoldHomology.SecondDegree.nativeCapKernelsTwo_free :
    Module.Free ℤ
      (∀ i : SpecialPeriods.Threefold.Puncture,
        ThreefoldHomology.CapElimination.NativeCapKernel i 2) := by
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Module.Free ℤ (ThreefoldHomology.CapElimination.NativeCapKernel i 2) :=
    nativeCapKernelTwo_free
  exact
    ThreefoldHomologyFreeProducts.free_pi_int
      (fun i : SpecialPeriods.Threefold.Puncture =>
        ThreefoldHomology.CapElimination.NativeCapKernel i 2)

private theorem ThreefoldHomology.SecondDegree.nativeCapKernelsTwo_finite :
    Module.Finite ℤ
      (∀ i : SpecialPeriods.Threefold.Puncture,
        ThreefoldHomology.CapElimination.NativeCapKernel i 2) := by
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Module.Finite ℤ (ThreefoldHomology.CapElimination.NativeCapKernel i 2) :=
    nativeCapKernelTwo_finite
  exact
    ThreefoldHomology.Finiteness.finite_pi_int
      (fun i : SpecialPeriods.Threefold.Puncture =>
        ThreefoldHomology.CapElimination.NativeCapKernel i 2)

private theorem ThreefoldHomology.SecondDegree.nativeCapKernelsTwo_finrank :
    Module.finrank ℤ
        (∀ i : SpecialPeriods.Threefold.Puncture,
          ThreefoldHomology.CapElimination.NativeCapKernel i 2) =
      6 := by
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Module.Free ℤ (ThreefoldHomology.CapElimination.NativeCapKernel i 2) :=
    nativeCapKernelTwo_free
  have :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      Module.Finite ℤ (ThreefoldHomology.CapElimination.NativeCapKernel i 2) :=
    nativeCapKernelTwo_finite
  rw [ThreefoldHomologyFreeProducts.finrank_pi_int
      (fun i : SpecialPeriods.Threefold.Puncture =>
        ThreefoldHomology.CapElimination.NativeCapKernel i 2)]
  simp only [nativeCapKernelTwo_finrank, Finset.sum_const, Finset.card_univ, puncture_card]
  decide

private theorem ThreefoldHomology.SecondDegree.nativeCapKernelRegularMap_two_bijective :
    Function.Bijective (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 2) := by
  have := nativeCapKernelsTwo_free
  have := nativeCapKernelsTwo_finite
  have := ThreefoldHomology.Finiteness.regularHomology_free 2
  have := ThreefoldHomology.Finiteness.regularHomology_finite 2
  apply
    OrzechProperty.bijective_of_surjective_of_finrank_le
      (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 2)
      nativeCapKernelRegularMap_two_surjective
  rw [nativeCapKernelsTwo_finrank, ThreefoldHomology.Finiteness.regularHomology_finrank]
  exact le_rfl

private theorem ThreefoldHomology.SecondDegree.starLeft_two_injective :
    Function.Injective (ThreefoldHomology.starLeftHomologyMap 2) := by
  intro a b hab
  have hz : ThreefoldHomology.starLeftHomologyMap 2 (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hreg : ThreefoldHomology.starOverlapToRegularHomologyMap 2 (a - b) = 0 :=
    congrArg Prod.fst hz
  have hcap : ThreefoldHomology.starOverlapToFillingsHomologyMap 2 (a - b) = 0 := by
    have h := congrArg Prod.snd hz
    change -ThreefoldHomology.starOverlapToFillingsHomologyMap 2 (a - b) = 0 at h
    exact neg_eq_zero.mp h
  let c : LinearMap.ker (ThreefoldHomology.starOverlapToFillingsHomologyMap 2) := ⟨a - b, hcap⟩
  have hc :
    ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 2
        (ThreefoldHomology.CapElimination.nativeCapKernelEquiv 2 c) =
      0 :=
    (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap_equiv 2 c).trans hreg
  have he : ThreefoldHomology.CapElimination.nativeCapKernelEquiv 2 c = 0 :=
    nativeCapKernelRegularMap_two_bijective.injective
      (hc.trans (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 2).map_zero.symm)
  have hc0 : c = 0 :=
    (ThreefoldHomology.CapElimination.nativeCapKernelEquiv 2).injective
      (he.trans (ThreefoldHomology.CapElimination.nativeCapKernelEquiv 2).map_zero.symm)
  have hab0 : a - b = 0 :=
    congrArg
      (fun x : LinearMap.ker (ThreefoldHomology.starOverlapToFillingsHomologyMap 2) => x.val) hc0
  exact sub_eq_zero.mp hab0

private theorem ThreefoldHomology.ThirdDegree.connecting_two_eq_zero :
    ThreefoldHomology.starConnectingHomomorphism 2 = 0 := by
  apply LinearMap.ext
  intro a
  change ThreefoldHomology.starConnectingHomomorphism 2 a = 0
  apply ThreefoldHomology.SecondDegree.starLeft_two_injective
  simpa only [map_zero] using
    (ThreefoldHomology.star_exact_at_intersection 2).apply_apply_eq_zero a

private theorem ThreefoldHomology.ThirdDegree.starRight_three_surjective :
    Function.Surjective (ThreefoldHomology.starRightHomologyMap 3) := by
  intro a
  apply (ThreefoldHomology.star_exact_at_ambient 2 a).mp
  rw [connecting_two_eq_zero, LinearMap.zero_apply]

private def ThreefoldHomology.ThirdSource.threeWangVector (c3 : ℤ) (a : Fin 2 → ℤ) : Fin 6 → ℤ :=
  (a 0 - c3 * a 1) • ![0, 0, 0, 3, -1, 2] + a 1 • ![0, 0, 1, 0, 2, -4]

private def ThreefoldHomology.ThirdSource.fourWangVector (c4 : ℤ) (a : Fin 2 → ℤ) : Fin 6 → ℤ :=
  (2 * a 0 - c4 * a 1) • ![0, 0, 0, 2, -1, 1] + a 1 • ![0, 0, -1, 0, -3, 3]

private theorem ThreefoldHomology.ThirdSource.threeWangVector_apply (c3 : ℤ) (a : Fin 2 → ℤ) :
    threeWangVector c3 a =
      ![0, 0, a 1, 3 * (a 0 - c3 * a 1), -(a 0 - c3 * a 1) + 2 * a 1,
        2 * (a 0 - c3 * a 1) - 4 * a 1] := by
  ext i
  fin_cases i <;> simp [threeWangVector] <;> ring

private theorem ThreefoldHomology.ThirdSource.fourWangVector_apply (c4 : ℤ) (a : Fin 2 → ℤ) :
    fourWangVector c4 a =
      ![0, 0, -a 1, 2 * (2 * a 0 - c4 * a 1), -(2 * a 0 - c4 * a 1) - 3 * a 1,
        (2 * a 0 - c4 * a 1) + 3 * a 1] := by
  ext i
  fin_cases i <;> simp [fourWangVector] <;> ring

private theorem ThreefoldHomology.ThirdSource.fourWangVector_fixed (c4 : ℤ) (a : Fin 2 → ℤ) :
    PeriodTorusHigherHomologyExterior.squareA₂ *ᵥ fourWangVector c4 a = fourWangVector c4 a := by
  rw [fourWangVector_apply, PeriodTorusHigherHomologyExterior.squareA₂_eq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

private def ThreefoldHomology.ThirdSource.cuspVector (b c d e : ℤ) : Fin 6 → ℤ :=
  ![0, b, c, d, -b, e]

private theorem ThreefoldHomology.ThirdSource.squareM₀_fixed_iff (v : Fin 6 → ℤ) :
    PeriodTorusHigherHomologyExterior.squareM₀ *ᵥ v = v ↔ v 0 = 0 ∧ v 4 = -v 1 := by
  constructor
  · intro h
    have h₁ := congrFun h (1 : Fin 6)
    have h₅ := congrFun h (5 : Fin 6)
    simp [PeriodTorusHigherHomologyExterior.squareM₀_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] at h₁ h₅
    omega
  · rintro ⟨h₀, h₄⟩
    ext i
    fin_cases i <;>
      simp [PeriodTorusHigherHomologyExterior.squareM₀_eq, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, h₀, h₄]

private theorem ThreefoldHomology.ThirdSource.cuspVector_fixed (b c d e : ℤ) :
    PeriodTorusHigherHomologyExterior.squareM₀ *ᵥ cuspVector b c d e = cuspVector b c d e := by
  apply (squareM₀_fixed_iff _).mpr
  exact ⟨rfl, rfl⟩

private theorem ThreefoldHomology.ThirdSource.squareA₂_cuspVector (b c d e : ℤ) :
    PeriodTorusHigherHomologyExterior.squareA₂ *ᵥ cuspVector b c d e =
      ![-b, 0, b + c, d - 6 * b, 3 * b - e, d - 7 * b - 6 * c] := by
  rw [PeriodTorusHigherHomologyExterior.squareA₂_eq]
  ext i
  fin_cases i <;> simp [cuspVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

private def
    ThreefoldHomology.ThirdSource.sourcePair (c3 c4 : ℤ) (a3 a4 : Fin 2 → ℤ) (v : Fin 6 → ℤ) :
    (Fin 6 → ℤ) × (Fin 6 → ℤ) :=
  (threeWangVector c3 a3 - PeriodTorusHigherHomologyExterior.squareA₂ *ᵥ v,
    fourWangVector c4 a4 - v)

private theorem ThreefoldHomology.ThirdSource.kernel_coordinates (x y : Fin 6 → ℤ)
    (hxy : (x, y) ∈ LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaTwo) :
    x 1 = 0 ∧
      y 0 = 0 ∧
        y 1 = -x 0 ∧
          y 3 = 5 * x 0 + 12 * x 2 - 2 * x 3 + 3 * x 5 + 6 * y 2 - 2 * y 4 ∧
            y 5 = 3 * x 0 + 6 * x 2 - x 3 - x 4 + x 5 - y 4 := by
  have h := LinearMap.mem_ker.mp hxy
  rw [TrianglePeriodFamilyHomologyLattice.deltaTwo_apply] at h
  have h₀ := congrFun h (0 : Fin 6)
  have h₁ := congrFun h (1 : Fin 6)
  have h₂ := congrFun h (2 : Fin 6)
  have h₄ := congrFun h (4 : Fin 6)
  have h₅ := congrFun h (5 : Fin 6)
  change -x 0 + x 1 - y 0 - y 1 = 0 at h₀
  change -x 0 - 2 * x 1 + y 0 - y 1 = 0 at h₁
  change x 0 + y 1 = 0 at h₂
  change 6 * x 0 + 2 * x 1 + 6 * x 2 - x 3 - x 4 + x 5 + 3 * y 1 - y 4 - y 5 = 0 at h₄
  change
    -8 * x 0 - 2 * x 1 - 6 * x 2 + x 3 - x 4 - 2 * x 5 - 3 * y 0 - 6 * y 1 - 6 * y 2 + y 3 + y 4 -
        y 5 =
      0 at h₅
  omega

private def ThreefoldHomology.ThirdSource.sourceC_mo1973_29424 (x y : Fin 6 → ℤ) : ℤ :=
  x 0 - y 4 - y 2

private def ThreefoldHomology.ThirdSource.sourceBThree_mo1973_29425 (x y : Fin 6 → ℤ) : ℤ :=
  x 2 + x 0 + sourceC_mo1973_29424 x y

private def ThreefoldHomology.ThirdSource.sourceBFour_mo1973_29426 (x y : Fin 6 → ℤ) : ℤ :=
  -y 2 - sourceC_mo1973_29424 x y

private def ThreefoldHomology.ThirdSource.sourceAlpha_mo1973_29427 (x y : Fin 6 → ℤ) : ℤ :=
  x 3 - x 5 - 4 * x 2 - 3 * x 0 + 2 * sourceC_mo1973_29424 x y

private def ThreefoldHomology.ThirdSource.threeCoordinates (c3 : ℤ) (x y : Fin 6 → ℤ) : Fin 2 → ℤ :=
  ![sourceAlpha_mo1973_29427 x y + c3 * sourceBThree_mo1973_29425 x y,
    sourceBThree_mo1973_29425 x y]

private def ThreefoldHomology.ThirdSource.fourCoordinates (k4 : ℤ) (x y : Fin 6 → ℤ) : Fin 2 → ℤ :=
  ![(2 - k4) * (x 0 - y 4), sourceBFour_mo1973_29426 x y]

private def ThreefoldHomology.ThirdSource.cuspCoordinates (x y : Fin 6 → ℤ) : Fin 6 → ℤ :=
  cuspVector (x 0) (sourceC_mo1973_29424 x y) (3 * sourceAlpha_mo1973_29427 x y + 6 * x 0 - x 3)
    (x 4 + sourceAlpha_mo1973_29427 x y - 2 * sourceBThree_mo1973_29425 x y + 3 * x 0)

private theorem ThreefoldHomology.ThirdSource.cuspCoordinates_fixed (x y : Fin 6 → ℤ) :
    PeriodTorusHigherHomologyExterior.squareM₀ *ᵥ cuspCoordinates x y = cuspCoordinates x y :=
  cuspVector_fixed _ _ _ _

private theorem ThreefoldHomology.ThirdSource.threeCoordinates_source (c3 : ℤ) (x y : Fin 6 → ℤ)
    (hxy : (x, y) ∈ LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaTwo) :
    threeWangVector c3 (threeCoordinates c3 x y) -
        PeriodTorusHigherHomologyExterior.squareA₂ *ᵥ cuspCoordinates x y =
      x := by
  have hx₁ := (kernel_coordinates x y hxy).1
  rw [threeWangVector_apply, cuspCoordinates, squareA₂_cuspVector]
  ext i
  fin_cases i <;>
      simp [threeCoordinates, sourceAlpha_mo1973_29427, sourceBThree_mo1973_29425,
        sourceC_mo1973_29424, hx₁] <;>
    ring

private theorem ThreefoldHomology.ThirdSource.fourCoordinates_source (k4 : ℤ) (x y : Fin 6 → ℤ)
    (hxy : (x, y) ∈ LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaTwo) :
    fourWangVector (2 * k4) (fourCoordinates k4 x y) - cuspCoordinates x y = y := by
  obtain ⟨_, hy₀, hy₁, hy₃, hy₅⟩ := kernel_coordinates x y hxy
  rw [fourWangVector_apply, cuspCoordinates]
  ext i
  fin_cases i <;>
      simp [fourCoordinates, cuspVector, sourceAlpha_mo1973_29427, sourceBThree_mo1973_29425,
        sourceBFour_mo1973_29426, sourceC_mo1973_29424, hy₀, hy₁, hy₃, hy₅] <;>
    ring

private def ThreefoldHomology.ThirdSource.kernelThreeCoordinates (c3 k : ℤ) : Fin 2 → ℤ :=
  ![(2 * c3 + 4) * k, 2 * k]

private def ThreefoldHomology.ThirdSource.kernelFourCoordinates (k4 k : ℤ) : Fin 2 → ℤ :=
  ![(3 - 2 * k4) * k, -2 * k]

private def ThreefoldHomology.ThirdSource.kernelCuspCoordinates (k : ℤ) : Fin 6 → ℤ :=
  cuspVector 0 (2 * k) (12 * k) 0

private theorem ThreefoldHomology.ThirdSource.kernelCoordinates_source_zero (c3 k4 k : ℤ) :
    sourcePair c3 (2 * k4) (kernelThreeCoordinates c3 k) (kernelFourCoordinates k4 k)
        (kernelCuspCoordinates k) =
      0 := by
  rw [sourcePair, threeWangVector_apply, fourWangVector_apply, kernelCuspCoordinates,
    squareA₂_cuspVector]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [kernelThreeCoordinates, kernelFourCoordinates, cuspVector] <;>
    ring

private theorem ThreefoldHomology.ThirdSource.sourcePair_eq_zero_iff (c3 k4 : ℤ) (a3 a4 : Fin 2 → ℤ)
    (v : Fin 6 → ℤ) :
    sourcePair c3 (2 * k4) a3 a4 v = 0 ↔
      ∃ k : ℤ,
        a3 = kernelThreeCoordinates c3 k ∧
          a4 = kernelFourCoordinates k4 k ∧ v = kernelCuspCoordinates k := by
  constructor
  · intro h
    have hz₃ : threeWangVector c3 a3 - PeriodTorusHigherHomologyExterior.squareA₂ *ᵥ v = 0 :=
      congrArg Prod.fst h
    have hz₄ : fourWangVector (2 * k4) a4 - v = 0 := congrArg Prod.snd h
    have hv : v = fourWangVector (2 * k4) a4 := (sub_eq_zero.mp hz₄).symm
    have heq : threeWangVector c3 a3 = fourWangVector (2 * k4) a4 := by
      have heq := sub_eq_zero.mp hz₃
      rw [hv, fourWangVector_fixed] at heq
      exact heq
    rw [threeWangVector_apply, fourWangVector_apply] at heq
    have h₂ := congrFun heq (2 : Fin 6)
    have h₃ := congrFun heq (3 : Fin 6)
    have h₄ := congrFun heq (4 : Fin 6)
    change a3 1 = -a4 1 at h₂
    change 3 * (a3 0 - c3 * a3 1) = 2 * (2 * a4 0 - (2 * k4) * a4 1) at h₃
    change -(a3 0 - c3 * a3 1) + 2 * a3 1 = -(2 * a4 0 - (2 * k4) * a4 1) - 3 * a4 1 at h₄
    have hb₄ : a4 1 = -a3 1 := by omega
    rw [hb₄] at h₃ h₄
    have hα : a3 0 - c3 * a3 1 = 2 * a3 1 := by linear_combination h₃ + 2 * h₄
    have hβ : 2 * a4 0 + 2 * k4 * a3 1 = 3 * a3 1 := by linear_combination h₄ + hα
    have heven : (2 : ℤ) ∣ a3 1 := by
      refine ⟨a4 0 + (k4 - 1) * a3 1, ?_⟩
      linear_combination -hβ
    obtain ⟨k, hk⟩ := heven
    have ha₃ : a3 = kernelThreeCoordinates c3 k := by
      ext i
      fin_cases i
      · change a3 0 = (2 * c3 + 4) * k
        rw [hk] at hα
        linear_combination hα
      · exact hk
    have ha₄ : a4 = kernelFourCoordinates k4 k := by
      ext i
      fin_cases i
      · change a4 0 = (3 - 2 * k4) * k
        apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
        rw [hk] at hβ
        linear_combination hβ
      · change a4 1 = -2 * k
        rw [hb₄, hk]
        ring
    have hv' : v = kernelCuspCoordinates k := by
      rw [hv, ha₄, fourWangVector_apply]
      ext i
      fin_cases i <;> simp [kernelFourCoordinates, kernelCuspCoordinates, cuspVector] <;> ring
    exact ⟨k, ha₃, ha₄, hv'⟩
  · rintro ⟨k, rfl, rfl, rfl⟩
    exact kernelCoordinates_source_zero c3 k4 k

private def ThreefoldHomology.ThirdDegree.ellipticTwoClass (j : Elliptic.Kind) (a : Fin 2 → ℤ) :
    ThreefoldHomology.CapElimination.NativeCapKernel (Option.some j) 3 :=
  (PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv j 2).symm
    ((Elliptic.HigherHomology.surfaceH2Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
      a)

private theorem
    ThreefoldHomology.ThirdDegree.ellipticTwoClass_wang (j : Elliptic.Kind) (a : Fin 2 → ℤ) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (MappingTorusHomology.wangBoundary
          (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 2 (ellipticTwoClass j a).val) =
      ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) * a 0 -
            PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo j * a 1) •
          PeriodFamily.Boundary.EllipticCapKernelWang.fibreInvariantPairVector j +
        a 1 • PeriodFamily.Boundary.EllipticCapKernelWang.twistDeltaVector j := by
  have h :=
    PeriodFamily.Boundary.EllipticCapKernelWang.capKernel_wang_h2_coordinates j
      ((Elliptic.HigherHomology.surfaceH2Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
        a)
  simpa only [LinearEquiv.apply_symm_apply, ellipticTwoClass] using! h

private theorem ThreefoldHomology.ThirdDegree.cuspMonodromy_two_coordinates
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (MappingTorusHomology.monodromyHomologyMap
          (ThreefoldOverlapMappingTorus.monodromy Option.none) 2 a) =
      PeriodTorusHigherHomologyExterior.squareM₀ *ᵥ
        PeriodFamily.FlatTorus.singularH2Coordinates a := by
  have h := LinearMap.congr_fun (PeriodFamily.Boundary.Cusp.monodromyHomology_triangle 2) a
  have h' :
    MappingTorusHomology.monodromyHomologyMap (ThreefoldOverlapMappingTorus.monodromy Option.none)
        2 a =
      PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleCuspGenerator 2 a :=
    h
  rw [h']
  change
    PeriodFamily.FlatTorus.singularH2Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph SpecialPeriods.triangleCuspGenerator :
            C(RealTorus₄, RealTorus₄))
          2 a) =
      _
  rw [PeriodFamily.FlatTorus.singularH2Coordinates_inducedHomology_triangle,
    SpecialPeriods.triangleDualRepresentation_cusp_matrix]
  rfl

private def ThreefoldHomology.ThirdDegree.cuspTwoInvariant (v : Fin 6 → ℤ)
    (hv : PeriodTorusHigherHomologyExterior.squareM₀ *ᵥ v = v) :
    LinearMap.ker
      (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy Option.none)
        2) :=
  ⟨PeriodFamily.FlatTorus.singularH2Coordinates.symm v,
    by
    apply PeriodFamily.FlatTorus.singularH2Coordinates.injective
    change
      PeriodFamily.FlatTorus.singularH2Coordinates
          (PeriodFamily.FlatTorus.singularH2Coordinates.symm v -
            MappingTorusHomology.monodromyHomologyMap
              (ThreefoldOverlapMappingTorus.monodromy Option.none) 2
              (PeriodFamily.FlatTorus.singularH2Coordinates.symm v)) =
        _
    rw [map_sub, cuspMonodromy_two_coordinates, LinearEquiv.apply_symm_apply, map_zero]
    exact sub_eq_zero.mpr hv.symm⟩

private def ThreefoldHomology.ThirdDegree.cuspTwoClass (v : Fin 6 → ℤ)
    (hv : PeriodTorusHigherHomologyExterior.squareM₀ *ᵥ v = v) :
    ThreefoldHomology.CapElimination.NativeCapKernel Option.none 3 :=
  (ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree 2).symm (cuspTwoInvariant v hv)

private theorem ThreefoldHomology.ThirdDegree.cuspTwoClass_wang (v : Fin 6 → ℤ)
    (hv : PeriodTorusHigherHomologyExterior.squareM₀ *ᵥ v = v) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy Option.none) 2
          (cuspTwoClass v hv).val) =
      v := by
  change
    PeriodFamily.FlatTorus.singularH2Coordinates
        (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy Option.none) 2
          ((ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree 2).symm
              (cuspTwoInvariant v hv)).val) =
      v
  rw [ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree_symm_wang]
  exact LinearEquiv.apply_symm_apply _ _

private theorem ThreefoldHomology.ThirdDegree.nativeCapKernelSourceMap_two_coordinates
    (a :
      ∀ i : SpecialPeriods.Threefold.Puncture,
        ThreefoldHomology.CapElimination.NativeCapKernel i 3) :
    (PeriodFamily.FlatTorus.singularH2Coordinates
          (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 2 a).val.1,
        PeriodFamily.FlatTorus.singularH2Coordinates
          (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 2 a).val.2) =
      (PeriodFamily.FlatTorus.singularH2Coordinates
            (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 2 a (Option.some .three)) -
          PeriodTorusHigherHomologyExterior.squareA₂ *ᵥ
            PeriodFamily.FlatTorus.singularH2Coordinates
              (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 2 a Option.none),
        PeriodFamily.FlatTorus.singularH2Coordinates
            (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 2 a (Option.some .four)) -
          PeriodFamily.FlatTorus.singularH2Coordinates
            (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 2 a Option.none)) := by
  rw [ThreefoldHomology.CapElimination.nativeCapKernelSourceMap_val_second]
  simp only [map_sub, PeriodFamily.HomologyDifference.generatorHomologyTwo_coordinates, ite_true]

private def ThreefoldHomology.ThirdDegree.commonWangVector : Fin 6 → ℤ :=
  ![0, 0, 2, 12, 0, 0]

private theorem ThreefoldHomology.ThirdDegree.commonWangVector_cusp_fixed :
    PeriodTorusHigherHomologyExterior.squareM₀ *ᵥ commonWangVector = commonWangVector := by
  rw [PeriodTorusHigherHomologyExterior.squareM₀_eq]
  decide

private theorem ThreefoldHomology.ThirdDegree.commonWangVector_second_fixed :
    PeriodTorusHigherHomologyExterior.squareA₂ *ᵥ commonWangVector = commonWangVector := by
  rw [PeriodTorusHigherHomologyExterior.squareA₂_eq]
  decide

private def ThreefoldHomology.ThirdDegree.referenceClasses :
    ∀ i : SpecialPeriods.Threefold.Puncture, ThreefoldHomology.CapElimination.NativeCapKernel i 3
  | none => cuspTwoClass commonWangVector commonWangVector_cusp_fixed
  | some .three =>
    ellipticTwoClass .three
      ![2 * PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo .three + 4, 2]
  | some .four =>
    ellipticTwoClass .four
      ![3 - PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo .four, -2]

private theorem ThreefoldHomology.ThirdDegree.referenceClasses_wang
    (i : SpecialPeriods.Threefold.Puncture) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 2 referenceClasses i) =
      commonWangVector := by
  cases i with
  | none => exact cuspTwoClass_wang _ _
  | some
    j =>
    cases j <;>
      change
        PeriodFamily.FlatTorus.singularH2Coordinates
            (MappingTorusHomology.wangBoundary
              (ThreefoldOverlapMappingTorus.monodromy (Option.some _)) 2
              (ellipticTwoClass _ _).val) =
          _
    all_goals rw [ellipticTwoClass_wang]
    all_goals
      ext i
      fin_cases i <;>
          simp [Elliptic.HigherHomology.fibreNormIndex,
            PeriodFamily.Boundary.EllipticCapKernelWang.fibreInvariantPairVector,
            Elliptic.HigherHomology.fibreSquareKernelVector,
            PeriodFamily.Boundary.EllipticCapKernelWang.twistDeltaVector, Elliptic.Kind.twist, ε,
            ε', commonWangVector] <;>
        ring

private theorem ThreefoldHomology.ThirdDegree.referenceClasses_source_eq_zero :
    ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 2 referenceClasses = 0 := by
  have h := nativeCapKernelSourceMap_two_coordinates referenceClasses
  simp only [referenceClasses_wang, commonWangVector_second_fixed, sub_self] at h
  apply Subtype.ext
  apply Prod.ext
  · apply PeriodFamily.FlatTorus.singularH2Coordinates.injective
    exact (congrArg Prod.fst h).trans (map_zero _).symm
  · apply PeriodFamily.FlatTorus.singularH2Coordinates.injective
    exact (congrArg Prod.snd h).trans (map_zero _).symm

private theorem ThreefoldHomology.ThirdSource.twice_fourShearCorrection :
    2 * (ThreefoldHomology.DeltaSweep.centralSweepShearCorrection Elliptic.Kind.four) =
      PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo .four := by
  simpa only [Elliptic.HigherHomology.fibreNormIndex_four, Nat.cast_ofNat] using
    ThreefoldHomology.DeltaSweep.fibreNormIndex_mul_centralSweepShearCorrection Elliptic.Kind.four

private theorem ThreefoldHomology.ThirdSource.ellipticTwoClass_wang_three (a : Fin 2 → ℤ) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (MappingTorusHomology.wangBoundary
          (ThreefoldOverlapMappingTorus.monodromy (Option.some .three)) 2
          (ThreefoldHomology.ThirdDegree.ellipticTwoClass .three a).val) =
      threeWangVector
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo Elliptic.Kind.three) a := by
  have h := ThreefoldHomology.ThirdDegree.ellipticTwoClass_wang .three a
  simpa only [Elliptic.HigherHomology.fibreNormIndex_three, Nat.cast_one, one_mul,
    PeriodFamily.Boundary.EllipticCapKernelWang.fibreInvariantPairVector,
    Elliptic.HigherHomology.fibreSquareKernelVector,
    PeriodFamily.Boundary.EllipticCapKernelWang.twistDeltaVector, Elliptic.Kind.twist, ε,
    threeWangVector] using! h

private theorem ThreefoldHomology.ThirdSource.ellipticTwoClass_wang_four (a : Fin 2 → ℤ) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (MappingTorusHomology.wangBoundary
          (ThreefoldOverlapMappingTorus.monodromy (Option.some .four)) 2
          (ThreefoldHomology.ThirdDegree.ellipticTwoClass .four a).val) =
      fourWangVector
        (2 * (ThreefoldHomology.DeltaSweep.centralSweepShearCorrection Elliptic.Kind.four)) a := by
  have h := ThreefoldHomology.ThirdDegree.ellipticTwoClass_wang .four a
  rw [← twice_fourShearCorrection] at h
  simpa only [Elliptic.HigherHomology.fibreNormIndex_four, Nat.cast_ofNat,
    PeriodFamily.Boundary.EllipticCapKernelWang.fibreInvariantPairVector,
    Elliptic.HigherHomology.fibreSquareKernelVector,
    PeriodFamily.Boundary.EllipticCapKernelWang.twistDeltaVector, Elliptic.Kind.twist, ε',
    fourWangVector] using! h

private def ThreefoldHomology.ThirdSource.nativeSourceClasses (x y : Fin 6 → ℤ) :
    ∀ i : SpecialPeriods.Threefold.Puncture, ThreefoldHomology.CapElimination.NativeCapKernel i 3
  | none =>
    ThreefoldHomology.ThirdDegree.cuspTwoClass (cuspCoordinates x y) (cuspCoordinates_fixed x y)
  | some .three =>
    ThreefoldHomology.ThirdDegree.ellipticTwoClass .three
      (threeCoordinates
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo Elliptic.Kind.three) x y)
  | some .four =>
    ThreefoldHomology.ThirdDegree.ellipticTwoClass .four
      (fourCoordinates
        (ThreefoldHomology.DeltaSweep.centralSweepShearCorrection Elliptic.Kind.four) x y)

private theorem ThreefoldHomology.ThirdSource.nativeSourceClasses_wang_three (x y : Fin 6 → ℤ) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 2 (nativeSourceClasses x y)
          (Option.some .three)) =
      threeWangVector
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo Elliptic.Kind.three)
        (threeCoordinates
          (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo Elliptic.Kind.three) x y) :=
  ellipticTwoClass_wang_three _

private theorem ThreefoldHomology.ThirdSource.nativeSourceClasses_wang_four (x y : Fin 6 → ℤ) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 2 (nativeSourceClasses x y)
          (Option.some .four)) =
      fourWangVector
        (2 * (ThreefoldHomology.DeltaSweep.centralSweepShearCorrection Elliptic.Kind.four))
        (fourCoordinates
          (ThreefoldHomology.DeltaSweep.centralSweepShearCorrection Elliptic.Kind.four) x y) :=
  ellipticTwoClass_wang_four _

private theorem ThreefoldHomology.ThirdSource.nativeSourceClasses_wang_cusp (x y : Fin 6 → ℤ) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 2 (nativeSourceClasses x y)
          Option.none) =
      cuspCoordinates x y :=
  ThreefoldHomology.ThirdDegree.cuspTwoClass_wang _ _

private theorem
    ThreefoldHomology.ThirdSource.nativeSourceClasses_source_coordinates (x y : Fin 6 → ℤ)
    (hxy : (x, y) ∈ LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaTwo) :
    (PeriodFamily.FlatTorus.singularH2Coordinates
          (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 2
                (nativeSourceClasses x y)).val.1,
        PeriodFamily.FlatTorus.singularH2Coordinates
          (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 2
                (nativeSourceClasses x y)).val.2) =
      (x, y) := by
  rw [ThreefoldHomology.ThirdDegree.nativeCapKernelSourceMap_two_coordinates]
  simp only [nativeSourceClasses_wang_three, nativeSourceClasses_wang_four,
    nativeSourceClasses_wang_cusp]
  exact
    Prod.ext
      (threeCoordinates_source
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo Elliptic.Kind.three) x y hxy)
      (fourCoordinates_source
        (ThreefoldHomology.DeltaSweep.centralSweepShearCorrection Elliptic.Kind.four) x y hxy)

private theorem ThreefoldHomology.ThirdSource.nativeCapKernelSourceMap_two_surjective :
    Function.Surjective (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 2) := by
  intro a
  have hxy :
    (PeriodFamily.FlatTorus.singularH2Coordinates a.val.1,
        PeriodFamily.FlatTorus.singularH2Coordinates a.val.2) ∈
      LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaTwo := by
    change
      TrianglePeriodFamilyHomologyLattice.deltaTwo
          (PeriodFamily.FlatTorus.singularH2Coordinates a.val.1,
            PeriodFamily.FlatTorus.singularH2Coordinates a.val.2) =
        0
    have h := PeriodFamily.HomologyDifference.sourceDifferenceTwo_coordinates a.val
    rw [show PeriodFamily.Homology.sourceDifference 2 a.val = 0 from a.property, map_zero] at h
    exact h.symm
  have h :=
    nativeSourceClasses_source_coordinates (PeriodFamily.FlatTorus.singularH2Coordinates a.val.1)
      (PeriodFamily.FlatTorus.singularH2Coordinates a.val.2) hxy
  refine
    ⟨nativeSourceClasses (PeriodFamily.FlatTorus.singularH2Coordinates a.val.1)
        (PeriodFamily.FlatTorus.singularH2Coordinates a.val.2),
      ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact PeriodFamily.FlatTorus.singularH2Coordinates.injective (congrArg Prod.fst h)
  · exact PeriodFamily.FlatTorus.singularH2Coordinates.injective (congrArg Prod.snd h)

private def ThreefoldHomology.ThirdSource.capKernelWangCoordinates
    (i : SpecialPeriods.Threefold.Puncture) :
    ThreefoldHomology.CapElimination.NativeCapKernel i 3 →ₗ[ℤ] (Fin 6 → ℤ) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun
        a :=
        PeriodFamily.FlatTorus.singularH2Coordinates
          (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy i) 2 a.val)
      map_zero' := by rw [Submodule.coe_zero, map_zero, map_zero]
      map_add' a b := by rw [Submodule.coe_add, map_add, map_add] }

private theorem ThreefoldHomology.ThirdSource.capKernelWangCoordinates_injective
    (i : SpecialPeriods.Threefold.Puncture) : Function.Injective (capKernelWangCoordinates i) := by
  cases i with
  | none =>
    intro a b h
    apply (ThreefoldHomologyCuspFibre.cuspCapKernelWangEquivDegree 2).injective
    apply Subtype.ext
    exact PeriodFamily.FlatTorus.singularH2Coordinates.injective h
  | some j =>
    intro a b h
    apply PeriodFamily.Boundary.EllipticCapKernelWang.capKernelWang_two_injective j
    exact PeriodFamily.FlatTorus.singularH2Coordinates.injective h

private theorem ThreefoldHomology.ThirdSource.ellipticTwoClass_surjective (j : Elliptic.Kind) :
    Function.Surjective (ThreefoldHomology.ThirdDegree.ellipticTwoClass j) := by
  intro a
  refine
    ⟨Elliptic.HigherHomology.surfaceH2Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv j 2 a),
      ?_⟩
  simp only [ThreefoldHomology.ThirdDegree.ellipticTwoClass, LinearEquiv.symm_apply_apply]

private theorem ThreefoldHomology.ThirdSource.capKernelWangCoordinates_reference
    (i : SpecialPeriods.Threefold.Puncture) :
    capKernelWangCoordinates i (ThreefoldHomology.ThirdDegree.referenceClasses i) =
      ThreefoldHomology.ThirdDegree.commonWangVector :=
  ThreefoldHomology.ThirdDegree.referenceClasses_wang i

private theorem ThreefoldHomology.ThirdSource.kernelCoordinates_wang_values (c3 k4 k : ℤ) :
    threeWangVector c3 (kernelThreeCoordinates c3 k) =
        k • ThreefoldHomology.ThirdDegree.commonWangVector ∧
      fourWangVector (2 * k4) (kernelFourCoordinates k4 k) =
          k • ThreefoldHomology.ThirdDegree.commonWangVector ∧
        kernelCuspCoordinates k = k • ThreefoldHomology.ThirdDegree.commonWangVector := by
  constructor
  · rw [threeWangVector_apply]
    ext i
    fin_cases i <;>
        simp [kernelThreeCoordinates, ThreefoldHomology.ThirdDegree.commonWangVector] <;>
      ring
  constructor
  · rw [fourWangVector_apply]
    ext i
    fin_cases i <;>
        simp [kernelFourCoordinates, ThreefoldHomology.ThirdDegree.commonWangVector] <;>
      ring
  · ext i
    fin_cases i <;>
        simp [kernelCuspCoordinates, cuspVector,
          ThreefoldHomology.ThirdDegree.commonWangVector] <;>
      ring

private theorem ThreefoldHomology.ThirdSource.nativeCapKernelSourceMap_two_eq_zero_exists
    (a :
      ∀ i : SpecialPeriods.Threefold.Puncture,
        ThreefoldHomology.CapElimination.NativeCapKernel i 3)
    (ha : ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 2 a = 0) :
    ∃ k : ℤ, a = k • ThreefoldHomology.ThirdDegree.referenceClasses := by
  obtain ⟨b3, hb3⟩ := ellipticTwoClass_surjective .three (a (Option.some .three))
  obtain ⟨b4, hb4⟩ := ellipticTwoClass_surjective .four (a (Option.some .four))
  let v := capKernelWangCoordinates Option.none (a Option.none)
  have h₃ :
    capKernelWangCoordinates (Option.some .three) (a (Option.some .three)) =
      threeWangVector
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo Elliptic.Kind.three) b3 := by
    rw [← hb3]
    exact ellipticTwoClass_wang_three b3
  have h₄ :
    capKernelWangCoordinates (Option.some .four) (a (Option.some .four)) =
      fourWangVector
        (2 * (ThreefoldHomology.DeltaSweep.centralSweepShearCorrection Elliptic.Kind.four)) b4 := by
    rw [← hb4]
    exact ellipticTwoClass_wang_four b4
  have hpair :
    sourcePair (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo Elliptic.Kind.three)
        (2 * (ThreefoldHomology.DeltaSweep.centralSweepShearCorrection Elliptic.Kind.four)) b3 b4
        v =
      0 := by
    have hz :
      (PeriodFamily.FlatTorus.singularH2Coordinates
            (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 2 a).val.1,
          PeriodFamily.FlatTorus.singularH2Coordinates
            (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 2 a).val.2) =
        (0, 0) := by
      rw [ha]
      exact Prod.ext (map_zero _) (map_zero _)
    have hs :=
      (ThreefoldHomology.ThirdDegree.nativeCapKernelSourceMap_two_coordinates a).symm.trans hz
    change
      (capKernelWangCoordinates (Option.some .three) (a (Option.some .three)) -
            PeriodTorusHigherHomologyExterior.squareA₂ *ᵥ v,
          capKernelWangCoordinates (Option.some .four) (a (Option.some .four)) - v) =
        0 at hs
    rw [h₃, h₄] at hs
    exact hs
  obtain ⟨k, hk₃, hk₄, hkv⟩ :=
    (sourcePair_eq_zero_iff
          (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo Elliptic.Kind.three)
          (ThreefoldHomology.DeltaSweep.centralSweepShearCorrection Elliptic.Kind.four) b3 b4
          v).mp
      hpair
  have hw :=
    kernelCoordinates_wang_values
      (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo Elliptic.Kind.three)
      (ThreefoldHomology.DeltaSweep.centralSweepShearCorrection Elliptic.Kind.four) k
  have hvalues :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      capKernelWangCoordinates i (a i) = k • ThreefoldHomology.ThirdDegree.commonWangVector := by
    intro i
    cases i with
    | none => exact hkv.trans hw.2.2
    | some j =>
      cases j with
      | three =>
        exact
          h₃.trans
            ((congrArg
                  (threeWangVector
                    (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo
                      Elliptic.Kind.three))
                  hk₃).trans
              hw.1)
      | four =>
        exact
          h₄.trans
            ((congrArg
                  (fourWangVector
                    (2 *
                      (ThreefoldHomology.DeltaSweep.centralSweepShearCorrection
                        Elliptic.Kind.four)))
                  hk₄).trans
              hw.2.1)
  refine ⟨k, ?_⟩
  funext i
  apply capKernelWangCoordinates_injective i
  rw [Pi.smul_apply, map_smul, capKernelWangCoordinates_reference]
  exact hvalues i

private theorem ThreefoldHomology.ThirdSource.referenceClasses_smul_injective :
    Function.Injective (fun k : ℤ => k • ThreefoldHomology.ThirdDegree.referenceClasses) := by
  intro k l h
  have hw :=
    congrArg
      (fun a :
          ∀ i : SpecialPeriods.Threefold.Puncture,
            ThreefoldHomology.CapElimination.NativeCapKernel i 3 =>
        capKernelWangCoordinates Option.none (a Option.none))
      h
  simp only [Pi.smul_apply, map_smul, capKernelWangCoordinates_reference] at hw
  have h₂ : k * 2 = l * 2 := by
    simpa [ThreefoldHomology.ThirdDegree.commonWangVector] using congrFun hw (2 : Fin 6)
  omega

private def ThreefoldHomology.ThirdDegree.thirdFibreCyclicMap :
    ℤ →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily 3 :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun
        z :=
        PeriodFamily.Homology.sourceCoinvariantInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          3 (PeriodFamily.HomologyDifference.cokernelThreeEquiv.symm z)
      map_zero' := by rw [map_zero, map_zero]
      map_add' a b := by rw [map_add, map_add] }

private theorem ThreefoldHomology.ThirdDegree.thirdFibreCyclicMap_injective :
    Function.Injective thirdFibreCyclicMap := by
  intro a b h
  apply PeriodFamily.HomologyDifference.cokernelThreeEquiv.symm.injective
  exact
    PeriodFamily.Homology.sourceCoinvariantInclusion_injective
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
      3 h

private theorem ThreefoldHomology.ThirdDegree.thirdFibreCyclicMap_quotient
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    thirdFibreCyclicMap
        (PeriodFamily.HomologyDifference.cokernelThreeEquiv (Submodule.Quotient.mk a)) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.familyFibreInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          PeriodFamily.Homology.normalizedSlitBaseLift)
        3 a := by
  change
    PeriodFamily.Homology.sourceCoinvariantInclusion
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        3
        (PeriodFamily.HomologyDifference.cokernelThreeEquiv.symm
          (PeriodFamily.HomologyDifference.cokernelThreeEquiv (Submodule.Quotient.mk a))) =
      _
  rw [LinearEquiv.symm_apply_apply, PeriodFamily.Homology.sourceCoinvariantInclusion_mk]

private theorem ThreefoldHomology.ThirdDegree.thirdFibreCyclicMap_apply (z : ℤ) :
    thirdFibreCyclicMap z =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.familyFibreInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          PeriodFamily.Homology.normalizedSlitBaseLift)
        3 (PeriodFamily.FlatTorus.singularH3Coordinates.symm ![z, 0, 0, 0]) := by
  change
    PeriodFamily.Homology.sourceCoinvariantInclusion
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        3 (PeriodFamily.HomologyDifference.cokernelThreeEquiv.symm z) =
      _
  rw [PeriodFamily.HomologyDifference.cokernelThreeEquiv_symm_apply,
    PeriodFamily.Homology.sourceCoinvariantInclusion_mk]

private theorem ThreefoldHomology.ThirdDegree.thirdFibre_cyclic_coordinates
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.familyFibreInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          PeriodFamily.Homology.normalizedSlitBaseLift)
        3 a =
      thirdFibreCyclicMap (PeriodFamily.FlatTorus.singularH3Coordinates a 0) := by
  rw [← PeriodFamily.HomologyDifference.cokernelThreeEquiv_mk]
  exact (thirdFibreCyclicMap_quotient a).symm

private theorem ThreefoldHomology.ThirdDegree.thirdFibreCyclicMap_source_eq_zero (z : ℤ) :
    PeriodFamily.Homology.sourceKernelProjection
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        2 (thirdFibreCyclicMap z) =
      0 :=
  (PeriodFamily.Homology.sourceCoinvariantInclusion_kernelProjection_exact
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        2).apply_apply_eq_zero
    (PeriodFamily.HomologyDifference.cokernelThreeEquiv.symm z)

private theorem ThreefoldHomology.ThirdDegree.thirdFibreCyclicMap_eq_zero_iff (z : ℤ) :
    thirdFibreCyclicMap z = 0 ↔ z = 0 := by
  constructor
  · intro h
    exact thirdFibreCyclicMap_injective (h.trans (map_zero _).symm)
  · rintro rfl
    exact map_zero _

private theorem ThreefoldHomology.ThirdDegree.thirdFibre_range_eq :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            PeriodFamily.Homology.normalizedSlitBaseLift)
          3) =
      LinearMap.range thirdFibreCyclicMap := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    exact
      ⟨PeriodFamily.FlatTorus.singularH3Coordinates a 0, (thirdFibre_cyclic_coordinates a).symm⟩
  · rintro x ⟨z, rfl⟩
    exact
      ⟨PeriodFamily.FlatTorus.singularH3Coordinates.symm ![z, 0, 0, 0],
        (thirdFibreCyclicMap_apply z).symm⟩

private theorem ThreefoldHomology.ThirdDegree.regularInclusion_three_surjective :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion 3) := by
  intro x
  obtain ⟨p, hp⟩ := starRight_three_surjective x
  obtain ⟨a, ha⟩ :=
    ThreefoldHomology.CapElimination.starOverlapToFillingsHomologyMap_surjective 3 (-p.2)
  have hshape :
    p - ThreefoldHomology.starLeftHomologyMap 3 a =
      (p.1 - ThreefoldHomology.starOverlapToRegularHomologyMap 3 a, 0) := by
    rw [ThreefoldHomology.CapElimination.starLeft_regular_fillings]
    apply Prod.ext
    · rfl
    · change p.2 - -ThreefoldHomology.starOverlapToFillingsHomologyMap 3 a = 0
      rw [ha, neg_neg, sub_self]
  refine ⟨p.1 - ThreefoldHomology.starOverlapToRegularHomologyMap 3 a, ?_⟩
  calc
    SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion 3
          (p.1 - ThreefoldHomology.starOverlapToRegularHomologyMap 3 a) =
        ThreefoldHomology.starRightHomologyMap 3
          (p.1 - ThreefoldHomology.starOverlapToRegularHomologyMap 3 a, 0) :=
      (ThreefoldHomology.CapElimination.starRight_regular 3 _).symm
    _ =
        ThreefoldHomology.starRightHomologyMap 3
          (p - ThreefoldHomology.starLeftHomologyMap 3 a) :=
      (congrArg (ThreefoldHomology.starRightHomologyMap 3) hshape.symm)
    _ =
        ThreefoldHomology.starRightHomologyMap 3 p -
          ThreefoldHomology.starRightHomologyMap 3 (ThreefoldHomology.starLeftHomologyMap 3 a) :=
      (map_sub _ _ _)
    _ = x := by rw [hp, (ThreefoldHomology.star_exact_at_pair 3).apply_apply_eq_zero a, sub_zero]

private theorem ThreefoldHomology.ThirdDegree.regularFibre_homologyThree_surjective :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap
        ThreefoldHomology.CapElimination.regularFibreIntoSpace 3) :=
  ThreefoldHomology.CapElimination.regularFibreIntoSpace_homology_surjective 2
    ThreefoldHomology.ThirdSource.nativeCapKernelSourceMap_two_surjective
    regularInclusion_three_surjective

private def ThreefoldHomology.ThirdDegree.homologyThreeCyclicMap :
    ℤ →ₗ[ℤ] SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 3 :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun
        z :=
        SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion 3
          (thirdFibreCyclicMap z)
      map_zero' := by rw [map_zero, map_zero]
      map_add' a b := by rw [map_add, map_add] }

@[simp]
private theorem ThreefoldHomology.ThirdDegree.homologyThreeCyclicMap_regular (z : ℤ) :
    homologyThreeCyclicMap z =
      SingularMayerVietoris.singularHomologyMap ThreefoldHomology.originalRegularInclusion 3
        (thirdFibreCyclicMap z) :=
  rfl

private theorem ThreefoldHomology.ThirdDegree.regularFibre_homologyThree_coordinates
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    SingularMayerVietoris.singularHomologyMap
        ThreefoldHomology.CapElimination.regularFibreIntoSpace 3 a =
      homologyThreeCyclicMap (PeriodFamily.FlatTorus.singularH3Coordinates a 0) := by
  rw [ThreefoldHomology.CapElimination.regularFibreIntoSpace_homology, LinearMap.comp_apply,
    thirdFibre_cyclic_coordinates, homologyThreeCyclicMap_regular]

private theorem ThreefoldHomology.ThirdDegree.homologyThreeCyclicMap_surjective :
    Function.Surjective homologyThreeCyclicMap := by
  intro x
  obtain ⟨a, ha⟩ := regularFibre_homologyThree_surjective x
  exact
    ⟨PeriodFamily.FlatTorus.singularH3Coordinates a 0,
      (regularFibre_homologyThree_coordinates a).symm.trans ha⟩

private def ThreefoldHomology.ThirdDegree.homologyThreeGenerator :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 3 :=
  homologyThreeCyclicMap 1

private theorem ThreefoldHomology.ThirdDegree.homologyThreeCyclicMap_eq_smul (z : ℤ) :
    homologyThreeCyclicMap z = z • homologyThreeGenerator := by
  simpa [homologyThreeGenerator] using map_zsmul homologyThreeCyclicMap z (1 : ℤ)

private theorem ThreefoldHomology.ThirdDegree.homologyThree_subsingleton_iff_generator_eq_zero :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 3) ↔
      homologyThreeGenerator = 0 := by
  constructor
  · intro h
    exact h.elim _ _
  · intro h
    have hz (x : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 3) :
      x = 0 := by
      obtain ⟨z, rfl⟩ := homologyThreeCyclicMap_surjective x
      rw [homologyThreeCyclicMap_eq_smul, h]
      exact
        @zsmul_zero (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 3) _ z
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩

private theorem ThreefoldHomology.ThirdDegree.existsUnique_referenceFibreCoefficient :
    ∃! z : ℤ,
      thirdFibreCyclicMap z =
        ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3 referenceClasses := by
  have hr :
    ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3 referenceClasses ∈
      LinearMap.ker
        (PeriodFamily.Homology.sourceKernelProjection
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          2) :=
    referenceClasses_source_eq_zero
  rw [PeriodFamily.Homology.sourceKernelProjection_kernel, thirdFibre_range_eq] at hr
  obtain ⟨z, hz⟩ := hr
  refine ⟨z, hz, ?_⟩
  intro w hw
  exact thirdFibreCyclicMap_injective (hw.trans hz.symm)

private def ThreefoldHomology.ThirdDegree.referenceFibreCoefficient : ℤ :=
  Classical.choose existsUnique_referenceFibreCoefficient

private theorem ThreefoldHomology.ThirdDegree.referenceFibreCoefficient_spec :
    thirdFibreCyclicMap referenceFibreCoefficient =
      ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3 referenceClasses :=
  (Classical.choose_spec existsUnique_referenceFibreCoefficient).1

private theorem ThreefoldHomology.ThirdDegree.referenceFibreCoefficient_eq_iff (z : ℤ) :
    referenceFibreCoefficient = z ↔
      ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3 referenceClasses =
        thirdFibreCyclicMap z := by
  rw [← referenceFibreCoefficient_spec]
  exact thirdFibreCyclicMap_injective.eq_iff.symm

private theorem ThreefoldHomology.ThirdDegree.nativeCapKernelRegularMap_smul_reference (k : ℤ) :
    ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3 (k • referenceClasses) =
      thirdFibreCyclicMap (k * referenceFibreCoefficient) := by
  rw [map_zsmul, ← referenceFibreCoefficient_spec, ← map_zsmul]
  rfl

private theorem ThreefoldHomology.ThirdDegree.homologyThreeCyclicMap_referenceFibreCoefficient :
    homologyThreeCyclicMap referenceFibreCoefficient = 0 := by
  rw [homologyThreeCyclicMap_regular, referenceFibreCoefficient_spec]
  exact
    (ThreefoldHomology.CapElimination.regularInclusion_eq_zero_iff_native 3 _).mpr
      ⟨referenceClasses, rfl⟩

private theorem ThreefoldHomology.ThirdDegree.homologyThreeCyclicMap_eq_zero_iff (z : ℤ) :
    homologyThreeCyclicMap z = 0 ↔ ∃ k : ℤ, k * referenceFibreCoefficient = z := by
  constructor
  · intro hz
    obtain ⟨a, ha⟩ :=
      (ThreefoldHomology.CapElimination.regularInclusion_eq_zero_iff_native 3
            (thirdFibreCyclicMap z)).mp
        hz
    have hs : ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 2 a = 0 :=
      (congrArg
            (PeriodFamily.Homology.sourceKernelProjection
              (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)
              2)
            ha).trans
        (thirdFibreCyclicMap_source_eq_zero z)
    obtain ⟨k, rfl⟩ :=
      ThreefoldHomology.ThirdSource.nativeCapKernelSourceMap_two_eq_zero_exists a hs
    rw [nativeCapKernelRegularMap_smul_reference] at ha
    exact ⟨k, thirdFibreCyclicMap_injective ha⟩
  · rintro ⟨k, rfl⟩
    change homologyThreeCyclicMap (k • referenceFibreCoefficient) = 0
    rw [map_zsmul, homologyThreeCyclicMap_referenceFibreCoefficient]
    exact
      @zsmul_zero (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 3) _ k

private theorem ThreefoldHomology.ThirdDegree.nativeCapKernelRegularMap_three_eq_zero_iff
    (a :
      ∀ i : SpecialPeriods.Threefold.Puncture,
        ThreefoldHomology.CapElimination.NativeCapKernel i 3) :
    ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3 a = 0 ↔
      ∃ k : ℤ, a = k • referenceClasses ∧ k * referenceFibreCoefficient = 0 := by
  constructor
  · intro ha
    have hs : ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 2 a = 0 := by
      rw [ThreefoldHomology.CapElimination.nativeCapKernelSourceMap_apply, ha, map_zero]
    obtain ⟨k, hk⟩ :=
      ThreefoldHomology.ThirdSource.nativeCapKernelSourceMap_two_eq_zero_exists a hs
    refine ⟨k, hk, ?_⟩
    rw [hk, nativeCapKernelRegularMap_smul_reference] at ha
    exact (thirdFibreCyclicMap_eq_zero_iff _).mp ha
  · rintro ⟨k, rfl, hk⟩
    rw [nativeCapKernelRegularMap_smul_reference, hk, map_zero]

private theorem ThreefoldHomology.FourthSource.deltaThree_kernel_coordinates (x y : Lattice)
    (hxy : (x, y) ∈ LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaThree) :
    y 0 = -2 * y 1 ∧ x 0 = -3 * (x 1 + y 1 + y 2) ∧ x 2 = -2 * (x 1 + y 1 + y 2) := by
  have h := LinearMap.mem_ker.mp hxy
  rw [TrianglePeriodFamilyHomologyLattice.deltaThree_apply] at h
  have h₁ := congrFun h (1 : Fin 4)
  have h₂ := congrFun h (2 : Fin 4)
  have h₃ := congrFun h (3 : Fin 4)
  change -x 0 - x 1 + x 2 - y 1 - y 2 = 0 at h₁
  change x 0 - x 1 - 2 * x 2 + y 0 + y 1 - y 2 = 0 at h₂
  change -2 * x 0 - 6 * x 1 + 3 * y 0 - 6 * y 2 = 0 at h₃
  omega

private theorem ThreefoldHomology.FourthSource.cubeA₂_cuspVector (c d : ℤ) :
    PeriodTorusHigherHomologyExterior.cubeA₂ *ᵥ ![0, 0, c, d] = ![0, -c, 0, d - 6 * c] := by
  rw [PeriodTorusHigherHomologyExterior.cubeA₂_eq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem ThreefoldHomology.FourthSource.cubeM₀_cuspVector (c d : ℤ) :
    PeriodTorusHigherHomologyExterior.cubeM₀ *ᵥ ![0, 0, c, d] = ![0, 0, c, d] := by
  rw [PeriodTorusHigherHomologyExterior.cubeM₀_eq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private def ThreefoldHomology.FourthSource.sourceU_mo1973_29516 (c3 : ℤ) (x y : Lattice) : ℤ :=
  x 3 + 3 * c3 * (-x 1 - y 1 - y 2) - 6 * (-y 2 - y 1)

private def ThreefoldHomology.FourthSource.sourceV_mo1973_29517 (c4 : ℤ) (y : Lattice) : ℤ :=
  y 3 + 2 * c4 * y 1

private def
    ThreefoldHomology.FourthSource.threeCoordinates (c3 c4 : ℤ) (x y : Lattice) : Fin 2 → ℤ :=
  ![sourceV_mo1973_29517 c4 y - sourceU_mo1973_29516 c3 x y, -x 1 - y 1 - y 2]

private def
    ThreefoldHomology.FourthSource.fourCoordinates (c3 c4 : ℤ) (x y : Lattice) : Fin 2 → ℤ :=
  ![sourceV_mo1973_29517 c4 y - sourceU_mo1973_29516 c3 x y, y 1]

private def ThreefoldHomology.FourthSource.cuspCoordinates (c3 c4 : ℤ) (x y : Lattice) : Lattice :=
  ![0, 0, -y 2 - y 1, 3 * sourceV_mo1973_29517 c4 y - 4 * sourceU_mo1973_29516 c3 x y]

private theorem ThreefoldHomology.FourthSource.cuspCoordinates_fixed (c3 c4 : ℤ) (x y : Lattice) :
    PeriodTorusHigherHomologyExterior.cubeM₀ *ᵥ cuspCoordinates c3 c4 x y =
      cuspCoordinates c3 c4 x y :=
  cubeM₀_cuspVector _ _

private theorem ThreefoldHomology.FourthSource.threeCoordinates_source (c3 c4 : ℤ) (x y : Lattice)
    (hxy : (x, y) ∈ LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaThree) :
    PeriodFamily.Boundary.EllipticCapKernelWang.topWangMatrix .three c3 *ᵥ
          threeCoordinates c3 c4 x y -
        PeriodTorusHigherHomologyExterior.cubeA₂ *ᵥ cuspCoordinates c3 c4 x y =
      x := by
  obtain ⟨_, hx₀, hx₂⟩ := deltaThree_kernel_coordinates x y hxy
  rw [PeriodFamily.Boundary.EllipticCapKernelWang.topWangMatrix_mulVec_three, cuspCoordinates,
    cubeA₂_cuspVector]
  ext i
  fin_cases i <;>
      simp [threeCoordinates, sourceU_mo1973_29516, sourceV_mo1973_29517, hx₀, hx₂] <;>
    ring

private theorem ThreefoldHomology.FourthSource.fourCoordinates_source (c3 c4 : ℤ) (x y : Lattice)
    (hxy : (x, y) ∈ LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaThree) :
    PeriodFamily.Boundary.EllipticCapKernelWang.topWangMatrix .four c4 *ᵥ
          fourCoordinates c3 c4 x y -
        cuspCoordinates c3 c4 x y =
      y := by
  have hy₀ := (deltaThree_kernel_coordinates x y hxy).1
  rw [PeriodFamily.Boundary.EllipticCapKernelWang.topWangMatrix_mulVec_four, cuspCoordinates]
  ext i
  fin_cases i <;> simp [fourCoordinates, sourceU_mo1973_29516, sourceV_mo1973_29517, hy₀] <;> ring

private def ThreefoldHomology.FourthSource.nativeSourceClasses (x y : Lattice) :
    ∀ i : SpecialPeriods.Threefold.Puncture, ThreefoldHomology.CapElimination.NativeCapKernel i 4
  | none =>
    ThreefoldHomology.CapElimination.cuspThreeClass
      (cuspCoordinates
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.three)
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.four) x y)
      (cuspCoordinates_fixed
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.three)
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.four) x y)
  | some .three =>
    ThreefoldHomology.CapElimination.ellipticThreeClass .three
      (threeCoordinates
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.three)
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.four) x y)
  | some .four =>
    ThreefoldHomology.CapElimination.ellipticThreeClass .four
      (fourCoordinates
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.three)
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.four) x y)

private theorem ThreefoldHomology.FourthSource.nativeSourceClasses_wang_three (x y : Lattice) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 3 (nativeSourceClasses x y)
          (Option.some .three)) =
      PeriodFamily.Boundary.EllipticCapKernelWang.topWangMatrix .three
          (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.three) *ᵥ
        threeCoordinates
          (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.three)
          (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.four) x y :=
  ThreefoldHomology.CapElimination.ellipticThreeClass_wang .three _

private theorem ThreefoldHomology.FourthSource.nativeSourceClasses_wang_four (x y : Lattice) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 3 (nativeSourceClasses x y)
          (Option.some .four)) =
      PeriodFamily.Boundary.EllipticCapKernelWang.topWangMatrix .four
          (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.four) *ᵥ
        fourCoordinates
          (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.three)
          (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.four) x y :=
  ThreefoldHomology.CapElimination.ellipticThreeClass_wang .four _

private theorem ThreefoldHomology.FourthSource.nativeSourceClasses_wang_cusp (x y : Lattice) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (ThreefoldHomology.CapElimination.nativeCapKernelWangValue 3 (nativeSourceClasses x y)
          Option.none) =
      cuspCoordinates
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.three)
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.four) x y :=
  ThreefoldHomology.CapElimination.cuspThreeClass_wang _ _

private theorem
    ThreefoldHomology.FourthSource.nativeSourceClasses_source_coordinates (x y : Lattice)
    (hxy : (x, y) ∈ LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaThree) :
    (PeriodFamily.FlatTorus.singularH3Coordinates
          (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 3
                (nativeSourceClasses x y)).val.1,
        PeriodFamily.FlatTorus.singularH3Coordinates
          (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 3
                (nativeSourceClasses x y)).val.2) =
      (x, y) := by
  rw [ThreefoldHomology.CapElimination.nativeCapKernelSourceMap_three_coordinates]
  simp only [nativeSourceClasses_wang_three, nativeSourceClasses_wang_four,
    nativeSourceClasses_wang_cusp]
  exact
    Prod.ext
      (threeCoordinates_source
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.three)
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.four) x y hxy)
      (fourCoordinates_source
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.three)
        (PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree Elliptic.Kind.four) x y hxy)

private theorem ThreefoldHomology.FourthSource.nativeCapKernelSourceMap_three_surjective :
    Function.Surjective (ThreefoldHomology.CapElimination.nativeCapKernelSourceMap 3) := by
  intro a
  have hxy :
    (PeriodFamily.FlatTorus.singularH3Coordinates a.val.1,
        PeriodFamily.FlatTorus.singularH3Coordinates a.val.2) ∈
      LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaThree := by
    change
      TrianglePeriodFamilyHomologyLattice.deltaThree
          (PeriodFamily.FlatTorus.singularH3Coordinates a.val.1,
            PeriodFamily.FlatTorus.singularH3Coordinates a.val.2) =
        0
    have h := PeriodFamily.HomologyDifference.sourceDifferenceThree_coordinates a.val
    rw [show PeriodFamily.Homology.sourceDifference 3 a.val = 0 from a.property, map_zero] at h
    exact h.symm
  have h :=
    nativeSourceClasses_source_coordinates (PeriodFamily.FlatTorus.singularH3Coordinates a.val.1)
      (PeriodFamily.FlatTorus.singularH3Coordinates a.val.2) hxy
  refine
    ⟨nativeSourceClasses (PeriodFamily.FlatTorus.singularH3Coordinates a.val.1)
        (PeriodFamily.FlatTorus.singularH3Coordinates a.val.2),
      ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact PeriodFamily.FlatTorus.singularH3Coordinates.injective (congrArg Prod.fst h)
  · exact PeriodFamily.FlatTorus.singularH3Coordinates.injective (congrArg Prod.snd h)

private theorem
    ThreefoldHomology.EllipticFibre.wangDifference_symm_range {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ) :
    LinearMap.range (MappingTorusHomology.wangDifference f.symm n) =
      LinearMap.range (MappingTorusHomology.wangDifference f n) := by
  let e := PeriodTorusHigherHomology.homeomorphHomologyEquiv f n
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨-e.symm b, ?_⟩
    change -e.symm b - e (-e.symm b) = b - e.symm b
    rw [map_neg, LinearEquiv.apply_symm_apply]
    abel
  · rintro ⟨b, rfl⟩
    refine ⟨-e b, ?_⟩
    change -e b - e.symm (-e b) = b - e b
    rw [map_neg, LinearEquiv.symm_apply_apply]
    abel

private theorem ThreefoldHomology.EllipticFibre.periodCover_ker_eq_deckDifference_range
    (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) (n : ℕ) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (Elliptic.HigherHomology.periodCover j p j.twist (Elliptic.mainTwist_admissible j)) n) =
      LinearMap.range (Elliptic.HigherHomology.periodDeckDifference j p n) := by
  by_cases hn : n ≤ 4
  · interval_cases n
    · exact Elliptic.HigherHomology.periodCover_h0_ker_eq_deckDifference_range j p
    · exact Elliptic.HigherHomology.periodCover_h1_ker_eq_deckDifference_range j p
    · exact Elliptic.HigherHomology.periodCover_h2_ker_eq_deckDifference_range j p
    · exact Elliptic.HigherHomology.periodCover_h3_ker_eq_deckDifference_range j p
    · exact Elliptic.HigherHomology.periodCover_h4_ker_eq_deckDifference_range j p
  · have :=
      PeriodTorusHigherHomology.periodTorus_homology_subsingleton_of_lt p.val
        (Nat.lt_of_not_ge hn)
    ext a
    rw [Subsingleton.elim a 0]
    simp only [Submodule.zero_mem]

private theorem ThreefoldHomology.EllipticFibre.periodHomologyEquiv_affine (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (Elliptic.flatTorusPeriodHomeomorph p.val) n
        (SingularMayerVietoris.singularHomologyMap
          (Elliptic.flatTorusAffine j j.twist : C(RealTorus₄, RealTorus₄)) n a) =
      SingularMayerVietoris.singularHomologyMap
        (Elliptic.HigherHomology.periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus)) n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (Elliptic.flatTorusPeriodHomeomorph p.val) n a) := by
  have h :
    (Elliptic.flatTorusPeriodHomeomorph p.val : C(RealTorus₄, p.val.Torus)).comp
        (Elliptic.flatTorusAffine j j.twist : C(RealTorus₄, RealTorus₄)) =
      (Elliptic.HigherHomology.periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus)).comp
        (Elliptic.flatTorusPeriodHomeomorph p.val : C(RealTorus₄, p.val.Torus)) := by
    ext x
    exact Elliptic.flatTorusAffine_periodHomeomorph j p j.twist x
  have hh :=
    congrArg (fun u : C(RealTorus₄, p.val.Torus) => SingularMayerVietoris.singularHomologyMap u n)
      h
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp] at hh
  exact LinearMap.congr_fun hh a

private theorem ThreefoldHomology.EllipticFibre.periodHomologyEquiv_affine_symm (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (Elliptic.flatTorusPeriodHomeomorph p.val) n
        (SingularMayerVietoris.singularHomologyMap
          ((Elliptic.flatTorusAffine j j.twist).symm : C(RealTorus₄, RealTorus₄)) n a) =
      SingularMayerVietoris.singularHomologyMap
        ((Elliptic.HigherHomology.periodAffineHomeomorph j p).symm : C(p.val.Torus, p.val.Torus))
        n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (Elliptic.flatTorusPeriodHomeomorph p.val) n a) := by
  let A :=
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (Elliptic.flatTorusAffine j j.twist) n
  let B :=
    PeriodTorusHigherHomology.homeomorphHomologyEquiv
      (Elliptic.HigherHomology.periodAffineHomeomorph j p) n
  let E :=
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (Elliptic.flatTorusPeriodHomeomorph p.val) n
  have h := periodHomologyEquiv_affine j p n (A.symm a)
  change E (A (A.symm a)) = B (E (A.symm a)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  change E (A.symm a) = B.symm (E a)
  apply B.injective
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

private theorem ThreefoldHomology.EllipticFibre.periodHomologyEquiv_inverseWangDifference
    (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (Elliptic.flatTorusPeriodHomeomorph p.val) n
        (MappingTorusHomology.wangDifference (Elliptic.flatTorusAffine j j.twist).symm n a) =
      Elliptic.HigherHomology.periodDeckDifference j p n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (Elliptic.flatTorusPeriodHomeomorph p.val) n a) := by
  rw [MappingTorusHomology.wangDifference_apply, map_sub,
    Elliptic.HigherHomology.periodDeckDifference_apply, periodHomologyEquiv_affine_symm]

private theorem ThreefoldHomology.EllipticFibre.periodHomologyEquiv_mem_deckDifference_range_iff
    (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (Elliptic.flatTorusPeriodHomeomorph p.val) n
          a ∈
        LinearMap.range (Elliptic.HigherHomology.periodDeckDifference j p n) ↔
      a ∈
        LinearMap.range
          (MappingTorusHomology.wangDifference (Elliptic.flatTorusAffine j j.twist) n) := by
  rw [← wangDifference_symm_range (Elliptic.flatTorusAffine j j.twist) n]
  let E :=
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (Elliptic.flatTorusPeriodHomeomorph p.val) n
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨E.symm b, E.injective ?_⟩
    change
      PeriodTorusHigherHomology.homeomorphHomologyEquiv (Elliptic.flatTorusPeriodHomeomorph p.val)
          n
          (MappingTorusHomology.wangDifference (Elliptic.flatTorusAffine j j.twist).symm n
            (E.symm b)) =
        E a
    rw [periodHomologyEquiv_inverseWangDifference]
    change Elliptic.HigherHomology.periodDeckDifference j p n (E (E.symm b)) = E a
    rw [LinearEquiv.apply_symm_apply]
    exact hb
  · rintro ⟨b, rfl⟩
    exact ⟨E b, (periodHomologyEquiv_inverseWangDifference j p n b).symm⟩

private theorem ThreefoldHomology.EllipticFibre.fibreToFilling_ker_eq_wangDifference_range
    (j : Elliptic.Kind) (n : ℕ) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) n) =
      LinearMap.range
        (MappingTorusHomology.wangDifference
          (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) n) := by
  ext a
  change
    SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) n a =
        0 ↔
      _
  rw [fibreToFilling_homology_eq_zero_iff]
  change
    centralPeriodHomologyEquiv j n a ∈
        LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap
            (Elliptic.HigherHomology.periodCover j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
              (Elliptic.mainTwist_admissible j))
            n) ↔
      _
  rw [periodCover_ker_eq_deckDifference_range]
  exact
    periodHomologyEquiv_mem_deckDifference_range_iff j
      (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod n a

private theorem ThreefoldHomology.EllipticFibre.fibreToFilling_eq_zero_iff_fibreHomologyMap_eq_zero
    (j : Elliptic.Kind) (n : ℕ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) n a =
        0 ↔
      MappingTorusHomology.fibreHomologyMap
          (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) n a =
        0 := by
  change
    a ∈
        LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap
            (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) n) ↔
      a ∈
        LinearMap.ker
          (MappingTorusHomology.fibreHomologyMap
            (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) n)
  rw [fibreToFilling_ker_eq_wangDifference_range, MappingTorusHomology.wang_exact_at_fibre]

private theorem
    ThreefoldHomology.EllipticFibre.boundaryFilling_wang_eq_zero (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (ThreefoldOverlapMappingTorus.Boundary (Option.some j)) (n + 1))
    (hcap : ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1) a = 0)
    (hwang :
      MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) n
          a =
        0) :
    a = 0 := by
  have ha :
    a ∈
      LinearMap.range
        (MappingTorusHomology.fibreHomologyMap
          (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) (n + 1)) := by
    rw [MappingTorusHomology.wang_exact_at_mappingTorus]
    exact hwang
  obtain ⟨b, rfl⟩ := ha
  have hf :=
    LinearMap.congr_fun
      (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_fibre (Option.some j) (n + 1)) b
  change
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1)
        (MappingTorusHomology.fibreHomologyMap
          (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) (n + 1) b) =
      SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) (n + 1) b at hf
  exact (fibreToFilling_eq_zero_iff_fibreHomologyMap_eq_zero j (n + 1) b).mp (hf.symm.trans hcap)

private theorem ThreefoldHomology.EllipticFibre.boundaryFilling_wang_injective (j : Elliptic.Kind)
    (n : ℕ) :
    Function.Injective
      (fun a :
          SingularMayerVietoris.SingularHomology
            (ThreefoldOverlapMappingTorus.Boundary (Option.some j)) (n + 1) =>
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1) a,
          MappingTorusHomology.wangBoundary
            (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) n a)) := by
  intro a b h
  have hc :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1) a =
      ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1) b :=
    congrArg Prod.fst h
  have hw :
    MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) n
        a =
      MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) n
        b :=
    congrArg Prod.snd h
  apply sub_eq_zero.mp
  apply boundaryFilling_wang_eq_zero j n
  · rw [map_sub, hc, sub_self]
  · rw [map_sub, hw, sub_self]

private theorem ThreefoldHomology.EllipticFibre.boundaryFilling_four_wang_three_injective
    (j : Elliptic.Kind) :
    Function.Injective
      (fun a :
          SingularMayerVietoris.SingularHomology
            (ThreefoldOverlapMappingTorus.Boundary (Option.some j)) 4 =>
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4 a,
          MappingTorusHomology.wangBoundary
            (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 3 a)) :=
  boundaryFilling_wang_injective j 3

private theorem
    ThreefoldHomology.EllipticFibre.overlapFilling_wang_eq_zero (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.RegularOverlap (Option.some j)) (n + 1))
    (hcap :
      SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.overlapToFilling (Option.some j)) (n + 1) a =
        0)
    (hwang :
      MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) n
          (ThreefoldOverlapMappingTorus.overlapHomologyEquiv (Option.some j) (n + 1) a) =
        0) :
    a = 0 := by
  apply (ThreefoldOverlapMappingTorus.overlapHomologyEquiv (Option.some j) (n + 1)).injective
  rw [map_zero]
  apply boundaryFilling_wang_eq_zero j n
  · have hf :=
      LinearMap.congr_fun
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_retraction (Option.some j)
          (n + 1))
        a
    change
      ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1)
          (ThreefoldOverlapMappingTorus.overlapHomologyEquiv (Option.some j) (n + 1) a) =
        SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.overlapToFilling (Option.some j)) (n + 1) a at hf
    exact hf.trans hcap
  · exact hwang

private def ThreefoldHomology.FourthFibre.positiveFibreClass :
    SingularMayerVietoris.SingularHomology RealTorus₄ 4 :=
  PeriodTorusHigherHomology.realTorusH4Equiv.symm 1

@[simp]
private theorem ThreefoldHomology.FourthFibre.positiveFibreClass_coordinates :
    PeriodTorusHigherHomology.realTorusH4Equiv positiveFibreClass = 1 :=
  PeriodTorusHigherHomology.realTorusH4Equiv.apply_symm_apply 1

private def ThreefoldHomology.FourthFibre.nativeUnitCapSection (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary (Option.some j))
      4 :=
  PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass j

private theorem ThreefoldHomology.FourthFibre.wang_three_fibre_four
    (i : SpecialPeriods.Threefold.Puncture)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy i) 3
        (MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 4 a) =
      0 := by
  have ha :
    MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 4 a ∈
      LinearMap.range
        (MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 4) :=
    ⟨a, rfl⟩
  rw [MappingTorusHomology.wang_exact_at_mappingTorus (ThreefoldOverlapMappingTorus.monodromy i)
      3] at ha
  exact ha

end Mathoverflow1973

end
