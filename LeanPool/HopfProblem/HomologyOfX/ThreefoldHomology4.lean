/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Hurewicz.SixthHurewicz
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
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
import all LeanPool.HopfProblem.PeriodFamily.Core4
import all LeanPool.HopfProblem.PeriodFamily.Core5
import all LeanPool.HopfProblem.PeriodFamily.Core6
import all LeanPool.HopfProblem.PeriodFamily.Core7
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology3
import all LeanPool.HopfProblem.PeriodFamily.Core8
import all LeanPool.HopfProblem.CuspFibre.CuspBoundaryTopVanishing
import all LeanPool.HopfProblem.PeriodFamily.Core9
import all LeanPool.HopfProblem.CuspFibre.CuspNegation
import all LeanPool.HopfProblem.Hurewicz.SixthHurewicz

/-!
# Hopf problem: homology of x · threefold homology 4

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

private theorem ThreefoldHomology.FourthFibre.ellipticFirstAxis_eq (j : Elliptic.Kind) :
    (ThreefoldHomology.CapElimination.ellipticThreeClass j ![1, 0]).val =
      γ j.twist •
          MappingTorusHomology.fibreHomologyMap
            (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 4 positiveFibreClass -
        (j.order : ℤ) • nativeUnitCapSection j := by
  apply ThreefoldHomology.EllipticFibre.boundaryFilling_four_wang_three_injective j
  apply Prod.ext
  · calc
      ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4
            (ThreefoldHomology.CapElimination.ellipticThreeClass j ![1, 0]).val =
          0 :=
        (ThreefoldHomology.CapElimination.ellipticThreeClass j ![1, 0]).property
      _ =
          ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4
            (γ j.twist •
                MappingTorusHomology.fibreHomologyMap
                  (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 4 positiveFibreClass -
              (j.order : ℤ) • nativeUnitCapSection j) := by
        symm
        let c :
          SingularMayerVietoris.SingularHomology
              (ThreefoldOverlapMappingTorus.Boundary (Option.some j)) 4 →ₗ[ℤ]
            ℤ :=
          (Elliptic.HigherHomology.surfaceH4Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData
                    j).centralPeriod).toLinearMap.comp
            ((ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j
                  4).toLinearMap.comp
              (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4))
        have hf :
          c
              (MappingTorusHomology.fibreHomologyMap
                (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 4 positiveFibreClass) =
            (j.order : ℤ) * γ j.twist := by
          have h :=
            PeriodFamily.Boundary.EllipticTopFibre.boundaryFilling_fibre_h4_coordinates j
              positiveFibreClass
          rw [positiveFibreClass_coordinates, mul_one] at h
          exact h
        have hu : c (nativeUnitCapSection j) = 1 :=
          PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass_filling j
        apply (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j 4).injective
        apply
          (Elliptic.HigherHomology.surfaceH4Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).injective
        change c (_ - _) = _
        rw [map_zero, map_zero, map_sub, map_zsmul, map_zsmul, hf, hu]
        cases j <;> norm_num [Elliptic.Kind.order, Elliptic.Kind.twist, γ, ε, ε']
  · apply PeriodFamily.FlatTorus.singularH3Coordinates.injective
    let w :
      SingularMayerVietoris.SingularHomology
          (ThreefoldOverlapMappingTorus.Boundary (Option.some j)) 4 →ₗ[ℤ]
        Lattice :=
      PeriodFamily.FlatTorus.singularH3Coordinates.toLinearMap.comp
        (MappingTorusHomology.wangBoundary
          (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 3)
    have hk :
      w (ThreefoldHomology.CapElimination.ellipticThreeClass j ![1, 0]).val =
        (j.order : ℤ) • ![0, 0, 0, 1] :=
      PeriodFamily.Boundary.EllipticCapKernelWang.capKernelWangH4Coordinates_first_axis j
    have hf :
      w
          (MappingTorusHomology.fibreHomologyMap
            (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 4 positiveFibreClass) =
        0 :=
      (congrArg PeriodFamily.FlatTorus.singularH3Coordinates
            (wang_three_fibre_four (Option.some j) positiveFibreClass)).trans
        PeriodFamily.FlatTorus.singularH3Coordinates.map_zero
    have hu : w (nativeUnitCapSection j) = -Pi.single (3 : Fin 4) 1 :=
      PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass_wang j
    change w _ = w (_ - _)
    rw [hk, map_sub, map_zsmul, map_zsmul, hf, hu]
    have haxis : (Pi.single (3 : Fin 4) (1 : ℤ) : Lattice) = ![0, 0, 0, 1] := by
      ext i
      fin_cases i <;> simp
    simp [haxis]

private theorem ThreefoldHomology.FourthFibre.ellipticThreeFirstAxis_eq :
    (ThreefoldHomology.CapElimination.ellipticThreeClass .three ![1, 0]).val =
      MappingTorusHomology.fibreHomologyMap
          (ThreefoldOverlapMappingTorus.monodromy (Option.some Elliptic.Kind.three)) 4
          positiveFibreClass -
        (3 : ℤ) • nativeUnitCapSection .three := by
  simpa [Elliptic.Kind.order, Elliptic.Kind.twist, γ, ε] using ellipticFirstAxis_eq .three

private theorem ThreefoldHomology.FourthFibre.ellipticFourFirstAxis_eq :
    (ThreefoldHomology.CapElimination.ellipticThreeClass .four ![1, 0]).val =
      -MappingTorusHomology.fibreHomologyMap
            (ThreefoldOverlapMappingTorus.monodromy (Option.some Elliptic.Kind.four)) 4
            positiveFibreClass -
        (4 : ℤ) • nativeUnitCapSection .four := by
  simpa [Elliptic.Kind.order, Elliptic.Kind.twist, γ, ε'] using ellipticFirstAxis_eq .four

private def ThreefoldHomology.FourthFibre.cuspClass :
    ThreefoldHomology.CapElimination.NativeCapKernel Option.none 4 :=
  ⟨CuspBoundaryGammaZero.nativeClass,
    CuspBoundaryTopVanishing.boundaryFillingHomologyMap_nativeClass_eq_zero⟩

private def ThreefoldHomology.FourthFibre.nativeFibrePreimage :
    ∀ i : SpecialPeriods.Threefold.Puncture, ThreefoldHomology.CapElimination.NativeCapKernel i 4
  | none => (12 : ℤ) • cuspClass
  | some .three => (4 : ℤ) • ThreefoldHomology.CapElimination.ellipticThreeClass .three ![1, 0]
  | some .four => (3 : ℤ) • ThreefoldHomology.CapElimination.ellipticThreeClass .four ![1, 0]

private theorem ThreefoldHomology.FourthFibre.ellipticThreeFirstAxis_regular :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.three) 4
        (ThreefoldHomology.CapElimination.ellipticThreeClass .three ![1, 0]).val =
      SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            PeriodFamily.Homology.normalizedSlitBaseLift)
          4 positiveFibreClass -
        (3 : ℤ) •
          ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap
            (Option.some Elliptic.Kind.three) 4
            (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .three) := by
  have h :=
    congrArg
      (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.three)
        4)
      ellipticThreeFirstAxis_eq
  rw [map_sub, map_zsmul,
    PeriodFamily.Boundary.boundaryRegularHomologyMap_common_fibre_apply] at h
  exact h

private theorem ThreefoldHomology.FourthFibre.ellipticFourFirstAxis_regular :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.four) 4
        (ThreefoldHomology.CapElimination.ellipticThreeClass .four ![1, 0]).val =
      -SingularMayerVietoris.singularHomologyMap
            (PeriodFamily.Homology.familyFibreInclusion
              (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)
              PeriodFamily.Homology.normalizedSlitBaseLift)
            4 positiveFibreClass -
        (4 : ℤ) •
          ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.four)
            4 (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .four) := by
  have h :=
    congrArg
      (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.four) 4)
      ellipticFourFirstAxis_eq
  rw [map_sub, map_neg, map_zsmul,
    PeriodFamily.Boundary.boundaryRegularHomologyMap_common_fibre_apply] at h
  exact h

private theorem ThreefoldHomology.FourthFibre.nativeFibrePreimage_map :
    ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 4 nativeFibrePreimage =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.familyFibreInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          PeriodFamily.Homology.normalizedSlitBaseLift)
        4 positiveFibreClass := by
  classical
  rw [ThreefoldHomology.CapElimination.nativeCapKernelRegularMap_apply, Fintype.sum_option]
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four)]
  have hc :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 4 cuspClass.val =
      ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.three) 4
          (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .three) +
        ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.four) 4
          (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .four) :=
    PeriodFamily.Boundary.FourthRelation.nativeClass_regular_eq_capSections
  change
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 4
          ((12 : ℤ) • cuspClass.val) +
        (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.three)
            4
            ((4 : ℤ) • (ThreefoldHomology.CapElimination.ellipticThreeClass .three ![1, 0]).val) +
          ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.four)
            4
            ((3 : ℤ) • (ThreefoldHomology.CapElimination.ellipticThreeClass .four ![1, 0]).val)) =
      _
  rw [map_zsmul, map_zsmul, map_zsmul, hc, ellipticThreeFirstAxis_regular,
    ellipticFourFirstAxis_regular]
  abel

private def ThreefoldHomology.FourthFibre.nativeFibrePreimageOf
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    ∀ i : SpecialPeriods.Threefold.Puncture,
      ThreefoldHomology.CapElimination.NativeCapKernel i 4 :=
  PeriodTorusHigherHomology.realTorusH4Equiv a • nativeFibrePreimage

private theorem ThreefoldHomology.FourthFibre.positiveFibreClass_spans
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    PeriodTorusHigherHomology.realTorusH4Equiv a • positiveFibreClass = a := by
  apply PeriodTorusHigherHomology.realTorusH4Equiv.injective
  rw [map_zsmul, positiveFibreClass_coordinates]
  simp

private theorem ThreefoldHomology.FourthFibre.nativeFibrePreimageOf_map
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 4 (nativeFibrePreimageOf a) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.familyFibreInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          PeriodFamily.Homology.normalizedSlitBaseLift)
        4 a := by
  calc
    ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 4 (nativeFibrePreimageOf a) =
        PeriodTorusHigherHomology.realTorusH4Equiv a •
          ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 4 nativeFibrePreimage :=
      map_zsmul (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 4)
        (PeriodTorusHigherHomology.realTorusH4Equiv a) nativeFibrePreimage
    _ =
        PeriodTorusHigherHomology.realTorusH4Equiv a •
          SingularMayerVietoris.singularHomologyMap
            (PeriodFamily.Homology.familyFibreInclusion
              (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)
              PeriodFamily.Homology.normalizedSlitBaseLift)
            4 positiveFibreClass :=
      (congrArg (fun b => PeriodTorusHigherHomology.realTorusH4Equiv a • b)
        nativeFibrePreimage_map)
    _ =
        SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            PeriodFamily.Homology.normalizedSlitBaseLift)
          4 (PeriodTorusHigherHomology.realTorusH4Equiv a • positiveFibreClass) :=
      (map_zsmul
          (SingularMayerVietoris.singularHomologyMap
            (PeriodFamily.Homology.familyFibreInclusion
              (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)
              PeriodFamily.Homology.normalizedSlitBaseLift)
            4)
          (PeriodTorusHigherHomology.realTorusH4Equiv a) positiveFibreClass).symm
    _ =
        SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            PeriodFamily.Homology.normalizedSlitBaseLift)
          4 a :=
      congrArg
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            PeriodFamily.Homology.normalizedSlitBaseLift)
          4)
        (positiveFibreClass_spans a)

private theorem ThreefoldHomology.FourthFibre.fibre_mem_range
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.familyFibreInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          PeriodFamily.Homology.normalizedSlitBaseLift)
        4 a ∈
      LinearMap.range (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 4) :=
  ⟨nativeFibrePreimageOf a, nativeFibrePreimageOf_map a⟩

private theorem ThreefoldHomology.FourthFibre.fibre_range_le :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            PeriodFamily.Homology.normalizedSlitBaseLift)
          4) ≤
      LinearMap.range (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 4) := by
  rintro _ ⟨a, rfl⟩
  exact fibre_mem_range a

private theorem ThreefoldHomology.FifthDegree.signed_residual_coordinate_zero (k u v d : ℤ)
    (hthree : 3 * u = k) (hfour : -4 * v = k) (hregular : u + v = d * k) : k = 0 := by
  have h : (12 * d - 1) * k = 0 := by linear_combination 4 * hthree - 3 * hfour - 12 * hregular
  have hn : 12 * d - 1 ≠ 0 := by omega
  exact (mul_eq_zero.mp h).resolve_left hn

private theorem ThreefoldHomology.TopDegree.connecting_five_injective :
    Function.Injective (ThreefoldHomology.starConnectingHomomorphism 5) := by
  have := ThreefoldHomology.Finiteness.starPairHomology_subsingleton (by decide : 5 < 6)
  intro a b hab
  have hz : ThreefoldHomology.starConnectingHomomorphism 5 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (ThreefoldHomology.star_exact_at_ambient 5 (a - b)).mp hz
  have hc₀ : c = 0 := Subsingleton.elim _ _
  rw [hc₀, map_zero] at hc
  exact sub_eq_zero.mp hc.symm

private def ThreefoldHomology.TopDegree.connectingIntoKernel :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6 →ₗ[ℤ]
      LinearMap.ker (ThreefoldHomology.starLeftHomologyMap 5) :=
  (ThreefoldHomology.starConnectingHomomorphism 5).codRestrict
    (LinearMap.ker (ThreefoldHomology.starLeftHomologyMap 5))
    (fun a => (ThreefoldHomology.star_exact_at_intersection 5).apply_apply_eq_zero a)

private theorem ThreefoldHomology.TopDegree.connectingIntoKernel_bijective :
    Function.Bijective connectingIntoKernel := by
  constructor
  · intro a b hab
    exact connecting_five_injective (congrArg Subtype.val hab)
  · intro a
    obtain ⟨b, hb⟩ := (ThreefoldHomology.star_exact_at_intersection 5 a.val).mp a.property
    exact ⟨b, Subtype.ext hb⟩

private def ThreefoldHomology.TopDegree.homologySixKernelEquiv :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6 ≃ₗ[ℤ]
      LinearMap.ker (ThreefoldHomology.starLeftHomologyMap 5) :=
  LinearEquiv.ofBijective connectingIntoKernel connectingIntoKernel_bijective

private theorem ThreefoldHomology.TopDegree.starLeft_five_eq_zero_iff
    (a : ThreefoldHomology.StarOverlapHomology 5) :
    ThreefoldHomology.starLeftHomologyMap 5 a = 0 ↔
      ThreefoldHomology.starOverlapToRegularHomologyMap 5 a = 0 := by
  have := ThreefoldHomology.Finiteness.starFillingHomology_subsingleton (by decide : 4 < 5)
  change
    (ThreefoldHomology.starOverlapToRegularHomologyMap 5 a,
          -ThreefoldHomology.starOverlapToFillingsHomologyMap 5 a) =
        (0, 0) ↔
      _
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    exact Prod.ext h (Subsingleton.elim _ _)

private def ThreefoldHomology.TopDegree.attachmentKernelEquiv :
    LinearMap.ker (ThreefoldHomology.starLeftHomologyMap 5) ≃ₗ[ℤ]
      LinearMap.ker (ThreefoldHomology.starOverlapToRegularHomologyMap 5)
    where
  toFun a := ⟨a.val, (starLeft_five_eq_zero_iff a.val).mp a.property⟩
  invFun a := ⟨a.val, (starLeft_five_eq_zero_iff a.val).mpr a.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private def ThreefoldHomology.TopDegree.homologySixRegularKernelEquiv :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6 ≃ₗ[ℤ]
      LinearMap.ker (ThreefoldHomology.starOverlapToRegularHomologyMap 5) :=
  homologySixKernelEquiv.trans attachmentKernelEquiv

private abbrev ThreefoldHomology.TopDegree.EllipticOverlapFifth :=
  ∀ j : Elliptic.Kind,
    SingularMayerVietoris.SingularHomology
      (SpecialPeriods.Threefold.RegularOverlap (Option.some j)) 5

private def ThreefoldHomology.TopDegree.groupedOverlapFifthEquiv :
    ThreefoldHomology.StarOverlapHomology 5 ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.RegularOverlap Option.none) 5 ×
        EllipticOverlapFifth) :=
  ({ Equiv.piOptionEquivProd with map_add' := fun _ _ => rfl } :
      ThreefoldHomology.StarOverlapHomology 5 ≃+
        (SingularMayerVietoris.SingularHomology
            (SpecialPeriods.Threefold.RegularOverlap Option.none) 5 ×
          EllipticOverlapFifth)).toIntLinearEquiv

private def ThreefoldHomology.TopDegree.ellipticAttachmentFifth :
    EllipticOverlapFifth →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily 5
    where
  toFun
    a :=
    ∑ j : Elliptic.Kind,
      SingularMayerVietoris.singularHomologyMap
        (ThreefoldHomology.overlapToRegularFamily (Option.some j)) 5 (a j)
  map_add' a b := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r
    a := by
    simp only [Pi.smul_apply, map_zsmul, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact (int_smul_eq_zsmul ..).symm

@[simp]
private theorem
    ThreefoldHomology.TopDegree.ellipticAttachmentFifth_apply (a : EllipticOverlapFifth) :
    ellipticAttachmentFifth a =
      ∑ j : Elliptic.Kind,
        SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.overlapToRegularFamily (Option.some j)) 5 (a j) :=
  rfl

private def ThreefoldHomology.TopDegree.groupedAttachmentFifth :
    (SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap Option.none)
          5 ×
        EllipticOverlapFifth) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily 5 :=
  (ThreefoldHomology.starOverlapToRegularHomologyMap 5).comp
    groupedOverlapFifthEquiv.symm.toLinearMap

@[simp]
private theorem ThreefoldHomology.TopDegree.groupedAttachmentFifth_apply
    (a :
      SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap Option.none)
        5)
    (b : EllipticOverlapFifth) :
    groupedAttachmentFifth (a, b) =
      SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.overlapToRegularFamily Option.none) 5 a +
        ellipticAttachmentFifth b := by
  change
    (∑ i : SpecialPeriods.Threefold.Puncture,
        SingularMayerVietoris.singularHomologyMap (ThreefoldHomology.overlapToRegularFamily i) 5
          (groupedOverlapFifthEquiv.symm (a, b) i)) =
      _
  rw [Fintype.sum_option]
  rfl

private def ThreefoldHomology.TopDegree.groupedAttachmentKernelEquiv :
    LinearMap.ker (ThreefoldHomology.starOverlapToRegularHomologyMap 5) ≃ₗ[ℤ]
      LinearMap.ker groupedAttachmentFifth :=
  ({    toFun := fun a =>
          ⟨groupedOverlapFifthEquiv a.val,
            by
            change
              ThreefoldHomology.starOverlapToRegularHomologyMap 5
                  (groupedOverlapFifthEquiv.symm (groupedOverlapFifthEquiv a.val)) =
                0
            rw [LinearEquiv.symm_apply_apply]
            exact a.property⟩
        invFun := fun a => ⟨groupedOverlapFifthEquiv.symm a.val, a.property⟩
        left_inv := fun a => Subtype.ext (LinearEquiv.symm_apply_apply _ a.val)
        right_inv := fun a => Subtype.ext (LinearEquiv.apply_symm_apply _ a.val)
        map_add' := fun a b => Subtype.ext (map_add groupedOverlapFifthEquiv a.val b.val) } :
      LinearMap.ker (ThreefoldHomology.starOverlapToRegularHomologyMap 5) ≃+
        LinearMap.ker groupedAttachmentFifth).toIntLinearEquiv

private def ThreefoldHomology.TopDegree.homologySixGroupedKernelEquiv :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6 ≃ₗ[ℤ]
      LinearMap.ker groupedAttachmentFifth :=
  homologySixRegularKernelEquiv.trans groupedAttachmentKernelEquiv

@[simp]
private theorem ThreefoldHomology.TopDegree.homologySixGroupedKernelEquiv_val
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6) :
    (homologySixGroupedKernelEquiv a :
        SingularMayerVietoris.SingularHomology
            (SpecialPeriods.Threefold.RegularOverlap Option.none) 5 ×
          EllipticOverlapFifth) =
      (ThreefoldHomology.starConnectingHomomorphism 5 a Option.none, fun j =>
        ThreefoldHomology.starConnectingHomomorphism 5 a (Option.some j)) :=
  rfl

private theorem ThreefoldHomology.TopDegree.triangleTopHomologyMap_identity
    (g : SpecialPeriods.TriangleGroup) :
    SingularMayerVietoris.singularHomologyMap
        (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 4 =
      LinearMap.id := by
  change (PeriodFamily.Homology.triangleHomologyEquiv g 4).toLinearMap = _
  rw [PeriodFamily.HomologyDifference.triangleHomologyFour_identity]
  rfl

private theorem ThreefoldHomology.TopDegree.boundaryMonodromy_four_identity
    (i : SpecialPeriods.Threefold.Puncture) :
    MappingTorusHomology.monodromyHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 4 =
      LinearMap.id := by
  cases i with
  |
    none =>
    change
      SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.CuspFamily.cuspTorusHomeomorph 1 : C(RealTorus₄, RealTorus₄)) 4 =
        _
    rw [← SpecialPeriods.triangleTorusHomeomorph_cusp_zpow 1]
    exact triangleTopHomologyMap_identity _
  | some
    j =>
    change
      SingularMayerVietoris.singularHomologyMap
          (Elliptic.flatTorusAffine j j.twist : C(RealTorus₄, RealTorus₄)) 4 =
        _
    rw [PeriodFamily.Boundary.flatTorusAffine_homology_triangle,
      PeriodFamily.HomologyDifference.triangleHomologyFour_identity]
    rfl

private def ThreefoldHomology.TopDegree.boundaryFifthEquiv (i : SpecialPeriods.Threefold.Puncture) :
    SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary i) 5 ≃ₗ[ℤ] ℤ :=
  (PeriodFamily.Boundary.H5ToH4WangEquiv (ThreefoldOverlapMappingTorus.monodromy i)
        (boundaryMonodromy_four_identity i)).trans
    PeriodTorusHigherHomology.realTorusH4Equiv

@[simp]
private theorem ThreefoldHomology.TopDegree.boundaryFifthEquiv_apply
    (i : SpecialPeriods.Threefold.Puncture)
    (a : SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary i) 5) :
    boundaryFifthEquiv i a =
      PeriodTorusHigherHomology.realTorusH4Equiv
        (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy i) 4 a) :=
  rfl

private def ThreefoldHomology.TopDegree.overlapFifthEquiv (i : SpecialPeriods.Threefold.Puncture) :
    SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) 5 ≃ₗ[ℤ]
      ℤ :=
  (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i 5).trans (boundaryFifthEquiv i)

@[simp]
private theorem ThreefoldHomology.TopDegree.overlapFifthEquiv_apply
    (i : SpecialPeriods.Threefold.Puncture)
    (a : SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) 5) :
    overlapFifthEquiv i a =
      boundaryFifthEquiv i (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i 5 a) :=
  LinearEquiv.trans_apply a

private def ThreefoldHomology.TopDegree.regularFifthEquiv :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily 5 ≃ₗ[ℤ]
      (ℤ × ℤ) :=
  PeriodFamily.Homology.familyH5ProductEquiv
    (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)

@[simp]
private theorem ThreefoldHomology.TopDegree.regularFifthEquiv_apply
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily 5) :
    regularFifthEquiv a =
      (PeriodTorusHigherHomology.realTorusH4Equiv
          (PeriodFamily.Homology.sourceKernelProjection
                (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                  SpecialPeriods.specialPeriodMap_generator₁
                  SpecialPeriods.specialPeriodMap_generator₂)
                4 a).val.1,
        PeriodTorusHigherHomology.realTorusH4Equiv
          (PeriodFamily.Homology.sourceKernelProjection
                (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                  SpecialPeriods.specialPeriodMap_generator₁
                  SpecialPeriods.specialPeriodMap_generator₂)
                4 a).val.2) :=
  rfl

private def
    ThreefoldHomology.TopDegree.ellipticFifthCoordinates : EllipticOverlapFifth ≃ₗ[ℤ] (ℤ × ℤ) :=
  ({    toFun := fun a =>
          (overlapFifthEquiv (Option.some .three) (a .three),
            overlapFifthEquiv (Option.some .four) (a .four))
        invFun := fun a j =>
          match j with
          | .three => (overlapFifthEquiv (Option.some .three)).symm a.1
          | .four => (overlapFifthEquiv (Option.some .four)).symm a.2
        left_inv := by
          intro a
          funext j
          cases j <;> exact LinearEquiv.symm_apply_apply _ _
        right_inv := fun a =>
          Prod.ext (LinearEquiv.apply_symm_apply _ a.1) (LinearEquiv.apply_symm_apply _ a.2)
        map_add' := fun a b => Prod.ext (map_add _ _ _) (map_add _ _ _) } :
      EllipticOverlapFifth ≃+ (ℤ × ℤ)).toIntLinearEquiv

@[simp]
private theorem
    ThreefoldHomology.TopDegree.ellipticFifthCoordinates_apply (a : EllipticOverlapFifth) :
    ellipticFifthCoordinates a =
      (overlapFifthEquiv (Option.some .three) (a .three),
        overlapFifthEquiv (Option.some .four) (a .four)) :=
  rfl

private theorem ThreefoldHomology.TopDegree.boundaryThree_fifth_column
    (a :
      SingularMayerVietoris.SingularHomology
        (ThreefoldOverlapMappingTorus.Boundary (Option.some .three)) 5) :
    regularFifthEquiv
        (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some .three) 5 a) =
      (boundaryFifthEquiv (Option.some .three) a, 0) := by
  rw [regularFifthEquiv_apply, boundaryFifthEquiv_apply]
  have h :=
    congrArg
      (fun p :
          SingularMayerVietoris.SingularHomology RealTorus₄ 4 ×
            SingularMayerVietoris.SingularHomology RealTorus₄ 4 =>
        (PeriodTorusHigherHomology.realTorusH4Equiv p.1,
          PeriodTorusHigherHomology.realTorusH4Equiv p.2))
      (PeriodFamily.Boundary.ellipticThreeBoundary_sourceKernelProjection 4 a)
  simpa only [map_zero, ThreefoldOverlapMappingTorus.monodromy] using! h

private theorem ThreefoldHomology.TopDegree.boundaryFour_fifth_column
    (a :
      SingularMayerVietoris.SingularHomology
        (ThreefoldOverlapMappingTorus.Boundary (Option.some .four)) 5) :
    regularFifthEquiv
        (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some .four) 5 a) =
      (0, boundaryFifthEquiv (Option.some .four) a) := by
  rw [regularFifthEquiv_apply, boundaryFifthEquiv_apply]
  have h :=
    congrArg
      (fun p :
          SingularMayerVietoris.SingularHomology RealTorus₄ 4 ×
            SingularMayerVietoris.SingularHomology RealTorus₄ 4 =>
        (PeriodTorusHigherHomology.realTorusH4Equiv p.1,
          PeriodTorusHigherHomology.realTorusH4Equiv p.2))
      (PeriodFamily.Boundary.ellipticFourBoundary_sourceKernelProjection 4 a)
  simpa only [map_zero, ThreefoldOverlapMappingTorus.monodromy] using! h

private theorem ThreefoldHomology.TopDegree.overlapThree_fifth_column
    (a :
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.RegularOverlap (Option.some .three)) 5) :
    regularFifthEquiv
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.overlapToRegularFamily (Option.some .three)) 5 a) =
      (overlapFifthEquiv (Option.some .three) a, 0) := by
  have h :=
    LinearMap.congr_fun
      (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap_retraction (Option.some .three) 5)
      a
  change
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some .three) 5
        (ThreefoldOverlapMappingTorus.overlapHomologyEquiv (Option.some .three) 5 a) =
      SingularMayerVietoris.singularHomologyMap
        (ThreefoldHomology.overlapToRegularFamily (Option.some .three)) 5 a at h
  rw [overlapFifthEquiv_apply, ← h]
  exact boundaryThree_fifth_column _

private theorem ThreefoldHomology.TopDegree.overlapFour_fifth_column
    (a :
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.RegularOverlap (Option.some .four)) 5) :
    regularFifthEquiv
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.overlapToRegularFamily (Option.some .four)) 5 a) =
      (0, overlapFifthEquiv (Option.some .four) a) := by
  have h :=
    LinearMap.congr_fun
      (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap_retraction (Option.some .four) 5) a
  change
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some .four) 5
        (ThreefoldOverlapMappingTorus.overlapHomologyEquiv (Option.some .four) 5 a) =
      SingularMayerVietoris.singularHomologyMap
        (ThreefoldHomology.overlapToRegularFamily (Option.some .four)) 5 a at h
  rw [overlapFifthEquiv_apply, ← h]
  exact boundaryFour_fifth_column _

private theorem ThreefoldHomology.TopDegree.ellipticAttachmentFifth_coordinates
    (a : EllipticOverlapFifth) :
    regularFifthEquiv (ellipticAttachmentFifth a) = ellipticFifthCoordinates a := by
  classical
  rw [ellipticAttachmentFifth_apply, map_sum]
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four), overlapThree_fifth_column,
    overlapFour_fifth_column, ellipticFifthCoordinates_apply]
  exact Prod.ext (add_zero _) (zero_add _)

private def ThreefoldHomology.TopDegree.ellipticAttachmentFifthEquiv :
    EllipticOverlapFifth ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily 5 :=
  ellipticFifthCoordinates.trans regularFifthEquiv.symm

private theorem ThreefoldHomology.TopDegree.ellipticAttachmentFifthEquiv_toLinearMap :
    ellipticAttachmentFifthEquiv.toLinearMap = ellipticAttachmentFifth := by
  apply LinearMap.ext
  intro a
  apply regularFifthEquiv.injective
  change regularFifthEquiv (regularFifthEquiv.symm (ellipticFifthCoordinates a)) = _
  rw [LinearEquiv.apply_symm_apply, ellipticAttachmentFifth_coordinates]

public
theorem
    ThreefoldHomologyTopDegreeAlgebra.surjective_of_columnIso {A B D : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup D] [Module ℤ A] [Module ℤ B] [Module ℤ D] [Module ℤ (A × B)]
    (F : (A × B) →ₗ[ℤ] D) (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D) (hF : ∀ a b, F (a, b) = f a + e b) :
    Function.Surjective F := by
  intro d
  refine ⟨(0, e.symm d), ?_⟩
  rw [hF, map_zero, LinearEquiv.apply_symm_apply, zero_add]

private def ThreefoldHomologyTopDegreeAlgebra.kernelProjectionAddEquiv_mo1973_30150
    {A B D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] [Module ℤ A] [Module ℤ B]
    [Module ℤ D] [Module ℤ (A × B)] (F : (A × B) →ₗ[ℤ] D) (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b) : LinearMap.ker F ≃+ A
    where
  toFun x := x.val.1
  invFun
    a :=
    ⟨(a, -e.symm (f a)), by
      change F (a, -e.symm (f a)) = 0
      rw [hF, map_neg, LinearEquiv.apply_symm_apply, add_neg_cancel]⟩
  left_inv
    x := by
    apply Subtype.ext
    change (x.val.1, -e.symm (f x.val.1)) = x.val
    refine Prod.ext (by rfl) ?_
    apply e.injective
    change e (-e.symm (f x.val.1)) = e x.val.2
    rw [map_neg, LinearEquiv.apply_symm_apply]
    have hx : f x.val.1 + e x.val.2 = 0 := (hF x.val.1 x.val.2).symm.trans x.property
    calc
      -f x.val.1 = -f x.val.1 + 0 := (add_zero _).symm
      _ = -f x.val.1 + (f x.val.1 + e x.val.2) := (congrArg (fun d => -f x.val.1 + d) hx.symm)
      _ = e x.val.2 := by rw [← add_assoc, neg_add_cancel, zero_add]
  right_inv _ := rfl
  map_add' _ _ := rfl

private def
    ThreefoldHomologyTopDegreeAlgebra.kernelEquivOfColumnIso {A B D : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup D] [Module ℤ A] [Module ℤ B] [Module ℤ D] [Module ℤ (A × B)]
    (F : (A × B) →ₗ[ℤ] D) (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D) (hF : ∀ a b, F (a, b) = f a + e b)
    [Module ℤ (LinearMap.ker F)] : LinearMap.ker F ≃ₗ[ℤ] A :=
  (kernelProjectionAddEquiv_mo1973_30150 F f e hF).toIntLinearEquiv

private theorem ThreefoldHomology.TopDegree.groupedAttachmentFifth_columnIso
    (a :
      SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap Option.none)
        5)
    (b : EllipticOverlapFifth) :
    groupedAttachmentFifth (a, b) =
      SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.overlapToRegularFamily Option.none) 5 a +
        ellipticAttachmentFifthEquiv b := by
  change
    groupedAttachmentFifth (a, b) =
      SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.overlapToRegularFamily Option.none) 5 a +
        ellipticAttachmentFifthEquiv.toLinearMap b
  rw [ellipticAttachmentFifthEquiv_toLinearMap, groupedAttachmentFifth_apply]

private def ThreefoldHomology.TopDegree.homologySixCuspEquiv :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap Option.none)
        5 :=
  (homologySixGroupedKernelEquiv.toAddEquiv.trans
      (ThreefoldHomologyTopDegreeAlgebra.kernelEquivOfColumnIso groupedAttachmentFifth
          (SingularMayerVietoris.singularHomologyMap
            (ThreefoldHomology.overlapToRegularFamily Option.none) 5)
          ellipticAttachmentFifthEquiv
          groupedAttachmentFifth_columnIso).toAddEquiv).toIntLinearEquiv

@[simp]
private theorem ThreefoldHomology.TopDegree.homologySixCuspEquiv_apply
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6) :
    homologySixCuspEquiv a = ThreefoldHomology.starConnectingHomomorphism 5 a Option.none := by
  change
    (homologySixGroupedKernelEquiv a :
          SingularMayerVietoris.SingularHomology
              (SpecialPeriods.Threefold.RegularOverlap Option.none) 5 ×
            EllipticOverlapFifth).1 =
      _
  rw [homologySixGroupedKernelEquiv_val]

private def ThreefoldHomology.TopDegree.homologySixEquiv :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6 ≃ₗ[ℤ] ℤ :=
  homologySixCuspEquiv.trans (overlapFifthEquiv Option.none)

@[simp]
private theorem ThreefoldHomology.TopDegree.homologySixEquiv_apply
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6) :
    homologySixEquiv a =
      overlapFifthEquiv Option.none
        (ThreefoldHomology.starConnectingHomomorphism 5 a Option.none) := by
  change overlapFifthEquiv Option.none (homologySixCuspEquiv a) = _
  rw [homologySixCuspEquiv_apply]

private def ThreefoldHomology.TopDegree.topClass :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6 :=
  homologySixEquiv.symm 1

private theorem
    ThreefoldHomology.TopDegree.homologySixEquiv_topClass : homologySixEquiv topClass = 1 :=
  LinearEquiv.apply_symm_apply _ _

private theorem ThreefoldHomology.TopDegree.eq_smul_topClass
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6) :
    a = homologySixEquiv a • topClass := by
  apply homologySixEquiv.injective
  rw [map_zsmul, homologySixEquiv_topClass]
  simp

private theorem ThreefoldHomology.FifthDegree.regularAttachment_five_surjective :
    Function.Surjective (ThreefoldHomology.starOverlapToRegularHomologyMap 5) := by
  have hs :=
    ThreefoldHomologyTopDegreeAlgebra.surjective_of_columnIso
      ThreefoldHomology.TopDegree.groupedAttachmentFifth
      (SingularMayerVietoris.singularHomologyMap
        (ThreefoldHomology.overlapToRegularFamily Option.none) 5)
      ThreefoldHomology.TopDegree.ellipticAttachmentFifthEquiv
      ThreefoldHomology.TopDegree.groupedAttachmentFifth_columnIso
  intro a
  obtain ⟨b, hb⟩ := hs a
  exact ⟨ThreefoldHomology.TopDegree.groupedOverlapFifthEquiv.symm b, hb⟩

private theorem ThreefoldHomology.FifthDegree.starLeft_five_surjective :
    Function.Surjective (ThreefoldHomology.starLeftHomologyMap 5) := by
  have := ThreefoldHomology.Finiteness.starFillingHomology_subsingleton (by decide : 4 < 5)
  intro a
  obtain ⟨b, hb⟩ := regularAttachment_five_surjective a.1
  refine ⟨b, ?_⟩
  apply Prod.ext
  · exact hb
  · exact Subsingleton.elim _ _

private theorem ThreefoldHomology.FifthDegree.starRight_five_eq_zero :
    ThreefoldHomology.starRightHomologyMap 5 = 0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := starLeft_five_surjective a
  exact (ThreefoldHomology.star_exact_at_pair 5).apply_apply_eq_zero b

private theorem ThreefoldHomology.FifthDegree.connecting_four_injective :
    Function.Injective (ThreefoldHomology.starConnectingHomomorphism 4) := by
  intro a b hab
  have hz : ThreefoldHomology.starConnectingHomomorphism 4 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (ThreefoldHomology.star_exact_at_ambient 4 (a - b)).mp hz
  rw [starRight_five_eq_zero, LinearMap.zero_apply] at hc
  exact sub_eq_zero.mp hc.symm

private theorem ThreefoldHomologyCuspFibre.fibreToFilling_four_bijective :
    Function.Bijective
      (SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.fibreToFilling Option.none) 4) := by
  have := PeriodTorusHigherHomology.realTorus_homology_free 4
  have := PeriodTorusHigherHomology.realTorus_homology_finite 4
  have :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) 4) :=
    ThreefoldHomologyFinitenessCusp.fullHomology_free
      ThreefoldOverlapMappingTorus.Cusp.specialData 4
  have :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) 4) :=
    ThreefoldHomologyFinitenessCusp.fullHomology_finite
      ThreefoldOverlapMappingTorus.Cusp.specialData 4
  have hcap :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology
          (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) 4) =
      1 :=
    ThreefoldHomologyFinitenessCusp.fullHomology_finrank
      ThreefoldOverlapMappingTorus.Cusp.specialData 4
  apply
    OrzechProperty.bijective_of_surjective_of_finrank_le
      (SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.fibreToFilling Option.none) 4)
      (fibreToFilling_homology_surjective 4)
  rw [PeriodTorusHigherHomology.realTorus_homology_finrank, hcap]
  decide

private def ThreefoldHomologyCuspFibre.cuspFibreFourEquiv :
    SingularMayerVietoris.SingularHomology RealTorus₄ 4 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (SpecialPeriods.Threefold.localPiece (Option.some Option.none)) 4 :=
  LinearEquiv.ofBijective
    (SingularMayerVietoris.singularHomologyMap
      (ThreefoldOverlapMappingTorus.fibreToFilling Option.none) 4)
    fibreToFilling_four_bijective

private theorem ThreefoldHomologyCuspFibre.cuspCap_four_fibre
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 4
        (MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy none) 4
          a) =
      cuspFibreFourEquiv a :=
  LinearMap.congr_fun
    (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_fibre Option.none 4) a

private theorem ThreefoldHomologyCuspFibre.cuspCap_wang_four_eq_zero
    (a :
      SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary Option.none)
        4)
    (hcap : ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 4 a = 0)
    (hwang :
      MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy none) 3 a = 0) :
    a = 0 := by
  have ha :
    a ∈
      LinearMap.range
        (MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy none) 4) :=
    by
    rw [MappingTorusHomology.wang_exact_at_mappingTorus
        (ThreefoldOverlapMappingTorus.monodromy none) 3]
    exact hwang
  obtain ⟨b, hb⟩ := ha
  have hb0 : cuspFibreFourEquiv b = 0 :=
    (cuspCap_four_fibre b).symm.trans
      ((congrArg (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 4) hb).trans
        hcap)
  have hb' : b = 0 := cuspFibreFourEquiv.injective (hb0.trans cuspFibreFourEquiv.map_zero.symm)
  rw [hb', map_zero] at hb
  exact hb.symm

private theorem ThreefoldHomology.FourthWang.overlap_wang_coordinates
    (a : ThreefoldHomology.StarOverlapHomology 4)
    (ha : ThreefoldHomology.starOverlapToRegularHomologyMap 4 a = 0)
    (i : SpecialPeriods.Threefold.Puncture) :
    PeriodFamily.FlatTorus.singularH3Coordinates (overlapWangHomologyMap i 3 (a i)) =
      Pi.single 3
        (PeriodFamily.FlatTorus.singularH3Coordinates
          (overlapWangHomologyMap Option.none 3 (a Option.none)) 3) := by
  have h := wang_cancellation 3 a ha
  have hc :=
    (commonThirdInvariant_iff (overlapWangHomologyMap Option.none 3 (a Option.none))).mp
      ⟨h.2.2.1, h.2.2.2⟩
  cases i with
  | none => exact hc
  | some j =>
    cases j with
    | three => rw [h.1]; exact hc
    | four => rw [h.2.1]; exact hc

private def ThreefoldHomology.FourthWang.fifthWangCoordinate :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5 →ₗ[ℤ] ℤ :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun := fun a =>
        PeriodFamily.FlatTorus.singularH3Coordinates
          (overlapWangHomologyMap Option.none 3
            (ThreefoldHomology.starConnectingHomomorphism 4 a Option.none))
          3
      map_zero' := by simp only [map_zero, Pi.zero_apply]
      map_add' := by intro a b; simp only [map_add, Pi.add_apply] }

private theorem ThreefoldHomology.FourthWang.connecting_four_regular_zero
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5) :
    ThreefoldHomology.starOverlapToRegularHomologyMap 4
        (ThreefoldHomology.starConnectingHomomorphism 4 a) =
      0 :=
  congrArg Prod.fst ((ThreefoldHomology.star_exact_at_intersection 4).apply_apply_eq_zero a)

private theorem ThreefoldHomology.FourthWang.connecting_four_cap_zero
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (i : SpecialPeriods.Threefold.Puncture) :
    SingularMayerVietoris.singularHomologyMap (ThreefoldHomology.overlapToFilling i) 4
        (ThreefoldHomology.starConnectingHomomorphism 4 a i) =
      0 := by
  have h :=
    congrFun
      (congrArg Prod.snd ((ThreefoldHomology.star_exact_at_intersection 4).apply_apply_eq_zero a))
      i
  exact neg_eq_zero.mp h

private theorem ThreefoldHomology.FourthWang.fifthWangCoordinate_coordinates
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (i : SpecialPeriods.Threefold.Puncture) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (overlapWangHomologyMap i 3 (ThreefoldHomology.starConnectingHomomorphism 4 a i)) =
      Pi.single 3 (fifthWangCoordinate a) :=
  overlap_wang_coordinates (ThreefoldHomology.starConnectingHomomorphism 4 a)
    (connecting_four_regular_zero a) i

private theorem ThreefoldHomology.FourthWang.fifthWangCoordinate_eq_zero
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (ha : fifthWangCoordinate a = 0) : a = 0 := by
  have hw (i : SpecialPeriods.Threefold.Puncture) :
    overlapWangHomologyMap i 3 (ThreefoldHomology.starConnectingHomomorphism 4 a i) = 0 := by
    apply PeriodFamily.FlatTorus.singularH3Coordinates.injective
    rw [fifthWangCoordinate_coordinates, ha, map_zero]
    simp
  have hd : ThreefoldHomology.starConnectingHomomorphism 4 a = 0 := by
    funext i
    cases i with
    |
      none =>
      apply (ThreefoldOverlapMappingTorus.overlapHomologyEquiv Option.none 4).injective
      rw [Pi.zero_apply, map_zero]
      apply ThreefoldHomologyCuspFibre.cuspCap_wang_four_eq_zero
      · have h :=
          LinearMap.congr_fun
            (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_retraction Option.none 4)
            (ThreefoldHomology.starConnectingHomomorphism 4 a Option.none)
        change
          ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 4
              (ThreefoldOverlapMappingTorus.overlapHomologyEquiv Option.none 4
                (ThreefoldHomology.starConnectingHomomorphism 4 a Option.none)) =
            SingularMayerVietoris.singularHomologyMap
              (ThreefoldHomology.overlapToFilling Option.none) 4
              (ThreefoldHomology.starConnectingHomomorphism 4 a Option.none) at h
        exact h.trans (connecting_four_cap_zero a Option.none)
      · exact hw Option.none
    | some j =>
      exact
        ThreefoldHomology.EllipticFibre.overlapFilling_wang_eq_zero j 3 _
          (connecting_four_cap_zero a (Option.some j)) (hw (Option.some j))
  apply ThreefoldHomology.FifthDegree.connecting_four_injective
  rw [hd, map_zero]

private def ThreefoldHomology.FifthDegree.nativeFifthBoundary
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (i : SpecialPeriods.Threefold.Puncture) :
    SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary i) 4 :=
  ThreefoldOverlapMappingTorus.overlapHomologyEquiv i 4
    (ThreefoldHomology.starConnectingHomomorphism 4 a i)

private theorem ThreefoldHomology.FifthDegree.nativeFifthBoundary_wang_coordinates
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (i : SpecialPeriods.Threefold.Puncture) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy i) 3
          (nativeFifthBoundary a i)) =
      Pi.single 3 (ThreefoldHomology.FourthWang.fifthWangCoordinate a) :=
  ThreefoldHomology.FourthWang.fifthWangCoordinate_coordinates a i

private theorem ThreefoldHomology.FifthDegree.nativeFifthBoundary_cap_zero
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (i : SpecialPeriods.Threefold.Puncture) :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap i 4 (nativeFifthBoundary a i) = 0 := by
  have h :=
    LinearMap.congr_fun (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_retraction i 4)
      (ThreefoldHomology.starConnectingHomomorphism 4 a i)
  exact h.trans (ThreefoldHomology.FourthWang.connecting_four_cap_zero a i)

private theorem ThreefoldHomology.FifthDegree.nativeFifthBoundary_regular_sum_zero
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5) :
    (∑ i : SpecialPeriods.Threefold.Puncture,
        ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i 4 (nativeFifthBoundary a i)) =
      0 := by
  calc
    _ =
        ∑ i : SpecialPeriods.Threefold.Puncture,
          SingularMayerVietoris.singularHomologyMap (ThreefoldHomology.overlapToRegularFamily i) 4
            (ThreefoldHomology.starConnectingHomomorphism 4 a i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact
        LinearMap.congr_fun
          (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap_retraction i 4) _
    _ = 0 := ThreefoldHomology.FourthWang.connecting_four_regular_zero a

private def ThreefoldHomology.FifthDegree.fifthReferenceBoundary :
    (i : SpecialPeriods.Threefold.Puncture) →
      SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary i) 4
  | none => CuspBoundaryGammaZero.nativeClass
  | some j => -PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass j

@[simp]
private theorem ThreefoldHomology.FifthDegree.fifthReferenceBoundary_cusp :
    fifthReferenceBoundary Option.none = CuspBoundaryGammaZero.nativeClass :=
  rfl

private theorem ThreefoldHomology.FifthDegree.fifthReferenceBoundary_wang_coordinates
    (i : SpecialPeriods.Threefold.Puncture) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy i) 3
          (fifthReferenceBoundary i)) =
      Pi.single (3 : Fin 4) 1 := by
  cases i with
  | none => exact CuspBoundaryGammaZero.nativeClass_wang_coordinates
  | some
    j =>
    change
      PeriodFamily.FlatTorus.singularH3Coordinates
          (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) 3
            (-PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass j)) =
        _
    rw [map_neg, map_neg, PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass_wang,
      neg_neg]

private theorem ThreefoldHomology.FifthDegree.nativeFifthBoundary_sub_reference_wang_zero
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (i : SpecialPeriods.Threefold.Puncture) :
    MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy i) 3
        (nativeFifthBoundary a i -
          ThreefoldHomology.FourthWang.fifthWangCoordinate a • fifthReferenceBoundary i) =
      0 := by
  apply PeriodFamily.FlatTorus.singularH3Coordinates.injective
  rw [map_sub, map_zsmul, map_sub, map_zsmul, nativeFifthBoundary_wang_coordinates,
    fifthReferenceBoundary_wang_coordinates, map_zero]
  ext j
  by_cases hj : j = 3
  · subst j
    simp
  · simp [Pi.single_eq_of_ne hj]

private theorem ThreefoldHomology.FifthDegree.exists_fifth_boundary_fibres
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5) :
    ∃ b : SpecialPeriods.Threefold.Puncture → SingularMayerVietoris.SingularHomology RealTorus₄ 4,
      ∀ i,
        MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 4 (b i) =
          nativeFifthBoundary a i -
            ThreefoldHomology.FourthWang.fifthWangCoordinate a • fifthReferenceBoundary i := by
  have h (i : SpecialPeriods.Threefold.Puncture) :
    nativeFifthBoundary a i -
        ThreefoldHomology.FourthWang.fifthWangCoordinate a • fifthReferenceBoundary i ∈
      LinearMap.range
        (MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 4) := by
    rw [MappingTorusHomology.wang_exact_at_mappingTorus (ThreefoldOverlapMappingTorus.monodromy i)
        3]
    exact nativeFifthBoundary_sub_reference_wang_zero a i
  choose b hb using h
  exact ⟨b, hb⟩

private def ThreefoldHomology.FifthDegree.cuspResidualCoefficient : ℤ :=
  PeriodTorusHigherHomology.realTorusH4Equiv
    (ThreefoldHomologyCuspFibre.cuspFibreFourEquiv.symm
      (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 4
        CuspBoundaryGammaZero.nativeClass))

private theorem ThreefoldHomology.FifthDegree.cuspFibre_coordinate_of_decomposition
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (b : SingularMayerVietoris.SingularHomology RealTorus₄ 4)
    (hb :
      MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy Option.none) 4
          b =
        nativeFifthBoundary a Option.none -
          ThreefoldHomology.FourthWang.fifthWangCoordinate a •
            fifthReferenceBoundary Option.none) :
    PeriodTorusHigherHomology.realTorusH4Equiv b =
      -(ThreefoldHomology.FourthWang.fifthWangCoordinate a * cuspResidualCoefficient) := by
  have h := congrArg (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 4) hb
  rw [ThreefoldHomologyCuspFibre.cuspCap_four_fibre, map_sub, map_zsmul,
    nativeFifthBoundary_cap_zero, fifthReferenceBoundary_cusp, zero_sub] at h
  have hc :=
    congrArg
      (fun x =>
        PeriodTorusHigherHomology.realTorusH4Equiv
          (ThreefoldHomologyCuspFibre.cuspFibreFourEquiv.symm x))
      h
  simpa only [LinearEquiv.symm_apply_apply, map_neg, map_zsmul, smul_eq_mul,
    cuspResidualCoefficient] using hc

private theorem ThreefoldHomology.FifthDegree.ellipticFibre_coordinate_of_decomposition
    (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (b : SingularMayerVietoris.SingularHomology RealTorus₄ 4)
    (hb :
      MappingTorusHomology.fibreHomologyMap
          (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 4 b =
        nativeFifthBoundary a (Option.some j) -
          ThreefoldHomology.FourthWang.fifthWangCoordinate a •
            fifthReferenceBoundary (Option.some j)) :
    (j.order : ℤ) * γ j.twist * PeriodTorusHigherHomology.realTorusH4Equiv b =
      ThreefoldHomology.FourthWang.fifthWangCoordinate a := by
  let c :
    SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary (Option.some j))
        4 →ₗ[ℤ]
      ℤ :=
    (Elliptic.HigherHomology.surfaceH4Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).toLinearMap.comp
      ((ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j 4).toLinearMap.comp
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4))
  have hunit : c (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass j) = 1 :=
    PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass_filling j
  have href : c (fifthReferenceBoundary (Option.some j)) = -1 :=
    (map_neg c (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass j)).trans
      (congrArg Neg.neg hunit)
  have hzero : c (nativeFifthBoundary a (Option.some j)) = 0 := by
    change
      Elliptic.HigherHomology.surfaceH4Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
          (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j 4
            (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4
              (nativeFifthBoundary a (Option.some j)))) =
        0
    rw [nativeFifthBoundary_cap_zero, map_zero, map_zero]
  have hfibre :
    c
        (MappingTorusHomology.fibreHomologyMap
          (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 4 b) =
      (j.order : ℤ) * γ j.twist * PeriodTorusHigherHomology.realTorusH4Equiv b :=
    PeriodFamily.Boundary.EllipticTopFibre.boundaryFilling_fibre_h4_coordinates j b
  have h := congrArg c hb
  rw [hfibre, map_sub, map_zsmul, hzero, href] at h
  simpa using h

private theorem ThreefoldHomology.FifthDegree.threeFibre_coordinate_of_decomposition
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (b : SingularMayerVietoris.SingularHomology RealTorus₄ 4)
    (hb :
      MappingTorusHomology.fibreHomologyMap
          (ThreefoldOverlapMappingTorus.monodromy (Option.some Elliptic.Kind.three)) 4 b =
        nativeFifthBoundary a (Option.some .three) -
          ThreefoldHomology.FourthWang.fifthWangCoordinate a •
            fifthReferenceBoundary (Option.some .three)) :
    3 * PeriodTorusHigherHomology.realTorusH4Equiv b =
      ThreefoldHomology.FourthWang.fifthWangCoordinate a := by
  simpa [Elliptic.Kind.order, Elliptic.Kind.twist, γ, ε] using
    ellipticFibre_coordinate_of_decomposition .three a b hb

private theorem ThreefoldHomology.FifthDegree.fourFibre_coordinate_of_decomposition
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (b : SingularMayerVietoris.SingularHomology RealTorus₄ 4)
    (hb :
      MappingTorusHomology.fibreHomologyMap
          (ThreefoldOverlapMappingTorus.monodromy (Option.some Elliptic.Kind.four)) 4 b =
        nativeFifthBoundary a (Option.some .four) -
          ThreefoldHomology.FourthWang.fifthWangCoordinate a •
            fifthReferenceBoundary (Option.some .four)) :
    -4 * PeriodTorusHigherHomology.realTorusH4Equiv b =
      ThreefoldHomology.FourthWang.fifthWangCoordinate a := by
  simpa [Elliptic.Kind.order, Elliptic.Kind.twist, γ, ε'] using
    ellipticFibre_coordinate_of_decomposition .four a b hb

private theorem ThreefoldHomology.FifthDegree.fifthReferenceBoundary_regular_sum_zero :
    (∑ i : SpecialPeriods.Threefold.Puncture,
        ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i 4 (fifthReferenceBoundary i)) =
      0 := by
  classical
  have he (j : Elliptic.Kind) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) 4
        (fifthReferenceBoundary (Option.some j)) =
      -ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) 4
          (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass j) :=
    map_neg (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) 4)
      (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass j)
  rw [Fintype.sum_option]
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four)]
  rw [fifthReferenceBoundary_cusp, he, he]
  rw [PeriodFamily.Boundary.FourthRelation.nativeClass_regular_eq_capSections]
  abel

private theorem ThreefoldHomology.FifthDegree.fifth_boundary_fibres_sum_zero
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (b : SpecialPeriods.Threefold.Puncture → SingularMayerVietoris.SingularHomology RealTorus₄ 4)
    (hb :
      ∀ i,
        MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 4 (b i) =
          nativeFifthBoundary a i -
            ThreefoldHomology.FourthWang.fifthWangCoordinate a • fifthReferenceBoundary i) :
    (∑ i : SpecialPeriods.Threefold.Puncture, b i) = 0 := by
  apply
    PeriodFamily.Boundary.normalizedFamilyFibreHomologyFour_injective
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
  rw [map_sum, map_zero]
  calc
    _ =
        ∑ i : SpecialPeriods.Threefold.Puncture,
          ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i 4
            (MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 4
              (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (PeriodFamily.Boundary.boundaryRegularHomologyMap_common_fibre_apply i 4 (b i)).symm
    _ =
        ∑ i : SpecialPeriods.Threefold.Puncture,
          ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i 4
            (nativeFifthBoundary a i -
              ThreefoldHomology.FourthWang.fifthWangCoordinate a • fifthReferenceBoundary i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hb i]
    _ =
        (∑ i : SpecialPeriods.Threefold.Puncture,
            ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i 4
              (nativeFifthBoundary a i)) -
          ThreefoldHomology.FourthWang.fifthWangCoordinate a •
            ∑ i : SpecialPeriods.Threefold.Puncture,
              ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i 4
                (fifthReferenceBoundary i) := by
      have hs (i : SpecialPeriods.Threefold.Puncture) :
        ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i 4
            (ThreefoldHomology.FourthWang.fifthWangCoordinate a • fifthReferenceBoundary i) =
          ThreefoldHomology.FourthWang.fifthWangCoordinate a •
            ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i 4
              (fifthReferenceBoundary i) :=
        map_zsmul (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i 4)
          (ThreefoldHomology.FourthWang.fifthWangCoordinate a) (fifthReferenceBoundary i)
      simp only [map_sub, hs, Finset.sum_sub_distrib]
      congr 1
      exact
        (map_sum
            (zsmulAddGroupHom (α :=
              SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily
                4)
              (ThreefoldHomology.FourthWang.fifthWangCoordinate a))
            (fun i : SpecialPeriods.Threefold.Puncture =>
              ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i 4
                (fifthReferenceBoundary i))
            Finset.univ).symm
    _ = 0 := by
      rw [nativeFifthBoundary_regular_sum_zero, fifthReferenceBoundary_regular_sum_zero]
      have hz :=
        @zsmul_zero
          (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily 4)
          _ (ThreefoldHomology.FourthWang.fifthWangCoordinate a)
      exact
        (congrArg
              (fun x :
                  SingularMayerVietoris.SingularHomology
                    SpecialPeriods.Threefold.SpecialRegularFamily 4 =>
                0 - x)
              hz).trans
          (sub_self 0)

private theorem ThreefoldHomology.FifthDegree.fifth_boundary_fibre_coordinates_sum_zero
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5)
    (b : SpecialPeriods.Threefold.Puncture → SingularMayerVietoris.SingularHomology RealTorus₄ 4)
    (hb :
      ∀ i,
        MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 4 (b i) =
          nativeFifthBoundary a i -
            ThreefoldHomology.FourthWang.fifthWangCoordinate a • fifthReferenceBoundary i) :
    PeriodTorusHigherHomology.realTorusH4Equiv (b (Option.some .three)) +
          PeriodTorusHigherHomology.realTorusH4Equiv (b (Option.some .four)) +
        PeriodTorusHigherHomology.realTorusH4Equiv (b Option.none) =
      0 := by
  have h :=
    congrArg PeriodTorusHigherHomology.realTorusH4Equiv (fifth_boundary_fibres_sum_zero a b hb)
  rw [map_sum, map_zero, Fintype.sum_option] at h
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four)] at h
  omega

private theorem ThreefoldHomology.FifthDegree.fifthWangCoordinate_vanishes
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5) :
    ThreefoldHomology.FourthWang.fifthWangCoordinate a = 0 := by
  obtain ⟨b, hb⟩ := exists_fifth_boundary_fibres a
  have hthree :=
    threeFibre_coordinate_of_decomposition a (b (Option.some .three)) (hb (Option.some .three))
  have hfour :=
    fourFibre_coordinate_of_decomposition a (b (Option.some .four)) (hb (Option.some .four))
  have hcusp := cuspFibre_coordinate_of_decomposition a (b Option.none) (hb Option.none)
  have hsum := fifth_boundary_fibre_coordinates_sum_zero a b hb
  have hregular :
    PeriodTorusHigherHomology.realTorusH4Equiv (b (Option.some .three)) +
        PeriodTorusHigherHomology.realTorusH4Equiv (b (Option.some .four)) =
      cuspResidualCoefficient * ThreefoldHomology.FourthWang.fifthWangCoordinate a := by
    linear_combination hsum - hcusp
  exact
    signed_residual_coordinate_zero (ThreefoldHomology.FourthWang.fifthWangCoordinate a)
      (PeriodTorusHigherHomology.realTorusH4Equiv (b (Option.some .three)))
      (PeriodTorusHigherHomology.realTorusH4Equiv (b (Option.some .four))) cuspResidualCoefficient
      hthree hfour hregular

private theorem ThreefoldHomology.FifthDegree.homologyFive_eq_zero
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5) : a = 0 :=
  ThreefoldHomology.FourthWang.fifthWangCoordinate_eq_zero a (fifthWangCoordinate_vanishes a)

private theorem ThreefoldHomology.FifthDegree.homologyFive_subsingleton :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 5) :=
  ⟨fun a b => (homologyFive_eq_zero a).trans (homologyFive_eq_zero b).symm⟩

private theorem ThreefoldHomology.FourthDegree.nativeCapKernelRegularMap_four_surjective :
    Function.Surjective (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 4) :=
  ThreefoldHomology.CapElimination.nativeCapKernelRegularMap_surjective_of_fibre_range 3
    ThreefoldHomology.FourthSource.nativeCapKernelSourceMap_three_surjective
    ThreefoldHomology.FourthFibre.fibre_range_le

private theorem ThreefoldHomology.FourthDegree.starLeft_four_surjective :
    Function.Surjective (ThreefoldHomology.starLeftHomologyMap 4) :=
  ThreefoldHomology.CapElimination.starLeft_surjective_of_nativeCapKernel 4
    nativeCapKernelRegularMap_four_surjective

private theorem ThreefoldHomology.FourthDegree.starRight_four_eq_zero :
    ThreefoldHomology.starRightHomologyMap 4 = 0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := starLeft_four_surjective a
  exact (ThreefoldHomology.star_exact_at_pair 4).apply_apply_eq_zero b

private theorem ThreefoldHomology.FourthDegree.connecting_three_injective :
    Function.Injective (ThreefoldHomology.starConnectingHomomorphism 3) := by
  intro a b hab
  have hz : ThreefoldHomology.starConnectingHomomorphism 3 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (ThreefoldHomology.star_exact_at_ambient 3 (a - b)).mp hz
  rw [starRight_four_eq_zero, LinearMap.zero_apply] at hc
  exact sub_eq_zero.mp hc.symm

private def ThreefoldHomology.FourthDegree.connectingIntoKernel :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 4 →ₗ[ℤ]
      LinearMap.ker (ThreefoldHomology.starLeftHomologyMap 3) :=
  (ThreefoldHomology.starConnectingHomomorphism 3).codRestrict
    (LinearMap.ker (ThreefoldHomology.starLeftHomologyMap 3))
    (fun a => (ThreefoldHomology.star_exact_at_intersection 3).apply_apply_eq_zero a)

private theorem ThreefoldHomology.FourthDegree.connectingIntoKernel_bijective :
    Function.Bijective connectingIntoKernel := by
  constructor
  · intro a b hab
    exact connecting_three_injective (congrArg Subtype.val hab)
  · intro a
    obtain ⟨b, hb⟩ := (ThreefoldHomology.star_exact_at_intersection 3 a.val).mp a.property
    exact ⟨b, Subtype.ext hb⟩

private def ThreefoldHomology.FourthDegree.homologyFourKernelEquiv :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 4 ≃ₗ[ℤ]
      LinearMap.ker (ThreefoldHomology.starLeftHomologyMap 3) :=
  LinearEquiv.ofBijective connectingIntoKernel connectingIntoKernel_bijective

private def ThreefoldHomology.ThirdDegree.starKernelIntoCapKernel (n : ℕ)
    (a : LinearMap.ker (ThreefoldHomology.starLeftHomologyMap n)) :
    LinearMap.ker (ThreefoldHomology.starOverlapToFillingsHomologyMap n) :=
  ⟨a.val,
    by
    have h : -ThreefoldHomology.starOverlapToFillingsHomologyMap n a.val = 0 :=
      congrArg Prod.snd a.property
    exact neg_eq_zero.mp h⟩

private def ThreefoldHomology.ThirdDegree.starKernelToNative (n : ℕ) :
    LinearMap.ker (ThreefoldHomology.starLeftHomologyMap n) →ₗ[ℤ]
      LinearMap.ker (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap n) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun
        a :=
        ⟨ThreefoldHomology.CapElimination.nativeCapKernelEquiv n (starKernelIntoCapKernel n a),
          by
          change
            ThreefoldHomology.CapElimination.nativeCapKernelRegularMap n
                (ThreefoldHomology.CapElimination.nativeCapKernelEquiv n
                  (starKernelIntoCapKernel n a)) =
              0
          rw [ThreefoldHomology.CapElimination.nativeCapKernelRegularMap_equiv]
          exact congrArg Prod.fst a.property⟩
      map_zero' := by
        apply Subtype.ext
        exact (ThreefoldHomology.CapElimination.nativeCapKernelEquiv n).map_zero
      map_add' a
        b := by
        apply Subtype.ext
        exact
          (ThreefoldHomology.CapElimination.nativeCapKernelEquiv n).map_add
            (starKernelIntoCapKernel n a) (starKernelIntoCapKernel n b) }

private theorem ThreefoldHomology.ThirdDegree.starKernelToNative_injective (n : ℕ) :
    Function.Injective (starKernelToNative n) := by
  intro a b hab
  apply Subtype.ext
  have h :=
    (ThreefoldHomology.CapElimination.nativeCapKernelEquiv n).injective (congrArg Subtype.val hab)
  exact
    congrArg
      (fun c : LinearMap.ker (ThreefoldHomology.starOverlapToFillingsHomologyMap n) => c.val) h

private theorem ThreefoldHomology.ThirdDegree.starKernelToNative_surjective (n : ℕ) :
    Function.Surjective (starKernelToNative n) := by
  intro a
  let b := (ThreefoldHomology.CapElimination.nativeCapKernelEquiv n).symm a.val
  have hreg : ThreefoldHomology.starOverlapToRegularHomologyMap n b.val = 0 := by
    have h := ThreefoldHomology.CapElimination.nativeCapKernelRegularMap_equiv n b
    change
      ThreefoldHomology.CapElimination.nativeCapKernelRegularMap n
          (ThreefoldHomology.CapElimination.nativeCapKernelEquiv n
            ((ThreefoldHomology.CapElimination.nativeCapKernelEquiv n).symm a.val)) =
        _ at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm.trans a.property
  refine ⟨⟨b.val, ?_⟩, ?_⟩
  · change ThreefoldHomology.starLeftHomologyMap n b.val = 0
    rw [ThreefoldHomology.CapElimination.starLeft_regular_fillings, hreg, b.property, neg_zero]
    rfl
  · apply Subtype.ext
    exact (ThreefoldHomology.CapElimination.nativeCapKernelEquiv n).apply_symm_apply a.val

private def ThreefoldHomology.ThirdDegree.starKernelNativeEquiv (n : ℕ) :
    LinearMap.ker (ThreefoldHomology.starLeftHomologyMap n) ≃ₗ[ℤ]
      LinearMap.ker (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap n) :=
  LinearEquiv.ofBijective (starKernelToNative n)
    ⟨starKernelToNative_injective n, starKernelToNative_surjective n⟩

private def ThreefoldHomology.ThirdDegree.residualMultiplication : ℤ →ₗ[ℤ] ℤ :=
  LinearMap.toSpanSingleton ℤ ℤ referenceFibreCoefficient

private def ThreefoldHomology.ThirdDegree.residualKernelToNative :
    LinearMap.ker residualMultiplication →ₗ[ℤ]
      LinearMap.ker (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun
        a :=
        ⟨a.val • referenceClasses,
          by
          change
            ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3
                (a.val • referenceClasses) =
              0
          rw [nativeCapKernelRegularMap_smul_reference]
          have ha : a.val * referenceFibreCoefficient = 0 := a.property
          rw [ha, map_zero]⟩
      map_zero' := by
        apply Subtype.ext
        exact zero_smul ℤ referenceClasses
      map_add' a
        b := by
        apply Subtype.ext
        exact add_smul a.val b.val referenceClasses }

private theorem ThreefoldHomology.ThirdDegree.residualKernelToNative_injective :
    Function.Injective residualKernelToNative := by
  intro a b hab
  apply Subtype.ext
  exact ThreefoldHomology.ThirdSource.referenceClasses_smul_injective (congrArg Subtype.val hab)

private theorem ThreefoldHomology.ThirdDegree.residualKernelToNative_surjective :
    Function.Surjective residualKernelToNative := by
  intro a
  obtain ⟨k, hk, hz⟩ := (nativeCapKernelRegularMap_three_eq_zero_iff a.val).mp a.property
  exact ⟨⟨k, hz⟩, Subtype.ext hk.symm⟩

private def ThreefoldHomology.ThirdDegree.residualNativeKernelEquiv :
    LinearMap.ker residualMultiplication ≃ₗ[ℤ]
      LinearMap.ker (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3) :=
  LinearEquiv.ofBijective residualKernelToNative
    ⟨residualKernelToNative_injective, residualKernelToNative_surjective⟩

private def ThreefoldHomology.ThirdDegree.homologyFourResidualKernelEquiv :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 4 ≃ₗ[ℤ]
      LinearMap.ker residualMultiplication :=
  (ThreefoldHomology.FourthDegree.homologyFourKernelEquiv.toAddEquiv.trans
      ((starKernelNativeEquiv 3).toAddEquiv.trans
        residualNativeKernelEquiv.symm.toAddEquiv)).toIntLinearEquiv

private def ThreefoldHomology.ThirdDegree.homologyFourCoefficientMap :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 4 →ₗ[ℤ] ℤ :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun a := (homologyFourResidualKernelEquiv a).val
      map_zero' := by rw [map_zero, Submodule.coe_zero]
      map_add' a b := by rw [map_add, Submodule.coe_add] }

private theorem ThreefoldHomology.ThirdDegree.homologyFourCoefficientMap_injective :
    Function.Injective homologyFourCoefficientMap := by
  intro a b hab
  exact homologyFourResidualKernelEquiv.injective (Subtype.ext hab)

private theorem ThreefoldHomology.ThirdDegree.homologyFourCoefficientMap_mul
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 4) :
    homologyFourCoefficientMap a * referenceFibreCoefficient = 0 :=
  (homologyFourResidualKernelEquiv a).property

private theorem
  ThreefoldHomology.ThirdDegree.homologyThree_subsingleton_iff_referenceFibreCoefficient_isUnit :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 3) ↔
      IsUnit referenceFibreCoefficient := by
  rw [homologyThree_subsingleton_iff_generator_eq_zero]
  change homologyThreeCyclicMap 1 = 0 ↔ IsUnit referenceFibreCoefficient
  rw [homologyThreeCyclicMap_eq_zero_iff, isUnit_iff_exists_inv']

private theorem
  ThreefoldHomology.ThirdDegree.homologyFour_subsingleton_iff_referenceFibreCoefficient_ne_zero :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 4) ↔
      referenceFibreCoefficient ≠ 0 := by
  constructor
  · intro hss hr
    let a : LinearMap.ker residualMultiplication :=
      ⟨1, by
        change 1 * referenceFibreCoefficient = 0
        rw [hr, MulZeroClass.mul_zero]⟩
    have h :=
      hss.elim (homologyFourResidualKernelEquiv.symm a) (homologyFourResidualKernelEquiv.symm 0)
    have ha : a = 0 := homologyFourResidualKernelEquiv.symm.injective h
    have hone : (1 : ℤ) = 0 := congrArg Subtype.val ha
    exact one_ne_zero hone
  · intro hr
    have hz (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 4) :
      a = 0 := by
      apply homologyFourCoefficientMap_injective
      rw [map_zero]
      exact (mul_eq_zero.mp (homologyFourCoefficientMap_mul a)).resolve_right hr
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩

private theorem ThreefoldHomology.ThirdDegree.referenceFibreCoefficient_eq_one :
    referenceFibreCoefficient = 1 :=
  (referenceFibreCoefficient_eq_iff 1).mpr
    PeriodFamily.Boundary.ThirdRelation.referenceClasses_regular

private theorem ThreefoldHomology.ThirdDegree.referenceFibreCoefficient_isUnit :
    IsUnit referenceFibreCoefficient := by
  rw [referenceFibreCoefficient_eq_one]
  exact isUnit_one

private theorem ThreefoldHomology.ThirdDegree.homologyThree_subsingleton :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 3) :=
  homologyThree_subsingleton_iff_referenceFibreCoefficient_isUnit.mpr
    referenceFibreCoefficient_isUnit

private theorem ThreefoldHomology.FourthDegree.homologyFour_subsingleton :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 4) :=
  ThreefoldHomology.ThirdDegree.homologyFour_subsingleton_iff_referenceFibreCoefficient_ne_zero.mpr
    ThreefoldHomology.ThirdDegree.referenceFibreCoefficient_isUnit.ne_zero

end Mathoverflow1973

end
