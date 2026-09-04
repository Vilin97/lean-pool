/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.CuspFibre.CuspBoundaryTopVanishing
public import LeanPool.HopfProblem.MainTheorem.SixSphereCube2
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.PeriodFamily.Core3
import all LeanPool.HopfProblem.PeriodFamily.Core4
import all LeanPool.HopfProblem.Pi1.TwistGroup
import all LeanPool.HopfProblem.PeriodFamily.Core5
import all LeanPool.HopfProblem.Elliptic.Core7
import all LeanPool.HopfProblem.PeriodFamily.Core6
import all LeanPool.HopfProblem.PeriodFamily.Core7
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology3
import all LeanPool.HopfProblem.PeriodFamily.Core8
import all LeanPool.HopfProblem.CuspFibre.CuspBoundaryTopVanishing
import all LeanPool.HopfProblem.MainTheorem.SixSphereCube2

/-!
# Hopf problem: period family · core 9

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

private theorem
    PeriodFamily.Boundary.FourthRelation.unitCapSection_wang_eq_neg_cusp (j : Elliptic.Kind) :
    MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) 3
        (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass j) =
      -MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
          CuspBoundaryGammaZero.nativeClass := by
  apply PeriodFamily.FlatTorus.singularH3Coordinates.injective
  rw [PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass_wang, map_neg,
    CuspBoundaryGammaZero.nativeClass_wang_coordinates]

private theorem PeriodFamily.Boundary.FourthRelation.nativeClass_wang_first_inv_fixed :
    PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ 3
        (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
          CuspBoundaryGammaZero.nativeClass) =
      MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
        CuspBoundaryGammaZero.nativeClass := by
  have h :=
    PeriodFamily.Boundary.ellipticWangBoundary_generator_inv_fixed .three
      Elliptic.Kind.three.twist 3
      (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .three)
  change
    PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ 3
        (MappingTorusHomology.wangBoundary
          (Elliptic.flatTorusAffine .three Elliptic.Kind.three.twist) 3
          (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .three)) =
      MappingTorusHomology.wangBoundary
        (Elliptic.flatTorusAffine .three Elliptic.Kind.three.twist) 3
        (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .three) at h
  rw [unitCapSection_wang_eq_neg_cusp, map_neg] at h
  exact neg_injective h

private theorem PeriodFamily.Boundary.FourthRelation.unitCapSection_regular_mem_range
    (j : Elliptic.Kind) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) 4
        (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass j) ∈
      LinearMap.range
        (PeriodFamily.GammaZero.homologyInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          4) :=
  PeriodFamily.Boundary.EllipticGaugeLinearization.boundaryRegularHomologyMap_capSection_mem_range
    j 0 4
    ((Elliptic.HigherHomology.surfaceH4Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
      1)

private theorem PeriodFamily.Boundary.FourthRelation.nativeClass_sourceKernel_eq_capSections :
    PeriodFamily.Homology.sourceKernelProjection
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        3
        (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 4
          CuspBoundaryGammaZero.nativeClass) =
      PeriodFamily.Homology.sourceKernelProjection
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        3
        (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.three)
            4 (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .three) +
          ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.four)
            4 (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .four)) := by
  apply Subtype.ext
  have hadd :
    (PeriodFamily.Homology.sourceKernelProjection
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          3
          (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap
              (Option.some Elliptic.Kind.three) 4
              (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .three) +
            ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap
              (Option.some Elliptic.Kind.four) 4
              (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .four)) :
        SingularMayerVietoris.SingularHomology RealTorus₄ 3 ×
          SingularMayerVietoris.SingularHomology RealTorus₄ 3) =
      (PeriodFamily.Homology.sourceKernelProjection
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            3
            (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap
              (Option.some Elliptic.Kind.three) 4
              (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .three)) :
          SingularMayerVietoris.SingularHomology RealTorus₄ 3 ×
            SingularMayerVietoris.SingularHomology RealTorus₄ 3) +
        (PeriodFamily.Homology.sourceKernelProjection
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            3
            (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap
              (Option.some Elliptic.Kind.four) 4
              (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .four)) :
          SingularMayerVietoris.SingularHomology RealTorus₄ 3 ×
            SingularMayerVietoris.SingularHomology RealTorus₄ 3) :=
    congrArg Subtype.val
      (map_add
        (PeriodFamily.Homology.sourceKernelProjection
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          3)
        _ _)
  have hc :
    (PeriodFamily.Homology.sourceKernelProjection
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          3
          (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 4
            CuspBoundaryGammaZero.nativeClass) :
        SingularMayerVietoris.SingularHomology RealTorus₄ 3 ×
          SingularMayerVietoris.SingularHomology RealTorus₄ 3) =
      (-PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ 3
            (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
              CuspBoundaryGammaZero.nativeClass),
        -MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
            CuspBoundaryGammaZero.nativeClass) :=
    PeriodFamily.Boundary.Cusp.boundary_four_sourceKernelProjection
      CuspBoundaryGammaZero.nativeClass
  rw [hc, hadd, PeriodFamily.Boundary.ellipticThreeBoundary_sourceKernelProjection,
    PeriodFamily.Boundary.ellipticFourBoundary_sourceKernelProjection,
    unitCapSection_wang_eq_neg_cusp, unitCapSection_wang_eq_neg_cusp,
    nativeClass_wang_first_inv_fixed]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

private theorem PeriodFamily.Boundary.FourthRelation.nativeClass_regular_eq_capSections :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 4
        CuspBoundaryGammaZero.nativeClass =
      ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.three) 4
          (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .three) +
        ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some Elliptic.Kind.four) 4
          (PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass .four) := by
  apply
    PeriodFamily.GammaZero.sourceKernelProjection_injOn_range
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
      CuspBoundaryGammaZero.nativeClass_regular_mem_range
      (Submodule.add_mem _ (unitCapSection_regular_mem_range .three)
        (unitCapSection_regular_mem_range .four))
  exact nativeClass_sourceKernel_eq_capSections

private theorem PeriodFamily.Boundary.H5ToH4Wang_injective (f : RealTorus₄ ≃ₜ RealTorus₄) :
    Function.Injective (MappingTorusHomology.wangBoundary f 4) := by
  let : Subsingleton (SingularMayerVietoris.SingularHomology RealTorus₄ 5) :=
    PeriodTorusHigherHomology.realTorus_homology_subsingleton_of_lt (by decide : 4 < 5)
  have hzero : MappingTorusHomology.fibreHomologyMap f 5 = 0 := by
    apply LinearMap.ext
    intro a
    exact
      (congrArg (MappingTorusHomology.fibreHomologyMap f 5) (Subsingleton.elim a 0)).trans
        (map_zero (MappingTorusHomology.fibreHomologyMap f 5))
  apply LinearMap.ker_eq_bot.mp
  rw [← MappingTorusHomology.wang_exact_at_mappingTorus f 4, hzero, LinearMap.range_zero]

private theorem PeriodFamily.Boundary.H5ToH4Wang_surjective (f : RealTorus₄ ≃ₜ RealTorus₄)
    (hf : MappingTorusHomology.monodromyHomologyMap f 4 = LinearMap.id) :
    Function.Surjective (MappingTorusHomology.wangBoundary f 4) := by
  intro a
  have ha : a ∈ LinearMap.ker (MappingTorusHomology.wangDifference f 4) := by
    change a - MappingTorusHomology.monodromyHomologyMap f 4 a = 0
    rw [hf, LinearMap.id_apply, sub_self]
  rw [← MappingTorusHomology.wangBoundary_range f 4] at ha
  exact ha

private def PeriodFamily.Boundary.H5ToH4WangEquiv (f : RealTorus₄ ≃ₜ RealTorus₄)
    (hf : MappingTorusHomology.monodromyHomologyMap f 4 = LinearMap.id) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) 5 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ 4 :=
  LinearEquiv.ofBijective (MappingTorusHomology.wangBoundary f 4)
    ⟨H5ToH4Wang_injective f, H5ToH4Wang_surjective f hf⟩

private theorem PeriodFamily.Boundary.ThirdRelation.capCircle_surfaceCover_class (j : Elliptic.Kind)
    (n : ℕ) (hn : n = 1 ∨ n = 2) (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    PeriodFamily.Boundary.EllipticCapProduct.boundaryPositiveCircleCross j n
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover j) n a) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover j) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n a) := by
  rw [PeriodFamily.Boundary.EllipticCapProduct.boundaryPositiveCircleCross_apply, ←
    PeriodTorusHigherHomology.positiveCircleCross_naturality]
  have hmap :=
    congrArg
      (fun f :
          C(MappingTorus.Circle × RealTorus₄,
            ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j) =>
        SingularMayerVietoris.singularHomologyMap f (n + 1))
      (PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover_comp_shear j)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp] at hmap
  have h :=
    LinearMap.congr_fun hmap (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n a)
  simpa only [LinearMap.comp_apply,
    PeriodFamily.Boundary.EllipticCapKernelWang.nativeShear_positiveCircleCross j n hn a] using
    h.symm

private theorem PeriodFamily.Boundary.ThirdRelation.surfaceCover_two_combination (j : Elliptic.Kind)
    (p q : ℤ) :
    Elliptic.HigherHomology.surfaceH2Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover j) 2
          (p • PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo j +
            q • PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo j)) =
      ![p + q * PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo j,
        q * (Elliptic.HigherHomology.fibreNormIndex j : ℤ)] := by
  rw [map_add, map_zsmul, map_zsmul, map_add, map_zsmul, map_zsmul,
    PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitFibreClassTwo,
    PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitCircleClassTwo]
  ext i
  fin_cases i <;> simp

private theorem PeriodFamily.Boundary.ThirdRelation.capCircle_two_combination (j : Elliptic.Kind)
    (p q : ℤ) :
    PeriodFamily.Boundary.EllipticCapProduct.boundaryPositiveCircleCross j 2
        ((Elliptic.HigherHomology.surfaceH2Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
          ![p + q * PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo j,
            q * (Elliptic.HigherHomology.fibreNormIndex j : ℤ)]) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover j) 3
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 2
          (p • PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo j +
            q • PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo j)) := by
  have h :
    (Elliptic.HigherHomology.surfaceH2Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
        ![p + q * PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo j,
          q * (Elliptic.HigherHomology.fibreNormIndex j : ℤ)] =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover j) 2
        (p • PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo j +
          q • PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo j) := by
    apply
      (Elliptic.HigherHomology.surfaceH2Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).injective
    rw [LinearEquiv.apply_symm_apply, surfaceCover_two_combination]
  rw [h]
  exact capCircle_surfaceCover_class j 2 (Or.inr rfl) _

private theorem PeriodFamily.Boundary.ThirdRelation.capCircle_three_reference :
    PeriodFamily.Boundary.EllipticCapProduct.boundaryPositiveCircleCross .three 2
        ((Elliptic.HigherHomology.surfaceH2Equiv .three
              (SpecialPeriods.EllipticFilling.specialLocalData .three).centralPeriod).symm
          ![2 * PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo .three + 4, 2]) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover .three) 3
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 2
          ((4 : ℤ) • PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo .three +
            (2 : ℤ) • PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo .three)) := by
  have h := capCircle_two_combination .three 4 2
  have h₀ :
    4 + 2 * PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo .three =
      2 * PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo .three + 4 :=
    add_comm _ _
  have h₁ : (2 : ℤ) * (Elliptic.HigherHomology.fibreNormIndex .three : ℤ) = 2 := by decide
  rw [h₀, h₁] at h
  exact h

private theorem PeriodFamily.Boundary.ThirdRelation.capCircle_four_reference :
    PeriodFamily.Boundary.EllipticCapProduct.boundaryPositiveCircleCross .four 2
        ((Elliptic.HigherHomology.surfaceH2Equiv .four
              (SpecialPeriods.EllipticFilling.specialLocalData .four).centralPeriod).symm
          ![3 - PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo .four, -2]) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover .four) 3
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 2
          ((3 : ℤ) • PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo .four -
            PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo .four)) := by
  have h := capCircle_two_combination .four 3 (-1)
  simpa only [neg_one_mul, sub_eq_add_neg, Elliptic.HigherHomology.fibreNormIndex_four,
    Nat.cast_ofNat, neg_one_zsmul] using h

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.ThirdRelation.flatNegation : C(RealTorus₄, RealTorus₄) :=
  ⟨Neg.neg, ContinuousNeg.continuous_neg⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.ThirdRelation.triangleTorusHomeomorph_neg
    (g : SpecialPeriods.TriangleGroup) (x : RealTorus₄) :
    SpecialPeriods.triangleTorusHomeomorph g (-x) = -SpecialPeriods.triangleTorusHomeomorph g x :=
  by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  rw [← map_neg, SpecialPeriods.triangleTorusHomeomorph_mkQ, map_neg, map_neg,
    SpecialPeriods.triangleTorusHomeomorph_mkQ]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.ThirdRelation.familyNegation
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) : C(D.Space, D.Space)
    where
  toFun :=
    Quotient.lift
      (fun x : SpecialPeriods.TriangleRegularPoint × RealTorus₄ => D.quotient (x.1, -x.2))
      (by
        rintro x y ⟨g, hg⟩
        apply (D.quotient_eq_iff _ _).mpr
        refine ⟨g, ?_⟩
        apply Prod.ext
        · change g • y.1 = x.1
          exact congrArg (fun p : SpecialPeriods.TriangleRegularPoint × RealTorus₄ => p.1) hg
        · change SpecialPeriods.triangleTorusHomeomorph g (-y.2) = -x.2
          rw [triangleTorusHomeomorph_neg]
          exact congrArg Neg.neg (congrArg Prod.snd hg))
  continuous_toFun :=
    D.quotient_isQuotientMap.continuous_iff.mpr
      (D.quotient_continuous.comp (continuous_fst.prodMk continuous_snd.neg))

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.Boundary.ThirdRelation.familyNegation_quotient
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : SpecialPeriods.TriangleRegularPoint) (x : RealTorus₄) :
    familyNegation D (D.quotient (b, x)) = D.quotient (b, -x) :=
  rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.ThirdRelation.familyNegation_comp_fibre
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : PeriodFamily.Homology.SlitBaseLift) :
    (familyNegation D).comp (PeriodFamily.Homology.familyFibreInclusion D b) =
      (PeriodFamily.Homology.familyFibreInclusion D b).comp flatNegation :=
  rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.ThirdRelation.torusMatrixMap_neg_one_mo1973_30293
    (x : PeriodTorusHigherHomology.ProductTorus 4) :
    PeriodTorusHigherHomology.torusMatrixMap (-1 : LatticeMatrix) x = -x := by
  ext i
  simp [PeriodTorusHigherHomology.torusMatrixMap_apply, Matrix.one_apply]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.ThirdRelation.square_neg_one_mo1973_30294 :
    LocalSystemMatrices.exteriorSquare (-1 : LatticeMatrix) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.ThirdRelation.cube_neg_one_mo1973_30295 :
    LocalSystemMatrices.exteriorCube (-1 : LatticeMatrix) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.ThirdRelation.flatNegation_circle_comp :
    (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4)).comp
        flatNegation =
      (PeriodTorusHigherHomology.torusMatrixMap (-1 : LatticeMatrix)).comp
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4)) := by
  apply ContinuousMap.ext
  intro x
  change
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph (-x) =
      PeriodTorusHigherHomology.torusMatrixMap (-1 : LatticeMatrix)
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph x)
  rw [torusMatrixMap_neg_one_mo1973_30293]
  exact map_neg PeriodTorusHigherHomology.flatTorusCircleMap x

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.ThirdRelation.flatNegation_circle_homology (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
        n (SingularMayerVietoris.singularHomologyMap flatNegation n a) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusMatrixMap (-1 : LatticeMatrix)) n
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
          n a) := by
  have h :=
    congrArg
      (fun f : C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4) =>
        SingularMayerVietoris.singularHomologyMap f n)
      flatNegation_circle_comp
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.ThirdRelation.flatNegation_homology_two
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    SingularMayerVietoris.singularHomologyMap flatNegation 2 a = a := by
  apply PeriodFamily.FlatTorus.singularH2Coordinates.injective
  change
    PeriodTorusHigherHomology.coordinateTorusH2Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
          2 (SingularMayerVietoris.singularHomologyMap flatNegation 2 a)) =
      PeriodTorusHigherHomology.coordinateTorusH2Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
          2 a)
  rw [flatNegation_circle_homology, PeriodTorusHigherHomology.coordinateTorusH2Coordinates_matrix,
    square_neg_one_mo1973_30294, Matrix.one_mulVec]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.ThirdRelation.flatNegation_homology_three
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    SingularMayerVietoris.singularHomologyMap flatNegation 3 a = -a := by
  apply PeriodFamily.FlatTorus.singularH3Coordinates.injective
  change
    PeriodTorusHigherHomology.coordinateTorusH3Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
          3 (SingularMayerVietoris.singularHomologyMap flatNegation 3 a)) =
      PeriodTorusHigherHomology.coordinateTorusH3Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
          3 (-a))
  rw [flatNegation_circle_homology, PeriodTorusHigherHomology.coordinateTorusH3Coordinates_matrix,
    cube_neg_one_mo1973_30295, Matrix.neg_mulVec, Matrix.one_mulVec, map_neg, map_neg]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.ThirdRelation.familyNegation_homology_fibre_three
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : PeriodFamily.Homology.SlitBaseLift)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    SingularMayerVietoris.singularHomologyMap (familyNegation D) 3
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion D b) 3 a) =
      -SingularMayerVietoris.singularHomologyMap (PeriodFamily.Homology.familyFibreInclusion D b)
          3 a := by
  have h :=
    congrArg (fun f : C(RealTorus₄, D.Space) => SingularMayerVietoris.singularHomologyMap f 3)
      (familyNegation_comp_fibre D b)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  have ha := LinearMap.congr_fun h a
  simpa only [LinearMap.comp_apply, flatNegation_homology_three, map_neg] using ha

private theorem PeriodFamily.Boundary.ThirdRelation.loopHomologyClass_add_zero {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] (p q : Path (0 : G) 0) :
    FirstHurewicz.loopHomologyClass (p.add q) =
      FirstHurewicz.loopHomologyClass p + FirstHurewicz.loopHomologyClass q := by
  have hp : (p.prod (Path.refl (0 : G))).map continuous_add = p.cast (add_zero 0) (add_zero 0) := by
    ext t
    simp only [Path.map_coe, Function.comp_apply, Path.prod_coe, Path.refl_apply, Path.cast_coe,
      add_zero]
  have hq : ((Path.refl (0 : G)).prod q).map continuous_add = q.cast (add_zero 0) (add_zero 0) := by
    ext t
    simp only [Path.map_coe, Function.comp_apply, Path.prod_coe, Path.refl_apply, Path.cast_coe,
      zero_add]
  have h :
    ((p.prod (Path.refl (0 : G))).trans ((Path.refl (0 : G)).prod q)).Homotopic (p.prod q) := by
    rw [Path.trans_prod_eq_prod_trans]
    exact ⟨Path.Homotopic.prodHomotopy (Path.Homotopy.transRefl p) (Path.Homotopy.reflTrans q)⟩
  have he :=
    FirstHurewicz.loopHomologyClass_homotopic
      (h.map (⟨fun x : G × G => x.1 + x.2, continuous_add⟩ : C(G × G, G)))
  rw [Path.map_trans, FirstHurewicz.loopHomologyClass_trans, hp, hq] at he
  exact he.symm

private theorem PeriodFamily.Boundary.ThirdRelation.inducedH1_add_of_zero {X G : Type}
    [TopologicalSpace X] [PathConnectedSpace X] [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G] (f g : C(X, G)) (b : X) (hf : f b = 0) (hg : g b = 0) :
    FirstHurewicz.inducedHomology (f + g) =
      FirstHurewicz.inducedHomology f + FirstHurewicz.inducedHomology g := by
  apply LinearMap.ext
  intro a
  obtain ⟨p, rfl⟩ := FirstHurewicz.loopHomologyClass_surjective b a
  let pf : Path (0 : G) 0 := (p.map f.continuous).cast hf.symm hf.symm
  let pg : Path (0 : G) 0 := (p.map g.continuous).cast hg.symm hg.symm
  have h :
    p.map (f + g).continuous =
      (pf.add pg).cast (by simp only [ContinuousMap.add_apply, hf, hg])
        (by simp only [ContinuousMap.add_apply, hf, hg]) := by
    ext t
    rfl
  simp only [LinearMap.add_apply, FirstHurewicz.inducedHomology_loopHomologyClass]
  rw [h]
  exact loopHomologyClass_add_zero pf pg

private def PeriodFamily.Boundary.ThirdRelation.circleHeadMap (G : Type) [TopologicalSpace G]
    [AddCommGroup G] :
    C((PeriodTorusHigherHomology.CircleTopology.Circle),
      (PeriodTorusHigherHomology.CircleTopology.Circle) × G) :=
  (ContinuousMap.id (PeriodTorusHigherHomology.CircleTopology.Circle)).prodMk
    (ContinuousMap.const (PeriodTorusHigherHomology.CircleTopology.Circle) 0)

@[simp]
private theorem
    PeriodFamily.Boundary.ThirdRelation.circleHeadMap_zero (G : Type) [TopologicalSpace G]
    [AddCommGroup G] : circleHeadMap G 0 = 0 :=
  rfl

private theorem
    PeriodFamily.Boundary.ThirdRelation.productSection_add (G : Type) [TopologicalSpace G]
    [AddCommGroup G] (x y : G) :
    PeriodTorusHigherHomology.CircleTopology.productSection G (x + y) =
      PeriodTorusHigherHomology.CircleTopology.productSection G x +
        PeriodTorusHigherHomology.CircleTopology.productSection G y := by
  exact Prod.ext (zero_add 0).symm rfl

private def PeriodFamily.Boundary.ThirdRelation.verticalProductShear (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (v : C((PeriodTorusHigherHomology.CircleTopology.Circle), G)) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) × G,
      (PeriodTorusHigherHomology.CircleTopology.Circle) × G) :=
  ⟨fun p => (p.1, p.2 + v p.1),
    continuous_fst.prodMk (continuous_snd.add (v.continuous.comp continuous_fst))⟩

private def PeriodFamily.Boundary.ThirdRelation.verticalProductShearHomeomorph (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (v : C((PeriodTorusHigherHomology.CircleTopology.Circle), G)) :
    ((PeriodTorusHigherHomology.CircleTopology.Circle) × G) ≃ₜ
      ((PeriodTorusHigherHomology.CircleTopology.Circle) × G)
    where
  toFun := verticalProductShear G v
  invFun p := (p.1, p.2 - v p.1)
  left_inv p := Prod.ext rfl (add_sub_cancel_right p.2 (v p.1))
  right_inv p := Prod.ext rfl (sub_add_cancel p.2 (v p.1))
  continuous_toFun := (verticalProductShear G v).continuous
  continuous_invFun :=
    continuous_fst.prodMk (continuous_snd.sub (v.continuous.comp continuous_fst))

public
theorem
    PeriodFamily.Boundary.ThirdRelation.circleMorphism_zero (G : Type) [TopologicalSpace G]
    [AddCommGroup G] (v : C((PeriodTorusHigherHomology.CircleTopology.Circle), G))
    (hv : ∀ x y, v (x + y) = v x + v y) : v 0 = 0 := by
  have h : v 0 + v 0 = v 0 + 0 := by simpa only [zero_add, add_zero] using (hv 0 0).symm
  exact add_left_cancel h

private theorem PeriodFamily.Boundary.ThirdRelation.verticalProductShear_add (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (v : C((PeriodTorusHigherHomology.CircleTopology.Circle), G))
    (hv : ∀ x y, v (x + y) = v x + v y)
    (x y : (PeriodTorusHigherHomology.CircleTopology.Circle) × G) :
    verticalProductShear G v (x + y) = verticalProductShear G v x + verticalProductShear G v y := by
  apply Prod.ext
  · rfl
  · change x.2 + y.2 + v (x.1 + y.1) = (x.2 + v x.1) + (y.2 + v y.1)
    rw [hv]
    abel

private theorem PeriodFamily.Boundary.ThirdRelation.verticalProductShear_comp_section (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (v : C((PeriodTorusHigherHomology.CircleTopology.Circle), G))
    (hv : ∀ x y, v (x + y) = v x + v y) :
    (verticalProductShear G v).comp (PeriodTorusHigherHomology.CircleTopology.productSection G) =
      PeriodTorusHigherHomology.CircleTopology.productSection G := by
  ext x
  · rfl
  · change x + v 0 = x
    rw [circleMorphism_zero G v hv, add_zero]

private theorem PeriodFamily.Boundary.ThirdRelation.verticalProductShear_comp_head (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (v : C((PeriodTorusHigherHomology.CircleTopology.Circle), G)) :
    (verticalProductShear G v).comp (circleHeadMap G) =
      circleHeadMap G + (PeriodTorusHigherHomology.CircleTopology.productSection G).comp v := by
  ext c
  · exact (add_zero c).symm
  · rfl

private theorem PeriodFamily.Boundary.ThirdRelation.circleProduct_identity_eq_add (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] :
    ContinuousMap.id ((PeriodTorusHigherHomology.CircleTopology.Circle) × G) =
      (PeriodTorusHigherHomologyPontryagin.additionMap
            ((PeriodTorusHigherHomology.CircleTopology.Circle) × G)).comp
        ((circleHeadMap G).prodMap (PeriodTorusHigherHomology.CircleTopology.productSection G)) :=
  by
  apply ContinuousMap.ext
  rintro ⟨c, x⟩
  exact Prod.ext (add_zero c).symm (zero_add x).symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodFamily.Boundary.ThirdRelation.circleCross_eq_product (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology G n) :
    PeriodTorusHigherHomology.positiveCircleCross G n b =
      PeriodTorusHigherHomologyPontryagin.product
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × G) n
        (SingularMayerVietoris.singularHomologyMap (circleHeadMap G) 1
          (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop))
        (PeriodTorusHigherHomology.circleSectionHomology G n b) := by
  rw [PeriodTorusHigherHomologyPontryagin.product_apply]
  rw [←
    PeriodTorusHigherHomology.crossProductHomology_natural (circleHeadMap G)
      (PeriodTorusHigherHomology.CircleTopology.productSection G) n
      (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) b]
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    circleProduct_identity_eq_add, PeriodTorusHigherHomology.singularHomologyMap_id]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.verticalProductShear_headHomology (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (v : C((PeriodTorusHigherHomology.CircleTopology.Circle), G))
    (hv : ∀ x y, v (x + y) = v x + v y)
    (a :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.CircleTopology.Circle)
        1) :
    SingularMayerVietoris.singularHomologyMap (verticalProductShear G v) 1
        (SingularMayerVietoris.singularHomologyMap (circleHeadMap G) 1 a) =
      SingularMayerVietoris.singularHomologyMap (circleHeadMap G) 1 a +
        PeriodTorusHigherHomology.circleSectionHomology G 1
          (SingularMayerVietoris.singularHomologyMap v 1 a) := by
  have hzero :
    ((PeriodTorusHigherHomology.CircleTopology.productSection G).comp v)
        (0 : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      0 := by
    change (0, v 0) = (0, 0)
    rw [circleMorphism_zero G v hv]
  have hsum :
    SingularMayerVietoris.singularHomologyMap
        (circleHeadMap G + (PeriodTorusHigherHomology.CircleTopology.productSection G).comp v) 1 =
      SingularMayerVietoris.singularHomologyMap (circleHeadMap G) 1 +
        SingularMayerVietoris.singularHomologyMap
          ((PeriodTorusHigherHomology.CircleTopology.productSection G).comp v) 1 := by
    simpa only [SingularMayerVietoris.singularHomologyMap_one] using
      inducedH1_add_of_zero (circleHeadMap G)
        ((PeriodTorusHigherHomology.CircleTopology.productSection G).comp v)
        (0 : (PeriodTorusHigherHomology.CircleTopology.Circle)) (circleHeadMap_zero G) hzero
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    verticalProductShear_comp_head, hsum, LinearMap.add_apply,
    PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.verticalProductShear_sectionHomology (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (v : C((PeriodTorusHigherHomology.CircleTopology.Circle), G))
    (hv : ∀ x y, v (x + y) = v x + v y) (n : ℕ) (b : SingularMayerVietoris.SingularHomology G n) :
    SingularMayerVietoris.singularHomologyMap (verticalProductShear G v) n
        (PeriodTorusHigherHomology.circleSectionHomology G n b) =
      PeriodTorusHigherHomology.circleSectionHomology G n b := by
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    verticalProductShear_comp_section G v hv]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodFamily.Boundary.ThirdRelation.verticalProductShear_positiveCircleCross (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (v : C((PeriodTorusHigherHomology.CircleTopology.Circle), G))
    (hv : ∀ x y, v (x + y) = v x + v y) (n : ℕ) (b : SingularMayerVietoris.SingularHomology G n) :
    SingularMayerVietoris.singularHomologyMap (verticalProductShear G v) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross G n b) =
      PeriodTorusHigherHomology.positiveCircleCross G n b +
        PeriodTorusHigherHomology.circleSectionHomology G (n + 1)
          (PeriodTorusHigherHomologyPontryagin.product G n
            (SingularMayerVietoris.singularHomologyMap v 1
              (FirstHurewicz.loopHomologyClass
                PeriodTorusHigherHomology.CirclePaths.positiveLoop))
            b) := by
  rw [circleCross_eq_product,
    PeriodTorusHigherHomologyPontryagin.product_natural (verticalProductShear G v)
      (verticalProductShear_add G v hv),
    verticalProductShear_headHomology G v hv, verticalProductShear_sectionHomology G v hv,
    (PeriodTorusHigherHomologyPontryagin.product
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × G) n).map_add,
    LinearMap.add_apply]
  rw [← circleCross_eq_product]
  congr 1
  exact
    (PeriodTorusHigherHomologyPontryagin.product_natural
        (PeriodTorusHigherHomology.CircleTopology.productSection G) (productSection_add G) n
        (SingularMayerVietoris.singularHomologyMap v 1
          (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop))
        b).symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodFamily.Boundary.ThirdRelation.periodCircle (v : Lattice) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle), RealTorus₄) :=
  (PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm :
        C(PeriodTorusHigherHomology.ProductTorus 4, RealTorus₄)).comp
    (PeriodTorusHigherHomology.coordinateCircleMap v)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    PeriodFamily.Boundary.ThirdRelation.flatTorusCircleHomeomorph_periodCircle (v : Lattice)
    (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph (periodCircle v t) =
      PeriodTorusHigherHomology.coordinateCircleMap v t :=
  PeriodTorusHigherHomology.flatTorusCircleHomeomorph.apply_symm_apply _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.periodCircle_real_apply (v : Lattice) (t : ℝ) :
    periodCircle v (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      standardLattice.mkQ (t • Elliptic.realCast v) := by
  apply PeriodTorusHigherHomology.flatTorusCircleHomeomorph.injective
  rw [flatTorusCircleHomeomorph_periodCircle,
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph_mkQ]
  ext i
  change
    v i • (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      (((t * (v i : ℝ)) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
  rw [← AddCircle.coe_zsmul]
  congr 1
  simp only [zsmul_eq_mul, mul_comm]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodFamily.Boundary.ThirdRelation.periodCircle_zero (v : Lattice) :
    periodCircle v 0 = 0 := by
  apply PeriodTorusHigherHomology.flatTorusCircleHomeomorph.injective
  rw [flatTorusCircleHomeomorph_periodCircle, PeriodTorusHigherHomology.coordinateCircleMap_zero,
    PeriodFamily.FlatTorus.flatTorusCircleHomeomorph_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.periodCircle_add (v : Lattice)
    (s t : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    periodCircle v (s + t) = periodCircle v s + periodCircle v t := by
  apply PeriodTorusHigherHomology.flatTorusCircleHomeomorph.injective
  rw [flatTorusCircleHomeomorph_periodCircle,
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph_add,
    flatTorusCircleHomeomorph_periodCircle, flatTorusCircleHomeomorph_periodCircle,
    PeriodTorusHigherHomology.coordinateCircleMap_add]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.periodCircle_positiveLoop (v : Lattice) :
    PeriodTorusHigherHomology.CirclePaths.positiveLoop.map (periodCircle v).continuous =
      (PeriodFamily.FlatTorus.periodLoop v).cast (periodCircle_zero v) (periodCircle_zero v) := by
  apply Path.ext
  funext t
  change
    periodCircle v (PeriodTorusHigherHomology.CirclePaths.positiveLoop t) =
      PeriodFamily.FlatTorus.periodLoop v t
  rw [PeriodTorusHigherHomology.CirclePaths.positiveLoop_apply, periodCircle_real_apply,
    PeriodFamily.FlatTorus.periodLoop_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.periodCircle_positiveHomology (v : Lattice) :
    SingularMayerVietoris.singularHomologyMap (periodCircle v) 1
        (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) =
      PeriodFamily.FlatTorus.singularH1Equiv.symm v := by
  rw [SingularMayerVietoris.singularHomologyMap_one,
    FirstHurewicz.inducedHomology_loopHomologyClass, periodCircle_positiveLoop,
    PeriodFamily.FlatTorus.singularH1Equiv_symm_apply]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodFamily.Boundary.ThirdRelation.verticalShear (v : Lattice) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) × RealTorus₄,
      (PeriodTorusHigherHomology.CircleTopology.Circle) × RealTorus₄) :=
  verticalProductShear RealTorus₄ (periodCircle v)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodFamily.Boundary.ThirdRelation.verticalShearHomeomorph (v : Lattice) :
    ((PeriodTorusHigherHomology.CircleTopology.Circle) × RealTorus₄) ≃ₜ
      ((PeriodTorusHigherHomology.CircleTopology.Circle) × RealTorus₄) :=
  verticalProductShearHomeomorph RealTorus₄ (periodCircle v)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.verticalShear_positiveCircleCross (v : Lattice)
    (n : ℕ) (b : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap (verticalShear v) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n b) =
      PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n b +
        PeriodTorusHigherHomology.circleSectionHomology RealTorus₄ (n + 1)
          (PeriodTorusHigherHomologyPontryagin.product RealTorus₄ n
            (PeriodFamily.FlatTorus.singularH1Equiv.symm v) b) := by
  simpa only [verticalShear, periodCircle_positiveHomology] using
    verticalProductShear_positiveCircleCross RealTorus₄ (periodCircle v) (periodCircle_add v) n b

private def PeriodFamily.Boundary.ThirdRelation.coveredRegularMap (j : Elliptic.Kind) (τ : ℝ) :
    C((MappingTorus.Circle) × RealTorus₄,
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).Space) :=
  (PeriodFamily.Boundary.EllipticGaugeLinearization.linearRegularBoundaryMap j τ).comp
    (PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover j)

private def PeriodFamily.Boundary.ThirdRelation.untwistedRegularMap (j : Elliptic.Kind) (τ : ℝ) :
    C((MappingTorus.Circle) × RealTorus₄,
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).Space) :=
  (coveredRegularMap j τ).comp
    ((verticalShearHomeomorph j.twist).symm :
      C((MappingTorus.Circle) × RealTorus₄, (MappingTorus.Circle) × RealTorus₄))

private theorem
    PeriodFamily.Boundary.ThirdRelation.untwistedRegularMap_real_apply (j : Elliptic.Kind)
    (τ t : ℝ) (x : RealTorus₄) :
    untwistedRegularMap j τ ((t : (MappingTorus.Circle)), x) =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (PeriodFamily.Boundary.nativeShiftedBase j τ (t * j.order), x) := by
  change
    PeriodFamily.Boundary.EllipticGaugeLinearization.linearRegularBoundaryMap j τ
        (PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover j
          ((t : (MappingTorus.Circle)), x - periodCircle j.twist (t : (MappingTorus.Circle)))) =
      _
  rw [PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover_real_apply,
    PeriodFamily.Boundary.EllipticGaugeLinearization.linearRegularBoundaryMap_mk,
    periodCircle_real_apply]
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast j.order_pos.ne'
  rw [mul_div_cancel_right₀ _ hm, sub_add_cancel]

private theorem
    PeriodFamily.Boundary.ThirdRelation.untwistedRegularMap_comp_shear (j : Elliptic.Kind)
    (τ : ℝ) : (untwistedRegularMap j τ).comp (verticalShear j.twist) = coveredRegularMap j τ := by
  apply ContinuousMap.ext
  intro p
  change
    coveredRegularMap j τ
        ((verticalShearHomeomorph j.twist).symm (verticalShearHomeomorph j.twist p)) =
      _
  rw [Homeomorph.symm_apply_apply]

private theorem PeriodFamily.Boundary.ThirdRelation.familyNegation_comp_untwistedRegularMap
    (j : Elliptic.Kind) (τ : ℝ) :
    (familyNegation
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).comp
        (untwistedRegularMap j τ) =
      (untwistedRegularMap j τ).comp (PeriodTorusHigherHomology.circleProductMap flatNegation) := by
  apply ContinuousMap.ext
  rintro ⟨c, x⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective c
  change
    familyNegation
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        (untwistedRegularMap j τ ((t : (MappingTorus.Circle)), x)) =
      untwistedRegularMap j τ ((t : (MappingTorus.Circle)), -x)
  rw [untwistedRegularMap_real_apply, familyNegation_quotient, untwistedRegularMap_real_apply]

private theorem PeriodFamily.Boundary.ThirdRelation.untwistedRegularMap_positiveCircleCross_negation
    (j : Elliptic.Kind) (τ : ℝ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    SingularMayerVietoris.singularHomologyMap
        (familyNegation
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂))
        3
        (SingularMayerVietoris.singularHomologyMap (untwistedRegularMap j τ) 3
          (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 2 a)) =
      SingularMayerVietoris.singularHomologyMap (untwistedRegularMap j τ) 3
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 2 a) := by
  have h :=
    congrArg
      (fun f :
          C((MappingTorus.Circle) × RealTorus₄,
            ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)).Space) =>
        SingularMayerVietoris.singularHomologyMap f 3)
      (familyNegation_comp_untwistedRegularMap j τ)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  have ha := LinearMap.congr_fun h (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 2 a)
  simpa only [LinearMap.comp_apply, PeriodTorusHigherHomology.positiveCircleCross_naturality,
    flatNegation_homology_two] using ha

private theorem PeriodFamily.Boundary.ThirdRelation.untwistedRegularMap_comp_circleSection
    (j : Elliptic.Kind) (τ : ℝ) :
    (untwistedRegularMap j τ).comp
        (PeriodTorusHigherHomology.CircleTopology.productSection RealTorus₄) =
      PeriodFamily.Homology.pointFamilyFibreInclusion
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        (PeriodFamily.Boundary.nativeShiftedBase j τ 0) := by
  apply ContinuousMap.ext
  intro x
  change
    untwistedRegularMap j τ (0, x) =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (PeriodFamily.Boundary.nativeShiftedBase j τ 0, x)
  have h := untwistedRegularMap_real_apply j τ 0 x
  simpa only [AddCircle.coe_zero, MulZeroClass.zero_mul] using h

private theorem PeriodFamily.Boundary.ThirdRelation.untwistedRegularMap_circleSection_homology
    (j : Elliptic.Kind) (τ : ℝ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap (untwistedRegularMap j τ) n
        (PeriodTorusHigherHomology.circleSectionHomology RealTorus₄ n a) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.familyFibreInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          PeriodFamily.Homology.normalizedSlitBaseLift)
        n a := by
  have h :=
    congrArg
      (fun f :
          C(RealTorus₄,
            ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)).Space) =>
        SingularMayerVietoris.singularHomologyMap f n)
      (untwistedRegularMap_comp_circleSection j τ)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodFamily.Homology.pointFamilyFibreInclusion_homology_eq_normalized] at h
  exact LinearMap.congr_fun h a

private theorem PeriodFamily.Boundary.ThirdRelation.coveredRegularMap_positiveCircleCross
    (j : Elliptic.Kind) (τ : ℝ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap (coveredRegularMap j τ) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n a) =
      SingularMayerVietoris.singularHomologyMap (untwistedRegularMap j τ) (n + 1)
          (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n a) +
        SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            PeriodFamily.Homology.normalizedSlitBaseLift)
          (n + 1)
          (PeriodTorusHigherHomologyPontryagin.product RealTorus₄ n
            (PeriodFamily.FlatTorus.singularH1Equiv.symm j.twist) a) := by
  have h :=
    congrArg
      (fun f :
          C((MappingTorus.Circle) × RealTorus₄,
            ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)).Space) =>
        SingularMayerVietoris.singularHomologyMap f (n + 1))
      (untwistedRegularMap_comp_shear j τ)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  have ha := LinearMap.congr_fun h (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n a)
  simpa only [LinearMap.comp_apply, verticalShear_positiveCircleCross, map_add,
    untwistedRegularMap_circleSection_homology] using ha.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.flat_tripleProduct_exterior (a b c : Lattice) :
    PeriodFamily.FlatTorus.singularH3Equiv
        (PeriodTorusHigherHomologyPontryagin.tripleProduct RealTorus₄
          (PeriodFamily.FlatTorus.singularH1Equiv.symm a)
          (PeriodFamily.FlatTorus.singularH1Equiv.symm b)
          (PeriodFamily.FlatTorus.singularH1Equiv.symm c)) =
      exteriorPower.ιMulti ℤ 3 ![a, b, c] := by
  rw [PeriodFamily.FlatTorus.singularH3Equiv_apply,
    PeriodTorusHigherHomologyPontryagin.tripleProduct_natural _
      PeriodTorusHigherHomology.flatTorusCircleHomeomorph_add,
    PeriodFamily.FlatTorus.coordinateH1_flatMarking,
    PeriodFamily.FlatTorus.coordinateH1_flatMarking,
    PeriodFamily.FlatTorus.coordinateH1_flatMarking]
  calc
    _ =
        PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
          (PeriodTorusHigherHomology.coordinateTorusWedgeThree
            (exteriorPower.ιMulti ℤ 3 ![a, b, c])) :=
      congrArg PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
        (PeriodTorusHigherHomology.coordinateTorusWedgeThree_apply_ιMulti ![a, b, c]).symm
    _ = _ := PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_wedge _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.flat_triple_uw_coordinates (a : Lattice) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (PeriodTorusHigherHomologyPontryagin.tripleProduct RealTorus₄
          (PeriodFamily.FlatTorus.singularH1Equiv.symm a)
          (PeriodFamily.FlatTorus.singularH1Equiv.symm (Pi.single 1 1))
          (PeriodFamily.FlatTorus.singularH1Equiv.symm (Pi.single 2 1))) =
      ![a 0, 0, 0, a 3] := by
  rw [PeriodFamily.FlatTorus.singularH3Coordinates_apply, flat_tripleProduct_exterior]
  funext i
  rw [PeriodTorusHigherHomologyExterior.cubeCoordinates_apply,
    PeriodTorusHigherHomologyExterior.cubeBasis, Module.Basis.repr_reindex_apply]
  change
    ((Pi.basisFun ℤ (Fin 4)).exteriorPower 3).repr
        (exteriorPower.ιMulti ℤ 3 ![a, Pi.single 1 1, Pi.single 2 1])
        (PeriodTorusHigherHomologyExterior.tripleSubset i) =
      _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [PeriodTorusHigherHomologyExterior.tripleSubset_ordered, Module.Basis.coord_apply,
    Pi.basisFun_repr]
  fin_cases i <;> simp [LocalSystemMatrices.tripleIndices, Matrix.det_fin_three]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodFamily.Boundary.ThirdRelation.gammaUWClass :
    SingularMayerVietoris.SingularHomology RealTorus₄ 3 :=
  PeriodFamily.FlatTorus.singularH3Coordinates.symm ![1, 0, 0, 0]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.gammaUWClass_coordinates :
    PeriodFamily.FlatTorus.singularH3Coordinates gammaUWClass = ![1, 0, 0, 0] :=
  PeriodFamily.FlatTorus.singularH3Coordinates.apply_symm_apply _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodFamily.Boundary.ThirdRelation.splitFibreClassTwo_eq_product (j : Elliptic.Kind) :
    PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo j =
      PeriodTorusHigherHomologyPontryagin.product11 RealTorus₄
        (PeriodFamily.FlatTorus.singularH1Equiv.symm (Pi.single 1 1))
        (PeriodFamily.FlatTorus.singularH1Equiv.symm (Pi.single 2 1)) := by
  apply PeriodFamily.FlatTorus.singularH2Coordinates.injective
  rw [PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo_coordinates,
    ThreefoldHomology.DeltaSweep.flat_product11_coordinates]
  simp

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodFamily.Boundary.ThirdRelation.splitCircleClassTwo_eq_product (j : Elliptic.Kind) :
    PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo j =
      PeriodTorusHigherHomologyPontryagin.product11 RealTorus₄
        (PeriodFamily.FlatTorus.singularH1Equiv.symm j.twist)
        (PeriodFamily.FlatTorus.singularH1Equiv.symm (Pi.single 2 1)) := by
  apply PeriodFamily.FlatTorus.singularH2Coordinates.injective
  rw [PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo_coordinates,
    ThreefoldHomology.DeltaSweep.flat_product11_coordinates]
  cases j <;> simp [Elliptic.Kind.twist, ε, ε']

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.twist_product_splitFibre (j : Elliptic.Kind) :
    PeriodTorusHigherHomologyPontryagin.product RealTorus₄ 2
        (PeriodFamily.FlatTorus.singularH1Equiv.symm j.twist)
        (PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo j) =
      j.twist 0 • gammaUWClass := by
  rw [splitFibreClassTwo_eq_product]
  apply PeriodFamily.FlatTorus.singularH3Coordinates.injective
  change
    PeriodFamily.FlatTorus.singularH3Coordinates
        (PeriodTorusHigherHomologyPontryagin.tripleProduct RealTorus₄
          (PeriodFamily.FlatTorus.singularH1Equiv.symm j.twist)
          (PeriodFamily.FlatTorus.singularH1Equiv.symm (Pi.single 1 1))
          (PeriodFamily.FlatTorus.singularH1Equiv.symm (Pi.single 2 1))) =
      _
  rw [flat_triple_uw_coordinates, map_zsmul, gammaUWClass_coordinates]
  cases j <;> ext i <;> fin_cases i <;> simp [Elliptic.Kind.twist, ε, ε']

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.twist_product_splitCircle (j : Elliptic.Kind) :
    PeriodTorusHigherHomologyPontryagin.product RealTorus₄ 2
        (PeriodFamily.FlatTorus.singularH1Equiv.symm j.twist)
        (PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo j) =
      0 := by
  rw [splitCircleClassTwo_eq_product]
  have := PeriodTorusHigherHomology.realTorus_homology_torsionFree 2
  exact PeriodTorusHigherHomologyPontryagin.tripleProduct_self01 RealTorus₄ _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.three_shear_correction :
    PeriodTorusHigherHomologyPontryagin.product RealTorus₄ 2
        (PeriodFamily.FlatTorus.singularH1Equiv.symm Elliptic.Kind.three.twist)
        (4 • PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo .three +
          2 • PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo .three) =
      (4 : ℤ) • gammaUWClass := by
  rw [map_add, map_nsmul, map_nsmul, twist_product_splitFibre, twist_product_splitCircle]
  simp [Elliptic.Kind.twist, ε, ofNat_zsmul]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.Boundary.ThirdRelation.four_shear_correction :
    PeriodTorusHigherHomologyPontryagin.product RealTorus₄ 2
        (PeriodFamily.FlatTorus.singularH1Equiv.symm Elliptic.Kind.four.twist)
        (3 • PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo .four -
          PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo .four) =
      (-3 : ℤ) • gammaUWClass := by
  rw [map_sub, map_nsmul, twist_product_splitFibre, twist_product_splitCircle]
  simp [Elliptic.Kind.twist, ε', ofNat_zsmul]

private def PeriodFamily.Boundary.ThirdRelation.referenceCoverInput :
    Elliptic.Kind → SingularMayerVietoris.SingularHomology RealTorus₄ 2
  | .three =>
    4 • PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo .three +
      2 • PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo .three
  | .four =>
    3 • PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo .four -
      PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo .four

private theorem
    PeriodFamily.Boundary.ThirdRelation.referenceClasses_elliptic_cover (j : Elliptic.Kind) :
    (ThreefoldHomology.ThirdDegree.referenceClasses (Option.some j)).val =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover j) 3
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 2 (referenceCoverInput j)) := by
  cases j
  · change
      ((PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv .three 2).symm _).val = _
    rw [PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv_symm_val]
    simpa only [referenceCoverInput, ofNat_zsmul] using! capCircle_three_reference
  · change
      ((PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv .four 2).symm _).val = _
    rw [PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv_symm_val]
    simpa only [referenceCoverInput, ofNat_zsmul] using! capCircle_four_reference

private theorem PeriodFamily.Boundary.ThirdRelation.referenceClasses_elliptic_regular_cover
    (j : Elliptic.Kind) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) 3
        (ThreefoldHomology.ThirdDegree.referenceClasses (Option.some j)).val =
      SingularMayerVietoris.singularHomologyMap (coveredRegularMap j 0) 3
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 2 (referenceCoverInput j)) := by
  rw [referenceClasses_elliptic_cover,
    PeriodFamily.Boundary.EllipticGaugeLinearization.boundaryRegularHomologyMap_linear j 0 3]
  exact
    (LinearMap.congr_fun
        (PeriodTorusHigherHomology.singularHomologyMap_comp
          (PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover j)
          (PeriodFamily.Boundary.EllipticGaugeLinearization.linearRegularBoundaryMap j 0) 3)
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 2 (referenceCoverInput j))).symm

private def PeriodFamily.Boundary.ThirdRelation.ellipticHorizontal (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).Space
      3 :=
  SingularMayerVietoris.singularHomologyMap (untwistedRegularMap j 0) 3
    (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 2 (referenceCoverInput j))

private theorem
    PeriodFamily.Boundary.ThirdRelation.ellipticHorizontal_negation (j : Elliptic.Kind) :
    SingularMayerVietoris.singularHomologyMap
        (familyNegation
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂))
        3 (ellipticHorizontal j) =
      ellipticHorizontal j :=
  untwistedRegularMap_positiveCircleCross_negation j 0 (referenceCoverInput j)

private def PeriodFamily.Boundary.ThirdRelation.regularGammaUW :
    SingularMayerVietoris.SingularHomology
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).Space
      3 :=
  SingularMayerVietoris.singularHomologyMap
    (PeriodFamily.Homology.familyFibreInclusion
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
      PeriodFamily.Homology.normalizedSlitBaseLift)
    3 gammaUWClass

private theorem PeriodFamily.Boundary.ThirdRelation.referenceClasses_three_regular :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some .three) 3
        (ThreefoldHomology.ThirdDegree.referenceClasses (Option.some .three)).val =
      ellipticHorizontal .three + (4 : ℤ) • regularGammaUW := by
  rw [referenceClasses_elliptic_regular_cover, coveredRegularMap_positiveCircleCross]
  change
    ellipticHorizontal .three +
        SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            PeriodFamily.Homology.normalizedSlitBaseLift)
          3
          (PeriodTorusHigherHomologyPontryagin.product RealTorus₄ 2
            (PeriodFamily.FlatTorus.singularH1Equiv.symm Elliptic.Kind.three.twist)
            (referenceCoverInput .three)) =
      _
  rw [referenceCoverInput, three_shear_correction, map_zsmul]
  rfl

private theorem PeriodFamily.Boundary.ThirdRelation.referenceClasses_four_regular :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some .four) 3
        (ThreefoldHomology.ThirdDegree.referenceClasses (Option.some .four)).val =
      ellipticHorizontal .four + (-3 : ℤ) • regularGammaUW := by
  rw [referenceClasses_elliptic_regular_cover, coveredRegularMap_positiveCircleCross]
  change
    ellipticHorizontal .four +
        SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            PeriodFamily.Homology.normalizedSlitBaseLift)
          3
          (PeriodTorusHigherHomologyPontryagin.product RealTorus₄ 2
            (PeriodFamily.FlatTorus.singularH1Equiv.symm Elliptic.Kind.four.twist)
            (referenceCoverInput .four)) =
      _
  rw [referenceCoverInput, four_shear_correction, map_zsmul]
  rfl

private theorem PeriodFamily.Boundary.ThirdRelation.negation_fixed_source_zero
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (a : SingularMayerVietoris.SingularHomology D.Space 3)
    (hneg : SingularMayerVietoris.singularHomologyMap (familyNegation D) 3 a = a)
    (hsource : PeriodFamily.Homology.sourceKernelProjection D 2 a = 0) : a = 0 := by
  have ha :
    a ∈
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion D
            PeriodFamily.Homology.normalizedSlitBaseLift)
          3) := by
    rw [← PeriodFamily.Homology.sourceKernelProjection_kernel D 2]
    exact hsource
  obtain ⟨b, hb⟩ := ha
  have hminus : SingularMayerVietoris.singularHomologyMap (familyNegation D) 3 a = -a := by
    rw [← hb]
    exact familyNegation_homology_fibre_three D PeriodFamily.Homology.normalizedSlitBaseLift b
  have heq : a = -a := hneg.symm.trans hminus
  apply (PeriodFamily.Homology.familyH3Equiv D).injective
  rw [map_zero]
  ext i
  have hi := congrArg (fun x => PeriodFamily.Homology.familyH3Equiv D x i) heq
  simp only [map_neg, Pi.neg_apply] at hi
  change PeriodFamily.Homology.familyH3Equiv D a i = 0
  omega

private theorem PeriodFamily.Boundary.ThirdRelation.regularGammaUW_eq_thirdFibreCyclicMap :
    regularGammaUW = ThreefoldHomology.ThirdDegree.thirdFibreCyclicMap 1 := by
  rw [ThreefoldHomology.ThirdDegree.thirdFibreCyclicMap_apply]
  rfl

private theorem PeriodFamily.Boundary.ThirdRelation.regularGammaUW_source_eq_zero :
    PeriodFamily.Homology.sourceKernelProjection
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        2 regularGammaUW =
      0 := by
  rw [regularGammaUW_eq_thirdFibreCyclicMap]
  exact ThreefoldHomology.ThirdDegree.thirdFibreCyclicMap_source_eq_zero 1

private def PeriodFamily.Boundary.ThirdRelation.horizontalRemainder :
    SingularMayerVietoris.SingularHomology
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).Space
      3 :=
  ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 3
        (ThreefoldHomology.ThirdDegree.referenceClasses Option.none).val +
      ellipticHorizontal .three +
    ellipticHorizontal .four

private theorem PeriodFamily.Boundary.ThirdRelation.referenceClasses_regular_split :
    ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3
        ThreefoldHomology.ThirdDegree.referenceClasses =
      horizontalRemainder + regularGammaUW := by
  classical
  rw [ThreefoldHomology.CapElimination.nativeCapKernelRegularMap_apply, Fintype.sum_option]
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four),
    referenceClasses_three_regular, referenceClasses_four_regular]
  unfold horizontalRemainder
  abel

private theorem PeriodFamily.Boundary.ThirdRelation.horizontalRemainder_source_eq_zero :
    PeriodFamily.Homology.sourceKernelProjection
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        2 horizontalRemainder =
      0 := by
  have h := ThreefoldHomology.ThirdDegree.referenceClasses_source_eq_zero
  change
    PeriodFamily.Homology.sourceKernelProjection
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        2
        (ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3
          ThreefoldHomology.ThirdDegree.referenceClasses) =
      0 at h
  rw [referenceClasses_regular_split, map_add, regularGammaUW_source_eq_zero, add_zero] at h
  exact h

private theorem PeriodFamily.Boundary.ThirdRelation.horizontalRemainder_negation
    (hC :
      SingularMayerVietoris.singularHomologyMap
          (familyNegation
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂))
          3
          (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 3
            (ThreefoldHomology.ThirdDegree.referenceClasses Option.none).val) =
        ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 3
          (ThreefoldHomology.ThirdDegree.referenceClasses Option.none).val) :
    SingularMayerVietoris.singularHomologyMap
        (familyNegation
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂))
        3 horizontalRemainder =
      horizontalRemainder := by
  unfold horizontalRemainder
  rw [map_add, map_add, hC, ellipticHorizontal_negation, ellipticHorizontal_negation]

private theorem PeriodFamily.Boundary.ThirdRelation.referenceClasses_regular_of_cusp_negation
    (hC :
      SingularMayerVietoris.singularHomologyMap
          (familyNegation
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂))
          3
          (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 3
            (ThreefoldHomology.ThirdDegree.referenceClasses Option.none).val) =
        ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 3
          (ThreefoldHomology.ThirdDegree.referenceClasses Option.none).val) :
    ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3
        ThreefoldHomology.ThirdDegree.referenceClasses =
      ThreefoldHomology.ThirdDegree.thirdFibreCyclicMap 1 := by
  have hzero : horizontalRemainder = 0 :=
    negation_fixed_source_zero
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
      horizontalRemainder (horizontalRemainder_negation hC) horizontalRemainder_source_eq_zero
  rw [referenceClasses_regular_split, hzero, zero_add, regularGammaUW_eq_thirdFibreCyclicMap]

private theorem PeriodFamily.Boundary.ThirdRelation.cuspMonodromy_negation_mo1973_30380
    (x : RealTorus₄) :
    flatNegation (ThreefoldOverlapMappingTorus.monodromy Option.none x) =
      ThreefoldOverlapMappingTorus.monodromy Option.none (flatNegation x) := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  change
    -SpecialPeriods.CuspFamily.cuspTorusHomeomorph 1 (standardLattice.mkQ v) =
      SpecialPeriods.CuspFamily.cuspTorusHomeomorph 1 (-standardLattice.mkQ v)
  rw [← map_neg standardLattice.mkQ v, SpecialPeriods.CuspFamily.cuspTorusHomeomorph_mkQ,
    SpecialPeriods.CuspFamily.cuspTorusHomeomorph_mkQ, map_neg, map_neg]

private theorem PeriodFamily.Boundary.ThirdRelation.cuspNegation_eq_mappingTorusMap
    (N :
      C(ThreefoldOverlapMappingTorus.Boundary Option.none,
        ThreefoldOverlapMappingTorus.Boundary Option.none))
    (hN :
      ∀ (t : ℝ) (x : RealTorus₄),
        N (MappingTorus.mk (ThreefoldOverlapMappingTorus.monodromy Option.none) (t, x)) =
          MappingTorus.mk (ThreefoldOverlapMappingTorus.monodromy Option.none) (t, -x)) :
    N =
      CuspBoundaryGammaZero.mappingTorusMap (ThreefoldOverlapMappingTorus.monodromy Option.none)
        (ThreefoldOverlapMappingTorus.monodromy Option.none) flatNegation
        cuspMonodromy_negation_mo1973_30380 := by
  apply ContinuousMap.ext
  intro p
  obtain ⟨⟨t, x⟩, rfl⟩ :=
    MappingTorus.mk_surjective (ThreefoldOverlapMappingTorus.monodromy Option.none) p
  exact hN t x

private theorem PeriodFamily.Boundary.ThirdRelation.cuspNegation_wang
    (N :
      C(ThreefoldOverlapMappingTorus.Boundary Option.none,
        ThreefoldOverlapMappingTorus.Boundary Option.none))
    (hN :
      ∀ (t : ℝ) (x : RealTorus₄),
        N (MappingTorus.mk (ThreefoldOverlapMappingTorus.monodromy Option.none) (t, x)) =
          MappingTorus.mk (ThreefoldOverlapMappingTorus.monodromy Option.none) (t, -x))
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary Option.none)
        (n + 1)) :
    MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy Option.none) n
        (SingularMayerVietoris.singularHomologyMap N (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap flatNegation n
        (MappingTorusHomology.wangBoundary (ThreefoldOverlapMappingTorus.monodromy Option.none) n
          a) := by
  rw [cuspNegation_eq_mappingTorusMap N hN]
  exact
    CuspBoundaryGammaZero.wangBoundary_mappingTorusMap
      (ThreefoldOverlapMappingTorus.monodromy Option.none)
      (ThreefoldOverlapMappingTorus.monodromy Option.none) flatNegation
      cuspMonodromy_negation_mo1973_30380 n a

private theorem PeriodFamily.Boundary.ThirdRelation.cuspNegation_regular_comp
    (N :
      C(ThreefoldOverlapMappingTorus.Boundary Option.none,
        ThreefoldOverlapMappingTorus.Boundary Option.none))
    (hN :
      ∀ (t : ℝ) (x : RealTorus₄),
        N (MappingTorus.mk (ThreefoldOverlapMappingTorus.monodromy Option.none) (t, x)) =
          MappingTorus.mk (ThreefoldOverlapMappingTorus.monodromy Option.none) (t, -x)) :
    (familyNegation
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).comp
        (ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none) =
      (ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none).comp N := by
  apply ContinuousMap.ext
  intro p
  obtain ⟨⟨t, x⟩, rfl⟩ :=
    MappingTorus.mk_surjective (ThreefoldOverlapMappingTorus.monodromy Option.none) p
  change
    familyNegation
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        (ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none
          (MappingTorus.mk (ThreefoldOverlapMappingTorus.monodromy Option.none) (t, x))) =
      ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none
        (N (MappingTorus.mk (ThreefoldOverlapMappingTorus.monodromy Option.none) (t, x)))
  rw [hN]
  change
    familyNegation
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        (ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none
          (MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, x))) =
      ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none
        (MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, -x))
  rw [ThreefoldOverlapMappingTorus.Cusp.boundaryToRegularFamily_cusp_mk,
    ThreefoldOverlapMappingTorus.Cusp.boundaryToRegularFamily_cusp_mk]
  rfl

private theorem PeriodFamily.Boundary.ThirdRelation.cuspNegation_cap_zero
    (N :
      C(ThreefoldOverlapMappingTorus.Boundary Option.none,
        ThreefoldOverlapMappingTorus.Boundary Option.none))
    (J :
      C(SpecialPeriods.Threefold.localPiece (Option.some Option.none),
        SpecialPeriods.Threefold.localPiece (Option.some Option.none)))
    (hJ :
      (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none).comp N =
        J.comp (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none))
    (a :
      SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary Option.none)
        3)
    (ha : ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 3 a = 0) :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 3
        (SingularMayerVietoris.singularHomologyMap N 3 a) =
      0 := by
  have h :=
    congrArg
      (fun f :
          C(ThreefoldOverlapMappingTorus.Boundary Option.none,
            SpecialPeriods.Threefold.localPiece (Option.some Option.none)) =>
        SingularMayerVietoris.singularHomologyMap f 3)
      hJ
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  have he := LinearMap.congr_fun h a
  change
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 3
        (SingularMayerVietoris.singularHomologyMap N 3 a) =
      SingularMayerVietoris.singularHomologyMap J 3
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 3 a) at he
  rw [he, ha, map_zero]

private theorem PeriodFamily.Boundary.ThirdRelation.cuspNegation_capKernel_fixed
    (N :
      C(ThreefoldOverlapMappingTorus.Boundary Option.none,
        ThreefoldOverlapMappingTorus.Boundary Option.none))
    (hN :
      ∀ (t : ℝ) (x : RealTorus₄),
        N (MappingTorus.mk (ThreefoldOverlapMappingTorus.monodromy Option.none) (t, x)) =
          MappingTorus.mk (ThreefoldOverlapMappingTorus.monodromy Option.none) (t, -x))
    (J :
      C(SpecialPeriods.Threefold.localPiece (Option.some Option.none),
        SpecialPeriods.Threefold.localPiece (Option.some Option.none)))
    (hJ :
      (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none).comp N =
        J.comp (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none))
    (a : LinearMap.ker (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 3)) :
    SingularMayerVietoris.singularHomologyMap N 3 a.val = a.val := by
  apply ThreefoldHomologyCuspFibre.cuspCap_wang_ext 2
  · exact (cuspNegation_cap_zero N J hJ a.val a.property).trans a.property.symm
  · rw [cuspNegation_wang N hN, flatNegation_homology_two]

private theorem PeriodFamily.Boundary.ThirdRelation.cuspNegation_capKernel_regular_fixed
    (N :
      C(ThreefoldOverlapMappingTorus.Boundary Option.none,
        ThreefoldOverlapMappingTorus.Boundary Option.none))
    (hN :
      ∀ (t : ℝ) (x : RealTorus₄),
        N (MappingTorus.mk (ThreefoldOverlapMappingTorus.monodromy Option.none) (t, x)) =
          MappingTorus.mk (ThreefoldOverlapMappingTorus.monodromy Option.none) (t, -x))
    (J :
      C(SpecialPeriods.Threefold.localPiece (Option.some Option.none),
        SpecialPeriods.Threefold.localPiece (Option.some Option.none)))
    (hJ :
      (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none).comp N =
        J.comp (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none))
    (a : LinearMap.ker (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 3)) :
    SingularMayerVietoris.singularHomologyMap
        (familyNegation
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂))
        3 (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 3 a.val) =
      ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 3 a.val := by
  have h :=
    congrArg
      (fun f :
          C(ThreefoldOverlapMappingTorus.Boundary Option.none,
            ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)).Space) =>
        SingularMayerVietoris.singularHomologyMap f 3)
      (cuspNegation_regular_comp N hN)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  have he := LinearMap.congr_fun h a.val
  change
    SingularMayerVietoris.singularHomologyMap
        (familyNegation
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂))
        3 (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 3 a.val) =
      ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 3
        (SingularMayerVietoris.singularHomologyMap N 3 a.val) at he
  rw [he, cuspNegation_capKernel_fixed N hN J hJ]

end Mathoverflow1973

end
