/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology3
public import LeanPool.HopfProblem.Recognition.Smale11
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Elliptic.Core1
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
import all LeanPool.HopfProblem.Threefold.SpecialPeriods9
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology2
import all LeanPool.HopfProblem.PeriodFamily.Core3
import all LeanPool.HopfProblem.PeriodFamily.Core4
import all LeanPool.HopfProblem.PeriodFamily.Core5
import all LeanPool.HopfProblem.Elliptic.Core7
import all LeanPool.HopfProblem.PeriodFamily.Core6
import all LeanPool.HopfProblem.PeriodFamily.Core7
import all LeanPool.HopfProblem.Recognition.Smale11
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology3

/-!
# Hopf problem: period family · core 8

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
    PeriodFamily.Boundary.EllipticTopFibre.centralRealCover_h4_coordinates (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    Elliptic.HigherHomology.surfaceH4Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldHomology.EllipticFibre.centralRealCover j) 4 a) =
      (j.order : ℤ) * γ j.twist * PeriodTorusHigherHomology.realTorusH4Equiv a := by
  rw [ThreefoldHomology.EllipticFibre.centralRealCover,
    PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply]
  change
    Elliptic.HigherHomology.surfacePeriodCoverH4Coordinates j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (Elliptic.flatTorusPeriodHomeomorph
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val)
          4 a) =
      _
  rw [Elliptic.HigherHomology.surfacePeriodCoverH4Coordinates_apply,
    surfacePeriodCoverCircleBoundary_flat]
  ring

private theorem
    PeriodFamily.Boundary.EllipticTopFibre.fibreToFilling_h4_coordinates (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    Elliptic.HigherHomology.surfaceH4Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j 4
          (SingularMayerVietoris.singularHomologyMap
            (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) 4 a)) =
      (j.order : ℤ) * γ j.twist * PeriodTorusHigherHomology.realTorusH4Equiv a := by
  have h :=
    LinearMap.congr_fun (ThreefoldHomology.EllipticFibre.fibreToFilling_homology_retraction j 4) a
  change
    ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j 4
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) 4 a) =
      SingularMayerVietoris.singularHomologyMap
        (Elliptic.HigherHomology.periodCover j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
          (Elliptic.mainTwist_admissible j))
        4 (ThreefoldHomology.EllipticFibre.centralPeriodHomologyEquiv j 4 a) at h
  refine
    (congrArg
          (Elliptic.HigherHomology.surfaceH4Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod)
          h).trans
      ?_
  have hc := centralRealCover_h4_coordinates j a
  rw [ThreefoldHomology.EllipticFibre.centralRealCover,
    PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply] at hc
  exact hc

private theorem PeriodFamily.Boundary.EllipticTopFibre.boundaryFilling_fibre_h4_coordinates
    (j : Elliptic.Kind) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    Elliptic.HigherHomology.surfaceH4Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j 4
          (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4
            (MappingTorusHomology.fibreHomologyMap
              (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 4 a))) =
      (j.order : ℤ) * γ j.twist * PeriodTorusHigherHomology.realTorusH4Equiv a := by
  have h :=
    LinearMap.congr_fun
      (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_fibre (Option.some j) 4) a
  change
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4
        (MappingTorusHomology.fibreHomologyMap
          (ThreefoldOverlapMappingTorus.monodromy (Option.some j)) 4 a) =
      SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.fibreToFilling (Option.some j)) 4 a at h
  exact
    (congrArg
          (fun b =>
            Elliptic.HigherHomology.surfaceH4Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
              (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j 4 b))
          h).trans
      (fibreToFilling_h4_coordinates j a)

private def PeriodFamily.GammaZero.fibreGamma : C(RealTorus₄, AddCircle (1 : ℝ)) :=
  ⟨fun x => PeriodTorusHigherHomology.flatTorusCircleHomeomorph x 0,
    (continuous_apply 0).comp PeriodTorusHigherHomology.flatTorusCircleHomeomorph.continuous⟩

private theorem PeriodFamily.GammaZero.fibreGamma_mkQ (x : RealPlane₄) :
    fibreGamma (standardLattice.mkQ x) = (x 0 : AddCircle (1 : ℝ)) := by
  change PeriodTorusHigherHomology.flatTorusCircleHomeomorph (standardLattice.mkQ x) 0 = _
  rw [PeriodTorusHigherHomology.flatTorusCircleHomeomorph_mkQ]
  rfl

private abbrev PeriodFamily.GammaZero.Fibre :=
  { x : RealTorus₄ // fibreGamma x = 0 }

private def PeriodFamily.GammaZero.fibreInclusion : C(Fibre, RealTorus₄) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def
    PeriodFamily.GammaZero.fibreHomeomorph : Fibre ≃ₜ PeriodTorusHigherHomology.ProductTorus 3
    where
  toFun x i := PeriodTorusHigherHomology.flatTorusCircleHomeomorph x.val i.succ
  invFun
    y :=
    ⟨PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm (Fin.cons 0 y),
      by
      change
        PeriodTorusHigherHomology.flatTorusCircleHomeomorph
            (PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm (Fin.cons 0 y)) 0 =
          0
      rw [Homeomorph.apply_symm_apply]
      rfl⟩
  left_inv
    x := by
    apply Subtype.ext
    apply PeriodTorusHigherHomology.flatTorusCircleHomeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact x.property.symm
    · rfl
  right_inv
    y := by
    funext i
    exact
      congrFun
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph.apply_symm_apply (Fin.cons 0 y))
        i.succ
  continuous_toFun :=
    continuous_pi fun i =>
      (continuous_apply i.succ).comp
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph.continuous.comp
          continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact
      PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm.continuous.comp
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm.continuous.comp
          (continuous_const.prodMk continuous_id))

private def PeriodFamily.GammaZero.fibreMkQ (x : Fin 3 → ℝ) : Fibre :=
  ⟨standardLattice.mkQ (Fin.cons 0 x), by rw [fibreGamma_mkQ]; rfl⟩

@[simp]
private theorem PeriodFamily.GammaZero.fibreHomeomorph_mkQ (x : Fin 3 → ℝ) :
    fibreHomeomorph (fibreMkQ x) = PeriodTorusHigherHomology.coordinateProjection 3 x := by
  funext i
  change
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph (standardLattice.mkQ (Fin.cons 0 x))
        i.succ =
      _
  rw [PeriodTorusHigherHomology.flatTorusCircleHomeomorph_mkQ]
  rfl

private theorem PeriodFamily.GammaZero.fibreHomeomorph_symm_coordinateProjection (x : Fin 3 → ℝ) :
    (fibreHomeomorph.symm (PeriodTorusHigherHomology.coordinateProjection 3 x)).val =
      standardLattice.mkQ (Fin.cons 0 x) := by
  have h :
    fibreHomeomorph.symm (PeriodTorusHigherHomology.coordinateProjection 3 x) = fibreMkQ x := by
    apply fibreHomeomorph.injective
    rw [Homeomorph.apply_symm_apply, fibreHomeomorph_mkQ]
  exact congrArg Subtype.val h

private def PeriodFamily.GammaZero.fibreRetraction : C(RealTorus₄, Fibre) :=
  ⟨fun x =>
    fibreHomeomorph.symm (fun i => PeriodTorusHigherHomology.flatTorusCircleHomeomorph x i.succ),
    fibreHomeomorph.symm.continuous.comp
      (continuous_pi fun i =>
        (continuous_apply i.succ).comp
          PeriodTorusHigherHomology.flatTorusCircleHomeomorph.continuous)⟩

@[simp]
private theorem PeriodFamily.GammaZero.fibreRetraction_inclusion (x : Fibre) :
    fibreRetraction (fibreInclusion x) = x :=
  fibreHomeomorph.symm_apply_apply x

private theorem PeriodFamily.GammaZero.triangleRealEquiv_generator₁_gamma (x : RealPlane₄) :
    SpecialPeriods.triangleRealEquiv SpecialPeriods.triangleGenerator₁ x 0 = x 0 := by
  rw [SpecialPeriods.triangleRealEquiv_apply,
    SpecialPeriods.triangleDualRepresentation_generator₁_matrix]
  simp [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private theorem PeriodFamily.GammaZero.triangleRealEquiv_generator₂_gamma (x : RealPlane₄) :
    SpecialPeriods.triangleRealEquiv SpecialPeriods.triangleGenerator₂ x 0 = x 0 := by
  rw [SpecialPeriods.triangleRealEquiv_apply,
    SpecialPeriods.triangleDualRepresentation_generator₂_matrix]
  simp [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

public
theorem PeriodFamily.GammaZero.triangleRealEquiv_gamma (g : SpecialPeriods.TriangleGroup)
    (x : RealPlane₄) : SpecialPeriods.triangleRealEquiv g x 0 = x 0 := by
  have hg :
    g ∈
      Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) := by
    rw [SpecialPeriods.triangle_generators_generate]
    exact Subgroup.mem_top g
  have h : ∀ x : RealPlane₄, SpecialPeriods.triangleRealEquiv g x 0 = x 0 := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · exact triangleRealEquiv_generator₁_gamma
      · have he : g = SpecialPeriods.triangleGenerator₂ := Set.mem_singleton_iff.mp hg
        subst g
        exact triangleRealEquiv_generator₂_gamma
    | one =>
      intro y
      rw [SpecialPeriods.triangleRealEquiv_one]
      rfl
    | mul g h _ _ ihg ihh =>
      intro y
      rw [SpecialPeriods.triangleRealEquiv_mul_apply, ihg, ihh]
    | inv g _ ihg =>
      intro y
      have hy := ihg (SpecialPeriods.triangleRealEquiv g⁻¹ y)
      rw [← SpecialPeriods.triangleRealEquiv_mul_apply, mul_inv_cancel,
        SpecialPeriods.triangleRealEquiv_one] at hy
      exact hy.symm
  exact h x

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.GammaZero.fibreGamma_triangleTorusHomeomorph
    (g : SpecialPeriods.TriangleGroup) (x : RealTorus₄) :
    fibreGamma (SpecialPeriods.triangleTorusHomeomorph g x) = fibreGamma x := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  rw [SpecialPeriods.triangleTorusHomeomorph_mkQ, fibreGamma_mkQ, fibreGamma_mkQ,
    triangleRealEquiv_gamma]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.GammaZero.familyGamma
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) : C(D.Space, AddCircle (1 : ℝ))
    where
  toFun :=
    Quotient.lift (fun x : SpecialPeriods.TriangleRegularPoint × RealTorus₄ => fibreGamma x.2)
      (by
        rintro x y ⟨g, hg⟩
        have he : SpecialPeriods.triangleTorusHomeomorph g y.2 = x.2 := congrArg Prod.snd hg
        rw [← he, fibreGamma_triangleTorusHomeomorph])
  continuous_toFun :=
    D.quotient_isQuotientMap.continuous_iff.mpr (fibreGamma.continuous.comp continuous_snd)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.GammaZero.familyGamma_quotient
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : SpecialPeriods.TriangleRegularPoint) (x : RealTorus₄) :
    familyGamma D (D.quotient (b, x)) = fibreGamma x :=
  rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private abbrev PeriodFamily.GammaZero.Space
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :=
  { x : D.Space // familyGamma D x = 0 }

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.GammaZero.inclusion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) : C(Space D, D.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.GammaZero.projection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    C(Space D, SpecialPeriods.TriangleRegularQuotient) :=
  ⟨fun x => D.projection x.val, D.projection_continuous.comp continuous_subtype_val⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.GammaZero.quotient
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    C(SpecialPeriods.TriangleRegularPoint × Fibre, Space D)
    where
  toFun
    x :=
    ⟨PeriodFamily.Data.quotient D (x.1, x.2.val),
      (familyGamma_quotient D x.1 x.2.val).trans x.2.property⟩
  continuous_toFun :=
    ((PeriodFamily.Data.quotient_continuous D).comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
      _

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def
    PeriodFamily.GammaZero.lift (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    {X : Type*} [TopologicalSpace X] (f : C(X, D.Space)) (hf : ∀ x, familyGamma D (f x) = 0) :
    C(X, Space D) :=
  ⟨fun x => ⟨f x, hf x⟩, f.continuous.subtype_mk _⟩

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.capSectionFibre_zero_gamma
    (j : Elliptic.Kind) (y : PeriodTorusHigherHomology.ProductTorus 3) :
    PeriodFamily.GammaZero.fibreGamma
        (PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre j 0 y) =
      0 := by
  obtain ⟨k, rfl⟩ := PeriodTorusHigherHomology.coordinateProjection_surjective 3 y
  rw [PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_zero_coordinateProjection,
    PeriodFamily.GammaZero.fibreGamma_mkQ]
  simp only [Fin.cons_zero, AddCircle.coe_zero]

private theorem
    PeriodFamily.Boundary.EllipticGaugeLinearization.familyGamma_linear_capSectionFromModel
    (j : Elliptic.Kind) (τ : ℝ) (q : Elliptic.HigherHomology.mappingTorusModel j) :
    PeriodFamily.GammaZero.familyGamma
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        (linearRegularBoundaryMap j τ
          (PeriodFamily.Boundary.EllipticCapProduct.capSectionFromModel j q)) =
      0 := by
  obtain ⟨⟨s, y⟩, rfl⟩ :=
    MappingTorus.mk_surjective (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm q
  rw [linearRegularBoundaryMap_capSectionFromModel_mk,
    PeriodFamily.GammaZero.familyGamma_quotient]
  exact capSectionFibre_zero_gamma j y

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.familyGamma_linear_capSection
    (j : Elliptic.Kind) (τ : ℝ)
    (q : ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) :
    PeriodFamily.GammaZero.familyGamma
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        (linearRegularBoundaryMap j τ (PeriodFamily.Boundary.EllipticCapProduct.capSection j q)) =
      0 := by
  obtain ⟨x, rfl⟩ :=
    (Elliptic.HigherHomology.surfaceMappingTorusHomeomorph j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm.surjective
      q
  exact familyGamma_linear_capSectionFromModel j τ x

private def
    PeriodFamily.Boundary.EllipticGaugeLinearization.capSectionGammaZeroMap (j : Elliptic.Kind)
    (τ : ℝ) :
    C(ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j,
      PeriodFamily.GammaZero.Space
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)) :=
  PeriodFamily.GammaZero.lift
    (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
    ((linearRegularBoundaryMap j τ).comp (PeriodFamily.Boundary.EllipticCapProduct.capSection j))
    (familyGamma_linear_capSection j τ)

@[simp]
private theorem
    PeriodFamily.Boundary.EllipticGaugeLinearization.inclusion_comp_capSectionGammaZeroMap
    (j : Elliptic.Kind) (τ : ℝ) :
    (PeriodFamily.GammaZero.inclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).comp
        (capSectionGammaZeroMap j τ) =
      (linearRegularBoundaryMap j τ).comp
        (PeriodFamily.Boundary.EllipticCapProduct.capSection j) :=
  rfl

private theorem
  PeriodFamily.Boundary.EllipticGaugeLinearization.boundaryRegular_capSection_homotopic_gammaZero
    (j : Elliptic.Kind) (τ : ℝ) :
    ((ThreefoldOverlapMappingTorus.boundaryToRegularFamily (Option.some j)).comp
          (PeriodFamily.Boundary.EllipticCapProduct.capSection j)).Homotopic
      ((PeriodFamily.GammaZero.inclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).comp
        (capSectionGammaZeroMap j τ)) := by
  rw [inclusion_comp_capSectionGammaZeroMap]
  exact
    (boundaryToRegularFamily_homotopic_linear j τ).comp
      (ContinuousMap.Homotopic.refl (PeriodFamily.Boundary.EllipticCapProduct.capSection j))

private theorem
  PeriodFamily.Boundary.EllipticGaugeLinearization.boundaryRegularHomologyMap_capSection_factor
    (j : Elliptic.Kind) (τ : ℝ) (n : ℕ) :
    (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) n).comp
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Boundary.EllipticCapProduct.capSection j) n) =
      (SingularMayerVietoris.singularHomologyMap
            (PeriodFamily.GammaZero.inclusion
              (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂))
            n).comp
        (SingularMayerVietoris.singularHomologyMap (capSectionGammaZeroMap j τ) n) := by
  exact
    (PeriodTorusHigherHomology.singularHomologyMap_comp
          (PeriodFamily.Boundary.EllipticCapProduct.capSection j)
          (ThreefoldOverlapMappingTorus.boundaryToRegularFamily (Option.some j)) n).symm.trans
      ((PeriodTorusHigherHomology.homotopic_homologyMap
            (boundaryRegular_capSection_homotopic_gammaZero j τ) n).trans
        (PeriodTorusHigherHomology.singularHomologyMap_comp (capSectionGammaZeroMap j τ)
          (PeriodFamily.GammaZero.inclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂))
          n))

private theorem
  PeriodFamily.Boundary.EllipticGaugeLinearization.boundaryRegularHomologyMap_capSection_mem_range
    (j : Elliptic.Kind) (τ : ℝ) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) n) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) n
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Boundary.EllipticCapProduct.capSection j) n a) ∈
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.GammaZero.inclusion
            (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂))
          n) := by
  refine ⟨SingularMayerVietoris.singularHomologyMap (capSectionGammaZeroMap j τ) n a, ?_⟩
  exact (LinearMap.congr_fun (boundaryRegularHomologyMap_capSection_factor j τ n) a).symm

private def PeriodFamily.GammaZero.familyOpen
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient) :
    TopologicalSpace.Opens (Space D) :=
  ⟨(projection D) ⁻¹' (U : Set SpecialPeriods.TriangleRegularQuotient),
    U.isOpen.preimage (projection D).continuous⟩

private def PeriodFamily.GammaZero.inclusionOnOpen
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient) :
    C(familyOpen D U, PeriodFamily.Homology.familyOpen D U) :=
  ⟨fun x => ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

private theorem PeriodFamily.GammaZero.oldSectionChart_gamma
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient)
    (s : C(U, SpecialPeriods.TriangleRegularPoint))
    (hs : ∀ x, SpecialPeriods.triangleRegularProject (s x) = x.val)
    (x : PeriodFamily.Homology.familyOpen D U) :
    fibreGamma (PeriodFamily.Homology.sectionChart D U s hs x).2 = familyGamma D x.val := by
  obtain ⟨y, rfl⟩ := (PeriodFamily.Homology.sectionChart D U s hs).symm.surjective x
  rw [Homeomorph.apply_symm_apply, PeriodFamily.Homology.sectionChart_symm_coe,
    familyGamma_quotient]

private def PeriodFamily.GammaZero.sectionChart
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient)
    (s : C(U, SpecialPeriods.TriangleRegularPoint))
    (hs : ∀ x, SpecialPeriods.triangleRegularProject (s x) = x.val) : familyOpen D U ≃ₜ U × Fibre
    where
  toFun
    x :=
    ((PeriodFamily.Homology.sectionChart D U s hs (inclusionOnOpen D U x)).1,
      ⟨(PeriodFamily.Homology.sectionChart D U s hs (inclusionOnOpen D U x)).2,
        (oldSectionChart_gamma D U s hs (inclusionOnOpen D U x)).trans x.val.property⟩)
  invFun
    y :=
    ⟨quotient D (s y.1, y.2),
      show SpecialPeriods.triangleRegularProject (s y.1) ∈ U from (hs y.1).symm ▸ y.1.property⟩
  left_inv
    x := by
    have h :=
      congrArg (fun z : PeriodFamily.Homology.familyOpen D U => z.val)
        ((PeriodFamily.Homology.sectionChart D U s hs).symm_apply_apply (inclusionOnOpen D U x))
    exact Subtype.ext (Subtype.ext h)
  right_inv
    y := by
    have h := PeriodFamily.Homology.sectionChart_apply_quotient D U s hs y.1 y.2.val
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    apply Prod.ext
    · exact h₁
    · exact Subtype.ext h₂
  continuous_toFun := by
    have h :=
      (PeriodFamily.Homology.sectionChart D U s hs).continuous.comp
        (inclusionOnOpen D U).continuous
    exact h.fst.prodMk (h.snd.subtype_mk _)
  continuous_invFun :=
    ((quotient D).continuous.comp
          ((s.continuous.comp continuous_fst).prodMk continuous_snd)).subtype_mk
      _

@[simp]
private theorem PeriodFamily.GammaZero.sectionChart_symm_projection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient)
    (s : C(U, SpecialPeriods.TriangleRegularPoint))
    (hs : ∀ x, SpecialPeriods.triangleRegularProject (s x) = x.val) (y : U × Fibre) :
    projection D ((sectionChart D U s hs).symm y).val = y.1.val :=
  hs y.1

private def PeriodFamily.GammaZero.sectionRetraction
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient)
    (s : C(U, SpecialPeriods.TriangleRegularPoint))
    (hs : ∀ x, SpecialPeriods.triangleRegularProject (s x) = x.val) :
    C(PeriodFamily.Homology.familyOpen D U, familyOpen D U) :=
  ((sectionChart D U s hs).symm : C(_, _)).comp
    ⟨fun x =>
      ((PeriodFamily.Homology.sectionChart D U s hs x).1,
        fibreRetraction (PeriodFamily.Homology.sectionChart D U s hs x).2),
      (PeriodFamily.Homology.sectionChart D U s hs).continuous.fst.prodMk
        (fibreRetraction.continuous.comp
          (PeriodFamily.Homology.sectionChart D U s hs).continuous.snd)⟩

@[simp]
private theorem PeriodFamily.GammaZero.sectionRetraction_projection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient)
    (s : C(U, SpecialPeriods.TriangleRegularPoint))
    (hs : ∀ x, SpecialPeriods.triangleRegularProject (s x) = x.val)
    (x : PeriodFamily.Homology.familyOpen D U) :
    projection D (sectionRetraction D U s hs x).val = D.projection x.val := by
  change
    projection D
        ((sectionChart D U s hs).symm
            ((PeriodFamily.Homology.sectionChart D U s hs x).1,
              fibreRetraction (PeriodFamily.Homology.sectionChart D U s hs x).2)).val =
      _
  rw [sectionChart_symm_projection]
  exact PeriodFamily.Homology.sectionChart_projection D U s hs x

@[simp]
private theorem PeriodFamily.GammaZero.sectionRetraction_inclusionOnOpen
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient)
    (s : C(U, SpecialPeriods.TriangleRegularPoint))
    (hs : ∀ x, SpecialPeriods.triangleRegularProject (s x) = x.val) (x : familyOpen D U) :
    sectionRetraction D U s hs (inclusionOnOpen D U x) = x := by
  apply (sectionChart D U s hs).injective
  change
    sectionChart D U s hs
        ((sectionChart D U s hs).symm
          ((PeriodFamily.Homology.sectionChart D U s hs (inclusionOnOpen D U x)).1,
            fibreRetraction
              (PeriodFamily.Homology.sectionChart D U s hs (inclusionOnOpen D U x)).2)) =
      _
  rw [Homeomorph.apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact fibreRetraction_inclusion (sectionChart D U s hs x).2

private theorem PeriodFamily.GammaZero.connecting_injective_of_local_homology_zero {X : Type}
    [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) [Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology V (n + 1))] :
    Function.Injective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← SingularMayerVietoris.exact_at_ambient U V hU hV hcover n]
  have hz : SingularMayerVietoris.rightHomologyMap U V (n + 1) = 0 := by
    apply LinearMap.ext
    intro a
    rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
  rw [hz, LinearMap.range_zero]

private theorem PeriodFamily.GammaZero.connecting_comp_homologyMap_injective {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ)
    (n : ℕ) [Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology V (n + 1))]
    (hIntersection :
      Function.Injective
        (SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.intersectionRestriction f U V U' V' hfU hfV) n)) :
    Function.Injective
      ((SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hcover' n).comp
        (SingularMayerVietoris.singularHomologyMap f (n + 1))) := by
  rw [←
    SingularMayerVietoris.connectingHomomorphism_naturality f U V U' V' hfU hfV hU hV hcover hU'
      hV' hcover' n]
  exact hIntersection.comp (connecting_injective_of_local_homology_zero U V hU hV hcover n)

private abbrev PeriodFamily.GammaZero.upperFamily
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :=
  familyOpen D PeriodFamily.Homology.upperBase

private abbrev PeriodFamily.GammaZero.lowerFamily
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :=
  familyOpen D PeriodFamily.Homology.lowerBase

private theorem PeriodFamily.GammaZero.upperFamily_union_lowerFamily
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    (upperFamily D : Set (Space D)) ∪ lowerFamily D = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have h :
    x.val ∈
      (PeriodFamily.Homology.upperFamily D : Set D.Space) ∪ PeriodFamily.Homology.lowerFamily D :=
    by
    rw [PeriodFamily.Homology.upperFamily_union_lowerFamily]
    trivial
  exact h

private theorem PeriodFamily.GammaZero.inclusion_mapsTo_upper
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    Set.MapsTo (PeriodFamily.GammaZero.inclusion D) (upperFamily D : Set (Space D))
      (PeriodFamily.Homology.upperFamily D) :=
  fun _ hx => hx

private theorem PeriodFamily.GammaZero.inclusion_mapsTo_lower
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    Set.MapsTo (PeriodFamily.GammaZero.inclusion D) (lowerFamily D : Set (Space D))
      (PeriodFamily.Homology.lowerFamily D) :=
  fun _ hx => hx

private abbrev PeriodFamily.GammaZero.intersectionFamily
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) : Set (Space D) :=
  (upperFamily D : Set (Space D)) ∩ lowerFamily D

private abbrev PeriodFamily.GammaZero.originalIntersection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) : Set D.Space :=
  (PeriodFamily.Homology.upperFamily D : Set D.Space) ∩ PeriodFamily.Homology.lowerFamily D

private def PeriodFamily.GammaZero.intersectionInclusion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    C(intersectionFamily D, originalIntersection D) :=
  SingularMayerVietoris.intersectionRestriction (PeriodFamily.GammaZero.inclusion D)
    (upperFamily D) (lowerFamily D) (PeriodFamily.Homology.upperFamily D)
    (PeriodFamily.Homology.lowerFamily D) (inclusion_mapsTo_upper D) (inclusion_mapsTo_lower D)

private def PeriodFamily.GammaZero.intersectionToUpper
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    C(originalIntersection D, PeriodFamily.Homology.upperFamily D) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

private def PeriodFamily.GammaZero.upperRetraction
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    C(PeriodFamily.Homology.upperFamily D, upperFamily D) :=
  sectionRetraction D PeriodFamily.Homology.upperBase
    (PeriodFamily.Homology.upperLift PeriodFamily.Homology.normalizedSlitBaseLift)
    (PeriodFamily.Homology.upperLift_project PeriodFamily.Homology.normalizedSlitBaseLift)

@[simp]
private theorem PeriodFamily.GammaZero.upperRetraction_projection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (x : PeriodFamily.Homology.upperFamily D) :
    projection D (upperRetraction D x).val = D.projection x.val :=
  sectionRetraction_projection D PeriodFamily.Homology.upperBase
    (PeriodFamily.Homology.upperLift PeriodFamily.Homology.normalizedSlitBaseLift)
    (PeriodFamily.Homology.upperLift_project PeriodFamily.Homology.normalizedSlitBaseLift) x

private theorem PeriodFamily.GammaZero.upperRetraction_intersection_mem_lower
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (x : originalIntersection D) :
    (upperRetraction D (intersectionToUpper D x)).val ∈ lowerFamily D := by
  change
    projection D (upperRetraction D (intersectionToUpper D x)).val ∈
      PeriodFamily.Homology.lowerBase
  rw [upperRetraction_projection]
  exact x.property.2

private def PeriodFamily.GammaZero.intersectionRetraction
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    C(originalIntersection D, intersectionFamily D)
    where
  toFun
    x :=
    ⟨(upperRetraction D (intersectionToUpper D x)).val,
      (upperRetraction D (intersectionToUpper D x)).property,
      upperRetraction_intersection_mem_lower D x⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((upperRetraction D).continuous.comp (intersectionToUpper D).continuous)).subtype_mk
      _

@[simp]
private theorem PeriodFamily.GammaZero.intersectionRetraction_inclusion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (x : intersectionFamily D) :
    intersectionRetraction D (intersectionInclusion D x) = x := by
  have h :=
    sectionRetraction_inclusionOnOpen D PeriodFamily.Homology.upperBase
      (PeriodFamily.Homology.upperLift PeriodFamily.Homology.normalizedSlitBaseLift)
      (PeriodFamily.Homology.upperLift_project PeriodFamily.Homology.normalizedSlitBaseLift)
      ⟨x.val, x.property.1⟩
  have hv := congrArg (fun z : upperFamily D => z.val) h
  exact Subtype.ext hv

private theorem PeriodFamily.GammaZero.intersectionRetraction_comp_inclusion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    (intersectionRetraction D).comp (intersectionInclusion D) =
      ContinuousMap.id (intersectionFamily D) :=
  ContinuousMap.ext (intersectionRetraction_inclusion D)

private theorem PeriodFamily.GammaZero.intersectionHomologyRetraction_comp_inclusion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (intersectionRetraction D) n).comp
        (SingularMayerVietoris.singularHomologyMap (intersectionInclusion D) n) =
      LinearMap.id := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, intersectionRetraction_comp_inclusion,
    PeriodTorusHigherHomology.singularHomologyMap_id]

private theorem PeriodFamily.GammaZero.intersectionHomologyInclusion_injective
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    Function.Injective (SingularMayerVietoris.singularHomologyMap (intersectionInclusion D) n) := by
  apply
    Function.LeftInverse.injective (g :=
      SingularMayerVietoris.singularHomologyMap (intersectionRetraction D) n)
  intro a
  exact LinearMap.congr_fun (intersectionHomologyRetraction_comp_inclusion D n) a

private def PeriodFamily.GammaZero.fibreTorusHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology Fibre n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n :=
  PeriodTorusHigherHomology.homeomorphHomologyEquiv fibreHomeomorph n

private theorem PeriodFamily.GammaZero.fibreHomology_subsingleton_of_lt (n : ℕ) (h : 3 < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology Fibre n) := by
  let := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt h
  exact (fibreTorusHomologyEquiv n).injective.subsingleton

private theorem PeriodFamily.GammaZero.fibreH4_subsingleton :
    Subsingleton (SingularMayerVietoris.SingularHomology Fibre 4) :=
  fibreHomology_subsingleton_of_lt 4 (by decide)

private def PeriodFamily.GammaZero.upperHomotopyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) : upperFamily D ≃ₕ Fibre :=
  (sectionChart D PeriodFamily.Homology.upperBase
        (PeriodFamily.Homology.upperLift PeriodFamily.Homology.normalizedSlitBaseLift)
        (PeriodFamily.Homology.upperLift_project
          PeriodFamily.Homology.normalizedSlitBaseLift)).toHomotopyEquiv.trans
    (PeriodTorusHigherHomology.CircleTopology.contractibleProdHomotopyEquiv
      PeriodFamily.Homology.upperBase Fibre)

private def PeriodFamily.GammaZero.lowerHomotopyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) : lowerFamily D ≃ₕ Fibre :=
  (sectionChart D PeriodFamily.Homology.lowerBase
        (PeriodFamily.Homology.lowerLift PeriodFamily.Homology.normalizedSlitBaseLift)
        (PeriodFamily.Homology.lowerLift_project
          PeriodFamily.Homology.normalizedSlitBaseLift)).toHomotopyEquiv.trans
    (PeriodTorusHigherHomology.CircleTopology.contractibleProdHomotopyEquiv
      PeriodFamily.Homology.lowerBase Fibre)

private def PeriodFamily.GammaZero.upperHomologyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (upperFamily D) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology Fibre n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (upperHomotopyEquiv D) n

private def PeriodFamily.GammaZero.lowerHomologyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (lowerFamily D) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology Fibre n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (lowerHomotopyEquiv D) n

private theorem PeriodFamily.GammaZero.upperH4_subsingleton
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    Subsingleton (SingularMayerVietoris.SingularHomology (upperFamily D) 4) := by
  let := fibreH4_subsingleton
  exact (upperHomologyEquiv D 4).injective.subsingleton

private theorem PeriodFamily.GammaZero.lowerH4_subsingleton
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    Subsingleton (SingularMayerVietoris.SingularHomology (lowerFamily D) 4) := by
  let := fibreH4_subsingleton
  exact (lowerHomologyEquiv D 4).injective.subsingleton

private def PeriodFamily.GammaZero.homologyInclusion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (Space D) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.Space n :=
  SingularMayerVietoris.singularHomologyMap (PeriodFamily.GammaZero.inclusion D) n

private theorem PeriodFamily.GammaZero.connecting_comp_homologyInclusion_injective
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    Function.Injective
      ((PeriodFamily.Homology.familyConnectingHomomorphism D 3).comp (homologyInclusion D 4)) := by
  let := upperH4_subsingleton D
  let := lowerH4_subsingleton D
  exact
    connecting_comp_homologyMap_injective (PeriodFamily.GammaZero.inclusion D) (upperFamily D)
      (lowerFamily D) (PeriodFamily.Homology.upperFamily D) (PeriodFamily.Homology.lowerFamily D)
      (inclusion_mapsTo_upper D) (inclusion_mapsTo_lower D) (upperFamily D).isOpen
      (lowerFamily D).isOpen (upperFamily_union_lowerFamily D)
      (PeriodFamily.Homology.upperFamily D).isOpen (PeriodFamily.Homology.lowerFamily D).isOpen
      (PeriodFamily.Homology.upperFamily_union_lowerFamily D) 3
      (intersectionHomologyInclusion_injective D 3)

private theorem PeriodFamily.GammaZero.sourceKernelProjection_eq_zero_iff_connecting
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology D.Space (n + 1)) :
    PeriodFamily.Homology.sourceKernelProjection D n a = 0 ↔
      PeriodFamily.Homology.familyConnectingHomomorphism D n a = 0 := by
  change
    a ∈ LinearMap.ker (PeriodFamily.Homology.sourceKernelProjection D n) ↔
      a ∈ LinearMap.ker (PeriodFamily.Homology.familyConnectingHomomorphism D n)
  rw [PeriodFamily.Homology.sourceKernelProjection_kernel,
    PeriodFamily.Homology.familyConnectingHomomorphism_ker_eq_fibre D
      PeriodFamily.Homology.normalizedSlitBaseLift]

private theorem PeriodFamily.GammaZero.sourceKernelProjection_eq_iff_connecting
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ)
    (a b : SingularMayerVietoris.SingularHomology D.Space (n + 1)) :
    PeriodFamily.Homology.sourceKernelProjection D n a =
        PeriodFamily.Homology.sourceKernelProjection D n b ↔
      PeriodFamily.Homology.familyConnectingHomomorphism D n a =
        PeriodFamily.Homology.familyConnectingHomomorphism D n b := by
  simpa only [map_sub, sub_eq_zero] using
    sourceKernelProjection_eq_zero_iff_connecting D n (a - b)

private theorem PeriodFamily.GammaZero.sourceKernelProjection_comp_homologyInclusion_injective
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    Function.Injective
      ((PeriodFamily.Homology.sourceKernelProjection D 3).comp (homologyInclusion D 4)) := by
  intro a b hab
  apply connecting_comp_homologyInclusion_injective D
  exact
    (sourceKernelProjection_eq_iff_connecting D 3 (homologyInclusion D 4 a)
          (homologyInclusion D 4 b)).mp
      hab

private theorem PeriodFamily.GammaZero.sourceKernelProjection_injOn_range
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    Set.InjOn (PeriodFamily.Homology.sourceKernelProjection D 3)
      (LinearMap.range (homologyInclusion D 4)) := by
  rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩ h
  exact
    congrArg (homologyInclusion D 4) (sourceKernelProjection_comp_homologyInclusion_injective D h)

end Mathoverflow1973

end
