/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Uniformization.CuspUniformization3
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Foundations.LocalOrbitQuotient
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldGluing1
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Uniformization.CuspUniformization3

/-!
# Hopf problem: threefold · special periods 7

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

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.specialBaseCover : BaseCover :=
  baseCoverOfSphere SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialBaseCover_cusp_radius_bounds :
    0 < specialBaseCover.radius Option.none ∧
      specialBaseCover.radius Option.none < SpecialPeriods.specialCuspData.radius ∧
        specialBaseCover.radius Option.none <
          SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width :=
  baseCoverOfSphere_cusp_radius_bounds SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.regularPatchPoint : regularPatch := by
  let x := SpecialPeriods.Triangle.triangleSphereUniformization.symm ((2 : ℂ) : RiemannSphere)
  have hx : SpecialPeriods.Triangle.triangleSphereUniformization x = ((2 : ℂ) : RiemannSphere) :=
    SpecialPeriods.Triangle.triangleSphereUniformization.apply_symm_apply _
  refine ⟨x, (mem_regularPatch x).mpr ⟨?_, ?_, ?_⟩⟩
  · intro h
    have he := congrArg SpecialPeriods.Triangle.triangleSphereUniformization h
    rw [hx, SpecialPeriods.Triangle.triangleSphereUniformization_cusp] at he
    exact OnePoint.coe_ne_infty (2 : ℂ) he
  · intro h
    have he := congrArg SpecialPeriods.Triangle.triangleSphereUniformization h
    change
      SpecialPeriods.Triangle.triangleSphereUniformization x =
        SpecialPeriods.Triangle.triangleSphereUniformization
          (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) at he
    rw [hx, SpecialPeriods.Triangle.triangleSphereUniformization_centerOne] at he
    have he' := OnePoint.coe_injective he
    norm_num at he'
  · intro h
    have he := congrArg SpecialPeriods.Triangle.triangleSphereUniformization h
    change
      SpecialPeriods.Triangle.triangleSphereUniformization x =
        SpecialPeriods.Triangle.triangleSphereUniformization
          (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) at he
    rw [hx, SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo] at he
    have he' := OnePoint.coe_injective he
    norm_num at he'

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.SpecialRegularFamily :=
  RegularFamily SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
    SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
private def SpecialPeriods.Threefold.specialRegularFamilyChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) SpecialRegularFamily :=
  regularFamilyChartedSpace SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.specialRegularFamilyProjection :
    SpecialRegularFamily → regularPatch :=
  regularFamilyProjection SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.specialRegularFamilyProjectionToBase :
    SpecialRegularFamily → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  regularFamilyProjectionToBase SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialRegularFamilyProjection_proper :
    IsProperMap specialRegularFamilyProjection :=
  regularFamilyProjection_proper SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.specialRegularFamily_t2Space : T2Space SpecialRegularFamily :=
  regularFamily_t2Space SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
    SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialRegularFamily_secondCountable :
    SecondCountableTopology SpecialRegularFamily :=
  regularFamily_secondCountable SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialRegularFamily_isManifold :
    letI := specialRegularFamilyChartedSpace
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω SpecialRegularFamily :=
  regularFamily_isManifold SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.specialRegularFamilyPoint : SpecialRegularFamily :=
  regularFamilyZeroSection SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    regularPatchPoint

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.specialRegularFamily_nonempty : Nonempty SpecialRegularFamily :=
  ⟨specialRegularFamilyPoint⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.ellipticNeighborhoodChart_symm_generator
    (j : Elliptic.Kind) (z : SpecialPeriods.Disc) :
    letI := SpecialPeriods.Triangle.ellipticNeighborhoodAction j
    (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm (Elliptic.familyRotation j z) =
      SpecialPeriods.Triangle.ellipticStabilizerGenerator j •
        (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z := by
  let := SpecialPeriods.Triangle.ellipticNeighborhoodAction j
  apply (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).injective
  change
    SpecialPeriods.Triangle.ellipticNeighborhoodChart j
        ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm
          (Elliptic.familyRotation j z)) =
      SpecialPeriods.Triangle.ellipticNeighborhoodChart j
        (SpecialPeriods.Triangle.ellipticStabilizerGenerator j •
          (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z)
  rw [Diffeomorph.apply_symm_apply, SpecialPeriods.Triangle.ellipticNeighborhoodChart_generator,
    Diffeomorph.apply_symm_apply]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.ellipticNeighborhoodChart_symm_generatorSL
    (j : Elliptic.Kind) (z : SpecialPeriods.Disc) :
    ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm (Elliptic.familyRotation j z) :
        ℍ) =
      SpecialPeriods.Triangle.ellipticGeneratorSL j •
        ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z : ℍ) := by
  let := SpecialPeriods.Triangle.ellipticNeighborhoodAction j
  have h :=
    congrArg (Subtype.val : SpecialPeriods.Triangle.ellipticNeighborhood j → ℍ)
      (ellipticNeighborhoodChart_symm_generator j z)
  simpa only [SpecialPeriods.Triangle.ellipticNeighborhood_smul_val,
    SpecialPeriods.Triangle.ellipticStabilizerGenerator_val,
    SpecialPeriods.Triangle.ellipticGenerator_smul] using h

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.EllipticFilling.neighborhoodLift (j : Elliptic.Kind)
    (z : SpecialPeriods.Disc) : ℍ :=
  ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z : ℍ)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.neighborhoodLift_holomorphic (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (neighborhoodLift j) :=
  contMDiff_subtype_val.comp (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm.contMDiff

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.neighborhoodLift_rotation (j : Elliptic.Kind)
    (z : SpecialPeriods.Disc) :
    neighborhoodLift j (Elliptic.familyRotation j z) =
      SpecialPeriods.Triangle.ellipticGeneratorSL j • neighborhoodLift j z :=
  ellipticNeighborhoodChart_symm_generatorSL j z

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.EllipticFilling.localPeriods (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind) : HolomorphicPeriodMap ℂ SpecialPeriods.Disc
    where
  point z := P.point (neighborhoodLift j z)
  holomorphic_tau := P.holomorphic_tau.comp (neighborhoodLift_holomorphic j)
  holomorphic_mu := P.holomorphic_mu.comp (neighborhoodLift_holomorphic j)
  holomorphic_beta := P.holomorphic_beta.comp (neighborhoodLift_holomorphic j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
private theorem SpecialPeriods.EllipticFilling.localPeriods_point (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind) (z : SpecialPeriods.Disc) :
    (localPeriods P j).point z = P.point (neighborhoodLift j z) :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem
    SpecialPeriods.EllipticFilling.localPeriods_covariance (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (z : SpecialPeriods.Disc) :
    (localPeriods P j).point (Elliptic.familyRotation j z) =
      Elliptic.periodStep j ((localPeriods P j).point z) := by
  simp only [localPeriods_point, neighborhoodLift_rotation]
  cases j
  · exact h₁ _
  · exact h₂ _

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.EllipticFilling.localData (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Elliptic.Equivariant.Data j
    where
  periods := localPeriods P j
  covariance := localPeriods_covariance P h₁ h₂ j

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
private theorem SpecialPeriods.EllipticFilling.localData_periods (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : (localData P h₁ h₂ j).periods = localPeriods P j :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private abbrev SpecialPeriods.EllipticFilling.fillingSpace (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) :=
  (localData P h₁ h₂ j).Space j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.EllipticFilling.fillingQuotient (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : (localPeriods P j).TotalSpace → fillingSpace P h₁ h₂ j :=
  (localData P h₁ h₂ j).quotient j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.EllipticFilling.fillingProjection (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : fillingSpace P h₁ h₂ j → SpecialPeriods.Disc :=
  (localData P h₁ h₂ j).projection j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[instance_reducible]
private def SpecialPeriods.EllipticFilling.fillingChartedSpace (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : ChartedSpace Elliptic.FamilyModel (fillingSpace P h₁ h₂ j) :=
  (localData P h₁ h₂ j).chartedSpace j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.filling_isManifold (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (fillingSpace P h₁ h₂ j) :=
  (localData P h₁ h₂ j).isManifold j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.fillingQuotient_isCoveringMap
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : IsCoveringMap (fillingQuotient P h₁ h₂ j) :=
  (localData P h₁ h₂ j).quotient_isCoveringMap j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem
    SpecialPeriods.EllipticFilling.fillingQuotient_surjective (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Function.Surjective (fillingQuotient P h₁ h₂ j) :=
  (localData P h₁ h₂ j).quotient_surjective j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem
    SpecialPeriods.EllipticFilling.fillingProjection_proper (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : IsProperMap (fillingProjection P h₁ h₂ j) :=
  (localData P h₁ h₂ j).projection_proper j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem
    SpecialPeriods.EllipticFilling.fillingProjection_surjective (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Function.Surjective (fillingProjection P h₁ h₂ j) :=
  (localData P h₁ h₂ j).projection_surjective j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem
    SpecialPeriods.EllipticFilling.fillingProjection_continuous (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Continuous (fillingProjection P h₁ h₂ j) :=
  (localData P h₁ h₂ j).projection_continuous j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.EllipticFilling.smallDisc (r : ℝ) :
    TopologicalSpace.Opens SpecialPeriods.Disc :=
  ⟨{z | ‖(z : ℂ)‖ < r}, isOpen_lt continuous_subtype_val.norm continuous_const⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.EllipticFilling.smallDiscHomeomorph (r : ℝ) (hr : r < 1) :
    smallDisc r ≃ₜ SpecialPeriods.Threefold.coordinateBall r
    where
  toFun
    z :=
    ⟨((z : SpecialPeriods.Disc) : ℂ), by
      simpa [SpecialPeriods.Threefold.coordinateBall, smallDisc] using z.property⟩
  invFun
    z := by
    have hz : ‖(z : ℂ)‖ < r := by
      simpa [SpecialPeriods.Threefold.coordinateBall, smallDisc] using z.property
    exact ⟨⟨(z : ℂ), by simpa [SpecialPeriods.unitDisc] using hz.trans hr⟩, hz⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.EllipticFilling.pieceDomain (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    TopologicalSpace.Opens (fillingSpace P h₁ h₂ j) :=
  ⟨{y | ‖(fillingProjection P h₁ h₂ j y : ℂ)‖ < C.radius (Option.some j)},
    isOpen_lt (continuous_subtype_val.comp (fillingProjection_continuous P h₁ h₂ j)).norm
      continuous_const⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.EllipticFilling.Piece (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :=
  pieceDomain P h₁ h₂ C j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
private def SpecialPeriods.EllipticFilling.pieceChartedSpace (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    ChartedSpace Elliptic.FamilyModel (Piece P h₁ h₂ C j) := by
  letI := fillingChartedSpace P h₁ h₂ j
  infer_instance

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.EllipticFilling.piece_t2Space (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) : T2Space (Piece P h₁ h₂ C j) :=
  inferInstance

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.EllipticFilling.piece_secondCountable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    SecondCountableTopology (Piece P h₁ h₂ C j) :=
  inferInstance

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.EllipticFilling.piece_isManifold (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    letI := pieceChartedSpace P h₁ h₂ C j
    IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (Piece P h₁ h₂ C j) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := filling_isManifold P h₁ h₂ j
  infer_instance

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.EllipticFilling.pieceCoordinate (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    Piece P h₁ h₂ C j → SpecialPeriods.Threefold.coordinateBall (C.radius (Option.some j)) :=
  fun y =>
  ⟨(fillingProjection P h₁ h₂ j y : ℂ),
    by
    change (fillingProjection P h₁ h₂ j y : ℂ) ∈ Metric.ball 0 (C.radius (Option.some j))
    rw [Metric.mem_ball, dist_zero_right]
    exact y.property⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.EllipticFilling.pieceCoordinate_surjective (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    Function.Surjective (pieceCoordinate P h₁ h₂ C j) := by
  intro z
  have hz : ‖(z : ℂ)‖ < C.radius (Option.some j) := by
    simpa only [SpecialPeriods.Threefold.mem_coordinateBall, Metric.mem_ball,
      dist_zero_right] using z.property
  have hr : C.radius (Option.some j) < 1 := C.radius_lt_chart (Option.some j)
  let w : SpecialPeriods.Disc :=
    ⟨z, by
      change (z : ℂ) ∈ Metric.ball 0 1
      simpa only [Metric.mem_ball, dist_zero_right] using hz.trans hr⟩
  obtain ⟨y, hy⟩ := fillingProjection_surjective P h₁ h₂ j w
  have hy' : y ∈ pieceDomain P h₁ h₂ C j := by
    change ‖(fillingProjection P h₁ h₂ j y : ℂ)‖ < C.radius (Option.some j)
    rw [hy]
    exact hz
  refine ⟨⟨y, hy'⟩, Subtype.ext ?_⟩
  exact congrArg (Subtype.val : SpecialPeriods.Disc → ℂ) hy

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.EllipticFilling.pieceCoordinate_proper (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    IsProperMap (pieceCoordinate P h₁ h₂ C j) :=
  (smallDiscHomeomorph (C.radius (Option.some j))
        (C.radius_lt_chart (Option.some j))).isProperMap.comp
    ((fillingProjection_proper P h₁ h₂ j).restrictPreimage
      (smallDisc (C.radius (Option.some j)) : Set SpecialPeriods.Disc))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.EllipticFilling.pieceProjection (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    Piece P h₁ h₂ C j → C.fillingPatch (Option.some j) :=
  (C.fillingChart (Option.some j)).symm ∘ pieceCoordinate P h₁ h₂ C j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.EllipticFilling.pieceProjection_surjective (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    Function.Surjective (pieceProjection P h₁ h₂ C j) :=
  (C.fillingChart (Option.some j)).symm.surjective.comp (pieceCoordinate_surjective P h₁ h₂ C j)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.EllipticFilling.pieceProjection_proper (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    IsProperMap (pieceProjection P h₁ h₂ C j) :=
  (C.fillingChart (Option.some j)).symm.toHomeomorph.isProperMap.comp
    (pieceCoordinate_proper P h₁ h₂ C j)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.EllipticFilling.pieceProjectionToBase (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    Piece P h₁ h₂ C j → SpecialPeriods.TriangleCompactifiedOrbitSpace := fun y =>
  (pieceProjection P h₁ h₂ C j y : SpecialPeriods.TriangleCompactifiedOrbitSpace)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.EllipticFilling.pieceProjectionToBase_mem_regular_iff
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) (y : Piece P h₁ h₂ C j) :
    pieceProjectionToBase P h₁ h₂ C j y ∈ SpecialPeriods.Threefold.regularPatch ↔
      (fillingProjection P h₁ h₂ j y : ℂ) ≠ 0 :=
  C.fillingEmbedding_mem_regular_iff (Option.some j) (pieceCoordinate P h₁ h₂ C j y)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.SpecialEllipticPiece (j : Elliptic.Kind) :=
  SpecialPeriods.EllipticFilling.Piece SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
private def SpecialPeriods.Threefold.specialEllipticPieceChartedSpace (j : Elliptic.Kind) :
    ChartedSpace (ℂ × ComplexPlane₂) (SpecialEllipticPiece j) :=
  SpecialPeriods.EllipticFilling.pieceChartedSpace SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.specialEllipticPieceProjection (j : Elliptic.Kind) :
    SpecialEllipticPiece j → specialBaseCover.fillingPatch (Option.some j) :=
  SpecialPeriods.EllipticFilling.pieceProjection SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.specialEllipticPieceProjectionToBase (j : Elliptic.Kind) :
    SpecialEllipticPiece j → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.EllipticFilling.pieceProjectionToBase SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialEllipticPieceProjection_proper (j : Elliptic.Kind) :
    IsProperMap (specialEllipticPieceProjection j) :=
  SpecialPeriods.EllipticFilling.pieceProjection_proper SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.specialEllipticPieceProjection_surjective (j : Elliptic.Kind) :
    Function.Surjective (specialEllipticPieceProjection j) :=
  SpecialPeriods.EllipticFilling.pieceProjection_surjective SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialEllipticPiece_t2Space (j : Elliptic.Kind) :
    T2Space (SpecialEllipticPiece j) :=
  SpecialPeriods.EllipticFilling.piece_t2Space SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialEllipticPiece_secondCountable (j : Elliptic.Kind) :
    SecondCountableTopology (SpecialEllipticPiece j) :=
  SpecialPeriods.EllipticFilling.piece_secondCountable SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialEllipticPiece_isManifold (j : Elliptic.Kind) :
    letI := specialEllipticPieceChartedSpace j
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (SpecialEllipticPiece j) :=
  SpecialPeriods.EllipticFilling.piece_isManifold SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialEllipticPiece_nonempty (j : Elliptic.Kind) :
    Nonempty (SpecialEllipticPiece j) := by
  obtain ⟨x, _⟩ :=
    specialEllipticPieceProjection_surjective j
      ⟨puncturePoint (Option.some j), specialBaseCover.point_mem_fillingPatch (Option.some j)⟩
  exact ⟨x⟩

private def SpecialPeriods.CuspFamily.Data.shrink (D : SpecialPeriods.CuspFamily.Data) (r : ℝ)
    (hr : 0 < r) (hrD : r ≤ D.radius) : SpecialPeriods.CuspFamily.Data
    where
  μ := D.μ
  b := D.b
  h := D.h
  radius := r
  radius_pos := hr
  radius_lt_one := hrD.trans_lt D.radius_lt_one
  holomorphic i j := (D.holomorphic i j).mono (Metric.ball_subset_ball hrD)
  smallDrift := D.smallDrift.mono hrD

private theorem SpecialPeriods.CuspFamily.complex_width_ne_zero_mo1973_20202 :
    (SpecialPeriods.Triangle.width : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr SpecialPeriods.Triangle.width_ne_zero

private theorem SpecialPeriods.CuspFamily.qParam_width_mul (s : ℂ) :
    Function.Periodic.qParam SpecialPeriods.Triangle.width
        ((SpecialPeriods.Triangle.width : ℂ) * s) =
      CuspUniformization.exponential s := by
  unfold Function.Periodic.qParam CuspUniformization.exponential
  congr 1
  rw [mul_left_comm, mul_div_cancel_left₀ _ complex_width_ne_zero_mo1973_20202]

private theorem SpecialPeriods.CuspFamily.exponential_div_width (z : ℍ) :
    CuspUniformization.exponential ((z : ℂ) / SpecialPeriods.Triangle.width) =
      SpecialPeriods.Triangle.cuspQ z := by
  simp only [CuspUniformization.exponential, SpecialPeriods.Triangle.cuspQ,
    Function.Periodic.qParam, mul_div_assoc]

private theorem SpecialPeriods.CuspFamily.logBase_scaled_height_mo1973_20205 (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    SpecialPeriods.Triangle.width < ((SpecialPeriods.Triangle.width : ℂ) * (s : ℂ)).im := by
  apply
    (Function.Periodic.norm_qParam_lt_iff SpecialPeriods.Triangle.width_pos
        SpecialPeriods.Triangle.width _).mp
  rw [qParam_width_mul]
  exact ((mem_logBase r s).mp s.property).trans_le hrcap

private def SpecialPeriods.CuspFamily.cuspOverlapUpperDomain (r : ℝ) : TopologicalSpace.Opens ℍ :=
  ⟨{z | ‖SpecialPeriods.Triangle.cuspQ z‖ < r},
    isOpen_lt SpecialPeriods.Triangle.cuspQ_continuous.norm continuous_const⟩

@[simp]
private theorem SpecialPeriods.CuspFamily.mem_cuspOverlapUpperDomain (r : ℝ) (z : ℍ) :
    z ∈ cuspOverlapUpperDomain r ↔ ‖SpecialPeriods.Triangle.cuspQ z‖ < r :=
  Iff.rfl

private theorem SpecialPeriods.CuspFamily.cuspOverlapUpperDomain_subset_horodisc (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    (cuspOverlapUpperDomain r : Set ℍ) ⊆
      SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width := by
  intro z hz
  exact
    (SpecialPeriods.Triangle.cuspQ_norm_lt_exp_iff SpecialPeriods.Triangle.width z).mp
      (hz.trans_le hrcap)

private theorem SpecialPeriods.CuspFamily.cuspOverlapUpperDomain_subset_regular (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    (cuspOverlapUpperDomain r : Set ℍ) ⊆ SpecialPeriods.triangleRegularLocus :=
  (cuspOverlapUpperDomain_subset_horodisc r hrcap).trans
    (SpecialPeriods.Triangle.horodisc_subset_triangleRegularLocus SpecialPeriods.Triangle.width
      le_rfl)

private def SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane (r : ℝ)
    (_hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) : ℍ :=
  UpperHalfPlane.ofComplex ((SpecialPeriods.Triangle.width : ℂ) * (s : ℂ))

@[simp]
private theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_coe (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    (logBaseToUpperHalfPlane r hrcap s : ℂ) = (SpecialPeriods.Triangle.width : ℂ) * (s : ℂ) :=
  congrArg UpperHalfPlane.coe
    (UpperHalfPlane.ofComplex_apply_of_im_pos
      (SpecialPeriods.Triangle.width_pos.trans (logBase_scaled_height_mo1973_20205 r hrcap s)))

private theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_mem_horodisc (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    logBaseToUpperHalfPlane r hrcap s ∈
      SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width := by
  change SpecialPeriods.Triangle.width < (logBaseToUpperHalfPlane r hrcap s).im
  rw [← UpperHalfPlane.coe_im, logBaseToUpperHalfPlane_coe]
  exact logBase_scaled_height_mo1973_20205 r hrcap s

@[simp]
private theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_cuspQ (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    SpecialPeriods.Triangle.cuspQ (logBaseToUpperHalfPlane r hrcap s) =
      CuspUniformization.exponential s := by
  rw [SpecialPeriods.Triangle.cuspQ, logBaseToUpperHalfPlane_coe, qParam_width_mul]

private theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_mem_domain (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) : logBaseToUpperHalfPlane r hrcap s ∈ cuspOverlapUpperDomain r := by
  rw [mem_cuspOverlapUpperDomain, logBaseToUpperHalfPlane_cuspQ]
  exact (mem_logBase r s).mp s.property

private theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_holomorphic (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToUpperHalfPlane r hrcap) := by
  have h :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun s : LogBase r => (SpecialPeriods.Triangle.width : ℂ) * (s : ℂ)) :=
    contMDiff_const.mul contMDiff_subtype_val
  intro s
  exact
    (UpperHalfPlane.contMDiffAt_ofComplex
          (SpecialPeriods.Triangle.width_pos.trans
            (logBase_scaled_height_mo1973_20205 r hrcap s))).comp
      s (h s)

private def SpecialPeriods.CuspFamily.logBaseToOverlapUpperDomain (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) : cuspOverlapUpperDomain r :=
  ⟨logBaseToUpperHalfPlane r hrcap s, logBaseToUpperHalfPlane_mem_domain r hrcap s⟩

private def SpecialPeriods.CuspFamily.overlapUpperToLogBase (r : ℝ) (z : cuspOverlapUpperDomain r) :
    LogBase r :=
  ⟨(z.val : ℂ) / SpecialPeriods.Triangle.width,
    by
    rw [mem_logBase, exponential_div_width]
    exact z.property⟩

@[simp]
private theorem SpecialPeriods.CuspFamily.overlapUpperToLogBase_coe (r : ℝ)
    (z : cuspOverlapUpperDomain r) :
    (overlapUpperToLogBase r z : ℂ) = (z.val : ℂ) / SpecialPeriods.Triangle.width :=
  rfl

private theorem SpecialPeriods.CuspFamily.logBaseToOverlapUpperDomain_holomorphic (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToOverlapUpperDomain r hrcap) := by
  intro s
  have hi :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ logBaseToOverlapUpperDomain r hrcap) s ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToOverlapUpperDomain r hrcap) s :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact hi.mp (logBaseToUpperHalfPlane_holomorphic r hrcap s)

private theorem SpecialPeriods.CuspFamily.overlapUpperToLogBase_holomorphic (r : ℝ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (overlapUpperToLogBase r) := by
  have h :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : cuspOverlapUpperDomain r => (z.val : ℂ) / SpecialPeriods.Triangle.width) :=
    (UpperHalfPlane.contMDiff_coe.comp contMDiff_subtype_val).div_const
      (SpecialPeriods.Triangle.width : ℂ)
  intro z
  have hi :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ overlapUpperToLogBase r) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (overlapUpperToLogBase r) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact hi.mp (h z)

private def SpecialPeriods.CuspFamily.logBaseBiholomorph (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (LogBase r) (cuspOverlapUpperDomain r) ω
    where
  toFun := logBaseToOverlapUpperDomain r hrcap
  invFun := overlapUpperToLogBase r
  left_inv
    s := by
    apply Subtype.ext
    change (logBaseToUpperHalfPlane r hrcap s : ℂ) / SpecialPeriods.Triangle.width = (s : ℂ)
    rw [logBaseToUpperHalfPlane_coe, mul_div_cancel_left₀ _ complex_width_ne_zero_mo1973_20202]
  right_inv
    z := by
    apply Subtype.ext
    apply UpperHalfPlane.ext
    change (logBaseToUpperHalfPlane r hrcap (overlapUpperToLogBase r z) : ℂ) = (z.val : ℂ)
    rw [logBaseToUpperHalfPlane_coe, overlapUpperToLogBase_coe,
      mul_div_cancel₀ _ complex_width_ne_zero_mo1973_20202]
  contMDiff_toFun := logBaseToOverlapUpperDomain_holomorphic r hrcap
  contMDiff_invFun := overlapUpperToLogBase_holomorphic r

private theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_injective (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Function.Injective (logBaseToUpperHalfPlane r hrcap) := by
  intro s t h
  exact (logBaseBiholomorph r hrcap).injective (Subtype.ext h)

private theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_isLocalDiffeomorph (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToUpperHalfPlane r hrcap) := by
  intro s
  exact
    ((logBaseBiholomorph r hrcap).isLocalDiffeomorph s).comp (K := 𝓘(ℂ)) (P := ℍ)
      (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) (cuspOverlapUpperDomain r)
        (logBaseBiholomorph r hrcap s))

private theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_range (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Set.range (logBaseToUpperHalfPlane r hrcap) = (cuspOverlapUpperDomain r : Set ℍ) := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact logBaseToUpperHalfPlane_mem_domain r hrcap s
  · intro hz
    obtain ⟨s, hs⟩ := (logBaseBiholomorph r hrcap).surjective ⟨z, hz⟩
    exact ⟨s, congrArg Subtype.val hs⟩

private def SpecialPeriods.CuspFamily.logBaseToRegular (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) : SpecialPeriods.TriangleRegularPoint :=
  ⟨logBaseToUpperHalfPlane r hrcap s,
    (cuspOverlapUpperDomain_subset_regular r hrcap)
      (logBaseToUpperHalfPlane_mem_domain r hrcap s)⟩

@[simp]
private theorem SpecialPeriods.CuspFamily.logBaseToRegular_coe (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    ((logBaseToRegular r hrcap s : ℍ) : ℂ) = (SpecialPeriods.Triangle.width : ℂ) * (s : ℂ) :=
  logBaseToUpperHalfPlane_coe r hrcap s

private theorem SpecialPeriods.CuspFamily.logBaseToRegular_mem_horodisc (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    (logBaseToRegular r hrcap s : ℍ) ∈
      SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width :=
  logBaseToUpperHalfPlane_mem_horodisc r hrcap s

@[simp]
private theorem SpecialPeriods.CuspFamily.logBaseToRegular_cuspQ (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    SpecialPeriods.Triangle.cuspQ (logBaseToRegular r hrcap s : ℍ) =
      CuspUniformization.exponential s :=
  logBaseToUpperHalfPlane_cuspQ r hrcap s

private theorem SpecialPeriods.CuspFamily.logBaseToRegular_injective (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Function.Injective (logBaseToRegular r hrcap) := by
  intro s t h
  exact logBaseToUpperHalfPlane_injective r hrcap (congrArg Subtype.val h)

private theorem SpecialPeriods.CuspFamily.logBaseToRegular_isLocalDiffeomorph (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToRegular r hrcap) :=
  isLocalDiffeomorph_codRestrictOpens 𝓘(ℂ) 𝓘(ℂ)
    (logBaseToUpperHalfPlane_isLocalDiffeomorph r hrcap) SpecialPeriods.triangleRegularDomain
    (fun s => (logBaseToRegular r hrcap s).property)

private theorem SpecialPeriods.CuspFamily.logBaseToRegular_holomorphic (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToRegular r hrcap) :=
  (logBaseToRegular_isLocalDiffeomorph r hrcap).contMDiff

private theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_translate (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) (k : ℤ)
    (s : LogBase r) :
    logBaseToUpperHalfPlane r hrcap (logBaseTranslate r k s) =
      SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleCuspGenerator ^ k)
        (logBaseToUpperHalfPlane r hrcap s) := by
  apply UpperHalfPlane.ext
  rw [logBaseToUpperHalfPlane_coe, logBaseTranslate_coe,
    SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_coe, logBaseToUpperHalfPlane_coe]
  ring

private theorem SpecialPeriods.CuspFamily.logBaseToRegular_translate (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) (k : ℤ)
    (s : LogBase r) :
    logBaseToRegular r hrcap (logBaseTranslate r k s) =
      (SpecialPeriods.triangleCuspGenerator ^ k) • logBaseToRegular r hrcap s :=
  Subtype.ext (logBaseToUpperHalfPlane_translate r hrcap k s)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.CuspPiece.restrictedData (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    SpecialPeriods.CuspFamily.Data :=
  D.shrink (C.radius Option.none) (C.radius_pos Option.none) hcap

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.CuspPiece.Space (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) :=
  CuspQuotient.QuotientSpace D.correction (C.radius Option.none)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
private def
    SpecialPeriods.Threefold.CuspPiece.nativeChartedSpace (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    ChartedSpace (ToricCharts.CoordinateSpace 3) (Space D C) :=
  CuspQuotient.chartedSpace D.correction (C.radius Option.none) (C.radius_pos Option.none)
    (restrictedData D C hcap).radius_lt_one (restrictedData D C hcap).holomorphic
    (restrictedData D C hcap).smallDrift

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.CuspPiece.space_t2Space (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    T2Space (Space D C) :=
  CuspQuotient.quotient_t2Space D.correction (C.radius Option.none) (C.radius_pos Option.none)
    (restrictedData D C hcap).radius_lt_one (restrictedData D C hcap).holomorphic
    (restrictedData D C hcap).smallDrift

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.CuspPiece.space_secondCountable
    (D : SpecialPeriods.CuspFamily.Data) (C : SpecialPeriods.Threefold.BaseCover)
    (hcap : C.radius Option.none ≤ D.radius) : SecondCountableTopology (Space D C) :=
  CuspQuotient.quotient_secondCountable D.correction (C.radius Option.none)
    (C.radius_pos Option.none) (restrictedData D C hcap).radius_lt_one
    (restrictedData D C hcap).holomorphic (restrictedData D C hcap).smallDrift

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.CuspPiece.space_connected (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) : ConnectedSpace (Space D C) :=
  CuspQuotient.quotient_connected D.correction (C.radius Option.none) (C.radius_pos Option.none)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.CuspPiece.space_nonempty (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) : Nonempty (Space D C) := by
  let := space_connected D C
  infer_instance

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.CuspPiece.native_isManifold (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    letI := nativeChartedSpace D C hcap
    IsManifold (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (Space D C) :=
  CuspQuotient.isManifold D.correction (C.radius Option.none) (C.radius_pos Option.none)
    (restrictedData D C hcap).radius_lt_one (restrictedData D C hcap).holomorphic
    (restrictedData D C hcap).smallDrift

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.CuspPiece.coordinate (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) :
    Space D C → SpecialPeriods.Threefold.coordinateBall (C.radius Option.none) :=
  CuspQuotient.baseMap D.correction (C.radius Option.none)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.CuspPiece.coordinate_proper (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    IsProperMap (coordinate D C) :=
  CuspQuotient.baseMap_proper D.correction (C.radius Option.none) (C.radius_pos Option.none)
    (restrictedData D C hcap).radius_lt_one (restrictedData D C hcap).holomorphic
    (restrictedData D C hcap).smallDrift

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.CuspPiece.projection (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) : Space D C → C.fillingPatch Option.none :=
  (C.fillingChart Option.none).symm ∘ coordinate D C

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.CuspPiece.projection_proper (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    IsProperMap (projection D C) :=
  (C.fillingChart Option.none).symm.toHomeomorph.isProperMap.comp (coordinate_proper D C hcap)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.CuspPiece.projectionToBase (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) :
    Space D C → SpecialPeriods.TriangleCompactifiedOrbitSpace := fun x =>
  (projection D C x : SpecialPeriods.TriangleCompactifiedOrbitSpace)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.CuspPiece.projectionToBase_apply
    (D : SpecialPeriods.CuspFamily.Data) (C : SpecialPeriods.Threefold.BaseCover)
    (x : Space D C) :
    projectionToBase D C x =
      (SpecialPeriods.Threefold.punctureChart Option.none).symm
        (CuspQuotient.projection D.correction (C.radius Option.none) x) :=
  rfl

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.CuspPiece.projectionToBase_mem_regular_iff
    (D : SpecialPeriods.CuspFamily.Data) (C : SpecialPeriods.Threefold.BaseCover)
    (x : Space D C) :
    projectionToBase D C x ∈ SpecialPeriods.Threefold.regularPatch ↔
      CuspQuotient.projection D.correction (C.radius Option.none) x ≠ 0 :=
  C.fillingEmbedding_mem_regular_iff Option.none (coordinate D C x)

private def SpecialPeriods.Threefold.cuspModelEquiv :
    ToricCharts.CoordinateSpace 3 ≃L[ℂ] (ℂ × ComplexPlane₂)
    where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := ![x.1, x.2 0, x.2 1]
  left_inv
    x := by
    ext i
    fin_cases i <;> rfl
  right_inv
    x := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> rfl
  map_add' x y := rfl
  map_smul' r x := rfl
  continuous_toFun := (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)
  continuous_invFun :=
    continuous_pi fun i => by
      fin_cases i
      · exact continuous_fst
      · exact (continuous_apply 0).comp continuous_snd
      · exact (continuous_apply 1).comp continuous_snd

@[instance_reducible]
private def SpecialPeriods.Threefold.ModelChange.chartedSpace {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] : ChartedSpace F X
    where
  atlas :=
    (fun c : OpenPartialHomeomorph X E => c.trans e.toHomeomorph.toOpenPartialHomeomorph) ''
      atlas E X
  chartAt x := (chartAt E x).trans e.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp only [mfld_simps]
  chart_mem_atlas x := Set.mem_image_of_mem _ (chart_mem_atlas E x)

@[simp]
private theorem
    SpecialPeriods.Threefold.ModelChange.chartAt_target {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] (x : X) :
    letI := chartedSpace e X
    (chartAt F x).target = e.symm ⁻¹' (chartAt E x).target := by
  simp [chartAt, ChartedSpace.chartAt]

private def SpecialPeriods.Threefold.ModelChange.diffeomorph {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] (n : ℕ∞ω) :
    letI := chartedSpace e X
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) X X n := by
  let := chartedSpace e X
  have hchart (x y : X) : chartAt F x y = e (chartAt E x y) := rfl
  have hsymm (x : X) (y : F) : (chartAt F x).symm y = (chartAt E x).symm (e.symm y) := rfl
  refine { toEquiv := Equiv.refl X, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · intro x
    apply contMDiffWithinAt_iff'.2
    refine ⟨continuousWithinAt_id, ?_⟩
    apply e.contDiff.contDiffWithinAt.congr_of_mem
    · intro y hy
      have hy' : y ∈ (chartAt E x).target := by simpa [hchart, hsymm] using hy.1
      simpa [hchart, hsymm, extChartAt, OpenPartialHomeomorph.extend, Function.comp_def] using
        congrArg e ((chartAt E x).right_inv hy')
    · simp only [mfld_simps]
  · intro x
    apply contMDiffWithinAt_iff'.2
    refine ⟨continuousWithinAt_id, ?_⟩
    apply e.symm.contDiff.contDiffWithinAt.congr_of_mem
    · intro y hy
      have hy' : e.symm y ∈ (chartAt E x).target := by
        simpa only [mfld_simps, chartAt_target] using hy.1
      simpa [hchart, hsymm, extChartAt, OpenPartialHomeomorph.extend, Function.comp_def] using
        (chartAt E x).right_inv hy'
    · simp only [mfld_simps]

private theorem SpecialPeriods.Threefold.ModelChange.isManifold {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n X] :
    letI := chartedSpace e X
    IsManifold (modelWithCornersSelf ℂ F) n X := by
  let := chartedSpace e X
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
  have hcd : ContDiffOn ℂ n (c.symm.trans d) (c.symm.trans d).source := by
    simpa [contDiffPregroupoid] using
      ((contDiffGroupoid n (modelWithCornersSelf ℂ E)).compatible hc hd).1
  have hcomp :=
    e.contDiff.comp_contDiffOn
      (hcd.comp e.symm.contDiff.contDiffOn
        (show Set.MapsTo e.symm (e.symm ⁻¹' (c.symm.trans d).source) (c.symm.trans d).source from
          fun _ hy => hy))
  simpa [Set.preimage_preimage, Function.comp_def, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.trans_target] using hcomp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
private def
    SpecialPeriods.Threefold.CuspPiece.commonChartedSpace (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    ChartedSpace (ℂ × ComplexPlane₂) (Space D C) := by
  let := nativeChartedSpace D C hcap
  exact
    SpecialPeriods.Threefold.ModelChange.chartedSpace SpecialPeriods.Threefold.cuspModelEquiv
      (Space D C)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.CuspPiece.common_isManifold (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    letI := commonChartedSpace D C hcap
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (Space D C) := by
  let := nativeChartedSpace D C hcap
  let := native_isManifold D C hcap
  exact
    SpecialPeriods.Threefold.ModelChange.isManifold SpecialPeriods.Threefold.cuspModelEquiv
      (Space D C) ω

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.CuspPiece.nativeToCommon (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    letI := nativeChartedSpace D C hcap
    letI := commonChartedSpace D C hcap
    Diffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (Space D C) (Space D C) ω := by
  let := nativeChartedSpace D C hcap
  exact
    SpecialPeriods.Threefold.ModelChange.diffeomorph SpecialPeriods.Threefold.cuspModelEquiv
      (Space D C) ω

private structure
    SpecialPeriods.Threefold.Star.Input (B : Type u) [TopologicalSpace B] (I : Type u) where
  patch : Option I → TopologicalSpace.Opens B
  cover : TopologicalSpace.IsOpenCover patch
  disjoint :
    Pairwise
      (fun i j : I => Disjoint (patch (Option.some i) : Set B) (patch (Option.some j) : Set B))
  piece : Option I → TopCat.{u}
  toBase : ∀ i, C(piece i, B)
  toBase_mem : ∀ i x, toBase i x ∈ patch i
  overlap : ∀ i, OpenPartialHomeomorph (piece (Option.some i)) (piece Option.none)
  source_eq : ∀ i, (overlap i).source = toBase (Option.some i) ⁻¹' (patch Option.none : Set B)
  target_eq : ∀ i, (overlap i).target = toBase Option.none ⁻¹' (patch (Option.some i) : Set B)
  preserves_base :
    ∀ i x, x ∈ (overlap i).source → toBase Option.none (overlap i x) = toBase (Option.some i) x

private def SpecialPeriods.Threefold.Star.Input.transition {B I : Type u} [TopologicalSpace B]
    (D : SpecialPeriods.Threefold.Star.Input B I) :
    ∀ i j : Option I, OpenPartialHomeomorph (D.piece i) (D.piece j)
  | none, Option.none => OpenPartialHomeomorph.refl _
  | none, Option.some j => (D.overlap j).symm
  | some i, Option.none => D.overlap i
  | some i, Option.some j => by
    classical
      exact
      if h : i = j then by
        subst j
        exact OpenPartialHomeomorph.refl _
      else (D.overlap i).trans (D.overlap j).symm

@[simp]
private theorem SpecialPeriods.Threefold.Star.Input.transition_none_none {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) :
    D.transition Option.none Option.none = OpenPartialHomeomorph.refl (D.piece Option.none) :=
  rfl

@[simp]
private theorem SpecialPeriods.Threefold.Star.Input.transition_none_some {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i : I) :
    D.transition Option.none (Option.some i) = (D.overlap i).symm :=
  rfl

@[simp]
private theorem SpecialPeriods.Threefold.Star.Input.transition_some_none {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i : I) :
    D.transition (Option.some i) Option.none = D.overlap i :=
  rfl

private theorem SpecialPeriods.Threefold.Star.Input.transition_some_self {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i : I) :
    D.transition (Option.some i) (Option.some i) =
      OpenPartialHomeomorph.refl (D.piece (Option.some i)) := by simp [transition]

private theorem SpecialPeriods.Threefold.Star.Input.transition_some_some_of_ne {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) {i j : I} (h : i ≠ j) :
    D.transition (Option.some i) (Option.some j) = (D.overlap i).trans (D.overlap j).symm := by
  simp [transition, h]

@[simp]
private theorem
    SpecialPeriods.Threefold.Star.Input.transition_self {B I : Type u} [TopologicalSpace B]
    (D : SpecialPeriods.Threefold.Star.Input B I) (i : Option I) :
    D.transition i i = OpenPartialHomeomorph.refl (D.piece i) := by
  cases i with
  | none => simp
  | some i => exact D.transition_some_self i

private theorem
    SpecialPeriods.Threefold.Star.Input.transition_symm {B I : Type u} [TopologicalSpace B]
    (D : SpecialPeriods.Threefold.Star.Input B I) (i j : Option I) :
    (D.transition i j).symm = D.transition j i := by
  cases i with
  | none => cases j <;> simp
  | some i =>
    cases j with
    | none => simp
    | some j =>
      by_cases h : i = j
      · subst j
        simp
      · rw [D.transition_some_some_of_ne h, D.transition_some_some_of_ne (Ne.symm h)]
        simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.symm_symm]

private theorem SpecialPeriods.Threefold.Star.Input.overlap_symm_preserves_base {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i : I)
    (x : D.piece Option.none) (hx : x ∈ (D.overlap i).target) :
    D.toBase (Option.some i) ((D.overlap i).symm x) = D.toBase Option.none x := by
  have h := D.preserves_base i ((D.overlap i).symm x) ((D.overlap i).map_target hx)
  rw [(D.overlap i).right_inv hx] at h
  exact h.symm

@[simp]
private theorem SpecialPeriods.Threefold.Star.Input.toBase_preimage_own {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i : Option I) :
    D.toBase i ⁻¹' (D.patch i : Set B) = Set.univ :=
  Set.eq_univ_of_forall (D.toBase_mem i)

private theorem SpecialPeriods.Threefold.Star.Input.filling_preimage_eq_empty {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) {i j : I} (h : i ≠ j) :
    D.toBase (Option.some i) ⁻¹' (D.patch (Option.some j) : Set B) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact Set.disjoint_left.mp (D.disjoint h) (D.toBase_mem (Option.some i) x) hx

private theorem
    SpecialPeriods.Threefold.Star.Input.transition_some_some_source_eq_empty {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) {i j : I} (h : i ≠ j) :
    (D.transition (Option.some i) (Option.some j)).source = ∅ := by
  rw [D.transition_some_some_of_ne h, OpenPartialHomeomorph.trans_source]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hy⟩
  have hb : D.toBase Option.none (D.overlap i x) ∈ D.patch (Option.some j) := by
    simpa only [OpenPartialHomeomorph.symm_source, D.target_eq j, Set.mem_preimage,
      SetLike.mem_coe] using hy
  rw [D.preserves_base i x hx] at hb
  exact Set.disjoint_left.mp (D.disjoint h) (D.toBase_mem (Option.some i) x) hb

private theorem SpecialPeriods.Threefold.Star.Input.transition_source_eq {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i j : Option I) :
    (D.transition i j).source = D.toBase i ⁻¹' (D.patch j : Set B) := by
  cases i with
  | none =>
    cases j with
    | none => simp
    | some j => simpa using D.target_eq j
  | some i =>
    cases j with
    | none => exact D.source_eq i
    | some j =>
      by_cases h : i = j
      · subst j
        simp
      · rw [D.transition_some_some_source_eq_empty h, D.filling_preimage_eq_empty h]

private theorem SpecialPeriods.Threefold.Star.Input.transition_preserves_base {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i j : Option I)
    (x : D.piece i) (hx : x ∈ (D.transition i j).source) :
    D.toBase j (D.transition i j x) = D.toBase i x := by
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact D.overlap_symm_preserves_base j x hx
  | some i =>
    cases j with
    | none => exact D.preserves_base i x hx
    | some j =>
      by_cases h : i = j
      · subst j
        simp
      · rw [D.transition_some_some_source_eq_empty h] at hx
        exact hx.elim

private theorem SpecialPeriods.Threefold.Star.Input.eq_or_eq_or_eq_of_common_base {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i j k : Option I) {b : B}
    (hi : b ∈ D.patch i) (hj : b ∈ D.patch j) (hk : b ∈ D.patch k) : i = j ∨ j = k ∨ i = k := by
  have he : ∀ a c : I, b ∈ D.patch (Option.some a) → b ∈ D.patch (Option.some c) → a = c := by
    intro a c ha hc
    by_contra h
    exact Set.disjoint_left.mp (D.disjoint h) ha hc
  cases i with
  | none =>
    cases j with
    | none => exact Or.inl rfl
    | some j =>
      cases k with
      | none => exact Or.inr (Or.inr rfl)
      | some k => exact Or.inr (Or.inl (congrArg Option.some (he j k hj hk)))
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact Or.inr (Or.inl rfl)
      | some k => exact Or.inr (Or.inr (congrArg Option.some (he i k hi hk)))
    | some j => exact Or.inl (congrArg Option.some (he i j hi hj))

private theorem
    SpecialPeriods.Threefold.Star.Input.transition_cocycle {B I : Type u} [TopologicalSpace B]
    (D : SpecialPeriods.Threefold.Star.Input B I) (i j k : Option I) (x : D.piece i)
    (hx : x ∈ (D.transition i j).source) (hy : D.transition i j x ∈ (D.transition j k).source) :
    D.transition j k (D.transition i j x) = D.transition i k x := by
  have hj : D.toBase i x ∈ D.patch j := by
    simpa only [D.transition_source_eq i j, Set.mem_preimage, SetLike.mem_coe] using hx
  have hk : D.toBase i x ∈ D.patch k := by
    have h : D.toBase j (D.transition i j x) ∈ D.patch k := by
      simpa only [D.transition_source_eq j k, Set.mem_preimage, SetLike.mem_coe] using hy
    rwa [D.transition_preserves_base i j x hx] at h
  rcases D.eq_or_eq_or_eq_of_common_base i j k (D.toBase_mem i x) hj hk with hij | hjk | hik
  · subst j
    simp
  · subst k
    simp
  · subst k
    rw [← D.transition_symm i j, D.transition_self]
    exact (D.transition i j).left_inv hx

private abbrev SpecialPeriods.Threefold.Star.Input.toData {B I : Type u} [TopologicalSpace B]
    (D : SpecialPeriods.Threefold.Star.Input B I) : ThreefoldGluing.Data B
    where
  J := Option I
  patch := D.patch
  cover := D.cover
  piece := D.piece
  toBase := D.toBase
  toBase_mem := D.toBase_mem
  transition := D.transition
  source_eq := D.transition_source_eq
  self_eq := D.transition_self
  symm_eq := D.transition_symm
  preserves_base := D.transition_preserves_base
  cocycle := D.transition_cocycle

private theorem SpecialPeriods.Threefold.Star.Input.transition_holomorphic {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [∀ i, ChartedSpace E (D.piece i)]
    (hhol :
      ∀ i,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.overlap i)
          (D.overlap i).source)
    (hinv :
      ∀ i,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.overlap i).symm
          (D.overlap i).target)
    (i j : Option I) :
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
      (D.transition i j).source := by
  cases i with
  | none =>
    cases j with
    | none =>
      rw [D.transition_none_none]
      change
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
          (id : D.piece Option.none → D.piece Option.none) Set.univ
      exact contMDiffOn_id
    | some j =>
      rw [D.transition_none_some]
      simpa only [OpenPartialHomeomorph.symm_source] using hinv j
  | some i =>
    cases j with
    | none =>
      rw [D.transition_some_none]
      exact hhol i
    | some j =>
      by_cases h : i = j
      · subst j
        rw [D.transition_some_self]
        change
          ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
            (id : D.piece (Option.some i) → D.piece (Option.some i)) Set.univ
        exact contMDiffOn_id
      · rw [D.transition_some_some_source_eq_empty h]
        exact contMDiffOn_empty

private theorem SpecialPeriods.Threefold.Star.Input.toData_transition_holomorphic {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [∀ i, ChartedSpace E (D.piece i)]
    (hhol :
      ∀ i,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.overlap i)
          (D.overlap i).source)
    (hinv :
      ∀ i,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.overlap i).symm
          (D.overlap i).target)
    (i j : D.toData.J) :
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.toData.transition i j)
      (D.toData.transition i j).source := by
  change
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
      (D.transition i j).source
  exact D.transition_holomorphic hhol hinv i j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialCuspRadius_le :
    specialBaseCover.radius Option.none ≤ SpecialPeriods.specialCuspData.radius :=
  specialBaseCover_cusp_radius_bounds.2.1.le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.SpecialCuspPiece :=
  CuspPiece.Space SpecialPeriods.specialCuspData specialBaseCover

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
private def SpecialPeriods.Threefold.specialCuspPieceChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) SpecialCuspPiece :=
  CuspPiece.commonChartedSpace SpecialPeriods.specialCuspData specialBaseCover
    specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.specialCuspPieceProjection :
    SpecialCuspPiece → specialBaseCover.fillingPatch Option.none :=
  CuspPiece.projection SpecialPeriods.specialCuspData specialBaseCover

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.specialCuspPieceProjectionToBase :
    SpecialCuspPiece → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  CuspPiece.projectionToBase SpecialPeriods.specialCuspData specialBaseCover

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialCuspPieceProjection_proper :
    IsProperMap specialCuspPieceProjection :=
  CuspPiece.projection_proper SpecialPeriods.specialCuspData specialBaseCover specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialCuspPiece_t2Space : T2Space SpecialCuspPiece :=
  CuspPiece.space_t2Space SpecialPeriods.specialCuspData specialBaseCover specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialCuspPiece_secondCountable :
    SecondCountableTopology SpecialCuspPiece :=
  CuspPiece.space_secondCountable SpecialPeriods.specialCuspData specialBaseCover
    specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialCuspPiece_isManifold :
    letI := specialCuspPieceChartedSpace
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω SpecialCuspPiece :=
  CuspPiece.common_isManifold SpecialPeriods.specialCuspData specialBaseCover specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialCuspPiece_nonempty : Nonempty SpecialCuspPiece :=
  CuspPiece.space_nonempty SpecialPeriods.specialCuspData specialBaseCover

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.localPiece : Index → TopCat
  | none => TopCat.of SpecialRegularFamily
  | some Option.none => TopCat.of SpecialCuspPiece
  | some (Option.some j) => TopCat.of (SpecialEllipticPiece j)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
private def SpecialPeriods.Threefold.localPieceChartedSpace (i : Index) :
    ChartedSpace (ℂ × ComplexPlane₂) (localPiece i) := by
  cases i with
  | none => exact specialRegularFamilyChartedSpace
  | some i =>
    cases i with
    | none => exact specialCuspPieceChartedSpace
    | some j => exact specialEllipticPieceChartedSpace j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem
    SpecialPeriods.Threefold.localPiece_nonempty (i : Index) : Nonempty (localPiece i) := by
  cases i with
  | none => exact specialRegularFamily_nonempty
  | some i =>
    cases i with
    | none => exact specialCuspPiece_nonempty
    | some j => exact specialEllipticPiece_nonempty j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem
    SpecialPeriods.Threefold.localPiece_t2Space (i : Index) : T2Space (localPiece i) := by
  cases i with
  | none => exact specialRegularFamily_t2Space
  | some i =>
    cases i with
    | none => exact specialCuspPiece_t2Space
    | some j => exact specialEllipticPiece_t2Space j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.localPiece_secondCountable (i : Index) :
    SecondCountableTopology (localPiece i) := by
  cases i with
  | none => exact specialRegularFamily_secondCountable
  | some i =>
    cases i with
    | none => exact specialCuspPiece_secondCountable
    | some j => exact specialEllipticPiece_secondCountable j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.localPiece_isManifold (i : Index) :
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (localPiece i) := by
  cases i with
  | none => exact specialRegularFamily_isManifold
  | some i =>
    cases i with
    | none => exact specialCuspPiece_isManifold
    | some j => exact specialEllipticPiece_isManifold j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private def SpecialPeriods.Threefold.localProjection :
    (i : Index) → localPiece i → specialBaseCover.patch i
  | none => specialRegularFamilyProjection
  | some Option.none => specialCuspPieceProjection
  | some (Option.some j) => specialEllipticPieceProjection j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.localProjection_proper (i : Index) :
    IsProperMap (localProjection i) := by
  cases i with
  | none => exact specialRegularFamilyProjection_proper
  | some i =>
    cases i with
    | none => exact specialCuspPieceProjection_proper
    | some j => exact specialEllipticPieceProjection_proper j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private def SpecialPeriods.Threefold.localProjectionToBase (i : Index) (x : localPiece i) :
    SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  localProjection i x

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.localProjectionToBase_mem (i : Index) (x : localPiece i) :
    localProjectionToBase i x ∈ specialBaseCover.patch i :=
  (localProjection i x).property

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.localProjectionToBase_continuous (i : Index) :
    Continuous (localProjectionToBase i) :=
  continuous_subtype_val.comp (localProjection_proper i).continuous

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private def SpecialPeriods.Threefold.localBaseMap (i : Index) :
    C(localPiece i, SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  ⟨localProjectionToBase i, localProjectionToBase_continuous i⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.CuspGlobalOverlap.sphereRegularData
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint :=
  PeriodFamily.regularData (SpecialPeriods.Construction.periodMapOfSphere π hπ h₀ h₁)
    (SpecialPeriods.Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁)
    (SpecialPeriods.Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.CuspGlobalOverlap.sphereCuspData
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (r : ℝ) (hr : 0 < r)
    (hrD : r ≤ (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius) :
    SpecialPeriods.CuspFamily.Data :=
  (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).shrink r hr hrD

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.CuspGlobalOverlap.sphereCuspData_periodPoint
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (r : ℝ) (hr : 0 < r)
    (hrD : r ≤ (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius)
    (s : SpecialPeriods.CuspFamily.LogBase r) :
    ((sphereCuspData π hπ h₀ h₁ r hr hrD).periods.point s).val =
      SpecialPeriods.cuspPeriodPoint (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).μ
        (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).b
        (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).h (s : ℂ) :=
  rfl

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.CuspGlobalOverlap.spherePeriod_point
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (r : ℝ) (hrD : r ≤ (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : SpecialPeriods.CuspFamily.LogBase r) :
    ((sphereRegularData π hπ h₀ h₁).periods.point
          (SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s)).val =
      SpecialPeriods.cuspPeriodPoint (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).μ
        (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).b
        (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).h (s : ℂ) := by
  have hz :
    ‖SpecialPeriods.Triangle.cuspQ (SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s : ℍ)‖ <
      (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius := by
    rw [SpecialPeriods.CuspFamily.logBaseToRegular_cuspQ]
    exact ((SpecialPeriods.CuspFamily.mem_logBase r s).mp s.property).trans_le hrD
  have h :=
    SpecialPeriods.Construction.cuspDataOfSphere_periodPoint π hπ h₀ h₁
      (SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s : ℍ) hz
  rw [SpecialPeriods.CuspFamily.logBaseToRegular_coe,
    mul_div_cancel_left₀ _
      (Complex.ofReal_ne_zero.mpr SpecialPeriods.Triangle.width_ne_zero)] at h
  exact h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.CuspGlobalOverlap.spherePeriod_agreement
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (r : ℝ) (hr : 0 < r)
    (hrD : r ≤ (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : SpecialPeriods.CuspFamily.LogBase r) :
    (sphereRegularData π hπ h₀ h₁).periods.point
        (SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s) =
      (sphereCuspData π hπ h₀ h₁ r hr hrD).periods.point s := by
  apply Subtype.ext
  rw [sphereCuspData_periodPoint]
  exact spherePeriod_point π hπ h₀ h₁ r hrD hrcap s

private def SpecialPeriods.CuspGlobalOverlap.QuotientComparison.totalMap
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (f : SpecialPeriods.CuspFamily.LogBase C.radius → SpecialPeriods.TriangleRegularPoint)
    (x : C.TotalSpace) : D.TotalSpace :=
  (f x.1, x.2)

private theorem SpecialPeriods.CuspGlobalOverlap.QuotientComparison.totalMap_injective
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (f : SpecialPeriods.CuspFamily.LogBase C.radius → SpecialPeriods.TriangleRegularPoint)
    (hf : Function.Injective f) : Function.Injective (totalMap C D f) := by
  intro x y h
  exact Prod.ext (hf (congrArg Prod.fst h)) (congrArg (fun z : D.TotalSpace => z.2) h)

private theorem SpecialPeriods.CuspGlobalOverlap.QuotientComparison.totalMap_equivariant
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (f : SpecialPeriods.CuspFamily.LogBase C.radius → SpecialPeriods.TriangleRegularPoint)
    (hbase :
      ∀ (k : ℤ) (s : SpecialPeriods.CuspFamily.LogBase C.radius),
        f (SpecialPeriods.CuspFamily.logBaseTranslate C.radius k s) =
          SpecialPeriods.triangleCuspGenerator ^ k • f s)
    (htorus :
      ∀ k : ℤ,
        SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.triangleCuspGenerator ^ k) =
          SpecialPeriods.CuspFamily.cuspTorusHomeomorph k)
    (k : Multiplicative ℤ) (x : C.TotalSpace) :
    letI := C.totalAction
    letI := D.totalAction
    totalMap C D f (k • x) = SpecialPeriods.triangleCuspGenerator ^ k.toAdd • totalMap C D f x := by
  let := C.totalAction
  let := D.totalAction
  change
    (f (SpecialPeriods.CuspFamily.logBaseTranslate C.radius k.toAdd x.1),
        SpecialPeriods.CuspFamily.cuspTorusHomeomorph k.toAdd x.2) =
      (SpecialPeriods.triangleCuspGenerator ^ k.toAdd • f x.1,
        SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.triangleCuspGenerator ^ k.toAdd)
          x.2)
  rw [hbase, htorus]

private def SpecialPeriods.CuspGlobalOverlap.QuotientComparison.descend
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (f : SpecialPeriods.CuspFamily.LogBase C.radius → SpecialPeriods.TriangleRegularPoint)
    (hbase :
      ∀ (k : ℤ) (s : SpecialPeriods.CuspFamily.LogBase C.radius),
        f (SpecialPeriods.CuspFamily.logBaseTranslate C.radius k s) =
          SpecialPeriods.triangleCuspGenerator ^ k • f s)
    (htorus :
      ∀ k : ℤ,
        SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.triangleCuspGenerator ^ k) =
          SpecialPeriods.CuspFamily.cuspTorusHomeomorph k) :
    C.Space → D.Space := by
  letI := C.totalAction
  letI := D.totalAction
  exact
    Quotient.lift (D.quotient ∘ totalMap C D f)
      (by
        rintro x y ⟨k, hk⟩
        change D.quotient (totalMap C D f x) = D.quotient (totalMap C D f y)
        rw [← hk, totalMap_equivariant C D f hbase htorus, D.quotient_smul])

private theorem SpecialPeriods.CuspGlobalOverlap.QuotientComparison.descend_injective
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (f : SpecialPeriods.CuspFamily.LogBase C.radius → SpecialPeriods.TriangleRegularPoint)
    (hbase :
      ∀ (k : ℤ) (s : SpecialPeriods.CuspFamily.LogBase C.radius),
        f (SpecialPeriods.CuspFamily.logBaseTranslate C.radius k s) =
          SpecialPeriods.triangleCuspGenerator ^ k • f s)
    (htorus :
      ∀ k : ℤ,
        SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.triangleCuspGenerator ^ k) =
          SpecialPeriods.CuspFamily.cuspTorusHomeomorph k)
    (hf : Function.Injective f)
    (hreturn :
      ∀ (g : SpecialPeriods.TriangleGroup) (s t : SpecialPeriods.CuspFamily.LogBase C.radius),
        g • f t = f s → ∃ k : ℤ, SpecialPeriods.triangleCuspGenerator ^ k = g) :
    Function.Injective (descend C D f hbase htorus) := by
  let := C.totalAction
  let := D.totalAction
  intro x y hxy
  obtain ⟨a, rfl⟩ := C.quotient_surjective x
  obtain ⟨b, rfl⟩ := C.quotient_surjective y
  obtain ⟨g, hg⟩ := (D.quotient_eq_iff _ _).mp hxy
  have hb : g • f b.1 = f a.1 := congrArg Prod.fst hg
  obtain ⟨k, rfl⟩ := hreturn g a.1 b.1 hb
  apply (C.quotient_eq_iff _ _).mpr
  refine ⟨Multiplicative.ofAdd k, ?_⟩
  apply totalMap_injective C D f hf
  rw [totalMap_equivariant C D f hbase htorus]
  exact hg

private theorem SpecialPeriods.CuspGlobalOverlap.QuotientComparison.range_descend
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (f : SpecialPeriods.CuspFamily.LogBase C.radius → SpecialPeriods.TriangleRegularPoint)
    (hbase :
      ∀ (k : ℤ) (s : SpecialPeriods.CuspFamily.LogBase C.radius),
        f (SpecialPeriods.CuspFamily.logBaseTranslate C.radius k s) =
          SpecialPeriods.triangleCuspGenerator ^ k • f s)
    (htorus :
      ∀ k : ℤ,
        SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.triangleCuspGenerator ^ k) =
          SpecialPeriods.CuspFamily.cuspTorusHomeomorph k) :
    Set.range (descend C D f hbase htorus) = D.projection ⁻¹' Set.range (D.baseQuotient ∘ f) := by
  let := D.totalAction
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := C.quotient_surjective x
    exact ⟨a.1, rfl⟩
  · rintro ⟨s, hs⟩
    obtain ⟨⟨b, t⟩, rfl⟩ := D.quotient_surjective y
    have hbase' : D.baseQuotient (f s) = D.baseQuotient b := hs
    have hrel : ∃ g : SpecialPeriods.TriangleGroup, g • b = f s := Quotient.eq''.mp hbase'
    obtain ⟨g, hg⟩ := hrel
    refine ⟨C.quotient (s, SpecialPeriods.triangleTorusHomeomorph g t), ?_⟩
    apply (D.quotient_eq_iff _ _).mpr
    exact ⟨g, Prod.ext hg rfl⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
private def SpecialPeriods.CuspGlobalOverlap.baseCover (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    SpecialPeriods.CuspFamily.LogBase r → SpecialPeriods.TriangleRegularQuotient :=
  SpecialPeriods.triangleRegularProject ∘ SpecialPeriods.CuspFamily.logBaseToRegular r hrcap

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.CuspGlobalOverlap.baseCover_isLocalDiffeomorph (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (baseCover r hrcap) := by
  intro s
  exact
    (SpecialPeriods.CuspFamily.logBaseToRegular_isLocalDiffeomorph r hrcap s).comp (K := 𝓘(ℂ))
      (P := SpecialPeriods.TriangleRegularQuotient)
      (SpecialPeriods.triangleRegularProject_isLocalDiffeomorph
        (SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
private def SpecialPeriods.CuspGlobalOverlap.basePatch (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient :=
  ⟨Set.range (baseCover r hrcap), (baseCover_isLocalDiffeomorph r hrcap).isOpen_range⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
private def SpecialPeriods.CuspGlobalOverlap.compactBase :
    SpecialPeriods.TriangleRegularQuotient → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.triangleOpenInclusion ∘ SpecialPeriods.triangleRegularToOrbit

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
@[simp]
private theorem SpecialPeriods.CuspGlobalOverlap.compactBase_baseCover (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : SpecialPeriods.CuspFamily.LogBase r) :
    compactBase (baseCover r hrcap s) =
      SpecialPeriods.triangleOpenInclusion
        (SpecialPeriods.triangleOrbitProjection
          (SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s : ℍ)) :=
  rfl

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.CuspGlobalOverlap.compactBase_baseCover_mem_chart (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : SpecialPeriods.CuspFamily.LogBase r) :
    compactBase (baseCover r hrcap s) ∈
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source := by
  apply
    (SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood SpecialPeriods.Triangle.width
        _).mpr
  exact
    ⟨(SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s : ℍ),
      SpecialPeriods.CuspFamily.logBaseToRegular_mem_horodisc r hrcap s, rfl⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.CuspGlobalOverlap.cuspFullChart_compactBase_baseCover (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : SpecialPeriods.CuspFamily.LogBase r) :
    SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
        (compactBase (baseCover r hrcap s)) =
      CuspUniformization.exponential s := by
  rw [compactBase_baseCover]
  exact
    (SpecialPeriods.Triangle.cuspFullChart_mk SpecialPeriods.Triangle.width le_rfl
          ⟨(SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s : ℍ),
            SpecialPeriods.CuspFamily.logBaseToRegular_mem_horodisc r hrcap s⟩).trans
      (SpecialPeriods.CuspFamily.logBaseToRegular_cuspQ r hrcap s)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.CuspGlobalOverlap.logBaseToRegular_return (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (g : SpecialPeriods.TriangleGroup) (s t : SpecialPeriods.CuspFamily.LogBase r)
    (he :
      g • SpecialPeriods.CuspFamily.logBaseToRegular r hrcap t =
        SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s) :
    ∃ k : ℤ, SpecialPeriods.triangleCuspGenerator ^ k = g := by
  apply Subgroup.mem_zpowers_iff.mp
  apply
    SpecialPeriods.Triangle.triangle_horodisc_overlap_mem_cusp SpecialPeriods.Triangle.width
      le_rfl g
  exact
    ⟨(SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s : ℍ),
      ⟨(SpecialPeriods.CuspFamily.logBaseToRegular r hrcap t : ℍ),
        SpecialPeriods.CuspFamily.logBaseToRegular_mem_horodisc r hrcap t,
        congrArg Subtype.val he⟩,
      SpecialPeriods.CuspFamily.logBaseToRegular_mem_horodisc r hrcap s⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.CuspGlobalOverlap.mem_basePatch_iff (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (q : SpecialPeriods.TriangleRegularQuotient) :
    q ∈ basePatch r hrcap ↔
      compactBase q ∈
          (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source ∧
        ‖SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (compactBase q)‖ <
          r := by
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨compactBase_baseCover_mem_chart r hrcap s, ?_⟩
    rw [cuspFullChart_compactBase_baseCover]
    exact (SpecialPeriods.CuspFamily.mem_logBase r s).mp s.property
  · rintro ⟨hsource, hnorm⟩
    have himage :
      SpecialPeriods.triangleRegularToOrbit q ∈
        SpecialPeriods.Triangle.cuspImage SpecialPeriods.Triangle.width :=
      (SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood SpecialPeriods.Triangle.width
            _).mp
        hsource
    obtain ⟨z, hz, he⟩ := himage
    have hqz : ‖SpecialPeriods.Triangle.cuspQ z‖ < r := by
      have hcoord :=
        SpecialPeriods.Triangle.cuspFullChart_mk SpecialPeriods.Triangle.width le_rfl
          (⟨z, hz⟩ : SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width)
      change
        SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
            (SpecialPeriods.triangleOpenInclusion (SpecialPeriods.triangleOrbitProjection z)) =
          SpecialPeriods.Triangle.cuspQ z at hcoord
      rw [he] at hcoord
      exact hcoord ▸ hnorm
    obtain ⟨s, hs⟩ :=
      (SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_range r hrcap ▸ hqz :
        z ∈ Set.range (SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane r hrcap))
    refine ⟨s, SpecialPeriods.triangleRegularToOrbit_injective ?_⟩
    change
      SpecialPeriods.triangleOrbitProjection
          (SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane r hrcap s) =
        SpecialPeriods.triangleRegularToOrbit q
    rw [hs]
    exact he

@[instance_reducible]
private def SpecialPeriods.EllipticFilling.coveringChartedSpace {A : Type*} [TopologicalSpace A]
    [ChartedSpace ℂ A] : ChartedSpace (ℂ × ComplexPlane₂) (A × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (A × ComplexPlane₂))

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace in
private theorem SpecialPeriods.EllipticFilling.coveringManifold {A : Type*} [TopologicalSpace A]
    [ChartedSpace ℂ A] [IsManifold (modelWithCornersSelf ℂ ℂ) ω A] :
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (A × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := (modelWithCornersSelf ℂ ℂ)) (I' :=
      (modelWithCornersSelf ℂ ComplexPlane₂)) A ComplexPlane₂

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
public
theorem SpecialPeriods.EllipticFilling.localDiffeomorphAt_of_comp {E F K M N T : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup K] [NormedSpace ℂ K] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N] [TopologicalSpace T] [ChartedSpace K T] {q : M → N}
    {f : N → T} {x : M}
    (hq : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) ω q x)
    (hf :
      IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ K) ω (f ∘ q) x) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ F) (modelWithCornersSelf ℂ K) ω f (q x) := by
  have hx : hq.localInverse (q x) = x := hq.localInverse_left_inv hq.localInverse_mem_target
  have hf' :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ K) ω (f ∘ q)
      (hq.localInverse (q x)) := by
    rw [hx]
    exact hf
  have h := hq.localInverse_isLocalDiffeomorphAt.comp (K := modelWithCornersSelf ℂ K) (P := T) hf'
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq h
  filter_upwards [hq.localInverse_eventuallyEq_right] with y hy
  change f y = f (q (hq.localInverse y))
  rw [show q (hq.localInverse y) = y from hy]

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
private def
    SpecialPeriods.EllipticFilling.productPartialDiffeomorph {A B : Type*} [TopologicalSpace A]
    [ChartedSpace ℂ A] [TopologicalSpace B] [ChartedSpace ℂ B]
    (e : PartialDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) A B ω) :
    PartialDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (A × ComplexPlane₂) (B × ComplexPlane₂) ω
    where
  toPartialEquiv :=
    (e.toOpenPartialHomeomorph.prod (OpenPartialHomeomorph.refl ComplexPlane₂)).toPartialEquiv
  open_source := e.open_source.prod isOpen_univ
  open_target := e.open_target.prod isOpen_univ
  contMDiffOn_toFun := by
    rw [modelWithCornersSelf_prod]
    exact
      (e.contMDiffOn_toFun.comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)).prodMk
        contMDiff_snd.contMDiffOn
  contMDiffOn_invFun := by
    rw [modelWithCornersSelf_prod]
    exact
      (e.contMDiffOn_invFun.comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)).prodMk
        contMDiff_snd.contMDiffOn

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
private theorem SpecialPeriods.EllipticFilling.productMap_isLocalDiffeomorph {A B : Type*}
    [TopologicalSpace A] [ChartedSpace ℂ A] [TopologicalSpace B] [ChartedSpace ℂ B] {f : A → B}
    (hf : IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun x : A × ComplexPlane₂ => (f x.1, x.2)) := by
  intro x
  obtain ⟨e, hx, he⟩ := hf x.1
  refine ⟨productPartialDiffeomorph e, ⟨hx, Set.mem_univ _⟩, ?_⟩
  intro y hy
  exact Prod.ext (he hy.1) rfl

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
private def SpecialPeriods.EllipticFilling.periodFamilyMap {A B : Type*} [TopologicalSpace A]
    [ChartedSpace ℂ A] [TopologicalSpace B] [ChartedSpace ℂ B] (Q : HolomorphicPeriodMap ℂ A)
    (P : HolomorphicPeriodMap ℂ B) (f : A → B) : Q.TotalSpace → P.TotalSpace := fun x =>
  (f x.1, x.2)

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
private theorem
    SpecialPeriods.EllipticFilling.periodFamilyMap_cover {A B : Type*} [TopologicalSpace A]
    [ChartedSpace ℂ A] [TopologicalSpace B] [ChartedSpace ℂ B] (Q : HolomorphicPeriodMap ℂ A)
    (P : HolomorphicPeriodMap ℂ B) (f : A → B) (hperiod : ∀ a, Q.point a = P.point (f a))
    (x : A × ComplexPlane₂) :
    periodFamilyMap Q P f (Q.quotientMap x) = P.quotientMap (f x.1, x.2) := by
  apply Prod.ext
  · rfl
  · change
      standardLattice.mkQ ((Q.periodEquiv x.1).symm x.2) =
        standardLattice.mkQ ((P.periodEquiv (f x.1)).symm x.2)
    rw [show Q.periodEquiv x.1 = P.periodEquiv (f x.1) by
        simp only [HolomorphicPeriodMap.periodEquiv, hperiod] ]

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
private theorem SpecialPeriods.EllipticFilling.periodFamilyMap_isLocalDiffeomorph {A B : Type*}
    [TopologicalSpace A] [ChartedSpace ℂ A] [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ω A] [IsManifold (modelWithCornersSelf ℂ ℂ) ω B]
    (Q : HolomorphicPeriodMap ℂ A) (P : HolomorphicPeriodMap ℂ B) (f : A → B)
    (hperiod : ∀ a, Q.point a = P.point (f a))
    (hf : IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    letI := Q.totalChartedSpace
    letI := P.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (periodFamilyMap Q P f) := by
  let := Q.totalChartedSpace
  let := P.totalChartedSpace
  let := Q.coveringAction
  have hQ :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω Q.quotientMap :=
    CoveringQuotient.project_isLocalDiffeomorph Q.quotientCoveringMap Q.coveringAction_holomorphic
  have hP :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω P.quotientMap := by
    let := P.coveringAction
    exact
      CoveringQuotient.project_isLocalDiffeomorph P.quotientCoveringMap
        P.coveringAction_holomorphic
  intro y
  obtain ⟨x, rfl⟩ := Q.quotientMap_surjective y
  apply localDiffeomorphAt_of_comp (hQ x)
  have h :=
    (productMap_isLocalDiffeomorph hf x).comp (K := (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)))
      (P := P.TotalSpace) (hP (f x.1, x.2))
  exact
    isLocalDiffeomorphAt_congr_of_eventuallyEq h
      (Filter.Eventually.of_forall (periodFamilyMap_cover Q P f hperiod))

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
private def SpecialPeriods.EllipticFilling.restrictPeriods {B : Type*} [TopologicalSpace B]
    [ChartedSpace ℂ B] (P : HolomorphicPeriodMap ℂ B) (U : TopologicalSpace.Opens B) :
    HolomorphicPeriodMap ℂ U where
  point x := P.point x
  holomorphic_tau := P.holomorphic_tau.comp contMDiff_subtype_val
  holomorphic_mu := P.holomorphic_mu.comp contMDiff_subtype_val
  holomorphic_beta := P.holomorphic_beta.comp contMDiff_subtype_val

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
private def SpecialPeriods.EllipticFilling.periodFamilyOpen {B : Type*} [TopologicalSpace B]
    [ChartedSpace ℂ B] (P : HolomorphicPeriodMap ℂ B) (U : TopologicalSpace.Opens B) :
    TopologicalSpace.Opens P.TotalSpace :=
  ⟨P.projection ⁻¹' (U : Set B), U.isOpen.preimage continuous_fst⟩

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
private def SpecialPeriods.EllipticFilling.restrictFamilyMap {B : Type*} [TopologicalSpace B]
    [ChartedSpace ℂ B] (P : HolomorphicPeriodMap ℂ B) (U : TopologicalSpace.Opens B) :
    (restrictPeriods P U).TotalSpace → periodFamilyOpen P U := fun x => ⟨(x.1.1, x.2), x.1.2⟩

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
private theorem SpecialPeriods.EllipticFilling.restrictFamilyMap_bijective {B : Type*}
    [TopologicalSpace B] [ChartedSpace ℂ B] (P : HolomorphicPeriodMap ℂ B)
    (U : TopologicalSpace.Opens B) : Function.Bijective (restrictFamilyMap P U) := by
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    exact
      Prod.ext (Subtype.ext (congrArg (fun z : B × RealTorus₄ => z.1) he))
        (congrArg (fun z : B × RealTorus₄ => z.2) he)
  · intro y
    exact ⟨(⟨y.1.1, y.2⟩, y.1.2), rfl⟩

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
private theorem SpecialPeriods.EllipticFilling.restrictFamilyMap_isLocalDiffeomorph {B : Type*}
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold (modelWithCornersSelf ℂ ℂ) ω B]
    (P : HolomorphicPeriodMap ℂ B) (U : TopologicalSpace.Opens B) :
    letI := (restrictPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (restrictFamilyMap P U) := by
  let := (restrictPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  exact
    isLocalDiffeomorph_codRestrictOpens (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (periodFamilyMap_isLocalDiffeomorph (restrictPeriods P U) P Subtype.val (fun _ => rfl)
        (isLocalDiffeomorph_subtypeVal (modelWithCornersSelf ℂ ℂ) U))
      (periodFamilyOpen P U) (fun x => x.1.2)

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
private def
    SpecialPeriods.EllipticFilling.restrictFamilyBiholomorph {B : Type*} [TopologicalSpace B]
    [ChartedSpace ℂ B] [IsManifold (modelWithCornersSelf ℂ ℂ) ω B] (P : HolomorphicPeriodMap ℂ B)
    (U : TopologicalSpace.Opens B) :
    letI := (restrictPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (restrictPeriods P U).TotalSpace
      (periodFamilyOpen P U) ω := by
  let := (restrictPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  exact
    (restrictFamilyMap_isLocalDiffeomorph P U).diffeomorphOfBijective
      (restrictFamilyMap_bijective P U)

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
@[simp]
private theorem SpecialPeriods.EllipticFilling.restrictFamilyBiholomorph_symm_apply {B : Type*}
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold (modelWithCornersSelf ℂ ℂ) ω B]
    (P : HolomorphicPeriodMap ℂ B) (U : TopologicalSpace.Opens B) (x : periodFamilyOpen P U) :
    letI := (restrictPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    (restrictFamilyBiholomorph P U).symm x = (⟨x.1.1, x.2⟩, x.1.2) := by
  let := (restrictPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  apply (restrictFamilyBiholomorph P U).injective
  exact (restrictFamilyBiholomorph P U).apply_symm_apply x

private theorem SpecialPeriods.CuspGlobalOverlap.familyCovering
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup :=
  SpecialPeriods.triangleRegularProject_covering

private def SpecialPeriods.CuspGlobalOverlap.familyMap (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    C.Space → D.Space :=
  QuotientComparison.descend C D (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap)
    (SpecialPeriods.CuspFamily.logBaseToRegular_translate C.radius hrcap)
    SpecialPeriods.triangleTorusHomeomorph_cusp_zpow

@[simp]
private theorem
    SpecialPeriods.CuspGlobalOverlap.familyMap_quotient (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (x : C.TotalSpace) :
    familyMap C D hrcap (C.quotient x) =
      D.quotient (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap x.1, x.2) :=
  rfl

private theorem
    SpecialPeriods.CuspGlobalOverlap.familyMap_injective (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Function.Injective (familyMap C D hrcap) :=
  QuotientComparison.descend_injective C D
    (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap)
    (SpecialPeriods.CuspFamily.logBaseToRegular_translate C.radius hrcap)
    SpecialPeriods.triangleTorusHomeomorph_cusp_zpow
    (SpecialPeriods.CuspFamily.logBaseToRegular_injective C.radius hrcap)
    (logBaseToRegular_return C.radius hrcap)

private def SpecialPeriods.CuspGlobalOverlap.familyPatch (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    TopologicalSpace.Opens D.Space :=
  ⟨D.projection ⁻¹' (basePatch C.radius hrcap : Set SpecialPeriods.TriangleRegularQuotient),
    (basePatch C.radius hrcap).isOpen.preimage D.projection_continuous⟩

private theorem
    SpecialPeriods.CuspGlobalOverlap.familyMap_range (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Set.range (familyMap C D hrcap) = (familyPatch C D hrcap : Set D.Space) :=
  QuotientComparison.range_descend C D (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap)
    (SpecialPeriods.CuspFamily.logBaseToRegular_translate C.radius hrcap)
    SpecialPeriods.triangleTorusHomeomorph_cusp_zpow

private theorem
    SpecialPeriods.CuspGlobalOverlap.familyMap_mem_patch (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (x : C.Space) : familyMap C D hrcap x ∈ familyPatch C D hrcap := by
  change familyMap C D hrcap x ∈ (familyPatch C D hrcap : Set D.Space)
  rw [← familyMap_range]
  exact Set.mem_range_self x

private def SpecialPeriods.CuspGlobalOverlap.familyMapInto (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (x : C.Space) : familyPatch C D hrcap :=
  ⟨familyMap C D hrcap x, familyMap_mem_patch C D hrcap x⟩

private theorem SpecialPeriods.CuspGlobalOverlap.familyMapInto_bijective
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Function.Bijective (familyMapInto C D hrcap) := by
  constructor
  · intro x y h
    exact familyMap_injective C D hrcap (congrArg Subtype.val h)
  · intro y
    have hy : y.val ∈ Set.range (familyMap C D hrcap) := by
      rw [familyMap_range]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

end Mathoverflow1973

end
