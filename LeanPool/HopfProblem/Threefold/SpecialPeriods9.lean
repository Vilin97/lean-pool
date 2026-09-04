/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Uniformization.SpecialPeriods8
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Elliptic.Core4
import all LeanPool.HopfProblem.Foundations.FibreTopology
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Foundations.TwoOpenTransition
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods8

/-!
# Hopf problem: threefold · special periods 9

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

private abbrev SpecialPeriods.EllipticFilling.SpecialCentralSurface (j : Elliptic.Kind) :=
  Elliptic.Surface j (specialLocalData j).centralPeriod j.twist (Elliptic.mainTwist_admissible j)

private def SpecialPeriods.EllipticFilling.specialCentralInclusion (j : Elliptic.Kind) :
    SpecialCentralSurface j → SpecialFullFilling j :=
  (specialLocalData j).centralFibreInclusion j.twist (Elliptic.mainTwist_admissible j)

private theorem SpecialPeriods.EllipticFilling.specialCentralInclusion_isClosedEmbedding
    (j : Elliptic.Kind) : Topology.IsClosedEmbedding (specialCentralInclusion j) :=
  (specialLocalData j).centralFibreInclusion_isClosedEmbedding j.twist
    (Elliptic.mainTwist_admissible j)

private theorem SpecialPeriods.EllipticFilling.specialCentralInclusion_range (j : Elliptic.Kind) :
    Set.range (specialCentralInclusion j) =
      specialFullFillingProjection j ⁻¹' { Elliptic.discZero } :=
  (specialLocalData j).range_centralFibreInclusion j.twist (Elliptic.mainTwist_admissible j)

private def SpecialPeriods.EllipticFilling.specialCentralSurfaceIntoFilling (j : Elliptic.Kind) :
    ContinuousMap (SpecialCentralSurface j) (SpecialFullFilling j) :=
  (specialLocalData j).surfaceIntoFilling j.twist (Elliptic.mainTwist_admissible j)

private def SpecialPeriods.EllipticFilling.specialCentralSurfaceRetraction (j : Elliptic.Kind) :
    ContinuousMap (SpecialFullFilling j) (SpecialCentralSurface j) :=
  (specialLocalData j).fillingSurfaceRetraction j.twist (Elliptic.mainTwist_admissible j)

private def SpecialPeriods.EllipticFilling.specialCentralSurfaceStrongDeformationRetraction
    (j : Elliptic.Kind) :
    (ContinuousMap.id (SpecialFullFilling j)).HomotopyRel
      ((specialCentralSurfaceIntoFilling j).comp (specialCentralSurfaceRetraction j))
      (Set.range (specialCentralSurfaceIntoFilling j)) :=
  (specialLocalData j).fillingSurfaceStrongDeformationRetraction j.twist
    (Elliptic.mainTwist_admissible j)

private abbrev SpecialPeriods.EllipticFilling.SpecialCentralPeriodTorus (j : Elliptic.Kind) :=
  (specialLocalData j).centralPeriod.val.Torus

private def SpecialPeriods.EllipticFilling.specialCentralPeriodCover (j : Elliptic.Kind) :
    C(SpecialCentralPeriodTorus j, SpecialCentralSurface j) :=
  Elliptic.HigherHomology.periodCover j (specialLocalData j).centralPeriod j.twist
    (Elliptic.mainTwist_admissible j)

private def
    SpecialPeriods.EllipticFilling.specialCentralSurfaceHomologyCoordinates (j : Elliptic.Kind)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (SpecialCentralSurface j) n ≃ₗ[ℤ]
      (Fin (Elliptic.HigherHomology.ellipticBettiNumber n) → ℤ) :=
  Elliptic.HigherHomology.surfaceHomologyCoordinates j (specialLocalData j).centralPeriod n

private abbrev SpecialPeriods.Threefold.EllipticGeometry.LocalSpace (j : Elliptic.Kind) :=
  SpecialPeriods.Threefold.SpecialEllipticPiece j

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private def
    SpecialPeriods.Threefold.EllipticGeometry.parameter (j : Elliptic.Kind) (x : LocalSpace j) :
    ℂ :=
  SpecialPeriods.EllipticFilling.specialFullFillingProjection j x.val

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.EllipticGeometry.inclusion (j : Elliptic.Kind) :
    LocalSpace j → SpecialPeriods.Threefold.Space :=
  SpecialPeriods.Threefold.inclusion (Option.some (Option.some j))

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.EllipticGeometry.inclusion_openEmbedding (j : Elliptic.Kind) :
    Topology.IsOpenEmbedding (SpecialPeriods.Threefold.EllipticGeometry.inclusion j) :=
  SpecialPeriods.Threefold.inclusion_openEmbedding (Option.some (Option.some j))

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.inclusion_injective (j : Elliptic.Kind) :
    Function.Injective (SpecialPeriods.Threefold.EllipticGeometry.inclusion j) :=
  (inclusion_openEmbedding j).injective

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.inclusion_continuous (j : Elliptic.Kind) :
    Continuous (SpecialPeriods.Threefold.EllipticGeometry.inclusion j) :=
  (inclusion_openEmbedding j).continuous

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.inclusion_range (j : Elliptic.Kind) :
    Set.range (SpecialPeriods.Threefold.EllipticGeometry.inclusion j) =
      SpecialPeriods.Threefold.projection ⁻¹'
        (SpecialPeriods.Threefold.specialBaseCover.fillingPatch (Option.some j) :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  SpecialPeriods.Threefold.inclusion_range (Option.some (Option.some j))

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.EllipticGeometry.projection_inclusion (j : Elliptic.Kind)
    (x : LocalSpace j) :
    SpecialPeriods.Threefold.projection
        (SpecialPeriods.Threefold.EllipticGeometry.inclusion j x) =
      SpecialPeriods.Threefold.specialEllipticPieceProjectionToBase j x :=
  SpecialPeriods.Threefold.projection_inclusion (Option.some (Option.some j)) x

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.projection_inclusion_eq_point_iff
    (j : Elliptic.Kind) (x : LocalSpace j) :
    SpecialPeriods.Threefold.projection
          (SpecialPeriods.Threefold.EllipticGeometry.inclusion j x) =
        SpecialPeriods.Threefold.puncturePoint (Option.some j) ↔
      parameter j x = 0 := by
  rw [projection_inclusion]
  exact
    SpecialPeriods.Threefold.specialBaseCover.fillingEmbedding_eq_point_iff (Option.some j)
      (SpecialPeriods.EllipticFilling.pieceCoordinate SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
        SpecialPeriods.Threefold.specialBaseCover j x)

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private def
    SpecialPeriods.Threefold.EllipticGeometry.sphereValue (j : Elliptic.Kind) : RiemannSphere :=
  SpecialPeriods.Triangle.triangleSphereUniformization
    (SpecialPeriods.Threefold.puncturePoint (Option.some j))

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.projectionSphere_inclusion_eq_value_iff
    (j : Elliptic.Kind) (x : LocalSpace j) :
    SpecialPeriods.Threefold.projectionSphere
          (SpecialPeriods.Threefold.EllipticGeometry.inclusion j x) =
        sphereValue j ↔
      parameter j x = 0 :=
  SpecialPeriods.Triangle.triangleSphereUniformization.injective.eq_iff.trans
    (projection_inclusion_eq_point_iff j x)

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
@[simp]
private theorem SpecialPeriods.Threefold.EllipticGeometry.fullProjection_specialCentralInclusion
    (j : Elliptic.Kind) (x : SpecialPeriods.EllipticFilling.SpecialCentralSurface j) :
    SpecialPeriods.EllipticFilling.specialFullFillingProjection j
        (SpecialPeriods.EllipticFilling.specialCentralInclusion j x) =
      Elliptic.discZero := by
  have hx := Set.mem_range_self (f := SpecialPeriods.EllipticFilling.specialCentralInclusion j) x
  rw [SpecialPeriods.EllipticFilling.specialCentralInclusion_range] at hx
  exact hx

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
private def SpecialPeriods.Threefold.EllipticGeometry.pieceCentralInclusion (j : Elliptic.Kind) :
    SpecialPeriods.EllipticFilling.SpecialCentralSurface j → LocalSpace j := fun x =>
  ⟨SpecialPeriods.EllipticFilling.specialCentralInclusion j x,
    by
    change
      ‖(SpecialPeriods.EllipticFilling.specialFullFillingProjection j
              (SpecialPeriods.EllipticFilling.specialCentralInclusion j x) :
            ℂ)‖ <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)
    rw [fullProjection_specialCentralInclusion]
    change ‖(0 : ℂ)‖ < SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)
    simpa only [norm_zero] using
      SpecialPeriods.Threefold.specialBaseCover.radius_pos (Option.some j)⟩

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
@[simp]
private theorem SpecialPeriods.Threefold.EllipticGeometry.parameter_pieceCentralInclusion
    (j : Elliptic.Kind) (x : SpecialPeriods.EllipticFilling.SpecialCentralSurface j) :
    parameter j (pieceCentralInclusion j x) = 0 := by
  change
    (SpecialPeriods.EllipticFilling.specialFullFillingProjection j
          (SpecialPeriods.EllipticFilling.specialCentralInclusion j x) :
        ℂ) =
      0
  rw [fullProjection_specialCentralInclusion]
  rfl

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
private theorem SpecialPeriods.Threefold.EllipticGeometry.pieceCentralInclusion_continuous
    (j : Elliptic.Kind) : Continuous (pieceCentralInclusion j) :=
  (SpecialPeriods.EllipticFilling.specialCentralInclusion_isClosedEmbedding
        j).continuous.subtype_mk
    _

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
private theorem SpecialPeriods.Threefold.EllipticGeometry.pieceCentralInclusion_injective
    (j : Elliptic.Kind) : Function.Injective (pieceCentralInclusion j) := by
  intro x y hxy
  exact
    (SpecialPeriods.EllipticFilling.specialCentralInclusion_isClosedEmbedding j).injective
      (congrArg Subtype.val hxy)

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
private theorem SpecialPeriods.Threefold.EllipticGeometry.pieceCentralInclusion_range
    (j : Elliptic.Kind) : Set.range (pieceCentralInclusion j) = parameter j ⁻¹' {0} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change
      (SpecialPeriods.EllipticFilling.specialFullFillingProjection j
            (SpecialPeriods.EllipticFilling.specialCentralInclusion j a) :
          ℂ) =
        0
    rw [fullProjection_specialCentralInclusion]
    rfl
  · intro hx
    have hm : x.val ∈ Set.range (SpecialPeriods.EllipticFilling.specialCentralInclusion j) := by
      rw [SpecialPeriods.EllipticFilling.specialCentralInclusion_range]
      exact Subtype.ext hx
    obtain ⟨a, ha⟩ := hm
    exact ⟨a, Subtype.ext ha⟩

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
private def SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceInclusion (j : Elliptic.Kind) :
    SpecialPeriods.EllipticFilling.SpecialCentralSurface j → SpecialPeriods.Threefold.Space :=
  SpecialPeriods.Threefold.EllipticGeometry.inclusion j ∘ pieceCentralInclusion j

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
private theorem SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceInclusion_continuous
    (j : Elliptic.Kind) : Continuous (centralSurfaceInclusion j) :=
  (inclusion_continuous j).comp (pieceCentralInclusion_continuous j)

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
private theorem SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceInclusion_injective
    (j : Elliptic.Kind) : Function.Injective (centralSurfaceInclusion j) :=
  (SpecialPeriods.Threefold.EllipticGeometry.inclusion_injective j).comp
    (pieceCentralInclusion_injective j)

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
private theorem SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceInclusion_isClosedEmbedding
    (j : Elliptic.Kind) : Topology.IsClosedEmbedding (centralSurfaceInclusion j) :=
  (centralSurfaceInclusion_continuous j).isClosedEmbedding (centralSurfaceInclusion_injective j)

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
private theorem SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceInclusion_isEmbedding
    (j : Elliptic.Kind) : Topology.IsEmbedding (centralSurfaceInclusion j) :=
  (centralSurfaceInclusion_isClosedEmbedding j).isEmbedding

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
@[simp]
private theorem SpecialPeriods.Threefold.EllipticGeometry.projectionSphere_centralSurfaceInclusion
    (j : Elliptic.Kind) (x : SpecialPeriods.EllipticFilling.SpecialCentralSurface j) :
    SpecialPeriods.Threefold.projectionSphere (centralSurfaceInclusion j x) = sphereValue j :=
  (projectionSphere_inclusion_eq_value_iff j (pieceCentralInclusion j x)).mpr
    (parameter_pieceCentralInclusion j x)

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
private theorem SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceInclusion_range
    (j : Elliptic.Kind) :
    Set.range (centralSurfaceInclusion j) =
      SpecialPeriods.Threefold.projectionSphere ⁻¹' {sphereValue j} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact projectionSphere_centralSurfaceInclusion j x
  · intro hy
    have hyproj :
      SpecialPeriods.Threefold.projection y =
        SpecialPeriods.Threefold.puncturePoint (Option.some j) :=
      SpecialPeriods.Triangle.triangleSphereUniformization.injective hy
    have hm : y ∈ Set.range (SpecialPeriods.Threefold.EllipticGeometry.inclusion j) := by
      rw [inclusion_range]
      change
        SpecialPeriods.Threefold.projection y ∈
          SpecialPeriods.Threefold.specialBaseCover.fillingPatch (Option.some j)
      rw [hyproj]
      exact SpecialPeriods.Threefold.specialBaseCover.point_mem_fillingPatch (Option.some j)
    obtain ⟨x, rfl⟩ := hm
    have hx : x ∈ Set.range (pieceCentralInclusion j) := by
      rw [pieceCentralInclusion_range]
      exact (projectionSphere_inclusion_eq_value_iff j x).mp hy
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, rfl⟩

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
private def
    SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceFibreHomeomorph (j : Elliptic.Kind) :
    SpecialPeriods.EllipticFilling.SpecialCentralSurface j ≃ₜ
      (SpecialPeriods.Threefold.projectionSphere ⁻¹' {sphereValue j}) :=
  (centralSurfaceInclusion_isEmbedding j).toHomeomorph.trans
    (Homeomorph.setCongr (centralSurfaceInclusion_range j))

attribute [local instance] SpecialPeriods.Threefold.space_t2Space in
private theorem
    SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceFibreHomeomorph_symm_inclusion
    (j : Elliptic.Kind) (x : SpecialPeriods.Threefold.projectionSphere ⁻¹' {sphereValue j}) :
    centralSurfaceInclusion j ((centralSurfaceFibreHomeomorph j).symm x) =
      (x : SpecialPeriods.Threefold.Space) :=
  congrArg Subtype.val ((centralSurfaceFibreHomeomorph j).apply_symm_apply x)

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private abbrev SpecialPeriods.Threefold.EllipticGeometry.pieceFullDomain (j : Elliptic.Kind) :
    Set (SpecialPeriods.EllipticFilling.SpecialFullFilling j) :=
  SpecialPeriods.EllipticFilling.pieceDomain SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    SpecialPeriods.Threefold.specialBaseCover j

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private def SpecialPeriods.Threefold.EllipticGeometry.centralSurfaceIntoPiece (j : Elliptic.Kind) :
    C(SpecialPeriods.EllipticFilling.SpecialCentralSurface j, LocalSpace j) :=
  ⟨pieceCentralInclusion j, pieceCentralInclusion_continuous j⟩

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.fullCentralSurface_subset_piece
    (j : Elliptic.Kind) :
    Set.range (SpecialPeriods.EllipticFilling.specialCentralSurfaceIntoFilling j) ⊆
      pieceFullDomain j := by
  rintro _ ⟨a, rfl⟩
  exact (pieceCentralInclusion j a).property

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.fullCentralHomotopy_preserves_piece
    (j : Elliptic.Kind) (t : unitInterval)
    (x : SpecialPeriods.EllipticFilling.SpecialFullFilling j) (hx : x ∈ pieceFullDomain j) :
    SpecialPeriods.EllipticFilling.specialCentralSurfaceStrongDeformationRetraction j (t, x) ∈
      pieceFullDomain j :=
  (Elliptic.fillingRadial_projection_norm_le j j.twist (Elliptic.mainTwist_admissible j) t
        x).trans_lt
    hx

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private def SpecialPeriods.Threefold.EllipticGeometry.pieceSurfaceRetraction (j : Elliptic.Kind) :
    C(LocalSpace j, SpecialPeriods.EllipticFilling.SpecialCentralSurface j) :=
  restrictedRetraction (SpecialPeriods.EllipticFilling.specialCentralSurfaceRetraction j)
    (pieceFullDomain j)

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.EllipticGeometry.pieceSurfaceRetraction_comp_inclusion
    (j : Elliptic.Kind) :
    (pieceSurfaceRetraction j).comp (centralSurfaceIntoPiece j) = ContinuousMap.id _ :=
  restrictedRetraction_comp_inclusion
    (SpecialPeriods.EllipticFilling.specialCentralSurfaceIntoFilling j)
    (SpecialPeriods.EllipticFilling.specialCentralSurfaceRetraction j)
    ((SpecialPeriods.EllipticFilling.specialLocalData j).fillingSurfaceRetraction_comp_inclusion
      j.twist (Elliptic.mainTwist_admissible j))
    (pieceFullDomain j) (fullCentralSurface_subset_piece j)

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private def SpecialPeriods.Threefold.EllipticGeometry.pieceStrongDeformationRetraction
    (j : Elliptic.Kind) :
    (ContinuousMap.id (LocalSpace j)).HomotopyRel
      ((centralSurfaceIntoPiece j).comp (pieceSurfaceRetraction j))
      (Set.range (centralSurfaceIntoPiece j)) :=
  restrictedRetractionHomotopy (SpecialPeriods.EllipticFilling.specialCentralSurfaceIntoFilling j)
    (SpecialPeriods.EllipticFilling.specialCentralSurfaceRetraction j)
    (SpecialPeriods.EllipticFilling.specialCentralSurfaceStrongDeformationRetraction j)
    (pieceFullDomain j) (fullCentralSurface_subset_piece j)
    (fullCentralHomotopy_preserves_piece j)

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private def
    SpecialPeriods.Threefold.EllipticGeometry.pieceSurfaceHomotopyEquiv (j : Elliptic.Kind) :
    SpecialPeriods.EllipticFilling.SpecialCentralSurface j ≃ₕ LocalSpace j :=
  retractionHomotopyEquiv (centralSurfaceIntoPiece j) (pieceSurfaceRetraction j)
    (pieceSurfaceRetraction_comp_inclusion j) (pieceStrongDeformationRetraction j)

private theorem SpecialPeriods.EllipticAttachingMeridians.cast_id_map_mo1973_23351 {X : Type*}
    [TopologicalSpace X] {a b : X} (p : Path a b) :
    (Path.id.map p.continuous).cast p.source.symm p.target.symm = p := by
  ext t
  rfl

private structure
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare {X : Type*} [TopologicalSpace X]
    {a b : X} (p : Path a a) (q : Path b b) where
  map : C(unitInterval × unitInterval, X)
  initial : ∀ u, map (0, u) = p u
  final : ∀ u, map (1, u) = q u
  closed : ∀ t, map (t, 0) = map (t, 1)

private def SpecialPeriods.EllipticAttachingMeridians.LoopSquare.ofContinuous {X : Type*}
    [TopologicalSpace X] {a b : X} {p : Path a a} {q : Path b b}
    (L : unitInterval × unitInterval → X) (hL : Continuous L) (h₀ : ∀ u, L (0, u) = p u)
    (h₁ : ∀ u, L (1, u) = q u) (hc : ∀ t, L (t, 0) = L (t, 1)) :
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q
    where
  map := ⟨L, hL⟩
  initial := h₀
  final := h₁
  closed := hc

private def
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare.tail {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) : Path a b
    where
  toFun t := S.map (t, 0)
  continuous_toFun := S.map.continuous.comp (continuous_id.prodMk continuous_const)
  source' := (S.initial 0).trans p.source
  target' := (S.final 0).trans q.source

private def
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare.homotopy {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) :
    p.toContinuousMap.Homotopy q.toContinuousMap
    where
  toFun := S.map
  continuous_toFun := S.map.continuous
  map_zero_left := S.initial
  map_one_left := S.final

private theorem
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare.homotopy_evalAt_zero {X : Type*}
    [TopologicalSpace X] {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) :
    (S.homotopy.evalAt 0).cast p.source.symm q.source.symm = S.tail := by
  ext t
  rfl

private theorem SpecialPeriods.EllipticAttachingMeridians.LoopSquare.homotopy_evalAt_one {X : Type*}
    [TopologicalSpace X] {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) :
    (S.homotopy.evalAt 1).cast p.target.symm q.target.symm = S.tail := by
  ext t
  exact (S.closed t).symm

private theorem SpecialPeriods.EllipticAttachingMeridians.LoopSquare.homotopic_boundary {X : Type*}
    [TopologicalSpace X] {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) :
    (p.trans S.tail).Homotopic (S.tail.trans q) := by
  have h :=
    (Path.Homotopic.map_trans_evalAt S.homotopy Path.id).pathCast p.source.symm q.target.symm
  rw [Path.cast_trans (Path.id.map p.continuous) (S.homotopy.evalAt 1) p.source.symm p.target.symm
      q.target.symm,
    Path.cast_trans (S.homotopy.evalAt 0) (Path.id.map q.continuous) p.source.symm q.source.symm
      q.target.symm,
    SpecialPeriods.EllipticAttachingMeridians.cast_id_map_mo1973_23351 p,
    SpecialPeriods.EllipticAttachingMeridians.cast_id_map_mo1973_23351 q, S.homotopy_evalAt_zero,
    S.homotopy_evalAt_one] at h
  exact h

private theorem SpecialPeriods.EllipticAttachingMeridians.LoopSquare.homotopic_conjugate {X : Type*}
    [TopologicalSpace X] {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) :
    p.Homotopic (S.tail.trans (q.trans S.tail.symm)) := by
  have hcancel : ((p.trans S.tail).trans S.tail.symm).Homotopic p :=
    (Path.Homotopic.trans_assoc p S.tail S.tail.symm).trans
      (((Path.Homotopic.refl p).hcomp (Path.Homotopic.trans_symm S.tail)).trans
        (Path.Homotopic.trans_refl p))
  exact
    hcancel.symm.trans
      ((S.homotopic_boundary.hcomp (Path.Homotopic.refl S.tail.symm)).trans
        (Path.Homotopic.trans_assoc S.tail q S.tail.symm))

private theorem SpecialPeriods.EllipticAttachingMeridians.LoopSquare.quotient_conjugate {X : Type*}
    [TopologicalSpace X] {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) :
    Path.Homotopic.Quotient.mk p =
      (Path.Homotopic.Quotient.mk S.tail).trans
        ((Path.Homotopic.Quotient.mk q).trans (Path.Homotopic.Quotient.mk S.tail).symm) :=
  Path.Homotopic.Quotient.eq.mpr S.homotopic_conjugate

private structure SpecialPeriods.EllipticAttachingMeridians.LinearizationControl (f : ℂ → ℂ) where
  radius : ℝ
  radius_pos : 0 < radius
  derivative_ne_zero : deriv f 0 ≠ 0
  continuousOn : ContinuousOn f (Metric.ball 0 radius)
  error : ∀ z : ℂ, ‖z‖ < radius → ‖f z - f 0 - deriv f 0 * z‖ ≤ ‖deriv f 0‖ / 2 * ‖z‖
  image_small : ∀ z : ℂ, ‖z‖ < radius → ‖f z - f 0‖ < 1 / 2
  linear_small : ∀ z : ℂ, ‖z‖ < radius → ‖deriv f 0 * z‖ < 1 / 2

private theorem SpecialPeriods.EllipticAttachingMeridians.nonempty_linearizationControl {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hd : deriv f 0 ≠ 0) : Nonempty (LinearizationControl f) := by
  have hderiv := hf.differentiableAt.hasDerivAt
  have herr : ∀ᶠ z in 𝓝 (0 : ℂ), ‖f z - f 0 - deriv f 0 * z‖ ≤ ‖deriv f 0‖ / 2 * ‖z‖ := by
    simpa only [sub_zero, smul_eq_mul, mul_comm] using
      hderiv.isLittleO.bound (half_pos (norm_pos_iff.mpr hd))
  have hv : ∀ᶠ z in 𝓝 (0 : ℂ), ‖f z - f 0‖ < 1 / 2 := by
    have h : ContinuousAt (fun z : ℂ => ‖f z - f 0‖) 0 :=
      (hf.continuousAt.sub continuousAt_const).norm
    exact h.eventually (gt_mem_nhds (by simp : ‖f 0 - f 0‖ < (1 / 2 : ℝ)))
  have hl : ∀ᶠ z in 𝓝 (0 : ℂ), ‖deriv f 0 * z‖ < 1 / 2 := by
    have h : ContinuousAt (fun z : ℂ => ‖deriv f 0 * z‖) 0 :=
      (continuousAt_const.mul continuousAt_id).norm
    exact h.eventually (gt_mem_nhds (by simp : ‖deriv f 0 * (0 : ℂ)‖ < (1 / 2 : ℝ)))
  obtain ⟨r, hr, hs⟩ :=
    Metric.eventually_nhds_iff.mp (hf.eventually_continuousAt.and (herr.and (hv.and hl)))
  refine
    ⟨{  radius := r
        radius_pos := hr
        derivative_ne_zero := hd
        continuousOn := ?_
        error := ?_
        image_small := ?_
        linear_small := ?_ }⟩
  · intro z hz
    exact (hs (by simpa only [Metric.mem_ball] using hz)).1.continuousWithinAt
  · intro z hz
    exact (hs (by simpa only [dist_zero_right] using hz)).2.1
  · intro z hz
    exact (hs (by simpa only [dist_zero_right] using hz)).2.2.1
  · intro z hz
    exact (hs (by simpa only [dist_zero_right] using hz)).2.2.2

private def SpecialPeriods.EllipticAttachingMeridians.analyticLinearizationControl {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hd : deriv f 0 ≠ 0) : LinearizationControl f :=
  Classical.choice (nonempty_linearizationControl hf hd)

private def
    SpecialPeriods.EllipticAttachingMeridians.interpolate (f : ℂ → ℂ) (s : unitInterval) (z : ℂ) :
    ℂ :=
  (((1 - (s : ℝ) : ℝ) : ℂ) * f z) + ((s : ℝ) : ℂ) * (f 0 + deriv f 0 * z)

@[simp]
private theorem SpecialPeriods.EllipticAttachingMeridians.interpolate_zero (f : ℂ → ℂ) (z : ℂ) :
    interpolate f 0 z = f z := by simp [interpolate]

@[simp]
private theorem SpecialPeriods.EllipticAttachingMeridians.interpolate_one (f : ℂ → ℂ) (z : ℂ) :
    interpolate f 1 z = f 0 + deriv f 0 * z := by simp [interpolate]

private theorem SpecialPeriods.EllipticAttachingMeridians.interpolate_sub_linear (f : ℂ → ℂ)
    (s : unitInterval) (z : ℂ) :
    interpolate f s z - f 0 - deriv f 0 * z =
      (((1 - (s : ℝ) : ℝ) : ℂ) * (f z - f 0 - deriv f 0 * z)) := by
  simp only [interpolate, Complex.ofReal_sub, Complex.ofReal_one]
  ring

private theorem SpecialPeriods.EllipticAttachingMeridians.interpolate_sub_center (f : ℂ → ℂ)
    (s : unitInterval) (z : ℂ) :
    interpolate f s z - f 0 =
      (((1 - (s : ℝ) : ℝ) : ℂ) * (f z - f 0)) + ((s : ℝ) : ℂ) * (deriv f 0 * z) := by
  simp only [interpolate, Complex.ofReal_sub, Complex.ofReal_one]
  ring

private theorem SpecialPeriods.EllipticAttachingMeridians.norm_coe_interval_mo1973_23380
    (s : unitInterval) : ‖((s : ℝ) : ℂ)‖ = (s : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.property.1]

public
theorem SpecialPeriods.EllipticAttachingMeridians.norm_one_sub_coe_interval_mo1973_23381
    (s : unitInterval) : ‖(((1 - (s : ℝ) : ℝ) : ℂ))‖ = 1 - (s : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr s.property.2)]

private theorem SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.interpolate_error
    {f : ℂ → ℂ} (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f)
    (s : unitInterval) {z : ℂ} (hz : ‖z‖ < D.radius) :
    ‖SpecialPeriods.EllipticAttachingMeridians.interpolate f s z - f 0 - deriv f 0 * z‖ ≤
      ‖deriv f 0‖ / 2 * ‖z‖ := by
  rw [SpecialPeriods.EllipticAttachingMeridians.interpolate_sub_linear, norm_mul,
    SpecialPeriods.EllipticAttachingMeridians.norm_one_sub_coe_interval_mo1973_23381]
  calc
    (1 - (s : ℝ)) * ‖f z - f 0 - deriv f 0 * z‖ ≤ 1 * ‖f z - f 0 - deriv f 0 * z‖ :=
      mul_le_mul_of_nonneg_right (by linarith [s.property.1]) (norm_nonneg _)
    _ ≤ ‖deriv f 0‖ / 2 * ‖z‖ := by simpa only [one_mul] using D.error z hz

private theorem SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.interpolate_ne_center
    {f : ℂ → ℂ} (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f)
    (s : unitInterval) {z : ℂ} (hz : ‖z‖ < D.radius) (hz0 : z ≠ 0) :
    SpecialPeriods.EllipticAttachingMeridians.interpolate f s z ≠ f 0 := by
  intro h
  have he := D.interpolate_error s hz
  rw [h, sub_self, zero_sub, norm_neg, norm_mul] at he
  have hprod : 0 < ‖deriv f 0‖ * ‖z‖ :=
    mul_pos (norm_pos_iff.mpr D.derivative_ne_zero) (norm_pos_iff.mpr hz0)
  nlinarith

private theorem SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.interpolate_norm_le
    {f : ℂ → ℂ} (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f)
    (s : unitInterval) {z : ℂ} (hz : ‖z‖ < D.radius) :
    ‖SpecialPeriods.EllipticAttachingMeridians.interpolate f s z - f 0‖ ≤ 1 / 2 := by
  rw [SpecialPeriods.EllipticAttachingMeridians.interpolate_sub_center]
  calc
    ‖(((1 - (s : ℝ) : ℝ) : ℂ) * (f z - f 0)) + ((s : ℝ) : ℂ) * (deriv f 0 * z)‖ ≤
        ‖(((1 - (s : ℝ) : ℝ) : ℂ) * (f z - f 0))‖ + ‖((s : ℝ) : ℂ) * (deriv f 0 * z)‖ :=
      norm_add_le _ _
    _ = (1 - (s : ℝ)) * ‖f z - f 0‖ + (s : ℝ) * ‖deriv f 0 * z‖ := by
      rw [norm_mul, norm_mul,
        SpecialPeriods.EllipticAttachingMeridians.norm_one_sub_coe_interval_mo1973_23381,
        SpecialPeriods.EllipticAttachingMeridians.norm_coe_interval_mo1973_23380]
    _ ≤ (1 - (s : ℝ)) * (1 / 2) + (s : ℝ) * (1 / 2) :=
      (add_le_add
        (mul_le_mul_of_nonneg_left (D.image_small z hz).le (sub_nonneg.mpr s.property.2))
        (mul_le_mul_of_nonneg_left (D.linear_small z hz).le s.property.1))
    _ = 1 / 2 := by ring

private def SpecialPeriods.EllipticAttachingMeridians.center (b : Bool) : ℂ :=
  if b then 1 else 0

private def SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit (t : unitInterval) : ℂ :=
  Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (t : ℝ))

private theorem SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit_continuous :
    Continuous clockwiseUnit := by
  unfold clockwiseUnit
  fun_prop

private theorem SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit_ne_zero (t : unitInterval) :
    clockwiseUnit t ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
private theorem SpecialPeriods.EllipticAttachingMeridians.norm_clockwiseUnit (t : unitInterval) :
    ‖clockwiseUnit t‖ = 1 := by simp [clockwiseUnit, Complex.norm_exp]

@[simp]
private theorem
    SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit_zero : clockwiseUnit 0 = 1 := by
  simp [clockwiseUnit]

@[simp]
private theorem
    SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit_one : clockwiseUnit 1 = 1 := by
  change Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (1 : ℝ)) = 1
  rw [Complex.ofReal_one, mul_one, neg_mul]
  simpa only [zero_sub, Complex.exp_zero] using Complex.exp_periodic.sub_eq (0 : ℂ)

private def SpecialPeriods.EllipticAttachingMeridians.clockwiseCircle (b : Bool) (A : ℂ)
    (t : unitInterval) : ℂ :=
  SpecialPeriods.EllipticAttachingMeridians.center b + A * clockwiseUnit t

private theorem
    SpecialPeriods.EllipticAttachingMeridians.clockwiseCircle_continuous (b : Bool) (A : ℂ) :
    Continuous (clockwiseCircle b A) :=
  continuous_const.add (continuous_const.mul clockwiseUnit_continuous)

@[simp]
private theorem SpecialPeriods.EllipticAttachingMeridians.clockwiseCircle_zero (b : Bool) (A : ℂ) :
    clockwiseCircle b A 0 = SpecialPeriods.EllipticAttachingMeridians.center b + A := by
  simp [clockwiseCircle]

@[simp]
private theorem SpecialPeriods.EllipticAttachingMeridians.clockwiseCircle_one (b : Bool) (A : ℂ) :
    clockwiseCircle b A 1 = SpecialPeriods.EllipticAttachingMeridians.center b + A := by
  simp [clockwiseCircle]

private theorem SpecialPeriods.EllipticAttachingMeridians.center_add_mem_twicePuncturedPlaneDomain
    (b : Bool) {z : ℂ} (hz : z ≠ 0) (hn : ‖z‖ < 1) :
    SpecialPeriods.EllipticAttachingMeridians.center b + z ∈
      SpecialPeriods.Triangle.twicePuncturedPlaneDomain := by
  have hz₁ : z ≠ 1 := by
    intro h
    rw [h, NormOneClass.norm_one] at hn
    exact (lt_irrefl 1) hn
  have hzneg : z ≠ -1 := by
    intro h
    rw [h, norm_neg, NormOneClass.norm_one] at hn
    exact (lt_irrefl 1) hn
  change
    SpecialPeriods.EllipticAttachingMeridians.center b + z ≠ 0 ∧
      SpecialPeriods.EllipticAttachingMeridians.center b + z ≠ 1
  cases b with
  | false =>
    simpa only [SpecialPeriods.EllipticAttachingMeridians.center, Bool.false_eq_true, ↓reduceIte,
      zero_add] using And.intro hz hz₁
  | true =>
    change 1 + z ≠ 0 ∧ 1 + z ≠ 1
    constructor
    · intro h
      apply hzneg
      calc
        z = (1 + z) - 1 := by ring
        _ = -1 := by rw [h, zero_sub]
    · intro h
      exact hz (add_left_cancel (h.trans (add_zero 1).symm))

private theorem SpecialPeriods.EllipticAttachingMeridians.clockwiseCircle_mem (b : Bool) (A : ℂ)
    (hA : A ≠ 0) (hAn : ‖A‖ < 1) (t : unitInterval) :
    clockwiseCircle b A t ∈ SpecialPeriods.Triangle.twicePuncturedPlaneDomain := by
  apply center_add_mem_twicePuncturedPlaneDomain b
  · exact mul_ne_zero hA (clockwiseUnit_ne_zero t)
  · simpa only [norm_mul, norm_clockwiseUnit, mul_one] using hAn

private def
    SpecialPeriods.EllipticAttachingMeridians.circleBasepoint (b : Bool) (A : ℂ) (hA : A ≠ 0)
    (hAn : ‖A‖ < 1) : SpecialPeriods.Triangle.TwicePuncturedPlane :=
  ⟨SpecialPeriods.EllipticAttachingMeridians.center b + A,
    center_add_mem_twicePuncturedPlaneDomain b hA hAn⟩

private def
    SpecialPeriods.EllipticAttachingMeridians.clockwiseCirclePath (b : Bool) (A : ℂ) (hA : A ≠ 0)
    (hAn : ‖A‖ < 1) : Path (circleBasepoint b A hA hAn) (circleBasepoint b A hA hAn)
    where
  toFun t := ⟨clockwiseCircle b A t, clockwiseCircle_mem b A hA hAn t⟩
  continuous_toFun := (clockwiseCircle_continuous b A).subtype_mk _
  source' := Subtype.ext (clockwiseCircle_zero b A)
  target' := Subtype.ext (clockwiseCircle_one b A)

private def SpecialPeriods.EllipticAttachingMeridians.anchor (b : Bool) : ℂ :=
  if b then -(1 / 2) else 1 / 2

private theorem
    SpecialPeriods.EllipticAttachingMeridians.anchor_ne_zero (b : Bool) : anchor b ≠ 0 := by
  cases b <;> norm_num [anchor]

private theorem SpecialPeriods.EllipticAttachingMeridians.norm_anchor_lt_one (b : Bool) :
    ‖anchor b‖ < 1 := by cases b <;> norm_num [anchor, norm_div]

private def SpecialPeriods.EllipticAttachingMeridians.fixedClockwiseMeridian (b : Bool) :
    Path SpecialPeriods.Triangle.meridianBasepoint SpecialPeriods.Triangle.meridianBasepoint :=
  (if b then SpecialPeriods.Triangle.positiveMeridianOne
    else SpecialPeriods.Triangle.positiveMeridianZero).symm

private theorem SpecialPeriods.EllipticAttachingMeridians.positiveTurn_symm_mo1973_23503
    (t : unitInterval) :
    Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (unitInterval.symm t : ℝ)) = clockwiseUnit t := by
  rw [unitInterval.coe_symm_eq]
  have he :
    (2 * Real.pi : ℂ) * Complex.I * ((1 - (t : ℝ) : ℝ) : ℂ) =
      -(2 * Real.pi : ℂ) * Complex.I * (t : ℝ) + 2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_periodic]
  rfl

private theorem SpecialPeriods.EllipticAttachingMeridians.fixedClockwiseMeridian_coe (b : Bool)
    (t : unitInterval) : (fixedClockwiseMeridian b t : ℂ) = clockwiseCircle b (anchor b) t := by
  cases b with
  |
    false =>
    change (SpecialPeriods.Triangle.positiveMeridianZero (unitInterval.symm t) : ℂ) = _
    rw [SpecialPeriods.Triangle.positiveMeridianZero_apply, positiveTurn_symm_mo1973_23503]
    simp [clockwiseCircle, SpecialPeriods.EllipticAttachingMeridians.center, anchor]
  |
    true =>
    change (SpecialPeriods.Triangle.positiveMeridianOne (unitInterval.symm t) : ℂ) = _
    rw [SpecialPeriods.Triangle.positiveMeridianOne_apply, positiveTurn_symm_mo1973_23503]
    simp [clockwiseCircle, SpecialPeriods.EllipticAttachingMeridians.center, anchor,
      sub_eq_add_neg]

private theorem
    SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.interpolate_mem {f : ℂ → ℂ}
    (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f) (b : Bool)
    (hc : f 0 = SpecialPeriods.EllipticAttachingMeridians.center b) (s : unitInterval) {z : ℂ}
    (hz : ‖z‖ < D.radius) (hz0 : z ≠ 0) :
    SpecialPeriods.EllipticAttachingMeridians.interpolate f s z ∈
      SpecialPeriods.Triangle.twicePuncturedPlaneDomain := by
  have hn : ‖SpecialPeriods.EllipticAttachingMeridians.interpolate f s z - f 0‖ < 1 :=
    (D.interpolate_norm_le s hz).trans_lt (by norm_num)
  have hm :=
    SpecialPeriods.EllipticAttachingMeridians.center_add_mem_twicePuncturedPlaneDomain b
      (sub_ne_zero.mpr (D.interpolate_ne_center s hz hz0)) hn
  have he :
    SpecialPeriods.EllipticAttachingMeridians.center b +
        (SpecialPeriods.EllipticAttachingMeridians.interpolate f s z - f 0) =
      SpecialPeriods.EllipticAttachingMeridians.interpolate f s z := by
    rw [← hc]
    ring
  rwa [he] at hm

private theorem
    SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.parameterCircle_norm_lt
    {f : ℂ → ℂ} (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f) (A : ℂ)
    (hAr : ‖A‖ < D.radius) (t : unitInterval) :
    ‖A * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit t‖ < D.radius := by
  simpa only [norm_mul, SpecialPeriods.EllipticAttachingMeridians.norm_clockwiseUnit,
    mul_one] using hAr

private theorem
    SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.parameterCircle_ne_zero
    (A : ℂ) (hA : A ≠ 0) (t : unitInterval) :
    A * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit t ≠ 0 :=
  mul_ne_zero hA (SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit_ne_zero t)

private def SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.analyticCircleBasepoint
    {f : ℂ → ℂ} (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f) (b : Bool)
    (hc : f 0 = SpecialPeriods.EllipticAttachingMeridians.center b) (A : ℂ) (hA : A ≠ 0)
    (hAr : ‖A‖ < D.radius) : SpecialPeriods.Triangle.TwicePuncturedPlane :=
  ⟨f A, by
    simpa only [SpecialPeriods.EllipticAttachingMeridians.interpolate_zero] using
      D.interpolate_mem b hc 0 hAr hA⟩

private theorem SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.analyticCircle_mem
    {f : ℂ → ℂ} (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f) (b : Bool)
    (hc : f 0 = SpecialPeriods.EllipticAttachingMeridians.center b) (A : ℂ) (hA : A ≠ 0)
    (hAr : ‖A‖ < D.radius) (t : unitInterval) :
    f (A * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit t) ∈
      SpecialPeriods.Triangle.twicePuncturedPlaneDomain := by
  simpa only [SpecialPeriods.EllipticAttachingMeridians.interpolate_zero] using
    D.interpolate_mem b hc 0 (D.parameterCircle_norm_lt A hAr t) (parameterCircle_ne_zero A hA t)

private theorem
    SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.analyticCircle_continuous
    {f : ℂ → ℂ} (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f) (A : ℂ)
    (hAr : ‖A‖ < D.radius) :
    Continuous
      (fun t : unitInterval =>
        f (A * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit t)) :=
  D.continuousOn.comp_continuous
    (continuous_const.mul SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit_continuous)
    (fun t => by
      rw [Metric.mem_ball, dist_zero_right]
      exact D.parameterCircle_norm_lt A hAr t)

private def
    SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.analyticCirclePath {f : ℂ → ℂ}
    (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f) (b : Bool)
    (hc : f 0 = SpecialPeriods.EllipticAttachingMeridians.center b) (A : ℂ) (hA : A ≠ 0)
    (hAr : ‖A‖ < D.radius) :
    Path (D.analyticCircleBasepoint b hc A hA hAr) (D.analyticCircleBasepoint b hc A hA hAr)
    where
  toFun
    t :=
    ⟨f (A * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit t),
      D.analyticCircle_mem b hc A hA hAr t⟩
  continuous_toFun := (D.analyticCircle_continuous A hAr).subtype_mk _
  source' := Subtype.ext (by simp [analyticCircleBasepoint])
  target' := Subtype.ext (by simp [analyticCircleBasepoint])

private theorem
    SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.linearCoefficient_ne_zero
    {f : ℂ → ℂ} (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f) (A : ℂ)
    (hA : A ≠ 0) : deriv f 0 * A ≠ 0 :=
  mul_ne_zero D.derivative_ne_zero hA

private theorem
  SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.linearCoefficient_norm_lt_one
    {f : ℂ → ℂ} (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f) (A : ℂ)
    (hAr : ‖A‖ < D.radius) : ‖deriv f 0 * A‖ < 1 :=
  (D.linear_small A hAr).trans (by norm_num)

private def SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.analyticCircleSquare
    {f : ℂ → ℂ} (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f) (b : Bool)
    (hc : f 0 = SpecialPeriods.EllipticAttachingMeridians.center b) (A : ℂ) (hA : A ≠ 0)
    (hAr : ‖A‖ < D.radius) :
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare (D.analyticCirclePath b hc A hA hAr)
      (SpecialPeriods.EllipticAttachingMeridians.clockwiseCirclePath b (deriv f 0 * A)
        (D.linearCoefficient_ne_zero A hA) (D.linearCoefficient_norm_lt_one A hAr)) := by
  let L : unitInterval × unitInterval → ℂ := fun tu =>
    SpecialPeriods.EllipticAttachingMeridians.interpolate f tu.1
      (A * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit tu.2)
  have hfc :
    Continuous
      (fun tu : unitInterval × unitInterval =>
        f (A * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit tu.2)) :=
    (D.analyticCircle_continuous A hAr).comp continuous_snd
  have hL : Continuous L := by
    have ht : Continuous (fun tu : unitInterval × unitInterval => (tu.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hu :
      Continuous
        (fun tu : unitInterval × unitInterval =>
          A * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit tu.2) :=
      continuous_const.mul
        (SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit_continuous.comp continuous_snd)
    exact
      ((Complex.continuous_ofReal.comp (continuous_const.sub ht)).mul hfc).add
        ((Complex.continuous_ofReal.comp ht).mul (continuous_const.add (continuous_const.mul hu)))
  refine
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare.ofContinuous
      (fun tu =>
        ⟨L tu,
          D.interpolate_mem b hc tu.1 (D.parameterCircle_norm_lt A hAr tu.2)
            (parameterCircle_ne_zero A hA tu.2)⟩)
      (hL.subtype_mk _) ?_ ?_ ?_
  · intro u
    apply Subtype.ext
    exact SpecialPeriods.EllipticAttachingMeridians.interpolate_zero f _
  · intro u
    apply Subtype.ext
    change
      SpecialPeriods.EllipticAttachingMeridians.interpolate f 1
          (A * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit u) =
        SpecialPeriods.EllipticAttachingMeridians.center b +
          (deriv f 0 * A) * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit u
    rw [SpecialPeriods.EllipticAttachingMeridians.interpolate_one, hc, mul_assoc]
  · intro t
    apply Subtype.ext
    change
      SpecialPeriods.EllipticAttachingMeridians.interpolate f t
          (A * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit 0) =
        SpecialPeriods.EllipticAttachingMeridians.interpolate f t
          (A * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit 1)
    rw [SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit_zero,
      SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit_one]

private def SpecialPeriods.EllipticAttachingMeridians.coefficientInterpolation (d a : ℂ)
    (s : unitInterval) : ℂ :=
  Complex.exp (((1 - (s : ℝ) : ℝ) : ℂ) * Complex.log d + ((s : ℝ) : ℂ) * Complex.log a)

private theorem
    SpecialPeriods.EllipticAttachingMeridians.coefficientInterpolation_continuous (d a : ℂ) :
    Continuous (coefficientInterpolation d a) := by
  unfold coefficientInterpolation
  exact
    Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp (continuous_const.sub continuous_subtype_val)).mul
            continuous_const).add
        ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const))

@[simp]
private theorem SpecialPeriods.EllipticAttachingMeridians.coefficientInterpolation_zero (d a : ℂ)
    (hd : d ≠ 0) : coefficientInterpolation d a 0 = d := by
  simpa [coefficientInterpolation] using Complex.exp_log hd

@[simp]
private theorem SpecialPeriods.EllipticAttachingMeridians.coefficientInterpolation_one (d a : ℂ)
    (ha : a ≠ 0) : coefficientInterpolation d a 1 = a := by
  simpa [coefficientInterpolation] using Complex.exp_log ha

private theorem SpecialPeriods.EllipticAttachingMeridians.coefficientInterpolation_ne_zero (d a : ℂ)
    (s : unitInterval) : coefficientInterpolation d a s ≠ 0 :=
  Complex.exp_ne_zero _

private theorem
    SpecialPeriods.EllipticAttachingMeridians.coefficientInterpolation_norm_lt_one (d a : ℂ)
    (s : unitInterval) (hd : d ≠ 0) (ha : a ≠ 0) (hdnorm : ‖d‖ < 1) (hanorm : ‖a‖ < 1) :
    ‖coefficientInterpolation d a s‖ < 1 := by
  have hdlog : Real.log ‖d‖ < 0 := Real.log_neg (norm_pos_iff.mpr hd) hdnorm
  have halog : Real.log ‖a‖ < 0 := Real.log_neg (norm_pos_iff.mpr ha) hanorm
  rw [coefficientInterpolation, Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    MulZeroClass.zero_mul, sub_zero, Complex.log_re]
  by_cases hs : (s : ℝ) = 0
  · simpa [hs] using hdlog
  · exact
      add_neg_of_nonpos_of_neg
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr s.property.2) hdlog.le)
        (mul_neg_of_pos_of_neg (lt_of_le_of_ne s.property.1 (Ne.symm hs)) halog)

private def SpecialPeriods.EllipticAttachingMeridians.clockwiseCircleSquare (b : Bool) (A : ℂ)
    (hA : A ≠ 0) (hAn : ‖A‖ < 1) :
    LoopSquare (clockwiseCirclePath b A hA hAn) (fixedClockwiseMeridian b)
    where
  map :=
    { toFun
        st :=
        ⟨clockwiseCircle b (coefficientInterpolation A (anchor b) st.1) st.2,
          clockwiseCircle_mem b _ (coefficientInterpolation_ne_zero A (anchor b) st.1)
            (coefficientInterpolation_norm_lt_one A (anchor b) st.1 hA (anchor_ne_zero b) hAn
              (norm_anchor_lt_one b))
            st.2⟩
      continuous_toFun :=
        (continuous_const.add
              (((coefficientInterpolation_continuous A (anchor b)).comp continuous_fst).mul
                (clockwiseUnit_continuous.comp continuous_snd))).subtype_mk
          _ }
  initial
    t := by
    apply Subtype.ext
    change clockwiseCircle b (coefficientInterpolation A (anchor b) 0) t = clockwiseCircle b A t
    rw [coefficientInterpolation_zero A (anchor b) hA]
  final
    t := by
    apply Subtype.ext
    change
      clockwiseCircle b (coefficientInterpolation A (anchor b) 1) t =
        (fixedClockwiseMeridian b t : ℂ)
    rw [coefficientInterpolation_one A (anchor b) (anchor_ne_zero b)]
    exact (fixedClockwiseMeridian_coe b t).symm
  closed
    s := by
    apply Subtype.ext
    exact
      (clockwiseCircle_zero b (coefficientInterpolation A (anchor b) s)).trans
        (clockwiseCircle_one b (coefficientInterpolation A (anchor b) s)).symm

private def SpecialPeriods.EllipticAttachingMeridians.LoopSquare.postcompose {X : Type*}
    [TopologicalSpace X] {a b : X} {p : Path a a} {q : Path b b} {Y : Type*} [TopologicalSpace Y]
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (f : X → Y)
    (hf : Continuous f) :
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare (p.map hf) (q.map hf)
    where
  map := ⟨fun z => f (S.map z), hf.comp S.map.continuous⟩
  initial u := congrArg f (S.initial u)
  final u := congrArg f (S.final u)
  closed t := congrArg f (S.closed t)

private def
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare.trans {X : Type*} [TopologicalSpace X]
    {a b c : X} {p : Path a a} {q : Path b b} {r : Path c c}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q)
    (T : SpecialPeriods.EllipticAttachingMeridians.LoopSquare q r) :
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare p r
    where
  map := (S.homotopy.trans T.homotopy).toContinuousMap
  initial := (S.homotopy.trans T.homotopy).map_zero_left
  final := (S.homotopy.trans T.homotopy).map_one_left
  closed
    t := by
    change (S.homotopy.trans T.homotopy) (t, 0) = (S.homotopy.trans T.homotopy) (t, 1)
    simp only [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · exact S.closed _
    · exact T.closed _

private theorem SpecialPeriods.EllipticAttachingMeridians.LoopSquare.homotopic_whisker_conjugate
    {X : Type*} [TopologicalSpace X] {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (τ : Path b a) :
    (τ.trans (p.trans τ.symm)).Homotopic
      ((τ.trans S.tail).trans (q.trans (τ.trans S.tail).symm)) := by
  apply Path.Homotopic.Quotient.eq.mp
  simp only [Path.trans_symm, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  rw [S.quotient_conjugate]
  simp only [Path.Homotopic.Quotient.trans_assoc]

end Mathoverflow1973

end
