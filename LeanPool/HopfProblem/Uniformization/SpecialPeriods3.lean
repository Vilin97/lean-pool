/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.TwoAffineCharts
public import LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Foundations.LocalOrbitQuotient
import all LeanPool.HopfProblem.Foundations.TwoAffineCharts
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2

/-!
# Hopf problem: uniformization · special periods 3

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

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticLocalDiscHomeomorph (j : Elliptic.Kind) :
    EllipticNeighborhoodQuotient j ≃ₜ SpecialPeriods.Disc := by
  letI := ellipticNeighborhoodAction j
  exact
    SpecialPeriods.TriangleQuotientPower.orbitDiscHomeomorph j
      (ellipticNeighborhoodChart j).toHomeomorph (ellipticStabilizerGenerator j)
      (ellipticStabilizer_eq_generator_pow j) (ellipticNeighborhoodChart_generator j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticLocalDiscHomeomorph_mk (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    ellipticLocalDiscHomeomorph j
        (LocalOrbitQuotient.localProjection (ellipticStabilizer j) (ellipticNeighborhood j)
          (ellipticNeighborhood_mapsTo j) z) =
      Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z) :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticImageDiscHomeomorph (j : Elliptic.Kind) :
    ellipticNeighborhoodImage j ≃ₜ SpecialPeriods.Disc :=
  (ellipticNeighborhoodQuotientHomeomorph j).symm.trans (ellipticLocalDiscHomeomorph j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticImageDiscHomeomorph_projection (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    ellipticImageDiscHomeomorph j
        (LocalOrbitQuotient.imageProjection (G := SpecialPeriods.TriangleGroup)
          (ellipticNeighborhood j) z) =
      Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z) := by
  let q :=
    LocalOrbitQuotient.localProjection (ellipticStabilizer j) (ellipticNeighborhood j)
      (ellipticNeighborhood_mapsTo j) z
  have he :
    ellipticNeighborhoodQuotientHomeomorph j q =
      LocalOrbitQuotient.imageProjection (G := SpecialPeriods.TriangleGroup)
        (ellipticNeighborhood j) z :=
    rfl
  change ellipticLocalDiscHomeomorph j ((ellipticNeighborhoodQuotientHomeomorph j).symm _) = _
  rw [← he, Homeomorph.symm_apply_apply]
  exact ellipticLocalDiscHomeomorph_mk j z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticOrbitParametrization (j : Elliptic.Kind) :
    OpenPartialHomeomorph SpecialPeriods.Disc SpecialPeriods.TriangleOrbitSpace :=
  (ellipticImageDiscHomeomorph j).symm.toOpenPartialHomeomorph.trans
    ((ellipticNeighborhoodImage j).openPartialHomeomorphSubtypeCoe
      ⟨⟨ellipticOrbitCenter j, ellipticOrbitCenter_mem_neighborhoodImage j⟩⟩)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticOrbitParametrization_source (j : Elliptic.Kind) :
    (ellipticOrbitParametrization j).source = Set.univ := by simp [ellipticOrbitParametrization]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticOrbitParametrization_target (j : Elliptic.Kind) :
    (ellipticOrbitParametrization j).target = ellipticNeighborhoodImage j := by
  simp [ellipticOrbitParametrization]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticOrbitParametrization_power (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    ellipticOrbitParametrization j
        (Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z)) =
      SpecialPeriods.triangleOrbitProjection z := by
  change
    ((ellipticImageDiscHomeomorph j).symm
          (Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z)) :
        SpecialPeriods.TriangleOrbitSpace) =
      SpecialPeriods.triangleOrbitProjection z
  rw [← ellipticImageDiscHomeomorph_projection j z]
  exact
    congrArg (fun q : ellipticNeighborhoodImage j => (q : SpecialPeriods.TriangleOrbitSpace))
      ((ellipticImageDiscHomeomorph j).symm_apply_apply
        (show ellipticNeighborhoodImage j from
          LocalOrbitQuotient.imageProjection (G := SpecialPeriods.TriangleGroup)
            (ellipticNeighborhood j) z))

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticFullChart (j : Elliptic.Kind) :
    OpenPartialHomeomorph SpecialPeriods.TriangleOrbitSpace ℂ :=
  (ellipticOrbitParametrization j).symm.trans
    (SpecialPeriods.unitDisc.openPartialHomeomorphSubtypeCoe ⟨SpecialPeriods.discZero⟩)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticFullChart_source (j : Elliptic.Kind) :
    (ellipticFullChart j).source = ellipticNeighborhoodImage j := by simp [ellipticFullChart]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticFullChart_target (j : Elliptic.Kind) :
    (ellipticFullChart j).target = SpecialPeriods.unitDisc := by simp [ellipticFullChart]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticFullChart_projection (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    ellipticFullChart j (SpecialPeriods.triangleOrbitProjection z) =
      normalizedCayleyBranch (ellipticCenter j) (ellipticNeighborhoodRadius j) j.order z := by
  have he :
    (ellipticOrbitParametrization j).symm (SpecialPeriods.triangleOrbitProjection z) =
      Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z) := by
    rw [← ellipticOrbitParametrization_power j z]
    exact (ellipticOrbitParametrization j).left_inv (by simp)
  change
    ((ellipticOrbitParametrization j).symm (SpecialPeriods.triangleOrbitProjection z) : ℂ) = _
  rw [he, Elliptic.discPower_coe, ellipticNeighborhoodChart_val]
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticFullChart_center_mem_source (j : Elliptic.Kind) :
    ellipticOrbitCenter j ∈ (ellipticFullChart j).source := by
  rw [ellipticFullChart_source]
  exact ellipticOrbitCenter_mem_neighborhoodImage j

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticFullChart_center (j : Elliptic.Kind) :
    ellipticFullChart j (ellipticOrbitCenter j) = 0 := by
  have he := ellipticFullChart_projection j (ellipticNeighborhoodCenter j)
  simpa only [ellipticOrbitCenter, ellipticNeighborhoodCenter, normalizedCayleyBranch,
    normalizedCayley, cayleyCoordinate, sub_self, zero_div, zero_pow j.order_pos.ne'] using he

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticFullChart_other_not_mem_source (j : Elliptic.Kind) :
    ellipticOrbitCenter (ellipticOtherKind j) ∉ (ellipticFullChart j).source := by
  rw [ellipticFullChart_source]
  exact ellipticOtherOrbitCenter_not_mem_neighborhoodImage j

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticFullChart_pullback_eventuallyEq (j : Elliptic.Kind)
    (g : SpecialPeriods.TriangleGroup) {z : ℍ}
    (hz : SpecialPeriods.triangleGeometricRepresentation g z ∈ ellipticNeighborhood j) :
    (ellipticFullChart j ∘ SpecialPeriods.triangleOrbitProjection) =ᶠ[𝓝 z]
      (normalizedCayleyBranch (ellipticCenter j) (ellipticNeighborhoodRadius j) j.order ∘
        SpecialPeriods.triangleGeometricRepresentation g) := by
  have hU :
    ∀ᶠ w in 𝓝 z, SpecialPeriods.triangleGeometricRepresentation g w ∈ ellipticNeighborhood j :=
    (SpecialPeriods.triangleGeometricRepresentation_holomorphic g).continuous.continuousAt
      ((ellipticNeighborhood j).isOpen.mem_nhds hz)
  filter_upwards [hU] with w hw
  change ellipticFullChart j (SpecialPeriods.triangleOrbitProjection w) = _
  rw [← SpecialPeriods.triangleOrbitProjection_smul g w]
  exact ellipticFullChart_projection j ⟨SpecialPeriods.triangleGeometricRepresentation g w, hw⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticFullChart_exists_lift (j : Elliptic.Kind) {z : ℍ}
    (hz : SpecialPeriods.triangleOrbitProjection z ∈ (ellipticFullChart j).source) :
    ∃ g : SpecialPeriods.TriangleGroup,
      SpecialPeriods.triangleGeometricRepresentation g z ∈ ellipticNeighborhood j := by
  rw [ellipticFullChart_source] at hz
  obtain ⟨w, hw, he⟩ := hz
  obtain ⟨g, hg⟩ := (SpecialPeriods.triangleOrbitProjection_eq_iff w z).mp he
  exact ⟨g, hg ▸ hw⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticFullChart_pullback_holomorphic (j : Elliptic.Kind) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (ellipticFullChart j ∘ SpecialPeriods.triangleOrbitProjection)
      (SpecialPeriods.triangleOrbitProjection ⁻¹' (ellipticFullChart j).source) := by
  intro z hz
  obtain ⟨g, hg⟩ := ellipticFullChart_exists_lift j hz
  have hf :=
    (normalizedCayleyBranch_holomorphic (ellipticCenter j) (ellipticNeighborhoodRadius j)
          (ellipticNeighborhoodRadius_pos j).ne' j.order).comp
      (SpecialPeriods.triangleGeometricRepresentation_holomorphic g)
  exact
    (hf.contMDiffAt.congr_of_eventuallyEq
        (ellipticFullChart_pullback_eventuallyEq j g hg)).contMDiffWithinAt

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticFullChart_pullback_isLocalDiffeomorphAt
    (j : Elliptic.Kind) {z : ℍ}
    (hz : SpecialPeriods.triangleOrbitProjection z ∈ (ellipticFullChart j).source)
    (hcenter : SpecialPeriods.triangleOrbitProjection z ≠ ellipticOrbitCenter j) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      (ellipticFullChart j ∘ SpecialPeriods.triangleOrbitProjection) z := by
  obtain ⟨g, hg⟩ := ellipticFullChart_exists_lift j hz
  have hgc : SpecialPeriods.triangleGeometricRepresentation g z ≠ ellipticCenter j := by
    intro h
    apply hcenter
    rw [← SpecialPeriods.triangleOrbitProjection_smul g z, h]
    rfl
  have hf :=
    ((SpecialPeriods.triangleGeometricBiholomorph g).isLocalDiffeomorph z).comp (K := 𝓘(ℂ)) (P :=
      ℂ)
      (normalizedCayleyBranch_isLocalDiffeomorphAt (ellipticCenter j)
        (SpecialPeriods.triangleGeometricRepresentation g z) (ellipticNeighborhoodRadius j)
        (ellipticNeighborhoodRadius_pos j).ne' j.order j.order_pos hgc)
  exact
    isLocalDiffeomorphAt_congr_of_eventuallyEq hf (ellipticFullChart_pullback_eventuallyEq j g hg)

private abbrev SpecialPeriods.TriangleOrbitChartIndex :=
  TriangleRegularQuotient ⊕ Elliptic.Kind

private def SpecialPeriods.triangleOrbitChart :
    TriangleOrbitChartIndex → OpenPartialHomeomorph TriangleOrbitSpace ℂ
  | .inl x => regularFullChart x
  | .inr j => Triangle.ellipticFullChart j

private theorem SpecialPeriods.triangleOrbitChart_cover (x : TriangleOrbitSpace) :
    ∃ i, x ∈ (triangleOrbitChart i).source := by
  by_cases h₁ : x = triangleOrbitCenterOne
  · subst x
    exact ⟨.inr .three, Triangle.ellipticFullChart_center_mem_source .three⟩
  by_cases h₂ : x = triangleOrbitCenterTwo
  · subst x
    exact ⟨.inr .four, Triangle.ellipticFullChart_center_mem_source .four⟩
  obtain ⟨r, hr⟩ :=
    exists_regularFullChart x ((triangleOrbitRegularDomain_mem_iff x).mpr ⟨h₁, h₂⟩)
  exact ⟨.inl r, hr⟩

private theorem SpecialPeriods.triangleOrbitChart_center_unique (j : Elliptic.Kind)
    (i : TriangleOrbitChartIndex)
    (hi : Triangle.ellipticOrbitCenter j ∈ (triangleOrbitChart i).source) : i = .inr j := by
  cases i with
  | inl
    x =>
    have h := (triangleOrbitRegularDomain_mem_iff _).mp (regularFullChart_source_subset x hi)
    cases j
    · exact (h.1 rfl).elim
    · exact (h.2 rfl).elim
  | inr k =>
    cases j <;> cases k
    · rfl
    · exact (Triangle.ellipticFullChart_other_not_mem_source .four hi).elim
    · exact (Triangle.ellipticFullChart_other_not_mem_source .three hi).elim
    · rfl

private def SpecialPeriods.triangleOrbitAtlasData :
    BranchedQuotientAtlas.Data (E := ℂ) triangleOrbitProjection TriangleOrbitChartIndex
    where
  chart := triangleOrbitChart
  cover := triangleOrbitChart_cover
  continuous_project := triangleOrbitProjection_continuous
  pullback_contMDiff
    i := by
    cases i with
    | inl x => exact regularFullChart_pullback_holomorphic x
    | inr j => exact Triangle.ellipticFullChart_pullback_holomorphic j
  overlap_lift i j hij z
    hz := by
    obtain ⟨a, ha⟩ := triangleOrbitProjection_surjective ((triangleOrbitChart i).symm z)
    have hsource : triangleOrbitProjection a ∈ (triangleOrbitChart i).source := by
      rw [ha]
      exact (triangleOrbitChart i).map_target hz.1
    refine ⟨a, ha, ?_⟩
    cases i with
    | inl r => exact regularFullChart_pullback_isLocalDiffeomorphAt r hsource
    | inr k =>
      apply Triangle.ellipticFullChart_pullback_isLocalDiffeomorphAt k hsource
      intro h
      have hcritical : Triangle.ellipticOrbitCenter k ∈ (triangleOrbitChart j).source := by
        rw [← h, ha]
        exact hz.2
      exact hij (triangleOrbitChart_center_unique k j hcritical).symm

@[instance_reducible]
private def SpecialPeriods.triangleOrbitChartedSpace : ChartedSpace ℂ TriangleOrbitSpace :=
  triangleOrbitAtlasData.chartedSpace

private theorem SpecialPeriods.triangleOrbit_isManifold :
    letI := triangleOrbitChartedSpace
    IsManifold 𝓘(ℂ) ω TriangleOrbitSpace :=
  triangleOrbitAtlasData.isManifold

private theorem SpecialPeriods.triangleOrbitChart_mem_atlas (i : TriangleOrbitChartIndex) :
    letI := triangleOrbitChartedSpace
    triangleOrbitChart i ∈ atlas ℂ TriangleOrbitSpace :=
  triangleOrbitAtlasData.chart_mem_atlas i

private theorem SpecialPeriods.triangleOrbitProjection_holomorphic :
    letI := triangleOrbitChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection :=
  triangleOrbitAtlasData.contMDiff_project

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.instIsManifold2 : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace :=
  triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
private def SpecialPeriods.triangleOrbitCoordinatePartial (i : TriangleOrbitChartIndex) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace ℂ ω
    where
  toPartialEquiv := (triangleOrbitChart i).toPartialEquiv
  open_source := (triangleOrbitChart i).open_source
  open_target := (triangleOrbitChart i).open_target
  contMDiffOn_toFun :=
    contMDiffOn_of_mem_maximalAtlas
      (StructureGroupoid.subset_maximalAtlas _ (triangleOrbitChart_mem_atlas i))
  contMDiffOn_invFun :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (StructureGroupoid.subset_maximalAtlas _ (triangleOrbitChart_mem_atlas i))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
private theorem SpecialPeriods.triangleOrbitProjection_isLocalDiffeomorphAt_of_regular {z : ℍ}
    (hz : z ∈ triangleRegularLocus) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection z := by
  obtain ⟨r, hr⟩ :=
    exists_regularFullChart (triangleOrbitProjection z)
      ((triangleOrbitProjection_mem_regularDomain_iff z).mpr hz)
  have hf := regularFullChart_pullback_isLocalDiffeomorphAt r hr
  have hinv :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (regularFullChart r).symm
      (regularFullChart r (triangleOrbitProjection z)) :=
    (triangleOrbitCoordinatePartial (.inl r)).symm.isLocalDiffeomorphAt _ _ _
      ((regularFullChart r).map_source hr)
  have hcomp := hf.comp (K := 𝓘(ℂ)) (P := TriangleOrbitSpace) hinv
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp
  have hU : ∀ᶠ w in 𝓝 z, triangleOrbitProjection w ∈ (regularFullChart r).source :=
    triangleOrbitProjection_continuous.continuousAt ((regularFullChart r).open_source.mem_nhds hr)
  exact hU.mono fun w hw => ((regularFullChart r).left_inv hw).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
private theorem SpecialPeriods.triangleOrbitProjection_isLocalDiffeomorphAt_of_not_elliptic {z : ℍ}
    (h₁ : triangleOrbitProjection z ≠ triangleOrbitCenterOne)
    (h₂ : triangleOrbitProjection z ≠ triangleOrbitCenterTwo) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection z :=
  triangleOrbitProjection_isLocalDiffeomorphAt_of_regular
    ((triangleOrbitProjection_mem_regularDomain_iff z).mp
      ((triangleOrbitRegularDomain_mem_iff _).mpr ⟨h₁, h₂⟩))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
private theorem SpecialPeriods.triangleRegularToOrbit_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularToOrbit := by
  apply CoveringQuotient.contMDiff_of_comp triangleRegularProject_covering 𝓘(ℂ) ω
  have hf :=
    triangleOrbitProjection_holomorphic.comp
      (contMDiff_subtype_val (U := triangleRegularDomain) (I := 𝓘(ℂ)) (n := ω))
  convert hf using 1
  funext z
  exact triangleRegularToOrbit_project z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
private theorem SpecialPeriods.triangleRegularOrbitHomeomorph_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularOrbitHomeomorph := by
  intro x
  have he :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun y : TriangleRegularQuotient =>
          (triangleRegularOrbitHomeomorph y : TriangleOrbitSpace))
        x ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularOrbitHomeomorph x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (triangleRegularToOrbit_holomorphic x)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
private def SpecialPeriods.triangleRegularFullProjection :
    TriangleRegularPoint → triangleOrbitRegularDomain := fun z =>
  ⟨triangleOrbitProjection z, (triangleOrbitProjection_mem_regularDomain_iff z).mpr z.property⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
private theorem SpecialPeriods.triangleRegularFullProjection_eq :
    triangleRegularFullProjection = triangleRegularOrbitHomeomorph ∘ triangleRegularProject := by
  funext z
  apply Subtype.ext
  exact (triangleRegularToOrbit_project z).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
private theorem SpecialPeriods.triangleRegularFullProjection_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularFullProjection := by
  intro z
  exact
    isLocalDiffeomorphAt_restrictOpens 𝓘(ℂ) 𝓘(ℂ)
      (triangleOrbitProjection_isLocalDiffeomorphAt_of_regular z.property) triangleRegularDomain
      triangleOrbitRegularDomain
      (fun w hw => (triangleOrbitProjection_mem_regularDomain_iff w).mpr hw) z.property

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
private theorem SpecialPeriods.triangleRegularFullProjection_surjective :
    Function.Surjective triangleRegularFullProjection := by
  rw [triangleRegularFullProjection_eq]
  exact triangleRegularOrbitHomeomorph.surjective.comp triangleRegularProject_surjective

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
private theorem SpecialPeriods.triangleRegularOrbitHomeomorph_symm_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularOrbitHomeomorph.symm := by
  apply
    contMDiff_of_comp_localDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 𝓘(ℂ)
      triangleRegularFullProjection_isLocalDiffeomorph triangleRegularFullProjection_surjective
  have he :
    triangleRegularOrbitHomeomorph.symm ∘ triangleRegularFullProjection =
      triangleRegularProject := by
    rw [triangleRegularFullProjection_eq]
    funext z
    exact triangleRegularOrbitHomeomorph.symm_apply_apply (triangleRegularProject z)
  rw [he]
  exact triangleRegularProject_holomorphic

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
private def SpecialPeriods.triangleRegularOrbitBiholomorph :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleRegularQuotient triangleOrbitRegularDomain ω
    where
  toEquiv := triangleRegularOrbitHomeomorph.toEquiv
  contMDiff_toFun := triangleRegularOrbitHomeomorph_holomorphic
  contMDiff_invFun := triangleRegularOrbitHomeomorph_symm_holomorphic

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem
    SpecialPeriods.Triangle.cuspImageProjection_isLocalDiffeomorph (Y : ℝ) (hY : width ≤ Y) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (cuspImageProjection Y) := by
  intro z
  exact
    isLocalDiffeomorphAt_restrictOpens 𝓘(ℂ) 𝓘(ℂ)
      (SpecialPeriods.triangleOrbitProjection_isLocalDiffeomorphAt_of_regular
        (horodisc_subset_triangleRegularLocus Y hY z.property))
      (horodisc Y) (cuspImage Y) (fun w hw => ⟨w, hw, rfl⟩) z.property

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem SpecialPeriods.Triangle.cuspImageHomeomorph_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspImageHomeomorph Y hY) := by
  apply
    contMDiff_of_comp_localDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 𝓘(ℂ)
      (cuspImageProjection_isLocalDiffeomorph Y hY) (cuspImageProjection_surjective Y)
  have he : (cuspImageHomeomorph Y hY) ∘ cuspImageProjection Y = cuspQHorodisc Y := by
    funext z
    exact cuspImageHomeomorph_mk Y hY z
  rw [he]
  exact cuspQHorodisc_holomorphic Y

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem
    SpecialPeriods.Triangle.cuspImageHomeomorph_symm_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspImageHomeomorph Y hY).symm := by
  apply
    contMDiff_of_comp_localDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 𝓘(ℂ) (cuspQHorodisc_isLocalDiffeomorph Y)
      (cuspQHorodisc_surjective Y (width_pos.le.trans hY))
  have he : (cuspImageHomeomorph Y hY).symm ∘ cuspQHorodisc Y = cuspImageProjection Y := by
    funext z
    exact cuspImageHomeomorph_symm_q Y hY z
  rw [he]
  exact (cuspImageProjection_isLocalDiffeomorph Y hY).contMDiff

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private def SpecialPeriods.Triangle.cuspImageBiholomorph (Y : ℝ) (hY : width ≤ Y) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (cuspImage Y) (puncturedCuspBall Y) ω
    where
  toEquiv := (cuspImageHomeomorph Y hY).toEquiv
  contMDiff_toFun := cuspImageHomeomorph_holomorphic Y hY
  contMDiff_invFun := cuspImageHomeomorph_symm_holomorphic Y hY

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
@[simp]
private theorem SpecialPeriods.Triangle.cuspImageBiholomorph_toHomeomorph (Y : ℝ) (hY : width ≤ Y) :
    (cuspImageBiholomorph Y hY).toHomeomorph = cuspImageHomeomorph Y hY := by
  ext x
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem SpecialPeriods.Triangle.cuspImageNonemptyForChart_mo1973_16605 (Y : ℝ) :
    Nonempty (cuspImage Y) := by
  obtain ⟨z, hz⟩ := horodisc_nonempty Y
  exact ⟨cuspImageProjection Y ⟨z, hz⟩⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private def SpecialPeriods.Triangle.cuspImagePartialDiffeomorph (Y : ℝ) (hY : width ≤ Y) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleOrbitSpace ℂ ω :=
  (opensInclusionPartialDiffeomorph 𝓘(ℂ) (cuspImage Y)
        (cuspImageNonemptyForChart_mo1973_16605 Y)).symm.trans
    ((cuspImageBiholomorph Y hY).toPartialDiffeomorph.trans
      (opensInclusionPartialDiffeomorph 𝓘(ℂ) (puncturedCuspBall Y)
        ((cuspImageNonemptyForChart_mo1973_16605 Y).map (cuspImageHomeomorph Y hY))))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
@[simp]
private theorem
    SpecialPeriods.Triangle.cuspImagePartialDiffeomorph_source (Y : ℝ) (hY : width ≤ Y) :
    (cuspImagePartialDiffeomorph Y hY).source =
      (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace) := by
  simp [cuspImagePartialDiffeomorph, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem SpecialPeriods.Triangle.cuspImagePartialDiffeomorph_apply (Y : ℝ) (hY : width ≤ Y)
    (x : SpecialPeriods.TriangleOrbitSpace) (hx : x ∈ cuspImage Y) :
    cuspImagePartialDiffeomorph Y hY x = (cuspImageHomeomorph Y hY ⟨x, hx⟩ : ℂ) := by
  let e :=
    (cuspImage Y).openPartialHomeomorphSubtypeCoe (cuspImageNonemptyForChart_mo1973_16605 Y)
  have he : e.symm x = ⟨x, hx⟩ := e.left_inv (Set.mem_univ (⟨x, hx⟩ : cuspImage Y))
  change (cuspImageBiholomorph Y hY (e.symm x) : ℂ) = _
  rw [he]
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem
    SpecialPeriods.Triangle.cuspImagePartialDiffeomorph_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (cuspImagePartialDiffeomorph Y hY)
      (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace) := by
  simpa only [cuspImagePartialDiffeomorph_source] using
    (cuspImagePartialDiffeomorph Y hY).contMDiffOn

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem SpecialPeriods.instIsManifold3 : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace :=
  triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
private theorem SpecialPeriods.Triangle.cuspFullChart_pullback_eqOn (Y : ℝ) (hY : width ≤ Y) :
    Set.EqOn (cuspFullChart Y hY ∘ SpecialPeriods.triangleOpenInclusion)
      (cuspImagePartialDiffeomorph Y hY) (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace) := by
  intro q hq
  simp only [Function.comp_apply, cuspFullChart_openInclusion Y hY q hq,
    cuspImagePartialDiffeomorph_apply Y hY q hq]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
private theorem
    SpecialPeriods.Triangle.cuspFullChart_pullback_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (cuspFullChart Y hY ∘ SpecialPeriods.triangleOpenInclusion)
      (SpecialPeriods.triangleOpenInclusion ⁻¹' (cuspFullChart Y hY).source) := by
  rw [cuspFullChart_source, cuspNeighborhood_preimage]
  exact (cuspImagePartialDiffeomorph_holomorphic Y hY).congr (cuspFullChart_pullback_eqOn Y hY)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
private theorem SpecialPeriods.Triangle.cuspFullChart_pullback_isLocalDiffeomorphAt (Y : ℝ)
    (hY : width ≤ Y) (q : SpecialPeriods.TriangleOrbitSpace)
    (hq : SpecialPeriods.triangleOpenInclusion q ∈ (cuspFullChart Y hY).source) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspFullChart Y hY ∘ SpecialPeriods.triangleOpenInclusion)
      q := by
  have hmem : q ∈ cuspImage Y := (openInclusion_mem_cuspNeighborhood Y q).mp hq
  refine ⟨cuspImagePartialDiffeomorph Y hY, ?_, ?_⟩
  · rw [cuspImagePartialDiffeomorph_source]
    exact hmem
  · rw [cuspImagePartialDiffeomorph_source]
    exact cuspFullChart_pullback_eqOn Y hY

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
private def SpecialPeriods.triangleCompactifiedAtlasData :
    BranchedQuotientAtlas.Data (E := ℂ) triangleOpenInclusion (Option TriangleOrbitSpace) :=
  OnePointAtlas.data (Triangle.cuspFullChart Triangle.width le_rfl)
    (Triangle.cuspPoint_mem_cuspNeighborhood Triangle.width)
    (Triangle.cuspFullChart_pullback_holomorphic Triangle.width le_rfl)
    (Triangle.cuspFullChart_pullback_isLocalDiffeomorphAt Triangle.width le_rfl)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
@[instance_reducible]
private def SpecialPeriods.triangleCompactifiedChartedSpace :
    ChartedSpace ℂ TriangleCompactifiedOrbitSpace :=
  triangleCompactifiedAtlasData.chartedSpace

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
private theorem SpecialPeriods.triangleCompactified_isManifold :
    letI := triangleCompactifiedChartedSpace
    IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactifiedAtlasData.isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
private theorem SpecialPeriods.triangleCompactified_cuspChart_mem_atlas :
    letI := triangleCompactifiedChartedSpace
    Triangle.cuspFullChart Triangle.width le_rfl ∈ atlas ℂ TriangleCompactifiedOrbitSpace :=
  triangleCompactifiedAtlasData.chart_mem_atlas Option.none

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
private theorem SpecialPeriods.triangleOpenInclusion_holomorphic :
    letI := triangleCompactifiedChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleOpenInclusion :=
  triangleCompactifiedAtlasData.contMDiff_project

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
private def SpecialPeriods.triangleCompactifiedProjection : ℍ → TriangleCompactifiedOrbitSpace :=
  triangleOpenInclusion ∘ triangleOrbitProjection

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
private theorem SpecialPeriods.triangleCompactified_cuspChart_holomorphic :
    letI := triangleCompactifiedChartedSpace
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (Triangle.cuspFullChart Triangle.width le_rfl)
      (Triangle.cuspNeighborhood Triangle.width : Set TriangleCompactifiedOrbitSpace) := by
  let := triangleCompactifiedChartedSpace
  let := triangleCompactified_isManifold
  exact
    contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas triangleCompactified_cuspChart_mem_atlas)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
private theorem SpecialPeriods.triangleCompactified_cuspChart_symm_holomorphic :
    letI := triangleCompactifiedChartedSpace
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (Triangle.cuspFullChart Triangle.width le_rfl).symm
      (Metric.ball 0 (Triangle.cuspRadius Triangle.width)) := by
  let := triangleCompactifiedChartedSpace
  let := triangleCompactified_isManifold
  exact
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas triangleCompactified_cuspChart_mem_atlas)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.instIsManifold4 : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace :=
  triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 in
private theorem SpecialPeriods.instIsManifold5 : IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactified_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
private def SpecialPeriods.triangleCompactifiedOldCoordinatePartial (q : TriangleOrbitSpace) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace ℂ ω
    where
  toPartialEquiv := (OnePointAtlas.oldChart q).toPartialEquiv
  open_source := (OnePointAtlas.oldChart q).open_source
  open_target := (OnePointAtlas.oldChart q).open_target
  contMDiffOn_toFun :=
    contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas
        (triangleCompactifiedAtlasData.chart_mem_atlas (Option.some q)))
  contMDiffOn_invFun :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas
        (triangleCompactifiedAtlasData.chart_mem_atlas (Option.some q)))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
private theorem SpecialPeriods.triangleOpenInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω triangleOpenInclusion := by
  intro q
  have hq : triangleOpenInclusion q ∈ (OnePointAtlas.oldChart q).source :=
    (OnePointAtlas.coe_mem_oldChart_source q q).mpr (mem_chart_source ℂ q)
  have hpull := OnePointAtlas.oldChart_pullback_localDiffeomorph q q hq
  have hinv :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (OnePointAtlas.oldChart q).symm
      (OnePointAtlas.oldChart q (triangleOpenInclusion q)) :=
    (triangleCompactifiedOldCoordinatePartial q).symm.isLocalDiffeomorphAt _ _ _
      ((OnePointAtlas.oldChart q).map_source hq)
  have hcomp := hpull.comp (K := 𝓘(ℂ)) (P := TriangleCompactifiedOrbitSpace) hinv
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp
  have hU : ∀ᶠ x in 𝓝 q, triangleOpenInclusion x ∈ (OnePointAtlas.oldChart q).source :=
    OnePoint.continuous_coe.continuousAt ((OnePointAtlas.oldChart q).open_source.mem_nhds hq)
  exact hU.mono fun x hx => ((OnePointAtlas.oldChart q).left_inv hx).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
private def SpecialPeriods.triangleCuspComplement :
    TopologicalSpace.Opens TriangleCompactifiedOrbitSpace :=
  ⟨{ triangleCuspPoint }ᶜ, isClosed_singleton.isOpen_compl⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
private def SpecialPeriods.triangleOpenInclusionToComplement (q : TriangleOrbitSpace) :
    triangleCuspComplement :=
  ⟨triangleOpenInclusion q, triangleOpenInclusion_ne_cusp q⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
private theorem SpecialPeriods.triangleOpenInclusionToComplement_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω triangleOpenInclusionToComplement :=
  isLocalDiffeomorph_codRestrictOpens 𝓘(ℂ) 𝓘(ℂ) triangleOpenInclusion_isLocalDiffeomorph
    triangleCuspComplement triangleOpenInclusion_ne_cusp

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
private theorem SpecialPeriods.triangleOpenInclusionToComplement_bijective :
    Function.Bijective triangleOpenInclusionToComplement := by
  constructor
  · intro x y h
    exact OnePoint.coe_injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨q, hq⟩ := OnePoint.ne_infty_iff_exists.mp x.property
    exact ⟨q, Subtype.ext hq⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
private def SpecialPeriods.triangleOpenComplementBiholomorph :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace triangleCuspComplement ω :=
  triangleOpenInclusionToComplement_isLocalDiffeomorph.diffeomorphOfBijective
    triangleOpenInclusionToComplement_bijective

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
@[simp]
private theorem
    SpecialPeriods.triangleOpenComplementBiholomorph_symm_apply (q : triangleCuspComplement) :
    triangleOpenInclusion (triangleOpenComplementBiholomorph.symm q) = q :=
  congrArg Subtype.val (triangleOpenComplementBiholomorph.apply_symm_apply q)

private def SpecialPeriods.triangleCompactifiedCenterOne : TriangleCompactifiedOrbitSpace :=
  triangleOpenInclusion triangleOrbitCenterOne

private def SpecialPeriods.triangleCompactifiedCenterTwo : TriangleCompactifiedOrbitSpace :=
  triangleOpenInclusion triangleOrbitCenterTwo

private theorem SpecialPeriods.triangleCompactifiedCenterOne_ne_centerTwo :
    triangleCompactifiedCenterOne ≠ triangleCompactifiedCenterTwo := by
  intro h
  exact triangleOrbitCenterOne_ne_centerTwo (OnePoint.coe_injective h)

private def SpecialPeriods.Triangle.ellipticCompactifiedCenter (j : Elliptic.Kind) :
    SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.triangleOpenInclusion (ellipticOrbitCenter j)

@[simp]
private theorem SpecialPeriods.Triangle.ellipticCompactifiedCenter_ne_cusp (j : Elliptic.Kind) :
    ellipticCompactifiedCenter j ≠ SpecialPeriods.triangleCuspPoint :=
  SpecialPeriods.triangleOpenInclusion_ne_cusp (ellipticOrbitCenter j)

private theorem SpecialPeriods.Triangle.normalizedCayley_analyticAt (a z : ℍ) (r : ℝ) (hr : r ≠ 0) :
    AnalyticAt ℂ (normalizedCayley a r ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
  (cayleyCoordinate_analyticAt a z).div analyticAt_const (Complex.ofReal_ne_zero.mpr hr)

private theorem SpecialPeriods.Triangle.normalizedCayley_order_center (a : ℍ) (r : ℝ) (hr : r ≠ 0) :
    analyticOrderAt (normalizedCayley a r ∘ UpperHalfPlane.ofComplex) (a : ℂ) = 1 := by
  have hc : AnalyticAt ℂ (fun _ : ℂ => (r : ℂ)⁻¹) (a : ℂ) := analyticAt_const
  have hcorder : analyticOrderAt (fun _ : ℂ => (r : ℂ)⁻¹) (a : ℂ) = 0 :=
    hc.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Complex.ofReal_ne_zero.mpr hr))
  have he :
    normalizedCayley a r ∘ UpperHalfPlane.ofComplex =
      (cayleyCoordinate a ∘ UpperHalfPlane.ofComplex) * (fun _ : ℂ => (r : ℂ)⁻¹) := by
    funext z
    exact div_eq_mul_inv _ _
  rw [he, analyticOrderAt_mul (cayleyCoordinate_analyticAt a a) hc, cayleyCoordinate_order_center,
    hcorder, add_zero]

private theorem
    SpecialPeriods.Triangle.normalizedCayleyBranch_analyticAt (a z : ℍ) (r : ℝ) (hr : r ≠ 0)
    (m : ℕ) : AnalyticAt ℂ (normalizedCayleyBranch a r m ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
  (normalizedCayley_analyticAt a z r hr).pow m

private theorem
    SpecialPeriods.Triangle.normalizedCayleyBranch_order_center (a : ℍ) (r : ℝ) (hr : r ≠ 0)
    (m : ℕ) :
    analyticOrderAt (normalizedCayleyBranch a r m ∘ UpperHalfPlane.ofComplex) (a : ℂ) =
      (m : ℕ∞) := by
  change analyticOrderAt ((normalizedCayley a r ∘ UpperHalfPlane.ofComplex) ^ m) (a : ℂ) = _
  rw [analyticOrderAt_pow (normalizedCayley_analyticAt a a r hr),
    normalizedCayley_order_center a r hr]
  simp

private theorem
    SpecialPeriods.Triangle.ellipticFullChart_complexGerm_eventuallyEq (j : Elliptic.Kind) :
    (ellipticFullChart j ∘
        SpecialPeriods.triangleOrbitProjection ∘
          UpperHalfPlane.ofComplex) =ᶠ[𝓝 (ellipticCenter j : ℂ)]
      (normalizedCayleyBranch (ellipticCenter j) (ellipticNeighborhoodRadius j) j.order ∘
        UpperHalfPlane.ofComplex) := by
  have hU : IsOpen (UpperHalfPlane.coe '' (ellipticNeighborhood j : Set ℍ)) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ (ellipticNeighborhood j).isOpen
  have hcenter :
    (ellipticCenter j : ℂ) ∈ UpperHalfPlane.coe '' (ellipticNeighborhood j : Set ℍ) :=
    ⟨ellipticCenter j, ellipticCenter_mem_neighborhood j, rfl⟩
  filter_upwards [hU.mem_nhds hcenter] with z hz
  obtain ⟨w, hw, rfl⟩ := hz
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply]
  exact ellipticFullChart_projection j ⟨w, hw⟩

private theorem
    SpecialPeriods.Triangle.ellipticFullChart_complexGerm_analyticAt (j : Elliptic.Kind) :
    AnalyticAt ℂ
      (ellipticFullChart j ∘ SpecialPeriods.triangleOrbitProjection ∘ UpperHalfPlane.ofComplex)
      (ellipticCenter j : ℂ) :=
  (normalizedCayleyBranch_analyticAt (ellipticCenter j) (ellipticCenter j)
        (ellipticNeighborhoodRadius j) (ellipticNeighborhoodRadius_pos j).ne' j.order).congr
    (ellipticFullChart_complexGerm_eventuallyEq j).symm

private theorem SpecialPeriods.Triangle.ellipticFullChart_order_center (j : Elliptic.Kind) :
    analyticOrderAt
        (ellipticFullChart j ∘ SpecialPeriods.triangleOrbitProjection ∘ UpperHalfPlane.ofComplex)
        (ellipticCenter j : ℂ) =
      (j.order : ℕ∞) := by
  rw [analyticOrderAt_congr (ellipticFullChart_complexGerm_eventuallyEq j)]
  exact
    normalizedCayleyBranch_order_center (ellipticCenter j) (ellipticNeighborhoodRadius j)
      (ellipticNeighborhoodRadius_pos j).ne' j.order

private theorem SpecialPeriods.Triangle.sl_analyticAt_smul (g : SL(2, ℝ)) (z : ℍ) :
    AnalyticAt ℂ (fun w : ℂ => ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) (z : ℂ) := by
  have h := UpperHalfPlane.analyticAt_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by simp) z
  simpa only [MulAction.compHom_smul_def] using h

private theorem
    SpecialPeriods.Triangle.sl_analyticOrderAt_comp_smul (f : ℍ → ℂ) (g : SL(2, ℝ)) (z : ℍ) :
    analyticOrderAt (fun w : ℂ => f (g • UpperHalfPlane.ofComplex w)) (z : ℂ) =
      analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) ((g • z : ℍ) : ℂ) := by
  let G : ℂ → ℂ := fun w => ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ)
  have he :
    (fun w : ℂ => f (g • UpperHalfPlane.ofComplex w)) = (f ∘ UpperHalfPlane.ofComplex) ∘ G := by
    funext w
    simp only [Function.comp_apply, G, UpperHalfPlane.ofComplex_apply]
  rw [he, analyticOrderAt_comp_of_deriv_ne_zero]
  · simp only [G, UpperHalfPlane.ofComplex_apply]
  · exact sl_analyticAt_smul g z
  · rw [sl_deriv_smul]
    exact div_ne_zero one_ne_zero (pow_ne_zero 2 (slDenom_ne_zero g z))

private theorem SpecialPeriods.Triangle.triangle_analyticOrderAt_comp_action (f : ℍ → ℂ)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    analyticOrderAt
        (fun w : ℂ =>
          f (SpecialPeriods.triangleGeometricRepresentation g (UpperHalfPlane.ofComplex w)))
        (z : ℂ) =
      analyticOrderAt (f ∘ UpperHalfPlane.ofComplex)
        (SpecialPeriods.triangleGeometricRepresentation g z : ℂ) := by
  have hl (w : ℍ) :
    (SpecialPeriods.triangleMatrixLift g).val • w =
      SpecialPeriods.triangleGeometricRepresentation g w :=
    SpecialPeriods.triangleMatrixLift_smul g w
  simpa only [hl] using sl_analyticOrderAt_comp_smul f (SpecialPeriods.triangleMatrixLift g).val z

private theorem SpecialPeriods.Triangle.triangle_invariant_analyticOrderAt (f : ℍ → ℂ)
    (hf :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    analyticOrderAt (f ∘ UpperHalfPlane.ofComplex)
        (SpecialPeriods.triangleGeometricRepresentation g z : ℂ) =
      analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (z : ℂ) := by
  have he :
    (fun w : ℂ =>
        f (SpecialPeriods.triangleGeometricRepresentation g (UpperHalfPlane.ofComplex w))) =
      f ∘ UpperHalfPlane.ofComplex := by
    funext w
    exact hf g (UpperHalfPlane.ofComplex w)
  have h := triangle_analyticOrderAt_comp_action f g z
  rw [he] at h
  exact h.symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.instIsManifold7 : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace :=
  triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
private theorem SpecialPeriods.triangleCuspComplement_nonempty_for_coordinates_mo1973_16685 :
    Nonempty triangleCuspComplement :=
  ⟨triangleOpenInclusionToComplement triangleOrbitCenterOne⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
private def SpecialPeriods.triangleOpenInclusionPartial :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace TriangleCompactifiedOrbitSpace ω :=
  triangleOpenComplementBiholomorph.toPartialDiffeomorph.trans
    (opensInclusionPartialDiffeomorph 𝓘(ℂ) triangleCuspComplement
      triangleCuspComplement_nonempty_for_coordinates_mo1973_16685)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
private theorem SpecialPeriods.triangleOpenInclusionPartial_source :
    triangleOpenInclusionPartial.source = Set.univ := by
  simp [triangleOpenInclusionPartial, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph,
    opensInclusionPartialDiffeomorph]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
private theorem SpecialPeriods.triangleOpenInclusionPartial_target :
    triangleOpenInclusionPartial.target =
      (triangleCuspComplement : Set TriangleCompactifiedOrbitSpace) := by
  simp [triangleOpenInclusionPartial, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph,
    opensInclusionPartialDiffeomorph]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
private theorem SpecialPeriods.triangleOpenInclusionPartial_symm_apply (q : TriangleOrbitSpace) :
    triangleOpenInclusionPartial.symm (triangleOpenInclusion q) = q := by
  change
    triangleOpenInclusionPartial.toPartialEquiv.invFun
        (triangleOpenInclusionPartial.toPartialEquiv.toFun q) =
      q
  exact triangleOpenInclusionPartial.toPartialEquiv.left_inv (by simp)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
private def SpecialPeriods.Triangle.ellipticCompactifiedPartial (j : Elliptic.Kind) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace ℂ ω :=
  SpecialPeriods.triangleOpenInclusionPartial.symm.trans
    (SpecialPeriods.triangleOrbitCoordinatePartial (.inr j))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
private def SpecialPeriods.Triangle.ellipticCompactifiedChart (j : Elliptic.Kind) :
    OpenPartialHomeomorph SpecialPeriods.TriangleCompactifiedOrbitSpace ℂ :=
  (ellipticCompactifiedPartial j).toOpenPartialHomeomorph

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticCompactifiedChart_openInclusion (j : Elliptic.Kind)
    (q : SpecialPeriods.TriangleOrbitSpace) :
    ellipticCompactifiedChart j (SpecialPeriods.triangleOpenInclusion q) =
      ellipticFullChart j q := by
  change
    ellipticFullChart j
        (SpecialPeriods.triangleOpenInclusionPartial.symm
          (SpecialPeriods.triangleOpenInclusion q)) =
      _
  rw [SpecialPeriods.triangleOpenInclusionPartial_symm_apply]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
private theorem SpecialPeriods.Triangle.openInclusion_mem_ellipticCompactifiedChart_source
    (j : Elliptic.Kind) (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.triangleOpenInclusion q ∈ (ellipticCompactifiedChart j).source ↔
      q ∈ (ellipticFullChart j).source := by
  change
    (SpecialPeriods.triangleOpenInclusion q ∈ SpecialPeriods.triangleOpenInclusionPartial.target ∧
        SpecialPeriods.triangleOpenInclusionPartial.symm
            (SpecialPeriods.triangleOpenInclusion q) ∈
          (ellipticFullChart j).source) ↔
      _
  rw [SpecialPeriods.triangleOpenInclusionPartial_target,
    SpecialPeriods.triangleOpenInclusionPartial_symm_apply]
  exact and_iff_right (SpecialPeriods.triangleOpenInclusion_ne_cusp q)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticCompactifiedChart_target (j : Elliptic.Kind) :
    (ellipticCompactifiedChart j).target = (SpecialPeriods.unitDisc : Set ℂ) := by
  change
    (ellipticFullChart j).target ∩
        (ellipticFullChart j).symm ⁻¹' SpecialPeriods.triangleOpenInclusionPartial.source =
      _
  rw [SpecialPeriods.triangleOpenInclusionPartial_source, Set.preimage_univ, Set.inter_univ,
    ellipticFullChart_target]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
private theorem
    SpecialPeriods.Triangle.ellipticCompactifiedChart_center_mem_source (j : Elliptic.Kind) :
    ellipticCompactifiedCenter j ∈ (ellipticCompactifiedChart j).source :=
  (openInclusion_mem_ellipticCompactifiedChart_source j (ellipticOrbitCenter j)).mpr
    (ellipticFullChart_center_mem_source j)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticCompactifiedChart_center (j : Elliptic.Kind) :
    ellipticCompactifiedChart j (ellipticCompactifiedCenter j) = 0 := by
  change
    ellipticCompactifiedChart j (SpecialPeriods.triangleOpenInclusion (ellipticOrbitCenter j)) = 0
  rw [ellipticCompactifiedChart_openInclusion, ellipticFullChart_center]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
private theorem SpecialPeriods.Triangle.ellipticCompactifiedChart_holomorphic (j : Elliptic.Kind) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (ellipticCompactifiedChart j) (ellipticCompactifiedChart j).source :=
  (ellipticCompactifiedPartial j).contMDiffOn

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
private theorem
    SpecialPeriods.Triangle.ellipticCompactifiedChart_symm_holomorphic (j : Elliptic.Kind) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (ellipticCompactifiedChart j).symm
      (ellipticCompactifiedChart j).target :=
  (ellipticCompactifiedPartial j).symm.contMDiffOn

private abbrev RiemannSphere :=
  OnePoint ℂ

private def RiemannSphere.infinityParametrization (z : ℂ) : RiemannSphere := by
  classical exact if z = 0 then ((OnePoint.infty) : RiemannSphere) else (z⁻¹ : ℂ)

@[simp]
private theorem RiemannSphere.infinityParametrization_zero :
    infinityParametrization 0 = ((OnePoint.infty) : RiemannSphere) := by
  simp [infinityParametrization]

private theorem RiemannSphere.infinityParametrization_of_ne {z : ℂ} (hz : z ≠ 0) :
    infinityParametrization z = (z⁻¹ : ℂ) := by simp [infinityParametrization, hz]

private theorem
    RiemannSphere.infinityParametrization_continuous : Continuous infinityParametrization := by
  classical
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    change Filter.Tendsto infinityParametrization (𝓝 (0 : ℂ)) (𝓝 (infinityParametrization 0))
    rw [infinityParametrization_zero, ← nhdsNE_sup_pure (0 : ℂ), Filter.tendsto_sup]
    constructor
    · have hc :
        Filter.Tendsto ((↑) : ℂ → OnePoint ℂ) (Bornology.cobounded ℂ)
          (𝓝 ((OnePoint.infty) : RiemannSphere)) := by
        simpa only [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
          (OnePoint.tendsto_coe_infty (X := ℂ))
      have hi := hc.comp (Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ))
      apply hi.congr'
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : w ≠ 0 := hw
      simp [infinityParametrization, hw']
    · simpa only [infinityParametrization_zero] using
        (tendsto_pure_nhds infinityParametrization (0 : ℂ))
  · have hc : ContinuousAt (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) z :=
      OnePoint.continuous_coe.continuousAt.comp (contDiffAt_inv ℂ hz (n := ω)).continuousAt
    apply hc.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hz] with w hw
    exact infinityParametrization_of_ne hw

private theorem RiemannSphere.infinityParametrization_injective :
    Function.Injective infinityParametrization := by
  classical
  intro z w he
  by_cases hz : z = 0 <;> by_cases hw : w = 0
  · exact hz.trans hw.symm
  · simp [infinityParametrization, hz, hw] at he
  · simp [infinityParametrization, hz, hw] at he
  · simpa [infinityParametrization, hz, hw] using he

private def RiemannSphere.standardCharts : TwoAffineCharts RiemannSphere
    where
  left := ((↑) : ℂ → OnePoint ℂ)
  right := infinityParametrization
  continuous_left := OnePoint.continuous_coe
  continuous_right := infinityParametrization_continuous
  left_injective := OnePoint.coe_injective
  right_injective := infinityParametrization_injective
  inversion z hz := by simp [infinityParametrization, inv_ne_zero hz]
  endpoints_ne := by simp [infinityParametrization]
  covered
    p := by
    induction p using OnePoint.rec with
    | infty => exact Or.inr ⟨0, infinityParametrization_zero⟩
    | coe z => exact Or.inl ⟨z, rfl⟩

private instance RiemannSphere.chartedSpace : ChartedSpace ℂ RiemannSphere :=
  standardCharts.chartedSpace

private instance RiemannSphere.isManifold : IsManifold (modelWithCornersSelf ℂ ℂ) ω RiemannSphere :=
  standardCharts.isManifold

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.Cover.finiteInverse
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℂ) : SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  π.symm (z : RiemannSphere)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.MuTorsor.Cover.apply_finiteInverse
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℂ) : π (finiteInverse π z) = (z : RiemannSphere) :=
  π.apply_symm_apply _

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.finiteInverse_continuous
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω) :
    Continuous (finiteInverse π) :=
  π.symm.continuous.comp OnePoint.continuous_coe

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.finiteInverse_holomorphic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (finiteInverse π) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℂ => (z : RiemannSphere)) :=
    RiemannSphere.standardCharts.affineMap_holomorphic Bool.false
  exact π.symm.contMDiff.comp hc

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.Cover.finitePullback
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (V : TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace) :
    TopologicalSpace.Opens ℂ :=
  ⟨finiteInverse π ⁻¹' (V : Set SpecialPeriods.TriangleCompactifiedOrbitSpace),
    V.isOpen.preimage (finiteInverse_continuous π)⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.MuTorsor.Cover.mem_finitePullback
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (V : TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace) (z : ℂ) :
    z ∈ finitePullback π V ↔ finiteInverse π z ∈ V :=
  Iff.rfl

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.symm_infty
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    π.symm ((OnePoint.infty) : RiemannSphere) = SpecialPeriods.triangleCuspPoint := by
  exact π.injective ((π.apply_symm_apply _).trans hπ.symm)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.finiteInverse_ne_cusp
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℂ) :
    finiteInverse π z ≠ SpecialPeriods.triangleCuspPoint := by
  intro h
  exact OnePoint.coe_ne_infty z ((apply_finiteInverse π z).symm.trans ((congrArg π h).trans hπ))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.finiteInverse_tendsto_cusp
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Filter.Tendsto (finiteInverse π) (Bornology.cobounded ℂ)
      (𝓝 SpecialPeriods.triangleCuspPoint) := by
  have hc :
    Filter.Tendsto (fun z : ℂ => (z : RiemannSphere)) (Bornology.cobounded ℂ)
      (𝓝 ((OnePoint.infty) : RiemannSphere)) := by
    simpa only [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
      (OnePoint.tendsto_coe_infty (X := ℂ))
  have h := π.symm.continuous.continuousAt.tendsto.comp hc
  change
    Filter.Tendsto (finiteInverse π) (Bornology.cobounded ℂ)
      (𝓝 (π.symm ((OnePoint.infty) : RiemannSphere))) at h
  simpa only [symm_infty π hπ] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.finitePullback_contains_exterior
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace)
    (hV : SpecialPeriods.triangleCuspPoint ∈ V) :
    ∃ R : ℝ, 0 < R ∧ (Metric.ball (0 : ℂ) R)ᶜ ⊆ finitePullback π V := by
  have hmem : (finitePullback π V : Set ℂ) ∈ Bornology.cobounded ℂ :=
    (finiteInverse_tendsto_cusp π hπ) (V.isOpen.mem_nhds hV)
  obtain ⟨r, _, hr⟩ := (Metric.hasBasis_cobounded_compl_ball (0 : ℂ)).mem_iff.mp hmem
  refine ⟨Max.max r 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  exact (Set.compl_subset_compl.mpr (Metric.ball_subset_ball (le_max_left r 1))).trans hr

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def
    SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate : RiemannSphere → ℂ :=
  (RiemannSphere.standardCharts.parametrization Bool.true).symm

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_mem_source
    {p : RiemannSphere} (hp : p ≠ ((0 : ℂ) : RiemannSphere)) :
    p ∈ (RiemannSphere.standardCharts.parametrization Bool.true).target := by
  rw [TwoAffineCharts.parametrization_target]
  change p ∈ Set.range RiemannSphere.standardCharts.right
  rw [RiemannSphere.standardCharts.range_right]
  exact hp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_infty :
    sphereReciprocalCoordinate ((OnePoint.infty) : RiemannSphere) = 0 := by
  have h := RiemannSphere.standardCharts.parametrization_symm_apply Bool.true (0 : ℂ)
  change sphereReciprocalCoordinate (RiemannSphere.infinityParametrization 0) = 0 at h
  simpa only [RiemannSphere.infinityParametrization_zero] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_coe {z : ℂ}
    (hz : z ≠ 0) : sphereReciprocalCoordinate (z : RiemannSphere) = z⁻¹ := by
  have he : RiemannSphere.infinityParametrization z⁻¹ = (z : RiemannSphere) := by
    rw [RiemannSphere.infinityParametrization_of_ne (inv_ne_zero hz), inv_inv]
  have h := RiemannSphere.standardCharts.parametrization_symm_apply Bool.true z⁻¹
  change sphereReciprocalCoordinate (RiemannSphere.infinityParametrization z⁻¹) = z⁻¹ at h
  simpa only [he] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_holomorphicAt
    {p : RiemannSphere} (hp : p ≠ ((0 : ℂ) : RiemannSphere)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereReciprocalCoordinate p := by
  apply
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (Set.mem_range_self Bool.true))
  exact sphereReciprocalCoordinate_mem_source hp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.CuspCoordinates.t
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (q : ℂ) : ℂ :=
  sphereReciprocalCoordinate
    (π ((SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm q))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.CuspCoordinates.tDivQ
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω) :
    ℂ → ℂ :=
  dslope (t π) 0

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.t_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) : t π 0 = 0 := by
  rw [t, SpecialPeriods.Triangle.cuspFullChart_symm_zero, hπ, sphereReciprocalCoordinate_infty]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.t_holomorphicAt_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (t π) 0 := by
  have hC :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm (0 : ℂ) :=
    SpecialPeriods.triangleCompactified_cuspChart_symm_holomorphic.contMDiffAt
      (Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self
          (SpecialPeriods.Triangle.cuspRadius_pos SpecialPeriods.Triangle.width)))
  have hR :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereReciprocalCoordinate
      (π ((SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm 0)) :=
    by
    rw [SpecialPeriods.Triangle.cuspFullChart_symm_zero, hπ]
    exact sphereReciprocalCoordinate_holomorphicAt (OnePoint.infty_ne_coe (0 : ℂ))
  exact hR.comp 0 (π.contMDiffAt.comp 0 hC)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.t_analyticAt_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    AnalyticAt ℂ (t π) 0 :=
  (t_holomorphicAt_zero π hπ).contDiffAt.analyticAt

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.tDivQ_analyticAt_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    AnalyticAt ℂ (tDivQ π) 0 :=
  (t_analyticAt_zero π hπ).hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.t_eq_mul_tDivQ
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (q : ℂ) :
    t π q = q * tDivQ π q := by
  simpa only [tDivQ, sub_zero, t_zero π hπ, smul_eq_mul] using (sub_smul_dslope (t π) 0 q).symm

private theorem SpecialPeriods.MuTorsor.SourceOrders.deriv_ne_zero_of_isLocalDiffeomorph {f : ℂ → ℂ}
    {z : ℂ} (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f z) : deriv f z ≠ 0 := by
  let e : ℂ ≃L[ℂ] ℂ := hf.mfderivToContinuousLinearEquiv (by simp)
  have he : e 1 = deriv f z := by
    change (show ℂ →L[ℂ] ℂ from mfderiv 𝓘(ℂ) 𝓘(ℂ) f z) 1 = deriv f z
    rw [mfderiv_eq_fderiv]
    rfl
  intro h
  have h10 : e 1 = e 0 := by rw [he, h, map_zero]
  exact one_ne_zero (e.injective h10)

private theorem SpecialPeriods.MuTorsor.SourceOrders.centered_order_eq_one_of_isLocalDiffeomorph
    {f : ℂ → ℂ} {z : ℂ} (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f z) :
    analyticOrderAt (fun w => f w - f z) z = 1 :=
  hf.contMDiffAt.contDiffAt.analyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero
    (deriv_ne_zero_of_isLocalDiffeomorph hf)

private theorem SpecialPeriods.MuTorsor.SourceOrders.order_eq_one_of_isLocalDiffeomorph {f : ℂ → ℂ}
    {z : ℂ} (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f z) (hz : f z = 0) :
    analyticOrderAt f z = 1 := by
  simpa only [hz, sub_zero] using centered_order_eq_one_of_isLocalDiffeomorph hf

private theorem SpecialPeriods.MuTorsor.SourceOrders.centered_order_comp {F f : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a) (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f (F a)) :
    analyticOrderAt (fun w => f (F w) - f (F a)) a = analyticOrderAt (fun w => F w - F a) a := by
  have houter : AnalyticAt ℂ (fun w => f w - f (F a)) (F a) :=
    hf.contMDiffAt.contDiffAt.analyticAt.sub analyticAt_const
  simpa only [Function.comp_def, centered_order_eq_one_of_isLocalDiffeomorph hf, one_mul] using
    houter.analyticOrderAt_comp hF

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.TriangleSource.cuspPartialDiffeomorph :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace ℂ ω
    where
  toPartialEquiv :=
    (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).toPartialEquiv
  open_source :=
    (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).open_source
  open_target :=
    (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).open_target
  contMDiffOn_toFun := SpecialPeriods.triangleCompactified_cuspChart_holomorphic
  contMDiffOn_invFun := SpecialPeriods.triangleCompactified_cuspChart_symm_holomorphic

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.TriangleSource.sphereReciprocalPartialDiffeomorph :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) RiemannSphere ℂ ω
    where
  toPartialEquiv := (RiemannSphere.standardCharts.parametrization Bool.true).symm.toPartialEquiv
  open_source := (RiemannSphere.standardCharts.parametrization Bool.true).open_target
  open_target := (RiemannSphere.standardCharts.parametrization Bool.true).open_source
  contMDiffOn_toFun :=
    contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (Set.mem_range_self Bool.true))
  contMDiffOn_invFun :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (Set.mem_range_self Bool.true))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.TriangleSource.meromorphicCuspJ
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (q : ℂ) : ℂ :=
  1728 / SpecialPeriods.MuTorsor.CuspCoordinates.t π q

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.reciprocalCusp_isLocalDiffeomorphAt
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (SpecialPeriods.MuTorsor.CuspCoordinates.t π) 0 := by
  have hc :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm 0 :=
    cuspPartialDiffeomorph.symm.isLocalDiffeomorphAt _ _ _
      (Metric.mem_ball_self
        (SpecialPeriods.Triangle.cuspRadius_pos SpecialPeriods.Triangle.width))
  have hr :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate
      (π ((SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm 0)) :=
    by
    rw [SpecialPeriods.Triangle.cuspFullChart_symm_zero, hπ]
    exact
      sphereReciprocalPartialDiffeomorph.isLocalDiffeomorphAt _ _ _
        (SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_mem_source
          (OnePoint.infty_ne_coe (0 : ℂ)))
  have hp :=
    hc.comp (K := 𝓘(ℂ)) (P := RiemannSphere)
      (π.isLocalDiffeomorph
        ((SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm 0))
  exact hp.comp (K := 𝓘(ℂ)) (P := ℂ) hr

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.reciprocalCusp_deriv_ne_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    deriv (SpecialPeriods.MuTorsor.CuspCoordinates.t π) 0 ≠ 0 :=
  SpecialPeriods.MuTorsor.SourceOrders.deriv_ne_zero_of_isLocalDiffeomorph
    (reciprocalCusp_isLocalDiffeomorphAt π hπ)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.reciprocalCusp_analyticOrder
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    analyticOrderAt (SpecialPeriods.MuTorsor.CuspCoordinates.t π) 0 = 1 :=
  SpecialPeriods.MuTorsor.SourceOrders.order_eq_one_of_isLocalDiffeomorph
    (reciprocalCusp_isLocalDiffeomorphAt π hπ)
    (SpecialPeriods.MuTorsor.CuspCoordinates.t_zero π hπ)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.meromorphicCuspJ_meromorphicAt
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    MeromorphicAt (meromorphicCuspJ π) 0 :=
  analyticAt_const.meromorphicAt.div
    (SpecialPeriods.MuTorsor.CuspCoordinates.t_analyticAt_zero π hπ).meromorphicAt

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.meromorphicCuspJ_order
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    meromorphicOrderAt (meromorphicCuspJ π) 0 = (-1 : ℤ) := by
  change
    meromorphicOrderAt ((fun _ : ℂ => (1728 : ℂ)) / SpecialPeriods.MuTorsor.CuspCoordinates.t π)
        0 =
      _
  rw [meromorphicOrderAt_div analyticAt_const.meromorphicAt
      (SpecialPeriods.MuTorsor.CuspCoordinates.t_analyticAt_zero π hπ).meromorphicAt,
    (SpecialPeriods.MuTorsor.CuspCoordinates.t_analyticAt_zero π hπ).meromorphicOrderAt_eq,
    reciprocalCusp_analyticOrder π hπ]
  norm_num [meromorphicOrderAt_const]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.sphereFiniteCoordinate : RiemannSphere → ℂ :=
  (RiemannSphere.standardCharts.parametrization Bool.false).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.BetaTorsor.sphereFiniteCoordinate_coe (z : ℂ) :
    sphereFiniteCoordinate (z : RiemannSphere) = z :=
  RiemannSphere.standardCharts.parametrization_symm_apply Bool.false z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.sphereFiniteCoordinate_mem_source {q : RiemannSphere}
    (hq : q ≠ ((OnePoint.infty) : RiemannSphere)) :
    q ∈ (RiemannSphere.standardCharts.parametrization Bool.false).target := by
  obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hq
  exact ⟨z, Set.mem_univ z, rfl⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.sphereFiniteCoordinate_coe_apply {q : RiemannSphere}
    (hq : q ≠ ((OnePoint.infty) : RiemannSphere)) :
    (sphereFiniteCoordinate q : RiemannSphere) = q :=
  (RiemannSphere.standardCharts.parametrization Bool.false).right_inv
    (sphereFiniteCoordinate_mem_source hq)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.sphereFiniteCoordinate_holomorphicAt {q : RiemannSphere}
    (hq : q ≠ ((OnePoint.infty) : RiemannSphere)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereFiniteCoordinate q := by
  apply
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (Set.mem_range_self Bool.false))
  exact sphereFiniteCoordinate_mem_source hq

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.finiteOrbitCoordinate
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (q : SpecialPeriods.TriangleOrbitSpace) : ℂ :=
  sphereFiniteCoordinate (π (SpecialPeriods.triangleOpenInclusion q))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.finiteProjection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℍ) : ℂ :=
  finiteOrbitCoordinate π (SpecialPeriods.triangleOrbitProjection z)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_target_ne_infty
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (q : SpecialPeriods.TriangleOrbitSpace) :
    π (SpecialPeriods.triangleOpenInclusion q) ≠ ((OnePoint.infty) : RiemannSphere) := by
  intro h
  exact SpecialPeriods.triangleOpenInclusion_ne_cusp q (π.injective (h.trans hπ.symm))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_coe
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (q : SpecialPeriods.TriangleOrbitSpace) :
    (finiteOrbitCoordinate π q : RiemannSphere) = π (SpecialPeriods.triangleOpenInclusion q) :=
  sphereFiniteCoordinate_coe_apply (finiteOrbitCoordinate_target_ne_infty π hπ q)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_holomorphic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (finiteOrbitCoordinate π) := by
  intro q
  exact
    (sphereFiniteCoordinate_holomorphicAt (finiteOrbitCoordinate_target_ne_infty π hπ q)).comp q
      ((π.contMDiff.comp SpecialPeriods.triangleOpenInclusion_holomorphic) q)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_injective
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Function.Injective (finiteOrbitCoordinate π) := by
  intro q r h
  apply OnePoint.coe_injective
  apply π.injective
  exact
    (finiteOrbitCoordinate_coe π hπ q).symm.trans
      ((congrArg (fun z : ℂ => (z : RiemannSphere)) h).trans (finiteOrbitCoordinate_coe π hπ r))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.finiteOrbitInverse
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℂ) :
    SpecialPeriods.TriangleOrbitSpace :=
  SpecialPeriods.triangleOpenComplementBiholomorph.symm
    ⟨SpecialPeriods.MuTorsor.Cover.finiteInverse π z,
      SpecialPeriods.MuTorsor.Cover.finiteInverse_ne_cusp π hπ z⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.openInclusion_finiteOrbitInverse
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℂ) :
    SpecialPeriods.triangleOpenInclusion (finiteOrbitInverse π hπ z) =
      SpecialPeriods.MuTorsor.Cover.finiteInverse π z :=
  SpecialPeriods.triangleOpenComplementBiholomorph_symm_apply _

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteOrbitInverse_holomorphic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (finiteOrbitInverse π hπ) := by
  have hcod :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : ℂ =>
        (⟨SpecialPeriods.MuTorsor.Cover.finiteInverse π z,
            SpecialPeriods.MuTorsor.Cover.finiteInverse_ne_cusp π hπ z⟩ :
          SpecialPeriods.triangleCuspComplement)) := by
    intro z
    exact
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
        (SpecialPeriods.MuTorsor.Cover.finiteInverse_holomorphic π z)
  exact SpecialPeriods.triangleOpenComplementBiholomorph.symm.contMDiff.comp hcod

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_inverse
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℂ) :
    finiteOrbitCoordinate π (finiteOrbitInverse π hπ z) = z := by
  apply OnePoint.coe_injective
  rw [finiteOrbitCoordinate_coe π hπ, openInclusion_finiteOrbitInverse,
    SpecialPeriods.MuTorsor.Cover.apply_finiteInverse]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.BetaTorsor.finiteOrbitInverse_coordinate
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (q : SpecialPeriods.TriangleOrbitSpace) :
    finiteOrbitInverse π hπ (finiteOrbitCoordinate π q) = q :=
  finiteOrbitCoordinate_injective π hπ (finiteOrbitCoordinate_inverse π hπ _)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.finiteOrbitBiholomorph
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleOrbitSpace ℂ ω
    where
  toEquiv :=
    { toFun := finiteOrbitCoordinate π
      invFun := finiteOrbitInverse π hπ
      left_inv := finiteOrbitInverse_coordinate π hπ
      right_inv := finiteOrbitCoordinate_inverse π hπ }
  contMDiff_toFun := finiteOrbitCoordinate_holomorphic π hπ
  contMDiff_invFun := finiteOrbitInverse_holomorphic π hπ

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteProjection_holomorphic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (finiteProjection π) :=
  (finiteOrbitCoordinate_holomorphic π hπ).comp SpecialPeriods.triangleOrbitProjection_holomorphic

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteProjection_surjective
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Function.Surjective (finiteProjection π) := by
  intro z
  obtain ⟨a, ha⟩ := SpecialPeriods.triangleOrbitProjection_surjective (finiteOrbitInverse π hπ z)
  exact ⟨a, by simp only [finiteProjection, ha, finiteOrbitCoordinate_inverse]⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteProjection_invariant
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    finiteProjection π (SpecialPeriods.triangleGeometricRepresentation g z) =
      finiteProjection π z := by
  simp only [finiteProjection, SpecialPeriods.triangleOrbitProjection_smul]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteInverse_finiteProjection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℍ) :
    SpecialPeriods.MuTorsor.Cover.finiteInverse π (finiteProjection π z) =
      SpecialPeriods.triangleCompactifiedProjection z := by
  apply π.injective
  change
    π (SpecialPeriods.MuTorsor.Cover.finiteInverse π (finiteProjection π z)) =
      π (SpecialPeriods.triangleCompactifiedProjection z)
  rw [SpecialPeriods.MuTorsor.Cover.apply_finiteInverse]
  exact finiteOrbitCoordinate_coe π hπ (SpecialPeriods.triangleOrbitProjection z)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteProjection_mem_pullback
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace) (z : ℍ) :
    finiteProjection π z ∈ SpecialPeriods.MuTorsor.Cover.finitePullback π V ↔
      SpecialPeriods.triangleCompactifiedProjection z ∈ V := by
  rw [SpecialPeriods.MuTorsor.Cover.mem_finitePullback, finiteInverse_finiteProjection π hπ]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.analyticOnNhd_finite_pullback
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace)
    {f : SpecialPeriods.TriangleOrbitSpace → ℂ} (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f U) :
    AnalyticOnNhd ℂ (f ∘ finiteOrbitInverse π hπ)
      (finiteOrbitInverse π hπ ⁻¹' (U : Set SpecialPeriods.TriangleOrbitSpace)) := by
  intro z hz
  have hh := hf.contMDiffAt (U.isOpen.mem_nhds hz)
  exact (hh.comp z (finiteOrbitInverse_holomorphic π hπ z)).contDiffAt.analyticAt

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.eventually_mem_horodisc (Y : ℝ) :
    ∀ᶠ z in UpperHalfPlane.atImInfty, z ∈ SpecialPeriods.Triangle.horodisc Y := by
  apply (UpperHalfPlane.atImInfty_mem _).mpr
  exact ⟨Y + 1, fun _ hz => lt_of_lt_of_le (lt_add_one Y) hz⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.compactifiedProjection_tendsto_cusp :
    Filter.Tendsto SpecialPeriods.triangleCompactifiedProjection UpperHalfPlane.atImInfty
      (𝓝 SpecialPeriods.triangleCuspPoint) := by
  rw [SpecialPeriods.Triangle.cuspNeighborhood_basis.tendsto_right_iff]
  intro Y _
  filter_upwards [eventually_mem_horodisc Y] with z hz
  change
    SpecialPeriods.triangleOpenInclusion (SpecialPeriods.triangleOrbitProjection z) ∈
      SpecialPeriods.Triangle.cuspNeighborhood Y
  apply (SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood Y _).mpr
  exact ⟨z, hz, rfl⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.sphereProjection_tendsto_infty
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Filter.Tendsto (π ∘ SpecialPeriods.triangleCompactifiedProjection) UpperHalfPlane.atImInfty
      (𝓝 ((OnePoint.infty) : RiemannSphere)) := by
  have h := π.continuous.continuousAt.tendsto.comp compactifiedProjection_tendsto_cusp
  simpa only [hπ] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.finiteProjection_coe
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℍ) :
    (SpecialPeriods.BetaTorsor.finiteProjection π z : RiemannSphere) =
      π (SpecialPeriods.triangleCompactifiedProjection z) :=
  SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_coe π hπ
    (SpecialPeriods.triangleOrbitProjection z)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.finiteProjection_tendsto_cobounded
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Filter.Tendsto (SpecialPeriods.BetaTorsor.finiteProjection π) UpperHalfPlane.atImInfty
      (Bornology.cobounded ℂ) := by
  have hc :
    Filter.comap (fun z : ℂ => (z : RiemannSphere)) (𝓝 ((OnePoint.infty) : RiemannSphere)) =
      Bornology.cobounded ℂ := by
    simpa only [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
      (OnePoint.comap_coe_nhds_infty (X := ℂ))
  rw [← hc, Filter.tendsto_comap_iff]
  simpa only [Function.comp_def, finiteProjection_coe π hπ] using
    sphereProjection_tendsto_infty π hπ

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.finiteProjection_norm_tendsto_atTop
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Filter.Tendsto (fun z : ℍ => ‖SpecialPeriods.BetaTorsor.finiteProjection π z‖)
      UpperHalfPlane.atImInfty Filter.atTop :=
  tendsto_norm_cobounded_atTop.comp (finiteProjection_tendsto_cobounded π hπ)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.eventually_lt_norm_finiteProjection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (R : ℝ) :
    ∀ᶠ z in UpperHalfPlane.atImInfty, R < ‖SpecialPeriods.BetaTorsor.finiteProjection π z‖ :=
  (finiteProjection_norm_tendsto_atTop π hπ).eventually_gt_atTop R

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.finiteProjection_eventually_ne_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ∀ᶠ z in UpperHalfPlane.atImInfty, SpecialPeriods.BetaTorsor.finiteProjection π z ≠ 0 := by
  filter_upwards [eventually_lt_norm_finiteProjection π hπ 0] with z hz
  exact norm_pos_iff.mp hz

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.finiteProjection_inv_tendsto_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Filter.Tendsto (fun z : ℍ => (SpecialPeriods.BetaTorsor.finiteProjection π z)⁻¹)
      UpperHalfPlane.atImInfty (𝓝[≠] (0 : ℂ)) :=
  Filter.tendsto_inv₀_cobounded'.comp (finiteProjection_tendsto_cobounded π hπ)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.cuspChart_symm_cuspQ_of_mem (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width) :
    (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm
        (SpecialPeriods.Triangle.cuspQ z) =
      SpecialPeriods.triangleCompactifiedProjection z := by
  have hs :
    SpecialPeriods.triangleCompactifiedProjection z ∈
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source := by
    rw [SpecialPeriods.Triangle.cuspFullChart_source]
    exact
      (SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood SpecialPeriods.Triangle.width
            _).mpr
        ⟨z, hz, rfl⟩
  have he := SpecialPeriods.Triangle.cuspFullChart_mk SpecialPeriods.Triangle.width le_rfl ⟨z, hz⟩
  exact
    (congrArg (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm
          he).symm.trans
      ((SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).left_inv hs)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.t_cuspQ_eq_inv_finiteProjection_of_mem
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width)
    (hp : SpecialPeriods.BetaTorsor.finiteProjection π z ≠ 0) :
    t π (SpecialPeriods.Triangle.cuspQ z) = (SpecialPeriods.BetaTorsor.finiteProjection π z)⁻¹ := by
  rw [t, cuspChart_symm_cuspQ_of_mem z hz, ← finiteProjection_coe π hπ z]
  exact sphereReciprocalCoordinate_coe hp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.t_cuspQ_eq_inv_finiteProjection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      t π (SpecialPeriods.Triangle.cuspQ z) =
        (SpecialPeriods.BetaTorsor.finiteProjection π z)⁻¹ := by
  filter_upwards [eventually_mem_horodisc SpecialPeriods.Triangle.width,
    finiteProjection_eventually_ne_zero π hπ] with z hz hp
  exact t_cuspQ_eq_inv_finiteProjection_of_mem π hπ z hz hp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.CuspCoordinates.analyticAt_correction
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {v S : ℂ → ℂ}
    (hv : AnalyticAt ℂ v 0) (hS : AnalyticAt ℂ S 0) :
    AnalyticAt ℂ (fun q => -v q * tDivQ π q * S (t π q)) 0 := by
  have hS' : AnalyticAt ℂ S (t π 0) := by simpa only [t_zero π hπ] using hS
  exact (hv.neg.mul (tDivQ_analyticAt_zero π hπ)).mul (hS'.comp (t_analyticAt_zero π hπ))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.exists_cusp_formula_radius
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ∃ r₀ : ℝ,
      0 < r₀ ∧
        ∀ z : ℍ,
          ‖Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)‖ < r₀ →
            1728 * SpecialPeriods.BetaTorsor.finiteProjection π z =
              1728 /
                SpecialPeriods.MuTorsor.CuspCoordinates.t π
                  (Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)) := by
  obtain ⟨Y, hY⟩ :=
    (UpperHalfPlane.atImInfty_mem _).mp
      (SpecialPeriods.MuTorsor.CuspCoordinates.t_cuspQ_eq_inv_finiteProjection π hπ)
  refine ⟨SpecialPeriods.Triangle.cuspRadius Y, SpecialPeriods.Triangle.cuspRadius_pos Y, ?_⟩
  intro z hz
  have hheight : Y < z.im := (SpecialPeriods.Triangle.cuspQ_norm_lt_exp_iff Y z).mp hz
  have he := hY z hheight.le
  change
    SpecialPeriods.MuTorsor.CuspCoordinates.t π
        (Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)) =
      (SpecialPeriods.BetaTorsor.finiteProjection π z)⁻¹ at he
  rw [he, div_inv_eq_mul]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.SourceOrders.chartToFinite
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (j : Elliptic.Kind) : ℂ → ℂ :=
  SpecialPeriods.BetaTorsor.finiteOrbitCoordinate π ∘
    (SpecialPeriods.Triangle.ellipticFullChart j).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.MuTorsor.SourceOrders.ellipticFullChart_symm_zero (j : Elliptic.Kind) :
    (SpecialPeriods.Triangle.ellipticFullChart j).symm 0 =
      SpecialPeriods.Triangle.ellipticOrbitCenter j := by
  simpa only [SpecialPeriods.Triangle.ellipticFullChart_center] using
    (SpecialPeriods.Triangle.ellipticFullChart j).left_inv
      (SpecialPeriods.Triangle.ellipticFullChart_center_mem_source j)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.MuTorsor.SourceOrders.chartToFinite_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (j : Elliptic.Kind) :
    chartToFinite π j 0 =
      SpecialPeriods.BetaTorsor.finiteProjection π (SpecialPeriods.Triangle.ellipticCenter j) := by
  rw [chartToFinite, Function.comp_apply, ellipticFullChart_symm_zero]
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_germ_eventuallyEq_chartToFinite
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (j : Elliptic.Kind) (z : ℍ)
    (hz :
      SpecialPeriods.triangleOrbitProjection z ∈
        (SpecialPeriods.Triangle.ellipticFullChart j).source) :
    (SpecialPeriods.BetaTorsor.finiteProjection π ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (z : ℂ)]
      chartToFinite π j ∘
        (SpecialPeriods.Triangle.ellipticFullChart j ∘
          SpecialPeriods.triangleOrbitProjection ∘ UpperHalfPlane.ofComplex) := by
  have hc :
    ContinuousAt (SpecialPeriods.triangleOrbitProjection ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
    SpecialPeriods.triangleOrbitProjection_continuous.continuousAt.comp
      (UpperHalfPlane.contMDiffAt_ofComplex (n := ω) z.im_pos).continuousAt
  have hz' :
    (SpecialPeriods.triangleOrbitProjection ∘ UpperHalfPlane.ofComplex) (z : ℂ) ∈
      (SpecialPeriods.Triangle.ellipticFullChart j).source := by
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hz
  have hU :
    ∀ᶠ w in 𝓝 (z : ℂ),
      SpecialPeriods.triangleOrbitProjection (UpperHalfPlane.ofComplex w) ∈
        (SpecialPeriods.Triangle.ellipticFullChart j).source :=
    hc ((SpecialPeriods.Triangle.ellipticFullChart j).open_source.mem_nhds hz')
  filter_upwards [hU] with w hw
  exact
    congrArg (SpecialPeriods.BetaTorsor.finiteOrbitCoordinate π)
      ((SpecialPeriods.Triangle.ellipticFullChart j).left_inv hw).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.chartToFinite_isLocalDiffeomorphAt_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (j : Elliptic.Kind) : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartToFinite π j) 0 := by
  have hzero : (0 : ℂ) ∈ (SpecialPeriods.Triangle.ellipticFullChart j).target := by
    simpa only [SpecialPeriods.Triangle.ellipticFullChart_center] using
      (SpecialPeriods.Triangle.ellipticFullChart j).map_source
        (SpecialPeriods.Triangle.ellipticFullChart_center_mem_source j)
  have hinv :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (SpecialPeriods.Triangle.ellipticFullChart j).symm 0 :=
    (SpecialPeriods.triangleOrbitCoordinatePartial (.inr j)).symm.isLocalDiffeomorphAt _ _ _ hzero
  exact
    hinv.comp (K := 𝓘(ℂ)) (P := ℂ)
      ((SpecialPeriods.BetaTorsor.finiteOrbitBiholomorph π hπ).isLocalDiffeomorph _)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_analyticAt
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℍ) :
    AnalyticAt ℂ (SpecialPeriods.BetaTorsor.finiteProjection π ∘ UpperHalfPlane.ofComplex)
      (z : ℂ) :=
  ((SpecialPeriods.BetaTorsor.finiteProjection_holomorphic π hπ).contMDiffAt.comp (z : ℂ)
      (UpperHalfPlane.contMDiffAt_ofComplex z.im_pos)).contDiffAt.analyticAt

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_eq_center_iff
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (j : Elliptic.Kind) (z : ℍ) :
    SpecialPeriods.BetaTorsor.finiteProjection π z =
        SpecialPeriods.BetaTorsor.finiteProjection π (SpecialPeriods.Triangle.ellipticCenter j) ↔
      SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.Triangle.ellipticOrbitCenter j :=
  (SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_injective π hπ).eq_iff

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_centered_order_center
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (j : Elliptic.Kind) :
    analyticOrderAt
        (fun w : ℂ =>
          SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) -
            SpecialPeriods.BetaTorsor.finiteProjection π
              (SpecialPeriods.Triangle.ellipticCenter j))
        (SpecialPeriods.Triangle.ellipticCenter j : ℂ) =
      (j.order : ℕ∞) := by
  let F : ℂ → ℂ :=
    SpecialPeriods.Triangle.ellipticFullChart j ∘
      SpecialPeriods.triangleOrbitProjection ∘ UpperHalfPlane.ofComplex
  have hF : AnalyticAt ℂ F (SpecialPeriods.Triangle.ellipticCenter j : ℂ) :=
    SpecialPeriods.Triangle.ellipticFullChart_complexGerm_analyticAt j
  have hF0 : F (SpecialPeriods.Triangle.ellipticCenter j : ℂ) = 0 := by
    simp only [F, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    exact SpecialPeriods.Triangle.ellipticFullChart_center j
  have hlocal :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartToFinite π j)
      (F (SpecialPeriods.Triangle.ellipticCenter j : ℂ)) := by
    rw [hF0]
    exact chartToFinite_isLocalDiffeomorphAt_zero π hπ j
  have horder := centered_order_comp hF hlocal
  have he :
    (fun w : ℂ =>
        SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) -
          SpecialPeriods.BetaTorsor.finiteProjection π
            (SpecialPeriods.Triangle.ellipticCenter
              j)) =ᶠ[𝓝 (SpecialPeriods.Triangle.ellipticCenter j : ℂ)]
      (fun w =>
        chartToFinite π j (F w) -
          SpecialPeriods.BetaTorsor.finiteProjection π
            (SpecialPeriods.Triangle.ellipticCenter j)) := by
    filter_upwards [finiteProjection_germ_eventuallyEq_chartToFinite π j
        (SpecialPeriods.Triangle.ellipticCenter j)
        (SpecialPeriods.Triangle.ellipticFullChart_center_mem_source j)] with
      w hw
    exact
      congrArg
        (fun a : ℂ =>
          a -
            SpecialPeriods.BetaTorsor.finiteProjection π
              (SpecialPeriods.Triangle.ellipticCenter j))
        hw
  calc
    analyticOrderAt
          (fun w : ℂ =>
            SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) -
              SpecialPeriods.BetaTorsor.finiteProjection π
                (SpecialPeriods.Triangle.ellipticCenter j))
          (SpecialPeriods.Triangle.ellipticCenter j : ℂ) =
        analyticOrderAt
          (fun w =>
            chartToFinite π j (F w) -
              SpecialPeriods.BetaTorsor.finiteProjection π
                (SpecialPeriods.Triangle.ellipticCenter j))
          (SpecialPeriods.Triangle.ellipticCenter j : ℂ) :=
      analyticOrderAt_congr he
    _ = analyticOrderAt F (SpecialPeriods.Triangle.ellipticCenter j : ℂ) := by
      simpa only [hF0, chartToFinite_zero, sub_zero] using horder
    _ = (j.order : ℕ∞) := SpecialPeriods.Triangle.ellipticFullChart_order_center j

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_centered_order_of_fibre
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (j : Elliptic.Kind) (z : ℍ)
    (hz :
      SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.Triangle.ellipticOrbitCenter j) :
    analyticOrderAt
        (fun w : ℂ =>
          SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) -
            SpecialPeriods.BetaTorsor.finiteProjection π
              (SpecialPeriods.Triangle.ellipticCenter j))
        (z : ℂ) =
      (j.order : ℕ∞) := by
  obtain ⟨g, rfl⟩ :=
    (SpecialPeriods.triangleOrbitProjection_eq_iff z
          (SpecialPeriods.Triangle.ellipticCenter j)).mp
      hz
  have ht :=
    SpecialPeriods.Triangle.triangle_invariant_analyticOrderAt
      (fun a : ℍ =>
        SpecialPeriods.BetaTorsor.finiteProjection π a -
          SpecialPeriods.BetaTorsor.finiteProjection π (SpecialPeriods.Triangle.ellipticCenter j))
      (fun g a => by rw [SpecialPeriods.BetaTorsor.finiteProjection_invariant]) g
      (SpecialPeriods.Triangle.ellipticCenter j)
  exact ht.trans (finiteProjection_centered_order_center π hπ j)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_centerOne
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere)) :
    SpecialPeriods.BetaTorsor.finiteProjection π SpecialPeriods.Triangle.centerOne = 0 := by
  apply OnePoint.coe_injective
  exact
    (SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_coe π hπ
          SpecialPeriods.triangleOrbitCenterOne).trans
      h₀

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_centerTwo
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    SpecialPeriods.BetaTorsor.finiteProjection π SpecialPeriods.Triangle.centerTwo = 1 := by
  apply OnePoint.coe_injective
  exact
    (SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_coe π hπ
          SpecialPeriods.triangleOrbitCenterTwo).trans
      h₁

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_eq_zero_iff
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (z : ℍ) :
    SpecialPeriods.BetaTorsor.finiteProjection π z = 0 ↔
      SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne := by
  rw [← finiteProjection_centerOne π hπ h₀]
  exact finiteProjection_eq_center_iff π hπ .three z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_eq_one_iff
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) :
    SpecialPeriods.BetaTorsor.finiteProjection π z = 1 ↔
      SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo := by
  rw [← finiteProjection_centerTwo π hπ h₁]
  exact finiteProjection_eq_center_iff π hπ .four z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.SourceOrders.sourceJ
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℍ) : ℂ :=
  1728 * SpecialPeriods.BetaTorsor.finiteProjection π z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_invariant
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    sourceJ π (SpecialPeriods.triangleGeometricRepresentation g z) = sourceJ π z := by
  simp only [sourceJ, SpecialPeriods.BetaTorsor.finiteProjection_invariant]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_eq_zero_iff_finiteProjection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℍ) : sourceJ π z = 0 ↔ SpecialPeriods.BetaTorsor.finiteProjection π z = 0 := by
  simp only [sourceJ, mul_eq_zero, show (1728 : ℂ) ≠ 0 by norm_num, false_or]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_eq_1728_iff_finiteProjection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℍ) : sourceJ π z = 1728 ↔ SpecialPeriods.BetaTorsor.finiteProjection π z = 1 := by
  constructor
  · intro h
    exact mul_left_cancel₀ (by norm_num : (1728 : ℂ) ≠ 0) (h.trans (mul_one (1728 : ℂ)).symm)
  · intro h
    simp only [sourceJ, h, mul_one]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_holomorphic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (sourceJ π) :=
  contMDiff_const.mul (SpecialPeriods.BetaTorsor.finiteProjection_holomorphic π hπ)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_order_of_eq_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : SpecialPeriods.BetaTorsor.finiteProjection π z = 0) :
    analyticOrderAt (SpecialPeriods.BetaTorsor.finiteProjection π ∘ UpperHalfPlane.ofComplex)
        (z : ℂ) =
      3 := by
  have h :=
    finiteProjection_centered_order_of_fibre π hπ .three z
      ((finiteProjection_eq_zero_iff π hπ h₀ z).mp hz)
  change
    analyticOrderAt
        (fun w : ℂ =>
          SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) -
            SpecialPeriods.BetaTorsor.finiteProjection π SpecialPeriods.Triangle.centerOne)
        (z : ℂ) =
      3 at h
  simpa only [finiteProjection_centerOne π hπ h₀, sub_zero, Function.comp_def] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_sub_one_order_of_eq_one
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : SpecialPeriods.BetaTorsor.finiteProjection π z = 1) :
    analyticOrderAt
        (fun w : ℂ =>
          SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) - 1)
        (z : ℂ) =
      4 := by
  have h :=
    finiteProjection_centered_order_of_fibre π hπ .four z
      ((finiteProjection_eq_one_iff π hπ h₁ z).mp hz)
  change
    analyticOrderAt
        (fun w : ℂ =>
          SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) -
            SpecialPeriods.BetaTorsor.finiteProjection π SpecialPeriods.Triangle.centerTwo)
        (z : ℂ) =
      4 at h
  simpa only [finiteProjection_centerTwo π hπ h₁] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_centerOne
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere)) :
    sourceJ π SpecialPeriods.Triangle.centerOne = 0 := by
  simp only [sourceJ, finiteProjection_centerOne π hπ h₀, MulZeroClass.mul_zero]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_centerTwo
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    sourceJ π SpecialPeriods.Triangle.centerTwo = 1728 := by
  simp only [sourceJ, finiteProjection_centerTwo π hπ h₁, mul_one]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_order_of_eq_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : sourceJ π z = 0) :
    analyticOrderAt (sourceJ π ∘ UpperHalfPlane.ofComplex) (z : ℂ) = 3 := by
  have hc : AnalyticAt ℂ (fun _ : ℂ => (1728 : ℂ)) (z : ℂ) := analyticAt_const
  have hco : analyticOrderAt (fun _ : ℂ => (1728 : ℂ)) (z : ℂ) = 0 :=
    hc.analyticOrderAt_eq_zero.mpr (by norm_num)
  change
    analyticOrderAt
        ((fun _ : ℂ => (1728 : ℂ)) *
          (SpecialPeriods.BetaTorsor.finiteProjection π ∘ UpperHalfPlane.ofComplex))
        (z : ℂ) =
      3
  rw [analyticOrderAt_mul hc (finiteProjection_analyticAt π hπ z), hco, zero_add]
  exact
    finiteProjection_order_of_eq_zero π hπ h₀ z ((sourceJ_eq_zero_iff_finiteProjection π z).mp hz)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_sub_1728_order_of_eq
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : sourceJ π z = 1728) :
    analyticOrderAt (fun w : ℂ => sourceJ π (UpperHalfPlane.ofComplex w) - 1728) (z : ℂ) = 4 := by
  have hc : AnalyticAt ℂ (fun _ : ℂ => (1728 : ℂ)) (z : ℂ) := analyticAt_const
  have hco : analyticOrderAt (fun _ : ℂ => (1728 : ℂ)) (z : ℂ) = 0 :=
    hc.analyticOrderAt_eq_zero.mpr (by norm_num)
  have hp :
    AnalyticAt ℂ
      (fun w : ℂ => SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) - 1)
      (z : ℂ) :=
    (finiteProjection_analyticAt π hπ z).sub analyticAt_const
  have he :
    (fun w : ℂ => sourceJ π (UpperHalfPlane.ofComplex w) - 1728) =
      (fun _ : ℂ => (1728 : ℂ)) *
        (fun w : ℂ =>
          SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) - 1) := by
    funext w
    simp only [sourceJ, Pi.mul_apply]
    ring
  rw [he, analyticOrderAt_mul hc hp, hco, zero_add]
  exact
    finiteProjection_sub_one_order_of_eq_one π hπ h₁ z
      ((sourceJ_eq_1728_iff_finiteProjection π z).mp hz)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_order_centerOne
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere)) :
    analyticOrderAt (sourceJ π ∘ UpperHalfPlane.ofComplex)
        (SpecialPeriods.Triangle.centerOne : ℂ) =
      3 :=
  sourceJ_order_of_eq_zero π hπ h₀ SpecialPeriods.Triangle.centerOne (sourceJ_centerOne π hπ h₀)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_sub_1728_order_centerTwo
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    analyticOrderAt (fun w : ℂ => sourceJ π (UpperHalfPlane.ofComplex w) - 1728)
        (SpecialPeriods.Triangle.centerTwo : ℂ) =
      4 :=
  sourceJ_sub_1728_order_of_eq π hπ h₁ SpecialPeriods.Triangle.centerTwo
    (sourceJ_centerTwo π hπ h₁)

private abbrev SpecialPeriods.ModularOrbitSpace :=
  Quotient (MulAction.orbitRel SL(2, ℤ) ℍ)

private def SpecialPeriods.modularOrbitProjection : ℍ → ModularOrbitSpace :=
  Quotient.mk _

private theorem
    SpecialPeriods.modularOrbitProjection_continuous : Continuous modularOrbitProjection :=
  continuous_quotient_mk'

private theorem SpecialPeriods.modularOrbitProjection_surjective :
    Function.Surjective modularOrbitProjection :=
  Quotient.mk_surjective

private theorem SpecialPeriods.modularOrbitProjection_smul (γ : SL(2, ℤ)) (z : ℍ) :
    modularOrbitProjection (γ • z) = modularOrbitProjection z :=
  MulAction.orbitRel.Quotient.quotient_smul_eq

private def SpecialPeriods.modularQuotientJ : ModularOrbitSpace → ℂ :=
  Quotient.lift modularJ
    (by
      intro z w h
      change z ∈ MulAction.orbit SL(2, ℤ) w at h
      obtain ⟨γ, rfl⟩ := h
      exact modularJ_SL_invariant γ w)

@[simp]
private theorem SpecialPeriods.modularQuotientJ_projection (z : ℍ) :
    modularQuotientJ (modularOrbitProjection z) = modularJ z :=
  rfl

private theorem SpecialPeriods.modularQuotientJ_continuous : Continuous modularQuotientJ :=
  modularJ_continuous.quotient_lift _

private theorem SpecialPeriods.modularJ_bounded_im (R : ℝ) :
    ∃ A : ℝ, ∀ z : ℍ, ‖modularJ z‖ ≤ R → z.im ≤ A := by
  have h := norm_modularJ_tendsto.eventually (Filter.eventually_gt_atTop R)
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem {z : ℍ | R < ‖modularJ z‖}).mp h
  refine ⟨A, fun z hz => ?_⟩
  by_contra hzA
  exact (not_lt_of_ge hz) (hA z (le_of_lt (lt_of_not_ge hzA)))

private theorem SpecialPeriods.modularQuotientJ_bounded_representatives (R : ℝ) :
    ∃ A : ℝ,
      ∀ x : ModularOrbitSpace,
        ‖modularQuotientJ x‖ ≤ R →
          x ∈ modularOrbitProjection '' ModularGroup.truncatedFundamentalDomain A := by
  obtain ⟨A, hA⟩ := modularJ_bounded_im R
  refine ⟨A, ?_⟩
  intro x hx
  obtain ⟨z, rfl⟩ := modularOrbitProjection_surjective x
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
  refine ⟨γ • z, ⟨hγ, hA (γ • z) ?_⟩, modularOrbitProjection_smul γ z⟩
  simpa only [modularJ_SL_invariant, modularQuotientJ_projection] using hx

private theorem SpecialPeriods.modularQuotientJ_isCompact_preimage {K : Set ℂ} (hK : IsCompact K) :
    IsCompact (modularQuotientJ ⁻¹' K) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨A, hA⟩ := modularQuotientJ_bounded_representatives R
  have hcompact :
    IsCompact (modularOrbitProjection '' ModularGroup.truncatedFundamentalDomain A) :=
    (ModularGroup.isCompact_truncatedFundamentalDomain A).image modularOrbitProjection_continuous
  exact
    hcompact.of_isClosed_subset (hK.isClosed.preimage modularQuotientJ_continuous)
      (fun x hx => hA x (hR _ hx))

private theorem SpecialPeriods.modularQuotientJ_proper : IsProperMap modularQuotientJ :=
  isProperMap_iff_isCompact_preimage.mpr
    ⟨modularQuotientJ_continuous, fun _ hK => modularQuotientJ_isCompact_preimage hK⟩

private theorem SpecialPeriods.modularQuotientJ_isClosedMap : IsClosedMap modularQuotientJ :=
  modularQuotientJ_proper.isClosedMap

private theorem
    SpecialPeriods.modularJ_compact_fibre_finite {K : Set ℍ} (hK : IsCompact K) (c : ℂ) :
    (K ∩ modularJ ⁻¹' { c }).Finite := by
  have hd : IsDiscrete (K ∩ {z : ℍ | modularJ z = c}) :=
    (modularJ_fibre_isDiscrete c).mono Set.inter_subset_right
  have h := (hK.inter_right (modularJ_fibre_isClosed c)).finite hd
  simpa only [Set.preimage, Set.mem_singleton_iff] using h

private theorem SpecialPeriods.modularQuotientJ_fibre_finite (c : ℂ) :
    (modularQuotientJ ⁻¹' { c }).Finite := by
  obtain ⟨A, hA⟩ := modularQuotientJ_bounded_representatives ‖c‖
  have hfinite :=
    modularJ_compact_fibre_finite (ModularGroup.isCompact_truncatedFundamentalDomain A) c
  apply (hfinite.image modularOrbitProjection).subset
  intro x hx
  have hxc : modularQuotientJ x = c := hx
  obtain ⟨z, hz, hzx⟩ := hA x (by rw [hxc])
  refine ⟨z, ⟨hz, ?_⟩, hzx⟩
  change modularJ z = c
  rw [← modularQuotientJ_projection, hzx, hxc]

private theorem
    SpecialPeriods.modularQuotientJ_surjective : Function.Surjective modularQuotientJ := by
  intro c
  obtain ⟨z, hz⟩ := modularJ_surjective c
  exact ⟨modularOrbitProjection z, hz⟩

private theorem SpecialPeriods.modularQuotientJ_isOpenMap : IsOpenMap modularQuotientJ :=
  IsOpenMap.of_comp modularOrbitProjection_continuous modularOrbitProjection_surjective
    modularJ_isOpenMap

private instance
    SpecialPeriods.modularGroup_continuousConstSMul : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul
    γ := ContinuousConstSMul.continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ)

private instance SpecialPeriods.modularGroup_properlyDiscontinuous :
    ProperlyDiscontinuousSMul SL(2, ℤ) ℍ := by
  constructor
  intro K L hK hL
  have hfinite : {g : GL (Fin 2) ℝ | g ∈ 𝒮ℒ ∧ (g • K ∩ L).Nonempty}.Finite :=
    (Subgroup.properlyDiscontinuousSMul_iff 𝒮ℒ).mp inferInstance hK hL
  have hpre :=
    hfinite.preimage
      (Matrix.SpecialLinearGroup.mapGL_injective (R := ℤ) (n := Fin 2) (S := ℝ)).injOn
  exact hpre.subset fun γ hγ => ⟨⟨γ, rfl⟩, hγ⟩

private theorem SpecialPeriods.modularOrbitProjection_isOpenQuotientMap :
    IsOpenQuotientMap modularOrbitProjection :=
  MulAction.isOpenQuotientMap_quotientMk

private theorem
    SpecialPeriods.modularOrbitProjection_isOpenMap : IsOpenMap modularOrbitProjection :=
  modularOrbitProjection_isOpenQuotientMap.isOpenMap

private instance SpecialPeriods.modularOrbitSpace_t2 : T2Space ModularOrbitSpace :=
  t2Space_of_properlyDiscontinuousSMul_of_t2Space

private theorem SpecialPeriods.hasDerivAt_qParam_one_mo1973_16934 (z : ℂ) :
    HasDerivAt (Function.Periodic.qParam 1)
      ((2 * Real.pi * Complex.I) * Function.Periodic.qParam 1 z) z := by
  change
    HasDerivAt (fun w : ℂ => Complex.exp ((2 * Real.pi * Complex.I) * w / 1))
      ((2 * Real.pi * Complex.I) * Complex.exp ((2 * Real.pi * Complex.I) * z / 1)) z
  simpa [Function.Periodic.qParam, mul_comm] using
    ((hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp

private theorem
    SpecialPeriods.normalizedDerivOfComplex_eq_q_mul_deriv {k : ℤ} (f : ModularForm 𝒮ℒ k)
    (z : ℍ) :
    Derivative.normalizedDerivOfComplex f z =
      Function.Periodic.qParam 1 z *
        deriv (UpperHalfPlane.cuspFunction 1 f) (Function.Periodic.qParam 1 z) := by
  have hdiff :=
    ModularFormClass.differentiableAt_cuspFunction f zero_lt_one one_mem_strictPeriods_SL
      (Function.Periodic.norm_qParam_lt_one zero_lt_one z.im_pos)
  have hcomp := hdiff.hasDerivAt.comp (z : ℂ) (hasDerivAt_qParam_one_mo1973_16934 z)
  have heq :
    (f ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (z : ℂ)]
      (fun w => UpperHalfPlane.cuspFunction 1 f (Function.Periodic.qParam 1 w)) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    have h :=
      SlashInvariantFormClass.eq_cuspFunction f (⟨w, hw⟩ : ℍ) one_mem_strictPeriods_SL one_ne_zero
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw] using h.symm
  have hd := (hcomp.congr_of_eventuallyEq heq).deriv
  rw [Derivative.normalizedDerivOfComplex, hd]
  field_simp [Complex.two_pi_I_ne_zero]

private theorem
    SpecialPeriods.normalizedDerivOfComplex_tendsto_zero {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Filter.Tendsto (Derivative.normalizedDerivOfComplex f) UpperHalfPlane.atImInfty (𝓝 0) := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f zero_lt_one one_mem_strictPeriods_SL
  have ht :=
    (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) zero_lt_one).mul
      (ha.deriv.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one))
  simpa only [MulZeroClass.zero_mul, Function.comp_def,
    ← normalizedDerivOfComplex_eq_q_mul_deriv] using ht

private theorem SpecialPeriods.E2_periodic_comp_ofComplex :
    Function.Periodic (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) (1 : ℂ) := by
  have hT (z : ℍ) : EisensteinSeries.E2 ((1 : ℝ) +ᵥ z) = EisensteinSeries.E2 z := by
    have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.T) z
    rw [ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_smul] at h
    have hd : UpperHalfPlane.denom (ModularGroup.T : SL(2, ℤ)) z = 1 := by
      rw [ModularGroup.denom_apply]
      rw [ModularGroup.coe_T]
      norm_num
    simpa only [hd, one_zpow, mul_one, EisensteinSeries.D2_T, smul_zero, sub_zero] using h
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + 1).im := by simpa using hw
    have hz : UpperHalfPlane.ofComplex (w + 1) = (1 : ℝ) +ᵥ (⟨w, hw⟩ : ℍ) := by
      apply UpperHalfPlane.ext
      simp [UpperHalfPlane.ofComplex_apply_of_im_pos hw', add_comm]
    simpa [Function.comp_apply, hz, UpperHalfPlane.ofComplex_apply_of_im_pos hw] using hT ⟨w, hw⟩
  · have hw' : (w + 1).im ≤ 0 := by simpa using le_of_not_gt hw
    simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_nonpos hw',
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (le_of_not_gt hw)]

private theorem SpecialPeriods.E2_cuspFunction_analyticAt_zero :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one E2_periodic_comp_ofComplex
    E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2

private theorem SpecialPeriods.E2_hasSum_qParam (z : ℍ) :
    HasSum
      (fun m : ℕ =>
        (if m = 0 then (1 : ℂ) else -24 * (ArithmeticFunction.sigma 1 m : ℂ)) •
          Function.Periodic.qParam 1 z ^ m)
      (EisensteinSeries.E2 z) := by
  simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one] using
    EisensteinSeries.hasSum_qExpansion_E2 (z := z)

private theorem SpecialPeriods.cuspFunction_zero_of_hasSum_mo1973_16940 (f : ℍ → ℂ) (c : ℕ → ℂ)
    (ha : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0)
    (hs : ∀ z : ℍ, HasSum (fun m => c m • Function.Periodic.qParam 1 z ^ m) (f z)) :
    UpperHalfPlane.cuspFunction 1 f 0 = c 0 := by
  have h :=
    (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction (h := 1) (f := f) (c := c) zero_lt_one ha
          hs).coeff_zero
      (fun i => Fin.elim0 i)
  simpa using h.symm

private theorem SpecialPeriods.E2_cuspFunction_zero :
    UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2 0 = 1 := by
  exact
    cuspFunction_zero_of_hasSum_mo1973_16940 EisensteinSeries.E2
      (fun m => if m = 0 then (1 : ℂ) else -24 * (ArithmeticFunction.sigma 1 m : ℂ))
      E2_cuspFunction_analyticAt_zero E2_hasSum_qParam

private theorem SpecialPeriods.E2_tendsto_one :
    Filter.Tendsto EisensteinSeries.E2 UpperHalfPlane.atImInfty (𝓝 1) := by
  have h :=
    E2_cuspFunction_analyticAt_zero.continuousAt.tendsto.comp
      (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) zero_lt_one)
  simpa only [Function.comp_def, E2_cuspFunction_zero,
    UpperHalfPlane.eq_cuspFunction _ one_ne_zero E2_periodic_comp_ofComplex] using h

private theorem
    SpecialPeriods.modularForm_tendsto_qExpansion_coeff_zero {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Filter.Tendsto f UpperHalfPlane.atImInfty (𝓝 ((UpperHalfPlane.qExpansion 1 f).coeff 0)) := by
  have h :=
    (ModularFormClass.analyticAt_cuspFunction_zero f zero_lt_one
          one_mem_strictPeriods_SL).continuousAt.tendsto.comp
      (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) zero_lt_one)
  simpa [Function.comp_def, UpperHalfPlane.qExpansion_coeff,
    SlashInvariantFormClass.eq_cuspFunction f _ one_mem_strictPeriods_SL one_ne_zero] using h

private theorem SpecialPeriods.serreDerivative_tendsto {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Filter.Tendsto (Derivative.serreDerivative k f) UpperHalfPlane.atImInfty
      (𝓝 (-(k : ℂ) / 12 * (UpperHalfPlane.qExpansion 1 f).coeff 0)) := by
  have h :=
    (normalizedDerivOfComplex_tendsto_zero f).sub
      (((tendsto_const_nhds (x := (k : ℂ) * 12⁻¹)).mul E2_tendsto_one).mul
        (modularForm_tendsto_qExpansion_coeff_zero f))
  convert h using 1
  · ext z
    rfl
  · congr 1
    ring

private theorem SpecialPeriods.serreDerivative_boundedAtImInfty {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    UpperHalfPlane.IsBoundedAtImInfty (Derivative.serreDerivative k f) :=
  (serreDerivative_tendsto f).isBigO_one ℝ

private def SpecialPeriods.serreDerivativeModularForm {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ModularForm 𝒮ℒ (k + 2)
    where
  toFun := Derivative.serreDerivative k f
  slash_action_eq' γ
    hγ := by
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
    apply Derivative.serreDerivative_slash_invariant (ModularFormClass.holo f)
    exact SlashInvariantFormClass.slash_action_eq f g (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
  holo' := Derivative.serreDerivative_mdifferentiable k (ModularFormClass.holo f)
  bdd_at_cusps'
    hc := by
    apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
    intro γ hγ
    rw [Derivative.serreDerivative_slash_invariant (ModularFormClass.holo f)
        (SlashInvariantFormClass.slash_action_eq f γ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩))]
    exact serreDerivative_boundedAtImInfty f

private theorem SpecialPeriods.serreDerivativeModularForm_qExpansion_coeff_zero {k : ℤ}
    (f : ModularForm 𝒮ℒ k) :
    (UpperHalfPlane.qExpansion 1 (serreDerivativeModularForm f)).coeff 0 =
      -(k : ℂ) / 12 * (UpperHalfPlane.qExpansion 1 f).coeff 0 := by
  apply
    tendsto_nhds_unique (modularForm_tendsto_qExpansion_coeff_zero (serreDerivativeModularForm f))
  exact serreDerivative_tendsto f

private theorem SpecialPeriods.serreDerivative_E₄ (z : ℍ) :
    Derivative.serreDerivative 4 ModularForm.E₄ z = -(ModularForm.E₆ z) / 3 := by
  have heq : serreDerivativeModularForm ModularForm.E₄ = (-1 / 3 : ℂ) • ModularForm.E₆ := by
    apply levelOne_eq_of_qExpansion_coeff_zero (by norm_num)
    rw [serreDerivativeModularForm_qExpansion_coeff_zero, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_smul,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
    norm_num
  have hz := congrArg (fun f : ModularForm 𝒮ℒ 6 => f z) heq
  change Derivative.serreDerivative 4 ModularForm.E₄ z = (-1 / 3 : ℂ) * ModularForm.E₆ z at hz
  rw [hz]
  ring

private theorem SpecialPeriods.serreDerivative_E₆ (z : ℍ) :
    Derivative.serreDerivative 6 ModularForm.E₆ z = -(ModularForm.E₄ z ^ 2) / 2 := by
  have heq :
    serreDerivativeModularForm ModularForm.E₆ =
      (-1 / 2 : ℂ) • ModularForm.E₄.mul ModularForm.E₄ := by
    apply levelOne_eq_of_qExpansion_coeff_zero (by norm_num)
    rw [serreDerivativeModularForm_qExpansion_coeff_zero, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_smul,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_mul]
    norm_num [EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩]
  have hz := congrArg (fun f : ModularForm 𝒮ℒ 8 => f z) heq
  change
    Derivative.serreDerivative 6 ModularForm.E₆ z =
      (-1 / 2 : ℂ) * (ModularForm.E₄ z * ModularForm.E₄ z) at hz
  rw [hz]
  ring

private theorem SpecialPeriods.normalizedDeriv_E₄ (z : ℍ) :
    Derivative.normalizedDerivOfComplex ModularForm.E₄ z =
      (EisensteinSeries.E2 z * ModularForm.E₄ z - ModularForm.E₆ z) / 3 := by
  have h := serreDerivative_E₄ z
  unfold Derivative.serreDerivative at h
  linear_combination h

private theorem SpecialPeriods.normalizedDeriv_E₆ (z : ℍ) :
    Derivative.normalizedDerivOfComplex ModularForm.E₆ z =
      (EisensteinSeries.E2 z * ModularForm.E₆ z - ModularForm.E₄ z ^ 2) / 2 := by
  have h := serreDerivative_E₆ z
  unfold Derivative.serreDerivative at h
  linear_combination h

private theorem SpecialPeriods.normalizedDeriv_discriminant (z : ℍ) :
    Derivative.normalizedDerivOfComplex ModularForm.discriminant z =
      EisensteinSeries.E2 z * ModularForm.discriminant z := by
  have hf :
    ModularForm.discriminant =
      (1 / 1728 : ℂ) • ((ModularForm.E₄ : ℍ → ℂ) ^ 3 - (ModularForm.E₆ : ℍ → ℂ) ^ 2) := by
    funext w
    change
      ModularForm.discriminant w = (1 / 1728 : ℂ) * (ModularForm.E₄ w ^ 3 - ModularForm.E₆ w ^ 2)
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  have h4 : MDiff (ModularForm.E₄ : ℍ → ℂ) := ModularFormClass.holo ModularForm.E₄
  have h6 : MDiff (ModularForm.E₆ : ℍ → ℂ) := ModularFormClass.holo ModularForm.E₆
  rw [hf, Derivative.normalizedDerivOfComplex_smul _ _ ((h4.pow 3).sub (h6.pow 2)),
    Derivative.normalizedDerivOfComplex_sub _ _ (h4.pow 3) (h6.pow 2),
    Derivative.normalizedDerivOfComplex_pow _ 3 h4,
    Derivative.normalizedDerivOfComplex_pow _ 2 h6]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply,
    smul_eq_mul]
  rw [normalizedDeriv_E₄, normalizedDeriv_E₆]
  ring

private theorem SpecialPeriods.deriv_eq_two_pi_I_mul_normalizedDeriv (f : ℍ → ℂ) (z : ℍ) :
    deriv (f ∘ UpperHalfPlane.ofComplex) (z : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) * Derivative.normalizedDerivOfComplex f z := by
  rw [Derivative.normalizedDerivOfComplex, ← mul_assoc, mul_inv_cancel₀ Complex.two_pi_I_ne_zero,
    one_mul]

private theorem SpecialPeriods.deriv_E₄ (z : ℍ) :
    deriv (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (z : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) / 3 *
        (EisensteinSeries.E2 z * ModularForm.E₄ z - ModularForm.E₆ z) := by
  rw [deriv_eq_two_pi_I_mul_normalizedDeriv, normalizedDeriv_E₄]
  ring

private theorem SpecialPeriods.deriv_E₆ (z : ℍ) :
    deriv (ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) (z : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) / 2 *
        (EisensteinSeries.E2 z * ModularForm.E₆ z - ModularForm.E₄ z ^ 2) := by
  rw [deriv_eq_two_pi_I_mul_normalizedDeriv, normalizedDeriv_E₆]
  ring

private theorem SpecialPeriods.deriv_discriminant (z : ℍ) :
    deriv (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex) (z : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) * EisensteinSeries.E2 z * ModularForm.discriminant z := by
  rw [deriv_eq_two_pi_I_mul_normalizedDeriv, normalizedDeriv_discriminant]
  ring

private theorem SpecialPeriods.deriv_E₄_ne_zero_of_eq_zero (z : ℍ) (hz : ModularForm.E₄ z = 0) :
    deriv (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (z : ℂ) ≠ 0 := by
  have h6 : ModularForm.E₆ z ≠ 0 := (E₄_E₆_not_both_zero z).resolve_left (by simp [hz])
  rw [deriv_E₄, hz, MulZeroClass.mul_zero, zero_sub]
  exact mul_ne_zero (div_ne_zero Complex.two_pi_I_ne_zero (by norm_num)) (neg_ne_zero.mpr h6)

private theorem SpecialPeriods.deriv_E₆_ne_zero_of_eq_zero (z : ℍ) (hz : ModularForm.E₆ z = 0) :
    deriv (ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) (z : ℂ) ≠ 0 := by
  have h4 : ModularForm.E₄ z ≠ 0 := (E₄_E₆_not_both_zero z).resolve_right (by simp [hz])
  rw [deriv_E₆, hz, MulZeroClass.mul_zero, zero_sub]
  exact
    mul_ne_zero (div_ne_zero Complex.two_pi_I_ne_zero (by norm_num))
      (neg_ne_zero.mpr (pow_ne_zero 2 h4))

private theorem SpecialPeriods.analyticOrderAt_E₄_of_eq_zero (z : ℍ) (hz : ModularForm.E₄ z = 0) :
    analyticOrderAt (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (z : ℂ) = 1 := by
  apply (modularForm_analyticAt ModularForm.E₄ z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hz
  · exact deriv_E₄_ne_zero_of_eq_zero z hz

public
theorem SpecialPeriods.analyticOrderAt_E₆_of_eq_zero (z : ℍ) (hz : ModularForm.E₆ z = 0) :
    analyticOrderAt (ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) (z : ℂ) = 1 := by
  apply (modularForm_analyticAt ModularForm.E₆ z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hz
  · exact deriv_E₆_ne_zero_of_eq_zero z hz

private theorem SpecialPeriods.discriminant_analyticAt (z : ℍ) :
    AnalyticAt ℂ (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
  modularForm_analyticAt (CuspForm.discriminant : ModularForm 𝒮ℒ 12) z

private theorem SpecialPeriods.deriv_modularJ (z : ℍ) :
    deriv (modularJ ∘ UpperHalfPlane.ofComplex) (z : ℂ) =
      -(2 * (Real.pi : ℂ) * Complex.I) * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) /
        ModularForm.discriminant z := by
  have h₄ := (modularForm_analyticAt ModularForm.E₄ z).differentiableAt.hasDerivAt
  have hΔ := (discriminant_analyticAt z).differentiableAt.hasDerivAt
  have hd :=
    (h₄.pow 3).div hΔ
      (by
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
          ModularForm.discriminant_ne_zero z)
  have he := hd.deriv
  change deriv (modularJ ∘ UpperHalfPlane.ofComplex) (z : ℂ) = _ at he
  rw [he]
  simp only [Pi.pow_apply, Function.comp_apply, UpperHalfPlane.ofComplex_apply, Nat.cast_ofNat,
    Nat.reduceSub]
  rw [deriv_E₄, deriv_discriminant]
  field_simp [ModularForm.discriminant_ne_zero z]
  ring

private theorem SpecialPeriods.deriv_modularJ_eq_zero_iff (z : ℍ) :
    deriv (modularJ ∘ UpperHalfPlane.ofComplex) (z : ℂ) = 0 ↔
      modularJ z = 0 ∨ modularJ z = 1728 := by
  rw [deriv_modularJ, modularJ_eq_zero_iff, modularJ_eq_1728_iff]
  simp [ModularForm.discriminant_ne_zero z]

private theorem SpecialPeriods.deriv_modularJ_ne_zero (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) : deriv (modularJ ∘ UpperHalfPlane.ofComplex) (z : ℂ) ≠ 0 := by
  exact fun he => ((deriv_modularJ_eq_zero_iff z).mp he).elim h₀ h₁

private theorem SpecialPeriods.discriminant_inv_order_zero (z : ℍ) :
    analyticOrderAt (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex)⁻¹ (z : ℂ) = 0 := by
  have hΔ :=
    (discriminant_analyticAt z).inv
      (by
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
          ModularForm.discriminant_ne_zero z)
  apply hΔ.analyticOrderAt_eq_zero.mpr
  simpa only [Pi.inv_apply, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    inv_ne_zero (ModularForm.discriminant_ne_zero z)

private theorem SpecialPeriods.analyticOrderAt_modularJ_of_eq_zero (z : ℍ) (hz : modularJ z = 0) :
    analyticOrderAt (modularJ ∘ UpperHalfPlane.ofComplex) (z : ℂ) = 3 := by
  have h₄ := modularForm_analyticAt ModularForm.E₄ z
  have hΔ :=
    (discriminant_analyticAt z).inv
      (by
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
          ModularForm.discriminant_ne_zero z)
  change
    analyticOrderAt
        (((ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) ^ 3) *
          (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex)⁻¹)
        (z : ℂ) =
      3
  rw [analyticOrderAt_mul (h₄.pow 3) hΔ, analyticOrderAt_pow h₄, discriminant_inv_order_zero,
    analyticOrderAt_E₄_of_eq_zero z ((modularJ_eq_zero_iff z).mp hz)]
  norm_num

private theorem
    SpecialPeriods.analyticOrderAt_modularJ_sub_1728_of_eq (z : ℍ) (hz : modularJ z = 1728) :
    analyticOrderAt (fun w : ℂ => modularJ (UpperHalfPlane.ofComplex w) - 1728) (z : ℂ) = 2 := by
  have h₆ := modularForm_analyticAt ModularForm.E₆ z
  have hΔ :=
    (discriminant_analyticAt z).inv
      (by
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
          ModularForm.discriminant_ne_zero z)
  simp_rw [modularJ_sub_1728, div_eq_mul_inv]
  change
    analyticOrderAt
        (((ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) ^ 2) *
          (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex)⁻¹)
        (z : ℂ) =
      2
  rw [analyticOrderAt_mul (h₆.pow 2) hΔ, analyticOrderAt_pow h₆, discriminant_inv_order_zero,
    analyticOrderAt_E₆_of_eq_zero z ((modularJ_eq_1728_iff z).mp hz)]
  norm_num

private def
    SpecialPeriods.modularLocalInverse (z : ℍ) (h₀ : modularJ z ≠ 0) (h₁ : modularJ z ≠ 1728) :
    ℂ → ℂ :=
  (modularJ_analyticAt z).hasStrictDerivAt.localInverse (modularJ ∘ UpperHalfPlane.ofComplex)
    (deriv (modularJ ∘ UpperHalfPlane.ofComplex) (z : ℂ)) (z : ℂ) (deriv_modularJ_ne_zero z h₀ h₁)

private theorem SpecialPeriods.modularLocalInverse_analyticAt (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) : AnalyticAt ℂ (modularLocalInverse z h₀ h₁) (modularJ z) := by
  simpa only [modularLocalInverse, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    (modularJ_analyticAt z).analyticAt_localInverse (deriv_modularJ_ne_zero z h₀ h₁)

private theorem
    SpecialPeriods.modularLocalInverse_eventually_left_inverse (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) :
    ∀ᶠ w in 𝓝 (z : ℂ), modularLocalInverse z h₀ h₁ (modularJ (UpperHalfPlane.ofComplex w)) = w :=
  (modularJ_analyticAt z).hasStrictDerivAt.eventually_left_inverse
    (deriv_modularJ_ne_zero z h₀ h₁)

private theorem
    SpecialPeriods.modularLocalInverse_eventually_right_inverse (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) :
    ∀ᶠ w in 𝓝 (modularJ z),
      modularJ (UpperHalfPlane.ofComplex (modularLocalInverse z h₀ h₁ w)) = w := by
  simpa only [modularLocalInverse, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    (modularJ_analyticAt z).hasStrictDerivAt.eventually_right_inverse
      (deriv_modularJ_ne_zero z h₀ h₁)

private def SpecialPeriods.modularRegularValues : Set ℂ :=
  ({0, 1728} : Set ℂ)ᶜ

@[simp]
private theorem SpecialPeriods.mem_modularRegularValues (c : ℂ) :
    c ∈ modularRegularValues ↔ c ≠ 0 ∧ c ≠ 1728 := by simp [modularRegularValues]

private theorem SpecialPeriods.modularJ_regular_injOn_neighbourhood (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) : ∃ U : Set ℍ, IsOpen U ∧ z ∈ U ∧ Set.InjOn modularJ U := by
  have hleft : ∀ᶠ w in 𝓝 z, modularLocalInverse z h₀ h₁ (modularJ w) = (w : ℂ) := by
    have h :=
      UpperHalfPlane.continuous_coe.continuousAt.tendsto.eventually
        (modularLocalInverse_eventually_left_inverse z h₀ h₁)
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using h
  obtain ⟨U, hU, hUo, hz⟩ := mem_nhds_iff.mp hleft
  refine ⟨U, hUo, hz, ?_⟩
  intro w hw v hv heq
  apply UpperHalfPlane.ext
  rw [← hU hw, ← hU hv, heq]

private theorem SpecialPeriods.modularQuotientJ_regular_injOn_neighbourhood (x : ModularOrbitSpace)
    (hx : modularQuotientJ x ∈ modularRegularValues) :
    ∃ V : Set ModularOrbitSpace, IsOpen V ∧ x ∈ V ∧ Set.InjOn modularQuotientJ V := by
  obtain ⟨z, rfl⟩ := modularOrbitProjection_surjective x
  obtain ⟨h₀, h₁⟩ := (mem_modularRegularValues _).mp hx
  obtain ⟨U, hUo, hz, hinj⟩ := modularJ_regular_injOn_neighbourhood z h₀ h₁
  refine ⟨modularOrbitProjection '' U, modularOrbitProjection_isOpenMap U hUo, ⟨z, hz, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩ _ ⟨v, hv, rfl⟩ h
  exact congrArg modularOrbitProjection (hinj hw hv h)

private theorem SpecialPeriods.modularQuotientJ_regular_isLocalHomeomorphOn :
    IsLocalHomeomorphOn modularQuotientJ (modularQuotientJ ⁻¹' modularRegularValues) := by
  intro x hx
  obtain ⟨V, hVo, hxV, hinj⟩ := modularQuotientJ_regular_injOn_neighbourhood x hx
  let e :=
    OpenPartialHomeomorph.ofContinuousOpen (hinj.toPartialEquiv modularQuotientJ V)
      modularQuotientJ_continuous.continuousOn modularQuotientJ_isOpenMap hVo
  exact ⟨e, hxV, rfl⟩

private theorem SpecialPeriods.modularQuotientJ_regular_isCoveringMapOn :
    IsCoveringMapOn modularQuotientJ modularRegularValues :=
  modularQuotientJ_isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun c _ => modularQuotientJ_fibre_finite c) modularQuotientJ_regular_isLocalHomeomorphOn

private abbrev SpecialPeriods.ModularRegularBase :=
  ↥modularRegularValues

private abbrev SpecialPeriods.ModularRegularOrbitSpace :=
  ↥(modularQuotientJ ⁻¹' modularRegularValues)

private def
    SpecialPeriods.modularRegularQuotientJ : ModularRegularOrbitSpace → ModularRegularBase :=
  modularRegularValues.restrictPreimage modularQuotientJ

private theorem SpecialPeriods.modularRegularQuotientJ_isCoveringMap :
    IsCoveringMap modularRegularQuotientJ :=
  modularQuotientJ_regular_isCoveringMapOn.isCoveringMap_restrictPreimage

private def SpecialPeriods.modularCuspBase (q : ℂ) : ℂ :=
  1728 * q / modularJUnit q

@[simp]
private theorem
    SpecialPeriods.modularCuspBase_zero : modularCuspBase 0 = 0 := by simp [modularCuspBase]

private theorem SpecialPeriods.modularCuspBase_analyticAt_zero : AnalyticAt ℂ modularCuspBase 0 :=
  (analyticAt_const.mul analyticAt_id).div modularJUnit_analyticAt_zero (by simp)

private theorem SpecialPeriods.modularCuspBase_hasDerivAt : HasDerivAt modularCuspBase 1728 0 := by
  have hn : HasDerivAt (fun q : ℂ => 1728 * q) 1728 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℂ)).const_mul (1728 : ℂ)
  have hu : HasDerivAt modularJUnit (deriv modularJUnit 0) 0 :=
    modularJUnit_analyticAt_zero.differentiableAt.hasDerivAt
  have hd := hn.div hu (by simp : modularJUnit 0 ≠ 0)
  change
    HasDerivAt modularCuspBase
      ((1728 * modularJUnit 0 - (1728 * (0 : ℂ)) * deriv modularJUnit 0) / modularJUnit 0 ^ 2)
      0 at hd
  simpa only [modularJUnit_zero, mul_one, MulZeroClass.mul_zero, MulZeroClass.zero_mul, sub_zero,
    one_pow, div_one] using hd

private theorem SpecialPeriods.modularCuspBase_deriv : deriv modularCuspBase 0 = 1728 :=
  modularCuspBase_hasDerivAt.deriv

private theorem SpecialPeriods.modularCuspBase_deriv_ne_zero : deriv modularCuspBase 0 ≠ 0 := by
  rw [modularCuspBase_deriv]
  norm_num

private def SpecialPeriods.modularCuspQ : ℂ → ℂ :=
  modularCuspBase_analyticAt_zero.hasStrictDerivAt.localInverse modularCuspBase
    (deriv modularCuspBase 0) 0 modularCuspBase_deriv_ne_zero

private theorem SpecialPeriods.modularCuspQ_analyticAt_zero : AnalyticAt ℂ modularCuspQ 0 := by
  simpa only [modularCuspQ, modularCuspBase_zero] using
    modularCuspBase_analyticAt_zero.analyticAt_localInverse modularCuspBase_deriv_ne_zero

private theorem SpecialPeriods.modularCuspQ_eventually_left_inverse :
    ∀ᶠ q in 𝓝 (0 : ℂ), modularCuspQ (modularCuspBase q) = q :=
  modularCuspBase_analyticAt_zero.hasStrictDerivAt.eventually_left_inverse
    modularCuspBase_deriv_ne_zero

private theorem SpecialPeriods.modularCuspQ_eventually_right_inverse :
    ∀ᶠ t in 𝓝 (0 : ℂ), modularCuspBase (modularCuspQ t) = t := by
  simpa only [modularCuspQ, modularCuspBase_zero] using
    modularCuspBase_analyticAt_zero.hasStrictDerivAt.eventually_right_inverse
      modularCuspBase_deriv_ne_zero

@[simp]
private theorem SpecialPeriods.modularCuspQ_zero : modularCuspQ 0 = 0 := by
  simpa only [modularCuspBase_zero] using modularCuspQ_eventually_left_inverse.self_of_nhds

private theorem SpecialPeriods.modularCuspQ_hasDerivAt : HasDerivAt modularCuspQ (1 / 1728) 0 := by
  simpa only [modularCuspQ, modularCuspBase_zero, modularCuspBase_deriv, one_div] using
    (modularCuspBase_analyticAt_zero.hasStrictDerivAt.to_localInverse
        modularCuspBase_deriv_ne_zero).hasDerivAt

private theorem SpecialPeriods.modularCuspQ_deriv : deriv modularCuspQ 0 = 1 / 1728 :=
  modularCuspQ_hasDerivAt.deriv

private def SpecialPeriods.modularCuspUnit : ℂ → ℂ :=
  dslope modularCuspQ 0

private theorem SpecialPeriods.modularCuspUnit_analyticAt_zero : AnalyticAt ℂ modularCuspUnit 0 :=
  modularCuspQ_analyticAt_zero.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

@[simp]
private theorem SpecialPeriods.modularCuspUnit_zero : modularCuspUnit 0 = 1 / 1728 := by
  rw [modularCuspUnit, dslope_same, modularCuspQ_deriv]

private theorem SpecialPeriods.modularCuspQ_eq_mul_unit (t : ℂ) :
    modularCuspQ t = t * modularCuspUnit t := by
  simpa only [modularCuspUnit, sub_zero, modularCuspQ_zero, smul_eq_mul] using
    (sub_smul_dslope modularCuspQ 0 t).symm

private theorem SpecialPeriods.modularCuspUnit_eventually_ne_zero :
    ∀ᶠ t in 𝓝 (0 : ℂ), modularCuspUnit t ≠ 0 :=
  modularCuspUnit_analyticAt_zero.continuousAt.eventually_ne (by simp)

private theorem SpecialPeriods.modularCuspQ_eventually_j_eq :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ), modularJInQ (modularCuspQ t) = 1728 / t := by
  filter_upwards [modularCuspQ_eventually_right_inverse.filter_mono nhdsWithin_le_nhds,
    modularCuspUnit_eventually_ne_zero.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t
    ht hu ht₀
  have ht₀' : t ≠ 0 := ht₀
  have hq : modularCuspQ t ≠ 0 := by rw [modularCuspQ_eq_mul_unit]; exact mul_ne_zero ht₀' hu
  have hj : modularJUnit (modularCuspQ t) ≠ 0 := by
    intro h
    simp [modularCuspBase, h] at ht
    exact ht₀' ht.symm
  unfold modularCuspBase at ht
  unfold modularJInQ
  rw [eq_div_iff ht₀']
  calc
    modularJUnit (modularCuspQ t) / modularCuspQ t * t =
        modularJUnit (modularCuspQ t) / modularCuspQ t *
          (1728 * modularCuspQ t / modularJUnit (modularCuspQ t)) :=
      congrArg (fun v => modularJUnit (modularCuspQ t) / modularCuspQ t * v) ht.symm
    _ = 1728 := by field_simp

private theorem SpecialPeriods.modularCuspBase_eq_div_j (q : ℂ) :
    modularCuspBase q = 1728 / modularJInQ q := by
  rw [modularCuspBase, modularJInQ, div_div_eq_mul_div]

private theorem SpecialPeriods.modularJInQ_injOn_small_disc :
    ∃ r : ℝ, 0 < r ∧ Set.InjOn modularJInQ (Metric.ball 0 r) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp modularCuspQ_eventually_left_inverse
  refine ⟨r, hr, ?_⟩
  intro q hq w hw he
  calc
    q = modularCuspQ (modularCuspBase q) := (hball hq).symm
    _ = modularCuspQ (modularCuspBase w) := by
      rw [modularCuspBase_eq_div_j, he, ← modularCuspBase_eq_div_j]
    _ = w := hball hw

private theorem SpecialPeriods.modularOrbitProjection_eq_of_qParam_eq {z w : ℍ}
    (hq : Function.Periodic.qParam 1 (z : ℂ) = Function.Periodic.qParam 1 (w : ℂ)) :
    modularOrbitProjection z = modularOrbitProjection w := by
  obtain ⟨m, hm⟩ :=
    Function.Periodic.qParam_left_inv_mod_period (h := (1 : ℝ)) one_ne_zero (z : ℂ)
  obtain ⟨n, hn⟩ :=
    Function.Periodic.qParam_left_inv_mod_period (h := (1 : ℝ)) one_ne_zero (w : ℂ)
  have he : (z : ℂ) + (m : ℂ) = (w : ℂ) + (n : ℂ) := by
    simpa only [Complex.ofReal_one, mul_one] using
      hm.symm.trans ((congrArg (Function.Periodic.invQParam 1) hq).trans hn)
  have htw : ModularGroup.T ^ (m - n) • z = w := by
    apply UpperHalfPlane.ext
    rw [ModularGroup.coe_T_zpow_smul_eq, Int.cast_sub]
    linear_combination he
  rw [← htw, modularOrbitProjection_smul]

private theorem SpecialPeriods.modularJ_high_im_orbit_separation :
    ∃ A : ℝ,
      ∀ z w : ℍ,
        A ≤ z.im →
          A ≤ w.im →
            modularJ z = modularJ w → modularOrbitProjection z = modularOrbitProjection w := by
  obtain ⟨r, hr, hinj⟩ := modularJInQ_injOn_small_disc
  have hevent :
    {z : ℍ | Function.Periodic.qParam 1 (z : ℂ) ∈ Metric.ball 0 r} ∈ UpperHalfPlane.atImInfty :=
    (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one).eventually (Metric.ball_mem_nhds 0 hr)
  obtain ⟨A, hA⟩ := UpperHalfPlane.atImInfty_mem _ |>.mp hevent
  refine ⟨A, fun z w hz hw hj => modularOrbitProjection_eq_of_qParam_eq ?_⟩
  apply hinj (hA z hz) (hA w hw)
  simpa only [modularJInQ_qParam] using hj

private theorem SpecialPeriods.modularQuotientJ_large_norm_injective :
    ∃ R : ℝ,
      ∀ x y : ModularOrbitSpace,
        R < ‖modularQuotientJ x‖ → modularQuotientJ x = modularQuotientJ y → x = y := by
  obtain ⟨A, hA⟩ := modularJ_high_im_orbit_separation
  have hcompact := ModularGroup.isCompact_truncatedFundamentalDomain A
  obtain ⟨R, hR⟩ := hcompact.exists_bound_of_continuousOn modularJ_continuous.continuousOn
  refine ⟨R, ?_⟩
  intro x y hx hxy
  obtain ⟨z, rfl⟩ := modularOrbitProjection_surjective x
  obtain ⟨w, rfl⟩ := modularOrbitProjection_surjective y
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
  obtain ⟨δ, hδ⟩ := ModularGroup.exists_smul_mem_fd w
  have hzlarge : R < ‖modularJ (γ • z)‖ := by
    simpa only [modularJ_SL_invariant, modularQuotientJ_projection] using hx
  have hwlarge : R < ‖modularJ (δ • w)‖ := by
    simpa only [modularJ_SL_invariant, modularQuotientJ_projection, hxy] using hx
  have hzheight : A ≤ (γ • z).im := by
    by_contra h
    exact (not_lt_of_ge (hR (γ • z) ⟨hγ, (lt_of_not_ge h).le⟩)) hzlarge
  have hwheight : A ≤ (δ • w).im := by
    by_contra h
    exact (not_lt_of_ge (hR (δ • w) ⟨hδ, (lt_of_not_ge h).le⟩)) hwlarge
  have heq : modularJ (γ • z) = modularJ (δ • w) := by
    simpa only [modularJ_SL_invariant, modularQuotientJ_projection] using hxy
  simpa only [modularOrbitProjection_smul] using hA _ _ hzheight hwheight heq

private theorem SpecialPeriods.modularQuotientJ_unique_fibre_at_large_values :
    ∃ R : ℝ, 0 < R ∧ ∀ c : ℂ, R < ‖c‖ → ∃! x : ModularOrbitSpace, modularQuotientJ x = c := by
  obtain ⟨R, hR⟩ := modularQuotientJ_large_norm_injective
  refine ⟨Max.max R 0 + 1, by positivity, ?_⟩
  intro c hc
  obtain ⟨x, hx⟩ := modularQuotientJ_surjective c
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply hR y x
  · rw [hy]
    exact
      (lt_of_le_of_lt (le_max_left R 0) (lt_add_of_pos_right (Max.max R 0) zero_lt_one)).trans hc
  · exact hy.trans hx.symm

end Mathoverflow1973

end
