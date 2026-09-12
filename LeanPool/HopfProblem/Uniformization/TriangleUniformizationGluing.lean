/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SpecialPeriods6
public import LeanPool.HopfProblem.HomologyOfX.ThreefoldGluing1
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Foundations.TwoAffineCharts
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods3
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.Foundations.Complex
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldGluing1

/-!
# Hopf problem: uniformization · triangle uniformization gluing

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

private theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_continuousOn_translate
    (D : TriangleUniformizationGluing.BoundaryMap) (g : SpecialPeriods.TriangleGroup) :
    ContinuousOn D.upstairsMap
      (SpecialPeriods.triangleGeometricRepresentation g '' SpecialPeriods.Triangle.fordRegion) := by
  have hc : Continuous (SpecialPeriods.triangleGeometricRepresentation g⁻¹ : ℍ → ℍ) :=
    (SpecialPeriods.triangleGeometricRepresentation_holomorphic g⁻¹).continuous
  have hm :
    Set.MapsTo (SpecialPeriods.triangleGeometricRepresentation g⁻¹)
      (SpecialPeriods.triangleGeometricRepresentation g '' SpecialPeriods.Triangle.fordRegion)
      SpecialPeriods.Triangle.fordRegion := by
    rintro z ⟨w, hw, rfl⟩
    rw [map_inv]
    change
      (SpecialPeriods.triangleGeometricRepresentation g).symm
          (SpecialPeriods.triangleGeometricRepresentation g w) ∈
        _
    rw [(SpecialPeriods.triangleGeometricRepresentation g).symm_apply_apply w]
    exact hw
  exact
    (D.foldedFordMap_continuousOn.comp hc.continuousOn hm).congr (D.upstairsMap_eqOn_translate g)

private theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_continuous
    (D : TriangleUniformizationGluing.BoundaryMap) : Continuous D.upstairsMap := by
  apply
    SpecialPeriods.Triangle.fordRegion_translates_locallyFinite.continuous
      SpecialPeriods.triangle_translates_fordRegion_cover
  · intro g
    have h :=
      (SpecialPeriods.triangleGeometricBiholomorph g).toHomeomorph.isClosedMap
        SpecialPeriods.Triangle.fordRegion SpecialPeriods.Triangle.fordRegion_closed
    have he :
      ((SpecialPeriods.triangleGeometricBiholomorph g).toHomeomorph : ℍ → ℍ) =
        SpecialPeriods.triangleGeometricRepresentation g :=
      rfl
    rwa [he] at h
  · exact D.upstairsMap_continuousOn_translate

private theorem TriangleUniformizationGluing.BoundaryMap.quotientMap_continuous
    (D : TriangleUniformizationGluing.BoundaryMap) : Continuous D.quotientMap := by
  apply SpecialPeriods.triangleOrbitProjection_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
  exact D.upstairsMap_continuous

private abbrev TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    SpecialPeriods.TriangleOrbitSpace → ℂ :=
  D.toBoundaryMap.quotientMap

private abbrev TriangleUniformizationGluing.SignedHalfPlaneMap.upstairsMap
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : ℍ → ℂ :=
  D.toBoundaryMap.upstairsMap

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap_continuous
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : Continuous D.quotientMap :=
  D.toBoundaryMap.quotientMap_continuous

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap_surjective
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : Function.Surjective D.quotientMap := by
  intro w
  obtain ⟨z, hz, he⟩ := D.foldedFordMap_surjOn (Set.mem_univ w)
  refine ⟨SpecialPeriods.triangleOrbitProjection z, ?_⟩
  change D.toBoundaryMap.quotientMap (SpecialPeriods.triangleOrbitProjection z) = w
  rw [D.toBoundaryMap.quotientMap_projection z hz]
  exact he

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap_injective
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : Function.Injective D.quotientMap := by
  intro q r he
  have hfold :
    D.foldedFordMap (TriangleUniformizationGluing.fordRepresentative q) =
      D.foldedFordMap (TriangleUniformizationGluing.fordRepresentative r) :=
    he
  have hor :=
    (SpecialPeriods.Triangle.orbitProjection_eq_iff_fordRegion
          (TriangleUniformizationGluing.fordRepresentative q).property
          (TriangleUniformizationGluing.fordRepresentative r).property).mpr
      ((D.foldedFordMap_eq_iff (TriangleUniformizationGluing.fordRepresentative q).property
            (TriangleUniformizationGluing.fordRepresentative r).property).mp
        hfold)
  simpa only [TriangleUniformizationGluing.fordRepresentative_projection] using hor

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap_bijective
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : Function.Bijective D.quotientMap :=
  ⟨D.quotientMap_injective, D.quotientMap_surjective⟩

private def TriangleUniformizationGluing.SignedHalfPlaneMap.quotientEquiv
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    SpecialPeriods.TriangleOrbitSpace ≃ ℂ :=
  Equiv.ofBijective D.quotientMap D.quotientMap_bijective

private theorem TriangleUniformizationGluing.BoundaryMap.quotientMap_preimage_eq_image_ford
    (D : TriangleUniformizationGluing.BoundaryMap) (K : Set ℂ) :
    D.quotientMap ⁻¹' K =
      SpecialPeriods.triangleOrbitProjection ''
        (SpecialPeriods.Triangle.fordRegion ∩ D.foldedFordMap ⁻¹' K) := by
  ext q
  constructor
  · intro hq
    exact
      ⟨TriangleUniformizationGluing.fordRepresentative q,
        ⟨(TriangleUniformizationGluing.fordRepresentative q).property, hq⟩,
        TriangleUniformizationGluing.fordRepresentative_projection q⟩
  · rintro ⟨z, ⟨hz, hzK⟩, rfl⟩
    change D.quotientMap (SpecialPeriods.triangleOrbitProjection z) ∈ K
    rw [D.quotientMap_projection z hz]
    exact hzK

private theorem TriangleUniformizationGluing.BoundaryMap.quotientMap_isProperMap
    (D : TriangleUniformizationGluing.BoundaryMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z)) :
    IsProperMap D.quotientMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨D.quotientMap_continuous, ?_⟩
  intro K hK
  rw [D.quotientMap_preimage_eq_image_ford K]
  exact
    (D.foldedFordMap_compact_preimage hlocal K hK).image
      SpecialPeriods.triangleOrbitProjection_continuous

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap_isProperMap
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z)) :
    IsProperMap D.quotientMap :=
  D.toBoundaryMap.quotientMap_isProperMap hlocal

private def TriangleUniformizationGluing.SignedHalfPlaneMap.quotientHomeomorph
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z)) :
    SpecialPeriods.TriangleOrbitSpace ≃ₜ ℂ :=
  D.quotientEquiv.toHomeomorphOfContinuousClosed D.quotientMap_continuous
    (D.quotientMap_isProperMap hlocal).isClosedMap

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientHomeomorph_projection
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z)) (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) :
    D.quotientHomeomorph hlocal (SpecialPeriods.triangleOrbitProjection z) = D.foldedFordMap z :=
  D.toBoundaryMap.quotientMap_projection z hz

private def TriangleUniformizationGluing.SignedHalfPlaneMap.compactifiedHomeomorph
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z)) :
    SpecialPeriods.TriangleCompactifiedOrbitSpace ≃ₜ RiemannSphere :=
  (D.quotientHomeomorph hlocal).onePointCongr

@[simp]
private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.compactifiedHomeomorph_openInclusion
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (q : SpecialPeriods.TriangleOrbitSpace) :
    D.compactifiedHomeomorph hlocal (SpecialPeriods.triangleOpenInclusion q) =
      (D.quotientMap q : RiemannSphere) :=
  rfl

private def SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph :
    SpecialPeriods.TriangleOrbitSpace ≃ₜ ℂ :=
  RiemannMapping.triangleSignedHalfPlaneMap.quotientHomeomorph
    RiemannMapping.triangleSignedHalfPlaneMap_isProperMap

private def SpecialPeriods.Triangle.triangleSphereUniformizationHomeomorph :
    SpecialPeriods.TriangleCompactifiedOrbitSpace ≃ₜ RiemannSphere :=
  RiemannMapping.triangleSignedHalfPlaneMap.compactifiedHomeomorph
    RiemannMapping.triangleSignedHalfPlaneMap_isProperMap

@[simp]
private theorem SpecialPeriods.Triangle.triangleSphereUniformizationHomeomorph_openInclusion
    (q : SpecialPeriods.TriangleOrbitSpace) :
    triangleSphereUniformizationHomeomorph (SpecialPeriods.triangleOpenInclusion q) =
      ((trianglePlaneUniformizationHomeomorph q : ℂ) : RiemannSphere) :=
  rfl

private theorem SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph_projection {z : ℍ}
    (hz : z ∈ halfFordRegion) :
    trianglePlaneUniformizationHomeomorph (SpecialPeriods.triangleOrbitProjection z) =
      RiemannMapping.triangleSignedHalfPlaneMap z := by
  change
    RiemannMapping.triangleSignedHalfPlaneMap.quotientHomeomorph
        RiemannMapping.triangleSignedHalfPlaneMap_isProperMap
        (SpecialPeriods.triangleOrbitProjection z) =
      _
  rw [RiemannMapping.triangleSignedHalfPlaneMap.quotientHomeomorph_projection
      RiemannMapping.triangleSignedHalfPlaneMap_isProperMap z hz.1]
  exact RiemannMapping.triangleSignedHalfPlaneMap.toBoundaryMap.foldedFordMap_of_left hz.2

@[simp]
private theorem SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph_centerOne :
    trianglePlaneUniformizationHomeomorph SpecialPeriods.triangleOrbitCenterOne = 0 := by
  rw [show
      SpecialPeriods.triangleOrbitCenterOne = SpecialPeriods.triangleOrbitProjection centerOne
      from rfl,
    trianglePlaneUniformizationHomeomorph_projection centerOne_mem_halfFordRegion,
    RiemannMapping.triangleSignedHalfPlaneMap_centerOne]

@[simp]
private theorem SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph_centerTwo :
    trianglePlaneUniformizationHomeomorph SpecialPeriods.triangleOrbitCenterTwo = 1 := by
  rw [show
      SpecialPeriods.triangleOrbitCenterTwo = SpecialPeriods.triangleOrbitProjection centerTwo
      from rfl,
    trianglePlaneUniformizationHomeomorph_projection centerTwo_mem_halfFordRegion,
    RiemannMapping.triangleSignedHalfPlaneMap_centerTwo]

private theorem SpecialPeriods.Triangle.triangleSphereUniformizationHomeomorph_centerOne :
    triangleSphereUniformizationHomeomorph
        (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
      ((0 : ℂ) : RiemannSphere) := by
  rw [triangleSphereUniformizationHomeomorph_openInclusion,
    trianglePlaneUniformizationHomeomorph_centerOne]

private theorem SpecialPeriods.Triangle.triangleSphereUniformizationHomeomorph_centerTwo :
    triangleSphereUniformizationHomeomorph
        (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
      ((1 : ℂ) : RiemannSphere) := by
  rw [triangleSphereUniformizationHomeomorph_openInclusion,
    trianglePlaneUniformizationHomeomorph_centerTwo]

private def TriangleUniformizationGluing.ContinuousRemovable (Ω S : Set ℂ) : Prop :=
  ∀ V : Set ℂ,
    IsOpen V →
      V ⊆ Ω →
        ∀ f : ℂ → ℂ,
          ContinuousOn f V → (∀ z ∈ V \ S, DifferentiableAt ℂ f z) → DifferentiableOn ℂ f V

private theorem TriangleUniformizationGluing.continuousRemovable_empty (Ω : Set ℂ) :
    ContinuousRemovable Ω ∅ := by
  intro V _ _ f _ hd z hz
  exact (hd z ⟨hz, Set.notMem_empty z⟩).differentiableWithinAt

private theorem TriangleUniformizationGluing.ContinuousRemovable.mono_domain {Ω Ω' S : Set ℂ}
    (hS : TriangleUniformizationGluing.ContinuousRemovable Ω S) (hΩ : Ω' ⊆ Ω) :
    TriangleUniformizationGluing.ContinuousRemovable Ω' S := by
  intro V hV hVΩ f hf hd
  exact hS V hV (hVΩ.trans hΩ) f hf hd

private theorem TriangleUniformizationGluing.ContinuousRemovable.mono_set_on {Ω S T : Set ℂ}
    (hS : TriangleUniformizationGluing.ContinuousRemovable Ω S) (hTS : ∀ z ∈ Ω, z ∈ T → z ∈ S) :
    TriangleUniformizationGluing.ContinuousRemovable Ω T := by
  intro V hV hVΩ f hf hd
  apply hS V hV hVΩ f hf
  intro z hz
  exact hd z ⟨hz.1, fun hT => hz.2 (hTS z (hVΩ hz.1) hT)⟩

private theorem TriangleUniformizationGluing.ContinuousRemovable.mono_set {Ω S T : Set ℂ}
    (hS : TriangleUniformizationGluing.ContinuousRemovable Ω S) (hTS : T ⊆ S) :
    TriangleUniformizationGluing.ContinuousRemovable Ω T :=
  hS.mono_set_on (fun _ _ hz => hTS hz)

private theorem TriangleUniformizationGluing.continuousRemovable_realAxis (Ω : Set ℂ) :
    ContinuousRemovable Ω {z : ℂ | z.im = 0} := by
  intro V hV _ f hf hd
  exact
    SchwarzReflection.differentiableOn_of_continuousOn_off_real hV hf
      (fun z hz him => hd z ⟨hz, him⟩)

private theorem TriangleUniformizationGluing.ContinuousRemovable.preimage {Ω S : Set ℂ}
    {e : OpenPartialHomeomorph ℂ ℂ}
    (hS : TriangleUniformizationGluing.ContinuousRemovable (e '' Ω) S) (hΩ : Ω ⊆ e.source)
    (he : DifferentiableOn ℂ e e.source) (he' : DifferentiableOn ℂ e.symm e.target) :
    TriangleUniformizationGluing.ContinuousRemovable Ω (e ⁻¹' S) := by
  intro V hV hVΩ f hf hd
  have hVs : V ⊆ e.source := hVΩ.trans hΩ
  have hW : IsOpen (e '' V) := e.isOpen_image_of_subset_source hV hVs
  have hWt : e '' V ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hVs hz)
  have hinv : Set.MapsTo e.symm (e '' V) V := by
    rintro y ⟨z, hz, rfl⟩
    simpa only [e.left_inv (hVs hz)] using hz
  have hc : ContinuousOn (f ∘ e.symm) (e '' V) := hf.comp (e.symm.continuousOn.mono hWt) hinv
  have hd' : ∀ y ∈ (e '' V) \ S, DifferentiableAt ℂ (f ∘ e.symm) y := by
    intro y hy
    have hnot : e.symm y ∉ e ⁻¹' S := by
      change e (e.symm y) ∉ S
      rw [e.right_inv (hWt hy.1)]
      exact hy.2
    exact
      (hd (e.symm y) ⟨hinv hy.1, hnot⟩).comp y
        (he'.differentiableAt (e.open_target.mem_nhds (hWt hy.1)))
  have hdiff := hS (e '' V) hW (Set.image_mono hVΩ) (f ∘ e.symm) hc hd'
  have hcomp : DifferentiableOn ℂ ((f ∘ e.symm) ∘ e) V :=
    hdiff.comp (he.mono hVs) (fun z hz => ⟨z, hz, rfl⟩)
  apply hcomp.congr
  intro z hz
  simp only [Function.comp_apply, e.left_inv (hVs hz)]

private theorem TriangleUniformizationGluing.ContinuousRemovable.image {Ω S : Set ℂ}
    {e : OpenPartialHomeomorph ℂ ℂ} (hS : TriangleUniformizationGluing.ContinuousRemovable Ω S)
    (hΩ : Ω ⊆ e.source) (hSΩ : S ⊆ Ω) (he : DifferentiableOn ℂ e e.source)
    (he' : DifferentiableOn ℂ e.symm e.target) :
    TriangleUniformizationGluing.ContinuousRemovable (e '' Ω) (e '' S) := by
  have htarget : e '' Ω ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hΩ hz)
  have hinverse : e.symm '' (e '' Ω) = Ω := e.toPartialEquiv.symm_image_image_of_subset_source hΩ
  have hS' : TriangleUniformizationGluing.ContinuousRemovable (e.symm '' (e '' Ω)) S := by
    rwa [hinverse]
  have hp : TriangleUniformizationGluing.ContinuousRemovable (e '' Ω) (e.symm ⁻¹' S) :=
    hS'.preimage (e := e.symm) htarget he' he
  apply hp.mono_set_on
  rintro y _ ⟨z, hz, rfl⟩
  change e.symm (e z) ∈ S
  simpa only [e.left_inv (hΩ (hSΩ hz))] using hz

private theorem TriangleUniformizationGluing.continuousRemovable_preimage_realAxis
    (e : OpenPartialHomeomorph ℂ ℂ) (Ω : Set ℂ) (hΩ : Ω ⊆ e.source)
    (he : DifferentiableOn ℂ e e.source) (he' : DifferentiableOn ℂ e.symm e.target) :
    ContinuousRemovable Ω {z : ℂ | (e z).im = 0} :=
  (continuousRemovable_realAxis (e '' Ω)).preimage hΩ he he'

private def TriangleUniformizationGluing.verticalLineChart_mo1973_19880 (a : ℝ) : ℂ ≃ₜ ℂ
    where
  toFun z := Complex.I * (z - (a : ℂ))
  invFun w := -Complex.I * w + (a : ℂ)
  left_inv z := by ring_nf; simp
  right_inv w := by ring_nf; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem TriangleUniformizationGluing.verticalLineChart_differentiable_mo1973_19881
    (a : ℝ) : Differentiable ℂ (verticalLineChart_mo1973_19880 a) := fun _ =>
  (differentiableAt_const Complex.I).mul (differentiableAt_id.sub_const _)

private theorem TriangleUniformizationGluing.verticalLineChart_symm_differentiable_mo1973_19882
    (a : ℝ) : Differentiable ℂ (verticalLineChart_mo1973_19880 a).symm := fun _ =>
  ((differentiableAt_const (-Complex.I)).mul differentiableAt_id).add_const _

private theorem TriangleUniformizationGluing.continuousRemovable_verticalLine (a : ℝ) :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet {z : ℂ | z.re = a} := by
  have h :=
    continuousRemovable_preimage_realAxis
      (verticalLineChart_mo1973_19880 a).toOpenPartialHomeomorph UpperHalfPlane.upperHalfPlaneSet
      (fun z _ => Set.mem_univ z)
      (verticalLineChart_differentiable_mo1973_19881 a).differentiableOn
      (verticalLineChart_symm_differentiable_mo1973_19882 a).differentiableOn
  apply h.mono_set
  intro z hz
  change (Complex.I * (z - (a : ℂ))).im = 0
  simpa using sub_eq_zero.mpr hz

private def TriangleUniformizationGluing.translatedUnitCircleChart_mo1973_19884 (a : ℝ) :
    OpenPartialHomeomorph ℂ ℂ :=
  (Homeomorph.subRight ((a : ℂ) + 1)).transOpenPartialHomeomorph
    SpecialPeriods.Triangle.circleBoundaryChart

private theorem
  TriangleUniformizationGluing.upperHalfPlane_subset_translatedUnitCircleChart_source_mo1973_19885
    (a : ℝ) :
    UpperHalfPlane.upperHalfPlaneSet ⊆ (translatedUnitCircleChart_mo1973_19884 a).source := by
  intro z hz
  change z - ((a : ℂ) + 1) + 2 ≠ 0
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.one_im, Complex.im_ofNat,
    add_zero, sub_zero, Complex.zero_im] at hi
  exact (show 0 < z.im from hz).ne' hi

private theorem
  TriangleUniformizationGluing.translatedUnitCircleChart_differentiableOn_mo1973_19886 (a : ℝ) :
    DifferentiableOn ℂ (translatedUnitCircleChart_mo1973_19884 a)
      (translatedUnitCircleChart_mo1973_19884 a).source := by
  intro z hz
  change
    DifferentiableWithinAt ℂ
      (fun w : ℂ => SpecialPeriods.Triangle.circleStraighten (w - ((a : ℂ) + 1))) _ z
  exact
    ((SpecialPeriods.Triangle.circleStraighten_analyticOnNhd _ hz).differentiableAt.comp z
        (differentiableAt_id.sub_const _)).differentiableWithinAt

private theorem
  TriangleUniformizationGluing.translatedUnitCircleChart_symm_differentiableOn_mo1973_19887
    (a : ℝ) :
    DifferentiableOn ℂ (translatedUnitCircleChart_mo1973_19884 a).symm
      (translatedUnitCircleChart_mo1973_19884 a).target := by
  intro z hz
  change
    DifferentiableWithinAt ℂ
      (fun w : ℂ => SpecialPeriods.Triangle.circleUnstraighten w + ((a : ℂ) + 1)) _ z
  exact
    ((SpecialPeriods.Triangle.circleUnstraighten_analyticOnNhd z hz).differentiableAt.add_const
        _).differentiableWithinAt

private theorem TriangleUniformizationGluing.translatedUnitCircleChart_im_eq_zero_iff_mo1973_19888
    (a : ℝ) {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    (translatedUnitCircleChart_mo1973_19884 a z).im = 0 ↔ ‖z - (a : ℂ)‖ = 1 := by
  change (SpecialPeriods.Triangle.circleStraighten (z - ((a : ℂ) + 1))).im = 0 ↔ _
  rw [SpecialPeriods.Triangle.circleStraighten_im_eq_zero_iff (z := z - ((a : ℂ) + 1))
      (upperHalfPlane_subset_translatedUnitCircleChart_source_mo1973_19885 a hz)]
  rw [show z - ((a : ℂ) + 1) + 1 = z - (a : ℂ) by ring]

private theorem TriangleUniformizationGluing.continuousRemovable_unitCircle (a : ℝ) :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet {z : ℂ | ‖z - (a : ℂ)‖ = 1} := by
  have h :=
    continuousRemovable_preimage_realAxis (translatedUnitCircleChart_mo1973_19884 a)
      UpperHalfPlane.upperHalfPlaneSet
      (upperHalfPlane_subset_translatedUnitCircleChart_source_mo1973_19885 a)
      (translatedUnitCircleChart_differentiableOn_mo1973_19886 a)
      (translatedUnitCircleChart_symm_differentiableOn_mo1973_19887 a)
  exact
    h.mono_set_on
      (fun z hz hnorm => (translatedUnitCircleChart_im_eq_zero_iff_mo1973_19888 a hz).mpr hnorm)

private def TriangleUniformizationGluing.triangleAmbientMap (g : SpecialPeriods.TriangleGroup) :
    OpenPartialHomeomorph ℂ ℂ :=
  (UpperHalfPlane.ofComplex.trans
        (SpecialPeriods.triangleGeometricBiholomorph
            g).toHomeomorph.toOpenPartialHomeomorph).trans
    UpperHalfPlane.ofComplex.symm

@[simp]
private theorem TriangleUniformizationGluing.triangleAmbientMap_source
    (g : SpecialPeriods.TriangleGroup) :
    (triangleAmbientMap g).source = UpperHalfPlane.upperHalfPlaneSet := by
  simp [triangleAmbientMap, UpperHalfPlane.ofComplex, UpperHalfPlane.range_coe]

@[simp]
private theorem TriangleUniformizationGluing.triangleAmbientMap_target
    (g : SpecialPeriods.TriangleGroup) :
    (triangleAmbientMap g).target = UpperHalfPlane.upperHalfPlaneSet := by
  simp [triangleAmbientMap, UpperHalfPlane.ofComplex, UpperHalfPlane.range_coe]

private theorem
    TriangleUniformizationGluing.triangleAmbientMap_apply (g : SpecialPeriods.TriangleGroup)
    (z : ℂ) :
    triangleAmbientMap g z =
      (SpecialPeriods.triangleGeometricRepresentation g (UpperHalfPlane.ofComplex z) : ℂ) :=
  rfl

@[simp]
private theorem TriangleUniformizationGluing.triangleAmbientMap_apply_coe
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    triangleAmbientMap g (z : ℂ) = (SpecialPeriods.triangleGeometricRepresentation g z : ℂ) := by
  rw [triangleAmbientMap_apply, UpperHalfPlane.ofComplex_apply]

private theorem TriangleUniformizationGluing.triangleAmbientMap_symm_apply
    (g : SpecialPeriods.TriangleGroup) (z : ℂ) :
    (triangleAmbientMap g).symm z =
      (SpecialPeriods.triangleGeometricRepresentation g⁻¹ (UpperHalfPlane.ofComplex z) : ℂ) := by
  rw [map_inv]
  rfl

@[simp]
private theorem
    TriangleUniformizationGluing.triangleAmbientMap_symm (g : SpecialPeriods.TriangleGroup) :
    (triangleAmbientMap g).symm = triangleAmbientMap g⁻¹ := by
  apply OpenPartialHomeomorph.ext
  · intro z
    rw [triangleAmbientMap_symm_apply, triangleAmbientMap_apply]
  · intro z
    simp only [OpenPartialHomeomorph.symm_symm, triangleAmbientMap_apply,
      triangleAmbientMap_symm_apply, inv_inv]
  · simp only [OpenPartialHomeomorph.symm_source, triangleAmbientMap_source,
      triangleAmbientMap_target]

private theorem TriangleUniformizationGluing.triangleAmbientMap_differentiableOn
    (g : SpecialPeriods.TriangleGroup) :
    DifferentiableOn ℂ (triangleAmbientMap g) (triangleAmbientMap g).source := by
  rw [triangleAmbientMap_source]
  exact
    UpperHalfPlane.mdifferentiable_iff.mp
      (UpperHalfPlane.mdifferentiable_coe.comp
        ((SpecialPeriods.triangleGeometricRepresentation_holomorphic g).mdifferentiable
          (by simp)))

private theorem TriangleUniformizationGluing.triangleAmbientMap_symm_differentiableOn
    (g : SpecialPeriods.TriangleGroup) :
    DifferentiableOn ℂ (triangleAmbientMap g).symm (triangleAmbientMap g).target := by
  simpa only [triangleAmbientMap_source, triangleAmbientMap_target, triangleAmbientMap_symm] using
    triangleAmbientMap_differentiableOn g⁻¹

private theorem TriangleUniformizationGluing.triangleAmbientMap_image_upperHalfPlaneSet
    (g : SpecialPeriods.TriangleGroup) :
    triangleAmbientMap g '' UpperHalfPlane.upperHalfPlaneSet = UpperHalfPlane.upperHalfPlaneSet :=
  by
  simpa only [triangleAmbientMap_source, triangleAmbientMap_target] using
    (triangleAmbientMap g).image_source_eq_target

private theorem TriangleUniformizationGluing.triangleAmbientMap_image_coe
    (g : SpecialPeriods.TriangleGroup) (S : Set ℍ) :
    triangleAmbientMap g '' (((↑) : ℍ → ℂ) '' S) =
      ((↑) : ℍ → ℂ) '' (SpecialPeriods.triangleGeometricRepresentation g '' S) := by
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro z _
  exact triangleAmbientMap_apply_coe g z

private def SpecialPeriods.Triangle.halfEdgeCarrier : Fin 3 → Set ℍ :=
  ![{z | z.re = stripLeft}, {z | z.re = -(1 / 2)}, {z | ‖(z : ℂ) + 1‖ = 1}]

private def SpecialPeriods.Triangle.halfFordEdge (k : Fin 3) : Set ℍ :=
  halfFordRegion ∩ halfEdgeCarrier k

private theorem SpecialPeriods.Triangle.halfEdgeCarrier_isClosed (k : Fin 3) :
    IsClosed (halfEdgeCarrier k) := by
  fin_cases k
  · exact isClosed_eq UpperHalfPlane.continuous_re continuous_const
  · exact isClosed_eq UpperHalfPlane.continuous_re continuous_const
  · exact isClosed_eq (UpperHalfPlane.continuous_coe.add continuous_const).norm continuous_const

private theorem
    SpecialPeriods.Triangle.halfFordEdge_isClosed (k : Fin 3) : IsClosed (halfFordEdge k) :=
  halfFordRegion_isClosed.inter (halfEdgeCarrier_isClosed k)

private theorem SpecialPeriods.Triangle.halfFordEdge_subset_region (k : Fin 3) :
    halfFordEdge k ⊆ halfFordRegion :=
  Set.inter_subset_left

private theorem SpecialPeriods.Triangle.halfFordEdge_subset_boundary (k : Fin 3) :
    halfFordEdge k ⊆ halfFordRegion \ halfFordInterior := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  intro hi
  have hc := hz.2
  fin_cases k
  · change z.re = stripLeft at hc
    exact (ne_of_gt hi.1.1) hc
  · change z.re = -(1 / 2) at hc
    exact (ne_of_lt hi.2) hc
  · change ‖(z : ℂ) + 1‖ = 1 at hc
    exact (ne_of_gt hi.1.2.2.1) hc

private theorem SpecialPeriods.Triangle.halfFordEdges_eq_boundary :
    (⋃ k : Fin 3, halfFordEdge k) = halfFordRegion \ halfFordInterior := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset halfFordEdge_subset_boundary
  · rintro z ⟨hz, hnot⟩
    by_cases hl : z.re = stripLeft
    · exact Set.mem_iUnion.mpr ⟨0, hz, hl⟩
    by_cases hr : z.re = -(1 / 2)
    · exact Set.mem_iUnion.mpr ⟨1, hz, hr⟩
    by_cases hn : ‖(z : ℂ) + 1‖ = 1
    · exact Set.mem_iUnion.mpr ⟨2, hz, hn⟩
    have hl' : stripLeft < z.re := lt_of_le_of_ne hz.1.1 (Ne.symm hl)
    have hr' : z.re < -(1 / 2) := lt_of_le_of_ne hz.2 hr
    have hn' : 1 < ‖(z : ℂ) + 1‖ := lt_of_le_of_ne hz.1.2.2.1 (Ne.symm hn)
    apply (hnot ?_).elim
    refine ⟨⟨hl', ?_, hn', one_lt_norm_of_re_lt_neg_half z hr' hn'⟩, hr'⟩
    linarith [stripRight_pos]

private def SpecialPeriods.Triangle.halfTriangleEdge (i : SpecialPeriods.TriangleGroup × Bool)
    (k : Fin 3) : Set ℍ :=
  halfTriangleMap i '' halfFordEdge k

private abbrev SpecialPeriods.Triangle.TriangleEdgeIndex :=
  (SpecialPeriods.TriangleGroup × Bool) × Fin 3

private theorem
    SpecialPeriods.Triangle.halfTriangleEdge_eq (i : SpecialPeriods.TriangleGroup × Bool)
    (k : Fin 3) :
    halfTriangleEdge i k =
      SpecialPeriods.triangleGeometricRepresentation i.1 '' (halfFold i.2 '' halfFordEdge k) := by
  rw [Set.image_image]
  rfl

private theorem SpecialPeriods.Triangle.halfTriangleEdge_isClosed
    (i : SpecialPeriods.TriangleGroup × Bool) (k : Fin 3) : IsClosed (halfTriangleEdge i k) :=
  (halfTriangleMap i).isClosedMap _ (halfFordEdge_isClosed k)

private theorem SpecialPeriods.Triangle.halfTriangleEdge_subset_tile
    (i : SpecialPeriods.TriangleGroup × Bool) (k : Fin 3) :
    halfTriangleEdge i k ⊆ halfTriangleTile i :=
  Set.image_mono (halfFordEdge_subset_region k)

private theorem SpecialPeriods.Triangle.halfTriangleEdges_eq_boundary
    (i : SpecialPeriods.TriangleGroup × Bool) :
    (⋃ k : Fin 3, halfTriangleEdge i k) = halfTriangleTile i \ halfTriangleOpenTile i := by
  unfold halfTriangleEdge halfTriangleTile halfTriangleOpenTile
  rw [← Set.image_iUnion, halfFordEdges_eq_boundary,
    Set.image_sdiff (halfTriangleMap i).injective]

private theorem SpecialPeriods.Triangle.triangleEdges_cover_openTile_complement :
    (⋃ i : SpecialPeriods.TriangleGroup × Bool, halfTriangleOpenTile i)ᶜ ⊆
      ⋃ j : TriangleEdgeIndex, halfTriangleEdge j.1 j.2 := by
  intro z hz
  have hcover : z ∈ ⋃ i : SpecialPeriods.TriangleGroup × Bool, halfTriangleTile i := by
    rw [halfTriangleTiles_cover]
    exact Set.mem_univ z
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcover
  have hb : z ∈ ⋃ k : Fin 3, halfTriangleEdge i k := by
    rw [halfTriangleEdges_eq_boundary]
    exact ⟨hi, fun h => hz (Set.mem_iUnion.mpr ⟨i, h⟩)⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hb
  exact Set.mem_iUnion.mpr ⟨(i, k), hk⟩

private theorem SpecialPeriods.Triangle.halfTriangleEdges_locallyFinite :
    LocallyFinite (fun j : TriangleEdgeIndex => halfTriangleEdge j.1 j.2) := by
  intro z
  obtain ⟨U, hU, hfin⟩ := halfTriangleTiles_locallyFinite z
  refine ⟨U, hU, (hfin.prod (Set.finite_univ : (Set.univ : Set (Fin 3)).Finite)).subset ?_⟩
  rintro j ⟨w, hw, hwU⟩
  exact ⟨⟨w, halfTriangleEdge_subset_tile j.1 j.2 hw, hwU⟩, Set.mem_univ _⟩

private def SpecialPeriods.Triangle.triangleEdgeComplex (j : TriangleEdgeIndex) : Set ℂ :=
  ((↑) : ℍ → ℂ) '' halfTriangleEdge j.1 j.2

private theorem SpecialPeriods.Triangle.triangleEdgeComplex_relative_compl_isOpen
    (j : TriangleEdgeIndex) : IsOpen (UpperHalfPlane.upperHalfPlaneSet \ triangleEdgeComplex j) :=
  by
  have h :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap (halfTriangleEdge j.1 j.2)ᶜ
      (halfTriangleEdge_isClosed j.1 j.2).isOpen_compl
  simpa only [triangleEdgeComplex,
    Set.image_compl_eq_range_sdiff_image UpperHalfPlane.coe_injective,
    UpperHalfPlane.range_coe] using h

private theorem SpecialPeriods.Triangle.triangleEdgeComplex_locallyFinite :
    LocallyFinite
      (fun j : TriangleEdgeIndex =>
        ((↑) : UpperHalfPlane.upperHalfPlaneSet → ℂ) ⁻¹' triangleEdgeComplex j) := by
  let g : UpperHalfPlane.upperHalfPlaneSet → ℍ := fun z => ⟨z.1, z.2⟩
  have hg : Continuous g :=
    UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr continuous_subtype_val
  have hpre :
    ∀ j : TriangleEdgeIndex,
      ((↑) : UpperHalfPlane.upperHalfPlaneSet → ℂ) ⁻¹' triangleEdgeComplex j =
        g ⁻¹' halfTriangleEdge j.1 j.2 := by
    intro j
    ext z
    simp only [triangleEdgeComplex, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hwg : w = g z := UpperHalfPlane.coe_injective hwz
      simpa only [hwg] using hw
    · intro h
      exact ⟨g z, h, rfl⟩
  simp_rw [hpre]
  exact halfTriangleEdges_locallyFinite.preimage_continuous hg

private theorem SpecialPeriods.Triangle.triangleEdgeComplex_cover_openTile_complement :
    UpperHalfPlane.upperHalfPlaneSet \
        (⋃ i : SpecialPeriods.TriangleGroup × Bool, ((↑) : ℍ → ℂ) '' halfTriangleOpenTile i) ⊆
      ⋃ j : TriangleEdgeIndex, triangleEdgeComplex j := by
  rintro z ⟨hz, hnot⟩
  let w : ℍ := ⟨z, hz⟩
  have hw : w ∈ (⋃ i : SpecialPeriods.TriangleGroup × Bool, halfTriangleOpenTile i)ᶜ := by
    intro hi
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hi
    exact hnot (Set.mem_iUnion.mpr ⟨i, w, hi, rfl⟩)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (triangleEdges_cover_openTile_complement hw)
  exact Set.mem_iUnion.mpr ⟨j, w, hj, rfl⟩

private def SpecialPeriods.Triangle.foldedEdgeComplexCarrier (b : Bool) : Fin 3 → Set ℂ :=
  if b then ![{z | z.re = stripRight}, {z | z.re = -(1 / 2)}, {z | ‖z‖ = 1}]
  else ![{z | z.re = stripLeft}, {z | z.re = -(1 / 2)}, {z | ‖z + 1‖ = 1}]

private theorem SpecialPeriods.Triangle.foldedEdgeComplex_subset_carrier (b : Bool) (k : Fin 3) :
    ((↑) : ℍ → ℂ) '' (halfFold b '' halfFordEdge k) ⊆ foldedEdgeComplexCarrier b k := by
  rintro z ⟨w, ⟨u, hu, rfl⟩, rfl⟩
  have hc := hu.2
  cases b <;> fin_cases k
  · exact hc
  · exact hc
  · exact hc
  · change u.re = stripLeft at hc
    change (rightReflection u).re = stripRight
    rw [rightReflection_re, hc]
    linarith [stripLeft_add_stripRight]
  · change u.re = -(1 / 2) at hc
    change (rightReflection u).re = -(1 / 2)
    rw [rightReflection_re, hc]
    norm_num
  · change ‖(u : ℂ) + 1‖ = 1 at hc
    change ‖(rightReflection u : ℂ)‖ = 1
    rw [rightReflection_norm]
    exact hc

private theorem TriangleUniformizationGluing.ContinuousRemovable.union {Ω S T : Set ℂ}
    (hS : TriangleUniformizationGluing.ContinuousRemovable Ω S)
    (hT : TriangleUniformizationGluing.ContinuousRemovable Ω T) (hclosedT : IsOpen (Ω \ T)) :
    TriangleUniformizationGluing.ContinuousRemovable Ω (S ∪ T) := by
  intro V hV hVΩ f hf hd
  have hVT : IsOpen (V \ T) := by
    have he : V \ T = V ∩ (Ω \ T) := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hVΩ hz.1, hz.2⟩
      · intro hz
        exact ⟨hz.1, hz.2.2⟩
    rw [he]
    exact hV.inter hclosedT
  have hdiff : DifferentiableOn ℂ f (V \ T) := by
    apply hS (V \ T) hVT (Set.sdiff_subset.trans hVΩ) f (hf.mono Set.sdiff_subset)
    intro z hz
    exact hd z ⟨hz.1.1, fun hu => hu.elim hz.2 hz.1.2⟩
  apply hT V hV hVΩ f hf
  intro z hz
  exact hdiff.differentiableAt (hVT.mem_nhds hz)

private theorem
    TriangleUniformizationGluing.continuousRemovable_biUnion_finset {ι : Type*} {Ω : Set ℂ}
    {S : ι → Set ℂ} (t : Finset ι) (hS : ∀ i ∈ t, ContinuousRemovable Ω (S i))
    (hclosed : ∀ i ∈ t, IsOpen (Ω \ S i)) : ContinuousRemovable Ω (⋃ i ∈ t, S i) := by
  classical
  revert hS hclosed
  induction t using Finset.induction_on with
  | empty =>
    intro _ _
    simpa using continuousRemovable_empty Ω
  | @insert a t hat ih =>
    intro hS hclosed
    have ht : ContinuousRemovable Ω (⋃ i ∈ t, S i) :=
      ih (fun i hi => hS i (Finset.mem_insert_of_mem hi))
        (fun i hi => hclosed i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, Set.union_comm] using
      ht.union (hS a (Finset.mem_insert_self a t)) (hclosed a (Finset.mem_insert_self a t))

private theorem TriangleUniformizationGluing.continuousRemovable_of_locally {Ω S : Set ℂ}
    (hlocal : ∀ z ∈ Ω, ∃ W : Set ℂ, IsOpen W ∧ z ∈ W ∧ ContinuousRemovable W S) :
    ContinuousRemovable Ω S := by
  intro V hV hVΩ f hf hd z hz
  obtain ⟨W, hW, hzW, hrem⟩ := hlocal z (hVΩ hz)
  have hVW : IsOpen (V ∩ W) := hV.inter hW
  have hdiff : DifferentiableOn ℂ f (V ∩ W) := by
    apply hrem (V ∩ W) hVW Set.inter_subset_right f (hf.mono Set.inter_subset_left)
    intro x hx
    exact hd x ⟨hx.1.1, hx.2⟩
  exact (hdiff.differentiableAt (hVW.mem_nhds ⟨hz, hzW⟩)).differentiableWithinAt

private theorem TriangleUniformizationGluing.continuousRemovable_iUnion_of_locallyFinite {ι : Type*}
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (S : ι → Set ℂ) (hS : ∀ i, ContinuousRemovable Ω (S i))
    (hclosed : ∀ i, IsOpen (Ω \ S i))
    (hloc : LocallyFinite (fun i => (Subtype.val : Ω → ℂ) ⁻¹' S i)) :
    ContinuousRemovable Ω (⋃ i, S i) := by
  classical
  apply continuousRemovable_of_locally
  intro z hz
  obtain ⟨N, hN, hfin⟩ := hloc ⟨z, hz⟩
  obtain ⟨W, hWN, hW, hzW⟩ := mem_nhds_iff.mp hN
  let t := hfin.toFinset
  have hWΩ : (Subtype.val '' W : Set ℂ) ⊆ Ω := by
    rintro x ⟨w, hw, rfl⟩
    exact w.property
  have hrem : ContinuousRemovable Ω (⋃ i ∈ t, S i) :=
    continuousRemovable_biUnion_finset t (fun i _ => hS i) (fun i _ => hclosed i)
  refine ⟨Subtype.val '' W, hΩ.isOpenMap_subtype_val _ hW, Set.mem_image_of_mem _ hzW, ?_⟩
  apply (hrem.mono_domain hWΩ).mono_set_on
  rintro x ⟨w, hw, rfl⟩ hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion₂.mpr
  refine ⟨i, ?_, hi⟩
  exact hfin.mem_toFinset.mpr ⟨w, hi, hWN hw⟩

private theorem TriangleUniformizationGluing.continuousRemovable_foldedEdgeComplexCarrier (b : Bool)
    (k : Fin 3) :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet
      (SpecialPeriods.Triangle.foldedEdgeComplexCarrier b k) := by
  cases b <;> fin_cases k
  · exact continuousRemovable_verticalLine SpecialPeriods.Triangle.stripLeft
  · exact continuousRemovable_verticalLine (-(1 / 2))
  · change ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet {z : ℂ | ‖z + 1‖ = 1}
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, sub_neg_eq_add] using
      continuousRemovable_unitCircle (-1)
  · exact continuousRemovable_verticalLine SpecialPeriods.Triangle.stripRight
  · exact continuousRemovable_verticalLine (-(1 / 2))
  · change ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet {z : ℂ | ‖z‖ = 1}
    simpa only [Complex.ofReal_zero, sub_zero] using continuousRemovable_unitCircle 0

private theorem
    TriangleUniformizationGluing.continuousRemovable_foldedHalfEdge (b : Bool) (k : Fin 3) :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet
      (((↑) : ℍ → ℂ) ''
        (SpecialPeriods.Triangle.halfFold b '' SpecialPeriods.Triangle.halfFordEdge k)) :=
  (continuousRemovable_foldedEdgeComplexCarrier b k).mono_set
    (SpecialPeriods.Triangle.foldedEdgeComplex_subset_carrier b k)

private theorem TriangleUniformizationGluing.continuousRemovable_triangleEdgeComplex
    (j : SpecialPeriods.Triangle.TriangleEdgeIndex) :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet
      (SpecialPeriods.Triangle.triangleEdgeComplex j) := by
  rcases j with ⟨⟨g, b⟩, k⟩
  have hsource : UpperHalfPlane.upperHalfPlaneSet ⊆ (triangleAmbientMap g).source := by
    rw [triangleAmbientMap_source]
  have hsubset :
    ((↑) : ℍ → ℂ) ''
        (SpecialPeriods.Triangle.halfFold b '' SpecialPeriods.Triangle.halfFordEdge k) ⊆
      UpperHalfPlane.upperHalfPlaneSet := by
    rintro z ⟨w, _, rfl⟩
    exact w.im_pos
  have h :=
    (continuousRemovable_foldedHalfEdge b k).image (e := triangleAmbientMap g) hsource hsubset
      (triangleAmbientMap_differentiableOn g) (triangleAmbientMap_symm_differentiableOn g)
  simpa only [triangleAmbientMap_image_upperHalfPlaneSet, triangleAmbientMap_image_coe,
    SpecialPeriods.Triangle.triangleEdgeComplex,
    SpecialPeriods.Triangle.halfTriangleEdge_eq] using h

private theorem TriangleUniformizationGluing.continuousRemovable_triangleEdges :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet
      (⋃ j : SpecialPeriods.Triangle.TriangleEdgeIndex,
        SpecialPeriods.Triangle.triangleEdgeComplex j) :=
  continuousRemovable_iUnion_of_locallyFinite UpperHalfPlane.isOpen_upperHalfPlaneSet
    SpecialPeriods.Triangle.triangleEdgeComplex continuousRemovable_triangleEdgeComplex
    SpecialPeriods.Triangle.triangleEdgeComplex_relative_compl_isOpen
    SpecialPeriods.Triangle.triangleEdgeComplex_locallyFinite

private theorem TriangleUniformizationGluing.differentiableOn_of_continuousOn_halfTriangleOpenTiles
    {f : ℂ → ℂ} (hf : ContinuousOn f UpperHalfPlane.upperHalfPlaneSet)
    (hd :
      ∀ i : SpecialPeriods.TriangleGroup × Bool,
        DifferentiableOn ℂ f (((↑) : ℍ → ℂ) '' SpecialPeriods.Triangle.halfTriangleOpenTile i)) :
    DifferentiableOn ℂ f UpperHalfPlane.upperHalfPlaneSet := by
  apply
    continuousRemovable_triangleEdges UpperHalfPlane.upperHalfPlaneSet
      UpperHalfPlane.isOpen_upperHalfPlaneSet Set.Subset.rfl f hf
  intro z hz
  have htile :
    z ∈
      ⋃ i : SpecialPeriods.TriangleGroup × Bool,
        ((↑) : ℍ → ℂ) '' SpecialPeriods.Triangle.halfTriangleOpenTile i := by
    by_contra hnot
    exact
      hz.2 (SpecialPeriods.Triangle.triangleEdgeComplex_cover_openTile_complement ⟨hz.1, hnot⟩)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp htile
  exact
    (hd i).differentiableAt
      ((UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _
            (SpecialPeriods.Triangle.halfTriangleOpenTile_isOpen i)).mem_nhds
        hi)

private theorem
    TriangleUniformizationGluing.contMDiff_of_continuous_of_halfTriangleOpenTiles {f : ℍ → ℂ}
    (hf : Continuous f)
    (hd :
      ∀ i : SpecialPeriods.TriangleGroup × Bool,
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f (SpecialPeriods.Triangle.halfTriangleOpenTile i)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  have hfc : ContinuousOn (f ∘ UpperHalfPlane.ofComplex) UpperHalfPlane.upperHalfPlaneSet := by
    intro z hz
    exact
      (hf.continuousAt.comp
          (UpperHalfPlane.contMDiffAt_ofComplex (n := ω) hz).continuousAt).continuousWithinAt
  have hfd :
    ∀ i : SpecialPeriods.TriangleGroup × Bool,
      DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex)
        (((↑) : ℍ → ℂ) '' SpecialPeriods.Triangle.halfTriangleOpenTile i) := by
    intro i z hz
    rcases hz with ⟨w, hw, rfl⟩
    have ht : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f w :=
      (hd i w hw).contMDiffAt
        ((SpecialPeriods.Triangle.halfTriangleOpenTile_isOpen i).mem_nhds hw)
    exact
      ((UpperHalfPlane.contMDiffAt_iff.mp ht).differentiableAt (by simp)).differentiableWithinAt
  have hglobal := differentiableOn_of_continuousOn_halfTriangleOpenTiles hfc hfd
  intro z
  apply UpperHalfPlane.contMDiffAt_iff.mpr
  exact (hglobal.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet z z.im_pos).contDiffAt

private theorem TriangleUniformizationGluing.differentiableAt_conj_affine_reflection_mo1973_19938
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f (-1 - conj z)) :
    DifferentiableAt ℂ (fun w => conj (f (-1 - conj w))) z := by
  have hc : DifferentiableAt ℂ (conj ∘ f ∘ conj) (-1 - z) := by
    simpa only [map_sub, map_neg, map_one, Complex.conj_conj] using hf.conj_conj
  have ha : DifferentiableAt ℂ (fun w : ℂ => -1 - w) z :=
    (differentiableAt_const (-1 : ℂ)).sub differentiableAt_id
  simpa only [Function.comp_def, map_sub, map_neg, map_one] using hc.comp z ha

private theorem
    TriangleUniformizationGluing.contMDiffOn_conj_rightReflection {f : ℍ → ℂ} {S : Set ℍ}
    (hS : IsOpen S) (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f S) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (fun z => conj (f (SpecialPeriods.Triangle.rightReflection z)))
      (SpecialPeriods.Triangle.rightReflection '' S) := by
  let F : ℂ → ℂ := fun z => conj (f (UpperHalfPlane.ofComplex (-1 - conj z)))
  have hU : IsOpen (((↑) : ℍ → ℂ) '' (SpecialPeriods.Triangle.rightReflection '' S)) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _
      (SpecialPeriods.Triangle.rightReflection.isOpenMap _ hS)
  have hF :
    DifferentiableOn ℂ F (((↑) : ℍ → ℂ) '' (SpecialPeriods.Triangle.rightReflection '' S)) := by
    rintro z ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    have hfx : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := (hf x hx).contMDiffAt (hS.mem_nhds hx)
    have hfd : DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) (x : ℂ) :=
      (UpperHalfPlane.contMDiffAt_iff.mp hfx).differentiableAt (by simp)
    have hr : (-1 : ℂ) - conj (SpecialPeriods.Triangle.rightReflection x : ℂ) = (x : ℂ) :=
      (SpecialPeriods.Triangle.rightReflection_coe
            (SpecialPeriods.Triangle.rightReflection x)).symm.trans
        (congrArg ((↑) : ℍ → ℂ) (SpecialPeriods.Triangle.rightReflection_involutive x))
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_conj_affine_reflection_mo1973_19938 (f := f ∘ UpperHalfPlane.ofComplex)
    rw [hr]
    exact hfd
  have hFM :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω F (((↑) : ℍ → ℂ) '' (SpecialPeriods.Triangle.rightReflection '' S)) :=
    contMDiffOn_iff_contDiffOn.mpr ((hF.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn)
  have hcomp :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (F ∘ ((↑) : ℍ → ℂ)) (SpecialPeriods.Triangle.rightReflection '' S) :=
    hFM.comp UpperHalfPlane.contMDiff_coe.contMDiffOn (fun z hz => ⟨z, hz, rfl⟩)
  apply hcomp.congr
  intro z _
  change
    conj (f (SpecialPeriods.Triangle.rightReflection z)) =
      conj (f (UpperHalfPlane.ofComplex (-1 - conj (z : ℂ))))
  rw [← SpecialPeriods.Triangle.rightReflection_coe, UpperHalfPlane.ofComplex_apply]

private theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_holomorphicOn_half
    (D : TriangleUniformizationGluing.BoundaryMap)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap SpecialPeriods.Triangle.halfFordInterior := by
  apply hd.congr
  intro z hz
  have hclosed := SpecialPeriods.Triangle.halfFordInterior_subset_halfFordRegion hz
  rw [D.upstairsMap_of_mem hclosed.1, D.foldedFordMap_of_left hclosed.2]

private theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_holomorphicOn_reflected_half
    (D : TriangleUniformizationGluing.BoundaryMap)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap
      (SpecialPeriods.Triangle.rightReflection '' SpecialPeriods.Triangle.halfFordInterior) := by
  have href :=
    TriangleUniformizationGluing.contMDiffOn_conj_rightReflection
      SpecialPeriods.Triangle.halfFordInterior_isOpen hd
  apply href.congr
  rintro z ⟨w, hw, rfl⟩
  have hclosed := SpecialPeriods.Triangle.halfFordInterior_subset_halfFordRegion hw
  rw [D.upstairsMap_of_mem (SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion hclosed.1)]
  exact D.foldedFordMap_eqOn_right ⟨w, hclosed, rfl⟩

private theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_holomorphicOn_fold
    (D : TriangleUniformizationGluing.BoundaryMap) (b : Bool)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap
      (SpecialPeriods.Triangle.halfFold b '' SpecialPeriods.Triangle.halfFordInterior) := by
  cases b
  · change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap (id '' SpecialPeriods.Triangle.halfFordInterior)
    rw [Set.image_id]
    exact D.upstairsMap_holomorphicOn_half hd
  · exact D.upstairsMap_holomorphicOn_reflected_half hd

private theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_holomorphicOn_tile
    (D : TriangleUniformizationGluing.BoundaryMap) (i : SpecialPeriods.TriangleGroup × Bool)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap (SpecialPeriods.Triangle.halfTriangleOpenTile i) := by
  rw [SpecialPeriods.Triangle.halfTriangleOpenTile_eq]
  have hm :
    Set.MapsTo (SpecialPeriods.triangleGeometricRepresentation i.1⁻¹)
      (SpecialPeriods.triangleGeometricRepresentation i.1 ''
        (SpecialPeriods.Triangle.halfFold i.2 '' SpecialPeriods.Triangle.halfFordInterior))
      (SpecialPeriods.Triangle.halfFold i.2 '' SpecialPeriods.Triangle.halfFordInterior) := by
    rintro z ⟨w, hw, rfl⟩
    rw [map_inv]
    change
      (SpecialPeriods.triangleGeometricRepresentation i.1).symm
          (SpecialPeriods.triangleGeometricRepresentation i.1 w) ∈
        _
    rw [(SpecialPeriods.triangleGeometricRepresentation i.1).symm_apply_apply w]
    exact hw
  have hc :=
    (D.upstairsMap_holomorphicOn_fold i.2 hd).comp
      (SpecialPeriods.triangleGeometricRepresentation_holomorphic i.1⁻¹).contMDiffOn hm
  apply hc.congr
  intro z _
  exact (D.upstairsMap_smul i.1⁻¹ z).symm

private theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_holomorphic
    (D : TriangleUniformizationGluing.BoundaryMap)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap :=
  TriangleUniformizationGluing.contMDiff_of_continuous_of_halfTriangleOpenTiles
    D.upstairsMap_continuous (fun i => D.upstairsMap_holomorphicOn_tile i hd)

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.upstairsMap_holomorphic
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.toFun : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap :=
  D.toBoundaryMap.upstairsMap_holomorphic hd

private theorem
  TriangleUniformizationGluing.openPartialHomeomorph_symm_tendsto_punctured_mo1973_19946
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    {x : X} (hx : x ∈ e.source) : Filter.Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] x) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨(e.tendsto_symm hx).mono_left nhdsWithin_le_nhds, ?_⟩
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, e.left_inv hx] using
    e.symm.eventually_ne_nhdsWithin (e.map_source hx)

private theorem TriangleUniformizationGluing.contMDiffAt_of_continuousAt_of_punctured {M N : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] [TopologicalSpace N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] {f : M → N} {x : M} (hf : ContinuousAt f x)
    (hd : ∀ᶠ z in 𝓝[≠] x, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f z) : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
  let e := chartAt ℂ x
  let e' := chartAt ℂ (f x)
  let F : ℂ → ℂ := e' ∘ f ∘ e.symm
  have hxe : x ∈ e.source := ChartedSpace.mem_chart_source x
  have hye : f x ∈ e'.source := ChartedSpace.mem_chart_source (f x)
  have hcF : ContinuousAt F (e x) := by
    have hcomposed : Filter.Tendsto F (𝓝 (e x)) (𝓝 (e' (f x))) :=
      (e'.continuousAt hye).tendsto.comp (hf.tendsto.comp (e.tendsto_symm hxe))
    simpa only [ContinuousAt, F, Function.comp_apply, e.left_inv hxe] using hcomposed
  have hdomain : ∀ᶠ z in 𝓝 (e x), z ∈ e.target := e.open_target.mem_nhds (e.map_source hxe)
  have htarget : ∀ᶠ z in 𝓝 (e x), f (e.symm z) ∈ e'.source :=
    (hf.tendsto.comp (e.tendsto_symm hxe)).eventually (e'.open_source.mem_nhds hye)
  have hdiff : ∀ᶠ z in 𝓝[≠] (e x), DifferentiableAt ℂ F z := by
    filter_upwards [(openPartialHomeomorph_symm_tendsto_punctured_mo1973_19946 e hxe).eventually
        hd,
      eventually_nhdsWithin_of_eventually_nhds hdomain,
      eventually_nhdsWithin_of_eventually_nhds htarget] with z hz hzDomain hzTarget
    have hcoords : ContDiffAt ℂ ω F (e (e.symm z)) := by
      have h :=
        (contMDiffAt_iff_of_mem_source (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (x := x) (y := f x)
              (e.map_target hzDomain) hzTarget).mp
          hz
      simpa only [e, e', F, mfld_simps, contDiffWithinAt_univ] using h.2
    rw [e.right_inv hzDomain] at hcoords
    exact hcoords.differentiableAt (by simp)
  have ha := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff hcF
  apply contMDiffAt_iff.mpr
  refine ⟨hf, ?_⟩
  have hsm : ContDiffAt ℂ ω F (e x) := ha.contDiffAt
  simpa only [e, e', F, mfld_simps] using hsm.contDiffWithinAt (s := Set.univ)

private theorem TriangleUniformizationGluing.contMDiff_of_continuous_of_finite {M N : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] [TopologicalSpace N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] {f : M → N} {S : Set M} (hf : Continuous f)
    (hS : S.Finite) (hd : ∀ z ∉ S, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f z) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  have : T1Space M := ChartedSpace.t1Space ℂ M
  intro x
  apply contMDiffAt_of_continuousAt_of_punctured hf.continuousAt
  have hclosed : IsClosed (S \ { x }) := (hS.subset Set.sdiff_subset).isClosed
  have haway : (S \ { x })ᶜ ∈ 𝓝 x := hclosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds haway, self_mem_nhdsWithin] with z hz
    hzx
  exact hd z (fun hzS => hz ⟨hzS, hzx⟩)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem TriangleUniformizationGluing.instIsManifold1 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleOrbitSpace :=
  SpecialPeriods.triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold1 in
private theorem TriangleUniformizationGluing.BoundaryMap.quotientMap_holomorphicAt_of_not_elliptic
    (D : TriangleUniformizationGluing.BoundaryMap) (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap)
    {q : SpecialPeriods.TriangleOrbitSpace} (h₁ : q ≠ SpecialPeriods.triangleOrbitCenterOne)
    (h₂ : q ≠ SpecialPeriods.triangleOrbitCenterTwo) : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω D.quotientMap q := by
  obtain ⟨z, rfl⟩ := SpecialPeriods.triangleOrbitProjection_surjective q
  have hp := SpecialPeriods.triangleOrbitProjection_isLocalDiffeomorphAt_of_not_elliptic h₁ h₂
  have h :=
    hup.contMDiffAt.comp (SpecialPeriods.triangleOrbitProjection z) hp.localInverse_contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [hp.localInverse_eventuallyEq_right] with y hy
  change
    D.quotientMap y = D.quotientMap (SpecialPeriods.triangleOrbitProjection (hp.localInverse y))
  rw [show SpecialPeriods.triangleOrbitProjection (hp.localInverse y) = y from hy]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold1 in
private theorem TriangleUniformizationGluing.BoundaryMap.quotientMap_holomorphic
    (D : TriangleUniformizationGluing.BoundaryMap) (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.quotientMap := by
  apply
    TriangleUniformizationGluing.contMDiff_of_continuous_of_finite D.quotientMap_continuous
      ((Set.finite_singleton SpecialPeriods.triangleOrbitCenterTwo).insert
        SpecialPeriods.triangleOrbitCenterOne)
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hq
  exact D.quotientMap_holomorphicAt_of_not_elliptic hup hq.1 hq.2

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold1 in
private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap_holomorphic
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.quotientMap :=
  D.toBoundaryMap.quotientMap_holomorphic hup

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold1 in
private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientHomeomorph_holomorphic
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.quotientHomeomorph hlocal) :=
  D.quotientMap_holomorphic hup

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem TriangleUniformizationGluing.instIsManifold2 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.triangleCompactified_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold2 in
private theorem
  TriangleUniformizationGluing.SignedHalfPlaneMap.compactifiedHomeomorph_holomorphicAt_of_ne_cusp
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (hq : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.quotientMap) {p : SpecialPeriods.TriangleCompactifiedOrbitSpace}
    (hp : p ≠ SpecialPeriods.triangleCuspPoint) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (D.compactifiedHomeomorph hlocal) p := by
  obtain ⟨q, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hp
  have hfinite : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((↑) : ℂ → RiemannSphere) :=
    RiemannSphere.standardCharts.affineMap_holomorphic Bool.false
  have hcomp :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      ((D.compactifiedHomeomorph hlocal) ∘ SpecialPeriods.triangleOpenInclusion) := by
    simpa only [Function.comp_def, D.compactifiedHomeomorph_openInclusion hlocal] using
      hfinite.comp hq
  have hi := SpecialPeriods.triangleOpenInclusion_isLocalDiffeomorph q
  have h :=
    hcomp.contMDiffAt.comp (SpecialPeriods.triangleOpenInclusion q) hi.localInverse_contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [hi.localInverse_eventuallyEq_right] with z hz
  change
    D.compactifiedHomeomorph hlocal z =
      D.compactifiedHomeomorph hlocal (SpecialPeriods.triangleOpenInclusion (hi.localInverse z))
  rw [show SpecialPeriods.triangleOpenInclusion (hi.localInverse z) = z from hz]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold2 in
private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.compactifiedHomeomorph_holomorphic
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.compactifiedHomeomorph hlocal) := by
  apply
    TriangleUniformizationGluing.contMDiff_of_continuous_of_finite
      (D.compactifiedHomeomorph hlocal).continuous
      (Set.finite_singleton SpecialPeriods.triangleCuspPoint)
  intro p hp
  exact
    D.compactifiedHomeomorph_holomorphicAt_of_ne_cusp hlocal (D.quotientMap_holomorphic hup)
      (by simpa only [Set.mem_singleton_iff] using hp)

private theorem TriangleUniformizationGluing.eventually_deriv_ne_zero_of_differentiableOn
    (e : OpenPartialHomeomorph ℂ ℂ) (he : DifferentiableOn ℂ e e.source) {a : ℂ}
    (ha : a ∈ e.source) : ∀ᶠ z in 𝓝[≠] a, deriv e z ≠ 0 := by
  have hda : AnalyticAt ℂ (deriv e) a := (he.analyticAt (e.open_source.mem_nhds ha)).deriv
  rcases hda.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
  · exfalso
    have hnear : ∀ᶠ z in 𝓝 a, z ∈ e.source ∧ deriv e z = 0 := by
      filter_upwards [e.open_source.mem_nhds ha, hzero] with z hz hdz
      exact ⟨hz, hdz⟩
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
    have hballSource : Metric.ball a r ⊆ e.source := fun z hz => (hball hz).1
    have hconstant : ∀ z ∈ Metric.ball a r, e z = e a := by
      intro z hz
      exact
        Metric.isOpen_ball.is_const_of_deriv_eq_zero Metric.isPreconnected_ball
          (he.mono hballSource) (fun w hw => (hball hw).2) hz (Metric.mem_ball_self hr)
    have hballNhds : ∀ᶠ z in 𝓝 a, z ∈ Metric.ball a r := Metric.ball_mem_nhds a hr
    have hballPunctured : ∀ᶠ z in 𝓝[≠] a, z ∈ Metric.ball a r :=
      hballNhds.filter_mono nhdsWithin_le_nhds
    obtain ⟨z, hz, hza⟩ :=
      (hballPunctured.and (self_mem_nhdsWithin : ∀ᶠ z in 𝓝[≠] a, z ≠ a)).exists
    exact hza (e.injOn (hballSource hz) ha (hconstant z hz))
  · exact hnonzero

private theorem TriangleUniformizationGluing.differentiableOn_symm_of_differentiableOn
    (e : OpenPartialHomeomorph ℂ ℂ) (he : DifferentiableOn ℂ e e.source) :
    DifferentiableOn ℂ e.symm e.target := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  apply AnalyticAt.differentiableAt
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hnonzero := eventually_deriv_ne_zero_of_differentiableOn e he (e.map_target hw)
    rw [eventually_nhdsWithin_iff] at hnonzero
    have hnear := (e.continuousAt_symm hw).tendsto.eventually hnonzero
    rw [eventually_nhdsWithin_iff]
    filter_upwards [e.open_target.mem_nhds hw, hnear] with z hz hdz hzw
    have hinvNe : e.symm z ≠ e.symm w := fun h => hzw (e.symm.injOn hz hw h)
    exact
      (e.hasDerivAt_symm hz (hdz hinvNe)
          (he.hasDerivAt (e.open_source.mem_nhds (e.map_target hz)))).differentiableAt
  · exact e.continuousAt_symm hw

public
theorem TriangleUniformizationGluing.contMDiff_symm_of_contMDiff {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω M] [IsManifold 𝓘(ℂ) ω N] (e : M ≃ₜ N) (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e.symm := by
  intro y
  let c : OpenPartialHomeomorph ℂ ℂ :=
    ((chartAt ℂ (e.symm y)).symm.trans e.toOpenPartialHomeomorph).trans (chartAt ℂ y)
  have hc : DifferentiableOn ℂ c c.source := by
    intro z hz
    have hz₁ : z ∈ (chartAt ℂ (e.symm y)).target := hz.1.1
    have hz₂ : e ((chartAt ℂ (e.symm y)).symm z) ∈ (chartAt ℂ y).source := hz.2
    have h₁ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ (e.symm y)).symm z :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (e.symm y)) hz₁
    have h₂ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ y) (e ((chartAt ℂ (e.symm y)).symm z)) :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y) hz₂
    exact
      ((h₂.comp z ((he _).comp z h₁)).contDiffAt.differentiableAt
          (by simp)).differentiableWithinAt
  have hy : (chartAt ℂ y) y ∈ c.target := by
    refine ⟨(chartAt ℂ y).map_source (mem_chart_source ℂ y), ?_⟩
    change
      (chartAt ℂ y).symm ((chartAt ℂ y) y) ∈ (Set.univ : Set N) ∧
        e.symm ((chartAt ℂ y).symm ((chartAt ℂ y) y)) ∈ (chartAt ℂ (e.symm y)).source
    rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
    exact ⟨Set.mem_univ _, mem_chart_source ℂ _⟩
  have hinv : ContDiffAt ℂ ω c.symm ((chartAt ℂ y) y) :=
    ((differentiableOn_symm_of_differentiableOn c hc).contDiffOn c.open_target).contDiffAt
      (c.open_target.mem_nhds hy)
  change
    ContDiffAt ℂ ω ((chartAt ℂ (e.symm y)) ∘ e.symm ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) y) at hinv
  apply contMDiffAt_iff.mpr
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.range_id,
    contDiffWithinAt_univ] using hinv

private def TriangleUniformizationGluing.biholomorphOfHomeomorph {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] [ChartedSpace ℂ M] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω M]
    [IsManifold 𝓘(ℂ) ω N] (e : M ≃ₜ N) (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) M N ω where
  toEquiv := e.toEquiv
  contMDiff_toFun := he
  contMDiff_invFun := contMDiff_symm_of_contMDiff e he

@[simp]
private theorem TriangleUniformizationGluing.biholomorphOfHomeomorph_toHomeomorph {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω M] [IsManifold 𝓘(ℂ) ω N] (e : M ≃ₜ N) (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e) :
    (biholomorphOfHomeomorph e he).toHomeomorph = e := by
  ext x
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem TriangleUniformizationGluing.instIsManifold3 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleOrbitSpace :=
  SpecialPeriods.triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold3 in
private theorem TriangleUniformizationGluing.instIsManifold4 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.triangleCompactified_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold3
    TriangleUniformizationGluing.instIsManifold4 in
private def TriangleUniformizationGluing.SignedHalfPlaneMap.quotientBiholomorph
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.toFun : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleOrbitSpace ℂ ω :=
  TriangleUniformizationGluing.biholomorphOfHomeomorph (D.quotientHomeomorph hlocal)
    (D.quotientHomeomorph_holomorphic hlocal (D.upstairsMap_holomorphic hd))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold3
    TriangleUniformizationGluing.instIsManifold4 in
private def TriangleUniformizationGluing.SignedHalfPlaneMap.compactifiedBiholomorph
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.toFun : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω :=
  TriangleUniformizationGluing.biholomorphOfHomeomorph (D.compactifiedHomeomorph hlocal)
    (D.compactifiedHomeomorph_holomorphic hlocal (D.upstairsMap_holomorphic hd))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold3
    TriangleUniformizationGluing.instIsManifold4 in
@[simp]
private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientBiholomorph_toHomeomorph
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.toFun : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    (D.quotientBiholomorph hlocal hd).toHomeomorph = D.quotientHomeomorph hlocal :=
  TriangleUniformizationGluing.biholomorphOfHomeomorph_toHomeomorph _ _

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Triangle.trianglePlaneUniformization :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleOrbitSpace ℂ ω :=
  RiemannMapping.triangleSignedHalfPlaneMap.quotientBiholomorph
    RiemannMapping.triangleSignedHalfPlaneMap_isProperMap
    RiemannMapping.triangleSignedHalfPlaneMap_holomorphicOn

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Triangle.triangleSphereUniformization :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω :=
  RiemannMapping.triangleSignedHalfPlaneMap.compactifiedBiholomorph
    RiemannMapping.triangleSignedHalfPlaneMap_isProperMap
    RiemannMapping.triangleSignedHalfPlaneMap_holomorphicOn

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Triangle.trianglePlaneUniformization_toHomeomorph :
    trianglePlaneUniformization.toHomeomorph = trianglePlaneUniformizationHomeomorph :=
  RiemannMapping.triangleSignedHalfPlaneMap.quotientBiholomorph_toHomeomorph
    RiemannMapping.triangleSignedHalfPlaneMap_isProperMap
    RiemannMapping.triangleSignedHalfPlaneMap_holomorphicOn

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Triangle.triangleSphereUniformization_cusp :
    triangleSphereUniformization SpecialPeriods.triangleCuspPoint =
      ((OnePoint.infty) : RiemannSphere) :=
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Triangle.triangleSphereUniformization_openInclusion
    (q : SpecialPeriods.TriangleOrbitSpace) :
    triangleSphereUniformization (SpecialPeriods.triangleOpenInclusion q) =
      ((trianglePlaneUniformization q : ℂ) : RiemannSphere) :=
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Triangle.trianglePlaneUniformization_centerOne :
    trianglePlaneUniformization SpecialPeriods.triangleOrbitCenterOne = 0 :=
  trianglePlaneUniformizationHomeomorph_centerOne

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Triangle.trianglePlaneUniformization_centerTwo :
    trianglePlaneUniformization SpecialPeriods.triangleOrbitCenterTwo = 1 :=
  trianglePlaneUniformizationHomeomorph_centerTwo

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Triangle.triangleSphereUniformization_centerOne :
    triangleSphereUniformization
        (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
      ((0 : ℂ) : RiemannSphere) :=
  triangleSphereUniformizationHomeomorph_centerOne

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo :
    triangleSphereUniformization
        (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
      ((1 : ℂ) : RiemannSphere) :=
  triangleSphereUniformizationHomeomorph_centerTwo

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.specialPeriodMap : HolomorphicPeriodMap ℂ ℍ :=
  Construction.periodMapOfSphere Triangle.triangleSphereUniformization
    Triangle.triangleSphereUniformization_cusp Triangle.triangleSphereUniformization_centerOne
    Triangle.triangleSphereUniformization_centerTwo

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.specialPeriodMap_generator₁ (z : ℍ) :
    specialPeriodMap.point (Triangle.generatorOneSL • z) = (specialPeriodMap.point z).step₁ :=
  Construction.periodMapOfSphere_generator₁ Triangle.triangleSphereUniformization
    Triangle.triangleSphereUniformization_cusp Triangle.triangleSphereUniformization_centerOne
    Triangle.triangleSphereUniformization_centerTwo z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.specialPeriodMap_generator₂ (z : ℍ) :
    specialPeriodMap.point (Triangle.generatorTwoSL • z) = (specialPeriodMap.point z).step₂ :=
  Construction.periodMapOfSphere_generator₂ Triangle.triangleSphereUniformization
    Triangle.triangleSphereUniformization_cusp Triangle.triangleSphereUniformization_centerOne
    Triangle.triangleSphereUniformization_centerTwo z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.specialCuspData : CuspFamily.Data :=
  Construction.cuspDataOfSphere Triangle.triangleSphereUniformization
    Triangle.triangleSphereUniformization_cusp Triangle.triangleSphereUniformization_centerOne
    Triangle.triangleSphereUniformization_centerTwo

private theorem SpecialPeriods.triangleDualRepresentation_cusp_zpow_matrix (k : ℤ) :
    (triangleDualRepresentation (triangleCuspGenerator ^ k) : LatticeMatrix) =
      CuspFamily.cuspIntegralMatrix k := by
  let C : Multiplicative ℤ →* LatticeMatrix :=
    { toFun := fun n => CuspFamily.cuspIntegralMatrix n.toAdd
      map_one' := CuspFamily.cuspIntegralMatrix_zero
      map_mul' := fun m n => CuspFamily.cuspIntegralMatrix_add m.toAdd n.toAdd }
  let R : Multiplicative ℤ →* LatticeMatrix :=
    { toFun := fun n =>
        (triangleDualRepresentation (triangleCuspGenerator ^ n.toAdd) : LatticeMatrix)
      map_one' := by simp
      map_mul' := by
        intro m n
        change
          (triangleDualRepresentation (triangleCuspGenerator ^ (m.toAdd + n.toAdd)) :
              LatticeMatrix) =
            _
        rw [_root_.zpow_add, map_mul, Matrix.SpecialLinearGroup.coe_mul] }
  have he : R = C := by
    apply MonoidHom.ext_mint
    change
      (triangleDualRepresentation (triangleCuspGenerator ^ (1 : ℤ)) : LatticeMatrix) =
        CuspFamily.cuspIntegralMatrix 1
    rw [zpow_one, CuspFamily.cuspIntegralMatrix_one, triangleDualRepresentation_cusp_matrix]
  exact DFunLike.congr_fun he (Multiplicative.ofAdd k)

private theorem SpecialPeriods.triangleRealEquiv_cusp_zpow (k : ℤ) :
    triangleRealEquiv (triangleCuspGenerator ^ k) = CuspFamily.cuspRealEquiv k := by
  apply LinearEquiv.ext
  intro x
  rw [triangleRealEquiv_apply, triangleDualRepresentation_cusp_zpow_matrix,
    CuspFamily.cuspRealEquiv_apply]

private theorem SpecialPeriods.triangleTorusHomeomorph_cusp_zpow (k : ℤ) :
    triangleTorusHomeomorph (triangleCuspGenerator ^ k) = CuspFamily.cuspTorusHomeomorph k := by
  apply Homeomorph.ext
  intro x
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  rw [triangleTorusHomeomorph_mkQ, CuspFamily.cuspTorusHomeomorph_mkQ,
    triangleRealEquiv_cusp_zpow]

end Mathoverflow1973

end
