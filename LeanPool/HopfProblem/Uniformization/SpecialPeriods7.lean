/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.Foundations.Complex
import all LeanPool.HopfProblem.PeriodFamily.Core2

/-!
# Hopf problem: uniformization · special periods 7

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

private theorem RiemannMapping.closure_normalizedClass {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    closure (normalizedClass U x₀) ⊆
      {f |
        Set.MapsTo (evaluation f) U (Metric.ball 0 1) ∧
          ((∃ C, Set.EqOn (evaluation f) (Function.const ℂ C) U) ∨ Set.InjOn (evaluation f) U) ∧
            DifferentiableOn ℂ (evaluation f) U ∧
              evaluation f x₀ = 0 ∧
                (Set.EqOn (deriv (evaluation f)) 0 U ∨ ∀ z ∈ U, deriv (evaluation f) z ≠ 0)} := by
  let := uniformity_isCountablyGenerated hUo
  intro f hf
  let : (𝓝[normalizedClass U x₀] f).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hf
  have htendsto :
    TendstoLocallyUniformlyOn evaluation (evaluation f) (𝓝[normalizedClass U x₀] f) U :=
    evaluation_tendstoLocallyUniformlyOn hUo
  have hFd : ∀ᶠ g in 𝓝[normalizedClass U x₀] f, DifferentiableOn ℂ (evaluation g) U :=
    eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.1
  have hdf : DifferentiableOn ℂ (evaluation f) U := htendsto.differentiableOn hFd hUo
  have hf_le : ∀ z ∈ U, ‖evaluation f z‖ ≤ 1 := by
    intro z hz
    refine le_of_tendsto (htendsto.tendsto_at hz).norm (eventually_mem_nhdsWithin.mono ?_)
    intro g hg
    exact (mem_ball_zero_iff.mp (hg.1 hz)).le
  have hfx₀ : evaluation f x₀ = 0 := by
    refine tendsto_nhds_unique (htendsto.tendsto_at hx₀) ?_
    refine tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun g hg => ?_)
    exact hg.2.2.2.2.symm
  refine ⟨?_, ?_, hdf, hfx₀, ?_⟩
  · by_contra hf_ball
    obtain ⟨z, hzU, hz⟩ : ∃ z ∈ U, 1 ≤ ‖evaluation f z‖ := by simpa [Set.MapsTo] using hf_ball
    have hm : IsMaxOn (fun z => ‖evaluation f z‖) U z := by
      intro y hy
      exact (hf_le y hy).trans hz
    have he : evaluation f x₀ = evaluation f z :=
      Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hdf hzU hm hx₀
    norm_num [← he, hfx₀] at hz
  · exact
      Complex.eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn hUo hUc
        (eventually_mem_nhdsWithin.mono fun g hg => hg.2.1) hFd htendsto
  · apply
      Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn hUo hUc
        (eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.2.1)
        (hFd.mono fun g hg => hg.deriv hUo)
    exact htendsto.deriv hFd hUo

private theorem RiemannMapping.norm_deriv_continuousOn_closure {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ContinuousOn (fun f : FunctionSpace U => ‖deriv (evaluation f) x₀‖)
      (closure (normalizedClass U x₀)) := by
  have hc := closure_normalizedClass hUo hUc hx₀
  refine ContinuousOn.mono (ContinuousOn.norm fun f hf => ?_) hc
  refine
    TendstoLocallyUniformlyOn.tendsto_at
      (TendstoLocallyUniformlyOn.deriv (evaluation_tendstoLocallyUniformlyOn hUo) ?_ hUo) hx₀
  exact eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.1

private theorem RiemannMapping.exists_maximal_normalizedMap {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) (hne : (normalizedClass U x₀).Nonempty) :
    ∃ f : FunctionSpace U,
      f ∈ normalizedClass U x₀ ∧
        ∀ g ∈ normalizedClass U x₀, ‖deriv (evaluation g) x₀‖ ≤ ‖deriv (evaluation f) x₀‖ := by
  obtain ⟨f, hf, hmax⟩ :=
    (normalizedClass_compact_closure hUo x₀).exists_isMaxOn hne.closure
      (norm_deriv_continuousOn_closure hUo hUc hx₀)
  have hpos : 0 < ‖deriv (evaluation f) x₀‖ := by
    obtain ⟨g, hg⟩ := hne
    exact (norm_pos_iff.mpr (hg.2.2.2.1 x₀ hx₀)).trans_le (hmax (subset_closure hg))
  obtain ⟨hmap, hinj, hdiff, hzero, hderiv⟩ := closure_normalizedClass hUo hUc hx₀ hf
  have hinj' : Set.InjOn (evaluation f) U := by
    apply hinj.resolve_left
    rintro ⟨C, hC⟩
    rw [(hC.eventuallyEq_of_mem (hUo.mem_nhds hx₀)).deriv_eq] at hpos
    change 0 < ‖deriv (fun _ : ℂ => C) x₀‖ at hpos
    simp only [deriv_const, norm_zero, lt_self_iff_false] at hpos
  have hderiv' : ∀ z ∈ U, deriv (evaluation f) z ≠ 0 := by
    apply hderiv.resolve_left
    intro hzero'
    have hz : deriv (evaluation f) x₀ = 0 := hzero' hx₀
    simp only [hz, norm_zero, lt_self_iff_false] at hpos
  exact ⟨f, ⟨hmap, hinj', hdiff, hderiv', hzero⟩, fun g hg => hmax (subset_closure hg)⟩

private def
    RiemannMapping.discExtension {U : Set ℂ} (f : ℂ → ℂ) (hf : Set.MapsTo f U (Metric.ball 0 1)) :
    ℂ → Complex.UnitDisc := by
  classical
    exact fun z =>
    if hz : z ∈ U then Complex.UnitDisc.mk (f z) (mem_ball_zero_iff.mp (hf hz)) else 0

@[simp]
private theorem RiemannMapping.discExtension_coe {U : Set ℂ} (f : ℂ → ℂ)
    (hf : Set.MapsTo f U (Metric.ball 0 1)) {z : ℂ} (hz : z ∈ U) :
    (discExtension f hf z : ℂ) = f z := by
  simp only [discExtension, dite_eq_left hz, Complex.UnitDisc.coe_mk]

private theorem RiemannMapping.discExtension_eqOn {U : Set ℂ} (f : ℂ → ℂ)
    (hf : Set.MapsTo f U (Metric.ball 0 1)) :
    Set.EqOn (Complex.UnitDisc.coe ∘ discExtension f hf) f U := fun _ hz =>
  discExtension_coe f hf hz

private theorem RiemannMapping.normalizedClass_nonempty {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ) (x₀ : ℂ) :
    (normalizedClass U x₀).Nonempty := by
  obtain ⟨f, hf₀, hf_inj, hfd⟩ :=
    Complex.exists_map_unitDisc_injOn_deriv_ne_zero₀ hUo hUc hU x₀
  refine ⟨UniformOnFun.ofFun (compactSubsets U) (Complex.UnitDisc.coe ∘ f), ?_⟩
  refine ⟨fun z _ => (f z).property, ?_, ?_, hfd, ?_⟩
  · intro z hz w hw he
    exact hf_inj hz hw (Complex.UnitDisc.coe_injective he)
  · intro z hz
    exact (differentiableAt_of_deriv_ne_zero (hfd z hz)).differentiableWithinAt
  · change (f x₀ : ℂ) = 0
    rw [hf₀]
    rfl

private theorem RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f U ∧
        Set.BijOn f U (Metric.ball 0 1) ∧ (∀ z ∈ U, deriv f z ≠ 0) ∧ f x₀ = 0 := by
  obtain ⟨f, hf, hmax⟩ :=
    exists_maximal_normalizedMap hUo hUc.isPathConnected.isConnected.isPreconnected hx₀
      (normalizedClass_nonempty hUo hUc hU x₀)
  obtain ⟨hfmap, hfinj, hfdiff, hfderiv, hfzero⟩ := hf
  refine ⟨evaluation f, hfdiff, ⟨hfmap, hfinj, ?_⟩, hfderiv, hfzero⟩
  by_contra hsurj
  let fDisc := discExtension (evaluation f) hfmap
  have hfeq : Set.EqOn (Complex.UnitDisc.coe ∘ fDisc) (evaluation f) U :=
    discExtension_eqOn (evaluation f) hfmap
  have hfdDisc : DifferentiableOn ℂ (Complex.UnitDisc.coe ∘ fDisc) U :=
    (differentiableOn_congr hfeq).mpr hfdiff
  have hfDisc0 : fDisc x₀ = 0 := by
    apply Complex.UnitDisc.coe_injective
    change (fDisc x₀ : ℂ) = 0
    exact (hfeq hx₀).trans hfzero
  have hfDiscInj : Set.InjOn fDisc U := by
    intro z hz w hw he
    apply hfinj hz hw
    exact (hfeq hz).symm.trans ((congrArg Complex.UnitDisc.coe he).trans (hfeq hw))
  have hfDiscDeriv : ∀ z ∈ U, deriv (Complex.UnitDisc.coe ∘ fDisc) z ≠ 0 := by
    intro z hz
    rw [(hfeq.eventuallyEq_of_mem (hUo.mem_nhds hz)).deriv_eq]
    exact hfderiv z hz
  have hfDiscSurj : ¬Set.SurjOn fDisc U Set.univ := by
    intro hs
    apply hsurj
    intro w hw
    obtain ⟨z, hz, he⟩ := hs (Set.mem_univ (Complex.UnitDisc.mk w (mem_ball_zero_iff.mp hw)))
    refine ⟨z, hz, ?_⟩
    exact (hfeq hz).symm.trans (congrArg Complex.UnitDisc.coe he)
  obtain ⟨g, hg₀, hginj, hgdiff, hgderiv, hglt⟩ :=
    Complex.exist_map_unitDisc_injOn_deriv_ne_zero_norm_deriv_gt hUo hUc hU hx₀ hfdDisc hfDisc0
      hfDiscInj hfDiscSurj hfDiscDeriv
  let gFun : FunctionSpace U := UniformOnFun.ofFun (compactSubsets U) (Complex.UnitDisc.coe ∘ g)
  have hgmem : gFun ∈ normalizedClass U x₀ := by
    refine ⟨fun z _ => (g z).property, ?_, hgdiff, hgderiv, ?_⟩
    · intro z hz w hw he
      exact hginj hz hw (Complex.UnitDisc.coe_injective he)
    · change (g x₀ : ℂ) = 0
      rw [hg₀]
      rfl
  have hle := hmax gFun hgmem
  have heDeriv : deriv (Complex.UnitDisc.coe ∘ fDisc) x₀ = deriv (evaluation f) x₀ :=
    (hfeq.eventuallyEq_of_mem (hUo.mem_nhds hx₀)).deriv_eq
  rw [heDeriv] at hglt
  exact hle.not_gt hglt

private theorem RiemannMapping.isLocalDiffeomorphAt_of_deriv_ne_zero (U : TopologicalSpace.Opens ℂ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U : Set ℂ)) (hderiv : ∀ z ∈ U, deriv f z ≠ 0) {z : ℂ}
    (hz : z ∈ U) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f z := by
  have hfω : ContDiffOn ℂ ω f (U : Set ℂ) := hf.contDiffOn U.isOpen
  have hF (w : ℂ) (hw : w ∈ U) : ContDiffAt ℂ ω f w := hfω.contDiffAt (U.isOpen.mem_nhds hw)
  have hD (w : ℂ) (hw : w ∈ U) : HasDerivAt f (deriv f w) w :=
    hf.hasDerivAt (U.isOpen.mem_nhds hw)
  let e : OpenPartialHomeomorph ℂ ℂ :=
    ((hF z hz).toOpenPartialHomeomorph f ((hD z hz).hasFDerivAt_equiv (hderiv z hz))
          (by simp)).restr
      (U : Set ℂ)
  have heU : e.source ⊆ (U : Set ℂ) := by
    intro w hw
    dsimp only [e] at hw
    rw [OpenPartialHomeomorph.restr_source' _ _ U.isOpen] at hw
    exact hw.2
  have hze : z ∈ e.source := by
    dsimp only [e]
    rw [OpenPartialHomeomorph.restr_source' _ _ U.isOpen]
    exact
      ⟨(hF z hz).mem_toOpenPartialHomeomorph_source ((hD z hz).hasFDerivAt_equiv (hderiv z hz))
          (by simp),
        hz⟩
  refine
    ⟨{  toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := ?_
        contMDiffOn_invFun := ?_ }, hze, fun _ _ => rfl⟩
  · change ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f e.source
    exact (hfω.mono heU).contMDiffOn
  · apply ContDiffOn.contMDiffOn
    intro w hw
    have hwU := heU (e.map_target hw)
    exact
      (e.contDiffAt_symm hw ((hD _ hwU).hasFDerivAt_equiv (hderiv _ hwU))
          (hF _ hwU)).contDiffWithinAt

private theorem
    RiemannMapping.restrict_isLocalDiffeomorph (U V : TopologicalSpace.Opens ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U : Set ℂ)) (hUV : Set.MapsTo f (U : Set ℂ) (V : Set ℂ))
    (hderiv : ∀ z ∈ U, deriv f z ≠ 0) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun z : U => (⟨f z, hUV z.property⟩ : V)) := by
  intro z
  exact
    isLocalDiffeomorphAt_restrictOpens (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (isLocalDiffeomorphAt_of_deriv_ne_zero U hf hderiv z.property) U V hUV z.property

private def RiemannMapping.biholomorphOfBijOn (U V : TopologicalSpace.Opens ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U : Set ℂ)) (hbij : Set.BijOn f (U : Set ℂ) (V : Set ℂ))
    (hderiv : ∀ z ∈ U, deriv f z ≠ 0) :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U V ω := by
  apply (restrict_isLocalDiffeomorph U V hf hbij.mapsTo hderiv).diffeomorphOfBijective
  constructor
  · intro z w hzw
    apply Subtype.ext
    exact hbij.injOn z.property w.property (congrArg Subtype.val hzw)
  · intro w
    obtain ⟨z, hz, hzw⟩ := hbij.surjOn w.property
    exact ⟨⟨z, hz⟩, Subtype.ext hzw⟩

private def RiemannMapping.unitDisc : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

private def
    RiemannMapping.riemannMap (U : TopologicalSpace.Opens ℂ) (hUc : IsSimplyConnected (U : Set ℂ))
    (hU : (U : Set ℂ) ≠ Set.univ) (x₀ : U) : ℂ → ℂ :=
  (exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero U.isOpen hUc hU x₀.property).choose

private theorem RiemannMapping.riemannMap_spec (U : TopologicalSpace.Opens ℂ)
    (hUc : IsSimplyConnected (U : Set ℂ)) (hU : (U : Set ℂ) ≠ Set.univ) (x₀ : U) :
    DifferentiableOn ℂ (riemannMap U hUc hU x₀) (U : Set ℂ) ∧
      Set.BijOn (riemannMap U hUc hU x₀) (U : Set ℂ) (unitDisc : Set ℂ) ∧
        (∀ z ∈ U, deriv (riemannMap U hUc hU x₀) z ≠ 0) ∧ riemannMap U hUc hU x₀ x₀ = 0 :=
  (exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero U.isOpen hUc hU x₀.property).choose_spec

private def RiemannMapping.biholomorphUnitDisc (U : TopologicalSpace.Opens ℂ)
    (hUc : IsSimplyConnected (U : Set ℂ)) (hU : (U : Set ℂ) ≠ Set.univ) (x₀ : U) :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U unitDisc ω :=
  biholomorphOfBijOn U unitDisc (riemannMap U hUc hU x₀) (riemannMap_spec U hUc hU x₀).1
    (riemannMap_spec U hUc hU x₀).2.1 (riemannMap_spec U hUc hU x₀).2.2.1

private def RiemannMapping.triangleDomain : TopologicalSpace.Opens ℂ :=
  ⟨SpecialPeriods.Triangle.triangleInterior, SpecialPeriods.Triangle.triangleInterior_isOpen⟩

private def RiemannMapping.trianglePoint : triangleDomain :=
  ⟨SpecialPeriods.Triangle.triangleBasepoint, SpecialPeriods.Triangle.triangleBasepoint_mem⟩

private def RiemannMapping.triangleBiholomorph :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) triangleDomain unitDisc ω :=
  biholomorphUnitDisc triangleDomain SpecialPeriods.Triangle.triangleInterior_isSimplyConnected
    SpecialPeriods.Triangle.triangleInterior_ne_univ trianglePoint

private def SpecialPeriods.Triangle.triangleClosedSet : Set (OnePoint ℂ) :=
  closure (RiemannBoundary.onePointDomain triangleInterior)

private abbrev SpecialPeriods.Triangle.TriangleClosedDomain :=
  triangleClosedSet

private theorem SpecialPeriods.Triangle.triangleClosedSet_isClosed : IsClosed triangleClosedSet :=
  isClosed_closure

private theorem SpecialPeriods.Triangle.triangleClosedSet_isCompact : IsCompact triangleClosedSet :=
  triangleClosedSet_isClosed.isCompact

private instance SpecialPeriods.Triangle.triangleClosedDomain_compactSpace :
    CompactSpace TriangleClosedDomain :=
  isCompact_iff_compactSpace.mp triangleClosedSet_isCompact

private instance
    SpecialPeriods.Triangle.triangleClosedDomain_t2Space : T2Space TriangleClosedDomain :=
  inferInstance

private theorem SpecialPeriods.Triangle.coe_mem_triangleClosedSet_iff_closure (z : ℂ) :
    (z : OnePoint ℂ) ∈ triangleClosedSet ↔ z ∈ closure triangleInterior := by
  change z ∈ ((↑) : ℂ → OnePoint ℂ) ⁻¹' closure (((↑) : ℂ → OnePoint ℂ) '' triangleInterior) ↔ _
  rw [← OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image]

private theorem SpecialPeriods.Triangle.coe_mem_triangleClosedSet_iff (z : ℂ) :
    (z : OnePoint ℂ) ∈ triangleClosedSet ↔
      stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 < z.im ∧ 1 ≤ ‖z + 1‖ := by
  rw [coe_mem_triangleClosedSet_iff_closure, closure_triangleInterior]
  rfl

private theorem SpecialPeriods.Triangle.infty_mem_triangleClosedSet :
    ((OnePoint.infty) : OnePoint ℂ) ∈ triangleClosedSet :=
  triangle_infty_mem_closure

private def SpecialPeriods.Triangle.triangleClosedInfinity : TriangleClosedDomain :=
  ⟨(OnePoint.infty), infty_mem_triangleClosedSet⟩

private def SpecialPeriods.Triangle.triangleClosedInterior :
    TopologicalSpace.Opens TriangleClosedDomain :=
  ⟨{x | x.val ∈ RiemannBoundary.onePointDomain triangleInterior},
    (RiemannBoundary.isOpen_onePointDomain triangleInterior_isOpen).preimage
      continuous_subtype_val⟩

private theorem SpecialPeriods.Triangle.triangleClosedInterior_dense :
    Dense (triangleClosedInterior : Set TriangleClosedDomain) := by
  have hi :
    ((↑) : TriangleClosedDomain → OnePoint ℂ) ''
        (triangleClosedInterior : Set TriangleClosedDomain) =
      RiemannBoundary.onePointDomain triangleInterior := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, subset_closure hx⟩, hx, rfl⟩
  apply Subtype.dense_iff.mpr
  rw [hi]
  exact Set.Subset.refl _

private def SpecialPeriods.Triangle.triangleClosedInclusion (z : RiemannMapping.triangleDomain) :
    TriangleClosedDomain :=
  ⟨(z : ℂ), subset_closure (RiemannBoundary.coe_mem_onePointDomain.mpr z.property)⟩

private theorem SpecialPeriods.Triangle.triangleClosedInclusion_continuous :
    Continuous triangleClosedInclusion :=
  (OnePoint.continuous_coe.comp continuous_subtype_val).subtype_mk _

private theorem SpecialPeriods.Triangle.triangleClosedInclusion_mem_interior
    (z : RiemannMapping.triangleDomain) : triangleClosedInclusion z ∈ triangleClosedInterior :=
  RiemannBoundary.coe_mem_onePointDomain.mpr z.property

private def SpecialPeriods.Triangle.triangleClosedInteriorHomeomorph :
    RiemannMapping.triangleDomain ≃ₜ triangleClosedInterior
    where
  toFun z := ⟨triangleClosedInclusion z, triangleClosedInclusion_mem_interior z⟩
  invFun
    x := (RiemannBoundary.onePointDomainHomeomorph triangleInterior).symm ⟨x.val.val, x.property⟩
  left_inv
    z := by exact (RiemannBoundary.onePointDomainHomeomorph triangleInterior).symm_apply_apply z
  right_inv
    x := by
    apply Subtype.ext
    apply Subtype.ext
    exact
      congrArg (fun y : RiemannBoundary.onePointDomain triangleInterior => (y : OnePoint ℂ))
        ((RiemannBoundary.onePointDomainHomeomorph triangleInterior).apply_symm_apply
          ⟨x.val.val, x.property⟩)
  continuous_toFun := triangleClosedInclusion_continuous.subtype_mk _
  continuous_invFun :=
    (RiemannBoundary.onePointDomainHomeomorph triangleInterior).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

private def SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph :
    triangleClosedInterior ≃ₜ Metric.ball (0 : ℂ) 1 :=
  triangleClosedInteriorHomeomorph.symm.trans RiemannMapping.triangleBiholomorph.toHomeomorph

@[simp]
private theorem SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph_apply
    (z : RiemannMapping.triangleDomain) :
    triangleClosedInteriorDiscHomeomorph (triangleClosedInteriorHomeomorph z) =
      RiemannMapping.triangleBiholomorph z := by
  change
    RiemannMapping.triangleBiholomorph
        (triangleClosedInteriorHomeomorph.symm (triangleClosedInteriorHomeomorph z)) =
      _
  rw [triangleClosedInteriorHomeomorph.symm_apply_apply]

private theorem SpecialPeriods.Triangle.coe_mem_triangleOnePoint_frontier_iff (z : ℂ) :
    (z : OnePoint ℂ) ∈ frontier (RiemannBoundary.onePointDomain triangleInterior) ↔
      z ∈ frontier triangleInterior := by
  change
    ((z : OnePoint ℂ) ∈ closure (RiemannBoundary.onePointDomain triangleInterior) ∧
        (z : OnePoint ℂ) ∉ interior (RiemannBoundary.onePointDomain triangleInterior)) ↔
      (z ∈ closure triangleInterior ∧ z ∉ interior triangleInterior)
  rw [(RiemannBoundary.isOpen_onePointDomain triangleInterior_isOpen).interior_eq,
    triangleInterior_isOpen.interior_eq]
  exact
    and_congr (coe_mem_triangleClosedSet_iff_closure z)
      (not_congr RiemannBoundary.coe_mem_onePointDomain)

private theorem
    SpecialPeriods.Triangle.triangleClosedBoundary_iff_frontier (x : TriangleClosedDomain) :
    x ∉ triangleClosedInterior ↔
      x.val ∈ frontier (RiemannBoundary.onePointDomain triangleInterior) := by
  change
    x.val ∉ RiemannBoundary.onePointDomain triangleInterior ↔
      x.val ∈ closure (RiemannBoundary.onePointDomain triangleInterior) ∧
        x.val ∉ interior (RiemannBoundary.onePointDomain triangleInterior)
  rw [(RiemannBoundary.isOpen_onePointDomain triangleInterior_isOpen).interior_eq]
  exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

private def SpecialPeriods.Triangle.circleStraighten (z : ℂ) : ℂ :=
  Complex.I * z / (z + 2)

private def SpecialPeriods.Triangle.circleUnstraighten (w : ℂ) : ℂ :=
  2 * w / (Complex.I - w)

private theorem SpecialPeriods.Triangle.circleStraighten_sub_I {z : ℂ} (hz : z + 2 ≠ 0) :
    Complex.I - circleStraighten z = 2 * Complex.I / (z + 2) := by
  unfold circleStraighten
  field_simp
  ring

private theorem SpecialPeriods.Triangle.circleStraighten_ne_I {z : ℂ} (hz : z + 2 ≠ 0) :
    circleStraighten z ≠ Complex.I := by
  have h : Complex.I - circleStraighten z ≠ 0 := by
    rw [circleStraighten_sub_I hz]
    exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hz
  exact fun he => h (by rw [he, sub_self])

private theorem
    SpecialPeriods.Triangle.circleUnstraighten_add_two {w : ℂ} (hw : Complex.I - w ≠ 0) :
    circleUnstraighten w + 2 = 2 * Complex.I / (Complex.I - w) := by
  unfold circleUnstraighten
  field_simp
  ring

private theorem SpecialPeriods.Triangle.circleUnstraighten_add_two_ne_zero {w : ℂ}
    (hw : Complex.I - w ≠ 0) : circleUnstraighten w + 2 ≠ 0 := by
  rw [circleUnstraighten_add_two hw]
  exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hw

private theorem SpecialPeriods.Triangle.circleUnstraighten_straighten {z : ℂ} (hz : z + 2 ≠ 0) :
    circleUnstraighten (circleStraighten z) = z := by
  rw [circleUnstraighten, circleStraighten_sub_I hz]
  unfold circleStraighten
  field_simp

private theorem
    SpecialPeriods.Triangle.circleStraighten_unstraighten {w : ℂ} (hw : Complex.I - w ≠ 0) :
    circleStraighten (circleUnstraighten w) = w := by
  rw [circleStraighten, circleUnstraighten_add_two hw]
  unfold circleUnstraighten
  field_simp

private def SpecialPeriods.Triangle.circleBoundaryChart : OpenPartialHomeomorph ℂ ℂ
    where
  toFun := circleStraighten
  invFun := circleUnstraighten
  source := {z | z + 2 ≠ 0}
  target := {w | Complex.I - w ≠ 0}
  map_source' z hz := sub_ne_zero.mpr (circleStraighten_ne_I hz).symm
  map_target' w hw := circleUnstraighten_add_two_ne_zero hw
  left_inv' z hz := circleUnstraighten_straighten hz
  right_inv' w hw := circleStraighten_unstraighten hw
  open_source := isOpen_ne_fun (continuous_id.add continuous_const) continuous_const
  open_target := isOpen_ne_fun (continuous_const.sub continuous_id) continuous_const
  continuousOn_toFun := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun z hz => hz
  continuousOn_invFun := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun z hz => hz

private theorem SpecialPeriods.Triangle.circleStraighten_analyticOnNhd :
    AnalyticOnNhd ℂ circleStraighten {z | z + 2 ≠ 0} := by
  intro z hz
  exact (analyticAt_const.mul analyticAt_id).div (analyticAt_id.add analyticAt_const) hz

private theorem SpecialPeriods.Triangle.circleUnstraighten_analyticOnNhd :
    AnalyticOnNhd ℂ circleUnstraighten {w | Complex.I - w ≠ 0} := by
  intro z hz
  exact (analyticAt_const.mul analyticAt_id).div (analyticAt_const.sub analyticAt_id) hz

private theorem SpecialPeriods.Triangle.circleStraighten_im (z : ℂ) :
    (circleStraighten z).im = (Complex.normSq (z + 1) - 1) / Complex.normSq (z + 2) := by
  simp only [circleStraighten, Complex.div_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    MulZeroClass.zero_mul, one_mul, zero_add, Complex.mul_re, zero_sub, Complex.add_re,
    Complex.re_ofNat, Complex.add_im, Complex.im_ofNat, add_zero]
  rw [← sub_div]
  congr 1
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero]
  ring

private theorem SpecialPeriods.Triangle.circleStraighten_im_pos_iff {z : ℂ} (hz : z + 2 ≠ 0) :
    0 < (circleStraighten z).im ↔ 1 < ‖z + 1‖ := by
  rw [circleStraighten_im, div_pos_iff_of_pos_right (Complex.normSq_pos.mpr hz), sub_pos]
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    nlinarith [norm_nonneg (z + 1)]
  · intro h
    nlinarith

private theorem SpecialPeriods.Triangle.circleStraighten_im_eq_zero_iff {z : ℂ} (hz : z + 2 ≠ 0) :
    (circleStraighten z).im = 0 ↔ ‖z + 1‖ = 1 := by
  rw [circleStraighten_im, div_eq_zero_iff, or_iff_left (Complex.normSq_pos.mpr hz).ne',
    sub_eq_zero, Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    nlinarith [norm_nonneg (z + 1)]
  · intro h
    rw [h]
    norm_num

private theorem
    SpecialPeriods.Triangle.exists_circle_side_neighborhood {a : ℂ} (haL : stripLeft < a.re)
    (haR : a.re < -1 / 2) (hai : 0 < a.im) :
    ∃ r > 0,
      ∀ z ∈ Metric.ball a r,
        z ∈ circleBoundaryChart.source ∧
          (z ∈ triangleInterior ↔ 0 < (circleBoundaryChart z).im) := by
  let V : Set ℂ := {z | stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a ⟨haL, haR, hai⟩
  refine ⟨r, hr, ?_⟩
  intro z hz
  have h := hball hz
  have hzden : z + 2 ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.im_ofNat, add_zero, Complex.zero_im] at hi
    exact h.2.2.ne' hi
  refine ⟨hzden, ?_⟩
  change (stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖) ↔ 0 < (circleStraighten z).im
  rw [circleStraighten_im_pos_iff hzden]
  exact ⟨fun hz' => hz'.2.2.2, fun hnorm => ⟨h.1, h.2.1, h.2.2, hnorm⟩⟩

private def SpecialPeriods.Triangle.leftBoundaryChart : ℂ ≃ₜ ℂ
    where
  toFun z := Complex.I * (z - stripLeft)
  invFun w := -Complex.I * w + stripLeft
  left_inv z := by ring_nf; simp
  right_inv w := by ring_nf; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def SpecialPeriods.Triangle.rightBoundaryChart : ℂ ≃ₜ ℂ
    where
  toFun z := -Complex.I * (z + 1 / 2)
  invFun w := Complex.I * w - 1 / 2
  left_inv z := by ring_nf; simp
  right_inv w := by ring_nf; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
private theorem SpecialPeriods.Triangle.leftBoundaryChart_im (z : ℂ) :
    (leftBoundaryChart z).im = z.re - stripLeft := by
  change (Complex.I * (z - (stripLeft : ℂ))).im = _
  simp

@[simp]
private theorem SpecialPeriods.Triangle.rightBoundaryChart_im (z : ℂ) :
    (rightBoundaryChart z).im = -(z.re + 1 / 2) := by
  change (-Complex.I * (z + 1 / 2)).im = _
  simp

private theorem SpecialPeriods.Triangle.leftBoundaryChart_symm_analyticAt (z : ℂ) :
    AnalyticAt ℂ leftBoundaryChart.symm z :=
  (analyticAt_const.mul analyticAt_id).add analyticAt_const

private theorem SpecialPeriods.Triangle.rightBoundaryChart_symm_analyticAt (z : ℂ) :
    AnalyticAt ℂ rightBoundaryChart.symm z :=
  (analyticAt_const.mul analyticAt_id).sub analyticAt_const

private theorem SpecialPeriods.Triangle.stripLeft_lt_right : stripLeft < -1 / 2 := by
  unfold stripLeft
  linarith [width_pos]

private theorem
    SpecialPeriods.Triangle.exists_left_side_neighborhood {a : ℂ} (ha : a.re = stripLeft)
    (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ r > 0, ∀ z ∈ Metric.ball a r, z ∈ triangleInterior ↔ 0 < (leftBoundaryChart z).im := by
  let V : Set ℂ := {z | z.re < -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖}
  have hV : IsOpen V :=
    (isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt continuous_const ((continuous_id.add continuous_const).norm)))
  have haV : a ∈ V := ⟨ha ▸ stripLeft_lt_right, hai, haC⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a haV
  refine ⟨r, hr, ?_⟩
  intro z hz
  have h := hball hz
  rw [leftBoundaryChart_im, sub_pos]
  exact ⟨fun hz' => hz'.1, fun hz' => ⟨hz', h.1, h.2.1, h.2.2⟩⟩

private theorem SpecialPeriods.Triangle.exists_right_side_neighborhood {a : ℂ} (ha : a.re = -1 / 2)
    (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ r > 0, ∀ z ∈ Metric.ball a r, z ∈ triangleInterior ↔ 0 < (rightBoundaryChart z).im := by
  let V : Set ℂ := {z | stripLeft < z.re ∧ 0 < z.im ∧ 1 < ‖z + 1‖}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt continuous_const ((continuous_id.add continuous_const).norm)))
  have haV : a ∈ V := ⟨ha ▸ stripLeft_lt_right, hai, haC⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a haV
  refine ⟨r, hr, ?_⟩
  intro z hz
  have h := hball hz
  rw [rightBoundaryChart_im]
  have he : 0 < -(z.re + 1 / 2) ↔ z.re < -1 / 2 := by constructor <;> intro hi <;> linarith
  rw [he]
  exact ⟨fun hz' => hz'.2.1, fun hz' => ⟨h.1, hz', h.2.1, h.2.2⟩⟩

private def SpecialPeriods.Triangle.triangleOpenLeftSide : Set ℂ :=
  {z | z.re = stripLeft ∧ 0 < z.im ∧ 1 < ‖z + 1‖}

private def SpecialPeriods.Triangle.triangleOpenRightSide : Set ℂ :=
  {z | z.re = -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖}

private def SpecialPeriods.Triangle.triangleOpenCircleSide : Set ℂ :=
  {z | stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im ∧ ‖z + 1‖ = 1}

private theorem SpecialPeriods.Triangle.triangleOpenLeftSide_disjoint_interior :
    Disjoint triangleOpenLeftSide triangleInterior := by
  apply Set.disjoint_left.mpr
  intro z hL hI
  exact (ne_of_gt hI.1) hL.1

private theorem SpecialPeriods.Triangle.triangleOpenRightSide_disjoint_interior :
    Disjoint triangleOpenRightSide triangleInterior := by
  apply Set.disjoint_left.mpr
  intro z hR hI
  exact (ne_of_lt hI.2.1) hR.1

private theorem SpecialPeriods.Triangle.triangleOpenCircleSide_disjoint_interior :
    Disjoint triangleOpenCircleSide triangleInterior := by
  apply Set.disjoint_left.mpr
  intro z hC hI
  exact (ne_of_gt hI.2.2.2) hC.2.2.2

private theorem SpecialPeriods.Triangle.centerOne_coe_re : (centerOne : ℂ).re = -1 / 2 := by
  simp only [centerOne_val, Complex.sub_re, SpecialPeriods.rho_re, Complex.one_re]
  norm_num

private theorem SpecialPeriods.Triangle.centerTwo_coe_re : (centerTwo : ℂ).re = stripLeft :=
  centerTwo_re

private theorem SpecialPeriods.Triangle.centerOne_norm_add_one : ‖(centerOne : ℂ) + 1‖ = 1 := by
  simpa only [centerOne_val, sub_add_cancel] using SpecialPeriods.norm_rho

private theorem SpecialPeriods.Triangle.centerTwo_norm_add_one : ‖(centerTwo : ℂ) + 1‖ = 1 := by
  have hsq : Complex.normSq ((centerTwo : ℂ) + 1) = 1 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im,
      Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, centerTwo_re,
      centerTwo_im]
    nlinarith [width_sq]
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg ((centerTwo : ℂ) + 1)]

public
theorem SpecialPeriods.Triangle.complex_eq_of_re_eq_norm_add_one_eq {z w : ℂ} (hr : z.re = w.re)
    (hz : 0 < z.im) (hw : 0 < w.im) (hn : ‖z + 1‖ = ‖w + 1‖) : z = w := by
  apply Complex.ext hr
  apply (sq_eq_sq₀ hz.le hw.le).mp
  have hsq : Complex.normSq (z + 1) = Complex.normSq (w + 1) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hn]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero, hr] at hsq
  nlinarith

private theorem SpecialPeriods.Triangle.right_circle_endpoint_iff (z : ℂ) :
    (z.re = -1 / 2 ∧ 0 < z.im ∧ ‖z + 1‖ = 1) ↔ z = (centerOne : ℂ) := by
  constructor
  · rintro ⟨hr, hi, hn⟩
    exact
      complex_eq_of_re_eq_norm_add_one_eq (hr.trans centerOne_coe_re.symm) hi centerOne.im_pos
        (hn.trans centerOne_norm_add_one.symm)
  · rintro rfl
    exact ⟨centerOne_coe_re, centerOne.im_pos, centerOne_norm_add_one⟩

private theorem SpecialPeriods.Triangle.left_circle_endpoint_iff (z : ℂ) :
    (z.re = stripLeft ∧ 0 < z.im ∧ ‖z + 1‖ = 1) ↔ z = (centerTwo : ℂ) := by
  constructor
  · rintro ⟨hr, hi, hn⟩
    exact
      complex_eq_of_re_eq_norm_add_one_eq (hr.trans centerTwo_coe_re.symm) hi centerTwo.im_pos
        (hn.trans centerTwo_norm_add_one.symm)
  · rintro rfl
    exact ⟨centerTwo_coe_re, centerTwo.im_pos, centerTwo_norm_add_one⟩

private theorem SpecialPeriods.Triangle.mem_frontier_triangleInterior_iff_closedRegion {z : ℂ} :
    z ∈ frontier triangleInterior ↔ z ∈ triangleClosedRegion ∧ z ∉ triangleInterior := by
  rw [frontier, triangleInterior_isOpen.interior_eq, closure_triangleInterior]
  rfl

private theorem SpecialPeriods.Triangle.triangleOpenLeftSide_subset_frontier :
    triangleOpenLeftSide ⊆ frontier triangleInterior := by
  intro z hz
  rw [mem_frontier_triangleInterior_iff_closedRegion]
  refine ⟨⟨hz.1.symm.le, ?_, hz.2.1, hz.2.2.le⟩, ?_⟩
  · simpa only [hz.1] using stripLeft_lt_right.le
  · exact fun h => Set.disjoint_left.mp triangleOpenLeftSide_disjoint_interior hz h

private theorem SpecialPeriods.Triangle.triangleOpenRightSide_subset_frontier :
    triangleOpenRightSide ⊆ frontier triangleInterior := by
  intro z hz
  rw [mem_frontier_triangleInterior_iff_closedRegion]
  refine ⟨⟨?_, hz.1.le, hz.2.1, hz.2.2.le⟩, ?_⟩
  · simpa only [hz.1] using stripLeft_lt_right.le
  · exact fun h => Set.disjoint_left.mp triangleOpenRightSide_disjoint_interior hz h

private theorem SpecialPeriods.Triangle.triangleOpenCircleSide_subset_frontier :
    triangleOpenCircleSide ⊆ frontier triangleInterior := by
  intro z hz
  rw [mem_frontier_triangleInterior_iff_closedRegion]
  exact
    ⟨⟨hz.1.le, hz.2.1.le, hz.2.2.1, hz.2.2.2.symm.le⟩, fun h =>
      Set.disjoint_left.mp triangleOpenCircleSide_disjoint_interior hz h⟩

private theorem SpecialPeriods.Triangle.centerOne_mem_triangleClosedRegion :
    (centerOne : ℂ) ∈ triangleClosedRegion := by
  refine ⟨?_, ?_, centerOne.im_pos, ?_⟩
  · rw [centerOne_coe_re]
    exact stripLeft_lt_right.le
  · rw [centerOne_coe_re]
  · rw [centerOne_norm_add_one]

private theorem SpecialPeriods.Triangle.centerTwo_mem_triangleClosedRegion :
    (centerTwo : ℂ) ∈ triangleClosedRegion := by
  refine ⟨?_, ?_, centerTwo.im_pos, ?_⟩
  · rw [centerTwo_coe_re]
  · rw [centerTwo_coe_re]
    exact stripLeft_lt_right.le
  · rw [centerTwo_norm_add_one]

private theorem SpecialPeriods.Triangle.centerOne_not_mem_triangleInterior :
    (centerOne : ℂ) ∉ triangleInterior := by
  intro hz
  have h := hz.2.1
  rw [centerOne_coe_re] at h
  exact lt_irrefl _ h

private theorem SpecialPeriods.Triangle.centerTwo_not_mem_triangleInterior :
    (centerTwo : ℂ) ∉ triangleInterior := by
  intro hz
  have h := hz.1
  rw [centerTwo_coe_re] at h
  exact lt_irrefl _ h

private theorem SpecialPeriods.Triangle.centerOne_mem_frontier_triangleInterior :
    (centerOne : ℂ) ∈ frontier triangleInterior :=
  mem_frontier_triangleInterior_iff_closedRegion.mpr
    ⟨centerOne_mem_triangleClosedRegion, centerOne_not_mem_triangleInterior⟩

private theorem SpecialPeriods.Triangle.centerTwo_mem_frontier_triangleInterior :
    (centerTwo : ℂ) ∈ frontier triangleInterior :=
  mem_frontier_triangleInterior_iff_closedRegion.mpr
    ⟨centerTwo_mem_triangleClosedRegion, centerTwo_not_mem_triangleInterior⟩

private theorem SpecialPeriods.Triangle.centerOne_mem_closure_triangleInterior :
    (centerOne : ℂ) ∈ closure triangleInterior := by
  rw [closure_triangleInterior]
  exact centerOne_mem_triangleClosedRegion

private theorem SpecialPeriods.Triangle.centerTwo_mem_closure_triangleInterior :
    (centerTwo : ℂ) ∈ closure triangleInterior := by
  rw [closure_triangleInterior]
  exact centerTwo_mem_triangleClosedRegion

private theorem
    SpecialPeriods.Triangle.centerOne_coe_ne_centerTwo : (centerOne : ℂ) ≠ (centerTwo : ℂ) := by
  intro h
  have hr := congrArg Complex.re h
  rw [centerOne_coe_re, centerTwo_coe_re] at hr
  exact (ne_of_gt stripLeft_lt_right) hr

private theorem SpecialPeriods.Triangle.mem_frontier_triangleInterior_iff {z : ℂ} :
    z ∈ frontier triangleInterior ↔
      z ∈ triangleOpenLeftSide ∨
        z ∈ triangleOpenRightSide ∨
          z ∈ triangleOpenCircleSide ∨ z = (centerOne : ℂ) ∨ z = (centerTwo : ℂ) := by
  constructor
  · intro hz
    obtain ⟨hR, hI⟩ := mem_frontier_triangleInterior_iff_closedRegion.mp hz
    rcases lt_or_eq_of_le hR.1 with hL | hL
    · rcases lt_or_eq_of_le hR.2.1 with hU | hU
      · rcases lt_or_eq_of_le hR.2.2.2 with hN | hN
        · exact (hI ⟨hL, hU, hR.2.2.1, hN⟩).elim
        · exact Or.inr (Or.inr (Or.inl ⟨hL, hU, hR.2.2.1, hN.symm⟩))
      · rcases lt_or_eq_of_le hR.2.2.2 with hN | hN
        · exact Or.inr (Or.inl ⟨hU, hR.2.2.1, hN⟩)
        · exact
            Or.inr
              (Or.inr
                (Or.inr (Or.inl ((right_circle_endpoint_iff z).mp ⟨hU, hR.2.2.1, hN.symm⟩))))
    · rcases lt_or_eq_of_le hR.2.2.2 with hN | hN
      · exact Or.inl ⟨hL.symm, hR.2.2.1, hN⟩
      · exact
          Or.inr
            (Or.inr
              (Or.inr (Or.inr ((left_circle_endpoint_iff z).mp ⟨hL.symm, hR.2.2.1, hN.symm⟩))))
  · rintro (h | h | h | rfl | rfl)
    · exact triangleOpenLeftSide_subset_frontier h
    · exact triangleOpenRightSide_subset_frontier h
    · exact triangleOpenCircleSide_subset_frontier h
    · exact centerOne_mem_frontier_triangleInterior
    · exact centerTwo_mem_frontier_triangleInterior

private def SpecialPeriods.Triangle.triangleClosedCenterOne : TriangleClosedDomain :=
  ⟨((centerOne : ℂ) : OnePoint ℂ),
    (coe_mem_triangleClosedSet_iff_closure _).mpr centerOne_mem_closure_triangleInterior⟩

private def SpecialPeriods.Triangle.triangleClosedCenterTwo : TriangleClosedDomain :=
  ⟨((centerTwo : ℂ) : OnePoint ℂ),
    (coe_mem_triangleClosedSet_iff_closure _).mpr centerTwo_mem_closure_triangleInterior⟩

@[simp]
private theorem SpecialPeriods.Triangle.triangleClosedCenterOne_val :
    (triangleClosedCenterOne : OnePoint ℂ) = ((centerOne : ℂ) : OnePoint ℂ) :=
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.triangleClosedCenterTwo_val :
    (triangleClosedCenterTwo : OnePoint ℂ) = ((centerTwo : ℂ) : OnePoint ℂ) :=
  rfl

private theorem SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo :
    triangleClosedCenterOne ≠ triangleClosedCenterTwo := by
  intro h
  exact centerOne_coe_ne_centerTwo (OnePoint.coe_injective (congrArg Subtype.val h))

@[simp]
private theorem SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty :
    triangleClosedCenterOne ≠ triangleClosedInfinity := by
  intro h
  exact OnePoint.coe_ne_infty (centerOne : ℂ) (congrArg Subtype.val h)

@[simp]
private theorem SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty :
    triangleClosedCenterTwo ≠ triangleClosedInfinity := by
  intro h
  exact OnePoint.coe_ne_infty (centerTwo : ℂ) (congrArg Subtype.val h)

private theorem SpecialPeriods.Triangle.mem_triangleOnePoint_frontier_iff {x : OnePoint ℂ} :
    x ∈ frontier (RiemannBoundary.onePointDomain triangleInterior) ↔
      x = (OnePoint.infty) ∨
        x ∈ RiemannBoundary.onePointDomain triangleOpenLeftSide ∨
          x ∈ RiemannBoundary.onePointDomain triangleOpenRightSide ∨
            x ∈ RiemannBoundary.onePointDomain triangleOpenCircleSide ∨
              x = ((centerOne : ℂ) : OnePoint ℂ) ∨ x = ((centerTwo : ℂ) : OnePoint ℂ) := by
  induction x using OnePoint.rec with
  | infty => exact iff_of_true triangle_infty_mem_frontier (Or.inl rfl)
  | coe z =>
    simpa only [coe_mem_triangleOnePoint_frontier_iff, OnePoint.coe_ne_infty, false_or,
      RiemannBoundary.coe_mem_onePointDomain, OnePoint.coe_eq_coe] using
      (mem_frontier_triangleInterior_iff (z := z))

private theorem
    SpecialPeriods.Triangle.triangleClosedBoundary_iff_cases (x : TriangleClosedDomain) :
    x ∉ triangleClosedInterior ↔
      x = triangleClosedInfinity ∨
        x.val ∈ RiemannBoundary.onePointDomain triangleOpenLeftSide ∨
          x.val ∈ RiemannBoundary.onePointDomain triangleOpenRightSide ∨
            x.val ∈ RiemannBoundary.onePointDomain triangleOpenCircleSide ∨
              x = triangleClosedCenterOne ∨ x = triangleClosedCenterTwo := by
  rw [triangleClosedBoundary_iff_frontier]
  simpa only [Subtype.ext_iff, triangleClosedInfinity, triangleClosedCenterOne_val,
    triangleClosedCenterTwo_val] using (mem_triangleOnePoint_frontier_iff (x := x.val))

private theorem SpecialPeriods.Triangle.triangleClosedBoundary_cases (x : TriangleClosedDomain)
    (hx : x ∉ triangleClosedInterior) :
    x = triangleClosedInfinity ∨
      (∃ z : ℂ, z ∈ triangleOpenLeftSide ∧ x.val = (z : OnePoint ℂ)) ∨
        (∃ z : ℂ, z ∈ triangleOpenRightSide ∧ x.val = (z : OnePoint ℂ)) ∨
          (∃ z : ℂ, z ∈ triangleOpenCircleSide ∧ x.val = (z : OnePoint ℂ)) ∨
            x = triangleClosedCenterOne ∨ x = triangleClosedCenterTwo := by
  rcases (triangleClosedBoundary_iff_cases x).mp hx with hi | hL | hR | hC | h₁ | h₂
  · exact Or.inl hi
  · obtain ⟨z, hz, he⟩ := hL
    exact Or.inr (Or.inl ⟨z, hz, he.symm⟩)
  · obtain ⟨z, hz, he⟩ := hR
    exact Or.inr (Or.inr (Or.inl ⟨z, hz, he.symm⟩))
  · obtain ⟨z, hz, he⟩ := hC
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨z, hz, he.symm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₂))))

private def RiemannBoundary.openRectangle (a b c d : ℝ) : Set ℂ :=
  {z | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d}

private theorem
    RiemannBoundary.isOpen_openRectangle (a b c d : ℝ) : IsOpen (openRectangle a b c d) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

private theorem
    RiemannBoundary.convex_openRectangle (a b c d : ℝ) : Convex ℝ (openRectangle a b c d) :=
  ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt b)).inter
    ((convex_halfSpace_im_gt c).inter (convex_halfSpace_im_lt d))

private theorem RiemannBoundary.mixed_mem_openRectangle {a b c d : ℝ} {z w : ℂ}
    (hz : z ∈ openRectangle a b c d) (hw : w ∈ openRectangle a b c d) :
    z.re + w.im * Complex.I ∈ openRectangle a b c d := by
  simpa only [openRectangle, Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, MulZeroClass.mul_zero, MulZeroClass.zero_mul,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add] using
    And.intro hz.1 hw.2

private theorem RiemannBoundary.rectangle_subset_openRectangle {a b c d : ℝ} {z w : ℂ}
    (hz : z ∈ openRectangle a b c d) (hw : w ∈ openRectangle a b c d) :
    Complex.Rectangle z w ⊆ openRectangle a b c d :=
  Complex.Convex.rectangle_subset (convex_openRectangle a b c d) hz hw
    (mixed_mem_openRectangle hz hw) (mixed_mem_openRectangle hw hz)

private theorem RiemannBoundary.horizontal_segment_subset_mo1973_19308 {a b c d : ℝ} {x₁ x₂ y : ℝ}
    (h₁ : (x₁ : ℂ) + y * Complex.I ∈ openRectangle a b c d)
    (h₂ : (x₂ : ℂ) + y * Complex.I ∈ openRectangle a b c d) :
    (fun x : ℝ => (x : ℂ) + y * Complex.I) '' [[x₁, x₂]] ⊆ openRectangle a b c d := by
  convert rectangle_subset_openRectangle h₁ h₂ using 1
  simp [Complex.horizontalSegment_eq x₁ x₂ y, Complex.Rectangle]

private theorem RiemannBoundary.vertical_segment_subset_mo1973_19309 {a b c d : ℝ} {x y₁ y₂ : ℝ}
    (h₁ : (x : ℂ) + y₁ * Complex.I ∈ openRectangle a b c d)
    (h₂ : (x : ℂ) + y₂ * Complex.I ∈ openRectangle a b c d) :
    (fun y : ℝ => (x : ℂ) + y * Complex.I) '' [[y₁, y₂]] ⊆ openRectangle a b c d := by
  convert rectangle_subset_openRectangle h₁ h₂ using 1
  simp [Complex.verticalSegment_eq x y₁ y₂, Complex.Rectangle]

private theorem
    RiemannBoundary.wedgeIntegral_sub_wedgeIntegral_openRectangle {a b c d : ℝ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (openRectangle a b c d))
    (hf : Complex.IsConservativeOn f (openRectangle a b c d)) {p z w : ℂ}
    (hp : p ∈ openRectangle a b c d) (hz : z ∈ openRectangle a b c d)
    (hw : w ∈ openRectangle a b c d) :
    Complex.wedgeIntegral p w f - Complex.wedgeIntegral p z f = Complex.wedgeIntegral z w f := by
  have integrableHoriz (x₁ x₂ y : ℝ) (h₁ : (x₁ : ℂ) + y * Complex.I ∈ openRectangle a b c d)
    (h₂ : (x₂ : ℂ) + y * Complex.I ∈ openRectangle a b c d) :
    IntervalIntegrable (fun x : ℝ => f (x + y * Complex.I)) MeasureTheory.MeasureSpace.volume x₁
      x₂ :=
    ((hc.mono (horizontal_segment_subset_mo1973_19308 h₁ h₂)).comp (by fun_prop)
        (Set.mapsTo_image _ _)).intervalIntegrable
  have integrableVert (x y₁ y₂ : ℝ) (h₁ : (x : ℂ) + y₁ * Complex.I ∈ openRectangle a b c d)
    (h₂ : (x : ℂ) + y₂ * Complex.I ∈ openRectangle a b c d) :
    IntervalIntegrable (fun y : ℝ => f (x + y * Complex.I)) MeasureTheory.MeasureSpace.volume y₁
      y₂ :=
    ((hc.mono (vertical_segment_subset_mo1973_19309 h₁ h₂)).comp (by fun_prop)
        (Set.mapsTo_image _ _)).intervalIntegrable
  have hHoriz :
    (∫ x in p.re..w.re, f (x + p.im * Complex.I)) =
      (∫ x in p.re..z.re, f (x + p.im * Complex.I)) +
        (∫ x in z.re..w.re, f (x + p.im * Complex.I)) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · apply integrableHoriz
      · simpa only [Complex.re_add_im] using hp
      · exact mixed_mem_openRectangle hz hp
    · apply integrableHoriz
      · exact mixed_mem_openRectangle hz hp
      · exact mixed_mem_openRectangle hw hp
  have hVert :
    Complex.I * (∫ y in p.im..w.im, f (w.re + y * Complex.I)) =
      Complex.I * (∫ y in p.im..z.im, f (w.re + y * Complex.I)) +
        Complex.I * (∫ y in z.im..w.im, f (w.re + y * Complex.I)) := by
    rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals]
    · apply integrableVert
      · exact mixed_mem_openRectangle hw hp
      · exact mixed_mem_openRectangle hw hz
    · apply integrableVert
      · exact mixed_mem_openRectangle hw hz
      · simpa only [Complex.re_add_im] using hw
  have hRect :=
    hf (z.re + p.im * Complex.I) (w.re + z.im * Complex.I)
      (rectangle_subset_openRectangle (mixed_mem_openRectangle hz hp)
        (mixed_mem_openRectangle hw hz))
  have hBoundary :
    (∫ x in z.re..w.re, f (x + p.im * Complex.I)) -
            (∫ x in z.re..w.re, f (x + z.im * Complex.I)) +
          Complex.I * (∫ y in p.im..z.im, f (w.re + y * Complex.I)) -
        Complex.I * (∫ y in p.im..z.im, f (z.re + y * Complex.I)) =
      0 := by
    simpa [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq] using hRect
  simp only [Complex.wedgeIntegral, smul_eq_mul]
  rw [hHoriz, hVert]
  linear_combination hBoundary

private theorem RiemannBoundary.hasDerivAt_wedgeIntegral_openRectangle {a b c d : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (openRectangle a b c d)) {p z : ℂ} (hp : p ∈ openRectangle a b c d)
    (hz : z ∈ openRectangle a b c d) :
    HasDerivAt (fun w => Complex.wedgeIntegral p w f) (f z) z := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (isOpen_openRectangle a b c d) z hz
  have hd : HasDerivAt (fun w => Complex.wedgeIntegral z w f) (f z) z :=
    (hf.isConservativeOn.mono hsub).hasDerivAt_wedgeIntegral (hf.continuousOn.mono hsub)
      (Metric.mem_ball_self hr)
  apply (hd.add_const (Complex.wedgeIntegral p z f)).congr_of_eventuallyEq
  filter_upwards [(isOpen_openRectangle a b c d).mem_nhds hz] with w hw
  exact
    sub_eq_iff_eq_add.mp
      (wedgeIntegral_sub_wedgeIntegral_openRectangle hf.continuousOn hf.isConservativeOn hp hz hw)

private theorem RiemannBoundary.isExactOn_openRectangle {a b c d : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (openRectangle a b c d)) :
    Complex.IsExactOn f (openRectangle a b c d) := by
  by_cases h : (openRectangle a b c d).Nonempty
  · obtain ⟨p, hp⟩ := h
    exact
      ⟨fun z => Complex.wedgeIntegral p z f, fun _ hz =>
        hasDerivAt_wedgeIntegral_openRectangle hf hp hz⟩
  · refine ⟨fun _ => 0, fun z hz => ?_⟩
    exact (h ⟨z, hz⟩).elim

private theorem RiemannBoundary.exists_lipschitz_extension_primitive_openRectangle {a b c d : ℝ}
    {f : ℂ → ℂ} {F : ℂ → ℂ} {K : ℝ≥0} (hF : ∀ z ∈ openRectangle a b c d, HasDerivAt F (f z) z)
    (hb : ∀ z ∈ openRectangle a b c d, ‖f z‖₊ ≤ K) :
    ∃ G : ℂ → ℂ,
      LipschitzWith (lipschitzExtensionConstant ℂ * K) G ∧
        Set.EqOn F G (openRectangle a b c d) ∧
          ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  have hLip : LipschitzOnWith K F (openRectangle a b c d) :=
    (convex_openRectangle a b c d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => (hF z hz).hasDerivWithinAt) hb
  obtain ⟨G, hG, heq⟩ := hLip.extend_finite_dimension
  refine ⟨G, hG, heq, fun z hz => ?_⟩
  apply (hF z hz).congr_of_eventuallyEq
  filter_upwards [(isOpen_openRectangle a b c d).mem_nhds hz] with w hw
  exact (heq hw).symm

private theorem RiemannBoundary.exists_continuous_primitive_openRectangle {a b c d : ℝ} {f : ℂ → ℂ}
    {K : ℝ≥0} (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (hb : ∀ z ∈ openRectangle a b c d, ‖f z‖₊ ≤ K) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  obtain ⟨F, hF⟩ := isExactOn_openRectangle hf
  obtain ⟨G, hG, _, hd⟩ := exists_lipschitz_extension_primitive_openRectangle hF hb
  exact ⟨G, hG.continuous, hd⟩

private theorem RiemannBoundary.exists_continuous_primitive_openRectangle_of_norm_le {a b c d : ℝ}
    {f : ℂ → ℂ} {M : ℝ} (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (hb : ∀ z ∈ openRectangle a b c d, ‖f z‖ ≤ M) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  apply exists_continuous_primitive_openRectangle (K := M.toNNReal) hf
  intro z hz
  exact_mod_cast (hb z hz).trans (Real.le_coe_toNNReal M)

private theorem RiemannBoundary.hasDerivAt_horizontal {F : ℂ → ℂ} {f : ℂ} {x y : ℝ}
    (hF : HasDerivAt F f ((x : ℂ) + y * Complex.I)) :
    HasDerivAt (fun t : ℝ => F (t + y * Complex.I)) f x := by
  have h := hF.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (y * Complex.I))
  simpa only [mul_one, Function.comp_def, id_eq] using h.comp_ofReal

private theorem RiemannBoundary.upper_limit_tendstoUniformlyOnFilter {q : ℂ → ℂ} {x : ℝ}
    (hq : Filter.Tendsto q (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0)) :
    TendstoUniformlyOnFilter (fun y t : ℝ => q (t + y * Complex.I)) (fun _ => 0) (𝓝[>] 0) (𝓝 x) :=
  by
  have ht :
    Filter.Tendsto (fun p : ℝ × ℝ => (p.2 : ℂ) + p.1 * Complex.I) ((𝓝[>] 0) ×ˢ 𝓝 x)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h₁ : Filter.Tendsto (fun p : ℝ × ℝ => (p.1 : ℂ)) ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝 (0 : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp
          (Filter.tendsto_fst.mono_right nhdsWithin_le_nhds)
      have h₂ : Filter.Tendsto (fun p : ℝ × ℝ => (p.2 : ℂ)) ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝 (x : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp Filter.tendsto_snd
      simpa using h₂.add (h₁.mul_const Complex.I)
    · have hy : ∀ᶠ p : ℝ × ℝ in (𝓝[>] 0) ×ˢ 𝓝 x, 0 < p.1 :=
        Filter.tendsto_fst.eventually eventually_mem_nhdsWithin
      filter_upwards [hy] with p hp
      simpa using hp
  apply Metric.tendstoUniformlyOnFilter_iff.mpr
  intro ε hε
  simpa only [Function.comp_def, dist_zero_left, dist_zero_right] using
    Metric.tendsto_nhds.mp (hq.comp ht) ε hε

private theorem
    RiemannBoundary.hasDerivAt_boundary_trace_sub {F G f g : ℂ → ℂ} {a b h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Set.Ioo a b) (hF : Continuous F) (hG : Continuous G)
    (hFd :
      ∀ t ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt F (f (t + y * Complex.I)) (t + y * Complex.I))
    (hGd :
      ∀ t ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt G (g (t - y * Complex.I)) (t - y * Complex.I))
    (hjump :
      ∀ t ∈ Set.Ioo a b,
        Filter.Tendsto (fun z => f z - g (conj z)) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 0)) :
    HasDerivAt (fun t : ℝ => F t - G t) 0 x := by
  let H : ℝ → ℝ → ℂ := fun y t => F (t + y * Complex.I) - G (t - y * Complex.I)
  let H' : ℝ → ℝ → ℂ := fun y t => f (t + y * Complex.I) - g (t - y * Complex.I)
  have hd : ∀ᶠ y in 𝓝[>] 0, ∀ t ∈ Set.Ioo a b, HasDerivAt (H y) (H' y t) t := by
    filter_upwards [Ioo_mem_nhdsGT hh] with y hy t ht
    have hu := hasDerivAt_horizontal (hFd t ht y hy)
    have hl : HasDerivAt (fun s : ℝ => G (s - y * Complex.I)) (g (t - y * Complex.I)) t := by
      have hi :=
        hasDerivAt_horizontal (y := -y)
          (by simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hGd t ht y hy)
      simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hi
    exact hu.sub hl
  have hdu : TendstoLocallyUniformlyOn H' (fun _ => 0) (𝓝[>] 0) (Set.Ioo a b) := by
    rw [tendstoLocallyUniformlyOn_iff_filter]
    intro t ht
    rw [isOpen_Ioo.nhdsWithin_eq ht]
    simpa only [H', map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      ← sub_eq_add_neg] using upper_limit_tendstoUniformlyOnFilter (hjump t ht)
  have hlim :
    ∀ t ∈ Set.Ioo a b, Filter.Tendsto (fun y => H y t) (𝓝[>] 0) (𝓝 (F (t : ℂ) - G (t : ℂ))) := by
    intro t _
    have hc : Continuous (fun y : ℝ => H y t) := by dsimp [H]; fun_prop
    simpa [H] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  exact hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioo hdu hd hlim hx

private theorem RiemannBoundary.boundary_trace_sub_eq {F G f g : ℂ → ℂ} {a b h x t : ℝ} (hh : 0 < h)
    (hx : x ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) (hF : Continuous F) (hG : Continuous G)
    (hFd :
      ∀ s ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt F (f (s + y * Complex.I)) (s + y * Complex.I))
    (hGd :
      ∀ s ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt G (g (s - y * Complex.I)) (s - y * Complex.I))
    (hjump :
      ∀ s ∈ Set.Ioo a b,
        Filter.Tendsto (fun z => f z - g (conj z)) (𝓝[{z : ℂ | 0 < z.im}] (s : ℂ)) (𝓝 0)) :
    F (x : ℂ) - G (x : ℂ) = F (t : ℂ) - G (t : ℂ) := by
  have hd (s : ℝ) (hs : s ∈ Set.Ioo a b) :=
    hasDerivAt_boundary_trace_sub hh hs hF hG hFd hGd hjump
  exact
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) hx ht

private theorem
    RiemannBoundary.exists_analytic_extension_of_vanishing_jump {f g : ℂ → ℂ} {a b h M N : ℝ}
    (hab : a < b) (hh : 0 < h) (hf : DifferentiableOn ℂ f (openRectangle a b 0 h))
    (hg : DifferentiableOn ℂ g (openRectangle a b (-h) 0))
    (hfb : ∀ z ∈ openRectangle a b 0 h, ‖f z‖ ≤ M)
    (hgb : ∀ z ∈ openRectangle a b (-h) 0, ‖g z‖ ≤ N)
    (hjump :
      ∀ x ∈ Set.Ioo a b,
        Filter.Tendsto (fun z => f z - g (conj z)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0)) :
    ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (openRectangle a b (-h) h) ∧
        Set.EqOn H f (openRectangle a b 0 h) ∧ Set.EqOn H g (openRectangle a b (-h) 0) := by
  obtain ⟨F, hFc, hFd⟩ := exists_continuous_primitive_openRectangle_of_norm_le hf hfb
  obtain ⟨G, hGc, hGd⟩ := exists_continuous_primitive_openRectangle_of_norm_le hg hgb
  let x₀ : ℝ := (a + b) / 2
  have hx₀ : x₀ ∈ Set.Ioo a b := by dsimp [x₀]; constructor <;> linarith
  let c : ℂ := F x₀ - G x₀
  have htrace : ∀ x ∈ Set.Ioo a b, F (x : ℂ) = G (x : ℂ) + c := by
    intro x hx
    have hdF :
      ∀ t ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt F (f (t + y * Complex.I)) (t + y * Complex.I) := by
      intro t ht y hy
      exact hFd _ (by simpa [openRectangle] using And.intro ht hy)
    have hdG :
      ∀ t ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt G (g (t - y * Complex.I)) (t - y * Complex.I) := by
      intro t ht y hy
      apply hGd
      simpa [openRectangle] using
        And.intro ht (show -y ∈ Set.Ioo (-h) 0 by constructor <;> linarith [hy.1, hy.2])
    have he := boundary_trace_sub_eq hh hx hx₀ hFc hGc hdF hdG hjump
    dsimp [c]
    linear_combination he
  let P := SchwarzReflection.pasteUpper F (fun z => G z + c)
  have hP : AnalyticOnNhd ℂ P (openRectangle a b (-h) h) := by
    apply
      SchwarzReflection.analyticOnNhd_pasteUpper (isOpen_openRectangle _ _ _ _) hFc.continuousOn
        (hGc.add continuous_const).continuousOn
    · intro z hz hpos
      exact (hFd z ⟨hz.1, hpos, hz.2.2⟩).differentiableAt
    · intro z hz hneg
      exact ((hGd z ⟨hz.1, hz.2.1, hneg⟩).add_const c).differentiableAt
    · intro z hz hzero
      change F z = G z + c
      have heq : (z.re : ℂ) = z := by exact Complex.ext (by simp) (by simpa using hzero.symm)
      simpa only [heq] using htrace z.re hz.1
  refine ⟨deriv P, hP.deriv, ?_, ?_⟩
  · intro z hz
    have hnear : P =ᶠ[𝓝 z] F := by
      filter_upwards [continuousAt_const.eventually_lt Complex.continuous_im.continuousAt
          hz.2.1] with
        w hw
      exact SchwarzReflection.pasteUpper_of_nonneg F (fun w => G w + c) hw.le
    exact ((hFd z hz).congr_of_eventuallyEq hnear).deriv
  · intro z hz
    have hnear : P =ᶠ[𝓝 z] (fun w => G w + c) := by
      filter_upwards [Complex.continuous_im.continuousAt.eventually_lt continuousAt_const
          hz.2.2] with
        w hw
      exact SchwarzReflection.pasteUpper_of_neg F (fun w => G w + c) hw
    exact (((hGd z hz).add_const c).congr_of_eventuallyEq hnear).deriv

private theorem
    RiemannBoundary.norm_sub_inv_conj (w : ℂ) : ‖w - (conj w)⁻¹‖ = |‖w‖ ^ 2 - 1| / ‖w‖ := by
  have heq : w - (conj w)⁻¹ = ((‖w‖ ^ 2 - 1 : ℝ) : ℂ) / conj w := by
    by_cases hw : w = 0
    · simp [hw]
    have hc : conj w ≠ 0 := by simpa using hw
    apply (eq_div_iff hc).mpr
    rw [sub_mul, inv_mul_cancel₀ hc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_sub, Complex.ofReal_one]
  rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]

private theorem RiemannBoundary.tendsto_sub_inv_conj_of_norm {α : Type*} {l : Filter α} {f : α → ℂ}
    (hf : Filter.Tendsto (fun x => ‖f x‖) l (𝓝 1)) :
    Filter.Tendsto (fun x => f x - (conj (f x))⁻¹) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_sub_inv_conj]
  have hn : Filter.Tendsto (fun x => |‖f x‖ ^ 2 - 1|) l (𝓝 (0 : ℝ)) := by
    simpa using ((hf.pow 2).sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  have hdiv := hn.div hf one_ne_zero
  have hfun :
    ((fun x => |‖f x‖ ^ 2 - 1|) / (fun x => ‖f x‖)) = (fun x => |‖f x‖ ^ 2 - 1| / ‖f x‖) := by rfl
  rw [hfun] at hdiv
  simpa only [zero_div] using hdiv

private theorem
    RiemannBoundary.norm_axis_eq_one_of_extension {H f : ℂ → ℂ} {a b h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Set.Ioo a b) (hH : ContinuousOn H (openRectangle a b (-h) h))
    (heq : Set.EqOn H f (openRectangle a b 0 h))
    (hmod : Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 1)) :
    ‖H (x : ℂ)‖ = 1 := by
  have hxU : (x : ℂ) ∈ openRectangle a b (-h) h := by
    simpa [openRectangle] using
      And.intro hx (show (0 : ℝ) ∈ Set.Ioo (-h) h by constructor <;> linarith)
  have hHt : Filter.Tendsto (fun y : ℝ => ‖H (x + y * Complex.I)‖) (𝓝[>] 0) (𝓝 ‖H (x : ℂ)‖) := by
    have hcont := (hH.continuousAt ((isOpen_openRectangle _ _ _ _).mem_nhds hxU)).norm
    have ht : Filter.Tendsto (fun y : ℝ => (x : ℂ) + y * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have hc : Continuous (fun y : ℝ => (x : ℂ) + y * Complex.I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    exact hcont.tendsto.comp ht
  have hft : Filter.Tendsto (fun y : ℝ => ‖f (x + y * Complex.I)‖) (𝓝[>] 0) (𝓝 1) := by
    apply hmod.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun y : ℝ => (x : ℂ) + y * Complex.I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
  have hevent :
    (fun y : ℝ => ‖H (x + y * Complex.I)‖) =ᶠ[𝓝[>] 0] (fun y : ℝ => ‖f (x + y * Complex.I)‖) := by
    filter_upwards [Ioo_mem_nhdsGT hh] with y hy
    rw [heq (by simpa [openRectangle] using And.intro hx hy)]
  exact tendsto_nhds_unique hHt (hft.congr' hevent.symm)

private theorem RiemannBoundary.exists_analytic_extension_of_modulus_one_bounded {f : ℂ → ℂ}
    {a b h M m : ℝ} (hab : a < b) (hh : 0 < h) (hm : 0 < m)
    (hf : DifferentiableOn ℂ f (openRectangle a b 0 h))
    (hfb : ∀ z ∈ openRectangle a b 0 h, ‖f z‖ ≤ M) (hfl : ∀ z ∈ openRectangle a b 0 h, m ≤ ‖f z‖)
    (hmod :
      ∀ x ∈ Set.Ioo a b, Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 1)) :
    ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (openRectangle a b (-h) h) ∧
        Set.EqOn H f (openRectangle a b 0 h) ∧
          Set.EqOn H (fun z => (conj (f (conj z)))⁻¹) (openRectangle a b (-h) 0) ∧
            ∀ x ∈ Set.Ioo a b, ‖H (x : ℂ)‖ = 1 := by
  let g : ℂ → ℂ := fun z => (conj (f (conj z)))⁻¹
  have hconj : ∀ z ∈ openRectangle a b (-h) 0, conj z ∈ openRectangle a b 0 h := by
    intro z hz
    refine ⟨by simpa using hz.1, ?_⟩
    simp only [Complex.conj_im, Set.mem_Ioo]
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hnz : ∀ z ∈ openRectangle a b 0 h, f z ≠ 0 := by
    intro z hz heq
    have hb := hfl z hz
    rw [heq, norm_zero] at hb
    exact (not_le.mpr hm) hb
  have hg : DifferentiableOn ℂ g (openRectangle a b (-h) 0) := by
    intro z hz
    have hd :=
      (hf.differentiableAt ((isOpen_openRectangle _ _ _ _).mem_nhds (hconj z hz))).conj_conj
    have hd' : DifferentiableAt ℂ (fun w => conj (f (conj w))) z := by
      simpa only [Function.comp_def, starRingEnd_self_apply] using hd
    exact (hd'.inv (by simpa using hnz (conj z) (hconj z hz))).differentiableWithinAt
  have hgb : ∀ z ∈ openRectangle a b (-h) 0, ‖g z‖ ≤ m⁻¹ := by
    intro z hz
    simp only [g, norm_inv, Complex.norm_conj]
    exact (inv_le_inv₀ (hm.trans_le (hfl _ (hconj z hz))) hm).mpr (hfl _ (hconj z hz))
  have hjump :
    ∀ x ∈ Set.Ioo a b,
      Filter.Tendsto (fun z => f z - g (conj z)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0) := by
    intro x hx
    simpa only [g, starRingEnd_self_apply] using tendsto_sub_inv_conj_of_norm (hmod x hx)
  obtain ⟨H, hH, he, hl⟩ := exists_analytic_extension_of_vanishing_jump hab hh hf hg hfb hgb hjump
  exact
    ⟨H, hH, he, hl, fun x hx =>
      norm_axis_eq_one_of_extension hh hx hH.continuousOn he (hmod x hx)⟩

private theorem RiemannBoundary.dist_lt_two_mul_of_mem_centeredRectangle {x r : ℝ} {z : ℂ}
    (hz : z ∈ openRectangle (x - r) (x + r) (-r) r) : Dist.dist z (x : ℂ) < 2 * r := by
  have hre : |(z - x).re| < r := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    exact abs_lt.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have him : |(z - x).im| < r := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using abs_lt.mpr hz.2
  rw [dist_eq_norm]
  exact (Complex.norm_le_abs_re_add_abs_im (z - x)).trans_lt (by linarith)

private theorem RiemannBoundary.ball_subset_centeredRectangle (x r : ℝ) :
    Metric.ball (x : ℂ) r ⊆ openRectangle (x - r) (x + r) (-r) r := by
  intro z hz
  have hn : ‖z - x‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hre := abs_lt.mp ((Complex.abs_re_le_norm (z - x)).trans_lt hn)
  have him := abs_lt.mp ((Complex.abs_im_le_norm (z - x)).trans_lt hn)
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    sub_zero] at hre him
  exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, him⟩

private theorem RiemannBoundary.exists_analytic_extension_of_modulus_one {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} {x : ℝ} (hx : (x : ℂ) ∈ U) (hf : DifferentiableOn ℂ f (U ∩ {z : ℂ | 0 < z.im}))
    (hmod :
      ∀ t : ℝ,
        (t : ℂ) ∈ U → Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1)) :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (x : ℂ) r) ∧
          Set.EqOn H f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (f (conj z)))⁻¹)
                (Metric.ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              ∀ t : ℝ, (t : ℂ) ∈ Metric.ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1 := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU (x : ℂ) hx
  obtain ⟨δ, hδ, hδf⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hmod x hx) (1 / 2) (by norm_num)
  let r : ℝ := Min.min ε δ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : 2 * r < ε := by
    have hm := min_le_left ε δ
    dsimp [r]
    linarith
  have hrδ : 2 * r < δ := by
    have hm := min_le_right ε δ
    dsimp [r]
    linarith
  have hrectU : openRectangle (x - r) (x + r) (-r) r ⊆ U := by
    intro z hz
    apply hεU
    exact (dist_lt_two_mul_of_mem_centeredRectangle hz).trans hrε
  have hu : openRectangle (x - r) (x + r) 0 r ⊆ U ∩ {z : ℂ | 0 < z.im} := by
    intro z hz
    exact ⟨hrectU ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩, hz.2.1⟩
  have hsize : ∀ z ∈ openRectangle (x - r) (x + r) 0 r, 1 / 2 ≤ ‖f z‖ ∧ ‖f z‖ ≤ 2 := by
    intro z hz
    have hzR : z ∈ openRectangle (x - r) (x + r) (-r) r := ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
    have he := hδf hz.2.1 ((dist_lt_two_mul_of_mem_centeredRectangle hzR).trans hrδ)
    rw [Real.dist_eq, abs_lt] at he
    constructor <;> linarith [he.1, he.2]
  have hmodR :
    ∀ t ∈ Set.Ioo (x - r) (x + r),
      Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1) := by
    intro t ht
    apply hmod
    apply hrectU
    simpa only [openRectangle, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im] using
      And.intro ht (show (0 : ℝ) ∈ Set.Ioo (-r) r by constructor <;> linarith)
  obtain ⟨H, hH, hHe, hHl, hHcircle⟩ :=
    exists_analytic_extension_of_modulus_one_bounded (by linarith) hr
      (show (0 : ℝ) < 1 / 2 by norm_num) (hf.mono hu) (fun z hz => (hsize z hz).2)
      (fun z hz => (hsize z hz).1) hmodR
  refine ⟨r, hr, H, hH.mono (ball_subset_centeredRectangle x r), ?_, ?_, ?_⟩
  · intro z hz
    have hzR := ball_subset_centeredRectangle x r hz.1
    exact hHe ⟨hzR.1, hz.2, hzR.2.2⟩
  · intro z hz
    have hzR := ball_subset_centeredRectangle x r hz.1
    exact hHl ⟨hzR.1, hzR.2.1, hz.2⟩
  · intro t ht
    have htR := ball_subset_centeredRectangle x r ht
    exact hHcircle t (by simpa only [Complex.ofReal_re] using htR.1)

private theorem RiemannBoundary.tendsto_norm_discHomeomorph_nhdsWithin_of_notMem {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) {a : ℂ}
    (ha : a ∉ D) : Filter.Tendsto (fun z => ‖f z‖) (𝓝[D] a) (𝓝 1) := by
  have hz :
    Filter.Tendsto (Subtype.val : D → ℂ) (Filter.comap (Subtype.val : D → ℂ) (𝓝[D] a)) (𝓝 a) :=
    Filter.tendsto_comap.mono_right nhdsWithin_le_nhds
  have ht := RiemannMapping.tendsto_norm_discHomeomorph_of_notMem e ha hz
  apply (Filter.tendsto_comap'_iff (i := (Subtype.val : D → ℂ)) ?_).mp
  · simpa only [Function.comp_def, he] using ht
  · simpa only [Subtype.range_coe] using (self_mem_nhdsWithin : D ∈ 𝓝[D] a)

private theorem RiemannBoundary.tendsto_norm_discHomeomorph_in_boundary_chart {D U : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f φ : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) (hU : IsOpen U)
    (hφ : ContinuousOn φ (U ∩ {z : ℂ | 0 ≤ z.im}))
    (hside : Set.MapsTo φ (U ∩ {z : ℂ | 0 < z.im}) D) {x : ℝ} (hx : (x : ℂ) ∈ U)
    (hout : φ (x : ℂ) ∉ D) :
    Filter.Tendsto (fun z => ‖f (φ z)‖) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 1) := by
  apply (tendsto_norm_discHomeomorph_nhdsWithin_of_notMem e he hout).comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc := hφ (x : ℂ) ⟨hx, by simp⟩
    apply hc.tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Filter.tendsto_id.mono_right nhdsWithin_le_nhds
    · have hnear : U ∈ 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ) :=
        mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)
      filter_upwards [hnear, self_mem_nhdsWithin] with z hz hu
      exact ⟨hz, le_of_lt hu⟩
  · have hnear : U ∈ 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ) := mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)
    filter_upwards [hnear, self_mem_nhdsWithin] with z hz hu
    exact hside ⟨hz, hu⟩

private theorem RiemannMapping.im_mul_exp_real_mo1973_19358 (c : ℂ) (θ : ℝ) :
    (c * Complex.exp ((θ : ℂ) * Complex.I)).im = ‖c‖ * Real.sin (c.arg + θ) := by
  calc
    (c * Complex.exp ((θ : ℂ) * Complex.I)).im =
        (((‖c‖ : ℝ) : ℂ) *
            (Complex.exp ((c.arg : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I))).im := by
      rw [← mul_assoc, Complex.norm_mul_exp_arg_mul_I]
    _ = (((‖c‖ : ℝ) : ℂ) * Complex.exp (((c.arg + θ : ℝ) : ℂ) * Complex.I)).im := by
      rw [← Complex.exp_add]
      congr 3
      push_cast
      ring
    _ = ‖c‖ * Real.sin (c.arg + θ) := by rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

private theorem RiemannMapping.im_mul_exp_real_pow_mo1973_19359 (c : ℂ) (θ : ℝ) (n : ℕ) :
    (c * Complex.exp ((θ : ℂ) * Complex.I) ^ n).im = ‖c‖ * Real.sin (c.arg + (n : ℝ) * θ) := by
  rw [← Complex.exp_nat_mul]
  have h : (n : ℂ) * ((θ : ℂ) * Complex.I) = (((n : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  exact im_mul_exp_real_mo1973_19358 c ((n : ℝ) * θ)

private theorem RiemannMapping.exists_unit_upperHalf_power_direction {c : ℂ} (hc : c ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) : ∃ v : ℂ, ‖v‖ = 1 ∧ 0 < v.im ∧ (c * v ^ n).im < 0 := by
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hc₀ : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hπ : 0 < Real.pi := Real.pi_pos
  have ha₁ : -Real.pi < c.arg := Complex.neg_pi_lt_arg c
  have ha₂ : c.arg ≤ Real.pi := Complex.arg_le_pi c
  have hπn : 2 * Real.pi ≤ Real.pi * n := by nlinarith
  by_cases ha : -(Real.pi / 2) < c.arg
  · let θ : ℝ := (3 * Real.pi / 2 - c.arg) / n
    have hθ₀ : 0 < θ := div_pos (by linarith) hn₀
    have hθπ : θ < Real.pi := by
      apply (div_lt_iff₀ hn₀).mpr
      linarith
    have hphase : c.arg + (n : ℝ) * θ = 3 * Real.pi / 2 := by
      dsimp [θ]
      rw [mul_comm (n : ℝ), div_mul_cancel₀ _ hn₀.ne']
      ring
    refine ⟨Complex.exp ((θ : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I θ, ?_, ?_⟩
    · rw [Complex.exp_ofReal_mul_I_im]
      exact Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ
    · rw [im_mul_exp_real_pow_mo1973_19359, hphase]
      rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
        Real.sin_pi_div_two]
      linarith
  · have ha' : c.arg ≤ -(Real.pi / 2) := le_of_not_gt ha
    let θ : ℝ := (-Real.pi / 4 - c.arg) / n
    have hθ₀ : 0 < θ := div_pos (by linarith) hn₀
    have hθπ : θ < Real.pi := by
      apply (div_lt_iff₀ hn₀).mpr
      linarith
    have hphase : c.arg + (n : ℝ) * θ = -Real.pi / 4 := by
      dsimp [θ]
      rw [mul_comm (n : ℝ), div_mul_cancel₀ _ hn₀.ne']
      ring
    refine ⟨Complex.exp ((θ : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I θ, ?_, ?_⟩
    · rw [Complex.exp_ofReal_mul_I_im]
      exact Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ
    · rw [im_mul_exp_real_pow_mo1973_19359, hphase]
      exact
        mul_neg_of_pos_of_neg hc₀ (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))

private theorem RiemannMapping.exists_upperHalf_power_direction {c : ℂ} (hc : c ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) : ∃ v : ℂ, 0 < v.im ∧ (c * v ^ n).im < 0 := by
  obtain ⟨v, _, hv, hcv⟩ := exists_unit_upperHalf_power_direction hc hn
  exact ⟨v, hv, hcv⟩

private theorem RiemannMapping.tendsto_boundaryRay (a v : ℂ) :
    Filter.Tendsto (fun t : ℝ => a + (t : ℂ) * v) (𝓝[>] 0) (𝓝 a) := by
  have hc : Continuous (fun t : ℝ => a + (t : ℂ) * v) := by fun_prop
  simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

private theorem RiemannMapping.boundaryRay_im_pos {a v : ℂ} (ha : a.im = 0) (hv : 0 < v.im) {t : ℝ}
    (ht : 0 < t) : 0 < (a + (t : ℂ) * v).im := by
  simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ha,
    MulZeroClass.zero_mul, MulZeroClass.mul_zero, add_zero, zero_add] using mul_pos ht hv

private theorem RiemannMapping.analyticOrderAt_ne_top_of_upper_halfPlane {f : ℂ → ℂ} {a : ℂ}
    (ha : a.im = 0) (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) : analyticOrderAt f a ≠ ⊤ := by
  intro htop
  have hz := (tendsto_boundaryRay a Complex.I).eventually (analyticOrderAt_eq_top.mp htop)
  have hp := (tendsto_boundaryRay a Complex.I).eventually hupper
  have hfalse : ∀ᶠ t : ℝ in 𝓝[>] 0, False := by
    filter_upwards [self_mem_nhdsWithin, hz, hp] with t ht hzero hpos
    have hi := hpos (boundaryRay_im_pos ha (by simp) ht)
    simp only [hzero, Complex.zero_im, lt_self_iff_false] at hi
  obtain ⟨t, ht⟩ := hfalse.exists
  exact ht

private theorem RiemannMapping.nonneg_im_leading_of_upper_halfPlane {f u : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (ha : a.im = 0) (hu : ContinuousAt u a) (hfactor : ∀ᶠ z in 𝓝 a, f z = (z - a) ^ m * u z)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) {v : ℂ} (hv : 0 < v.im) :
    0 ≤ (v ^ m * u a).im := by
  have hray := tendsto_boundaryRay a v
  have hlimC :
    Filter.Tendsto (fun t : ℝ => v ^ m * u (a + (t : ℂ) * v)) (𝓝[>] 0) (𝓝 (v ^ m * u a)) :=
    tendsto_const_nhds.mul (hu.tendsto.comp hray)
  have hlim :
    Filter.Tendsto (fun t : ℝ => (v ^ m * u (a + (t : ℂ) * v)).im) (𝓝[>] 0)
      (𝓝 (v ^ m * u a).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hlimC
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, hray.eventually hfactor, hray.eventually hupper] with t ht
    hft hpos
  have hft' : (f (a + (t : ℂ) * v)).im = t ^ m * (v ^ m * u (a + (t : ℂ) * v)).im := by
    rw [hft, add_sub_cancel_left, mul_pow, mul_assoc]
    simp only [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      MulZeroClass.zero_mul, add_zero]
  have hp : 0 < t ^ m * (v ^ m * u (a + (t : ℂ) * v)).im := by
    rw [← hft']
    exact hpos (boundaryRay_im_pos ha hv ht)
  exact ((mul_pos_iff_of_pos_left (pow_pos ht m)).mp hp).le

private theorem RiemannMapping.analyticOrderAt_eq_one_of_upper_halfPlane {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (ha : a.im = 0) (hfa : f a = 0)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) : analyticOrderAt f a = 1 := by
  have hfin := analyticOrderAt_ne_top_of_upper_halfPlane ha hupper
  let m := analyticOrderNatAt f a
  have horder : (m : ℕ∞) = analyticOrderAt f a := Nat.cast_analyticOrderNatAt hfin
  have hm0 : m ≠ 0 := by
    intro hm
    have hf0 : analyticOrderAt f a = 0 := by simpa [hm] using horder.symm
    exact (hf.analyticOrderAt_ne_zero.mpr hfa) hf0
  obtain ⟨u, hu, hua, hfactor⟩ := hf.analyticOrderAt_eq_natCast.mp horder.symm
  have hm2 : ¬2 ≤ m := by
    intro hm
    obtain ⟨v, hv, hneg⟩ := exists_upperHalf_power_direction hua hm
    have hnonneg : 0 ≤ (v ^ m * u a).im :=
      nonneg_im_leading_of_upper_halfPlane ha hu.continuousAt
        (by simpa only [smul_eq_mul] using hfactor) hupper hv
    rw [mul_comm] at hneg
    exact hneg.not_ge hnonneg
  have hm : m = 1 := by omega
  rw [← horder, hm]
  rfl

private theorem RiemannMapping.deriv_ne_zero_of_upper_halfPlane {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (ha : a.im = 0) (hfa : f a = 0)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) : deriv f a ≠ 0 := by
  have ho := analyticOrderAt_eq_one_of_upper_halfPlane hf ha hfa hupper
  have hd := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp ho
  simpa only [iteratedDeriv_one] using hd.2

private def RiemannMapping.boundaryLog (f : ℂ → ℂ) (a z : ℂ) : ℂ :=
  -Complex.I * Complex.log (f z / f a)

@[simp]
private theorem RiemannMapping.boundaryLog_self {f : ℂ → ℂ} {a : ℂ} (hfa : f a ≠ 0) :
    boundaryLog f a a = 0 := by simp [boundaryLog, hfa]

private theorem RiemannMapping.analyticAt_boundaryLog {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hfa : f a ≠ 0) : AnalyticAt ℂ (boundaryLog f a) a := by
  have hratio : AnalyticAt ℂ (fun z => f z / f a) a := hf.div_const
  have hslit : f a / f a ∈ Complex.slitPlane := by simp [hfa]
  exact analyticAt_const.mul (hratio.clog hslit)

private theorem RiemannMapping.hasDerivAt_boundaryLog {f : ℂ → ℂ} {a d : ℂ} (hf : HasDerivAt f d a)
    (hfa : f a ≠ 0) : HasDerivAt (boundaryLog f a) (-Complex.I * (d / f a)) a := by
  have hslit : f a / f a ∈ Complex.slitPlane := by simp [hfa]
  have hlog := (hf.div_const (f a)).clog hslit
  change HasDerivAt (fun z => -Complex.I * Complex.log (f z / f a)) (-Complex.I * (d / f a)) a
  simpa only [div_self hfa, div_one] using hlog.const_mul (-Complex.I)

private theorem
    RiemannMapping.im_boundaryLog_pos {f : ℂ → ℂ} {a z : ℂ} (hfa : ‖f a‖ = 1) (hfz : f z ≠ 0)
    (hz : ‖f z‖ < 1) : 0 < (boundaryLog f a z).im := by
  have hfa0 : f a ≠ 0 := by
    intro hzero
    simp [hzero] at hfa
  have hratio0 : 0 < ‖f z / f a‖ := norm_pos_iff.mpr (div_ne_zero hfz hfa0)
  have hratio1 : ‖f z / f a‖ < 1 := by simpa only [norm_div, hfa, div_one] using hz
  have hlog := Real.log_neg hratio0 hratio1
  simpa [boundaryLog, Complex.mul_im, Complex.log_re] using neg_pos.mpr hlog

private theorem RiemannMapping.deriv_ne_zero_of_upper_halfPlane_to_unitDisc {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (ha : a.im = 0) (hfa : ‖f a‖ = 1)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → ‖f z‖ < 1) : deriv f a ≠ 0 := by
  have hfa0 : f a ≠ 0 := by
    intro hzero
    simp [hzero] at hfa
  have hnz : ∀ᶠ z in 𝓝 a, f z ≠ 0 := hf.continuousAt.eventually_ne hfa0
  have hlogUpper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (boundaryLog f a z).im := by
    filter_upwards [hupper, hnz] with z hz hzne hzim
    exact im_boundaryLog_pos hfa hzne (hz hzim)
  have hlogDeriv :=
    deriv_ne_zero_of_upper_halfPlane (analyticAt_boundaryLog hf hfa0) ha (boundaryLog_self hfa0)
      hlogUpper
  intro hderiv
  apply hlogDeriv
  simpa [hderiv] using (hasDerivAt_boundaryLog hf.differentiableAt.hasDerivAt hfa0).deriv

private def RiemannMapping.triangleMap : ℂ → ℂ :=
  riemannMap triangleDomain SpecialPeriods.Triangle.triangleInterior_isSimplyConnected
    SpecialPeriods.Triangle.triangleInterior_ne_univ trianglePoint

private theorem RiemannMapping.triangleMap_differentiable :
    DifferentiableOn ℂ triangleMap SpecialPeriods.Triangle.triangleInterior :=
  (riemannMap_spec triangleDomain SpecialPeriods.Triangle.triangleInterior_isSimplyConnected
      SpecialPeriods.Triangle.triangleInterior_ne_univ trianglePoint).1

private theorem RiemannMapping.triangleMap_bijOn :
    Set.BijOn triangleMap SpecialPeriods.Triangle.triangleInterior (Metric.ball (0 : ℂ) 1) :=
  (riemannMap_spec triangleDomain SpecialPeriods.Triangle.triangleInterior_isSimplyConnected
        SpecialPeriods.Triangle.triangleInterior_ne_univ trianglePoint).2.1

private theorem RiemannMapping.triangleMap_biholomorph (z : triangleDomain) :
    triangleMap z = (triangleBiholomorph z : ℂ) :=
  rfl

private theorem RiemannMapping.triangleMap_norm_lt_one {z : ℂ}
    (hz : z ∈ SpecialPeriods.Triangle.triangleInterior) : ‖triangleMap z‖ < 1 := by
  simpa using triangleMap_bijOn.mapsTo hz

private theorem
    RiemannMapping.exists_boundary_chart_target_ball (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ w ∈ Metric.ball (e a) δ, w ∈ e.target ∧ e.symm w ∈ Metric.ball a r := by
  have hat := e.map_source ha
  have hinv : Filter.Tendsto e.symm (𝓝 (e a)) (𝓝 a) := by
    have h := (e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hat)).tendsto
    rwa [e.left_inv ha] at h
  have hnear : ∀ᶠ w in 𝓝 (e a), w ∈ e.target ∧ e.symm w ∈ Metric.ball a r := by
    filter_upwards [e.open_target.mem_nhds hat, hinv.eventually (Metric.ball_mem_nhds a hr)] with
      w hw hb
    exact ⟨hw, hb⟩
  exact Metric.mem_nhds_iff.mp hnear

private theorem SpecialPeriods.Triangle.cayley_re_sub (a z : ℂ) (hz : 1 - z ≠ 0) :
    (SpecialPeriods.cayley a z).re - a.re = -2 * a.im * z.im / Complex.normSq (1 - z) := by
  have hd : Complex.normSq (1 - z) ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  simp only [SpecialPeriods.cayley, Complex.div_re, Complex.sub_re, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.sub_im, Complex.mul_im, Complex.one_re,
    Complex.one_im]
  field_simp [hd]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

private theorem SpecialPeriods.Triangle.cayley_add_one (a z : ℂ) (hz : 1 - z ≠ 0) :
    SpecialPeriods.cayley a z + 1 = ((a + 1) - conj (a + 1) * z) / (1 - z) := by
  unfold SpecialPeriods.cayley
  simp only [map_add, map_one]
  field_simp
  ring

private theorem SpecialPeriods.Triangle.cayley_circle_normSq (a z : ℂ) (hz : 1 - z ≠ 0)
    (ha : Complex.normSq (a + 1) = 1) :
    Complex.normSq (SpecialPeriods.cayley a z + 1) - 1 =
      (2 * z.re - 2 * ((a + 1) ^ 2 * conj z).re) / Complex.normSq (1 - z) := by
  have hd : Complex.normSq (1 - z) ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  rw [cayley_add_one a z hz, map_div₀]
  field_simp [hd]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, add_zero, pow_two] at ha ⊢
  linear_combination (1 + z.re ^ 2 + z.im ^ 2) * ha

private theorem SpecialPeriods.Triangle.centerOne_re : centerOne.re = -1 / 2 := by
  simp only [UpperHalfPlane.re, centerOne_val, Complex.sub_re, SpecialPeriods.rho_re,
    Complex.one_re]
  norm_num

private theorem SpecialPeriods.Triangle.centerOne_circle_normSq :
    Complex.normSq ((centerOne : ℂ) + 1) = 1 := by
  rw [centerOne_val, sub_add_cancel, Complex.normSq_eq_norm_sq, SpecialPeriods.norm_rho]
  norm_num

private theorem SpecialPeriods.Triangle.centerTwo_circle_normSq :
    Complex.normSq ((centerTwo : ℂ) + 1) = 1 := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, centerTwo_re, centerTwo_im]
  nlinarith [width_sq]

private theorem SpecialPeriods.Triangle.cayley_centerOne_circle_normSq {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.normSq (SpecialPeriods.cayley centerOne z + 1) - 1 =
      (3 * z.re - Real.sqrt 3 * z.im) / Complex.normSq (1 - z) := by
  rw [cayley_circle_normSq _ _ (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)
      centerOne_circle_normSq]
  congr 1
  simp only [centerOne_val, sub_add_cancel, SpecialPeriods.rho_sq, Complex.mul_re, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im, sub_zero,
    SpecialPeriods.rho_re, SpecialPeriods.rho_im]
  ring

private theorem SpecialPeriods.Triangle.cayley_centerTwo_circle_normSq {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.normSq (SpecialPeriods.cayley centerTwo z + 1) - 1 =
      2 * (z.re + z.im) / Complex.normSq (1 - z) := by
  rw [cayley_circle_normSq _ _ (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)
      centerTwo_circle_normSq]
  congr 1
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, add_zero, Complex.conj_re, Complex.conj_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, centerTwo_re, centerTwo_im]
  linear_combination z.im * width_sq

private def SpecialPeriods.Triangle.cornerSectorThree : Set ℂ :=
  {z | 0 < z.im ∧ Real.sqrt 3 * z.im < 3 * z.re}

private def SpecialPeriods.Triangle.cornerSectorFour : Set ℂ :=
  {z | z.im < 0 ∧ 0 < z.re + z.im}

private theorem SpecialPeriods.Triangle.cayley_centerOne_right_iff {z : ℂ} (hz : ‖z‖ < 1) :
    (SpecialPeriods.cayley centerOne z).re < -1 / 2 ↔ 0 < z.im := by
  have h := cayley_re_sub centerOne z (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)
  rw [UpperHalfPlane.coe_re, centerOne_re] at h
  have hd := Complex.normSq_pos.mpr (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)
  have hc : 0 < (centerOne : ℂ).im := centerOne.im_pos
  have hsign : -2 * (centerOne : ℂ).im * z.im / Complex.normSq (1 - z) < 0 ↔ 0 < z.im := by
    rw [div_lt_iff₀ hd, MulZeroClass.zero_mul]
    constructor
    · intro hi
      by_contra hn
      have hle : z.im ≤ 0 := le_of_not_gt hn
      have hnonneg : 0 ≤ -2 * (centerOne : ℂ).im * z.im :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hle
      linarith
    · intro hi
      exact mul_neg_of_neg_of_pos (by linarith) hi
  rw [← h, sub_neg] at hsign
  exact hsign

private theorem SpecialPeriods.Triangle.cayley_centerTwo_left_iff {z : ℂ} (hz : ‖z‖ < 1) :
    stripLeft < (SpecialPeriods.cayley centerTwo z).re ↔ z.im < 0 := by
  have h := cayley_re_sub centerTwo z (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)
  rw [UpperHalfPlane.coe_re, centerTwo_re] at h
  change (SpecialPeriods.cayley centerTwo z).re - stripLeft = _ at h
  have hd := Complex.normSq_pos.mpr (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)
  have hc : 0 < (centerTwo : ℂ).im := centerTwo.im_pos
  have hsign : 0 < -2 * (centerTwo : ℂ).im * z.im / Complex.normSq (1 - z) ↔ z.im < 0 := by
    rw [div_pos_iff_of_pos_right hd]
    constructor
    · intro hi
      by_contra hn
      have hle : 0 ≤ z.im := le_of_not_gt hn
      have hnonpos : -2 * (centerTwo : ℂ).im * z.im ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hle
      linarith
    · intro hi
      exact mul_pos_of_neg_of_neg (by linarith) hi
  rw [← h, sub_pos] at hsign
  exact hsign

private theorem SpecialPeriods.Triangle.one_lt_norm_iff_normSq_sub_pos (u : ℂ) :
    1 < ‖u‖ ↔ 0 < Complex.normSq u - 1 := by
  rw [Complex.normSq_eq_norm_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg u]

private theorem SpecialPeriods.Triangle.cayley_centerOne_circle_iff {z : ℂ} (hz : ‖z‖ < 1) :
    1 < ‖SpecialPeriods.cayley centerOne z + 1‖ ↔ Real.sqrt 3 * z.im < 3 * z.re := by
  rw [one_lt_norm_iff_normSq_sub_pos, cayley_centerOne_circle_normSq hz,
    div_pos_iff_of_pos_right
      (Complex.normSq_pos.mpr (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)),
    sub_pos]

private theorem SpecialPeriods.Triangle.cayley_centerTwo_circle_iff {z : ℂ} (hz : ‖z‖ < 1) :
    1 < ‖SpecialPeriods.cayley centerTwo z + 1‖ ↔ 0 < z.re + z.im := by
  rw [one_lt_norm_iff_normSq_sub_pos, cayley_centerTwo_circle_normSq hz,
    div_pos_iff_of_pos_right
      (Complex.normSq_pos.mpr (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz))]
  exact mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)

private theorem SpecialPeriods.Triangle.cayley_analyticAt (a : ℂ) {z : ℂ} (hz : 1 - z ≠ 0) :
    AnalyticAt ℂ (SpecialPeriods.cayley a) z :=
  (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) hz

private theorem SpecialPeriods.Triangle.exists_cornerThree_radius :
    ∃ r : ℝ,
      0 < r ∧
        r ≤ 1 ∧
          ∀ z : ℂ,
            ‖z‖ < r →
              (SpecialPeriods.cayley centerOne z ∈ triangleInterior ↔ z ∈ cornerSectorThree) := by
  have hc : ContinuousAt (fun z : ℂ => (SpecialPeriods.cayley centerOne z).re) 0 :=
    Complex.continuous_re.continuousAt.comp
      (cayley_analyticAt centerOne (z := 0) (by simp)).continuousAt
  have hleft : ∀ᶠ z : ℂ in 𝓝 0, stripLeft < (SpecialPeriods.cayley centerOne z).re :=
    continuousAt_const.eventually_lt hc
      (by
        simp only [SpecialPeriods.cayley_zero, UpperHalfPlane.coe_re, centerOne_re]
        unfold stripLeft
        linarith [width_pos])
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp hleft
  refine ⟨Min.min s 1, lt_min hs zero_lt_one, min_le_right _ _, ?_⟩
  intro z hz
  have hz1 : ‖z‖ < 1 := hz.trans_le (min_le_right _ _)
  have hzs : z ∈ Metric.ball 0 s := by simpa using hz.trans_le (min_le_left _ _)
  have hzi := SpecialPeriods.cayley_im_pos centerOne.im_pos hz1
  change
    (stripLeft < (SpecialPeriods.cayley centerOne z).re ∧
        (SpecialPeriods.cayley centerOne z).re < -1 / 2 ∧
          0 < (SpecialPeriods.cayley centerOne z).im ∧
            1 < ‖SpecialPeriods.cayley centerOne z + 1‖) ↔
      _
  rw [cayley_centerOne_right_iff hz1, cayley_centerOne_circle_iff hz1]
  exact ⟨fun h => ⟨h.2.1, h.2.2.2⟩, fun h => ⟨hball hzs, h.1, hzi, h.2⟩⟩

private theorem SpecialPeriods.Triangle.exists_cornerFour_radius :
    ∃ r : ℝ,
      0 < r ∧
        r ≤ 1 ∧
          ∀ z : ℂ,
            ‖z‖ < r →
              (SpecialPeriods.cayley centerTwo z ∈ triangleInterior ↔ z ∈ cornerSectorFour) := by
  have hc : ContinuousAt (fun z : ℂ => (SpecialPeriods.cayley centerTwo z).re) 0 :=
    Complex.continuous_re.continuousAt.comp
      (cayley_analyticAt centerTwo (z := 0) (by simp)).continuousAt
  have hright : ∀ᶠ z : ℂ in 𝓝 0, (SpecialPeriods.cayley centerTwo z).re < -1 / 2 :=
    hc.eventually_lt continuousAt_const
      (by
        simp only [SpecialPeriods.cayley_zero, UpperHalfPlane.coe_re, centerTwo_re]
        linarith [width_pos])
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp hright
  refine ⟨Min.min s 1, lt_min hs zero_lt_one, min_le_right _ _, ?_⟩
  intro z hz
  have hz1 : ‖z‖ < 1 := hz.trans_le (min_le_right _ _)
  have hzs : z ∈ Metric.ball 0 s := by simpa using hz.trans_le (min_le_left _ _)
  have hzi := SpecialPeriods.cayley_im_pos centerTwo.im_pos hz1
  change
    (stripLeft < (SpecialPeriods.cayley centerTwo z).re ∧
        (SpecialPeriods.cayley centerTwo z).re < -1 / 2 ∧
          0 < (SpecialPeriods.cayley centerTwo z).im ∧
            1 < ‖SpecialPeriods.cayley centerTwo z + 1‖) ↔
      _
  rw [cayley_centerTwo_left_iff hz1, cayley_centerTwo_circle_iff hz1]
  exact ⟨fun h => ⟨h.1, h.2.2.2⟩, fun h => ⟨h.1, hball hzs, hzi, h.2⟩⟩

private def RiemannBoundary.principalRoot (n : ℕ) (z : ℂ) : ℂ :=
  z ^ ((n : ℂ)⁻¹)

@[simp]
private theorem RiemannBoundary.principalRoot_pow {n : ℕ} (hn : 0 < n) (z : ℂ) :
    principalRoot n z ^ n = z :=
  Complex.cpow_nat_inv_pow z hn.ne'

@[simp]
private theorem
    RiemannBoundary.principalRoot_zero {n : ℕ} (hn : 0 < n) : principalRoot n 0 = 0 := by
  exact Complex.zero_cpow (inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne'))

private theorem RiemannBoundary.principalRoot_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (principalRoot n) := by
  intro z w h
  simpa only [principalRoot_pow hn] using congrArg (fun u : ℂ => u ^ n) h

@[simp]
private theorem RiemannBoundary.principalRoot_eq_zero_iff {n : ℕ} (hn : 0 < n) {z : ℂ} :
    principalRoot n z = 0 ↔ z = 0 := by
  have h : principalRoot n z = principalRoot n 0 ↔ z = 0 := (principalRoot_injective hn).eq_iff
  simpa only [principalRoot_zero hn] using h

@[simp]
private theorem RiemannBoundary.norm_principalRoot (n : ℕ) (z : ℂ) :
    ‖principalRoot n z‖ = ‖z‖ ^ ((n : ℝ)⁻¹) :=
  Complex.norm_cpow_inv_nat z n

private theorem RiemannBoundary.principalRoot_exponent_re_pos_mo1973_19407 {n : ℕ} (hn : 0 < n) :
    0 < ((n : ℂ)⁻¹).re := by
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re] using
    inv_pos.mpr (Nat.cast_pos.mpr hn : (0 : ℝ) < n)

private theorem RiemannBoundary.continuousAt_principalRoot_zero {n : ℕ} (hn : 0 < n) :
    ContinuousAt (principalRoot n) 0 :=
  Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp))
    (principalRoot_exponent_re_pos_mo1973_19407 hn)

private theorem RiemannBoundary.continuousOn_principalRoot_closedUpper {n : ℕ} (hn : 0 < n) :
    ContinuousOn (principalRoot n) {z : ℂ | 0 ≤ z.im} := by
  intro z _hz
  change ContinuousWithinAt (fun w : ℂ => w ^ ((n : ℂ)⁻¹)) _ z
  by_cases h : 0 ≤ z.re ∨ z.im ≠ 0
  · exact
      (Complex.continuousAt_cpow_const_of_re_pos h
          (principalRoot_exponent_re_pos_mo1973_19407 hn)).continuousWithinAt
  push Not at h
  have hz0 : z ≠ 0 := fun hz => by simpa only [hz, Complex.zero_re, lt_self_iff_false] using h.1
  have hc :
    ContinuousWithinAt (fun w : ℂ => Complex.exp (Complex.log w * (n : ℂ)⁻¹)) {w : ℂ | 0 ≤ w.im}
      z :=
    Complex.continuous_exp.continuousAt.comp_continuousWithinAt
      ((Complex.continuousWithinAt_log_of_re_neg_of_im_zero h.1 h.2).mul_const _)
  exact
    hc.congr_of_eventuallyEq ((cpow_eq_nhds hz0).filter_mono nhdsWithin_le_nhds)
      (Complex.cpow_def_of_ne_zero hz0 _)

private theorem RiemannBoundary.differentiableOn_principalRoot_upper (n : ℕ) :
    DifferentiableOn ℂ (principalRoot n) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact
    ((differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ => w) z).cpow_const
        (Or.inr (ne_of_gt hz))).differentiableWithinAt

private theorem RiemannBoundary.analyticOnNhd_principalRoot_upper (n : ℕ) :
    AnalyticOnNhd ℂ (principalRoot n) {z : ℂ | 0 < z.im} :=
  (differentiableOn_principalRoot_upper n).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_im)

private theorem RiemannBoundary.principalRoot_ofReal_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    principalRoot n (x : ℂ) = (x ^ ((n : ℝ)⁻¹) : ℝ) := by
  simpa only [principalRoot, Complex.ofReal_inv, Complex.ofReal_natCast] using
    (Complex.ofReal_cpow hx ((n : ℝ)⁻¹)).symm

private theorem RiemannBoundary.principalRoot_ofReal_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    principalRoot n (x : ℂ) =
      ((-x) ^ ((n : ℝ)⁻¹) : ℝ) * Complex.exp ((Real.pi / (n : ℝ) : ℝ) * Complex.I) := by
  rw [principalRoot, Complex.ofReal_cpow_of_nonpos hx]
  have hr : (-(x : ℂ)) ^ ((n : ℂ)⁻¹) = ((-x) ^ ((n : ℝ)⁻¹) : ℝ) := by
    simpa only [principalRoot, Complex.ofReal_neg] using
      principalRoot_ofReal_nonneg n (neg_nonneg.mpr hx)
  rw [hr]
  congr 2
  simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

private theorem RiemannBoundary.arg_div_nat_mem_Ioc_mo1973_19416 {n : ℕ} (hn : 0 < n) (z : ℂ) :
    z.arg / (n : ℝ) ∈ Set.Ioc (-Real.pi) Real.pi := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · rw [lt_div_iff₀ hnR]
    have hl : -Real.pi * (n : ℝ) ≤ -Real.pi := by nlinarith [Real.pi_pos]
    exact hl.trans_lt (Complex.neg_pi_lt_arg z)
  · rw [div_le_iff₀ hnR]
    have hu : Real.pi ≤ Real.pi * (n : ℝ) := by nlinarith [Real.pi_pos]
    exact (Complex.arg_le_pi z).trans hu

private theorem RiemannBoundary.arg_principalRoot {n : ℕ} (hn : 0 < n) (z : ℂ) :
    Complex.arg (principalRoot n z) = z.arg / (n : ℝ) := by
  by_cases hz : z = 0
  · simp only [hz, principalRoot_zero hn, Complex.arg_zero, zero_div]
  have hpolar :
    principalRoot n z =
      (‖z‖ ^ ((n : ℝ)⁻¹) : ℝ) *
        (Real.cos (z.arg / (n : ℝ)) + Real.sin (z.arg / (n : ℝ)) * Complex.I) := by
    simpa only [principalRoot, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv] using
      Complex.cpow_ofReal z ((n : ℝ)⁻¹)
  rw [hpolar]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    Complex.arg_mul_cos_add_sin_mul_I (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) ((n : ℝ)⁻¹))
      (arg_div_nat_mem_Ioc_mo1973_19416 hn z)

private theorem
    RiemannBoundary.principalRoot_arg_mem_Ioo {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : 0 < z.im) :
    Complex.arg (principalRoot n z) ∈ Set.Ioo 0 (Real.pi / (n : ℝ)) := by
  rw [arg_principalRoot hn]
  have harg0 : z.arg ≠ 0 := fun h => (ne_of_gt hz) (Complex.arg_eq_zero_iff.mp h).2
  have harg : 0 < z.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) harg0.symm
  exact
    ⟨div_pos harg (Nat.cast_pos.mpr hn),
      (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hn)).mpr
        (Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hz)))⟩

private theorem RiemannBoundary.principalRoot_pow_of_sector {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : z.arg ∈ Set.Icc 0 (Real.pi / (n : ℝ))) : principalRoot n (z ^ n) = z := by
  apply Complex.pow_cpow_nat_inv hn.ne' _ hz.2
  exact (neg_neg_of_pos (div_pos Real.pi_pos (Nat.cast_pos.mpr hn))).trans_le hz.1

private theorem RiemannBoundary.cubic_sector_slack_mo1973_19421 (w : ℂ) :
    3 * w.re - Real.sqrt 3 * w.im = (2 * Real.sqrt 3 * ‖w‖) * Real.sin (Real.pi / 3 - w.arg) := by
  rw [Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three]
  rw [← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w]
  calc
    3 * (‖w‖ * Real.cos w.arg) - Real.sqrt 3 * (‖w‖ * Real.sin w.arg) =
        ‖w‖ * ((Real.sqrt 3 * Real.sqrt 3) * Real.cos w.arg - Real.sqrt 3 * Real.sin w.arg) := by
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    _ = _ := by ring

private theorem RiemannBoundary.quartic_sector_slack_mo1973_19422 (w : ℂ) :
    w.re - w.im = (Real.sqrt 2 * ‖w‖) * Real.sin (Real.pi / 4 - w.arg) := by
  rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
  rw [← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w]
  calc
    ‖w‖ * Real.cos w.arg - ‖w‖ * Real.sin w.arg =
        (‖w‖ / 2) *
          ((Real.sqrt 2 * Real.sqrt 2) * Real.cos w.arg -
            (Real.sqrt 2 * Real.sqrt 2) * Real.sin w.arg) := by
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ = _ := by ring

private theorem RiemannBoundary.principalRoot_three_upper {z : ℂ} (hz : 0 < z.im) :
    0 < (principalRoot 3 z).im ∧
      Real.sqrt 3 * (principalRoot 3 z).im < 3 * (principalRoot 3 z).re := by
  have ha := principalRoot_arg_mem_Ioo (by norm_num : 0 < 3) hz
  norm_num only [Nat.cast_ofNat] at ha
  have hw : principalRoot 3 z ≠ 0 := by
    rw [ne_eq, principalRoot_eq_zero_iff (by norm_num : 0 < 3)]
    exact fun h => by simp only [h, Complex.zero_im, lt_self_iff_false] at hz
  constructor
  · rw [← Complex.norm_mul_sin_arg]
    exact
      mul_pos (norm_pos_iff.mpr hw)
        (Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [Real.pi_pos, ha.2]))
  · apply sub_pos.mp
    rw [cubic_sector_slack_mo1973_19421]
    exact
      mul_pos
        (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))) (norm_pos_iff.mpr hw))
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [ha.2]) (by linarith [Real.pi_pos, ha.1]))

private theorem RiemannBoundary.principalRoot_three_ofReal_nonneg_im {x : ℝ} (hx : 0 ≤ x) :
    (principalRoot 3 (x : ℂ)).im = 0 := by
  rw [principalRoot_ofReal_nonneg 3 hx]
  exact Complex.ofReal_im _

private theorem RiemannBoundary.principalRoot_three_ofReal_nonpos_boundary {x : ℝ} (hx : x ≤ 0) :
    Real.sqrt 3 * (principalRoot 3 (x : ℂ)).im = 3 * (principalRoot 3 (x : ℂ)).re := by
  rw [principalRoot_ofReal_nonpos 3 hx]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    MulZeroClass.zero_mul, add_zero, sub_zero, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_re, Nat.cast_ofNat, Real.sin_pi_div_three, Real.cos_pi_div_three]
  have hsq := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  calc
    Real.sqrt 3 * ((-x) ^ (3 : ℝ)⁻¹ * (Real.sqrt 3 / 2)) =
        (Real.sqrt 3 * Real.sqrt 3) * ((-x) ^ (3 : ℝ)⁻¹ / 2) := by ring
    _ = _ := by rw [hsq]; ring

private theorem RiemannBoundary.principalRoot_three_real_boundary {z : ℂ} (hz : z.im = 0) :
    (principalRoot 3 z).im = 0 ∨
      Real.sqrt 3 * (principalRoot 3 z).im = 3 * (principalRoot 3 z).re := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he]
  rcases le_total 0 z.re with hp | hn
  · exact Or.inl (principalRoot_three_ofReal_nonneg_im hp)
  · exact Or.inr (principalRoot_three_ofReal_nonpos_boundary hn)

private def RiemannBoundary.quarticRootRotation : ℂ :=
  Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * Complex.I)

@[simp]
private theorem
    RiemannBoundary.quarticRootRotation_re : quarticRootRotation.re = Real.sqrt 2 / 2 := by
  simp only [quarticRootRotation, Complex.exp_ofReal_mul_I_re, neg_div, Real.cos_neg,
    Real.cos_pi_div_four]

@[simp]
private theorem
    RiemannBoundary.quarticRootRotation_im : quarticRootRotation.im = -(Real.sqrt 2 / 2) := by
  simp only [quarticRootRotation, Complex.exp_ofReal_mul_I_im, neg_div, Real.sin_neg,
    Real.sin_pi_div_four]

@[simp]
private theorem RiemannBoundary.norm_quarticRootRotation : ‖quarticRootRotation‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem RiemannBoundary.quarticRootRotation_ne_zero : quarticRootRotation ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
private theorem RiemannBoundary.quarticRootRotation_pow_four : quarticRootRotation ^ 4 = -1 := by
  rw [quarticRootRotation, ← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (4 : ℂ) * (((-Real.pi / 4 : ℝ) : ℂ) * Complex.I) = -(Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

private def RiemannBoundary.rotatedPrincipalRootFour (z : ℂ) : ℂ :=
  quarticRootRotation * principalRoot 4 z

@[simp]
private theorem RiemannBoundary.rotatedPrincipalRootFour_pow (z : ℂ) :
    rotatedPrincipalRootFour z ^ 4 = -z := by
  rw [rotatedPrincipalRootFour, mul_pow, quarticRootRotation_pow_four,
    principalRoot_pow (by norm_num : 0 < 4)]
  ring

@[simp]
private theorem RiemannBoundary.rotatedPrincipalRootFour_zero : rotatedPrincipalRootFour 0 = 0 := by
  rw [rotatedPrincipalRootFour, principalRoot_zero (by norm_num : 0 < 4), MulZeroClass.mul_zero]

@[simp]
private theorem RiemannBoundary.norm_rotatedPrincipalRootFour (z : ℂ) :
    ‖rotatedPrincipalRootFour z‖ = ‖z‖ ^ (4 : ℝ)⁻¹ := by
  rw [rotatedPrincipalRootFour, norm_mul, norm_quarticRootRotation, one_mul, norm_principalRoot]
  norm_num only [Nat.cast_ofNat]

private theorem RiemannBoundary.rotatedPrincipalRootFour_re (z : ℂ) :
    (rotatedPrincipalRootFour z).re =
      (Real.sqrt 2 / 2) * ((principalRoot 4 z).re + (principalRoot 4 z).im) := by
  simp only [rotatedPrincipalRootFour, Complex.mul_re, quarticRootRotation_re,
    quarticRootRotation_im]
  ring

private theorem RiemannBoundary.rotatedPrincipalRootFour_im (z : ℂ) :
    (rotatedPrincipalRootFour z).im =
      (Real.sqrt 2 / 2) * ((principalRoot 4 z).im - (principalRoot 4 z).re) := by
  simp only [rotatedPrincipalRootFour, Complex.mul_im, quarticRootRotation_re,
    quarticRootRotation_im]
  ring

private theorem RiemannBoundary.rotatedPrincipalRootFour_re_add_im (z : ℂ) :
    (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im =
      Real.sqrt 2 * (principalRoot 4 z).im := by
  rw [rotatedPrincipalRootFour_re, rotatedPrincipalRootFour_im]
  ring

private theorem RiemannBoundary.rotatedPrincipalRootFour_upper {z : ℂ} (hz : 0 < z.im) :
    (rotatedPrincipalRootFour z).im < 0 ∧
      0 < (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im := by
  have ha := principalRoot_arg_mem_Ioo (by norm_num : 0 < 4) hz
  norm_num only [Nat.cast_ofNat] at ha
  have hw : principalRoot 4 z ≠ 0 := by
    rw [ne_eq, principalRoot_eq_zero_iff (by norm_num : 0 < 4)]
    exact fun h => by simp only [h, Complex.zero_im, lt_self_iff_false] at hz
  have hi : 0 < (principalRoot 4 z).im := by
    rw [← Complex.norm_mul_sin_arg]
    exact
      mul_pos (norm_pos_iff.mpr hw)
        (Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [Real.pi_pos, ha.2]))
  have hri : (principalRoot 4 z).im < (principalRoot 4 z).re := by
    apply sub_pos.mp
    rw [quartic_sector_slack_mo1973_19422]
    exact
      mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (norm_pos_iff.mpr hw))
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [ha.2]) (by linarith [Real.pi_pos, ha.1]))
  constructor
  · rw [rotatedPrincipalRootFour_im]
    exact mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hri)
  · rw [rotatedPrincipalRootFour_re_add_im]
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) hi

private theorem
    RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonneg_boundary {x : ℝ} (hx : 0 ≤ x) :
    (rotatedPrincipalRootFour (x : ℂ)).re + (rotatedPrincipalRootFour (x : ℂ)).im = 0 := by
  rw [rotatedPrincipalRootFour_re_add_im, principalRoot_ofReal_nonneg 4 hx]
  simp only [Complex.ofReal_im, MulZeroClass.mul_zero]

private theorem RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonpos_im {x : ℝ} (hx : x ≤ 0) :
    (rotatedPrincipalRootFour (x : ℂ)).im = 0 := by
  rw [rotatedPrincipalRootFour_im, principalRoot_ofReal_nonpos 4 hx]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    MulZeroClass.zero_mul, add_zero, sub_zero, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_re, Nat.cast_ofNat, Real.sin_pi_div_four, Real.cos_pi_div_four,
    sub_self, MulZeroClass.mul_zero]

private theorem RiemannBoundary.rotatedPrincipalRootFour_real_boundary {z : ℂ} (hz : z.im = 0) :
    (rotatedPrincipalRootFour z).im = 0 ∨
      (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im = 0 := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he]
  rcases le_total 0 z.re with hp | hn
  · exact Or.inr (rotatedPrincipalRootFour_ofReal_nonneg_boundary hp)
  · exact Or.inl (rotatedPrincipalRootFour_ofReal_nonpos_im hn)

private theorem RiemannBoundary.continuousOn_rotatedPrincipalRootFour_closedUpper :
    ContinuousOn rotatedPrincipalRootFour {z : ℂ | 0 ≤ z.im} :=
  continuousOn_const.mul (continuousOn_principalRoot_closedUpper (by norm_num : 0 < 4))

private theorem RiemannBoundary.continuousAt_rotatedPrincipalRootFour_zero :
    ContinuousAt rotatedPrincipalRootFour 0 :=
  continuousAt_const.mul (continuousAt_principalRoot_zero (by norm_num : 0 < 4))

private theorem RiemannBoundary.analyticOnNhd_rotatedPrincipalRootFour_upper :
    AnalyticOnNhd ℂ rotatedPrincipalRootFour {z : ℂ | 0 < z.im} := by
  intro z hz
  exact analyticAt_const.mul (analyticOnNhd_principalRoot_upper 4 z hz)

private def SpecialPeriods.Triangle.cornerParameterThree (w : ℂ) : ℂ :=
  SpecialPeriods.cayley centerOne (RiemannBoundary.principalRoot 3 w)

private def SpecialPeriods.Triangle.cornerParameterFour (w : ℂ) : ℂ :=
  SpecialPeriods.cayley centerTwo (RiemannBoundary.rotatedPrincipalRootFour w)

@[simp]
private theorem
    SpecialPeriods.Triangle.cornerParameterThree_zero : cornerParameterThree 0 = centerOne := by
  simp [cornerParameterThree, RiemannBoundary.principalRoot_zero (by norm_num : 0 < 3)]

@[simp]
private theorem
    SpecialPeriods.Triangle.cornerParameterFour_zero : cornerParameterFour 0 = centerTwo := by
  simp [cornerParameterFour]

private theorem SpecialPeriods.Triangle.continuousAt_cornerParameterThree_zero :
    ContinuousAt cornerParameterThree 0 := by
  have hc : ContinuousAt (SpecialPeriods.cayley (centerOne : ℂ)) 0 :=
    (cayley_analyticAt centerOne (by simp)).continuousAt
  have h0 : RiemannBoundary.principalRoot 3 (0 : ℂ) = 0 :=
    RiemannBoundary.principalRoot_zero (by norm_num)
  exact (h0 ▸ hc).comp (RiemannBoundary.continuousAt_principalRoot_zero (by norm_num : 0 < 3))

private theorem SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero :
    ContinuousAt cornerParameterFour 0 := by
  have hc : ContinuousAt (SpecialPeriods.cayley (centerTwo : ℂ)) 0 :=
    (cayley_analyticAt centerTwo (by simp)).continuousAt
  exact
    (RiemannBoundary.rotatedPrincipalRootFour_zero ▸ hc).comp
      RiemannBoundary.continuousAt_rotatedPrincipalRootFour_zero

private theorem SpecialPeriods.Triangle.cornerParameterThree_im_pos {w : ℂ}
    (hw : ‖RiemannBoundary.principalRoot 3 w‖ < 1) : 0 < (cornerParameterThree w).im :=
  SpecialPeriods.cayley_im_pos centerOne.im_pos hw

private theorem SpecialPeriods.Triangle.cornerParameterFour_im_pos {w : ℂ}
    (hw : ‖RiemannBoundary.rotatedPrincipalRootFour w‖ < 1) : 0 < (cornerParameterFour w).im :=
  SpecialPeriods.cayley_im_pos centerTwo.im_pos hw

private theorem SpecialPeriods.Triangle.cayley_coordinate_inverse (a : UpperHalfPlane) {z : ℂ}
    (hz : ‖z‖ < 1) :
    (SpecialPeriods.cayley a z - a) / (SpecialPeriods.cayley a z - conj (a : ℂ)) = z := by
  have he :=
    congrArg Subtype.val (toDisc_fromDisc a ⟨z, by simpa [SpecialPeriods.unitDisc] using hz⟩)
  simpa only [toDisc_val, cayleyCoordinate, fromDisc_val] using he

private theorem SpecialPeriods.Triangle.cornerParameterThree_power {w : ℂ}
    (hw : ‖RiemannBoundary.principalRoot 3 w‖ < 1) :
    ((cornerParameterThree w - centerOne) / (cornerParameterThree w - conj (centerOne : ℂ))) ^ 3 =
      w := by
  rw [cornerParameterThree, cayley_coordinate_inverse centerOne hw,
    RiemannBoundary.principalRoot_pow (by norm_num : 0 < 3)]

private theorem SpecialPeriods.Triangle.cornerParameterFour_power {w : ℂ}
    (hw : ‖RiemannBoundary.rotatedPrincipalRootFour w‖ < 1) :
    ((cornerParameterFour w - centerTwo) / (cornerParameterFour w - conj (centerTwo : ℂ))) ^ 4 =
      -w := by
  rw [cornerParameterFour, cayley_coordinate_inverse centerTwo hw,
    RiemannBoundary.rotatedPrincipalRootFour_pow]

private theorem SpecialPeriods.Triangle.exists_small_root_ball_mo1973_19462 {f : ℂ → ℂ}
    (hf : ContinuousAt f 0) (hf0 : f 0 = 0) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ Metric.ball (0 : ℂ) δ, ‖f w‖ < r := by
  have hn : ∀ᶠ w in 𝓝 (0 : ℂ), ‖f w‖ < r :=
    hf.norm.eventually_lt continuousAt_const (by simpa only [hf0, norm_zero] using hr)
  exact Metric.mem_nhds_iff.mp hn

private theorem SpecialPeriods.Triangle.cornerParameterThree_analyticOnNhd {U : Set ℂ}
    (hU : ∀ w ∈ U, ‖RiemannBoundary.principalRoot 3 w‖ < 1) :
    AnalyticOnNhd ℂ cornerParameterThree (U ∩ {w : ℂ | 0 < w.im}) := by
  intro w hw
  exact
    (cayley_analyticAt centerOne (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one (hU w hw.1))).comp
      (RiemannBoundary.analyticOnNhd_principalRoot_upper 3 w hw.2)

private theorem SpecialPeriods.Triangle.cornerParameterFour_analyticOnNhd {U : Set ℂ}
    (hU : ∀ w ∈ U, ‖RiemannBoundary.rotatedPrincipalRootFour w‖ < 1) :
    AnalyticOnNhd ℂ cornerParameterFour (U ∩ {w : ℂ | 0 < w.im}) := by
  intro w hw
  exact
    (cayley_analyticAt centerTwo (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one (hU w hw.1))).comp
      (RiemannBoundary.analyticOnNhd_rotatedPrincipalRootFour_upper w hw.2)

private theorem SpecialPeriods.Triangle.cornerParameterThree_continuousOn {U : Set ℂ}
    (hU : ∀ w ∈ U, ‖RiemannBoundary.principalRoot 3 w‖ < 1) :
    ContinuousOn cornerParameterThree (U ∩ {w : ℂ | 0 ≤ w.im}) := by
  have hc := (SpecialPeriods.cayley_contDiffOn (centerOne : ℂ)).continuousOn
  exact
    hc.comp
      ((RiemannBoundary.continuousOn_principalRoot_closedUpper (by norm_num : 0 < 3)).mono
        (fun _ h => h.2))
      (fun w hw => by simpa using hU w hw.1)

private theorem SpecialPeriods.Triangle.cornerParameterFour_continuousOn {U : Set ℂ}
    (hU : ∀ w ∈ U, ‖RiemannBoundary.rotatedPrincipalRootFour w‖ < 1) :
    ContinuousOn cornerParameterFour (U ∩ {w : ℂ | 0 ≤ w.im}) := by
  have hc := (SpecialPeriods.cayley_contDiffOn (centerTwo : ℂ)).continuousOn
  exact
    hc.comp
      (RiemannBoundary.continuousOn_rotatedPrincipalRootFour_closedUpper.mono (fun _ h => h.2))
      (fun w hw => by simpa using hU w hw.1)

private theorem SpecialPeriods.Triangle.exists_cornerParameterThree_neighborhood :
    ∃ δ : ℝ,
      0 < δ ∧
        AnalyticOnNhd ℂ cornerParameterThree (Metric.ball 0 δ ∩ {w : ℂ | 0 < w.im}) ∧
          ContinuousOn cornerParameterThree (Metric.ball 0 δ ∩ {w : ℂ | 0 ≤ w.im}) ∧
            Set.MapsTo cornerParameterThree (Metric.ball 0 δ ∩ {w : ℂ | 0 < w.im})
                triangleInterior ∧
              (∀ t : ℝ,
                  (t : ℂ) ∈ Metric.ball 0 δ → cornerParameterThree (t : ℂ) ∉ triangleInterior) ∧
                (∀ w ∈ Metric.ball 0 δ, 0 < (cornerParameterThree w).im) ∧
                  (∀ w ∈ Metric.ball 0 δ,
                    ((cornerParameterThree w - centerOne) /
                          (cornerParameterThree w - conj (centerOne : ℂ))) ^
                        3 =
                      w) := by
  obtain ⟨r, hr, hr1, hsector⟩ := exists_cornerThree_radius
  obtain ⟨δ, hδ, hδr⟩ :=
    exists_small_root_ball_mo1973_19462
      (RiemannBoundary.continuousAt_principalRoot_zero (by norm_num : 0 < 3))
      (RiemannBoundary.principalRoot_zero (by norm_num : 0 < 3)) hr
  have hδ1 : ∀ w ∈ Metric.ball (0 : ℂ) δ, ‖RiemannBoundary.principalRoot 3 w‖ < 1 := fun w hw =>
    (hδr w hw).trans_le hr1
  refine
    ⟨δ, hδ, cornerParameterThree_analyticOnNhd hδ1, cornerParameterThree_continuousOn hδ1, ?_, ?_,
      ?_, ?_⟩
  · intro w hw
    exact (hsector _ (hδr w hw.1)).mpr (RiemannBoundary.principalRoot_three_upper hw.2)
  · intro t ht hmem
    have hs := (hsector _ (hδr (t : ℂ) ht)).mp hmem
    rcases RiemannBoundary.principalRoot_three_real_boundary (Complex.ofReal_im t) with h | h
    · exact hs.1.ne' h
    · exact hs.2.ne h
  · exact fun w hw => cornerParameterThree_im_pos (hδ1 w hw)
  · exact fun w hw => cornerParameterThree_power (hδ1 w hw)

private theorem SpecialPeriods.Triangle.exists_cornerParameterFour_neighborhood :
    ∃ δ : ℝ,
      0 < δ ∧
        AnalyticOnNhd ℂ cornerParameterFour (Metric.ball 0 δ ∩ {w : ℂ | 0 < w.im}) ∧
          ContinuousOn cornerParameterFour (Metric.ball 0 δ ∩ {w : ℂ | 0 ≤ w.im}) ∧
            Set.MapsTo cornerParameterFour (Metric.ball 0 δ ∩ {w : ℂ | 0 < w.im})
                triangleInterior ∧
              (∀ t : ℝ,
                  (t : ℂ) ∈ Metric.ball 0 δ → cornerParameterFour (t : ℂ) ∉ triangleInterior) ∧
                (∀ w ∈ Metric.ball 0 δ, 0 < (cornerParameterFour w).im) ∧
                  (∀ w ∈ Metric.ball 0 δ,
                    ((cornerParameterFour w - centerTwo) /
                          (cornerParameterFour w - conj (centerTwo : ℂ))) ^
                        4 =
                      -w) := by
  obtain ⟨r, hr, hr1, hsector⟩ := exists_cornerFour_radius
  obtain ⟨δ, hδ, hδr⟩ :=
    exists_small_root_ball_mo1973_19462 RiemannBoundary.continuousAt_rotatedPrincipalRootFour_zero
      RiemannBoundary.rotatedPrincipalRootFour_zero hr
  have hδ1 : ∀ w ∈ Metric.ball (0 : ℂ) δ, ‖RiemannBoundary.rotatedPrincipalRootFour w‖ < 1 :=
    fun w hw => (hδr w hw).trans_le hr1
  refine
    ⟨δ, hδ, cornerParameterFour_analyticOnNhd hδ1, cornerParameterFour_continuousOn hδ1, ?_, ?_,
      ?_, ?_⟩
  · intro w hw
    exact (hsector _ (hδr w hw.1)).mpr (RiemannBoundary.rotatedPrincipalRootFour_upper hw.2)
  · intro t ht hmem
    have hs := (hsector _ (hδr (t : ℂ) ht)).mp hmem
    rcases RiemannBoundary.rotatedPrincipalRootFour_real_boundary (Complex.ofReal_im t) with h | h
    · exact hs.1.ne h
    · exact hs.2.ne' h
  · exact fun w hw => cornerParameterFour_im_pos (hδ1 w hw)
  · exact fun w hw => cornerParameterFour_power (hδ1 w hw)

private theorem RiemannBoundary.norm_lt_one_iff_im_pos_eventually {H k : ℂ → ℂ} {x : ℝ}
    (hH : ContinuousAt H (x : ℂ)) (hcenter : ‖H (x : ℂ)‖ = 1)
    (hk : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → ‖k z‖ < 1) (hu : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → H z = k z)
    (hl : ∀ᶠ z in 𝓝 (x : ℂ), z.im < 0 → H z = (conj (k (conj z)))⁻¹)
    (hr : ∀ᶠ z in 𝓝 (x : ℂ), z.im = 0 → ‖H z‖ = 1) : ∀ᶠ z in 𝓝 (x : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  have hcenter0 : H (x : ℂ) ≠ 0 := by
    intro hzero
    simp [hzero] at hcenter
  have hnz := hH.eventually_ne hcenter0
  have hconj : Filter.Tendsto (conj : ℂ → ℂ) (𝓝 (x : ℂ)) (𝓝 (x : ℂ)) := by
    simpa only [Complex.conj_ofReal] using Complex.continuous_conj.tendsto (x : ℂ)
  have hkc := hconj.eventually hk
  filter_upwards [hk, hu, hl, hr, hnz, hkc] with z hzk hzu hzl hzr hzne hzconj
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · have hw : ‖k (conj z)‖ < 1 := hzconj (by simpa using hneg)
    have hw0 : k (conj z) ≠ 0 := by
      intro heq
      apply hzne
      rw [hzl hneg, heq]
      simp
    have hlarge : 1 < ‖H z‖ := by
      rw [hzl hneg, norm_inv, Complex.norm_conj]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hw0)).mpr hw
    exact iff_of_false (not_lt_of_ge hlarge.le) (not_lt_of_ge hneg.le)
  · rw [hzr hzero]
    simp only [lt_self_iff_false, hzero]
  · rw [hzu hpos]
    exact iff_of_true (hzk hpos) hpos

private theorem
    RiemannBoundary.exists_conformal_extension_of_modulus_one {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} {x : ℝ} (hx : (x : ℂ) ∈ U) (hf : DifferentiableOn ℂ f (U ∩ {z : ℂ | 0 < z.im}))
    (hmod :
      ∀ t : ℝ,
        (t : ℂ) ∈ U → Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1))
    (hdisc : ∀ z ∈ U ∩ {z : ℂ | 0 < z.im}, ‖f z‖ < 1) :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (x : ℂ) r) ∧
          Set.EqOn H f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (f (conj z)))⁻¹)
                (Metric.ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              (∀ t : ℝ, (t : ℂ) ∈ Metric.ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
                HasStrictDerivAt H (deriv H (x : ℂ)) (x : ℂ) ∧
                  deriv H (x : ℂ) ≠ 0 ∧ ∀ᶠ z in 𝓝 (x : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  obtain ⟨r, hr, H, hHa, hHe, hHl, hHc⟩ := exists_analytic_extension_of_modulus_one hU hx hf hmod
  have hHx := hHa (x : ℂ) (Metric.mem_ball_self hr)
  have hcenter := hHc x (Metric.mem_ball_self hr)
  have hk : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → ‖f z‖ < 1 := by
    filter_upwards [hU.mem_nhds hx] with z hz hpos
    exact hdisc z ⟨hz, hpos⟩
  have hu : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → H z = f z := by
    filter_upwards [Metric.ball_mem_nhds (x : ℂ) hr] with z hz hpos
    exact hHe ⟨hz, hpos⟩
  have hl : ∀ᶠ z in 𝓝 (x : ℂ), z.im < 0 → H z = (conj (f (conj z)))⁻¹ := by
    filter_upwards [Metric.ball_mem_nhds (x : ℂ) hr] with z hz hneg
    exact hHl ⟨hz, hneg⟩
  have hreal : ∀ᶠ z in 𝓝 (x : ℂ), z.im = 0 → ‖H z‖ = 1 := by
    filter_upwards [Metric.ball_mem_nhds (x : ℂ) hr] with z hz hzero
    have heq : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using hzero.symm)
    simpa only [heq] using hHc z.re (by simpa only [heq] using hz)
  have hinside : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → ‖H z‖ < 1 := by
    filter_upwards [hu, hk] with z heq hz hpos
    rw [heq hpos]
    exact hz hpos
  have hnonzero :=
    RiemannMapping.deriv_ne_zero_of_upper_halfPlane_to_unitDisc hHx (by simp) hcenter hinside
  exact
    ⟨r, hr, H, hHa, hHe, hHl, hHc, hHx.hasStrictDerivAt, hnonzero,
      norm_lt_one_iff_im_pos_eventually hHx.continuousAt hcenter hk hu hl hreal⟩

private theorem
    RiemannBoundary.exists_conformal_extension_discHomeomorph_in_half_chart {D U : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f φ : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f D) (hφ : DifferentiableOn ℂ φ (U ∩ {z : ℂ | 0 < z.im}))
    (hφc : ContinuousOn φ (U ∩ {z : ℂ | 0 ≤ z.im}))
    (hside : Set.MapsTo φ (U ∩ {z : ℂ | 0 < z.im}) D)
    (hout : ∀ t : ℝ, (t : ℂ) ∈ U → φ (t : ℂ) ∉ D) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (x : ℂ) r) ∧
          Set.EqOn H (f ∘ φ) (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (f (φ (conj z))))⁻¹)
                (Metric.ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              (∀ t : ℝ, (t : ℂ) ∈ Metric.ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
                HasStrictDerivAt H (deriv H (x : ℂ)) (x : ℂ) ∧
                  deriv H (x : ℂ) ≠ 0 ∧ ∀ᶠ z in 𝓝 (x : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  apply exists_conformal_extension_of_modulus_one hU hx (hf.comp hφ hside)
  · intro t ht
    exact tendsto_norm_discHomeomorph_in_boundary_chart e he hU hφc hside ht (hout t ht)
  · intro z hz
    have hp := hside hz
    have hv := he ⟨φ z, hp⟩
    simpa only [Function.comp_def, Metric.mem_ball, dist_zero_right, ← hv] using
      (e ⟨φ z, hp⟩).property

private def RiemannBoundary.discHomeomorphInverse {X : Type*} [TopologicalSpace X] {D : Set X}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (z : ℂ) : X := by
  classical
    exact
    if hz : z ∈ Metric.ball (0 : ℂ) 1 then (e.symm ⟨z, hz⟩ : X) else (e.symm ⟨0, by simp⟩ : X)

private theorem
    RiemannBoundary.discHomeomorphInverse_of_mem {X : Type*} [TopologicalSpace X] {D : Set X}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discHomeomorphInverse e z = (e.symm ⟨z, hz⟩ : X) := by
  simp only [discHomeomorphInverse, dite_eq_left hz]

private theorem RiemannBoundary.tendsto_discHomeomorphInverse_of_boundary_chart {X : Type*}
    [TopologicalSpace X] {D : Set X} (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : X → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) {φ : ℂ → X} {H : ℂ → ℂ} {d : ℂ} (hφ : ContinuousAt φ 0)
    (hH : HasStrictDerivAt H d 0) (hd : d ≠ 0)
    (hcoord : ∀ᶠ z in 𝓝 (0 : ℂ), ‖H z‖ < 1 → φ z ∈ D ∧ f (φ z) = H z) :
    Filter.Tendsto (discHomeomorphInverse e) (𝓝[Metric.ball (0 : ℂ) 1] (H 0)) (𝓝 (φ 0)) := by
  let k := hH.localInverse H d 0 hd
  have hk0 : k (H 0) = 0 := hH.eventually_left_inverse hd |>.self_of_nhds
  have hk : Filter.Tendsto k (𝓝 (H 0)) (𝓝 (0 : ℂ)) := by
    have ht : Filter.Tendsto k (𝓝 (H 0)) (𝓝 (k (H 0))) :=
      (hH.to_localInverse hd).hasDerivAt.continuousAt.tendsto
    rwa [hk0] at ht
  have ht : Filter.Tendsto (φ ∘ k) (𝓝[Metric.ball (0 : ℂ) 1] (H 0)) (𝓝 (φ 0)) :=
    (hφ.tendsto.comp hk).mono_left nhdsWithin_le_nhds
  have heq : discHomeomorphInverse e =ᶠ[𝓝[Metric.ball (0 : ℂ) 1] (H 0)] φ ∘ k := by
    have hright : ∀ᶠ y in 𝓝[Metric.ball (0 : ℂ) 1] (H 0), H (k y) = y :=
      (hH.eventually_right_inverse hd).filter_mono nhdsWithin_le_nhds
    have hparam :
      ∀ᶠ y in 𝓝[Metric.ball (0 : ℂ) 1] (H 0),
        ‖H (k y)‖ < 1 → φ (k y) ∈ D ∧ f (φ (k y)) = H (k y) :=
      (hk.eventually hcoord).filter_mono nhdsWithin_le_nhds
    filter_upwards [hright, hparam, self_mem_nhdsWithin] with y hy hcy hyD
    have hyn : ‖y‖ < 1 := by simpa using hyD
    obtain ⟨hmem, hval⟩ := hcy (by simpa only [hy] using hyn)
    have himage : e ⟨φ (k y), hmem⟩ = ⟨y, hyD⟩ := by
      apply Subtype.ext
      exact (he ⟨φ (k y), hmem⟩).symm.trans (hval.trans hy)
    rw [discHomeomorphInverse_of_mem e hyD]
    change (e.symm ⟨y, hyD⟩ : X) = φ (k y)
    have hinv : e.symm ⟨y, hyD⟩ = ⟨φ (k y), hmem⟩ := by rw [← himage, e.symm_apply_apply]
    exact congrArg Subtype.val hinv
  exact ht.congr' heq.symm

private theorem RiemannBoundary.unitCircle_mem_closure_unitBall {w : ℂ} (hw : ‖w‖ = 1) :
    w ∈ closure (Metric.ball (0 : ℂ) 1) := by
  rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  simpa only [Metric.mem_closedBall, dist_zero_right, hw] using le_rfl (a := (1 : ℝ))

private theorem
    RiemannBoundary.boundary_points_eq_of_equal_disc_values {X : Type*} [TopologicalSpace X]
    {D : Set X} [T2Space X] (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : X → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) {φ ψ : ℂ → X} {F G : ℂ → ℂ} {dF dG : ℂ}
    (hφ : ContinuousAt φ 0) (hψ : ContinuousAt ψ 0) (hF : HasStrictDerivAt F dF 0) (hdF : dF ≠ 0)
    (hG : HasStrictDerivAt G dG 0) (hdG : dG ≠ 0)
    (hcoordF : ∀ᶠ z in 𝓝 (0 : ℂ), ‖F z‖ < 1 → φ z ∈ D ∧ f (φ z) = F z)
    (hcoordG : ∀ᶠ z in 𝓝 (0 : ℂ), ‖G z‖ < 1 → ψ z ∈ D ∧ f (ψ z) = G z) (hcircle : ‖F 0‖ = 1)
    (hvalue : F 0 = G 0) : φ 0 = ψ 0 := by
  have : Filter.NeBot (𝓝[Metric.ball (0 : ℂ) 1] (F 0)) :=
    (mem_closure_iff_nhdsWithin_neBot).mp (unitCircle_mem_closure_unitBall hcircle)
  have htF := tendsto_discHomeomorphInverse_of_boundary_chart e he hφ hF hdF hcoordF
  have htG := tendsto_discHomeomorphInverse_of_boundary_chart e he hψ hG hdG hcoordG
  rw [← hvalue] at htG
  exact tendsto_nhds_unique htF htG

private structure RiemannMapping.TriangleBoundaryGerm (φ : ℂ → ℂ) where
  function : ℂ → ℂ
  radius : ℝ
  radius_pos : 0 < radius
  analytic : AnalyticOnNhd ℂ function (Metric.ball 0 radius)
  agrees : Set.EqOn function (triangleMap ∘ φ) (Metric.ball 0 radius ∩ {z | 0 < z.im})
  unit : ‖function 0‖ = 1
  strictDeriv : HasStrictDerivAt function (deriv function 0) 0
  deriv_ne_zero : deriv function 0 ≠ 0
  sourceCorrespondence :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      ‖function z‖ < 1 →
        φ z ∈ SpecialPeriods.Triangle.triangleInterior ∧ triangleMap (φ z) = function z

private theorem RiemannMapping.exists_triangleBoundaryGerm {φ : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hφ : AnalyticOnNhd ℂ φ (Metric.ball 0 δ ∩ {z | 0 < z.im}))
    (hφc : ContinuousOn φ (Metric.ball 0 δ ∩ {z | 0 ≤ z.im}))
    (hside :
      Set.MapsTo φ (Metric.ball 0 δ ∩ {z | 0 < z.im}) SpecialPeriods.Triangle.triangleInterior)
    (hout :
      ∀ t : ℝ, (t : ℂ) ∈ Metric.ball 0 δ → φ (t : ℂ) ∉ SpecialPeriods.Triangle.triangleInterior) :
    Nonempty (TriangleBoundaryGerm φ) := by
  obtain ⟨r, hr, H, hHa, hHe, _, hHc, hHd, hHn, hHside⟩ :=
    RiemannBoundary.exists_conformal_extension_discHomeomorph_in_half_chart
      triangleBiholomorph.toHomeomorph triangleMap_biholomorph Metric.isOpen_ball
      triangleMap_differentiable hφ.differentiableOn hφc hside hout
      (show ((0 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) δ from Metric.mem_ball_self hδ)
  refine
    ⟨{  function := H
        radius := r
        radius_pos := hr
        analytic := hHa
        agrees := hHe
        unit := hHc 0 (Metric.mem_ball_self hr)
        strictDeriv := hHd
        deriv_ne_zero := hHn
        sourceCorrespondence := ?_ }⟩
  filter_upwards [hHside, Metric.ball_mem_nhds (0 : ℂ) hr, Metric.ball_mem_nhds (0 : ℂ) hδ] with z
    hz hrz hδz hn
  have hi := hz.mp hn
  exact ⟨hside ⟨hδz, hi⟩, (hHe ⟨hrz, hi⟩).symm⟩

private theorem RiemannMapping.exists_triangleCornerThreeGerm :
    Nonempty (TriangleBoundaryGerm SpecialPeriods.Triangle.cornerParameterThree) := by
  obtain ⟨δ, hδ, hφ, hφc, hside, hout, _, _⟩ :=
    SpecialPeriods.Triangle.exists_cornerParameterThree_neighborhood
  exact exists_triangleBoundaryGerm hδ hφ hφc hside hout

private theorem RiemannMapping.exists_triangleCornerFourGerm :
    Nonempty (TriangleBoundaryGerm SpecialPeriods.Triangle.cornerParameterFour) := by
  obtain ⟨δ, hδ, hφ, hφc, hside, hout, _, _⟩ :=
    SpecialPeriods.Triangle.exists_cornerParameterFour_neighborhood
  exact exists_triangleBoundaryGerm hδ hφ hφc hside hout

private def RiemannMapping.triangleCornerThreeGerm :
    TriangleBoundaryGerm SpecialPeriods.Triangle.cornerParameterThree :=
  Classical.choice exists_triangleCornerThreeGerm

private def RiemannMapping.triangleCornerFourGerm :
    TriangleBoundaryGerm SpecialPeriods.Triangle.cornerParameterFour :=
  Classical.choice exists_triangleCornerFourGerm

private theorem RiemannMapping.triangleCornerThree_inverse_limit :
    Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
      (𝓝[Metric.ball (0 : ℂ) 1] (triangleCornerThreeGerm.function 0))
      (𝓝 (SpecialPeriods.Triangle.centerOne : ℂ)) := by
  simpa only [SpecialPeriods.Triangle.cornerParameterThree_zero] using
    RiemannBoundary.tendsto_discHomeomorphInverse_of_boundary_chart
      triangleBiholomorph.toHomeomorph triangleMap_biholomorph
      SpecialPeriods.Triangle.continuousAt_cornerParameterThree_zero
      triangleCornerThreeGerm.strictDeriv triangleCornerThreeGerm.deriv_ne_zero
      triangleCornerThreeGerm.sourceCorrespondence

private theorem RiemannMapping.triangleCornerFour_inverse_limit :
    Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
      (𝓝[Metric.ball (0 : ℂ) 1] (triangleCornerFourGerm.function 0))
      (𝓝 (SpecialPeriods.Triangle.centerTwo : ℂ)) := by
  simpa only [SpecialPeriods.Triangle.cornerParameterFour_zero] using
    RiemannBoundary.tendsto_discHomeomorphInverse_of_boundary_chart
      triangleBiholomorph.toHomeomorph triangleMap_biholomorph
      SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero
      triangleCornerFourGerm.strictDeriv triangleCornerFourGerm.deriv_ne_zero
      triangleCornerFourGerm.sourceCorrespondence

private theorem RiemannMapping.triangle_centers_complex_ne :
    (SpecialPeriods.Triangle.centerOne : ℂ) ≠ (SpecialPeriods.Triangle.centerTwo : ℂ) := by
  intro h
  have hr := congrArg Complex.re h
  change SpecialPeriods.Triangle.centerOne.re = SpecialPeriods.Triangle.centerTwo.re at hr
  rw [SpecialPeriods.Triangle.centerTwo_re] at hr
  have hleft : SpecialPeriods.Triangle.centerOne.re = -1 / 2 := by
    change (SpecialPeriods.rho - 1).re = -1 / 2
    simp only [Complex.sub_re, SpecialPeriods.rho_re, Complex.one_re]
    norm_num
  rw [hleft] at hr
  linarith [SpecialPeriods.Triangle.width_pos]

private theorem RiemannMapping.triangleCorner_boundary_values_ne :
    triangleCornerThreeGerm.function 0 ≠ triangleCornerFourGerm.function 0 := by
  intro h
  have hp :=
    RiemannBoundary.boundary_points_eq_of_equal_disc_values triangleBiholomorph.toHomeomorph
      triangleMap_biholomorph SpecialPeriods.Triangle.continuousAt_cornerParameterThree_zero
      SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero
      triangleCornerThreeGerm.strictDeriv triangleCornerThreeGerm.deriv_ne_zero
      triangleCornerFourGerm.strictDeriv triangleCornerFourGerm.deriv_ne_zero
      triangleCornerThreeGerm.sourceCorrespondence triangleCornerFourGerm.sourceCorrespondence
      triangleCornerThreeGerm.unit h
  exact
    triangle_centers_complex_ne
      (by
        simpa only [SpecialPeriods.Triangle.cornerParameterThree_zero,
          SpecialPeriods.Triangle.cornerParameterFour_zero] using hp)

private theorem RiemannBoundary.continuousWithinAt_log_closedUpper {q : ℂ} (hq : q ≠ 0) :
    ContinuousWithinAt Complex.log {z : ℂ | 0 ≤ z.im} q := by
  by_cases hi : q.im = 0
  · by_cases hr : 0 < q.re
    · exact (continuousAt_clog (Or.inl hr)).continuousWithinAt
    · have hre : q.re < 0 := by
        have hne : q.re ≠ 0 := by
          intro heq
          apply hq
          exact Complex.ext heq hi
        exact lt_of_le_of_ne (le_of_not_gt hr) hne
      exact Complex.continuousWithinAt_log_of_re_neg_of_im_zero hre hi
  · exact (continuousAt_clog (Or.inr hi)).continuousWithinAt

private theorem RiemannBoundary.continuousWithinAt_logHalfStrip_closedUpper (a c : ℝ) {q : ℂ}
    (hq : q ≠ 0) : ContinuousWithinAt (logHalfStrip a c) {z : ℂ | 0 ≤ z.im} q := by
  exact
    continuousWithinAt_const.sub
      (continuousWithinAt_const.mul (continuousWithinAt_log_closedUpper hq))

private theorem RiemannBoundary.analyticOnNhd_logHalfStrip_upper (a c : ℝ) :
    AnalyticOnNhd ℂ (logHalfStrip a c) {z : ℂ | 0 < z.im} := by
  intro q hq
  exact analyticAt_const.sub (analyticAt_const.mul (analyticAt_clog (Or.inr (ne_of_gt hq))))

private theorem RiemannBoundary.logHalfStrip_re_mem_Ioo (a : ℝ) {c : ℝ} (hc : 0 < c) {q : ℂ}
    (hq : 0 < q.im) : (logHalfStrip a c q).re ∈ Set.Ioo a (a + c * Real.pi) := by
  have harg0 : q.arg ≠ 0 := fun h => (ne_of_gt hq) (Complex.arg_eq_zero_iff.mp h).2
  have harg : 0 < q.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hq.le) harg0.symm
  have hargπ : q.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hq))
  rw [logHalfStrip_re]
  constructor <;> nlinarith

private theorem RiemannBoundary.logHalfStrip_real_re (a c : ℝ) (t : ℝ) :
    (logHalfStrip a c (t : ℂ)).re = a ∨ (logHalfStrip a c (t : ℂ)).re = a + c * Real.pi := by
  by_cases ht : 0 ≤ t
  · left
    simp [logHalfStrip_re, Complex.arg_ofReal_of_nonneg ht]
  · right
    simp [logHalfStrip_re, Complex.arg_ofReal_of_neg (lt_of_not_ge ht)]

private theorem RiemannBoundary.exists_logHalfStrip_height_radius (a B : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ R > 0, ∀ q ∈ Metric.ball (0 : ℂ) R, q ≠ 0 → B < (logHalfStrip a c q).im := by
  have ht : ∀ᶠ q in 𝓝[≠] (0 : ℂ), B < (logHalfStrip a c q).im :=
    (tendsto_logHalfStrip_im_atTop a hc).eventually_gt_atTop B
  obtain ⟨R, hR, hs⟩ := Metric.mem_nhdsWithin_iff.mp ht
  exact ⟨R, hR, fun q hq hne => hs ⟨hq, hne⟩⟩

private theorem
    RiemannBoundary.exists_conformal_extension_discHomeomorph_at_ideal_vertex {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ))
    (hf : DifferentiableOn ℂ f D) (a B : ℝ) {c : ℝ} (hc : 0 < c)
    (hstrip : ∀ z : ℂ, a < z.re → z.re < a + c * Real.pi → B < z.im → z ∈ D)
    (hedge : ∀ z : ℂ, B < z.im → (z.re = a ∨ z.re = a + c * Real.pi) → z ∉ D) :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (0 : ℂ) r) ∧
          Set.EqOn H (f ∘ logHalfStrip a c) (Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (f (logHalfStrip a c (conj z))))⁻¹)
                (Metric.ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              (∀ t : ℝ, (t : ℂ) ∈ Metric.ball (0 : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
                HasStrictDerivAt H (deriv H 0) 0 ∧
                  deriv H 0 ≠ 0 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  obtain ⟨R, hR, hheight⟩ := exists_logHalfStrip_height_radius a B hc
  let U : Set ℂ := Metric.ball (0 : ℂ) R
  have hU : IsOpen U := Metric.isOpen_ball
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self hR
  have hside : Set.MapsTo (logHalfStrip a c) (U ∩ {z : ℂ | 0 < z.im}) D := by
    intro q hq
    have hq0 : q ≠ 0 := by
      intro heq
      have hi := hq.2
      rw [heq] at hi
      exact (lt_irrefl (0 : ℝ)) hi
    have hRe := logHalfStrip_re_mem_Ioo a hc hq.2
    exact hstrip _ hRe.1 hRe.2 (hheight q hq.1 hq0)
  have hφ : DifferentiableOn ℂ (logHalfStrip a c) (U ∩ {z : ℂ | 0 < z.im}) :=
    (analyticOnNhd_logHalfStrip_upper a c).differentiableOn.mono Set.inter_subset_right
  have hdiff : DifferentiableOn ℂ (f ∘ logHalfStrip a c) (U ∩ {z : ℂ | 0 < z.im}) :=
    hf.comp hφ hside
  have hmod :
    ∀ t : ℝ,
      (t : ℂ) ∈ U →
        Filter.Tendsto (fun q => ‖f (logHalfStrip a c q)‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ))
          (𝓝 1) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      apply tendsto_norm_discHomeomorph_logHalfStrip e he a hc
      have hnear : U ∈ 𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ) :=
        mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h0U)
      filter_upwards [hnear, self_mem_nhdsWithin] with q hq hi
      exact hside ⟨hq, hi⟩
    · let V : Set ℂ := U \ {0}
      have hV : IsOpen V := hU.sdiff isClosed_singleton
      have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
      have htV : (t : ℂ) ∈ V := ⟨ht, htC⟩
      have hcont : ContinuousOn (logHalfStrip a c) (V ∩ {z : ℂ | 0 ≤ z.im}) := by
        intro q hq
        exact (continuousWithinAt_logHalfStrip_closedUpper a c hq.1.2).mono Set.inter_subset_right
      have hsideV : Set.MapsTo (logHalfStrip a c) (V ∩ {z : ℂ | 0 < z.im}) D := by
        intro q hq
        exact hside ⟨hq.1.1, hq.2⟩
      exact
        tendsto_norm_discHomeomorph_in_boundary_chart e he hV hcont hsideV htV
          (hedge _ (hheight _ ht htC) (logHalfStrip_real_re a c t))
  apply exists_conformal_extension_of_modulus_one hU h0U hdiff hmod
  intro q hq
  have hp := hside hq
  have hv := he ⟨logHalfStrip a c q, hp⟩
  simpa only [Function.comp_def, Metric.mem_ball, dist_zero_right, ← hv] using
    (e ⟨logHalfStrip a c q, hp⟩).property

private def RiemannMapping.triangleCuspScale : ℝ :=
  SpecialPeriods.Triangle.width / (2 * Real.pi)

private theorem RiemannMapping.triangleCuspScale_pos : 0 < triangleCuspScale := by
  exact div_pos SpecialPeriods.Triangle.width_pos (mul_pos (by norm_num) Real.pi_pos)

private theorem RiemannMapping.triangleCuspScale_endpoint :
    SpecialPeriods.Triangle.stripLeft + triangleCuspScale * Real.pi = -1 / 2 := by
  unfold SpecialPeriods.Triangle.stripLeft triangleCuspScale
  field_simp [Real.pi_ne_zero]
  ring

private def RiemannMapping.triangleCuspLog : ℂ → ℂ :=
  RiemannBoundary.logHalfStrip SpecialPeriods.Triangle.stripLeft triangleCuspScale

private theorem RiemannMapping.triangle_high_halfStrip_mem (z : ℂ)
    (hl : SpecialPeriods.Triangle.stripLeft < z.re)
    (hr : z.re < SpecialPeriods.Triangle.stripLeft + triangleCuspScale * Real.pi)
    (hi : 1 < z.im) : z ∈ SpecialPeriods.Triangle.triangleInterior := by
  rw [SpecialPeriods.Triangle.mem_triangleInterior_iff_epigraph]
  exact
    ⟨hl, by simpa only [triangleCuspScale_endpoint] using hr,
      (SpecialPeriods.Triangle.boundaryHeight_le_one z.re).trans_lt hi⟩

private theorem RiemannMapping.triangle_high_halfStrip_edge_notMem (z : ℂ)
    (he :
      z.re = SpecialPeriods.Triangle.stripLeft ∨
        z.re = SpecialPeriods.Triangle.stripLeft + triangleCuspScale * Real.pi) :
    z ∉ SpecialPeriods.Triangle.triangleInterior := by
  intro hz
  rcases he with hl | hr
  · exact (lt_irrefl SpecialPeriods.Triangle.stripLeft) (hl ▸ hz.1)
  · rw [triangleCuspScale_endpoint] at hr
    exact (lt_irrefl (-1 / 2 : ℝ)) (hr ▸ hz.2.1)

private theorem RiemannMapping.exists_triangleMap_extension_ideal_vertex :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (0 : ℂ) r) ∧
          Set.EqOn H (triangleMap ∘ triangleCuspLog)
              (Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (triangleMap (triangleCuspLog (conj z))))⁻¹)
                (Metric.ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              (∀ t : ℝ, (t : ℂ) ∈ Metric.ball (0 : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
                HasStrictDerivAt H (deriv H 0) 0 ∧
                  deriv H 0 ≠ 0 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  exact
    RiemannBoundary.exists_conformal_extension_discHomeomorph_at_ideal_vertex
      triangleBiholomorph.toHomeomorph triangleMap_biholomorph triangleMap_differentiable
      SpecialPeriods.Triangle.stripLeft 1 triangleCuspScale_pos triangle_high_halfStrip_mem
      (fun z _ he => triangle_high_halfStrip_edge_notMem z he)

private theorem RiemannMapping.exists_triangleIdealGerm :
    Nonempty (TriangleBoundaryGerm triangleCuspLog) := by
  obtain ⟨r, hr, H, hHa, hHe, _, hHc, hHd, hHn, hHside⟩ :=
    exists_triangleMap_extension_ideal_vertex
  obtain ⟨R, hR, hheight⟩ :=
    RiemannBoundary.exists_logHalfStrip_height_radius SpecialPeriods.Triangle.stripLeft 1
      triangleCuspScale_pos
  refine
    ⟨{  function := H
        radius := r
        radius_pos := hr
        analytic := hHa
        agrees := hHe
        unit := hHc 0 (Metric.mem_ball_self hr)
        strictDeriv := hHd
        deriv_ne_zero := hHn
        sourceCorrespondence := ?_ }⟩
  filter_upwards [hHside, Metric.ball_mem_nhds (0 : ℂ) hr, Metric.ball_mem_nhds (0 : ℂ) hR] with q
    hq hrq hRq hn
  have hi : 0 < q.im := hq.mp hn
  have hq0 : q ≠ 0 := by
    intro heq
    rw [heq, Complex.zero_im] at hi
    exact (lt_irrefl 0) hi
  have hRe :=
    RiemannBoundary.logHalfStrip_re_mem_Ioo SpecialPeriods.Triangle.stripLeft
      triangleCuspScale_pos hi
  have hD : triangleCuspLog q ∈ SpecialPeriods.Triangle.triangleInterior :=
    triangle_high_halfStrip_mem _ hRe.1 hRe.2 (hheight q hRq hq0)
  exact ⟨hD, (hHe ⟨hrq, hi⟩).symm⟩

private def RiemannMapping.triangleIdealGerm : TriangleBoundaryGerm triangleCuspLog :=
  Classical.choice exists_triangleIdealGerm

private def RiemannMapping.triangleDiscOnOnePointDomain :
    RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior ≃ₜ
      Metric.ball (0 : ℂ) 1 :=
  RiemannBoundary.onePointDomainDiscHomeomorph triangleBiholomorph.toHomeomorph

private def RiemannMapping.triangleOnePointRepresentative (z : OnePoint ℂ) : ℂ :=
  z.elim 0 triangleMap

@[simp]
private theorem RiemannMapping.triangleOnePointRepresentative_coe (z : ℂ) :
    triangleOnePointRepresentative (z : OnePoint ℂ) = triangleMap z :=
  rfl

private theorem RiemannMapping.triangleOnePointRepresentative_homeomorph
    (z : RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior) :
    triangleOnePointRepresentative z = (triangleDiscOnOnePointDomain z : ℂ) :=
  RiemannBoundary.onePointDomainDiscHomeomorph_representative triangleBiholomorph.toHomeomorph
    triangleMap_biholomorph 0 z

private def RiemannMapping.triangleIdealParameter : ℂ → OnePoint ℂ :=
  RiemannBoundary.onePointLogHalfStrip SpecialPeriods.Triangle.stripLeft triangleCuspScale

@[simp]
private theorem RiemannMapping.triangleIdealParameter_zero :
    triangleIdealParameter 0 = (OnePoint.infty) :=
  RiemannBoundary.onePointLogHalfStrip_zero _ _

private theorem RiemannMapping.continuousAt_triangleIdealParameter_zero :
    ContinuousAt triangleIdealParameter 0 :=
  RiemannBoundary.continuousAt_onePointLogHalfStrip_zero SpecialPeriods.Triangle.stripLeft
    triangleCuspScale_pos

private theorem RiemannMapping.triangleIdeal_onePoint_sourceCorrespondence :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      ‖triangleIdealGerm.function z‖ < 1 →
        triangleIdealParameter z ∈
            RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior ∧
          triangleOnePointRepresentative (triangleIdealParameter z) =
            triangleIdealGerm.function z := by
  filter_upwards [triangleIdealGerm.sourceCorrespondence] with z hz hn
  have hzne : z ≠ 0 := by
    intro heq
    rw [heq, triangleIdealGerm.unit] at hn
    exact (lt_irrefl 1) hn
  have hparameter : triangleIdealParameter z = (triangleCuspLog z : OnePoint ℂ) :=
    RiemannBoundary.onePointLogHalfStrip_of_ne_zero SpecialPeriods.Triangle.stripLeft
      triangleCuspScale hzne
  rw [hparameter]
  obtain ⟨hmem, hvalue⟩ := hz hn
  exact ⟨RiemannBoundary.coe_mem_onePointDomain.mpr hmem, hvalue⟩

private theorem RiemannMapping.triangleIdeal_inverse_limit :
    Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleDiscOnOnePointDomain)
      (𝓝[Metric.ball (0 : ℂ) 1] (triangleIdealGerm.function 0))
      (𝓝 ((OnePoint.infty) : OnePoint ℂ)) := by
  simpa only [triangleIdealParameter_zero] using
    RiemannBoundary.tendsto_discHomeomorphInverse_of_boundary_chart triangleDiscOnOnePointDomain
      triangleOnePointRepresentative_homeomorph continuousAt_triangleIdealParameter_zero
      triangleIdealGerm.strictDeriv triangleIdealGerm.deriv_ne_zero
      triangleIdeal_onePoint_sourceCorrespondence

private def RiemannBoundary.discCompactificationMap {X : Type*} [TopologicalSpace X] {D : Set X}
    (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) : X → ℂ :=
  hD.extend (fun z : D => (e z : ℂ))

private theorem
    RiemannBoundary.discCompactificationMap_coe {X : Type*} [TopologicalSpace X] {D : Set X}
    (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (z : D) :
    discCompactificationMap hD e z = (e z : ℂ) :=
  hD.extend_eq (continuous_subtype_val.comp e.continuous) z

private def RiemannBoundary.DiscBoundaryLimits {X : Type*} [TopologicalSpace X] {D : Set X}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) : Prop :=
  ∀ x ∉ D,
    ∃ w : ℂ,
      ‖w‖ = 1 ∧
        Filter.Tendsto (fun z : D => (e z : ℂ)) (Filter.comap Subtype.val (𝓝 x)) (𝓝 w) ∧
          Filter.Tendsto (discHomeomorphInverse e) (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 x)

private theorem RiemannBoundary.discCompactificationMap_continuous {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    Continuous (discCompactificationMap hD e) := by
  apply hD.continuous_extend
  intro x
  by_cases hx : x ∈ D
  · refine ⟨(e ⟨x, hx⟩ : ℂ), ?_⟩
    rw [← hD.isDenseInducing_val.nhds_eq_comap ⟨x, hx⟩]
    exact (continuous_subtype_val.comp e.continuous).continuousAt
  · obtain ⟨w, _, hw, _⟩ := hb x hx
    exact ⟨w, hw⟩

private theorem RiemannBoundary.discCompactificationMap_boundary {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e)
    {x : X} (hx : x ∉ D) :
    ‖discCompactificationMap hD e x‖ = 1 ∧
      Filter.Tendsto (discHomeomorphInverse e)
        (𝓝[Metric.ball (0 : ℂ) 1] (discCompactificationMap hD e x)) (𝓝 x) := by
  obtain ⟨w, hw, ht, hi⟩ := hb x hx
  have he : discCompactificationMap hD e x = w := hD.extend_eq_of_tendsto ht
  rw [he]
  exact ⟨hw, hi⟩

private theorem RiemannBoundary.discCompactificationMap_norm_le {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e)
    (x : X) : ‖discCompactificationMap hD e x‖ ≤ 1 := by
  by_cases hx : x ∈ D
  · rw [discCompactificationMap_coe hD e ⟨x, hx⟩]
    exact
      (show ‖(e ⟨x, hx⟩ : ℂ)‖ < 1 by
          simpa only [Metric.mem_ball, dist_zero_right] using (e ⟨x, hx⟩).property).le
  · exact ((discCompactificationMap_boundary hD e hb hx).1).le

private theorem RiemannBoundary.discCompactificationMap_injective {X : Type*} [TopologicalSpace X]
    {D : Set X} [T2Space X] (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1)
    (hb : DiscBoundaryLimits e) : Function.Injective (discCompactificationMap hD e) := by
  intro x y hxy
  by_cases hx : x ∈ D
  · by_cases hy : y ∈ D
    · apply congrArg Subtype.val (e.injective ?_ : (⟨x, hx⟩ : D) = ⟨y, hy⟩)
      apply Subtype.ext
      simpa only [discCompactificationMap_coe hD e ⟨x, hx⟩,
        discCompactificationMap_coe hD e ⟨y, hy⟩] using hxy
    · have hn := (discCompactificationMap_boundary hD e hb hy).1
      rw [← hxy, discCompactificationMap_coe hD e ⟨x, hx⟩] at hn
      have hlt : ‖(e ⟨x, hx⟩ : ℂ)‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using (e ⟨x, hx⟩).property
      exact (hlt.ne hn).elim
  · by_cases hy : y ∈ D
    · have hn := (discCompactificationMap_boundary hD e hb hx).1
      rw [hxy, discCompactificationMap_coe hD e ⟨y, hy⟩] at hn
      have hlt : ‖(e ⟨y, hy⟩ : ℂ)‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using (e ⟨y, hy⟩).property
      exact (hlt.ne hn).elim
    · obtain ⟨hn, ht⟩ := discCompactificationMap_boundary hD e hb hx
      have hu := (discCompactificationMap_boundary hD e hb hy).2
      rw [← hxy] at hu
      have : Filter.NeBot (𝓝[Metric.ball (0 : ℂ) 1] (discCompactificationMap hD e x)) :=
        mem_closure_iff_nhdsWithin_neBot.mp (unitCircle_mem_closure_unitBall hn)
      exact tendsto_nhds_unique ht hu

private theorem
    RiemannBoundary.discCompactificationMap_range {X : Type*} [TopologicalSpace X] {D : Set X}
    [CompactSpace X] (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    Set.range (discCompactificationMap hD e) = Metric.closedBall (0 : ℂ) 1 := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    simpa using discCompactificationMap_norm_le hD e hb x
  · have hclosed : IsClosed (Set.range (discCompactificationMap hD e)) :=
      (isCompact_range (discCompactificationMap_continuous hD e hb)).isClosed
    have hdisc : Metric.ball (0 : ℂ) 1 ⊆ Set.range (discCompactificationMap hD e) := by
      intro y hy
      refine ⟨(e.symm ⟨y, hy⟩ : X), ?_⟩
      rw [discCompactificationMap_coe, e.apply_symm_apply]
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact closure_minimal hdisc hclosed

private def
    RiemannBoundary.closedDiscHomeomorph {X : Type*} [TopologicalSpace X] {D : Set X} [T2Space X]
    [CompactSpace X] (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    X ≃ₜ Metric.closedBall (0 : ℂ) 1 := by
  let F : X → Metric.closedBall (0 : ℂ) 1 := fun x =>
    ⟨discCompactificationMap hD e x, by simpa using discCompactificationMap_norm_le hD e hb x⟩
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      exact discCompactificationMap_injective hD e hb (congrArg Subtype.val hxy)
    · intro y
      have hy : (y : ℂ) ∈ Set.range (discCompactificationMap hD e) := by
        rw [discCompactificationMap_range hD e hb]
        exact y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  exact
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hF)
      ((discCompactificationMap_continuous hD e hb).subtype_mk _)

private theorem
    RiemannBoundary.closedDiscHomeomorph_coe {X : Type*} [TopologicalSpace X] {D : Set X}
    [T2Space X] [CompactSpace X] (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1)
    (hb : DiscBoundaryLimits e) (z : D) : (closedDiscHomeomorph hD e hb z : ℂ) = (e z : ℂ) :=
  discCompactificationMap_coe hD e z

private def SpecialPeriods.Triangle.triangleClosedInteriorToOnePoint :
    triangleClosedInterior ≃ₜ RiemannBoundary.onePointDomain triangleInterior
    where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, subset_closure x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem SpecialPeriods.Triangle.triangleClosedInterior_comap_onePoint_filter
    (x : TriangleClosedDomain) :
    Filter.comap triangleClosedInteriorToOnePoint
        (Filter.comap (Subtype.val : RiemannBoundary.onePointDomain triangleInterior → OnePoint ℂ)
          (𝓝 x.val)) =
      Filter.comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x) := by
  rw [nhds_subtype_eq_comap, Filter.comap_comap, Filter.comap_comap]
  rfl

private theorem SpecialPeriods.Triangle.triangleClosedInterior_map_onePoint_filter
    (x : TriangleClosedDomain) :
    Filter.map triangleClosedInteriorToOnePoint
        (Filter.comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x)) =
      Filter.comap (Subtype.val : RiemannBoundary.onePointDomain triangleInterior → OnePoint ℂ)
        (𝓝 x.val) := by
  rw [← triangleClosedInterior_comap_onePoint_filter x,
    Filter.map_comap_of_surjective triangleClosedInteriorToOnePoint.surjective]

private theorem SpecialPeriods.Triangle.triangleClosedInterior_forward_tendsto_iff
    (x : TriangleClosedDomain) {l : Filter ℂ} :
    Filter.Tendsto
        (fun z : triangleClosedInterior => (triangleClosedInteriorDiscHomeomorph z : ℂ))
        (Filter.comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x)) l ↔
      Filter.Tendsto
        (fun z : RiemannBoundary.onePointDomain triangleInterior =>
          (RiemannMapping.triangleDiscOnOnePointDomain z : ℂ))
        (Filter.comap (Subtype.val : RiemannBoundary.onePointDomain triangleInterior → OnePoint ℂ)
          (𝓝 x.val))
        l := by
  rw [← triangleClosedInterior_map_onePoint_filter x, Filter.tendsto_map'_iff]
  rfl

private theorem SpecialPeriods.Triangle.triangleClosedInterior_forward_representative_tendsto_iff
    (x : TriangleClosedDomain) {l : Filter ℂ} :
    Filter.Tendsto
        (fun z : triangleClosedInterior => (triangleClosedInteriorDiscHomeomorph z : ℂ))
        (Filter.comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x)) l ↔
      Filter.Tendsto RiemannMapping.triangleOnePointRepresentative
        (𝓝[RiemannBoundary.onePointDomain triangleInterior] x.val) l := by
  rw [triangleClosedInterior_forward_tendsto_iff]
  have he :
    (fun z : RiemannBoundary.onePointDomain triangleInterior =>
        (RiemannMapping.triangleDiscOnOnePointDomain z : ℂ)) =
      RiemannMapping.triangleOnePointRepresentative ∘
        (Subtype.val : RiemannBoundary.onePointDomain triangleInterior → OnePoint ℂ) := by
    funext z
    exact (RiemannMapping.triangleOnePointRepresentative_homeomorph z).symm
  rw [he, ← Filter.tendsto_map'_iff, Filter.map_comap_setCoe_val]
  rfl

private theorem SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph_inverse_coe (z : ℂ) :
    ((RiemannBoundary.discHomeomorphInverse triangleClosedInteriorDiscHomeomorph z :
          TriangleClosedDomain) :
        OnePoint ℂ) =
      RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleDiscOnOnePointDomain z := by
  classical
  unfold RiemannBoundary.discHomeomorphInverse
  split_ifs <;> rfl

private theorem SpecialPeriods.Triangle.triangleClosedInterior_inverse_tendsto_iff
    (x : TriangleClosedDomain) {l : Filter ℂ} :
    Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleClosedInteriorDiscHomeomorph) l
        (𝓝 x) ↔
      Filter.Tendsto
        (RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleDiscOnOnePointDomain) l
        (𝓝 x.val) := by
  rw [tendsto_subtype_rng]
  simp only [triangleClosedInteriorDiscHomeomorph_inverse_coe]

private theorem SpecialPeriods.Triangle.triangleOnePointRepresentative_finite_tendsto_iff {a : ℂ}
    {l : Filter ℂ} :
    Filter.Tendsto RiemannMapping.triangleOnePointRepresentative
        (𝓝[RiemannBoundary.onePointDomain triangleInterior] (a : OnePoint ℂ)) l ↔
      Filter.Tendsto RiemannMapping.triangleMap (𝓝[triangleInterior] a) l := by
  change
    Filter.Tendsto RiemannMapping.triangleOnePointRepresentative
        (𝓝[((↑) : ℂ → OnePoint ℂ) '' triangleInterior] (a : OnePoint ℂ)) l ↔
      _
  rw [OnePoint.nhdsWithin_coe_image, Filter.tendsto_map'_iff]
  rfl

private theorem SpecialPeriods.Triangle.triangleDiscOnOnePointDomain_inverse_coe (z : ℂ) :
    RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleDiscOnOnePointDomain z =
      ((RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleBiholomorph.toHomeomorph z :
          ℂ) :
        OnePoint ℂ) := by
  classical
  unfold RiemannBoundary.discHomeomorphInverse
  split_ifs <;> rfl

private theorem
    SpecialPeriods.Triangle.triangleDiscOnOnePointDomain_finite_inverse_tendsto_iff {a : ℂ}
    {l : Filter ℂ} :
    Filter.Tendsto
        (RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleDiscOnOnePointDomain) l
        (𝓝 (a : OnePoint ℂ)) ↔
      Filter.Tendsto
        (RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleBiholomorph.toHomeomorph) l
        (𝓝 a) := by
  have h :=
    (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding.tendsto_nhds_iff (f :=
      RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleBiholomorph.toHomeomorph) (l :=
      l) (y := a)
  simpa only [Function.comp_def, ← triangleDiscOnOnePointDomain_inverse_coe] using h.symm

private def RiemannMapping.triangleSideParameter (e : OpenPartialHomeomorph ℂ ℂ) (a w : ℂ) : ℂ :=
  e.symm (w + e a)

private theorem RiemannMapping.triangleSideParameter_zero (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) : triangleSideParameter e a 0 = a := by
  simp only [triangleSideParameter, zero_add, e.left_inv ha]

private theorem
    RiemannMapping.continuousAt_triangleSideParameter_zero (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) : ContinuousAt (triangleSideParameter e a) 0 := by
  have hi := e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (e.map_source ha))
  exact
    ContinuousAt.comp (g := e.symm) (f := fun w : ℂ => w + e a) (x := 0)
      (by simpa only [zero_add] using hi) (continuousAt_id.add_const (e a))

private theorem
    RiemannMapping.exists_triangleSideBoundaryGerm (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) (he : AnalyticOnNhd ℂ e.symm e.target) (hreal : (e a).im = 0) {r : ℝ}
    (hr : 0 < r)
    (hside : ∀ z ∈ Metric.ball a r, z ∈ SpecialPeriods.Triangle.triangleInterior ↔ 0 < (e z).im) :
    Nonempty (TriangleBoundaryGerm (triangleSideParameter e a)) := by
  obtain ⟨δ, hδ, hδball⟩ := exists_boundary_chart_target_ball e ha hr
  have hadd : ∀ w ∈ Metric.ball (0 : ℂ) δ, w + e a ∈ Metric.ball (e a) δ := by
    intro w hw
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hw
  have hφ : AnalyticOnNhd ℂ (triangleSideParameter e a) (Metric.ball 0 δ) := by
    intro w hw
    exact
      (he (w + e a) (hδball _ (hadd w hw)).1).comp (f := fun z : ℂ => z + e a)
        (analyticAt_id.add analyticAt_const)
  apply
    exists_triangleBoundaryGerm hδ (hφ.mono Set.inter_subset_left)
      (hφ.continuousOn.mono Set.inter_subset_left)
  · intro w hw
    apply (hside _ (hδball _ (hadd w hw.1)).2).mpr
    rw [e.right_inv (hδball _ (hadd w hw.1)).1, Complex.add_im, hreal, add_zero]
    exact hw.2
  · intro t ht hin
    have hi := (hside _ (hδball _ (hadd t ht)).2).mp hin
    change 0 < (e (e.symm ((t : ℂ) + e a))).im at hi
    rw [e.right_inv (hδball _ (hadd t ht)).1, Complex.add_im, Complex.ofReal_im, hreal,
      add_zero] at hi
    exact lt_irrefl _ hi

private theorem
    RiemannMapping.triangleSideBoundaryGerm_forward_limit (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) (hreal : (e a).im = 0) {r : ℝ} (hr : 0 < r)
    (hside : ∀ z ∈ Metric.ball a r, z ∈ SpecialPeriods.Triangle.triangleInterior ↔ 0 < (e z).im)
    (g : TriangleBoundaryGerm (triangleSideParameter e a)) :
    Filter.Tendsto triangleMap (𝓝[SpecialPeriods.Triangle.triangleInterior] a)
      (𝓝 (g.function 0)) := by
  have hec : ContinuousAt e a := e.continuousOn.continuousAt (e.open_source.mem_nhds ha)
  have ht : Filter.Tendsto (fun z => e z - e a) (𝓝 a) (𝓝 (0 : ℂ)) := by
    have hsub : Filter.Tendsto (fun z => e z - e a) (𝓝 a) (𝓝 (e a - e a)) :=
      hec.tendsto.sub_const (e a)
    simpa only [sub_self] using hsub
  have hlim :
    Filter.Tendsto (fun z => g.function (e z - e a))
      (𝓝[SpecialPeriods.Triangle.triangleInterior] a) (𝓝 (g.function 0)) :=
    ((g.analytic 0 (Metric.mem_ball_self g.radius_pos)).continuousAt.tendsto.comp ht).mono_left
      nhdsWithin_le_nhds
  have heq :
    triangleMap =ᶠ[𝓝[SpecialPeriods.Triangle.triangleInterior] a]
      (fun z => g.function (e z - e a)) := by
    have hs : ∀ᶠ z in 𝓝[SpecialPeriods.Triangle.triangleInterior] a, z ∈ e.source :=
      mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds ha)
    have hb : ∀ᶠ z in 𝓝[SpecialPeriods.Triangle.triangleInterior] a, z ∈ Metric.ball a r :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds a hr)
    have hp :
      ∀ᶠ z in 𝓝[SpecialPeriods.Triangle.triangleInterior] a,
        e z - e a ∈ Metric.ball (0 : ℂ) g.radius :=
      (ht.eventually (Metric.ball_mem_nhds (0 : ℂ) g.radius_pos)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hs, hb, hp, self_mem_nhdsWithin] with z hz hbz hpz hzT
    have hi : 0 < (e z - e a).im := by
      rw [Complex.sub_im, hreal, sub_zero]
      exact (hside z hbz).mp hzT
    have hg := g.agrees ⟨hpz, hi⟩
    simpa only [Function.comp_apply, triangleSideParameter, sub_add_cancel, e.left_inv hz] using
      hg.symm
  exact hlim.congr' heq.symm

private theorem
    RiemannMapping.triangleSideBoundaryGerm_inverse_limit (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) (g : TriangleBoundaryGerm (triangleSideParameter e a)) :
    Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
      (𝓝[Metric.ball (0 : ℂ) 1] (g.function 0)) (𝓝 a) := by
  simpa only [triangleSideParameter_zero e ha] using
    RiemannBoundary.tendsto_discHomeomorphInverse_of_boundary_chart
      triangleBiholomorph.toHomeomorph triangleMap_biholomorph
      (continuousAt_triangleSideParameter_zero e ha) g.strictDeriv g.deriv_ne_zero
      g.sourceCorrespondence

private theorem
    RiemannMapping.exists_triangleMap_side_limits (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) (he : AnalyticOnNhd ℂ e.symm e.target) (hreal : (e a).im = 0) {r : ℝ}
    (hr : 0 < r)
    (hside : ∀ z ∈ Metric.ball a r, z ∈ SpecialPeriods.Triangle.triangleInterior ↔ 0 < (e z).im) :
    ∃ w : ℂ,
      ‖w‖ = 1 ∧
        Filter.Tendsto triangleMap (𝓝[SpecialPeriods.Triangle.triangleInterior] a) (𝓝 w) ∧
          Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
            (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 a) := by
  obtain ⟨g⟩ := exists_triangleSideBoundaryGerm e ha he hreal hr hside
  exact
    ⟨g.function 0, g.unit, triangleSideBoundaryGerm_forward_limit e ha hreal hr hside g,
      triangleSideBoundaryGerm_inverse_limit e ha g⟩

private theorem RiemannMapping.exists_triangleMap_circle_side_limits {a : ℂ}
    (haL : SpecialPeriods.Triangle.stripLeft < a.re) (haR : a.re < -1 / 2) (hai : 0 < a.im)
    (haC : ‖a + 1‖ = 1) :
    ∃ w : ℂ,
      ‖w‖ = 1 ∧
        Filter.Tendsto triangleMap (𝓝[SpecialPeriods.Triangle.triangleInterior] a) (𝓝 w) ∧
          Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
            (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 a) := by
  obtain ⟨r, hr, hside⟩ := SpecialPeriods.Triangle.exists_circle_side_neighborhood haL haR hai
  have ha : a ∈ SpecialPeriods.Triangle.circleBoundaryChart.source :=
    (hside a (Metric.mem_ball_self hr)).1
  exact
    exists_triangleMap_side_limits SpecialPeriods.Triangle.circleBoundaryChart ha
      SpecialPeriods.Triangle.circleUnstraighten_analyticOnNhd
      ((SpecialPeriods.Triangle.circleStraighten_im_eq_zero_iff ha).mpr haC) hr
      (fun z hz => (hside z hz).2)

private theorem RiemannMapping.exists_triangleMap_left_side_limits {a : ℂ}
    (ha : a.re = SpecialPeriods.Triangle.stripLeft) (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ w : ℂ,
      ‖w‖ = 1 ∧
        Filter.Tendsto triangleMap (𝓝[SpecialPeriods.Triangle.triangleInterior] a) (𝓝 w) ∧
          Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
            (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 a) := by
  obtain ⟨r, hr, hside⟩ := SpecialPeriods.Triangle.exists_left_side_neighborhood ha hai haC
  apply
    exists_triangleMap_side_limits
      SpecialPeriods.Triangle.leftBoundaryChart.toOpenPartialHomeomorph (Set.mem_univ a)
      (fun z _ => SpecialPeriods.Triangle.leftBoundaryChart_symm_analyticAt z)
  · change (SpecialPeriods.Triangle.leftBoundaryChart a).im = 0
    simp [ha]
  · exact hr
  · exact hside

private theorem RiemannMapping.exists_triangleMap_right_side_limits {a : ℂ} (ha : a.re = -1 / 2)
    (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ w : ℂ,
      ‖w‖ = 1 ∧
        Filter.Tendsto triangleMap (𝓝[SpecialPeriods.Triangle.triangleInterior] a) (𝓝 w) ∧
          Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
            (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 a) := by
  obtain ⟨r, hr, hside⟩ := SpecialPeriods.Triangle.exists_right_side_neighborhood ha hai haC
  apply
    exists_triangleMap_side_limits
      SpecialPeriods.Triangle.rightBoundaryChart.toOpenPartialHomeomorph (Set.mem_univ a)
      (fun z _ => SpecialPeriods.Triangle.rightBoundaryChart_symm_analyticAt z)
  · change (SpecialPeriods.Triangle.rightBoundaryChart a).im = 0
    norm_num [SpecialPeriods.Triangle.rightBoundaryChart_im, ha]
  · exact hr
  · exact hside

private def SpecialPeriods.Triangle.cornerCoordinate (a : UpperHalfPlane) (z : ℂ) : ℂ :=
  (z - a) / (z - conj (a : ℂ))

@[simp]
private theorem SpecialPeriods.Triangle.cornerCoordinate_self (a : UpperHalfPlane) :
    cornerCoordinate a a = 0 := by simp [cornerCoordinate]

private theorem SpecialPeriods.Triangle.cornerCoordinate_analyticAt (a : UpperHalfPlane) {z : ℂ}
    (hz : z - conj (a : ℂ) ≠ 0) : AnalyticAt ℂ (cornerCoordinate a) z :=
  (analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) hz

private theorem SpecialPeriods.Triangle.cornerCoordinate_analyticAt_self (a : UpperHalfPlane) :
    AnalyticAt ℂ (cornerCoordinate a) (a : ℂ) :=
  cornerCoordinate_analyticAt a (sub_conj_ne_zero a a)

private theorem SpecialPeriods.Triangle.cayley_cornerCoordinate (a : UpperHalfPlane) {z : ℂ}
    (hz : 0 < z.im) : SpecialPeriods.cayley a (cornerCoordinate a z) = z := by
  have he := congrArg (fun w : UpperHalfPlane => (w : ℂ)) (fromDisc_toDisc a ⟨z, hz⟩)
  simpa only [fromDisc_val, toDisc_val, cornerCoordinate, cayleyCoordinate] using he

private def SpecialPeriods.Triangle.cornerPowerThree (z : ℂ) : ℂ :=
  cornerCoordinate centerOne z ^ 3

private def SpecialPeriods.Triangle.cornerPowerFour (z : ℂ) : ℂ :=
  -(cornerCoordinate centerTwo z ^ 4)

private theorem
    SpecialPeriods.Triangle.cornerPowerThree_center : cornerPowerThree centerOne = 0 := by
  simp only [cornerPowerThree, cornerCoordinate_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true]

private theorem SpecialPeriods.Triangle.cornerPowerFour_center : cornerPowerFour centerTwo = 0 := by
  simp only [cornerPowerFour, cornerCoordinate_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, neg_zero]

private theorem SpecialPeriods.Triangle.cornerPowerThree_analyticAt_center :
    AnalyticAt ℂ cornerPowerThree (centerOne : ℂ) :=
  (cornerCoordinate_analyticAt_self centerOne).pow 3

private theorem SpecialPeriods.Triangle.cornerPowerFour_analyticAt_center :
    AnalyticAt ℂ cornerPowerFour (centerTwo : ℂ) :=
  ((cornerCoordinate_analyticAt_self centerTwo).pow 4).neg

private theorem
    SpecialPeriods.Triangle.exists_cornerCoordinate_neighborhood (a : UpperHalfPlane) {r : ℝ}
    (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Metric.ball (a : ℂ) ε, 0 < z.im ∧ ‖cornerCoordinate a z‖ < r := by
  have him : ∀ᶠ z : ℂ in 𝓝 (a : ℂ), 0 < z.im :=
    continuousAt_const.eventually_lt Complex.continuous_im.continuousAt a.im_pos
  have hnorm : ∀ᶠ z : ℂ in 𝓝 (a : ℂ), ‖cornerCoordinate a z‖ < r :=
    (cornerCoordinate_analyticAt_self a).continuousAt.norm.eventually_lt continuousAt_const
      (by simpa only [cornerCoordinate_self, norm_zero] using hr)
  exact Metric.mem_nhds_iff.mp (him.and hnorm)

private theorem SpecialPeriods.Triangle.exists_cornerThree_neighborhood :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ z ∈ Metric.ball (centerOne : ℂ) ε,
          0 < z.im ∧ (z ∈ triangleInterior ↔ cornerCoordinate centerOne z ∈ cornerSectorThree) := by
  obtain ⟨r, hr, _, hsector⟩ := exists_cornerThree_radius
  obtain ⟨ε, hε, hball⟩ := exists_cornerCoordinate_neighborhood centerOne hr
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have h := hball z hz
  refine ⟨h.1, ?_⟩
  have he := hsector _ h.2
  rwa [cayley_cornerCoordinate centerOne h.1] at he

private theorem SpecialPeriods.Triangle.exists_cornerFour_neighborhood :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ z ∈ Metric.ball (centerTwo : ℂ) ε,
          0 < z.im ∧ (z ∈ triangleInterior ↔ cornerCoordinate centerTwo z ∈ cornerSectorFour) := by
  obtain ⟨r, hr, _, hsector⟩ := exists_cornerFour_radius
  obtain ⟨ε, hε, hball⟩ := exists_cornerCoordinate_neighborhood centerTwo hr
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have h := hball z hz
  refine ⟨h.1, ?_⟩
  have he := hsector _ h.2
  rwa [cayley_cornerCoordinate centerTwo h.1] at he

private theorem
    SpecialPeriods.Triangle.cornerSectorThree_re_pos {z : ℂ} (hz : z ∈ cornerSectorThree) :
    0 < z.re := by
  change 0 < z.im ∧ Real.sqrt 3 * z.im < 3 * z.re at hz
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [mul_pos hsqrt hz.1]

private theorem SpecialPeriods.Triangle.cornerSectorThree_arg {z : ℂ} (hz : z ∈ cornerSectorThree) :
    z.arg ∈ Set.Ioo 0 (Real.pi / 3) := by
  have hr := cornerSectorThree_re_pos hz
  change 0 < z.im ∧ Real.sqrt 3 * z.im < 3 * z.re at hz
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hm : Real.sqrt 3 * z.im < Real.sqrt 3 * (Real.sqrt 3 * z.re) := by
    rw [← mul_assoc, hsq]
    exact hz.2
  have him : z.im < Real.sqrt 3 * z.re := (mul_lt_mul_iff_right₀ hsqrt).mp hm
  have hargHalf : z.arg ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr))
  have hthird : Real.pi / 3 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have htan : Real.tan z.arg < Real.tan (Real.pi / 3) := by
    rw [Complex.tan_arg, Real.tan_pi_div_three]
    exact (div_lt_iff₀ hr).mpr him
  have harg0 : 0 < z.arg := by
    have hn : z.arg ≠ 0 := fun h => (ne_of_gt hz.1) (Complex.arg_eq_zero_iff.mp h).2
    exact lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.1.le) hn.symm
  exact ⟨harg0, (Real.strictMonoOn_tan.lt_iff_lt hargHalf hthird).mp htan⟩

private theorem
    SpecialPeriods.Triangle.cornerSectorThree_root_pow {z : ℂ} (hz : z ∈ cornerSectorThree) :
    RiemannBoundary.principalRoot 3 (z ^ 3) = z := by
  apply RiemannBoundary.principalRoot_pow_of_sector (by norm_num : 0 < 3)
  exact ⟨(cornerSectorThree_arg hz).1.le, (cornerSectorThree_arg hz).2.le⟩

private theorem SpecialPeriods.Triangle.im_pos_of_principalRoot_arg_mo1973_19574 {n : ℕ}
    (hn : 0 < n) {z : ℂ}
    (ha : (RiemannBoundary.principalRoot n z).arg ∈ Set.Ioo 0 (Real.pi / (n : ℝ))) : 0 < z.im := by
  rw [RiemannBoundary.arg_principalRoot hn] at ha
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have harg0 : 0 < z.arg := (div_pos_iff_of_pos_right hnR).mp ha.1
  have hargPi : z.arg < Real.pi := (div_lt_div_iff_of_pos_right hnR).mp ha.2
  have hz0 : z ≠ 0 := by
    intro hz
    simp only [hz, Complex.arg_zero, lt_self_iff_false] at harg0
  rw [← Complex.norm_mul_sin_arg]
  exact mul_pos (norm_pos_iff.mpr hz0) (Real.sin_pos_of_pos_of_lt_pi harg0 hargPi)

private theorem SpecialPeriods.Triangle.cornerSectorThree_pow_im_pos {z : ℂ}
    (hz : z ∈ cornerSectorThree) : 0 < (z ^ 3).im := by
  apply im_pos_of_principalRoot_arg_mo1973_19574 (by norm_num : 0 < 3)
  rw [cornerSectorThree_root_pow hz]
  exact cornerSectorThree_arg hz

private theorem
    SpecialPeriods.Triangle.cornerSectorFour_re_pos {z : ℂ} (hz : z ∈ cornerSectorFour) :
    0 < z.re := by
  change z.im < 0 ∧ 0 < z.re + z.im at hz
  linarith [hz.1, hz.2]

private theorem SpecialPeriods.Triangle.cornerSectorFour_arg {z : ℂ} (hz : z ∈ cornerSectorFour) :
    z.arg ∈ Set.Ioo (-Real.pi / 4) 0 := by
  have hr := cornerSectorFour_re_pos hz
  change z.im < 0 ∧ 0 < z.re + z.im at hz
  have hargHalf : z.arg ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr))
  have hfourth : -Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have htan : Real.tan (-Real.pi / 4) < Real.tan z.arg := by
    rw [neg_div, Real.tan_neg, Real.tan_pi_div_four, Complex.tan_arg]
    apply (lt_div_iff₀ hr).mpr
    linarith [hz.2]
  exact ⟨(Real.strictMonoOn_tan.lt_iff_lt hfourth hargHalf).mp htan, Complex.arg_neg_iff.mpr hz.1⟩

private theorem SpecialPeriods.Triangle.quarticRootRotation_arg :
    RiemannBoundary.quarticRootRotation.arg = -Real.pi / 4 := by
  rw [RiemannBoundary.quarticRootRotation, Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  constructor <;> linarith [Real.pi_pos]

private theorem SpecialPeriods.Triangle.quarticRootRotation_inv_arg :
    (RiemannBoundary.quarticRootRotation⁻¹).arg = Real.pi / 4 := by
  rw [Complex.arg_inv, quarticRootRotation_arg]
  have hn : -Real.pi / 4 ≠ Real.pi := by linarith [Real.pi_pos]
  rw [ite_eq_right hn]
  ring

private theorem SpecialPeriods.Triangle.cornerSectorFour_unrotate_arg {z : ℂ}
    (hz : z ∈ cornerSectorFour) :
    (RiemannBoundary.quarticRootRotation⁻¹ * z).arg ∈ Set.Ioo 0 (Real.pi / 4) := by
  have ha := cornerSectorFour_arg hz
  have hz0 : z ≠ 0 := by
    intro h
    have hi := hz.1
    simp only [h, Complex.zero_im, lt_self_iff_false] at hi
  have hsum : (RiemannBoundary.quarticRootRotation⁻¹).arg + z.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [quarticRootRotation_inv_arg]
    constructor <;> linarith [ha.1, ha.2, Real.pi_pos]
  rw [Complex.arg_mul (inv_ne_zero RiemannBoundary.quarticRootRotation_ne_zero) hz0 hsum,
    quarticRootRotation_inv_arg]
  constructor <;> linarith [ha.1, ha.2]

private theorem SpecialPeriods.Triangle.quarticRootRotation_inv_mul_pow_four (z : ℂ) :
    (RiemannBoundary.quarticRootRotation⁻¹ * z) ^ 4 = -(z ^ 4) := by
  rw [mul_pow, inv_pow, RiemannBoundary.quarticRootRotation_pow_four]
  norm_num

private theorem SpecialPeriods.Triangle.cornerSectorFour_unrotate_root_pow {z : ℂ}
    (hz : z ∈ cornerSectorFour) :
    RiemannBoundary.principalRoot 4 (-(z ^ 4)) = RiemannBoundary.quarticRootRotation⁻¹ * z := by
  rw [← quarticRootRotation_inv_mul_pow_four]
  apply RiemannBoundary.principalRoot_pow_of_sector (by norm_num : 0 < 4)
  exact ⟨(cornerSectorFour_unrotate_arg hz).1.le, (cornerSectorFour_unrotate_arg hz).2.le⟩

private theorem
    SpecialPeriods.Triangle.cornerSectorFour_root_pow {z : ℂ} (hz : z ∈ cornerSectorFour) :
    RiemannBoundary.rotatedPrincipalRootFour (-(z ^ 4)) = z := by
  rw [RiemannBoundary.rotatedPrincipalRootFour, cornerSectorFour_unrotate_root_pow hz, ←
    mul_assoc, mul_inv_cancel₀ RiemannBoundary.quarticRootRotation_ne_zero, one_mul]

private theorem
    SpecialPeriods.Triangle.cornerSectorFour_pow_im_pos {z : ℂ} (hz : z ∈ cornerSectorFour) :
    0 < (-(z ^ 4)).im := by
  apply im_pos_of_principalRoot_arg_mo1973_19574 (by norm_num : 0 < 4)
  rw [cornerSectorFour_unrotate_root_pow hz]
  exact cornerSectorFour_unrotate_arg hz

private theorem SpecialPeriods.Triangle.cornerParameterThree_cornerPower {z : ℂ} (hzi : 0 < z.im)
    (hz : cornerCoordinate centerOne z ∈ cornerSectorThree) :
    cornerParameterThree (cornerPowerThree z) = z := by
  change
    SpecialPeriods.cayley centerOne
        (RiemannBoundary.principalRoot 3 (cornerCoordinate centerOne z ^ 3)) =
      z
  rw [cornerSectorThree_root_pow hz, cayley_cornerCoordinate centerOne hzi]

private theorem SpecialPeriods.Triangle.cornerParameterFour_cornerPower {z : ℂ} (hzi : 0 < z.im)
    (hz : cornerCoordinate centerTwo z ∈ cornerSectorFour) :
    cornerParameterFour (cornerPowerFour z) = z := by
  change
    SpecialPeriods.cayley centerTwo
        (RiemannBoundary.rotatedPrincipalRootFour (-(cornerCoordinate centerTwo z ^ 4))) =
      z
  rw [cornerSectorFour_root_pow hz, cayley_cornerCoordinate centerTwo hzi]

private theorem SpecialPeriods.Triangle.exists_cornerParameterThree_coverage {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ z ∈ Metric.ball (centerOne : ℂ) ε,
          z ∈ triangleInterior →
            cornerPowerThree z ∈ Metric.ball 0 δ ∩ {w : ℂ | 0 < w.im} ∧
              cornerParameterThree (cornerPowerThree z) = z := by
  obtain ⟨r, hr, hgeom⟩ := exists_cornerThree_neighborhood
  have hp : ∀ᶠ z : ℂ in 𝓝 (centerOne : ℂ), ‖cornerPowerThree z‖ < δ :=
    cornerPowerThree_analyticAt_center.continuousAt.norm.eventually_lt continuousAt_const
      (by simpa only [cornerPowerThree_center, norm_zero] using hδ)
  have hb : ∀ᶠ z : ℂ in 𝓝 (centerOne : ℂ), z ∈ Metric.ball (centerOne : ℂ) r :=
    Metric.ball_mem_nhds (centerOne : ℂ) hr
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hb.and hp)
  refine ⟨ε, hε, ?_⟩
  intro z hz hT
  have hnear := hball hz
  have h := hgeom z hnear.1
  have hs := h.2.mp hT
  refine
    ⟨⟨by simpa only [Metric.mem_ball, dist_zero_right] using hnear.2, ?_⟩,
      cornerParameterThree_cornerPower h.1 hs⟩
  exact cornerSectorThree_pow_im_pos hs

private theorem SpecialPeriods.Triangle.exists_cornerParameterFour_coverage {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ z ∈ Metric.ball (centerTwo : ℂ) ε,
          z ∈ triangleInterior →
            cornerPowerFour z ∈ Metric.ball 0 δ ∩ {w : ℂ | 0 < w.im} ∧
              cornerParameterFour (cornerPowerFour z) = z := by
  obtain ⟨r, hr, hgeom⟩ := exists_cornerFour_neighborhood
  have hp : ∀ᶠ z : ℂ in 𝓝 (centerTwo : ℂ), ‖cornerPowerFour z‖ < δ :=
    cornerPowerFour_analyticAt_center.continuousAt.norm.eventually_lt continuousAt_const
      (by simpa only [cornerPowerFour_center, norm_zero] using hδ)
  have hb : ∀ᶠ z : ℂ in 𝓝 (centerTwo : ℂ), z ∈ Metric.ball (centerTwo : ℂ) r :=
    Metric.ball_mem_nhds (centerTwo : ℂ) hr
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hb.and hp)
  refine ⟨ε, hε, ?_⟩
  intro z hz hT
  have hnear := hball hz
  have h := hgeom z hnear.1
  have hs := h.2.mp hT
  refine
    ⟨⟨by simpa only [Metric.mem_ball, dist_zero_right] using hnear.2, ?_⟩,
      cornerParameterFour_cornerPower h.1 hs⟩
  exact cornerSectorFour_pow_im_pos hs

private def RiemannMapping.triangleCornerThreePatch : ℂ → ℂ :=
  triangleCornerThreeGerm.function ∘ SpecialPeriods.Triangle.cornerPowerThree

private def RiemannMapping.triangleCornerFourPatch : ℂ → ℂ :=
  triangleCornerFourGerm.function ∘ SpecialPeriods.Triangle.cornerPowerFour

private theorem RiemannMapping.triangleCornerThreePatch_center :
    triangleCornerThreePatch SpecialPeriods.Triangle.centerOne =
      triangleCornerThreeGerm.function 0 := by
  simp only [triangleCornerThreePatch, Function.comp_apply,
    SpecialPeriods.Triangle.cornerPowerThree_center]

private theorem RiemannMapping.triangleCornerFourPatch_center :
    triangleCornerFourPatch SpecialPeriods.Triangle.centerTwo =
      triangleCornerFourGerm.function 0 := by
  simp only [triangleCornerFourPatch, Function.comp_apply,
    SpecialPeriods.Triangle.cornerPowerFour_center]

private theorem RiemannMapping.triangleCornerThreePatch_analyticAt :
    AnalyticAt ℂ triangleCornerThreePatch (SpecialPeriods.Triangle.centerOne : ℂ) := by
  have hH :
    AnalyticAt ℂ triangleCornerThreeGerm.function
      (SpecialPeriods.Triangle.cornerPowerThree SpecialPeriods.Triangle.centerOne) := by
    rw [SpecialPeriods.Triangle.cornerPowerThree_center]
    exact
      triangleCornerThreeGerm.analytic 0 (Metric.mem_ball_self triangleCornerThreeGerm.radius_pos)
  exact hH.comp SpecialPeriods.Triangle.cornerPowerThree_analyticAt_center

private theorem RiemannMapping.triangleCornerFourPatch_analyticAt :
    AnalyticAt ℂ triangleCornerFourPatch (SpecialPeriods.Triangle.centerTwo : ℂ) := by
  have hH :
    AnalyticAt ℂ triangleCornerFourGerm.function
      (SpecialPeriods.Triangle.cornerPowerFour SpecialPeriods.Triangle.centerTwo) := by
    rw [SpecialPeriods.Triangle.cornerPowerFour_center]
    exact
      triangleCornerFourGerm.analytic 0 (Metric.mem_ball_self triangleCornerFourGerm.radius_pos)
  exact hH.comp SpecialPeriods.Triangle.cornerPowerFour_analyticAt_center

private theorem RiemannMapping.exists_triangleCornerThreePatch_agrees :
    ∃ ε : ℝ,
      0 < ε ∧
        Set.EqOn triangleCornerThreePatch triangleMap
          (Metric.ball (SpecialPeriods.Triangle.centerOne : ℂ) ε ∩
            SpecialPeriods.Triangle.triangleInterior) := by
  obtain ⟨ε, hε, hcover⟩ :=
    SpecialPeriods.Triangle.exists_cornerParameterThree_coverage
      triangleCornerThreeGerm.radius_pos
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have hc := hcover z hz.1 hz.2
  have he := triangleCornerThreeGerm.agrees hc.1
  change
    triangleCornerThreeGerm.function (SpecialPeriods.Triangle.cornerPowerThree z) = triangleMap z
  simpa only [Function.comp_apply, hc.2] using he

private theorem RiemannMapping.exists_triangleCornerFourPatch_agrees :
    ∃ ε : ℝ,
      0 < ε ∧
        Set.EqOn triangleCornerFourPatch triangleMap
          (Metric.ball (SpecialPeriods.Triangle.centerTwo : ℂ) ε ∩
            SpecialPeriods.Triangle.triangleInterior) := by
  obtain ⟨ε, hε, hcover⟩ :=
    SpecialPeriods.Triangle.exists_cornerParameterFour_coverage triangleCornerFourGerm.radius_pos
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have hc := hcover z hz.1 hz.2
  have he := triangleCornerFourGerm.agrees hc.1
  change
    triangleCornerFourGerm.function (SpecialPeriods.Triangle.cornerPowerFour z) = triangleMap z
  simpa only [Function.comp_apply, hc.2] using he

private theorem RiemannMapping.triangleCornerThreePatch_eventuallyEq :
    triangleCornerThreePatch =ᶠ[𝓝[SpecialPeriods.Triangle.triangleInterior]
        (SpecialPeriods.Triangle.centerOne : ℂ)]
      triangleMap := by
  obtain ⟨ε, hε, he⟩ := exists_triangleCornerThreePatch_agrees
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds (SpecialPeriods.Triangle.centerOne : ℂ) hε)] with
    z hz hb
  exact he ⟨hb, hz⟩

private theorem RiemannMapping.triangleCornerFourPatch_eventuallyEq :
    triangleCornerFourPatch =ᶠ[𝓝[SpecialPeriods.Triangle.triangleInterior]
        (SpecialPeriods.Triangle.centerTwo : ℂ)]
      triangleMap := by
  obtain ⟨ε, hε, he⟩ := exists_triangleCornerFourPatch_agrees
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds (SpecialPeriods.Triangle.centerTwo : ℂ) hε)] with
    z hz hb
  exact he ⟨hb, hz⟩

private theorem RiemannMapping.triangleCornerThree_forward_limit :
    Filter.Tendsto triangleMap
      (𝓝[SpecialPeriods.Triangle.triangleInterior] (SpecialPeriods.Triangle.centerOne : ℂ))
      (𝓝 (triangleCornerThreeGerm.function 0)) := by
  have h :
    Filter.Tendsto triangleCornerThreePatch
      (𝓝[SpecialPeriods.Triangle.triangleInterior] (SpecialPeriods.Triangle.centerOne : ℂ))
      (𝓝 (triangleCornerThreePatch SpecialPeriods.Triangle.centerOne)) :=
    triangleCornerThreePatch_analyticAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [triangleCornerThreePatch_center] at h
  exact h.congr' triangleCornerThreePatch_eventuallyEq

private theorem RiemannMapping.triangleCornerFour_forward_limit :
    Filter.Tendsto triangleMap
      (𝓝[SpecialPeriods.Triangle.triangleInterior] (SpecialPeriods.Triangle.centerTwo : ℂ))
      (𝓝 (triangleCornerFourGerm.function 0)) := by
  have h :
    Filter.Tendsto triangleCornerFourPatch
      (𝓝[SpecialPeriods.Triangle.triangleInterior] (SpecialPeriods.Triangle.centerTwo : ℂ))
      (𝓝 (triangleCornerFourPatch SpecialPeriods.Triangle.centerTwo)) :=
    triangleCornerFourPatch_analyticAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [triangleCornerFourPatch_center] at h
  exact h.congr' triangleCornerFourPatch_eventuallyEq

private def RiemannBoundary.halfStripExp (a c : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (z - a) / c)

private theorem RiemannBoundary.logHalfStrip_halfStripExp (a : ℝ) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z.re ∈ Set.Ioo a (a + c * Real.pi)) : logHalfStrip a c (halfStripExp a c z) = z := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have him : (Complex.I * (z - a) / c).im = (z.re - a) / c := by simp
  have hpos : 0 < (Complex.I * (z - a) / c).im := by
    rw [him]
    exact div_pos (sub_pos.mpr hz.1) hc
  have hpi : (Complex.I * (z - a) / c).im < Real.pi := by
    rw [him, div_lt_iff₀ hc]
    linarith [hz.2]
  rw [logHalfStrip, halfStripExp, Complex.log_exp (by linarith [Real.pi_pos]) hpi.le]
  field_simp
  ring_nf
  simp

@[simp]
private theorem RiemannBoundary.norm_halfStripExp (a c : ℝ) (z : ℂ) :
    ‖halfStripExp a c z‖ = Real.exp (-z.im / c) := by simp [halfStripExp, Complex.norm_exp]

private theorem RiemannBoundary.halfStripExp_im_pos (a : ℝ) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z.re ∈ Set.Ioo a (a + c * Real.pi)) : 0 < (halfStripExp a c z).im := by
  rw [halfStripExp, Complex.exp_im]
  apply mul_pos (Real.exp_pos _)
  apply Real.sin_pos_of_pos_of_lt_pi
  · simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.I_re, Complex.sub_im,
      Complex.ofReal_im, MulZeroClass.zero_mul, Complex.I_im, Complex.sub_re, Complex.ofReal_re,
      one_mul, zero_add]
    exact div_pos (sub_pos.mpr hz.1) hc
  · simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.I_re, Complex.sub_im,
      Complex.ofReal_im, MulZeroClass.zero_mul, Complex.I_im, Complex.sub_re, Complex.ofReal_re,
      one_mul, zero_add]
    rw [div_lt_iff₀ hc]
    linarith [hz.2]

private def RiemannMapping.triangleCuspExp : ℂ → ℂ :=
  RiemannBoundary.halfStripExp SpecialPeriods.Triangle.stripLeft triangleCuspScale

@[simp]
private theorem RiemannMapping.norm_triangleCuspExp (z : ℂ) :
    ‖triangleCuspExp z‖ = Real.exp (-z.im / triangleCuspScale) :=
  RiemannBoundary.norm_halfStripExp _ _ _

private theorem RiemannMapping.triangleCuspExp_im_pos {z : ℂ}
    (hz : z ∈ SpecialPeriods.Triangle.triangleInterior) : 0 < (triangleCuspExp z).im := by
  apply
    RiemannBoundary.halfStripExp_im_pos SpecialPeriods.Triangle.stripLeft triangleCuspScale_pos
  exact ⟨hz.1, by simpa only [triangleCuspScale_endpoint] using hz.2.1⟩

private theorem RiemannMapping.triangleCuspLog_triangleCuspExp {z : ℂ}
    (hz : z ∈ SpecialPeriods.Triangle.triangleInterior) :
    triangleCuspLog (triangleCuspExp z) = z := by
  apply
    RiemannBoundary.logHalfStrip_halfStripExp SpecialPeriods.Triangle.stripLeft
      triangleCuspScale_pos
  exact ⟨hz.1, by simpa only [triangleCuspScale_endpoint] using hz.2.1⟩

private def RiemannMapping.triangleInfinityFilter : Filter ℂ :=
  Filter.cocompact ℂ ⊓ 𝓟 SpecialPeriods.Triangle.triangleInterior

private theorem RiemannMapping.triangleInfinity_eventually_mem :
    ∀ᶠ z in triangleInfinityFilter, z ∈ SpecialPeriods.Triangle.triangleInterior :=
  (show
        ∀ᶠ z in 𝓟 SpecialPeriods.Triangle.triangleInterior,
          z ∈ SpecialPeriods.Triangle.triangleInterior
        by simp).filter_mono
    inf_le_right

private theorem RiemannMapping.triangle_norm_add_stripLeft_le_im {z : ℂ}
    (hz : z ∈ SpecialPeriods.Triangle.triangleInterior) :
    ‖z‖ + SpecialPeriods.Triangle.stripLeft ≤ z.im := by
  have hre : z.re < 0 := hz.2.1.trans (by norm_num)
  have hnorm := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_neg hre, abs_of_pos hz.2.2.1] at hnorm
  linarith [hz.1]

private theorem RiemannMapping.tendsto_im_triangleInfinity :
    Filter.Tendsto (fun z : ℂ => z.im) triangleInfinityFilter Filter.atTop := by
  have hn : Filter.Tendsto (fun z : ℂ => ‖z‖) triangleInfinityFilter Filter.atTop :=
    tendsto_norm_cocompact_atTop.mono_left inf_le_left
  have hshift :
    Filter.Tendsto (fun z : ℂ => ‖z‖ + SpecialPeriods.Triangle.stripLeft) triangleInfinityFilter
      Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ SpecialPeriods.Triangle.stripLeft hn
  apply Filter.tendsto_atTop_mono' triangleInfinityFilter _ hshift
  filter_upwards [triangleInfinity_eventually_mem] with z hz
  exact triangle_norm_add_stripLeft_le_im hz

private theorem RiemannMapping.tendsto_triangleCuspExp_triangleInfinity :
    Filter.Tendsto triangleCuspExp triangleInfinityFilter (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_triangleCuspExp]
  apply Real.tendsto_exp_atBot.comp
  have ht :=
    Filter.tendsto_neg_atTop_atBot.comp
      (tendsto_im_triangleInfinity.atTop_div_const triangleCuspScale_pos)
  simpa only [Function.comp_def, neg_div] using ht

private theorem RiemannMapping.triangleMap_eq_ideal_cusp_of_param_mem {z : ℂ}
    (hz : z ∈ SpecialPeriods.Triangle.triangleInterior)
    (hq : triangleCuspExp z ∈ Metric.ball (0 : ℂ) triangleIdealGerm.radius) :
    triangleMap z = triangleIdealGerm.function (triangleCuspExp z) := by
  have he := triangleIdealGerm.agrees ⟨hq, triangleCuspExp_im_pos hz⟩
  simpa only [Function.comp_def, triangleCuspLog_triangleCuspExp hz] using he.symm

private theorem RiemannMapping.triangleMap_eventually_eq_ideal_cusp :
    triangleMap =ᶠ[triangleInfinityFilter]
      (fun z => triangleIdealGerm.function (triangleCuspExp z)) := by
  have hsmall :=
    tendsto_triangleCuspExp_triangleInfinity.eventually
      (Metric.ball_mem_nhds (0 : ℂ) triangleIdealGerm.radius_pos)
  filter_upwards [triangleInfinity_eventually_mem, hsmall] with z hz hq
  exact triangleMap_eq_ideal_cusp_of_param_mem hz hq

private theorem RiemannMapping.triangleIdeal_forward_limit :
    Filter.Tendsto triangleMap triangleInfinityFilter (𝓝 (triangleIdealGerm.function 0)) := by
  have hc :=
    (triangleIdealGerm.analytic 0
        (Metric.mem_ball_self triangleIdealGerm.radius_pos)).continuousAt
  exact
    (hc.tendsto.comp tendsto_triangleCuspExp_triangleInfinity).congr'
      triangleMap_eventually_eq_ideal_cusp.symm

private theorem RiemannMapping.comap_coe_triangle_onePoint_nhds_infty :
    Filter.comap ((↑) : ℂ → OnePoint ℂ)
        (𝓝[RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior]
          ((OnePoint.infty) : OnePoint ℂ)) =
      triangleInfinityFilter := by
  have hp :
    ((↑) : ℂ → OnePoint ℂ) ⁻¹'
        RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior =
      SpecialPeriods.Triangle.triangleInterior :=
    Set.ext fun _ => RiemannBoundary.coe_mem_onePointDomain
  rw [nhdsWithin, Filter.comap_inf, OnePoint.comap_coe_nhds_infty,
    Filter.coclosedCompact_eq_cocompact, Filter.comap_principal, hp]
  rfl

private theorem RiemannMapping.triangleIdeal_forward_limit_onePoint :
    Filter.Tendsto triangleOnePointRepresentative
      (𝓝[RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior]
        ((OnePoint.infty) : OnePoint ℂ))
      (𝓝 (triangleIdealGerm.function 0)) := by
  have hRange :
    Set.range ((↑) : ℂ → OnePoint ℂ) ∈
      𝓝[RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior]
        ((OnePoint.infty) : OnePoint ℂ) := by
    apply Filter.mem_of_superset self_mem_nhdsWithin
    rintro _ ⟨z, _, rfl⟩
    exact Set.mem_range_self z
  apply (Filter.tendsto_comap'_iff (i := ((↑) : ℂ → OnePoint ℂ)) hRange).mp
  simpa only [Function.comp_def, triangleOnePointRepresentative_coe,
    comap_coe_triangle_onePoint_nhds_infty] using triangleIdeal_forward_limit

private theorem RiemannMapping.triangleClosed_finite_forward_limit
    (x : SpecialPeriods.Triangle.TriangleClosedDomain) {a w : ℂ} (hxa : x.val = (a : OnePoint ℂ))
    (hf : Filter.Tendsto triangleMap (𝓝[SpecialPeriods.Triangle.triangleInterior] a) (𝓝 w)) :
    Filter.Tendsto
      (fun z : SpecialPeriods.Triangle.triangleClosedInterior =>
        (SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph z : ℂ))
      (Filter.comap
        (Subtype.val :
          SpecialPeriods.Triangle.triangleClosedInterior →
            SpecialPeriods.Triangle.TriangleClosedDomain)
        (𝓝 x))
      (𝓝 w) := by
  apply (SpecialPeriods.Triangle.triangleClosedInterior_forward_representative_tendsto_iff x).mpr
  rw [hxa]
  exact SpecialPeriods.Triangle.triangleOnePointRepresentative_finite_tendsto_iff.mpr hf

private theorem RiemannMapping.triangleClosed_finite_inverse_limit
    (x : SpecialPeriods.Triangle.TriangleClosedDomain) {a w : ℂ} (hxa : x.val = (a : OnePoint ℂ))
    (hi :
      Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
        (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 a)) :
    Filter.Tendsto
      (RiemannBoundary.discHomeomorphInverse
        SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph)
      (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 x) := by
  apply (SpecialPeriods.Triangle.triangleClosedInterior_inverse_tendsto_iff x).mpr
  rw [hxa]
  exact SpecialPeriods.Triangle.triangleDiscOnOnePointDomain_finite_inverse_tendsto_iff.mpr hi

private theorem RiemannMapping.triangleClosedDiscBoundaryLimits :
    RiemannBoundary.DiscBoundaryLimits
      SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph := by
  intro x hx
  rcases SpecialPeriods.Triangle.triangleClosedBoundary_cases x hx with rfl | ⟨a, ha, hxa⟩ |
    ⟨a, ha, hxa⟩ | ⟨a, ha, hxa⟩ | rfl | rfl
  · exact
      ⟨triangleIdealGerm.function 0, triangleIdealGerm.unit,
        (SpecialPeriods.Triangle.triangleClosedInterior_forward_representative_tendsto_iff _).mpr
          triangleIdeal_forward_limit_onePoint,
        (SpecialPeriods.Triangle.triangleClosedInterior_inverse_tendsto_iff _).mpr
          triangleIdeal_inverse_limit⟩
  · obtain ⟨w, hw, hf, hi⟩ := exists_triangleMap_left_side_limits ha.1 ha.2.1 ha.2.2
    exact
      ⟨w, hw, triangleClosed_finite_forward_limit x hxa hf,
        triangleClosed_finite_inverse_limit x hxa hi⟩
  · obtain ⟨w, hw, hf, hi⟩ := exists_triangleMap_right_side_limits ha.1 ha.2.1 ha.2.2
    exact
      ⟨w, hw, triangleClosed_finite_forward_limit x hxa hf,
        triangleClosed_finite_inverse_limit x hxa hi⟩
  · obtain ⟨w, hw, hf, hi⟩ := exists_triangleMap_circle_side_limits ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
    exact
      ⟨w, hw, triangleClosed_finite_forward_limit x hxa hf,
        triangleClosed_finite_inverse_limit x hxa hi⟩
  · exact
      ⟨triangleCornerThreeGerm.function 0, triangleCornerThreeGerm.unit,
        triangleClosed_finite_forward_limit _ rfl triangleCornerThree_forward_limit,
        triangleClosed_finite_inverse_limit _ rfl triangleCornerThree_inverse_limit⟩
  · exact
      ⟨triangleCornerFourGerm.function 0, triangleCornerFourGerm.unit,
        triangleClosed_finite_forward_limit _ rfl triangleCornerFour_forward_limit,
        triangleClosed_finite_inverse_limit _ rfl triangleCornerFour_inverse_limit⟩

private def RiemannMapping.triangleClosedDiscHomeomorph :
    SpecialPeriods.Triangle.TriangleClosedDomain ≃ₜ Metric.closedBall (0 : ℂ) 1 :=
  RiemannBoundary.closedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedInterior_dense
    SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph triangleClosedDiscBoundaryLimits

private theorem RiemannMapping.triangleClosedDiscHomeomorph_interior
    (z : SpecialPeriods.Triangle.triangleClosedInterior) :
    (triangleClosedDiscHomeomorph z : ℂ) =
      (SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph z : ℂ) :=
  RiemannBoundary.closedDiscHomeomorph_coe SpecialPeriods.Triangle.triangleClosedInterior_dense
    SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph triangleClosedDiscBoundaryLimits
    z

private theorem RiemannMapping.triangleClosedDiscHomeomorph_triangle (z : triangleDomain) :
    (triangleClosedDiscHomeomorph (SpecialPeriods.Triangle.triangleClosedInclusion z) : ℂ) =
      triangleMap z := by
  rw [triangleMap_biholomorph z]
  exact
    (triangleClosedDiscHomeomorph_interior
          (SpecialPeriods.Triangle.triangleClosedInteriorHomeomorph z)).trans
      (congrArg (fun w : Metric.ball (0 : ℂ) 1 => (w : ℂ))
        (SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph_apply z))

private theorem RiemannMapping.triangleClosedDiscHomeomorph_boundary
    {x : SpecialPeriods.Triangle.TriangleClosedDomain}
    (hx : x ∉ SpecialPeriods.Triangle.triangleClosedInterior) :
    ‖(triangleClosedDiscHomeomorph x : ℂ)‖ = 1 :=
  (RiemannBoundary.discCompactificationMap_boundary
      SpecialPeriods.Triangle.triangleClosedInterior_dense
      SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph
      triangleClosedDiscBoundaryLimits hx).1

private theorem RiemannMapping.triangleClosedDiscHomeomorph_norm_lt_iff
    (x : SpecialPeriods.Triangle.TriangleClosedDomain) :
    ‖(triangleClosedDiscHomeomorph x : ℂ)‖ < 1 ↔
      x ∈ SpecialPeriods.Triangle.triangleClosedInterior := by
  constructor
  · intro h
    by_contra hx
    rw [triangleClosedDiscHomeomorph_boundary hx] at h
    exact lt_irrefl _ h
  · intro hx
    rw [triangleClosedDiscHomeomorph_interior
        (⟨x, hx⟩ : SpecialPeriods.Triangle.triangleClosedInterior)]
    simpa only [Metric.mem_ball, dist_zero_right] using
      (SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph ⟨x, hx⟩).property

@[simp]
private theorem RiemannMapping.triangleClosedDiscHomeomorph_centerOne :
    (triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedCenterOne : ℂ) =
      triangleCornerThreeGerm.function 0 := by
  change
    RiemannBoundary.discCompactificationMap SpecialPeriods.Triangle.triangleClosedInterior_dense
        SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph
        SpecialPeriods.Triangle.triangleClosedCenterOne =
      _
  exact
    SpecialPeriods.Triangle.triangleClosedInterior_dense.extend_eq_of_tendsto
      (triangleClosed_finite_forward_limit _ rfl triangleCornerThree_forward_limit)

@[simp]
private theorem RiemannMapping.triangleClosedDiscHomeomorph_centerTwo :
    (triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedCenterTwo : ℂ) =
      triangleCornerFourGerm.function 0 := by
  change
    RiemannBoundary.discCompactificationMap SpecialPeriods.Triangle.triangleClosedInterior_dense
        SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph
        SpecialPeriods.Triangle.triangleClosedCenterTwo =
      _
  exact
    SpecialPeriods.Triangle.triangleClosedInterior_dense.extend_eq_of_tendsto
      (triangleClosed_finite_forward_limit _ rfl triangleCornerFour_forward_limit)

@[simp]
private theorem RiemannMapping.triangleClosedDiscHomeomorph_infty :
    (triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedInfinity : ℂ) =
      triangleIdealGerm.function 0 := by
  change
    RiemannBoundary.discCompactificationMap SpecialPeriods.Triangle.triangleClosedInterior_dense
        SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph
        SpecialPeriods.Triangle.triangleClosedInfinity =
      _
  exact
    SpecialPeriods.Triangle.triangleClosedInterior_dense.extend_eq_of_tendsto
      ((SpecialPeriods.Triangle.triangleClosedInterior_forward_representative_tendsto_iff _).mpr
        triangleIdeal_forward_limit_onePoint)

private theorem RiemannMapping.triangleClosedDiscHomeomorph_norm_centerOne :
    ‖(triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedCenterOne : ℂ)‖ = 1 := by
  rw [triangleClosedDiscHomeomorph_centerOne]
  exact triangleCornerThreeGerm.unit

private theorem RiemannMapping.triangleClosedDiscHomeomorph_norm_centerTwo :
    ‖(triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedCenterTwo : ℂ)‖ = 1 := by
  rw [triangleClosedDiscHomeomorph_centerTwo]
  exact triangleCornerFourGerm.unit

private theorem RiemannMapping.triangleClosedDiscHomeomorph_norm_infty :
    ‖(triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedInfinity : ℂ)‖ = 1 := by
  rw [triangleClosedDiscHomeomorph_infty]
  exact triangleIdealGerm.unit

private abbrev SpecialPeriods.Triangle.TriangleClosedFinite :=
  { x : TriangleClosedDomain // x ≠ triangleClosedInfinity }

private theorem SpecialPeriods.Triangle.coe_mem_triangleClosedSet_iff_halfFordRegion (z : ℍ) :
    ((z : ℂ) : OnePoint ℂ) ∈ triangleClosedSet ↔ z ∈ halfFordRegion := by
  rw [coe_mem_triangleClosedSet_iff_closure, closure_triangleInterior]
  exact coe_mem_triangleClosedRegion_iff_halfFordRegion z

private def
    SpecialPeriods.Triangle.halfFordToClosedDomain (z : halfFordRegion) : TriangleClosedDomain :=
  ⟨((z : ℍ) : ℂ), (coe_mem_triangleClosedSet_iff_halfFordRegion z).mpr z.property⟩

private theorem SpecialPeriods.Triangle.halfFordToClosedDomain_ne_infinity (z : halfFordRegion) :
    halfFordToClosedDomain z ≠ triangleClosedInfinity := by
  intro h
  exact OnePoint.coe_ne_infty ((z : ℍ) : ℂ) (congrArg Subtype.val h)

private def
    SpecialPeriods.Triangle.halfFordToClosedFinite (z : halfFordRegion) : TriangleClosedFinite :=
  ⟨halfFordToClosedDomain z, halfFordToClosedDomain_ne_infinity z⟩

private theorem SpecialPeriods.Triangle.halfFordToClosedFinite_isEmbedding :
    Topology.IsEmbedding halfFordToClosedFinite := by
  have htarget : Topology.IsEmbedding (fun x : TriangleClosedFinite => x.val.val) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  apply htarget.of_comp_iff.mp
  exact
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp
      (UpperHalfPlane.isEmbedding_coe.comp Topology.IsEmbedding.subtypeVal)

private theorem SpecialPeriods.Triangle.halfFordToClosedFinite_surjective :
    Function.Surjective halfFordToClosedFinite := by
  intro x
  have hx : x.val.val ≠ ((OnePoint.infty) : OnePoint ℂ) := by
    intro h
    exact x.property (Subtype.ext h)
  obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hx
  have hmem : (z : OnePoint ℂ) ∈ triangleClosedSet := by
    rw [hz]
    exact x.val.property
  have him : 0 < z.im := ((coe_mem_triangleClosedSet_iff z).mp hmem).2.2.1
  let w : ℍ := ⟨z, him⟩
  have hw : w ∈ halfFordRegion := (coe_mem_triangleClosedSet_iff_halfFordRegion w).mp hmem
  exact ⟨⟨w, hw⟩, Subtype.ext (Subtype.ext hz)⟩

private def
    SpecialPeriods.Triangle.halfFordClosedHomeomorph : halfFordRegion ≃ₜ TriangleClosedFinite :=
  halfFordToClosedFinite_isEmbedding.toHomeomorphOfSurjective halfFordToClosedFinite_surjective

private theorem
    SpecialPeriods.Triangle.halfFordClosedHomeomorph_mem_interior_iff (z : halfFordRegion) :
    (halfFordClosedHomeomorph z).val ∈ triangleClosedInterior ↔ (z : ℍ) ∈ halfFordInterior := by
  change (((z : ℍ) : ℂ) : OnePoint ℂ) ∈ RiemannBoundary.onePointDomain triangleInterior ↔ _
  rw [RiemannBoundary.coe_mem_onePointDomain, halfFordInterior_eq_preimage_triangleInterior]
  rfl

private theorem SpecialPeriods.Triangle.halfFordClosedHomeomorph_of_interior (z : ℍ)
    (hz : z ∈ halfFordInterior) :
    (halfFordClosedHomeomorph ⟨z, halfFordInterior_subset_halfFordRegion hz⟩).val =
      triangleClosedInclusion
        (⟨(z : ℂ), by
            change (z : ℂ) ∈ triangleInterior
            simpa only [halfFordInterior_eq_preimage_triangleInterior, Set.mem_preimage] using
              hz⟩ :
          RiemannMapping.triangleDomain) :=
  rfl

private theorem SpecialPeriods.Triangle.centerOne_mem_halfFordRegion : centerOne ∈ halfFordRegion :=
  (coe_mem_triangleClosedSet_iff_halfFordRegion centerOne).mp triangleClosedCenterOne.property

private theorem SpecialPeriods.Triangle.centerTwo_mem_halfFordRegion : centerTwo ∈ halfFordRegion :=
  (coe_mem_triangleClosedSet_iff_halfFordRegion centerTwo).mp triangleClosedCenterTwo.property

private def RiemannMapping.normalizationZeroValue : ℂ :=
  triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedCenterOne

private def RiemannMapping.normalizationOneValue : ℂ :=
  triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedCenterTwo

private def RiemannMapping.normalizationPoleValue : ℂ :=
  triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedInfinity

@[simp]
private theorem RiemannMapping.normalizationZeroValue_eq :
    normalizationZeroValue = triangleCornerThreeGerm.function 0 :=
  triangleClosedDiscHomeomorph_centerOne

@[simp]
private theorem RiemannMapping.normalizationOneValue_eq :
    normalizationOneValue = triangleCornerFourGerm.function 0 :=
  triangleClosedDiscHomeomorph_centerTwo

@[simp]
private theorem RiemannMapping.normalizationPoleValue_eq :
    normalizationPoleValue = triangleIdealGerm.function 0 :=
  triangleClosedDiscHomeomorph_infty

private def RiemannMapping.normalizationOrientation : ℝ :=
  RiemannSphere.MobiusCircle.orientation normalizationZeroValue normalizationOneValue
    normalizationPoleValue

private theorem RiemannMapping.normalizationOrientation_ne_zero : normalizationOrientation ≠ 0 :=
  TriangleRiemannNormalization.normalization_orientation_ne_zero triangleClosedDiscHomeomorph
    SpecialPeriods.Triangle.triangleClosedCenterOne
    SpecialPeriods.Triangle.triangleClosedCenterTwo SpecialPeriods.Triangle.triangleClosedInfinity
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty
    SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty
    triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
    triangleClosedDiscHomeomorph_norm_infty

private def RiemannMapping.triangleFiniteNormalizationHomeomorph :
    SpecialPeriods.Triangle.TriangleClosedFinite ≃ₜ
      RiemannSphere.closedOrientedHalfPlane normalizationOrientation :=
  TriangleRiemannNormalization.normalizationHomeomorph triangleClosedDiscHomeomorph
    SpecialPeriods.Triangle.triangleClosedCenterOne
    SpecialPeriods.Triangle.triangleClosedCenterTwo SpecialPeriods.Triangle.triangleClosedInfinity
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty
    SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty
    triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
    triangleClosedDiscHomeomorph_norm_infty

@[simp]
private theorem RiemannMapping.triangleFiniteNormalizationHomeomorph_apply
    (x : SpecialPeriods.Triangle.TriangleClosedFinite) :
    (triangleFiniteNormalizationHomeomorph x : ℂ) =
      RiemannSphere.MobiusCircle.crossRatio normalizationZeroValue normalizationOneValue
        normalizationPoleValue
        (triangleClosedDiscHomeomorph (x : SpecialPeriods.Triangle.TriangleClosedDomain) : ℂ) :=
  TriangleRiemannNormalization.normalizationHomeomorph_apply triangleClosedDiscHomeomorph
    SpecialPeriods.Triangle.triangleClosedCenterOne
    SpecialPeriods.Triangle.triangleClosedCenterTwo SpecialPeriods.Triangle.triangleClosedInfinity
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty
    SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty
    triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
    triangleClosedDiscHomeomorph_norm_infty x

private theorem RiemannMapping.triangleFiniteNormalizationHomeomorph_centerOne :
    (triangleFiniteNormalizationHomeomorph
          ⟨SpecialPeriods.Triangle.triangleClosedCenterOne,
            SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty⟩ :
        ℂ) =
      0 :=
  TriangleRiemannNormalization.normalizationHomeomorph_first triangleClosedDiscHomeomorph
    SpecialPeriods.Triangle.triangleClosedCenterOne
    SpecialPeriods.Triangle.triangleClosedCenterTwo SpecialPeriods.Triangle.triangleClosedInfinity
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty
    SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty
    triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
    triangleClosedDiscHomeomorph_norm_infty

private theorem RiemannMapping.triangleFiniteNormalizationHomeomorph_centerTwo :
    (triangleFiniteNormalizationHomeomorph
          ⟨SpecialPeriods.Triangle.triangleClosedCenterTwo,
            SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty⟩ :
        ℂ) =
      1 :=
  TriangleRiemannNormalization.normalizationHomeomorph_second triangleClosedDiscHomeomorph
    SpecialPeriods.Triangle.triangleClosedCenterOne
    SpecialPeriods.Triangle.triangleClosedCenterTwo SpecialPeriods.Triangle.triangleClosedInfinity
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty
    SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty
    triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
    triangleClosedDiscHomeomorph_norm_infty

private theorem RiemannMapping.triangleFiniteNormalizationHomeomorph_strict_iff
    (x : SpecialPeriods.Triangle.TriangleClosedFinite) :
    0 < normalizationOrientation * (triangleFiniteNormalizationHomeomorph x : ℂ).im ↔
      (x : SpecialPeriods.Triangle.TriangleClosedDomain) ∈
        SpecialPeriods.Triangle.triangleClosedInterior := by
  have h :=
    TriangleRiemannNormalization.normalizationHomeomorph_strict_iff triangleClosedDiscHomeomorph
      SpecialPeriods.Triangle.triangleClosedCenterOne
      SpecialPeriods.Triangle.triangleClosedCenterTwo
      SpecialPeriods.Triangle.triangleClosedInfinity
      SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo
      SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty
      SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty
      triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
      triangleClosedDiscHomeomorph_norm_infty x
  exact h.trans (triangleClosedDiscHomeomorph_norm_lt_iff x)

private def RiemannMapping.halfFordNormalizationHomeomorph :
    SpecialPeriods.Triangle.halfFordRegion ≃ₜ
      RiemannSphere.closedOrientedHalfPlane normalizationOrientation :=
  SpecialPeriods.Triangle.halfFordClosedHomeomorph.trans triangleFiniteNormalizationHomeomorph

@[simp]
private theorem RiemannMapping.halfFordNormalizationHomeomorph_apply
    (z : SpecialPeriods.Triangle.halfFordRegion) :
    (halfFordNormalizationHomeomorph z : ℂ) =
      RiemannSphere.MobiusCircle.crossRatio normalizationZeroValue normalizationOneValue
        normalizationPoleValue
        (triangleClosedDiscHomeomorph (SpecialPeriods.Triangle.halfFordClosedHomeomorph z).val :
          ℂ) :=
  triangleFiniteNormalizationHomeomorph_apply (SpecialPeriods.Triangle.halfFordClosedHomeomorph z)

private theorem RiemannMapping.halfFordNormalizationHomeomorph_centerOne :
    (halfFordNormalizationHomeomorph
          ⟨SpecialPeriods.Triangle.centerOne,
            SpecialPeriods.Triangle.centerOne_mem_halfFordRegion⟩ :
        ℂ) =
      0 :=
  triangleFiniteNormalizationHomeomorph_centerOne

private theorem RiemannMapping.halfFordNormalizationHomeomorph_centerTwo :
    (halfFordNormalizationHomeomorph
          ⟨SpecialPeriods.Triangle.centerTwo,
            SpecialPeriods.Triangle.centerTwo_mem_halfFordRegion⟩ :
        ℂ) =
      1 :=
  triangleFiniteNormalizationHomeomorph_centerTwo

private theorem RiemannMapping.halfFordNormalizationHomeomorph_apply_of_interior (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.halfFordInterior) :
    (halfFordNormalizationHomeomorph
          ⟨z, SpecialPeriods.Triangle.halfFordInterior_subset_halfFordRegion hz⟩ :
        ℂ) =
      RiemannSphere.MobiusCircle.crossRatio normalizationZeroValue normalizationOneValue
        normalizationPoleValue (triangleMap (z : ℂ)) := by
  rw [halfFordNormalizationHomeomorph_apply,
    SpecialPeriods.Triangle.halfFordClosedHomeomorph_of_interior z hz,
    triangleClosedDiscHomeomorph_triangle]

private theorem RiemannMapping.halfFordNormalizationHomeomorph_strict_iff
    (z : SpecialPeriods.Triangle.halfFordRegion) :
    0 < normalizationOrientation * (halfFordNormalizationHomeomorph z : ℂ).im ↔
      (z : ℍ) ∈ SpecialPeriods.Triangle.halfFordInterior :=
  (triangleFiniteNormalizationHomeomorph_strict_iff
        (SpecialPeriods.Triangle.halfFordClosedHomeomorph z)).trans
    (SpecialPeriods.Triangle.halfFordClosedHomeomorph_mem_interior_iff z)

private theorem RiemannMapping.halfFordNormalizationHomeomorph_boundary_iff
    (z : SpecialPeriods.Triangle.halfFordRegion) :
    (halfFordNormalizationHomeomorph z : ℂ).im = 0 ↔
      (z : ℍ) ∉ SpecialPeriods.Triangle.halfFordInterior := by
  constructor
  · intro hz hin
    have h := (halfFordNormalizationHomeomorph_strict_iff z).mpr hin
    simp only [hz, MulZeroClass.mul_zero, lt_self_iff_false] at h
  · intro hz
    have hn : ¬0 < normalizationOrientation * (halfFordNormalizationHomeomorph z : ℂ).im :=
      fun h => hz ((halfFordNormalizationHomeomorph_strict_iff z).mp h)
    have he : normalizationOrientation * (halfFordNormalizationHomeomorph z : ℂ).im = 0 :=
      le_antisymm (le_of_not_gt hn) (halfFordNormalizationHomeomorph z).property
    exact (mul_eq_zero.mp he).resolve_left normalizationOrientation_ne_zero

private def
    RiemannMapping.triangleSignedHalfPlaneMap : TriangleUniformizationGluing.SignedHalfPlaneMap :=
  TriangleUniformizationGluing.signedHalfPlaneMapOfHomeomorph normalizationOrientation_ne_zero
    halfFordNormalizationHomeomorph halfFordNormalizationHomeomorph_strict_iff

@[simp]
private theorem RiemannMapping.triangleSignedHalfPlaneMap_coe
    (z : SpecialPeriods.Triangle.halfFordRegion) :
    triangleSignedHalfPlaneMap z = (halfFordNormalizationHomeomorph z : ℂ) :=
  TriangleUniformizationGluing.signedHalfPlaneMapOfHomeomorph_apply
    normalizationOrientation_ne_zero halfFordNormalizationHomeomorph
    halfFordNormalizationHomeomorph_strict_iff z

private theorem RiemannMapping.triangleSignedHalfPlaneMap_of_mem {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion) :
    triangleSignedHalfPlaneMap z = (halfFordNormalizationHomeomorph ⟨z, hz⟩ : ℂ) :=
  triangleSignedHalfPlaneMap_coe ⟨z, hz⟩

private theorem RiemannMapping.triangleSignedHalfPlaneMap_of_interior (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.halfFordInterior) :
    triangleSignedHalfPlaneMap z =
      RiemannSphere.MobiusCircle.crossRatio normalizationZeroValue normalizationOneValue
        normalizationPoleValue (triangleMap (z : ℂ)) := by
  rw [triangleSignedHalfPlaneMap_of_mem
      (SpecialPeriods.Triangle.halfFordInterior_subset_halfFordRegion hz)]
  exact halfFordNormalizationHomeomorph_apply_of_interior z hz

@[simp]
private theorem RiemannMapping.triangleSignedHalfPlaneMap_centerOne :
    triangleSignedHalfPlaneMap SpecialPeriods.Triangle.centerOne = 0 := by
  rw [triangleSignedHalfPlaneMap_of_mem SpecialPeriods.Triangle.centerOne_mem_halfFordRegion]
  exact halfFordNormalizationHomeomorph_centerOne

@[simp]
private theorem RiemannMapping.triangleSignedHalfPlaneMap_centerTwo :
    triangleSignedHalfPlaneMap SpecialPeriods.Triangle.centerTwo = 1 := by
  rw [triangleSignedHalfPlaneMap_of_mem SpecialPeriods.Triangle.centerTwo_mem_halfFordRegion]
  exact halfFordNormalizationHomeomorph_centerTwo

private theorem RiemannMapping.triangleSignedHalfPlaneMap_isProperMap :
    IsProperMap
      (fun z : SpecialPeriods.Triangle.halfFordRegion => triangleSignedHalfPlaneMap z) :=
  TriangleUniformizationGluing.halfFordHomeomorphExtension_isProperMap
    halfFordNormalizationHomeomorph

private theorem RiemannMapping.triangleSignedHalfPlaneMap_holomorphicOn :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω triangleSignedHalfPlaneMap SpecialPeriods.Triangle.halfFordInterior :=
  by
  have hab : normalizationZeroValue ≠ normalizationOneValue := by
    simpa only [normalizationZeroValue_eq, normalizationOneValue_eq] using
      triangleCorner_boundary_values_ne
  have hc : ‖normalizationPoleValue‖ = 1 := by
    simpa only [normalizationPoleValue_eq] using triangleIdealGerm.unit
  have hf : ContDiffOn ℂ ω triangleMap SpecialPeriods.Triangle.triangleInterior :=
    (triangleMap_differentiable.analyticOnNhd
          SpecialPeriods.Triangle.triangleInterior_isOpen).contDiffOn
      SpecialPeriods.Triangle.triangleInterior_isOpen.uniqueDiffOn
  have hcr :
    ContDiffOn ℂ ω
      (RiemannSphere.MobiusCircle.crossRatio normalizationZeroValue normalizationOneValue
        normalizationPoleValue)
      {z : ℂ | ‖z‖ < 1} :=
    RiemannSphere.crossRatio_holomorphicOn_disc hab hc
  have hcomp :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : ℂ =>
        RiemannSphere.MobiusCircle.crossRatio normalizationZeroValue normalizationOneValue
          normalizationPoleValue (triangleMap z))
      SpecialPeriods.Triangle.triangleInterior :=
    contMDiffOn_iff_contDiffOn.mpr (hcr.comp hf (fun _ hz => triangleMap_norm_lt_one hz))
  have hu :=
    hcomp.comp UpperHalfPlane.contMDiff_coe.contMDiffOn
      (show
        Set.MapsTo ((↑) : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior
          SpecialPeriods.Triangle.triangleInterior
        from by
        intro z hz
        simpa only [SpecialPeriods.Triangle.halfFordInterior_eq_preimage_triangleInterior,
          Set.mem_preimage] using hz)
  apply hu.congr
  intro z hz
  exact triangleSignedHalfPlaneMap_of_interior z hz

private theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_compact_preimage
    (D : TriangleUniformizationGluing.BoundaryMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (K : Set ℂ) (hK : IsCompact K) :
    IsCompact (SpecialPeriods.Triangle.fordRegion ∩ D.foldedFordMap ⁻¹' K) := by
  have hhalf (L : Set ℂ) (hL : IsCompact L) :
    IsCompact (SpecialPeriods.Triangle.halfFordRegion ∩ D.toFun ⁻¹' L) := by
    have hs := (hlocal.isCompact_preimage hL).image continuous_subtype_val
    change
      IsCompact
        ((Subtype.val : SpecialPeriods.Triangle.halfFordRegion → ℍ) ''
          ((Subtype.val : SpecialPeriods.Triangle.halfFordRegion → ℍ) ⁻¹' (D.toFun ⁻¹' L))) at hs
    simpa only [Subtype.image_preimage_val] using hs
  have hconj : IsCompact ((conj : ℂ → ℂ) ⁻¹' K) :=
    Complex.conjCLE.toHomeomorph.isCompact_preimage.mpr hK
  have heq :
    SpecialPeriods.Triangle.fordRegion ∩ D.foldedFordMap ⁻¹' K =
      (SpecialPeriods.Triangle.halfFordRegion ∩ D.toFun ⁻¹' K) ∪
        SpecialPeriods.Triangle.rightReflection ''
          (SpecialPeriods.Triangle.halfFordRegion ∩ D.toFun ⁻¹' ((conj : ℂ → ℂ) ⁻¹' K)) := by
    ext z
    constructor
    · rintro ⟨hz, hKz⟩
      change D.foldedFordMap z ∈ K at hKz
      rw [← SpecialPeriods.Triangle.halfFordRegion_union_reflection] at hz
      rcases hz with hz | ⟨w, hw, rfl⟩
      · left
        refine ⟨hz, ?_⟩
        change D z ∈ K
        rwa [D.foldedFordMap_of_left hz.2] at hKz
      · right
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        change conj (D w) ∈ K
        rwa [D.foldedFordMap_reflected w hw] at hKz
    · rintro (⟨hz, hKz⟩ | ⟨w, ⟨hw, hKw⟩, rfl⟩)
      · refine ⟨hz.1, ?_⟩
        change D.foldedFordMap z ∈ K
        rwa [D.foldedFordMap_of_left hz.2]
      · refine ⟨SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion hw.1, ?_⟩
        change D.foldedFordMap (SpecialPeriods.Triangle.rightReflection w) ∈ K
        rw [D.foldedFordMap_reflected w hw]
        exact hKw
  rw [heq]
  exact
    (hhalf K hK).union ((hhalf _ hconj).image SpecialPeriods.Triangle.rightReflection.continuous)

private def SpecialPeriods.Triangle.closedFirstSector : Set ℍ :=
  {z | z.re ≤ -(1 / 2) ∧ 1 ≤ ‖(z : ℂ)‖}

private def SpecialPeriods.Triangle.closedSecondSector : Set ℍ :=
  {z | stripLeft ≤ z.re ∧ stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖}

private def SpecialPeriods.Triangle.firstWeakExcluded : Set ℍ :=
  {z | -(1 / 2) ≤ z.re ∨ ‖(z : ℂ)‖ ≤ 1}

private def SpecialPeriods.Triangle.secondWeakExcluded : Set ℍ :=
  {z | z.re ≤ stripLeft ∨ ‖(z : ℂ) - (stripLeft : ℂ)‖ ≤ stripRight}

private def SpecialPeriods.Triangle.circularDoubleRegion : Set ℍ :=
  closedFirstSector ∩ closedSecondSector

private theorem SpecialPeriods.Triangle.firstExcluded_subset_firstWeakExcluded :
    firstExcluded ⊆ firstWeakExcluded := by
  intro z hz
  exact hz.imp le_of_lt le_of_lt

private theorem SpecialPeriods.Triangle.secondExcluded_subset_secondWeakExcluded :
    secondExcluded ⊆ secondWeakExcluded := by
  intro z hz
  exact hz.imp le_of_lt le_of_lt

private theorem SpecialPeriods.Triangle.firstWeakExcluded_subset_pingPongOne :
    firstWeakExcluded ⊆ pingPongOne := by
  intro z hz
  change -1 < z.re
  rcases hz with hx | hn
  · linarith
  · have habs : |z.re| < ‖(z : ℂ)‖ := Complex.abs_re_lt_norm.mpr z.im_ne_zero
    linarith [neg_le_abs z.re]

private theorem SpecialPeriods.Triangle.secondWeakExcluded_subset_pingPongTwo :
    secondWeakExcluded ⊆ pingPongTwo := by
  intro z hz
  change z.re < -1
  rcases hz with hx | hn
  · exact hx.trans_lt stripLeft_lt_neg_one
  · have him : ((z : ℂ) - (stripLeft : ℂ)).im ≠ 0 := by simpa using z.im_ne_zero
    have habs := Complex.abs_re_lt_norm.mpr him
    have hr := le_abs_self (((z : ℂ) - (stripLeft : ℂ)).re)
    simp only [Complex.sub_re, UpperHalfPlane.coe_re, Complex.ofReal_re] at habs hr
    linarith [stripLeft_add_stripRight]

private theorem SpecialPeriods.Triangle.firstWeakExcluded_subset_secondSector :
    firstWeakExcluded ⊆ secondSector :=
  firstWeakExcluded_subset_pingPongOne.trans pingPongOne_subset_secondSector

private theorem SpecialPeriods.Triangle.secondWeakExcluded_subset_firstSector :
    secondWeakExcluded ⊆ firstSector :=
  secondWeakExcluded_subset_pingPongTwo.trans pingPongTwo_subset_firstSector

private theorem SpecialPeriods.Triangle.circularDoubleRegion_disjoint_firstExcluded :
    Disjoint circularDoubleRegion firstExcluded := by
  apply Set.disjoint_left.mpr
  intro z hz he
  rcases he with hx | hn
  · exact (not_lt_of_ge hz.1.1) hx
  · exact (not_lt_of_ge hz.1.2) hn

private theorem SpecialPeriods.Triangle.circularDoubleRegion_disjoint_secondExcluded :
    Disjoint circularDoubleRegion secondExcluded := by
  apply Set.disjoint_left.mpr
  intro z hz he
  rcases he with hx | hn
  · exact (not_lt_of_ge hz.2.1) hx
  · exact (not_lt_of_ge hz.2.2) hn

private theorem SpecialPeriods.Triangle.generatorOne_closedFirstSector :
    Set.MapsTo (fun z : ℍ => generatorOneSL • z) closedFirstSector firstWeakExcluded := by
  intro z hz
  left
  change -(1 / 2) ≤ (((generatorOneSL • z : ℍ) : ℂ)).re
  rw [generatorOneSL_smul_coe]
  simp only [Complex.neg_re, Complex.inv_re, Complex.add_re, UpperHalfPlane.coe_re,
    Complex.one_re]
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hn : 1 ≤ Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2]
  simp only [← neg_div]
  apply (le_div_iff₀ hd).mpr
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hn ⊢
  nlinarith

private theorem SpecialPeriods.Triangle.norm_add_one_le_norm_of_re_le_half_mo1973_19719 (z : ℍ)
    (hz : z.re ≤ -(1 / 2)) : ‖(z : ℂ) + 1‖ ≤ ‖(z : ℂ)‖ := by
  have hsq : ‖(z : ℂ) + 1‖ ^ 2 ≤ ‖(z : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    linarith
  nlinarith [norm_nonneg ((z : ℂ) + 1), norm_nonneg (z : ℂ)]

private theorem SpecialPeriods.Triangle.generatorOne_sq_closedFirstSector :
    Set.MapsTo (fun z : ℍ => (generatorOneSL ^ 2 : SL(2, ℝ)) • z) closedFirstSector
      firstWeakExcluded := by
  intro z hz
  right
  rw [generatorOneSL_sq_smul_coe]
  have he : (-1 : ℂ) - (z : ℂ)⁻¹ = -(((z : ℂ) + 1) / (z : ℂ)) := by
    field_simp [z.ne_zero]
    ring
  rw [he, norm_neg, norm_div]
  exact
    (div_le_one (norm_pos_iff.mpr z.ne_zero)).mpr
      (norm_add_one_le_norm_of_re_le_half_mo1973_19719 z hz.1)

private def SpecialPeriods.Triangle.secondShift_mo1973_19721 (z : ℍ) : ℂ :=
  (z : ℂ) - (stripLeft : ℂ)

private theorem SpecialPeriods.Triangle.secondShift_re_mo1973_19722 (z : ℍ) :
    (secondShift_mo1973_19721 z).re = z.re - stripLeft := by simp [secondShift_mo1973_19721]

private theorem SpecialPeriods.Triangle.secondShift_add_real_ne_zero_mo1973_19723 (z : ℍ)
    (a : ℝ) : secondShift_mo1973_19721 z + (a : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [secondShift_mo1973_19721, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
    sub_zero, add_zero, Complex.zero_im, UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

private theorem SpecialPeriods.Triangle.stripLeft_eq_neg_stripRight_sub_one_mo1973_19724 :
    stripLeft = -stripRight - 1 := by linarith [stripLeft_add_stripRight]

private theorem SpecialPeriods.Triangle.width_eq_two_stripRight_add_one_mo1973_19725 :
    width = 2 * stripRight + 1 := by
  unfold stripRight
  ring

private theorem SpecialPeriods.Triangle.stripRight_sq_complex_mo1973_19726 :
    (stripRight : ℂ) ^ 2 = 1 / 2 := by
  rw [← Complex.ofReal_pow, stripRight_sq]
  norm_num

private theorem SpecialPeriods.Triangle.generatorTwo_secondShift_mo1973_19727 (z : ℍ) :
    secondShift_mo1973_19721 (generatorTwoSL • z) =
      (stripRight : ℂ) * (secondShift_mo1973_19721 z - stripRight) /
        (secondShift_mo1973_19721 z + stripRight) := by
  have hd := secondShift_add_real_ne_zero_mo1973_19723 z stripRight
  have hs := stripRight_sq_complex_mo1973_19726
  unfold secondShift_mo1973_19721 at *
  rw [generatorTwoSL_smul_coe]
  rw [stripLeft_eq_neg_stripRight_sub_one_mo1973_19724,
    width_eq_two_stripRight_add_one_mo1973_19725] at *
  push_cast at *
  have he :
    (z : ℂ) + (2 * (stripRight : ℂ) + 1) = (z : ℂ) - (-(stripRight : ℂ) - 1) + stripRight := by
    ring
  rw [he]
  field_simp [hd]
  linear_combination 2 * hs

private theorem SpecialPeriods.Triangle.generatorTwo_sq_secondShift_mo1973_19728 (z : ℍ) :
    secondShift_mo1973_19721 ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z) =
      -(stripRight : ℂ) ^ 2 / secondShift_mo1973_19721 z := by
  have hz : secondShift_mo1973_19721 z ≠ 0 := by
    simpa using secondShift_add_real_ne_zero_mo1973_19723 z 0
  have hd := secondShift_add_real_ne_zero_mo1973_19723 z stripRight
  have hR : (stripRight : ℂ) ≠ 0 := by exact_mod_cast stripRight_pos.ne'
  rw [pow_two, SemigroupAction.mul_smul, generatorTwo_secondShift_mo1973_19727,
    generatorTwo_secondShift_mo1973_19727]
  field_simp [hz, hd, hR]
  ring

private theorem SpecialPeriods.Triangle.generatorTwo_cube_secondShift_mo1973_19729 (z : ℍ) :
    secondShift_mo1973_19721 ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z) =
      -(stripRight : ℂ) * (secondShift_mo1973_19721 z + stripRight) /
        (secondShift_mo1973_19721 z - stripRight) := by
  have hd : secondShift_mo1973_19721 z - (stripRight : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_neg, sub_eq_add_neg] using
      secondShift_add_real_ne_zero_mo1973_19723 z (-stripRight)
  have hs := stripRight_sq_complex_mo1973_19726
  unfold secondShift_mo1973_19721 at *
  rw [generatorTwoSL_cube_smul_coe]
  rw [stripLeft_eq_neg_stripRight_sub_one_mo1973_19724,
    width_eq_two_stripRight_add_one_mo1973_19725] at *
  push_cast at *
  have he : (z : ℂ) + 1 = (z : ℂ) - (-(stripRight : ℂ) - 1) - stripRight := by ring
  rw [he]
  field_simp [hd]
  linear_combination 2 * hs

private theorem SpecialPeriods.Triangle.norm_sub_div_add_le_one_mo1973_19730 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : 0 ≤ u.re) : ‖(u - (r : ℂ)) / (u + (r : ℂ))‖ ≤ 1 := by
  have hd : u + (r : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  rw [norm_div]
  apply (div_le_one (norm_pos_iff.mpr hd)).mpr
  have hsq : ‖u - (r : ℂ)‖ ^ 2 ≤ ‖u + (r : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, add_zero]
    nlinarith [mul_nonneg hr.le hu]
  nlinarith [norm_nonneg (u - (r : ℂ)), norm_nonneg (u + (r : ℂ))]

private theorem SpecialPeriods.Triangle.re_add_div_sub_nonneg_mo1973_19731 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : r ≤ ‖u‖) : 0 ≤ ((u + (r : ℂ)) / (u - (r : ℂ))).re := by
  have hsq : r ^ 2 ≤ Complex.normSq u := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  rw [Complex.div_re, ← add_div]
  apply div_nonneg ?_ (Complex.normSq_nonneg _)
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.add_im, Complex.sub_im,
    Complex.ofReal_im, add_zero, sub_zero]
  rw [Complex.normSq_apply] at hsq
  nlinarith

private theorem SpecialPeriods.Triangle.re_neg_sq_div_nonpos_mo1973_19732 {r : ℝ} {u : ℂ}
    (hu : 0 ≤ u.re) : (-(r : ℂ) ^ 2 / u).re ≤ 0 := by
  have hnum : -(r ^ 2) * u.re ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg r)) hu
  simpa [Complex.div_re, ← Complex.ofReal_pow] using
    div_nonpos_of_nonpos_of_nonneg hnum (Complex.normSq_nonneg u)

private theorem SpecialPeriods.Triangle.norm_sub_div_add_lt_one_mo1973_19733 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : 0 < u.re) : ‖(u - (r : ℂ)) / (u + (r : ℂ))‖ < 1 := by
  have hd : u + (r : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  rw [norm_div]
  apply (div_lt_one (norm_pos_iff.mpr hd)).mpr
  have hsq : ‖u - (r : ℂ)‖ ^ 2 < ‖u + (r : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, add_zero]
    nlinarith [mul_pos hr hu]
  nlinarith [norm_nonneg (u - (r : ℂ)), norm_nonneg (u + (r : ℂ))]

private theorem SpecialPeriods.Triangle.re_neg_sq_div_neg_mo1973_19735 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : 0 < u.re) : (-(r : ℂ) ^ 2 / u).re < 0 := by
  have hd : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hnum : -(r ^ 2) * u.re < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hr)) hu
  simpa [Complex.div_re, ← Complex.ofReal_pow] using
    div_neg_of_neg_of_pos hnum (Complex.normSq_pos.mpr hd)

private theorem SpecialPeriods.Triangle.generatorTwo_sq_shift (z : ℍ) :
    (((generatorTwoSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ) - (stripLeft : ℂ) =
      -(stripRight : ℂ) ^ 2 / ((z : ℂ) - (stripLeft : ℂ)) :=
  generatorTwo_sq_secondShift_mo1973_19728 z

private theorem SpecialPeriods.Triangle.generatorTwo_shift_norm_le (z : ℍ) (hx : stripLeft ≤ z.re) :
    ‖((generatorTwoSL • z : ℍ) : ℂ) - (stripLeft : ℂ)‖ ≤ stripRight := by
  change ‖secondShift_mo1973_19721 (generatorTwoSL • z)‖ ≤ stripRight
  rw [generatorTwo_secondShift_mo1973_19727, mul_div_assoc, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos stripRight_pos]
  have hrez : 0 ≤ (secondShift_mo1973_19721 z).re := by
    rw [secondShift_re_mo1973_19722]
    exact sub_nonneg.mpr hx
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (norm_sub_div_add_le_one_mo1973_19730 stripRight_pos hrez)
      stripRight_pos.le

private theorem SpecialPeriods.Triangle.generatorTwo_shift_norm_lt (z : ℍ) (hx : stripLeft < z.re) :
    ‖((generatorTwoSL • z : ℍ) : ℂ) - (stripLeft : ℂ)‖ < stripRight := by
  change ‖secondShift_mo1973_19721 (generatorTwoSL • z)‖ < stripRight
  rw [generatorTwo_secondShift_mo1973_19727, mul_div_assoc, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos stripRight_pos]
  have hrez : 0 < (secondShift_mo1973_19721 z).re := by
    rw [secondShift_re_mo1973_19722]
    exact sub_pos.mpr hx
  simpa only [mul_one] using
    mul_lt_mul_of_pos_left (norm_sub_div_add_lt_one_mo1973_19733 stripRight_pos hrez)
      stripRight_pos

private theorem
    SpecialPeriods.Triangle.generatorTwo_sq_re_le_stripLeft (z : ℍ) (hx : stripLeft ≤ z.re) :
    ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z).re ≤ stripLeft := by
  have hrez : 0 ≤ (secondShift_mo1973_19721 z).re := by
    rw [secondShift_re_mo1973_19722]
    exact sub_nonneg.mpr hx
  have h := re_neg_sq_div_nonpos_mo1973_19732 (r := stripRight) hrez
  rw [← generatorTwo_sq_secondShift_mo1973_19728 z, secondShift_re_mo1973_19722] at h
  exact sub_nonpos.mp h

private theorem
    SpecialPeriods.Triangle.generatorTwo_sq_re_lt_stripLeft (z : ℍ) (hx : stripLeft < z.re) :
    ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z).re < stripLeft := by
  have hrez : 0 < (secondShift_mo1973_19721 z).re := by
    rw [secondShift_re_mo1973_19722]
    exact sub_pos.mpr hx
  have h := re_neg_sq_div_neg_mo1973_19735 stripRight_pos hrez
  rw [← generatorTwo_sq_secondShift_mo1973_19728 z, secondShift_re_mo1973_19722] at h
  exact sub_neg.mp h

private theorem SpecialPeriods.Triangle.generatorTwo_cube_re_le_stripLeft (z : ℍ)
    (hn : stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖) :
    ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z).re ≤ stripLeft := by
  have h : (secondShift_mo1973_19721 ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z)).re ≤ 0 := by
    rw [generatorTwo_cube_secondShift_mo1973_19729, mul_div_assoc]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, MulZeroClass.zero_mul, sub_zero]
    exact
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr stripRight_pos.le)
        (re_add_div_sub_nonneg_mo1973_19731 stripRight_pos hn)
  rw [secondShift_re_mo1973_19722] at h
  exact sub_nonpos.mp h

private theorem SpecialPeriods.Triangle.generatorTwo_closedSecondSector :
    Set.MapsTo (fun z : ℍ => generatorTwoSL • z) closedSecondSector secondWeakExcluded :=
  fun z hz => Or.inr (generatorTwo_shift_norm_le z hz.1)

private theorem SpecialPeriods.Triangle.generatorTwo_sq_closedSecondSector :
    Set.MapsTo (fun z : ℍ => (generatorTwoSL ^ 2 : SL(2, ℝ)) • z) closedSecondSector
      secondWeakExcluded :=
  fun z hz => Or.inl (generatorTwo_sq_re_le_stripLeft z hz.1)

private theorem SpecialPeriods.Triangle.generatorTwo_cube_closedSecondSector :
    Set.MapsTo (fun z : ℍ => (generatorTwoSL ^ 3 : SL(2, ℝ)) • z) closedSecondSector
      secondWeakExcluded :=
  fun z hz => Or.inl (generatorTwo_cube_re_le_stripLeft z hz.2)

private theorem SpecialPeriods.Triangle.generatorOne_re_lower_of_one_le_norm_mo1973_19748 (z : ℍ)
    (hn : 1 ≤ ‖(z : ℂ)‖) : -(1 / 2) ≤ (generatorOneSL • z).re := by
  change -(1 / 2) ≤ (((generatorOneSL • z : ℍ) : ℂ)).re
  rw [generatorOneSL_smul_coe]
  simp only [Complex.neg_re, Complex.inv_re, Complex.add_re, UpperHalfPlane.coe_re,
    Complex.one_re]
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hsq : 1 ≤ Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  simp only [← neg_div]
  apply (le_div_iff₀ hd).mpr
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hsq ⊢
  nlinarith

private theorem SpecialPeriods.Triangle.re_lower_of_one_le_generatorOne_sq_norm_mo1973_19749
    (z : ℍ) (hn : 1 ≤ ‖(((generatorOneSL ^ 2) • z : ℍ) : ℂ)‖) : -(1 / 2) ≤ z.re := by
  rw [generatorOneSL_sq_smul_coe] at hn
  have he : (-1 : ℂ) - (z : ℂ)⁻¹ = -(((z : ℂ) + 1) / (z : ℂ)) := by
    field_simp [z.ne_zero]
    ring
  rw [he, norm_neg, norm_div] at hn
  have hnorm : ‖(z : ℂ)‖ ≤ ‖(z : ℂ) + 1‖ := (one_le_div (norm_pos_iff.mpr z.ne_zero)).mp hn
  have hsq := (sq_le_sq₀ (norm_nonneg (z : ℂ)) (norm_nonneg ((z : ℂ) + 1))).mpr hnorm
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hsq
  linarith

private theorem SpecialPeriods.Triangle.generatorOne_sq_reflections (z : ℍ) :
    (generatorOneSL ^ 2) • z = circleReflection (rightReflection z) := by
  apply UpperHalfPlane.ext
  rw [generatorOneSL_sq_smul_coe, circleReflection_coe, rightReflection_coe]
  simp only [map_sub, map_neg, map_one, Complex.conj_conj]
  rw [show (-1 : ℂ) - (z : ℂ) + 1 = -(z : ℂ) by ring]
  simp [one_div, sub_eq_add_neg]

private theorem SpecialPeriods.Triangle.generatorOne_closedFirst_return (z : ℍ)
    (hz : z ∈ closedFirstSector) (hw : generatorOneSL • z ∈ closedFirstSector) :
    generatorOneSL • z = circleReflection z := by
  have hx : (generatorOneSL • z).re = -(1 / 2) :=
    le_antisymm hw.1 (generatorOne_re_lower_of_one_le_norm_mo1973_19748 z hz.2)
  have hfix := (rightReflection_fixed_iff (generatorOneSL • z)).mpr hx
  calc
    generatorOneSL • z = rightReflection (generatorOneSL • z) := hfix.symm
    _ = circleReflection z := by rw [generatorOne_reflections, rightReflection_involutive]

private theorem SpecialPeriods.Triangle.generatorOne_sq_closedFirst_return (z : ℍ)
    (hz : z ∈ closedFirstSector) (hw : (generatorOneSL ^ 2) • z ∈ closedFirstSector) :
    (generatorOneSL ^ 2) • z = circleReflection z := by
  have hx : z.re = -(1 / 2) :=
    le_antisymm hz.1 (re_lower_of_one_le_generatorOne_sq_norm_mo1973_19749 z hw.2)
  rw [generatorOne_sq_reflections, (rightReflection_fixed_iff z).mpr hx]

private theorem
    SpecialPeriods.Triangle.generatorOne_closed_return (z : ℍ) (hz : z ∈ circularDoubleRegion)
    (hw : generatorOneSL • z ∈ circularDoubleRegion) : generatorOneSL • z = circleReflection z :=
  generatorOne_closedFirst_return z hz.1 hw.1

private theorem SpecialPeriods.Triangle.generatorOne_sq_closed_return (z : ℍ)
    (hz : z ∈ circularDoubleRegion) (hw : (generatorOneSL ^ 2) • z ∈ circularDoubleRegion) :
    (generatorOneSL ^ 2) • z = circleReflection z :=
  generatorOne_sq_closedFirst_return z hz.1 hw.1

private theorem SpecialPeriods.Triangle.eq_centerTwo_of_secondSector_boundaries_mo1973_19755
    (z : ℍ) (hr : z.re = stripLeft) (hn : ‖(z : ℂ) - (stripLeft : ℂ)‖ = stripRight) :
    z = centerTwo := by
  have hs := congrArg (fun r : ℝ => r ^ 2) hn
  rw [Complex.sq_norm, Complex.normSq_apply] at hs
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hr, sub_self, sub_zero, MulZeroClass.zero_mul,
    zero_add] at hs
  have hi : z.im = stripRight := by nlinarith [z.im_pos, stripRight_pos]
  apply UpperHalfPlane.ext
  apply Complex.ext
  · simpa only [UpperHalfPlane.coe_re, centerTwo_re, stripLeft] using hr
  · simpa only [UpperHalfPlane.coe_im, centerTwo_im, stripRight] using hi

private theorem SpecialPeriods.Triangle.generatorTwo_smul_cube_mo1973_19756 (z : ℍ) :
    generatorTwoSL • ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z) = z := by
  rw [← SemigroupAction.mul_smul, ← pow_succ']
  change realSLPermutation (generatorTwoSL ^ 4) z = z
  rw [generatorTwoSL_fourth, realSLPermutation_neg_one]
  rfl

private theorem SpecialPeriods.Triangle.generatorTwo_closedSecond_return (z : ℍ)
    (hz : z ∈ closedSecondSector) (hgz : generatorTwoSL • z ∈ closedSecondSector) :
    generatorTwoSL • z = circleReflection z := by
  have hr : z.re = stripLeft :=
    le_antisymm (le_of_not_gt fun h => (not_lt_of_ge hgz.2) (generatorTwo_shift_norm_lt z h)) hz.1
  rw [generatorTwo_reflections, (leftReflection_fixed_iff z).mpr hr]

private theorem SpecialPeriods.Triangle.generatorTwo_sq_closedSecond_return_eq_centerTwo (z : ℍ)
    (hz : z ∈ closedSecondSector)
    (hgz : (generatorTwoSL ^ 2 : SL(2, ℝ)) • z ∈ closedSecondSector) : z = centerTwo := by
  have hr : z.re = stripLeft :=
    le_antisymm (le_of_not_gt fun h => (not_lt_of_ge hgz.1) (generatorTwo_sq_re_lt_stripLeft z h))
      hz.1
  have hn := hgz.2
  rw [generatorTwo_sq_shift, norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos stripRight_pos] at hn
  have hp : 0 < ‖(z : ℂ) - (stripLeft : ℂ)‖ := stripRight_pos.trans_le hz.2
  have hle : ‖(z : ℂ) - (stripLeft : ℂ)‖ ≤ stripRight := by
    apply (mul_le_mul_iff_of_pos_left stripRight_pos).mp
    simpa only [pow_two] using (le_div_iff₀ hp).mp hn
  exact eq_centerTwo_of_secondSector_boundaries_mo1973_19755 z hr (le_antisymm hle hz.2)

private theorem SpecialPeriods.Triangle.generatorTwo_sq_closedSecond_return (z : ℍ)
    (hz : z ∈ closedSecondSector)
    (hgz : (generatorTwoSL ^ 2 : SL(2, ℝ)) • z ∈ closedSecondSector) :
    (generatorTwoSL ^ 2 : SL(2, ℝ)) • z = circleReflection z := by
  obtain rfl := generatorTwo_sq_closedSecond_return_eq_centerTwo z hz hgz
  have hl : leftReflection centerTwo = centerTwo :=
    (leftReflection_fixed_iff centerTwo).mpr centerTwo_re
  have hc : circleReflection centerTwo = centerTwo := by
    have h := generatorTwo_reflections centerTwo
    rw [generatorTwo_fix, hl] at h
    exact h.symm
  simp only [pow_two, SemigroupAction.mul_smul, generatorTwo_fix, hc]

private theorem SpecialPeriods.Triangle.generatorTwo_cube_closedSecond_return (z : ℍ)
    (hz : z ∈ closedSecondSector)
    (hgz : (generatorTwoSL ^ 3 : SL(2, ℝ)) • z ∈ closedSecondSector) :
    (generatorTwoSL ^ 3 : SL(2, ℝ)) • z = circleReflection z := by
  have h :=
    generatorTwo_closedSecond_return ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z) hgz
      (by simpa only [generatorTwo_smul_cube_mo1973_19756] using hz)
  have hc := congrArg circleReflection h
  simpa only [generatorTwo_smul_cube_mo1973_19756,
    circleReflection_involutive ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z)] using hc.symm

private theorem
    SpecialPeriods.Triangle.generatorTwo_closed_return (z : ℍ) (hz : z ∈ circularDoubleRegion)
    (hgz : generatorTwoSL • z ∈ circularDoubleRegion) : generatorTwoSL • z = circleReflection z :=
  generatorTwo_closedSecond_return z hz.2 hgz.2

private theorem SpecialPeriods.Triangle.generatorTwo_sq_closed_return (z : ℍ)
    (hz : z ∈ circularDoubleRegion)
    (hgz : (generatorTwoSL ^ 2 : SL(2, ℝ)) • z ∈ circularDoubleRegion) :
    (generatorTwoSL ^ 2 : SL(2, ℝ)) • z = circleReflection z :=
  generatorTwo_sq_closedSecond_return z hz.2 hgz.2

private theorem SpecialPeriods.Triangle.generatorTwo_cube_closed_return (z : ℍ)
    (hz : z ∈ circularDoubleRegion)
    (hgz : (generatorTwoSL ^ 3 : SL(2, ℝ)) • z ∈ circularDoubleRegion) :
    (generatorTwoSL ^ 3 : SL(2, ℝ)) • z = circleReflection z :=
  generatorTwo_cube_closedSecond_return z hz.2 hgz.2

private theorem SpecialPeriods.Triangle.circleReflection_re (z : ℍ) :
    (circleReflection z).re = -1 + (z.re + 1) / Complex.normSq ((z : ℂ) + 1) := by
  change (-1 + 1 / (conj (z : ℂ) + 1)).re = _
  rw [show conj (z : ℂ) + 1 = conj ((z : ℂ) + 1) by simp]
  simp only [one_div, Complex.add_re, Complex.neg_re, Complex.one_re, Complex.inv_re,
    Complex.conj_re, Complex.normSq_conj, UpperHalfPlane.coe_re]

private theorem SpecialPeriods.Triangle.circleReflection_re_le_neg_half_iff (z : ℍ) :
    (circleReflection z).re ≤ -(1 / 2) ↔ 1 ≤ ‖(z : ℂ)‖ := by
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  calc
    (circleReflection z).re ≤ -(1 / 2) ↔ (z.re + 1) / Complex.normSq ((z : ℂ) + 1) ≤ 1 / 2 := by
      rw [circleReflection_re]
      constructor <;> intro h <;> linarith
    _ ↔ z.re + 1 ≤ (1 / 2) * Complex.normSq ((z : ℂ) + 1) := (div_le_iff₀ hd)
    _ ↔ (1 : ℝ) ^ 2 ≤ ‖(z : ℂ)‖ ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.one_re,
        Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      constructor <;> intro h <;> nlinarith
    _ ↔ 1 ≤ ‖(z : ℂ)‖ := sq_le_sq₀ (by norm_num) (norm_nonneg _)

private theorem SpecialPeriods.Triangle.one_le_circleReflection_norm_iff (z : ℍ) :
    1 ≤ ‖(circleReflection z : ℂ)‖ ↔ z.re ≤ -(1 / 2) := by
  simpa only [circleReflection_involutive z] using
    (circleReflection_re_le_neg_half_iff (circleReflection z)).symm

private theorem SpecialPeriods.Triangle.circleReflection_re_ge_stripLeft_iff (z : ℍ) :
    stripLeft ≤ (circleReflection z).re ↔ stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ := by
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hL : stripLeft = -stripRight - 1 := by linarith [stripLeft_add_stripRight]
  have he :
    stripRight * (‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 - stripRight ^ 2) =
      z.re + 1 + stripRight * Complex.normSq ((z : ℂ) + 1) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hL]
    linear_combination (2 * z.re + 2) * stripRight_sq
  calc
    stripLeft ≤ (circleReflection z).re ↔
        -stripRight ≤ (z.re + 1) / Complex.normSq ((z : ℂ) + 1) := by
      rw [circleReflection_re, hL]
      constructor <;> intro h <;> linarith
    _ ↔ -stripRight * Complex.normSq ((z : ℂ) + 1) ≤ z.re + 1 := (le_div_iff₀ hd)
    _ ↔ 0 ≤ z.re + 1 + stripRight * Complex.normSq ((z : ℂ) + 1) := by
      constructor <;> intro h <;> linarith
    _ ↔ 0 ≤ stripRight * (‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 - stripRight ^ 2) := by rw [he]
    _ ↔ 0 ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 - stripRight ^ 2 :=
      (mul_nonneg_iff_of_pos_left stripRight_pos)
    _ ↔ stripRight ^ 2 ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 := sub_nonneg
    _ ↔ stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ := sq_le_sq₀ stripRight_pos.le (norm_nonneg _)

private theorem
    SpecialPeriods.Triangle.stripRight_le_circleReflection_sub_stripLeft_norm_iff (z : ℍ) :
    stripRight ≤ ‖(circleReflection z : ℂ) - (stripLeft : ℂ)‖ ↔ stripLeft ≤ z.re := by
  simpa only [circleReflection_involutive z] using
    (circleReflection_re_ge_stripLeft_iff (circleReflection z)).symm

@[simp]
private theorem SpecialPeriods.Triangle.circleReflection_mem_closedFirstSector_iff (z : ℍ) :
    circleReflection z ∈ closedFirstSector ↔ z ∈ closedFirstSector := by
  change
    (circleReflection z).re ≤ -(1 / 2) ∧ 1 ≤ ‖(circleReflection z : ℂ)‖ ↔
      z.re ≤ -(1 / 2) ∧ 1 ≤ ‖(z : ℂ)‖
  rw [circleReflection_re_le_neg_half_iff, one_le_circleReflection_norm_iff, and_comm]

@[simp]
private theorem SpecialPeriods.Triangle.circleReflection_mem_closedSecondSector_iff (z : ℍ) :
    circleReflection z ∈ closedSecondSector ↔ z ∈ closedSecondSector := by
  change
    stripLeft ≤ (circleReflection z).re ∧
        stripRight ≤ ‖(circleReflection z : ℂ) - (stripLeft : ℂ)‖ ↔
      stripLeft ≤ z.re ∧ stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖
  rw [circleReflection_re_ge_stripLeft_iff, stripRight_le_circleReflection_sub_stripLeft_norm_iff,
    and_comm]

@[simp]
private theorem SpecialPeriods.Triangle.circleReflection_mem_circularDoubleRegion_iff (z : ℍ) :
    circleReflection z ∈ circularDoubleRegion ↔ z ∈ circularDoubleRegion := by
  simp only [circularDoubleRegion, Set.mem_inter_iff, circleReflection_mem_closedFirstSector_iff,
    circleReflection_mem_closedSecondSector_iff]

private theorem SpecialPeriods.Triangle.circleReflection_mapsTo_circularDoubleRegion :
    Set.MapsTo circleReflection circularDoubleRegion circularDoubleRegion := fun z hz =>
  (circleReflection_mem_circularDoubleRegion_iff z).mpr hz

private theorem SpecialPeriods.Triangle.circleReflection_add_one_norm (z : ℍ) :
    ‖(circleReflection z : ℂ) + 1‖ = 1 / ‖(z : ℂ) + 1‖ := by
  rw [circleReflection_coe]
  have he : (-1 : ℂ) + 1 / (conj (z : ℂ) + 1) + 1 = 1 / (conj (z : ℂ) + 1) := by ring
  rw [he, norm_div, NormOneClass.norm_one, show conj (z : ℂ) + 1 = conj ((z : ℂ) + 1) by simp,
    Complex.norm_conj]

private theorem SpecialPeriods.Triangle.fordRegion_subset_closedSecondSector :
    fordRegion ⊆ closedSecondSector := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hn : 1 ≤ Complex.normSq ((z : ℂ) + 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2.2.1]
  have hprod : 0 ≤ stripRight * (z.re - stripLeft) :=
    mul_nonneg stripRight_pos.le (sub_nonneg.mpr hz.1)
  have hs : stripRight ^ 2 ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, sub_zero, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
      add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hn ⊢
    have hleft : stripLeft = -1 - stripRight := by linarith [stripLeft_add_stripRight]
    rw [hleft] at hprod ⊢
    nlinarith [stripRight_sq]
  exact (sq_le_sq₀ stripRight_pos.le (norm_nonneg _)).mp hs

private theorem SpecialPeriods.Triangle.halfFordRegion_subset_circularDoubleRegion :
    halfFordRegion ⊆ circularDoubleRegion := by
  intro z hz
  exact ⟨⟨hz.2, hz.1.2.2.2⟩, fordRegion_subset_closedSecondSector hz.1⟩

private theorem
    SpecialPeriods.Triangle.circularDoubleRegion_and_norm_add_one_iff_halfFordRegion (z : ℍ) :
    z ∈ circularDoubleRegion ∧ 1 ≤ ‖(z : ℂ) + 1‖ ↔ z ∈ halfFordRegion := by
  constructor
  · rintro ⟨hz, hn⟩
    refine ⟨⟨hz.2.1, ?_, hn, hz.1.2⟩, hz.1.1⟩
    linarith [hz.1.1, stripRight_pos]
  · intro hz
    exact ⟨halfFordRegion_subset_circularDoubleRegion hz, hz.1.2.2.1⟩

private theorem SpecialPeriods.Triangle.halfFordRegion_eq_circularDoubleRegion_inter :
    halfFordRegion = circularDoubleRegion ∩ {z | 1 ≤ ‖(z : ℂ) + 1‖} := by
  ext z
  exact (circularDoubleRegion_and_norm_add_one_iff_halfFordRegion z).symm

private theorem SpecialPeriods.Triangle.fordRegion_left_mem_circularDoubleRegion (z : ℍ)
    (hz : z ∈ fordRegion) (hx : z.re ≤ -(1 / 2)) : z ∈ circularDoubleRegion :=
  halfFordRegion_subset_circularDoubleRegion ⟨hz, hx⟩

private theorem SpecialPeriods.Triangle.circleReflection_image_halfFordRegion :
    circleReflection '' halfFordRegion = circularDoubleRegion ∩ {z | ‖(z : ℂ) + 1‖ ≤ 1} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine
      ⟨circleReflection_mapsTo_circularDoubleRegion
          (halfFordRegion_subset_circularDoubleRegion hw),
        ?_⟩
    change ‖(circleReflection w : ℂ) + 1‖ ≤ 1
    rw [circleReflection_add_one_norm]
    exact (div_le_one (norm_pos_iff.mpr (denominatorOne_ne_zero w))).mpr hw.1.2.2.1
  · rintro ⟨hz, hn⟩
    refine ⟨circleReflection z, ?_, circleReflection_involutive z⟩
    apply (circularDoubleRegion_and_norm_add_one_iff_halfFordRegion (circleReflection z)).mp
    refine ⟨circleReflection_mapsTo_circularDoubleRegion hz, ?_⟩
    rw [circleReflection_add_one_norm]
    exact (one_le_div (norm_pos_iff.mpr (denominatorOne_ne_zero z))).mpr hn

private theorem SpecialPeriods.Triangle.circularDoubleRegion_eq_halfFordRegion_union_circle :
    circularDoubleRegion = halfFordRegion ∪ circleReflection '' halfFordRegion := by
  rw [circleReflection_image_halfFordRegion, halfFordRegion_eq_circularDoubleRegion_inter]
  ext z
  change
    z ∈ circularDoubleRegion ↔
      ((z ∈ circularDoubleRegion ∧ 1 ≤ ‖(z : ℂ) + 1‖) ∨
        (z ∈ circularDoubleRegion ∧ ‖(z : ℂ) + 1‖ ≤ 1))
  constructor
  · intro hz
    rcases le_total 1 ‖(z : ℂ) + 1‖ with hn | hn
    · exact Or.inl ⟨hz, hn⟩
    · exact Or.inr ⟨hz, hn⟩
  · rintro (hz | hz) <;> exact hz.1

private theorem SpecialPeriods.Triangle.circleReflection_eq_self_of_halfFordRegion_mem (z : ℍ)
    (hz : z ∈ halfFordRegion) (hcz : circleReflection z ∈ halfFordRegion) :
    circleReflection z = z := by
  have hn : 1 ≤ ‖(circleReflection z : ℂ) + 1‖ := hcz.1.2.2.1
  rw [circleReflection_add_one_norm] at hn
  have hle := (one_le_div (norm_pos_iff.mpr (denominatorOne_ne_zero z))).mp hn
  exact (circleReflection_fixed_iff z).mpr (le_antisymm hle hz.1.2.2.1)

private theorem SpecialPeriods.Triangle.generatorOne_inv_reflections (z : ℍ) :
    generatorOneSL⁻¹ • z = circleReflection (rightReflection z) := by
  have h : generatorOneSL • circleReflection (rightReflection z) = z := by
    rw [generatorOne_reflections, circleReflection_involutive, rightReflection_involutive]
  simpa only [inv_smul_smul] using congrArg (fun w : ℍ => generatorOneSL⁻¹ • w) h.symm

private theorem SpecialPeriods.lift_neWord_weak_to_strict_mo1973_19793 {ι G α : Type*} [Group G]
    [MulAction G α] {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G) (X W : ι → Set α)
    (hXW : ∀ i, X i ⊆ W i) (hcross : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • W j ⊆ X i)
    {i j k : ι} (w : Monoid.CoprodI.NeWord H i j) (hk : j ≠ k) :
    Monoid.CoprodI.lift f w.prod • W k ⊆ X i := by
  induction w generalizing k with
  | singleton x hx => simpa using hcross hk x hx
  | @append i j m l w₁ hne w₂ ih₁
    ih₂ =>
    rw [Monoid.CoprodI.NeWord.append_prod, map_mul, SemigroupAction.mul_smul]
    exact (Set.smul_set_subset_smul_set_iff.mpr ((ih₂ hk).trans (hXW m))).trans (ih₁ hne)

private theorem SpecialPeriods.lift_neWord_closed_domain_subset_mo1973_19794 {ι G α : Type*}
    [Group G] [MulAction G α] {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G)
    (X W : ι → Set α) (D : Set α) (hXW : ∀ i, X i ⊆ W i)
    (hcross : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • W j ⊆ X i)
    (hD : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ W i) {i j : ι} (w : Monoid.CoprodI.NeWord H i j) :
    Monoid.CoprodI.lift f w.prod • D ⊆ W i := by
  induction w with
  | singleton x hx => simpa using hD _ x hx
  | @append i j k l w₁ hne w₂ _ih₁
    ih₂ =>
    rw [Monoid.CoprodI.NeWord.append_prod, map_mul, SemigroupAction.mul_smul]
    exact
      (Set.smul_set_subset_smul_set_iff.mpr ih₂).trans
        ((lift_neWord_weak_to_strict_mo1973_19793 f X W hXW hcross w₁ hne).trans (hXW i))

private theorem SpecialPeriods.lift_neWord_factor_or_strict_mo1973_19795 {ι G α : Type*} [Group G]
    [MulAction G α] {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G) (X W : ι → Set α)
    (D : Set α) (hXW : ∀ i, X i ⊆ W i)
    (hcross : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • W j ⊆ X i)
    (hD : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ W i) {i j : ι} (w : Monoid.CoprodI.NeWord H i j) :
    (∃ x : H i, w.prod = Monoid.CoprodI.of x) ∨ Monoid.CoprodI.lift f w.prod • D ⊆ X i := by
  cases w with
  | singleton x hx => exact Or.inl ⟨x, Monoid.CoprodI.NeWord.prod_singleton x hx⟩
  | @append i j k l w₁ hne w₂ =>
    right
    rw [Monoid.CoprodI.NeWord.append_prod, map_mul, SemigroupAction.mul_smul]
    exact
      (Set.smul_set_subset_smul_set_iff.mpr
            (lift_neWord_closed_domain_subset_mo1973_19794 f X W D hXW hcross hD w₂)).trans
        (lift_neWord_weak_to_strict_mo1973_19793 f X W hXW hcross w₁ hne)

private theorem SpecialPeriods.gluing_cyclicPowerHom_two_mo1973_19796 {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (2 : ZMod n)) = a ^ 2 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (2 : ℤ)

private theorem SpecialPeriods.gluing_cyclicPowerHom_three_mo1973_19797 {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (3 : ZMod n)) = a ^ 3 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (3 : ℤ)

private theorem SpecialPeriods.cyclicThree_closed_subset_mo1973_19798 {G α : Type*} [Group G]
    [MulAction G α] (a : G) (ha : a ^ 3 = 1) (S T : Set α) (h₁ : Set.MapsTo (fun z => a • z) S T)
    (h₂ : Set.MapsTo (fun z => a ^ 2 • z) S T) (g : Multiplicative (ZMod 3)) (hg : g ≠ 1) :
    cyclicPowerHom 3 a ha g • S ⊆ T := by
  have hc : g = Multiplicative.ofAdd (1 : ZMod 3) ∨ g = Multiplicative.ofAdd (2 : ZMod 3) :=
    (by decide :
        ∀ x : Multiplicative (ZMod 3),
          x ≠ 1 → x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2)
      g hg
  rcases hc with rfl | rfl
  · rw [cyclicPowerHom_one]
    exact Set.smul_set_subset_iff.mpr h₁
  · rw [gluing_cyclicPowerHom_two_mo1973_19796]
    exact Set.smul_set_subset_iff.mpr h₂

private theorem SpecialPeriods.cyclicFour_closed_subset_mo1973_19799 {G α : Type*} [Group G]
    [MulAction G α] (b : G) (hb : b ^ 4 = 1) (S T : Set α) (h₁ : Set.MapsTo (fun z => b • z) S T)
    (h₂ : Set.MapsTo (fun z => b ^ 2 • z) S T) (h₃ : Set.MapsTo (fun z => b ^ 3 • z) S T)
    (g : Multiplicative (ZMod 4)) (hg : g ≠ 1) : cyclicPowerHom 4 b hb g • S ⊆ T := by
  have hc :
    g = Multiplicative.ofAdd (1 : ZMod 4) ∨
      g = Multiplicative.ofAdd (2 : ZMod 4) ∨ g = Multiplicative.ofAdd (3 : ZMod 4) :=
    (by decide :
        ∀ x : Multiplicative (ZMod 4),
          x ≠ 1 →
            x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2 ∨ x = Multiplicative.ofAdd 3)
      g hg
  rcases hc with rfl | rfl | rfl
  · rw [cyclicPowerHom_one]
    exact Set.smul_set_subset_iff.mpr h₁
  · rw [gluing_cyclicPowerHom_two_mo1973_19796]
    exact Set.smul_set_subset_iff.mpr h₂
  · rw [gluing_cyclicPowerHom_three_mo1973_19797]
    exact Set.smul_set_subset_iff.mpr h₃

private theorem SpecialPeriods.cyclic_eq_generator_pow_val_mo1973_19800 {n : ℕ} [NeZero n]
    (x : Multiplicative (ZMod n)) : x = Multiplicative.ofAdd (1 : ZMod n) ^ x.toAdd.val := by
  change x.toAdd = x.toAdd.val • (1 : ZMod n)
  simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

private theorem
    SpecialPeriods.triangleLift_eq_generator_pow_of_closed_domain_mem {G α : Type*} [Group G]
    [MulAction G α] (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y XB YB D : Set α)
    (hXXB : X ⊆ XB) (hYYB : Y ⊆ YB) (ha₁ : Set.MapsTo (fun z => a • z) YB X)
    (ha₂ : Set.MapsTo (fun z => a ^ 2 • z) YB X) (hb₁ : Set.MapsTo (fun z => b • z) XB Y)
    (hb₂ : Set.MapsTo (fun z => b ^ 2 • z) XB Y) (hb₃ : Set.MapsTo (fun z => b ^ 3 • z) XB Y)
    (hDa₁ : Set.MapsTo (fun z => a • z) D XB) (hDa₂ : Set.MapsTo (fun z => a ^ 2 • z) D XB)
    (hDb₁ : Set.MapsTo (fun z => b • z) D YB) (hDb₂ : Set.MapsTo (fun z => b ^ 2 • z) D YB)
    (hDb₃ : Set.MapsTo (fun z => b ^ 3 • z) D YB) (hDX : Disjoint D X) (hDY : Disjoint D Y)
    (g : TriangleGroup) {z : α} (hz : z ∈ D) (hgz : triangleLift a b ha hb g • z ∈ D) :
    (∃ n : ℕ, n < 3 ∧ g = triangleGenerator₁ ^ n) ∨
      (∃ n : ℕ, n < 4 ∧ g = triangleGenerator₂ ^ n) := by
  classical
  by_cases hg : g = 1
  · exact Or.inl ⟨0, by decide, by simpa using hg⟩
  let H : Bool → Type := fun i => cond i (Multiplicative (ZMod 4)) (Multiplicative (ZMod 3))
  let : ∀ i, Group (H i) :=
    Bool.rec (inferInstance : Group (Multiplicative (ZMod 3)))
      (inferInstance : Group (Multiplicative (ZMod 4)))
  let f : ∀ i, H i →* G := fun i =>
    match i with
    | false => cyclicPowerHom 3 a ha
    | true => cyclicPowerHom 4 b hb
  let toI : TriangleGroup →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := Bool.false))
      (Monoid.CoprodI.of (M := H) (i := Bool.true))
  let fromI : Monoid.CoprodI H →* TriangleGroup :=
    Monoid.CoprodI.lift fun i =>
      match i with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id TriangleGroup := by
    apply triangle_hom_ext
    · simp [toI, fromI, triangleGenerator₁]
    · simp [toI, fromI, triangleGenerator₂]
  have hto_ne : toI g ≠ 1 := by
    intro h
    apply hg
    calc
      g = fromI (toI g) := (DFunLike.congr_fun hleft g).symm
      _ = 1 := by rw [h, map_one]
  have hrepresentation : triangleLift a b ha hb = (Monoid.CoprodI.lift f).comp toI := by
    apply triangle_hom_ext
    · simp only [triangleLift_generator₁, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 3 a ha).symm
    · simp only [triangleLift_generator₂, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 4 b hb).symm
  let U : Bool → Set α := fun i => cond i Y X
  let W : Bool → Set α := fun i => cond i YB XB
  have hUW : ∀ i, U i ⊆ W i := by
    intro i
    cases i
    · exact hXXB
    · exact hYYB
  have hcross : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • W j ⊆ U i := by
    intro i j hij h hh
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact cyclicThree_closed_subset_mo1973_19798 a ha YB X ha₁ ha₂ h hh
    · exact cyclicFour_closed_subset_mo1973_19799 b hb XB Y hb₁ hb₂ hb₃ h hh
    · exact (hij rfl).elim
  have hstart : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ W i := by
    intro i h hh
    cases i
    · exact cyclicThree_closed_subset_mo1973_19798 a ha D XB hDa₁ hDa₂ h hh
    · exact cyclicFour_closed_subset_mo1973_19799 b hb D YB hDb₁ hDb₂ hDb₃ h hh
  let : (i : Bool) → DecidableEq (H i) := fun _ => Classical.decEq _
  let r := Monoid.CoprodI.Word.equiv (M := H) (toI g)
  have hr : r.prod = toI g := (Monoid.CoprodI.Word.equiv (M := H)).symm_apply_apply (toI g)
  have hr_ne : r ≠ Monoid.CoprodI.Word.empty := by
    intro h
    apply hto_ne
    rw [← hr, h, Monoid.CoprodI.Word.prod_empty]
  obtain ⟨i, j, w, hw⟩ := Monoid.CoprodI.NeWord.of_word r hr_ne
  have hwprod : w.prod = toI g := by
    change w.toWord.prod = toI g
    rw [hw]
    exact hr
  rcases lift_neWord_factor_or_strict_mo1973_19795 f U W D hUW hcross hstart w with ⟨x, hx⟩ |
    himage
  · have hfrom : fromI (Monoid.CoprodI.of x) = g := by
      rw [← hx, hwprod]
      exact DFunLike.congr_fun hleft g
    cases i
    · left
      refine ⟨x.toAdd.val, ZMod.val_lt x.toAdd, ?_⟩
      calc
        g = Monoid.Coprod.inl x := by simpa [fromI] using hfrom.symm
        _ = triangleGenerator₁ ^ x.toAdd.val := by
          rw [triangleGenerator₁, ← map_pow]
          exact congrArg Monoid.Coprod.inl (cyclic_eq_generator_pow_val_mo1973_19800 x)
    · right
      refine ⟨x.toAdd.val, ZMod.val_lt x.toAdd, ?_⟩
      calc
        g = Monoid.Coprod.inr x := by simpa [fromI] using hfrom.symm
        _ = triangleGenerator₂ ^ x.toAdd.val := by
          rw [triangleGenerator₂, ← map_pow]
          exact congrArg Monoid.Coprod.inr (cyclic_eq_generator_pow_val_mo1973_19800 x)
  · have heval : triangleLift a b ha hb g = Monoid.CoprodI.lift f (toI g) :=
      DFunLike.congr_fun hrepresentation g
    have hstrict : triangleLift a b ha hb g • z ∈ U i := by
      rw [heval, ← hwprod]
      exact Set.smul_set_subset_iff.mp himage hz
    cases i
    · exact (hDX.le_bot ⟨hgz, hstrict⟩).elim
    · exact (hDY.le_bot ⟨hgz, hstrict⟩).elim

private theorem SpecialPeriods.Triangle.circularDoubleRegion_return_generator_pow
    (g : SpecialPeriods.TriangleGroup) {z : ℍ} (hz : z ∈ circularDoubleRegion)
    (hgz : SpecialPeriods.triangleGeometricRepresentation g z ∈ circularDoubleRegion) :
    (∃ n : ℕ, n < 3 ∧ g = SpecialPeriods.triangleGenerator₁ ^ n) ∨
      (∃ n : ℕ, n < 4 ∧ g = SpecialPeriods.triangleGenerator₂ ^ n) := by
  exact
    SpecialPeriods.triangleLift_eq_generator_pow_of_closed_domain_mem generatorOnePerm
      generatorTwoPerm generatorOnePerm_cube generatorTwoPerm_fourth firstExcluded secondExcluded
      firstWeakExcluded secondWeakExcluded circularDoubleRegion
      firstExcluded_subset_firstWeakExcluded secondExcluded_subset_secondWeakExcluded
      (fun _ hw => generatorOnePerm_firstSector (secondWeakExcluded_subset_firstSector hw))
      (fun _ hw => generatorOnePerm_sq_firstSector (secondWeakExcluded_subset_firstSector hw))
      (fun _ hw => generatorTwoPerm_secondSector (firstWeakExcluded_subset_secondSector hw))
      (fun _ hw => generatorTwoPerm_sq_secondSector (firstWeakExcluded_subset_secondSector hw))
      (fun _ hw => generatorTwoPerm_cube_secondSector (firstWeakExcluded_subset_secondSector hw))
      (fun _ hw => generatorOne_closedFirstSector hw.1)
      (fun z hw => by
        change (generatorOnePerm ^ 2) z ∈ firstWeakExcluded
        rw [generatorOnePerm_pow_apply]
        exact generatorOne_sq_closedFirstSector hw.1)
      (fun _ hw => generatorTwo_closedSecondSector hw.2)
      (fun z hw => by
        change (generatorTwoPerm ^ 2) z ∈ secondWeakExcluded
        rw [generatorTwoPerm_pow_apply]
        exact generatorTwo_sq_closedSecondSector hw.2)
      (fun z hw => by
        change (generatorTwoPerm ^ 3) z ∈ secondWeakExcluded
        rw [generatorTwoPerm_pow_apply]
        exact generatorTwo_cube_closedSecondSector hw.2)
      circularDoubleRegion_disjoint_firstExcluded circularDoubleRegion_disjoint_secondExcluded g
      hz hgz

private theorem SpecialPeriods.Triangle.circularDoubleRegion_orbit_point
    (g : SpecialPeriods.TriangleGroup) {z : ℍ} (hz : z ∈ circularDoubleRegion)
    (hgz : SpecialPeriods.triangleGeometricRepresentation g z ∈ circularDoubleRegion) :
    SpecialPeriods.triangleGeometricRepresentation g z = z ∨
      SpecialPeriods.triangleGeometricRepresentation g z = circleReflection z := by
  rcases circularDoubleRegion_return_generator_pow g hz hgz with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · simp only [map_pow, SpecialPeriods.triangleGeometricRepresentation_generator₁,
      generatorOnePerm_pow_apply] at hgz ⊢
    interval_cases n
    · exact Or.inl (by simp)
    · right
      simp only [pow_one] at hgz ⊢
      exact generatorOne_closed_return z hz hgz
    · exact Or.inr (generatorOne_sq_closed_return z hz hgz)
  · simp only [map_pow, SpecialPeriods.triangleGeometricRepresentation_generator₂,
      generatorTwoPerm_pow_apply] at hgz ⊢
    interval_cases n
    · exact Or.inl (by simp)
    · right
      simp only [pow_one] at hgz ⊢
      exact generatorTwo_closed_return z hz hgz
    · exact Or.inr (generatorTwo_sq_closed_return z hz hgz)
    · exact Or.inr (generatorTwo_cube_closed_return z hz hgz)

private theorem SpecialPeriods.Triangle.circularDoubleRegion_orbit_point_of_eq
    (g : SpecialPeriods.TriangleGroup) {z w : ℍ} (hz : z ∈ circularDoubleRegion)
    (hw : w ∈ circularDoubleRegion)
    (hzw : SpecialPeriods.triangleGeometricRepresentation g z = w) :
    w = z ∨ w = circleReflection z := by
  simpa only [hzw] using circularDoubleRegion_orbit_point g hz (hzw ▸ hw)

private def SpecialPeriods.Triangle.circularHalfPoint_mo1973_19807 (z : ℍ) : ℍ := by
  classical exact if 1 ≤ ‖(z : ℂ) + 1‖ then z else circleReflection z

private theorem SpecialPeriods.Triangle.circularHalfPoint_of_half_mo1973_19808 {z : ℍ}
    (hz : z ∈ halfFordRegion) : circularHalfPoint_mo1973_19807 z = z := by
  simp only [circularHalfPoint_mo1973_19807, ite_eq_left hz.1.2.2.1]

private theorem SpecialPeriods.Triangle.circularHalfPoint_circle_of_half_mo1973_19809 {z : ℍ}
    (hz : z ∈ halfFordRegion) : circularHalfPoint_mo1973_19807 (circleReflection z) = z := by
  by_cases hn : 1 ≤ ‖(circleReflection z : ℂ) + 1‖
  · rw [circularHalfPoint_mo1973_19807, ite_eq_left hn]
    apply circleReflection_eq_self_of_halfFordRegion_mem z hz
    exact
      (circularDoubleRegion_and_norm_add_one_iff_halfFordRegion _).mp
        ⟨circleReflection_mapsTo_circularDoubleRegion
            (halfFordRegion_subset_circularDoubleRegion hz),
          hn⟩
  · rw [circularHalfPoint_mo1973_19807, ite_eq_right hn, circleReflection_involutive z]

private theorem SpecialPeriods.Triangle.circularHalfPoint_circle_mo1973_19810 {z : ℍ}
    (hz : z ∈ circularDoubleRegion) :
    circularHalfPoint_mo1973_19807 (circleReflection z) = circularHalfPoint_mo1973_19807 z := by
  rw [circularDoubleRegion_eq_halfFordRegion_union_circle] at hz
  rcases hz with hz | ⟨w, hw, rfl⟩
  · rw [circularHalfPoint_circle_of_half_mo1973_19809 hz,
      circularHalfPoint_of_half_mo1973_19808 hz]
  · rw [circleReflection_involutive w, circularHalfPoint_of_half_mo1973_19808 hw,
      circularHalfPoint_circle_of_half_mo1973_19809 hw]

private def SpecialPeriods.Triangle.fordHalfPoint_mo1973_19811 (z : ℍ) : ℍ := by
  classical exact if z.re ≤ -(1 / 2) then z else rightReflection z

private theorem SpecialPeriods.Triangle.fordHalfPoint_mem_mo1973_19812 {z : ℍ}
    (hz : z ∈ fordRegion) : fordHalfPoint_mo1973_19811 z ∈ halfFordRegion := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [fordHalfPoint_mo1973_19811, ite_eq_left hx]
    exact ⟨hz, hx⟩
  · rw [fordHalfPoint_mo1973_19811, ite_eq_right hx]
    refine ⟨rightReflection_mapsTo_fordRegion hz, ?_⟩
    change (rightReflection z).re ≤ -(1 / 2)
    rw [rightReflection_re]
    have hh := lt_of_not_ge hx
    linarith

private theorem SpecialPeriods.Triangle.eq_or_reflection_of_fordHalfPoint_eq_mo1973_19813
    {z w : ℍ} (h : fordHalfPoint_mo1973_19811 w = fordHalfPoint_mo1973_19811 z) :
    w = z ∨ w = rightReflection z := by
  by_cases hz : z.re ≤ -(1 / 2) <;> by_cases hw : w.re ≤ -(1 / 2)
  · left
    simpa only [fordHalfPoint_mo1973_19811, ite_eq_left hz, ite_eq_left hw] using h
  · right
    have hh : rightReflection w = z := by
      simpa only [fordHalfPoint_mo1973_19811, ite_eq_left hz, ite_eq_right hw] using h
    have he := congrArg rightReflection hh
    simpa only [rightReflection_involutive w] using he
  · right
    simpa only [fordHalfPoint_mo1973_19811, ite_eq_right hz, ite_eq_left hw] using h
  · left
    apply rightReflection.injective
    simpa only [fordHalfPoint_mo1973_19811, ite_eq_right hz, ite_eq_right hw] using h

private def SpecialPeriods.Triangle.fordCircularNormalizer_mo1973_19814 (z : ℍ) :
    SpecialPeriods.TriangleGroup := by
  classical exact if z.re ≤ -(1 / 2) then 1 else SpecialPeriods.triangleGenerator₁⁻¹

private def SpecialPeriods.Triangle.fordCircularPoint_mo1973_19815 (z : ℍ) : ℍ :=
  SpecialPeriods.triangleGeometricRepresentation (fordCircularNormalizer_mo1973_19814 z) z

private theorem SpecialPeriods.Triangle.generatorOne_inv_representation_apply_mo1973_19816
    (z : ℍ) :
    SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁⁻¹ z =
      generatorOneSL⁻¹ • z := by
  rw [map_inv, SpecialPeriods.triangleGeometricRepresentation_generator₁]
  change (realSLPermutation generatorOneSL)⁻¹ z = _
  rw [← map_inv]
  rfl

private theorem SpecialPeriods.Triangle.fordCircularPoint_of_left_mo1973_19817 {z : ℍ}
    (hz : z.re ≤ -(1 / 2)) : fordCircularPoint_mo1973_19815 z = z := by
  rw [fordCircularPoint_mo1973_19815, fordCircularNormalizer_mo1973_19814, ite_eq_left hz, map_one]
  rfl

private theorem SpecialPeriods.Triangle.fordCircularPoint_of_right_mo1973_19818 {z : ℍ}
    (hz : ¬z.re ≤ -(1 / 2)) :
    fordCircularPoint_mo1973_19815 z = circleReflection (rightReflection z) := by
  rw [fordCircularPoint_mo1973_19815, fordCircularNormalizer_mo1973_19814, ite_eq_right hz,
    generatorOne_inv_representation_apply_mo1973_19816, generatorOne_inv_reflections]

private theorem SpecialPeriods.Triangle.fordCircularPoint_mem_mo1973_19819 {z : ℍ}
    (hz : z ∈ fordRegion) : fordCircularPoint_mo1973_19815 z ∈ circularDoubleRegion := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [fordCircularPoint_of_left_mo1973_19817 hx]
    exact fordRegion_left_mem_circularDoubleRegion z hz hx
  · rw [fordCircularPoint_of_right_mo1973_19818 hx]
    apply circleReflection_mapsTo_circularDoubleRegion
    have hh := fordHalfPoint_mem_mo1973_19812 hz
    rw [fordHalfPoint_mo1973_19811, ite_eq_right hx] at hh
    exact halfFordRegion_subset_circularDoubleRegion hh

private theorem SpecialPeriods.Triangle.circularHalfPoint_fordCircularPoint_mo1973_19820 {z : ℍ}
    (hz : z ∈ fordRegion) :
    circularHalfPoint_mo1973_19807 (fordCircularPoint_mo1973_19815 z) =
      fordHalfPoint_mo1973_19811 z := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [fordCircularPoint_of_left_mo1973_19817 hx, fordHalfPoint_mo1973_19811, ite_eq_left hx]
    exact circularHalfPoint_of_half_mo1973_19808 ⟨hz, hx⟩
  · rw [fordCircularPoint_of_right_mo1973_19818 hx, fordHalfPoint_mo1973_19811, ite_eq_right hx]
    apply circularHalfPoint_circle_of_half_mo1973_19809
    have hh := fordHalfPoint_mem_mo1973_19812 hz
    simpa only [fordHalfPoint_mo1973_19811, ite_eq_right hx] using hh

private theorem SpecialPeriods.Triangle.fordHalfPoint_eq_of_orbit_mo1973_19821
    (g : SpecialPeriods.TriangleGroup) {z w : ℍ} (hz : z ∈ fordRegion) (hw : w ∈ fordRegion)
    (hzw : SpecialPeriods.triangleGeometricRepresentation g z = w) :
    fordHalfPoint_mo1973_19811 w = fordHalfPoint_mo1973_19811 z := by
  let h : SpecialPeriods.TriangleGroup :=
    fordCircularNormalizer_mo1973_19814 w * g * (fordCircularNormalizer_mo1973_19814 z)⁻¹
  have he :
    SpecialPeriods.triangleGeometricRepresentation h (fordCircularPoint_mo1973_19815 z) =
      fordCircularPoint_mo1973_19815 w := by
    dsimp only [h, fordCircularPoint_mo1973_19815]
    rw [map_mul, map_mul, map_inv]
    change
      SpecialPeriods.triangleGeometricRepresentation (fordCircularNormalizer_mo1973_19814 w)
          (SpecialPeriods.triangleGeometricRepresentation g
            ((SpecialPeriods.triangleGeometricRepresentation
                  (fordCircularNormalizer_mo1973_19814 z)).symm
              (SpecialPeriods.triangleGeometricRepresentation
                (fordCircularNormalizer_mo1973_19814 z) z))) =
        _
    rw [(SpecialPeriods.triangleGeometricRepresentation
            (fordCircularNormalizer_mo1973_19814 z)).symm_apply_apply
        z,
      hzw]
  have hor :=
    circularDoubleRegion_orbit_point_of_eq h (fordCircularPoint_mem_mo1973_19819 hz)
      (fordCircularPoint_mem_mo1973_19819 hw) he
  have hh :
    circularHalfPoint_mo1973_19807 (fordCircularPoint_mo1973_19815 w) =
      circularHalfPoint_mo1973_19807 (fordCircularPoint_mo1973_19815 z) := by
    rcases hor with hor | hor
    · exact congrArg circularHalfPoint_mo1973_19807 hor
    · rw [hor, circularHalfPoint_circle_mo1973_19810 (fordCircularPoint_mem_mo1973_19819 hz)]
  rwa [circularHalfPoint_fordCircularPoint_mo1973_19820 hw,
    circularHalfPoint_fordCircularPoint_mo1973_19820 hz] at hh

private theorem
    SpecialPeriods.Triangle.fordRegion_orbit_point_of_eq (g : SpecialPeriods.TriangleGroup)
    {z w : ℍ} (hz : z ∈ fordRegion) (hw : w ∈ fordRegion)
    (hzw : SpecialPeriods.triangleGeometricRepresentation g z = w) :
    w = z ∨ (w = rightReflection z ∧ z ∉ fordInterior) := by
  rcases
    eq_or_reflection_of_fordHalfPoint_eq_mo1973_19813
      (fordHalfPoint_eq_of_orbit_mo1973_19821 g hz hw hzw) with
    he | he
  · exact Or.inl he
  · by_cases hwz : w = z
    · exact Or.inl hwz
    · refine Or.inr ⟨he, ?_⟩
      intro hi
      have hwi : w ∈ fordInterior := he ▸ rightReflection_mapsTo_fordInterior hi
      have hg := eq_one_of_fordInterior_eq g hi hwi hzw
      apply hwz
      rw [hg, map_one] at hzw
      exact hzw.symm

private theorem SpecialPeriods.Triangle.fordRegion_boundary_cases {z : ℍ} (hz : z ∈ fordRegion)
    (hi : z ∉ fordInterior) :
    z.re = stripLeft ∨ z.re = stripRight ∨ ‖(z : ℂ) + 1‖ = 1 ∨ ‖(z : ℂ)‖ = 1 := by
  by_cases hl : stripLeft < z.re
  · by_cases hr : z.re < stripRight
    · by_cases hc : 1 < ‖(z : ℂ) + 1‖
      · right; right; right
        apply le_antisymm _ hz.2.2.2
        apply le_of_not_gt
        intro hn
        exact hi ⟨hl, hr, hc, hn⟩
      · exact Or.inr (Or.inr (Or.inl (le_antisymm (le_of_not_gt hc) hz.2.2.1)))
    · exact Or.inr (Or.inl (le_antisymm hz.2.1 (le_of_not_gt hr)))
  · exact Or.inl (le_antisymm (le_of_not_gt hl) hz.1)

private theorem SpecialPeriods.Triangle.orbitProjection_rightReflection_of_right_side_mo1973_19825
    {z : ℍ} (hz : z.re = stripRight) :
    SpecialPeriods.triangleOrbitProjection (rightReflection z) =
      SpecialPeriods.triangleOrbitProjection z := by
  have h := SpecialPeriods.triangleOrbitProjection_smul SpecialPeriods.triangleCuspGenerator z
  rw [SpecialPeriods.triangleGeometricRepresentation_cusp] at h
  change
    SpecialPeriods.triangleOrbitProjection (cuspSL • z) =
      SpecialPeriods.triangleOrbitProjection z at h
  rwa [cusp_eq_rightReflection_of_re_eq_stripRight z hz] at h

private theorem SpecialPeriods.Triangle.orbitProjection_rightReflection_boundary {z : ℍ}
    (hz : z ∈ fordRegion) (hi : z ∉ fordInterior) :
    SpecialPeriods.triangleOrbitProjection (rightReflection z) =
      SpecialPeriods.triangleOrbitProjection z := by
  rcases fordRegion_boundary_cases hz hi with hl | hr | hc | hn
  · have hr' : (rightReflection z).re = stripRight :=
      (rightReflection_re_eq_stripRight_iff z).mpr hl
    have h := orbitProjection_rightReflection_of_right_side_mo1973_19825 hr'
    rw [rightReflection_involutive z] at h
    exact h.symm
  · exact orbitProjection_rightReflection_of_right_side_mo1973_19825 hr
  · have h := SpecialPeriods.triangleOrbitProjection_smul SpecialPeriods.triangleGenerator₁ z
    rwa [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply,
      generatorOne_eq_rightReflection_of_norm_add_one z hc] at h
  · have h := SpecialPeriods.triangleOrbitProjection_smul SpecialPeriods.triangleGenerator₁⁻¹ z
    rwa [generatorOne_inv_representation_apply_mo1973_19816,
      generatorOne_inv_eq_rightReflection_of_norm z hn] at h

private theorem
    SpecialPeriods.Triangle.orbitProjection_eq_iff_fordRegion {z w : ℍ} (hz : z ∈ fordRegion)
    (hw : w ∈ fordRegion) :
    SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitProjection w ↔
      z = w ∨ (w = rightReflection z ∧ z ∉ fordInterior) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (SpecialPeriods.triangleOrbitProjection_eq_iff w z).mp h.symm
    rcases fordRegion_orbit_point_of_eq g hz hw hg with he | he
    · exact Or.inl he.symm
    · exact Or.inr he
  · rintro (rfl | ⟨he, hi⟩)
    · rfl
    · rw [he]
      exact (orbitProjection_rightReflection_boundary hz hi).symm

private theorem TriangleUniformizationGluing.exists_fordRepresentative
    (q : SpecialPeriods.TriangleOrbitSpace) :
    ∃ z : ℍ,
      z ∈ SpecialPeriods.Triangle.fordRegion ∧ SpecialPeriods.triangleOrbitProjection z = q := by
  obtain ⟨u, rfl⟩ := SpecialPeriods.triangleOrbitProjection_surjective q
  obtain ⟨g, hg⟩ := SpecialPeriods.triangle_exists_fordRegion_representative u
  exact
    ⟨SpecialPeriods.triangleGeometricRepresentation g u, hg,
      SpecialPeriods.triangleOrbitProjection_smul g u⟩

private def
    TriangleUniformizationGluing.fordRepresentative (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.Triangle.fordRegion :=
  ⟨Classical.choose (exists_fordRepresentative q),
    (Classical.choose_spec (exists_fordRepresentative q)).1⟩

@[simp]
private theorem TriangleUniformizationGluing.fordRepresentative_projection
    (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.triangleOrbitProjection (fordRepresentative q) = q :=
  (Classical.choose_spec (exists_fordRepresentative q)).2

private theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_eq_of_projection_eq
    (D : TriangleUniformizationGluing.BoundaryMap) {z w : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) (hw : w ∈ SpecialPeriods.Triangle.fordRegion)
    (he : SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitProjection w) :
    D.foldedFordMap z = D.foldedFordMap w := by
  rcases (SpecialPeriods.Triangle.orbitProjection_eq_iff_fordRegion hz hw).mp he with rfl |
    ⟨hr, hi⟩
  · rfl
  · rw [hr, D.foldedFordMap_rightReflection_boundary hz hi]

private def TriangleUniformizationGluing.BoundaryMap.quotientMap
    (D : TriangleUniformizationGluing.BoundaryMap) (q : SpecialPeriods.TriangleOrbitSpace) : ℂ :=
  D.foldedFordMap (TriangleUniformizationGluing.fordRepresentative q)

private theorem TriangleUniformizationGluing.BoundaryMap.quotientMap_projection
    (D : TriangleUniformizationGluing.BoundaryMap) (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) :
    D.quotientMap (SpecialPeriods.triangleOrbitProjection z) = D.foldedFordMap z :=
  D.foldedFordMap_eq_of_projection_eq (TriangleUniformizationGluing.fordRepresentative _).property
    hz (TriangleUniformizationGluing.fordRepresentative_projection _)

private def TriangleUniformizationGluing.BoundaryMap.upstairsMap
    (D : TriangleUniformizationGluing.BoundaryMap) (z : ℍ) : ℂ :=
  D.quotientMap (SpecialPeriods.triangleOrbitProjection z)

private theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_of_mem
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) : D.upstairsMap z = D.foldedFordMap z :=
  D.quotientMap_projection z hz

@[simp]
private theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_smul
    (D : TriangleUniformizationGluing.BoundaryMap) (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    D.upstairsMap (SpecialPeriods.triangleGeometricRepresentation g z) = D.upstairsMap z := by
  change
    D.quotientMap
        (SpecialPeriods.triangleOrbitProjection
          (SpecialPeriods.triangleGeometricRepresentation g z)) =
      _
  rw [SpecialPeriods.triangleOrbitProjection_smul]
  rfl

private theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_eqOn_translate
    (D : TriangleUniformizationGluing.BoundaryMap) (g : SpecialPeriods.TriangleGroup) :
    Set.EqOn D.upstairsMap
      (fun z => D.foldedFordMap (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z))
      (SpecialPeriods.triangleGeometricRepresentation g '' SpecialPeriods.Triangle.fordRegion) := by
  rintro z ⟨w, hw, rfl⟩
  change
    D.upstairsMap (SpecialPeriods.triangleGeometricRepresentation g w) =
      D.foldedFordMap
        (SpecialPeriods.triangleGeometricRepresentation g⁻¹
          (SpecialPeriods.triangleGeometricRepresentation g w))
  rw [D.upstairsMap_smul, map_inv]
  change
    D.upstairsMap w =
      D.foldedFordMap
        ((SpecialPeriods.triangleGeometricRepresentation g).symm
          (SpecialPeriods.triangleGeometricRepresentation g w))
  rw [(SpecialPeriods.triangleGeometricRepresentation g).symm_apply_apply w,
    D.upstairsMap_of_mem hw]

end Mathoverflow1973

end
