/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.FibreTopology
public import LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap2
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen1
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Foundations.Core4
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods2
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
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Elliptic.Core4
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldGluing2
import all LeanPool.HopfProblem.Foundations.FibreTopology
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap2

/-!
# Hopf problem: threefold · special periods 8

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

private theorem SpecialPeriods.CuspGlobalOverlap.familyMap_isLocalDiffeomorph
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI := C.chartedSpace
    letI := D.chartedSpace (familyCovering D)
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (familyMap C D hrcap) := by
  let := C.periods.totalChartedSpace
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := C.chartedSpace
  let := D.chartedSpace (familyCovering D)
  have hmap :=
    HolomorphicPeriodMap.periodPullbackMap_isLocalDiffeomorph C.periods D.periods
      (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap) hperiod
      (SpecialPeriods.CuspFamily.logBaseToRegular_isLocalDiffeomorph C.radius hrcap)
  have hq :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.quotient := by
    let := D.totalAction
    exact
      CoveringQuotient.project_isLocalDiffeomorph (D.quotientCoveringMap (familyCovering D))
        D.totalAction_holomorphic
  apply
    isLocalDiffeomorph_of_comp_surjective (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      C.quotient_isLocalDiffeomorph C.quotient_surjective
  intro x
  exact
    (hmap x).comp (K := (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))) (P := D.Space)
      (hq (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap x.1, x.2))

private theorem SpecialPeriods.CuspGlobalOverlap.familyMapInto_isLocalDiffeomorph
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI := C.chartedSpace
    letI := D.chartedSpace (familyCovering D)
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (familyMapInto C D hrcap) := by
  let := C.chartedSpace
  let := D.chartedSpace (familyCovering D)
  exact
    isLocalDiffeomorph_codRestrictOpens (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (familyMap_isLocalDiffeomorph C D hrcap hperiod) (familyPatch C D hrcap)
      (familyMap_mem_patch C D hrcap)

private def SpecialPeriods.CuspGlobalOverlap.familyBiholomorph (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI := C.chartedSpace
    letI := D.chartedSpace (familyCovering D)
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) C.Space (familyPatch C D hrcap) ω := by
  letI := C.chartedSpace
  letI := D.chartedSpace (familyCovering D)
  exact
    (familyMapInto_isLocalDiffeomorph C D hrcap hperiod).diffeomorphOfBijective
      (familyMapInto_bijective C D hrcap)

private def SpecialPeriods.CuspGlobalOverlap.compactProjection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    D.Space → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  compactBase ∘ D.projection

private def
    SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    Diffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (CuspUniformization.PuncturedQuotient C.correction C.radius) (familyPatch C D hrcap) ω := by
  letI := C.chartedSpace
  letI :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  letI := D.chartedSpace (familyCovering D)
  exact C.puncturedFamilyBiholomorph.symm.trans (familyBiholomorph C D hrcap hperiod)

private theorem SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph_cover
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspUniformization.LogCover C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    (puncturedBiholomorph C D hrcap hperiod
          (CuspUniformization.puncturedCuspCover C.correction C.radius x) :
        D.Space) =
      familyMap C D hrcap (C.iteratedCover x) := by
  let := C.chartedSpace
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  change
    familyMap C D hrcap
        (C.puncturedFamilyBiholomorph.symm
          (CuspUniformization.puncturedCuspCover C.correction C.radius x)) =
      _
  rw [← C.puncturedFamilyBiholomorph_iteratedCover, Diffeomorph.symm_apply_apply]

private theorem SpecialPeriods.CuspGlobalOverlap.familyMap_compactProjection_mem_chart
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (x : C.Space) :
    compactProjection D (familyMap C D hrcap x) ∈
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source := by
  obtain ⟨a, rfl⟩ := C.quotient_surjective x
  exact compactBase_baseCover_mem_chart C.radius hrcap a.1

private theorem SpecialPeriods.CuspGlobalOverlap.familyMap_compactProjection_coordinate
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (x : C.Space) :
    SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
        (compactProjection D (familyMap C D hrcap x)) =
      (C.projection x : ℂ) := by
  obtain ⟨a, rfl⟩ := C.quotient_surjective x
  exact cuspFullChart_compactBase_baseCover C.radius hrcap a.1

private theorem SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph_coordinate
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspUniformization.PuncturedQuotient C.correction C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
        (compactProjection D (puncturedBiholomorph C D hrcap hperiod x)) =
      CuspQuotient.projection C.correction C.radius x := by
  let := C.chartedSpace
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  obtain ⟨y, rfl⟩ := C.puncturedFamilyBiholomorph.surjective x
  change
    SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
        (compactProjection D
          (familyMap C D hrcap
            (C.puncturedFamilyBiholomorph.symm (C.puncturedFamilyBiholomorph y)))) =
      _
  rw [Diffeomorph.symm_apply_apply, familyMap_compactProjection_coordinate]
  exact (C.puncturedFamilyBiholomorph_preserves_base y).symm

private theorem SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph_base_mem_chart
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspUniformization.PuncturedQuotient C.correction C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    compactProjection D (puncturedBiholomorph C D hrcap hperiod x) ∈
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source := by
  let := C.chartedSpace
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  exact familyMap_compactProjection_mem_chart C D hrcap (C.puncturedFamilyBiholomorph.symm x)

private theorem SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph_preserves_base
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspUniformization.PuncturedQuotient C.correction C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    compactProjection D (puncturedBiholomorph C D hrcap hperiod x) =
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm
        (CuspQuotient.projection C.correction C.radius x) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [← puncturedBiholomorph_coordinate C D hrcap hperiod x]
  exact
    ((SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).left_inv
        (puncturedBiholomorph_base_mem_chart C D hrcap hperiod x)).symm

private theorem SpecialPeriods.CuspGlobalOverlap.logBase_nonempty (r : ℝ) (hr : 0 < r) :
    Nonempty (SpecialPeriods.CuspFamily.LogBase r) := by
  have hhalf : 0 < r / 2 := half_pos hr
  have hnorm : ‖((r / 2 : ℝ) : ℂ)‖ < r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhalf]
    linarith
  let t : SpecialPeriods.CuspFamily.puncturedDisc r :=
    ⟨((r / 2 : ℝ) : ℂ),
      (SpecialPeriods.CuspFamily.mem_puncturedDisc r _).mpr
        ⟨hnorm, Complex.ofReal_ne_zero.mpr hhalf.ne'⟩⟩
  obtain ⟨s, _⟩ := SpecialPeriods.CuspFamily.baseExponential_surjective r t
  exact ⟨s⟩

private theorem SpecialPeriods.CuspGlobalOverlap.cyclicSpace_nonempty
    (C : SpecialPeriods.CuspFamily.Data) : Nonempty C.Space := by
  obtain ⟨s⟩ := logBase_nonempty C.radius C.radius_pos
  exact ⟨C.quotient (s, 0)⟩

private theorem SpecialPeriods.CuspGlobalOverlap.puncturedSpace_nonempty
    (C : SpecialPeriods.CuspFamily.Data) :
    Nonempty (CuspUniformization.PuncturedQuotient C.correction C.radius) := by
  obtain ⟨s⟩ := logBase_nonempty C.radius C.radius_pos
  exact ⟨CuspUniformization.puncturedCuspCover C.correction C.radius ⟨((s : ℂ), 0), s.property⟩⟩

private theorem
    SpecialPeriods.CuspGlobalOverlap.familyPatch_nonempty (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Nonempty (familyPatch C D hrcap) :=
  (cyclicSpace_nonempty C).map (familyMapInto C D hrcap)

private def
    SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    PartialDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (CuspQuotient.QuotientSpace C.correction C.radius) D.Space ω := by
  letI :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  letI := D.chartedSpace (familyCovering D)
  exact
    (opensInclusionPartialDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
          (CuspUniformization.puncturedQuotientOpen C.correction C.radius)
          (puncturedSpace_nonempty C)).symm.trans
      ((puncturedBiholomorph C D hrcap hperiod).toPartialDiffeomorph.trans
        (opensInclusionPartialDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
          (familyPatch C D hrcap) (familyPatch_nonempty C D hrcap)))

@[simp]
private theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_source
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    (cuspToRegularPartial C D hrcap hperiod).source =
      (CuspUniformization.puncturedQuotientOpen C.correction C.radius : Set _) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  simp [cuspToRegularPartial, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp]
private theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_target
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    (cuspToRegularPartial C D hrcap hperiod).target = (familyPatch C D hrcap : Set D.Space) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  simp [cuspToRegularPartial, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

private theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_source_iff
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspQuotient.QuotientSpace C.correction C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    x ∈ (cuspToRegularPartial C D hrcap hperiod).source ↔
      CuspQuotient.projection C.correction C.radius x ≠ 0 := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [cuspToRegularPartial_source]
  rfl

private theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_target_iff
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (y : D.Space) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    y ∈ (cuspToRegularPartial C D hrcap hperiod).target ↔
      compactProjection D y ∈
          (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source ∧
        ‖SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (compactProjection D y)‖ <
          C.radius := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [cuspToRegularPartial_target]
  exact mem_basePatch_iff C.radius hrcap (D.projection y)

private theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_apply
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspQuotient.QuotientSpace C.correction C.radius)
    (hx : x ∈ CuspUniformization.puncturedQuotientOpen C.correction C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    cuspToRegularPartial C D hrcap hperiod x =
      (puncturedBiholomorph C D hrcap hperiod ⟨x, hx⟩ : D.Space) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  let e :=
    (CuspUniformization.puncturedQuotientOpen C.correction
          C.radius).openPartialHomeomorphSubtypeCoe
      (puncturedSpace_nonempty C)
  have he : e.symm x = ⟨x, hx⟩ :=
    e.left_inv (Set.mem_univ (⟨x, hx⟩ : CuspUniformization.PuncturedQuotient _ _))
  change (puncturedBiholomorph C D hrcap hperiod (e.symm x) : D.Space) = _
  rw [he]

private theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_preserves_base
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspQuotient.QuotientSpace C.correction C.radius)
    (hx : x ∈ CuspUniformization.puncturedQuotientOpen C.correction C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    compactProjection D (cuspToRegularPartial C D hrcap hperiod x) =
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm
        (CuspQuotient.projection C.correction C.radius x) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [cuspToRegularPartial_apply C D hrcap hperiod x hx]
  exact puncturedBiholomorph_preserves_base C D hrcap hperiod ⟨x, hx⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial
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
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    letI :=
      CuspQuotient.chartedSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_pos
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_lt_one
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).holomorphic
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).smallDrift
    letI :=
      ((sphereRegularData π hπ h₀ h₁)).chartedSpace
        (familyCovering (sphereRegularData π hπ h₀ h₁))
    PartialDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (CuspQuotient.QuotientSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius)
      ((sphereRegularData π hπ h₀ h₁)).Space ω :=
  cuspToRegularPartial (sphereCuspData π hπ h₀ h₁ r hr hrD) (sphereRegularData π hπ h₀ h₁) hrcap
    (spherePeriod_agreement π hπ h₀ h₁ r hr hrD hrcap)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial_source_iff
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
    (x :
      CuspQuotient.QuotientSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius) :
    letI :=
      CuspQuotient.chartedSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_pos
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_lt_one
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).holomorphic
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).smallDrift
    letI :=
      ((sphereRegularData π hπ h₀ h₁)).chartedSpace
        (familyCovering (sphereRegularData π hπ h₀ h₁))
    x ∈ (sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap).source ↔
      CuspQuotient.projection ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
          ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius x ≠
        0 :=
  cuspToRegularPartial_source_iff (sphereCuspData π hπ h₀ h₁ r hr hrD)
    (sphereRegularData π hπ h₀ h₁) hrcap (spherePeriod_agreement π hπ h₀ h₁ r hr hrD hrcap) x

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial_target_iff
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
    (y : ((sphereRegularData π hπ h₀ h₁)).Space) :
    letI :=
      CuspQuotient.chartedSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_pos
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_lt_one
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).holomorphic
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).smallDrift
    letI :=
      ((sphereRegularData π hπ h₀ h₁)).chartedSpace
        (familyCovering (sphereRegularData π hπ h₀ h₁))
    y ∈ (sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap).target ↔
      compactProjection (sphereRegularData π hπ h₀ h₁) y ∈
          (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source ∧
        ‖SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (compactProjection (sphereRegularData π hπ h₀ h₁) y)‖ <
          r :=
  cuspToRegularPartial_target_iff (sphereCuspData π hπ h₀ h₁ r hr hrD)
    (sphereRegularData π hπ h₀ h₁) hrcap (spherePeriod_agreement π hπ h₀ h₁ r hr hrD hrcap) y

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial_preserves_base
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
    (x :
      CuspQuotient.QuotientSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius)
    (hx :
      x ∈
        CuspUniformization.puncturedQuotientOpen ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
          ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius) :
    letI :=
      CuspQuotient.chartedSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_pos
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_lt_one
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).holomorphic
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).smallDrift
    letI :=
      ((sphereRegularData π hπ h₀ h₁)).chartedSpace
        (familyCovering (sphereRegularData π hπ h₀ h₁))
    compactProjection (sphereRegularData π hπ h₀ h₁)
        (sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap x) =
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm
        (CuspQuotient.projection ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
          ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius x) :=
  cuspToRegularPartial_preserves_base (sphereCuspData π hπ h₀ h₁ r hr hrD)
    (sphereRegularData π hπ h₀ h₁) hrcap (spherePeriod_agreement π hπ h₀ h₁ r hr hrD hrcap) x hx

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
@[instance_reducible]
private def SpecialPeriods.Threefold.instChartedSpace1 :
    ChartedSpace (ToricCharts.CoordinateSpace 3) SpecialCuspPiece :=
  CuspPiece.nativeChartedSpace SpecialPeriods.specialCuspData specialBaseCover
    specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
private def SpecialPeriods.Threefold.specialCuspNativeOverlap :
    PartialDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) SpecialCuspPiece SpecialRegularFamily ω :=
  SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo
    (specialBaseCover.radius Option.none) (specialBaseCover.radius_pos Option.none)
    specialCuspRadius_le specialBaseCover_cusp_radius_bounds.2.2.le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
private theorem
    SpecialPeriods.Threefold.specialCuspNativeOverlap_source_iff (x : SpecialCuspPiece) :
    x ∈ specialCuspNativeOverlap.source ↔
      CuspQuotient.projection SpecialPeriods.specialCuspData.correction
          (specialBaseCover.radius Option.none) x ≠
        0 :=
  SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial_source_iff
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo
    (specialBaseCover.radius Option.none) (specialBaseCover.radius_pos Option.none)
    specialCuspRadius_le specialBaseCover_cusp_radius_bounds.2.2.le x

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
private theorem
    SpecialPeriods.Threefold.specialCuspNativeOverlap_target_iff (y : SpecialRegularFamily) :
    y ∈ specialCuspNativeOverlap.target ↔
      specialRegularFamilyProjectionToBase y ∈ (punctureChart Option.none).source ∧
        ‖punctureChart Option.none (specialRegularFamilyProjectionToBase y)‖ <
          specialBaseCover.radius Option.none :=
  SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial_target_iff
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo
    (specialBaseCover.radius Option.none) (specialBaseCover.radius_pos Option.none)
    specialCuspRadius_le specialBaseCover_cusp_radius_bounds.2.2.le y

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
private theorem SpecialPeriods.Threefold.specialCuspNativeOverlap_base (x : SpecialCuspPiece)
    (hx : x ∈ specialCuspNativeOverlap.source) :
    specialRegularFamilyProjectionToBase (specialCuspNativeOverlap x) =
      specialCuspPieceProjectionToBase x :=
  SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial_preserves_base
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo
    (specialBaseCover.radius Option.none) (specialBaseCover.radius_pos Option.none)
    specialCuspRadius_le specialBaseCover_cusp_radius_bounds.2.2.le x
    ((specialCuspNativeOverlap_source_iff x).mp hx)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
private def SpecialPeriods.Threefold.specialCuspOverlap :
    PartialDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) SpecialCuspPiece SpecialRegularFamily ω :=
  (Diffeomorph.toPartialDiffeomorph
        (CuspPiece.nativeToCommon SpecialPeriods.specialCuspData specialBaseCover
            specialCuspRadius_le).symm).trans
    specialCuspNativeOverlap

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
private theorem SpecialPeriods.Threefold.specialCuspOverlap_source :
    specialCuspOverlap.source =
      specialCuspPieceProjectionToBase ⁻¹'
        (regularPatch : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  ext x
  change (x ∈ (Set.univ : Set SpecialCuspPiece) ∧ x ∈ specialCuspNativeOverlap.source) ↔ _
  simp only [Set.mem_univ, true_and]
  exact
    (specialCuspNativeOverlap_source_iff x).trans
      (CuspPiece.projectionToBase_mem_regular_iff SpecialPeriods.specialCuspData specialBaseCover
          x).symm

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
private theorem SpecialPeriods.Threefold.specialCuspOverlap_target :
    specialCuspOverlap.target =
      specialRegularFamilyProjectionToBase ⁻¹'
        (specialBaseCover.fillingPatch Option.none :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  ext y
  change
    (y ∈ specialCuspNativeOverlap.target ∧
        specialCuspNativeOverlap.symm y ∈ (Set.univ : Set SpecialCuspPiece)) ↔
      _
  simp only [Set.mem_univ, and_true]
  exact
    (specialCuspNativeOverlap_target_iff y).trans
      (specialBaseCover.mem_fillingPatch Option.none
          (specialRegularFamilyProjectionToBase y)).symm

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
private theorem SpecialPeriods.Threefold.specialCuspOverlap_base (x : SpecialCuspPiece)
    (hx : x ∈ specialCuspOverlap.source) :
    specialRegularFamilyProjectionToBase (specialCuspOverlap x) =
      specialCuspPieceProjectionToBase x :=
  specialCuspNativeOverlap_base x hx.2

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.EllipticFilling.neighborhoodPoint (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) : SpecialPeriods.Triangle.ellipticNeighborhood j :=
  (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z.val

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.neighborhoodPoint_ne_center (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    neighborhoodPoint j z ≠ SpecialPeriods.Triangle.ellipticNeighborhoodCenter j := by
  intro he
  have hc := congrArg (SpecialPeriods.Triangle.ellipticNeighborhoodChart j) he
  have hz : z.val = SpecialPeriods.discZero := by
    simpa only [neighborhoodPoint, Diffeomorph.apply_symm_apply,
      SpecialPeriods.Triangle.ellipticNeighborhoodChart_center] using hc
  exact z.property (congrArg (fun u : SpecialPeriods.Disc => (u : ℂ)) hz)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.localBase_regular (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    (neighborhoodPoint j z : ℍ) ∈ SpecialPeriods.triangleRegularLocus := by
  have hself :
    SpecialPeriods.triangleOrbitProjection (neighborhoodPoint j z) ≠
      SpecialPeriods.Triangle.ellipticOrbitCenter j :=
    fun he =>
    neighborhoodPoint_ne_center j z
      ((SpecialPeriods.Triangle.ellipticNeighborhood_projection_eq_center_iff j
            (neighborhoodPoint j z)).mp
        he)
  have hother :=
    SpecialPeriods.Triangle.ellipticNeighborhood_avoids_other j (neighborhoodPoint j z)
      (neighborhoodPoint j z).property
  apply (SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff _).mp
  apply (SpecialPeriods.triangleOrbitRegularDomain_mem_iff _).mpr
  cases j
  · exact ⟨hself, hother⟩
  · exact ⟨hother, hself⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.EllipticFilling.localBase (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) : SpecialPeriods.TriangleRegularPoint :=
  ⟨neighborhoodPoint j z, localBase_regular j z⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
private theorem SpecialPeriods.EllipticFilling.localBase_val (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    (localBase j z : ℍ) =
      ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z.val : ℍ) :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.localBase_mem_neighborhood (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    (localBase j z : ℍ) ∈ SpecialPeriods.Triangle.ellipticNeighborhood j :=
  (neighborhoodPoint j z).property

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.localBase_injective (j : Elliptic.Kind) :
    Function.Injective (localBase j) := by
  intro z w he
  have hv : (localBase j z : ℍ) = (localBase j w : ℍ) :=
    congrArg (fun u : SpecialPeriods.TriangleRegularPoint => (u : ℍ)) he
  have hn :
    (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z.val =
      (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm w.val :=
    Subtype.ext hv
  exact Subtype.ext ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm.injective hn)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.localBase_isLocalDiffeomorph (j : Elliptic.Kind) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (localBase j) := by
  have hn : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (neighborhoodPoint j) := by
    intro z
    exact
      (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) Elliptic.LogGauge.baseOpen z).comp (K := 𝓘(ℂ)) (P :=
        SpecialPeriods.Triangle.ellipticNeighborhood j)
        ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm.isLocalDiffeomorph z.val)
  have hv :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : Elliptic.LogGauge.BaseStar => (neighborhoodPoint j z : ℍ)) := by
    intro z
    exact
      (hn z).comp (K := 𝓘(ℂ)) (P := ℍ)
        (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) (SpecialPeriods.Triangle.ellipticNeighborhood j)
          (neighborhoodPoint j z))
  exact
    isLocalDiffeomorph_codRestrictOpens 𝓘(ℂ) 𝓘(ℂ) hv SpecialPeriods.triangleRegularDomain
      (localBase_regular j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.localBase_holomorphic (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (localBase j) :=
  (localBase_isLocalDiffeomorph j).contMDiff

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.localBase_continuous (j : Elliptic.Kind) :
    Continuous (localBase j) :=
  (localBase_holomorphic j).continuous

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.ellipticCenter_not_regular (j : Elliptic.Kind) :
    SpecialPeriods.Triangle.ellipticCenter j ∉ SpecialPeriods.triangleRegularLocus := by
  cases j
  · exact SpecialPeriods.triangle_centerOne_not_regular
  · exact SpecialPeriods.triangle_centerTwo_not_regular

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem
    SpecialPeriods.EllipticFilling.neighborhoodChart_ne_zero_of_regular (j : Elliptic.Kind)
    (u : SpecialPeriods.Triangle.ellipticNeighborhood j)
    (hu : (u : ℍ) ∈ SpecialPeriods.triangleRegularLocus) :
    (SpecialPeriods.Triangle.ellipticNeighborhoodChart j u : ℂ) ≠ 0 := by
  intro he
  have hchart : SpecialPeriods.Triangle.ellipticNeighborhoodChart j u = SpecialPeriods.discZero :=
    Subtype.ext he
  have huc : u = SpecialPeriods.Triangle.ellipticNeighborhoodCenter j :=
    (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).injective
      (hchart.trans (SpecialPeriods.Triangle.ellipticNeighborhoodChart_center j).symm)
  have hc : (u : ℍ) = SpecialPeriods.Triangle.ellipticCenter j := congrArg Subtype.val huc
  exact ellipticCenter_not_regular j (hc ▸ hu)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.localBase_range (j : Elliptic.Kind) :
    Set.range (localBase j) =
      {u : SpecialPeriods.TriangleRegularPoint |
        (u : ℍ) ∈ SpecialPeriods.Triangle.ellipticNeighborhood j} := by
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    exact localBase_mem_neighborhood j z
  · intro hu
    let v : SpecialPeriods.Triangle.ellipticNeighborhood j := ⟨u.val, hu⟩
    let z : Elliptic.LogGauge.BaseStar :=
      ⟨SpecialPeriods.Triangle.ellipticNeighborhoodChart j v,
        neighborhoodChart_ne_zero_of_regular j v u.property⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change
      ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm
            (SpecialPeriods.Triangle.ellipticNeighborhoodChart j v) :
          ℍ) =
        (u : ℍ)
    exact
      congrArg (fun q : SpecialPeriods.Triangle.ellipticNeighborhood j => (q : ℍ))
        ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm_apply_apply v)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.EllipticFilling.puncturedRotation (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) : Elliptic.LogGauge.BaseStar :=
  ⟨Elliptic.familyRotation j z.val, Elliptic.LogGauge.familyRotation_ne_zero j z.val z.property⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
private theorem SpecialPeriods.EllipticFilling.puncturedRotation_val (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    (puncturedRotation j z).val = Elliptic.familyRotation j z.val :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.localBase_rotation (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    localBase j (puncturedRotation j z) =
      SpecialPeriods.Triangle.ellipticGenerator j • localBase j z := by
  let := SpecialPeriods.Triangle.ellipticNeighborhoodAction j
  have he :
    (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm (Elliptic.familyRotation j z.val) =
      SpecialPeriods.Triangle.ellipticStabilizerGenerator j •
        (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z.val := by
    apply (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).injective
    change
      SpecialPeriods.Triangle.ellipticNeighborhoodChart j
          ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm
            (Elliptic.familyRotation j z.val)) =
        SpecialPeriods.Triangle.ellipticNeighborhoodChart j
          (SpecialPeriods.Triangle.ellipticStabilizerGenerator j •
            (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z.val)
    rw [Diffeomorph.apply_symm_apply, SpecialPeriods.Triangle.ellipticNeighborhoodChart_generator,
      Diffeomorph.apply_symm_apply]
  apply Subtype.ext
  exact congrArg (fun u : SpecialPeriods.Triangle.ellipticNeighborhood j => (u : ℍ)) he

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem
    SpecialPeriods.EllipticFilling.localBase_rotation_iterate (j : Elliptic.Kind) (n : ℕ)
    (z : Elliptic.LogGauge.BaseStar) :
    localBase j ((puncturedRotation j)^[n] z) =
      SpecialPeriods.Triangle.ellipticGenerator j ^ n • localBase j z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', localBase_rotation, ih, pow_succ', SemigroupAction.mul_smul]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.EllipticFilling.baseQuotient (j : Elliptic.Kind) :
    Elliptic.LogGauge.BaseStar → SpecialPeriods.TriangleRegularQuotient :=
  SpecialPeriods.triangleRegularProject ∘ localBase j

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
private theorem SpecialPeriods.EllipticFilling.baseQuotient_toOrbit (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    SpecialPeriods.triangleRegularToOrbit (baseQuotient j z) =
      SpecialPeriods.triangleOrbitProjection (localBase j z : ℍ) :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.localBase_orbit_classification (j : Elliptic.Kind)
    (g : SpecialPeriods.TriangleGroup) (z w : Elliptic.LogGauge.BaseStar)
    (h : g • localBase j z = localBase j w) :
    ∃ n : ℕ,
      n < j.order ∧
        g = SpecialPeriods.Triangle.ellipticGenerator j ^ n ∧ w = (puncturedRotation j)^[n] z := by
  have hambient : g • (localBase j z : ℍ) = (localBase j w : ℍ) := congrArg Subtype.val h
  have hg : g ∈ SpecialPeriods.Triangle.ellipticStabilizer j :=
    SpecialPeriods.Triangle.ellipticNeighborhood_return j g
      ⟨(localBase j w : ℍ), ⟨(localBase j z : ℍ), localBase_mem_neighborhood j z, hambient⟩,
        localBase_mem_neighborhood j w⟩
  obtain ⟨n, hn, rfl⟩ := (SpecialPeriods.Triangle.mem_ellipticStabilizer_iff j g).mp hg
  refine ⟨n, hn, rfl, ?_⟩
  apply localBase_injective j
  exact ((localBase_rotation_iterate j n z).trans h).symm

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.ellipticFullChart_localBase (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    SpecialPeriods.Triangle.ellipticFullChart j
        (SpecialPeriods.triangleOrbitProjection (localBase j z : ℍ)) =
      (z.val : ℂ) ^ j.order := by
  rw [localBase_val, SpecialPeriods.Triangle.ellipticFullChart_projection]
  change
    ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j
              ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z.val) :
            SpecialPeriods.Disc) :
          ℂ) ^
        j.order =
      _
  rw [Diffeomorph.apply_symm_apply]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.ellipticFullChart_baseQuotient (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    SpecialPeriods.Triangle.ellipticFullChart j
        (SpecialPeriods.triangleRegularToOrbit (baseQuotient j z)) =
      (z.val : ℂ) ^ j.order :=
  ellipticFullChart_localBase j z

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.EllipticFilling.regularBasePatch (j : Elliptic.Kind) :
    TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient :=
  ⟨SpecialPeriods.triangleRegularToOrbit ⁻¹'
      (SpecialPeriods.Triangle.ellipticNeighborhoodImage j :
        Set SpecialPeriods.TriangleOrbitSpace),
    (SpecialPeriods.Triangle.ellipticNeighborhoodImage j).isOpen.preimage
      SpecialPeriods.triangleRegularToOrbit_continuous⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.baseQuotient_mem_regularBasePatch (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) : baseQuotient j z ∈ regularBasePatch j :=
  ⟨(localBase j z : ℍ), localBase_mem_neighborhood j z, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.baseQuotient_range (j : Elliptic.Kind) :
    Set.range (baseQuotient j) =
      (regularBasePatch j : Set SpecialPeriods.TriangleRegularQuotient) := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact baseQuotient_mem_regularBasePatch j z
  · rintro ⟨u, hu, he⟩
    change
      SpecialPeriods.triangleOrbitProjection u = SpecialPeriods.triangleRegularToOrbit q at he
    have hreg : u ∈ SpecialPeriods.triangleRegularLocus := by
      apply (SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff u).mp
      rw [he]
      exact ⟨q, rfl⟩
    have hin : (⟨u, hreg⟩ : SpecialPeriods.TriangleRegularPoint) ∈ Set.range (localBase j) := by
      rw [localBase_range]
      exact hu
    obtain ⟨z, hz⟩ := hin
    refine ⟨z, SpecialPeriods.triangleRegularToOrbit_injective ?_⟩
    rw [baseQuotient_toOrbit, hz]
    exact he

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.EllipticFilling.regularBasePatch_mem_iff_compactifiedChart
    (j : Elliptic.Kind) (q : SpecialPeriods.TriangleRegularQuotient) :
    q ∈ regularBasePatch j ↔
      SpecialPeriods.triangleOpenInclusion (SpecialPeriods.triangleRegularToOrbit q) ∈
        (SpecialPeriods.Triangle.ellipticCompactifiedChart j).source := by
  rw [SpecialPeriods.Triangle.openInclusion_mem_ellipticCompactifiedChart_source,
    SpecialPeriods.Triangle.ellipticFullChart_source]
  rfl

private theorem SpecialPeriods.EllipticFilling.ellipticGenerator_dual_matrix (j : Elliptic.Kind) :
    (SpecialPeriods.triangleDualRepresentation (SpecialPeriods.Triangle.ellipticGenerator j) :
        LatticeMatrix) =
      j.matrix := by
  cases j
  · exact SpecialPeriods.triangleDualRepresentation_generator₁_matrix
  · exact SpecialPeriods.triangleDualRepresentation_generator₂_matrix

private theorem SpecialPeriods.EllipticFilling.ellipticGenerator_torus_mkQ (j : Elliptic.Kind)
    (x : Elliptic.RealCoordinates) :
    SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j)
        (standardLattice.mkQ x) =
      standardLattice.mkQ (Elliptic.flatLinear j x) := by
  rw [SpecialPeriods.triangleTorusHomeomorph_mkQ, SpecialPeriods.triangleRealEquiv_apply,
    ellipticGenerator_dual_matrix]
  rfl

private theorem SpecialPeriods.EllipticFilling.ellipticGenerator_torus_eq (j : Elliptic.Kind) :
    SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j) =
      Elliptic.flatTorusAffine j 0 := by
  apply Homeomorph.ext
  intro x
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  rw [ellipticGenerator_torus_mkQ, Elliptic.flatTorusAffine_mkQ]
  have hz : Elliptic.realCast (0 : Lattice) = 0 := by
    ext i
    simp [Elliptic.realCast]
  rw [Elliptic.flatAffine, hz, smul_zero, add_zero]

private theorem
    SpecialPeriods.EllipticFilling.flatTorusAffine_zero_iterate (j : Elliptic.Kind) (n : ℕ)
    (x : RealTorus₄) :
    (Elliptic.flatTorusAffine j 0)^[n] x =
      SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j ^ n)
        x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ',
      SpecialPeriods.triangleTorusHomeomorph_mul_apply, ellipticGenerator_torus_eq]

private theorem SpecialPeriods.EllipticFilling.zeroAction_apply {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (g : Elliptic.CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action 0 (Matrix.mulVec_zero j.matrix)
    g • x =
      ((Elliptic.familyRotation j)^[g.toAdd.val] x.1,
        SpecialPeriods.triangleTorusHomeomorph
          (SpecialPeriods.Triangle.ellipticGenerator j ^ g.toAdd.val) x.2) := by
  let := D.action 0 (Matrix.mulVec_zero j.matrix)
  rw [D.action_apply, flatTorusAffine_zero_iterate]

private theorem SpecialPeriods.EllipticFilling.zeroStarAction_coe {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (g : Elliptic.CyclicGroup j)
    (x : Elliptic.LogGauge.FamilyStar D.periods) :
    letI := Elliptic.LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
    ((g • x : Elliptic.LogGauge.FamilyStar D.periods) : D.TotalSpace) =
      ((Elliptic.familyRotation j)^[g.toAdd.val] x.1.1,
        SpecialPeriods.triangleTorusHomeomorph
          (SpecialPeriods.Triangle.ellipticGenerator j ^ g.toAdd.val) x.1.2) := by
  let := D.action 0 (Matrix.mulVec_zero j.matrix)
  let := Elliptic.LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
  rw [Elliptic.LogGauge.starAction_coe, zeroAction_apply]

private theorem SpecialPeriods.EllipticFilling.zeroStarAction_fst {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (g : Elliptic.CyclicGroup j)
    (x : Elliptic.LogGauge.FamilyStar D.periods) :
    letI := Elliptic.LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
    (g • x : Elliptic.LogGauge.FamilyStar D.periods).1.1 =
      (Elliptic.familyRotation j)^[g.toAdd.val] x.1.1 := by
  let := Elliptic.LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
  exact congrArg Prod.fst (zeroStarAction_coe D g x)

private theorem SpecialPeriods.EllipticFilling.zeroStarAction_snd {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (g : Elliptic.CyclicGroup j)
    (x : Elliptic.LogGauge.FamilyStar D.periods) :
    letI := Elliptic.LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
    (g • x : Elliptic.LogGauge.FamilyStar D.periods).1.2 =
      SpecialPeriods.triangleTorusHomeomorph
        (SpecialPeriods.Triangle.ellipticGenerator j ^ g.toAdd.val) x.1.2 := by
  let := Elliptic.LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
  exact congrArg Prod.snd (zeroStarAction_coe D g x)

private def SpecialPeriods.EllipticFilling.localTotalMap (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind) :
    Elliptic.LogGauge.FamilyStar (localPeriods P j) →
      (PeriodFamily.regularPeriods P).TotalSpace :=
  fun x => (localBase j ⟨x.1.1, x.2⟩, x.1.2)

private theorem
    SpecialPeriods.EllipticFilling.localTotalMap_injective (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind) : Function.Injective (localTotalMap P j) := by
  intro x y h
  have hb := localBase_injective j (congrArg Prod.fst h)
  apply Subtype.ext
  exact
    Prod.ext (congrArg Subtype.val hb)
      (congrArg (fun z : (PeriodFamily.regularPeriods P).TotalSpace => z.2) h)

private theorem SpecialPeriods.EllipticFilling.localTotalMap_isLocalDiffeomorph
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind) :
    letI := (localPeriods P j).totalChartedSpace
    letI := (PeriodFamily.regularPeriods P).totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (localTotalMap P j) := by
  let Q := restrictPeriods (localPeriods P j) Elliptic.LogGauge.baseOpen
  let := (localPeriods P j).totalChartedSpace
  let := (PeriodFamily.regularPeriods P).totalChartedSpace
  let := Q.totalChartedSpace
  let e := restrictFamilyBiholomorph (localPeriods P j) Elliptic.LogGauge.baseOpen
  have hm :=
    periodFamilyMap_isLocalDiffeomorph Q (PeriodFamily.regularPeriods P) (localBase j)
      (fun _ => rfl) (localBase_isLocalDiffeomorph j)
  intro x
  have h :=
    (e.symm.isLocalDiffeomorph x).comp (K := (modelWithCornersSelf ℂ Elliptic.FamilyModel)) (P :=
      (PeriodFamily.regularPeriods P).TotalSpace) (hm (e.symm x))
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq h
  apply Filter.Eventually.of_forall
  intro y
  change
    localTotalMap P j y =
      periodFamilyMap Q (PeriodFamily.regularPeriods P) (localBase j)
        ((restrictFamilyBiholomorph (localPeriods P j) Elliptic.LogGauge.baseOpen).symm y)
  rw [restrictFamilyBiholomorph_symm_apply]
  rfl

private theorem
    SpecialPeriods.EllipticFilling.puncturedRotation_iterate_coe (j : Elliptic.Kind) (n : ℕ)
    (z : Elliptic.LogGauge.BaseStar) :
    ((puncturedRotation j)^[n] z).val = (Elliptic.familyRotation j)^[n] z.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', puncturedRotation_val, ih, Function.iterate_succ_apply']

private theorem SpecialPeriods.EllipticFilling.localTotalMap_smul (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (g : Elliptic.CyclicGroup j) (x : Elliptic.LogGauge.FamilyStar (localPeriods P j)) :
    letI := Elliptic.LogGauge.starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    letI := (PeriodFamily.regularData P h₁ h₂).totalAction
    localTotalMap P j (g • x) =
      SpecialPeriods.Triangle.ellipticGenerator j ^ g.toAdd.val • localTotalMap P j x := by
  let L := localData P h₁ h₂ j
  let D := PeriodFamily.regularData P h₁ h₂
  let := Elliptic.LogGauge.starAction L 0 (Matrix.mulVec_zero j.matrix)
  let := D.totalAction
  have hb :
    (⟨(g • x : Elliptic.LogGauge.FamilyStar L.periods).1.1,
          (g • x : Elliptic.LogGauge.FamilyStar L.periods).2⟩ :
        Elliptic.LogGauge.BaseStar) =
      (puncturedRotation j)^[g.toAdd.val] ⟨x.1.1, x.2⟩ := by
    apply Subtype.ext
    exact
      (zeroStarAction_fst L g x).trans
        (puncturedRotation_iterate_coe j g.toAdd.val ⟨x.1.1, x.2⟩).symm
  apply Prod.ext
  · change
      localBase j
          ⟨(g • x : Elliptic.LogGauge.FamilyStar L.periods).1.1,
            (g • x : Elliptic.LogGauge.FamilyStar L.periods).2⟩ =
        SpecialPeriods.Triangle.ellipticGenerator j ^ g.toAdd.val • localBase j ⟨x.1.1, x.2⟩
    rw [hb, localBase_rotation_iterate]
  · exact zeroStarAction_snd L g x

private def
    SpecialPeriods.EllipticFilling.regularMap (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Elliptic.LogGauge.FamilyStar (localPeriods P j) → (PeriodFamily.regularData P h₁ h₂).Space :=
  (PeriodFamily.regularData P h₁ h₂).quotient ∘ localTotalMap P j

@[simp]
private theorem SpecialPeriods.EllipticFilling.regularMap_base (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : Elliptic.LogGauge.FamilyStar (localPeriods P j)) :
    (PeriodFamily.regularData P h₁ h₂).projection (regularMap P j h₁ h₂ x) =
      baseQuotient j ⟨x.1.1, x.2⟩ :=
  rfl

private theorem SpecialPeriods.EllipticFilling.regularMap_smul (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (g : Elliptic.CyclicGroup j) (x : Elliptic.LogGauge.FamilyStar (localPeriods P j)) :
    letI := Elliptic.LogGauge.starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    regularMap P j h₁ h₂ (g • x) = regularMap P j h₁ h₂ x := by
  let := Elliptic.LogGauge.starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
  let := (PeriodFamily.regularData P h₁ h₂).totalAction
  change
    (PeriodFamily.regularData P h₁ h₂).quotient (localTotalMap P j (g • x)) =
      (PeriodFamily.regularData P h₁ h₂).quotient (localTotalMap P j x)
  rw [localTotalMap_smul, PeriodFamily.Data.quotient_smul]

private theorem SpecialPeriods.EllipticFilling.regularMap_isLocalDiffeomorph
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    letI := (localPeriods P j).totalChartedSpace
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (regularMap P j h₁ h₂) := by
  let := (localPeriods P j).totalChartedSpace
  let := (PeriodFamily.regularPeriods P).totalChartedSpace
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  intro x
  exact
    (localTotalMap_isLocalDiffeomorph P j x).comp (K :=
      (modelWithCornersSelf ℂ Elliptic.FamilyModel)) (P :=
      (PeriodFamily.regularData P h₁ h₂).Space)
      ((PeriodFamily.regularData P h₁ h₂).quotient_isLocalDiffeomorph
        (PeriodFamily.regularCovering P h₁ h₂) (localTotalMap P j x))

private def SpecialPeriods.EllipticFilling.regularOverlap (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    TopologicalSpace.Opens (PeriodFamily.regularData P h₁ h₂).Space :=
  ⟨(PeriodFamily.regularData P h₁ h₂).projection ⁻¹'
      (regularBasePatch j : Set SpecialPeriods.TriangleRegularQuotient),
    (regularBasePatch j).isOpen.preimage (PeriodFamily.regularData P h₁ h₂).projection_continuous⟩

@[simp]
private theorem SpecialPeriods.EllipticFilling.regularOverlap_mem (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (y : (PeriodFamily.regularData P h₁ h₂).Space) :
    y ∈ regularOverlap P j h₁ h₂ ↔
      (PeriodFamily.regularData P h₁ h₂).projection y ∈ regularBasePatch j :=
  Iff.rfl

private theorem SpecialPeriods.EllipticFilling.regularMap_mem_overlap (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : Elliptic.LogGauge.FamilyStar (localPeriods P j)) :
    regularMap P j h₁ h₂ x ∈ regularOverlap P j h₁ h₂ := by
  rw [regularOverlap_mem, regularMap_base]
  exact baseQuotient_mem_regularBasePatch j ⟨x.1.1, x.2⟩

private theorem SpecialPeriods.EllipticFilling.regularMap_range (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Set.range (regularMap P j h₁ h₂) =
      (regularOverlap P j h₁ h₂ : Set (PeriodFamily.regularData P h₁ h₂).Space) := by
  let D := PeriodFamily.regularData P h₁ h₂
  let := D.totalAction
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact regularMap_mem_overlap P j h₁ h₂ x
  · intro hy
    obtain ⟨u, rfl⟩ := D.quotient_surjective y
    have hb : D.baseQuotient u.1 ∈ regularBasePatch j := hy
    have hz' : D.baseQuotient u.1 ∈ Set.range (baseQuotient j) := by
      rw [baseQuotient_range]
      exact hb
    obtain ⟨z, hz⟩ := hz'
    have hbase : D.baseQuotient (localBase j z) = D.baseQuotient u.1 := hz
    obtain ⟨g, hg⟩ := (PeriodFamily.regularCovering P h₁ h₂).apply_eq_iff_mem_orbit.mp hbase
    let x : Elliptic.LogGauge.FamilyStar (localPeriods P j) :=
      ⟨(z.val, SpecialPeriods.triangleTorusHomeomorph g u.2), z.property⟩
    refine ⟨x, ?_⟩
    change D.quotient (localTotalMap P j x) = D.quotient u
    apply (D.quotient_eq_iff _ _).mpr
    exact ⟨g, Prod.ext hg rfl⟩

private theorem SpecialPeriods.EllipticFilling.regularMap_eq_iff (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x y : Elliptic.LogGauge.FamilyStar (localPeriods P j)) :
    letI := Elliptic.LogGauge.starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    regularMap P j h₁ h₂ x = regularMap P j h₁ h₂ y ↔ ∃ g : Elliptic.CyclicGroup j, g • y = x := by
  let L := localData P h₁ h₂ j
  let D := PeriodFamily.regularData P h₁ h₂
  let := Elliptic.LogGauge.starAction L 0 (Matrix.mulVec_zero j.matrix)
  let := D.totalAction
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (D.quotient_eq_iff (localTotalMap P j x) (localTotalMap P j y)).mp h
    have hb : g • localBase j ⟨y.1.1, y.2⟩ = localBase j ⟨x.1.1, x.2⟩ := congrArg Prod.fst hg
    obtain ⟨n, hn, hgn, _⟩ := localBase_orbit_classification j g ⟨y.1.1, y.2⟩ ⟨x.1.1, x.2⟩ hb
    let c : Elliptic.CyclicGroup j := Multiplicative.ofAdd (n : ZMod j.order)
    refine ⟨c, localTotalMap_injective P j ?_⟩
    calc
      localTotalMap P j (c • y) =
          SpecialPeriods.Triangle.ellipticGenerator j ^ n • localTotalMap P j y := by
        rw [localTotalMap_smul]
        simp only [c, toAdd_ofAdd, ZMod.val_natCast_of_lt hn]
      _ = localTotalMap P j x := hgn ▸ hg
  · rintro ⟨g, rfl⟩
    exact regularMap_smul P j h₁ h₂ g y

private def SpecialPeriods.EllipticFilling.regularMapToOverlap (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : Elliptic.LogGauge.FamilyStar (localPeriods P j)) : regularOverlap P j h₁ h₂ :=
  ⟨regularMap P j h₁ h₂ x, regularMap_mem_overlap P j h₁ h₂ x⟩

private theorem SpecialPeriods.EllipticFilling.regularMapToOverlap_surjective
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Function.Surjective (regularMapToOverlap P j h₁ h₂) := by
  intro y
  have hy : y.val ∈ Set.range (regularMap P j h₁ h₂) := by
    rw [regularMap_range]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

private def SpecialPeriods.EllipticFilling.tautologicalToOverlap (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Elliptic.LogGauge.TautologicalStar (localData P h₁ h₂ j) → regularOverlap P j h₁ h₂ := by
  let := Elliptic.LogGauge.starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
  exact
    Quotient.lift (regularMapToOverlap P j h₁ h₂)
      (by
        rintro x y ⟨g, hg⟩
        apply Subtype.ext
        exact (regularMap_eq_iff P j h₁ h₂ x y).mpr ⟨g, hg⟩)

private theorem SpecialPeriods.EllipticFilling.tautologicalToOverlap_injective
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Function.Injective (tautologicalToOverlap P j h₁ h₂) := by
  let L := localData P h₁ h₂ j
  let := Elliptic.LogGauge.starAction L 0 (Matrix.mulVec_zero j.matrix)
  intro a b h
  obtain ⟨x, rfl⟩ := Elliptic.LogGauge.starProject_surjective L 0 (Matrix.mulVec_zero j.matrix) a
  obtain ⟨y, rfl⟩ := Elliptic.LogGauge.starProject_surjective L 0 (Matrix.mulVec_zero j.matrix) b
  have hxy : regularMap P j h₁ h₂ x = regularMap P j h₁ h₂ y := congrArg Subtype.val h
  exact Quotient.sound ((regularMap_eq_iff P j h₁ h₂ x y).mp hxy)

private theorem SpecialPeriods.EllipticFilling.tautologicalToOverlap_surjective
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Function.Surjective (tautologicalToOverlap P j h₁ h₂) := by
  intro y
  obtain ⟨x, rfl⟩ := regularMapToOverlap_surjective P j h₁ h₂ y
  exact
    ⟨Elliptic.LogGauge.starProject (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix) x, rfl⟩

private theorem SpecialPeriods.EllipticFilling.tautologicalToOverlap_bijective
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Function.Bijective (tautologicalToOverlap P j h₁ h₂) :=
  ⟨tautologicalToOverlap_injective P j h₁ h₂, tautologicalToOverlap_surjective P j h₁ h₂⟩

private theorem SpecialPeriods.EllipticFilling.regularMapToOverlap_isLocalDiffeomorph
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    letI := (localPeriods P j).totalChartedSpace
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (regularMapToOverlap P j h₁ h₂) := by
  let := (localPeriods P j).totalChartedSpace
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  exact
    isLocalDiffeomorph_codRestrictOpens (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (regularMap_isLocalDiffeomorph P j h₁ h₂)
      (regularOverlap P j h₁ h₂) (regularMap_mem_overlap P j h₁ h₂)

private theorem SpecialPeriods.EllipticFilling.tautologicalToOverlap_isLocalDiffeomorph
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    letI :=
      Elliptic.LogGauge.starChartedSpace (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (tautologicalToOverlap P j h₁ h₂) := by
  let L := localData P h₁ h₂ j
  let := L.periods.totalChartedSpace
  let := L.periods.totalSpace_isManifold
  let := Elliptic.LogGauge.starAction L 0 (Matrix.mulVec_zero j.matrix)
  let := Elliptic.LogGauge.starChartedSpace L 0 (Matrix.mulVec_zero j.matrix)
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  have hq :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (Elliptic.LogGauge.starProject L 0 (Matrix.mulVec_zero j.matrix)) :=
    CoveringQuotient.project_isLocalDiffeomorph
      (Elliptic.LogGauge.starCoveringMap L 0 (Matrix.mulVec_zero j.matrix))
      (Elliptic.LogGauge.starAction_holomorphic L 0 (Matrix.mulVec_zero j.matrix))
  intro y
  obtain ⟨x, rfl⟩ := Elliptic.LogGauge.starProject_surjective L 0 (Matrix.mulVec_zero j.matrix) y
  exact localDiffeomorphAt_of_comp (hq x) (regularMapToOverlap_isLocalDiffeomorph P j h₁ h₂ x)

private def
    SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    letI :=
      Elliptic.LogGauge.starChartedSpace (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    Diffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (Elliptic.LogGauge.TautologicalStar (localData P h₁ h₂ j)) (regularOverlap P j h₁ h₂) ω := by
  let := Elliptic.LogGauge.starChartedSpace (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  exact
    (tautologicalToOverlap_isLocalDiffeomorph P j h₁ h₂).diffeomorphOfBijective
      (tautologicalToOverlap_bijective P j h₁ h₂)

@[simp]
private theorem SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph_project
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : Elliptic.LogGauge.FamilyStar (localPeriods P j)) :
    tautologicalOverlapBiholomorph P j h₁ h₂
        (Elliptic.LogGauge.starProject (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix) x) =
      regularMapToOverlap P j h₁ h₂ x :=
  rfl

private theorem SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph_coordinate
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : Elliptic.LogGauge.TautologicalStar (localData P h₁ h₂ j)) :
    SpecialPeriods.Triangle.ellipticFullChart j
        (SpecialPeriods.triangleRegularToOrbit
          ((PeriodFamily.regularData P h₁ h₂).projection
            (tautologicalOverlapBiholomorph P j h₁ h₂ x).val)) =
      ((Elliptic.LogGauge.starProjection (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix) x :
          SpecialPeriods.Disc) :
        ℂ) := by
  obtain ⟨y, rfl⟩ :=
    Elliptic.LogGauge.starProject_surjective (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
      x
  change
    SpecialPeriods.Triangle.ellipticFullChart j
        (SpecialPeriods.triangleRegularToOrbit (baseQuotient j ⟨y.1.1, y.2⟩)) =
      (y.1.1 : ℂ) ^ j.order
  exact ellipticFullChart_baseQuotient j ⟨y.1.1, y.2⟩

private abbrev SpecialPeriods.EllipticFilling.MainFillingStar (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :=
  Elliptic.LogGauge.FillingStar (localData P h₁ h₂ j) j.twist (Elliptic.mainTwist_admissible j)

private def
    SpecialPeriods.EllipticFilling.puncturedFillingBiholomorph (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    Diffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (MainFillingStar P j h₁ h₂)
      (regularOverlap P j h₁ h₂) ω := by
  let L := localData P h₁ h₂ j
  let := fillingChartedSpace P h₁ h₂ j
  let := Elliptic.LogGauge.starChartedSpace L 0 (Matrix.mulVec_zero j.matrix)
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  exact
    (Elliptic.LogGauge.mainFillingToTautologicalBiholomorph L).trans
      (tautologicalOverlapBiholomorph P j h₁ h₂)

private theorem SpecialPeriods.EllipticFilling.puncturedFillingBiholomorph_coordinate
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : MainFillingStar P j h₁ h₂) :
    SpecialPeriods.Triangle.ellipticFullChart j
        (SpecialPeriods.triangleRegularToOrbit
          ((PeriodFamily.regularData P h₁ h₂).projection
            (puncturedFillingBiholomorph P j h₁ h₂ x).val)) =
      (fillingProjection P h₁ h₂ j x.val : ℂ) := by
  let L := localData P h₁ h₂ j
  have h :=
    tautologicalOverlapBiholomorph_coordinate P j h₁ h₂
      (Elliptic.LogGauge.mainFillingToTautologicalBiholomorph L x)
  have hb :=
    congrArg (fun z : Elliptic.LogGauge.BaseStar => ((z : SpecialPeriods.Disc) : ℂ))
      (Elliptic.LogGauge.mainFillingToTautologicalBiholomorph_base L x)
  exact h.trans hb

private def SpecialPeriods.EllipticFilling.regularCompactProjection (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    (PeriodFamily.regularData P h₁ h₂).Space → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  fun x =>
  SpecialPeriods.triangleOpenInclusion
    (SpecialPeriods.triangleRegularToOrbit ((PeriodFamily.regularData P h₁ h₂).projection x))

private theorem SpecialPeriods.EllipticFilling.puncturedFillingBiholomorph_base
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : MainFillingStar P j h₁ h₂) :
    regularCompactProjection P h₁ h₂ (puncturedFillingBiholomorph P j h₁ h₂ x).val =
      (SpecialPeriods.Triangle.ellipticCompactifiedChart j).symm
        (fillingProjection P h₁ h₂ j x.val : ℂ) := by
  let y := puncturedFillingBiholomorph P j h₁ h₂ x
  have hs :
    regularCompactProjection P h₁ h₂ y.val ∈
      (SpecialPeriods.Triangle.ellipticCompactifiedChart j).source :=
    (regularBasePatch_mem_iff_compactifiedChart j _).mp y.property
  have hc :
    SpecialPeriods.Triangle.ellipticCompactifiedChart j (regularCompactProjection P h₁ h₂ y.val) =
      (fillingProjection P h₁ h₂ j x.val : ℂ) := by
    rw [regularCompactProjection, SpecialPeriods.Triangle.ellipticCompactifiedChart_openInclusion]
    exact puncturedFillingBiholomorph_coordinate P j h₁ h₂ x
  exact
    ((SpecialPeriods.Triangle.ellipticCompactifiedChart j).left_inv hs).symm.trans
      (congrArg (SpecialPeriods.Triangle.ellipticCompactifiedChart j).symm hc)

private theorem
    SpecialPeriods.EllipticFilling.mainFillingStar_nonempty (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Nonempty (MainFillingStar P j h₁ h₂) := by
  let z : SpecialPeriods.Disc := ⟨(1 / 2 : ℂ), by norm_num [SpecialPeriods.unitDisc]⟩
  obtain ⟨y, hy⟩ := fillingProjection_surjective P h₁ h₂ j z
  refine ⟨⟨y, ?_⟩⟩
  change (fillingProjection P h₁ h₂ j y : ℂ) ≠ 0
  rw [hy]
  norm_num [z]

private theorem
    SpecialPeriods.EllipticFilling.regularOverlap_nonempty (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Nonempty (regularOverlap P j h₁ h₂) := by
  obtain ⟨x⟩ := mainFillingStar_nonempty P h₁ h₂ j
  exact ⟨puncturedFillingBiholomorph P j h₁ h₂ x⟩

private theorem SpecialPeriods.EllipticFilling.piece_nonempty (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) : Nonempty (Piece P h₁ h₂ C j) :=
  by
  obtain ⟨x, _⟩ :=
    pieceProjection_surjective P h₁ h₂ C j
      ⟨SpecialPeriods.Threefold.puncturePoint (Option.some j),
        C.point_mem_fillingPatch (Option.some j)⟩
  exact ⟨x⟩

private theorem SpecialPeriods.EllipticFilling.regularOverlap_mem_iff_compactifiedChart
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (y : (PeriodFamily.regularData P h₁ h₂).Space) :
    y ∈ regularOverlap P j h₁ h₂ ↔
      regularCompactProjection P h₁ h₂ y ∈
        (SpecialPeriods.Triangle.ellipticCompactifiedChart j).source :=
  regularBasePatch_mem_iff_compactifiedChart j ((PeriodFamily.regularData P h₁ h₂).projection y)

private def SpecialPeriods.EllipticFilling.puncturedFillingPartial (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    PartialDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (fillingSpace P h₁ h₂ j)
      (PeriodFamily.regularData P h₁ h₂).Space ω := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  exact
    (opensInclusionPartialDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
          (Elliptic.LogGauge.fillingOpen (localData P h₁ h₂ j) j.twist
            (Elliptic.mainTwist_admissible j))
          (mainFillingStar_nonempty P h₁ h₂ j)).symm.trans
      ((puncturedFillingBiholomorph P j h₁ h₂).toPartialDiffeomorph.trans
        (opensInclusionPartialDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
          (regularOverlap P j h₁ h₂) (regularOverlap_nonempty P h₁ h₂ j)))

@[simp]
private theorem SpecialPeriods.EllipticFilling.puncturedFillingPartial_source
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    (puncturedFillingPartial P h₁ h₂ j).source =
      (Elliptic.LogGauge.fillingOpen (localData P h₁ h₂ j) j.twist
          (Elliptic.mainTwist_admissible j) :
        Set _) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  simp [puncturedFillingPartial, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp]
private theorem SpecialPeriods.EllipticFilling.puncturedFillingPartial_target
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    (puncturedFillingPartial P h₁ h₂ j).target =
      (regularOverlap P j h₁ h₂ : Set (PeriodFamily.regularData P h₁ h₂).Space) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  simp [puncturedFillingPartial, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp]
private theorem SpecialPeriods.EllipticFilling.puncturedFillingPartial_apply
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (x : MainFillingStar P j h₁ h₂) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    puncturedFillingPartial P h₁ h₂ j x.val = (puncturedFillingBiholomorph P j h₁ h₂ x).val := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  let e :=
    (Elliptic.LogGauge.fillingOpen (localData P h₁ h₂ j) j.twist
          (Elliptic.mainTwist_admissible j)).openPartialHomeomorphSubtypeCoe
      (mainFillingStar_nonempty P h₁ h₂ j)
  have he : e.symm x.val = x := e.left_inv (Set.mem_univ x)
  change
    (puncturedFillingBiholomorph P j h₁ h₂ (e.symm x.val) :
        (PeriodFamily.regularData P h₁ h₂).Space) =
      _
  rw [he]

private theorem
    SpecialPeriods.EllipticFilling.puncturedFillingPartial_base (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (x : fillingSpace P h₁ h₂ j)
    (hx : x ∈ (puncturedFillingPartial P h₁ h₂ j).source) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    regularCompactProjection P h₁ h₂ (puncturedFillingPartial P h₁ h₂ j x) =
      (SpecialPeriods.Triangle.ellipticCompactifiedChart j).symm
        (fillingProjection P h₁ h₂ j x : ℂ) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  have hx' :
    x ∈
      (Elliptic.LogGauge.fillingOpen (localData P h₁ h₂ j) j.twist
          (Elliptic.mainTwist_admissible j) :
        Set (fillingSpace P h₁ h₂ j)) := by simpa only [puncturedFillingPartial_source] using hx
  rw [puncturedFillingPartial_apply P h₁ h₂ j ⟨x, hx'⟩]
  exact puncturedFillingBiholomorph_base P j h₁ h₂ ⟨x, hx'⟩

private theorem SpecialPeriods.EllipticFilling.puncturedFillingPartial_coordinate
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (x : fillingSpace P h₁ h₂ j)
    (hx : x ∈ (puncturedFillingPartial P h₁ h₂ j).source) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    SpecialPeriods.Triangle.ellipticCompactifiedChart j
        (regularCompactProjection P h₁ h₂ (puncturedFillingPartial P h₁ h₂ j x)) =
      (fillingProjection P h₁ h₂ j x : ℂ) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  have hx' :
    x ∈
      (Elliptic.LogGauge.fillingOpen (localData P h₁ h₂ j) j.twist
          (Elliptic.mainTwist_admissible j) :
        Set (fillingSpace P h₁ h₂ j)) := by simpa only [puncturedFillingPartial_source] using hx
  rw [puncturedFillingPartial_apply P h₁ h₂ j ⟨x, hx'⟩, regularCompactProjection,
    SpecialPeriods.Triangle.ellipticCompactifiedChart_openInclusion]
  exact puncturedFillingBiholomorph_coordinate P j h₁ h₂ ⟨x, hx'⟩

private theorem SpecialPeriods.EllipticFilling.puncturedFillingPartial_symm_coordinate
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (y : (PeriodFamily.regularData P h₁ h₂).Space)
    (hy : y ∈ (puncturedFillingPartial P h₁ h₂ j).target) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    (fillingProjection P h₁ h₂ j ((puncturedFillingPartial P h₁ h₂ j).symm y) : ℂ) =
      SpecialPeriods.Triangle.ellipticCompactifiedChart j (regularCompactProjection P h₁ h₂ y) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  have h :=
    puncturedFillingPartial_coordinate P h₁ h₂ j ((puncturedFillingPartial P h₁ h₂ j).symm y)
      ((puncturedFillingPartial P h₁ h₂ j).map_target hy)
  have he : puncturedFillingPartial P h₁ h₂ j ((puncturedFillingPartial P h₁ h₂ j).symm y) = y :=
    (puncturedFillingPartial P h₁ h₂ j).right_inv hy
  exact
    h.symm.trans
      (congrArg
        (fun z : (PeriodFamily.regularData P h₁ h₂).Space =>
          SpecialPeriods.Triangle.ellipticCompactifiedChart j
            (regularCompactProjection P h₁ h₂ z))
        he)

private def SpecialPeriods.EllipticFilling.smallOverlap (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    letI := pieceChartedSpace P h₁ h₂ C j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    PartialDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (Piece P h₁ h₂ C j)
      (PeriodFamily.regularData P h₁ h₂).Space ω := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  exact
    (opensInclusionPartialDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
          (pieceDomain P h₁ h₂ C j) (piece_nonempty P h₁ h₂ C j)).trans
      (puncturedFillingPartial P h₁ h₂ j)

@[simp]
private theorem SpecialPeriods.EllipticFilling.smallOverlap_apply (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) (x : Piece P h₁ h₂ C j) :
    smallOverlap P h₁ h₂ C j x = puncturedFillingPartial P h₁ h₂ j x.val :=
  rfl

@[simp]
private theorem SpecialPeriods.EllipticFilling.smallOverlap_source (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    (smallOverlap P h₁ h₂ C j).source =
      pieceProjectionToBase P h₁ h₂ C j ⁻¹'
        (SpecialPeriods.Threefold.regularPatch :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  change
    Set.univ ∩
        (Subtype.val : Piece P h₁ h₂ C j → fillingSpace P h₁ h₂ j) ⁻¹'
          (puncturedFillingPartial P h₁ h₂ j).source =
      _
  rw [Set.univ_inter, puncturedFillingPartial_source]
  ext x
  exact (pieceProjectionToBase_mem_regular_iff P h₁ h₂ C j x).symm

private theorem
    SpecialPeriods.EllipticFilling.smallOverlap_mem_source (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) (x : Piece P h₁ h₂ C j) :
    x ∈ (smallOverlap P h₁ h₂ C j).source ↔ (fillingProjection P h₁ h₂ j x.val : ℂ) ≠ 0 := by
  rw [smallOverlap_source]
  exact pieceProjectionToBase_mem_regular_iff P h₁ h₂ C j x

private theorem
    SpecialPeriods.EllipticFilling.smallOverlap_apply_mainStar (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) (x : Piece P h₁ h₂ C j)
    (hx : (fillingProjection P h₁ h₂ j x.val : ℂ) ≠ 0) :
    smallOverlap P h₁ h₂ C j x =
      (puncturedFillingBiholomorph P j h₁ h₂ (⟨x.val, hx⟩ : MainFillingStar P j h₁ h₂)).val :=
  puncturedFillingPartial_apply P h₁ h₂ j ⟨x.val, hx⟩

@[simp]
private theorem SpecialPeriods.EllipticFilling.smallOverlap_target (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    (smallOverlap P h₁ h₂ C j).target =
      regularCompactProjection P h₁ h₂ ⁻¹'
        (C.fillingPatch (Option.some j) : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  change
    (puncturedFillingPartial P h₁ h₂ j).target ∩
        (puncturedFillingPartial P h₁ h₂ j).symm ⁻¹'
          ((pieceDomain P h₁ h₂ C j).openPartialHomeomorphSubtypeCoe
              (piece_nonempty P h₁ h₂ C j)).target =
      _
  rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  ext y
  constructor
  · rintro ⟨hy, hyV⟩
    have hyOverlap : y ∈ regularOverlap P j h₁ h₂ := by
      change y ∈ (regularOverlap P j h₁ h₂ : Set (PeriodFamily.regularData P h₁ h₂).Space)
      rw [← puncturedFillingPartial_target P h₁ h₂ j]
      exact hy
    refine
      (C.mem_fillingPatch (Option.some j) (regularCompactProjection P h₁ h₂ y)).mpr
        ⟨(regularOverlap_mem_iff_compactifiedChart P h₁ h₂ j y).mp hyOverlap, ?_⟩
    change
      ‖SpecialPeriods.Triangle.ellipticCompactifiedChart j (regularCompactProjection P h₁ h₂ y)‖ <
        C.radius (Option.some j)
    rw [← puncturedFillingPartial_symm_coordinate P h₁ h₂ j y hy]
    exact hyV
  · intro hy
    have hy' := (C.mem_fillingPatch (Option.some j) (regularCompactProjection P h₁ h₂ y)).mp hy
    have hyFull : y ∈ (puncturedFillingPartial P h₁ h₂ j).target := by
      rw [puncturedFillingPartial_target]
      exact (regularOverlap_mem_iff_compactifiedChart P h₁ h₂ j y).mpr hy'.1
    refine ⟨hyFull, ?_⟩
    change
      ‖(fillingProjection P h₁ h₂ j ((puncturedFillingPartial P h₁ h₂ j).symm y) : ℂ)‖ <
        C.radius (Option.some j)
    rw [puncturedFillingPartial_symm_coordinate P h₁ h₂ j y hyFull]
    exact hy'.2

private theorem SpecialPeriods.EllipticFilling.smallOverlap_base (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) (x : Piece P h₁ h₂ C j)
    (hx : x ∈ (smallOverlap P h₁ h₂ C j).source) :
    regularCompactProjection P h₁ h₂ (smallOverlap P h₁ h₂ C j x) =
      pieceProjectionToBase P h₁ h₂ C j x := by
  rw [smallOverlap_apply]
  exact
    puncturedFillingPartial_base P h₁ h₂ j x.val
      (by
        rw [puncturedFillingPartial_source]
        exact (smallOverlap_mem_source P h₁ h₂ C j x).mp hx)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private def SpecialPeriods.Threefold.specialEllipticOverlap (j : Elliptic.Kind) :
    PartialDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (SpecialEllipticPiece j) SpecialRegularFamily
      ω :=
  SpecialPeriods.EllipticFilling.smallOverlap SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem SpecialPeriods.Threefold.specialEllipticOverlap_source (j : Elliptic.Kind) :
    (specialEllipticOverlap j).source =
      specialEllipticPieceProjectionToBase j ⁻¹'
        (regularPatch : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  SpecialPeriods.EllipticFilling.smallOverlap_source SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem SpecialPeriods.Threefold.specialEllipticOverlap_target (j : Elliptic.Kind) :
    (specialEllipticOverlap j).target =
      specialRegularFamilyProjectionToBase ⁻¹'
        (specialBaseCover.fillingPatch (Option.some j) :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  SpecialPeriods.EllipticFilling.smallOverlap_target SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem SpecialPeriods.Threefold.specialEllipticOverlap_base (j : Elliptic.Kind)
    (x : SpecialEllipticPiece j) (hx : x ∈ (specialEllipticOverlap j).source) :
    specialRegularFamilyProjectionToBase (specialEllipticOverlap j x) =
      specialEllipticPieceProjectionToBase j x :=
  SpecialPeriods.EllipticFilling.smallOverlap_base SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j x hx

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private def SpecialPeriods.Threefold.localOverlap :
    (i : Puncture) →
      PartialDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (localPiece (Option.some i))
        (localPiece Option.none) ω
  | none => specialCuspOverlap
  | some j => specialEllipticOverlap j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.localOverlap_source (i : Puncture) :
    (localOverlap i).source =
      localBaseMap (Option.some i) ⁻¹'
        (specialBaseCover.patch Option.none :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  cases i with
  | none => exact specialCuspOverlap_source
  | some j => exact specialEllipticOverlap_source j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.localOverlap_target (i : Puncture) :
    (localOverlap i).target =
      localBaseMap Option.none ⁻¹'
        (specialBaseCover.patch (Option.some i) :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  cases i with
  | none => exact specialCuspOverlap_target
  | some j => exact specialEllipticOverlap_target j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem
    SpecialPeriods.Threefold.localOverlap_base (i : Puncture) (x : localPiece (Option.some i))
    (hx : x ∈ (localOverlap i).source) :
    localBaseMap Option.none (localOverlap i x) = localBaseMap (Option.some i) x := by
  cases i with
  | none => exact specialCuspOverlap_base x hx
  | some j => exact specialEllipticOverlap_base j x hx

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private abbrev SpecialPeriods.Threefold.gluingStar :
    Star.Input SpecialPeriods.TriangleCompactifiedOrbitSpace Puncture
    where
  patch := specialBaseCover.patch
  cover := specialBaseCover.isOpenCover
  disjoint := specialBaseCover.pairwise_disjoint
  piece := localPiece
  toBase := localBaseMap
  toBase_mem := localProjectionToBase_mem
  overlap i := (localOverlap i).toOpenPartialHomeomorph
  source_eq := localOverlap_source
  target_eq := localOverlap_target
  preserves_base := localOverlap_base

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private abbrev SpecialPeriods.Threefold.gluingData :
    ThreefoldGluing.Data SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  gluingStar.toData

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.gluingData_transition_holomorphic (i j : Index) :
    ContMDiffOn (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (gluingData.transition i j)
      (gluingData.transition i j).source :=
  gluingStar.toData_transition_holomorphic (fun i => (localOverlap i).contMDiffOn)
    (fun i => (localOverlap i).symm.contMDiffOn) i j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.gluingData_localProjection_proper (i : Index) :
    IsProperMap (gluingData.localProjection i) :=
  localProjection_proper i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
private abbrev SpecialPeriods.Threefold.Space :=
  gluingData.Space

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
@[instance_reducible]
private def SpecialPeriods.Threefold.chartedSpace : ChartedSpace (ℂ × ComplexPlane₂) Space :=
  gluingData.chartedSpace

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private abbrev SpecialPeriods.Threefold.projection :
    Space → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  gluingData.projection

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.projection_proper : IsProperMap projection :=
  gluingData.projection_proper gluingData_localProjection_proper

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.space_compact : CompactSpace Space :=
  gluingData.compactSpace gluingData_localProjection_proper

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.space_t2Space : T2Space Space :=
  gluingData.spaceT2

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.space_secondCountable : SecondCountableTopology Space :=
  gluingData.secondCountableSpace_of_compactBase

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.space_isManifold :
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω Space :=
  gluingData.isManifold gluingData_transition_holomorphic

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.space_nonempty : Nonempty Space :=
  ⟨gluingData.inclusion Option.none specialRegularFamilyPoint⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private def SpecialPeriods.Threefold.projectionSphere : Space → RiemannSphere :=
  SpecialPeriods.Triangle.triangleSphereUniformization ∘ projection

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private abbrev SpecialPeriods.Threefold.inclusion (i : Index) : localPiece i → Space :=
  gluingData.inclusion i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.inclusion_openEmbedding (i : Index) :
    Topology.IsOpenEmbedding (SpecialPeriods.Threefold.inclusion i) :=
  gluingData.inclusion_openEmbedding i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.inclusion_holomorphic (i : Index) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (SpecialPeriods.Threefold.inclusion i) :=
  gluingData.inclusion_holomorphic gluingData_transition_holomorphic i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.projection_inclusion (i : Index) (x : localPiece i) :
    projection (SpecialPeriods.Threefold.inclusion i x) = localProjectionToBase i x :=
  gluingData.projection_inclusion i x

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.inclusion_range (i : Index) :
    Set.range (SpecialPeriods.Threefold.inclusion i) =
      projection ⁻¹'
        (specialBaseCover.patch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  gluingData.inclusion_range i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private abbrev SpecialPeriods.Threefold.liftedPatch (i : Index) : TopologicalSpace.Opens Space :=
  gluingData.liftedPatch i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private def SpecialPeriods.Threefold.patchBiholomorph (i : Index) :
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (localPiece i) (liftedPatch i) ω :=
  gluingData.patchBiholomorph gluingData_transition_holomorphic i

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialRegularFamilyProjection_fibre_isConnected
    (b : regularPatch) : IsConnected (specialRegularFamilyProjection ⁻¹' { b }) := by
  let D :=
    regularFamilyData SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
      SpecialPeriods.specialPeriodMap_generator₂
  have hf (q : SpecialPeriods.TriangleRegularQuotient) : IsConnected (D.projection ⁻¹' { q }) := by
    obtain ⟨z, rfl⟩ :=
      (PeriodFamily.regularCovering SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂).surjective
        q
    apply isConnected_iff_connectedSpace.mpr
    exact
      (D.fibreHomeomorph
            (PeriodFamily.regularCovering SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            z).connectedSpace_iff.mp
        inferInstance
  change IsConnected ((regularBiholomorph.toHomeomorph ∘ D.projection) ⁻¹' { b })
  exact
    FibreTopology.fibre_isConnected_comp_homeomorph D.projection regularBiholomorph.toHomeomorph b
      (hf (regularBiholomorph.symm b))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialCuspPieceCoordinate_fibre_isConnected
    (b : coordinateBall (specialBaseCover.radius Option.none)) :
    IsConnected
      (CuspPiece.coordinate SpecialPeriods.specialCuspData specialBaseCover ⁻¹' { b }) := by
  let D :=
    CuspPiece.restrictedData SpecialPeriods.specialCuspData specialBaseCover specialCuspRadius_le
  have he :
    CuspPiece.coordinate SpecialPeriods.specialCuspData specialBaseCover ⁻¹' { b } =
      CuspQuotient.projection SpecialPeriods.specialCuspData.correction
          (specialBaseCover.radius Option.none) ⁻¹'
        {(b : ℂ)} := by
    ext x
    exact Subtype.ext_iff
  rw [he]
  exact
    CuspUniformization.fibre_connected SpecialPeriods.specialCuspData.correction
      (specialBaseCover.radius Option.none) (specialBaseCover.radius_pos Option.none)
      D.radius_lt_one D.holomorphic D.smallDrift b

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialCuspPieceProjection_fibre_isConnected
    (b : specialBaseCover.fillingPatch Option.none) :
    IsConnected (specialCuspPieceProjection ⁻¹' { b }) := by
  change
    IsConnected
      ((((specialBaseCover.fillingChart Option.none).symm.toHomeomorph) ∘
          CuspPiece.coordinate SpecialPeriods.specialCuspData specialBaseCover) ⁻¹'
        { b })
  exact
    FibreTopology.fibre_isConnected_comp_homeomorph
      (CuspPiece.coordinate SpecialPeriods.specialCuspData specialBaseCover)
      (specialBaseCover.fillingChart Option.none).symm.toHomeomorph b
      (specialCuspPieceCoordinate_fibre_isConnected (specialBaseCover.fillingChart Option.none b))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialEllipticPieceCoordinate_fibre_isConnected
    (j : Elliptic.Kind) (b : coordinateBall (specialBaseCover.radius (Option.some j))) :
    IsConnected
      (SpecialPeriods.EllipticFilling.pieceCoordinate SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
          specialBaseCover j ⁻¹'
        { b }) := by
  let f :=
    SpecialPeriods.EllipticFilling.fillingProjection SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂ j
  let S : Set SpecialPeriods.Disc :=
    SpecialPeriods.EllipticFilling.smallDisc (specialBaseCover.radius (Option.some j))
  let e :=
    SpecialPeriods.EllipticFilling.smallDiscHomeomorph (specialBaseCover.radius (Option.some j))
      (specialBaseCover.radius_lt_chart (Option.some j))
  have hf (q : SpecialPeriods.Disc) : IsConnected (f ⁻¹' { q }) :=
    (SpecialPeriods.EllipticFilling.localData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
          j).projection_fibre_isConnected
      j.twist (Elliptic.mainTwist_admissible j) q
  change IsConnected ((e ∘ S.restrictPreimage f) ⁻¹' { b })
  exact
    FibreTopology.fibre_isConnected_comp_homeomorph (S.restrictPreimage f) e b
      (FibreTopology.restrictPreimage_fibre_isConnected f S (e.symm b) (hf (e.symm b).val))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.specialEllipticPieceProjection_fibre_isConnected
    (j : Elliptic.Kind) (b : specialBaseCover.fillingPatch (Option.some j)) :
    IsConnected (specialEllipticPieceProjection j ⁻¹' { b }) := by
  change
    IsConnected
      ((((specialBaseCover.fillingChart (Option.some j)).symm.toHomeomorph) ∘
          SpecialPeriods.EllipticFilling.pieceCoordinate SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
            specialBaseCover j) ⁻¹'
        { b })
  exact
    FibreTopology.fibre_isConnected_comp_homeomorph
      (SpecialPeriods.EllipticFilling.pieceCoordinate SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
        specialBaseCover j)
      (specialBaseCover.fillingChart (Option.some j)).symm.toHomeomorph b
      (specialEllipticPieceCoordinate_fibre_isConnected j
        (specialBaseCover.fillingChart (Option.some j) b))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.localProjection_fibre_isConnected (i : Index)
    (b : specialBaseCover.patch i) : IsConnected (localProjection i ⁻¹' { b }) := by
  cases i with
  | none => exact specialRegularFamilyProjection_fibre_isConnected b
  | some i =>
    cases i with
    | none => exact specialCuspPieceProjection_fibre_isConnected b
    | some j => exact specialEllipticPieceProjection_fibre_isConnected j b

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.gluingData_localProjection_fibre_isConnected (i : Index)
    (b : specialBaseCover.patch i) : IsConnected (gluingData.localProjection i ⁻¹' { b }) :=
  localProjection_fibre_isConnected i b

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.projection_fibre_isConnected
    (b : SpecialPeriods.TriangleCompactifiedOrbitSpace) : IsConnected (projection ⁻¹' { b }) :=
  gluingData.projection_fibre_isConnected gluingData_localProjection_fibre_isConnected b

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.space_connected : ConnectedSpace Space :=
  gluingData.connectedSpace gluingData_localProjection_proper
    gluingData_localProjection_fibre_isConnected

public
theorem SpecialPeriods.Threefold.punctured_complex_ball_isPathConnected {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball (0 : ℂ) r \ {0}) := by
  let e : OpenPartialHomeomorph ℂ ℂ := OpenPartialHomeomorph.univBall (0 : ℂ) r
  have hsource : e.source = Set.univ := OpenPartialHomeomorph.univBall_source _ _
  have htarget : e.target = Metric.ball 0 r := OpenPartialHomeomorph.univBall_target _ hr
  have hzero : e 0 = 0 := OpenPartialHomeomorph.univBall_apply_zero _ _
  have hinj : Function.Injective e := by
    intro z w h
    exact e.injOn (by rw [hsource]; trivial) (by rw [hsource]; trivial) h
  have himage : e '' ({0}ᶜ : Set ℂ) = Metric.ball 0 r \ {0} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← htarget]
        exact e.map_source (by rw [hsource]; trivial)
      · change e w ≠ 0
        intro h
        exact hw (hinj (h.trans hzero.symm))
    · rintro ⟨hz, hne⟩
      have hzt : z ∈ e.target := by rwa [htarget]
      refine ⟨e.symm z, ?_, e.right_inv hzt⟩
      change e.symm z ≠ 0
      intro h
      have he := e.right_inv hzt
      rw [h, hzero] at he
      exact hne he.symm
  have hconn : IsPathConnected ({0}ᶜ : Set ℂ) :=
    isPathConnected_compl_singleton_of_one_lt_rank (by simp) 0
  have him := hconn.image (OpenPartialHomeomorph.continuous_univBall (0 : ℂ) r)
  change IsPathConnected (e '' ({0}ᶜ : Set ℂ)) at him
  rwa [himage] at him

private theorem SpecialPeriods.Threefold.regularPatch_isPathConnected :
    IsPathConnected (regularPatch : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  rw [← regularInclusion_range]
  exact isPathConnected_range regularInclusion_isOpenEmbedding.continuous

private theorem SpecialPeriods.Threefold.BaseCover.fillingPatch_isPathConnected
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) :
    IsPathConnected (C.fillingPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  rw [C.fillingPatch_eq_inverse_image i]
  exact
    (Metric.isPathConnected_ball (C.radius_pos i)).image'
      ((SpecialPeriods.Threefold.punctureChart i).continuousOn_symm.mono
        (C.coordinateBall_subset_target i))

private theorem SpecialPeriods.Threefold.BaseCover.regular_inter_fillingPatch_eq_image
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) :
    (SpecialPeriods.Threefold.regularPatch : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ∩
        C.fillingPatch i =
      (SpecialPeriods.Threefold.punctureChart i).symm '' (Metric.ball 0 (C.radius i) \ {0}) := by
  ext x
  constructor
  · rintro ⟨hr, hx⟩
    refine
      ⟨SpecialPeriods.Threefold.punctureChart i x, ⟨?_, ?_⟩,
        (SpecialPeriods.Threefold.punctureChart i).left_inv (C.fillingPatch_subset_chart i hx)⟩
    · simpa only [Metric.mem_ball, dist_zero_right] using ((C.mem_fillingPatch i x).mp hx).2
    · exact (C.fillingPatch_regular_iff_coordinate_ne_zero i hx).mp hr
  · rintro ⟨z, ⟨hz, hne⟩, rfl⟩
    exact ⟨(C.inverse_mem_regular_iff i hz).mpr hne, C.inverse_mem_fillingPatch i hz⟩

private theorem SpecialPeriods.Threefold.BaseCover.regular_inter_fillingPatch_isPathConnected
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) :
    IsPathConnected
      ((SpecialPeriods.Threefold.regularPatch :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ∩
        C.fillingPatch i) := by
  rw [C.regular_inter_fillingPatch_eq_image i]
  exact
    (SpecialPeriods.Threefold.punctured_complex_ball_isPathConnected (C.radius_pos i)).image'
      ((SpecialPeriods.Threefold.punctureChart i).continuousOn_symm.mono
        (Set.sdiff_subset.trans (C.coordinateBall_subset_target i)))

private theorem SpecialPeriods.Threefold.BaseCover.patch_isPathConnected
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Index) :
    IsPathConnected (C.patch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  cases i with
  | none => exact SpecialPeriods.Threefold.regularPatch_isPathConnected
  | some i => exact C.fillingPatch_isPathConnected i

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.instLocal1 : LocallyPathConnectedSpace Space :=
  ChartedSpace.locallyPathConnectedSpace (ℂ × ComplexPlane₂) Space

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instLocal1 in
private theorem SpecialPeriods.Threefold.projection_preimage_isPathConnected
    {s : Set SpecialPeriods.TriangleCompactifiedOrbitSpace} (hsopen : IsOpen s)
    (hs : IsConnected s) : IsPathConnected (projection ⁻¹' s) :=
  FibreTopology.isPathConnected_preimage_of_proper_of_connected_fibres projection_proper
    projection_fibre_isConnected hsopen hs

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instLocal1 in
private theorem SpecialPeriods.Threefold.liftedPatch_isPathConnected (i : Index) :
    IsPathConnected (liftedPatch i : Set Space) :=
  projection_preimage_isPathConnected (specialBaseCover.patch i).isOpen
    (specialBaseCover.patch_isPathConnected i).isConnected

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instLocal1 in
private theorem SpecialPeriods.Threefold.liftedPatch_regular_inter_isPathConnected (i : Puncture) :
    IsPathConnected ((liftedPatch Option.none : Set Space) ∩ liftedPatch (Option.some i)) :=
  projection_preimage_isPathConnected
    (regularPatch.isOpen.inter (specialBaseCover.fillingPatch i).isOpen)
    (specialBaseCover.regular_inter_fillingPatch_isPathConnected i).isConnected

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instLocal1 in
private theorem SpecialPeriods.Threefold.liftedPatch_regular_inter_nonempty (i : Puncture) :
    ((liftedPatch Option.none : Set Space) ∩ liftedPatch (Option.some i)).Nonempty :=
  (liftedPatch_regular_inter_isPathConnected i).nonempty

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instLocal1 in
private theorem
    SpecialPeriods.Threefold.liftedPatch_regular_inter_pathConnectedSpace (i : Puncture) :
    PathConnectedSpace
      ↥((liftedPatch Option.none : Set Space) ∩ (liftedPatch (Option.some i) : Set Space)) :=
  isPathConnected_iff_pathConnectedSpace.mp (liftedPatch_regular_inter_isPathConnected i)

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instLocal1 in
private theorem SpecialPeriods.Threefold.liftedFilling_disjoint {i j : Puncture} (hij : i ≠ j) :
    Disjoint (liftedPatch (Option.some i) : Set Space) (liftedPatch (Option.some j)) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact Set.disjoint_left.mp (specialBaseCover.fillingPatch_disjoint hij) hi hj

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instLocal1 in
private theorem SpecialPeriods.Threefold.liftedPatch_iUnion :
    ⋃ i : Index, (liftedPatch i : Set Space) = Set.univ := by
  change
    (⋃ i : Index,
        projection ⁻¹'
          (specialBaseCover.patch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace)) =
      Set.univ
  rw [← Set.preimage_iUnion, specialBaseCover.patch_iUnion, Set.preimage_univ]

private def
    SpecialPeriods.Threefold.partialPatch (s : Finset Puncture) : TopologicalSpace.Opens Space :=
  liftedPatch Option.none ⊔ ⨆ i ∈ s, liftedPatch (Option.some i)

@[simp]
private theorem SpecialPeriods.Threefold.mem_partialPatch (s : Finset Puncture) (x : Space) :
    x ∈ partialPatch s ↔ x ∈ liftedPatch Option.none ∨ ∃ i ∈ s, x ∈ liftedPatch (Option.some i) :=
  by
  simp only [partialPatch, TopologicalSpace.Opens.mem_sup, TopologicalSpace.Opens.mem_iSup,
    exists_prop]

@[simp]
private theorem
    SpecialPeriods.Threefold.partialPatch_empty : partialPatch ∅ = liftedPatch Option.none := by
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  change x ∈ partialPatch ∅ ↔ x ∈ liftedPatch Option.none
  simp only [mem_partialPatch, Finset.notMem_empty, false_and, exists_false, or_false]

private theorem SpecialPeriods.Threefold.regular_le_partialPatch (s : Finset Puncture) :
    liftedPatch Option.none ≤ partialPatch s := fun x hx => (mem_partialPatch s x).mpr (Or.inl hx)

private theorem
    SpecialPeriods.Threefold.filling_le_partialPatch {s : Finset Puncture} {i : Puncture}
    (hi : i ∈ s) : liftedPatch (Option.some i) ≤ partialPatch s := fun x hx =>
  (mem_partialPatch s x).mpr (Or.inr ⟨i, hi, hx⟩)

private theorem SpecialPeriods.Threefold.partialPatch_mono {s t : Finset Puncture} (hst : s ⊆ t) :
    partialPatch s ≤ partialPatch t := by
  intro x hx
  rcases (mem_partialPatch s x).mp hx with hx | ⟨i, hi, hx⟩
  · exact regular_le_partialPatch t hx
  · exact filling_le_partialPatch (hst hi) hx

@[simp]
private theorem SpecialPeriods.Threefold.partialPatch_insert (s : Finset Puncture) (i : Puncture) :
    partialPatch (Insert.insert i s) = partialPatch s ⊔ liftedPatch (Option.some i) := by
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  change x ∈ partialPatch (Insert.insert i s) ↔ x ∈ partialPatch s ⊔ liftedPatch (Option.some i)
  simp only [mem_partialPatch, Finset.mem_insert, TopologicalSpace.Opens.mem_sup]
  constructor
  · rintro (hr | ⟨j, hj | hj, hx⟩)
    · exact Or.inl (Or.inl hr)
    · subst j
      exact Or.inr hx
    · exact Or.inl (Or.inr ⟨j, hj, hx⟩)
  · rintro ((hr | ⟨j, hj, hx⟩) | hx)
    · exact Or.inl hr
    · exact Or.inr ⟨j, Or.inr hj, hx⟩
    · exact Or.inr ⟨i, Or.inl rfl, hx⟩

private theorem
    SpecialPeriods.Threefold.partialPatch_le_insert (s : Finset Puncture) (i : Puncture) :
    partialPatch s ≤ partialPatch (Insert.insert i s) :=
  partialPatch_mono (Finset.subset_insert i s)

private theorem SpecialPeriods.Threefold.filling_le_partialPatch_insert (s : Finset Puncture)
    (i : Puncture) : liftedPatch (Option.some i) ≤ partialPatch (Insert.insert i s) :=
  filling_le_partialPatch (Finset.mem_insert_self i s)

@[simp]
private theorem SpecialPeriods.Threefold.partialPatch_univ : partialPatch Finset.univ = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ ⋃ j : Index, (liftedPatch j : Set Space) := by
    rw [liftedPatch_iUnion]
    trivial
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  cases j with
  | none => exact regular_le_partialPatch _ hj
  | some i => exact filling_le_partialPatch (Finset.mem_univ i) hj

private theorem SpecialPeriods.Threefold.partialPatch_inter_filling_eq (s : Finset Puncture)
    (i : Puncture) (hi : i ∉ s) :
    (partialPatch s : Set Space) ∩ liftedPatch (Option.some i) =
      (liftedPatch Option.none : Set Space) ∩ liftedPatch (Option.some i) := by
  ext x
  constructor
  · rintro ⟨hx, hxi⟩
    rcases (mem_partialPatch s x).mp hx with hr | ⟨j, hj, hxj⟩
    · exact ⟨hr, hxi⟩
    · have hji : j ≠ i := fun h => hi (h ▸ hj)
      exact (Set.disjoint_left.mp (liftedFilling_disjoint hji) hxj hxi).elim
  · rintro ⟨hr, hxi⟩
    exact ⟨regular_le_partialPatch s hr, hxi⟩

private theorem SpecialPeriods.Threefold.partialPatch_isPathConnected (s : Finset Puncture) :
    IsPathConnected (partialPatch s : Set Space) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [partialPatch_empty]
    exact liftedPatch_isPathConnected Option.none
  | @insert i s _ ih =>
    rw [partialPatch_insert, TopologicalSpace.Opens.coe_sup]
    apply ih.union (liftedPatch_isPathConnected (Option.some i))
    obtain ⟨x, hr, hi⟩ := liftedPatch_regular_inter_nonempty i
    exact ⟨x, regular_le_partialPatch s hr, hi⟩

private theorem SpecialPeriods.Threefold.partialPatch_pathConnectedSpace (s : Finset Puncture) :
    PathConnectedSpace (partialPatch s) :=
  isPathConnected_iff_pathConnectedSpace.mp (partialPatch_isPathConnected s)

private def SpecialPeriods.Threefold.attachmentPoint (i : Puncture) : Space :=
  (liftedPatch_regular_inter_nonempty i).choose

private theorem SpecialPeriods.Threefold.attachmentPoint_mem_regular (i : Puncture) :
    attachmentPoint i ∈ liftedPatch Option.none :=
  (liftedPatch_regular_inter_nonempty i).choose_spec.1

private theorem SpecialPeriods.Threefold.attachmentPoint_mem_filling (i : Puncture) :
    attachmentPoint i ∈ liftedPatch (Option.some i) :=
  (liftedPatch_regular_inter_nonempty i).choose_spec.2

private theorem SpecialPeriods.Threefold.attachmentPoint_mem_partialPatch (s : Finset Puncture)
    (i : Puncture) : attachmentPoint i ∈ partialPatch s :=
  regular_le_partialPatch s (attachmentPoint_mem_regular i)

private def SpecialPeriods.Threefold.subspacePreimageHomeomorph {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hBA : B ⊆ A) : ((Subtype.val : A → X) ⁻¹' B) ≃ₜ B
    where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hBA x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private def
    SpecialPeriods.Threefold.subspacePreimageInterHomeomorph {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hBC : B ∩ C ⊆ A) :
    ↥(((Subtype.val : A → X) ⁻¹' B) ∩ ((Subtype.val : A → X) ⁻¹' C)) ≃ₜ ↥(B ∩ C) :=
  subspacePreimageHomeomorph hBC

private def SpecialPeriods.Threefold.attachmentLeft (s : Finset Puncture) (i : Puncture) :
    TopologicalSpace.Opens (partialPatch (Insert.insert i s)) :=
  TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ (partialPatch s)

private def SpecialPeriods.Threefold.attachmentRight (s : Finset Puncture) (i : Puncture) :
    TopologicalSpace.Opens (partialPatch (Insert.insert i s)) :=
  TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ (liftedPatch (Option.some i))

private def SpecialPeriods.Threefold.attachmentBase (s : Finset Puncture) (i : Puncture) :
    partialPatch (Insert.insert i s) :=
  ⟨attachmentPoint i, attachmentPoint_mem_partialPatch (Insert.insert i s) i⟩

private theorem
    SpecialPeriods.Threefold.attachmentLeft_union_right (s : Finset Puncture) (i : Puncture) :
    (attachmentLeft s i : Set (partialPatch (Insert.insert i s))) ∪ attachmentRight s i =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  change (x : Space) ∈ partialPatch s ∨ (x : Space) ∈ liftedPatch (Option.some i)
  exact (le_of_eq (partialPatch_insert s i)) x.property

private theorem SpecialPeriods.Threefold.attachmentLeft_isPathConnected (s : Finset Puncture)
    (i : Puncture) :
    IsPathConnected (attachmentLeft s i : Set (partialPatch (Insert.insert i s))) :=
  (partialPatch_isPathConnected s).preimage_coe (partialPatch_le_insert s i)

private theorem SpecialPeriods.Threefold.attachmentRight_isPathConnected (s : Finset Puncture)
    (i : Puncture) :
    IsPathConnected (attachmentRight s i : Set (partialPatch (Insert.insert i s))) :=
  (liftedPatch_isPathConnected (Option.some i)).preimage_coe (filling_le_partialPatch_insert s i)

private theorem
    SpecialPeriods.Threefold.attachment_intersection_eq (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) :
    (attachmentLeft s i : Set (partialPatch (Insert.insert i s))) ∩ attachmentRight s i =
      (Subtype.val : partialPatch (Insert.insert i s) → Space) ⁻¹'
        ((liftedPatch Option.none : Set Space) ∩ liftedPatch (Option.some i)) := by
  change
    (Subtype.val : partialPatch (Insert.insert i s) → Space) ⁻¹' (partialPatch s : Set Space) ∩
        (Subtype.val : partialPatch (Insert.insert i s) → Space) ⁻¹'
          (liftedPatch (Option.some i) : Set Space) =
      _
  rw [← Set.preimage_inter, partialPatch_inter_filling_eq s i hi]

private theorem
    SpecialPeriods.Threefold.attachmentIntersection_isPathConnected (s : Finset Puncture)
    (i : Puncture) (hi : i ∉ s) :
    IsPathConnected
      ((attachmentLeft s i : Set (partialPatch (Insert.insert i s))) ∩ attachmentRight s i) := by
  rw [attachment_intersection_eq s i hi]
  exact
    (liftedPatch_regular_inter_isPathConnected i).preimage_coe
      (fun _ hx => regular_le_partialPatch (Insert.insert i s) hx.1)

private def
    SpecialPeriods.Threefold.attachmentCover (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) :
    FundamentalGroupVanKampen.TwoOpenCover (partialPatch (Insert.insert i s))
    where
  U := attachmentLeft s i
  V := attachmentRight s i
  cover := attachmentLeft_union_right s i
  pathConnectedU := attachmentLeft_isPathConnected s i
  pathConnectedV := attachmentRight_isPathConnected s i
  pathConnectedIntersection := attachmentIntersection_isPathConnected s i hi
  base := attachmentBase s i
  baseU := attachmentPoint_mem_partialPatch s i
  baseV := attachmentPoint_mem_filling i

private def SpecialPeriods.Threefold.attachmentLeftHomeomorph (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) : (attachmentCover s i hi).U ≃ₜ partialPatch s :=
  subspacePreimageHomeomorph (partialPatch_le_insert s i)

private def SpecialPeriods.Threefold.attachmentRightHomeomorph (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) : (attachmentCover s i hi).V ≃ₜ liftedPatch (Option.some i) :=
  subspacePreimageHomeomorph (filling_le_partialPatch_insert s i)

private def
    SpecialPeriods.Threefold.attachmentOverlapHomeomorph (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) :
    (attachmentCover s i hi).overlap ≃ₜ
      ((liftedPatch Option.none : Set Space) ∩ liftedPatch (Option.some i) : Set Space) :=
  (subspacePreimageInterHomeomorph (fun _ hx => partialPatch_le_insert s i hx.1)).trans
    (Homeomorph.setCongr (partialPatch_inter_filling_eq s i hi))

private abbrev SpecialPeriods.Threefold.AttachmentGroup (s : Finset Puncture) (i : Puncture) :=
  FundamentalGroup (partialPatch (Insert.insert i s)) (attachmentBase s i)

private abbrev SpecialPeriods.Threefold.PreviousStageGroup (s : Finset Puncture) (i : Puncture) :=
  FundamentalGroup (partialPatch s) ⟨attachmentPoint i, attachmentPoint_mem_partialPatch s i⟩

private abbrev SpecialPeriods.Threefold.FillingGroup (i : Puncture) :=
  FundamentalGroup (liftedPatch (Option.some i))
    ⟨attachmentPoint i, attachmentPoint_mem_filling i⟩

private abbrev SpecialPeriods.Threefold.RegularOverlap (i : Puncture) :=
  ((liftedPatch Option.none : Set Space) ∩ liftedPatch (Option.some i) : Set Space)

private abbrev SpecialPeriods.Threefold.regularOverlapPoint (i : Puncture) : RegularOverlap i :=
  ⟨attachmentPoint i, attachmentPoint_mem_regular i, attachmentPoint_mem_filling i⟩

private abbrev SpecialPeriods.Threefold.RegularOverlapGroup (i : Puncture) :=
  FundamentalGroup (RegularOverlap i) (regularOverlapPoint i)

private def SpecialPeriods.Threefold.previousStageInclusion (s : Finset Puncture) (i : Puncture) :
    C(partialPatch s, partialPatch (Insert.insert i s)) :=
  ⟨fun x => ⟨x.val, partialPatch_le_insert s i x.property⟩, continuous_subtype_val.subtype_mk _⟩

private def SpecialPeriods.Threefold.overlapFillingInclusion (i : Puncture) :
    C(RegularOverlap i, liftedPatch (Option.some i)) :=
  ⟨fun x => ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩

private def SpecialPeriods.Threefold.previousStageHom (s : Finset Puncture) (i : Puncture) :
    PreviousStageGroup s i →* AttachmentGroup s i :=
  FundamentalGroup.map (previousStageInclusion s i)
    ⟨attachmentPoint i, attachmentPoint_mem_partialPatch s i⟩

private def SpecialPeriods.Threefold.overlapFillingHom (i : Puncture) :
    RegularOverlapGroup i →* FillingGroup i :=
  FundamentalGroup.map (overlapFillingInclusion i) (regularOverlapPoint i)

private def SpecialPeriods.Threefold.attachmentLeftGroupEquiv (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) : (attachmentCover s i hi).UGroup ≃* PreviousStageGroup s i :=
  homeomorphFundamentalGroupEquiv (attachmentLeftHomeomorph s i hi)
    (attachmentCover s i hi).baseUPoint

private def SpecialPeriods.Threefold.attachmentRightGroupEquiv (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) : (attachmentCover s i hi).VGroup ≃* FillingGroup i :=
  homeomorphFundamentalGroupEquiv (attachmentRightHomeomorph s i hi)
    (attachmentCover s i hi).baseVPoint

private def
    SpecialPeriods.Threefold.attachmentOverlapGroupEquiv (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) : (attachmentCover s i hi).OverlapGroup ≃* RegularOverlapGroup i :=
  homeomorphFundamentalGroupEquiv (attachmentOverlapHomeomorph s i hi)
    (attachmentCover s i hi).baseOverlapPoint

private theorem SpecialPeriods.Threefold.attachmentLeftGroupEquiv_inclusion (s : Finset Puncture)
    (i : Puncture) (hi : i ∉ s) :
    (previousStageHom s i).comp (attachmentLeftGroupEquiv s i hi).toMonoidHom =
      (attachmentCover s i hi).inclusionHomU := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

private theorem SpecialPeriods.Threefold.attachmentRightGroupEquiv_overlap (s : Finset Puncture)
    (i : Puncture) (hi : i ∉ s) :
    (attachmentRightGroupEquiv s i hi).toMonoidHom.comp (attachmentCover s i hi).overlapHomV =
      (overlapFillingHom i).comp (attachmentOverlapGroupEquiv s i hi).toMonoidHom := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

private def
    SpecialPeriods.Threefold.emptyStageHomeomorph : partialPatch ∅ ≃ₜ liftedPatch Option.none :=
  Homeomorph.setCongr (by rw [partialPatch_empty])

private def SpecialPeriods.Threefold.fullStageHomeomorph : partialPatch Finset.univ ≃ₜ Space
    where
  toFun := Subtype.val
  invFun x := ⟨x, by rw [partialPatch_univ]; trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun :=
    continuous_id.subtype_mk (fun x : Space => by rw [partialPatch_univ]; trivial)

private def SpecialPeriods.Threefold.fullStageFundamentalGroupEquiv (x : partialPatch Finset.univ) :
    FundamentalGroup (partialPatch Finset.univ) x ≃* FundamentalGroup Space x.val :=
  homeomorphFundamentalGroupEquiv fullStageHomeomorph x

private def SpecialPeriods.EllipticFilling.specialLocalData (j : Elliptic.Kind) :
    Elliptic.Equivariant.Data j :=
  localData SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
    SpecialPeriods.specialPeriodMap_generator₂ j

private abbrev SpecialPeriods.EllipticFilling.SpecialFullFilling (j : Elliptic.Kind) :=
  fillingSpace SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
    SpecialPeriods.specialPeriodMap_generator₂ j

@[instance_reducible]
private def SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace (j : Elliptic.Kind) :
    ChartedSpace Elliptic.FamilyModel (SpecialFullFilling j) :=
  fillingChartedSpace SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
    SpecialPeriods.specialPeriodMap_generator₂ j

private def SpecialPeriods.EllipticFilling.specialFullFillingProjection (j : Elliptic.Kind) :
    SpecialFullFilling j → SpecialPeriods.Disc :=
  fillingProjection SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
    SpecialPeriods.specialPeriodMap_generator₂ j

end Mathoverflow1973

end
