/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Elliptic.Core6
import all LeanPool.HopfProblem.Lattice.Core1
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
import all LeanPool.HopfProblem.Uniformization.CuspUniformization2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldGluing1
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Elliptic.Core4
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Foundations.TwoOpenTransition
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods8
import all LeanPool.HopfProblem.Threefold.SpecialPeriods9
import all LeanPool.HopfProblem.Toric.DiagonalQuotient2
import all LeanPool.HopfProblem.Foundations.SplitGroupExtension
import all LeanPool.HopfProblem.Uniformization.CuspUniformization4
import all LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus2
import all LeanPool.HopfProblem.PeriodFamily.Core3
import all LeanPool.HopfProblem.Elliptic.Core6

/-!
# Hopf problem: threefold · special periods 10

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

private def SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian (b : Bool) :
    Path
      (SpecialPeriods.triangleRegularProject
        PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
      (SpecialPeriods.triangleRegularProject
        PeriodFamily.Meridians.normalizedRegularMeridianBasepoint) :=
  if PeriodFamily.Meridians.normalizationReversesMeridians then
    PeriodFamily.Meridians.compatibleRegularMeridian b
  else (PeriodFamily.Meridians.compatibleRegularMeridian b).symm

private theorem
    SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian_coordinate (b : Bool)
    (t : unitInterval) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph (clockwiseRegularMeridian b t) =
      fixedClockwiseMeridian b t := by
  by_cases ho : 0 < RiemannMapping.normalizationOrientation
  · have h := PeriodFamily.Meridians.compatibleRegularMeridian_coordinate b t
    rw [PeriodFamily.Meridians.compatiblePlanarMeridian_eq, ite_eq_left ho] at h
    simpa only [clockwiseRegularMeridian, PeriodFamily.Meridians.normalizationReversesMeridians,
      decide_eq_true_eq.mpr ho, ↓reduceIte, fixedClockwiseMeridian] using h
  · have h := PeriodFamily.Meridians.compatibleRegularMeridian_coordinate b (unitInterval.symm t)
    rw [PeriodFamily.Meridians.compatiblePlanarMeridian_eq, ite_eq_right ho] at h
    simpa only [clockwiseRegularMeridian, PeriodFamily.Meridians.normalizationReversesMeridians,
      decide_eq_false_iff_not.mpr ho, Bool.false_eq_true, ↓reduceIte, fixedClockwiseMeridian,
      Path.symm_apply, Function.comp_apply] using h

private theorem
    SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian_class (b : Bool) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (clockwiseRegularMeridian b)) =
      if PeriodFamily.Meridians.normalizationReversesMeridians then
        PeriodFamily.Meridians.compatibleRegularMeridianClass b
      else (PeriodFamily.Meridians.compatibleRegularMeridianClass b)⁻¹ := by
  by_cases h : PeriodFamily.Meridians.normalizationReversesMeridians = Bool.true
  · simp only [clockwiseRegularMeridian, h, ↓reduceIte]
    rfl
  · have hn : PeriodFamily.Meridians.normalizationReversesMeridians = Bool.false :=
      Bool.eq_false_iff.mpr h
    simp only [clockwiseRegularMeridian, hn, Bool.false_eq_true, ↓reduceIte]
    rw [FundamentalGroup.inv_def]
    exact Path.Homotopic.Quotient.mk_symm _

private def SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.analyticMeridianSquare
    {f : ℂ → ℂ} (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f) (b : Bool)
    (hc : f 0 = SpecialPeriods.EllipticAttachingMeridians.center b) (A : ℂ) (hA : A ≠ 0)
    (hAr : ‖A‖ < D.radius) :
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare (D.analyticCirclePath b hc A hA hAr)
      (SpecialPeriods.EllipticAttachingMeridians.fixedClockwiseMeridian b) :=
  (D.analyticCircleSquare b hc A hA hAr).trans
    (SpecialPeriods.EllipticAttachingMeridians.clockwiseCircleSquare b (deriv f 0 * A)
      (D.linearCoefficient_ne_zero A hA) (D.linearCoefficient_norm_lt_one A hAr))

private def SpecialPeriods.EllipticAttachingMeridians.LinearizationControl.regularMeridianSquare
    {f : ℂ → ℂ} (D : SpecialPeriods.EllipticAttachingMeridians.LinearizationControl f) (b : Bool)
    (hc : f 0 = SpecialPeriods.EllipticAttachingMeridians.center b) (A : ℂ) (hA : A ≠ 0)
    (hAr : ‖A‖ < D.radius) {a : SpecialPeriods.TriangleRegularQuotient} (p : Path a a)
    (hp :
      ∀ t : unitInterval,
        (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph (p t) : ℂ) =
          f (A * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit t)) :
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare p
      (SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian b) := by
  let S := D.analyticMeridianSquare b hc A hA hAr
  refine
    { map :=
        ⟨fun tu => SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm (S.map tu),
          SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm.continuous.comp
            S.map.continuous⟩
      initial := ?_
      final := ?_
      closed := ?_ }
  · intro t
    have he : S.map (0, t) = SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph (p t) := by
      apply Subtype.ext
      exact (congrArg Subtype.val (S.initial t)).trans (hp t).symm
    change SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm (S.map (0, t)) = p t
    rw [he, SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm_apply_apply]
  · intro t
    change
      SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm (S.map (1, t)) =
        SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian b t
    rw [S.final t, ←
      SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian_coordinate b t,
      SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm_apply_apply]
  · intro t
    exact congrArg SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm (S.closed t)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.EllipticGeometry.attachingPlanePartial (j : Elliptic.Kind) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ω :=
  (SpecialPeriods.triangleOrbitCoordinatePartial (.inr j)).symm.trans
    SpecialPeriods.Triangle.trianglePlaneUniformization.toPartialDiffeomorph

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingPlanePartial_source
    (j : Elliptic.Kind) : (attachingPlanePartial j).source = (SpecialPeriods.unitDisc : Set ℂ) := by
  change
    (SpecialPeriods.Triangle.ellipticFullChart j).target ∩
        (SpecialPeriods.Triangle.ellipticFullChart j).symm ⁻¹'
          (Set.univ : Set SpecialPeriods.TriangleOrbitSpace) =
      _
  rw [Set.preimage_univ, Set.inter_univ, SpecialPeriods.Triangle.ellipticFullChart_target]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate (j : Elliptic.Kind) :
    ℂ → ℂ :=
  attachingPlanePartial j

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate_apply
    (j : Elliptic.Kind) (q : ℂ) :
    attachingPlaneCoordinate j q =
      SpecialPeriods.Triangle.trianglePlaneUniformization
        ((SpecialPeriods.Triangle.ellipticFullChart j).symm q) :=
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate_isLocalDiffeomorphAt
    (j : Elliptic.Kind) {q : ℂ} (hq : q ∈ SpecialPeriods.unitDisc) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (attachingPlaneCoordinate j) q := by
  apply (attachingPlanePartial j).isLocalDiffeomorphAt _ _ _
  rwa [attachingPlanePartial_source]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate_analyticAt
    (j : Elliptic.Kind) {q : ℂ} (hq : q ∈ SpecialPeriods.unitDisc) :
    AnalyticAt ℂ (attachingPlaneCoordinate j) q :=
  (attachingPlaneCoordinate_isLocalDiffeomorphAt j hq).contMDiffAt.contDiffAt.analyticAt

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate_deriv_ne_zero
    (j : Elliptic.Kind) {q : ℂ} (hq : q ∈ SpecialPeriods.unitDisc) :
    deriv (attachingPlaneCoordinate j) q ≠ 0 :=
  SpecialPeriods.MuTorsor.SourceOrders.deriv_ne_zero_of_isLocalDiffeomorph
    (attachingPlaneCoordinate_isLocalDiffeomorphAt j hq)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate_analyticAt_zero
    (j : Elliptic.Kind) : AnalyticAt ℂ (attachingPlaneCoordinate j) 0 :=
  attachingPlaneCoordinate_analyticAt j (by simp [SpecialPeriods.unitDisc])

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate_deriv_zero_ne_zero
    (j : Elliptic.Kind) : deriv (attachingPlaneCoordinate j) 0 ≠ 0 :=
  attachingPlaneCoordinate_deriv_ne_zero j (by simp [SpecialPeriods.unitDisc])

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate_zero
    (j : Elliptic.Kind) :
    attachingPlaneCoordinate j 0 =
      SpecialPeriods.Triangle.trianglePlaneUniformization
        (SpecialPeriods.Triangle.ellipticOrbitCenter j) := by
  rw [attachingPlaneCoordinate_apply, ← SpecialPeriods.Triangle.ellipticFullChart_center j]
  rw [(SpecialPeriods.Triangle.ellipticFullChart j).left_inv
      (SpecialPeriods.Triangle.ellipticFullChart_center_mem_source j)]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate_three_zero :
    attachingPlaneCoordinate .three 0 = 0 := by
  rw [attachingPlaneCoordinate_zero, SpecialPeriods.Triangle.ellipticOrbitCenter_three,
    SpecialPeriods.Triangle.trianglePlaneUniformization_centerOne]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate_four_zero :
    attachingPlaneCoordinate .four 0 = 1 := by
  rw [attachingPlaneCoordinate_zero, SpecialPeriods.Triangle.ellipticOrbitCenter_four,
    SpecialPeriods.Triangle.trianglePlaneUniformization_centerTwo]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.EllipticGeometry.attaching_compactInverse_eq (j : Elliptic.Kind)
    (q : ℂ) :
    (SpecialPeriods.Threefold.punctureChart (Option.some j)).symm q =
      SpecialPeriods.triangleOpenInclusion
        ((SpecialPeriods.Triangle.ellipticFullChart j).symm q) :=
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate_compactInverse
    (j : Elliptic.Kind) (q : ℂ) :
    SpecialPeriods.Triangle.triangleSphereUniformization
        ((SpecialPeriods.Threefold.punctureChart (Option.some j)).symm q) =
      ((attachingPlaneCoordinate j q : ℂ) : RiemannSphere) := by
  rw [attaching_compactInverse_eq,
    SpecialPeriods.Triangle.triangleSphereUniformization_openInclusion]
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate_eq_regularPlane
    (j : Elliptic.Kind) (q : ℂ) (x : SpecialPeriods.TriangleRegularQuotient)
    (hx :
      SpecialPeriods.Threefold.regularInclusion x =
        (SpecialPeriods.Threefold.punctureChart (Option.some j)).symm q) :
    (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph x : ℂ) =
      attachingPlaneCoordinate j q := by
  apply OnePoint.coe_injective (X := ℂ)
  calc
    ((SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph x : ℂ) : RiemannSphere) =
        SpecialPeriods.Triangle.triangleSphereUniformization
          (SpecialPeriods.Threefold.regularInclusion x) :=
      rfl
    _ =
        SpecialPeriods.Triangle.triangleSphereUniformization
          ((SpecialPeriods.Threefold.punctureChart (Option.some j)).symm q) :=
      (congrArg SpecialPeriods.Triangle.triangleSphereUniformization hx)
    _ = ((attachingPlaneCoordinate j q : ℂ) : RiemannSphere) :=
      attachingPlaneCoordinate_compactInverse j q

private def SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex : Elliptic.Kind → Bool
  | .three => Bool.false
  | .four => Bool.true

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneCoordinate_zero_eq_center
    (j : Elliptic.Kind) :
    attachingPlaneCoordinate j 0 =
      SpecialPeriods.EllipticAttachingMeridians.center (attachingMeridianIndex j) := by
  cases j with
  | three => exact attachingPlaneCoordinate_three_zero
  | four => exact attachingPlaneCoordinate_four_zero

private def SpecialPeriods.Threefold.EllipticGeometry.attachingPlaneControl (j : Elliptic.Kind) :
    SpecialPeriods.EllipticAttachingMeridians.LinearizationControl (attachingPlaneCoordinate j) :=
  SpecialPeriods.EllipticAttachingMeridians.analyticLinearizationControl
    (attachingPlaneCoordinate_analyticAt_zero j) (attachingPlaneCoordinate_deriv_zero_ne_zero j)

private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianRadius (j : Elliptic.Kind) : ℝ :=
  Min.min (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (attachingPlaneControl j).radius

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianRadius_pos
    (j : Elliptic.Kind) : 0 < attachingMeridianRadius j :=
  lt_min (SpecialPeriods.Threefold.specialBaseCover.radius_pos (Option.some j))
    (attachingPlaneControl j).radius_pos

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianRadius_le_filling
    (j : Elliptic.Kind) :
    attachingMeridianRadius j ≤
      SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j) :=
  min_le_left _ _

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianRadius_le_control
    (j : Elliptic.Kind) : attachingMeridianRadius j ≤ (attachingPlaneControl j).radius :=
  min_le_right _ _

private theorem SpecialPeriods.Threefold.EllipticGeometry.exists_small_attaching_parameters
    (j : Elliptic.Kind) :
    ∃ s₀ : ℂ,
      0 < s₀.im ∧ ‖CuspUniformization.exponential s₀‖ ^ j.order < attachingMeridianRadius j :=
  Elliptic.LogGauge.exists_logMeridian_parameters j (attachingMeridianRadius j)
    (attachingMeridianRadius_pos j)

private theorem SpecialPeriods.Threefold.EllipticGeometry.attaching_parameters_filling_bound
    (j : Elliptic.Kind) {s₀ : ℂ}
    (hr : ‖CuspUniformization.exponential s₀‖ ^ j.order < attachingMeridianRadius j) :
    ‖CuspUniformization.exponential s₀‖ ^ j.order <
      SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j) :=
  hr.trans_le (attachingMeridianRadius_le_filling j)

private theorem SpecialPeriods.Threefold.EllipticGeometry.attaching_parameters_control_bound
    (j : Elliptic.Kind) {s₀ : ℂ}
    (hr : ‖CuspUniformization.exponential s₀‖ ^ j.order < attachingMeridianRadius j) :
    ‖CuspUniformization.exponential s₀ ^ j.order‖ < (attachingPlaneControl j).radius := by
  rw [norm_pow]
  exact hr.trans_le (attachingMeridianRadius_le_control j)

private theorem SpecialPeriods.Threefold.EllipticGeometry.attaching_initial_coordinate_ne_zero
    (j : Elliptic.Kind) (s₀ : ℂ) : CuspUniformization.exponential s₀ ^ j.order ≠ 0 :=
  pow_ne_zero j.order (CuspUniformization.exponential_ne_zero s₀)

private theorem SpecialPeriods.Threefold.EllipticGeometry.attaching_log_parameter_clockwise
    (j : Elliptic.Kind) (s₀ : ℂ) (t : (unitInterval)) :
    CuspUniformization.exponential (s₀ - ((t : ℝ) : ℂ) / (j.order : ℂ)) ^ j.order =
      CuspUniformization.exponential s₀ ^ j.order *
        SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit t := by
  have hn : (j.order : ℂ) ≠ 0 := by exact_mod_cast j.order_pos.ne'
  simp only [CuspUniformization.exponential,
    SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  field_simp
  ring

public
theorem SpecialPeriods.EllipticAttachingMeridians.homotopic_conjugate_map_eq {X : Type*}
    [TopologicalSpace X] {b : X} {G : Type*} [Group G] {p q : Path b b} (K : Path b b)
    (h : p.Homotopic (K.trans (q.trans K.symm))) (φ : FundamentalGroup X b →* G)
    (hcomm : ∀ g h : G, Commute g h) :
    φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) := by
  have hclass :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk K))⁻¹ *
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk K) :=
    Path.Homotopic.Quotient.eq.mpr h
  rw [hclass, map_mul, map_mul, map_inv]
  exact (hcomm _ _).inv_mul_cancel

private theorem SpecialPeriods.EllipticAttachingMeridians.LoopSquare.map_whisker_eq {X : Type*}
    [TopologicalSpace X] {a b : X} {G : Type*} [Group G] {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (τ : Path b a)
    (φ : FundamentalGroup X b →* G) (hcomm : ∀ g h : G, Commute g h) :
    φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (τ.trans (p.trans τ.symm)))) =
      φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) :=
  SpecialPeriods.EllipticAttachingMeridians.homotopic_conjugate_map_eq (τ.trans S.tail)
    (S.homotopic_whisker_conjugate τ) φ hcomm

private abbrev
    SpecialPeriods.Threefold.EllipticGeometry.attachingFullLoop (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) :=
  Elliptic.LogGauge.logMeridianLoop (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
    (Elliptic.mainTwist_admissible j) s₀ hs₀

@[simp]
private theorem
    SpecialPeriods.Threefold.EllipticGeometry.attachingFullLoop_projection (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : (unitInterval)) :
    (SpecialPeriods.EllipticFilling.specialFullFillingProjection j
          (attachingFullLoop j s₀ hs₀ t) :
        ℂ) =
      (Elliptic.LogGauge.logMeridianRoot j s₀ hs₀ t : ℂ) ^ j.order :=
  rfl

private theorem
    SpecialPeriods.Threefold.EllipticGeometry.attachingFullLoop_mem_piece (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (t : (unitInterval)) :
    attachingFullLoop j s₀ hs₀ t ∈
      SpecialPeriods.EllipticFilling.pieceDomain SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
        SpecialPeriods.Threefold.specialBaseCover j := by
  change
    ‖(SpecialPeriods.EllipticFilling.specialFullFillingProjection j
            (attachingFullLoop j s₀ hs₀ t) :
          ℂ)‖ <
      _
  rw [attachingFullLoop_projection, Elliptic.LogGauge.logMeridianRoot_pow_norm]
  exact hr

private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingBasepoint (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    LocalSpace j :=
  ⟨attachingFullLoop j s₀ hs₀ 0, attachingFullLoop_mem_piece j s₀ hs₀ hr 0⟩

private def SpecialPeriods.Threefold.EllipticGeometry.attachingLoop (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    Path (attachingBasepoint j s₀ hs₀ hr) (attachingBasepoint j s₀ hs₀ hr)
    where
  toFun t := ⟨attachingFullLoop j s₀ hs₀ t, attachingFullLoop_mem_piece j s₀ hs₀ hr t⟩
  continuous_toFun := (attachingFullLoop j s₀ hs₀).continuous.subtype_mk _
  source' := rfl
  target' := Subtype.ext (attachingFullLoop j s₀ hs₀).target

private theorem SpecialPeriods.Threefold.EllipticGeometry.parameter_attachingLoop_ne_zero
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (t : (unitInterval)) : parameter j (attachingLoop j s₀ hs₀ hr t) ≠ 0 :=
  pow_ne_zero j.order (Elliptic.LogGauge.logMeridianRoot_ne_zero j s₀ hs₀ t)

private theorem SpecialPeriods.Threefold.EllipticGeometry.projectionToBase_attachingLoop
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (t : (unitInterval)) :
    SpecialPeriods.Threefold.specialEllipticPieceProjectionToBase j
        (attachingLoop j s₀ hs₀ hr t) =
      (SpecialPeriods.Threefold.punctureChart (Option.some j)).symm
        ((Elliptic.LogGauge.logMeridianRoot j s₀ hs₀ t : ℂ) ^ j.order) :=
  rfl

private theorem SpecialPeriods.Threefold.EllipticGeometry.projectionToBase_attachingLoop_mem_regular
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (t : (unitInterval)) :
    SpecialPeriods.Threefold.specialEllipticPieceProjectionToBase j
        (attachingLoop j s₀ hs₀ hr t) ∈
      SpecialPeriods.Threefold.regularPatch :=
  (SpecialPeriods.EllipticFilling.pieceProjectionToBase_mem_regular_iff
        SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
        SpecialPeriods.specialPeriodMap_generator₂ SpecialPeriods.Threefold.specialBaseCover j
        _).mpr
    (parameter_attachingLoop_ne_zero j s₀ hs₀ hr t)

private def SpecialPeriods.Threefold.EllipticGeometry.pieceSurfaceRetractionFundamentalGroupEquiv
    (j : Elliptic.Kind) (x : LocalSpace j) :
    FundamentalGroup (LocalSpace j) x ≃*
      FundamentalGroup (SpecialPeriods.EllipticFilling.SpecialCentralSurface j)
        (pieceSurfaceRetraction j x) :=
  EllipticRetractionTopology.fundamentalGroupEquivAt (pieceSurfaceHomotopyEquiv j).symm x

private abbrev
    SpecialPeriods.Threefold.EllipticGeometry.attachingFlatBase (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) : RealPlane₄ :=
  Elliptic.LogGauge.logMeridianFlat (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist s₀
    hs₀ 0

private theorem SpecialPeriods.Threefold.EllipticGeometry.pieceSurfaceRetraction_attachingBasepoint
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    pieceSurfaceRetraction j (attachingBasepoint j s₀ hs₀ hr) =
      Elliptic.affineCoverProjection j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j) (attachingFlatBase j s₀ hs₀) :=
  Elliptic.LogGauge.fillingSurfaceRetraction_quotient_flat
    (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist (Elliptic.mainTwist_admissible j)
    (Elliptic.LogGauge.logMeridianRoot j s₀ hs₀ 0) (attachingFlatBase j s₀ hs₀)

private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingDeckEquiv (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    FundamentalGroup (LocalSpace j) (attachingBasepoint j s₀ hs₀ hr) ≃*
      Elliptic.AffineDeckGroup j j.twist :=
  (pieceSurfaceRetractionFundamentalGroupEquiv j (attachingBasepoint j s₀ hs₀ hr)).trans
    ((MulEquiv.cast (M :=
          FundamentalGroup (SpecialPeriods.EllipticFilling.SpecialCentralSurface j))
          (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr)).trans
      (Elliptic.surfaceFundamentalGroupDeckEquiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)))

private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingRetractionLoop (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    Path
      (Elliptic.affineCoverProjection j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j) (attachingFlatBase j s₀ hs₀))
      (Elliptic.affineCoverProjection j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)) :=
  ((attachingLoop j s₀ hs₀ hr).map (pieceSurfaceRetraction j).continuous).cast
    (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr).symm
    (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr).symm

private theorem
    SpecialPeriods.Threefold.EllipticGeometry.attachingRetractionLoop_eq (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    attachingRetractionLoop j s₀ hs₀ hr =
      Elliptic.LogGauge.logMeridianSurfaceLoop (SpecialPeriods.EllipticFilling.specialLocalData j)
        j.twist (Elliptic.mainTwist_admissible j) s₀ hs₀ := by
  ext t
  rfl

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingDeckEquiv_attachingLoop
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    attachingDeckEquiv j s₀ hs₀ hr (FundamentalGroup.fromPath ⟦attachingLoop j s₀ hs₀ hr⟧) =
      (Elliptic.deckGenerator j j.twist)⁻¹ := by
  change
    Elliptic.surfaceFundamentalGroupDeckEquiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)
        (MulEquiv.cast (M :=
          FundamentalGroup (SpecialPeriods.EllipticFilling.SpecialCentralSurface j))
          (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr)
          (FundamentalGroup.fromPath
            ⟦(attachingLoop j s₀ hs₀ hr).map (pieceSurfaceRetraction j).continuous⟧)) =
      _
  rw [Elliptic.LogGauge.fundamentalGroup_cast_loop]
  change
    Elliptic.surfaceFundamentalGroupDeckEquiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)
        (FundamentalGroup.fromPath ⟦attachingRetractionLoop j s₀ hs₀ hr⟧) =
      _
  rw [attachingRetractionLoop_eq]
  exact
    Elliptic.LogGauge.surfaceFundamentalGroupDeckEquiv_logMeridian
      (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
      (Elliptic.mainTwist_admissible j) s₀ hs₀

private abbrev SpecialPeriods.Threefold.EllipticGeometry.attachingFibreFullLoop (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) (w : Lattice) :=
  Elliptic.LogGauge.fibreTranslationLoop (SpecialPeriods.EllipticFilling.specialLocalData j)
    j.twist (Elliptic.mainTwist_admissible j) (Elliptic.LogGauge.logMeridianRoot j s₀ hs₀ 0)
    (attachingFlatBase j s₀ hs₀) w

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingFibreFullLoop_projection
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (w : Lattice) (t : (unitInterval)) :
    (SpecialPeriods.EllipticFilling.specialFullFillingProjection j
          (attachingFibreFullLoop j s₀ hs₀ w t) :
        ℂ) =
      CuspUniformization.exponential s₀ ^ j.order := by
  change (Elliptic.LogGauge.logMeridianRoot j s₀ hs₀ 0 : ℂ) ^ j.order = _
  rw [Elliptic.LogGauge.logMeridianRoot_zero]

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingFibreFullLoop_mem_piece
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) (t : (unitInterval)) :
    attachingFibreFullLoop j s₀ hs₀ w t ∈
      SpecialPeriods.EllipticFilling.pieceDomain SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
        SpecialPeriods.Threefold.specialBaseCover j := by
  change
    ‖(SpecialPeriods.EllipticFilling.specialFullFillingProjection j
            (attachingFibreFullLoop j s₀ hs₀ w t) :
          ℂ)‖ <
      _
  rw [attachingFibreFullLoop_projection, norm_pow]
  exact hr

private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingFibreLoop (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) : Path (attachingBasepoint j s₀ hs₀ hr) (attachingBasepoint j s₀ hs₀ hr)
    where
  toFun
    t := ⟨attachingFibreFullLoop j s₀ hs₀ w t, attachingFibreFullLoop_mem_piece j s₀ hs₀ hr w t⟩
  continuous_toFun := (attachingFibreFullLoop j s₀ hs₀ w).continuous.subtype_mk _
  source' := Subtype.ext (attachingFibreFullLoop j s₀ hs₀ w).source
  target' := Subtype.ext (attachingFibreFullLoop j s₀ hs₀ w).target

@[simp]
private theorem
    SpecialPeriods.Threefold.EllipticGeometry.parameter_attachingFibreLoop (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) (t : (unitInterval)) :
    parameter j (attachingFibreLoop j s₀ hs₀ hr w t) =
      CuspUniformization.exponential s₀ ^ j.order :=
  attachingFibreFullLoop_projection j s₀ hs₀ w t

private theorem SpecialPeriods.Threefold.EllipticGeometry.parameter_attachingFibreLoop_ne_zero
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) (t : (unitInterval)) : parameter j (attachingFibreLoop j s₀ hs₀ hr w t) ≠ 0 := by
  rw [parameter_attachingFibreLoop]
  exact pow_ne_zero j.order (CuspUniformization.exponential_ne_zero s₀)

private theorem
    SpecialPeriods.Threefold.EllipticGeometry.projectionToBase_attachingFibreLoop_mem_regular
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) (t : (unitInterval)) :
    SpecialPeriods.Threefold.specialEllipticPieceProjectionToBase j
        (attachingFibreLoop j s₀ hs₀ hr w t) ∈
      SpecialPeriods.Threefold.regularPatch :=
  (SpecialPeriods.EllipticFilling.pieceProjectionToBase_mem_regular_iff
        SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
        SpecialPeriods.specialPeriodMap_generator₂ SpecialPeriods.Threefold.specialBaseCover j
        _).mpr
    (parameter_attachingFibreLoop_ne_zero j s₀ hs₀ hr w t)

private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingFibreRetractionLoop (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) :
    Path
      (Elliptic.affineCoverProjection j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j) (attachingFlatBase j s₀ hs₀))
      (Elliptic.affineCoverProjection j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)) :=
  ((attachingFibreLoop j s₀ hs₀ hr w).map (pieceSurfaceRetraction j).continuous).cast
    (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr).symm
    (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr).symm

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingFibreRetractionLoop_eq
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) :
    attachingFibreRetractionLoop j s₀ hs₀ hr w =
      Elliptic.LogGauge.fibreTranslationSurfaceLoop
        (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
        (Elliptic.mainTwist_admissible j) (Elliptic.LogGauge.logMeridianRoot j s₀ hs₀ 0)
        (attachingFlatBase j s₀ hs₀) w := by
  ext t
  rfl

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingDeckEquiv_attachingFibreLoop
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) :
    attachingDeckEquiv j s₀ hs₀ hr
        (FundamentalGroup.fromPath ⟦attachingFibreLoop j s₀ hs₀ hr w⟧) =
      Elliptic.deckTranslationHom j j.twist (Multiplicative.ofAdd (-w)) := by
  change
    Elliptic.surfaceFundamentalGroupDeckEquiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)
        (MulEquiv.cast (M :=
          FundamentalGroup (SpecialPeriods.EllipticFilling.SpecialCentralSurface j))
          (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr)
          (FundamentalGroup.fromPath
            ⟦(attachingFibreLoop j s₀ hs₀ hr w).map (pieceSurfaceRetraction j).continuous⟧)) =
      _
  rw [Elliptic.LogGauge.fundamentalGroup_cast_loop]
  change
    Elliptic.surfaceFundamentalGroupDeckEquiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)
        (FundamentalGroup.fromPath ⟦attachingFibreRetractionLoop j s₀ hs₀ hr w⟧) =
      _
  rw [attachingFibreRetractionLoop_eq]
  exact
    Elliptic.LogGauge.fibreTranslationSurfaceLoop_deck
      (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
      (Elliptic.mainTwist_admissible j) (Elliptic.LogGauge.logMeridianRoot j s₀ hs₀ 0)
      (attachingFlatBase j s₀ hs₀) w

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingUpstairsPoint (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) (t : (unitInterval)) : SpecialPeriods.TriangleRegularPoint :=
  SpecialPeriods.EllipticFilling.localBase j
    (Elliptic.LogGauge.logMeridianRootStar (j := j) s₀ hs₀ t)

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingUpstairsPoint_continuous
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (attachingUpstairsPoint j s₀ hs₀) :=
  (SpecialPeriods.EllipticFilling.localBase_continuous j).comp
    (Elliptic.LogGauge.logMeridianRootStar_continuous s₀ hs₀)

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem
    SpecialPeriods.Threefold.EllipticGeometry.attachingUpstairsPoint_one (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    attachingUpstairsPoint j s₀ hs₀ 1 =
      SpecialPeriods.Triangle.ellipticGenerator j • attachingUpstairsPoint j s₀ hs₀ 0 := by
  have hr :
    Elliptic.LogGauge.logMeridianRootStar (j := j) s₀ hs₀ 1 =
      SpecialPeriods.EllipticFilling.puncturedRotation j
        (Elliptic.LogGauge.logMeridianRootStar (j := j) s₀ hs₀ 0) :=
    Subtype.ext (Elliptic.LogGauge.logMeridianRoot_one j s₀ hs₀)
  unfold attachingUpstairsPoint
  rw [hr, SpecialPeriods.EllipticFilling.localBase_rotation]

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingFlatBase_eq_negativeLog
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    attachingFlatBase j s₀ hs₀ =
      ((SpecialPeriods.EllipticFilling.specialLocalData j).periods.periodEquiv
            (Elliptic.LogGauge.logMeridianRoot j s₀ hs₀ 0)).symm
        (-s₀ •
          Elliptic.LogGauge.periodVector
            (SpecialPeriods.EllipticFilling.specialLocalData j).periods j.twist
            (Elliptic.LogGauge.logMeridianRoot j s₀ hs₀ 0)) := by
  change
    ((SpecialPeriods.EllipticFilling.specialLocalData j).periods.periodEquiv _).symm
        (-Elliptic.LogGauge.logMeridianParameter j s₀ 0 •
          Elliptic.LogGauge.periodVector
            (SpecialPeriods.EllipticFilling.specialLocalData j).periods j.twist _) =
      _
  rw [Elliptic.LogGauge.logMeridianParameter_zero]

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.specialPuncturedOverlap_eq_gauge
    (j : Elliptic.Kind)
    (x :
      SpecialPeriods.EllipticFilling.MainFillingStar SpecialPeriods.specialPeriodMap j
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂) :
    (SpecialPeriods.EllipticFilling.puncturedFillingBiholomorph SpecialPeriods.specialPeriodMap j
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
          x).val =
      (SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph
          SpecialPeriods.specialPeriodMap j SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂
          (Elliptic.LogGauge.fillingToTautologicalBiholomorph
            (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
            (Elliptic.mainTwist_admissible j) x)).val :=
  rfl

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem
    SpecialPeriods.Threefold.EllipticGeometry.smallOverlap_attachingLoop (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (t : (unitInterval)) :
    SpecialPeriods.EllipticFilling.smallOverlap SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
        SpecialPeriods.Threefold.specialBaseCover j (attachingLoop j s₀ hs₀ hr t) =
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂).quotient
        (attachingUpstairsPoint j s₀ hs₀ t, 0) := by
  rw [SpecialPeriods.EllipticFilling.smallOverlap_apply_mainStar SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
      SpecialPeriods.Threefold.specialBaseCover j _
      (parameter_attachingLoop_ne_zero j s₀ hs₀ hr t),
    specialPuncturedOverlap_eq_gauge]
  change
    (SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph SpecialPeriods.specialPeriodMap
          j SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
          (Elliptic.LogGauge.fillingToTautologicalBiholomorph
            (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
            (Elliptic.mainTwist_admissible j)
            (Elliptic.LogGauge.logMeridianFillingPoint
              (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
              (Elliptic.mainTwist_admissible j) s₀ hs₀ t))).val =
      _
  rw [Elliptic.LogGauge.fillingToTautological_logMeridian]
  change
    (SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph SpecialPeriods.specialPeriodMap
          j SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
          (Elliptic.LogGauge.starProject (SpecialPeriods.EllipticFilling.specialLocalData j) 0
            (Matrix.mulVec_zero j.matrix)
            (Elliptic.LogGauge.zeroSection
              (SpecialPeriods.EllipticFilling.specialLocalData j).periods
              (Elliptic.LogGauge.logMeridianRootStar (j := j) s₀ hs₀ t)))).val =
      _
  exact
    congrArg Subtype.val
      (SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph_project
        SpecialPeriods.specialPeriodMap j SpecialPeriods.specialPeriodMap_generator₁
        SpecialPeriods.specialPeriodMap_generator₂
        (Elliptic.LogGauge.zeroSection (SpecialPeriods.EllipticFilling.specialLocalData j).periods
          (Elliptic.LogGauge.logMeridianRootStar (j := j) s₀ hs₀ t)))

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.smallOverlap_attachingFibreLoop
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) (t : (unitInterval)) :
    SpecialPeriods.EllipticFilling.smallOverlap SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
        SpecialPeriods.Threefold.specialBaseCover j (attachingFibreLoop j s₀ hs₀ hr w t) =
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂).quotient
        (attachingUpstairsPoint j s₀ hs₀ 0,
          standardLattice.mkQ ((t : ℝ) • Elliptic.realCast w)) := by
  rw [SpecialPeriods.EllipticFilling.smallOverlap_apply_mainStar SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
      SpecialPeriods.Threefold.specialBaseCover j _
      (parameter_attachingFibreLoop_ne_zero j s₀ hs₀ hr w t),
    specialPuncturedOverlap_eq_gauge]
  change
    (SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph SpecialPeriods.specialPeriodMap
          j SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
          (Elliptic.LogGauge.fillingToTautologicalBiholomorph
            (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
            (Elliptic.mainTwist_admissible j)
            (Elliptic.LogGauge.fibreTranslationFillingPoint
              (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
              (Elliptic.mainTwist_admissible j)
              (Elliptic.LogGauge.logMeridianRootStar (j := j) s₀ hs₀ 0)
              (attachingFlatBase j s₀ hs₀) w t))).val =
      _
  rw [attachingFlatBase_eq_negativeLog]
  have hg :=
    Elliptic.LogGauge.fillingToTautological_fibreTranslation
      (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
      (Elliptic.mainTwist_admissible j) (Elliptic.LogGauge.logMeridianRootStar (j := j) s₀ hs₀ 0)
      w s₀ (Elliptic.LogGauge.logMeridianRoot_zero j s₀ hs₀).symm t
  refine
    (congrArg
          (fun q :
              Elliptic.LogGauge.TautologicalStar
                (SpecialPeriods.EllipticFilling.specialLocalData j) =>
            (SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph
                SpecialPeriods.specialPeriodMap j SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂ q).val)
          hg).trans
      ?_
  refine
    (congrArg Subtype.val
          (SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph_project
            SpecialPeriods.specialPeriodMap j SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂
            (Elliptic.LogGauge.fibreTranslationFamilyStar
              (SpecialPeriods.EllipticFilling.specialLocalData j)
              (Elliptic.LogGauge.logMeridianRootStar (j := j) s₀ hs₀ 0) 0 w t))).trans
      ?_
  change
    (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂).quotient
        (attachingUpstairsPoint j s₀ hs₀ 0,
          standardLattice.mkQ (0 + (t : ℝ) • Elliptic.realCast w)) =
      _
  rw [zero_add]

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.specialEllipticOverlap_attachingLoop
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (t : (unitInterval)) :
    SpecialPeriods.Threefold.specialEllipticOverlap j (attachingLoop j s₀ hs₀ hr t) =
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂).quotient
        (attachingUpstairsPoint j s₀ hs₀ t, 0) :=
  smallOverlap_attachingLoop j s₀ hs₀ hr t

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem SpecialPeriods.Threefold.EllipticGeometry.specialEllipticOverlap_attachingFibreLoop
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) (t : (unitInterval)) :
    SpecialPeriods.Threefold.specialEllipticOverlap j (attachingFibreLoop j s₀ hs₀ hr w t) =
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂).quotient
        (attachingUpstairsPoint j s₀ hs₀ 0,
          standardLattice.mkQ ((t : ℝ) • Elliptic.realCast w)) :=
  smallOverlap_attachingFibreLoop j s₀ hs₀ hr w t

private theorem SpecialPeriods.Threefold.previousStageHom_surjective_of_overlapFillingHom_surjective
    (s : Finset Puncture) (i : Puncture) (hi : i ∉ s)
    (hF : Function.Surjective (overlapFillingHom i)) :
    Function.Surjective (previousStageHom s i) := by
  have hV : Function.Surjective (attachmentCover s i hi).overlapHomV := by
    intro γ
    obtain ⟨δ, hδ⟩ := hF (attachmentRightGroupEquiv s i hi γ)
    obtain ⟨ε, hε⟩ := (attachmentOverlapGroupEquiv s i hi).surjective δ
    refine ⟨ε, (attachmentRightGroupEquiv s i hi).injective ?_⟩
    exact
      (DFunLike.congr_fun (attachmentRightGroupEquiv_overlap s i hi) ε).trans
        ((congrArg (overlapFillingHom i) hε).trans hδ)
  intro γ
  obtain ⟨δ, hδ⟩ :=
    (attachmentCover s i hi).inclusionHomU_surjective_of_overlapHomV_surjective hV γ
  exact
    ⟨attachmentLeftGroupEquiv s i hi δ,
      (DFunLike.congr_fun (attachmentLeftGroupEquiv_inclusion s i hi) δ).trans hδ⟩

private def SpecialPeriods.Threefold.stageRegularInclusion (s : Finset Puncture) :
    C(liftedPatch Option.none, partialPatch s) :=
  ⟨fun x => ⟨x.val, regular_le_partialPatch s x.property⟩, continuous_subtype_val.subtype_mk _⟩

private theorem SpecialPeriods.Threefold.stageRegularInclusion_empty_fundamentalGroup_map_surjective
    (x : liftedPatch Option.none) :
    Function.Surjective (FundamentalGroup.map (stageRegularInclusion ∅) x) := by
  exact (homeomorphFundamentalGroupEquiv emptyStageHomeomorph.symm x).surjective

private theorem SpecialPeriods.Threefold.stageRegularInclusion_insert_fundamentalGroup_map
    (s : Finset Puncture) (i : Puncture) (x : liftedPatch Option.none) :
    (FundamentalGroup.map (previousStageInclusion s i) (stageRegularInclusion s x)).comp
        (FundamentalGroup.map (stageRegularInclusion s) x) =
      FundamentalGroup.map (stageRegularInclusion (Insert.insert i s)) x := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

private theorem SpecialPeriods.Threefold.stageRegularInclusion_fundamentalGroup_map_surjective
    (hF : ∀ i : Puncture, Function.Surjective (overlapFillingHom i)) (s : Finset Puncture)
    (x : liftedPatch Option.none) :
    Function.Surjective (FundamentalGroup.map (stageRegularInclusion s) x) := by
  induction s using Finset.induction_on with
  | empty => exact stageRegularInclusion_empty_fundamentalGroup_map_surjective x
  | @insert i s hi ih =>
    have := partialPatch_pathConnectedSpace s
    have hprev :=
      fundamentalGroup_map_surjective_at_of_pathConnected (previousStageInclusion s i)
        ⟨attachmentPoint i, attachmentPoint_mem_partialPatch s i⟩ (stageRegularInclusion s x)
        (previousStageHom_surjective_of_overlapFillingHom_surjective s i hi (hF i))
    have hcomp := hprev.comp ih
    rw [← stageRegularInclusion_insert_fundamentalGroup_map s i x]
    exact hcomp

private def SpecialPeriods.Threefold.regularLiftedInclusion : C(liftedPatch Option.none, Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private theorem SpecialPeriods.Threefold.regularLiftedInclusion_fundamentalGroup_map_surjective
    (hF : ∀ i : Puncture, Function.Surjective (overlapFillingHom i))
    (x : liftedPatch Option.none) :
    Function.Surjective (FundamentalGroup.map regularLiftedInclusion x) := by
  have hstage := stageRegularInclusion_fundamentalGroup_map_surjective hF Finset.univ x
  have hfull := (fullStageFundamentalGroupEquiv (stageRegularInclusion Finset.univ x)).surjective
  have hmap :
    (fullStageFundamentalGroupEquiv (stageRegularInclusion Finset.univ x)).toMonoidHom.comp
        (FundamentalGroup.map (stageRegularInclusion Finset.univ) x) =
      FundamentalGroup.map regularLiftedInclusion x := by
    ext γ
    obtain ⟨p⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    rfl
  rw [← hmap]
  exact hfull.comp hstage

private def SpecialPeriods.EllipticAttachingSurjectivity.fullCover (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) :
    SpecialPeriods.Disc × ComplexPlane₂ → SpecialPeriods.EllipticFilling.fillingSpace P h₁ h₂ j :=
  SpecialPeriods.EllipticFilling.fillingQuotient P h₁ h₂ j ∘
    (SpecialPeriods.EllipticFilling.localPeriods P j).quotientMap

@[simp]
private theorem SpecialPeriods.EllipticAttachingSurjectivity.fullCover_projection_coe
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (x : SpecialPeriods.Disc × ComplexPlane₂) :
    (SpecialPeriods.EllipticFilling.fillingProjection P h₁ h₂ j (fullCover P h₁ h₂ j x) : ℂ) =
      (x.1 : ℂ) ^ j.order :=
  rfl

private theorem SpecialPeriods.EllipticAttachingSurjectivity.fillingQuotient_finite_fibre
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (y : SpecialPeriods.EllipticFilling.fillingSpace P h₁ h₂ j) :
    Finite (SpecialPeriods.EllipticFilling.fillingQuotient P h₁ h₂ j ⁻¹' { y }) := by
  apply Nat.finite_of_card_ne_zero
  have hcard :=
    (SpecialPeriods.EllipticFilling.localData P h₁ h₂ j).quotient_fibre_card j.twist
      (Elliptic.mainTwist_admissible j) y
  change
    Nat.card (SpecialPeriods.EllipticFilling.fillingQuotient P h₁ h₂ j ⁻¹' { y }) =
      j.order at hcard
  rw [hcard]
  exact j.order_pos.ne'

private theorem SpecialPeriods.EllipticAttachingSurjectivity.fullCover_isCoveringMap
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : IsCoveringMap (fullCover P h₁ h₂ j) := by
  let := (SpecialPeriods.EllipticFilling.localPeriods P j).coveringAction
  exact
    CoveringComposition.covering_comp_of_finite_fibres
      (SpecialPeriods.EllipticFilling.localPeriods P j).quotientCoveringMap.isCoveringMap
      (SpecialPeriods.EllipticFilling.fillingQuotient_isCoveringMap P h₁ h₂ j)
      (fillingQuotient_finite_fibre P h₁ h₂ j)

private theorem SpecialPeriods.EllipticAttachingSurjectivity.fullCover_surjective
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Function.Surjective (fullCover P h₁ h₂ j) :=
  (SpecialPeriods.EllipticFilling.fillingQuotient_surjective P h₁ h₂ j).comp
    (SpecialPeriods.EllipticFilling.localPeriods P j).quotientMap_surjective

private def SpecialPeriods.EllipticAttachingSurjectivity.powerDisc (m : ℕ) (r : ℝ) :
    TopologicalSpace.Opens SpecialPeriods.Disc :=
  ⟨{z | ‖(z : ℂ)‖ ^ m < r}, isOpen_lt (continuous_subtype_val.norm.pow m) continuous_const⟩

private def SpecialPeriods.EllipticAttachingSurjectivity.powerDiscRadius (m : ℕ) (r : ℝ) : ℝ :=
  r ^ (m : ℝ)⁻¹

private theorem SpecialPeriods.EllipticAttachingSurjectivity.powerDiscRadius_pos (m : ℕ) (r : ℝ)
    (hr : 0 < r) : 0 < powerDiscRadius m r :=
  Real.rpow_pos_of_pos hr _

private theorem SpecialPeriods.EllipticAttachingSurjectivity.powerDiscRadius_pow (m : ℕ) (r : ℝ)
    (hm : 0 < m) (hr : 0 < r) : powerDiscRadius m r ^ m = r :=
  Real.rpow_inv_natCast_pow hr.le hm.ne'

private theorem SpecialPeriods.EllipticAttachingSurjectivity.powerDiscRadius_lt_one (m : ℕ) (r : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hr1 : r < 1) : powerDiscRadius m r < 1 :=
  Real.rpow_lt_one hr.le hr1 (inv_pos.mpr (Nat.cast_pos.mpr hm))

private theorem SpecialPeriods.EllipticAttachingSurjectivity.norm_pow_lt_iff_norm_lt_powerDiscRadius
    (m : ℕ) (r : ℝ) (hm : 0 < m) (hr : 0 < r) (z : ℂ) : ‖z‖ ^ m < r ↔ ‖z‖ < powerDiscRadius m r :=
  by
  calc
    ‖z‖ ^ m < r ↔ ‖z‖ ^ m < powerDiscRadius m r ^ m := by rw [powerDiscRadius_pow m r hm hr]
    _ ↔ ‖z‖ < powerDiscRadius m r :=
      pow_lt_pow_iff_left₀ (norm_nonneg z) (powerDiscRadius_pos m r hr).le hm.ne'

private def SpecialPeriods.EllipticAttachingSurjectivity.powerDiscBallHomeomorph (m : ℕ) (r : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hr1 : r < 1) :
    powerDisc m r ≃ₜ Metric.ball (0 : ℂ) (powerDiscRadius m r)
    where
  toFun
    z :=
    ⟨((z : SpecialPeriods.Disc) : ℂ), by
      simpa only [Metric.mem_ball, dist_zero_right] using
        (norm_pow_lt_iff_norm_lt_powerDiscRadius m r hm hr _).mp z.property⟩
  invFun
    z :=
    ⟨⟨z, by
        change (z : ℂ) ∈ Metric.ball (0 : ℂ) 1
        simpa only [Metric.mem_ball, dist_zero_right] using
          (show ‖(z : ℂ)‖ < powerDiscRadius m r by
                simpa only [Metric.mem_ball, dist_zero_right] using z.property).trans
            (powerDiscRadius_lt_one m r hm hr hr1)⟩,
      by
      apply (norm_pow_lt_iff_norm_lt_powerDiscRadius m r hm hr _).mpr
      simpa only [Metric.mem_ball, dist_zero_right] using z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem
    SpecialPeriods.EllipticAttachingSurjectivity.powerDisc_contractibleSpace (m : ℕ) (r : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hr1 : r < 1) : ContractibleSpace (powerDisc m r) := by
  apply (powerDiscBallHomeomorph m r hm hr hr1).contractibleSpace_iff.mpr
  exact
    (convex_ball (0 : ℂ) (powerDiscRadius m r)).contractibleSpace
      ⟨0, Metric.mem_ball_self (powerDiscRadius_pos m r hr)⟩

private theorem
    SpecialPeriods.EllipticAttachingSurjectivity.powerDisc_punctured_image (m : ℕ) (r : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hr1 : r < 1) :
    (fun z : powerDisc m r => ((z : SpecialPeriods.Disc) : ℂ)) ''
        {z : powerDisc m r | ((z : SpecialPeriods.Disc) : ℂ) ≠ 0} =
      Metric.ball (0 : ℂ) (powerDiscRadius m r) \ {0} := by
  let e := powerDiscBallHomeomorph m r hm hr hr1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(e w).property, hw⟩
  · rintro ⟨hz, hne⟩
    refine ⟨e.symm ⟨z, hz⟩, ?_, rfl⟩
    exact hne

private theorem
    SpecialPeriods.EllipticAttachingSurjectivity.powerDisc_punctured_isPathConnected (m : ℕ)
    (r : ℝ) (hm : 0 < m) (hr : 0 < r) (hr1 : r < 1) :
    IsPathConnected {z : powerDisc m r | ((z : SpecialPeriods.Disc) : ℂ) ≠ 0} := by
  have h : Topology.IsInducing (fun z : powerDisc m r => ((z : SpecialPeriods.Disc) : ℂ)) :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  apply h.isPathConnected_iff.mpr
  rw [powerDisc_punctured_image m r hm hr hr1]
  exact
    SpecialPeriods.Threefold.punctured_complex_ball_isPathConnected (powerDiscRadius_pos m r hr)

private abbrev SpecialPeriods.EllipticAttachingSurjectivity.SmallCoverSource
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :=
  powerDisc j.order (C.radius (Option.some j)) × ComplexPlane₂

private theorem SpecialPeriods.EllipticAttachingSurjectivity.fullCover_mem_pieceDomain_iff
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind)
    (x : SpecialPeriods.Disc × ComplexPlane₂) :
    fullCover P h₁ h₂ j x ∈ SpecialPeriods.EllipticFilling.pieceDomain P h₁ h₂ C j ↔
      x.1 ∈ powerDisc j.order (C.radius (Option.some j)) := by
  change
    ‖(SpecialPeriods.EllipticFilling.fillingProjection P h₁ h₂ j (fullCover P h₁ h₂ j x) : ℂ)‖ <
        _ ↔
      _
  rw [fullCover_projection_coe, norm_pow]
  rfl

private def SpecialPeriods.EllipticAttachingSurjectivity.smallCoverHomeomorph
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    SmallCoverSource C j ≃ₜ
      (fullCover P h₁ h₂ j ⁻¹'
        (SpecialPeriods.EllipticFilling.pieceDomain P h₁ h₂ C j :
          Set (SpecialPeriods.EllipticFilling.fillingSpace P h₁ h₂ j)))
    where
  toFun
    x :=
    ⟨((x.1 : SpecialPeriods.Disc), x.2),
      (fullCover_mem_pieceDomain_iff P h₁ h₂ C j _).mpr x.1.property⟩
  invFun x := (⟨x.val.1, (fullCover_mem_pieceDomain_iff P h₁ h₂ C j _).mp x.property⟩, x.val.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)

private def SpecialPeriods.EllipticAttachingSurjectivity.smallCover (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    SmallCoverSource C j → SpecialPeriods.EllipticFilling.Piece P h₁ h₂ C j :=
  (SpecialPeriods.EllipticFilling.pieceDomain P h₁ h₂ C j :
          Set (SpecialPeriods.EllipticFilling.fillingSpace P h₁ h₂ j)).restrictPreimage
      (fullCover P h₁ h₂ j) ∘
    smallCoverHomeomorph P h₁ h₂ C j

private theorem SpecialPeriods.EllipticAttachingSurjectivity.smallCover_isCoveringMap
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    IsCoveringMap (smallCover P h₁ h₂ C j) :=
  ((fullCover_isCoveringMap P h₁ h₂ j).restrictPreimage
        (SpecialPeriods.EllipticFilling.pieceDomain P h₁ h₂ C j :
          Set (SpecialPeriods.EllipticFilling.fillingSpace P h₁ h₂ j))).comp_homeomorph
    (smallCoverHomeomorph P h₁ h₂ C j)

private theorem SpecialPeriods.EllipticAttachingSurjectivity.smallCover_surjective
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    Function.Surjective (smallCover P h₁ h₂ C j) :=
  ((fullCover_surjective P h₁ h₂ j).restrictPreimage
        (SpecialPeriods.EllipticFilling.pieceDomain P h₁ h₂ C j :
          Set (SpecialPeriods.EllipticFilling.fillingSpace P h₁ h₂ j))).comp
    (smallCoverHomeomorph P h₁ h₂ C j).surjective

private theorem SpecialPeriods.EllipticAttachingSurjectivity.smallCoverSource_simplyConnectedSpace
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    SimplyConnectedSpace (SmallCoverSource C j) := by
  let :=
    powerDisc_contractibleSpace j.order (C.radius (Option.some j)) j.order_pos
      (C.radius_pos (Option.some j)) (C.radius_lt_chart (Option.some j))
  infer_instance

private def
    SpecialPeriods.EllipticAttachingSurjectivity.puncturedPiece (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    Set (SpecialPeriods.EllipticFilling.Piece P h₁ h₂ C j) :=
  {x | (SpecialPeriods.EllipticFilling.fillingProjection P h₁ h₂ j x : ℂ) ≠ 0}

private theorem SpecialPeriods.EllipticAttachingSurjectivity.smallCover_preimage_puncturedPiece
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    smallCover P h₁ h₂ C j ⁻¹' puncturedPiece P h₁ h₂ C j =
      {z : powerDisc j.order (C.radius (Option.some j)) | ((z : SpecialPeriods.Disc) : ℂ) ≠ 0} ×ˢ
        (Set.univ : Set ComplexPlane₂) := by
  ext x
  change
    (((x.1 : SpecialPeriods.Disc) : ℂ) ^ j.order ≠ 0) ↔
      (((x.1 : SpecialPeriods.Disc) : ℂ) ≠ 0 ∧ True)
  simp only [ne_eq, pow_eq_zero_iff j.order_pos.ne', and_true]

private theorem
    SpecialPeriods.EllipticAttachingSurjectivity.smallCover_punctured_preimage_isPathConnected
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    IsPathConnected (smallCover P h₁ h₂ C j ⁻¹' puncturedPiece P h₁ h₂ C j) := by
  rw [smallCover_preimage_puncturedPiece]
  exact
    (powerDisc_punctured_isPathConnected j.order (C.radius (Option.some j)) j.order_pos
          (C.radius_pos (Option.some j)) (C.radius_lt_chart (Option.some j))).prod
      isPathConnected_univ

private def SpecialPeriods.EllipticAttachingSurjectivity.puncturedPieceInclusion
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    C(puncturedPiece P h₁ h₂ C j, SpecialPeriods.EllipticFilling.Piece P h₁ h₂ C j) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private theorem
  SpecialPeriods.EllipticAttachingSurjectivity.puncturedPieceInclusion_fundamentalGroup_surjective
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind)
    (x : puncturedPiece P h₁ h₂ C j) :
    Function.Surjective (FundamentalGroup.map (puncturedPieceInclusion P h₁ h₂ C j) x) := by
  let := smallCoverSource_simplyConnectedSpace C j
  exact
    covering_restriction_fundamentalGroup_map_surjective (smallCover_isCoveringMap P h₁ h₂ C j)
      (smallCover_surjective P h₁ h₂ C j) (puncturedPiece P h₁ h₂ C j)
      (smallCover_punctured_preimage_isPathConnected P h₁ h₂ C j) x

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.Threefold.localPieceChartedSpace in
private abbrev SpecialPeriods.Threefold.ellipticPuncturedPiece (j : Elliptic.Kind) :
    Set (SpecialEllipticPiece j) :=
  SpecialPeriods.EllipticAttachingSurjectivity.puncturedPiece SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.Threefold.localPieceChartedSpace in
private def SpecialPeriods.Threefold.ellipticPuncturedPieceInclusion (j : Elliptic.Kind) :
    C(ellipticPuncturedPiece j, SpecialEllipticPiece j) :=
  ⟨Subtype.val, continuous_subtype_val⟩

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.ellipticPuncturedPieceInclusion_fundamentalGroup_surjective
    (j : Elliptic.Kind) (x : ellipticPuncturedPiece j) :
    Function.Surjective (FundamentalGroup.map (ellipticPuncturedPieceInclusion j) x) :=
  SpecialPeriods.EllipticAttachingSurjectivity.puncturedPieceInclusion_fundamentalGroup_surjective
    SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
    SpecialPeriods.specialPeriodMap_generator₂ specialBaseCover j x

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.Threefold.localPieceChartedSpace in
private def SpecialPeriods.Threefold.overlapAsFillingSubsetHomeomorph (i : Puncture) :
    {x : liftedPatch (Option.some i) | (x : Space) ∈ liftedPatch Option.none} ≃ₜ RegularOverlap i
    where
  toFun x := ⟨x.val.val, x.property, x.val.property⟩
  invFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.ellipticPuncturedPiece_mem_iff (j : Elliptic.Kind)
    (x : SpecialEllipticPiece j) :
    x ∈ ellipticPuncturedPiece j ↔
      ((patchBiholomorph (Option.some (Option.some j)) x :
            liftedPatch (Option.some (Option.some j))) :
          Space) ∈
        liftedPatch Option.none := by
  change
    (SpecialPeriods.EllipticFilling.fillingProjection SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
            j x :
          ℂ) ≠
        0 ↔
      projection (SpecialPeriods.Threefold.inclusion (Option.some (Option.some j)) x) ∈
        regularPatch
  exact
    (SpecialPeriods.EllipticFilling.pieceProjectionToBase_mem_regular_iff
          SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂ specialBaseCover j x).symm.trans
      (Iff.of_eq
        (congrArg (fun y => y ∈ regularPatch)
          (projection_inclusion (Option.some (Option.some j)) x).symm))

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.Threefold.localPieceChartedSpace in
private def SpecialPeriods.Threefold.ellipticPuncturedPieceHomeomorph (j : Elliptic.Kind) :
    ellipticPuncturedPiece j ≃ₜ RegularOverlap (Option.some j) :=
  ((patchBiholomorph (Option.some (Option.some j))).toHomeomorph.subtype (p := fun x =>
        x ∈ ellipticPuncturedPiece j) (q := fun x : liftedPatch (Option.some (Option.some j)) =>
        (x : Space) ∈ liftedPatch Option.none) (ellipticPuncturedPiece_mem_iff j)).trans
    (overlapAsFillingSubsetHomeomorph (Option.some j))

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.ellipticPuncturedPiece_fundamentalGroup_naturality
    (j : Elliptic.Kind) (x : RegularOverlap (Option.some j)) :
    (homeomorphFundamentalGroupEquiv
            (patchBiholomorph (Option.some (Option.some j))).toHomeomorph.symm
            (overlapFillingInclusion (Option.some j) x)).toMonoidHom.comp
        (FundamentalGroup.map (overlapFillingInclusion (Option.some j)) x) =
      (FundamentalGroup.map (ellipticPuncturedPieceInclusion j)
            ((ellipticPuncturedPieceHomeomorph j).symm x)).comp
        (homeomorphFundamentalGroupEquiv (ellipticPuncturedPieceHomeomorph j).symm
            x).toMonoidHom := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem
    SpecialPeriods.Threefold.overlapFillingInclusion_elliptic_fundamentalGroup_surjective
    (j : Elliptic.Kind) (x : RegularOverlap (Option.some j)) :
    Function.Surjective (FundamentalGroup.map (overlapFillingInclusion (Option.some j)) x) := by
  let eF :=
    homeomorphFundamentalGroupEquiv
      (patchBiholomorph (Option.some (Option.some j))).toHomeomorph.symm
      (overlapFillingInclusion (Option.some j) x)
  let eO := homeomorphFundamentalGroupEquiv (ellipticPuncturedPieceHomeomorph j).symm x
  let f :=
    FundamentalGroup.map (ellipticPuncturedPieceInclusion j)
      ((ellipticPuncturedPieceHomeomorph j).symm x)
  intro γ
  obtain ⟨δ, hδ⟩ :=
    ellipticPuncturedPieceInclusion_fundamentalGroup_surjective j
      ((ellipticPuncturedPieceHomeomorph j).symm x) (eF γ)
  refine ⟨eO.symm δ, eF.injective ?_⟩
  exact
    (DFunLike.congr_fun (ellipticPuncturedPiece_fundamentalGroup_naturality j x)
          (eO.symm δ)).trans
      ((congrArg f (eO.apply_symm_apply δ)).trans hδ)

attribute [local instance] SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.overlapFillingHom_elliptic_surjective (j : Elliptic.Kind) :
    Function.Surjective (overlapFillingHom (Option.some j)) :=
  overlapFillingInclusion_elliptic_fundamentalGroup_surjective j
    (regularOverlapPoint (Option.some j))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.CuspAttaching.radius : ℝ :=
  SpecialPeriods.Threefold.specialBaseCover.radius Option.none

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.CuspAttaching.Disc :=
  CuspQuotient.disc radius

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.CuspAttaching.data : SpecialPeriods.CuspFamily.Data :=
  SpecialPeriods.specialCuspData.shrink radius
    (SpecialPeriods.Threefold.specialBaseCover.radius_pos Option.none)
    SpecialPeriods.Threefold.specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.CuspAttaching.regularData :
    PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint :=
  SpecialPeriods.Threefold.regularFamilyData SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.CuspAttaching.cuspZeroSection :
    Disc → SpecialPeriods.Threefold.SpecialCuspPiece :=
  CuspQuotient.zeroSection SpecialPeriods.specialCuspData.correction radius

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.cuspZeroSection_continuous :
    Continuous cuspZeroSection :=
  CuspQuotient.zeroSection_continuous SpecialPeriods.specialCuspData.correction radius

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.CuspAttaching.regularZeroSection :
    SpecialPeriods.Threefold.regularPatch → SpecialPeriods.Threefold.SpecialRegularFamily :=
  SpecialPeriods.Threefold.regularFamilyZeroSection SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.regularZeroSection_continuous :
    Continuous regularZeroSection :=
  SpecialPeriods.Threefold.regularFamilyZeroSection_continuous SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.CuspAttaching.regularBase (t : Disc) (ht : (t : ℂ) ≠ 0) :
    SpecialPeriods.Threefold.regularPatch :=
  ⟨SpecialPeriods.Threefold.specialBaseCover.fillingEmbedding Option.none t,
    (SpecialPeriods.Threefold.specialBaseCover.fillingEmbedding_mem_regular_iff Option.none t).mpr
      ht⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.cuspZeroSection_projection (t : Disc) :
    SpecialPeriods.Threefold.specialCuspPieceProjectionToBase (cuspZeroSection t) =
      SpecialPeriods.Threefold.specialBaseCover.fillingEmbedding Option.none t := by
  change
    (SpecialPeriods.Threefold.punctureChart Option.none).symm
        (CuspQuotient.projection SpecialPeriods.specialCuspData.correction radius
          (CuspQuotient.zeroSection SpecialPeriods.specialCuspData.correction radius t)) =
      _
  rw [CuspQuotient.projection_zeroSection]
  rfl

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.cuspZeroSection_mem_overlap (t : Disc)
    (ht : (t : ℂ) ≠ 0) : cuspZeroSection t ∈ SpecialPeriods.Threefold.specialCuspOverlap.source :=
  by
  rw [SpecialPeriods.Threefold.specialCuspOverlap_source]
  change
    SpecialPeriods.Threefold.specialCuspPieceProjectionToBase (cuspZeroSection t) ∈
      SpecialPeriods.Threefold.regularPatch
  rw [cuspZeroSection_projection]
  exact (regularBase t ht).property

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.overlap_cuspZeroSection_projection (t : Disc)
    (ht : (t : ℂ) ≠ 0) :
    SpecialPeriods.Threefold.specialRegularFamilyProjection
        (SpecialPeriods.Threefold.specialCuspOverlap (cuspZeroSection t)) =
      regularBase t ht := by
  apply Subtype.ext
  exact
    (SpecialPeriods.Threefold.specialCuspOverlap_base _ (cuspZeroSection_mem_overlap t ht)).trans
      (cuspZeroSection_projection t)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.CuspAttaching.OverlapBase :=
  { b : SpecialPeriods.Threefold.regularPatch //
    (b : SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
      SpecialPeriods.Threefold.specialBaseCover.fillingPatch Option.none }

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.CuspAttaching.overlapCoordinate (b : OverlapBase) : Disc :=
  SpecialPeriods.Threefold.specialBaseCover.fillingChart Option.none ⟨b.val, b.property⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.overlapCoordinate_continuous :
    Continuous overlapCoordinate :=
  (SpecialPeriods.Threefold.specialBaseCover.fillingChart Option.none).continuous.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.overlapCoordinate_ne_zero (b : OverlapBase) :
    (overlapCoordinate b : ℂ) ≠ 0 :=
  (SpecialPeriods.Threefold.specialBaseCover.fillingPatch_regular_iff_coordinate_ne_zero
        Option.none b.property).mp
    b.val.property

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem
    SpecialPeriods.Threefold.CuspAttaching.regularBase_overlapCoordinate (b : OverlapBase) :
    regularBase (overlapCoordinate b) (overlapCoordinate_ne_zero b) = b.val := by
  apply Subtype.ext
  change
    ((SpecialPeriods.Threefold.specialBaseCover.fillingChart Option.none).symm
          (SpecialPeriods.Threefold.specialBaseCover.fillingChart Option.none
            ⟨b.val, b.property⟩)).val =
      b.val.val
  exact
    congrArg Subtype.val
      ((SpecialPeriods.Threefold.specialBaseCover.fillingChart Option.none).symm_apply_apply
        ⟨b.val, b.property⟩)

private theorem SpecialPeriods.CuspFamily.Data.familyCover_zero (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) :
    D.familyCover ⟨((s : ℂ), 0), s.property⟩ = (s, 0) := by
  simp only [familyCover_apply, HolomorphicPeriodMap.quotientMap, map_zero]

@[simp]
private theorem
    SpecialPeriods.CuspFamily.Data.iteratedCover_zero (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) :
    D.iteratedCover ⟨((s : ℂ), 0), s.property⟩ = D.quotient (s, 0) := by
  change D.quotient (D.familyCover _) = _
  rw [D.familyCover_zero]

private theorem SpecialPeriods.CuspGlobalOverlap.familyMap_iteratedCover_zero
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : SpecialPeriods.CuspFamily.LogBase C.radius) :
    familyMap C D hrcap (C.iteratedCover ⟨((s : ℂ), 0), s.property⟩) =
      D.zeroSection
        (D.baseQuotient (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s)) := by
  rw [C.iteratedCover_zero, familyMap_quotient, D.zeroSection_baseQuotient]
  rfl

private theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_zeroSection_log
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (s : SpecialPeriods.CuspFamily.LogBase C.radius) (t : CuspQuotient.disc C.radius)
    (ht : (t : ℂ) = CuspUniformization.exponential s) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    cuspToRegularPartial C D hrcap hperiod (CuspQuotient.zeroSection C.correction C.radius t) =
      D.zeroSection
        (D.baseQuotient (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s)) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  have htne : (t : ℂ) ≠ 0 := by
    rw [ht]
    exact CuspUniformization.exponential_ne_zero s
  have hsource :
    CuspQuotient.zeroSection C.correction C.radius t ∈
      CuspUniformization.puncturedQuotientOpen C.correction C.radius := by
    change
      CuspQuotient.projection C.correction C.radius
          (CuspQuotient.zeroSection C.correction C.radius t) ≠
        0
    rw [CuspQuotient.projection_zeroSection]
    exact htne
  rw [cuspToRegularPartial_apply C D hrcap hperiod _ hsource]
  have he :
    (⟨CuspQuotient.zeroSection C.correction C.radius t, hsource⟩ :
        CuspUniformization.PuncturedQuotient C.correction C.radius) =
      CuspUniformization.puncturedCuspCover C.correction C.radius ⟨((s : ℂ), 0), s.property⟩ := by
    apply Subtype.ext
    exact (CuspUniformization.puncturedCuspCover_zero C.correction C.radius s t ht).symm
  rw [he, puncturedBiholomorph_cover C D hrcap hperiod]
  exact familyMap_iteratedCover_zero C D hrcap s

private theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_zeroSection
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (t : CuspQuotient.disc C.radius) (ht : (t : ℂ) ≠ 0) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    cuspToRegularPartial C D hrcap hperiod (CuspQuotient.zeroSection C.correction C.radius t) =
      D.zeroSection
        (D.projection
          (cuspToRegularPartial C D hrcap hperiod
            (CuspQuotient.zeroSection C.correction C.radius t))) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  obtain ⟨s, hs⟩ :=
    SpecialPeriods.CuspFamily.baseExponential_surjective C.radius
      (⟨t, t.property, ht⟩ : SpecialPeriods.CuspFamily.puncturedDisc C.radius)
  have he : (t : ℂ) = CuspUniformization.exponential s := (congrArg Subtype.val hs).symm
  rw [cuspToRegularPartial_zeroSection_log C D hrcap hperiod s t he, D.projection_zeroSection]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.radius_le_cuspChart :
    radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width :=
  SpecialPeriods.Threefold.specialBaseCover_cusp_radius_bounds.2.2.le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.period_agreement
    (s : SpecialPeriods.CuspFamily.LogBase radius) :
    regularData.periods.point
        (SpecialPeriods.CuspFamily.logBaseToRegular radius radius_le_cuspChart s) =
      data.periods.point s :=
  SpecialPeriods.CuspGlobalOverlap.spherePeriod_agreement
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo radius
    (SpecialPeriods.Threefold.specialBaseCover.radius_pos Option.none)
    SpecialPeriods.Threefold.specialCuspRadius_le radius_le_cuspChart s

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.regularZeroSection_projection_eq
    (x : SpecialPeriods.Threefold.SpecialRegularFamily) :
    regularZeroSection (SpecialPeriods.Threefold.specialRegularFamilyProjection x) =
      regularData.zeroSection (regularData.projection x) := by
  change
    regularData.zeroSection
        (SpecialPeriods.Threefold.regularBiholomorph.symm
          (SpecialPeriods.Threefold.regularBiholomorph (regularData.projection x))) =
      _
  exact
    congrArg regularData.zeroSection
      (SpecialPeriods.Threefold.regularBiholomorph.symm_apply_apply (regularData.projection x))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.overlap_cuspZeroSection (t : Disc)
    (ht : (t : ℂ) ≠ 0) :
    SpecialPeriods.Threefold.specialCuspOverlap (cuspZeroSection t) =
      regularZeroSection (regularBase t ht) := by
  have hzero :=
    SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_zeroSection data regularData
      radius_le_cuspChart period_agreement t ht
  change
    SpecialPeriods.Threefold.specialCuspOverlap (cuspZeroSection t) =
      regularData.zeroSection
        (regularData.projection
          (SpecialPeriods.Threefold.specialCuspOverlap (cuspZeroSection t))) at hzero
  calc
    SpecialPeriods.Threefold.specialCuspOverlap (cuspZeroSection t) =
        regularData.zeroSection
          (regularData.projection
            (SpecialPeriods.Threefold.specialCuspOverlap (cuspZeroSection t))) :=
      hzero
    _ =
        regularZeroSection
          (SpecialPeriods.Threefold.specialRegularFamilyProjection
            (SpecialPeriods.Threefold.specialCuspOverlap (cuspZeroSection t))) :=
      (regularZeroSection_projection_eq _).symm
    _ = regularZeroSection (regularBase t ht) :=
      congrArg regularZeroSection (overlap_cuspZeroSection_projection t ht)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.inclusion_cuspZeroSection (t : Disc)
    (ht : (t : ℂ) ≠ 0) :
    SpecialPeriods.Threefold.inclusion (Option.some Option.none) (cuspZeroSection t) =
      SpecialPeriods.Threefold.inclusion Option.none (regularZeroSection (regularBase t ht)) := by
  apply
    (SpecialPeriods.Threefold.gluingData.inclusion_eq_iff (Option.some Option.none) Option.none _
        _).mpr
  exact ⟨cuspZeroSection_mem_overlap t ht, overlap_cuspZeroSection t ht⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private def SpecialPeriods.Threefold.CuspAttaching.extendedSection :
    Disc → SpecialPeriods.Threefold.Space :=
  SpecialPeriods.Threefold.inclusion (Option.some Option.none) ∘ cuspZeroSection

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.extendedSection_continuous :
    Continuous extendedSection :=
  (SpecialPeriods.Threefold.inclusion_openEmbedding (Option.some Option.none)).continuous.comp
    cuspZeroSection_continuous

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private def SpecialPeriods.Threefold.CuspAttaching.regularSection :
    SpecialPeriods.Threefold.regularPatch → SpecialPeriods.Threefold.Space :=
  SpecialPeriods.Threefold.inclusion Option.none ∘ regularZeroSection

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.regularSection_continuous :
    Continuous regularSection :=
  (SpecialPeriods.Threefold.inclusion_openEmbedding Option.none).continuous.comp
    regularZeroSection_continuous

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private def SpecialPeriods.Threefold.CuspAttaching.attachedRegularSection :
    OverlapBase → SpecialPeriods.Threefold.Space :=
  regularSection ∘ Subtype.val

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.attachedRegularSection_continuous :
    Continuous attachedRegularSection :=
  regularSection_continuous.comp continuous_subtype_val

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.attachedRegularSection_eq_extended
    (b : OverlapBase) : attachedRegularSection b = extendedSection (overlapCoordinate b) := by
  have h := inclusion_cuspZeroSection (overlapCoordinate b) (overlapCoordinate_ne_zero b)
  rw [regularBase_overlapCoordinate] at h
  exact h.symm

private def
    SpecialPeriods.Threefold.CuspAttaching.attachedRegularSectionLoopContraction {b : OverlapBase}
    (p : Path b b) :
    (p.map attachedRegularSection_continuous).Homotopy (Path.refl (attachedRegularSection b)) := by
  let H := CuspQuotient.discLoopContraction (p.map overlapCoordinate_continuous)
  refine
    { toFun := fun u => extendedSection (H u)
      continuous_toFun := extendedSection_continuous.comp H.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro t
    exact
      (congrArg extendedSection (H.map_zero_left t)).trans
        (attachedRegularSection_eq_extended (p t)).symm
  · intro t
    exact
      (congrArg extendedSection (H.map_one_left t)).trans
        (attachedRegularSection_eq_extended b).symm
  · intro r t ht
    rcases ht with rfl | rfl
    · exact
        (congrArg extendedSection (Path.Homotopy.source H r)).trans
          ((attachedRegularSection_eq_extended b).symm.trans
            (congrArg attachedRegularSection p.source.symm))
    · exact
        (congrArg extendedSection (Path.Homotopy.target H r)).trans
          ((attachedRegularSection_eq_extended b).symm.trans
            (congrArg attachedRegularSection p.target.symm))

private def SpecialPeriods.Threefold.CuspAttaching.regularLoopInOverlap
    {b : SpecialPeriods.Threefold.regularPatch}
    (hb :
      (b : SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
        SpecialPeriods.Threefold.specialBaseCover.fillingPatch Option.none)
    (p : Path b b)
    (hp :
      ∀ t,
        (p t : SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
          SpecialPeriods.Threefold.specialBaseCover.fillingPatch Option.none) :
    Path (⟨b, hb⟩ : OverlapBase) ⟨b, hb⟩
    where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

private theorem SpecialPeriods.Threefold.CuspAttaching.regularLoopInOverlap_map
    {b : SpecialPeriods.Threefold.regularPatch}
    (hb :
      (b : SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
        SpecialPeriods.Threefold.specialBaseCover.fillingPatch Option.none)
    (p : Path b b)
    (hp :
      ∀ t,
        (p t : SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
          SpecialPeriods.Threefold.specialBaseCover.fillingPatch Option.none) :
    (regularLoopInOverlap hb p hp).map attachedRegularSection_continuous =
      p.map regularSection_continuous := by
  ext t
  rfl

private def SpecialPeriods.Threefold.CuspAttaching.regularSectionLoopContraction_of_mem
    {b : SpecialPeriods.Threefold.regularPatch} (p : Path b b)
    (hp :
      ∀ t,
        (p t : SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
          SpecialPeriods.Threefold.specialBaseCover.fillingPatch Option.none) :
    (p.map regularSection_continuous).Homotopy (Path.refl (regularSection b)) := by
  have hb :
    (b : SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
      SpecialPeriods.Threefold.specialBaseCover.fillingPatch Option.none := by
    simpa only [p.source] using hp 0
  exact
    (attachedRegularSectionLoopContraction (regularLoopInOverlap hb p hp)).cast
      (regularLoopInOverlap_map hb p hp) rfl

private theorem SpecialPeriods.Threefold.CuspAttaching.regularSection_loop_nullhomotopic_of_mem
    {b : SpecialPeriods.Threefold.regularPatch} (p : Path b b)
    (hp :
      ∀ t,
        (p t : SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
          SpecialPeriods.Threefold.specialBaseCover.fillingPatch Option.none) :
    Path.Homotopic (p.map regularSection_continuous) (Path.refl (regularSection b)) :=
  ⟨regularSectionLoopContraction_of_mem p hp⟩

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private def SpecialPeriods.Threefold.CuspAttaching.fillingHomeomorph :
    SpecialPeriods.Threefold.SpecialCuspPiece ≃ₜ
      SpecialPeriods.Threefold.liftedPatch (Option.some Option.none) :=
  (SpecialPeriods.Threefold.patchBiholomorph (Option.some Option.none)).toHomeomorph

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private abbrev SpecialPeriods.Threefold.CuspAttaching.NonzeroFibre (s : ℂ) :=
  CuspQuotient.projection data.correction radius ⁻¹' {CuspUniformization.exponential s}

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.nonzeroFibre_mem_regular (s : ℂ)
    (x : NonzeroFibre s) :
    (fillingHomeomorph x.val).val ∈ SpecialPeriods.Threefold.liftedPatch Option.none := by
  change
    SpecialPeriods.Threefold.projection (fillingHomeomorph x.val) ∈
      SpecialPeriods.Threefold.regularPatch
  have hp :
    SpecialPeriods.Threefold.projection (fillingHomeomorph x.val) =
      SpecialPeriods.Threefold.CuspPiece.projectionToBase SpecialPeriods.specialCuspData
        SpecialPeriods.Threefold.specialBaseCover x.val :=
    SpecialPeriods.Threefold.gluingData.projection_inclusion (Option.some Option.none) x.val
  rw [hp]
  apply
    (SpecialPeriods.Threefold.CuspPiece.projectionToBase_mem_regular_iff
        SpecialPeriods.specialCuspData SpecialPeriods.Threefold.specialBaseCover x.val).mpr
  have hx :
    CuspQuotient.projection data.correction radius x.val = CuspUniformization.exponential s :=
    x.property
  exact hx.trans_ne (CuspUniformization.exponential_ne_zero s)

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private def SpecialPeriods.Threefold.CuspAttaching.fibreToOverlap (s : ℂ) :
    C(NonzeroFibre s, SpecialPeriods.Threefold.RegularOverlap Option.none)
    where
  toFun
    x :=
    ⟨fillingHomeomorph x.val, nonzeroFibre_mem_regular s x, (fillingHomeomorph x.val).property⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          (fillingHomeomorph.continuous.comp continuous_subtype_val)).subtype_mk
      _

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private theorem
    SpecialPeriods.Threefold.CuspAttaching.fibreToOverlap_fundamentalGroup_factors (s : ℂ)
    (x : NonzeroFibre s) (γ : FundamentalGroup (NonzeroFibre s) x) :
    FundamentalGroup.map (SpecialPeriods.Threefold.overlapFillingInclusion Option.none)
        (fibreToOverlap s x) (FundamentalGroup.map (fibreToOverlap s) x γ) =
      homeomorphFundamentalGroupEquiv fillingHomeomorph x.val
        (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ x γ) := by
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.exists_surjective_overlap_basepoint (s : ℂ)
    (hs : ‖CuspUniformization.exponential s‖ < radius) :
    ∃ x : SpecialPeriods.Threefold.RegularOverlap Option.none,
      Function.Surjective
        (FundamentalGroup.map (SpecialPeriods.Threefold.overlapFillingInclusion Option.none) x) :=
  by
  have hpos : 0 < ‖CuspUniformization.exponential s‖ :=
    norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero s)
  have hlog := Real.log_neg hpos (hs.trans data.radius_lt_one)
  have hRp := data.smallDrift _ hpos hs
  let x : NonzeroFibre s := CuspUniformization.fibreBasePoint data.correction radius s hs hlog hRp
  have hf : Function.Surjective (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ x) :=
    CuspUniformization.fibreInclusionFundamentalGroupMap_surjective data.correction radius s hs
      hlog hRp data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift
  refine ⟨fibreToOverlap s x, ?_⟩
  intro γ
  obtain ⟨δ, rfl⟩ := (homeomorphFundamentalGroupEquiv fillingHomeomorph x.val).surjective γ
  obtain ⟨ε, rfl⟩ := hf δ
  exact
    ⟨FundamentalGroup.map (fibreToOverlap s) x ε, fibreToOverlap_fundamentalGroup_factors s x ε⟩

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.exists_small_exponential :
    ∃ s : ℂ, ‖CuspUniformization.exponential s‖ < radius := by
  have hr : 0 < radius / 2 := half_pos data.radius_pos
  have ht : ((radius / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  refine ⟨CuspUniformization.logarithm ((radius / 2 : ℝ) : ℂ), ?_⟩
  rw [CuspUniformization.exponential_logarithm ht, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  exact half_lt_self data.radius_pos

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.cusp_overlapFillingHom_surjective :
    Function.Surjective (overlapFillingHom (Option.none : Puncture)) := by
  obtain ⟨s, hs⟩ := CuspAttaching.exists_small_exponential
  obtain ⟨x, hx⟩ := CuspAttaching.exists_surjective_overlap_basepoint s hs
  let := liftedPatch_regular_inter_pathConnectedSpace (Option.none : Puncture)
  exact
    fundamentalGroup_map_surjective_at_of_pathConnected (overlapFillingInclusion Option.none) x
      (regularOverlapPoint Option.none) hx

private theorem SpecialPeriods.Threefold.overlapFillingHom_surjective (i : Puncture) :
    Function.Surjective (overlapFillingHom i) := by
  cases i with
  | none => exact cusp_overlapFillingHom_surjective
  | some j => exact overlapFillingHom_elliptic_surjective j

private theorem SpecialPeriods.Threefold.regularLiftedInclusion_fundamentalGroup_surjective
    (x : liftedPatch Option.none) :
    Function.Surjective (FundamentalGroup.map regularLiftedInclusion x) :=
  regularLiftedInclusion_fundamentalGroup_map_surjective overlapFillingHom_surjective x

private def SpecialPeriods.Threefold.regularFamilyInclusionMap : C(SpecialRegularFamily, Space) :=
  ⟨SpecialPeriods.Threefold.inclusion Option.none,
    (inclusion_openEmbedding Option.none).continuous⟩

private theorem SpecialPeriods.Threefold.regularFamilyInclusionMap_fundamentalGroup_surjective
    (x : SpecialRegularFamily) :
    Function.Surjective (FundamentalGroup.map regularFamilyInclusionMap x) := by
  let e := gluingData.patchHomeomorph Option.none
  have hpatch := regularLiftedInclusion_fundamentalGroup_surjective (e x)
  have hlocal := (homeomorphFundamentalGroupEquiv e x).surjective
  have hmap :
    (FundamentalGroup.map regularLiftedInclusion (e x)).comp
        (homeomorphFundamentalGroupEquiv e x).toMonoidHom =
      FundamentalGroup.map regularFamilyInclusionMap x := by
    ext γ
    obtain ⟨p⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    rfl
  rw [← hmap]
  exact hpatch.comp hlocal

private def SpecialPeriods.Threefold.specialRegularFamilyMarkedPoint : SpecialRegularFamily :=
  ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁
        SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
    (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)

private def SpecialPeriods.Threefold.specialRegularFamilyMarkedLatticeHom :
    Multiplicative Lattice →*
      FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint :=
  ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁
        SpecialPeriods.specialPeriodMap_generator₂)).latticeFundamentalGroupHom
    (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)

private def SpecialPeriods.Threefold.specialRegularFamilyMarkedSectionHom :
    FundamentalGroup SpecialPeriods.TriangleRegularQuotient
        (SpecialPeriods.triangleRegularProject
          (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)) →*
      FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint :=
  ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁
        SpecialPeriods.specialPeriodMap_generator₂)).sectionFundamentalGroupHom
    (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)

private def SpecialPeriods.Threefold.specialRegularFamilyMarkedMeridianPath (b : Bool) :
    Path specialRegularFamilyMarkedPoint specialRegularFamilyMarkedPoint :=
  (PeriodFamily.Meridians.compatibleRegularMeridian b).map
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁
        SpecialPeriods.specialPeriodMap_generator₂)).zeroSection_continuous

private def SpecialPeriods.Threefold.specialRegularFamilyMarkedMeridianClass (b : Bool) :
    FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (specialRegularFamilyMarkedMeridianPath b))

@[simp]
private theorem
    SpecialPeriods.Threefold.specialRegularFamilyMarkedMeridianClass_eq_section (b : Bool) :
    specialRegularFamilyMarkedMeridianClass b =
      specialRegularFamilyMarkedSectionHom
        (PeriodFamily.Meridians.compatibleRegularMeridianClass b) :=
  rfl

private def SpecialPeriods.Threefold.specialRegularFamilyMarkedFundamentalGroupEquiv :
    FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint ≃*
      (Multiplicative Lattice) ⋊[PeriodFamily.Meridians.sourceFreeLatticeAction]
        (FreeGroup Bool) :=
  PeriodFamily.markedRegularFundamentalGroupEquiv SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

@[simp]
private theorem SpecialPeriods.Threefold.specialRegularFamilyMarkedFundamentalGroupEquiv_lattice
    (v : Multiplicative Lattice) :
    specialRegularFamilyMarkedFundamentalGroupEquiv (specialRegularFamilyMarkedLatticeHom v) =
      SemidirectProduct.inl v :=
  PeriodFamily.markedRegularFundamentalGroupEquiv_lattice SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂ v

private theorem SpecialPeriods.Threefold.specialRegularFamilyMarkedFundamentalGroupEquiv_meridian
    (b : Bool) :
    specialRegularFamilyMarkedFundamentalGroupEquiv (specialRegularFamilyMarkedMeridianClass b) =
      SemidirectProduct.inr (FreeGroup.of b) :=
  PeriodFamily.markedRegularFundamentalGroupEquiv_meridian SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂ b

private theorem SpecialPeriods.Threefold.specialRegularFamilyMarkedMeridian_conjugation (b : Bool)
    (v : Multiplicative Lattice) :
    specialRegularFamilyMarkedMeridianClass b * specialRegularFamilyMarkedLatticeHom v *
        (specialRegularFamilyMarkedMeridianClass b)⁻¹ =
      specialRegularFamilyMarkedLatticeHom
        (PeriodFamily.Meridians.sourceFreeLatticeAction (FreeGroup.of b) v) := by
  apply specialRegularFamilyMarkedFundamentalGroupEquiv.injective
  rw [map_mul, map_mul, map_inv, specialRegularFamilyMarkedFundamentalGroupEquiv_meridian,
    specialRegularFamilyMarkedFundamentalGroupEquiv_lattice,
    specialRegularFamilyMarkedFundamentalGroupEquiv_lattice]
  simpa only [map_inv] using
    (SemidirectProduct.inl_aut (φ := PeriodFamily.Meridians.sourceFreeLatticeAction)
        (FreeGroup.of b) v).symm

private theorem SpecialPeriods.Threefold.specialRegularFamilyMarkedMeridian_first_conjugation
    (v : Lattice) :
    specialRegularFamilyMarkedMeridianClass Bool.false *
          specialRegularFamilyMarkedLatticeHom (Multiplicative.ofAdd v) *
        (specialRegularFamilyMarkedMeridianClass Bool.false)⁻¹ =
      specialRegularFamilyMarkedLatticeHom (Multiplicative.ofAdd (A₁ *ᵥ v)) := by
  rw [specialRegularFamilyMarkedMeridian_conjugation]
  exact
    congrArg specialRegularFamilyMarkedLatticeHom
      (Multiplicative.toAdd.injective
        (PeriodFamily.Meridians.sourceFreeLatticeAction_first (Multiplicative.ofAdd v)))

private theorem SpecialPeriods.Threefold.specialRegularFamilyMarkedMeridian_second_conjugation
    (v : Lattice) :
    specialRegularFamilyMarkedMeridianClass Bool.true *
          specialRegularFamilyMarkedLatticeHom (Multiplicative.ofAdd v) *
        (specialRegularFamilyMarkedMeridianClass Bool.true)⁻¹ =
      specialRegularFamilyMarkedLatticeHom (Multiplicative.ofAdd (A₂ *ᵥ v)) := by
  rw [specialRegularFamilyMarkedMeridian_conjugation]
  exact
    congrArg specialRegularFamilyMarkedLatticeHom
      (Multiplicative.toAdd.injective
        (PeriodFamily.Meridians.sourceFreeLatticeAction_second (Multiplicative.ofAdd v)))

private def SpecialPeriods.Threefold.PiOne.basepoint : SpecialPeriods.Threefold.Space :=
  SpecialPeriods.Threefold.regularFamilyInclusionMap
    SpecialPeriods.Threefold.specialRegularFamilyMarkedPoint

private abbrev SpecialPeriods.Threefold.PiOne.GlobalGroup :=
  FundamentalGroup SpecialPeriods.Threefold.Space basepoint

private def SpecialPeriods.Threefold.PiOne.regularHom :
    FundamentalGroup SpecialPeriods.Threefold.SpecialRegularFamily
        SpecialPeriods.Threefold.specialRegularFamilyMarkedPoint →*
      GlobalGroup :=
  FundamentalGroup.map SpecialPeriods.Threefold.regularFamilyInclusionMap
    SpecialPeriods.Threefold.specialRegularFamilyMarkedPoint

private theorem
    SpecialPeriods.Threefold.PiOne.regularHom_surjective : Function.Surjective regularHom :=
  SpecialPeriods.Threefold.regularFamilyInclusionMap_fundamentalGroup_surjective
    SpecialPeriods.Threefold.specialRegularFamilyMarkedPoint

private def SpecialPeriods.Threefold.PiOne.latticeHom : Multiplicative Lattice →* GlobalGroup :=
  regularHom.comp SpecialPeriods.Threefold.specialRegularFamilyMarkedLatticeHom

private def SpecialPeriods.Threefold.PiOne.meridian (b : Bool) : GlobalGroup :=
  regularHom (SpecialPeriods.Threefold.specialRegularFamilyMarkedMeridianClass b)

private theorem SpecialPeriods.Threefold.PiOne.meridian_first_conjugation (v : Lattice) :
    meridian Bool.false * latticeHom (Multiplicative.ofAdd v) * (meridian Bool.false)⁻¹ =
      latticeHom (Multiplicative.ofAdd (A₁ *ᵥ v)) := by
  simpa only [map_mul, map_inv, meridian, latticeHom, MonoidHom.comp_apply] using
    congrArg regularHom
      (SpecialPeriods.Threefold.specialRegularFamilyMarkedMeridian_first_conjugation v)

private theorem SpecialPeriods.Threefold.PiOne.meridian_second_conjugation (v : Lattice) :
    meridian Bool.true * latticeHom (Multiplicative.ofAdd v) * (meridian Bool.true)⁻¹ =
      latticeHom (Multiplicative.ofAdd (A₂ *ᵥ v)) := by
  simpa only [map_mul, map_inv, meridian, latticeHom, MonoidHom.comp_apply] using
    congrArg regularHom
      (SpecialPeriods.Threefold.specialRegularFamilyMarkedMeridian_second_conjugation v)

private theorem
    SpecialPeriods.Threefold.PiOne.hom_ext {H : Type*} [Monoid H] (f g : GlobalGroup →* H)
    (hL : ∀ v : Multiplicative Lattice, f (latticeHom v) = g (latticeHom v))
    (hM : ∀ b : Bool, f (meridian b) = g (meridian b)) : f = g := by
  have h :=
    PeriodFamily.markedRegularFundamentalGroupHom_ext SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
      (f.comp regularHom) (g.comp regularHom) hL hM
  ext γ
  obtain ⟨δ, rfl⟩ := regularHom_surjective γ
  exact DFunLike.congr_fun h δ

private theorem
    SpecialPeriods.Threefold.PiOne.hom_eq_one {H : Type*} [Monoid H] (f : GlobalGroup →* H)
    (hL : ∀ v : Multiplicative Lattice, f (latticeHom v) = 1)
    (hM : ∀ b : Bool, f (meridian b) = 1) : f = 1 :=
  hom_ext f 1 hL hM

private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingPieceInclusionMap (j : Elliptic.Kind) :
    C(LocalSpace j, SpecialPeriods.Threefold.Space) :=
  ⟨SpecialPeriods.Threefold.EllipticGeometry.inclusion j, inclusion_continuous j⟩

private theorem
    SpecialPeriods.Threefold.EllipticGeometry.inclusion_eq_regular_overlap (j : Elliptic.Kind)
    (x : LocalSpace j) (hx : x ∈ (SpecialPeriods.Threefold.specialEllipticOverlap j).source) :
    SpecialPeriods.Threefold.EllipticGeometry.inclusion j x =
      SpecialPeriods.Threefold.regularFamilyInclusionMap
        (SpecialPeriods.Threefold.specialEllipticOverlap j x) := by
  change
    SpecialPeriods.Threefold.gluingData.inclusion (Option.some (Option.some j)) x =
      SpecialPeriods.Threefold.gluingData.inclusion Option.none
        (SpecialPeriods.Threefold.specialEllipticOverlap j x)
  exact
    (SpecialPeriods.Threefold.gluingData.inclusion_eq_iff (Option.some (Option.some j))
          Option.none x _).mpr
      ⟨hx, rfl⟩

private theorem
    SpecialPeriods.Threefold.EllipticGeometry.attachingLoop_mem_overlap (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (t : (unitInterval)) :
    attachingLoop j s₀ hs₀ hr t ∈ (SpecialPeriods.Threefold.specialEllipticOverlap j).source := by
  rw [SpecialPeriods.Threefold.specialEllipticOverlap_source]
  exact projectionToBase_attachingLoop_mem_regular j s₀ hs₀ hr t

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingFibreLoop_mem_overlap
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) (t : (unitInterval)) :
    attachingFibreLoop j s₀ hs₀ hr w t ∈
      (SpecialPeriods.Threefold.specialEllipticOverlap j).source := by
  rw [SpecialPeriods.Threefold.specialEllipticOverlap_source]
  exact projectionToBase_attachingFibreLoop_mem_regular j s₀ hs₀ hr w t

private theorem
    SpecialPeriods.Threefold.EllipticGeometry.attachingRegularPoint_one_eq (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (attachingUpstairsPoint j s₀ hs₀ 1, 0) =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (attachingUpstairsPoint j s₀ hs₀ 0, 0) := by
  calc
    _ = SpecialPeriods.Threefold.specialEllipticOverlap j (attachingLoop j s₀ hs₀ hr 1) :=
      (specialEllipticOverlap_attachingLoop j s₀ hs₀ hr 1).symm
    _ = SpecialPeriods.Threefold.specialEllipticOverlap j (attachingLoop j s₀ hs₀ hr 0) :=
      (congrArg (SpecialPeriods.Threefold.specialEllipticOverlap j)
        (attachingLoop j s₀ hs₀ hr).target)
    _ = _ := specialEllipticOverlap_attachingLoop j s₀ hs₀ hr 0

private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingRegularLoop (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    Path
      (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
        (attachingUpstairsPoint j s₀ hs₀ 0))
      (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
        (attachingUpstairsPoint j s₀ hs₀ 0))
    where
  toFun
    t :=
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).quotient
      (attachingUpstairsPoint j s₀ hs₀ t, 0)
  continuous_toFun :=
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).quotient_continuous.comp
      ((attachingUpstairsPoint_continuous j s₀ hs₀).prodMk continuous_const)
  source' := rfl
  target' := attachingRegularPoint_one_eq j s₀ hs₀ hr

private def SpecialPeriods.Threefold.EllipticGeometry.attachingRegularBaseLoop (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    Path (SpecialPeriods.triangleRegularProject (attachingUpstairsPoint j s₀ hs₀ 0))
      (SpecialPeriods.triangleRegularProject (attachingUpstairsPoint j s₀ hs₀ 0)) :=
  (attachingRegularLoop j s₀ hs₀ hr).map
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁
        SpecialPeriods.specialPeriodMap_generator₂)).projection_continuous

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingRegularLoop_eq_zeroSection
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    attachingRegularLoop j s₀ hs₀ hr =
      (attachingRegularBaseLoop j s₀ hs₀ hr).map
        ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).zeroSection_continuous := by
  ext t
  rfl

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingRegularBaseLoop_compact
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (t : (unitInterval)) :
    SpecialPeriods.Threefold.regularInclusion (attachingRegularBaseLoop j s₀ hs₀ hr t) =
      (SpecialPeriods.Threefold.punctureChart (Option.some j)).symm
        (CuspUniformization.exponential (s₀ - ((t : ℝ) : ℂ) / (j.order : ℂ)) ^ j.order) := by
  have h :=
    SpecialPeriods.Threefold.specialEllipticOverlap_base j (attachingLoop j s₀ hs₀ hr t)
      (attachingLoop_mem_overlap j s₀ hs₀ hr t)
  rw [specialEllipticOverlap_attachingLoop] at h
  exact h.trans (projectionToBase_attachingLoop j s₀ hs₀ hr t)

private theorem
    SpecialPeriods.Threefold.EllipticGeometry.attachingGlobalBasepoint_eq (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    SpecialPeriods.Threefold.EllipticGeometry.inclusion j (attachingBasepoint j s₀ hs₀ hr) =
      SpecialPeriods.Threefold.regularFamilyInclusionMap
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
          (attachingUpstairsPoint j s₀ hs₀ 0)) := by
  exact
    (inclusion_eq_regular_overlap j (attachingLoop j s₀ hs₀ hr 0)
          (attachingLoop_mem_overlap j s₀ hs₀ hr 0)).trans
      (congrArg SpecialPeriods.Threefold.regularFamilyInclusionMap
        (specialEllipticOverlap_attachingLoop j s₀ hs₀ hr 0))

private def
    SpecialPeriods.Threefold.EllipticGeometry.includedAttachingLoop (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    Path
      (SpecialPeriods.Threefold.regularFamilyInclusionMap
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
          (attachingUpstairsPoint j s₀ hs₀ 0)))
      (SpecialPeriods.Threefold.regularFamilyInclusionMap
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
          (attachingUpstairsPoint j s₀ hs₀ 0))) :=
  ((attachingLoop j s₀ hs₀ hr).map (inclusion_continuous j)).cast
    (attachingGlobalBasepoint_eq j s₀ hs₀ hr).symm (attachingGlobalBasepoint_eq j s₀ hs₀ hr).symm

private theorem SpecialPeriods.Threefold.EllipticGeometry.includedAttachingLoop_eq_regular
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    includedAttachingLoop j s₀ hs₀ hr =
      (attachingRegularLoop j s₀ hs₀ hr).map
        SpecialPeriods.Threefold.regularFamilyInclusionMap.continuous := by
  ext t
  exact
    (inclusion_eq_regular_overlap j (attachingLoop j s₀ hs₀ hr t)
          (attachingLoop_mem_overlap j s₀ hs₀ hr t)).trans
      (congrArg SpecialPeriods.Threefold.regularFamilyInclusionMap
        (specialEllipticOverlap_attachingLoop j s₀ hs₀ hr t))

private def SpecialPeriods.Threefold.EllipticGeometry.includedAttachingFibreLoop (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) :
    Path
      (SpecialPeriods.Threefold.regularFamilyInclusionMap
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
          (attachingUpstairsPoint j s₀ hs₀ 0)))
      (SpecialPeriods.Threefold.regularFamilyInclusionMap
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
          (attachingUpstairsPoint j s₀ hs₀ 0))) :=
  ((attachingFibreLoop j s₀ hs₀ hr w).map (inclusion_continuous j)).cast
    (attachingGlobalBasepoint_eq j s₀ hs₀ hr).symm (attachingGlobalBasepoint_eq j s₀ hs₀ hr).symm

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingRegularBaseLoop_plane
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (t : (unitInterval)) :
    (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
          (attachingRegularBaseLoop j s₀ hs₀ hr t) :
        ℂ) =
      attachingPlaneCoordinate j
        (CuspUniformization.exponential s₀ ^ j.order *
          SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit t) := by
  have h :=
    attachingPlaneCoordinate_eq_regularPlane j _ (attachingRegularBaseLoop j s₀ hs₀ hr t)
      (attachingRegularBaseLoop_compact j s₀ hs₀ hr t)
  rwa [attaching_log_parameter_clockwise] at h

private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianSquare (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (hsmall : ‖CuspUniformization.exponential s₀‖ ^ j.order < attachingMeridianRadius j) :
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare (attachingRegularBaseLoop j s₀ hs₀ hr)
      (SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian
        (attachingMeridianIndex j)) :=
  (attachingPlaneControl j).regularMeridianSquare (attachingMeridianIndex j)
    (attachingPlaneCoordinate_zero_eq_center j) (CuspUniformization.exponential s₀ ^ j.order)
    (attaching_initial_coordinate_ne_zero j s₀) (attaching_parameters_control_bound j hsmall)
    (attachingRegularBaseLoop j s₀ hs₀ hr) (attachingRegularBaseLoop_plane j s₀ hs₀ hr)

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingMeridian_map_whisker
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (hsmall : ‖CuspUniformization.exponential s₀‖ ^ j.order < attachingMeridianRadius j)
    {G : Type*} [Group G]
    (τ :
      Path
        (SpecialPeriods.triangleRegularProject
          PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
        (SpecialPeriods.triangleRegularProject (attachingUpstairsPoint j s₀ hs₀ 0)))
    (φ :
      FundamentalGroup SpecialPeriods.TriangleRegularQuotient
          (SpecialPeriods.triangleRegularProject
            PeriodFamily.Meridians.normalizedRegularMeridianBasepoint) →*
        G)
    (hcomm : ∀ g h : G, Commute g h) :
    φ
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk
            (τ.trans ((attachingRegularBaseLoop j s₀ hs₀ hr).trans τ.symm)))) =
      if PeriodFamily.Meridians.normalizationReversesMeridians then
        φ (PeriodFamily.Meridians.compatibleRegularMeridianClass (attachingMeridianIndex j))
      else
        (φ
            (PeriodFamily.Meridians.compatibleRegularMeridianClass
              (attachingMeridianIndex j)))⁻¹ := by
  have h := (attachingMeridianSquare j s₀ hs₀ hr hsmall).map_whisker_eq τ φ hcomm
  rw [SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian_class] at h
  simpa only [apply_ite, map_inv] using h

private def
    SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter (j : Elliptic.Kind) : ℂ :=
  (exists_small_attaching_parameters j).choose

private theorem SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter_im_pos
    (j : Elliptic.Kind) : 0 < (chosenAttachingParameter j).im :=
  (exists_small_attaching_parameters j).choose_spec.1

private theorem SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter_bound
    (j : Elliptic.Kind) :
    ‖CuspUniformization.exponential (chosenAttachingParameter j)‖ ^ j.order <
      attachingMeridianRadius j :=
  (exists_small_attaching_parameters j).choose_spec.2

private theorem SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter_filling_bound
    (j : Elliptic.Kind) :
    ‖CuspUniformization.exponential (chosenAttachingParameter j)‖ ^ j.order <
      SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j) :=
  attaching_parameters_filling_bound j (chosenAttachingParameter_bound j)

private def SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBasepoint (j : Elliptic.Kind) :
    SpecialPeriods.TriangleRegularQuotient :=
  SpecialPeriods.triangleRegularProject
    (attachingUpstairsPoint j (chosenAttachingParameter j) (chosenAttachingParameter_im_pos j) 0)

private def SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBaseLoop (j : Elliptic.Kind) :
    Path (chosenAttachingBasepoint j) (chosenAttachingBasepoint j) :=
  attachingRegularBaseLoop j (chosenAttachingParameter j) (chosenAttachingParameter_im_pos j)
    (chosenAttachingParameter_filling_bound j)

private def SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare (j : Elliptic.Kind) :
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare (chosenAttachingBaseLoop j)
      (SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian
        (attachingMeridianIndex j)) :=
  attachingMeridianSquare j (chosenAttachingParameter j) (chosenAttachingParameter_im_pos j)
    (chosenAttachingParameter_filling_bound j) (chosenAttachingParameter_bound j)

end Mathoverflow1973

end
