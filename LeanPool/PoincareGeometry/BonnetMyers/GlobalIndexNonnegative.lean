/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.GlobalSecondVariation
import LeanPool.PoincareGeometry.BonnetMyers.MinimizingGeodesic
import LeanPool.PoincareGeometry.BonnetMyers.SecondVariationGeometry
import LeanPool.PoincareGeometry.BonnetMyers.MetricBridge

/-!
# Global nonnegativity of the sine index form

This module glues the chartwise broken variations constructed in
`GlobalSecondVariation` and compares their total energy with an
endpoint-minimizing unit-speed geodesic.
-/

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology Interval RealInnerProductSpace BigOperators

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- The ordinary speed of a coordinate broken variation, read as an actual
tangent vector in the fixed chart frame. -/
def LocalGeodesicData.CoordinateBrokenVariationData.coordinateSpeed
    (d : LocalGeodesicData.CoordinateBrokenVariationData E)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (e t : ℝ) : ℝ :=
  ‖LocalGeodesicData.coordinateFrameCombination
      (I := I) (M := M) (x₀ := c) basis (d.velocity e t)
      ((extChartAt I c).symm (d.position e t))‖

theorem LocalGeodesicData.CoordinateBrokenVariationData.energyDensity_eq_half_speed_sq
    (d : LocalGeodesicData.CoordinateBrokenVariationData E)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (e t : ℝ) :
    d.energyDensity (I := I) (M := M) c basis e t =
      (2 : ℝ)⁻¹ * (d.coordinateSpeed (I := I) (M := M) c basis e t) ^ 2 := by
  unfold LocalGeodesicData.CoordinateBrokenVariationData.energyDensity
    LocalGeodesicData.coordinateEnergyDensity
    LocalGeodesicData.CoordinateBrokenVariationData.coordinateSpeed
  rw [real_inner_self_eq_norm_sq]

/-- The path length of an inverse-chart curve on an arbitrary ordered
interval is the extended integral of its coordinate-frame speed. -/
theorem inverseChart_pathELength_eq_coordinate_speed_Ioo
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z z' : ℝ → E) {a b : ℝ}
    (htarget : ∀ t ∈ Ioo a b, z t ∈ (extChartAt I c).target)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt z (z' t) t) :
    pathELength I ((extChartAt I c).symm ∘ z) a b =
      ∫⁻ t in Ioo a b,
        ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis (z' t)
          ((extChartAt I c).symm (z t))‖ₑ := by
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hmf := CurveConnection.hasMFDerivAt_inverseChartCurve_of_hasDerivAt
    (I := I) (M := M) (E := E) c basis z (htarget t ht) (hderiv t ht)
  change ‖mfderiv% ((extChartAt I c).symm ∘ z) t 1‖ₑ = _
  rw [hmf.mfderiv, CurveConnection.timeTangentMap_eq_toSpanSingleton]
  change ‖(1 : ℝ) • LocalGeodesicData.coordinateFrameCombination
    (I := I) (M := M) (x₀ := c) basis (z' t)
      ((extChartAt I c).symm (z t))‖ₑ = _
  rw [one_smul]

/-- A coordinate broken variation is a genuine `C¹` manifold path when its
displayed position derivative and velocity are continuous on the piece. -/
theorem LocalGeodesicData.CoordinateBrokenVariationData.manifoldPath_contMDiffOn
    (d : LocalGeodesicData.CoordinateBrokenVariationData E)
    (c : M) {e a b : ℝ} (hab : a < b)
    (hderiv : ∀ t ∈ Icc a b,
      HasDerivAt (d.position e) (d.velocity e t) t)
    (hvelocity : ContinuousOn (d.velocity e) (Icc a b))
    (htarget : ∀ t ∈ Icc a b,
      d.position e t ∈ (extChartAt I c).target) :
    ContMDiffOn (𝓘(ℝ, ℝ)) I 1
      ((extChartAt I c).symm ∘ d.position e) (Icc a b) := by
  have hcoordinate : ContDiffOn ℝ 1 (d.position e) (Icc a b) := by
    rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)]
    constructor
    · intro t ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · apply hvelocity.congr
      intro t ht
      exact (hderiv t ht).hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt ht)
  have hcurve := (contMDiffOn_extChartAt_symm
    (I := I) (n := (1 : WithTop ℕ∞)) c).comp
      hcoordinate.contMDiffOn htarget
  simpa only [Function.comp_def] using hcurve

/-- For a continuous coordinate speed, the ordinary interval integral is
the real representative of the inverse-chart path length. -/
theorem LocalGeodesicData.CoordinateBrokenVariationData.pathELength_eq_ofReal_integral_speed
    (d : LocalGeodesicData.CoordinateBrokenVariationData E)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {e a b : ℝ} (hab : a < b)
    (hderiv : ∀ t ∈ Icc a b,
      HasDerivAt (d.position e) (d.velocity e t) t)
    (htarget : ∀ t ∈ Icc a b,
      d.position e t ∈ (extChartAt I c).target)
    (hspeed : ContinuousOn
      (d.coordinateSpeed (I := I) (M := M) c basis e) (Icc a b)) :
    pathELength I ((extChartAt I c).symm ∘ d.position e) a b =
      ENNReal.ofReal (∫ t in a..b,
        d.coordinateSpeed (I := I) (M := M) c basis e t) := by
  let B : ℝ → ℝ := d.coordinateSpeed (I := I) (M := M) c basis e
  have hBintIoc : Integrable B (volume.restrict (Ioc a b)) := by
    change IntegrableOn B (Ioc a b)
    exact hspeed.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hIntEq : ENNReal.ofReal (∫ t in a..b, B t) =
      ∫⁻ t in Ioo a b,
        ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis (d.velocity e t)
          ((extChartAt I c).symm (d.position e t))‖ₑ := by
    rw [intervalIntegral.integral_of_le hab.le]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      hBintIoc (ae_of_all _ fun _ ↦ norm_nonneg _)]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    apply lintegral_congr
    intro t
    exact ofReal_norm _
  rw [hIntEq]
  exact inverseChart_pathELength_eq_coordinate_speed_Ioo
    (I := I) (M := M) c basis (d.position e) (d.velocity e)
      (fun t ht ↦ htarget t ⟨ht.1.le, ht.2.le⟩)
      (fun t ht ↦ hderiv t ⟨ht.1.le, ht.2.le⟩)

/-- Joint continuity of position and velocity in one fixed chart makes the
ordinary coordinate-frame speed jointly continuous. -/
theorem LocalGeodesicData.CoordinateBrokenVariationData.coordinateSpeed_continuousAt
    [IsContinuousRiemannianBundle E TM]
    (d : LocalGeodesicData.CoordinateBrokenVariationData E)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {q : ℝ × ℝ}
    (hposition : ContinuousAt (fun x : ℝ × ℝ ↦ d.position x.1 x.2) q)
    (hvelocity : ContinuousAt (fun x : ℝ × ℝ ↦ d.velocity x.1 x.2) q)
    (htarget : d.position q.1 q.2 ∈ (extChartAt I c).target) :
    ContinuousAt (fun x : ℝ × ℝ ↦
      d.coordinateSpeed (I := I) (M := M) c basis x.1 x.2) q := by
  have hy : ContinuousAt
      (fun x : ℝ × ℝ ↦ (extChartAt I c).symm (d.position x.1 x.2)) q :=
    (continuousAt_extChartAt_symm'' htarget).comp_of_eq hposition rfl
  have hsource : (extChartAt I c).symm (d.position q.1 q.2) ∈
      (extChartAt I c).source :=
    (extChartAt I c).map_target htarget
  have hinner :=
    IntrinsicGeodesic.GlobalGeodesic.coordinateFrameCombination_inner_continuousAt
      (I := I) (M := M) c basis hy hvelocity hvelocity hsource
  have hsqrt : ContinuousAt (fun x : ℝ × ℝ ↦ Real.sqrt
      (inner ℝ
        (LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis (d.velocity x.1 x.2)
            ((extChartAt I c).symm (d.position x.1 x.2)))
        (LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis (d.velocity x.1 x.2)
            ((extChartAt I c).symm (d.position x.1 x.2))))) q :=
    Real.continuous_sqrt.continuousAt.comp hinner
  apply hsqrt.congr_of_eventuallyEq
  filter_upwards [] with x
  unfold LocalGeodesicData.CoordinateBrokenVariationData.coordinateSpeed
  rw [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm]

namespace IntrinsicGeodesic.GlobalGeodesic

/-- A complete-time geodesic with zero initial velocity is constant.  This
uses the intrinsic length estimate and the separated Riemannian distance,
not a coordinate uniqueness shortcut. -/
theorem curve_eq_initial_of_initial_velocity_eq_zero
    [ConnectedSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (hmetric : cov.IsMetricCompatibleTangent) (hv₀ : v₀ = 0)
    (t : ℝ) : curve γ t = x₀ := by
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : IsRiemannianManifold I M := by infer_instance
  have hzeroNorm : ‖v₀‖ₑ = 0 := by simp [hv₀]
  rcases le_total (0 : ℝ) t with ht | ht
  · have hdist : riemannianEDist I (curve γ 0) (curve γ t) = 0 := by
      apply le_antisymm
      · calc
          riemannianEDist I (curve γ 0) (curve γ t) ≤
              ‖v₀‖ₑ * ENNReal.ofReal (t - 0) :=
            riemannianEDist_le_constant_speed_mul
              (I := I) (M := M) γ hmetric ht
          _ = 0 := by rw [hzeroNorm, zero_mul]
      · exact bot_le
    have hed : edist (curve γ 0) (curve γ t) = 0 := by
      rw [IsRiemannianManifold.out (I := I) (M := M)]
      exact hdist
    have hcurve : curve γ 0 = curve γ t := edist_eq_zero.mp hed
    rw [← hcurve, γ.curve_initial]
  · have hdist : riemannianEDist I (curve γ t) (curve γ 0) = 0 := by
      apply le_antisymm
      · calc
          riemannianEDist I (curve γ t) (curve γ 0) ≤
              ‖v₀‖ₑ * ENNReal.ofReal (0 - t) :=
            riemannianEDist_le_constant_speed_mul
              (I := I) (M := M) γ hmetric ht
          _ = 0 := by rw [hzeroNorm, zero_mul]
      · exact bot_le
    have hed : edist (curve γ t) (curve γ 0) = 0 := by
      rw [IsRiemannianManifold.out (I := I) (M := M)]
      exact hdist
    have hcurve : curve γ t = curve γ 0 := edist_eq_zero.mp hed
    rw [hcurve, γ.curve_initial]

/-- On one strict chart piece, sufficiently small variation parameters give
a genuine manifold path with continuous speed.  Its endpoint distance is
therefore bounded by the corresponding ordinary speed integral. -/
theorem GlobalParallelField.eventually_sineBrokenChartData_speed_and_distance
    [IsContinuousRiemannianBundle E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [IsContMDiffRiemannianBundle I 2 E TM]
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (htorsion : cov.torsion = 0)
    (L : ℝ) {a b : ℝ} (hab : a < b)
    (Nleft : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) a) (p.sineTestField L a))
    (Nright : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) b) (p.sineTestField L b))
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {O : Set M} (hOopen : IsOpen O)
    (hOsub : O ⊆ IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c basis)
    (hbase : ∀ t ∈ Icc a b, curve (shift G t₀) t ∈ O) :
    let d := p.sineBrokenChartData L Nleft Nright c basis
    ∀ᶠ e in nhds (0 : ℝ),
      ContinuousOn
          (d.coordinateSpeed (I := I) (M := M) c basis e) (Icc a b) ∧
        riemannianEDist I (curve Nleft e) (curve Nright e) ≤
          ENNReal.ofReal (∫ t in a..b,
            d.coordinateSpeed (I := I) (M := M) c basis e t) := by
  let d := p.sineBrokenChartData L Nleft Nright c basis
  obtain ⟨s, _hsCompact, hs0, _henergy, _hfirst, _hsecond,
      hnodesO, hposition⟩ :=
    p.exists_sineBrokenChartData_regular_rectangle hmetric htorsion L hab
      Nleft Nright c basis hOopen hOsub hbase
  filter_upwards [hs0] with e he
  have hcomponents : ∀ t ∈ Icc a b,
      ContinuousAt d.z t ∧ ContinuousAt d.dz t ∧
      ContinuousAt d.J t ∧ ContinuousAt d.dJ t ∧
      ContinuousAt d.leftNode e ∧ ContinuousAt d.rightNode e ∧
      ContinuousAt d.leftVelocity e ∧ ContinuousAt d.rightVelocity e ∧
      ContinuousAt d.leftAcceleration e ∧
        ContinuousAt d.rightAcceleration e := by
    intro t ht
    exact p.sineBrokenChartData_component_continuity hmetric L Nleft Nright
      c basis hOopen hOsub (hbase t ht) (hnodesO e he).1 (hnodesO e he).2
  have hpositionJoint : ∀ t ∈ Icc a b,
      ContinuousAt (fun q : ℝ × ℝ ↦ d.position q.1 q.2) (e, t) := by
    intro t ht
    obtain ⟨hz, _hdz, hJ, _hdJ, hln, hrn, _hlv, _hrv, _hla, _hra⟩ :=
      hcomponents t ht
    exact LocalGeodesicData.CoordinateBrokenVariationData.position_continuousAt
      d hz hJ hln hrn
  have hvelocityJoint : ∀ t ∈ Icc a b,
      ContinuousAt (fun q : ℝ × ℝ ↦ d.velocity q.1 q.2) (e, t) := by
    intro t ht
    obtain ⟨hz, hdz, hJ, hdJ, hln, hrn, _hlv, _hrv, _hla, _hra⟩ :=
      hcomponents t ht
    exact LocalGeodesicData.CoordinateBrokenVariationData.velocity_continuousAt
      d hdz hdJ hz hJ hln hrn
  have hspeed : ContinuousOn
      (d.coordinateSpeed (I := I) (M := M) c basis e) (Icc a b) := by
    intro t ht
    have h := d.coordinateSpeed_continuousAt (I := I) (M := M) c basis
      (hpositionJoint t ht) (hvelocityJoint t ht) (hposition e he t ht).1
    exact (h.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hbaseData : ∀ t ∈ Icc a b,
      HasDerivAt d.z (d.dz t) t ∧ HasDerivAt d.J (d.dJ t) t := by
    intro t ht
    have h := p.sineBrokenChartData_base_derivatives hmetric L Nleft Nright
      c basis hOopen hOsub (hbase t ht)
    exact ⟨h.1, h.2.2.1⟩
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivAt (d.position e) (d.velocity e t) t := by
    intro t ht
    exact LocalGeodesicData.coordinateBrokenVariationPiece_hasDerivAt_time
      d.a d.b e t d.dz d.dJ d.z d.J d.leftNode d.rightNode
        (hbaseData t ht).1 (hbaseData t ht).2
  have hvelocity : ContinuousOn (d.velocity e) (Icc a b) := by
    intro t ht
    exact ((hvelocityJoint t ht).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have htarget : ∀ t ∈ Icc a b,
      d.position e t ∈ (extChartAt I c).target :=
    fun t ht ↦ (hposition e he t ht).1
  have hpath : ContMDiffOn (𝓘(ℝ, ℝ)) I 1
      ((extChartAt I c).symm ∘ d.position e) (Icc a b) :=
    d.manifoldPath_contMDiffOn (I := I) (M := M) c hab
      hderiv hvelocity htarget
  have hleft : ((extChartAt I c).symm ∘ d.position e) a = curve Nleft e := by
    change (extChartAt I c).symm (d.position e a) = curve Nleft e
    rw [show d.position e a = d.leftNode e by
      exact LocalGeodesicData.coordinateBrokenVariationPiece_left
        hab d.z d.J d.leftNode d.rightNode e]
    unfold d GlobalParallelField.sineBrokenChartData fixedChartPosition
    exact (extChartAt I c).left_inv (hOsub (hnodesO e he).1).1
  have hright : ((extChartAt I c).symm ∘ d.position e) b = curve Nright e := by
    change (extChartAt I c).symm (d.position e b) = curve Nright e
    rw [show d.position e b = d.rightNode e by
      exact LocalGeodesicData.coordinateBrokenVariationPiece_right
        hab d.z d.J d.leftNode d.rightNode e]
    unfold d GlobalParallelField.sineBrokenChartData fixedChartPosition
    exact (extChartAt I c).left_inv (hOsub (hnodesO e he).2).1
  have hlength := d.pathELength_eq_ofReal_integral_speed
    (I := I) (M := M) c basis hab hderiv htarget hspeed
  refine ⟨hspeed, ?_⟩
  calc
    riemannianEDist I (curve Nleft e) (curve Nright e) ≤
        pathELength I ((extChartAt I c).symm ∘ d.position e) a b :=
      riemannianEDist_le_pathELength hpath hleft hright hab.le
    _ = ENNReal.ofReal (∫ t in a..b,
          d.coordinateSpeed (I := I) (M := M) c basis e t) := hlength
/-- The sine index form is nonnegative along every unit-speed global geodesic
segment which realizes the intrinsic distance between its endpoints.  The
proof constructs a finite chartwise broken variation with shared geodesic
nodes, applies endpoint minimality to its total length, and telescopes the
piecewise second-variation identities. -/
theorem GlobalParallelField.globalIndexForm_sine_nonnegative_of_endpoint_minimizing
    [ConnectedSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [IsContMDiffRiemannianBundle I 2 E TM]
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (htorsion : cov.torsion = 0)
    (hcomplete : @CompleteSpace M
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace.toUniformSpace)
    {L : ℝ} (hL : 0 < L)
    (hunit : ‖velocity G t₀‖ = 1)
    (hendpoint : riemannianEDist I
      (curve (shift G t₀) 0) (curve (shift G t₀) L) = ENNReal.ofReal L) :
    0 ≤ globalIndexForm (curvature (I := I) (M := M) cov) G t₀
      (p.sineTestField L) (p.sineTestDerivativeField L) L := by
  classical
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : IsRiemannianManifold I M := by infer_instance
  let γ := shift G t₀
  obtain ⟨τ, hτ0, hτmono, ⟨m, hm⟩, hcharts⟩ :=
    exists_smoothFrameAgreementPartition
      (I := I) (M := M) (cov := cov) γ hL.le
  choose c O hOopen hOsub hbase using hcharts
  let N : ∀ q : Icc (0 : ℝ) L,
      GlobalGeodesic (I := I) (M := M) cov
        (curve γ q.1) (p.sineTestField L q.1) := fun q ↦
    Classical.choice (PartialGeodesic.exists_globalGeodesic_of_complete
      (I := I) (M := M) (cov := cov)
      (x₀ := curve γ q.1) (v₀ := p.sineTestField L q.1)
      hmetric hcomplete)
  let a : ℕ → ℝ := fun n ↦ (τ n).1
  let b : ℕ → ℝ := fun n ↦ (τ (n + 1)).1
  let d : ℕ → LocalGeodesicData.CoordinateBrokenVariationData E := fun n ↦
    p.sineBrokenChartData L (N (τ n)) (N (τ (n + 1)))
      (c n) (Module.finBasis ℝ E)
  let speed : ℝ → ℕ → ℝ → ℝ := fun e n ↦
    (d n).coordinateSpeed (I := I) (M := M) (c n)
      (Module.finBasis ℝ E) e
  let S : Finset ℕ := (Finset.range m).filter (fun n ↦ a n < b n)
  have hτm : τ m = ⟨L, hL.le, le_rfl⟩ := hm m le_rfl
  have hab : ∀ n ∈ S, a n < b n := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hduration : (∑ n ∈ S, (b n - a n)) = L := by
    calc
      (∑ n ∈ S, (b n - a n)) =
          ∑ n ∈ Finset.range m, (b n - a n) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro n hnRange hnS
        have hnonstrict : ¬ a n < b n := by
          intro hstrict
          exact hnS (Finset.mem_filter.mpr ⟨hnRange, hstrict⟩)
        have hmono : a n ≤ b n := by
          exact_mod_cast hτmono (Nat.le_succ n)
        exact sub_eq_zero.mpr (le_antisymm (not_lt.mp hnonstrict) hmono)
      _ = (τ m).1 - (τ 0).1 := by
        simpa [a, b] using Finset.sum_range_sub (fun n ↦ (τ n).1) m
      _ = L := by rw [hτm, hτ0]; simp
  have hbasePiece : ∀ n, ∀ t ∈ Icc (a n) (b n), curve γ t ∈ O n := by
    intro n t ht
    let q : Icc (0 : ℝ) L :=
      ⟨t, le_trans (τ n).property.1 ht.1,
        le_trans ht.2 (τ (n + 1)).property.2⟩
    apply hbase n q
    exact ⟨ht.1, ht.2⟩
  have hregular : ∀ n ∈ S, ∀ᶠ e in nhds (0 : ℝ),
      ContinuousOn (speed e n) (Icc (a n) (b n)) ∧
        riemannianEDist I (curve (N (τ n)) e) (curve (N (τ (n + 1))) e) ≤
          ENNReal.ofReal (∫ t in a n..b n, speed e n t) := by
    intro n hn
    have h := p.eventually_sineBrokenChartData_speed_and_distance
      hmetric htorsion L (hab n hn) (N (τ n)) (N (τ (n + 1)))
      (c n) (Module.finBasis ℝ E) (hOopen n) (hOsub n) (hbasePiece n)
    simpa [γ, a, b, d, speed] using h
  have hregularAll : ∀ᶠ e in nhds (0 : ℝ), ∀ n ∈ S,
      ContinuousOn (speed e n) (Icc (a n) (b n)) ∧
        riemannianEDist I (curve (N (τ n)) e) (curve (N (τ (n + 1))) e) ≤
          ENNReal.ofReal (∫ t in a n..b n, speed e n t) :=
    (Filter.eventually_all_finset S).2 hregular
  have hspeedZero : ∀ n, n ∈ S → ∀ t ∈ Icc (a n) (b n),
      speed 0 n t = 1 := by
    intro n hn t ht
    obtain ⟨hleftNode, hrightNode, _hleftVelocity, _hrightVelocity,
        _hleftAcceleration, _hrightAcceleration⟩ :=
      p.sineBrokenChartData_node_initial_data L
        (N (τ n)) (N (τ (n + 1))) (c n) (Module.finBasis ℝ E)
    have hpositionZero : (d n).position 0 t = (d n).z t := by
      exact LocalGeodesicData.coordinateBrokenVariationPiece_zero
        (d n).a (d n).b (d n).z (d n).J
          (d n).leftNode (d n).rightNode hleftNode hrightNode t
    have hvelocityZero : (d n).velocity 0 t = (d n).dz t := by
      exact LocalGeodesicData.coordinateBrokenVariationVelocity_zero
        (d n).a (d n).b (d n).dz (d n).dJ (d n).z (d n).J
          (d n).leftNode (d n).rightNode hleftNode hrightNode t
    have hmem := hOsub n (hbasePiece n t ht)
    have hread := coordinateFrameCombination_fixedChartReadout
      (I := I) (M := M) (c n) (Module.finBasis ℝ E) hmem.1
        (velocity γ t)
    have hinverse : (extChartAt I (c n)).symm
        (fixedChartPosition (E := E) γ (c n) t) = curve γ t := by
      unfold fixedChartPosition
      exact (extChartAt I (c n)).left_inv hmem.1
    unfold speed LocalGeodesicData.CoordinateBrokenVariationData.coordinateSpeed
    rw [hpositionZero, hvelocityZero]
    change ‖LocalGeodesicData.coordinateFrameCombination
      (I := I) (M := M) (x₀ := c n) (Module.finBasis ℝ E)
        (fixedChartVelocity (E := E) γ (c n) t)
        ((extChartAt I (c n)).symm
          (fixedChartPosition (E := E) γ (c n) t))‖ = 1
    rw [hinverse]
    unfold fixedChartVelocity
    rw [hread,
      norm_velocity_eq_initial (I := I) (M := M) γ hmetric t]
    simpa [γ] using hunit
  have hspeedNonneg : ∀ᶠ e in nhds (0 : ℝ), ∀ n, n ∈ S →
      ∀ t ∈ Icc (a n) (b n), 0 ≤ speed e n t := by
    apply Filter.Eventually.of_forall
    intro e n hn t ht
    exact norm_nonneg _
  have hleftFixed : ∀ e : ℝ,
      curve (N (τ 0)) e = curve γ 0 := by
    intro e
    have hv : p.sineTestField L (τ 0).1 = 0 := by
      rw [hτ0]
      exact p.sineTestField_zero_left L
    have h := curve_eq_initial_of_initial_velocity_eq_zero
      (I := I) (M := M) (N (τ 0)) hmetric hv e
    simpa [hτ0] using h
  have hrightFixed : ∀ e : ℝ,
      curve (N (τ m)) e = curve γ L := by
    intro e
    have hv : p.sineTestField L (τ m).1 = 0 := by
      rw [hτm]
      exact p.sineTestField_zero_right hL
    have h := curve_eq_initial_of_initial_velocity_eq_zero
      (I := I) (M := M) (N (τ m)) hmetric hv e
    simpa [hτm] using h
  have hlength : ∀ᶠ e in nhds (0 : ℝ),
      L ≤ ∑ n ∈ S, ∫ t in a n..b n, speed e n t := by
    filter_upwards [hregularAll] with e he
    let edge : ℕ → ℝ≥0∞ := fun n ↦
      if a n < b n then
        ENNReal.ofReal (∫ t in a n..b n, speed e n t)
      else 0
    have hedge : ∀ {n}, n < m →
        edist (curve (N (τ n)) e) (curve (N (τ (n + 1))) e) ≤ edge n := by
      intro n hn
      by_cases hstrict : a n < b n
      · have hnS : n ∈ S := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hn, hstrict⟩
        have hpiece := (he n hnS).2
        rw [← IsRiemannianManifold.out (I := I) (M := M)] at hpiece
        simpa [edge, hstrict] using hpiece
      · have hmono : a n ≤ b n := by
          exact_mod_cast hτmono (Nat.le_succ n)
        have habEq : a n = b n := le_antisymm hmono (not_lt.mp hstrict)
        have hτeq : τ n = τ (n + 1) := Subtype.ext habEq
        have hcurveEq : curve (N (τ n)) e = curve (N (τ (n + 1))) e :=
          congrArg (fun q ↦ curve (N q) e) hτeq
        simp [edge, hstrict, hcurveEq]
    have hpolygon := edist_le_range_sum_of_edist_le
      (f := fun n ↦ curve (N (τ n)) e) m hedge
    rw [hleftFixed e, hrightFixed e,
      IsRiemannianManifold.out (I := I) (M := M), hendpoint] at hpolygon
    have hintegralNonneg : ∀ n, n ∈ S →
        0 ≤ ∫ t in a n..b n, speed e n t := by
      intro n hn
      exact intervalIntegral.integral_nonneg (hab n hn).le
        (fun t ht ↦ norm_nonneg _)
    have hedgeSum : (∑ n ∈ Finset.range m, edge n) =
        ENNReal.ofReal (∑ n ∈ S, ∫ t in a n..b n, speed e n t) := by
      calc
        (∑ n ∈ Finset.range m, edge n) =
            ∑ n ∈ S, ENNReal.ofReal (∫ t in a n..b n, speed e n t) := by
          simp [edge, S, Finset.sum_filter]
        _ = ENNReal.ofReal (∑ n ∈ S,
              ∫ t in a n..b n, speed e n t) := by
          exact (ENNReal.ofReal_sum_of_nonneg hintegralNonneg).symm
    rw [hedgeSum] at hpolygon
    exact (ENNReal.ofReal_le_ofReal_iff
      (Finset.sum_nonneg fun n hn ↦ hintegralNonneg n hn)).mp hpolygon
  let Kdensity : ℝ → ℝ := fun t ↦
    inner ℝ (p.sineTestDerivativeField L t)
        (p.sineTestDerivativeField L t) -
      inner ℝ (p.sineTestField L t)
        (curvature (cov := cov) (curve γ t)
          (p.sineTestField L t) (velocity γ t) (velocity γ t))
  let pieceEnergy : ℕ → ℝ → ℝ := fun n e ↦
    ∫ t in a n..b n,
      (d n).energyDensity (I := I) (M := M) (c n)
        (Module.finBasis ℝ E) e t
  have hpieceSecond : ∀ n ∈ S,
      ContDiffAt ℝ 2 (pieceEnergy n) 0 ∧
        iteratedDeriv 2 (pieceEnergy n) 0 =
          ∫ t in a n..b n, Kdensity t := by
    intro n hn
    have h := p.sineBrokenChartData_piece_secondVariation
      hmetric htorsion L (hab n hn) (N (τ n)) (N (τ (n + 1)))
      (c n) (Module.finBasis ℝ E) (hOopen n) (hOsub n) (hbasePiece n)
    simpa [γ, a, b, d, pieceEnergy, Kdensity] using h
  have henergyEq :
      (fun e ↦ (2 : ℝ)⁻¹ *
        ∑ n ∈ S, ∫ t in a n..b n, (speed e n t) ^ 2) =
      (fun e ↦ ∑ n ∈ S, pieceEnergy n e) := by
    funext e
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    calc
      (2 : ℝ)⁻¹ * (∫ t in a n..b n, (speed e n t) ^ 2) =
          ∫ t in a n..b n, (2 : ℝ)⁻¹ * (speed e n t) ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
      _ = pieceEnergy n e := by
        unfold pieceEnergy
        apply intervalIntegral.integral_congr
        intro t ht
        exact ((d n).energyDensity_eq_half_speed_sq
          (I := I) (M := M) (c n) (Module.finBasis ℝ E) e t).symm.trans
            (by rfl)
  have henergyC2 : ContDiffAt ℝ 2
      (fun e ↦ (2 : ℝ)⁻¹ *
        ∑ n ∈ S, ∫ t in a n..b n, (speed e n t) ^ 2) 0 := by
    rw [henergyEq]
    exact ContDiffAt.sum (fun n hn ↦ (hpieceSecond n hn).1)
  have hsecondNonneg : 0 ≤ iteratedDeriv 2
      (fun e ↦ (2 : ℝ)⁻¹ *
        ∑ n ∈ S, ∫ t in a n..b n, (speed e n t) ^ 2) 0 :=
    brokenEnergy_secondVariation_nonnegative_of_eventually_length_lower_bound
      hab hduration
      (hregularAll.mono fun e he n hn ↦ (he n hn).1)
      hspeedNonneg hspeedZero hlength henergyC2
  have hsumSecondNonneg : 0 ≤ ∑ n ∈ S, ∫ t in a n..b n, Kdensity t := by
    rw [henergyEq] at hsecondNonneg
    have hderivSum := iteratedDeriv_fun_sum
      (n := 2) (x := (0 : ℝ)) (I := S)
      (fun n hn ↦ (hpieceSecond n hn).1)
    rw [hderivSum] at hsecondNonneg
    calc
      0 ≤ ∑ n ∈ S, iteratedDeriv 2 (pieceEnergy n) 0 := hsecondNonneg
      _ = ∑ n ∈ S, ∫ t in a n..b n, Kdensity t := by
        apply Finset.sum_congr rfl
        intro n hn
        exact (hpieceSecond n hn).2
  have hsumAllNonneg : 0 ≤ ∑ n ∈ Finset.range m,
      ∫ t in a n..b n, Kdensity t := by
    have hsumEq : (∑ n ∈ S, ∫ t in a n..b n, Kdensity t) =
        ∑ n ∈ Finset.range m, ∫ t in a n..b n, Kdensity t := by
      apply Finset.sum_subset (show S ⊆ Finset.range m by
        exact Finset.filter_subset _ _)
      intro n hnRange hnS
      have hnonstrict : ¬ a n < b n := by
        intro hstrict
        exact hnS (Finset.mem_filter.mpr ⟨hnRange, hstrict⟩)
      have hmono : a n ≤ b n := by
        exact_mod_cast hτmono (Nat.le_succ n)
      have habEq : a n = b n := le_antisymm hmono (not_lt.mp hnonstrict)
      rw [habEq]
      simp
    rw [← hsumEq]
    exact hsumSecondNonneg
  have hKintegrable : ∀ x y : ℝ,
      IntervalIntegrable Kdensity volume x y := by
    intro x y
    have hkinetic : Continuous
        (fun t ↦ sineTestDeriv L t ^ 2 * inner ℝ w₀ w₀) := by
      unfold sineTestDeriv
      fun_prop
    have hscalar : IntervalIntegrable
        (fun t ↦ sineTestDeriv L t ^ 2 * inner ℝ w₀ w₀ -
          sineTest L t ^ 2 * p.curvatureCoefficient
            (curvature (I := I) (M := M) cov) t) volume x y :=
      (hkinetic.intervalIntegrable x y).sub
        (p.intervalIntegrable_sineTest_square_mul_curvatureCoefficient_curvature
          L x y)
    apply hscalar.congr
    intro t ht
    unfold Kdensity γ
    rw [p.inner_sineTestDerivativeField_self hmetric L t,
      p.inner_sineTestField_curvature
        (curvature (I := I) (M := M) cov) L t]
  have htelescope : (∑ n ∈ Finset.range m,
      ∫ t in a n..b n, Kdensity t) = ∫ t in (0 : ℝ)..L, Kdensity t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun n ↦ (τ n).1) (n := m)
      (fun n hn ↦ hKintegrable (τ n).1 (τ (n + 1)).1)
    simpa [a, b, hτ0, hτm] using h
  have hKnonneg : 0 ≤ ∫ t in (0 : ℝ)..L, Kdensity t := by
    rwa [htelescope] at hsumAllNonneg
  have hkineticIntegrable : IntervalIntegrable
      (fun t ↦ inner ℝ (p.sineTestDerivativeField L t)
        (p.sineTestDerivativeField L t)) volume 0 L := by
    have hkinetic : IntervalIntegrable
        (fun t ↦ sineTestDeriv L t ^ 2 * inner ℝ w₀ w₀) volume 0 L := by
      apply Continuous.intervalIntegrable
      unfold sineTestDeriv
      fun_prop
    apply hkinetic.congr
    intro t ht
    exact (p.inner_sineTestDerivativeField_self hmetric L t).symm
  have hcurvatureIntegrable : IntervalIntegrable
      (fun t ↦ inner ℝ (p.sineTestField L t)
        (curvature (cov := cov) (curve γ t)
          (p.sineTestField L t) (velocity γ t) (velocity γ t))) volume 0 L := by
    have hscalar :=
      p.intervalIntegrable_sineTest_square_mul_curvatureCoefficient_curvature
        L 0 L
    apply hscalar.congr
    intro t ht
    unfold γ
    exact (p.inner_sineTestField_curvature
      (curvature (I := I) (M := M) cov) L t).symm
  have hindexEq : globalIndexForm (curvature (I := I) (M := M) cov) G t₀
      (p.sineTestField L) (p.sineTestDerivativeField L) L =
        ∫ t in (0 : ℝ)..L, Kdensity t := by
    unfold globalIndexForm Kdensity γ
    exact (intervalIntegral.integral_sub
      hkineticIntegrable hcurvatureIntegrable).symm
  rwa [hindexEq]

end IntrinsicGeodesic.GlobalGeodesic

end BonnetMyersEntry
