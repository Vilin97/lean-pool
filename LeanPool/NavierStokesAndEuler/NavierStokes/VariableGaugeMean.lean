/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanChartCompatibility
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalMeanDomain
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalSignedRequest

@[expose] public section

/-!
# The actual similarity-dependent mean gauge

The endpoints are multiplied by the actual `sqrt(q)`.  The cutoff and
normalized density are defined explicitly, and the primitive is the existing
integral operator evaluated with those endpoints on each slow fiber.

The estimates use the moving profile `R / sqrt(q)` and the full ordinary
Fréchet derivatives.  Their constants are uniform in the source family and
the radial transport frequency.  The exact cutoff alias is retained.

The final State theorems derive pressure, pressure-change and temporal
increment classes from the actual input fields on the valid slow domain.
The common torus index and its bounded gap from the native index remain
explicit.  This module does not assert arbitrary-power alias decay.
-/

namespace NavierStokes.VariableGaugeMean

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators

section Scale

theorem positiveRadius_scale {l : ℝ} (hl : l ≠ 0) (a r : ℝ) :
    RadialPullback.positiveRadius (l * a) (l * r) = l * RadialPullback.positiveRadius a r := by
  unfold RadialPullback.positiveRadius
  rw [show l * r - l * a = l * (r - a) by ring, mul_div_mul_left _ _ hl]
  ring

theorem powerChart_scale {l a : ℝ} (hl : 0 < l) (ha : 0 < a) (d r : ℝ) :
    RadialPullback.powerChart d (l * a) (l * r) = l ^ d * RadialPullback.powerChart d a r := by
  unfold RadialPullback.powerChart
  rw [show l * a / 4 = l * (a / 4) by ring, positiveRadius_scale hl.ne',
    Real.mul_rpow hl.le (RadialPullback.positiveRadius_pos (by positivity) r).le]

theorem physicalCutoff_scale {l a b : ℝ} (hl : 0 < l) (ha : 0 < a) (hab : a < b)
    (d r : ℝ) :
    RadialPullback.physicalCutoff d (l * a) (l * b) (l * r) =
      RadialPullback.physicalCutoff d a b r := by
  unfold RadialPullback.physicalCutoff
  rw [powerChart_scale hl ha, Real.mul_rpow hl.le ha.le,
    Real.mul_rpow hl.le (ha.trans hab).le]
  exact MeanChartCompatibility.interiorCutoff_scale (Real.rpow_pos_of_pos hl d).ne' _ _ _

end Scale

section Gauge

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

noncomputable def radialRatio (ell : S → ℝ) (z : PressureStream.Lift S) : ℝ := z.1 / ell z.2.1

noncomputable def cutoff (d a b : ℝ) (ell : S → ℝ) (z : PressureStream.Lift S) : ℝ :=
  RadialPullback.physicalCutoff d a b (radialRatio ell z)

noncomputable def density (a b : ℝ) (hab : a < b) (ell : S → ℝ)
    (z : PressureStream.Lift S) : ℝ :=
  (ell z.2.1)⁻¹ * PressureStream.rho a b hab (radialRatio ell z)

noncomputable def SupportedGauge (a b : ℝ) (ell : S → ℝ) (U : Set S)
    (f : PressureStream.Lift S → ℝ) : Prop :=
  ∀ z, z.2.1 ∈ U → f z ≠ 0 → z.1 ∈ Icc (ell z.2.1 * a) (ell z.2.1 * b)

/-- Genuine integral with the actual endpoints on this slow fiber. -/
noncomputable def compactPrimitive (d a b M : ℝ) (ell : S → ℝ) (v : PressureStream.Plane)
    (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) : ℝ :=
  RadialPullback.physicalCompact d (ell z.2.1 * a) (ell z.2.1 * b) M ((0 : S), v) f z

noncomputable def pressureSource (a b : ℝ) (hab : a < b) (ell : S → ℝ)
    (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) : ℝ :=
  f z - density a b hab ell z * PressureStream.pressureMass f z.2.1

noncomputable def meanPressure (d a b M : ℝ) (hab : a < b) (ell : S → ℝ)
    (v : PressureStream.Plane) (f : PressureStream.Lift S → ℝ) : PressureStream.Lift S → ℝ :=
  compactPrimitive d a b M ell v (pressureSource a b hab ell f)

noncomputable def streamPotential (d a b M : ℝ) (ell : S → ℝ) (v : PressureStream.Plane)
    (f : PressureStream.Lift S → ℝ) : PressureStream.Lift S → ℝ :=
  PressureStream.divideRadius (compactPrimitive d a b M ell v (PressureStream.weightedSource f))

noncomputable def compactAlias (d a b M : ℝ) (ell : S → ℝ) (v : PressureStream.Plane)
    (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) : ℝ :=
  RadialPullback.physicalAlias d (ell z.2.1 * a) (ell z.2.1 * b) M ((0 : S), v) f z

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem cutoff_eq_scaled {a b : ℝ} (ha : 0 < a) (hab : a < b) (d : ℝ)
    (ell : S → ℝ) (z : PressureStream.Lift S) (hl : 0 < ell z.2.1) :
    cutoff d a b ell z =
      RadialPullback.physicalCutoff d (ell z.2.1 * a) (ell z.2.1 * b) z.1 := by
  have h := physicalCutoff_scale hl ha hab d (z.1 / ell z.2.1)
  rw [mul_div_cancel₀ _ hl.ne'] at h
  exact h.symm

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem density_eq_scaled {a b : ℝ} (hab : a < b) (ell : S → ℝ)
    (z : PressureStream.Lift S) (hl : 0 < ell z.2.1) :
    density a b hab ell z = PressureStream.rho (ell z.2.1 * a) (ell z.2.1 * b)
      (mul_lt_mul_of_pos_left hab hl) z.1 := by
  have h := MeanChartCompatibility.rho_scale hl hab (z.1 / ell z.2.1)
  rw [mul_div_cancel₀ _ hl.ne'] at h
  exact h.symm

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem density_integral {a b : ℝ} (hab : a < b) (ell : S → ℝ) (s : S)
    (hl : 0 < ell s) (Y : PressureStream.Plane) :
    (∫ r, density a b hab ell (r, (s, Y))) = 1 := by
  have he : (fun r => density a b hab ell (r, (s, Y))) =
      PressureStream.rho (ell s * a) (ell s * b) (mul_lt_mul_of_pos_left hab hl) :=
    funext fun r => density_eq_scaled hab ell (r, (s, Y)) hl
  rw [he]
  exact PressureStream.rho_integral _ _ _

theorem radialRatio_contDiffOn {ell : S → ℝ} {U : Set S}
    (hl : ContDiffOn ℝ ∞ ell U) (hp : ∀ s ∈ U, 0 < ell s) :
    ContDiffOn ℝ ∞ (radialRatio ell) (PhysicalMeanDomain.slowDomain U) :=
  contDiffOn_fst.div (hl.comp contDiffOn_snd.fst (fun _ hs => hs)) (fun _ hs => (hp _ hs).ne')

theorem cutoff_contDiffOn {a : ℝ} (ha : 0 < a) (d b : ℝ) {ell : S → ℝ} {U : Set S}
    (hl : ContDiffOn ℝ ∞ ell U) (hp : ∀ s ∈ U, 0 < ell s) :
    ContDiffOn ℝ ∞ (cutoff d a b ell) (PhysicalMeanDomain.slowDomain U) :=
  (RadialPullback.physicalCutoff_contDiff ha d b).comp_contDiffOn (radialRatio_contDiffOn hl hp)

theorem density_contDiffOn {a b : ℝ} (hab : a < b) {ell : S → ℝ} {U : Set S}
    (hl : ContDiffOn ℝ ∞ ell U) (hp : ∀ s ∈ U, 0 < ell s) :
    ContDiffOn ℝ ∞ (density a b hab ell) (PhysicalMeanDomain.slowDomain U) :=
  ((hl.comp contDiffOn_snd.fst (fun _ hs => hs)).inv (fun _ hs => (hp _ hs).ne')).mul
    ((PressureStream.rho_contDiff a b hab).comp_contDiffOn (radialRatio_contDiffOn hl hp))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem density_supported {a b : ℝ} (hab : a < b) (ell : S → ℝ) (U : Set S)
    (hl : ∀ s ∈ U, 0 < ell s) : SupportedGauge a b ell U (density a b hab ell) := by
  intro z hz hn
  rw [density_eq_scaled hab ell z (hl _ hz)] at hn
  exact PressureStream.rho_support _ _ _ hn

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem pressureSource_supported {a b : ℝ} (hab : a < b) {ell : S → ℝ} {U : Set S}
    (hl : ∀ s ∈ U, 0 < ell s) {f : PressureStream.Lift S → ℝ}
    (hf : SupportedGauge a b ell U f) : SupportedGauge a b ell U (pressureSource a b hab ell f) :=
      by
  intro z hz hn
  by_contra hnot
  have hf0 : f z = 0 := by by_contra he; exact hnot (hf z hz he)
  have hd0 : density a b hab ell z = 0 := by
    by_contra he
    exact hnot (density_supported hab ell U hl z hz he)
  exact hn (by simp [pressureSource, hf0, hd0])

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem supportedGauge_containing {a b c e l L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hleft : c ≤ l * a) (hright : L * b ≤ e) {ell : S → ℝ} {U : Set S}
    (hl : ∀ s ∈ U, ell s ∈ Icc l L) {f : PressureStream.Lift S → ℝ}
    (hf : SupportedGauge a b ell U f) : PhysicalMeanDomain.SupportedOn c e U f := by
  intro z hz hn
  have hs := hf z hz hn
  exact ⟨hleft.trans ((mul_le_mul_of_nonneg_right (hl _ hz).1 ha).trans hs.1),
    hs.2.trans ((mul_le_mul_of_nonneg_right (hl _ hz).2 hb).trans hright)⟩

end Gauge

section ActualQ

open TorusInverse

/-- Slow variables in this module follow the rank/domain convention `(T,Z)`. -/
noncomputable def qLength (coord : ℝ) (s : Plane) : ℝ :=
  Real.sqrt (SimilarityCoordinates.coordinateQ coord s)

theorem qLength_pos {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {s : Plane} (hs : 0 < s.1) : 0 < qLength coord s :=
  Real.sqrt_pos.mpr (SimilarityCoordinates.coordinateQ_spec hc hc1 hs).1

theorem qLength_contDiffOn {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1) :
    ContDiffOn ℝ ∞ (qLength coord) {s : Plane | 0 < s.1} := by
  intro s hs
  exact ((SimilarityCoordinates.coordinateQ_smooth hc hc1 hs).sqrt
    (SimilarityCoordinates.coordinateQ_spec hc hc1 hs).1.ne').contDiffWithinAt

noncomputable def cutoffModel (d a b : ℝ) (y : MeanRankUpdate.ModelPoint) : ℝ :=
  RadialPullback.physicalCutoff d a b (y.2.1 / Real.sqrt y.1)

noncomputable def densityModel (a b : ℝ) (hab : a < b) (y : MeanRankUpdate.ModelPoint) : ℝ :=
  (Real.sqrt y.1)⁻¹ * PressureStream.rho a b hab (y.2.1 / Real.sqrt y.1)

theorem cutoffModel_contDiffOn {a : ℝ} (ha : 0 < a) (d b : ℝ) :
    ContDiffOn ℝ ∞ (cutoffModel d a b) PhysicalCoordinateBounds.positiveTime := by
  intro y hy
  exact ((RadialPullback.physicalCutoff_contDiff ha d b).contDiffAt.comp y
    (contDiffAt_snd.fst.div (contDiffAt_fst.sqrt (ne_of_gt hy))
      (Real.sqrt_pos.mpr hy).ne')).contDiffWithinAt

theorem densityModel_contDiffOn {a b : ℝ} (hab : a < b) :
    ContDiffOn ℝ ∞ (densityModel a b hab) PhysicalCoordinateBounds.positiveTime := by
  intro y hy
  have hs : ContDiffAt ℝ ∞ (fun y : MeanRankUpdate.ModelPoint => Real.sqrt y.1) y :=
    contDiffAt_fst.sqrt (ne_of_gt hy)
  exact ((hs.inv (Real.sqrt_pos.mpr hy).ne').mul
    ((PressureStream.rho_contDiff a b hab).contDiffAt.comp y
      (contDiffAt_snd.fst.div hs (Real.sqrt_pos.mpr hy).ne'))).contDiffWithinAt

theorem cutoff_q_eq_kernel (coord d a b : ℝ) :
    cutoff d a b (qLength coord) = MeanRankUpdate.chartKernel coord (cutoffModel d a b) := rfl

theorem density_q_eq_kernel (coord a b : ℝ) (hab : a < b) :
    density a b hab (qLength coord) = MeanRankUpdate.chartKernel coord (densityModel a b hab) := rfl

/-- All joint cutoff jets, including actual derivatives of `q`, are derived
from the inverse-coordinate jet theorem on its compact model box. -/
theorem cutoff_q_finiteJets {coord qlo qhi rlo rhi a : ℝ}
    (hc : 0 < coord) (hc1 : coord < 1) (hqlo : 0 < qlo) (ha : 0 < a) (d b : ℝ)
    {U : Set MeanRankUpdate.ChartPoint}
    (hT : ∀ p ∈ U, MeanRankUpdate.chartInput p ∈ PhysicalCoordinateBounds.positiveTime)
    (hq : ∀ p ∈ U, MeanRankUpdate.chartQ coord p ∈ Icc qlo qhi)
    (hR : ∀ p ∈ U, p.1 ∈ Icc rlo rhi) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ JetBounds.FiniteJetBound m (cutoff d a b (qLength coord)) U C := by
  rw [cutoff_q_eq_kernel]
  exact MeanRankUpdate.chartKernel_finiteJetBounds hc hc1 hqlo hT hq hR
    (cutoffModel_contDiffOn ha d b) m

theorem density_q_finiteJets {coord qlo qhi rlo rhi a b : ℝ}
    (hc : 0 < coord) (hc1 : coord < 1) (hqlo : 0 < qlo) (hab : a < b)
    {U : Set MeanRankUpdate.ChartPoint}
    (hT : ∀ p ∈ U, MeanRankUpdate.chartInput p ∈ PhysicalCoordinateBounds.positiveTime)
    (hq : ∀ p ∈ U, MeanRankUpdate.chartQ coord p ∈ Icc qlo qhi)
    (hR : ∀ p ∈ U, p.1 ∈ Icc rlo rhi) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ JetBounds.FiniteJetBound m (density a b hab (qLength coord)) U C := by
  rw [density_q_eq_kernel]
  exact MeanRankUpdate.chartKernel_finiteJetBounds hc hc1 hqlo hT hq hR
    (densityModel_contDiffOn hab) m

end ActualQ

section AnchorReference

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def physicalPast (d c M : ℝ) (v : E) (f : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  TransportPrimitive.pastIntegral M v (RadialPullback.normalizeSource d c f)
    (RadialPullback.liftChart (RadialPullback.powerChart d c) z)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem normalizeSource_anchor_eq {c a b d : ℝ} (hc : 0 < c) (hca : c ≤ a)
    (hab : a < b) (hd : 0 < d) {f : ℝ × E → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialPullback.normalizeSource d c f = RadialPullback.normalizeSource d a f := by
  have ha : 0 < a := hc.trans_le hca
  have hcb : c < b := hca.trans_lt hab
  have hcs : RadialAlias.RadiallySupported c b f := fun z hz =>
    ⟨hca.trans (hs hz).1, (hs hz).2⟩
  funext z
  by_cases hz : 0 < z.1
  · rw [RadialPullback.normalizeSource_eq_formula hc hcb hd hz hcs,
      RadialPullback.normalizeSource_eq_formula ha hab hd hz hs]
  · rw [TransportPrimitive.radial_zero_of_lt (RadialPullback.normalizeSource_supported hc hcb hd
    hcs)
      ((le_of_not_gt hz).trans_lt (Real.rpow_pos_of_pos hc d)),
      TransportPrimitive.radial_zero_of_lt (RadialPullback.normalizeSource_supported ha hab hd hs)
        ((le_of_not_gt hz).trans_lt (Real.rpow_pos_of_pos ha d))]

theorem powerChart_anchor_lt {c a d R : ℝ} (hc : 0 < c) (hca : c ≤ a) (hd : 0 < d)
    (hR : R < a) : RadialPullback.powerChart d c R < a ^ d := by
  apply Real.rpow_lt_rpow (RadialPullback.positiveRadius_pos (by positivity) R).le _ hd
  exact RadialPullback.positiveRadius_lt (by positivity) (by linarith) hR

/-- Changing the auxiliary regularization radius leaves the actual primitive
unchanged; only the compactification cutoff remains. -/
theorem physicalCompact_reference {c a b d M : ℝ} (hc : 0 < c) (hca : c ≤ a)
    (hab : a < b) (hd : 0 < d) (v : E) {f : ℝ × E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    RadialPullback.physicalCompact d a b M v f z = physicalPast d c M v f z -
      RadialPullback.physicalCutoff d a b z.1 * PressureStream.physicalTotal d c M v f z := by
  have ha : 0 < a := hc.trans_le hca
  have he := normalizeSource_anchor_eq hc hca hab hd hs
  by_cases hz : a ≤ z.1
  · unfold RadialPullback.physicalCompact RadialPullback.pullback TransportPrimitive.compactIntegral
      physicalPast PressureStream.physicalTotal RadialPullback.physicalCutoff
        RadialPullback.liftChart
    simp only [Function.comp_apply, smul_eq_mul]
    rw [RadialPullback.powerChart_eq ha (by linarith) d,
      RadialPullback.powerChart_eq hc (by linarith) d, he]
  · have hlt : z.1 < a := lt_of_not_ge hz
    rw [TransportPrimitive.radial_zero_of_lt
      (RadialPullback.physicalCompact_supported ha hab hd hf hs M v) hlt,
      RadialPullback.physicalCutoff_zero_left ha hab hd hlt, zero_mul, sub_zero]
    unfold physicalPast
    rw [he]
    exact (TransportPrimitive.pastIntegral_eq_zero_of_le
      (RadialPullback.normalizeSource_contDiff ha hd hf).continuous
      (RadialPullback.normalizeSource_supported ha hab hd hs) _
      (powerChart_anchor_lt hc hca hd hlt).le).symm

theorem physicalPast_contDiff {c e d M : ℝ} (hc : 0 < c) (hce : c < e) (hd : 0 < d)
    (v : E) {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported c e f) : ContDiff ℝ ∞ (physicalPast d c M v f) :=
  RadialPullback.pullback_contDiff hc d
    (TransportPrimitive.pastIntegral_contDiff (RadialPullback.normalizeSource_contDiff hc hd hf)
      (RadialPullback.normalizeSource_supported hc hce hd hs))

theorem physicalTotal_contDiff {c e d M : ℝ} (hc : 0 < c) (hce : c < e) (hd : 0 < d)
    (v : E) {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported c e f) :
    ContDiff ℝ ∞ (PressureStream.physicalTotal d c M v f) :=
  RadialPullback.pullback_contDiff hc d
    (TransportPrimitive.totalIntegral_contDiff (RadialPullback.normalizeSource_contDiff hc hd hf)
      (RadialPullback.normalizeSource_supported hc hce hd hs))

end AnchorReference

section LocalGauge

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem compactPrimitive_fiberLocal (d a b M : ℝ) (ell : S → ℝ) (v : PressureStream.Plane) :
    PhysicalMeanDomain.FiberLocal (compactPrimitive d a b M ell v) := by
  intro f g s he r Y
  exact PhysicalMeanDomain.physicalCompact_fiberLocal d (ell s * a) (ell s * b) M v f g s he r Y

theorem physicalPast_fiberLocal (d c M : ℝ) (v : PressureStream.Plane) :
    PhysicalMeanDomain.FiberLocal (physicalPast d c M ((0 : S), v)) := by
  intro f g s he r Y
  simp [physicalPast, TransportPrimitive.pastIntegral, TransportPrimitive.shift,
    RadialPullback.normalizeSource, RadialPullback.liftChart, he]

theorem physicalTotal_fiberLocal (d c M : ℝ) (v : PressureStream.Plane) :
    PhysicalMeanDomain.FiberLocal (PressureStream.physicalTotal d c M ((0 : S), v)) := by
  intro f g s he r Y
  simp [PressureStream.physicalTotal, TransportPrimitive.totalIntegral, TransportPrimitive.shift,
    RadialPullback.normalizeSource, RadialPullback.liftChart, he]

theorem freezeSlow_contDiff {U : Set S} (hU : IsOpen U) {s : S} (hs : s ∈ U)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U)) :
    ContDiff ℝ ∞ (PhysicalMeanDomain.freezeSlow s f) := by
  have hm : ContDiff ℝ ∞ (fun z : PressureStream.Lift S => (z.1, (s, z.2.2))) :=
    contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd.snd)
  rw [contDiff_iff_contDiffAt]
  intro z
  exact (hf.contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hs)).comp z hm.contDiffAt

theorem compactPrimitive_reference {c a b d M : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (ell : S → ℝ) (v : PressureStream.Plane)
    {U : Set S} (hU : IsOpen U) (hl : ∀ s ∈ U, 0 < ell s)
    (hleft : ∀ s ∈ U, c ≤ ell s * a) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U)) (hs : SupportedGauge a b ell U f)
    (z : PressureStream.Lift S) (hz : z.2.1 ∈ U) :
    compactPrimitive d a b M ell v f z = physicalPast d c M ((0 : S), v) f z -
      cutoff d a b ell z * PressureStream.physicalTotal d c M ((0 : S), v) f z := by
  let g := PhysicalMeanDomain.freezeSlow z.2.1 f
  have hg : ContDiff ℝ ∞ g := freezeSlow_contDiff hU hz hf
  have hgs : RadialAlias.RadiallySupported (ell z.2.1 * a) (ell z.2.1 * b) g := by
    intro p hp
    exact hs (p.1, (z.2.1, p.2.2)) hz hp
  have he (r : ℝ) (Y : PressureStream.Plane) : g (r, (z.2.1, Y)) = f (r, (z.2.1, Y)) := rfl
  have hp := physicalCompact_reference (M := M) hc (hleft _ hz) (mul_lt_mul_of_pos_left hab (hl _
    hz))
    hd ((0 : S), v) hg hgs z
  rw [PhysicalMeanDomain.physicalCompact_fiberLocal d _ _ M v g f z.2.1 he z.1 z.2.2,
    physicalPast_fiberLocal d c M v g f z.2.1 he z.1 z.2.2,
    physicalTotal_fiberLocal d c M v g f z.2.1 he z.1 z.2.2,
    ← cutoff_eq_scaled ha hab d ell z (hl _ hz)] at hp
  exact hp

variable [FiniteDimensional ℝ S]

theorem physicalPast_contDiffOn {c e d M : ℝ} (hc : 0 < c) (hce : c < e) (hd : 0 < d)
    (v : PressureStream.Plane) {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : PhysicalMeanDomain.SupportedOn c e U f) :
    ContDiffOn ℝ ∞ (physicalPast d c M ((0 : S), v) f) (PhysicalMeanDomain.slowDomain U) :=
  (physicalPast_fiberLocal d c M v).contDiffOn_of_supported
    (fun _ hf hs => physicalPast_contDiff hc hce hd ((0 : S), v) hf hs) hU hf hs

theorem physicalTotal_contDiffOn {c e d M : ℝ} (hc : 0 < c) (hce : c < e) (hd : 0 < d)
    (v : PressureStream.Plane) {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : PhysicalMeanDomain.SupportedOn c e U f) :
    ContDiffOn ℝ ∞ (PressureStream.physicalTotal d c M ((0 : S), v) f)
      (PhysicalMeanDomain.slowDomain U) :=
  (physicalTotal_fiberLocal d c M v).contDiffOn_of_supported
    (fun _ hf hs => physicalTotal_contDiff hc hce hd ((0 : S), v) hf hs) hU hf hs

theorem compactPrimitive_contDiffOn {c e a b d M : ℝ} (hc : 0 < c) (hce : c < e)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : PressureStream.Plane)
    {ell : S → ℝ} {U : Set S} (hU : IsOpen U) (hell : ContDiffOn ℝ ∞ ell U)
    (hl : ∀ s ∈ U, 0 < ell s) (hleft : ∀ s ∈ U, c ≤ ell s * a)
    (hright : ∀ s ∈ U, ell s * b ≤ e) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U)) (hs : SupportedGauge a b ell U f) :
    ContDiffOn ℝ ∞ (compactPrimitive d a b M ell v f) (PhysicalMeanDomain.slowDomain U) := by
  have hsup : PhysicalMeanDomain.SupportedOn c e U f := by
    intro z hz hn
    exact ⟨(hleft _ hz).trans (hs z hz hn).1, (hs z hz hn).2.trans (hright _ hz)⟩
  have hg := (physicalPast_contDiffOn (M := M) hc hce hd v hU hf hsup).sub
    ((cutoff_contDiffOn ha d b hell hl).mul (physicalTotal_contDiffOn (M := M) hc hce hd v hU hf
      hsup))
  apply hg.congr
  intro z hz
  exact compactPrimitive_reference hc ha hab hd ell v hU hl hleft hf hs z hz

end LocalGauge

section IntegralJets

open WeightedRadialPrimitive

theorem logWeight_zero_zero {a b R : ℝ} (ha : 0 < a) (hR : R ∈ Ioo a b) :
    logWeight 0 0 a b 0 R = 1 := by
  have hx := logPosition_mem ha hR
  simp [logWeight, weight, zeta, FlatCutoff.edge_of_pos _ hx.1,
    FlatCutoff.edge_of_pos _ (sub_pos.mpr hx.2)]

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem normalizeSource_unweighted_fiber {c e d : ℝ} (hc : 0 < c) (hce : c < e)
    (hd : 0 < d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : PressureStream.Lift S → ℝ), ContDiff ℝ ∞ f →
      RadialAlias.RadiallySupported c e f → ∀ A : ℝ, 0 ≤ A → ∀ s : S,
      (∀ j ≤ m, ∀ R ∈ Ioo c e, ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ j f (R, (s, Y))‖ ≤ A) →
      ∀ z : PressureStream.Lift S, z.2.1 = s → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (RadialPullback.normalizeSource d c f) z‖ ≤ K * A := by
  obtain ⟨K, hK, hb⟩ := PhysicalMeanDomain.normalizeSource_finiteJets_fiber
    (S := S) (V := ℝ) hc hce hd 0 0 0 m
  refine ⟨K, hK, ?_⟩
  intro f hf hs A hA s hin z hz j hj
  by_cases hR : z.1 ∈ Ioo (c ^ d) (e ^ d)
  · have h := hb f hf A hA s (fun j hj R hR Y => by
        simpa only [logWeight_zero_zero hc hR, mul_one] using hin j hj R hR Y) z hR hz j hj
    simpa only [mul_zero, logWeight_zero_zero (Real.rpow_pos_of_pos hc d) hR, mul_one] using h
  · rw [MeanMomentBounds.supported_zero_outside_open
      (TransportPrimitive.iteratedFDeriv_contDiff (RadialPullback.normalizeSource_contDiff hc hd
        hf) j).continuous
      (TransportPrimitive.iteratedFDeriv_supported (RadialPullback.normalizeSource_supported hc hce
        hd hs) j) hR,
      norm_zero]
    exact mul_nonneg hK hA

theorem transportIntegrals_jet_bound_fiber {c e M A : ℝ} (hce : c ≤ e)
    (v : PressureStream.Plane) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported c e f) (s : S) (j : ℕ)
    (hin : ∀ R ∈ Icc c e, ∀ Y : PressureStream.Plane,
      ‖iteratedFDeriv ℝ j f (R, (s, Y))‖ ≤ A)
    (z : PressureStream.Lift S) (hz : z.2.1 = s) :
    ‖iteratedFDeriv ℝ j (TransportPrimitive.pastIntegral M ((0 : S), v) f) z‖ ≤ A * (e - c) ∧
      ‖iteratedFDeriv ℝ j (TransportPrimitive.totalIntegral M ((0 : S), v) f) z‖ ≤ A * (e - c) := by
  let g := iteratedFDeriv ℝ j f
  have hg : Continuous g := (TransportPrimitive.iteratedFDeriv_contDiff hf j).continuous
  have hgs := TransportPrimitive.iteratedFDeriv_supported hs j
  have hgc := PhysicalMeanDomain.freezeSlow_continuous hg z.2.1
  have hss := PhysicalMeanDomain.freezeSlow_supported hgs z.2.1
  have hb : ∀ R ∈ Icc c e, ∀ Y : S × PressureStream.Plane,
      ‖PhysicalMeanDomain.freezeSlow z.2.1 g (R, Y)‖ ≤ A := by
    intro R hR Y
    change ‖iteratedFDeriv ℝ j f (R, (z.2.1, Y.2))‖ ≤ A
    rw [hz]
    exact hin R hR Y.2
  constructor
  · rw [TransportPrimitive.iteratedFDeriv_pastIntegral hf hs,
      ← PhysicalMeanDomain.pastIntegral_freeze M v g z]
    exact TransportPrimitive.pastIntegral_norm_le hce hgc hss hb z
  · rw [TransportPrimitive.iteratedFDeriv_totalIntegral hf hs,
      ← PhysicalMeanDomain.totalIntegral_freeze M v g z]
    exact TransportPrimitive.totalIntegral_norm_le hce hgc hss hb z

/-- The integration and physical radial pullback cost is uniform in the
transport frequency. Every input and output derivative is an actual joint jet. -/
theorem physicalIntegrals_finiteJets_fiber {c e d : ℝ} (hc : 0 < c) (hce : c < e)
    (hd : 0 < d) (rlo rhi : ℝ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : PressureStream.Plane) (f : PressureStream.Lift S → ℝ),
      ContDiff ℝ ∞ f → RadialAlias.RadiallySupported c e f → ∀ A : ℝ, 0 ≤ A → ∀ s : S,
      (∀ j ≤ m, ∀ R ∈ Ioo c e, ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ j f (R, (s, Y))‖ ≤ A) →
      ∀ z : PressureStream.Lift S, z.1 ∈ Icc rlo rhi → z.2.1 = s → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (physicalPast d c M ((0 : S), v) f) z‖ ≤ K * A ∧
        ‖iteratedFDeriv ℝ j (PressureStream.physicalTotal d c M ((0 : S), v) f) z‖ ≤ K * A := by
  obtain ⟨KN, hKN, hbN⟩ := normalizeSource_unweighted_fiber (S := S) hc hce hd m
  obtain ⟨KP, hKP, hbP⟩ := RadialPullback.radial_comp_finiteJets_uniform
    (E := S × PressureStream.Plane) (V := ℝ) rlo rhi (RadialPullback.powerChart_contDiff hc d) m
  have hlen : 0 ≤ e ^ d - c ^ d := sub_nonneg.mpr (Real.rpow_le_rpow hc.le hce.le hd.le)
  refine ⟨KP * KN * (e ^ d - c ^ d), mul_nonneg (mul_nonneg hKP hKN) hlen, ?_⟩
  intro M v f hf hs A hA s hin z hR hz j hj
  have hN := RadialPullback.normalizeSource_contDiff hc hd hf
  have hsN := RadialPullback.normalizeSource_supported hc hce hd hs
  have hB : 0 ≤ KN * A * (e ^ d - c ^ d) := mul_nonneg (mul_nonneg hKN hA) hlen
  have hI (w : PressureStream.Lift S) (hw : w.2.1 = s) (j : ℕ) (hj : j ≤ m) :=
    transportIntegrals_jet_bound_fiber (M := M) (Real.rpow_le_rpow hc.le hce.le hd.le)
      v hN hsN s j (fun R _ Y => hbN f hf hs A hA s hin (R, (s, Y)) rfl j hj) w hw
  have hp := hbP (TransportPrimitive.pastIntegral M ((0 : S), v) (RadialPullback.normalizeSource d
    c f))
    (TransportPrimitive.pastIntegral_contDiff hN hsN) z hR _ hB
    (fun j hj => (hI (RadialPullback.liftChart (RadialPullback.powerChart d c) z) hz j hj).1) j hj
  have ht := hbP (TransportPrimitive.totalIntegral M ((0 : S), v) (RadialPullback.normalizeSource d
    c f))
    (TransportPrimitive.totalIntegral_contDiff hN hsN) z hR _ hB
    (fun j hj => (hI (RadialPullback.liftChart (RadialPullback.powerChart d c) z) hz j hj).2) j hj
  constructor
  · convert! hp using 1
    ring
  · convert! ht using 1
    ring

end IntegralJets

section StateConstructors

structure GaugeData (S : Type) where
  radial : CorrectionState.ReconstructionData
  length : ℕ → S → ℝ

/-- The actual similarity gauge in every normalized chart. -/
noncomputable def similarityGauge (h d a b M : ℝ) (hab : a < b) (index : ℕ → ℕ) :
    GaugeData PressureStream.Plane where
  radial :=
    { exponent := d, inner := a, outer := b, inner_lt_outer := hab,
      frequency := fun n => MeanChartCompatibility.radialFrequency h n (index n) d M,
      radialDirection := TorusInverse.vector .radial }
  length := fun _ => qLength (2 * h)

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

noncomputable def reconstructState (g : GaugeData S)
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) : CorrectionState.State
      (PressureStream.Lift S) :=
  { u with
    pressure := fun n =>
      meanPressure g.radial.exponent g.radial.inner g.radial.outer (g.radial.frequency n)
        g.radial.inner_lt_outer (g.length n) g.radial.radialDirection (u.gr c n) }

noncomputable def pressureAliasState (g : GaugeData S)
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) : CorrectionState.Oscillation
      (PressureStream.Lift S) :=
  fun n p => ![-compactAlias g.radial.exponent g.radial.inner g.radial.outer
    (g.radial.frequency n) (g.length n) g.radial.radialDirection
    (pressureSource g.radial.inner g.radial.outer g.radial.inner_lt_outer (g.length n) (u.gr c n))
      p.1, 0, 0]

noncomputable def temporalPotential (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) (n : ℕ) : PressureStream.Lift S → ℝ :=
  streamPotential g.radial.exponent g.radial.inner g.radial.outer (g.radial.frequency n)
    (g.length n) g.radial.radialDirection (MeanChartCompatibility.temporalAtIndex h n (index n)
      (u.axialResidual c n))

noncomputable def temporalIncrementState (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) : MeanIncrementBounds.Triple
      (PressureStream.Lift S) where
  radial := fun n => PressureStream.streamBeta (c.operators.epsilon n • axial) (temporalPotential g
    h index c u n)
  angular := fun n => MeanChartCompatibility.temporalAtIndex h n (index n) (u.thetaResidual c n)
  axial := fun n => PressureStream.streamGamma
    (PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n)) ((0 : S),
      g.radial.radialDirection)
    (temporalPotential g h index c u n)

noncomputable def temporalAxialDifference (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) (n : ℕ) (z : PressureStream.Lift S) : ℝ :=
  MeanChartCompatibility.temporalAtIndex h n (index n) (u.axialResidual c n) z -
    PressureStream.streamGamma (PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency
      n))
      ((0 : S), g.radial.radialDirection) (temporalPotential g h index c u n) z

noncomputable def temporalAliasState (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) : CorrectionState.Oscillation
      (PressureStream.Lift S) :=
  fun n p => ![0, 0, -c.operators.fastTime (temporalAxialDifference g h index c u) n p.1]

noncomputable def temporalStageState (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) : CorrectionState.State
      (PressureStream.Lift S) :=
  reconstructState g c (u.addIncrement (temporalIncrementState g h index axial c u) 0 0 0
    ⟨0, 0, temporalAliasState g h index c u⟩)

noncomputable def rankPotential (g : GaugeData S) (r : CorrectionState.RankData S)
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) (n : ℕ) : PressureStream.Lift S → ℝ :=
  streamPotential g.radial.exponent g.radial.inner g.radial.outer (g.radial.frequency n)
    (g.length n) g.radial.radialDirection (MeanRankUpdate.slowLift
      (CorrectionState.rankDesiredAxial r c u n))

noncomputable def rankIncrementState (g : GaugeData S) (r : CorrectionState.RankData S)
    (axial : S × PressureStream.Plane) (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) : MeanIncrementBounds.Triple
      (PressureStream.Lift S) where
  radial := fun n => PressureStream.streamBeta (c.operators.epsilon n • axial) (rankPotential g r c
    u n)
  angular := fun n => MeanRankUpdate.slowLift (CorrectionState.rankAngular r c u n)
  axial := fun n => PressureStream.streamGamma
    (PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n)) ((0 : S),
      g.radial.radialDirection)
    (rankPotential g r c u n)

noncomputable def rankStageState (g : GaugeData S) (r : CorrectionState.RankData S)
    (axial : S × PressureStream.Plane) (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) : CorrectionState.State
      (PressureStream.Lift S) :=
  reconstructState g c (u.addIncrement (rankIncrementState g r axial c u) 0 0 0
    CorrectionState.ExcludedErrors.zero)

end StateConstructors

section GaugeNaturality

open MeanChartCompatibility

variable {S T : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem pressureSource_eq_fixed {a b : ℝ} (hab : a < b) (ell : S → ℝ)
    (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) (hl : 0 < ell z.2.1) :
    pressureSource a b hab ell f z = PressureStream.pressureSource (ell z.2.1 * a) (ell z.2.1 * b)
      (mul_lt_mul_of_pos_left hab hl) f z := by
  unfold pressureSource PressureStream.pressureSource
  rw [density_eq_scaled hab ell z hl]

theorem meanPressure_eq_fixed {a b : ℝ} (hab : a < b) (d M : ℝ) (ell : S → ℝ)
    (v : PressureStream.Plane) (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S)
    (hl : 0 < ell z.2.1) :
    meanPressure d a b M hab ell v f z = PressureStream.meanPressure d
      (ell z.2.1 * a) (ell z.2.1 * b) M (mul_lt_mul_of_pos_left hab hl) v f z := by
  unfold meanPressure compactPrimitive PressureStream.meanPressure
  exact PhysicalMeanDomain.physicalCompact_fiberLocal d (ell z.2.1 * a) (ell z.2.1 * b) M v
    _ _ z.2.1 (fun r Y => pressureSource_eq_fixed hab ell f (r, (z.2.1, Y)) hl) z.1 z.2.2

theorem streamPotential_eq_fixed (d a b M : ℝ) (ell : S → ℝ)
    (v : PressureStream.Plane) (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) :
    streamPotential d a b M ell v f z = PressureStream.streamPotential d
      (ell z.2.1 * a) (ell z.2.1 * b) M ((0 : S), v) f z := by
  simp only [streamPotential, PressureStream.streamPotential, PressureStream.divideRadius,
    compactPrimitive]

theorem meanPressure_congr_endpoints {a b a' b' : ℝ} {hab : a < b} {hab' : a' < b'}
    (ha : a = a') (hb : b = b') (d M : ℝ) (v : PressureStream.Plane)
    (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) :
    PressureStream.meanPressure d a b M hab v f z =
      PressureStream.meanPressure d a' b' M hab' v f z := by
  subst a'
  subst b'
  rfl

/-- Naturality on a single genuine slow fiber.  The source is only required
to be smooth and periodic on its open physical slow domain. -/
theorem meanPressure_coverPull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (P : S →L[ℝ] T) (k : ℕ) (M N u : ℝ)
    (v w : PressureStream.Plane) (hshift : M • TemporalMeanUpdate.coverMap k v = (N * l ^ d) • w)
    (ell : S → ℝ) (ell' : T → ℝ) {U : Set T} (hU : IsOpen U)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U f) (hs : SupportedGauge a b ell' U f)
    (z : PressureStream.Lift S) (hz : P z.2.1 ∈ U) (hzl : 0 < ell z.2.1)
    (hell : ell' (P z.2.1) = l * ell z.2.1) :
    meanPressure d a b M hab ell v (coverPull l P k u f) z =
      (u / l) * meanPressure d a b N hab ell' w f
        (chartLinear l (P.prodMap (TemporalMeanUpdate.coverMap k)) z) := by
  let g := PhysicalMeanDomain.freezeSlow (P z.2.1) f
  have hg : ContDiff ℝ ∞ g := freezeSlow_contDiff hU hz hf
  have hgp : PressureStream.TorusPeriodicLift g := by
    intro r s Y j
    exact hp r (P z.2.1) hz Y j
  have hgs : RadialAlias.RadiallySupported (l * (ell z.2.1 * a)) (l * (ell z.2.1 * b)) g := by
    intro p hne
    have h := hs (p.1, (P z.2.1, p.2.2)) hz hne
    rw [hell] at h
    simp only [mul_assoc] at h
    exact h
  have he (r : ℝ) (Y : PressureStream.Plane) : g (r, (P z.2.1, Y)) = f (r, (P z.2.1, Y)) := rfl
  have hscaleA : l * (ell z.2.1 * a) = ell' (P z.2.1) * a := by rw [hell]; ring
  have hscaleB : l * (ell z.2.1 * b) = ell' (P z.2.1) * b := by rw [hell]; ring
  have ht := MeanChartCompatibility.meanPressure_coverPull hl (mul_pos hzl ha)
    (mul_lt_mul_of_pos_left hab hzl) hd P k M N u v w hshift hg hgp hgs z
  have hleft : PressureStream.meanPressure d (ell z.2.1 * a) (ell z.2.1 * b) M
      (mul_lt_mul_of_pos_left hab hzl) v (coverPull l P k u g) z =
    PressureStream.meanPressure d (ell z.2.1 * a) (ell z.2.1 * b) M
      (mul_lt_mul_of_pos_left hab hzl) v (coverPull l P k u f) z :=
    PhysicalMeanDomain.meanPressure_fiberLocal d _ _ M _ v
      (coverPull l P k u g) (coverPull l P k u f) z.2.1 (fun _ _ => rfl) z.1 z.2.2
  have hzl' : 0 < ell' (P z.2.1) := by rw [hell]; exact mul_pos hl hzl
  rw [meanPressure_eq_fixed hab d M ell v _ z hzl,
    meanPressure_eq_fixed hab d N ell' w f _ hzl']
  change _ = (u / l) * PressureStream.meanPressure d (l * (ell z.2.1 * a))
    (l * (ell z.2.1 * b)) N _ w g (chartLinear l (P.prodMap (TemporalMeanUpdate.coverMap k)) z) at
      ht
  rw [hleft] at ht
  rw [meanPressure_congr_endpoints (hab' := mul_lt_mul_of_pos_left hab hzl') hscaleA hscaleB] at ht
  exact ht.trans (congrArg (fun t : ℝ => (u / l) * t)
    (PhysicalMeanDomain.meanPressure_fiberLocal d (ell' (P z.2.1) * a)
      (ell' (P z.2.1) * b) N (mul_lt_mul_of_pos_left hab hzl') w g f (P z.2.1) he
      (l * z.1) (TemporalMeanUpdate.coverMap k z.2.2)))

theorem streamPotential_coverPull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (P : S →L[ℝ] T) (k : ℕ) (M N u : ℝ)
    (v w : PressureStream.Plane) (hshift : M • TemporalMeanUpdate.coverMap k v = (N * l ^ d) • w)
    (ell : S → ℝ) (ell' : T → ℝ) {U : Set T} (hU : IsOpen U)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : SupportedGauge a b ell' U f)
    (z : PressureStream.Lift S) (hz : P z.2.1 ∈ U) (hzl : 0 < ell z.2.1)
    (hell : ell' (P z.2.1) = l * ell z.2.1) :
    streamPotential d a b M ell v (coverPull l P k u f) z =
      (u / l) * streamPotential d a b N ell' w f
        (chartLinear l (P.prodMap (TemporalMeanUpdate.coverMap k)) z) := by
  let C := P.prodMap (TemporalMeanUpdate.coverMap k)
  let g := PhysicalMeanDomain.freezeSlow (P z.2.1) f
  have hg : ContDiff ℝ ∞ g := freezeSlow_contDiff hU hz hf
  have hgs : RadialAlias.RadiallySupported (l * (ell z.2.1 * a)) (l * (ell z.2.1 * b)) g := by
    intro p hne
    have h := hs (p.1, (P z.2.1, p.2.2)) hz hne
    rw [hell] at h
    simp only [mul_assoc] at h
    exact h
  have he (r : ℝ) (Y : PressureStream.Plane) : g (r, (P z.2.1, Y)) = f (r, (P z.2.1, Y)) := rfl
  have hscaleA : l * (ell z.2.1 * a) = ell' (P z.2.1) * a := by rw [hell]; ring
  have hscaleB : l * (ell z.2.1 * b) = ell' (P z.2.1) * b := by rw [hell]; ring
  have hvector : M • C ((0 : S), v) = (N * l ^ d) • ((0 : T), w) := by
    apply Prod.ext
    · simp [C]
    · exact hshift
  have ht := congrFun (MeanChartCompatibility.streamPotential_pull hl (mul_pos hzl ha)
    (mul_lt_mul_of_pos_left hab hzl) hd C M N u ((0 : S), v) ((0 : T), w) hvector hg hgs) z
  rw [hscaleA, hscaleB] at ht
  have hleft : PressureStream.streamPotential d (ell z.2.1 * a) (ell z.2.1 * b) M
      ((0 : S), v) (coverPull l P k u g) z =
    PressureStream.streamPotential d (ell z.2.1 * a) (ell z.2.1 * b) M
      ((0 : S), v) (coverPull l P k u f) z :=
    PhysicalMeanDomain.streamPotential_fiberLocal d _ _ M v
      (coverPull l P k u g) (coverPull l P k u f) z.2.1 (fun _ _ => rfl) z.1 z.2.2
  rw [streamPotential_eq_fixed, streamPotential_eq_fixed]
  change PressureStream.streamPotential d (ell z.2.1 * a) (ell z.2.1 * b) M
    ((0 : S), v) (coverPull l P k u g) z = (u / l) *
      PressureStream.streamPotential d (ell' (P z.2.1) * a) (ell' (P z.2.1) * b) N
        ((0 : T), w) g (chartLinear l C z) at ht
  rw [hleft] at ht
  exact ht.trans (congrArg (fun t : ℝ => (u / l) * t)
    (PhysicalMeanDomain.streamPotential_fiberLocal d (ell' (P z.2.1) * a)
      (ell' (P z.2.1) * b) N w g f (P z.2.1) he
      (l * z.1) (TemporalMeanUpdate.coverMap k z.2.2)))

end GaugeNaturality

section ProductJets

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem product_jet_bound {U : Set D} (hU : IsOpen U) {f g : D → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {z : D} (hz : z ∈ U)
    {m j : ℕ} (hj : j ≤ m) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfa : ∀ i ≤ m, ‖iteratedFDeriv ℝ i f z‖ ≤ A)
    (hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g z‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun x => f x * g x) z‖ ≤ (2 : ℝ) ^ m * A * B := by
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f z‖ * ‖iteratedFDeriv ℝ (j - i) g z‖ :=
      JetBounds.norm_iteratedFDeriv_mul_le_on hU hf hg hz
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfa i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj))
          (Nat.cast_nonneg _))
        (hgb (j - i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ j * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ (2 : ℝ) ^ m * A * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hB

theorem sub_jet_norm_le {U : Set D} (hU : IsOpen U) {f g : D → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {z : D} (hz : z ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun x => f x - g x) z‖ ≤
      ‖iteratedFDeriv ℝ j f z‖ + ‖iteratedFDeriv ℝ j g z‖ := by
  have hfj : ContDiffAt ℝ j f z := (hf.contDiffAt (hU.mem_nhds hz)).of_le
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  have hgj : ContDiffAt ℝ j g z := (hg.contDiffAt (hU.mem_nhds hz)).of_le
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  have he : (fun x => f x - g x) = f + -g := by funext x; exact sub_eq_add_neg _ _
  rw [he, iteratedFDeriv_add_apply (i := j) (x := z) (f := f) (g := -g) hfj hgj.neg,
    iteratedFDeriv_neg_apply]
  simpa only [norm_neg] using norm_add_le (iteratedFDeriv ℝ j f z) (-iteratedFDeriv ℝ j g z)

end ProductJets

section LocalQuantitative

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

theorem physicalIntegrals_finiteJets_local {c e d : ℝ} (hc : 0 < c) (hce : c < e)
    (hd : 0 < d) (rlo rhi : ℝ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : Set S), IsOpen U → ∀ (M : ℝ) (v : PressureStream.Plane)
      (f : PressureStream.Lift S → ℝ), ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U) →
      PhysicalMeanDomain.SupportedOn c e U f → ∀ A : ℝ, 0 ≤ A →
      ∀ z : PressureStream.Lift S, z.2.1 ∈ U → z.1 ∈ Icc rlo rhi →
      (∀ j ≤ m, ∀ R ∈ Ioo c e, ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ j f (R, (z.2.1, Y))‖ ≤ A) → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (physicalPast d c M ((0 : S), v) f) z‖ ≤ K * A ∧
        ‖iteratedFDeriv ℝ j (PressureStream.physicalTotal d c M ((0 : S), v) f) z‖ ≤ K * A := by
  obtain ⟨K, hK, hb⟩ := physicalIntegrals_finiteJets_fiber (S := S) hc hce hd rlo rhi m
  refine ⟨K, hK, ?_⟩
  intro U hU M v f hf hs A hA z hz hR hin j hj
  obtain ⟨χ, _, hχs, hχf, he⟩ := PhysicalMeanDomain.exists_fiber_localization hU hz hf
  have hχsup := PhysicalMeanDomain.localize_supported hχs hs
  have hbound := hb M v (PhysicalMeanDomain.localize χ f) hχf hχsup A hA z.2.1
    (fun k hk R hR Y => by rw [he.jet_eq k R Y]; exact hin k hk R hR Y) z hR rfl j hj
  rw [((physicalPast_fiberLocal d c M v).germ he).jet_eq j z.1 z.2.2,
    ((physicalTotal_fiberLocal d c M v).germ he).jet_eq j z.1 z.2.2] at hbound
  exact hbound

omit [FiniteDimensional ℝ S] in
theorem compactPrimitive_supportedGauge {a b d M : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (ell : S → ℝ) (v : PressureStream.Plane) {U : Set S} (hU : IsOpen U)
    (hl : ∀ s ∈ U, 0 < ell s) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U)) (hs : SupportedGauge a b ell U f) :
    SupportedGauge a b ell U (compactPrimitive d a b M ell v f) := by
  intro z hz hn
  let g := PhysicalMeanDomain.freezeSlow z.2.1 f
  have hg : ContDiff ℝ ∞ g := freezeSlow_contDiff hU hz hf
  have hgs : RadialAlias.RadiallySupported (ell z.2.1 * a) (ell z.2.1 * b) g :=
    fun p hp => hs (p.1, (z.2.1, p.2.2)) hz hp
  have he := PhysicalMeanDomain.physicalCompact_fiberLocal d (ell z.2.1 * a) (ell z.2.1 * b)
    M v g f z.2.1 (fun _ _ => rfl) z.1 z.2.2
  apply RadialPullback.physicalCompact_supported (mul_pos (hl _ hz) ha)
    (mul_lt_mul_of_pos_left hab (hl _ hz)) hd hg hgs M ((0 : S), v)
  change RadialPullback.physicalCompact d (ell z.2.1 * a) (ell z.2.1 * b) M
    ((0 : S), v) g z ≠ 0
  change RadialPullback.physicalCompact d (ell z.2.1 * a) (ell z.2.1 * b) M
    ((0 : S), v) f z ≠ 0 at hn
  exact fun hzero => hn (he.symm.trans hzero)

/-- Full Leibniz control with an explicit cutoff-jet bound.  The integration
constant is chosen before the domain, scale function, frequency and source. -/
theorem compactPrimitive_finiteJets_local {c e d a b : ℝ} (hc : 0 < c) (hce : c < e)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (rlo rhi : ℝ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : Set S), IsOpen U → ∀ (ell : S → ℝ), ContDiffOn ℝ ∞ ell U →
      (∀ s ∈ U, 0 < ell s) → (∀ s ∈ U, c ≤ ell s * a) → (∀ s ∈ U, ell s * b ≤ e) →
      ∀ (M : ℝ) (v : PressureStream.Plane) (f : PressureStream.Lift S → ℝ),
      ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U) → SupportedGauge a b ell U f →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → ∀ z : PressureStream.Lift S,
      z.2.1 ∈ U → z.1 ∈ Icc rlo rhi →
      (∀ j ≤ m, ∀ R ∈ Ioo c e, ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ j f (R, (z.2.1, Y))‖ ≤ A) →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (cutoff d a b ell) z‖ ≤ B) → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (compactPrimitive d a b M ell v f) z‖ ≤ K * (1 + (2 : ℝ) ^ m * B) * A
          := by
  obtain ⟨K, hK, hb⟩ := physicalIntegrals_finiteJets_local (S := S) hc hce hd rlo rhi m
  refine ⟨K, hK, ?_⟩
  intro U hU ell hell hl hleft hright M v f hf hs A B hA hB z hz hR hin hcut j hj
  have hsup : PhysicalMeanDomain.SupportedOn c e U f := fun p hp hn =>
    ⟨(hleft _ hp).trans (hs p hp hn).1, (hs p hp hn).2.trans (hright _ hp)⟩
  have hI := physicalPast_contDiffOn (M := M) hc hce hd v hU hf hsup
  have hJ := physicalTotal_contDiffOn (M := M) hc hce hd v hU hf hsup
  have hC := cutoff_contDiffOn ha d b hell hl
  have he : compactPrimitive d a b M ell v f =ᶠ[𝓝 z]
      (fun p => physicalPast d c M ((0 : S), v) f p -
        cutoff d a b ell p * PressureStream.physicalTotal d c M ((0 : S), v) f p) := by
    filter_upwards [(PhysicalMeanDomain.slowDomain_open hU).mem_nhds hz] with p hp
    exact compactPrimitive_reference hc ha hab hd ell v hU hl hleft hf hs p hp
  rw [MeanRankUpdate.iteratedFDeriv_congr_germ he j]
  have hprod := product_jet_bound (PhysicalMeanDomain.slowDomain_open hU) hC hJ hz hj hB
    (mul_nonneg hK hA) hcut (fun i hi => (hb U hU M v f hf hsup A hA z hz hR hin i hi).2)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (physicalPast d c M ((0 : S), v) f) z‖ +
        ‖iteratedFDeriv ℝ j (fun p => cutoff d a b ell p * PressureStream.physicalTotal d c M ((0 :
          S), v) f p) z‖ :=
      sub_jet_norm_le (PhysicalMeanDomain.slowDomain_open hU) hI (hC.mul hJ) hz j
    _ ≤ K * A + (2 : ℝ) ^ m * B * (K * A) :=
      add_le_add (hb U hU M v f hf hsup A hA z hz hR hin j hj).1 hprod
    _ = K * (1 + (2 : ℝ) ^ m * B) * A := by ring

end LocalQuantitative

section ActualChart

open TorusInverse MeanChartCompatibility

/-- The same physical change, in the rank/domain order `(T,Z)`. -/
noncomputable def slowToChartTZ (h : ℝ) (n : ℕ) : Plane →L[ℝ] Plane :=
  (ChartScales.Q n ^ (-1 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ChartScales.Q n ^ (-CoordinateAlgebra.D h) • ContinuousLinearMap.snd ℝ ℝ ℝ)

noncomputable def swapSlow : PressureStream.Lift Plane →L[ℝ] PressureStream.Lift Plane :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap
    ((ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap.prodMap
      (ContinuousLinearMap.id ℝ Plane))

noncomputable def physicalToChartTZ (h : ℝ) (n i : ℕ) :
    PressureStream.Lift Plane →L[ℝ] PressureStream.Lift Plane :=
  chartLinear (chartScale n) ((slowToChartTZ h n).prodMap (TemporalMeanUpdate.coverMap i))

theorem physicalToChartTZ_swap (h : ℝ) (n i : ℕ) (z : PressureStream.Lift Plane) :
    physicalToChartTZ h n i (swapSlow z) = swapSlow (physicalToChart h n i z) := rfl

noncomputable def fieldOnPhysicalTZ (h : ℝ) (n i : ℕ) (a : ℝ)
    (f : PressureStream.Lift Plane → ℝ) : PressureStream.Lift Plane → ℝ :=
  coverPull (chartScale n) (slowToChartTZ h n) i (ChartScales.Q n ^ (-a)) f

theorem qLength_chart {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n : ℕ) {s : Plane} (hs : 0 < s.1) :
    qLength (2 * h) (slowToChartTZ h n s) = chartScale n * qLength (2 * h) s := by
  have he := SimilarityHomogeneity.coordinateQ_scale_h (z := s.2) hh hh1
    (inv_pos.mpr (ChartScales.Q_pos n)) hs
  have hp : ChartScales.Q n ^ (-CoordinateAlgebra.D h) =
      (ChartScales.Q n)⁻¹ ^ CoordinateAlgebra.D h := by
    rw [Real.rpow_neg (ChartScales.Q_pos n).le, Real.inv_rpow (ChartScales.Q_pos n).le]
  change Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h)
    (ChartScales.Q n ^ (-1 : ℝ) * s.1, ChartScales.Q n ^ (-CoordinateAlgebra.D h) * s.2)) = _
  rw [Real.rpow_neg_one, hp, he, Real.sqrt_mul (inv_pos.mpr (ChartScales.Q_pos n)).le]
  have hroot : Real.sqrt (ChartScales.Q n)⁻¹ = chartScale n := by
    rw [Real.sqrt_eq_rpow, Real.inv_rpow (ChartScales.Q_pos n).le, chartScale,
      Real.rpow_neg (ChartScales.Q_pos n).le]
  rw [hroot]
  rfl

theorem cutoff_chart {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n i : ℕ) (d a b : ℝ) {z : PressureStream.Lift Plane} (hz : 0 < z.2.1.1) :
    cutoff d a b (qLength (2 * h)) (physicalToChartTZ h n i z) =
      cutoff d a b (qLength (2 * h)) z := by
  change RadialPullback.physicalCutoff d a b
    (chartScale n * z.1 / qLength (2 * h) (slowToChartTZ h n z.2.1)) = _
  rw [qLength_chart hh hh1 n hz, mul_div_mul_left _ _ (chartScale_pos n).ne']
  rfl

theorem density_chart {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n i : ℕ) {a b : ℝ} (hab : a < b) {z : PressureStream.Lift Plane} (hz : 0 < z.2.1.1) :
    density a b hab (qLength (2 * h)) (physicalToChartTZ h n i z) =
      (chartScale n)⁻¹ * density a b hab (qLength (2 * h)) z := by
  change (qLength (2 * h) (slowToChartTZ h n z.2.1))⁻¹ * PressureStream.rho a b hab
    (chartScale n * z.1 / qLength (2 * h) (slowToChartTZ h n z.2.1)) = _
  rw [qLength_chart hh hh1 n hz, mul_div_mul_left _ _ (chartScale_pos n).ne', mul_inv_rev]
  unfold density radialRatio
  ring

/-- The actual variable-gauge chart pressures are the same physical
operator, with the exact pressure and momentum units. -/
theorem physicalMeanPressure_naturality {h d a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (n i : ℕ) (M : ℝ)
    {U : Set Plane} (hU : IsOpen U) {f : PressureStream.Lift Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U f) (hs : SupportedGauge a b (qLength (2 * h)) U f)
    (z : PressureStream.Lift Plane) (hz : 0 < z.2.1.1) (hzU : slowToChartTZ h n z.2.1 ∈ U) :
    meanPressure d a b M hab (qLength (2 * h)) (vector .radial)
      (fieldOnPhysicalTZ h n i (2 * CoordinateAlgebra.A h + 1 / 2) f) z =
    fieldOnPhysicalTZ h n i (2 * CoordinateAlgebra.A h)
      (meanPressure d a b (radialFrequency h n i d M) hab (qLength (2 * h)) (vector .radial) f) z
        := by
  have hc : 0 < 2 * h := by linarith
  have hc1 : 2 * h < 1 := by linarith
  have he := meanPressure_coverPull (chartScale_pos n) ha hab hd (slowToChartTZ h n) i M
    (radialFrequency h n i d M) (ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)))
    (vector .radial) (vector .radial) (radialFrequency_shift h n i d M)
    (qLength (2 * h)) (qLength (2 * h)) hU hf hp hs z hzU
    (qLength_pos hc hc1 hz) (qLength_chart hh hh1 n hz)
  rw [pressure_unit_factor] at he
  exact he

theorem stream_unit_factor (h : ℝ) (n : ℕ) :
    ChartScales.Q n ^ (-CoordinateAlgebra.A h) / chartScale n =
      ChartScales.Q n ^ (-(CoordinateAlgebra.A h - 1 / 2)) := by
  rw [chartScale, ← Real.rpow_sub (ChartScales.Q_pos n)]
  congr 1
  ring

theorem physicalStreamPotential_naturality {h d a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (n i : ℕ) (M : ℝ)
    {U : Set Plane} (hU : IsOpen U) {f : PressureStream.Lift Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : SupportedGauge a b (qLength (2 * h)) U f)
    (z : PressureStream.Lift Plane) (hz : 0 < z.2.1.1) (hzU : slowToChartTZ h n z.2.1 ∈ U) :
    streamPotential d a b M (qLength (2 * h)) (vector .radial)
      (fieldOnPhysicalTZ h n i (CoordinateAlgebra.A h) f) z =
    fieldOnPhysicalTZ h n i (CoordinateAlgebra.A h - 1 / 2)
      (streamPotential d a b (radialFrequency h n i d M) (qLength (2 * h)) (vector .radial) f) z :=
        by
  have hc : 0 < 2 * h := by linarith
  have hc1 : 2 * h < 1 := by linarith
  have he := streamPotential_coverPull (chartScale_pos n) ha hab hd (slowToChartTZ h n) i M
    (radialFrequency h n i d M) (ChartScales.Q n ^ (-CoordinateAlgebra.A h))
    (vector .radial) (vector .radial) (radialFrequency_shift h n i d M)
    (qLength (2 * h)) (qLength (2 * h)) hU hf hs z hzU
    (qLength_pos hc hc1 hz) (qLength_chart hh hh1 n hz)
  rw [stream_unit_factor] at he
  exact he

end ActualChart


open WeightedRadialPrimitive RadialPullback

section MovingSupport
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem iteratedFDeriv_supportedGauge_fiber {a b : ℝ} {ell : S → ℝ} {U : Set S}
    (hU : IsOpen U) (hell : ContinuousOn ell U) {f : PressureStream.Lift S → V}
    (hs : ∀ z, z.2.1 ∈ U → f z ≠ 0 → z.1 ∈ Icc (ell z.2.1 * a) (ell z.2.1 * b))
    {s : S} (hsU : s ∈ U) (j : ℕ) :
    RadialAlias.RadiallySupported (ell s * a) (ell s * b)
      (PhysicalMeanDomain.freezeSlow s (iteratedFDeriv ℝ j f)) := by
  intro p hp
  by_contra hmem
  let z : PressureStream.Lift S := (p.1, (s, p.2.2))
  have he : ContinuousAt (fun x : PressureStream.Lift S => ell x.2.1) z :=
    (hell.continuousAt (hU.mem_nhds hsU)).comp continuous_snd.fst.continuousAt
  have hu : ∀ᶠ x : PressureStream.Lift S in 𝓝 z, x.2.1 ∈ U :=
    (PhysicalMeanDomain.slowDomain_open hU).mem_nhds hsU
  have hz0 : f =ᶠ[𝓝 z] (fun _ : PressureStream.Lift S => (0 : V)) := by
    rcases not_and_or.mp hmem with hleft | hright
    · have hlt : z.1 < ell z.2.1 * a := lt_of_not_ge hleft
      have hv := continuous_fst.continuousAt.eventually_lt (he.mul_const a) hlt
      filter_upwards [hu, hv] with x hx hxr
      by_contra hn
      exact (not_le_of_gt hxr) (hs x hx hn).1
    · have hlt : ell z.2.1 * b < z.1 := lt_of_not_ge hright
      have hv := (he.mul_const b).eventually_lt continuous_fst.continuousAt hlt
      filter_upwards [hu, hv] with x hx hxr
      by_contra hn
      exact (not_le_of_gt hxr) (hs x hx hn).2
  have hj0 : iteratedFDeriv ℝ j f z = 0 := by
    have hew : f =ᶠ[𝓝[univ] z] (fun _ : PressureStream.Lift S => (0 : V)) := by
      simpa only [nhdsWithin_univ] using hz0
    simpa only [iteratedFDerivWithin_univ, iteratedFDeriv_fun_zero, Pi.zero_apply] using
      hew.iteratedFDerivWithin_eq (𝕜 := ℝ) hz0.self_of_nhds j
  exact hp hj0

theorem iteratedFDeriv_zero_outsideGauge {a b : ℝ} {ell : S → ℝ} {U : Set S}
    (hU : IsOpen U) (hell : ContinuousOn ell U) {f : PressureStream.Lift S → V}
    (hf : ContDiff ℝ ∞ f)
    (hs : ∀ z, z.2.1 ∈ U → f z ≠ 0 → z.1 ∈ Icc (ell z.2.1 * a) (ell z.2.1 * b))
    {z : PressureStream.Lift S} (hz : z.2.1 ∈ U)
    (hR : z.1 ∉ Ioo (ell z.2.1 * a) (ell z.2.1 * b)) (j : ℕ) :
    iteratedFDeriv ℝ j f z = 0 := by
  exact MeanMomentBounds.supported_zero_outside_open
    (PhysicalMeanDomain.freezeSlow_continuous (TransportPrimitive.iteratedFDeriv_contDiff hf
      j).continuous z.2.1)
    (iteratedFDeriv_supportedGauge_fiber hU hell hs hz j) hR

end MovingSupport

section ScaledIntegrals
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem integral_scaled {l : ℝ} (hl : l ≠ 0) (f : ℝ → V) (a b : ℝ) :
    (∫ x in (l * a)..(l * b), f x) = l • ∫ x in a..b, f (l * x) := by
  rw [intervalIntegral.integral_comp_mul_left f hl, smul_smul, mul_inv_cancel₀ hl, one_smul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ V] in
theorem radialScale_supported {l a b : ℝ} (hl : 0 < l) {f : ℝ × E → V}
    (hs : RadialAlias.RadiallySupported (l * a) (l * b) f) :
    RadialAlias.RadiallySupported a b (fun z : ℝ × E => f (l * z.1, z.2)) := by
  intro z hz
  have h := hs hz
  exact ⟨(mul_le_mul_iff_right₀ hl).mp h.1, (mul_le_mul_iff_right₀ hl).mp h.2⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem radialSlice_scaled {l : ℝ} (hl : l ≠ 0) (M : ℝ) (v : E)
    (f : ℝ × E → V) (z : ℝ × E) (s : ℝ) :
    radialSlice (M * l) v (fun q : ℝ × E => f (l * q.1, q.2)) (z.1 / l, z.2) s =
      radialSlice M v f z (l * s) := by
  have hcoeff : (M * l) * (s - z.1 / l) = M * (l * s - z.1) := by
    field_simp [hl]
  simp only [radialSlice, hcoeff]

theorem pastIntegral_scaled {l a b : ℝ} (hl : 0 < l) (M : ℝ) (v : E)
    {f : ℝ × E → V} (hf : Continuous f) (hs : RadialAlias.RadiallySupported (l * a) (l * b) f)
    (z : ℝ × E) :
    TransportPrimitive.pastIntegral M v f z =
      l • TransportPrimitive.pastIntegral (M * l) v (fun q : ℝ × E => f (l * q.1, q.2)) (z.1 / l,
        z.2) := by
  have hc : Continuous (fun q : ℝ × E => f (l * q.1, q.2)) :=
    hf.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  rw [TransportPrimitive.pastIntegral_eq_radialInterval hf hs,
    TransportPrimitive.pastIntegral_eq_radialInterval (f := fun q : ℝ × E => f (l * q.1, q.2))
      hc (radialScale_supported hl hs)]
  change (∫ s in (l * a)..z.1, radialSlice M v f z s) =
    l • ∫ s in a..(z.1 / l), radialSlice (M * l) v (fun q : ℝ × E => f (l * q.1, q.2)) (z.1 / l,
      z.2) s
  simp_rw [radialSlice_scaled hl.ne']
  rw [← integral_scaled hl.ne', mul_div_cancel₀ _ hl.ne']

theorem futureIntegral_scaled {l a b : ℝ} (hl : 0 < l) (M : ℝ) (v : E)
    {f : ℝ × E → V} (hf : Continuous f) (hs : RadialAlias.RadiallySupported (l * a) (l * b) f)
    (z : ℝ × E) :
    TransportPrimitive.futureIntegral M v f z =
      l • TransportPrimitive.futureIntegral (M * l) v (fun q : ℝ × E => f (l * q.1, q.2)) (z.1 / l,
        z.2) := by
  have hc : Continuous (fun q : ℝ × E => f (l * q.1, q.2)) :=
    hf.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  rw [TransportPrimitive.futureIntegral_eq_radialInterval hf hs,
    TransportPrimitive.futureIntegral_eq_radialInterval (f := fun q : ℝ × E => f (l * q.1, q.2))
      hc (radialScale_supported hl hs)]
  change (∫ s in z.1..(l * b), radialSlice M v f z s) =
    l • ∫ s in (z.1 / l)..b, radialSlice (M * l) v (fun q : ℝ × E => f (l * q.1, q.2)) (z.1 / l,
      z.2) s
  simp_rw [radialSlice_scaled hl.ne']
  rw [← integral_scaled hl.ne', mul_div_cancel₀ _ hl.ne']

theorem scaled_transport_past_left_uniform {a b cL cR L : ℝ}
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR) (hL : 0 < L) (p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (l : ℝ), 0 < l → l ≤ L → ∀ (M : ℝ) (v : E) (f : ℝ × E → V),
      Continuous f → RadialAlias.RadiallySupported (l * a) (l * b) f →
      ∀ A : ℝ, 0 ≤ A →
      (∀ R, R / l ∈ Ioo a b → ∀ Y : E, ‖f (R, Y)‖ ≤ A * logWeight cL cR a b p (R / l)) →
      ∀ z : ℝ × E, z.1 / l ∈ Ioo a b → logPosition a (z.1 / l) ≤ logLength a b / 2 →
      ‖TransportPrimitive.pastIntegral M v f z‖ ≤ K * A * logWeight cL cR a b p (z.1 / l) := by
  obtain ⟨K, hK, hb⟩ := transport_past_left_uniform (E := E) (V := V) ha hab hcL hcR p
  refine ⟨L * K, mul_nonneg hL.le hK, ?_⟩
  intro l hl hlL M v f hf hs A hA hin z hz hh
  have hpull := radialScale_supported hl hs
  have hpullc : Continuous (fun q : ℝ × E => f (l * q.1, q.2)) :=
    hf.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hsource : ∀ R ∈ Ioo a b, ∀ Y : E,
      ‖f (l * R, Y)‖ ≤ A * logWeight cL cR a b p R := by
    intro R hR Y
    simpa only [mul_div_cancel_left₀ _ hl.ne'] using
      hin (l * R) (by simpa only [mul_div_cancel_left₀ _ hl.ne'] using hR) Y
  have h := hb (M * l) v (fun q : ℝ × E => f (l * q.1, q.2)) hpullc hpull A hA hsource (z.1 / l,
    z.2) hz hh
  rw [pastIntegral_scaled hl M v hf hs, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
  calc
    _ ≤ l * (K * A * logWeight cL cR a b p (z.1 / l)) := mul_le_mul_of_nonneg_left h hl.le
    _ ≤ L * (K * A * logWeight cL cR a b p (z.1 / l)) :=
      mul_le_mul_of_nonneg_right hlL (mul_nonneg (mul_nonneg hK hA) (weight_pos cL cR p
        (logPosition_mem ha hz)).le)
    _ = _ := by ring

theorem scaled_transport_future_right_uniform {a b cL cR L : ℝ}
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR) (hL : 0 < L) (p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (l : ℝ), 0 < l → l ≤ L → ∀ (M : ℝ) (v : E) (f : ℝ × E → V),
      Continuous f → RadialAlias.RadiallySupported (l * a) (l * b) f →
      ∀ A : ℝ, 0 ≤ A →
      (∀ R, R / l ∈ Ioo a b → ∀ Y : E, ‖f (R, Y)‖ ≤ A * logWeight cL cR a b p (R / l)) →
      ∀ z : ℝ × E, z.1 / l ∈ Ioo a b → logLength a b / 2 ≤ logPosition a (z.1 / l) →
      ‖TransportPrimitive.futureIntegral M v f z‖ ≤ K * A * logWeight cL cR a b p (z.1 / l) := by
  obtain ⟨K, hK, hb⟩ := transport_future_right_uniform (E := E) (V := V) ha hab hcL hcR p
  refine ⟨L * K, mul_nonneg hL.le hK, ?_⟩
  intro l hl hlL M v f hf hs A hA hin z hz hh
  have hpull := radialScale_supported hl hs
  have hpullc : Continuous (fun q : ℝ × E => f (l * q.1, q.2)) :=
    hf.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hsource : ∀ R ∈ Ioo a b, ∀ Y : E,
      ‖f (l * R, Y)‖ ≤ A * logWeight cL cR a b p R := by
    intro R hR Y
    simpa only [mul_div_cancel_left₀ _ hl.ne'] using
      hin (l * R) (by simpa only [mul_div_cancel_left₀ _ hl.ne'] using hR) Y
  have h := hb (M * l) v (fun q : ℝ × E => f (l * q.1, q.2)) hpullc hpull A hA hsource (z.1 / l,
    z.2) hz hh
  rw [futureIntegral_scaled hl M v hf hs, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
  calc
    _ ≤ l * (K * A * logWeight cL cR a b p (z.1 / l)) := mul_le_mul_of_nonneg_left h hl.le
    _ ≤ L * (K * A * logWeight cL cR a b p (z.1 / l)) :=
      mul_le_mul_of_nonneg_right hlL (mul_nonneg (mul_nonneg hK hA) (weight_pos cL cR p
        (logPosition_mem ha hz)).le)
    _ = _ := by ring

end ScaledIntegrals

section ScaledNormalization
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The fixed normalization map has uniform weighted jet bounds when the
weight is read on any admissible dilated radial fiber. -/
theorem normalizeSource_gauge_finiteJets {c e a b d : ℝ}
    (hc : 0 < c) (hce : c < e) (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (cL cR : ℝ) (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (l : ℝ), 0 < l → c ≤ l * a → l * b ≤ e →
      ∀ (f : PressureStream.Lift S → ℝ), ContDiff ℝ ∞ f → ∀ A : ℝ, 0 ≤ A → ∀ s : S,
      (∀ j ≤ m, ∀ R, R / l ∈ Ioo a b → ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ j f (R, (s, Y))‖ ≤ A * logWeight cL cR a b p (R / l)) →
      ∀ z : PressureStream.Lift S, z.1 / l ^ d ∈ Ioo (a ^ d) (b ^ d) → z.2.1 = s → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (normalizeSource d c f) z‖ ≤
          K * A * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (z.1 / l ^ d) := by
  obtain ⟨KC, hKC, hbC⟩ := radial_comp_finiteJets_uniform (E := S × PressureStream.Plane) (V := ℝ)
    (c ^ d) (e ^ d) (inverseChart_contDiff hc d) m
  obtain ⟨KM, hKM, hbM⟩ := radial_multiplier_finiteJets_uniform (E := S × PressureStream.Plane) (V
    := ℝ)
    (c ^ d) (e ^ d) (sourceMultiplier_contDiff hc hd) m
  let Q := ((min 1 d⁻¹) ^ p)⁻¹
  have hQ : 0 ≤ Q := (inv_pos.mpr (pow_pos (lt_min zero_lt_one (inv_pos.mpr hd)) p)).le
  refine ⟨KM * KC * Q, mul_nonneg (mul_nonneg hKM hKC) hQ, ?_⟩
  intro l hl hca hbe f hf A hA s hin z hz hzs j hj
  subst s
  have hlp := Real.rpow_pos_of_pos hl d
  have hlaz : (l * a) ^ d < z.1 := by
    rw [Real.mul_rpow hl.le ha.le]
    nlinarith [(lt_div_iff₀ hlp).mp hz.1]
  have hlbz : z.1 < (l * b) ^ d := by
    rw [Real.mul_rpow hl.le (ha.trans hab).le]
    nlinarith [(div_lt_iff₀ hlp).mp hz.2]
  have hzce : z.1 ∈ Ioo (c ^ d) (e ^ d) :=
    ⟨(Real.rpow_le_rpow hc.le hca hd.le).trans_lt hlaz,
      hlbz.trans_le (Real.rpow_le_rpow (mul_pos hl (ha.trans hab)).le hbe hd.le)⟩
  have hrce := inverseChart_mem hc hce hd hzce
  have hrp : 0 < inverseChart d c z.1 := hc.trans hrce.1
  have hrpow := inverseChart_rpow hc hd hzce.1.le
  have har : l * a < inverseChart d c z.1 :=
    (Real.rpow_lt_rpow_iff (mul_pos hl ha).le hrp.le hd).mp (by simpa only [hrpow] using hlaz)
  have hrb : inverseChart d c z.1 < l * b :=
    (Real.rpow_lt_rpow_iff hrp.le (mul_pos hl (ha.trans hab)).le hd).mp (by simpa only [hrpow]
      using hlbz)
  have hr : inverseChart d c z.1 / l ∈ Ioo a b :=
    ⟨(lt_div_iff₀ hl).mpr (by nlinarith), (div_lt_iff₀ hl).mpr (by nlinarith)⟩
  have hratio : (inverseChart d c z.1 / l) ^ d = z.1 / l ^ d := by
    rw [Real.div_rpow hrp.le hl.le, hrpow]
  have hw : 0 ≤ logWeight cL cR a b p (inverseChart d c z.1 / l) :=
    (weight_pos cL cR p (logPosition_mem ha hr)).le
  have hcomp (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i (f ∘ liftChart (inverseChart d c)) z‖ ≤
        KC * (A * logWeight cL cR a b p (inverseChart d c z.1 / l)) :=
    hbC f hf z ⟨hzce.1.le, hzce.2.le⟩ _ (mul_nonneg hA hw)
      (fun k hk => hin k hk _ hr z.2.2) i hi
  have hmul := hbM (f ∘ liftChart (inverseChart d c))
    (hf.comp (liftChart_contDiff (inverseChart_contDiff hc d))) z ⟨hzce.1.le, hzce.2.le⟩
    (KC * (A * logWeight cL cR a b p (inverseChart d c z.1 / l)))
    (mul_nonneg hKC (mul_nonneg hA hw)) hcomp j hj
  change ‖iteratedFDeriv ℝ j (normalizeSource d c f) z‖ ≤
    KM * (KC * (A * logWeight cL cR a b p (inverseChart d c z.1 / l))) at hmul
  have hweight := logWeight_power_reverse ha hd hr cL cR p
  rw [hratio] at hweight
  calc
    _ ≤ KM * (KC * (A * logWeight cL cR a b p (inverseChart d c z.1 / l))) := hmul
    _ ≤ KM * (KC * (A * (Q * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (z.1 / l ^ d))))
      :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hweight hA) hKC) hKM
    _ = _ := by ring

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem normalizeSource_supportedGauge {c e a b d : ℝ} (hc : 0 < c) (hce : c < e)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) {ell : S → ℝ} {U : Set S}
    (hl : ∀ s ∈ U, 0 < ell s) {f : PressureStream.Lift S → ℝ}
    (hs : RadialAlias.RadiallySupported c e f) (hsg : SupportedGauge a b ell U f) :
    SupportedGauge (a ^ d) (b ^ d) (fun s => ell s ^ d) U (normalizeSource d c f) := by
  intro z hz hn
  have hzpos : 0 < z.1 := by
    by_contra h
    exact hn (TransportPrimitive.radial_zero_of_lt (normalizeSource_supported hc hce hd hs)
      ((le_of_not_gt h).trans_lt (Real.rpow_pos_of_pos hc d)))
  have he := normalizeSource_eq_formula hc hce hd hzpos hs z.2
  have hfn : f (z.1 ^ d⁻¹, z.2) ≠ 0 := by
    intro hzero
    apply hn
    rw [he, hzero, smul_zero]
  have h := hsg (z.1 ^ d⁻¹, z.2) hz hfn
  have hrpos := Real.rpow_pos_of_pos hzpos d⁻¹
  constructor
  · calc
      ell z.2.1 ^ d * a ^ d = (ell z.2.1 * a) ^ d := (Real.mul_rpow (hl _ hz).le ha.le).symm
      _ ≤ (z.1 ^ d⁻¹) ^ d := Real.rpow_le_rpow (mul_pos (hl _ hz) ha).le h.1 hd.le
      _ = z.1 := Real.rpow_inv_rpow hzpos.le hd.ne'
  · calc
      z.1 = (z.1 ^ d⁻¹) ^ d := (Real.rpow_inv_rpow hzpos.le hd.ne').symm
      _ ≤ (ell z.2.1 * b) ^ d := Real.rpow_le_rpow hrpos.le h.2 hd.le
      _ = ell z.2.1 ^ d * b ^ d := Real.mul_rpow (hl _ hz).le (ha.trans hab).le

end ScaledNormalization

section VariableTransport
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

noncomputable def normalizedCutoff (a b : ℝ) (ell : S → ℝ) (z : PressureStream.Lift S) : ℝ :=
  TransportPrimitive.interiorCutoff a b (radialRatio ell z)

noncomputable def transportGauge (a b M : ℝ) (ell : S → ℝ) (v : PressureStream.Plane)
    (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) : ℝ :=
  TransportPrimitive.pastIntegral M ((0 : S), v) f z -
    normalizedCutoff a b ell z * TransportPrimitive.totalIntegral M ((0 : S), v) f z

theorem normalizedCutoff_contDiffOn (a b : ℝ) {ell : S → ℝ} {U : Set S}
    (hell : ContDiffOn ℝ ∞ ell U) (hl : ∀ s ∈ U, 0 < ell s) :
    ContDiffOn ℝ ∞ (normalizedCutoff a b ell) (PhysicalMeanDomain.slowDomain U) :=
  (TransportPrimitive.interiorCutoff_contDiff a b).comp_contDiffOn (radialRatio_contDiffOn hell hl)

theorem transportGauge_contDiffOn {c e a b M : ℝ} {ell : S → ℝ} {U : Set S}
    (hell : ContDiffOn ℝ ∞ ell U) (hl : ∀ s ∈ U, 0 < ell s) (v : PressureStream.Plane)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported c e
      f) :
    ContDiffOn ℝ ∞ (transportGauge a b M ell v f) (PhysicalMeanDomain.slowDomain U) :=
  (TransportPrimitive.pastIntegral_contDiff hf hs).contDiffOn.sub
    ((normalizedCutoff_contDiffOn a b hell hl).mul
      (TransportPrimitive.totalIntegral_contDiff hf hs).contDiffOn)

/-- No derivative is taken after the scalar change of integration variable.
The estimate uses the original full joint derivatives under the fixed-u integral. -/
theorem transportGauge_finiteJets {c e a b cL cR L : ℝ} (hce : c < e)
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR) (hL : 0 < L)
    (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : Set S), IsOpen U → ∀ (ell : S → ℝ), ContDiffOn ℝ ∞ ell U →
      (∀ s ∈ U, 0 < ell s) → (∀ s ∈ U, ell s ≤ L) →
      ∀ (M : ℝ) (v : PressureStream.Plane) (f : PressureStream.Lift S → ℝ), ContDiff ℝ ∞ f →
      RadialAlias.RadiallySupported c e f → SupportedGauge a b ell U f →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → ∀ z : PressureStream.Lift S, z.2.1 ∈ U →
      z.1 / ell z.2.1 ∈ Ioo a b →
      (∀ j ≤ m, ∀ R, R / ell z.2.1 ∈ Ioo a b → ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ j f (R, (z.2.1, Y))‖ ≤ A * logWeight cL cR a b p (R / ell z.2.1)) →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (normalizedCutoff a b ell) z‖ ≤ B) → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (transportGauge a b M ell v f) z‖ ≤
        K * (1 + B) * A * logWeight cL cR a b p (z.1 / ell z.2.1) := by
  classical
  obtain ⟨ρ, hρ, hρL, hleft, hright⟩ := exists_log_plateau_width (b := b) ha
    (c := (2 * a + b) / 3) (d := (a + 2 * b) / 3)
    (by linarith) (by linarith) (by linarith)
    (TransportPrimitive.interiorCutoff a b)
    (fun X hX => TransportPrimitive.interiorCutoff_zero hab hX)
    (fun X hX => TransportPrimitive.interiorCutoff_one hab hX)
  obtain ⟨δ, hδ, hmiddle⟩ := middle_weight_lower_bound
    (L := logLength a b) hcL hcR (half_pos hρ)
  obtain ⟨W, hW, hweight⟩ := weight_uniform_bound hcL hcR (logLength a b) p
  choose KL hKL hbL using fun j : Fin (m + 1) =>
    scaled_transport_past_left_uniform (E := S × PressureStream.Plane)
      (V := ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => PressureStream.Lift S) ℝ)
      ha hab hcL hcR hL p
  choose KR hKR hbR using fun j : Fin (m + 1) =>
    scaled_transport_future_right_uniform (E := S × PressureStream.Plane)
      (V := ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => PressureStream.Lift S) ℝ)
      ha hab hcL hcR hL p
  let leftK := ∑ j, KL j
  let rightK := ∑ j, KR j
  let massK := W * (e - c)
  let midK := massK * (1 + (2 : ℝ) ^ m) / δ
  let K := leftK + rightK + midK
  have hLK : 0 ≤ leftK := Finset.sum_nonneg (fun j _ => hKL j)
  have hRK : 0 ≤ rightK := Finset.sum_nonneg (fun j _ => hKR j)
  have hmassK : 0 ≤ massK := mul_nonneg hW (sub_pos.mpr hce).le
  have hmidK : 0 ≤ midK := div_nonneg (mul_nonneg hmassK (by positivity)) hδ.le
  have hleftK : leftK ≤ K := by dsimp [K]; linarith
  have hrightK : rightK ≤ K := by dsimp [K]; linarith
  have hmiddleK : midK ≤ K := by dsimp [K]; linarith
  have hKK : 0 ≤ K := hLK.trans hleftK
  refine ⟨K, hKK, ?_⟩
  intro U hU ell hell hl hu M v f hf hs hsg A B hA hB z hz hR hin hcut j hj
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hratio : ContinuousAt (radialRatio ell) z :=
    (radialRatio_contDiffOn hell hl).continuousOn.continuousAt
      ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hz)
  have hratioPos : 0 < radialRatio ell z := ha.trans hR.1
  have hlog : ContinuousAt (fun x : PressureStream.Lift S => logPosition a (radialRatio ell x)) z :=
    (hratio.div_const a).log (div_ne_zero hratioPos.ne' ha.ne')
  have hpos : ∀ᶠ x in 𝓝 z, 0 < radialRatio ell x := hratio.eventually (lt_mem_nhds hratioPos)
  have hnorm : 0 ≤ logWeight cL cR a b p (z.1 / ell z.2.1) :=
    (weight_pos cL cR p (logPosition_mem ha hR)).le
  have hKone : K ≤ K * (1 + B) := by nlinarith
  have hmass (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i (TransportPrimitive.pastIntegral M ((0 : S), v) f) z‖ ≤ massK * A ∧
      ‖iteratedFDeriv ℝ i (TransportPrimitive.totalIntegral M ((0 : S), v) f) z‖ ≤ massK * A := by
    have hbound (R : ℝ) (_hR : R ∈ Icc c e) (Y : PressureStream.Plane) :
        ‖iteratedFDeriv ℝ i f (R, (z.2.1, Y))‖ ≤ A * W := by
      by_cases hp : R / ell z.2.1 ∈ Ioo a b
      · exact (hin i hi R hp Y).trans
          (mul_le_mul_of_nonneg_left (hweight _ (logPosition_mem ha hp)) hA)
      · have hp' : R ∉ Ioo (ell z.2.1 * a) (ell z.2.1 * b) := by
          intro h
          exact hp ⟨(lt_div_iff₀ (hl _ hz)).mpr (by nlinarith [h.1]),
            (div_lt_iff₀ (hl _ hz)).mpr (by nlinarith [h.2])⟩
        rw [iteratedFDeriv_zero_outsideGauge (z := (R, (z.2.1, Y)))
          hU hell.continuousOn hf hsg hz hp' i, norm_zero]
        exact mul_nonneg hA hW
    have h := transportIntegrals_jet_bound_fiber (M := M) hce.le v hf hs z.2.1 i hbound z rfl
    exact ⟨h.1.trans_eq (by dsimp [massK]; ring), h.2.trans_eq (by dsimp [massK]; ring)⟩
  by_cases hzleft : logPosition a (z.1 / ell z.2.1) ≤ ρ / 2
  · have heq : transportGauge a b M ell v f =ᶠ[𝓝 z]
        TransportPrimitive.pastIntegral M ((0 : S), v) f := by
      have hlogleft : ∀ᶠ x in 𝓝 z, logPosition a (radialRatio ell x) < ρ :=
        hlog.eventually (gt_mem_nhds (by change logPosition a (z.1 / ell z.2.1) < ρ; linarith))
      filter_upwards [hpos, hlogleft] with x hxp hxl
      have hzero : normalizedCutoff a b ell x = 0 := by
        have he := hleft (logPosition a (radialRatio ell x)) hxl.le
        simp only [expCoordinate_logPosition ha hxp] at he
        exact he
      simp only [transportGauge, hzero, zero_mul, sub_zero]
    rw [MeanRankUpdate.iteratedFDeriv_congr_germ heq j,
      TransportPrimitive.iteratedFDeriv_pastIntegral hf hs,
      ← PhysicalMeanDomain.pastIntegral_freeze]
    have h := hbL j' (ell z.2.1) (hl _ hz) (hu _ hz) M ((0 : S), v)
      (PhysicalMeanDomain.freezeSlow z.2.1 (iteratedFDeriv ℝ j f))
      (PhysicalMeanDomain.freezeSlow_continuous (TransportPrimitive.iteratedFDeriv_contDiff hf
        j).continuous _)
      (iteratedFDeriv_supportedGauge_fiber hU hell.continuousOn hsg hz j) A hA
      (fun R hR Y => hin j hj R hR Y.2) z hR (by linarith)
    have hsingle : KL j' ≤ leftK := Finset.single_le_sum (fun i _ => hKL i) (Finset.mem_univ j')
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((hsingle.trans hleftK).trans hKone) hA) hnorm)
  · by_cases hzright : logLength a b - ρ / 2 ≤ logPosition a (z.1 / ell z.2.1)
    · have heq : transportGauge a b M ell v f =ᶠ[𝓝 z]
          -TransportPrimitive.futureIntegral M ((0 : S), v) f := by
        have hlogright : ∀ᶠ x in 𝓝 z, logLength a b - ρ < logPosition a (radialRatio ell x) :=
          hlog.eventually (lt_mem_nhds (by change logLength a b - ρ < logPosition a (z.1 / ell
            z.2.1); linarith))
        filter_upwards [hpos, hlogright] with x hxp hxr
        have hone : normalizedCutoff a b ell x = 1 := by
          have he := hright (logPosition a (radialRatio ell x)) hxr.le
          simp only [expCoordinate_logPosition ha hxp] at he
          exact he
        simp only [transportGauge, hone, one_mul, Pi.neg_apply]
        rw [TransportPrimitive.futureIntegral_eq_total_sub_past hf.continuous hs]
        ring
      rw [MeanRankUpdate.iteratedFDeriv_congr_germ heq j, iteratedFDeriv_neg_apply, norm_neg,
        TransportPrimitive.iteratedFDeriv_futureIntegral hf hs,
        ← PhysicalMeanDomain.futureIntegral_freeze]
      have h := hbR j' (ell z.2.1) (hl _ hz) (hu _ hz) M ((0 : S), v)
        (PhysicalMeanDomain.freezeSlow z.2.1 (iteratedFDeriv ℝ j f))
        (PhysicalMeanDomain.freezeSlow_continuous (TransportPrimitive.iteratedFDeriv_contDiff hf
          j).continuous _)
        (iteratedFDeriv_supportedGauge_fiber hU hell.continuousOn hsg hz j) A hA
        (fun R hR Y => hin j hj R hR Y.2) z hR (by linarith)
      have hsingle : KR j' ≤ rightK := Finset.single_le_sum (fun i _ => hKR i) (Finset.mem_univ j')
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ((hsingle.trans hrightK).trans hKone) hA) hnorm)
    · have hw : δ ≤ logWeight cL cR a b p (z.1 / ell z.2.1) :=
        hmiddle p (logPosition a (z.1 / ell z.2.1)) ⟨le_of_not_ge hzleft, le_of_not_ge hzright⟩
      have hC := normalizedCutoff_contDiffOn a b hell hl
      have hJ := (TransportPrimitive.totalIntegral_contDiff hf hs (M := M) (v := ((0 : S),
        v))).contDiffOn (s := PhysicalMeanDomain.slowDomain U)
      have hI := (TransportPrimitive.pastIntegral_contDiff hf hs (M := M) (v := ((0 : S),
        v))).contDiffOn (s := PhysicalMeanDomain.slowDomain U)
      have hprod := product_jet_bound (PhysicalMeanDomain.slowDomain_open hU) hC hJ hz hj hB
        (mul_nonneg hmassK hA) hcut (fun i hi => (hmass i hi).2)
      have hb : ‖iteratedFDeriv ℝ j (transportGauge a b M ell v f) z‖ ≤
          massK * A + (2 : ℝ) ^ m * B * (massK * A) :=
        (sub_jet_norm_le (PhysicalMeanDomain.slowDomain_open hU) hI (hC.mul hJ) hz j).trans
          (add_le_add (hmass j hj).1 hprod)
      have hmid : massK * A + (2 : ℝ) ^ m * B * (massK * A) ≤ midK * (1 + B) * A * δ := by
        dsimp [midK]
        have hpow : 0 ≤ (2 : ℝ) ^ m := by positivity
        have : 1 + (2 : ℝ) ^ m * B ≤ (1 + (2 : ℝ) ^ m) * (1 + B) := by nlinarith
        field_simp [hδ.ne']
        nlinarith [mul_nonneg (mul_nonneg hmassK hA) (sub_nonneg.mpr this)]
      exact (hb.trans hmid).trans ((mul_le_mul_of_nonneg_left hw
        (mul_nonneg (mul_nonneg hmidK (by positivity)) hA)).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmiddleK (by positivity)) hA)
              hnorm))

end VariableTransport

section LocalComposition
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

theorem radial_comp_finiteJets_local (a b : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : Set S), IsOpen U → ∀ (F : PressureStream.Lift S → ℝ),
      ContDiffOn ℝ ∞ F (PhysicalMeanDomain.slowDomain U) → ∀ z : PressureStream.Lift S,
      z.2.1 ∈ U → z.1 ∈ Icc a b → ∀ C : ℝ, 0 ≤ C →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i F (liftChart φ z)‖ ≤ C) → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (F ∘ liftChart φ) z‖ ≤ K * C := by
  obtain ⟨K, hK, hb⟩ := radial_comp_finiteJets_uniform (E := S × PressureStream.Plane) (V := ℝ) a b
    hφ m
  refine ⟨K, hK, ?_⟩
  intro U hU F hF z hz hR C hC hin j hj
  obtain ⟨χ, _, _, hχF, he⟩ := PhysicalMeanDomain.exists_fiber_localization hU hz hF
  have h := hb (PhysicalMeanDomain.localize χ F) hχF z hR C hC (fun i hi => by
      change ‖iteratedFDeriv ℝ i (PhysicalMeanDomain.localize χ F) (φ z.1, (z.2.1, z.2.2))‖ ≤ C
      rw [he.jet_eq i (φ z.1) z.2.2]
      exact hin i hi) j hj
  have hgerm : (PhysicalMeanDomain.localize χ F ∘ liftChart φ) =ᶠ[𝓝 z] (F ∘ liftChart φ) :=
    (he.eventuallyEq (φ z.1) z.2.2).comp_tendsto (liftChart_contDiff hφ).continuous.continuousAt
  rwa [MeanRankUpdate.iteratedFDeriv_congr_germ hgerm j] at h

end LocalComposition

section PhysicalTransportIdentity
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem cutoff_eq_normalizedCutoff {c a b d : ℝ} (hc : 0 < c) (ha : 0 < a)
    (ell : S → ℝ) (z : PressureStream.Lift S) (hl : 0 < ell z.2.1)
    (hleft : c ≤ ell z.2.1 * a) (hR : z.1 / ell z.2.1 ∈ Ioo a b) :
    cutoff d a b ell z = normalizedCutoff (a ^ d) (b ^ d) (fun s => ell s ^ d)
      (liftChart (powerChart d c) z) := by
  have hr : c < z.1 := hleft.trans_lt (by nlinarith [(lt_div_iff₀ hl).mp hR.1])
  have hratio : 0 < z.1 / ell z.2.1 := ha.trans hR.1
  simp only [cutoff, radialRatio, physicalCutoff, normalizedCutoff, liftChart]
  rw [powerChart_eq ha (by linarith [hR.1]) d, powerChart_eq hc (by linarith) d,
    Real.div_rpow (hc.trans hr).le hl.le]

theorem compactPrimitive_eq_transportGauge {c a b d M : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (ell : S → ℝ) (v : PressureStream.Plane) {U : Set S} (hU : IsOpen U)
    (hl : ∀ s ∈ U, 0 < ell s) (hleft : ∀ s ∈ U, c ≤ ell s * a)
    {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U)) (hs : SupportedGauge a b ell U f)
    (z : PressureStream.Lift S) (hz : z.2.1 ∈ U) (hR : z.1 / ell z.2.1 ∈ Ioo a b) :
    compactPrimitive d a b M ell v f z =
      transportGauge (a ^ d) (b ^ d) M (fun s => ell s ^ d) v (normalizeSource d c f)
        (liftChart (powerChart d c) z) := by
  rw [compactPrimitive_reference hc ha hab hd ell v hU hl hleft hf hs z hz,
    cutoff_eq_normalizedCutoff hc ha ell z (hl _ hz) (hleft _ hz) hR]
  rfl

theorem compactPrimitive_transportGauge_germ {c a b d M : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (ell : S → ℝ) (v : PressureStream.Plane) {U : Set S} (hU : IsOpen U)
    (hell : ContDiffOn ℝ ∞ ell U) (hl : ∀ s ∈ U, 0 < ell s)
    (hleft : ∀ s ∈ U, c ≤ ell s * a) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U)) (hs : SupportedGauge a b ell U f)
    (z : PressureStream.Lift S) (hz : z.2.1 ∈ U) (hR : z.1 / ell z.2.1 ∈ Ioo a b) :
    compactPrimitive d a b M ell v f =ᶠ[𝓝 z]
      (transportGauge (a ^ d) (b ^ d) M (fun s => ell s ^ d) v (normalizeSource d c f) ∘
        liftChart (powerChart d c)) := by
  have hV : IsOpen (PhysicalMeanDomain.slowDomain U ∩ radialRatio ell ⁻¹' Ioo a b) :=
    (radialRatio_contDiffOn hell hl).continuousOn.isOpen_inter_preimage
      (PhysicalMeanDomain.slowDomain_open hU) isOpen_Ioo
  filter_upwards [hV.mem_nhds ⟨hz, hR⟩] with p hp
  exact compactPrimitive_eq_transportGauge hc ha hab hd ell v hU hl hleft hf hs p hp.1 hp.2

end PhysicalTransportIdentity

section QWeighted
open LocalSignedRequest

/-- A fixed containing shell is used only to normalize the integral.  The
weight and the actual cutoff continue to use the moving profile endpoints. -/
theorem qLength_reference_bounds {coord a b : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) :
    ∃ c e L : ℝ, 0 < c ∧ c < e ∧ 0 < L ∧
      (∀ s ∈ U.carrier, 0 < qLength coord s) ∧
      (∀ s ∈ U.carrier, c ≤ qLength coord s * a) ∧
      (∀ s ∈ U.carrier, qLength coord s * b ≤ e) ∧
      (∀ s ∈ U.carrier, qLength coord s ≤ L) := by
  let l := Real.sqrt U.qlo
  let L := Real.sqrt (|U.qhi| + U.qlo + 1)
  have hl : 0 < l := Real.sqrt_pos.mpr U.qlo_pos
  have hL : 0 < L := Real.sqrt_pos.mpr (by have := abs_nonneg U.qhi; linarith [U.qlo_pos])
  have hlL : l ≤ L := Real.sqrt_le_sqrt (by have := abs_nonneg U.qhi; linarith)
  have hlow : ∀ s ∈ U.carrier, l ≤ qLength coord s :=
    fun s hs => Real.sqrt_le_sqrt (U.q_mem s hs).1
  have hupp : ∀ s ∈ U.carrier, qLength coord s ≤ L := by
    intro s hs
    apply Real.sqrt_le_sqrt
    exact (U.q_mem s hs).2.trans (by have := le_abs_self U.qhi; linarith [U.qlo_pos])
  refine ⟨l * a / 2, L * b + 1, L, by positivity, ?_, hL,
    fun s hs => hl.trans_le (hlow s hs), ?_, ?_, hupp⟩
  · have h1 : l * a ≤ L * a := mul_le_mul_of_nonneg_right hlL ha.le
    have h2 : L * a < L * b := mul_lt_mul_of_pos_left hab hL
    have hp : 0 < l * a := mul_pos hl ha
    linarith
  · intro s hs
    have hh := mul_le_mul_of_nonneg_right (hlow s hs) ha.le
    have hp : 0 < l * a := mul_pos hl ha
    linarith
  · intro s hs
    have hh := mul_le_mul_of_nonneg_right (hupp s hs) (ha.trans hab).le
    linarith

noncomputable def normalizedCutoffModel (d a b : ℝ) (y : MeanRankUpdate.ModelPoint) : ℝ :=
  TransportPrimitive.interiorCutoff (a ^ d) (b ^ d) (y.2.1 / (Real.sqrt y.1) ^ d)

theorem normalizedCutoffModel_contDiffOn (d a b : ℝ) :
    ContDiffOn ℝ ∞ (normalizedCutoffModel d a b) PhysicalCoordinateBounds.positiveTime := by
  intro y hy
  have hp : 0 < Real.sqrt y.1 := Real.sqrt_pos.mpr hy
  exact ((TransportPrimitive.interiorCutoff_contDiff (a ^ d) (b ^ d)).contDiffAt.comp y
    (contDiffAt_snd.fst.div
      ((contDiffAt_fst.sqrt (ne_of_gt hy)).rpow_const_of_ne hp.ne')
      (Real.rpow_pos_of_pos hp d).ne')).contDiffWithinAt

theorem normalizedCutoff_q_eq_kernel (coord d a b : ℝ) :
    normalizedCutoff (a ^ d) (b ^ d) (fun s => qLength coord s ^ d) =
      MeanRankUpdate.chartKernel coord (normalizedCutoffModel d a b) := rfl

theorem normalizedCutoff_q_finiteJets {coord qlo qhi rlo rhi : ℝ}
    (hc : 0 < coord) (hc1 : coord < 1) (hqlo : 0 < qlo) (d a b : ℝ)
    {V : Set MeanRankUpdate.ChartPoint}
    (hT : ∀ z ∈ V, MeanRankUpdate.chartInput z ∈ PhysicalCoordinateBounds.positiveTime)
    (hq : ∀ z ∈ V, MeanRankUpdate.chartQ coord z ∈ Icc qlo qhi)
    (hR : ∀ z ∈ V, z.1 ∈ Icc rlo rhi) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ JetBounds.FiniteJetBound m
      (normalizedCutoff (a ^ d) (b ^ d) (fun s => qLength coord s ^ d)) V B := by
  rw [normalizedCutoff_q_eq_kernel]
  exact MeanRankUpdate.chartKernel_finiteJetBounds hc hc1 hqlo hT hq hR
    (normalizedCutoffModel_contDiffOn d a b) m

/-- Uniform finite seminorm inequality for the actual q-gauge primitive.
The constant precedes all frequencies, sources, amplitudes and evaluation points. -/
theorem compactPrimitive_q_finiteJets_global {coord a b c e d cL cR L : ℝ}
    (U : SlowRegion coord) (hc : 0 < c) (hce : c < e) (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hL : 0 < L)
    (hl : ∀ s ∈ U.carrier, 0 < qLength coord s)
    (hleft : ∀ s ∈ U.carrier, c ≤ qLength coord s * a)
    (hright : ∀ s ∈ U.carrier, qLength coord s * b ≤ e)
    (hupp : ∀ s ∈ U.carrier, qLength coord s ≤ L) (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : PressureStream.Plane) (f : PressureStream.Lift
      PressureStream.Plane → ℝ),
      ContDiff ℝ ∞ f → RadialAlias.RadiallySupported c e f → SupportedGauge a b (qLength coord)
        U.carrier f →
      ∀ A : ℝ, 0 ≤ A → ∀ z : PressureStream.Lift PressureStream.Plane,
      z.2.1 ∈ U.carrier → z.1 / qLength coord z.2.1 ∈ Ioo a b →
      (∀ j ≤ m, ∀ R, R / qLength coord z.2.1 ∈ Ioo a b → ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ j f (R, (z.2.1, Y))‖ ≤ A * logWeight cL cR a b p (R / qLength coord
          z.2.1)) →
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j (compactPrimitive d a b M (qLength coord) v f) z‖ ≤
        K * A * logWeight cL cR a b p (z.1 / qLength coord z.2.1) := by
  have hcU : 0 < c ^ d := Real.rpow_pos_of_pos hc d
  have hceU : c ^ d < e ^ d := Real.rpow_lt_rpow hc.le hce hd
  have haU : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have habU : a ^ d < b ^ d := Real.rpow_lt_rpow ha.le hab hd
  have hcLU : 0 < d ^ 2 * cL := mul_pos (sq_pos_of_pos hd) hcL
  have hcRU : 0 < d ^ 2 * cR := mul_pos (sq_pos_of_pos hd) hcR
  have hLU : 0 < L ^ d := Real.rpow_pos_of_pos hL d
  have hell : ContDiffOn ℝ ∞ (qLength coord) U.carrier :=
    (qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun s hs => U.time_pos s hs)
  have hellpow : ContDiffOn ℝ ∞ (fun s => qLength coord s ^ d) U.carrier :=
    hell.rpow_const_of_ne (fun s hs => (hl s hs).ne')
  let V : Set MeanRankUpdate.ChartPoint := {z | z.2.1 ∈ U.carrier ∧ z.1 ∈ Icc (c ^ d) (e ^ d)}
  obtain ⟨B, hB, hbB⟩ := normalizedCutoff_q_finiteJets U.coord_pos U.coord_lt_one U.qlo_pos d a b
    (V := V) (fun z hz => U.time_pos z.2.1 hz.1) (fun z hz => U.q_mem z.2.1 hz.1) (fun _ hz =>
      hz.2) m
  obtain ⟨KN, hKN, hbN⟩ := normalizeSource_gauge_finiteJets (S := PressureStream.Plane) hc hce ha
    hab hd cL cR p m
  obtain ⟨KT, hKT, hbT⟩ := transportGauge_finiteJets (S := PressureStream.Plane) hceU haU habU hcLU
    hcRU hLU p m
  obtain ⟨KP, hKP, hbP⟩ := radial_comp_finiteJets_local (S := PressureStream.Plane) c e
    (powerChart_contDiff hc d) m
  let Q := ((min 1 d) ^ p)⁻¹
  have hQ : 0 ≤ Q := (inv_pos.mpr (pow_pos (lt_min zero_lt_one hd) p)).le
  refine ⟨KP * KT * (1 + B) * KN * Q, by positivity, ?_⟩
  intro M v f hf hs hsg A hA z hz hR hin j hj
  have hrleft : c < z.1 := (hleft _ hz).trans_lt (by nlinarith [(lt_div_iff₀ (hl _ hz)).mp hR.1])
  have hrright : z.1 < e := (show z.1 < qLength coord z.2.1 * b by
      nlinarith [(div_lt_iff₀ (hl _ hz)).mp hR.2]).trans_le (hright _ hz)
  have hrpow : powerChart d c z.1 = z.1 ^ d := powerChart_eq hc (by linarith) d
  let zU := liftChart (powerChart d c) z
  have hzU : zU.1 ∈ Icc (c ^ d) (e ^ d) := by
    change powerChart d c z.1 ∈ Icc (c ^ d) (e ^ d)
    rw [hrpow]
    exact ⟨Real.rpow_le_rpow hc.le hrleft.le hd.le,
      Real.rpow_le_rpow (hc.trans hrleft).le hrright.le hd.le⟩
  have hratio : zU.1 / qLength coord z.2.1 ^ d = (z.1 / qLength coord z.2.1) ^ d := by
    change powerChart d c z.1 / qLength coord z.2.1 ^ d = _
    rw [hrpow, Real.div_rpow (hc.trans hrleft).le (hl _ hz).le]
  have hR_U : zU.1 / qLength coord z.2.1 ^ d ∈ Ioo (a ^ d) (b ^ d) := by
    rw [hratio]
    exact ⟨Real.rpow_lt_rpow ha.le hR.1 hd,
      Real.rpow_lt_rpow (ha.trans hR.1).le hR.2 hd⟩
  let g := normalizeSource d c f
  have hg : ContDiff ℝ ∞ g := normalizeSource_contDiff hc hd hf
  have hgs : RadialAlias.RadiallySupported (c ^ d) (e ^ d) g := normalizeSource_supported hc hce hd
    hs
  have hgg := normalizeSource_supportedGauge hc hce ha hab hd hl hs hsg
  have hgp := transportGauge_contDiffOn (a := a ^ d) (b := b ^ d) (M := M) hellpow (fun s hs =>
    Real.rpow_pos_of_pos (hl s hs) d) v hg hgs
  have hbound (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i (transportGauge (a ^ d) (b ^ d) M (fun s => qLength coord s ^ d) v g) zU‖
        ≤
        KT * (1 + B) * (KN * A) * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p
          (zU.1 / qLength coord z.2.1 ^ d) := by
    exact hbT U.carrier U.isOpen _ hellpow (fun s hs => Real.rpow_pos_of_pos (hl s hs) d)
      (fun s hs => Real.rpow_le_rpow (hl s hs).le (hupp s hs) hd.le)
      M v g hg hgs hgg (KN * A) B (mul_nonneg hKN hA) hB zU hz hR_U
      (fun k hk R hR Y => hbN (qLength coord z.2.1) (hl _ hz) (hleft _ hz) (hright _ hz)
        f hf A hA z.2.1 hin (R, (z.2.1, Y)) hR rfl k hk)
      (fun k hk => hbB k hk zU ⟨hz, hzU⟩) i hi
  have hn : 0 ≤ KT * (1 + B) * (KN * A) *
      logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (zU.1 / qLength coord z.2.1 ^ d) :=
    mul_nonneg (by positivity) (weight_pos _ _ p (logPosition_mem haU hR_U)).le
  have hp := hbP U.carrier U.isOpen _ hgp z hz ⟨hrleft.le, hrright.le⟩ _ hn hbound j hj
  have he := compactPrimitive_transportGauge_germ (M := M) hc ha hab hd (qLength coord) v U.isOpen
    hell hl hleft hf.contDiffOn hsg z hz hR
  rw [MeanRankUpdate.iteratedFDeriv_congr_germ he j]
  have hw := logWeight_power_forward ha hd hR cL cR p
  rw [← hratio] at hw
  calc
    _ ≤ KP * (KT * (1 + B) * (KN * A) *
        logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (zU.1 / qLength coord z.2.1 ^ d)) :=
          hp
    _ = (KP * (KT * (1 + B) * (KN * A))) *
        logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (zU.1 / qLength coord z.2.1 ^ d) :=
          by ring
    _ ≤ (KP * (KT * (1 + B) * (KN * A))) *
        (Q * logWeight cL cR a b p (z.1 / qLength coord z.2.1)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

end QWeighted

section LocalWeighted
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem localize_supportedGauge {a b : ℝ} {ell : S → ℝ} {U : Set S}
    {f : PressureStream.Lift S → ℝ} (hs : SupportedGauge a b ell U f) (χ : S → ℝ) :
    SupportedGauge a b ell U (PhysicalMeanDomain.localize χ f) := by
  intro z hz hn
  apply hs z hz
  intro hzero
  exact hn (by simp only [PhysicalMeanDomain.localize, hzero, smul_zero])

variable [FiniteDimensional ℝ S]

theorem iteratedFDeriv_zero_outsideGauge_on {a b : ℝ} {ell : S → ℝ} {U : Set S}
    (hU : IsOpen U) (hell : ContinuousOn ell U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U)) (hs : SupportedGauge a b ell U f)
    {z : PressureStream.Lift S} (hz : z.2.1 ∈ U)
    (hR : z.1 ∉ Ioo (ell z.2.1 * a) (ell z.2.1 * b)) (j : ℕ) :
    iteratedFDeriv ℝ j f z = 0 := by
  obtain ⟨χ, _, _, hχf, he⟩ := PhysicalMeanDomain.exists_fiber_localization hU hz hf
  rw [← he.jet_eq j z.1 z.2.2]
  exact iteratedFDeriv_zero_outsideGauge hU hell hχf (localize_supportedGauge hs χ) hz hR j

end LocalWeighted

section MovingClasses
open LocalSignedRequest WeightedClasses

variable {coord a b d cL cR : ℝ} (U : SlowRegion coord)

theorem compactPrimitive_q_contDiffOn (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (M : ℝ) (v : PressureStream.Plane) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f) :
    ContDiffOn ℝ ∞ (compactPrimitive d a b M (qLength coord) v f)
      (PhysicalMeanDomain.slowDomain U.carrier) := by
  obtain ⟨c, e, L, hc, hce, _, hl, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  exact compactPrimitive_contDiffOn hc hce ha hab hd v U.isOpen
    ((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun s hs => U.time_pos s hs))
    hl hleft hright hf hs

theorem compactPrimitive_q_finiteJets (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (hcL : 0 < cL) (hcR : 0 < cR) (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : PressureStream.Plane) (f : Point → ℝ),
      ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier) →
      SupportedGauge a b (qLength coord) U.carrier f → ∀ A : ℝ, 0 ≤ A →
      ∀ z : Point, z.2.1 ∈ U.carrier → z.1 / qLength coord z.2.1 ∈ Ioo a b →
      (∀ j ≤ m, ∀ R, R / qLength coord z.2.1 ∈ Ioo a b → ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ j f (R, (z.2.1, Y))‖ ≤ A * logWeight cL cR a b p (R / qLength coord
          z.2.1)) →
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j (compactPrimitive d a b M (qLength coord) v f) z‖ ≤
        K * A * logWeight cL cR a b p (z.1 / qLength coord z.2.1) := by
  obtain ⟨c, e, L, hc, hce, hL, hl, hleft, hright, hupp⟩ := qLength_reference_bounds U ha hab
  obtain ⟨K, hK, hb⟩ := compactPrimitive_q_finiteJets_global U hc hce ha hab hd hcL hcR hL
    hl hleft hright hupp p m
  refine ⟨K, hK, ?_⟩
  intro M v f hf hs A hA z hz hR hin j hj
  have hfixed : PhysicalMeanDomain.SupportedOn c e U.carrier f := fun x hx hn =>
    ⟨(hleft _ hx).trans (hs x hx hn).1, (hs x hx hn).2.trans (hright _ hx)⟩
  obtain ⟨χ, _, hχs, hχf, he⟩ := PhysicalMeanDomain.exists_fiber_localization U.isOpen hz hf
  have h := hb M v (PhysicalMeanDomain.localize χ f) hχf
    (PhysicalMeanDomain.localize_supported hχs hfixed) (localize_supportedGauge hs χ)
    A hA z hz hR (fun i hi R hR Y => by rw [he.jet_eq i R Y]; exact hin i hi R hR Y) j hj
  rwa [((compactPrimitive_fiberLocal d a b M (qLength coord) v).germ he).jet_eq j z.1 z.2.2] at h

variable (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

theorem meanClass_compactPrimitive (hab : a < b) (hd : 0 < d)
    {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => compactPrimitive d a b (M n) (qLength coord) (v n) (f n)) := by
  let st := movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL
  have hdom : st.domain ⊆ PhysicalMeanDomain.slowDomain U.carrier := fun x hx =>
    ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL x).mp hx).1
  refine ⟨fun _ z hz => st.zeta_nonneg z hz,
    fun n => (compactPrimitive_q_contDiffOn U ha hab hd (M n) (v n) (hf n) (hs n)).mono hdom, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hclass.bounds m
  obtain ⟨K, hK, hKbound⟩ := compactPrimitive_q_finiteJets U ha hab hd hcL hcR p m
  refine ⟨K * C, mul_nonneg hK hC, p, ?_⟩
  intro n z hz j hj
  have hzm := (movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL z).mp hz
  have hA : 0 ≤ C * ε n ^ α * L n ^ p :=
    mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hL n)) p)
  have hsource (i : ℕ) (hi : i ≤ m) (R : ℝ) (hR : R / qLength coord z.2.1 ∈ Ioo a b)
      (Y : PressureStream.Plane) :
      ‖iteratedFDeriv ℝ i (f n) (R, (z.2.1, Y))‖ ≤
        (C * ε n ^ α * L n ^ p) * logWeight cL cR a b p (R / qLength coord z.2.1) := by
    have hpoint : (R, (z.2.1, Y)) ∈ st.domain :=
      (movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL _).mpr ⟨hzm.1, hR⟩
    have h := hb n (R, (z.2.1, Y)) hpoint i hi
    rw [movingStrip_majorant_eq U a b cL cR ha hcL hcR ε L hε hεone hL α C p n (R, (z.2.1, Y)) hR]
      at h
    exact h
  have h := hKbound (M n) (v n) (f n) (hf n) (hs n) _ hA z hzm.1 hzm.2 hsource j hj
  rw [movingStrip_majorant_eq U a b cL cR ha hcL hcR ε L hε hεone hL α (K * C) p n z hzm.2]
  exact h.trans_eq (by
    change K * (C * ε n ^ α * L n ^ p) * logWeight cL cR a b p (z.1 / qLength coord z.2.1) =
      (K * C * ε n ^ α * L n ^ p) * logWeight cL cR a b p (z.1 / qLength coord z.2.1)
    ring)

theorem meanClass_moving_localBandJets {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    PhysicalMeanDomain.LocalBandJets U.carrier ε L α f := by
  intro m
  obtain ⟨C, hC, p, hb⟩ := hclass.bounds m
  obtain ⟨W, hW, hweight⟩ := weight_uniform_bound hcL hcR (logLength a b) p
  refine ⟨C * W, mul_nonneg hC hW, p, ?_⟩
  intro n z hz j hj
  have hp : 0 < qLength coord z.2.1 := qLength_pos U.coord_pos U.coord_lt_one (U.time_pos _ hz)
  have hA : 0 ≤ C * ε n ^ α * L n ^ p :=
    mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hL n)) p)
  by_cases hR : z.1 / qLength coord z.2.1 ∈ Ioo a b
  · have hpoint := (movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL z).mpr ⟨hz, hR⟩
    have h := hb n z hpoint j hj
    rw [movingStrip_majorant_eq U a b cL cR ha hcL hcR ε L hε hεone hL α C p n z hR] at h
    exact (h.trans (mul_le_mul_of_nonneg_left (hweight _ (logPosition_mem ha hR)) hA)).trans_eq (by
      ring)
  · have hR' : z.1 ∉ Ioo (qLength coord z.2.1 * a) (qLength coord z.2.1 * b) := by
      intro h
      exact hR ⟨(lt_div_iff₀ hp).mpr (by nlinarith [h.1]), (div_lt_iff₀ hp).mpr (by nlinarith
        [h.2])⟩
    have hell : ContinuousOn (qLength coord) U.carrier :=
      ((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun s hs => U.time_pos s
        hs)).continuousOn
    rw [iteratedFDeriv_zero_outsideGauge_on U.isOpen hell (hf n) (hs n) hz hR' j, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC hW) (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hL n)) p)

theorem localBandJets_unweighted_moving {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hb : PhysicalMeanDomain.LocalBandJets U.carrier ε L α f) :
    UnweightedClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f := by
  let st := movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL
  have hdom : st.domain ⊆ PhysicalMeanDomain.slowDomain U.carrier := fun x hx =>
    ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL x).mp hx).1
  refine ⟨fun _ _ _ => zero_le_one, fun n => (hf n).mono hdom, ?_⟩
  intro m
  obtain ⟨C, hC, k, hbound⟩ := hb m
  refine ⟨C, hC, k, ?_⟩
  intro n z hz j hj
  apply (hbound n z (hdom hz) j hj).trans
  change C * ε n ^ α * L n ^ k ≤ C * ε n ^ α * st.growth n z ^ k * 1
  rw [mul_one]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans (hL n)) (st.slow_le_growth n z) k)
    (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)

theorem meanClass_pressureMass_moving (hab : a < b) {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    UnweightedClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => MeanMomentBounds.liftedPressureMass (f n)) := by
  obtain ⟨c, e, R, hc, hce, hR, hl, hleft, hright, hupp⟩ := qLength_reference_bounds U ha hab
  have hfixed (n : ℕ) : PhysicalMeanDomain.SupportedOn c e U.carrier (f n) := fun x hx hn =>
    ⟨(hleft _ hx).trans (hs n x hx hn).1, (hs n x hx hn).2.trans (hright _ hx)⟩
  exact localBandJets_unweighted_moving U ha hcL hcR ε L hε hεone hL
    (fun n => PhysicalMeanDomain.liftedPressureMass_contDiffOn U.isOpen (hf n) (hfixed n))
    (PhysicalMeanDomain.LocalBandJets.liftedPressureMass hce.le U.isOpen
      (meanClass_moving_localBandJets U ha hcL hcR ε L hε hεone hL hf hs hclass) hf hfixed)

theorem chartKernel_unweighted_moving (g : MeanRankUpdate.ModelPoint → ℝ)
    (hg : ContDiffOn ℝ ∞ g PhysicalCoordinateBounds.positiveTime) :
    UnweightedClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) 0
      (fun _ => MeanRankUpdate.chartKernel coord g) := by
  let st := movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL
  have hdom : st.domain ⊆ PhysicalMeanDomain.slowDomain U.carrier := fun x hx =>
    ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL x).mp hx).1
  have ht : ∀ z ∈ st.domain, MeanRankUpdate.chartInput z ∈ PhysicalCoordinateBounds.positiveTime :=
    fun z hz => U.time_pos z.2.1 (hdom hz)
  apply unweighted_of_finiteJetBounds st _ (MeanRankUpdate.chartKernel_contDiffOn U.coord_pos
    U.coord_lt_one ht hg)
  intro m
  obtain ⟨C, _, hb⟩ := MeanRankUpdate.chartKernel_finiteJetBounds U.coord_pos U.coord_lt_one
    U.qlo_pos
    ht (fun z hz => U.q_mem z.2.1 (hdom hz))
    (fun z hz => moving_radial_bounds U ha (hdom hz)
      ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL z).mp hz).2) hg m
  exact ⟨C, hb⟩

theorem inverseLength_unweighted_moving :
    UnweightedClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) 0
      (fun _ z => (qLength coord z.2.1)⁻¹) := by
  apply chartKernel_unweighted_moving U ha hcL hcR ε L hε hεone hL (fun y => (Real.sqrt y.1)⁻¹)
  intro y hy
  exact ((contDiffAt_fst.sqrt (ne_of_gt hy)).inv (Real.sqrt_pos.mpr hy).ne').contDiffWithinAt

theorem density_meanClass_moving (hab : a < b) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) 0
      (fun _ => density a b hab (qLength coord)) := by
  have hρ := meanClass_profileMap U a b cL cR ha hcL hcR ε L hε hεone hL
    (PhysicalMeanDomain.memClass_restrict ha hcL hcR ε L hε hεone hL U.carrier U.isOpen
      (MeanIncrementBounds.rho_meanClass (P := PressureStream.Plane × PressureStream.Plane)
        ha hab hcL hcR ε L hε hεone hL))
  have hi := inverseLength_unweighted_moving (b := b) U ha hcL hcR ε L hε hεone hL
  have he := MeanIncrementBounds.Class.coefficient_mul hi hρ
  simp only [zero_add] at he
  exact he

include ha in
theorem pressureSource_q_contDiffOn (hab : a < b) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f) :
    ContDiffOn ℝ ∞ (pressureSource a b hab (qLength coord) f)
      (PhysicalMeanDomain.slowDomain U.carrier) := by
  obtain ⟨c, e, R, hc, hce, hR, hl, hleft, hright, hupp⟩ := qLength_reference_bounds U ha hab
  have hfixed : PhysicalMeanDomain.SupportedOn c e U.carrier f := fun x hx hn =>
    ⟨(hleft _ hx).trans (hs x hx hn).1, (hs x hx hn).2.trans (hright _ hx)⟩
  exact hf.sub ((density_contDiffOn hab
    ((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun s hs => U.time_pos s hs)) hl).mul
    (PhysicalMeanDomain.liftedPressureMass_contDiffOn U.isOpen hf hfixed))

include ha in
theorem meanPressure_q_contDiffOn (hab : a < b) (hd : 0 < d) (M : ℝ) (v : PressureStream.Plane)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f) :
    ContDiffOn ℝ ∞ (meanPressure d a b M hab (qLength coord) v f)
      (PhysicalMeanDomain.slowDomain U.carrier) :=
  compactPrimitive_q_contDiffOn U ha hab hd M v (pressureSource_q_contDiffOn U ha hab hf hs)
    (pressureSource_supported hab (ell := qLength coord) (U := U.carrier)
      (fun s hs => qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs)) hs)

include ha in
theorem meanPressure_q_supportedGauge (hab : a < b) (hd : 0 < d) (M : ℝ) (v : PressureStream.Plane)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f) :
    SupportedGauge a b (qLength coord) U.carrier (meanPressure d a b M hab (qLength coord) v f) :=
  compactPrimitive_supportedGauge ha hab hd (qLength coord) v U.isOpen
    (fun s hs => qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs))
    (pressureSource_q_contDiffOn U ha hab hf hs)
    (pressureSource_supported hab (ell := qLength coord) (U := U.carrier)
      (fun s hs => qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs)) hs)

theorem meanClass_pressureSource (hab : a < b) {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => pressureSource a b hab (qLength coord) (f n)) := by
  have hmass := meanClass_pressureMass_moving U ha hcL hcR ε L hε hεone hL hab hf hs hclass
  have hρ := density_meanClass_moving U ha hcL hcR ε L hε hεone hL hab
  have hprod := MeanIncrementBounds.Class.mul_coefficient hρ hmass
  simp only [zero_add] at hprod
  exact MeanIncrementBounds.Class.sub hclass hprod

theorem meanClass_meanPressure (hab : a < b) (hd : 0 < d) {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => meanPressure d a b (M n) hab (qLength coord) (v n) (f n)) := by
  exact meanClass_compactPrimitive U ha hcL hcR ε L hε hεone hL hab hd
    (fun n => pressureSource_q_contDiffOn U ha hab (hf n) (hs n))
    (fun n => pressureSource_supported hab (ell := qLength coord) (U := U.carrier)
      (fun s hs => qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs)) (hs n))
    (meanClass_pressureSource U ha hcL hcR ε L hε hεone hL hab hf hs hclass) M v

end MovingClasses

section Periodicity
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem compactPrimitive_periodicOn (d a b M : ℝ) (ell : S → ℝ) (v : PressureStream.Plane)
    {U : Set S} {f : PressureStream.Lift S → ℝ} (hp : PhysicalMeanDomain.PeriodicOn U f) :
    PhysicalMeanDomain.PeriodicOn U (compactPrimitive d a b M ell v f) := by
  intro R s hs Y k
  have he : (fun q : ℝ => normalizeSource d (ell s * a) f
      (TransportPrimitive.shift M ((0 : S), v)
        (powerChart d (ell s * a) R, (s, Y + ((k.1 : ℝ), (k.2 : ℝ)))) q)) =
      fun q : ℝ => normalizeSource d (ell s * a) f
      (TransportPrimitive.shift M ((0 : S), v)
        (powerChart d (ell s * a) R, (s, Y)) q) := by
    funext q
    simp only [normalizeSource, liftChart, TransportPrimitive.shift,
      Prod.add_def, Prod.smul_def, smul_zero, add_zero]
    simpa only [Prod.add_def, Prod.smul_def, add_right_comm] using
      congrArg (fun u : ℝ => sourceMultiplier d (ell s * a)
        (powerChart d (ell s * a) R + q) • u)
        (hp (inverseChart d (ell s * a) (powerChart d (ell s * a) R + q)) s hs
          (Y + (M * q) • v) k)
  simp only [compactPrimitive, physicalCompact, pullback, liftChart, Function.comp_def,
    TransportPrimitive.compactIntegral, TransportPrimitive.pastIntegral,
      TransportPrimitive.totalIntegral, he]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem pressureSource_periodicOn {a b : ℝ} (hab : a < b) (ell : S → ℝ)
    {U : Set S} {f : PressureStream.Lift S → ℝ} (hp : PhysicalMeanDomain.PeriodicOn U f) :
    PhysicalMeanDomain.PeriodicOn U (pressureSource a b hab ell f) := by
  intro r s hs Y k
  dsimp only [pressureSource, density, radialRatio]
  exact congrArg (fun x : ℝ => x - (ell s)⁻¹ * PressureStream.rho a b hab (r / ell s) *
    PressureStream.pressureMass f s) (hp r s hs Y k)

theorem meanPressure_periodicOn {a b : ℝ} (hab : a < b) (d M : ℝ) (ell : S → ℝ)
    (v : PressureStream.Plane) {U : Set S} {f : PressureStream.Lift S → ℝ}
    (hp : PhysicalMeanDomain.PeriodicOn U f) :
    PhysicalMeanDomain.PeriodicOn U (meanPressure d a b M hab ell v f) :=
  compactPrimitive_periodicOn d a b M ell v (pressureSource_periodicOn hab ell hp)

theorem streamPotential_periodicOn (d a b M : ℝ) (ell : S → ℝ) (v : PressureStream.Plane)
    {U : Set S} {f : PressureStream.Lift S → ℝ} (hp : PhysicalMeanDomain.PeriodicOn U f) :
    PhysicalMeanDomain.PeriodicOn U (streamPotential d a b M ell v f) := by
  have hw : PhysicalMeanDomain.PeriodicOn U (PressureStream.weightedSource f) := by
    intro r s hs Y k
    dsimp only [PressureStream.weightedSource]
    exact congrArg (fun x : ℝ => r * x) (hp r s hs Y k)
  intro r s hs Y k
  exact congrArg (fun x : ℝ => x / r) (compactPrimitive_periodicOn d a b M ell v hw r s hs Y k)

end Periodicity

section MovingSupportClass
open LocalSignedRequest WeightedClasses
variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

theorem localBandJets_meanClass_of_gaugeInteriorSupport {c e α : ℝ}
    (hac : a < c) (heb : e < b) {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge c e (qLength coord) U.carrier (f n))
    (hb : PhysicalMeanDomain.LocalBandJets U.carrier ε L α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f := by
  let st := movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL
  let sb := logStripData (E := PressureStream.Plane × PressureStream.Plane)
    a b cL cR ha hcL hcR ε L hε hεone hL
  have hmem (r : ℝ) (hr : r ∈ Icc c e) : (r, (0 : PressureStream.Plane × PressureStream.Plane)) ∈
    sb.domain :=
    ⟨hac.trans_le hr.1, hr.2.trans_lt heb⟩
  have hcont : ContinuousOn (fun r : ℝ => sb.zeta (r, 0)) (Icc c e) :=
    sb.zeta_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmem
  have hpos (r : ℝ) (hr : r ∈ Icc c e) : 0 < sb.zeta (r, 0) :=
    zeta_pos cL cR (logPosition_mem ha (hmem r hr))
  obtain ⟨δ, hδ, hmargin⟩ := UniformCone.positive_uniform_margin isCompact_Icc hcont hpos
  have hdom : st.domain ⊆ PhysicalMeanDomain.slowDomain U.carrier := fun x hx =>
    ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL x).mp hx).1
  refine ⟨fun _ z hz => st.zeta_nonneg z hz, fun n => (hf n).mono hdom, ?_⟩
  intro m
  obtain ⟨C, hC, k, hbound⟩ := hb m
  refine ⟨C / δ, div_nonneg hC hδ.le, k, ?_⟩
  intro n z hz j hj
  have hzs := hdom hz
  have hEll : 0 < qLength coord z.2.1 := qLength_pos U.coord_pos U.coord_lt_one (U.time_pos _ hzs)
  by_cases hpi : z.1 / qLength coord z.2.1 ∈ Icc c e
  · have hζ : δ ≤ st.zeta z := hmargin (z.1 / qLength coord z.2.1) hpi
    have hgr : L n ^ k ≤ st.growth n z ^ k :=
      pow_le_pow_left₀ (zero_le_one.trans (hL n)) (st.slow_le_growth n z) k
    have hA : 0 ≤ C / δ * ε n ^ α * st.growth n z ^ k :=
      mul_nonneg (mul_nonneg (div_nonneg hC hδ.le) (Real.rpow_pos_of_pos (hε n) α).le)
        (pow_nonneg (st.growth_nonneg n z) _)
    calc
      _ ≤ C * ε n ^ α * L n ^ k := hbound n z hzs j hj
      _ ≤ C * ε n ^ α * st.growth n z ^ k :=
        mul_le_mul_of_nonneg_left hgr (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
      _ = (C / δ * ε n ^ α * st.growth n z ^ k) * δ := by field_simp
      _ ≤ (C / δ * ε n ^ α * st.growth n z ^ k) * st.zeta z := mul_le_mul_of_nonneg_left hζ hA
      _ = _ := rfl
  · have hr : z.1 ∉ Ioo (qLength coord z.2.1 * c) (qLength coord z.2.1 * e) := by
      intro h
      exact hpi ⟨((lt_div_iff₀ hEll).mpr (by nlinarith [h.1])).le,
        ((div_lt_iff₀ hEll).mpr (by nlinarith [h.2])).le⟩
    rw [iteratedFDeriv_zero_outsideGauge_on U.isOpen
      ((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun s hs => U.time_pos s
        hs)).continuousOn
      (hf n) (hs n) hzs hr j, norm_zero]
    exact majorant_nonneg st _ α (div_nonneg hC hδ.le) k n z (st.zeta_nonneg z hz)

theorem meanClass_radialMultiply_moving {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n z => φ z.1 * f n z) := by
  let st := movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL
  have hrad (z : Point) (hz : z ∈ st.domain) : z.1 ∈ Icc (Real.sqrt U.qlo * a) (Real.sqrt U.qhi *
    b) :=
    moving_radial_bounds U ha
      ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL z).mp hz).1
      ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL z).mp hz).2
  have hc : UnweightedClass st 0 (fun _ z => φ z.1) := by
    apply unweighted_of_finiteJetBounds st _ (hφ.comp contDiff_fst).contDiffOn
    intro m
    obtain ⟨C, _, hbound⟩ := cutoff_finiteJet_bound (E := PressureStream.Plane ×
      PressureStream.Plane)
      (Real.sqrt U.qlo * a) (Real.sqrt U.qhi * b) φ hφ m
    exact ⟨C, fun j hj z hz => hbound j hj z (hrad z hz)⟩
  have he := MeanIncrementBounds.Class.coefficient_mul hc hf
  simp only [zero_add] at he
  exact he

theorem meanClass_divideRadius_moving {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => PressureStream.divideRadius (f n)) := by
  let c := Real.sqrt U.qlo * a / 4
  have hc : 0 < c := by dsimp [c]; exact div_pos (mul_pos (Real.sqrt_pos.mpr U.qlo_pos) ha) (by
    norm_num)
  let φ := fun r => (positiveRadius c r)⁻¹
  have hφ : ContDiff ℝ ∞ φ := (positiveRadius_contDiff c).inv (fun r => (positiveRadius_pos hc
    r).ne')
  have hm := meanClass_radialMultiply_moving U ha hcL hcR ε L hε hεone hL hφ hf
  apply MeanRankUpdate.meanClass_congr_on hm
  intro n z hz
  have hrad := moving_radial_bounds U ha
    ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL z).mp hz).1
    ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL z).mp hz).2
  have hcz : 2 * c ≤ z.1 := by dsimp [c]; have := mul_pos (Real.sqrt_pos.mpr U.qlo_pos) ha;
    linarith [hrad.1]
  change f n z / z.1 = (positiveRadius c z.1)⁻¹ * f n z
  rw [positiveRadius_eq_self hc hcz]
  ring

theorem meanClass_streamPotential {d : ℝ} (hab : a < b) (hd : 0 < d)
    {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => streamPotential d a b (M n) (qLength coord) (v n) (f n)) := by
  have hw := meanClass_radialMultiply_moving U ha hcL hcR ε L hε hεone hL contDiff_id hclass
  have hc := meanClass_compactPrimitive U ha hcL hcR ε L hε hεone hL hab hd
    (fun n => contDiffOn_fst.mul (hf n))
    (fun n z hz hn => hs n z hz (right_ne_zero_of_mul hn)) hw M v
  exact meanClass_divideRadius_moving U ha hcL hcR ε L hε hεone hL hc

theorem meanClass_streamBeta {d : ℝ} (hab : a < b) (hd : 0 < d)
    {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) (w : PressureStream.Plane × PressureStream.Plane) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => PressureStream.streamBeta w (streamPotential d a b (M n) (qLength coord) (v n) (f
        n))) := by
  have hp := meanClass_streamPotential U ha hcL hcR ε L hε hεone hL hab hd hf hs hclass M v
  have hD := (hp.directional (0, w)).map (-ContinuousLinearMap.id ℝ ℝ)
  simp only [
    _root_.neg_apply, ContinuousLinearMap.id_apply] at hD ⊢
  exact hD

end MovingSupportClass

section FiberDerivatives
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem fderiv_eq_on_radialFiber {f g : PressureStream.Lift S → ℝ} {z : PressureStream.Lift S}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (he : ∀ r Y, f (r, (z.2.1, Y)) = g (r, (z.2.1, Y))) (r : ℝ) (Y : PressureStream.Plane) :
    fderiv ℝ f z (r, ((0 : S), Y)) = fderiv ℝ g z (r, ((0 : S), Y)) := by
  let L : (ℝ × PressureStream.Plane) →L[ℝ] PressureStream.Lift S :=
    (ContinuousLinearMap.fst ℝ ℝ PressureStream.Plane).prod
      ((0 : (ℝ × PressureStream.Plane) →L[ℝ] S).prod (ContinuousLinearMap.snd ℝ ℝ
        PressureStream.Plane))
  have hi : HasFDerivAt (fun q : ℝ × PressureStream.Plane => (q.1, (z.2.1, q.2))) L (z.1, z.2.2) :=
    hasFDerivAt_fst.prodMk ((hasFDerivAt_const z.2.1 _).prodMk hasFDerivAt_snd)
  have hff := hf.hasFDerivAt.comp (z.1, z.2.2) hi
  have hgg := hg.hasFDerivAt.comp (z.1, z.2.2) hi
  have heq : (f ∘ fun q : ℝ × PressureStream.Plane => (q.1, (z.2.1, q.2))) =
      (g ∘ fun q : ℝ × PressureStream.Plane => (q.1, (z.2.1, q.2))) := by
    funext q
    exact he q.1 q.2
  rw [heq] at hff
  have h := congrArg (fun A : (ℝ × PressureStream.Plane) →L[ℝ] ℝ => A (r, Y)) (hff.unique hgg)
  simpa [L] using h

theorem graphDr_eq_on_radialFiber {f g : PressureStream.Lift S → ℝ} {z : PressureStream.Lift S}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (he : ∀ r Y, f (r, (z.2.1, Y)) = g (r, (z.2.1, Y)))
    (k : ℝ → ℝ) (v : PressureStream.Plane) :
    PressureStream.graphDr k ((0 : S), v) f z = PressureStream.graphDr k ((0 : S), v) g z := by
  simpa only [PressureStream.graphDr, PressureStream.radialVector, Prod.smul_mk, smul_zero] using
    fderiv_eq_on_radialFiber hf hg he 1 (k z.1 • v)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem divideRadius_fiberLocal : PhysicalMeanDomain.FiberLocal (S := S)
  PressureStream.divideRadius := by
  intro f g s he r Y
  exact congrArg (fun x : ℝ => x / r) (he r Y)

variable [FiniteDimensional ℝ S]

theorem divideRadius_contDiffOn {a b : ℝ} (ha : 0 < a) {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : PhysicalMeanDomain.SupportedOn a b U f) :
    ContDiffOn ℝ ∞ (PressureStream.divideRadius f) (PhysicalMeanDomain.slowDomain U) :=
  divideRadius_fiberLocal.contDiffOn_of_supported
    (fun _ hf hs => PressureStream.divideRadius_contDiff ha hf hs) hU hf hs

end FiberDerivatives

section ActualIdentities
open LocalSignedRequest
variable {coord a b d : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d)

include ha hab hd

theorem compactPrimitive_radial_identity (M : ℝ) (v : PressureStream.Plane) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f) {z : Point} (hz : z.2.1 ∈ U.carrier) :
    PressureStream.graphDr (PressureStream.physicalSpeed d M) ((0 : PressureStream.Plane), v)
      (compactPrimitive d a b M (qLength coord) v f) z =
        f z - compactAlias d a b M (qLength coord) v f z := by
  let ell := qLength coord z.2.1
  have hell : 0 < ell := qLength_pos U.coord_pos U.coord_lt_one (U.time_pos _ hz)
  let g := PhysicalMeanDomain.freezeSlow z.2.1 f
  have hg : ContDiff ℝ ∞ g := freezeSlow_contDiff U.isOpen hz hf
  have hgs : RadialAlias.RadiallySupported (ell * a) (ell * b) g :=
    fun p hp => hs (p.1, (z.2.1, p.2.2)) hz hp
  have hleft : DifferentiableAt ℝ (compactPrimitive d a b M (qLength coord) v f) z :=
    ((compactPrimitive_q_contDiffOn U ha hab hd M v hf hs).contDiffAt
      ((PhysicalMeanDomain.slowDomain_open U.isOpen).mem_nhds hz)).differentiableAt (by simp)
  have hright : DifferentiableAt ℝ (physicalCompact d (ell * a) (ell * b) M ((0 :
    PressureStream.Plane), v) g) z :=
    (physicalCompact_contDiff (mul_pos hell ha) (mul_lt_mul_of_pos_left hab hell) hd hg hgs M
      ((0 : PressureStream.Plane), v)).differentiable (by simp) z
  have he : ∀ r Y, compactPrimitive d a b M (qLength coord) v f (r, (z.2.1, Y)) =
      physicalCompact d (ell * a) (ell * b) M ((0 : PressureStream.Plane), v) g (r, (z.2.1, Y)) :=
        by
    intro r Y
    exact PhysicalMeanDomain.physicalCompact_fiberLocal d (ell * a) (ell * b) M v f g z.2.1 (fun _
      _ => rfl) r Y
  rw [graphDr_eq_on_radialFiber hleft hright he]
  rw [PressureStream.graphDr_eq_physical,
    physicalGraphDeriv_physicalCompact_global (mul_pos hell ha) (mul_lt_mul_of_pos_left hab hell)
      hd hg hgs]
  have halias := PhysicalMeanDomain.physicalAlias_fiberLocal d (ell * a) (ell * b) M v g f z.2.1
    (fun _ _ => rfl) z.1 z.2.2
  exact congrArg (fun x : ℝ => f z - x) halias

theorem meanPressure_radial_identity (M : ℝ) (v : PressureStream.Plane) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f) {z : Point} (hz : z.2.1 ∈ U.carrier) :
    PressureStream.graphDr (PressureStream.physicalSpeed d M) ((0 : PressureStream.Plane), v)
      (meanPressure d a b M hab (qLength coord) v f) z =
        f z - density a b hab (qLength coord) z * PressureStream.pressureMass f z.2.1 -
          compactAlias d a b M (qLength coord) v (pressureSource a b hab (qLength coord) f) z :=
  compactPrimitive_radial_identity U ha hab hd M v (pressureSource_q_contDiffOn U ha hab hf hs)
    (pressureSource_supported hab (ell := qLength coord) (U := U.carrier)
      (fun s hs => qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs)) hs) hz

theorem streamPotential_q_contDiffOn (M : ℝ) (v : PressureStream.Plane) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f) :
    ContDiffOn ℝ ∞ (streamPotential d a b M (qLength coord) v f)
      (PhysicalMeanDomain.slowDomain U.carrier) := by
  have hw : SupportedGauge a b (qLength coord) U.carrier (PressureStream.weightedSource f) :=
    fun z hz hn => hs z hz (right_ne_zero_of_mul hn)
  have hIc := compactPrimitive_q_contDiffOn U ha hab hd M v (contDiffOn_fst.mul hf) hw
  have hIcs := compactPrimitive_supportedGauge (M := M) ha hab hd (qLength coord) v U.isOpen
    (fun s hs => qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs)) (contDiffOn_fst.mul hf)
      hw
  obtain ⟨c, e, L, hc, hce, _, hl, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  exact divideRadius_contDiffOn hc U.isOpen hIc (fun z hz hn =>
    ⟨(hleft _ hz).trans (hIcs z hz hn).1, (hIcs z hz hn).2.trans (hright _ hz)⟩)

theorem streamGamma_eq_desired_sub_alias (M : ℝ) (v : PressureStream.Plane) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f) {z : Point} (hz : z.2.1 ∈ U.carrier)
    (hr : z.1 ≠ 0) :
    PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : PressureStream.Plane), v)
      (streamPotential d a b M (qLength coord) v f) z =
        f z - compactAlias d a b M (qLength coord) v (PressureStream.weightedSource f) z / z.1 := by
  have hw : SupportedGauge a b (qLength coord) U.carrier (PressureStream.weightedSource f) :=
    fun z hz hn => hs z hz (right_ne_zero_of_mul hn)
  have hIc := compactPrimitive_q_contDiffOn U ha hab hd M v (contDiffOn_fst.mul hf) hw
  have hId : DifferentiableAt ℝ
      (compactPrimitive d a b M (qLength coord) v (PressureStream.weightedSource f)) z :=
    (hIc.contDiffAt ((PhysicalMeanDomain.slowDomain_open U.isOpen).mem_nhds hz)).differentiableAt
      (by simp)
  change PressureStream.graphDr _ _ (PressureStream.divideRadius _) z +
    PressureStream.divideRadius (PressureStream.divideRadius _) z = _
  change PressureStream.graphDr _ _ (PressureStream.divideRadius _) z +
    PressureStream.divideRadius _ z / z.1 = _
  rw [PressureStream.graphDr_divideRadius (PressureStream.physicalSpeed d M) ((0 :
    PressureStream.Plane), v) hId hr,
    compactPrimitive_radial_identity U ha hab hd M v (f := PressureStream.weightedSource f)
      (contDiffOn_fst.mul hf) hw hz]
  dsimp only [PressureStream.weightedSource]
  field_simp

theorem stream_divergence_zero (M : ℝ) (v : PressureStream.Plane)
    (w : PressureStream.Plane × PressureStream.Plane) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f) {z : Point} (hz : z.2.1 ∈ U.carrier)
    (hr : z.1 ≠ 0) :
    PressureStream.graphDivergence (PressureStream.physicalSpeed d M) ((0 : PressureStream.Plane),
      v) w
      (PressureStream.streamBeta w (streamPotential d a b M (qLength coord) v f))
      (PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : PressureStream.Plane), v)
        (streamPotential d a b M (qLength coord) v f)) z = 0 := by
  have hpot := (streamPotential_q_contDiffOn U ha hab hd M v hf hs).contDiffAt
    ((PhysicalMeanDomain.slowDomain_open U.isOpen).mem_nhds hz)
  exact PressureStream.stream_divergence_zero ((0 : PressureStream.Plane), v) w
    (hpot.of_le (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le)
    ((PressureStream.physicalSpeed_smooth d M hr).differentiableAt (by simp)) hr

end ActualIdentities

section AliasRepresentation
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

noncomputable def cutoffRadialDerivative (d a b : ℝ) (ell : S → ℝ)
    (z : PressureStream.Lift S) : ℝ :=
  (ell z.2.1)⁻¹ * deriv (physicalCutoff d a b) (radialRatio ell z)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem deriv_physicalCutoff_scale {l a b : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (d R : ℝ) :
    deriv (physicalCutoff d (l * a) (l * b)) R =
      l⁻¹ * deriv (physicalCutoff d a b) (R / l) := by
  have he : physicalCutoff d (l * a) (l * b) = fun x => physicalCutoff d a b (x / l) := by
    funext x
    have h := physicalCutoff_scale hl ha hab d (x / l)
    rwa [mul_div_cancel₀ _ hl.ne'] at h
  have hdif := ((physicalCutoff_contDiff ha d b).differentiable (by simp) (R / l)).hasDerivAt.comp R
    ((hasDerivAt_id R).div_const l)
  rw [he]
  calc
    _ = deriv (physicalCutoff d a b) (R / l) * (1 / l) := hdif.deriv
    _ = _ := by ring

theorem compactAlias_eq_movingTotal {a b d M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (ell : S → ℝ) (v : PressureStream.Plane) (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) (hl : 0 < ell z.2.1) :
    compactAlias d a b M ell v f z = cutoffRadialDerivative d a b ell z *
      PressureStream.physicalTotal d (ell z.2.1 * a) M ((0 : S), v) f z := by
  rw [compactAlias, physicalAlias_eq_cutoff_derivative_global (mul_pos hl ha)
    (mul_lt_mul_of_pos_left hab hl) hd]
  rw [deriv_physicalCutoff_scale hl ha hab]
  rfl

theorem physicalTotal_anchor_eq {c a b d M : ℝ} (hc : 0 < c) (hca : c ≤ a)
    (hab : a < b) (hd : 0 < d) (v : S × PressureStream.Plane)
    {f : PressureStream.Lift S → ℝ} (hs : RadialAlias.RadiallySupported a b f)
    (z : PressureStream.Lift S) (hz : a ≤ z.1) :
    PressureStream.physicalTotal d c M v f z = PressureStream.physicalTotal d a M v f z := by
  have ha := hc.trans_le hca
  simp only [PressureStream.physicalTotal, liftChart]
  rw [normalizeSource_anchor_eq hc hca hab hd hs,
    powerChart_eq hc (by linarith) d, powerChart_eq ha (by linarith) d]

theorem compactAlias_reference {c a b d M : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (ell : S → ℝ) (v : PressureStream.Plane)
    {U : Set S} (hl : ∀ s ∈ U, 0 < ell s) (hleft : ∀ s ∈ U, c ≤ ell s * a)
    {f : PressureStream.Lift S → ℝ} (hs : SupportedGauge a b ell U f)
    (z : PressureStream.Lift S) (hz : z.2.1 ∈ U) :
    compactAlias d a b M ell v f z = cutoffRadialDerivative d a b ell z *
      PressureStream.physicalTotal d c M ((0 : S), v) f z := by
  rw [compactAlias_eq_movingTotal ha hab hd ell v f z (hl _ hz)]
  by_cases hR : ell z.2.1 * a ≤ z.1
  · let g := PhysicalMeanDomain.freezeSlow z.2.1 f
    have hgs : RadialAlias.RadiallySupported (ell z.2.1 * a) (ell z.2.1 * b) g :=
      fun p hp => hs (p.1, (z.2.1, p.2.2)) hz hp
    have h := physicalTotal_anchor_eq (M := M) hc (hleft _ hz)
      (mul_lt_mul_of_pos_left hab (hl _ hz)) hd ((0 : S), v) hgs z hR
    rw [physicalTotal_fiberLocal d c M v g f z.2.1 (fun _ _ => rfl) z.1 z.2.2,
      physicalTotal_fiberLocal d (ell z.2.1 * a) M v g f z.2.1 (fun _ _ => rfl) z.1 z.2.2] at h
    exact congrArg (fun t : ℝ => cutoffRadialDerivative d a b ell z * t) h.symm
  · have hsmall : z.1 / ell z.2.1 < a :=
      (div_lt_iff₀ (hl _ hz)).mpr (by nlinarith [lt_of_not_ge hR])
    have he : cutoffRadialDerivative d a b ell z = 0 := by
      simp only [cutoffRadialDerivative, radialRatio, deriv_physicalCutoff_zero_left ha hab hd
        hsmall, mul_zero]
    simp only [he, zero_mul]

theorem cutoffRadialDerivative_contDiffOn {a : ℝ} (ha : 0 < a) (d b : ℝ)
    {ell : S → ℝ} {U : Set S} (hell : ContDiffOn ℝ ∞ ell U) (hl : ∀ s ∈ U, 0 < ell s) :
    ContDiffOn ℝ ∞ (cutoffRadialDerivative d a b ell) (PhysicalMeanDomain.slowDomain U) :=
  ((hell.comp contDiffOn_snd.fst (fun _ hz => hz)).inv (fun _ hz => (hl _ hz).ne')).mul
    (((contDiff_infty_iff_deriv.mp (physicalCutoff_contDiff ha d b)).2).comp_contDiffOn
      (radialRatio_contDiffOn hell hl))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
/-- The derivative of the actual cutoff is supported in one reserved
profile interval, independently of the source and transport frequency. -/
theorem cutoffRadialDerivative_interior_support {a b d : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
  :
    ∃ c e : ℝ, a < c ∧ c < e ∧ e < b ∧ ∀ (ell : S → ℝ) (U : Set S),
      (∀ s ∈ U, 0 < ell s) → SupportedGauge c e ell U (cutoffRadialDerivative d a b ell) := by
  have hb : 0 < b := ha.trans hab
  have haU : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have habU : a ^ d < b ^ d := Real.rpow_lt_rpow ha.le hab hd
  let cU := (2 * a ^ d + b ^ d) / 3
  let eU := (a ^ d + 2 * b ^ d) / 3
  have hacU : a ^ d < cU := by dsimp [cU]; linarith
  have hceU : cU < eU := by dsimp [cU, eU]; linarith
  have hebU : eU < b ^ d := by dsimp [eU]; linarith
  have hcU : 0 < cU := haU.trans hacU
  have heU : 0 < eU := hcU.trans hceU
  let c := cU ^ d⁻¹
  let e := eU ^ d⁻¹
  have hac : a < c := by
    simpa only [Real.rpow_rpow_inv ha.le hd.ne'] using Real.rpow_lt_rpow haU.le hacU (inv_pos.mpr
      hd)
  have hce : c < e := Real.rpow_lt_rpow hcU.le hceU (inv_pos.mpr hd)
  have heb : e < b := by
    simpa only [Real.rpow_rpow_inv hb.le hd.ne'] using Real.rpow_lt_rpow heU.le hebU (inv_pos.mpr
      hd)
  have hcPow : c ^ d = cU := Real.rpow_inv_rpow hcU.le hd.ne'
  have hePow : e ^ d = eU := Real.rpow_inv_rpow heU.le hd.ne'
  have hzeroLeft (r : ℝ) (hr : r < c) : deriv (physicalCutoff d a b) r = 0 := by
    by_cases hra : a ≤ r
    · rw [deriv_physicalCutoff ha (by linarith) d b]
      have hχ : deriv (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d)) (powerChart d a r) = 0 :=
        by
        apply TemporalMeanUpdate.interiorCutoff_deriv_zero_left habU
        rw [powerChart_eq ha (by linarith) d]
        exact (Real.rpow_lt_rpow (ha.trans_le hra).le hr hd).trans_eq hcPow
      rw [hχ, mul_zero]
    · exact deriv_physicalCutoff_zero_left ha hab hd (lt_of_not_ge hra)
  have hzeroRight (r : ℝ) (hr : e < r) : deriv (physicalCutoff d a b) r = 0 := by
    rw [deriv_physicalCutoff ha (by linarith) d b]
    have hχ : deriv (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d)) (powerChart d a r) = 0 := by
      apply TemporalMeanUpdate.interiorCutoff_deriv_zero_right habU
      change eU < powerChart d a r
      rw [powerChart_eq ha (by linarith) d, ← hePow]
      exact Real.rpow_lt_rpow (ha.trans (hac.trans hce)).le hr hd
    rw [hχ, mul_zero]
  refine ⟨c, e, hac, hce, heb, ?_⟩
  intro ell U hl z hz hn
  have hprofile : z.1 / ell z.2.1 ∈ Icc c e := by
    constructor
    · apply le_of_not_gt
      intro hlt
      apply hn
      dsimp only [cutoffRadialDerivative, radialRatio]
      rw [hzeroLeft _ hlt, mul_zero]
    · apply le_of_not_gt
      intro hlt
      apply hn
      dsimp only [cutoffRadialDerivative, radialRatio]
      rw [hzeroRight _ hlt, mul_zero]
  exact ⟨by nlinarith [(le_div_iff₀ (hl _ hz)).mp hprofile.1],
    by nlinarith [(div_le_iff₀ (hl _ hz)).mp hprofile.2]⟩

theorem compactAlias_interior_support {a b d : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d) :
    ∃ c e : ℝ, a < c ∧ c < e ∧ e < b ∧ ∀ (ell : S → ℝ) (U : Set S),
      (∀ s ∈ U, 0 < ell s) → ∀ (M : ℝ) (v : PressureStream.Plane) (f : PressureStream.Lift S → ℝ),
      SupportedGauge c e ell U (compactAlias d a b M ell v f) := by
  obtain ⟨c, e, hac, hce, heb, hs⟩ := cutoffRadialDerivative_interior_support (S := S) ha hab hd
  refine ⟨c, e, hac, hce, heb, ?_⟩
  intro ell U hl M v f z hz hn
  apply hs ell U hl z hz
  intro hzero
  exact hn (by rw [compactAlias_eq_movingTotal ha hab hd ell v f z (hl _ hz), hzero, zero_mul])

end AliasRepresentation

section PressureChanges
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem SupportedGauge.sub {a b : ℝ} {ell : S → ℝ} {U : Set S}
    {f g : PressureStream.Lift S → ℝ} (hf : SupportedGauge a b ell U f)
    (hg : SupportedGauge a b ell U g) : SupportedGauge a b ell U (fun z => f z - g z) := by
  intro z hz hn
  by_cases hzero : f z = 0
  · exact hg z hz (fun hzero' => hn (by simp only [hzero, hzero', sub_self]))
  · exact hf z hz hzero

theorem meanPressure_sub_on {a b d M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (ell : S → ℝ) (v : PressureStream.Plane) {U : Set S} (hU : IsOpen U)
    {f g : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hg : ContDiffOn ℝ ∞ g (PhysicalMeanDomain.slowDomain U))
    (hsf : SupportedGauge a b ell U f) (hsg : SupportedGauge a b ell U g)
    {z : PressureStream.Lift S} (hz : z.2.1 ∈ U) (hl : 0 < ell z.2.1) :
    meanPressure d a b M hab ell v (fun p => f p - g p) z =
      meanPressure d a b M hab ell v f z - meanPressure d a b M hab ell v g z := by
  let F := PhysicalMeanDomain.freezeSlow z.2.1 f
  let G := PhysicalMeanDomain.freezeSlow z.2.1 g
  have hF : ContDiff ℝ ∞ F := freezeSlow_contDiff hU hz hf
  have hG : ContDiff ℝ ∞ G := freezeSlow_contDiff hU hz hg
  have hsF : RadialAlias.RadiallySupported (ell z.2.1 * a) (ell z.2.1 * b) F :=
    fun p hp => hsf (p.1, (z.2.1, p.2.2)) hz hp
  have hsG : RadialAlias.RadiallySupported (ell z.2.1 * a) (ell z.2.1 * b) G :=
    fun p hp => hsg (p.1, (z.2.1, p.2.2)) hz hp
  rw [meanPressure_eq_fixed hab d M ell v _ z hl,
    meanPressure_eq_fixed hab d M ell v f z hl,
    meanPressure_eq_fixed hab d M ell v g z hl]
  have hFval := PhysicalMeanDomain.meanPressure_fiberLocal d (ell z.2.1 * a) (ell z.2.1 * b)
    M (mul_lt_mul_of_pos_left hab hl) v F f z.2.1 (fun _ _ => rfl) z.1 z.2.2
  have hGval := PhysicalMeanDomain.meanPressure_fiberLocal d (ell z.2.1 * a) (ell z.2.1 * b)
    M (mul_lt_mul_of_pos_left hab hl) v G g z.2.1 (fun _ _ => rfl) z.1 z.2.2
  rw [← PhysicalMeanDomain.meanPressure_fiberLocal d (ell z.2.1 * a) (ell z.2.1 * b)
    M (mul_lt_mul_of_pos_left hab hl) v (fun p => F p - G p) (fun p => f p - g p)
    z.2.1 (fun _ _ => rfl) z.1 z.2.2,
    congrFun (MeanIncrementBounds.meanPressure_sub (mul_pos hl ha) (mul_lt_mul_of_pos_left hab hl)
      hd hF hG hsF hsG M v) z, hFval, hGval]

end PressureChanges

section MovingPressureChanges
open LocalSignedRequest WeightedClasses
variable {coord a b cL cR d : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

include hd in
theorem meanClass_meanPressure_change {α : ℝ} {f g : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hg : ∀ n, ContDiffOn ℝ ∞ (g n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hsf : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hsg : ∀ n, SupportedGauge a b (qLength coord) U.carrier (g n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α (f - g))
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n z => meanPressure d a b (M n) hab (qLength coord) (v n) (f n) z -
        meanPressure d a b (M n) hab (qLength coord) (v n) (g n) z) := by
  apply MeanRankUpdate.meanClass_congr_on
    (meanClass_meanPressure U ha hcL hcR ε L hε hεone hL hab hd
      (fun n => (hf n).sub (hg n)) (fun n => (hsf n).sub (hsg n)) hclass M v)
  intro n z hz
  have hzu := ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL z).mp hz).1
  exact (meanPressure_sub_on ha hab hd (qLength coord) (v n) U.isOpen (hf n) (hg n)
    (hsf n) (hsg n) hzu (qLength_pos U.coord_pos U.coord_lt_one (U.time_pos _ hzu))).symm

end MovingPressureChanges

section MovingTemporal
open LocalSignedRequest WeightedClasses
variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

theorem meanClass_liftedTorusAverage_moving {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => MeanMomentBounds.liftedTorusAverage (f n)) := by
  let st := movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL
  refine ⟨hclass.weight_nonneg, fun n => (PhysicalMeanDomain.liftedTorusAverage_contDiffOn
    U.isOpen (hf n)).mono (fun p hp => ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL
      p).mp hp).1), ?_⟩
  intro m
  obtain ⟨C, hC, k, hb⟩ := hclass.bounds m
  refine ⟨C, hC, k, ?_⟩
  intro n p hp j hj
  have hpu := ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL p).mp hp).1
  obtain ⟨c, _, _, hcf, he⟩ := PhysicalMeanDomain.exists_fiber_localization U.isOpen hpu (hf n)
  have hout := PhysicalMeanDomain.liftedTorusAverage_jet_bound hcf j p
    (majorant st (fun _ x => st.zeta x) α C k n p) (fun Y => by
      rw [he.jet_eq j p.1 Y]
      exact hb n (p.1, (p.2.1, Y)) hp j hj)
  rwa [(PhysicalMeanDomain.liftedTorusAverage_fiberLocal.germ he).jet_eq j p.1 p.2.2] at hout

theorem meanClass_centered_moving {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => TemporalMeanUpdate.centered (f n)) :=
  MeanIncrementBounds.Class.sub hclass
    (meanClass_liftedTorusAverage_moving U ha hcL hcR ε L hε hεone hL hf hclass)

theorem meanClass_temporalInverse_moving {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => TemporalMeanUpdate.temporalInverse (f n)) := by
  let st := movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL
  refine ⟨hclass.weight_nonneg, fun n => (PhysicalMeanDomain.temporalInverse_contDiffOn
    U.isOpen (hf n) (hp n)).mono
      (fun p hp => ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL p).mp hp).1), ?_⟩
  intro m
  obtain ⟨K, hK, hbound⟩ := UniformFourierAlias.realInverse_finiteJets
    (P := ℝ × PressureStream.Plane) .temporal m
  obtain ⟨C, hC, k, hb⟩ := hclass.bounds (m + 5)
  refine ⟨K * C, mul_nonneg hK hC, k, ?_⟩
  intro n p hpu j hj
  have hps := ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL p).mp hpu).1
  obtain ⟨c, _, hcs, hcf, he⟩ := PhysicalMeanDomain.exists_fiber_localization U.isOpen hps (hf n)
  let B := majorant st (fun _ x => st.zeta x) α C k n p
  have hB : 0 ≤ B := majorant_nonneg st _ α hC k n p (st.zeta_nonneg p hpu)
  have hin : ∀ i ≤ m + 5, ∀ q ∈ ({(p.1, p.2.1)} : Set (ℝ × PressureStream.Plane)), ∀ Y,
      ‖iteratedFDeriv ℝ i (UniformFourierAlias.toProduct (PhysicalMeanDomain.localize c (f n))) (q,
        Y)‖ ≤ B := by
    intro i hi q hq Y
    rcases mem_singleton_iff.mp hq with rfl
    rw [UniformFourierAlias.norm_iteratedFDeriv_toProduct, he.jet_eq i p.1 Y]
    exact hb n (p.1, (p.2.1, Y)) hpu i hi
  have hper : UniformFourierAlias.ParameterPeriodic
      (UniformFourierAlias.toProduct (PhysicalMeanDomain.localize c (f n))) :=
    fun q => PhysicalMeanDomain.localize_periodic hcs (hp n) q.1 q.2
  have ho := hbound _ {(p.1, p.2.1)} B (UniformFourierAlias.toProduct_smooth hcf)
    hper hB hin j hj (p.1, p.2.1) (mem_singleton _) p.2.2
  rw [← UniformFourierAlias.norm_iteratedFDeriv_fromProduct] at ho
  change ‖iteratedFDeriv ℝ j (TemporalMeanUpdate.temporalInverse (PhysicalMeanDomain.localize c (f
    n))) p‖ ≤ K * B at ho
  rw [(PhysicalMeanDomain.temporalInverse_fiberLocal.germ he).jet_eq j p.1 p.2.2] at ho
  exact ho.trans_eq (by dsimp [B, majorant]; ring)

theorem meanClass_desiredIncrement_moving {h α : ℝ} (hh : 0 ≤ h)
    (hscale : ∀ n, ChartScales.S n ≤ L n) {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => TemporalMeanUpdate.desiredIncrement h n (f n)) := by
  have hc := meanClass_centered_moving U ha hcL hcR ε L hε hεone hL hf hclass
  have hi := meanClass_temporalInverse_moving U ha hcL hcR ε L hε hεone hL
    (fun n => PhysicalMeanDomain.centered_contDiffOn U.isOpen (hf n))
    (fun n => PhysicalMeanDomain.centered_periodicOn (hp n)) hc
  have hm := (TemporalMeanUpdate.meanClass_chartPrefactor_all hh hscale hi).map
    (-ContinuousLinearMap.id ℝ ℝ)
  change MeanClass _ α (fun n z => -TemporalMeanUpdate.chartPrefactor h n *
    TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered (f n)) z)
  simpa only [TemporalMeanUpdate.desiredIncrement, _root_.neg_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, neg_mul] using hm

theorem meanClass_temporalAtIndex_moving {h α : ℝ} (hh : 0 ≤ h)
    (hscale : ∀ n, ChartScales.S n ≤ L n) (index : ℕ → ℕ) (D : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D) {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => MeanChartCompatibility.temporalAtIndex h n (index n) (f n)) :=
  MeanChartCompatibility.meanClass_temporalAtIndex_of_native _ index D hgap
    (meanClass_desiredIncrement_moving U ha hcL hcR ε L hε hεone hL hh hscale hf hp hclass)

end MovingTemporal

section TemporalLocal
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem temporalAtIndex_fiberLocal (h : ℝ) (n i : ℕ) :
    PhysicalMeanDomain.FiberLocal (S := S) (MeanChartCompatibility.temporalAtIndex h n i) := by
  intro f g s he r Y
  rw [MeanChartCompatibility.temporalAtIndex_eq_native,
    MeanChartCompatibility.temporalAtIndex_eq_native]
  exact congrArg (fun z : ℝ => MeanChartCompatibility.commonRatio h n i * z)
    (PhysicalMeanDomain.desiredIncrement_fiberLocal h n f g s he r Y)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem temporalAtIndex_supportedGauge (h : ℝ) (n i : ℕ) {a b : ℝ}
    {ell : S → ℝ} {U : Set S} {f : PressureStream.Lift S → ℝ}
    (hs : SupportedGauge a b ell U f) :
    SupportedGauge a b ell U (MeanChartCompatibility.temporalAtIndex h n i f) := by
  intro z hz hn
  let g := PhysicalMeanDomain.freezeSlow z.2.1 f
  have hgs : RadialAlias.RadiallySupported (ell z.2.1 * a) (ell z.2.1 * b) g :=
    fun p hp => hs (p.1, (z.2.1, p.2.2)) hz hp
  have he := temporalAtIndex_fiberLocal h n i g f z.2.1 (fun _ _ => rfl) z.1 z.2.2
  exact MeanChartCompatibility.temporalAtIndex_supported h n i hgs (fun hzero => hn (he.symm.trans
    hzero))


theorem temporalAtIndex_contDiffOn (h : ℝ) (n i : ℕ) {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U f) :
    ContDiffOn ℝ ∞ (MeanChartCompatibility.temporalAtIndex h n i f) (PhysicalMeanDomain.slowDomain
      U) :=
  (temporalAtIndex_fiberLocal h n i).contDiffOn_of_periodic
    (fun _ hf hp => MeanChartCompatibility.temporalAtIndex_smooth h n i hf hp) hU hf hp

theorem temporalAtIndex_fast_cancellation_on (h : ℝ) (n i : ℕ) {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U f) {z : PressureStream.Lift S} (hz : z.2.1 ∈ U) :
    MeanChartCompatibility.fastAtIndex h n i (MeanChartCompatibility.temporalAtIndex h n i f) z =
      -TemporalMeanUpdate.centered f z := by
  obtain ⟨c, _, hcs, hcf, he⟩ := PhysicalMeanDomain.exists_fiber_localization hU hz hf
  have hD : fderiv ℝ (MeanChartCompatibility.temporalAtIndex h n i (PhysicalMeanDomain.localize c
    f)) z =
      fderiv ℝ (MeanChartCompatibility.temporalAtIndex h n i f) z :=
    (((temporalAtIndex_fiberLocal h n i).germ he).eventuallyEq z.1 z.2.2).fderiv_eq
  have hC := ((PhysicalMeanDomain.centered_fiberLocal.germ he).eventuallyEq z.1 z.2.2).self_of_nhds
  have hout := MeanChartCompatibility.temporalAtIndex_fast_cancellation h n i hcf
    (PhysicalMeanDomain.localize_periodic hcs hp) z
  simpa only [MeanChartCompatibility.fastAtIndex, PressureStream.graphDz, hD, hC] using hout

end TemporalLocal

section AliasClass
open LocalSignedRequest WeightedClasses

noncomputable def cutoffRadialDerivativeModel (d a b : ℝ) (y : MeanRankUpdate.ModelPoint) : ℝ :=
  (Real.sqrt y.1)⁻¹ * deriv (physicalCutoff d a b) (y.2.1 / Real.sqrt y.1)

theorem cutoffRadialDerivativeModel_contDiffOn {a : ℝ} (ha : 0 < a) (d b : ℝ) :
    ContDiffOn ℝ ∞ (cutoffRadialDerivativeModel d a b) PhysicalCoordinateBounds.positiveTime := by
  intro y hy
  have hp : 0 < Real.sqrt y.1 := Real.sqrt_pos.mpr hy
  have hr : ContDiffAt ℝ ∞ (fun x : MeanRankUpdate.ModelPoint => Real.sqrt x.1) y :=
    contDiffAt_fst.sqrt (ne_of_gt hy)
  have hder := (contDiff_infty_iff_deriv.mp (physicalCutoff_contDiff ha d b)).2
  exact ((hr.inv hp.ne').mul (hder.contDiffAt.comp y
    (contDiffAt_snd.fst.div hr hp.ne'))).contDiffWithinAt

theorem cutoffRadialDerivative_q_eq_kernel (coord d a b : ℝ) :
    cutoffRadialDerivative d a b (qLength coord) =
      MeanRankUpdate.chartKernel coord (cutoffRadialDerivativeModel d a b) := rfl

theorem cutoffRadialDerivative_q_finiteJets {coord qlo qhi rlo rhi a : ℝ}
    (hc : 0 < coord) (hc1 : coord < 1) (hqlo : 0 < qlo) (ha : 0 < a) (d b : ℝ)
    {V : Set MeanRankUpdate.ChartPoint}
    (hT : ∀ z ∈ V, MeanRankUpdate.chartInput z ∈ PhysicalCoordinateBounds.positiveTime)
    (hq : ∀ z ∈ V, MeanRankUpdate.chartQ coord z ∈ Icc qlo qhi)
    (hR : ∀ z ∈ V, z.1 ∈ Icc rlo rhi) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ JetBounds.FiniteJetBound m (cutoffRadialDerivative d a b (qLength coord)) V B
      := by
  rw [cutoffRadialDerivative_q_eq_kernel]
  exact MeanRankUpdate.chartKernel_finiteJetBounds hc hc1 hqlo hT hq hR
    (cutoffRadialDerivativeModel_contDiffOn ha d b) m

variable {coord a b d : ℝ} (U : SlowRegion coord) (ha : 0 < a) (hab : a < b) (hd : 0 < d)
include ha hab hd

theorem compactAlias_q_contDiffOn (M : ℝ) (v : PressureStream.Plane) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f) :
    ContDiffOn ℝ ∞ (compactAlias d a b M (qLength coord) v f)
      (PhysicalMeanDomain.slowDomain U.carrier) := by
  obtain ⟨c, e, L, hc, hce, _, hl, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  have hfixed : PhysicalMeanDomain.SupportedOn c e U.carrier f := fun z hz hn =>
    ⟨(hleft _ hz).trans (hs z hz hn).1, (hs z hz hn).2.trans (hright _ hz)⟩
  have hC := cutoffRadialDerivative_contDiffOn ha d b
    ((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun s hs => U.time_pos s hs)) hl
  have hJ := physicalTotal_contDiffOn (M := M) hc hce hd v U.isOpen hf hfixed
  apply (hC.mul hJ).congr
  intro z hz
  exact compactAlias_reference hc ha hab hd (qLength coord) v hl hleft hs z hz

theorem compactAlias_q_supportedGauge (M : ℝ) (v : PressureStream.Plane) (f : Point → ℝ) :
    SupportedGauge a b (qLength coord) U.carrier (compactAlias d a b M (qLength coord) v f) := by
  intro z hz hn
  have hpos := qLength_pos U.coord_pos U.coord_lt_one (U.time_pos _ hz)
  exact physicalAlias_supported (mul_pos hpos ha) (mul_lt_mul_of_pos_left hab hpos) hd M ((0 :
    PressureStream.Plane), v) f hn

theorem localBandJets_compactAlias {ε L : ℕ → ℝ} {α : ℝ} {f : ℕ → Point → ℝ}
    (hε : ∀ n, 0 < ε n) (hL : ∀ n, 1 ≤ L n)
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hb : PhysicalMeanDomain.LocalBandJets U.carrier ε L α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    PhysicalMeanDomain.LocalBandJets U.carrier ε L α
      (fun n => compactAlias d a b (M n) (qLength coord) (v n) (f n)) := by
  obtain ⟨c, e, R, hc, hce, _, hl, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  have hfixed (n : ℕ) : PhysicalMeanDomain.SupportedOn c e U.carrier (f n) := fun z hz hn =>
    ⟨(hleft _ hz).trans (hs n z hz hn).1, (hs n z hz hn).2.trans (hright _ hz)⟩
  have hAfixed (n : ℕ) : PhysicalMeanDomain.SupportedOn c e U.carrier
      (compactAlias d a b (M n) (qLength coord) (v n) (f n)) := fun z hz hn =>
    ⟨(hleft _ hz).trans (compactAlias_q_supportedGauge U ha hab hd (M n) (v n) (f n) z hz hn).1,
      (compactAlias_q_supportedGauge U ha hab hd (M n) (v n) (f n) z hz hn).2.trans (hright _ hz)⟩
  have hC := cutoffRadialDerivative_contDiffOn ha d b
    ((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun s hs => U.time_pos s hs)) hl
  intro m
  obtain ⟨C, hC0, k, hbound⟩ := hb m
  obtain ⟨K, hK, hJbound⟩ := physicalIntegrals_finiteJets_local (S := PressureStream.Plane) hc hce
    hd c e m
  let V : Set Point := {z | z.2.1 ∈ U.carrier ∧ z.1 ∈ Icc c e}
  obtain ⟨B, hB, hBbound⟩ := cutoffRadialDerivative_q_finiteJets U.coord_pos U.coord_lt_one
    U.qlo_pos ha d b
    (V := V) (fun z hz => U.time_pos z.2.1 hz.1) (fun z hz => U.q_mem z.2.1 hz.1) (fun _ hz =>
      hz.2) m
  refine ⟨(2 : ℝ) ^ m * B * K * C, by positivity, k, ?_⟩
  intro n z hz j hj
  have hA : 0 ≤ C * ε n ^ α * L n ^ k :=
    mul_nonneg (mul_nonneg hC0 (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hL n)) k)
  by_cases hr : z.1 ∈ Ioo c e
  · have hJ := physicalTotal_contDiffOn (M := M n) hc hce hd (v n) U.isOpen (hf n) (hfixed n)
    have hlocal : compactAlias d a b (M n) (qLength coord) (v n) (f n) =ᶠ[𝓝 z]
        (fun x => cutoffRadialDerivative d a b (qLength coord) x *
          PressureStream.physicalTotal d c (M n) ((0 : PressureStream.Plane), v n) (f n) x) := by
      filter_upwards [(PhysicalMeanDomain.slowDomain_open U.isOpen).mem_nhds hz] with x hx
      exact compactAlias_reference hc ha hab hd (qLength coord) (v n) hl hleft (hs n) x hx
    rw [MeanRankUpdate.iteratedFDeriv_congr_germ hlocal j]
    have hp := product_jet_bound (PhysicalMeanDomain.slowDomain_open U.isOpen) hC hJ hz hj hB
      (mul_nonneg hK hA) (fun i hi => hBbound i hi z ⟨hz, hr.1.le, hr.2.le⟩)
      (fun i hi => (hJbound U.carrier U.isOpen (M n) (v n) (f n) (hf n) (hfixed n) _ hA z hz
        ⟨hr.1.le, hr.2.le⟩ (fun q hq R hR Y => hbound n (R, (z.2.1, Y)) hz q hq) i hi).2)
    exact hp.trans_eq (by ring)
  · rw [PhysicalMeanDomain.jet_zero_outside U.isOpen (compactAlias_q_contDiffOn U ha hab hd (M n)
    (v n) (hf n) (hs n))
      (hAfixed n) hz hr j, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hL n)) k)

variable {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

theorem meanClass_compactAlias {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => compactAlias d a b (M n) (qLength coord) (v n) (f n)) := by
  obtain ⟨c, e, hac, _, heb, hsup⟩ := compactAlias_interior_support (S := PressureStream.Plane) ha
    hab hd
  exact localBandJets_meanClass_of_gaugeInteriorSupport U ha hcL hcR ε L hε hεone hL hac heb
    (fun n => compactAlias_q_contDiffOn U ha hab hd (M n) (v n) (hf n) (hs n))
    (fun n => hsup (qLength coord) U.carrier
      (fun s hs => qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs)) (M n) (v n) (f n))
    (localBandJets_compactAlias U ha hab hd hε hL hf hs
      (meanClass_moving_localBandJets U ha hcL hcR ε L hε hεone hL hf hs hclass) M v)

theorem meanClass_dividedCompactAlias {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => PressureStream.divideRadius (compactAlias d a b (M n) (qLength coord) (v n) (f n)))
        :=
  meanClass_divideRadius_moving U ha hcL hcR ε L hε hεone hL
    (meanClass_compactAlias U ha hab hd hcL hcR ε L hε hεone hL hf hs hclass M v)

theorem meanClass_streamGamma {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => PressureStream.streamGamma (PressureStream.physicalSpeed d (M n)) ((0 :
        PressureStream.Plane), v n)
        (streamPotential d a b (M n) (qLength coord) (v n) (f n))) := by
  have hw := meanClass_radialMultiply_moving U ha hcL hcR ε L hε hεone hL contDiff_id hclass
  have hA := meanClass_dividedCompactAlias U ha hab hd hcL hcR ε L hε hεone hL
    (f := fun n => PressureStream.weightedSource (f n))
    (fun n => contDiffOn_fst.mul (hf n)) (fun n z hz hn => hs n z hz (right_ne_zero_of_mul hn)) hw
      M v
  apply MeanRankUpdate.meanClass_congr_on (MeanIncrementBounds.Class.sub hclass hA)
  intro n z hz
  have hzm := (movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL z).mp hz
  have hpos := qLength_pos U.coord_pos U.coord_lt_one (U.time_pos _ hzm.1)
  have hr : z.1 ≠ 0 := ne_of_gt (by
    have hp : 0 < z.1 / qLength coord z.2.1 := ha.trans hzm.2.1
    simpa only [zero_mul] using (lt_div_iff₀ hpos).mp hp)
  exact streamGamma_eq_desired_sub_alias U ha hab hd (M n) (v n) (hf n) (hs n) hzm.1 hr

end AliasClass

section MovingStageClasses
open LocalSignedRequest WeightedClasses
variable {coord a b cL cR d : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

include hab hd

theorem meanClass_temporalStreamPotential {h α : ℝ} (hh : 0 ≤ h)
    (hscale : ∀ n, ChartScales.S n ≤ L n) (index : ℕ → ℕ) (D : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D) {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => streamPotential d a b (M n) (qLength coord) (v n)
        (MeanChartCompatibility.temporalAtIndex h n (index n) (f n))) :=
  meanClass_streamPotential U ha hcL hcR ε L hε hεone hL hab hd
    (fun n => temporalAtIndex_contDiffOn h n (index n) U.isOpen (hf n) (hp n))
    (fun n => temporalAtIndex_supportedGauge h n (index n) (hs n))
    (meanClass_temporalAtIndex_moving U ha hcL hcR ε L hε hεone hL hh hscale index D hgap hf hp
      hclass) M v

theorem meanClass_temporalStreamGamma {h α : ℝ} (hh : 0 ≤ h)
    (hscale : ∀ n, ChartScales.S n ≤ L n) (index : ℕ → ℕ) (D : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D) {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => PressureStream.streamGamma (PressureStream.physicalSpeed d (M n)) ((0 :
        PressureStream.Plane), v n)
        (streamPotential d a b (M n) (qLength coord) (v n)
          (MeanChartCompatibility.temporalAtIndex h n (index n) (f n)))) :=
  meanClass_streamGamma U ha hab hd hcL hcR ε L hε hεone hL
    (fun n => temporalAtIndex_contDiffOn h n (index n) U.isOpen (hf n) (hp n))
    (fun n => temporalAtIndex_supportedGauge h n (index n) (hs n))
    (meanClass_temporalAtIndex_moving U ha hcL hcR ε L hε hεone hL hh hscale index D hgap hf hp
      hclass) M v

omit hab hd in
theorem streamBeta_smul_direction {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (w : E) (f : ℝ × E → ℝ) :
    PressureStream.streamBeta (r • w) f = fun z => r • PressureStream.streamBeta w f z := by
  funext z
  change -fderiv ℝ f z ((0 : ℝ), r • w) = r • -fderiv ℝ f z ((0 : ℝ), w)
  rw [show ((0 : ℝ), r • w) = r • ((0 : ℝ), w) by simp]
  simp only [map_smul, smul_neg]

theorem meanClass_scaledTemporalStreamBeta {h α : ℝ} (hh : 0 ≤ h)
    (hscale : ∀ n, ChartScales.S n ≤ L n) (index : ℕ → ℕ) (D : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D) {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) (w : PressureStream.Plane × PressureStream.Plane) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) (α + 1)
      (fun n => PressureStream.streamBeta (ε n • w)
        (streamPotential d a b (M n) (qLength coord) (v n)
          (MeanChartCompatibility.temporalAtIndex h n (index n) (f n)))) := by
  let st := movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL
  have hc := meanClass_temporalAtIndex_moving U ha hcL hcR ε L hε hεone hL hh hscale index D hgap
    hf hp hclass
  have hi := meanClass_streamBeta U ha hcL hcR ε L hε hεone hL hab hd
    (fun n => temporalAtIndex_contDiffOn h n (index n) U.isOpen (hf n) (hp n))
    (fun n => temporalAtIndex_supportedGauge h n (index n) (hs n)) hc M v w
  have hb : BandBound st 1 ε := by
    have he := bandBound_rpow st 1
    simp only [Real.rpow_one] at he
    exact he
  simpa only [streamBeta_smul_direction] using hi.band_smul hb

end MovingStageClasses

section ActualStateClasses
open LocalSignedRequest WeightedClasses
variable {coord cL cR : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)

include hd hell

theorem reconstructState_pressure_class
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) {α : ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (u.gr c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier (u.gr c n))
    (hclass : MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
      hεone hL)
      α (u.gr c)) :
    MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      α (reconstructState g c u).pressure := by
  simpa only [reconstructState, hell] using
    meanClass_meanPressure U ha hcL hcR ε L hε hεone hL g.radial.inner_lt_outer hd hf hs hclass
      g.radial.frequency (fun _ => g.radial.radialDirection)

theorem reconstructState_pressure_change_class
    (c : CorrectionState.Context Point) (u v : CorrectionState.State Point) {α : ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (u.gr c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hg : ∀ n, ContDiffOn ℝ ∞ (v.gr c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hsf : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier (u.gr c n))
    (hsg : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier (v.gr c n))
    (hclass : MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
      hεone hL)
      α (u.gr c - v.gr c)) :
    MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      α ((reconstructState g c u).pressure - (reconstructState g c v).pressure) := by
  have he := meanClass_meanPressure_change U ha g.radial.inner_lt_outer hd hcL hcR ε L hε hεone hL
    hf hg hsf hsg hclass
      g.radial.frequency (fun _ => g.radial.radialDirection)
  simp only [reconstructState, hell] at he ⊢
  exact he

theorem temporalIncrementState_classes
    {h α : ℝ} (hh : 0 ≤ h) (hscale : ∀ n, ChartScales.S n ≤ L n) (index : ℕ → ℕ) (D : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (axial : PressureStream.Plane × PressureStream.Plane)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (heps : c.operators.epsilon = ε)
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsz : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      (u.axialResidual c n))
    (hcθ : MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone
      hL)
      α (u.thetaResidual c))
    (hcz : MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone
      hL)
      α (u.axialResidual c)) :
    MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      (α + 1) (temporalIncrementState g h index axial c u).radial ∧
    MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      α (temporalIncrementState g h index axial c u).angular ∧
    MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      α (temporalIncrementState g h index axial c u).axial := by
  have hB := meanClass_scaledTemporalStreamBeta U ha g.radial.inner_lt_outer hd hcL hcR ε L hε
    hεone hL
    hh hscale index D hgap hz hpz hsz hcz g.radial.frequency (fun _ => g.radial.radialDirection)
      axial
  have hT := meanClass_temporalAtIndex_moving U ha hcL hcR ε L hε hεone hL hh hscale index D hgap
    hθ hpθ hcθ
  have hG := meanClass_temporalStreamGamma U ha g.radial.inner_lt_outer hd hcL hcR ε L hε hεone hL
    hh hscale index D hgap hz hpz hsz hcz g.radial.frequency (fun _ => g.radial.radialDirection)
  simpa only [temporalIncrementState, temporalPotential, hell, heps] using And.intro hB (And.intro
    hT hG)

end ActualStateClasses

section DifferentialSupport
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem fderiv_apply_supportedGauge {a b : ℝ} {ell : S → ℝ} {U : Set S}
    (hU : IsOpen U) (hell : ContinuousOn ell U) {f : PressureStream.Lift S → ℝ}
    (hs : SupportedGauge a b ell U f) (w : PressureStream.Lift S → PressureStream.Lift S) :
    SupportedGauge a b ell U (fun z => fderiv ℝ f z (w z)) := by
  intro z hz hn
  have hsupport := iteratedFDeriv_supportedGauge_fiber hU hell hs hz 1
  apply @hsupport z
  intro hzero
  change iteratedFDeriv ℝ 1 f z = 0 at hzero
  have he := congrArg (fun T : (PressureStream.Lift S) [×1]→L[ℝ] ℝ => T (fun _ => w z)) hzero
  exact hn (by simpa only [iteratedFDeriv_one_apply, _root_.zero_apply] using he)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem divideRadius_supportedGauge {a b : ℝ} {ell : S → ℝ} {U : Set S}
    {f : PressureStream.Lift S → ℝ} (hs : SupportedGauge a b ell U f) :
    SupportedGauge a b ell U (PressureStream.divideRadius f) := by
  intro z hz hn
  exact hs z hz (fun hzero => hn (by simp only [PressureStream.divideRadius, hzero, zero_div]))

theorem streamBeta_supportedGauge {a b : ℝ} {ell : S → ℝ} {U : Set S}
    (hU : IsOpen U) (hell : ContinuousOn ell U) {f : PressureStream.Lift S → ℝ}
    (hs : SupportedGauge a b ell U f) (w : S × PressureStream.Plane) :
    SupportedGauge a b ell U (PressureStream.streamBeta w f) := by
  intro z hz hn
  apply fderiv_apply_supportedGauge hU hell hs (fun _ => (0, w)) z hz
  exact fun hzero => hn (by simp only [PressureStream.streamBeta, PressureStream.graphDz, hzero,
    neg_zero])

theorem streamGamma_supportedGauge {a b : ℝ} {ell : S → ℝ} {U : Set S}
    (hU : IsOpen U) (hell : ContinuousOn ell U) {f : PressureStream.Lift S → ℝ}
    (hs : SupportedGauge a b ell U f) (k : ℝ → ℝ) (v : S × PressureStream.Plane) :
    SupportedGauge a b ell U (PressureStream.streamGamma k v f) := by
  intro z hz hn
  by_contra hnot
  have hD : PressureStream.graphDr k v f z = 0 := by
    by_contra hd
    exact hnot (fderiv_apply_supportedGauge hU hell hs (PressureStream.radialVector k v) z hz hd)
  have hF : f z = 0 := by
    by_contra hf
    exact hnot (hs z hz hf)
  exact hn (by simp only [PressureStream.streamGamma, PressureStream.divideRadius, hD, hF,
    zero_div, add_zero])

theorem streamPotential_supportedGauge {a b d M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (ell : S → ℝ) (v : PressureStream.Plane) {U : Set S} (hU : IsOpen U)
    (hl : ∀ s ∈ U, 0 < ell s) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U)) (hs : SupportedGauge a b ell U f) :
    SupportedGauge a b ell U (streamPotential d a b M ell v f) :=
  divideRadius_supportedGauge (compactPrimitive_supportedGauge (M := M) ha hab hd ell v hU hl
    (contDiffOn_fst.mul hf) (fun z hz hn => hs z hz (right_ne_zero_of_mul hn)))

end DifferentialSupport

section ActualStateIdentities
open LocalSignedRequest
variable {coord : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) (hell : ∀ n, g.length n = qLength coord)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)

include ha hd hell

theorem reconstructState_radial_identity (n : ℕ)
    (hf : ContDiffOn ℝ ∞ (u.gr c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier (u.gr c n))
    {z : Point} (hz : z.2.1 ∈ U.carrier) :
    PressureStream.graphDr (PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n))
      ((0 : PressureStream.Plane), g.radial.radialDirection) ((reconstructState g c u).pressure n)
        z =
        u.gr c n z - density g.radial.inner g.radial.outer g.radial.inner_lt_outer (g.length n) z *
          PressureStream.pressureMass (u.gr c n) z.2.1 -
        compactAlias g.radial.exponent g.radial.inner g.radial.outer (g.radial.frequency n)
          (g.length n) g.radial.radialDirection
          (pressureSource g.radial.inner g.radial.outer g.radial.inner_lt_outer (g.length n) (u.gr
            c n)) z := by
  simpa only [reconstructState, hell] using
    meanPressure_radial_identity U ha g.radial.inner_lt_outer hd (g.radial.frequency n)
      g.radial.radialDirection hf hs hz

theorem temporalAxialDifference_eq_dividedAlias (h : ℝ) (index : ℕ → ℕ) (n : ℕ)
    (hf : ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hp : PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hs : SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier (u.axialResidual c
      n))
    {z : Point} (hz : z.2.1 ∈ U.carrier) (hr : z.1 ≠ 0) :
    temporalAxialDifference g h index c u n z =
      compactAlias g.radial.exponent g.radial.inner g.radial.outer (g.radial.frequency n)
        (g.length n) g.radial.radialDirection
        (PressureStream.weightedSource (MeanChartCompatibility.temporalAtIndex h n (index n)
          (u.axialResidual c n))) z / z.1 := by
  simp only [temporalAxialDifference, temporalPotential, hell]
  rw [streamGamma_eq_desired_sub_alias U ha g.radial.inner_lt_outer hd (g.radial.frequency n)
    g.radial.radialDirection (temporalAtIndex_contDiffOn h n (index n) U.isOpen hf hp)
    (temporalAtIndex_supportedGauge h n (index n) hs) hz hr]
  ring

theorem temporalIncrementState_divergence_zero (h : ℝ) (index : ℕ → ℕ)
    (axial : PressureStream.Plane × PressureStream.Plane) (n : ℕ)
    (hf : ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hp : PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hs : SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier (u.axialResidual c
      n))
    {z : Point} (hz : z.2.1 ∈ U.carrier) (hr : z.1 ≠ 0) :
    PressureStream.graphDivergence (PressureStream.physicalSpeed g.radial.exponent
      (g.radial.frequency n))
      ((0 : PressureStream.Plane), g.radial.radialDirection) (c.operators.epsilon n • axial)
      ((temporalIncrementState g h index axial c u).radial n)
      ((temporalIncrementState g h index axial c u).axial n) z = 0 := by
  simpa only [temporalIncrementState, temporalPotential, hell] using
    stream_divergence_zero U ha g.radial.inner_lt_outer hd (g.radial.frequency n)
      g.radial.radialDirection (c.operators.epsilon n • axial)
      (temporalAtIndex_contDiffOn h n (index n) U.isOpen hf hp)
      (temporalAtIndex_supportedGauge h n (index n) hs) hz hr

theorem temporalIncrementState_supportedGauge (h : ℝ) (index : ℕ → ℕ)
    (axial : PressureStream.Plane × PressureStream.Plane) (n : ℕ)
    (hf : ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hp : PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsz : SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier (u.axialResidual
      c n))
    (hsθ : SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier (u.thetaResidual
      c n)) :
    SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      ((temporalIncrementState g h index axial c u).radial n) ∧
    SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      ((temporalIncrementState g h index axial c u).angular n) ∧
    SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      ((temporalIncrementState g h index axial c u).axial n) := by
  have hL : ContinuousOn (qLength coord) U.carrier :=
    ((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun s hs => U.time_pos s
      hs)).continuousOn
  have hpot := streamPotential_supportedGauge (M := g.radial.frequency n) ha
    g.radial.inner_lt_outer hd
    (qLength coord) g.radial.radialDirection U.isOpen
    (fun s hs => qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs))
    (temporalAtIndex_contDiffOn h n (index n) U.isOpen hf hp)
    (temporalAtIndex_supportedGauge h n (index n) hsz)
  have hB := streamBeta_supportedGauge U.isOpen hL hpot (c.operators.epsilon n • axial)
  have hG := streamGamma_supportedGauge U.isOpen hL hpot
    (PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n)) ((0 :
      PressureStream.Plane), g.radial.radialDirection)
  simpa only [temporalIncrementState, temporalPotential, hell] using
    And.intro hB (And.intro (temporalAtIndex_supportedGauge h n (index n) hsθ) hG)

end ActualStateIdentities

end

end NavierStokes.VariableGaugeMean
