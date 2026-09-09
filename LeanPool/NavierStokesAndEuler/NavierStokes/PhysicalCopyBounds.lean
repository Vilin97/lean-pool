/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalClassBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodizedWaveBounds

@[expose] public section

/-!
# Physical bounds for locally finite native copies

Each native copy retains its own center and its own full oscillatory carrier.
We sum these waves, not their amplitudes under one unwrapped phase.  Closed,
locally finite, disjoint native cells give an actual single-copy germ.  The
physical estimate is then the center-independent single-carrier estimate,
followed by the existing bounded overlap estimate for the outer labels.
-/

noncomputable section

namespace NavierStokes.PhysicalCopyBounds

open Set Function Filter ProblemStatement PhysicalWaveSum
open scoped Topology ContDiff BigOperators

section Germs

variable {X Y E I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E]

/-- Pull back the native cells only near the evaluation point.  Global
continuity of the physical graph at the axis is not needed. -/
theorem copySum_pullback_germ (K : PeriodizedWaveBounds.Cells Y I) (n : ℕ)
    (φ : X → Y) (f : I → X → E)
    (hs : ∀ i x, f i x ≠ 0 → φ x ∈ K.carrier n i)
    {x : X} (hφ : ContinuousAt φ x) {i : I} (hi : φ x ∈ K.carrier n i) :
    (fun y => ∑' k, f k y) =ᶠ[𝓝 x] f i := by
  classical
  have hn := hφ ((K.locallyFinite n).iInter_compl_mem_nhds (K.closed n) (φ x))
  filter_upwards [hn] with y hy
  apply tsum_eq_single i
  intro j hji
  have hxj : φ x ∉ K.carrier n j := fun hxj => hji (K.unique n j i (φ x) hxj hi)
  by_contra hne
  exact (mem_iInter₂.mp hy j hxj) (hs j y hne)

theorem copySum_pullback_zero_germ (K : PeriodizedWaveBounds.Cells Y I) (n : ℕ)
    (φ : X → Y) (f : I → X → E)
    (hs : ∀ i x, f i x ≠ 0 → φ x ∈ K.carrier n i)
    {x : X} (hφ : ContinuousAt φ x) (hi : ∀ i, φ x ∉ K.carrier n i) :
    (fun y => ∑' k, f k y) =ᶠ[𝓝 x] fun _ => 0 := by
  classical
  have hn := hφ ((K.locallyFinite n).iInter_compl_mem_nhds (K.closed n) (φ x))
  filter_upwards [hn] with y hy
  suffices hz : ∀ i, f i y = 0 by simp only [hz, tsum_zero]
  intro i
  by_contra hne
  exact (mem_iInter₂.mp hy i (hi i)) (hs i y hne)

theorem copySum_pullback_germ_cover (K : PeriodizedWaveBounds.Cells Y I) (n : ℕ)
    (φ : X → Y) (f : I → X → E)
    (hs : ∀ i x, f i x ≠ 0 → φ x ∈ K.carrier n i)
    {x : X} (hφ : ContinuousAt φ x) :
    (∃ i, φ x ∈ K.carrier n i ∧ (fun y => ∑' k, f k y) =ᶠ[𝓝 x] f i) ∨
      (fun y => ∑' k, f k y) =ᶠ[𝓝 x] fun _ => 0 := by
  classical
  by_cases hx : ∃ i, φ x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := hx
    exact Or.inl ⟨i, hi, copySum_pullback_germ K n φ f hs hφ hi⟩
  · exact Or.inr (copySum_pullback_zero_germ K n φ f hs hφ (not_exists.mp hx))

end Germs

/-- The lattice copy is a separate index.  In particular, neither the center
nor the phase profiles have to agree between different copies. -/
structure CopyFamily (H : ℕ) (K : Type*) where
  gap : BandLabel → ℕ
  carrier : K → BandLabel → CarrierData
  amplitude : K → WaveIndex H → LiftPoint → ℂ

noncomputable def CopyFamily.copy {H : ℕ} {K : Type*} (f : CopyFamily H K) (k : K) :
    WaveFamily H := ⟨f.gap, f.carrier k, f.amplitude k⟩

noncomputable def CopyFamily.term {H : ℕ} {K : Type*} (f : CopyFamily H K)
    (a h r0 : ℝ) (I : WaveIndex H) (k : K) : SpaceTime → ℂ :=
  (f.copy k).term a h r0 I

/-- Sum full local carriers, including their individual phases. -/
noncomputable def CopyFamily.periodized {H : ℕ} {K : Type*} (f : CopyFamily H K)
    (a h r0 : ℝ) (I : WaveIndex H) (w : SpaceTime) : ℂ :=
  ∑' k, f.term a h r0 I k w

noncomputable def CopyFamily.sum {H : ℕ} {K : Type*} (f : CopyFamily H K)
    (a h r0 : ℝ) (w : SpaceTime) : ℂ :=
  ∑ᶠ I, f.periodized a h r0 I w

/-- The old single-copy regularity hypotheses are imposed separately on
each actual copy.  No support condition is imposed using one center for the
whole periodized amplitude. -/
structure RegularFamily {H : ℕ} {K : Type*} (f : CopyFamily H K)
    (a b h r0 Z : ℝ) (Δ : ℕ) : Prop where
  copy : ∀ k, PhysicalWaveSum.RegularFamily (f.copy k) a b h r0 Z Δ

/-- Native support cells can depend on the outer label.  Their index is
independent of both the harmonic and the physical point. -/
structure SupportCells {H : ℕ} {K : Type*} (f : CopyFamily H K) where
  cells : BandLabel → PeriodizedWaveBounds.Cells LiftPoint K
  support : ∀ I k, support (f.amplitude k I) ⊆ (cells I.1).carrier I.1.val.1 k

variable {H Δ : ℕ} {K : Type*} {f : CopyFamily H K} {a b h r0 Z : ℝ}

theorem RegularFamily.term_smooth (hr : RegularFamily f a b h r0 Z Δ)
    (ha : 0 < a) (I : WaveIndex H) (k : K) : ContDiff ℝ ∞ (f.term a h r0 I k) :=
  (hr.copy k).term_smooth ha I

theorem SupportCells.term_mem (hc : SupportCells f) (I : WaveIndex H) (k : K)
    (w : SpaceTime) (hw : f.term a h r0 I k w ≠ 0) :
    commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k :=
  hc.support I k (globalWave_ne_zero_amp hw)

/-- Off the fixed radial annulus, all copies vanish on one common
neighborhood.  This also handles the axis without a smooth graph there. -/
theorem RegularFamily.periodized_zero_off_annulus (hr : RegularFamily f a b h r0 Z Δ)
    (I : WaveIndex H) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial I.1.val.1 w ∉ PhysicalGraphBounds.annulus a b) :
    f.periodized a h r0 I =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [(PhysicalGraphBounds.scaledRadial I.1.val.1).continuous.continuousAt
    ((PhysicalGraphBounds.isCompact_annulus a b).isClosed.isOpen_compl.mem_nhds hw)] with y hy
  suffices hz : ∀ k, f.term a h r0 I k y = 0 by
    simp only [CopyFamily.periodized, hz, tsum_zero]
  intro k
  apply globalWave_eq_zero
  by_contra hn
  exact hy ((hr.copy k).geometry_support I y hn).1

theorem commonLift_continuousAt_of_annulus (ha : 0 < a) (n d : ℕ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b) :
    ContinuousAt (commonLift h n d) w := by
  apply (commonLift_smoothAt h n d ?_).continuousAt
  exact PhysicalGraphBounds.scaledRadial_ne_zero
    (PhysicalGraphBounds.annulus_axisFree ha hw)

theorem RegularFamily.periodized_germ_cover (hr : RegularFamily f a b h r0 Z Δ)
    (hc : SupportCells f) (ha : 0 < a) (I : WaveIndex H) (w : SpaceTime) :
    (∃ k, commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k ∧
      f.periodized a h r0 I =ᶠ[𝓝 w] f.term a h r0 I k) ∨
      f.periodized a h r0 I =ᶠ[𝓝 w] fun _ => 0 := by
  classical
  by_cases hann : PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b
  · exact copySum_pullback_germ_cover (hc.cells I.1) I.1.val.1
      (commonLift h I.1.val.1 (f.gap I.1)) (f.term a h r0 I)
      (hc.term_mem I) (commonLift_continuousAt_of_annulus ha _ _ hann)
  · exact Or.inr (hr.periodized_zero_off_annulus I hann)

theorem RegularFamily.periodized_smooth (hr : RegularFamily f a b h r0 Z Δ)
    (hc : SupportCells f) (ha : 0 < a) (I : WaveIndex H) :
    ContDiff ℝ ∞ (f.periodized a h r0 I) := by
  apply contDiff_iff_contDiffAt.mpr
  intro w
  rcases hr.periodized_germ_cover hc ha I w with ⟨k, _, hg⟩ | hg
  · exact (hr.term_smooth ha I k).contDiffAt.congr_of_eventuallyEq hg
  · exact contDiffAt_const.congr_of_eventuallyEq hg

/-- On a specified native copy cell, the full sum equals that full copy.
The identity keeps the copy's own phase as well as its amplitude. -/
theorem SupportCells.periodized_eq (hc : SupportCells f) (I : WaveIndex H) (k : K)
    (w : SpaceTime)
    (hk : commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k) :
    f.periodized a h r0 I w = f.term a h r0 I k w := by
  classical
  apply tsum_eq_single k
  intro j hj
  by_contra hn
  exact hj ((hc.cells I.1).unique _ j k _ (hc.term_mem I j w hn) hk)

theorem RegularFamily.periodized_germ_of_cell (hr : RegularFamily f a b h r0 Z Δ)
    (hc : SupportCells f) (ha : 0 < a) (I : WaveIndex H) (k : K) {w : SpaceTime}
    (hk : commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k) :
    f.periodized a h r0 I =ᶠ[𝓝 w] f.term a h r0 I k := by
  classical
  by_cases hann : PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b
  · exact copySum_pullback_germ (hc.cells I.1) I.1.val.1
      (commonLift h I.1.val.1 (f.gap I.1)) (f.term a h r0 I)
      (hc.term_mem I) (commonLift_continuousAt_of_annulus ha _ _ hann) hk
  · exact (hr.periodized_zero_off_annulus I hann).trans
      (globalWave_eventually_zero_off_annulus (f.carrier k I.1) (f.amplitude k I) I.2.val
        (fun y hy => ((hr.copy k).geometry_support I y hy).1) hann).symm

/-- Actual full derivative tensors agree with the selected local copy. -/
theorem RegularFamily.periodized_jet_eq (hr : RegularFamily f a b h r0 Z Δ)
    (hc : SupportCells f) (ha : 0 < a) (I : WaveIndex H) (k : K) {w : SpaceTime}
    (hk : commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k)
    (m : ℕ) :
    iteratedFDeriv ℝ m (f.periodized a h r0 I) w =
      iteratedFDeriv ℝ m (f.term a h r0 I k) w :=
  iteratedFDeriv_eq_of_eventuallyEq (hr.periodized_germ_of_cell hc ha I k hk) m

theorem RegularFamily.periodized_support (hr : RegularFamily f a b h r0 Z Δ)
    (I : WaveIndex H) (w : SpaceTime) (hw : w ∈ preterminal)
    (hn : f.periodized a h r0 I w ≠ 0) :
    physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val := by
  classical
  by_contra hout
  apply hn
  suffices hz : ∀ k, f.term a h r0 I k w = 0 by
    simp only [CopyFamily.periodized, hz, tsum_zero]
  intro k
  by_contra hne
  exact hout ((hr.copy k).term_support I w hw hne)

theorem RegularFamily.sum_smooth (hr : RegularFamily f a b h r0 Z Δ)
    (hc : SupportCells f) (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (f.sum a h r0) preterminal :=
  masked_finsum_smooth hh hh1 (f.periodized a h r0)
    (fun I _ _ => (hr.periodized_smooth hc ha I).contDiffAt) hr.periodized_support

theorem RegularFamily.sum_locally_finite (hr : RegularFamily f a b h r0 Z Δ)
    (hh : 0 < h) (hh1 : h < 1 / 2) {w : SpaceTime} (hw : w ∈ preterminal) :
    ∃ s : Finset (WaveIndex H), s.card ≤ 2250 * (2 * H + 1) ∧
      f.sum a h r0 =ᶠ[𝓝 w] fun y => ∑ I ∈ s, f.periodized a h r0 I y := by
  obtain ⟨s, hs, he⟩ := masked_finsum_eventually hh hh1 (f.periodized a h r0)
    hr.periodized_support hw
  exact ⟨s, waveRegion_card_le (physicalQ_pos hh hh1 hw) s (fun I hI => (hs I).mp hI), he⟩

/-- Closed-cell membership holds at every point where a copy can have a
nonzero jet, including the boundary of its amplitude support. -/
theorem SupportCells.term_tsupport_mem (hc : SupportCells f)
    (ha : 0 < a) (I : WaveIndex H) (k : K) {w : SpaceTime}
    (hann : PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b)
    (hw : w ∈ tsupport (f.term a h r0 I k)) :
    commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k :=
  closed_property_on_tsupport isOpen_univ (mem_univ w)
    (commonLift_continuousAt_of_annulus ha _ _ hann) ((hc.cells I.1).closed _ k)
    (fun y _ hy => hc.term_mem I k y hy) hw

/-- Only native jets on a copy's own closed cell are used.  No bounds for
uncut data far from that copy are required. -/
structure LocalStrippedClass (f : CopyFamily H K) (hc : SupportCells f)
    (a b h r0 P A B g eAmp eBase : ℝ) (m : ℕ) : Prop where
  parameters : ∀ k L, |(f.carrier k L).angular| ≤ P ∧
    |(f.carrier k L).axial| ≤ P ∧ |(f.carrier k L).radial| ≤ P
  amplitude : ∀ k (I : WaveIndex H) (w : SpaceTime), w ∈ preterminal →
    physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k →
    ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f.amplitude k I) (commonLift h I.1.val.1 (f.gap I.1) w)‖ ≤
      A * ChartScales.Q I.1.val.1 ^ g * ChartScales.S I.1.val.1 ^ eAmp
  base_F : ∀ k (I : WaveIndex H) (w : SpaceTime), w ∈ preterminal →
    physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart →
    ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f.carrier k I.1).F
      (PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
        (ChartScales.timeCoefficient h I.1.val.1) (f.carrier k I.1).center r0
        (PhysicalGraphBounds.physicalLift h I.1.val.1 w)).1‖ ≤ B * ChartScales.S I.1.val.1 ^ eBase
  base_G : ∀ k (I : WaveIndex H) (w : SpaceTime), w ∈ preterminal →
    physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart →
    ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f.carrier k I.1).G
      (PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
        (ChartScales.timeCoefficient h I.1.val.1) (f.carrier k I.1).center r0
        (PhysicalGraphBounds.physicalLift h I.1.val.1 w)).1‖ ≤ B * ChartScales.S I.1.val.1 ^ eBase

/-- The number of native copies does not enter the constant or the power
loss.  At a physical point the actual wave has just one copy germ. -/
theorem physical_sum_jet_bound {h a b Z r0 P B eBase : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (H Δ m : ℕ) (g eAmp A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : CopyFamily H K,
      RegularFamily f a b h r0 Z Δ → ∀ hc : SupportCells f,
      LocalStrippedClass f hc a b h r0 P A B g eAmp eBase m →
      ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (f.sum a h r0) w‖ ≤
        C * physicalQ h w ^ (g - PhysicalGraphBounds.waveLoss h m) := by
  obtain ⟨C, hC, hpoint⟩ := common_carrier_physical_bound (b := b) hh.le hh1.le ha
    hZ hr0 hP hB heBase Δ m g eAmp A (H : ℝ) hA (Nat.cast_nonneg H)
  refine ⟨((2250 * (2 * H + 1) : ℕ) : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro f hr hc hb w hw ht
  have hq := physicalQ_pos hh hh1 hw
  have hcopy : ∀ (I : WaveIndex H),
      physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val → ∀ k,
      ‖iteratedFDeriv ℝ m (f.term a h r0 I k) w‖ ≤
        C * physicalQ h w ^ (g - PhysicalGraphBounds.waveLoss h m) := by
    intro I hregion k
    by_cases hs : w ∈ tsupport (f.term a h r0 I k)
    · have hgeo := globalWave_tsupport_geometry (f.carrier k I.1) (f.amplitude k I) I.2.val
        ((hr.copy k).geometry_support I) hs
      have hcell := hc.term_tsupport_mem ha I k hgeo.1 hs
      obtain ⟨mode, hmode⟩ := (hr.copy k).angular_integer I.1
      let chart := chooseChart a (PhysicalGraphBounds.scaledRadial I.1.val.1 w)
      have hchart : PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart
        :=
        chooseChart_valid ha hgeo.1
      have he := globalWave_eventually_common (r0 := r0) ha I.1.val.1 (f.gap I.1)
        (f.carrier k I.1) (f.amplitude k I) I.2.val mode hmode
        (fun y hy => ((hr.copy k).geometry_support I y hy).1) chart hchart
      change ‖iteratedFDeriv ℝ m (globalWave a h I.1.val.1 (f.gap I.1) r0
        (f.carrier k I.1) (f.amplitude k I) I.2.val) w‖ ≤ _
      rw [iteratedFDeriv_eq_of_eventuallyEq he m]
      have hband := labelRegion_active_relation hregion
      exact hpoint I.1.val.1 I.1.property (f.gap I.1) ((hr.copy k).gap_le I.1)
        w hgeo.1 ht hgeo.2.1 (physicalQ h w) hq hband.1 hband.2
        ((f.carrier k I.1).withChart chart) (f.amplitude k I) I.2.val
        (hb.parameters k I.1).1 (hb.parameters k I.1).2.1 (hb.parameters k I.1).2.2 hgeo.2.2
        ((hr.copy k).amplitude_smooth I) ((hr.copy k).F_smooth I.1)
        ((hr.copy k).G_smooth I.1) (harmonic_bound I.2)
        (hb.amplitude k I w hw hregion hgeo.1 hcell)
        (hb.base_F k I w hw hregion hgeo.1 hcell chart hchart)
        (hb.base_G k I w hw hregion hgeo.1 hcell chart hchart)
    · rw [jet_zero_off_tsupport _ _ hs, norm_zero]
      positivity
  have hsum := masked_finsum_jet_bound hh hh1 (f.periodized a h r0)
    (fun I _ _ => (hr.periodized_smooth hc ha I).contDiffAt) hr.periodized_support hw m
    (B := C * physicalQ h w ^ (g - PhysicalGraphBounds.waveLoss h m)) (by positivity)
  refine (hsum ?_).trans_eq (by ring)
  intro I hregion
  rcases hr.periodized_germ_cover hc ha I w with ⟨k, _, hg⟩ | hg
  · rw [iteratedFDeriv_eq_of_eventuallyEq hg m]
    exact hcopy I hregion k
  · rw [iteratedFDeriv_eq_of_eventuallyEq hg m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity

section WeightedInputs

open WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {ι : Type*}

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

/-- Actual cutoff amplitudes, pulled from their weighted native coefficient
through the common-coordinate map.  Only the map's positive jets are bounded;
its values and the copy centers may be unbounded. -/
structure CommonChart (f : CopyFamily H K) (hc : SupportCells f)
    (a b h σ : ℝ) (source : ι → ℕ → D → ℂ) where
  sourceIndex : K → WaveIndex H → ι
  map : K → WaveIndex H → LiftPoint → D
  domain : K → WaveIndex H → Set LiftPoint
  open_domain : ∀ k I, IsOpen (domain k I)
  smooth : ∀ k I, ContDiffOn ℝ ∞ (map k I) (domain k I)
  positive_jets : ∀ m : ℕ, ∃ B : ℝ, 1 ≤ B ∧ ∃ q : ℕ,
    ∀ k I x, x ∈ domain k I → ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j (map k I) x‖ ≤ B * ChartScales.S I.1.val.1 ^ q
  amplitude_eq : ∀ k I, f.amplitude k I = fun x =>
    (ChartScales.Q I.1.val.1 ^ σ) • source (sourceIndex k I) I.1.val.1 (map k I x)
  contains : ∀ k I z, z ∈ preterminal →
    physicalParams h z ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) z ∈ (hc.cells I.1).carrier I.1.val.1 k →
    commonLift h I.1.val.1 (f.gap I.1) z ∈ domain k I

/-- The native weighted bound is converted using the genuine higher chain
rule.  The same constants work for every label and every native copy. -/
theorem CommonChart.amplitude_bound {s : StripData D} {α σ : ℝ}
    {w : ι → ℕ → D → ℝ} {source : ι → ℕ → D → ℂ}
    (hs : PhysicalClassBounds.SourceBounds s h α w source) {hc : SupportCells f}
    (hchart : CommonChart f hc a b h σ source) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ k I x, x ∈ hchart.domain k I → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f.amplitude k I) x‖ ≤
        A * ChartScales.Q I.1.val.1 ^ (h * α + σ) * ChartScales.S I.1.val.1 ^ p := by
  obtain ⟨A, hA, p, hb⟩ := hs.chart_bound m
  obtain ⟨B, hB, q, hq⟩ := hchart.positive_jets m
  refine ⟨(m.factorial : ℝ) * A * B ^ m, by positivity, p + q * m, ?_⟩
  intro k I x hx j hj
  have hS : 1 ≤ ChartScales.S I.1.val.1 := PhysicalGraphBounds.S_ge_one (by have := I.1.property;
    omega)
  have hQ := ChartScales.Q_pos I.1.val.1
  have hS0 : 0 ≤ ChartScales.S I.1.val.1 := zero_le_one.trans hS
  have hA0 : 0 ≤ A * ChartScales.Q I.1.val.1 ^ (h * α) * ChartScales.S I.1.val.1 ^ p := by
    positivity
  have hB0 : 1 ≤ B * ChartScales.S I.1.val.1 ^ q :=
    one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hS)
  have hjb := PhysicalClassBounds.composition_jet_bound
    (hs.smooth (hchart.sourceIndex k I) I.1.val.1)
    (hchart.open_domain k I) (hchart.smooth k I) hx m hA0 hB0
    (fun j hj => hb (hchart.sourceIndex k I) I.1.val.1 I.1.property (hchart.map k I x) j hj)
    (fun j hj hjm => hq k I x hx j hj hjm) j hj
  have hcomp : ContDiffAt ℝ ∞ (source (hchart.sourceIndex k I) I.1.val.1 ∘ hchart.map k I) x :=
    (hs.smooth (hchart.sourceIndex k I) I.1.val.1).contDiffAt.comp x
      ((hchart.smooth k I).contDiffAt ((hchart.open_domain k I).mem_nhds hx))
  rw [hchart.amplitude_eq k I]
  change ‖iteratedFDeriv ℝ j (fun x => (ChartScales.Q I.1.val.1 ^ σ) •
    (source (hchart.sourceIndex k I) I.1.val.1 ∘ hchart.map k I) x) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hcomp.of_le (nat_le_infty j)),
    norm_smul (ChartScales.Q I.1.val.1 ^ σ)
      (iteratedFDeriv ℝ j (source (hchart.sourceIndex k I) I.1.val.1 ∘ hchart.map k I) x),
    Real.norm_of_nonneg (Real.rpow_pos_of_pos hQ σ).le]
  calc
    _ ≤ ChartScales.Q I.1.val.1 ^ σ * ((m.factorial : ℝ) *
        (A * ChartScales.Q I.1.val.1 ^ (h * α) * ChartScales.S I.1.val.1 ^ p) *
        (B * ChartScales.S I.1.val.1 ^ q) ^ m) :=
      mul_le_mul_of_nonneg_left hjb (Real.rpow_pos_of_pos hQ σ).le
    _ = _ := by rw [Real.rpow_add hQ, pow_add, mul_pow, ← pow_mul]; ring

noncomputable def copyBandDomain {V : Type*} [NormedAddCommGroup V]
    (U : K → BandLabel → Set V) (hU : ∀ k L, IsOpen (U k L)) :
    PhaseJetBounds.Domain (K × BandLabel) V where
  scale i := ChartScales.S i.2.val.1
  carrier i := U i.1 i.2
  isOpen i := hU i.1 i.2
  one_le_scale i := PhysicalGraphBounds.S_ge_one (by have := i.2.property; omega)

/-- The carrier profiles are estimated on their actual local slow regions.
The regions need contain a point only when that point belongs to this copy. -/
structure CarrierBounds (f : CopyFamily H K) (hc : SupportCells f) (a b h r0 : ℝ) where
  region : K → BandLabel → Set PhysicalGraphBounds.Slow
  open_region : ∀ k L, IsOpen (region k L)
  jets : PhaseJetBounds.PolynomialJets (copyBandDomain region open_region)
    (fun i x => ((f.carrier i.1 i.2).F x, (f.carrier i.1 i.2).G x))
  contains : ∀ k (I : WaveIndex H) z, z ∈ preterminal →
    physicalParams h z ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) z ∈ (hc.cells I.1).carrier I.1.val.1 k →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PolarCharts.chartDomain a chart →
    (PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
      (ChartScales.timeCoefficient h I.1.val.1) (f.carrier k I.1).center r0
      (PhysicalGraphBounds.physicalLift h I.1.val.1 z)).1 ∈ region k I.1

theorem CarrierBounds.profile_bound {hc : SupportCells f}
    (hb : CarrierBounds f hc a b h r0) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ p : ℕ, ∀ k L x, x ∈ hb.region k L → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f.carrier k L).F x‖ ≤ B * ChartScales.S L.val.1 ^ p ∧
      ‖iteratedFDeriv ℝ j (f.carrier k L).G x‖ ≤ B * ChartScales.S L.val.1 ^ p := by
  obtain ⟨B, hB, p, hp⟩ := hb.jets.bound m
  refine ⟨B, hB, p, ?_⟩
  intro k L x hx j hj
  have hpair := (hb.jets.smooth (k, L)).contDiffAt ((hb.open_region k L).mem_nhds hx)
  have he := hp (k, L) j hj x hx
  rw [PhysicalGraphBounds.iteratedFDeriv_pair
    (hpair.fst.of_le (nat_le_infty j)) (hpair.snd.of_le (nat_le_infty j)),
    ContinuousMultilinearMap.opNorm_prod] at he
  exact ⟨(le_max_left _ _).trans he, (le_max_right _ _).trans he⟩

/-- Lower weighted coefficient classes and actual phase jets supply all
inputs of the physical theorem; no physical derivative estimate is assumed. -/
theorem localStrippedClass {s : StripData D} {α σ P : ℝ}
    {w : ι → ℕ → D → ℝ} {source : ι → ℕ → D → ℂ}
    (hs : PhysicalClassBounds.SourceBounds s h α w source) {hc : SupportCells f}
    (hchart : CommonChart f hc a b h σ source) (hb : CarrierBounds f hc a b h r0)
    (hp : ∀ k L, |(f.carrier k L).angular| ≤ P ∧
      |(f.carrier k L).axial| ≤ P ∧ |(f.carrier k L).radial| ≤ P) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ B : ℝ, 1 ≤ B ∧ ∃ p q : ℕ,
      LocalStrippedClass f hc a b h r0 P A B (h * α + σ) p q m := by
  obtain ⟨A, hA, p, hAp⟩ := hchart.amplitude_bound hs m
  obtain ⟨B, hB, q, hBq⟩ := hb.profile_bound m
  refine ⟨A, hA, B, hB, p, q, hp, ?_, ?_, ?_⟩
  · intro k I z hz hregion hann hcell j hj
    simpa only [Real.rpow_natCast] using
      hAp k I _ (hchart.contains k I z hz hregion hann hcell) j hj
  · intro k I z hz hregion hann hcell chart hpolar j hj
    simpa only [Real.rpow_natCast] using
      (hBq k I.1 _ (hb.contains k I z hz hregion hann hcell chart hpolar) j hj).1
  · intro k I z hz hregion hann hcell chart hpolar j hj
    simpa only [Real.rpow_natCast] using
      (hBq k I.1 _ (hb.contains k I z hz hregion hann hcell chart hpolar) j hj).2

/-- All actual physical jets of the full copy and label sum, from the lower
weighted class.  Slow polynomial degrees and copy count do not enter the
derivative-loss function. -/
theorem physical_sum_jet_bound_of_weighted {s : StripData D} {α σ P : ℝ}
    {w : ι → ℕ → D → ℝ} {source : ι → ℕ → D → ℂ}
    (hs : PhysicalClassBounds.SourceBounds s h α w source) {hc : SupportCells f}
    (hchart : CommonChart f hc a b h σ source) (hb : CarrierBounds f hc a b h r0)
    (hr : RegularFamily f a b h r0 Z Δ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0)
    (hP : 1 ≤ P) (hp : ∀ k L, |(f.carrier k L).angular| ≤ P ∧
      |(f.carrier k L).axial| ≤ P ∧ |(f.carrier k L).radial| ≤ P) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : SpaceTime,
      z ∈ preterminal → |z.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (f.sum a h r0) z‖ ≤
        C * physicalQ h z ^ (h * α - PhysicalClassBounds.physicalLoss h σ m) := by
  obtain ⟨A, hA, B, hB, p, q, hclass⟩ := localStrippedClass hs hchart hb hp m
  obtain ⟨C, hC, hbound⟩ := physical_sum_jet_bound (K := K)
    (b := b) hh hh1 ha hZ hr0 hP hB (Nat.cast_nonneg q) H Δ m
      (h * α + σ) p A hA
  refine ⟨C, hC, ?_⟩
  intro z hz ht
  convert! hbound f hr hc hclass z hz ht using 1
  congr 2
  unfold PhysicalClassBounds.physicalLoss
  ring

end WeightedInputs

/-! ## Literal native cells and their lattice centers -/

section NativeCells

open CommonCoverSolve

noncomputable def nativeCenter (g : Geometry) (k : TorusInverse.Frequency) : Plane :=
  g.center + TorusAverages.latticePoint k

/-- The center used by a copy is its own lattice translate. -/
theorem native_offset (g : Geometry) (k : TorusInverse.Frequency) (Y : Plane) :
    coverPower g.gap Y - nativeCenter g k = g.basis (g.coordinates k Y) := by
  rw [Geometry.coordinates, ContinuousLinearEquiv.apply_symm_apply]
  unfold nativeCenter
  abel

theorem nativeGraph_eq_cover_commonLift (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    PhysicalGraphBounds.nativeGraph h n w = coverPower d (commonLift h n d w).2 := by
  change PhysicalGraphBounds.nativeGraph h n w =
    coverPower d ((coverPower d).symm (PhysicalGraphBounds.nativeGraph h n w))
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem physical_native_offset (g : Geometry) (k : TorusInverse.Frequency)
    (h : ℝ) (n d : ℕ) (hgap : g.gap = d) (w : SpaceTime) :
    PhysicalGraphBounds.nativeGraph h n w - nativeCenter g k =
      g.basis (g.coordinates k (commonLift h n d w).2) := by
  rw [nativeGraph_eq_cover_commonLift h n d w]
  simpa only [hgap] using native_offset g k (commonLift h n d w).2

/-- The physical slot-width bound follows from the native cell width and
the exact cover map, rather than being assumed for a periodized field. -/
theorem physical_native_width (g : Geometry) (k : TorusInverse.Frequency)
    (h : ℝ) (n d : ℕ) (hgap : g.gap = d) {U : Set Plane} {r0 : ℝ}
    (hU : ∀ z ∈ U, |PhysicalGraphBounds.etaCoordinate (g.basis z)| ≤ r0)
    (w : SpaceTime) (hw : g.coordinates k (commonLift h n d w).2 ∈ U) :
    |PhysicalGraphBounds.etaCoordinate (PhysicalGraphBounds.nativeGraph h n w - nativeCenter g k)|
      ≤ r0 := by
  rw [physical_native_offset g k h n d hgap w]
  exact hU _ hw

variable {F : CopyFamily H TorusInverse.Frequency}

/-- Build the abstract support cells from the actual native affine lattice
charts.  Compactness gives local finiteness; quotient injectivity gives
disjointness, both through `PeriodizedWaveBounds.nativeCells`. -/
noncomputable def nativeSupportCells (g : BandLabel → Geometry) (U : BandLabel → Set Plane)
    (hU : ∀ L, IsCompact (U L))
    (hinj : ∀ L, InjOn TorusAverages.quotientPoint
      ((fun z => (g L).center + (g L).basis z) '' U L))
    (hs : ∀ k I x, F.amplitude k I x ≠ 0 → (g I.1).coordinates k x.2 ∈ U I.1) :
    SupportCells F where
  cells L := PeriodizedWaveBounds.nativeCells (P := PhysicalGraphBounds.ChartPoint)
    (fun _ => g L) (fun _ => U L) (fun _ => hU L) (fun _ => hinj L)
  support I k x hx := hs k I x hx

@[simp] theorem nativeSupportCells_mem (g : BandLabel → Geometry) (U : BandLabel → Set Plane)
    (hU : ∀ L, IsCompact (U L))
    (hinj : ∀ L, InjOn TorusAverages.quotientPoint
      ((fun z => (g L).center + (g L).basis z) '' U L))
    (hs : ∀ k I x, F.amplitude k I x ≠ 0 → (g I.1).coordinates k x.2 ∈ U I.1)
    (I : WaveIndex H) (k : TorusInverse.Frequency) (x : LiftPoint) :
    x ∈ ((nativeSupportCells g U hU hinj hs).cells I.1).carrier I.1.val.1 k ↔
      (g I.1).coordinates k x.2 ∈ U I.1 := Iff.rfl

/-- For the actual localized coefficients, the support premise is itself
derived from the literal cutoff factor. -/
noncomputable def nativeCutoffSupportCells (g : BandLabel → Geometry) (U : BandLabel → Set Plane)
    (hU : ∀ L, IsCompact (U L))
    (hinj : ∀ L, InjOn TorusAverages.quotientPoint
      ((fun z => (g L).center + (g L).basis z) '' U L))
    (κ : BandLabel → Plane → ℝ) (hκ : ∀ L, support (κ L) ⊆ U L)
    (v : TorusInverse.Frequency → WaveIndex H → LiftPoint → ℂ)
    (he : ∀ k I x, F.amplitude k I x = κ I.1 ((g I.1).coordinates k x.2) • v k I x) :
    SupportCells F :=
  nativeSupportCells g U hU hinj (by
    intro k I x hx
    apply hκ I.1
    intro hz
    exact hx (by rw [he, hz, zero_smul]))

/-- A native cell description proves all copy-width support conditions in
the regularity record.  The radial annulus, slow mask, and smooth coefficient
inputs are separate, as in the original construction. -/
theorem regular_of_native (g : BandLabel → Geometry) (U : BandLabel → Set Plane)
    (hgap : ∀ L, (g L).gap = F.gap L)
    (hcenter : ∀ k L, (F.carrier k L).center = nativeCenter (g L) k)
    (hwidth : ∀ L z, z ∈ U L → |PhysicalGraphBounds.etaCoordinate ((g L).basis z)| ≤ r0)
    (hs : ∀ k I x, F.amplitude k I x ≠ 0 → (g I.1).coordinates k x.2 ∈ U I.1)
    (hgap_le : ∀ L, F.gap L ≤ Δ)
    (hgap_native : ∀ L, F.gap L ≤ ChartScales.nativeIndex h L.val.1)
    (hamp : ∀ k I, ContDiff ℝ ∞ (F.amplitude k I))
    (hF : ∀ k L, ContDiff ℝ ∞ (F.carrier k L).F)
    (hG : ∀ k L, ContDiff ℝ ∞ (F.carrier k L).G)
    (hint : ∀ k L, ∃ m : ℤ,
      (ChartScales.carrier h L.val.1 : ℝ) * (F.carrier k L).angular = (m : ℝ))
    (hgeo : ∀ k I y, F.amplitude k I (commonLift h I.1.val.1 (F.gap I.1) y) ≠ 0 →
      PhysicalGraphBounds.scaledRadial I.1.val.1 y ∈ PhysicalGraphBounds.annulus a b ∧
      ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h I.1.val.1 y)‖ ≤ Z)
    (hmask : ∀ k I y, y ∈ preterminal →
      F.amplitude k I (commonLift h I.1.val.1 (F.gap I.1) y) ≠ 0 →
      physicalMask (CoordinateAlgebra.D h) I.1.val (physicalParams h y) ≠ 0) :
    RegularFamily F a b h r0 Z Δ := by
  refine ⟨fun k => ⟨hgap_le, hgap_native, hamp k, hF k, hG k, hint k, ?_, hmask k⟩⟩
  intro I y hy
  refine ⟨(hgeo k I y hy).1, (hgeo k I y hy).2, ?_⟩
  change |PhysicalGraphBounds.etaCoordinate
    (PhysicalGraphBounds.nativeGraph h I.1.val.1 y - (F.carrier k I.1).center)| ≤ r0
  rw [hcenter]
  exact physical_native_width (g I.1) k h I.1.val.1 (F.gap I.1) (hgap I.1)
    (hwidth I.1) y (hs k I _ hy)

end NativeCells

/-! ## Exact support and vector-valued consequences -/

theorem CopyFamily.sum_nonzero_term (f : CopyFamily H K) {a h r0 : ℝ} {w : SpaceTime}
    (hw : f.sum a h r0 w ≠ 0) : ∃ I k, f.term a h r0 I k w ≠ 0 := by
  classical
  by_contra! hn
  have hp : ∀ I, f.periodized a h r0 I w = 0 := by
    intro I
    simp only [CopyFamily.periodized, hn, tsum_zero]
  exact hw (by simp only [CopyFamily.sum, hp, finsum_zero])

/-- A nonzero full sum has a genuine supported copy witness.  This is the
primitive support statement needed for the shrinking physical annulus. -/
theorem RegularFamily.sum_support (hr : RegularFamily f a b h r0 Z Δ)
    {w : SpaceTime} (hw : w ∈ preterminal) (hn : f.sum a h r0 w ≠ 0) :
    ∃ (I : WaveIndex H) (k : K),
      f.amplitude k I (commonLift h I.1.val.1 (f.gap I.1) w) ≠ 0 ∧
      PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b ∧
      physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val := by
  obtain ⟨I, k, hk⟩ := f.sum_nonzero_term hn
  have ha := globalWave_ne_zero_amp hk
  exact ⟨I, k, ha, ((hr.copy k).geometry_support I w ha).1,
    (hr.copy k).term_support I w hw hk⟩

noncomputable def vectorSum (f : Fin 3 → CopyFamily H K) (a h r0 : ℝ)
    (w : SpaceTime) : Space := ∑ i : Fin 3, realCoordinate i ((f i).sum a h r0 w)

theorem vectorSum_smooth {f : Fin 3 → CopyFamily H K}
    (hr : ∀ i, RegularFamily (f i) a b h r0 Z Δ)
    (hc : ∀ i, SupportCells (f i)) (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (vectorSum f a h r0) preterminal := by
  apply ContDiffOn.sum
  intro i _
  exact (realCoordinate i).contDiff.comp_contDiffOn ((hr i).sum_smooth (hc i) ha hh hh1)

theorem vectorSum_jet_bound {f : Fin 3 → CopyFamily H K}
    (hr : ∀ i, RegularFamily (f i) a b h r0 Z Δ)
    (hc : ∀ i, SupportCells (f i)) (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (hw : w ∈ preterminal) (m : ℕ) {B : ℝ}
    (hb : ∀ i, ‖iteratedFDeriv ℝ m ((f i).sum a h r0) w‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (vectorSum f a h r0) w‖ ≤ 3 * B := by
  have hs i : ContDiffAt ℝ ∞ ((f i).sum a h r0) w :=
    ((hr i).sum_smooth (hc i) ha hh hh1).contDiffAt (preterminal_open.mem_nhds hw)
  unfold vectorSum
  rw [iteratedFDeriv_finset_sum_at (f := fun i y => realCoordinate i ((f i).sum a h r0 y))
    Finset.univ
    (fun i _ => ((realCoordinate i).contDiff.contDiffAt.comp w (hs i)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))]
  calc
    _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ m (fun y => realCoordinate i ((f i).sum a h r0 y)) w‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, B := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_jet_linear_comp_at ((hs i).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)) (realCoordinate i)).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (norm_realCoordinate_le i)).trans (hb i))
    _ = 3 * B := by simp

/-- Uniform scalar input bounds give the actual real three-component
physical estimate with the same loss exponent. -/
theorem physical_vector_sum_jet_bound {h a b Z r0 P B eBase : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (H Δ m : ℕ) (g eAmp A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Fin 3 → CopyFamily H K,
      (∀ i, RegularFamily (f i) a b h r0 Z Δ) → ∀ hc : ∀ i, SupportCells (f i),
      (∀ i, LocalStrippedClass (f i) (hc i) a b h r0 P A B g eAmp eBase m) →
      ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (vectorSum f a h r0) w‖ ≤
        C * physicalQ h w ^ (g - PhysicalGraphBounds.waveLoss h m) := by
  obtain ⟨C, hC, hb⟩ := physical_sum_jet_bound (K := K) (b := b)
    hh hh1 ha hZ hr0 hP hB heBase H Δ m g eAmp A hA
  refine ⟨3 * C, by positivity, ?_⟩
  intro f hr hc hclass w hw ht
  exact (vectorSum_jet_bound hr hc ha hh hh1 hw m
    (fun i => hb (f i) (hr i) (hc i) (hclass i) w hw ht)).trans_eq (by ring)

section WeightedVector

open WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {ι : Type*}

theorem physical_vector_sum_jet_bound_of_weighted {s : StripData D} {α σ P : ℝ}
    {w : ι → ℕ → D → ℝ} {source : ι → ℕ → D → ℂ}
    (hs : PhysicalClassBounds.SourceBounds s h α w source) {f : Fin 3 → CopyFamily H K}
    (hc : ∀ i, SupportCells (f i))
    (hchart : ∀ i, CommonChart (f i) (hc i) a b h σ source)
    (hb : ∀ i, CarrierBounds (f i) (hc i) a b h r0)
    (hr : ∀ i, RegularFamily (f i) a b h r0 Z Δ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0)
    (hP : 1 ≤ P) (hp : ∀ i k L, |((f i).carrier k L).angular| ≤ P ∧
      |((f i).carrier k L).axial| ≤ P ∧ |((f i).carrier k L).radial| ≤ P) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : SpaceTime,
      z ∈ preterminal → |z.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (vectorSum f a h r0) z‖ ≤
        C * physicalQ h z ^ (h * α - PhysicalClassBounds.physicalLoss h σ m) := by
  classical
  have hbnd := fun i => physical_sum_jet_bound_of_weighted hs (hchart i) (hb i) (hr i)
    hh hh1 ha hZ hr0 hP (hp i) m
  choose C hC hbound using hbnd
  refine ⟨3 * ∑ i : Fin 3, C i,
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => hC i)), ?_⟩
  intro z hz ht
  have hq := physicalQ_pos hh hh1 hz
  have hi (i : Fin 3) : C i ≤ ∑ j : Fin 3, C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  have he := vectorSum_jet_bound hr hc ha hh hh1 hz m
    (B := (∑ i : Fin 3, C i) * physicalQ h z ^ (h * α - PhysicalClassBounds.physicalLoss h σ m))
    (fun i => (hbound i z hz ht).trans
      (mul_le_mul_of_nonneg_right (hi i) (Real.rpow_pos_of_pos hq _).le))
  exact he.trans_eq (by ring)

end WeightedVector

end NavierStokes.PhysicalCopyBounds
