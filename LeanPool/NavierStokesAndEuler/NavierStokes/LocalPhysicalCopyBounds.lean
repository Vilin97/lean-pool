/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalCopyBounds
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-!
# Physical copy bounds from local native smoothness

Raw native coefficients and phase profiles are only used on their valid open
patches.  A smooth bump produces a globally smooth function with the exact same
germ at one evaluation point.  The physical carrier bound measures only jets at
that point, so no bound on the extension away from it is needed.
-/

noncomputable section

namespace NavierStokes.LocalPhysicalCopyBounds

open Set Function Filter ProblemStatement PhysicalWaveSum PhysicalCopyBounds
open scoped Topology ContDiff BigOperators

section SmoothExtensions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smoothness on one genuine open neighborhood.  Unlike a bare
`ContDiffAt ℝ ∞`, the same neighborhood works for all derivative orders. -/
def SmoothNear (f : E → F) (x : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ f U

theorem SmoothNear.of_open {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) : SmoothNear f x :=
  ⟨U, hU, hx, hf⟩

theorem SmoothNear.contDiffAt {f : E → F} {x : E} (hf : SmoothNear f x) :
    ContDiffAt ℝ ∞ f x := by
  obtain ⟨U, hU, hx, h⟩ := hf
  exact h.contDiffAt (hU.mem_nhds hx)

/-- Local smoothness on an open patch and an actual zero germ off it suffice
for global smoothness.  No raw totalization is assumed smooth. -/
theorem contDiff_of_patch_zero {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hz : ∀ x, x ∉ U → f =ᶠ[𝓝 x] fun _ => 0) : ContDiff ℝ ∞ f := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hx)
  · exact contDiffAt_const.congr_of_eventuallyEq (hz x hx)

theorem contDiff_of_patch_tsupport {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport f ⊆ U) : ContDiff ℝ ∞ f :=
  contDiff_of_patch_zero hU hf (fun _ hx =>
    notMem_tsupport_iff_eventuallyEq.mp (fun hxs => hx (hs hxs)))

/-- Construct the replacement using a smooth bump inside the actual open
patch.  Its values and all its derivatives agree with the raw input near `x`.
No bound on the extension away from `x` is imposed or used. -/
theorem SmoothNear.exists_global_germ [FiniteDimensional ℝ E]
    {f : E → F} {x : E} (hf : SmoothNear f x) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ f =ᶠ[𝓝 x] g := by
  obtain ⟨U, hU, hx, hlocal⟩ := hf
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let b : ContDiffBump x := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hbs : tsupport (b : E → ℝ) ⊆ U := by
    rw [b.tsupport_eq]
    exact hball
  refine ⟨fun y => b y • f y, ?_, ?_⟩
  · apply contDiff_of_patch_zero hU (b.contDiff.contDiffOn.smul hlocal)
    intro y hy
    have hz : (b : E → ℝ) =ᶠ[𝓝 y] fun _ => 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hys => hy (hbs hys))
    filter_upwards [hz] with z hz
    change b z • f z = 0
    change b z = 0 at hz
    rw [hz, zero_smul]
  · filter_upwards [b.eventuallyEq_one] with y hy
    change b y = 1 at hy
    simp only [hy, one_smul]

/-- An interior native jet bound persists at a boundary point where the
actual coefficient is locally smooth.  This covers the zero-extended moving
edges without requiring their points to belong to the open weighted strip. -/
theorem jet_bound_at_closure {f : E → F} {U : Set E} {x : E} {B : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hx : x ∈ closure U) (j : ℕ)
    (hb : ∀ y ∈ U, ‖iteratedFDeriv ℝ j f y‖ ≤ B) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  have hcont : ContinuousAt (iteratedFDeriv ℝ j f) x :=
    (hf.iteratedFDeriv_right (m := 0) (by simp)).continuousAt
  have : NeBot (𝓝[U] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have ht : Tendsto (fun y => ‖iteratedFDeriv ℝ j f y‖) (𝓝[U] x)
      (𝓝 ‖iteratedFDeriv ℝ j f x‖) := hcont.norm.mono_left inf_le_left
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hb y hy

end SmoothExtensions

noncomputable def replaceProfiles (c : CarrierData)
    (F G : PhysicalGraphBounds.Slow → ℝ) : CarrierData := { c with F := F, G := G }

noncomputable def slotSlow (c : CarrierData) (a h : ℝ) (n : ℕ) (r0 : ℝ)
    (w : SpaceTime) : PhysicalGraphBounds.Slow :=
  (PhysicalGraphBounds.slotMap (PolarCharts.chart a c.chart)
    (ChartScales.timeCoefficient h n) c.center r0 (PhysicalGraphBounds.physicalLift h n w)).1

theorem slotSlow_continuousAt {a : ℝ} (ha : 0 < a) (c : CarrierData)
    (h : ℝ) (n : ℕ) (r0 : ℝ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.radialProjection w ≠ 0) :
    ContinuousAt (slotSlow c a h n r0) w := by
  have hLift := (PhysicalGraphBounds.physicalChart_smooth h n).contDiffAt.prodMk
    (PhysicalGraphBounds.contDiffAt_nativeGraph h n hw)
  exact (((PhysicalGraphBounds.slotMap_smooth (PolarCharts.chart_contDiff ha c.chart)
    (ChartScales.timeCoefficient h n) c.center r0).contDiffAt.comp w hLift).fst).continuousAt

/-- Replacing native inputs by functions with the same germs preserves the
actual physical carrier germ, including the full phase. -/
theorem commonWave_germ {a : ℝ} (ha : 0 < a) (h : ℝ) (n d : ℕ) (r0 : ℝ)
    (c : CarrierData) (j : ℤ) {amp amp' : LiftPoint → ℂ}
    {F G : PhysicalGraphBounds.Slow → ℝ} {w : SpaceTime}
    (hw : PhysicalGraphBounds.radialProjection w ≠ 0)
    (hamp : amp =ᶠ[𝓝 (commonLift h n d w)] amp')
    (hF : c.F =ᶠ[𝓝 (slotSlow c a h n r0 w)] F)
    (hG : c.G =ᶠ[𝓝 (slotSlow c a h n r0 w)] G) :
    commonWave a h n d r0 c amp j =ᶠ[𝓝 w]
      commonWave a h n d r0 (replaceProfiles c F G) amp' j := by
  have ha' := hamp.comp_tendsto (commonLift_smoothAt h n d hw).continuousAt
  have hF' := hF.comp_tendsto (slotSlow_continuousAt ha c h n r0 hw)
  have hG' := hG.comp_tendsto (slotSlow_continuousAt ha c h n r0 hw)
  filter_upwards [ha', hF', hG'] with y hya hyF hyG
  dsimp only [Function.comp_apply] at hya hyF hyG
  simp only [slotSlow] at hyF hyG
  simp only [commonWave, replaceProfiles, CarrierData.phase, PhysicalGraphBounds.liftedPhase,
    Function.comp_apply, PhaseCalculus.phase, hya, hyF, hyG]

theorem commonWave_smoothAt_local {a : ℝ} (ha : 0 < a) (h : ℝ) (n d : ℕ) (r0 : ℝ)
    (c : CarrierData) {amp : LiftPoint → ℂ} (j : ℤ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.radialProjection w ≠ 0)
    (hamp : SmoothNear amp (commonLift h n d w))
    (hF : SmoothNear c.F (slotSlow c a h n r0 w))
    (hG : SmoothNear c.G (slotSlow c a h n r0 w)) :
    ContDiffAt ℝ ∞ (commonWave a h n d r0 c amp j) w := by
  obtain ⟨amp', ha', hea⟩ := hamp.exists_global_germ
  obtain ⟨F, hF', heF⟩ := hF.exists_global_germ
  obtain ⟨G, hG', heG⟩ := hG.exists_global_germ
  have hs := commonWave_smoothAt ha h n d r0 (replaceProfiles c F G) ha' hF' hG' j hw
  exact hs.congr_of_eventuallyEq (commonWave_germ ha h n d r0 c j hw hea heF heG)

/-- The pointwise global-carrier estimate applies to the constructed
same-germ replacements.  Its constants therefore remain unchanged. -/
theorem common_carrier_physical_bound_local {h a b Z r0 P B eBase : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (Δ m : ℕ) (g eAmp A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
      |w.1| ≤ 1 → ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w)‖ ≤ Z →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ (c : CarrierData) (amp : LiftPoint → ℂ) (j : ℤ),
      |c.angular| ≤ P → |c.axial| ≤ P → |c.radial| ≤ P →
      |PhysicalGraphBounds.etaCoordinate (PhysicalGraphBounds.nativeGraph h n w - c.center)| ≤ r0 →
      SmoothNear amp (commonLift h n d w) → SmoothNear c.F (slotSlow c a h n r0 w) →
      SmoothNear c.G (slotSlow c a h n r0 w) → |(j : ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i amp (commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ eAmp) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i c.F (slotSlow c a h n r0 w)‖ ≤
        B * ChartScales.S n ^ eBase) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i c.G (slotSlow c a h n r0 w)‖ ≤
        B * ChartScales.S n ^ eBase) →
      ‖iteratedFDeriv ℝ m (commonWave a h n d r0 c amp j) w‖ ≤
        C * q ^ (g - PhysicalGraphBounds.waveLoss h m) := by
  obtain ⟨C, hC, hb⟩ := common_carrier_physical_bound (b := b)
    hh hh1 ha hZ hr0 hP hB heBase Δ m g eAmp A H hA hH
  refine ⟨C, hC, ?_⟩
  intro n hn d hd w hann ht hz q hq hlo hhi c amp j hp hpz hpx hslot haNear hFNear hGNear hj hab
    hFb hGb
  obtain ⟨amp', ha', hea⟩ := haNear.exists_global_germ
  obtain ⟨F, hF', heF⟩ := hFNear.exists_global_germ
  obtain ⟨G, hG', heG⟩ := hGNear.exists_global_germ
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha
    hann)
  rw [iteratedFDeriv_eq_of_eventuallyEq (commonWave_germ ha h n d r0 c j haxis hea heF heG) m]
  apply hb n hn d hd w hann ht hz q hq hlo hhi (replaceProfiles c F G) amp' j
    hp hpz hpx hslot ha' hF' hG' hj
  · intro i hi
    rw [← iteratedFDeriv_eq_of_eventuallyEq hea i]
    exact hab i hi
  · intro i hi
    change ‖iteratedFDeriv ℝ i F (slotSlow c a h n r0 w)‖ ≤ _
    rw [← iteratedFDeriv_eq_of_eventuallyEq heF i]
    exact hFb i hi
  · intro i hi
    change ‖iteratedFDeriv ℝ i G (slotSlow c a h n r0 w)‖ ≤ _
    rw [← iteratedFDeriv_eq_of_eventuallyEq heG i]
    exact hGb i hi

/-! ## Support-local families -/

/-- Only the primitive support geometry and angular integrality.  There is
no global smoothness condition in this record. -/
structure SupportData {H : ℕ} {K : Type*} (f : CopyFamily H K)
    (a b h r0 Z : ℝ) (Δ : ℕ) : Prop where
  gap_le : ∀ L, f.gap L ≤ Δ
  gap_native : ∀ L, f.gap L ≤ ChartScales.nativeIndex h L.val.1
  angular_integer : ∀ k L, ∃ m : ℤ,
    (ChartScales.carrier h L.val.1 : ℝ) * (f.carrier k L).angular = (m : ℝ)
  geometry_support : ∀ k I y,
    f.amplitude k I (commonLift h I.1.val.1 (f.gap I.1) y) ≠ 0 →
      PhysicalGraphBounds.scaledRadial I.1.val.1 y ∈ PhysicalGraphBounds.annulus a b ∧
      ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h I.1.val.1 y)‖ ≤ Z ∧
      |PhysicalGraphBounds.etaCoordinate
        (PhysicalGraphBounds.nativeGraph h I.1.val.1 y - (f.carrier k I.1).center)| ≤ r0
  mask_support : ∀ k I y, y ∈ preterminal →
    f.amplitude k I (commonLift h I.1.val.1 (f.gap I.1) y) ≠ 0 →
      physicalMask (CoordinateAlgebra.D h) I.1.val (physicalParams h y) ≠ 0

/-- The genuine raw inputs need be smooth only near points at which this
copy has support.  In particular, phase profiles need not be smooth at a
singular totalization of `coordinateQ` outside the actual native patch. -/
structure SmoothData {H : ℕ} {K : Type*} (f : CopyFamily H K) (a h r0 : ℝ) : Prop where
  amplitude : ∀ k I w, w ∈ preterminal → w ∈ tsupport (f.term a h r0 I k) →
    SmoothNear (f.amplitude k I) (commonLift h I.1.val.1 (f.gap I.1) w)
  profiles : ∀ k I w, w ∈ preterminal → w ∈ tsupport (f.term a h r0 I k) →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart →
    SmoothNear (f.carrier k I.1).F
      (slotSlow ((f.carrier k I.1).withChart chart) a h I.1.val.1 r0 w) ∧
    SmoothNear (f.carrier k I.1).G
      (slotSlow ((f.carrier k I.1).withChart chart) a h I.1.val.1 r0 w)

/-- Native jets are needed only for a copy with nonzero local support.
This permits zero germs outside the valid native patch. -/
structure JetData {H : ℕ} {K : Type*} (f : CopyFamily H K) (hc : SupportCells f)
    (a b h r0 P A B g eAmp eBase : ℝ) (m : ℕ) : Prop where
  parameters : ∀ k L, |(f.carrier k L).angular| ≤ P ∧
    |(f.carrier k L).axial| ≤ P ∧ |(f.carrier k L).radial| ≤ P
  jets : ∀ k (I : WaveIndex H) (w : SpaceTime), w ∈ preterminal →
    physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k →
    w ∈ tsupport (f.term a h r0 I k) →
    (∀ i ≤ m, ‖iteratedFDeriv ℝ i (f.amplitude k I) (commonLift h I.1.val.1 (f.gap I.1) w)‖ ≤
      A * ChartScales.Q I.1.val.1 ^ g * ChartScales.S I.1.val.1 ^ eAmp) ∧
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart →
    (∀ i ≤ m, ‖iteratedFDeriv ℝ i (f.carrier k I.1).F
      (slotSlow ((f.carrier k I.1).withChart chart) a h I.1.val.1 r0 w)‖ ≤
        B * ChartScales.S I.1.val.1 ^ eBase) ∧
    (∀ i ≤ m, ‖iteratedFDeriv ℝ i (f.carrier k I.1).G
      (slotSlow ((f.carrier k I.1).withChart chart) a h I.1.val.1 r0 w)‖ ≤
        B * ChartScales.S I.1.val.1 ^ eBase)

variable {H Δ : ℕ} {K : Type*} {f : CopyFamily H K} {a b h r0 Z : ℝ}

theorem SupportData.tsupport_geometry (hr : SupportData f a b h r0 Z Δ)
    (I : WaveIndex H) (k : K) {w : SpaceTime} (hw : w ∈ tsupport (f.term a h r0 I k)) :
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b ∧
      ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h I.1.val.1 w)‖ ≤ Z ∧
      |PhysicalGraphBounds.etaCoordinate
        (PhysicalGraphBounds.nativeGraph h I.1.val.1 w - (f.carrier k I.1).center)| ≤ r0 :=
  globalWave_tsupport_geometry (f.carrier k I.1) (f.amplitude k I) I.2.val
    (hr.geometry_support k I) hw

theorem SupportData.periodized_zero_off_annulus (hr : SupportData f a b h r0 Z Δ)
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
  exact hy (hr.geometry_support k I y hn).1

theorem SupportData.periodized_germ_cover (hr : SupportData f a b h r0 Z Δ)
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

theorem SupportData.periodized_support (hr : SupportData f a b h r0 Z Δ)
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
  exact hout (physicalMask_support_subset _ _
    (hr.mask_support k I w hw (globalWave_ne_zero_amp hne)))

/-- Local native smoothness and the actual support geometry prove physical
smoothness at every preterminal point.  Outside support this uses the genuine
zero germ, not regularity of an unused raw phase. -/
theorem SupportData.term_smoothAt (hr : SupportData f a b h r0 Z Δ)
    (hs : SmoothData f a h r0) (ha : 0 < a) (I : WaveIndex H) (k : K)
    (w : SpaceTime) (hw : w ∈ preterminal) : ContDiffAt ℝ ∞ (f.term a h r0 I k) w := by
  classical
  by_cases ht : w ∈ tsupport (f.term a h r0 I k)
  · have hgeo := hr.tsupport_geometry I k ht
    let chart := chooseChart a (PhysicalGraphBounds.scaledRadial I.1.val.1 w)
    have hchart : PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart :=
      chooseChart_valid ha hgeo.1
    obtain ⟨mode, hmode⟩ := hr.angular_integer k I.1
    have he := globalWave_eventually_common (r0 := r0) ha I.1.val.1 (f.gap I.1)
      (f.carrier k I.1) (f.amplitude k I) I.2.val mode hmode
      (fun y hy => (hr.geometry_support k I y hy).1) chart hchart
    have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha
      hgeo.1)
    have hp := hs.profiles k I w hw ht chart hchart
    have hlocal := commonWave_smoothAt_local ha h I.1.val.1 (f.gap I.1) r0
      ((f.carrier k I.1).withChart chart) I.2.val haxis (hs.amplitude k I w hw ht) hp.1 hp.2
    exact hlocal.congr_of_eventuallyEq he
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp ht)

theorem SupportData.periodized_smoothAt (hr : SupportData f a b h r0 Z Δ)
    (hs : SmoothData f a h r0) (hc : SupportCells f) (ha : 0 < a)
    (I : WaveIndex H) (w : SpaceTime) (hw : w ∈ preterminal) :
    ContDiffAt ℝ ∞ (f.periodized a h r0 I) w := by
  rcases hr.periodized_germ_cover hc ha I w with ⟨k, _, hg⟩ | hg
  · exact (hr.term_smoothAt hs ha I k w hw).congr_of_eventuallyEq hg
  · exact contDiffAt_const.congr_of_eventuallyEq hg

theorem SupportData.sum_smooth (hr : SupportData f a b h r0 Z Δ)
    (hs : SmoothData f a h r0) (hc : SupportCells f) (ha : 0 < a)
    (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (f.sum a h r0) preterminal :=
  masked_finsum_smooth hh hh1 (f.periodized a h r0)
    (hr.periodized_smoothAt hs hc ha) hr.periodized_support

/-- The same physical derivative loss as before, with only local raw input
smoothness.  The pointwise smooth replacements never enter the output field. -/
theorem physical_sum_jet_bound {h a b Z r0 P B eBase : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (H Δ m : ℕ) (g eAmp A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : CopyFamily H K,
      SupportData f a b h r0 Z Δ → SmoothData f a h r0 → ∀ hc : SupportCells f,
      JetData f hc a b h r0 P A B g eAmp eBase m →
      ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (f.sum a h r0) w‖ ≤
        C * physicalQ h w ^ (g - PhysicalGraphBounds.waveLoss h m) := by
  obtain ⟨C, hC, hpoint⟩ := common_carrier_physical_bound_local (b := b) hh.le hh1.le ha
    hZ hr0 hP hB heBase Δ m g eAmp A (H : ℝ) hA (Nat.cast_nonneg H)
  refine ⟨((2250 * (2 * H + 1) : ℕ) : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro f hr hs hc hb w hw ht
  have hq := physicalQ_pos hh hh1 hw
  have hcopy : ∀ (I : WaveIndex H),
      physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val → ∀ k,
      ‖iteratedFDeriv ℝ m (f.term a h r0 I k) w‖ ≤
        C * physicalQ h w ^ (g - PhysicalGraphBounds.waveLoss h m) := by
    intro I hregion k
    by_cases hts : w ∈ tsupport (f.term a h r0 I k)
    · have hgeo := hr.tsupport_geometry I k hts
      have hcell := hc.term_tsupport_mem ha I k hgeo.1 hts
      obtain ⟨mode, hmode⟩ := hr.angular_integer k I.1
      let chart := chooseChart a (PhysicalGraphBounds.scaledRadial I.1.val.1 w)
      have hchart : PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart
        :=
        chooseChart_valid ha hgeo.1
      have he := globalWave_eventually_common (r0 := r0) ha I.1.val.1 (f.gap I.1)
        (f.carrier k I.1) (f.amplitude k I) I.2.val mode hmode
        (fun y hy => (hr.geometry_support k I y hy).1) chart hchart
      change ‖iteratedFDeriv ℝ m (globalWave a h I.1.val.1 (f.gap I.1) r0
        (f.carrier k I.1) (f.amplitude k I) I.2.val) w‖ ≤ _
      rw [iteratedFDeriv_eq_of_eventuallyEq he m]
      have hband := labelRegion_active_relation hregion
      have hp := hs.profiles k I w hw hts chart hchart
      have hjets := hb.jets k I w hw hregion hgeo.1 hcell hts
      exact hpoint I.1.val.1 I.1.property (f.gap I.1) (hr.gap_le I.1)
        w hgeo.1 ht hgeo.2.1 (physicalQ h w) hq hband.1 hband.2
        ((f.carrier k I.1).withChart chart) (f.amplitude k I) I.2.val
        (hb.parameters k I.1).1 (hb.parameters k I.1).2.1 (hb.parameters k I.1).2.2 hgeo.2.2
        (hs.amplitude k I w hw hts) hp.1 hp.2 (harmonic_bound I.2)
        hjets.1 (hjets.2 chart hchart).1 (hjets.2 chart hchart).2
    · rw [jet_zero_off_tsupport _ _ hts, norm_zero]
      positivity
  have hsum := masked_finsum_jet_bound hh hh1 (f.periodized a h r0)
    (hr.periodized_smoothAt hs hc ha) hr.periodized_support hw m
    (B := C * physicalQ h w ^ (g - PhysicalGraphBounds.waveLoss h m)) (by positivity)
  refine (hsum ?_).trans_eq (by ring)
  intro I hregion
  rcases hr.periodized_germ_cover hc ha I w with ⟨k, _, hg⟩ | hg
  · rw [iteratedFDeriv_eq_of_eventuallyEq hg m]
    exact hcopy I hregion k
  · rw [iteratedFDeriv_eq_of_eventuallyEq hg m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity

/-! ## Deriving local smoothness from padded native patches -/

/-- Actual native closed cores inside the open smooth patches.  The core
support fields concern input amplitudes and their native phase evaluation,
not the smoothness or derivatives of a final physical output. -/
structure PatchData (f : CopyFamily H K) (a h r0 : ℝ) where
  amplitudeDomain : K → WaveIndex H → Set LiftPoint
  amplitudeCore : K → WaveIndex H → Set LiftPoint
  amplitudeOpen : ∀ k I, IsOpen (amplitudeDomain k I)
  amplitudeClosed : ∀ k I, IsClosed (amplitudeCore k I)
  amplitudeSubset : ∀ k I, amplitudeCore k I ⊆ amplitudeDomain k I
  amplitudeSmooth : ∀ k I, ContDiffOn ℝ ∞ (f.amplitude k I) (amplitudeDomain k I)
  amplitudeSupport : ∀ k I, support (f.amplitude k I) ⊆ amplitudeCore k I
  slowDomain : K → BandLabel → Set PhysicalGraphBounds.Slow
  slowCore : K → BandLabel → Set PhysicalGraphBounds.Slow
  slowOpen : ∀ k L, IsOpen (slowDomain k L)
  slowClosed : ∀ k L, IsClosed (slowCore k L)
  slowSubset : ∀ k L, slowCore k L ⊆ slowDomain k L
  FSmooth : ∀ k L, ContDiffOn ℝ ∞ (f.carrier k L).F (slowDomain k L)
  GSmooth : ∀ k L, ContDiffOn ℝ ∞ (f.carrier k L).G (slowDomain k L)
  slowSupport : ∀ k I y, y ∈ preterminal →
    f.amplitude k I (commonLift h I.1.val.1 (f.gap I.1) y) ≠ 0 →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 y ∈ PolarCharts.chartDomain a chart →
    slotSlow ((f.carrier k I.1).withChart chart) a h I.1.val.1 r0 y ∈ slowCore k I.1

/-- The constructed, already localized amplitude is globally smooth if its
closed native support is contained in the local smooth patch.  This is a
conclusion; raw phase profiles retain only local smoothness. -/
theorem PatchData.amplitude_contDiff (hp : PatchData f a h r0) (k : K) (I : WaveIndex H) :
    ContDiff ℝ ∞ (f.amplitude k I) := by
  apply contDiff_of_patch_tsupport (hp.amplitudeOpen k I) (hp.amplitudeSmooth k I)
  exact (closure_minimal (hp.amplitudeSupport k I) (hp.amplitudeClosed k I)).trans
    (hp.amplitudeSubset k I)

/-- Closed cores keep every supported phase evaluation inside the genuine
smooth patch even at the boundary of the amplitude's support. -/
theorem PatchData.smoothData (hp : PatchData f a h r0)
    (hr : SupportData f a b h r0 Z Δ) (ha : 0 < a) : SmoothData f a h r0 := by
  constructor
  · intro k I w hw hts
    have hgeo := hr.tsupport_geometry I k hts
    have hx : commonLift h I.1.val.1 (f.gap I.1) w ∈ hp.amplitudeCore k I :=
      closed_property_on_tsupport isOpen_univ (mem_univ w)
        (commonLift_continuousAt_of_annulus ha _ _ hgeo.1) (hp.amplitudeClosed k I)
        (fun y _ hy => hp.amplitudeSupport k I (globalWave_ne_zero_amp hy)) hts
    exact SmoothNear.of_open (hp.amplitudeOpen k I) (hp.amplitudeSmooth k I)
      (hp.amplitudeSubset k I hx)
  · intro k I w hw hts chart hchart
    have hgeo := hr.tsupport_geometry I k hts
    have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha
      hgeo.1)
    let U : Set SpaceTime := preterminal ∩ (PhysicalGraphBounds.scaledRadial I.1.val.1) ⁻¹'
      PolarCharts.chartDomain a chart
    have hU : IsOpen U := preterminal_open.inter
      ((PolarCharts.chartDomain_open a chart).preimage (PhysicalGraphBounds.scaledRadial
        I.1.val.1).continuous)
    have hwU : w ∈ U := ⟨hw, hchart⟩
    have hx : slotSlow ((f.carrier k I.1).withChart chart) a h I.1.val.1 r0 w ∈ hp.slowCore k I.1 :=
      closed_property_on_tsupport hU hwU
        (slotSlow_continuousAt ha ((f.carrier k I.1).withChart chart) h I.1.val.1 r0 haxis)
        (hp.slowClosed k I.1)
        (fun y hy hne => hp.slowSupport k I y hy.1 (globalWave_ne_zero_amp hne) chart hy.2) hts
    exact ⟨SmoothNear.of_open (hp.slowOpen k I.1) (hp.FSmooth k I.1) (hp.slowSubset k I.1 hx),
      SmoothNear.of_open (hp.slowOpen k I.1) (hp.GSmooth k I.1) (hp.slowSubset k I.1 hx)⟩

theorem PatchData.sum_smooth (hp : PatchData f a h r0)
    (hr : SupportData f a b h r0 Z Δ) (hc : SupportCells f) (ha : 0 < a)
    (hh : 0 < h) (hh1 : h < 1 / 2) : ContDiffOn ℝ ∞ (f.sum a h r0) preterminal :=
  hr.sum_smooth (hp.smoothData hr ha) hc ha hh hh1

/-- The actual full sum still has a supported-copy witness.  This statement
needs no smoothness of the raw coefficient or phase totalizations. -/
theorem SupportData.sum_support (hr : SupportData f a b h r0 Z Δ)
    {w : SpaceTime} (hw : w ∈ preterminal) (hn : f.sum a h r0 w ≠ 0) :
    ∃ (I : WaveIndex H) (k : K),
      f.amplitude k I (commonLift h I.1.val.1 (f.gap I.1) w) ≠ 0 ∧
      PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b ∧
      physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val := by
  obtain ⟨I, k, hk⟩ := f.sum_nonzero_term hn
  have ha := globalWave_ne_zero_amp hk
  exact ⟨I, k, ha, (hr.geometry_support k I w ha).1,
    physicalMask_support_subset _ _ (hr.mask_support k I w hw ha)⟩

theorem SupportData.sum_locally_finite (hr : SupportData f a b h r0 Z Δ)
    (hh : 0 < h) (hh1 : h < 1 / 2) {w : SpaceTime} (hw : w ∈ preterminal) :
    ∃ s : Finset (WaveIndex H), s.card ≤ 2250 * (2 * H + 1) ∧
      f.sum a h r0 =ᶠ[𝓝 w] fun y => ∑ I ∈ s, f.periodized a h r0 I y := by
  obtain ⟨s, hs, he⟩ := masked_finsum_eventually hh hh1 (f.periodized a h r0)
    hr.periodized_support hw
  exact ⟨s, waveRegion_card_le (physicalQ_pos hh hh1 hw) s (fun I hI => (hs I).mp hI), he⟩

theorem SupportData.periodized_germ_of_cell (hr : SupportData f a b h r0 Z Δ)
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
        (fun y hy => (hr.geometry_support k I y hy).1) hann).symm

theorem SupportData.periodized_jet_eq (hr : SupportData f a b h r0 Z Δ)
    (hc : SupportCells f) (ha : 0 < a) (I : WaveIndex H) (k : K) {w : SpaceTime}
    (hk : commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k)
    (m : ℕ) :
    iteratedFDeriv ℝ m (f.periodized a h r0 I) w =
      iteratedFDeriv ℝ m (f.term a h r0 I k) w :=
  iteratedFDeriv_eq_of_eventuallyEq (hr.periodized_germ_of_cell hc ha I k hk) m

/-! ## Weighted bounds confined to the genuine native strip -/

section LocalWeightedInputs

open WeightedClasses LabelSumBounds

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

/-- The lower weighted input is only smooth on its actual open native
strip.  No global smoothness or global support condition on its raw
totalization is included. -/
structure LocalSourceBounds (s : StripData D) (h α : ℝ)
    (w : ι → ℕ → D → ℝ) (source : ι → ℕ → D → E) : Prop where
  uniform : UniformClass s w α source
  flat_geometry : ∃ cL cR L : ℝ, ∃ ρ : D → ℝ, PhysicalClassBounds.FlatGeometry s cL cR L ρ
  weight_le : ∃ c : ℝ, 0 < c ∧ ∀ l n x, x ∈ s.domain → w l n x ≤ s.zeta x ^ c
  epsilon_eq : ∀ n, s.epsilon n = ChartScales.epsilon h n
  slow_le : ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ,
    ∀ n, 4 ≤ n → s.slow n ≤ C * ChartScales.S n ^ p

/-- Absorb the actual two flat edges and keep the estimate on the valid
strip.  Extending the raw source outside that strip is unnecessary. -/
theorem LocalSourceBounds.chart_bound {s : StripData D} {α : ℝ}
    {w : ι → ℕ → D → ℝ} {source : ι → ℕ → D → E}
    (hs : LocalSourceBounds s h α w source) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ l n, 4 ≤ n → ∀ x ∈ s.domain, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (source l n) x‖ ≤
        A * ChartScales.Q n ^ (h * α) * ChartScales.S n ^ p := by
  obtain ⟨cL, cR, L, ρ, hflat⟩ := hs.flat_geometry
  obtain ⟨c, hc, hw⟩ := hs.weight_le
  obtain ⟨C, hC, q, hslow⟩ := hs.slow_le
  obtain ⟨A, hA, p, hb⟩ := PhysicalClassBounds.UniformClass.edge_absorbed
    hflat hc hs.uniform hw m
  refine ⟨A * C ^ p, mul_nonneg hA (pow_nonneg (zero_le_one.trans hC) _), q * p, ?_⟩
  intro l n hn x hx j hj
  have he : s.epsilon n ^ α = ChartScales.Q n ^ (h * α) := by
    rw [hs.epsilon_eq, ChartScales.epsilon, ← Real.rpow_mul (ChartScales.Q_pos n).le]
  calc
    _ ≤ A * s.epsilon n ^ α * s.slow n ^ p := hb l n x hx j hj
    _ ≤ A * s.epsilon n ^ α * (C * ChartScales.S n ^ q) ^ p :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (hslow n hn) p)
        (mul_nonneg hA (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le)
    _ = _ := by rw [he, mul_pow, ← pow_mul]; ring

/-- Higher chain-rule estimate using only open source and target patches. -/
theorem composition_jet_bound_on {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {g : D → E} {φ : X → D} {U : Set X} {V : Set D}
    (hU : IsOpen U) (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (hφ : ContDiffOn ℝ ∞ φ U) (hmap : MapsTo φ U V)
    {x : X} (hx : x ∈ U) (m : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g (φ x)‖ ≤ A)
    (hφb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i φ x‖ ≤ B) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (g ∘ φ) x‖ ≤ (m.factorial : ℝ) * A * B ^ m := by
  intro j hj
  have hb := norm_iteratedFDerivWithin_comp_le hg hφ (nat_le_infty j)
    hV.uniqueDiffOn hU.uniqueDiffOn hmap hx (C := A) (D := B)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i hV (hmap hx)]
      exact hgb i (hi.trans hj))
    (fun i hi hij => by
      rw [iteratedFDerivWithin_of_isOpen i hU hx]
      exact (hφb i hi (hij.trans hj)).trans (by simpa using pow_le_pow_right₀ hB hi))
  rw [iteratedFDerivWithin_of_isOpen j hU hx] at hb
  exact hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hA)
    (pow_le_pow_right₀ hB hj) (by positivity) (by positivity))

/-- The genuine common-chart formula holds on the open interior.  Supported
physical points may lie in its closure, including a moving radial edge. -/
structure CommonChart (f : CopyFamily H K) (hc : SupportCells f)
    (a b h r0 σ : ℝ) (source : ι → ℕ → D → ℂ) where
  sourceIndex : K → WaveIndex H → ι
  map : K → WaveIndex H → LiftPoint → D
  domain : K → WaveIndex H → Set LiftPoint
  open_domain : ∀ k I, IsOpen (domain k I)
  smooth : ∀ k I, ContDiffOn ℝ ∞ (map k I) (domain k I)
  positive_jets : ∀ m : ℕ, ∃ B : ℝ, 1 ≤ B ∧ ∃ q : ℕ,
    ∀ k I x, x ∈ domain k I → ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j (map k I) x‖ ≤ B * ChartScales.S I.1.val.1 ^ q
  amplitude_eq : ∀ k I, EqOn (f.amplitude k I)
    (fun x => (ChartScales.Q I.1.val.1 ^ σ) • source (sourceIndex k I) I.1.val.1 (map k I x))
    (domain k I)
  contains : ∀ k I z, z ∈ preterminal →
    physicalParams h z ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) z ∈ (hc.cells I.1).carrier I.1.val.1 k →
    z ∈ tsupport (f.term a h r0 I k) →
    commonLift h I.1.val.1 (f.gap I.1) z ∈ closure (domain k I)

theorem commonChart_amplitude_bound {s : StripData D} {α σ : ℝ}
    {w : ι → ℕ → D → ℝ} {source : ι → ℕ → D → ℂ}
    (hs : LocalSourceBounds s h α w source) {hc : SupportCells f}
    (hchart : CommonChart f hc a b h r0 σ source)
    (hmap : ∀ k I, MapsTo (hchart.map k I) (hchart.domain k I) s.domain) (m : ℕ) :
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
  have hjb := composition_jet_bound_on (hchart.open_domain k I) s.isOpen_domain
    (hs.uniform.smooth (hchart.sourceIndex k I) I.1.val.1)
    (hchart.smooth k I) (hmap k I) hx m hA0 hB0
    (fun j hj => hb (hchart.sourceIndex k I) I.1.val.1 I.1.property
      (hchart.map k I x) (hmap k I hx) j hj)
    (fun j hj hjm => hq k I x hx j hj hjm) j hj
  have hcomp : ContDiffAt ℝ ∞ (source (hchart.sourceIndex k I) I.1.val.1 ∘ hchart.map k I) x :=
    ((hs.uniform.smooth (hchart.sourceIndex k I) I.1.val.1).contDiffAt
      (s.isOpen_domain.mem_nhds (hmap k I hx))).comp x
      ((hchart.smooth k I).contDiffAt ((hchart.open_domain k I).mem_nhds hx))
  have he : f.amplitude k I =ᶠ[𝓝 x] fun y => (ChartScales.Q I.1.val.1 ^ σ) •
      source (hchart.sourceIndex k I) I.1.val.1 (hchart.map k I y) :=
    eventuallyEq_of_mem ((hchart.open_domain k I).mem_nhds hx) (hchart.amplitude_eq k I)
  rw [iteratedFDeriv_eq_of_eventuallyEq he j]
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

theorem localStrippedClass_of_weighted {s : StripData D} {α σ P : ℝ}
    {w : ι → ℕ → D → ℝ} {source : ι → ℕ → D → ℂ}
    (hs : LocalSourceBounds s h α w source) {hc : SupportCells f}
    (hchart : CommonChart f hc a b h r0 σ source)
    (hmap : ∀ k I, MapsTo (hchart.map k I) (hchart.domain k I) s.domain)
    (hb : PhysicalCopyBounds.CarrierBounds f hc a b h r0)
    (hsmooth : SmoothData f a h r0)
    (hp : ∀ k L, |(f.carrier k L).angular| ≤ P ∧
      |(f.carrier k L).axial| ≤ P ∧ |(f.carrier k L).radial| ≤ P) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ B : ℝ, 1 ≤ B ∧ ∃ p q : ℕ,
      JetData f hc a b h r0 P A B (h * α + σ) p q m := by
  obtain ⟨A, hA, p, hAp⟩ := commonChart_amplitude_bound hs hchart hmap m
  obtain ⟨B, hB, q, hBq⟩ := hb.profile_bound m
  refine ⟨A, hA, B, hB, p, q, hp, ?_⟩
  intro k I z hz hregion hann hcell hts
  constructor
  · intro j hj
    simpa only [Real.rpow_natCast] using jet_bound_at_closure
      (hsmooth.amplitude k I z hz hts).contDiffAt
      (hchart.contains k I z hz hregion hann hcell hts) j
      (fun y hy => hAp k I y hy j hj)
  · intro chart hpolar
    constructor
    · intro j hj
      have he := (hBq k I.1 _ (hb.contains k I z hz hregion hann hcell chart hpolar) j hj).1
      simp only [Real.rpow_natCast]
      exact he
    · intro j hj
      have he := (hBq k I.1 _ (hb.contains k I z hz hregion hann hcell chart hpolar) j hj).2
      simp only [Real.rpow_natCast]
      exact he

theorem physical_sum_jet_bound_of_weighted {s : StripData D} {α σ P : ℝ}
    {w : ι → ℕ → D → ℝ} {source : ι → ℕ → D → ℂ}
    (hsource : LocalSourceBounds s h α w source) {hc : SupportCells f}
    (hchart : CommonChart f hc a b h r0 σ source)
    (hmap : ∀ k I, MapsTo (hchart.map k I) (hchart.domain k I) s.domain)
    (hb : PhysicalCopyBounds.CarrierBounds f hc a b h r0)
    (hr : SupportData f a b h r0 Z Δ) (hs : SmoothData f a h r0)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0)
    (hP : 1 ≤ P) (hp : ∀ k L, |(f.carrier k L).angular| ≤ P ∧
      |(f.carrier k L).axial| ≤ P ∧ |(f.carrier k L).radial| ≤ P) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : SpaceTime,
      z ∈ preterminal → |z.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (f.sum a h r0) z‖ ≤
        C * physicalQ h z ^ (h * α - PhysicalClassBounds.physicalLoss h σ m) := by
  obtain ⟨A, hA, B, hB, p, q, hclass⟩ := localStrippedClass_of_weighted hsource hchart hmap hb hs
    hp m
  obtain ⟨C, hC, hbound⟩ := physical_sum_jet_bound (K := K)
    (b := b) hh hh1 ha hZ hr0 hP hB (Nat.cast_nonneg q) H Δ m
      (h * α + σ) p A hA
  refine ⟨C, hC, ?_⟩
  intro z hz ht
  convert! hbound f hr hs hc hclass z hz ht using 1
  congr 2
  unfold PhysicalClassBounds.physicalLoss
  ring

end LocalWeightedInputs

/-- Direct interface for the actual valid native open patches, including
patches whose raw totalizations need not be smooth on their boundary. -/
theorem SmoothData.of_open_patches
    (UA : K → WaveIndex H → Set LiftPoint) (UP : K → BandLabel → Set PhysicalGraphBounds.Slow)
    (hUA : ∀ k I, IsOpen (UA k I)) (hUP : ∀ k L, IsOpen (UP k L))
    (hA : ∀ k I, ContDiffOn ℝ ∞ (f.amplitude k I) (UA k I))
    (hF : ∀ k L, ContDiffOn ℝ ∞ (f.carrier k L).F (UP k L))
    (hG : ∀ k L, ContDiffOn ℝ ∞ (f.carrier k L).G (UP k L))
    (haCover : ∀ k I w, w ∈ preterminal → w ∈ tsupport (f.term a h r0 I k) →
      commonLift h I.1.val.1 (f.gap I.1) w ∈ UA k I)
    (hpCover : ∀ k I w, w ∈ preterminal → w ∈ tsupport (f.term a h r0 I k) →
      ∀ chart : PolarCharts.Index,
      PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart →
      slotSlow ((f.carrier k I.1).withChart chart) a h I.1.val.1 r0 w ∈ UP k I.1) :
    SmoothData f a h r0 := by
  constructor
  · intro k I w hw hts
    exact SmoothNear.of_open (hUA k I) (hA k I) (haCover k I w hw hts)
  · intro k I w hw hts chart hchart
    exact ⟨SmoothNear.of_open (hUP k I.1) (hF k I.1) (hpCover k I w hw hts chart hchart),
      SmoothNear.of_open (hUP k I.1) (hG k I.1) (hpCover k I w hw hts chart hchart)⟩

theorem JetData.of_stripped {hc : SupportCells f} {P A B g eAmp eBase : ℝ} {m : ℕ}
    (hb : PhysicalCopyBounds.LocalStrippedClass f hc a b h r0 P A B g eAmp eBase m) :
    JetData f hc a b h r0 P A B g eAmp eBase m := by
  refine ⟨hb.parameters, ?_⟩
  intro k I w hw hreg hann hcell _
  exact ⟨hb.amplitude k I w hw hreg hann hcell,
    fun chart hchart => ⟨hb.base_F k I w hw hreg hann hcell chart hchart,
      hb.base_G k I w hw hreg hann hcell chart hchart⟩⟩

/-- The native lattice-center construction proves the support data without
any global smoothness hypotheses on amplitudes or phase profiles. -/
theorem supportData_of_native {F : CopyFamily H TorusInverse.Frequency}
    (g : BandLabel → CommonCoverSolve.Geometry) (U : BandLabel → Set Plane)
    (hgap : ∀ L, (g L).gap = F.gap L)
    (hcenter : ∀ k L, (F.carrier k L).center = nativeCenter (g L) k)
    (hwidth : ∀ L z, z ∈ U L → |PhysicalGraphBounds.etaCoordinate ((g L).basis z)| ≤ r0)
    (hs : ∀ k I x, F.amplitude k I x ≠ 0 → (g I.1).coordinates k x.2 ∈ U I.1)
    (hgap_le : ∀ L, F.gap L ≤ Δ)
    (hgap_native : ∀ L, F.gap L ≤ ChartScales.nativeIndex h L.val.1)
    (hint : ∀ k L, ∃ m : ℤ,
      (ChartScales.carrier h L.val.1 : ℝ) * (F.carrier k L).angular = (m : ℝ))
    (hgeo : ∀ k I y, F.amplitude k I (commonLift h I.1.val.1 (F.gap I.1) y) ≠ 0 →
      PhysicalGraphBounds.scaledRadial I.1.val.1 y ∈ PhysicalGraphBounds.annulus a b ∧
      ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h I.1.val.1 y)‖ ≤ Z)
    (hmask : ∀ k I y, y ∈ preterminal →
      F.amplitude k I (commonLift h I.1.val.1 (F.gap I.1) y) ≠ 0 →
      physicalMask (CoordinateAlgebra.D h) I.1.val (physicalParams h y) ≠ 0) :
    SupportData F a b h r0 Z Δ := by
  refine ⟨hgap_le, hgap_native, hint, ?_, hmask⟩
  intro k I y hy
  refine ⟨(hgeo k I y hy).1, (hgeo k I y hy).2, ?_⟩
  rw [hcenter]
  exact physical_native_width (g I.1) k h I.1.val.1 (F.gap I.1) (hgap I.1)
    (hwidth I.1) y (hs k I _ hy)

/-! ## Real Cartesian vectors -/

theorem vectorSum_smooth {f : Fin 3 → CopyFamily H K}
    (hr : ∀ i, SupportData (f i) a b h r0 Z Δ)
    (hs : ∀ i, SmoothData (f i) a h r0)
    (hc : ∀ i, SupportCells (f i)) (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (PhysicalCopyBounds.vectorSum f a h r0) preterminal := by
  apply ContDiffOn.sum
  intro i _
  exact (realCoordinate i).contDiff.comp_contDiffOn ((hr i).sum_smooth (hs i) (hc i) ha hh hh1)

theorem vectorSum_jet_bound {f : Fin 3 → CopyFamily H K}
    (hr : ∀ i, SupportData (f i) a b h r0 Z Δ)
    (hs : ∀ i, SmoothData (f i) a h r0)
    (hc : ∀ i, SupportCells (f i)) (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (hw : w ∈ preterminal) (m : ℕ) {B : ℝ}
    (hb : ∀ i, ‖iteratedFDeriv ℝ m ((f i).sum a h r0) w‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (PhysicalCopyBounds.vectorSum f a h r0) w‖ ≤ 3 * B := by
  have hlocal i : ContDiffAt ℝ m ((f i).sum a h r0) w :=
    (((hr i).sum_smooth (hs i) (hc i) ha hh hh1).contDiffAt
      (preterminal_open.mem_nhds hw)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)
  unfold PhysicalCopyBounds.vectorSum
  rw [iteratedFDeriv_finset_sum_at (f := fun i y => realCoordinate i ((f i).sum a h r0 y))
    Finset.univ
    (fun i _ => (realCoordinate i).contDiff.contDiffAt.comp w (hlocal i))]
  calc
    _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ m (fun y => realCoordinate i ((f i).sum a h r0 y)) w‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, B := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_jet_linear_comp_at (hlocal i) (realCoordinate i)).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (norm_realCoordinate_le i)).trans (hb i))
    _ = 3 * B := by simp

theorem physical_vector_sum_jet_bound {h a b Z r0 P B eBase : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (H Δ m : ℕ) (g eAmp A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Fin 3 → CopyFamily H K,
      (∀ i, SupportData (f i) a b h r0 Z Δ) →
      (∀ i, SmoothData (f i) a h r0) → ∀ hc : ∀ i, SupportCells (f i),
      (∀ i, JetData (f i) (hc i) a b h r0 P A B g eAmp eBase m) →
      ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (PhysicalCopyBounds.vectorSum f a h r0) w‖ ≤
        C * physicalQ h w ^ (g - PhysicalGraphBounds.waveLoss h m) := by
  obtain ⟨C, hC, hb⟩ := physical_sum_jet_bound (K := K) (b := b)
    hh hh1 ha hZ hr0 hP hB heBase H Δ m g eAmp A hA
  refine ⟨3 * C, by positivity, ?_⟩
  intro f hr hs hc hclass w hw ht
  exact (vectorSum_jet_bound hr hs hc ha hh hh1 hw m
    (fun i => hb (f i) (hr i) (hs i) (hc i) (hclass i) w hw ht)).trans_eq (by ring)

section WeightedVector

open WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {ι : Type*}

theorem physical_vector_sum_jet_bound_of_weighted {s : StripData D} {α σ P : ℝ}
    {w : ι → ℕ → D → ℝ} {source : ι → ℕ → D → ℂ}
    (hsource : LocalSourceBounds s h α w source) {f : Fin 3 → CopyFamily H K}
    (hc : ∀ i, SupportCells (f i))
    (hchart : ∀ i, CommonChart (f i) (hc i) a b h r0 σ source)
    (hmap : ∀ i k I, MapsTo ((hchart i).map k I) ((hchart i).domain k I) s.domain)
    (hb : ∀ i, PhysicalCopyBounds.CarrierBounds (f i) (hc i) a b h r0)
    (hr : ∀ i, SupportData (f i) a b h r0 Z Δ)
    (hs : ∀ i, SmoothData (f i) a h r0)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0)
    (hP : 1 ≤ P) (hp : ∀ i k L, |((f i).carrier k L).angular| ≤ P ∧
      |((f i).carrier k L).axial| ≤ P ∧ |((f i).carrier k L).radial| ≤ P) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : SpaceTime,
      z ∈ preterminal → |z.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (PhysicalCopyBounds.vectorSum f a h r0) z‖ ≤
        C * physicalQ h z ^ (h * α - PhysicalClassBounds.physicalLoss h σ m) := by
  classical
  have hbnd := fun i => physical_sum_jet_bound_of_weighted hsource (hchart i) (hmap i)
    (hb i) (hr i) (hs i) hh hh1 ha hZ hr0 hP (hp i) m
  choose C hC hbound using hbnd
  refine ⟨3 * ∑ i : Fin 3, C i,
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => hC i)), ?_⟩
  intro z hz ht
  have hq := physicalQ_pos hh hh1 hz
  have hi (i : Fin 3) : C i ≤ ∑ j : Fin 3, C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  have he := vectorSum_jet_bound hr hs hc ha hh hh1 hz m
    (B := (∑ i : Fin 3, C i) * physicalQ h z ^ (h * α - PhysicalClassBounds.physicalLoss h σ m))
    (fun i => (hbound i z hz ht).trans
      (mul_le_mul_of_nonneg_right (hi i) (Real.rpow_pos_of_pos hq _).le))
  exact he.trans_eq (by ring)

end WeightedVector

end NavierStokes.LocalPhysicalCopyBounds
