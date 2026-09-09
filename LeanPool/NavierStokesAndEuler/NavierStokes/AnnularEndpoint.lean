/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalCopyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityApproach
public import LeanPool.NavierStokesAndEuler.NavierStokes.TailGaugePotential

@[expose] public section

/-!
# Terminal extensions from a common shrinking outer support

The actual similarity coordinate tends jointly to zero at a terminal point
whose axial coordinate is zero.  A family supported inside a common multiple
of its square root therefore vanishes on one common open past neighborhood
of every nonzero such point.  This argument applies before summing or taking
the spatial curl, and requires neither a lower support radius nor estimates
on the individual summands.
-/

noncomputable section

namespace NavierStokes.AnnularEndpoint

open Set Filter Function
open scoped Topology ContDiff BigOperators

abbrev Space := ProblemStatement.Space
abbrev SpaceTime := ProblemStatement.SpaceTime

/-- The actual Cartesian distance to the symmetry axis. -/
noncomputable def radius (w : SpaceTime) : ℝ :=
  PolarCharts.radius (PhysicalGraphBounds.radialProjection w)

theorem radius_continuous : Continuous radius :=
  PolarCharts.radius_continuous.comp PhysicalGraphBounds.radialProjection.continuous

theorem radius_nonneg (w : SpaceTime) : 0 ≤ radius w :=
  PolarCharts.radius_nonneg _

theorem radius_pos_at_terminal {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) :
    0 < radius (1, x) := by
  have hs := SlowBaseEndpoint.radialEnergy_pos_of_nonzero_of_axial_zero hx hz
  apply Real.sqrt_pos.mpr
  change 0 < x 0 ^ 2 + x 1 ^ 2
  dsimp only [AxisymmetricFields.radialEnergy] at hs
  linarith

/-- The support radius uses the same physical similarity coordinate as the
wave construction, rather than a separately postulated scale. -/
noncomputable def outerRadius (h C : ℝ) (w : SpaceTime) : ℝ :=
  C * Real.sqrt (PhysicalWaveSum.physicalQ h w)

theorem physicalQ_tendsto_zero {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : Space} (hz : x 2 = 0) :
    Tendsto (PhysicalWaveSum.physicalQ h) (𝓝[SpacetimeEndpoint.openPast 1] (1, x)) (𝓝 0) := by
  apply SimilarityApproach.physical_q_tendsto_zero hh hh1
  · exact continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · change Tendsto (fun w : SpaceTime => w.2 2)
      (𝓝[SpacetimeEndpoint.openPast 1] (1, x)) (𝓝 0)
    have hc : Tendsto (fun w : SpaceTime => w.2 2) (𝓝 (1, x)) (𝓝 (x 2)) :=
      ((AxisymmetricFields.projection 2).continuous.comp continuous_snd).tendsto (1, x)
    rw [hz] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact hw.1

theorem outerRadius_tendsto_zero {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) {x : Space} (hz : x 2 = 0) :
    Tendsto (outerRadius h C) (𝓝[SpacetimeEndpoint.openPast 1] (1, x)) (𝓝 0) := by
  have he := tendsto_const_nhds (x := C) |>.mul (Real.continuous_sqrt.continuousAt.tendsto.comp
      (physicalQ_tendsto_zero hh hh1 hz))
  simp only [Real.sqrt_zero, mul_zero] at he ⊢
  exact he

theorem outerRadius_continuousAt {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1) : ContinuousAt (outerRadius h C) w :=
  continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
    (PhysicalWaveSum.physicalQ_smoothAt hh hh1 ht).continuousAt)

/-- One geometric neighborhood works for every member of any family with
the same outer support constant.  No sign or size assumption on `C` is needed. -/
theorem exists_separating_neighborhood {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) :
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      ∀ w ∈ U, w.1 < 1 → outerRadius h C w < radius w := by
  have hr := radius_pos_at_terminal hx hz
  have hout := (outerRadius_tendsto_zero hh hh1 C hz).eventually
    (gt_mem_nhds (half_pos hr))
  have hin := (radius_continuous.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := SpacetimeEndpoint.openPast 1))).eventually
      (lt_mem_nhds (half_lt_self hr))
  have he : ∀ᶠ w in 𝓝[SpacetimeEndpoint.openPast 1] (1, x),
      outerRadius h C w < radius w := by
    filter_upwards [hout, hin] with w ho hi
    exact ho.trans hi
  obtain ⟨U, hU, hxU, hsep⟩ := mem_nhdsWithin.mp he
  exact ⟨U, hU, hxU, fun w hw ht => hsep ⟨hw, ht, mem_univ _⟩⟩

section Support

variable {V : Type*} [Zero V]

/-- A pointwise physical support invariant.  It contains no endpoint or
derivative assertion. -/
def ShrinkingSupport (h C : ℝ) (f : SpaceTime → V) : Prop :=
  ∀ w, w.1 < 1 → f w ≠ 0 → radius w ≤ outerRadius h C w

theorem ShrinkingSupport.zero_of_separated {h C : ℝ} {f : SpaceTime → V}
    (hf : ShrinkingSupport h C f) {w : SpaceTime} (ht : w.1 < 1)
    (hs : outerRadius h C w < radius w) : f w = 0 := by
  by_contra hn
  exact (not_lt_of_ge (hf w ht hn)) hs

/-- Zero-preserving pointwise reconstructions, including real parts and
vector-valued coefficient maps, preserve the physical support invariant. -/
theorem ShrinkingSupport.map_zero {W : Type*} [Zero W] {h C : ℝ}
    {f : SpaceTime → V} (hf : ShrinkingSupport h C f)
    (T : SpaceTime → V → W) (hT : ∀ w, T w 0 = 0) :
    ShrinkingSupport h C (fun w => T w (f w)) := by
  intro w ht hn
  apply hf w ht
  intro hz
  exact hn (by simpa only [hz] using hT w)

theorem exists_common_zero_neighborhood {ι : Type*} {h C : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ι → SpaceTime → V}
    (hf : ∀ i, ShrinkingSupport h C (f i)) {x : Space}
    (hx : x ≠ 0) (hz : x 2 = 0) :
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      ∀ w ∈ U, w.1 < 1 → ∀ i, f i w = 0 := by
  obtain ⟨U, hU, hxU, hs⟩ := exists_separating_neighborhood hh hh1 C hx hz
  exact ⟨U, hU, hxU, fun w hw ht i => (hf i).zero_of_separated ht (hs w hw ht)⟩

theorem exists_zero_neighborhood {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : SpaceTime → V} (hf : ShrinkingSupport h C f) {x : Space}
    (hx : x ≠ 0) (hz : x 2 = 0) :
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      EqOn f (fun _ => 0) (U ∩ SpacetimeEndpoint.openPast 1) := by
  obtain ⟨U, hU, hxU, hs⟩ := exists_separating_neighborhood hh hh1 C hx hz
  exact ⟨U, hU, hxU, fun w hw => hf.zero_of_separated hw.2.1 (hs w hw.1 hw.2.1)⟩

end Support

section Sums

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Multiplying a correction by any scalar cutoff preserves its outer
support; the cutoff can depend on all physical variables. -/
theorem ShrinkingSupport.smul {h C : ℝ} {f : SpaceTime → V}
    (hf : ShrinkingSupport h C f) (c : SpaceTime → ℝ) :
    ShrinkingSupport h C (fun w => c w • f w) := by
  intro w ht hn
  apply hf w ht
  intro hz
  exact hn (by simp only [hz, smul_zero])

omit [NormedSpace ℝ V] in
theorem ShrinkingSupport.add {h C : ℝ} {f g : SpaceTime → V}
    (hf : ShrinkingSupport h C f) (hg : ShrinkingSupport h C g) :
    ShrinkingSupport h C (fun w => f w + g w) := by
  intro w ht hn
  by_contra hs
  exact hn (by simp only [hf.zero_of_separated ht (lt_of_not_ge hs),
    hg.zero_of_separated ht (lt_of_not_ge hs), add_zero])

omit [NormedSpace ℝ V] in
theorem ShrinkingSupport.finset_sum {ι : Type*} {h C : ℝ} {f : ι → SpaceTime → V}
    (s : Finset ι) (hf : ∀ i ∈ s, ShrinkingSupport h C (f i)) :
    ShrinkingSupport h C (fun w => ∑ i ∈ s, f i w) := by
  intro w ht hn
  by_contra hs
  apply hn
  apply Finset.sum_eq_zero
  intro i hi
  exact (hf i hi).zero_of_separated ht (lt_of_not_ge hs)

omit [NormedSpace ℝ V] in
theorem ShrinkingSupport.tsum {ι : Type*} {h C : ℝ} {f : ι → SpaceTime → V}
    (hf : ∀ i, ShrinkingSupport h C (f i)) :
    ShrinkingSupport h C (fun w => ∑' i, f i w) := by
  intro w ht hn
  by_contra hs
  apply hn
  have he : ∀ i, f i w = 0 := fun i => (hf i).zero_of_separated ht (lt_of_not_ge hs)
  simp only [he, tsum_zero]

omit [NormedSpace ℝ V] in
theorem ShrinkingSupport.finsum {ι : Type*} {h C : ℝ} {f : ι → SpaceTime → V}
    (hf : ∀ i, ShrinkingSupport h C (f i)) :
    ShrinkingSupport h C (fun w => ∑ᶠ i, f i w) := by
  intro w ht hn
  by_contra hs
  apply hn
  apply finsum_eq_zero_of_forall_eq_zero
  intro i
  exact (hf i).zero_of_separated ht (lt_of_not_ge hs)

theorem ShrinkingSupport.potentialSum {h C : ℝ} {f : ℕ → SpaceTime → V}
    (hf : ∀ j, ShrinkingSupport h C (f j)) (a : ℕ → ℝ) (q : SpaceTime → ℝ) :
    ShrinkingSupport h C (SolenoidalDiagonal.potentialSum a q f) :=
  ShrinkingSupport.tsum (fun j => (hf j).smul
    (fun w => SmoothCutoffs.scaledCutoff (a j) (q w)))

end Sums

section WaveSupport

/-- The normalized annulus and the actual dyadic-mask comparison imply a
uniform physical outer radius.  The product norm costs a factor of two. -/
theorem radius_le_of_scaled_annulus {a b q : ℝ} {n : ℕ} {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b)
    (hQ : ChartScales.Q n ≤ 2 * q) :
    radius w ≤ (2 * b * Real.sqrt 2) * Real.sqrt q := by
  have hn : ‖PhysicalGraphBounds.scaledRadial n w‖ ≤ b := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1
  have hb : 0 ≤ b := (norm_nonneg _).trans hn
  have hr : PolarCharts.radius (PhysicalGraphBounds.scaledRadial n w) ≤ 2 * b :=
    (PolarCharts.radius_le_two_norm _).trans (mul_le_mul_of_nonneg_left hn (by norm_num))
  have he : radius w = Real.sqrt (ChartScales.Q n) *
      PolarCharts.radius (PhysicalGraphBounds.scaledRadial n w) := by
    unfold radius
    rw [← PhysicalGraphBounds.unscale_radial n w,
      PolarCharts.radius_smul (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _),
      ← Real.sqrt_eq_rpow]
  calc
    radius w ≤ Real.sqrt (ChartScales.Q n) * (2 * b) := by
      rw [he]
      exact mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (2 * q) * (2 * b) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hQ) (mul_nonneg (by norm_num) hb)
    _ = (2 * b * Real.sqrt 2) * Real.sqrt q := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem shrinkingSupport_of_normalized_annulus {V : Type*} [Zero V]
    {a b h : ℝ} {f : SpaceTime → V}
    (hf : ∀ w, w.1 < 1 → f w ≠ 0 → ∃ n : ℕ,
      PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b ∧
      ChartScales.Q n ≤ 2 * PhysicalWaveSum.physicalQ h w) :
    ShrinkingSupport h (2 * b * Real.sqrt 2) f := by
  intro w ht hn
  obtain ⟨n, ha, hq⟩ := hf w ht hn
  exact radius_le_of_scaled_annulus ha hq

/-- An adapter from the already constructed scalar physical wave family.
This uses its actual amplitude support and its actual slow mask. -/
theorem regularFamily_term_support {H : ℕ} {f : PhysicalWaveSum.WaveFamily H}
    {a b h r0 Z : ℝ} {Δ : ℕ}
    (hf : PhysicalWaveSum.RegularFamily f a b h r0 Z Δ)
    (I : PhysicalWaveSum.WaveIndex H) :
    ShrinkingSupport h (2 * b * Real.sqrt 2) (f.term a h r0 I) := by
  apply shrinkingSupport_of_normalized_annulus
  intro w ht hn
  exact ⟨I.1.val.1, (hf.geometry_support I w
    (PhysicalWaveSum.globalWave_ne_zero_amp hn)).1,
    (PhysicalWaveSum.labelRegion_active_relation (hf.term_support I w ht hn)).2⟩

theorem regularFamily_sum_support {H : ℕ} {f : PhysicalWaveSum.WaveFamily H}
    {a b h r0 Z : ℝ} {Δ : ℕ}
    (hf : PhysicalWaveSum.RegularFamily f a b h r0 Z Δ) :
    ShrinkingSupport h (2 * b * Real.sqrt 2) (f.sum a h r0) :=
  ShrinkingSupport.finsum (regularFamily_term_support hf)

/-- The complete physical copy-and-label sum has the same outer support.
The support witness keeps the individual copy and its own carrier center. -/
theorem copyFamily_sum_support {H Δ : ℕ} {K : Type*}
    {f : PhysicalCopyBounds.CopyFamily H K} {a b h r0 Z : ℝ}
    (hf : PhysicalCopyBounds.RegularFamily f a b h r0 Z Δ) :
    ShrinkingSupport h (2 * b * Real.sqrt 2) (f.sum a h r0) := by
  apply shrinkingSupport_of_normalized_annulus
  intro w ht hn
  obtain ⟨I, _, _, ha, hm⟩ := hf.sum_support ht hn
  exact ⟨I.1.val.1, ha, (PhysicalWaveSum.labelRegion_active_relation hm).2⟩

theorem copyFamily_real_sum_support {H Δ : ℕ} {K : Type*}
    {f : PhysicalCopyBounds.CopyFamily H K} {a b h r0 Z : ℝ}
    (hf : PhysicalCopyBounds.RegularFamily f a b h r0 Z Δ) :
    ShrinkingSupport h (2 * b * Real.sqrt 2) (fun w => (f.sum a h r0 w).re) :=
  (copyFamily_sum_support hf).map_zero (fun _ z => z.re) (by intro; rfl)

theorem copyFamily_vector_support {H Δ : ℕ} {K : Type*}
    {f : Fin 3 → PhysicalCopyBounds.CopyFamily H K} {a b h r0 Z : ℝ}
    (hf : ∀ i, PhysicalCopyBounds.RegularFamily (f i) a b h r0 Z Δ) :
    ShrinkingSupport h (2 * b * Real.sqrt 2) (PhysicalCopyBounds.vectorSum f a h r0) := by
  apply ShrinkingSupport.finset_sum
  intro i _
  exact (copyFamily_sum_support (hf i)).map_zero
    (fun _ z => PhysicalWaveSum.realCoordinate i z) (by intro; simp)

end WaveSupport

section Extensions

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
theorem zero_germ_of_eqOn {f : SpaceTime → V} {U : Set SpaceTime}
    (hU : IsOpen U) (hf : EqOn f (fun _ => 0) (U ∩ SpacetimeEndpoint.openPast 1))
    {w : SpaceTime} (hw : w ∈ U) (ht : w.1 < 1) :
    f =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [(hU.inter (SpacetimeEndpoint.openPast_isOpen 1)).mem_nhds
    (show w ∈ U ∩ SpacetimeEndpoint.openPast 1 from ⟨hw, ht, mem_univ _⟩)] with y hy
  exact hf hy

omit [NormedSpace ℝ V] in
/-- At every preterminal point strictly outside the support radius the
field is zero on an ambient neighborhood. -/
theorem ShrinkingSupport.zero_germ {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : SpaceTime → V} (hf : ShrinkingSupport h C f) {w : SpaceTime}
    (ht : w.1 < 1) (hs : outerRadius h C w < radius w) :
    f =ᶠ[𝓝 w] fun _ => 0 := by
  have he := (outerRadius_continuousAt hh hh1 ht).eventually_lt
    radius_continuous.continuousAt hs
  filter_upwards [he, PhysicalWaveSum.preterminal_open.mem_nhds ht] with y hy hyt
  exact hf.zero_of_separated hyt hy

theorem ShrinkingSupport.derivative_support {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : SpaceTime → V} (hf : ShrinkingSupport h C f) (m : ℕ) :
    ShrinkingSupport h C (iteratedFDeriv ℝ m f) := by
  intro w ht hn
  by_contra hs
  have he := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (hf.zero_germ hh hh1 ht (lt_of_not_ge hs)) m).self_of_nhds
  apply hn
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using he

/-- Actual joint derivatives vanish on the same open past neighborhood. -/
theorem jets_zero_of_eqOn {f : SpaceTime → V} {U : Set SpaceTime}
    (hU : IsOpen U) (hf : EqOn f (fun _ => 0) (U ∩ SpacetimeEndpoint.openPast 1))
    (m : ℕ) : EqOn (iteratedFDeriv ℝ m f) (fun _ => 0)
      (U ∩ SpacetimeEndpoint.openPast 1) := by
  intro w hw
  have he := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (zero_germ_of_eqOn hU hf hw.1 hw.2.1)
    m).self_of_nhds
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using he

/-- The extension is the literal zero function on an actual ambient open
neighborhood, not only a limiting boundary value. -/
noncomputable def zeroExtension {f : SpaceTime → V} {x : Space} {U : Set SpaceTime}
    (hU : IsOpen U) (hxU : (1, x) ∈ U)
    (hf : EqOn f (fun _ => 0) (U ∩ SpacetimeEndpoint.openPast 1)) :
    JointResidualLimits.OneSidedExtension f x where
  value := fun _ => 0
  domain := U
  isOpen := hU
  mem := hxU
  smooth := contDiffOn_const
  agrees := hf.symm

theorem ShrinkingSupport.oneSidedExtension {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : SpaceTime → V} (hf : ShrinkingSupport h C f) {x : Space}
    (hx : x ≠ 0) (hz : x 2 = 0) : Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  obtain ⟨U, hU, hxU, hfU⟩ := exists_zero_neighborhood hh hh1 hf hx hz
  exact ⟨zeroExtension hU hxU hfU⟩

theorem ShrinkingSupport.jets_eventually_zero {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : SpaceTime → V} (hf : ShrinkingSupport h C f) {x : Space}
    (hx : x ≠ 0) (hz : x 2 = 0) (m : ℕ) :
    iteratedFDeriv ℝ m f =ᶠ[𝓝[SpacetimeEndpoint.openPast 1] (1, x)] fun _ => 0 := by
  obtain ⟨U, hU, hxU, hfU⟩ := exists_zero_neighborhood hh hh1 hf hx hz
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hxU), self_mem_nhdsWithin] with w hw ht
  exact jets_zero_of_eqOn hU hfU m ⟨hw, ht⟩

theorem ShrinkingSupport.jets_tendsto_zero {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : SpaceTime → V} (hf : ShrinkingSupport h C f) {x : Space}
    (hx : x ≠ 0) (hz : x 2 = 0) (m : ℕ) :
    Tendsto (iteratedFDeriv ℝ m f) (𝓝[SpacetimeEndpoint.openPast 1] (1, x)) (𝓝 0) :=
  tendsto_const_nhds.congr' (hf.jets_eventually_zero hh hh1 hx hz m).symm

/-- The support argument supplies the central-plane branch.  Extensions
at nonzero axial coordinate remain a separate, explicit input. -/
theorem awayExtensions_of_offplane {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : SpaceTime → V} (hf : ShrinkingSupport h C f)
    (hoff : ∀ x : Space, x 2 ≠ 0 → Nonempty (JointResidualLimits.OneSidedExtension f x)) :
    JointResidualLimits.AwayExtensions f := by
  intro x hx
  by_cases hz : x 2 = 0
  · exact hf.oneSidedExtension hh hh1 hx hz
  · exact hoff x hz

/-- Adding a correction which vanishes on a past neighborhood preserves
the literal extension of the base field on the intersection. -/
noncomputable def addZeroExtension {f g : SpaceTime → V} {x : Space}
    (e : JointResidualLimits.OneSidedExtension f x) {U : Set SpaceTime}
    (hU : IsOpen U) (hxU : (1, x) ∈ U)
    (hg : EqOn g (fun _ => 0) (U ∩ SpacetimeEndpoint.openPast 1)) :
    JointResidualLimits.OneSidedExtension (fun w => f w + g w) x where
  value := e.value
  domain := e.domain ∩ U
  isOpen := e.isOpen.inter hU
  mem := ⟨e.mem, hxU⟩
  smooth := e.smooth.mono inter_subset_left
  agrees := by
    intro w hw
    change e.value w = f w + g w
    rw [hg ⟨hw.1.2, hw.2⟩, add_zero]
    exact e.agrees ⟨hw.1.1, hw.2⟩

theorem add_supported_extension {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f g : SpaceTime → V} {x : Space}
    (e : JointResidualLimits.OneSidedExtension f x) (hg : ShrinkingSupport h C g)
    (hx : x ≠ 0) (hz : x 2 = 0) :
    Nonempty (JointResidualLimits.OneSidedExtension (fun w => f w + g w) x) := by
  obtain ⟨U, hU, hxU, hgU⟩ := exists_zero_neighborhood hh hh1 hg hx hz
  exact ⟨addZeroExtension e hU hxU hgU⟩

end Extensions

section Curl

theorem ShrinkingSupport.spatialCurl {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {A : SpaceTime → Space} (hA : ShrinkingSupport h C A) :
    ShrinkingSupport h C (SpatialCurl.spatialCurl A) := by
  intro w ht hn
  by_contra hs
  have he := SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq
    (hA.zero_germ hh hh1 ht (lt_of_not_ge hs))
  exact hn (he.trans (SpatialCurl.curl_zero _))

/-- The extension of a potential yields the extension of its actual
Cartesian spatial curl. -/
noncomputable def curlExtension {A : SpaceTime → Space} {x : Space}
    (e : JointResidualLimits.OneSidedExtension A x) :
    JointResidualLimits.OneSidedExtension (SpatialCurl.spatialCurl A) x where
  value := SpatialCurl.spatialCurl e.value
  domain := e.domain
  isOpen := e.isOpen
  mem := e.mem
  smooth := by
    intro w hw
    exact (SpatialCurl.contDiffAt_spatialCurl
      (e.smooth.contDiffAt (e.isOpen.mem_nhds hw)) (by simp)).contDiffWithinAt
  agrees := by
    intro w hw
    apply SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq
    filter_upwards [(e.isOpen.inter (SpacetimeEndpoint.openPast_isOpen 1)).mem_nhds hw]
      with y hy
    exact e.agrees hy

end Curl

section Diagonal

/-- One neighborhood kills both complete diagonal sums, their actual
curl, and every joint derivative.  The scalar cutoffs are arbitrary. -/
theorem diagonal_sums_zero_near_terminal {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {A : ℕ → SpaceTime → Space} {p : ℕ → SpaceTime → ℝ}
    (hA : ∀ j, ShrinkingSupport h C (A j)) (hp : ∀ j, ShrinkingSupport h C (p j))
    (a : ℕ → ℝ) (q : SpaceTime → ℝ) {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) :
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      EqOn (SolenoidalDiagonal.potentialSum a q A) (fun _ => 0)
        (U ∩ SpacetimeEndpoint.openPast 1) ∧
      EqOn (SolenoidalDiagonal.potentialSum a q p) (fun _ => 0)
        (U ∩ SpacetimeEndpoint.openPast 1) ∧
      EqOn (SolenoidalDiagonal.velocitySum a q A) (fun _ => 0)
        (U ∩ SpacetimeEndpoint.openPast 1) ∧
      ∀ m : ℕ,
        EqOn (iteratedFDeriv ℝ m (SolenoidalDiagonal.potentialSum a q A)) (fun _ => 0)
          (U ∩ SpacetimeEndpoint.openPast 1) ∧
        EqOn (iteratedFDeriv ℝ m (SolenoidalDiagonal.potentialSum a q p)) (fun _ => 0)
          (U ∩ SpacetimeEndpoint.openPast 1) ∧
        EqOn (iteratedFDeriv ℝ m (SolenoidalDiagonal.velocitySum a q A)) (fun _ => 0)
          (U ∩ SpacetimeEndpoint.openPast 1) := by
  obtain ⟨U, hU, hxU, hsep⟩ := exists_separating_neighborhood hh hh1 C hx hz
  have hAS := ShrinkingSupport.potentialSum hA a q
  have hpS := ShrinkingSupport.potentialSum hp a q
  have hvS := hAS.spatialCurl hh hh1
  have hAz : EqOn (SolenoidalDiagonal.potentialSum a q A) (fun _ => 0)
      (U ∩ SpacetimeEndpoint.openPast 1) :=
    fun w hw => hAS.zero_of_separated hw.2.1 (hsep w hw.1 hw.2.1)
  have hpz : EqOn (SolenoidalDiagonal.potentialSum a q p) (fun _ => 0)
      (U ∩ SpacetimeEndpoint.openPast 1) :=
    fun w hw => hpS.zero_of_separated hw.2.1 (hsep w hw.1 hw.2.1)
  have hvz : EqOn (SolenoidalDiagonal.velocitySum a q A) (fun _ => 0)
      (U ∩ SpacetimeEndpoint.openPast 1) :=
    fun w hw => hvS.zero_of_separated hw.2.1 (hsep w hw.1 hw.2.1)
  exact ⟨U, hU, hxU, hAz, hpz, hvz, fun m =>
    ⟨jets_zero_of_eqOn hU hAz m, jets_zero_of_eqOn hU hpz m,
      jets_zero_of_eqOn hU hvz m⟩⟩

/-- Add the actual diagonal sum before taking any velocity derivative. -/
noncomputable def diagonalAddition {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : SpaceTime → V) (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (F : ℕ → SpaceTime → V) (w : SpaceTime) : V :=
  f w + SolenoidalDiagonal.potentialSum a q F w

theorem diagonal_addition_extension {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : SpaceTime → V} {F : ℕ → SpaceTime → V}
    (hF : ∀ j, ShrinkingSupport h C (F j)) (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) (e : JointResidualLimits.OneSidedExtension f x) :
    Nonempty (JointResidualLimits.OneSidedExtension (diagonalAddition f a q F) x) :=
  add_supported_extension hh hh1 e (ShrinkingSupport.potentialSum hF a q) hx hz

/-- Exact local agreement includes the concrete nonlinear Cartesian
residual, without an assumed residual estimate. -/
theorem diagonal_addition_germs {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (A0 : SpaceTime → Space) (p0 : SpaceTime → ℝ)
    {A : ℕ → SpaceTime → Space} {p : ℕ → SpaceTime → ℝ}
    (hA : ∀ j, ShrinkingSupport h C (A j)) (hp : ∀ j, ShrinkingSupport h C (p j))
    (a : ℕ → ℝ) (q : SpaceTime → ℝ) {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) :
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      ∀ w ∈ U, w.1 < 1 →
        diagonalAddition A0 a q A =ᶠ[𝓝 w] A0 ∧
        SpatialCurl.spatialCurl (diagonalAddition A0 a q A) =ᶠ[𝓝 w]
          SpatialCurl.spatialCurl A0 ∧
        diagonalAddition p0 a q p =ᶠ[𝓝 w] p0 ∧
        (fun z => ProblemStatement.navierStokesResidual
          (SpatialCurl.spatialCurl (diagonalAddition A0 a q A))
          (diagonalAddition p0 a q p) z.1 z.2) =ᶠ[𝓝 w]
        (fun z => ProblemStatement.navierStokesResidual
          (SpatialCurl.spatialCurl A0) p0 z.1 z.2) := by
  obtain ⟨U, hU, hxU, hAz, hpz, _, _⟩ :=
    diagonal_sums_zero_near_terminal hh hh1 hA hp a q hx hz
  refine ⟨U, hU, hxU, ?_⟩
  intro w hw ht
  have hAg : diagonalAddition A0 a q A =ᶠ[𝓝 w] A0 := by
    filter_upwards [zero_germ_of_eqOn hU hAz hw ht] with y hy
    simp only [diagonalAddition, hy, add_zero]
  have hpg : diagonalAddition p0 a q p =ᶠ[𝓝 w] p0 := by
    filter_upwards [zero_germ_of_eqOn hU hpz hw ht] with y hy
    simp only [diagonalAddition, hy, add_zero]
  have hvg := SolenoidalDiagonal.spatialCurl_eventuallyEq hAg
  exact ⟨hAg, hvg, hpg, ResidualRegularity.residual_eventuallyEq hvg hpg⟩

end Diagonal

/-- Local smooth field extensions determine a smooth extension of the
actual Navier--Stokes residual by its differential formula. -/
noncomputable def residualExtension {u : SpaceTime → Space} {p : SpaceTime → ℝ}
    {x : Space} (eu : JointResidualLimits.OneSidedExtension u x)
    (ep : JointResidualLimits.OneSidedExtension p x) :
    JointResidualLimits.OneSidedExtension
      (fun w => ProblemStatement.navierStokesResidual u p w.1 w.2) x where
  value := fun w => ProblemStatement.navierStokesResidual eu.value ep.value w.1 w.2
  domain := eu.domain ∩ ep.domain
  isOpen := eu.isOpen.inter ep.isOpen
  mem := ⟨eu.mem, ep.mem⟩
  smooth := ResidualRegularity.contDiffOn_residual (eu.isOpen.inter ep.isOpen)
    (eu.smooth.mono inter_subset_left) (ep.smooth.mono inter_subset_right)
  agrees := by
    intro w hw
    apply ResidualRegularity.residual_congr
    · filter_upwards [(eu.isOpen.inter (SpacetimeEndpoint.openPast_isOpen 1)).mem_nhds
        ⟨hw.1.1, hw.2⟩] with y hy
      exact eu.agrees hy
    · filter_upwards [(ep.isOpen.inter (SpacetimeEndpoint.openPast_isOpen 1)).mem_nhds
        ⟨hw.1.2, hw.2⟩] with y hy
      exact ep.agrees hy

section FinalBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- Apply the shrinking-support construction to the actual selected
slow-base potential in the terminally smooth radial gauge.  All correction
orders are retained.  This assertion is at the central plane only. -/
theorem final_diagonal_extensions (upper : ℝ) (B : ℕ) {C : ℝ}
    {A : ℕ → SpaceTime → Space} {p : ℕ → SpaceTime → ℝ}
    (hA : ∀ j, ShrinkingSupport F.data.h C (A j))
    (hp : ∀ j, ShrinkingSupport F.data.h C (p j))
    (a : ℕ → ℝ) (q : SpaceTime → ℝ) {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) :
    let A' := diagonalAddition (TailGaugePotential.finalPotential H v upper B) a q A
    let p' := diagonalAddition (FinalSlowBase.pressure H v upper B) a q p
    Nonempty (JointResidualLimits.OneSidedExtension A' x) ∧
      Nonempty (JointResidualLimits.OneSidedExtension (SpatialCurl.spatialCurl A') x) ∧
      Nonempty (JointResidualLimits.OneSidedExtension p' x) ∧
      Nonempty (JointResidualLimits.OneSidedExtension
        (fun w => ProblemStatement.navierStokesResidual (SpatialCurl.spatialCurl A') p' w.1 w.2) x)
          := by
  obtain ⟨eA0⟩ := TailGaugePotential.finalPotential_awayExtensions H v upper B x hx
  obtain ⟨ep0⟩ := (SlowBaseEndpoint.final_fields_awayExtensions H v upper B).2 x hx
  obtain ⟨eA⟩ := diagonal_addition_extension F.data.h_pos F.data.h_lt_half hA a q hx hz eA0
  obtain ⟨ep⟩ := diagonal_addition_extension F.data.h_pos F.data.h_lt_half hp a q hx hz ep0
  exact ⟨⟨eA⟩, ⟨curlExtension eA⟩, ⟨ep⟩, ⟨residualExtension (curlExtension eA) ep⟩⟩

/-- Near each nonzero terminal central-plane point, the corrected actual
velocity, pressure, and residual agree as ambient germs with the same
constructed slow base.  All joint derivatives therefore agree there too. -/
theorem final_diagonal_germs (upper : ℝ) (B : ℕ) {C : ℝ}
    {A : ℕ → SpaceTime → Space} {p : ℕ → SpaceTime → ℝ}
    (hA : ∀ j, ShrinkingSupport F.data.h C (A j))
    (hp : ∀ j, ShrinkingSupport F.data.h C (p j))
    (a : ℕ → ℝ) (q : SpaceTime → ℝ) {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) :
    let A' := diagonalAddition (TailGaugePotential.finalPotential H v upper B) a q A
    let p' := diagonalAddition (FinalSlowBase.pressure H v upper B) a q p
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      ∀ w ∈ U, w.1 < 1 →
        SpatialCurl.spatialCurl A' =ᶠ[𝓝 w] FinalSlowBase.velocity H v upper B ∧
        p' =ᶠ[𝓝 w] FinalSlowBase.pressure H v upper B ∧
        (fun z => ProblemStatement.navierStokesResidual
          (SpatialCurl.spatialCurl A') p' z.1 z.2) =ᶠ[𝓝 w]
        (fun z => ProblemStatement.navierStokesResidual (FinalSlowBase.velocity H v upper B)
          (FinalSlowBase.pressure H v upper B) z.1 z.2) := by
  obtain ⟨U, hU, hxU, hg⟩ := diagonal_addition_germs F.data.h_pos F.data.h_lt_half
    (TailGaugePotential.finalPotential H v upper B) (FinalSlowBase.pressure H v upper B)
    hA hp a q hx hz
  refine ⟨U, hU, hxU, ?_⟩
  intro w hw ht
  have hbase : SpatialCurl.spatialCurl (TailGaugePotential.finalPotential H v upper B) =ᶠ[𝓝 w]
      FinalSlowBase.velocity H v upper B := by
    filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds ht] with y hy
    exact TailGaugePotential.finalPotential_sameCurl H v upper B hy
  have hv := (hg w hw ht).2.1.trans hbase
  have hpr := (hg w hw ht).2.2.1
  exact ⟨hv, hpr, ResidualRegularity.residual_eventuallyEq hv hpr⟩

end FinalBase

end NavierStokes.AnnularEndpoint
