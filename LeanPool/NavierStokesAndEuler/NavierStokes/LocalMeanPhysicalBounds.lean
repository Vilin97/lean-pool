/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalStageSupport

@[expose] public section

/-!
# Physical mean estimates on the actual normalized slow region

The comparable band satisfies `q ≤ Q_n < 2q`. Its normalized slow scale
therefore lies strictly in `(1/2, 2)`. The estimates below use that actual
open region and a genuine local equality with the selected band field.
The field itself is the existing coherent physical field, not a band sum.
-/

noncomputable section

namespace NavierStokes.LocalMeanPhysicalBounds

open Set Function Filter ProblemStatement PhysicalWaveSum LocalPhysicalCopyBounds
open PhysicalMeanJetBounds
open scoped Topology ContDiff BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {h degree a b : ℝ} {N Δ : ℕ} {U : Set PhysicalGraphBounds.Plane}

/-- Band selection gives an actual field germ on the original native
region, even when the physical point lies on a band-selection boundary. -/
theorem exists_field_germ (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    {w : SpaceTime} (hw : w ∈ preterminal) (hsmall : physicalQ h w ≤ ChartScales.Q N) :
    ∃ n : ℕ, N ≤ n ∧ physicalQ h w ≤ ChartScales.Q n ∧
      ChartScales.Q n < 2 * physicalQ h w ∧
      (graph h n (D.gap n) w).2.1 ∈ U ∧
      D.field =ᶠ[𝓝 w] bandField h n (D.gap n) degree (D.native n) := by
  obtain ⟨n, hn, hqn, hnq⟩ := exists_comparable_band N (physicalQ_pos hh hh1 hw) hsmall
  have hu := hcover (PhysicalStageSupport.comparable_graph_mem hh hh1 n (D.gap n) hw hqn hnq)
  exact ⟨n, hn, hqn, hnq, hu, D.field_germ hU n hn hw hu⟩

theorem exists_angularField_germ (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    {w : SpaceTime} (hw : w ∈ preterminal) (hsmall : physicalQ h w ≤ ChartScales.Q N) :
    ∃ n : ℕ, N ≤ n ∧ physicalQ h w ≤ ChartScales.Q n ∧
      ChartScales.Q n < 2 * physicalQ h w ∧
      (graph h n (D.gap n) w).2.1 ∈ U ∧
      D.angularField =ᶠ[𝓝 w] bandAngularField h n (D.gap n) degree (D.native n) := by
  obtain ⟨n, hn, hqn, hnq, hu, _⟩ := exists_field_germ D hh hh1 hU hcover hw hsmall
  exact ⟨n, hn, hqn, hnq, hu, D.angularField_germ hU n hn hw hu⟩

/-- The original physical loss holds on the smaller, actual native region. -/
theorem field_jet_bound (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      physicalQ h w ≤ ChartScales.Q N →
      ‖iteratedFDeriv ℝ m D.field w‖ ≤ C * physicalQ h w ^ (gain - loss degree m) := by
  obtain ⟨A, hA, e, hjet⟩ := hj m
  obtain ⟨C, hC, hb⟩ := bandField_jet_bound (E := E) (b := 2 * b)
    hh.le hh1.le (div_pos ha (by norm_num : (0 : ℝ) < 4)) Δ m gain degree e A hA
  refine ⟨C, hC, ?_⟩
  intro w hw ht hsmall
  have hq := physicalQ_pos hh hh1 hw
  by_cases hts : w ∈ tsupport D.field
  · obtain ⟨n, hn, hqn, hnq, hu, he⟩ := exists_field_germ D hh hh1 hU hcover hw hsmall
    have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
    have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn hw hu hlo hnq.le hts
    rw [iteratedFDeriv_eq_of_eventuallyEq he m]
    apply hb n (hN.trans hn) (D.gap n) (D.gap_le n hn) w hann ht
      (physicalQ h w) hq hlo hnq.le (D.native n)
    · exact SmoothNear.of_open (PhysicalMeanDomain.slowDomain_open hU) (hsm n hn) hu
    · intro j hjm
      simpa only [Real.rpow_natCast] using hjet n hn _ hu j hjm
  · rw [jet_zero_off_tsupport _ _ hts, norm_zero]
    positivity

theorem field_smoothAt (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {w : SpaceTime} (hw : w ∈ preterminal)
    (hsmall : physicalQ h w ≤ ChartScales.Q N) : ContDiffAt ℝ ∞ D.field w := by
  classical
  by_cases hts : w ∈ tsupport D.field
  · obtain ⟨n, hn, hqn, hnq, hu, he⟩ := exists_field_germ D hh hh1 hU hcover hw hsmall
    have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by
      have := physicalQ_pos hh hh1 hw
      linarith
    have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn hw hu hlo hnq.le hts
    have hnative := (hsm n hn).contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hu)
    have hc := (hnative.comp w (graph_smoothAt (div_pos ha (by norm_num : (0 : ℝ) < 4)) h n
      (D.gap n) hann)).const_smul (ChartScales.Q n ^ (-degree))
    exact hc.congr_of_eventuallyEq he
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hts)

theorem field_smooth (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) :
    ContDiffOn ℝ ∞ D.field (physicalDomain h N) := by
  intro w hw
  exact (field_smoothAt D hh hh1 ha hab hU hcover hsm hs hw.1 hw.2.le).contDiffWithinAt

theorem angularField_jet_bound (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      physicalQ h w ≤ ChartScales.Q N →
      ‖iteratedFDeriv ℝ m D.angularField w‖ ≤ C * physicalQ h w ^ (gain - loss degree m) := by
  obtain ⟨A, hA, e, hjet⟩ := hj m
  obtain ⟨C, hC, hb⟩ := bandAngularField_jet_bound (b := 2 * b)
    hh.le hh1.le (div_pos ha (by norm_num : (0 : ℝ) < 4)) Δ m gain degree e A hA
  refine ⟨C, hC, ?_⟩
  intro w hw ht hsmall
  have hq := physicalQ_pos hh hh1 hw
  by_cases hts : w ∈ tsupport D.field
  · obtain ⟨n, hn, hqn, hnq, hu, he⟩ := exists_angularField_germ D hh hh1 hU hcover hw hsmall
    have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
    have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn hw hu hlo hnq.le hts
    rw [iteratedFDeriv_eq_of_eventuallyEq he m]
    apply hb n (hN.trans hn) (D.gap n) (D.gap_le n hn) w hann ht
      (physicalQ h w) hq hlo hnq.le (D.native n)
    · exact SmoothNear.of_open (PhysicalMeanDomain.slowDomain_open hU) (hsm n hn) hu
    · intro j hjm
      simpa only [Real.rpow_natCast] using hjet n hn _ hu j hjm
  · rw [jet_zero_off_tsupport _ _
      (notMem_tsupport_iff_eventuallyEq.mpr (D.angularField_zero_germ hts)), norm_zero]
    positivity

theorem angularField_smoothAt (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {w : SpaceTime} (hw : w ∈ preterminal)
    (hsmall : physicalQ h w ≤ ChartScales.Q N) : ContDiffAt ℝ ∞ D.angularField w := by
  classical
  by_cases hts : w ∈ tsupport D.field
  · obtain ⟨n, hn, hqn, hnq, hu, _⟩ := exists_field_germ D hh hh1 hU hcover hw hsmall
    have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by
      have := physicalQ_pos hh hh1 hw
      linarith
    have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn hw hu hlo hnq.le hts
    have haxis := PhysicalGraphBounds.scaledRadial_ne_zero
      (PhysicalGraphBounds.annulus_axisFree (div_pos ha (by norm_num : (0 : ℝ) < 4)) hann)
    exact (field_smoothAt D hh hh1 ha hab hU hcover hsm hs hw hsmall).smul
      ((angularVector_smooth.contDiffAt (PhysicalGraphBounds.axisFree_open.mem_nhds haxis)).comp w
        PhysicalGraphBounds.radialProjection.contDiff.contDiffAt)
  · exact contDiffAt_const.congr_of_eventuallyEq (D.angularField_zero_germ hts)

theorem angularField_smooth (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) :
    ContDiffOn ℝ ∞ D.angularField (physicalDomain h N) := by
  intro w hw
  exact (angularField_smoothAt D hh hh1 ha hab hU hcover hsm hs hw.1 hw.2.le).contDiffWithinAt

/-- Curl costs one actual derivative, with the same fixed PMJB loss. -/
theorem curl_angularField_jet_bound (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SpaceTime, w ∈ physicalDomain h N → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl D.angularField) w‖ ≤
        C * physicalQ h w ^ (gain - loss degree (m + 1)) := by
  obtain ⟨C, hC, hb⟩ := angularField_jet_bound D hh hh1 ha hab hN hU hcover hsm hs hj (m + 1)
  refine ⟨‖PhysicalClassBounds.jointCurl‖ * C,
    mul_nonneg (norm_nonneg PhysicalClassBounds.jointCurl) hC, ?_⟩
  intro w hw ht
  exact (PhysicalClassBounds.spatialCurl_jet_bound (physicalDomain_open hh hh1 N)
    (angularField_smooth D hh hh1 ha hab hU hcover hsm hs) hw m).trans
    ((mul_le_mul_of_nonneg_left (hb w hw.1 ht hw.2.le)
      (norm_nonneg PhysicalClassBounds.jointCurl)).trans_eq (by ring))

theorem curl_angularField_smooth (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) :
    ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl D.angularField) (physicalDomain h N) := by
  intro w hw
  exact (SpatialCurl.contDiffAt_spatialCurl
    (angularField_smoothAt D hh hh1 ha hab hU hcover hsm hs hw.1 hw.2.le)
    (by simp)).contDiffWithinAt

/-! ## Native class inputs on the same region -/

theorem field_jet_bound_of_localBandJets (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {α : ℝ} {ε L : ℕ → ℝ}
    (hj : PhysicalMeanDomain.LocalBandJets U ε L α D.native)
    (hε : ∀ n ≥ N, ε n = ChartScales.epsilon h n)
    (hL0 : ∀ n ≥ N, 0 ≤ L n) {C : ℝ} {p : ℕ} (hC : 1 ≤ C)
    (hL : ∀ n ≥ N, L n ≤ C * ChartScales.S n ^ p) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      physicalQ h w ≤ ChartScales.Q N →
      ‖iteratedFDeriv ℝ m D.field w‖ ≤ K * physicalQ h w ^ (h * α - loss degree m) :=
  field_jet_bound D hh hh1 ha hab hN hU hcover hsm hs
    (NativeJets.of_localBandJets hj hε hL0 hC hL) m

theorem angularField_jet_bound_of_localBandJets (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {α : ℝ} {ε L : ℕ → ℝ}
    (hj : PhysicalMeanDomain.LocalBandJets U ε L α D.native)
    (hε : ∀ n ≥ N, ε n = ChartScales.epsilon h n)
    (hL0 : ∀ n ≥ N, 0 ≤ L n) {C : ℝ} {p : ℕ} (hC : 1 ≤ C)
    (hL : ∀ n ≥ N, L n ≤ C * ChartScales.S n ^ p) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      physicalQ h w ≤ ChartScales.Q N →
      ‖iteratedFDeriv ℝ m D.angularField w‖ ≤ K * physicalQ h w ^ (h * α - loss degree m) :=
  angularField_jet_bound D hh hh1 ha hab hN hU hcover hsm hs
    (NativeJets.of_localBandJets hj hε hL0 hC hL) m

theorem curl_angularField_jet_bound_of_localBandJets (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {α : ℝ} {ε L : ℕ → ℝ}
    (hj : PhysicalMeanDomain.LocalBandJets U ε L α D.native)
    (hε : ∀ n ≥ N, ε n = ChartScales.epsilon h n)
    (hL0 : ∀ n ≥ N, 0 ≤ L n) {C : ℝ} {p : ℕ} (hC : 1 ≤ C)
    (hL : ∀ n ≥ N, L n ≤ C * ChartScales.S n ^ p) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : SpaceTime, w ∈ physicalDomain h N → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl D.angularField) w‖ ≤
        K * physicalQ h w ^ (h * α - loss degree (m + 1)) :=
  curl_angularField_jet_bound D hh hh1 ha hab hN hU hcover hsm hs
    (NativeJets.of_localBandJets hj hε hL0 hC hL) m

/-! ## Open physical sublevel interfaces -/

theorem field_sublevel_smooth (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    ContDiffOn ℝ ∞ D.field (CutStageEstimates.physicalSublevel h qbig) :=
  (field_smooth D hh hh1 ha hab hU hcover hsm hs).mono
    (fun _ hw => ⟨hw.1, hw.2.trans_le hq⟩)

theorem angularField_sublevel_smooth (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    ContDiffOn ℝ ∞ D.angularField (CutStageEstimates.physicalSublevel h qbig) :=
  (angularField_smooth D hh hh1 ha hab hU hcover hsm hs).mono
    (fun _ hw => ⟨hw.1, hw.2.trans_le hq⟩)

theorem curl_angularField_sublevel_smooth (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl D.angularField)
      (CutStageEstimates.physicalSublevel h qbig) :=
  (curl_angularField_smooth D hh hh1 ha hab hU hcover hsm hs).mono
    (fun _ hw => ⟨hw.1, hw.2.trans_le hq⟩)

theorem field_sublevel_bound (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m D.field w‖ ≤ C * physicalQ h w ^ (gain - loss degree m) := by
  obtain ⟨C, hC, hb⟩ := field_jet_bound D hh hh1 ha hab hN hU hcover hsm hs hj m
  exact ⟨C, hC, fun w hw hqw => hb w hw.1
    (PhysicalStageBounds.abs_time_le_one hh hh1 hw.1 hqw) (hw.2.le.trans hq)⟩

theorem angularField_sublevel_bound (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m D.angularField w‖ ≤ C * physicalQ h w ^ (gain - loss degree m) := by
  obtain ⟨C, hC, hb⟩ := angularField_jet_bound D hh hh1 ha hab hN hU hcover hsm hs hj m
  exact ⟨C, hC, fun w hw hqw => hb w hw.1
    (PhysicalStageBounds.abs_time_le_one hh hh1 hw.1 hqw) (hw.2.le.trans hq)⟩

theorem curl_angularField_sublevel_bound (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl D.angularField) w‖ ≤
        C * physicalQ h w ^ (gain - loss degree (m + 1)) := by
  obtain ⟨C, hC, hb⟩ := curl_angularField_jet_bound D hh hh1 ha hab hN hU hcover hsm hs hj m
  exact ⟨C, hC, fun w hw hqw => hb w ⟨hw.1, hw.2.trans_le hq⟩
    (PhysicalStageBounds.abs_time_le_one hh hh1 hw.1 hqw)⟩

end NavierStokes.LocalMeanPhysicalBounds
