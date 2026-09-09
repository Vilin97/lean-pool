/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularBackground
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCarrierGeometry

@[expose] public section

/-!
# Actual particular background on the full retained carrier

The retained source mask gives the padded native scale interval `(1/4,4)`.
The cells below use its phase carrier and closed clock core without adding
the narrower dyadic mask of the original primary coefficient support.
-/

noncomputable section

namespace NavierStokes.ParticularPaddedBackground

open Set Function Filter WeightedClasses PhaseJetBounds
open LinearWaveBounds LocalizedWaveBounds CorrectionState CorrectionStep
open CorrectionInitialization ActualPrimaryBounds
open scoped Topology ContDiff

variable {B N0 : ℕ}

noncomputable def paddedCell (n : ℕ) (i : CopyIndex B N0) : Set ActualPrimary.FullPoint :=
  {x | near i.1 n ∧
    (fullCopy i.1 n i.2 x).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
        N0).prepared.N).carrier i.1.2 ∧
    (fullCopy i.1 n i.2 x).2 ∈ (ActualPrimary.clockWindow i.1.2).core}

noncomputable def cells (n : ℕ) (i : CopyIndex B N0) : Set ActualParticularBackground.Native :=
  ActualParticularBackground.nativeToFull ⁻¹' paddedCell n i

theorem primary_control_subset_padded (n : ℕ) (i : CopyIndex B N0) :
    controlCell n i ⊆ paddedCell n i :=
  fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.1⟩

theorem padded_q (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {n : ℕ} {i : CopyIndex B N0} {x : ActualPrimary.FullPoint}
    (hc : x ∈ paddedCell n i) :
    SimilarityHomogeneity.chartQ ActualPrimary.h (fullCopy i.1 n i.2 x).1 ∈
      Ioo (1 / 4 : ℝ) 4 :=
  (ActualCarrierGeometry.cell_geometry hN i.1.2 hc.2.1).2.2.2.2.1

theorem padded_maps (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {n : ℕ} {i : CopyIndex B N0} {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ paddedCell n i) :
    ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2) ∈
      (ActualPhaseDefect.reducedJetDomain ActualPhaseDefect.paddedRegion).carrier i.1 := by
  have hr := copyPoint_radial i.1 n i.2 (x := ActualSignedGeometry.meanEquiv.symm x.1) hx
  apply ActualPhaseDefect.native_reduced_domain_mem ActualPhaseDefect.paddedRegion i.1.1 i.1.2
    hc.2.1
  · apply (BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal ActualPhaseDefect.paddedRegion
      (BaseContextAssembly.insertSlow (fullCopy i.1 n i.2 x).1)).mpr
    exact ⟨⟨hr.1, padded_q hN hc⟩, hr.2⟩
  · simp only [ActualPrimary.length_sign i.1.1 i.1.2]
    exact hc.2.2.2

theorem polynomial_on_padded (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SignedLabel B N0 → PhaseCalculus.Slow × ℝ → E}
    (hf : PolynomialJets (ActualPhaseDefect.reducedJetDomain ActualPhaseDefect.paddedRegion) f) :
    LocalUnweighted fullStrip paddedCell 0
      (fun n i x => f i.1 ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2)) := by
  let D := ActualPhaseDefect.reducedJetDomain (B := B) (N0 := N0) ActualPhaseDefect.paddedRegion
  refine ⟨fun _ _ _ _ => zero_le_one, ?_, ?_⟩
  · intro n i x hx hc
    have hm := padded_maps hN hx hc
    rw [slotCopy_affine] at hm
    have hh := ((hf.smooth i.1).contDiffAt ((D.isOpen i.1).mem_nhds hm)).comp x
      (((slotLinear i.1 n).contDiff.add
        (contDiff_const (c := slotOfNative (copyPoint i.1 n i.2 0)))).contDiffAt)
    simpa only [← slotCopy_affine, Function.comp_def] using hh
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bound m
    have hcost := copyCost_one
    refine ⟨C * 25 ^ p * copyCost ^ m, by positivity, p + m, ?_⟩
    intro n i x hx hc j hj
    have hG := fullStrip.one_le_growth n x
    have hS := fullStrip.one_le_slow n
    have hm := padded_maps hN hx hc
    have hscale : D.scale i.1 ≤ 25 * fullStrip.growth n x := by
      exact (ActualSignedGeometry.S_window_le hc.1.1 (near_distance hc.1).2).trans
        (mul_le_mul_of_nonneg_left
          ((le_max_right 1 (ChartScales.S n)).trans (fullStrip.slow_le_growth n x)) (by norm_num))
    have hlin : ‖slotLinear i.1 n‖ ^ j ≤ copyCost ^ m * fullStrip.growth n x ^ m := by
      calc
        _ ≤ (copyCost * fullStrip.slow n) ^ m :=
          (pow_le_pow_left₀ (norm_nonneg _) (slotLinear_bound hc.1) j).trans
            (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hcost hS) hj)
        _ ≤ (copyCost * fullStrip.growth n x) ^ m := by gcongr; exact fullStrip.slow_le_growth n x
        _ = _ := mul_pow _ _ _
    have hu := PhaseJetBounds.norm_jet_comp_affine (D.isOpen i.1) (hf.smooth i.1)
      (slotLinear i.1 n) (slotOfNative (copyPoint i.1 n i.2 0))
      (by simpa only [← slotCopy_affine] using hm) j
    simp only [← slotCopy_affine] at hu
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (f i.1) ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2)‖ *
          ‖slotLinear i.1 n‖ ^ j := hu
      _ ≤ (C * (25 * fullStrip.growth n x) ^ p) * (copyCost ^ m * fullStrip.growth n x ^ m) := by
        have hfb := (hb i.1 j hj _ hm).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (D.one_le_scale i.1)) hscale p) (zero_le_one.trans
            hC))
        exact mul_le_mul hfb hlin (pow_nonneg (norm_nonneg _) _) ((norm_nonneg _).trans hfb)
      _ = majorant fullStrip (fun _ _ => 1) 0 (C * 25 ^ p * copyCost ^ m) (p + m) n x := by
        rw [majorant, mul_pow, pow_add, Real.rpow_zero]
        ring

/-! ## The actual normal and material defect on the larger cells -/

theorem padded_normal_germ {i : CopyIndex B N0} {n : ℕ} {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ paddedCell n i) :
    chartNormal i.1 n =ᶠ[𝓝 x] fun y => normalScale i.1 n •
      (jointPhase (B := B) (N0 := N0)).normal i.1
        ((fullCopy i.1 n i.2 y).1, (fullCopy i.1 n i.2 y).2.2) := by
  let P := ActualPrimary.phases B N0 i.1.1
  let l := spatialLabel i.1
  let gap := ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand i.1.2) -
    CommonWindow.index ActualPrimary.h n
  have hp : ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand i.1.2))
      ((PhysicalResidualTZ.swapCylinder x).1.1, (PhysicalResidualTZ.swapCylinder x).1.2.1) ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
        N0).prepared.N).carrier i.1.2 := hc.2.1
  have hcore : (ActualSignedGeometry.slotGeometry ActualPrimary.slots
    ActualSignedGeometry.vectors_det l 0).coordinates i.2
      (CommonCoverSolve.coverPower gap (PhysicalResidualTZ.swapCylinder x).1.2.2) ∈
      (ActualSignedGeometry.clockWindow ActualPrimary.slots l.1).core := by
    erw [ActualSignedGeometry.slot_coordinates_from_zero]
    have hl : l.1 = BaseChartJets.cellBand i.1.2 := rfl
    have hg : gap = ChartScales.nativeIndex ActualPrimary.h (spatialLabel i.1).1 -
      CommonWindow.index ActualPrimary.h n := rfl
    have hY : (PhysicalResidualTZ.swapCylinder x).1.2.2 = (ActualSignedGeometry.meanEquiv.symm
      x.1).2 := rfl
    rw [hg, hY, ← fullCopy_slot]
    rw [hl, ← clock_eq i.1]
    exact hc.2.2
  have hxR : 0 < x.1.1 := BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal region hx
  have hphys := ActualSignedGeometry.phase_normal_view_germ ActualPrimary.slots
    ActualPrimary.outgoing.data.h_pos.le (label_large i.1) (CommonWindow.index ActualPrimary.h n)
      gap
    (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand i.1.2))
    (ChartScales.carrier ActualPrimary.h n) (ChartScales.carrier ActualPrimary.h
      (BaseChartJets.cellBand i.1.2))
    (P.phase.p i.1.2) (P.phase.pz i.1.2) (P.phase.x0 i.1.2) (P.phase.F i.1.2) (P.phase.G i.1.2)
    ((PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
      N0).prepared.N).isOpen i.1.2)
    (P.baseF.smooth i.1.2) (P.baseG.smooth i.1.2) i.2 (P.phase.theta i.1.2)
    (x := PhysicalResidualTZ.swapCylinder x)
    hxR hp hcore
  have hfull := hphys.comp_tendsto PhysicalResidualTZ.swapCylinder.continuous.continuousAt
  filter_upwards [hfull] with y hy
  rw [chartNormal, fullStrip, context_normal_swap (ActualPrimary.commonContext B) strip
    (ActualPrimary.chartCoefficients i.1.1 i.1.2) n
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h (CommonWindow.index
      ActualPrimary.h n))
    (CommonBaseContext.context_matches_physical ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B _ n)
    rfl rfl
    (ActualSignedGeometry.preparedViewPhase ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.slots
      (ActualPrimary.choice B N0).prepared i.1.1 i.1.2 n (CommonWindow.index ActualPrimary.h n))
    (funext (ActualPrimary.chartCoefficients_phase_view i.1.1 i.1.2 n (CommonWindow.index_le
      hc.1.2)))]
  apply hy.trans
  change normalScale i.1 n • _ = normalScale i.1 n • _
  apply congrArg (fun z => normalScale i.1 n • z)
  change PhaseCalculus.phaseNormal _ _ _ _ _ _ _ = PhaseCalculus.phaseNormal _ _ _ _ _ _ _
  erw [ActualSignedGeometry.slot_coordinates_from_zero]
  rfl


theorem padded_normalScale_local : LocalUnweighted fullStrip (paddedCell (B := B) (N0 := N0)) 0
    (fun n i (_ : ActualPrimary.FullPoint) => normalScale i.1 n) := by
  apply local_constant normalUpper_pos.le
  intro n i x _ hx
  have h := normalScale_bounds hx.1
  rw [abs_of_pos (normalLower_pos.trans_le h.1)]
  exact h.2

theorem padded_normal_local (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    LocalUnweighted fullStrip (paddedCell (B := B) (N0 := N0)) 0
      (fun n i => chartNormal i.1 n) := by
  have hn := LocalizedWaveBounds.unweighted_smul
    (padded_normalScale_local (B := B) (N0 := N0))
    (polynomial_on_padded hN native_normal_polynomial)
  have hn' : LocalUnweighted fullStrip (paddedCell (B := B) (N0 := N0)) 0
      (fun n i x => normalScale i.1 n • (jointPhase (B := B) (N0 := N0)).normal i.1
        ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2)) := by
    simpa only [zero_add] using hn
  exact hn'.congr_germ (fun _ _ _ hx hc => (padded_normal_germ hx hc).symm)

theorem padded_normal_range {i : CopyIndex B N0} {n : ℕ} {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ paddedCell n i) :
    normalFloor B N0 ≤ ‖chartNormal i.1 n x‖ ∧
      ‖chartNormal i.1 n x‖ ≤ normalCeiling B N0 := by
  let P := ActualPrimary.phases B N0 i.1.1
  have ht : (fullCopy i.1 n i.2 x).2.2 ∈ P.V i.1.2 :=
    P.interval i.1.2 (by erw [ActualPrimary.length_sign i.1.1 i.1.2]; exact hc.2.2.2)
  have hdom : ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2) ∈
      ((PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
        N0).prepared.N).slot P.V P.openV).carrier i.1.2 :=
    ⟨hc.2.1, ht⟩
  have hlow := P.normal_range.1 i.1.2 _ hdom
  have hupp := P.normal_range.2 i.1.2 _ hdom
  have hscale := normalScale_bounds hc.1
  rw [(padded_normal_germ hx hc).eq_of_nhds, norm_smul, Real.norm_eq_abs,
    abs_of_pos (normalLower_pos.trans_le hscale.1)]
  have hj : i.1.1 = 0 ∨ i.1.1 = 1 := by omega
  have hb : min (ActualPrimary.phases B N0 0).b (ActualPrimary.phases B N0 1).b ≤ P.b := by
    rcases hj with h | h <;> simp only [P, h]
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hM : P.M ^ 2 + 3 * P.M ≤
      max ((ActualPrimary.phases B N0 0).M ^ 2 + 3 * (ActualPrimary.phases B N0 0).M)
        ((ActualPrimary.phases B N0 1).M ^ 2 + 3 * (ActualPrimary.phases B N0 1).M) := by
    rcases hj with h | h <;> simp only [P, h]
    · exact le_max_left _ _
    · exact le_max_right _ _
  exact ⟨mul_le_mul hscale.1 (hb.trans hlow)
      (le_min (ActualPrimary.phases B N0 0).b_pos.le (ActualPrimary.phases B N0 1).b_pos.le)
      (normalLower_pos.trans_le hscale.1).le,
    mul_le_mul hscale.2 (hupp.trans hM) (norm_nonneg _) normalUpper_pos.le⟩


theorem padded_defect_local (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
  LocalizedWaveBounds.LocalUnweighted fullStrip (paddedCell (B := B) (N0 := N0)) 1
    (fun n i => ActualPhaseDefect.defect i.1.1 i.1.2 n) := by
  have hweight : LocalizedWaveBounds.LocalUnweighted fullStrip (paddedCell (B := B) (N0 := N0)) 0
      (fun n i (_ : ActualPrimary.FullPoint) => ActualPhaseDefect.materialWeight i.1.2 n) := by
    apply local_constant (show 0 ≤ ActualPhaseDefect.materialWeightBound by
      have h0 := ActualSignedGeometry.powerBound_one (ActualPrimary.h / 2 + 1 / 2)
      have h1 := ActualSignedGeometry.powerBound_one (CoordinateAlgebra.A ActualPrimary.h -
        ActualPrimary.h)
      unfold ActualPhaseDefect.materialWeightBound
      positivity)
    intro n i x _ hc
    obtain ⟨hp, hu⟩ := ActualPhaseDefect.active_materialWeight_bound i.1.2 n hc.1.2
    simpa only [abs_of_pos hp] using hu
  have hr := polynomial_on_padded hN (ActualPhaseDefect.native_reduced_polynomial
    (B := B) (N0 := N0) ActualPhaseDefect.paddedRegion)
  have hm := (LocalizedWaveBounds.unweighted_mul hweight hr).band_smul
    (LinearWaveBounds.band_epsilon fullStrip)
  have hm' : LocalizedWaveBounds.LocalUnweighted fullStrip (paddedCell (B := B) (N0 := N0)) 1
      (fun n i x => ChartScales.epsilon ActualPrimary.h n * ActualPhaseDefect.materialWeight i.1.2
        n *
        ActualPhaseDefect.reducedExpression i.1.1 i.1.2 n i.2 x) := by
    simp only [zero_add, smul_eq_mul, mul_assoc, ActualPhaseDefect.reducedExpression_eq_native] at
      hm ⊢
    exact hm
  apply hm'.congr_germ
  intro n i x hx hc
  apply Filter.EventuallyEq.symm
  apply ActualPhaseDefect.active_copy_defect_germ i.1.1 i.1.2 n hc.1.2 i.2 hx hc.2.1
  rw [← clock_eq i.1]
  exact hc.2.2


/-! ## Zero input slots and the unchanged native carrier -/

theorem full_background_inputs (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (j : ℤ) (W : ℕ → CopyIndex B N0 → ActualPrimary.FullPoint → ℝ)
    (hW : ∀ n i x, x ∈ fullStrip.domain → 0 ≤ W n i x) :
    InputBounds fullStrip paddedCell W 0 ChartScales.kappa (directions B)
      (ActualParticularBackground.zeroRescale (j : ℝ) (actualFamily (B := B) (N0 := N0))) := by
  have ho := CommonBaseContext.context_operator_bounds ActualPrimary.certificate
    ActualPrimary.modulation
    ActualPrimary.upper B region (CommonWindow.index_le_native ActualPrimary.h)
  refine {
    loss_nonneg := by norm_num [ChartScales.kappa]
    radial_profile := LocalClass.of_global (HarmonicWaveInteraction.class_lift ho.radialProfile)
    radial_scale := ho.radialFrequency
    fast_scale := ho.fastCoefficient
    frequency_scale := LocalizedWaveBounds.constant_real_mul (LocalClass.band_const carrier_band)
      (j : ℝ)
    radius := LocalClass.of_global radius_unweighted
    inverse_radius := LocalClass.of_global (HarmonicWaveInteraction.class_lift ho.invRadius)
    radial_base := LocalClass.of_global (HarmonicWaveInteraction.class_lift
      (BaseContextAssembly.radialBase_unweighted ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B region))
    frequency_base := LocalClass.of_global (HarmonicWaveInteraction.class_lift
      (BaseContextAssembly.frequencyBase_unweighted ActualPrimary.certificate
        ActualPrimary.modulation ActualPrimary.upper B region))
    axial_base := LocalClass.of_global (HarmonicWaveInteraction.class_lift
      (BaseContextAssembly.axialBase_unweighted ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B region))
    radial_base_aux := ?_
    frequency_base_aux := ?_
    axial_base_aux := ?_
    normal := ?_
    defect := ?_
    amplitude := fun _ => LocalClass.zero (fun n i x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n i
      x hx))
    pressure := LocalClass.zero (fun n i x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n i x hx)) }
  · intro n i x _ _
    exact Filter.Eventually.of_forall (slow_field_auxiliary B
      (BaseContextAssembly.radialSlow ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B n))
  · intro n i x _ _
    exact Filter.Eventually.of_forall (slow_field_auxiliary B
      (BaseContextAssembly.frequencySlow ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B n))
  · intro n i x _ _
    exact Filter.Eventually.of_forall (slow_field_auxiliary B
      (BaseContextAssembly.axialSlow ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B n))
  · rw [ActualParticularBackground.zeroRescale_normal, actualFamily_normal_eq]
    exact padded_normal_local hN
  · rw [ActualParticularBackground.zeroRescale_defect, actualFamily_defect_eq]
    exact padded_defect_local hN

/-- The literal `actualCarrier`, now controlled on every retained padded
cell. No dyadic mask or additional support hypothesis is imposed. -/
theorem actual_background_inputs (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (b : SignedLabel B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (ActualParticularBackground.primaryBlock l))
    (j : ℤ) (W : ℕ → CopyIndex B N0 → ActualParticularBackground.Native → ℝ)
    (hW : ∀ n i x, x ∈ ActualParticularBackground.nativeStrip.domain → 0 ≤ W n i x) :
    InputBounds ActualParticularBackground.nativeStrip cells W 0 ChartScales.kappa
      (ActualParticularBackground.directions B) (ActualParticularBackground.backgroundFamily b j)
        := by
  rw [ActualParticularBackground.backgroundFamily_eq b hb j]
  let Wfull : ℕ → CopyIndex B N0 → ActualPrimary.FullPoint → ℝ :=
    fun n i x => W n i (ActualParticularBackground.nativeToFull.symm x)
  have hWfull : ∀ n i x, x ∈ fullStrip.domain → 0 ≤ Wfull n i x := by
    intro n i x hx
    apply hW
    change ActualParticularBackground.nativeToFull (ActualParticularBackground.nativeToFull.symm x)
      ∈
      fullStrip.domain
    simpa only [ActualParticularBackground.nativeToFull.apply_symm_apply] using hx
  have hh := ActualParticularBackground.inputBounds_reindex ActualParticularBackground.nativeToFull
    (full_background_inputs hN j Wfull hWfull)
  simp only [Wfull, ActualParticularBackground.nativeToFull.symm_apply_apply] at hh
  exact hh

theorem background_normal_range
    (b : SignedLabel B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (ActualParticularBackground.primaryBlock l)) (j : ℤ)
    {n : ℕ} {i : CopyIndex B N0} {x : ActualParticularBackground.Native}
    (hx : x ∈ ActualParticularBackground.nativeStrip.domain) (hi : x ∈ cells n i) :
    normalFloor B N0 ≤ ‖(ActualParticularBackground.backgroundFamily b j).normal
      ActualParticularBackground.nativeStrip (ActualParticularBackground.directions B) n i x‖ ∧
    ‖(ActualParticularBackground.backgroundFamily b j).normal ActualParticularBackground.nativeStrip
      (ActualParticularBackground.directions B) n i x‖ ≤ normalCeiling B N0 := by
  rw [ActualParticularBackground.background_normal b hb j]
  exact padded_normal_range hx hi

theorem background_inverse_frequency
    (b : SignedLabel B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (ActualParticularBackground.primaryBlock l)) (j : ℤ) :
    LocalUnweighted ActualParticularBackground.nativeStrip (cells (B := B) (N0 := N0)) (1 / 2 : ℝ)
      (fun n i (_ : ActualParticularBackground.Native) =>
        1 / (ActualParticularBackground.backgroundFamily b j).frequency n i) := by
  have hh : LocalUnweighted ActualParticularBackground.nativeStrip (cells (B := B) (N0 := N0)) (1 /
    2 : ℝ)
      (fun n _ (_ : ActualParticularBackground.Native) =>
        1 / (ChartScales.carrier ActualPrimary.h n : ℝ)) :=
    LocalClass.band_const inverse_carrier_band
  apply (LocalizedWaveBounds.constant_real_mul hh ((j : ℝ)⁻¹)).congr
  intro n i x
  change (j : ℝ)⁻¹ * (1 / (ChartScales.carrier ActualPrimary.h n : ℝ)) =
    1 / (ActualParticularBackground.carrier b j i.1).frequency n
  rw [ActualParticularBackground.carrier_frequency b hb j]
  simp only [one_div, mul_inv_rev]
  ring

end NavierStokes.ParticularPaddedBackground
