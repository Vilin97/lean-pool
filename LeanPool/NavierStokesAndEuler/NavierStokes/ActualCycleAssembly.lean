/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleParameters
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCoreSupport
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCarrierTransport
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveRegularityData
import LeanPool.NavierStokesAndEuler.NavierStokes.LabelSupportPreservation

/-!
# The actual finite signed-wave assembly

The selected primary slots, physical windows, and absolute auxiliary
coordinate are shared by the current block and both wave increments.
Support comes from the canonical source carrier and the actual native
mask/cutoff product.  Quantitative wave bounds are separate inputs.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualCycleAssembly

open Set Function Filter WeightedClasses CorrectionState CorrectionStep CorrectionInitialization
open scoped ContDiff Topology BigOperators


/-- Point: an abbreviation for `ActualInitialization.Point`. -/
abbrev Point := ActualInitialization.Point
/-- Index: an abbreviation for `ActualInitialization.Index B N0`. -/
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0

/-- The same label map used by the actual primary covariance. -/
noncomputable def label {B N0 : ℕ} (_n : ℕ) (l : Index B N0) : SlotColoring.Label :=
  ActualPrimaryCovariance.signedLabelOf l

theorem label_injective {B N0 : ℕ} (n : ℕ) :
    Injective (label (B := B) (N0 := N0) n) := ActualPrimaryCovariance.signedLabelOf_injective

theorem label_level {B N0 : ℕ} (n : ℕ) (l : Index B N0) :
    1 ≤ (label n l).1 := l.1.val.property.1

/-- Canonical carrier support gives both pieces of the actual slot/window
support predicate.  This applies to any real oscillatory field. -/
theorem supported_of_zero_outside {B N0 : ℕ}
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (u : Index B N0 → Oscillation Point)
    (hz : ∀ l n x, x ∈ ActualInitialization.geometry.strip.domain → x ∉
        ActualInitialization.labelCarrier l n →
      ∀ θ i, u l n (x, θ) i = 0) :
    LabelSumBounds.SupportedOscillations ActualPrimary.slots label
        ActualPrimaryCovariance.physicalWindow ActualPrimaryCovariance.absoluteAuxiliary
      ActualInitialization.geometry.strip.domain u := by
  intro l n x hx θ i hn
  have hc : x ∈ ActualInitialization.labelCarrier l n := by
    by_contra hc
    exact hn (hz l n x hx hc θ i)
  exact ⟨ActualCarrierGeometry.labelCarrier_window hN (l.2,l.1) n hx hc,
    ActualCarrierGeometry.labelCarrier_liftedSupport (l.2,l.1) n hc⟩

/-- Zero nonconstant real coefficients and an actual zero mode imply
zero real field; no angular cancellation is postulated. -/
theorem oscillation_zero_of_inputSupport
    (b : HarmonicBlock Point) (G A : HarmonicResidual.BlockCoefficients Point)
    {U : Set Point} {K : ℕ → Set Point}
    (hs : HarmonicSourceSupport.InputSupportOn U K b G A) (hzero : HarmonicWaveInteraction.ZeroMode
        b)
    (n : ℕ) {x : Point} (hx : x ∈ U) (hn : x ∉ K n) (θ : ℝ) (i : Fin 3) :
    b.oscillation n (x, θ) i = 0 := by
  have hcoeff (j : ℤ) : HarmonicResidual.realCoefficients (b.velocity n i) j x = 0 := by
    by_cases hj : j = 0
    · subst j
      simp [HarmonicResidual.realCoefficients_apply, hzero n i]
    · exact hs.velocity n i j hj x hx hn
  have hfield : HarmonicFields.field (HarmonicResidual.realCoefficients (b.velocity n i))
      (b.frequency n) (b.phase n) (b.angularFrequency n) (x, θ) = 0 := by
    rw [HarmonicFields.field_expansion]
    apply Finset.sum_eq_zero
    intro j _
    rw [hcoeff j, zero_mul, zero_mul]
  rw [HarmonicResidual.field_realCoefficients] at hfield
  exact Complex.ofReal_eq_zero.mp hfield

theorem supported_of_inputSupport {B N0 : ℕ}
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (b : Index B N0 → HarmonicBlock Point)
    (G A : Index B N0 → HarmonicResidual.BlockCoefficients Point)
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
        (ActualInitialization.labelCarrier l) (b l) (G l) (A l))
    (hzero : ∀ l, HarmonicWaveInteraction.ZeroMode (b l)) :
    LabelSumBounds.SupportedOscillations ActualPrimary.slots label
        ActualPrimaryCovariance.physicalWindow ActualPrimaryCovariance.absoluteAuxiliary
      ActualInitialization.geometry.strip.domain (fun l => (b l).oscillation) := by
  apply supported_of_zero_outside hN
  intro l n x hx hn θ i
  exact oscillation_zero_of_inputSupport (b l) (G l) (A l) (hs l) (hzero l)
    n (ActualInitialization.geometry.strip_subset hx) hn θ i

theorem primary_supported {B N0 : ℕ} :
    LabelSumBounds.SupportedOscillations ActualPrimary.slots label
        ActualPrimaryCovariance.physicalWindow ActualPrimaryCovariance.absoluteAuxiliary
      ActualInitialization.geometry.strip.domain (fun l : Index B N0 =>
          (ActualInitialization.tangentBlock l).oscillation) := by
  intro l n x hx θ i hn
  apply ActualPrimaryCovariance.piece_support l n x hx θ
  apply subset_closure
  intro hz
  change (((ActualInitialization.primaryPiece l).coefficients.withCutoff
    (ActualInitialization.primaryPiece l).cutoff).amplitude n (x, θ)) = 0 at hz
  apply hn
  change (ActualInitialization.tangentBlock l).oscillation n (x, θ) i = 0
  rw [ActualInitialization.tangentBlock_represents]
  change ((HarmonicCalculus.vectorMode _ _ _ _ i).re) = 0
  simp only [HarmonicCalculus.vectorMode, HarmonicCalculus.mode, hz, Pi.zero_apply,
    zero_mul, Complex.zero_re]

section SignedSupport

variable {B N0 : ℕ}

/-- Nonzero values of the actual spatial mask and native cutoff locate
the point in the fixed closed source carrier. -/
theorem signed_mask_cutoff_source (l : Index B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : Point × ℝ)
    (hm : ActualSignedStageControls.mask l k n x ≠ 0)
    (hc : ActualSignedStageControls.cutoff l k n x ≠ 0) :
    x.1 ∈ ActualInitialization.labelCarrier l n := by
  let z := ActualSignedStageControls.nativePoint l n k x
  have hs := ActualPrimary.spatialMask_native_support l.1 z.1 hm
  have ht : PartitionedCovariance.cutoff ActualPrimary.slots.radius z.2.1 ≠ 0 := by
    intro hz
    apply hc
    change PartitionedCovariance.cutoff ActualPrimary.slots.radius z.2.1 *
      ActualPrimary.gaussian l.1 z = 0
    rw [hz, zero_mul]
  have hg : ActualPrimary.gaussian l.1 z ≠ 0 := by
    intro hz
    apply hc
    change PartitionedCovariance.cutoff ActualPrimary.slots.radius z.2.1 *
      ActualPrimary.gaussian l.1 z = 0
    rw [hz, mul_zero]
  have htrans : z.2.1 ∈ Ioo (-ActualPrimary.slots.radius) ActualPrimary.slots.radius := by
    rw [← PartitionedCovariance.cutoff_support ActualPrimary.slots.radius_pos]
    exact ht
  have hga : |z.2.2 / ((ActualPrimary.phases B N0 0).L l.1) - 1 / 2| < 1 / 3 :=
    lt_of_not_ge (fun h => hg (GaussianTailFlat.profile_zero h))
  have hL := (ActualPrimary.phases B N0 0).L_pos l.1
  have hlo : (1 / 6 : ℝ) ≤ z.2.2 / ((ActualPrimary.phases B N0 0).L l.1) := by
    linarith [(abs_lt.mp hga).1]
  have hhi : z.2.2 / ((ActualPrimary.phases B N0 0).L l.1) ≤ 5 / 6 := by
    linarith [(abs_lt.mp hga).2]
  refine ⟨k, hs, ⟨htrans.1.le, htrans.2.le⟩, ?_, ?_⟩
  · change ((ActualPrimary.phases B N0 0).L l.1 / 1) / 6 ≤ z.2.2
    simpa only [div_eq_mul_inv, inv_one, mul_one, one_mul, mul_comm] using
      (le_div_iff₀ hL).mp hlo
  · change z.2.2 ≤ 5 * ((ActualPrimary.phases B N0 0).L l.1 / 1) / 6
    simpa only [div_eq_mul_inv, inv_one, mul_one, one_mul, mul_comm, mul_assoc, mul_left_comm] using
      (div_le_iff₀ hL).mp hhi

theorem signed_mask_or_cutoff_zero (l : Index B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : Point × ℝ}
    (hx : x.1 ∉ ActualInitialization.labelCarrier l n) :
    ActualSignedStageControls.mask l k n x = 0 ∨ ActualSignedStageControls.cutoff l k n x = 0 := by
  by_cases hm : ActualSignedStageControls.mask l k n x = 0
  · exact Or.inl hm
  · right
    by_contra hc
    exact hx (signed_mask_cutoff_source l n k x hm hc)

theorem signed_localized_zero (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2)
    (n : ℕ) (k : TorusInverse.Frequency) {x : Point × ℝ}
    (hx : x.1 ∉ ActualInitialization.labelCarrier l n) :
    ((((ActualSignedStageControls.parameters l).copyData s request).localized k).amplitude n x = 0)
        ∧
    ((((ActualSignedStageControls.parameters l).copyData s request).localized k).pressure n x = 0)
        := by
  rcases signed_mask_or_cutoff_zero l n k hx with hm | hc
  · have hh := PeriodizedSignedParameters.raw_zero_of_mask
      (p := ActualSignedStageControls.parameters l) (s := s) request n k x hm
    constructor
    · change ActualSignedStageControls.cutoff l k n x •
        ((ActualSignedStageControls.parameters l).copyData s request).amplitude n k x = 0
      rw [hh.1, smul_zero]
    · change (ActualSignedStageControls.cutoff l k n x : ℂ) *
        ((ActualSignedStageControls.parameters l).copyData s request).pressure n k x = 0
      rw [hh.2, mul_zero]
  · constructor
    · change ActualSignedStageControls.cutoff l k n x • _ = 0
      rw [hc, zero_smul]
    · change (ActualSignedStageControls.cutoff l k n x : ℂ) * _ = 0
      rw [hc, Complex.ofReal_zero, zero_mul]

theorem signed_common_zero (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2)
    (n : ℕ) {x : Point × ℝ} (hx : x.1 ∉ ActualInitialization.labelCarrier l n) :
    ((ActualSignedStageControls.parameters l).copyData s request).common.amplitude n x = 0 ∧
    ((ActualSignedStageControls.parameters l).copyData s request).common.pressure n x = 0 := by
  constructor
  · change (∑' k, _) = 0
    calc
      _ = ∑' _k : TorusInverse.Frequency, (0 : Fin 3 → ℂ) :=
        tsum_congr (fun k => (signed_localized_zero l s request n k hx).1)
      _ = 0 := tsum_zero
  · change (∑' k, _) = 0
    calc
      _ = ∑' _k : TorusInverse.Frequency, (0 : ℂ) :=
        tsum_congr (fun k => (signed_localized_zero l s request n k hx).2)
      _ = 0 := tsum_zero

/-- The common tangent and the exact curl-corrected amplitude both vanish
as genuine ambient germs outside the same closed carrier. -/
theorem signed_common_zero_germs (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2)
    (n : ℕ) {x : Point × ℝ} (hx : x.1 ∉ ActualInitialization.labelCarrier l n) :
    let a := (ActualSignedStageControls.parameters l).copyData s request
    (a.common.amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
    ((a.commonCorrected (HarmonicWaveInteraction.productStrip s)
      (ActualSignedStageControls.parameters l).directions).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.common.pressure n =ᶠ[𝓝 x] fun _ => 0) := by
  let a := (ActualSignedStageControls.parameters l).copyData s request
  have hn : ∀ᶠ y : Point × ℝ in 𝓝 x, y.1 ∉ ActualInitialization.labelCarrier l n :=
    ((ActualInitialization.labelCarrier_closed l n).preimage continuous_fst).isOpen_compl.mem_nhds
        hx
  have ha : a.common.amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hn] with y hy
    exact (signed_common_zero l s request n hy).1
  have hp : a.common.pressure n =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hn] with y hy
    exact (signed_common_zero l s request n hy).2
  refine ⟨ha, ?_, hp⟩
  have he := ParticularWaveAssembly.realizedCoefficient_germ ha
    (a.background.frequency n) (a.background.radius n)
    ((ActualSignedStageControls.parameters l).directions.radialField n)
    (fun _ => (ActualSignedStageControls.parameters l).directions.angular)
    ((ActualSignedStageControls.parameters l).directions.axialField
        (HarmonicWaveInteraction.productStrip s) n)
    (a.background.phase n)
  simp only [PeriodizedWaveBounds.realizedCoefficient_zero] at he
  exact he

theorem block_inputSupport_of_zero
    (a : LinearWaveBounds.WaveCoefficients (Point × ℝ)) (kp : ℕ → ℤ)
    {U : Set Point} {K : ℕ → Set Point}
    (hv : ∀ n x, x ∈ U → x ∉ K n → a.amplitude n (x, 0) = 0)
    (hp : ∀ n x, x ∈ U → x ∉ K n → a.pressure n (x, 0) = 0) :
    HarmonicSourceSupport.InputSupportOn U K (SignedWaveUpdate.blockOfCoefficients a kp) 0 0 := by
  have hh := LabelSupportPreservation.blockOfCoefficients_inputSupport a kp
    (g := fun _ _ => 0) hv hp (fun _ _ _ _ => rfl)
  refine ⟨hh.velocity, hh.pressure, ?_, ?_⟩
  · intro n i j hj x hx hn
    simp [HarmonicResidual.realCoefficients_apply]
  · intro n i j hj x hx hn
    simp [HarmonicResidual.realCoefficients_apply]

theorem tangent_inputSupport (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualInitialization.labelCarrier l)
      ((ActualSignedStageControls.parameters l).tangentBlock s request) 0 0 := by
  apply block_inputSupport_of_zero
  · intro n x _ hn
    exact (signed_common_zero l s request n (x := (x, 0)) hn).1
  · intro n x _ hn
    exact (signed_common_zero l s request n (x := (x, 0)) hn).2

theorem exact_inputSupport (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualInitialization.labelCarrier l)
      ((ActualSignedStageControls.parameters l).exactBlock s request) 0 0 := by
  apply block_inputSupport_of_zero
  · intro n x _ hn
    exact (signed_common_zero_germs l s request n (x := (x, 0)) hn).2.1.self_of_nhds
  · intro n x _ hn
    exact (signed_common_zero l s request n (x := (x, 0)) hn).2

theorem inputSupport_subBlock {U : Set Point} {K : ℕ → Set Point}
    {a b : HarmonicBlock Point}
    (ha : HarmonicSourceSupport.InputSupportOn U K a 0 0)
    (hb : HarmonicSourceSupport.InputSupportOn U K b 0 0) :
    HarmonicSourceSupport.InputSupportOn U K (LabelSumBounds.subBlock a b) 0 0 := by
  refine ⟨?_, ?_, ha.gaussian, ha.aliasError⟩
  · intro n i
    change HarmonicSourceSupport.NonzeroSupportedOn U (K n)
      (HarmonicResidual.realCoefficients (a.velocity n i - b.velocity n i))
    rw [HarmonicMeanInteraction.realCoefficients_sub]
    exact (ha.velocity n i).sub (hb.velocity n i)
  · intro n
    change HarmonicSourceSupport.NonzeroSupportedOn U (K n)
      (HarmonicResidual.realCoefficients (a.pressure n - b.pressure n))
    rw [HarmonicMeanInteraction.realCoefficients_sub]
    exact (ha.pressure n).sub (hb.pressure n)

theorem curl_inputSupport (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualInitialization.labelCarrier l)
      ((ActualSignedStageControls.parameters l).curlBlock s request) 0 0 :=
  inputSupport_subBlock (exact_inputSupport l s request) (tangent_inputSupport l s request)

theorem tangent_zeroMode (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicWaveInteraction.ZeroMode ((ActualSignedStageControls.parameters l).tangentBlock s
        request) :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient _ _ _ _ _).1

theorem curl_zeroMode (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicWaveInteraction.ZeroMode ((ActualSignedStageControls.parameters l).curlBlock s request)
        := by
  intro n i
  change ((ActualSignedStageControls.parameters l).exactBlock s request).velocity n i 0 -
    ((ActualSignedStageControls.parameters l).tangentBlock s request).velocity n i 0 = 0
  rw [PeriodizedSignedParameters.exactBlock_zero, tangent_zeroMode, sub_self]

theorem tangent_supported (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (s : StripData Point) (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) :
    LabelSumBounds.SupportedOscillations ActualPrimary.slots label
      ActualPrimaryCovariance.physicalWindow ActualPrimaryCovariance.absoluteAuxiliary
      ActualInitialization.geometry.strip.domain
      (fun l : Index B N0 => ((ActualSignedStageControls.parameters l).tangentBlock s
          request).oscillation) :=
  supported_of_inputSupport hN _ (fun _ => 0) (fun _ => 0)
    (fun l => tangent_inputSupport l s request) (fun l => tangent_zeroMode l s request)

theorem curl_supported (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (s : StripData Point) (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) :
    LabelSumBounds.SupportedOscillations ActualPrimary.slots label
      ActualPrimaryCovariance.physicalWindow ActualPrimaryCovariance.absoluteAuxiliary
      ActualInitialization.geometry.strip.domain
      (fun l : Index B N0 => ((ActualSignedStageControls.parameters l).curlBlock s
          request).oscillation) :=
  supported_of_inputSupport hN _ (fun _ => 0) (fun _ => 0)
    (fun l => curl_inputSupport l s request) (fun l => curl_zeroMode l s request)

end SignedSupport

section RefinedSignedSupport

variable {B N0 : ℕ}

theorem signed_cutoff_sourceCell (l : Index B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : Point × ℝ}
    (hc : ActualSignedStageControls.cutoff l k n x ≠ 0) :
    (ActualSignedStageControls.nativePoint l n k x).2 ∈
      ActualGaussianCoverage.sourceCell ActualPrimary.slots.radius
        ((ActualPrimary.phases B N0 0).L l.1) 1 := by
  let z := ActualSignedStageControls.nativePoint l n k x
  have ht : PartitionedCovariance.cutoff ActualPrimary.slots.radius z.2.1 ≠ 0 := by
    intro hz
    exact hc (by change PartitionedCovariance.cutoff _ _ * _ = 0; rw [hz, zero_mul])
  have hg : ActualPrimary.gaussian l.1 z ≠ 0 := by
    intro hz
    exact hc (by change _ * ActualPrimary.gaussian l.1 z = 0; rw [hz, mul_zero])
  have htrans : z.2.1 ∈ Ioo (-ActualPrimary.slots.radius) ActualPrimary.slots.radius := by
    rw [← PartitionedCovariance.cutoff_support ActualPrimary.slots.radius_pos]
    exact ht
  have hga : |z.2.2 / ((ActualPrimary.phases B N0 0).L l.1) - 1 / 2| < 1 / 3 :=
    lt_of_not_ge (fun h => hg (GaussianTailFlat.profile_zero h))
  have hL := (ActualPrimary.phases B N0 0).L_pos l.1
  have hlo : (1 / 6 : ℝ) ≤ z.2.2 / ((ActualPrimary.phases B N0 0).L l.1) := by
    linarith [(abs_lt.mp hga).1]
  have hhi : z.2.2 / ((ActualPrimary.phases B N0 0).L l.1) ≤ 5 / 6 := by
    linarith [(abs_lt.mp hga).2]
  refine ⟨⟨htrans.1.le, htrans.2.le⟩, ?_, ?_⟩
  · change ((ActualPrimary.phases B N0 0).L l.1 / 1) / 6 ≤ z.2.2
    simpa only [div_eq_mul_inv, inv_one, mul_one, one_mul, mul_comm] using
      (le_div_iff₀ hL).mp hlo
  · change z.2.2 ≤ 5 * ((ActualPrimary.phases B N0 0).L l.1 / 1) / 6
    simpa only [div_eq_mul_inv, inv_one, mul_one, one_mul, mul_comm, mul_assoc, mul_left_comm] using
      (div_le_iff₀ hL).mp hhi

/-- Outside the broad carrier the actual cutoff or the actual slow mask
vanishes on a neighborhood. This also controls cutoff derivatives. -/
theorem signed_cutoff_or_mask_germ (l : Index B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : Point × ℝ}
    (hx : x.1 ∉ ActualInitialization.labelCarrier l n) :
    (ActualSignedStageControls.cutoff l k n =ᶠ[𝓝 x] fun _ => 0) ∨
    (ActualSignedStageControls.mask l k n =ᶠ[𝓝 x] fun _ => 0) := by
  by_cases hs : (ActualSignedStageControls.nativePoint l n k x).1 ∈
      ActualGaussianCoverage.actualSlowCore ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared l.1
  · left
    apply PeriodizedWaveBounds.zero_germ_of_support
      ((ActualGaussianCoverage.sourceCell_compact ActualPrimary.slots.radius
        ((ActualPrimary.phases B N0 0).L l.1) 1).isClosed.preimage
          (ActualSignedStageControls.nativePoint_smooth l n k).continuous.snd)
      (fun _ hy => signed_cutoff_sourceCell l n k hy)
    intro hz
    exact hx ⟨k, hs, hz⟩
  · right
    exact PeriodizedWaveBounds.zero_germ_of_support
      ((ActualGaussianCoverage.actualSlowCore_closed ActualPrimary.certificate
          ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared l.1).preimage
          (ActualSignedStageControls.nativePoint_smooth l n k).continuous.fst)
      (fun y hy => ActualPrimary.spatialMask_native_support l.1
        (ActualSignedStageControls.nativePoint l n k y).1 hy) hs

theorem signed_exact_gaussian_zero_germs (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) (n : ℕ) {x : Point × ℝ}
    (hx : x.1 ∉ ActualInitialization.labelCarrier l n) :
    let a := (ActualSignedStageControls.parameters l).copyData s request
    ((a.commonCorrected (HarmonicWaveInteraction.productStrip s)
      (ActualSignedStageControls.parameters l).directions).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.common.pressure n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.globalGaussian (ActualSignedStageControls.parameters l).directions n =ᶠ[𝓝 x] fun _ => 0) :=
        by
  dsimp only
  apply LabelSupportPreservation.common_zero_germs_of_native _ (ActualSignedStageControls.cells l)
    (ActualSignedStageControls.cutoff_support l) _ _
  · exact Filter.Eventually.of_forall (fun _ => rfl)
  · intro k _
    rcases signed_cutoff_or_mask_germ l n k hx with hc | hm
    · exact Or.inl hc
    · right
      constructor
      · filter_upwards [hm] with y hy
        exact ((ActualSignedStageControls.parameters l).raw_zero_of_mask request n k y hy).1
      · filter_upwards [hm] with y hy
        exact ((ActualSignedStageControls.parameters l).raw_zero_of_mask request n k y hy).2

/-- The refined radial and dyadic constraints are literal factors of the
signed target and mask, for any request. -/
theorem refined_signed_localized_zero (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) (n : ℕ) (k : TorusInverse.Frequency)
    {x : Point × ℝ} (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : x.1 ∉ ActualCoreSupport.refinedCarrier l n) :
    (((ActualSignedStageControls.parameters l).copyData s request).localized k).amplitude n x = 0 ∧
    (((ActualSignedStageControls.parameters l).copyData s request).localized k).pressure n x = 0 :=
        by
  by_cases hb : x.1 ∈ ActualInitialization.labelCarrier l n
  · have hfull : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion := ⟨hx, mem_univ
      _⟩
    by_cases hr : ActualCoreSupport.radialRatio x.1 ∈
        Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
    · have hq : ActualCoreSupport.nativeQ l n x.1 ∉ Icc (1 / 2 : ℝ) 2 := by
        intro hq
        exact hn (ActualCoreSupport.mem_refinedCarrier_of_mem l n hx.1 hb hr hq)
      have hm := ActualWaveRegularityData.mask_zero_germ_outside_band l n k hfull hq
      have hz := (ActualSignedStageControls.parameters l).localized_zero_of_mask (s := s) request hm
      exact ⟨hz.1.self_of_nhds, hz.2.self_of_nhds⟩
    · have hz := ActualWaveRegularityData.signed_raw_zero_outside l s request n k hfull
        (fun ho => hr ⟨ho.1.le, ho.2.le⟩)
      constructor
      · change ActualSignedStageControls.cutoff l k n x •
          ((ActualSignedStageControls.parameters l).copyData s request).amplitude n k x = 0
        rw [hz.1, smul_zero]
      · change (ActualSignedStageControls.cutoff l k n x : ℂ) *
          ((ActualSignedStageControls.parameters l).copyData s request).pressure n k x = 0
        rw [hz.2, mul_zero]
  · exact signed_localized_zero l s request n k hb

theorem refined_signed_common_zero (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) (n : ℕ) {x : Point × ℝ}
    (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : x.1 ∉ ActualCoreSupport.refinedCarrier l n) :
    ((ActualSignedStageControls.parameters l).copyData s request).common.amplitude n x = 0 ∧
    ((ActualSignedStageControls.parameters l).copyData s request).common.pressure n x = 0 := by
  constructor
  · change (∑' k, _) = 0
    calc
      _ = ∑' _k : TorusInverse.Frequency, (0 : Fin 3 → ℂ) :=
        tsum_congr (fun k => (refined_signed_localized_zero l s request n k hx hn).1)
      _ = 0 := tsum_zero
  · change (∑' k, _) = 0
    calc
      _ = ∑' _k : TorusInverse.Frequency, (0 : ℂ) :=
        tsum_congr (fun k => (refined_signed_localized_zero l s request n k hx hn).2)
      _ = 0 := tsum_zero

theorem refined_signed_common_zero_germs (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) (n : ℕ) {x : Point × ℝ}
    (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : x.1 ∉ ActualCoreSupport.refinedCarrier l n) :
    let a := (ActualSignedStageControls.parameters l).copyData s request
    (a.common.amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
    ((a.commonCorrected (HarmonicWaveInteraction.productStrip s)
      (ActualSignedStageControls.parameters l).directions).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.common.pressure n =ᶠ[𝓝 x] fun _ => 0) := by
  let a := (ActualSignedStageControls.parameters l).copyData s request
  have hd : ∀ᶠ y : Point × ℝ in 𝓝 x, y.1 ∈ ActualInitialization.geometry.domain :=
    (ActualInitialization.geometry.domain_open.preimage continuous_fst).mem_nhds hx
  have hk : ∀ᶠ y : Point × ℝ in 𝓝 x, y.1 ∉ ActualCoreSupport.refinedCarrier l n :=
    ((ActualCoreSupport.refinedCarrier_closed l n).preimage continuous_fst).isOpen_compl.mem_nhds hn
  have ha : a.common.amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hd, hk] with y hy hny
    exact (refined_signed_common_zero l s request n hy hny).1
  have hp : a.common.pressure n =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hd, hk] with y hy hny
    exact (refined_signed_common_zero l s request n hy hny).2
  refine ⟨ha, ?_, hp⟩
  have he := ParticularWaveAssembly.realizedCoefficient_germ ha
    (a.background.frequency n) (a.background.radius n)
    ((ActualSignedStageControls.parameters l).directions.radialField n)
    (fun _ => (ActualSignedStageControls.parameters l).directions.angular)
    ((ActualSignedStageControls.parameters l).directions.axialField
        (HarmonicWaveInteraction.productStrip s) n)
    (a.background.phase n)
  simp only [PeriodizedWaveBounds.realizedCoefficient_zero] at he
  exact he

theorem refined_signed_gaussian_zero (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) (n : ℕ) {x : Point × ℝ}
    (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : x.1 ∉ ActualCoreSupport.refinedCarrier l n) :
    ((ActualSignedStageControls.parameters l).copyData s request).globalGaussian
      (ActualSignedStageControls.parameters l).directions n x = 0 := by
  by_cases hb : x.1 ∈ ActualInitialization.labelCarrier l n
  · have hfull : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion := ⟨hx, mem_univ
      _⟩
    by_cases hr : ActualCoreSupport.radialRatio x.1 ∈
        Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
    · have hq : ActualCoreSupport.nativeQ l n x.1 ∉ Icc (1 / 2 : ℝ) 2 := by
        intro hq
        exact hn (ActualCoreSupport.mem_refinedCarrier_of_mem l n hx.1 hb hr hq)
      have hm := fun k => ActualWaveRegularityData.mask_zero_germ_outside_band l n k hfull hq
      have hh :
          ((((ActualSignedStageControls.parameters l).copyData s request).commonCorrected
            (HarmonicWaveInteraction.productStrip s) (ActualSignedStageControls.parameters
                l).directions).amplitude n
              =ᶠ[𝓝 x] fun _ => 0) ∧
          (((ActualSignedStageControls.parameters l).copyData s request).common.pressure n
              =ᶠ[𝓝 x] fun _ => 0) ∧
          (((ActualSignedStageControls.parameters l).copyData s request).globalGaussian
            (ActualSignedStageControls.parameters l).directions n =ᶠ[𝓝 x] fun _ => 0) := by
        apply LabelSupportPreservation.common_zero_germs_of_native _
            (ActualSignedStageControls.cells l)
          (ActualSignedStageControls.cutoff_support l) _ _
        · exact Filter.Eventually.of_forall (fun _ => rfl)
        · intro k _
          right
          constructor
          · filter_upwards [hm k] with y hy
            exact ((ActualSignedStageControls.parameters l).raw_zero_of_mask request n k y hy).1
          · filter_upwards [hm k] with y hy
            exact ((ActualSignedStageControls.parameters l).raw_zero_of_mask request n k y hy).2
      exact hh.2.2.self_of_nhds
    · have hz := fun k => (ActualWaveRegularityData.signed_raw_zero_outside l s request n k hfull
        (fun ho => hr ⟨ho.1.le, ho.2.le⟩)).1
      simp only [PeriodizedWaveBounds.CopyData.globalGaussian,
          PeriodizedWaveBounds.CopyData.globalTail,
        PeriodizedWaveBounds.copySum, PeriodizedWaveBounds.CopyData.localTail,
        PeriodizedSignedParameters.copyData] at *
      simp only [hz, smul_zero, tsum_zero, add_zero]
  · exact (signed_exact_gaussian_zero_germs l s request n hb).2.2.self_of_nhds

/-- The exact signed block and its actual Gaussian error preserve the
refined source carrier. Neither the request nor its support is assumed. -/
theorem refined_signed_inputSupport (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier l)
      ((ActualSignedStageControls.parameters l).exactBlock s request)
      ((ActualSignedStageControls.parameters l).gaussianBlock s request).velocity 0 := by
  apply LabelSupportPreservation.blockOfCoefficients_inputSupport
  · intro n x hx hn
    exact (refined_signed_common_zero_germs l s request n (x := (x,0)) hx hn).2.1.self_of_nhds
  · intro n x hx hn
    exact (refined_signed_common_zero l s request n (x := (x,0)) hx hn).2
  · intro n x hx hn
    exact refined_signed_gaussian_zero l s request n hx hn

theorem refined_tangent_inputSupport (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier l)
      ((ActualSignedStageControls.parameters l).tangentBlock s request) 0 0 := by
  apply block_inputSupport_of_zero
  · intro n x hx hn
    exact (refined_signed_common_zero l s request n (x := (x,0)) hx hn).1
  · intro n x hx hn
    exact (refined_signed_common_zero l s request n (x := (x,0)) hx hn).2

theorem refined_curl_inputSupport (l : Index B N0) (s : StripData Point)
    (request : ℕ → Point × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier l)
      ((ActualSignedStageControls.parameters l).curlBlock s request) 0 0 := by
  apply inputSupport_subBlock _ (refined_tangent_inputSupport l s request)
  apply block_inputSupport_of_zero
  · intro n x hx hn
    exact (refined_signed_common_zero_germs l s request n (x := (x,0)) hx hn).2.1.self_of_nhds
  · intro n x hx hn
    exact (refined_signed_common_zero l s request n (x := (x,0)) hx hn).2

end RefinedSignedSupport



section SupportReindex

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inputSupport_reindex_on (e : D ≃ₗᵢ[ℝ] E)
    {U : Set E} {K : ℕ → Set E} {V : Set D} {T : ℕ → Set D}
    {b : HarmonicBlock E} {G A : HarmonicResidual.BlockCoefficients E}
    (hs : HarmonicSourceSupport.InputSupportOn U K b G A)
    (hU : ∀ z ∈ V, e z ∈ U)
    (hK : ∀ n z, z ∈ V → e z ∈ K n → z ∈ T n) :
    HarmonicSourceSupport.InputSupportOn V T (StateReindex.block e b)
      (StateReindex.blockCoefficients e G) (StateReindex.blockCoefficients e A) := by
  have hm {c : HarmonicFields.Coefficients E} {n : ℕ}
      (hc : HarmonicSourceSupport.NonzeroSupportedOn U (K n) c) :
      HarmonicSourceSupport.NonzeroSupportedOn V (T n) (StateReindex.coefficients e c) := by
    intro j hj z hz hn
    exact hc j hj (e z) (hU z hz) (fun hk => hn (hK n z hz hk))
  constructor
  · intro n i
    change HarmonicSourceSupport.NonzeroSupportedOn V (T n)
      (HarmonicResidual.realCoefficients (StateReindex.coefficients e (b.velocity n i)))
    rw [StateReindex.realCoefficients_pull]
    exact hm (hs.velocity n i)
  · intro n
    change HarmonicSourceSupport.NonzeroSupportedOn V (T n)
      (HarmonicResidual.realCoefficients (StateReindex.coefficients e (b.pressure n)))
    rw [StateReindex.realCoefficients_pull]
    exact hm (hs.pressure n)
  · intro n i
    change HarmonicSourceSupport.NonzeroSupportedOn V (T n)
      (HarmonicResidual.realCoefficients (StateReindex.coefficients e (G n i)))
    rw [StateReindex.realCoefficients_pull]
    exact hm (hs.gaussian n i)
  · intro n i
    change HarmonicSourceSupport.NonzeroSupportedOn V (T n)
      (HarmonicResidual.realCoefficients (StateReindex.coefficients e (A n i)))
    rw [StateReindex.realCoefficients_pull]
    exact hm (hs.aliasError n i)

end SupportReindex

section CanonicalParticular

variable {B N0 : ℕ} (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0)

theorem parameterDomain_open : IsOpen ActualCarrierTransport.parameterDomain :=
  ActualPrimary.standardRegion.isOpen.preimage continuous_snd

include hN in
theorem associated_inputSupport
    {b : HarmonicBlock Point} {G A : HarmonicResidual.BlockCoefficients Point}
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualInitialization.labelCarrier l) b G A) :
    HarmonicSourceSupport.InputSupportOn (ActualCarrierTransport.parameterDomain ×ˢ Set.univ)
      (ActualCarrierTransport.canonicalSourceRegion l) (StateReindex.block cycleAssoc.symm b)
      (StateReindex.blockCoefficients cycleAssoc.symm G) (StateReindex.blockCoefficients
          cycleAssoc.symm A) := by
  apply inputSupport_reindex_on cycleAssoc.symm hs
  · intro z hz
    exact hz.1
  · intro n z hz hk
    exact (ActualCarrierTransport.labelCarrier_iff_canonicalSourceRegion hN l n hz.1 z.2).mp hk

theorem canonical_copyData_eq_scalar
    (c : Context (CycleSlow × TorusInverse.Plane)) (u : State (CycleSlow × TorusInverse.Plane))
    (b : HarmonicBlock (CycleSlow × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (CycleSlow × TorusInverse.Plane)) (j : ℤ) :
    let p := ActualParticularStageControls.canonicalParameters (l.2,l.1)
    p.copyData c u b G A j =
      ScalarParticularSupport.scalarData (ParticularWaveAssembly.actualCarrier p.background b j)
        (fun n => ParticularWaveAssembly.angleTangent (p.tangent j n))
        (ParticularWaveAssembly.sourceFamily c u b G A j)
        (ActualCarrierTransport.geometry l) (fun _ => ActualPrimary.slots.radius)
        (fun _ => ActualCarrierTransport.referenceLength l) (ActualCarrierTransport.clock l)
        (fun _ => ActualPrimary.slots.radius_pos) (fun _ =>
            ActualCarrierTransport.referenceLength_pos l)
        (ActualCarrierTransport.clock_pos l) := by
  dsimp only
  unfold ParticularParameters.copyData ScalarParticularSupport.scalarData
    PeriodizedWaveBounds.complexCopyData ParticularWaveBounds.complexCopyCoefficients
  congr 1
  funext n k z
  exact congrFun (ActualCarrierTransport.canonical_cutoff l n)
    ((ActualCarrierTransport.geometry l n).coordinates k z.2)

/-- Particular cells, constructed using `ScalarParticularSupport.scalarCells`. -/
noncomputable def particularCells :
    PeriodizedWaveBounds.Cells ((CycleSlow × ℝ) × TorusInverse.Plane) TorusInverse.Frequency :=
  ScalarParticularSupport.scalarCells (ActualCarrierTransport.geometry l)
    (fun _ => ActualPrimary.slots.radius) (fun _ => ActualCarrierTransport.referenceLength l)
    (ActualCarrierTransport.clock l) (ActualCarrierTransport.geometry_outer_injective l)

theorem canonical_cutoff_support
    (c : Context (CycleSlow × TorusInverse.Plane)) (u : State (CycleSlow × TorusInverse.Plane))
    (b : HarmonicBlock (CycleSlow × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (CycleSlow × TorusInverse.Plane)) (j : ℤ)
    (n : ℕ) (k : TorusInverse.Frequency) :
    support (((ActualParticularStageControls.canonicalParameters (l.2,l.1)).copyData c u b G A
        j).cutoff n k) ⊆
      (particularCells l).carrier n k := by
  rw [canonical_copyData_eq_scalar]
  exact ScalarParticularSupport.scalarData_cutoff_support _ _ _ _ _ _ _ _ _ _
    (ActualCarrierTransport.geometry_outer_injective l) n k

variable (c : Context Point) (u : State Point) (b : HarmonicBlock Point)
    (G A : HarmonicResidual.BlockCoefficients Point)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualInitialization.labelCarrier l) b G A)

include hN hs

theorem canonical_source_zero_germ (j : ℤ) (n : ℕ)
    {z : (CycleSlow × ℝ) × TorusInverse.Plane}
    (hz : z.1.1 ∈ ActualCarrierTransport.parameterDomain)
    (hn : (z.1.1, z.2) ∉ ActualCarrierTransport.canonicalSourceRegion l n) :
    ParticularWaveAssembly.sourceFamily (StateReindex.context cycleAssoc.symm c)
      (StateReindex.state cycleAssoc.symm u) (StateReindex.block cycleAssoc.symm b)
      (StateReindex.blockCoefficients cycleAssoc.symm G) (StateReindex.blockCoefficients
          cycleAssoc.symm A)
      j n =ᶠ[𝓝 z] fun _ => 0 :=
  ActualGaussianCoverage.sourceFamily_zero_germ _ _ _ _ _ (parameterDomain_open.prod isOpen_univ)
    (ActualCarrierTransport.canonicalSourceRegion_closed l) (associated_inputSupport hN l hs)
    j n ⟨hz, mem_univ _⟩ hn

theorem canonical_copy_zero_germs (j : ℤ)
    (s : StripData ((CycleSlow × ℝ) × TorusInverse.Plane))
    (d : LinearWaveBounds.GraphDirections ((CycleSlow × ℝ) × TorusInverse.Plane))
    (n : ℕ) {z : (CycleSlow × ℝ) × TorusInverse.Plane}
    (hz : z.1.1 ∈ ActualCarrierTransport.parameterDomain)
    (hn : (z.1.1, z.2) ∉ ActualCarrierTransport.canonicalSourceRegion l n) :
    let a := (ActualParticularStageControls.canonicalParameters (l.2,l.1)).copyData
      (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm u)
      (StateReindex.block cycleAssoc.symm b) (StateReindex.blockCoefficients cycleAssoc.symm G)
      (StateReindex.blockCoefficients cycleAssoc.symm A) j
    ((a.commonCorrected s d).amplitude n =ᶠ[𝓝 z] fun _ => 0) ∧
    (a.common.pressure n =ᶠ[𝓝 z] fun _ => 0) ∧
    (a.globalGaussian d n =ᶠ[𝓝 z] fun _ => 0) := by
  dsimp only
  rw [canonical_copyData_eq_scalar]
  exact ScalarParticularSupport.scalarData_zero_germs _ _ _ _ _ _ _ _ _ _
    (ActualCarrierTransport.geometry_outer_injective l) ActualCarrierTransport.parameterDomain
    (ActualCarrierTransport.activeSlowCore l)
    (fun n z hz hn => canonical_source_zero_germ hN l c u b G A hs j n hz hn) s d n hz hn

end CanonicalParticular

section FactorizedCarrier

variable {B N0 : ℕ} (l : Index B N0)
    (K : ℕ → Set Point) (slowCarrier : ℕ → Set CycleSlow)
    (hK : ∀ n, IsClosed (K n))
    (hfactor : ∀ n p, p ∈ ActualCarrierTransport.parameterDomain → ∀ Y,
      ActualCarrierTransport.associatedPoint p Y ∈ K n ↔
        (p, Y) ∈ ActualGaussianCoverage.sourceRegion (slowCarrier n)
          (ActualCarrierTransport.geometry l n) ActualPrimary.slots.radius
          (ActualCarrierTransport.referenceLength l) (ActualCarrierTransport.clock l n))
    (c : Context Point) (u : State Point) (b : HarmonicBlock Point)
    (G A : HarmonicResidual.BlockCoefficients Point)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain K b G A)

include hK hfactor hs

/-- A closed incoming carrier with slow-coordinate factors supplies the
whole-path source germs, including additional refined slow constraints. -/
theorem source_zero_germ_of_factorization (j : ℤ) (n : ℕ)
    {z : (CycleSlow × ℝ) × TorusInverse.Plane}
    (hz : z.1.1 ∈ ActualCarrierTransport.parameterDomain)
    (hn : (z.1.1, z.2) ∉ ActualGaussianCoverage.sourceRegion (slowCarrier n)
      (ActualCarrierTransport.geometry l n) ActualPrimary.slots.radius
      (ActualCarrierTransport.referenceLength l) (ActualCarrierTransport.clock l n)) :
    ParticularWaveAssembly.sourceFamily (StateReindex.context cycleAssoc.symm c)
      (StateReindex.state cycleAssoc.symm u) (StateReindex.block cycleAssoc.symm b)
      (StateReindex.blockCoefficients cycleAssoc.symm G) (StateReindex.blockCoefficients
          cycleAssoc.symm A)
      j n =ᶠ[𝓝 z] fun _ => 0 := by
  have hass : HarmonicSourceSupport.InputSupportOn
      (ActualCarrierTransport.parameterDomain ×ˢ Set.univ)
      (fun n => cycleAssoc.symm ⁻¹' K n)
      (StateReindex.block cycleAssoc.symm b) (StateReindex.blockCoefficients cycleAssoc.symm G)
      (StateReindex.blockCoefficients cycleAssoc.symm A) :=
    inputSupport_reindex_on cycleAssoc.symm hs (fun _ hx => hx.1) (fun _ _ _ hx => hx)
  apply ActualGaussianCoverage.sourceFamily_zero_germ _ _ _ _ _
    (parameterDomain_open.prod isOpen_univ)
    (fun n => (hK n).preimage cycleAssoc.symm.continuous) hass j n ⟨hz, mem_univ _⟩
  intro hk
  exact hn ((hfactor n z.1.1 hz z.2).mp hk)

/-- The source germ is retained in the raw-zero branch, as required by
the actual linear cancellation identity. -/
theorem native_zero_alternative_of_factorization (j : ℤ) (n : ℕ)
    (k : TorusInverse.Frequency) {z : (CycleSlow × ℝ) × TorusInverse.Plane}
    (hz : z.1.1 ∈ ActualCarrierTransport.parameterDomain)
    (hk : z ∈ (particularCells l).carrier n k)
    (hn : (z.1.1, z.2) ∉ ActualGaussianCoverage.sourceRegion (slowCarrier n)
      (ActualCarrierTransport.geometry l n) ActualPrimary.slots.radius
      (ActualCarrierTransport.referenceLength l) (ActualCarrierTransport.clock l n)) :
    let a := (ActualParticularStageControls.canonicalParameters (l.2,l.1)).copyData
      (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm u)
      (StateReindex.block cycleAssoc.symm b) (StateReindex.blockCoefficients cycleAssoc.symm G)
      (StateReindex.blockCoefficients cycleAssoc.symm A) j
    (a.cutoff n k =ᶠ[𝓝 z] fun _ => 0) ∨
      ((a.amplitude n k =ᶠ[𝓝 z] fun _ => 0) ∧
       (a.pressure n k =ᶠ[𝓝 z] fun _ => 0) ∧
       (a.source n =ᶠ[𝓝 z] fun _ => 0)) := by
  dsimp only
  rw [canonical_copyData_eq_scalar]
  have ha := ScalarParticularSupport.scalarData_native_zero_alternative
    (ParticularWaveAssembly.actualCarrier
      (ActualParticularStageControls.canonicalParameters (l.2,l.1)).background
      (StateReindex.block cycleAssoc.symm b) j)
    (fun n => ParticularWaveAssembly.angleTangent
      ((ActualParticularStageControls.canonicalParameters (l.2,l.1)).tangent j n))
    (ParticularWaveAssembly.sourceFamily (StateReindex.context cycleAssoc.symm c)
      (StateReindex.state cycleAssoc.symm u) (StateReindex.block cycleAssoc.symm b)
      (StateReindex.blockCoefficients cycleAssoc.symm G)
      (StateReindex.blockCoefficients cycleAssoc.symm A) j)
    (ActualCarrierTransport.geometry l) (fun _ => ActualPrimary.slots.radius)
    (fun _ => ActualCarrierTransport.referenceLength l) (ActualCarrierTransport.clock l)
    (fun _ => ActualPrimary.slots.radius_pos)
    (fun _ => ActualCarrierTransport.referenceLength_pos l) (ActualCarrierTransport.clock_pos l)
    (ActualCarrierTransport.geometry_outer_injective l) ActualCarrierTransport.parameterDomain
    slowCarrier (fun n z hz hn => source_zero_germ_of_factorization l K slowCarrier hK hfactor
      c u b G A hs j n hz hn) n k hz hk hn
  rcases ha with ha | ⟨ha, hp⟩
  · exact Or.inl ha
  · exact Or.inr ⟨ha, hp, source_zero_germ_of_factorization l K slowCarrier hK hfactor
      c u b G A hs j n hz hn⟩

theorem common_raw_zero_germ_of_factorization (j : ℤ) (n : ℕ)
    {z : (CycleSlow × ℝ) × TorusInverse.Plane}
    (hz : z.1.1 ∈ ActualCarrierTransport.parameterDomain)
    (hn : (z.1.1, z.2) ∉ ActualGaussianCoverage.sourceRegion (slowCarrier n)
      (ActualCarrierTransport.geometry l n) ActualPrimary.slots.radius
      (ActualCarrierTransport.referenceLength l) (ActualCarrierTransport.clock l n)) :
    let a := (ActualParticularStageControls.canonicalParameters (l.2,l.1)).copyData
      (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm u)
      (StateReindex.block cycleAssoc.symm b) (StateReindex.blockCoefficients cycleAssoc.symm G)
      (StateReindex.blockCoefficients cycleAssoc.symm A) j
    a.common.amplitude n =ᶠ[𝓝 z] fun _ => 0 := by
  classical
  let a := (ActualParticularStageControls.canonicalParameters (l.2,l.1)).copyData
    (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm u)
    (StateReindex.block cycleAssoc.symm b) (StateReindex.blockCoefficients cycleAssoc.symm G)
    (StateReindex.blockCoefficients cycleAssoc.symm A) j
  have hsupp : ∀ n k, support (a.cutoff n k) ⊆ (particularCells l).carrier n k :=
    canonical_cutoff_support l _ _ _ _ _ j
  by_cases hcell : ∃ k, z ∈ (particularCells l).carrier n k
  · obtain ⟨k, hk⟩ := hcell
    have hg := a.common_amplitude_germ (particularCells l) hsupp n hk
    rcases native_zero_alternative_of_factorization l K slowCarrier hK hfactor c u b G A hs
      j n k hz hk hn with hcut | ⟨ha, _, _⟩
    · exact hg.trans (a.localized_zero_germs hcut).1
    · apply hg.trans
      filter_upwards [ha] with y hy
      change a.cutoff n k y • a.amplitude n k y = 0
      rw [hy, smul_zero]
  · exact (a.common_zero_germs (particularCells l) hsupp (not_exists.mp hcell)).1

theorem copy_zero_germs_of_factorization (j : ℤ)
    (s : StripData ((CycleSlow × ℝ) × TorusInverse.Plane))
    (d : LinearWaveBounds.GraphDirections ((CycleSlow × ℝ) × TorusInverse.Plane))
    (n : ℕ) {z : (CycleSlow × ℝ) × TorusInverse.Plane}
    (hz : z.1.1 ∈ ActualCarrierTransport.parameterDomain)
    (hn : (z.1.1, z.2) ∉ ActualGaussianCoverage.sourceRegion (slowCarrier n)
      (ActualCarrierTransport.geometry l n) ActualPrimary.slots.radius
      (ActualCarrierTransport.referenceLength l) (ActualCarrierTransport.clock l n)) :
    let a := (ActualParticularStageControls.canonicalParameters (l.2,l.1)).copyData
      (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm u)
      (StateReindex.block cycleAssoc.symm b) (StateReindex.blockCoefficients cycleAssoc.symm G)
      (StateReindex.blockCoefficients cycleAssoc.symm A) j
    ((a.commonCorrected s d).amplitude n =ᶠ[𝓝 z] fun _ => 0) ∧
    (a.common.pressure n =ᶠ[𝓝 z] fun _ => 0) ∧
    (a.globalGaussian d n =ᶠ[𝓝 z] fun _ => 0) := by
  dsimp only
  rw [canonical_copyData_eq_scalar]
  exact ScalarParticularSupport.scalarData_zero_germs _ _ _ _ _ _ _ _ _ _
    (ActualCarrierTransport.geometry_outer_injective l) ActualCarrierTransport.parameterDomain
    slowCarrier (fun n z hz hn => source_zero_germ_of_factorization l K slowCarrier hK hfactor
      c u b G A hs j n hz hn) s d n hz hn

theorem associated_update_inputSupport (s : StripData (CycleSlow × TorusInverse.Plane)) (N : ℕ) :
    let p := ActualParticularStageControls.canonicalParameters (l.2,l.1)
    HarmonicSourceSupport.InputSupportOn (ActualCarrierTransport.parameterDomain ×ˢ Set.univ)
      (fun n => ActualGaussianCoverage.sourceRegion (slowCarrier n)
        (ActualCarrierTransport.geometry l n) ActualPrimary.slots.radius
        (ActualCarrierTransport.referenceLength l) (ActualCarrierTransport.clock l n))
      (p.updateBlock s (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm
          u)
        (StateReindex.block cycleAssoc.symm b) (StateReindex.blockCoefficients cycleAssoc.symm G)
        (StateReindex.blockCoefficients cycleAssoc.symm A) N)
      (p.gaussianBlock (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm
          u)
        (StateReindex.block cycleAssoc.symm b) (StateReindex.blockCoefficients cycleAssoc.symm G)
        (StateReindex.blockCoefficients cycleAssoc.symm A) N).velocity 0 := by
  dsimp only
  apply LabelSupportPreservation.assembledBlock_inputSupport
  · intro j hj n x hx hn
    exact (copy_zero_germs_of_factorization l K slowCarrier hK hfactor c u b G A hs j
      (ParticularParameters.nativeStrip s) (ActualParticularStageControls.canonicalParameters
          (l.2,l.1)).directions
      n (z := ((x.1,0),x.2)) hx.1 hn).1.self_of_nhds
  · intro j hj n x hx hn
    exact (copy_zero_germs_of_factorization l K slowCarrier hK hfactor c u b G A hs j
      (ParticularParameters.nativeStrip s) (ActualParticularStageControls.canonicalParameters
          (l.2,l.1)).directions
      n (z := ((x.1,0),x.2)) hx.1 hn).2.1.self_of_nhds
  · intro j hj n x hx hn
    exact (copy_zero_germs_of_factorization l K slowCarrier hK hfactor c u b G A hs j
      (ParticularParameters.nativeStrip s) (ActualParticularStageControls.canonicalParameters
          (l.2,l.1)).directions
      n (z := ((x.1,0),x.2)) hx.1 hn).2.2.self_of_nhds

/-- The literal finite particular update and its Gaussian error preserve
the closed incoming carrier. Only its slow-factor geometry is required. -/
theorem particular_inputSupport_of_factorization (s : StripData Point) (N : ℕ) :
    let p := ActualParticularStageControls.canonicalParameters (l.2,l.1)
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain K
      (StateReindex.block cycleAssoc
        (p.updateBlock (ParticularWaveBounds.reindexStrip cycleAssoc.symm s)
          (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm u)
          (StateReindex.block cycleAssoc.symm b) (StateReindex.blockCoefficients cycleAssoc.symm G)
          (StateReindex.blockCoefficients cycleAssoc.symm A) N))
      (StateReindex.block cycleAssoc
        (p.gaussianBlock (StateReindex.context cycleAssoc.symm c) (StateReindex.state
            cycleAssoc.symm u)
          (StateReindex.block cycleAssoc.symm b) (StateReindex.blockCoefficients cycleAssoc.symm G)
          (StateReindex.blockCoefficients cycleAssoc.symm A) N)).velocity 0 := by
  have hass := associated_update_inputSupport l K slowCarrier hK hfactor c u b G A hs
    (ParticularWaveBounds.reindexStrip cycleAssoc.symm s) N
  have hout := inputSupport_reindex_on cycleAssoc hass
    (V := ActualInitialization.geometry.domain) (T := K)
    (fun z hz => ⟨hz, mem_univ _⟩)
    (fun n z hz hk => (hfactor n (cycleAssoc z).1 hz (cycleAssoc z).2).mpr hk)
  refine ⟨hout.velocity, hout.pressure, hout.gaussian, ?_⟩
  intro n i j hj z hz hn
  simp [HarmonicResidual.realCoefficients_apply]

end FactorizedCarrier

section ConcreteCarriers

variable {B N0 : ℕ}

/-- Refined slow core, constructed using `ActualCarrierTransport.activeSlowCore`. -/
noncomputable def refinedSlowCore (l : Index B N0) (n : ℕ) : Set CycleSlow :=
  ActualCarrierTransport.activeSlowCore l n ∩ {p |
    ActualCoreSupport.radialRatio (ActualCarrierTransport.associatedPoint p 0) ∈
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) ∧
    ActualCoreSupport.nativeQ l n (ActualCarrierTransport.associatedPoint p 0) ∈ Icc (1/2 : ℝ) 2}

theorem refined_carrier_factorization (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (n : ℕ) (p : CycleSlow)
    (hp : p ∈ ActualCarrierTransport.parameterDomain) (Y : TorusInverse.Plane) :
    ActualCarrierTransport.associatedPoint p Y ∈ ActualCoreSupport.refinedCarrier l n ↔
      (p,Y) ∈ ActualGaussianCoverage.sourceRegion (refinedSlowCore l n)
        (ActualCarrierTransport.geometry l n) ActualPrimary.slots.radius
        (ActualCarrierTransport.referenceLength l) (ActualCarrierTransport.clock l n) := by
  have hb : ActualCarrierTransport.associatedPoint p Y ∈ ActualInitialization.labelCarrier l n ↔
      (p,Y) ∈ ActualCarrierTransport.canonicalSourceRegion l n :=
    ActualCarrierTransport.labelCarrier_iff_canonicalSourceRegion hN l n hp Y
  rw [ActualCoreSupport.mem_refinedCarrier_iff l n (show 0 < p.2.1 from hp.1), hb]
  have hr : ActualCoreSupport.radialRatio (ActualCarrierTransport.associatedPoint p Y) =
      ActualCoreSupport.radialRatio (ActualCarrierTransport.associatedPoint p 0) := rfl
  have hq : ActualCoreSupport.nativeQ l n (ActualCarrierTransport.associatedPoint p Y) =
      ActualCoreSupport.nativeQ l n (ActualCarrierTransport.associatedPoint p 0) := rfl
  rw [hr, hq]
  simp only [ActualCarrierTransport.canonicalSourceRegion, ActualGaussianCoverage.sourceRegion,
    refinedSlowCore, mem_inter_iff, mem_preimage, Set.mem_ofPred_eq]
  tauto

theorem cycle_particular_inputSupport (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CycleState (Index B N0)) (c : Context Point)
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualInitialization.labelCarrier l) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)) (l : Index B N0) :
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualInitialization.labelCarrier l)
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients c x.state l)
      ((ActualCycleParameters.fixedParameters B N0).particularGaussianBlock x.coefficients c
          x.state l).velocity 0 :=
  particular_inputSupport_of_factorization l (ActualInitialization.labelCarrier l)
    (ActualCarrierTransport.activeSlowCore l) (ActualInitialization.labelCarrier_closed l)
    (fun n _p hp Y => ActualCarrierTransport.labelCarrier_iff_canonicalSourceRegion hN l n hp Y)
    c x.state (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l)
    (hs l) ActualInitialization.geometry.strip x.coefficients.residualBand

theorem cycle_refined_particular_inputSupport (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CycleState (Index B N0)) (c : Context Point)
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier l) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)) (l : Index B N0) :
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier l)
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients c x.state l)
      ((ActualCycleParameters.fixedParameters B N0).particularGaussianBlock x.coefficients c
          x.state l).velocity 0 :=
  particular_inputSupport_of_factorization l (ActualCoreSupport.refinedCarrier l)
    (refinedSlowCore l) (ActualCoreSupport.refinedCarrier_closed l)
    (refined_carrier_factorization hN l)
    c x.state (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l)
    (hs l) ActualInitialization.geometry.strip x.coefficients.residualBand

/-- All four actual common fields have zero germs off the refined
carrier. The uncorrected amplitude is retained for edge continuation. -/
theorem refined_particular_zero_germs (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (c : Context Point) (u : State Point) (b : HarmonicBlock Point)
    (G A : HarmonicResidual.BlockCoefficients Point)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier l) b G A)
    (j : ℤ) (s : StripData ((CycleSlow × ℝ) × TorusInverse.Plane))
    (n : ℕ) {z : (CycleSlow × ℝ) × TorusInverse.Plane}
    (hz : z.1.1 ∈ ActualCarrierTransport.parameterDomain)
    (hn : ActualCarrierTransport.associatedPoint z.1.1 z.2 ∉ ActualCoreSupport.refinedCarrier l n) :
    let p := ActualParticularStageControls.canonicalParameters (l.2,l.1)
    let a := p.copyData (StateReindex.context cycleAssoc.symm c) (StateReindex.state
        cycleAssoc.symm u)
      (StateReindex.block cycleAssoc.symm b) (StateReindex.blockCoefficients cycleAssoc.symm G)
      (StateReindex.blockCoefficients cycleAssoc.symm A) j
    (a.common.amplitude n =ᶠ[𝓝 z] fun _ => 0) ∧
    ((a.commonCorrected s p.directions).amplitude n =ᶠ[𝓝 z] fun _ => 0) ∧
    (a.common.pressure n =ᶠ[𝓝 z] fun _ => 0) ∧
    (a.globalGaussian p.directions n =ᶠ[𝓝 z] fun _ => 0) := by
  have hns : (z.1.1,z.2) ∉ ActualGaussianCoverage.sourceRegion (refinedSlowCore l n)
      (ActualCarrierTransport.geometry l n) ActualPrimary.slots.radius
      (ActualCarrierTransport.referenceLength l) (ActualCarrierTransport.clock l n) := by
    intro hh
    exact hn ((refined_carrier_factorization hN l n z.1.1 hz z.2).mpr hh)
  exact ⟨common_raw_zero_germ_of_factorization l (ActualCoreSupport.refinedCarrier l)
      (refinedSlowCore l) (ActualCoreSupport.refinedCarrier_closed l)
      (refined_carrier_factorization hN l) c u b G A hs j n hz hns,
    copy_zero_germs_of_factorization l (ActualCoreSupport.refinedCarrier l)
      (refinedSlowCore l) (ActualCoreSupport.refinedCarrier_closed l)
      (refined_carrier_factorization hN l) c u b G A hs j s
      (ActualParticularStageControls.canonicalParameters (l.2,l.1)).directions n hz hns⟩

/-- The literal recomputed signed request is allowed, so this is the
fixed cycle's exact block and Gaussian coefficient support. -/
theorem cycle_refined_signed_inputSupport (x : CycleState (Index B N0)) (c : Context Point)
    (l : Index B N0) :
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier l)
      ((ActualCycleParameters.fixedParameters B N0).signedBlock x.coefficients c x.state l)
      ((ActualCycleParameters.fixedParameters B N0).signedGaussianBlock x.coefficients c x.state
          l).velocity 0 :=
  refined_signed_inputSupport l ActualInitialization.geometry.strip
    ((ActualCycleParameters.fixedParameters B N0).signedRequest x.coefficients c x.state)

end ConcreteCarriers

section ComputedFamily

variable {B N0 : ℕ} {σ κ : ℝ}
    {P : Index B N0 → ℕ → Point → ℝ}
    {carrier : Index B N0 → ℕ → Set Point}
    (x : CycleState (Index B N0))
    (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock P carrier σ x)
    (hσ : 1 / 5 ≤ σ)
    (hpart : ∀ i j, LabelSumBounds.UniformWaveClass ActualInitialization.geometry.strip P (1 / 2 +
        σ)
      (fun l n z => ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients
        (ActualPrimary.commonContext B) x.state l).velocity n i j z))
    (htangent : ∀ i j, LabelSumBounds.UniformWaveClass ActualInitialization.geometry.strip P
        (1 / 2 + σ - κ)
      (fun l n z => ((ActualCycleParameters.fixedParameters B N0).signedTangent x.coefficients
        (ActualPrimary.commonContext B) x.state l).velocity n i j z))
    (hcurl : ∀ i j, LabelSumBounds.UniformWaveClass ActualInitialization.geometry.strip P (1 +
        σ - 2 * κ)
      (fun l n z => ((ActualCycleParameters.fixedParameters B N0).signedCurl x.coefficients
        (ActualPrimary.commonContext B) x.state l).velocity n i j z))
    (hP0 : ∀ l n z, z ∈ ActualInitialization.geometry.strip.domain → 0 ≤ P l n z)
    (hP1 : ∀ l n z, z ∈ ActualInitialization.geometry.strip.domain → P l n z ≤ 1)

theorem primary_tangent_band (l : Index B N0) : (ActualInitialization.tangentBlock l).BandLimited 1
    :=
  PrimaryHarmonics.block_band _ _ _

/-- The family is the literal cycle constructor, using the current
coefficients and the fixed primary choice. -/
noncomputable def family :
    LabelSumBounds.SignedFamily ActualInitialization.geometry.strip P
      (1/2) (17/25) (1/2+σ-κ) (1+σ-2*κ) :=
  (ActualCycleParameters.fixedParameters B N0).signedFamily x.coefficients
    (ActualPrimary.commonContext B) x.state ActualInitialization.tangentBlock P hσ 1
    primary_tangent_band H.bands H.carrier
        (ActualCycleParameters.invariant_fixedParameters_signed_carrier H)
    H.wave H.difference hpart htangent hcurl hP0 hP1 H.angular

theorem inputSupport_mono {U : Set Point} {K T : ℕ → Set Point}
    {b : HarmonicBlock Point} {G A : HarmonicResidual.BlockCoefficients Point}
    (hs : HarmonicSourceSupport.InputSupportOn U K b G A) (hKT : ∀ n, K n ⊆ T n) :
    HarmonicSourceSupport.InputSupportOn U T b G A := by
  have hm {c : HarmonicFields.Coefficients Point} {n : ℕ}
      (hc : HarmonicSourceSupport.NonzeroSupportedOn U (K n) c) :
      HarmonicSourceSupport.NonzeroSupportedOn U (T n) c := by
    intro j hj z hz hn
    exact hc j hj z hz (fun hk => hn (hKT n hk))
  exact ⟨fun n i => hm (hs.velocity n i), fun n => hm (hs.pressure n),
    fun n i => hm (hs.gaussian n i), fun n i => hm (hs.aliasError n i)⟩

include H in
theorem old_supported (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hcarrier : ∀ l n, carrier l n ⊆ ActualInitialization.labelCarrier l n) :
    LabelSumBounds.SupportedOscillations ActualPrimary.slots label
      ActualPrimaryCovariance.physicalWindow ActualPrimaryCovariance.absoluteAuxiliary
      ActualInitialization.geometry.strip.domain (fun l => (x.coefficients.blocks l).oscillation) :=
  supported_of_inputSupport hN _ x.coefficients.gaussian x.coefficients.aliasCoefficients
    (fun l => inputSupport_mono (H.inputSupport l) (hcarrier l)) H.zeroVelocity

variable (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hcarrier : ∀ l n, carrier l n ⊆ ActualInitialization.labelCarrier l n)
    (hpartSupport : ∀ l, HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualInitialization.labelCarrier l)
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients
        (ActualPrimary.commonContext B) x.state l)
      ((ActualCycleParameters.fixedParameters B N0).particularGaussianBlock x.coefficients
        (ActualPrimary.commonContext B) x.state l).velocity 0)

include hN hpartSupport in
theorem particular_supported_of_inputSupport :
    LabelSumBounds.SupportedOscillations ActualPrimary.slots label
      ActualPrimaryCovariance.physicalWindow ActualPrimaryCovariance.absoluteAuxiliary
      ActualInitialization.geometry.strip.domain
      (fun l => ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients
        (ActualPrimary.commonContext B) x.state l).oscillation) :=
  supported_of_inputSupport hN _ _ (fun _ => 0) hpartSupport
    (fun l => (ActualCycleParameters.fixedParameters B N0).particularBlock_zero
      x.coefficients (ActualPrimary.commonContext B) x.state l)

/-- The geometric record uses the same fixed slots and the current
finite label set.  The particular support adapter is supplied below. -/
noncomputable def assemblyOfParticularSupport :
    SignedMeanGain.Assembly (family x H hσ hpart htangent hcurl hP0 hP1) where
  width := CoordinateAlgebra.D ActualPrimary.h
  exponent := ActualPrimary.h
  vr := ActualPrimary.radialVector
  vt := ActualPrimary.temporalVector
  slots := ActualPrimary.slots
  labels := x.coefficients.labels
  label := label
  injective n := (label_injective n).injOn
  level n l _ := label_level n l
  window := ActualPrimaryCovariance.physicalWindow
  window_continuous := ActualPrimaryCovariance.physicalWindow_continuousOn
  auxiliary := ActualPrimaryCovariance.absoluteAuxiliary
  primary_support := primary_supported
  old_support := by
    have hs := (old_supported x H hN hcarrier).add
      (particular_supported_of_inputSupport x hN hpartSupport)
    intro l n z hz θ i hn
    apply hs l n z hz θ i
    change (LabelSumBounds.addBlock (x.coefficients.blocks l)
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients
        (ActualPrimary.commonContext B) x.state l)).oscillation n (z, θ) i ≠ 0 at hn
    have hcar := (ActualCycleParameters.fixedParameters B N0).particular_carrier
      x.coefficients (ActualPrimary.commonContext B) x.state l
    rwa [LabelSumBounds.addBlock_oscillation _ _
      ⟨hcar.frequency, hcar.phase, hcar.angular⟩] at hn
  tangent_support := tangent_supported hN ActualInitialization.geometry.strip
    ((ActualCycleParameters.fixedParameters B N0).signedRequest x.coefficients
      (ActualPrimary.commonContext B) x.state)
  curl_support := curl_supported hN ActualInitialization.geometry.strip
    ((ActualCycleParameters.fixedParameters B N0).signedRequest x.coefficients
      (ActualPrimary.commonContext B) x.state)

theorem assemblyOfParticularSupport_labels :
    (assemblyOfParticularSupport x H hσ hpart htangent hcurl hP0 hP1 hN hcarrier
        hpartSupport).labels =
      x.coefficients.labels := rfl

/-- The actual geometric constructor. Incoming primitive support is
transported through the particular solve; signed support is proved above. -/
noncomputable def assembly :
    SignedMeanGain.Assembly (family x H hσ hpart htangent hcurl hP0 hP1) :=
  assemblyOfParticularSupport x H hσ hpart htangent hcurl hP0 hP1 hN hcarrier
    (cycle_particular_inputSupport hN x (ActualPrimary.commonContext B)
      (fun l => inputSupport_mono (H.inputSupport l) (hcarrier l)))

theorem assembly_labels :
    (assembly x H hσ hpart htangent hcurl hP0 hP1 hN hcarrier).labels = x.coefficients.labels := rfl

theorem family_primary :
    (family x H hσ hpart htangent hcurl hP0 hP1).primary = ActualInitialization.tangentBlock := rfl

theorem family_tangent :
    (family x H hσ hpart htangent hcurl hP0 hP1).tangent =
      (ActualCycleParameters.fixedParameters B N0).signedTangent x.coefficients
        (ActualPrimary.commonContext B) x.state := rfl

/-- The two additional support predicates consumed by mean composition
come from the same assembly and the same finite labels. -/
theorem assembly_supports :
    let a := assembly x H hσ hpart htangent hcurl hP0 hP1 hN hcarrier
    a.labels = x.coefficients.labels ∧
    LabelSumBounds.SupportedOscillations a.slots a.label a.window a.auxiliary
      ActualInitialization.geometry.strip.domain (fun l => (x.coefficients.blocks l).oscillation) ∧
    LabelSumBounds.SupportedOscillations a.slots a.label a.window a.auxiliary
      ActualInitialization.geometry.strip.domain
      (fun l => ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients
        (ActualPrimary.commonContext B) x.state l).oscillation) := by
  exact ⟨rfl, old_supported x H hN hcarrier,
    particular_supported_of_inputSupport x hN
      (cycle_particular_inputSupport hN x (ActualPrimary.commonContext B)
        (fun l => inputSupport_mono (H.inputSupport l) (hcarrier l)))⟩

end ComputedFamily

end NavierStokes.ActualCycleAssembly
