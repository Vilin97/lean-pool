/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedOutputBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedUnmaskedBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.InitialPhysicalData

/-!
# Joint native bounds for the actual signed physical sources

The sources are the literal masked sources of the canonical dependent
family. Bounds are uniform before selecting an outer label, a harmonic,
a band, or a lattice copy. No physical derivative estimate is assumed.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualSignedNativeBounds

open Set Function Filter WeightedClasses LabelSumBounds CorrectionState
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators


/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label`. -/
abbrev Label := ActualSignedPhysicalBinding.Label
/-- Native: an abbreviation for `ActualSignedPhysicalData.Native`. -/
abbrev Native := ActualSignedPhysicalData.Native
/-- Full: an abbreviation for `ActualSignedStageControls.FullPoint`. -/
abbrev Full := ActualSignedStageControls.FullPoint
/-- Copy: an abbreviation for `TorusInverse.Frequency`. -/
abbrev Copy := TorusInverse.Frequency
/-- Source index: an abbreviation for `Σ (_ : PhysicalWaveSum.BandLabel),
ActualSignedPhysicalData.SourceIndex`. -/
abbrev SourceIndex := Σ (_ : PhysicalWaveSum.BandLabel), ActualSignedPhysicalData.SourceIndex

variable {B N0 : ℕ}

section Sources

variable (P : SignedStressPrimitive.Patch) (u : State LocalSignedRequest.Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)

/-- Family, given by `ActualSignedExterior.family (fun l : Label B N0 =>
ActualSignedPhysicalBinding.nativeStateData l P u H hp)`. -/
noncomputable def family : DependentSignedPhysicalFamily.Family :=
  ActualSignedExterior.family (fun l : Label B N0 => ActualSignedPhysicalBinding.nativeStateData l
      P u H hp)

/-- Potential source, given by `DependentSignedPhysicalFamily.jointSource ((family (N0 := N0) P
u H hp).potentialSource slots outgoing.data.h_pos.le)`. -/
noncomputable def potentialSource : SourceIndex → ℕ → Native → HarmonicCalculus.ComplexVector :=
  DependentSignedPhysicalFamily.jointSource
    ((family (N0 := N0) P u H hp).potentialSource slots outgoing.data.h_pos.le)

/-- Pressure source, given by `DependentSignedPhysicalFamily.jointSource ((family (N0 := N0) P u
H hp).pressureSource slots outgoing.data.h_pos.le)`. -/
noncomputable def pressureSource : SourceIndex → ℕ → Native → ℂ :=
  DependentSignedPhysicalFamily.jointSource
    ((family (N0 := N0) P u H hp).pressureSource slots outgoing.data.h_pos.le)

end Sources

/-- Weight, given by `Real.sqrt (ActualPrimaryBounds.strip.zeta y) /-! ## The reference pullback
is a contraction on the free coordinates -/`. -/
noncomputable def weight (_ : SourceIndex) (_ : ℕ) (y : Native) : ℝ :=
  Real.sqrt (ActualPrimaryBounds.strip.zeta y)

/-! ## The reference pullback is a contraction on the free coordinates -/

theorem norm_coverEquiv_symm_le (y : TorusInverse.Plane) :
    ‖CommonCoverSolve.coverEquiv.symm y‖ ≤ ‖y‖ := by
  let x := CommonCoverSolve.coverEquiv.symm y
  have he : CommonCoverSolve.coverEquiv x = y :=
    CommonCoverSolve.coverEquiv.apply_symm_apply y
  rw [CommonCoverSolve.coverEquiv_apply, SlotGeometry.cover_apply] at he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  have hx : x.1 = (5 * y.1 - y.2) / 14 := by dsimp only at h1 h2; linarith
  have hy : x.2 = (3 * y.2 - y.1) / 14 := by dsimp only at h1 h2; linarith
  have hY1 : |y.1| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le y
  have hY2 : |y.2| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le y
  have hX : |x.1| ≤ ‖y‖ := by
    rw [hx, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 14)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 14)).mpr
    have ha := abs_sub (5 * y.1) y.2
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)] at ha
    nlinarith [norm_nonneg y]
  have hY : |x.2| ≤ ‖y‖ := by
    rw [hy, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 14)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 14)).mpr
    have ha := abs_sub (3 * y.2) y.1
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at ha
    nlinarith [norm_nonneg y]
  exact max_le hX hY

theorem norm_coverPower_symm_le (d : ℕ) (y : TorusInverse.Plane) :
    ‖(CommonCoverSolve.coverPower d).symm y‖ ≤ ‖y‖ := by
  induction d generalizing y with
  | zero => exact le_rfl
  | succ d ih =>
      change ‖(CommonCoverSolve.coverPower d).symm (CommonCoverSolve.coverEquiv.symm y)‖ ≤ ‖y‖
      exact (ih _).trans (norm_coverEquiv_symm_le y)

/-- Native to common as an element of `Native →L[ℝ] Full`. -/
noncomputable def nativeToCommon (l : Label B N0) : Native →L[ℝ] Full :=
  (ActualSignedPhysicalBinding.toCommonCylinder l).toContinuousLinearMap.comp
    (PhysicalResidualTZ.swapCylinder.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (SignedWaveUpdate.zeroSection (D := Native)))

theorem nativeToCommon_eq (l : Label B N0) (y : Native) :
    nativeToCommon l y = ActualSignedPhysicalBinding.toCommonCylinder l
      (ActualSignedPhysicalData.nativeCylinder y) := rfl

theorem nativeToCommon_apply (l : Label B N0) (y : Native) :
    nativeToCommon l y = ((y.1, (y.2.1,
      (CommonCoverSolve.coverPower
        (ChartScales.nativeIndex h (ActualSignedPhysicalBinding.reference l) -
          CommonWindow.index h (ActualSignedPhysicalBinding.reference l))).symm y.2.2)), 0) := rfl

theorem norm_nativeToCommon_le (l : Label B N0) : ‖nativeToCommon l‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  rw [nativeToCommon_apply, one_mul]
  apply max_le
  · apply max_le (norm_fst_le y)
    exact max_le ((norm_fst_le y.2).trans (norm_snd_le y))
      ((norm_coverPower_symm_le _ y.2.2).trans ((norm_snd_le y.2).trans (norm_snd_le y)))
  · simpa only [norm_zero] using norm_nonneg y

theorem nativeToCommon_mem (l : Label B N0) {y : Native}
    (hy : y ∈ ActualPrimaryBounds.strip.domain) :
    nativeToCommon l y ∈ ActualSignedStageControls.fullStrip.domain := by
  rw [nativeToCommon_apply]
  exact hy

theorem nativeToCommon_majorant (l : Label B N0) (α C : ℝ) (p n : ℕ) (y : Native) :
    majorant ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α C p n (nativeToCommon l
          y) =
    majorant ActualPrimaryBounds.strip
      (fun _ x => Real.sqrt (ActualPrimaryBounds.strip.zeta x)) α C p n y := by
  rw [nativeToCommon_apply]
  rfl

theorem uniform_nativeToCommon {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {f : (Label B N0 × Copy) → ℕ → Full → E}
    (hf : UniformClass ActualSignedStageControls.fullStrip
      (fun _ _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α f) :
    UniformClass ActualPrimaryBounds.strip (fun _ _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta
        y)) α
      (fun i n y => f i n (nativeToCommon i.1 y)) := by
  refine ⟨fun _ _ _ _ => Real.sqrt_nonneg _, ?_, ?_⟩
  · intro i n
    exact (hf.smooth i n).comp (nativeToCommon i.1).contDiff.contDiffOn
      (fun _ hy => nativeToCommon_mem i.1 hy)
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro i n y hy j hj
    have hc := PhaseJetBounds.norm_jet_comp_linear ActualSignedStageControls.fullStrip.isOpen_domain
      (hf.smooth i n) (nativeToCommon i.1) (nativeToCommon_mem i.1 hy) j
    have hp : ‖nativeToCommon i.1‖ ^ j ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_nativeToCommon_le i.1)
    exact (hc.trans (mul_le_of_le_one_right (norm_nonneg _) hp)).trans
      ((hb i n _ (nativeToCommon_mem i.1 hy) j hj).trans_eq
        (nativeToCommon_majorant i.1 α C p n y))

/-! ## The masked native coefficients on their complete own-band strip -/

/-- Own potential, given by `ActualSignedUnmaskedBounds.ownField (fun l k n =>
ActualSignedOutputBounds.localPotential request l n k)`. -/
noncomputable def ownPotential (request : ℕ → Full → SignedWaveUpdate.Vec2) :
    (Label B N0 × Copy) → ℕ → Full → HarmonicCalculus.ComplexVector :=
  ActualSignedUnmaskedBounds.ownField
    (fun l k n => ActualSignedOutputBounds.localPotential request l n k)

/-- Own pressure, given by `ActualSignedUnmaskedBounds.ownField (fun l k n =>
((ActualSignedOutputBounds.copies request l).localized k).pressure n)`. -/
noncomputable def ownPressure (request : ℕ → Full → SignedWaveUpdate.Vec2) :
    (Label B N0 × Copy) → ℕ → Full → ℂ :=
  ActualSignedUnmaskedBounds.ownField
    (fun l k n => ((ActualSignedOutputBounds.copies request l).localized k).pressure n)

theorem localPotential_zero_germ (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (n : ℕ) (k : Copy) {x : Full}
    (ha : ((ActualSignedOutputBounds.copies request l).localized k).amplitude n =ᶠ[𝓝 x]
      fun _ => 0) :
    ActualSignedOutputBounds.localPotential request l n k =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [ha] with y hy
  simp only [ActualSignedOutputBounds.localPotential, hy, CurlClassBounds.normalCoefficient,
    CurlClassBounds.normalCross, map_zero, smul_zero]

theorem own_potential_pressure_uniform {β : ℝ} {request : ℕ → Full → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets ActualSignedStageControls.fullStrip
      (fun _ _ x => ActualSignedStageControls.fullStrip.zeta x) β
      (ActualSignedStageControls.phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) :
    UniformClass ActualSignedStageControls.fullStrip
      (fun _ _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) (β + 1)
      (ownPotential (B := B) (N0 := N0) request) ∧
    UniformClass ActualSignedStageControls.fullStrip
      (fun _ _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) (β + 1)
      (ownPressure (B := B) (N0 := N0) request) := by
  have hw (l : Label B N0) n x (_ : x ∈ ActualSignedStageControls.fullStrip.domain) :=
    mul_nonneg (Real.sqrt_nonneg (ActualSignedStageControls.fullStrip.zeta x))
      (ActualSignedOutputBounds.envelope_nonneg l n x)
  have hp := ActualSignedUnmaskedBounds.ownField_uniform hw
    (ActualSignedOutputBounds.localPotential_jets hR) (fun l k x hx => by
      rcases ActualSignedOutputBounds.phaseCell_or_localized_zero request l
        (ActualSignedUnmaskedBounds.reference l) k hx with hc | hz
      · exact Or.inl hc
      · exact Or.inr (localPotential_zero_germ request l _ k hz.1))
  have hq := ActualSignedUnmaskedBounds.ownField_uniform hw
    (ActualSignedOutputBounds.localized_pressure_jets hR) (fun l k x hx => by
      rcases ActualSignedOutputBounds.phaseCell_or_localized_zero request l
        (ActualSignedUnmaskedBounds.reference l) k hx with hc | hz
      · exact Or.inl hc
      · exact Or.inr hz.2)
  have hweight (i : Label B N0 × Copy) n x (_ : x ∈ ActualSignedStageControls.fullStrip.domain) :
      Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) * ActualSignedStageControls.envelope
          i.1 n x ≤
        Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) :=
    mul_le_of_le_one_right (Real.sqrt_nonneg _)
      (ActualPrimaryBounds.fullEnvelope_le_one (i.1.2, i.1.1) n x)
  exact ⟨hp.mono_weight (fun _ _ _ _ => Real.sqrt_nonneg _) hweight,
    hq.mono_weight (fun _ _ _ _ => Real.sqrt_nonneg _) hweight⟩

/-- Request, given by `LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P (2 * h)
(commonContext B) u`. -/
noncomputable def request (P : SignedStressPrimitive.Patch) (u : State LocalSignedRequest.Point) :
    ℕ → Full → SignedWaveUpdate.Vec2 :=
  LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P (2 * h) (commonContext B) u

section NativeCoefficients

variable (l : Label B N0) (P : SignedStressPrimitive.Patch) (u : State LocalSignedRequest.Point)

/-- Native potential coefficient, constructed using `ActualSignedPhysicalData.potentialMap`. -/
noncomputable def nativePotentialCoefficient (k : Copy) (z : ActualSignedPhysicalBinding.Cylinder) :
    HarmonicCalculus.ComplexVector :=
  ActualSignedPhysicalData.potentialMap
    ((ActualSignedPhysicalBinding.primary l).base.frequency (ActualSignedPhysicalBinding.reference
        l))
    ((ActualSignedPhysicalBinding.primary l).base.normal (ActualSignedPhysicalBinding.primary
        l).strip
      (ActualSignedPhysicalBinding.primary l).directions (ActualSignedPhysicalBinding.reference l)
          z)
    (((ActualSignedPhysicalBinding.nativeCopies l P u).localized k).amplitude
      (ActualSignedPhysicalBinding.reference l) z)

/-- Native pressure coefficient, given by `((ActualSignedPhysicalBinding.nativeCopies l P
u).localized k).pressure (ActualSignedPhysicalBinding.reference l) z`. -/
noncomputable def nativePressureCoefficient (k : Copy) (z : ActualSignedPhysicalBinding.Cylinder) :
    ℂ :=
  ((ActualSignedPhysicalBinding.nativeCopies l P u).localized k).pressure
    (ActualSignedPhysicalBinding.reference l) z

theorem native_cutoff (n : ℕ) (k : Copy) (z : ActualSignedPhysicalBinding.Cylinder) :
    (ActualSignedPhysicalBinding.nativeCopies l P u).cutoff n k z =
      ActualSignedPhysicalData.waveMask slots (ActualSignedPhysicalBinding.spatialLabel l)
        ((ActualSignedPhysicalBinding.geometry l).coordinates k z.1.2.2) := by
  change PartitionedCovariance.cutoff slots.radius
      ((ActualSignedPhysicalBinding.geometry l).coordinates k
        ((ActualSignedPhysicalBinding.nativeViews l).map n z).1.2.2).1 *
    (ActualSignedPhysicalBinding.layout l).nativeGaussian (ActualSignedPhysicalBinding.reference l)
        k
      ((ActualSignedPhysicalBinding.nativeViews l).map n z).1.2.2 = _
  rw [ActualSignedPhysicalBinding.nativeViews_map]
  rfl

theorem native_raw_amplitude (k : Copy) (z : ActualSignedPhysicalBinding.Cylinder) :
    (ActualSignedPhysicalBinding.nativeCopies l P u).amplitude
      (ActualSignedPhysicalBinding.reference l) k z =
      ActualPeriodizedSignedRealization.referenceScalar (ActualSignedPhysicalBinding.primary l)
        (ActualSignedPhysicalBinding.nativeRequest l P u) l.2
            (ActualSignedPhysicalBinding.reference l) z •
      CurlClassBounds.complexify (ActualPeriodizedSignedRealization.referenceNativeUnit
        (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.layout l) l.2
          (ActualSignedPhysicalBinding.reference l) k z) := by
  change (ActualSignedPhysicalData.dynamicCoefficients slots outgoing.data.h_pos.le
    (ActualSignedPhysicalBinding.spatialLabel l) (ActualSignedPhysicalBinding.label_large l) 0
    (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.nativeViews l)
    (ActualSignedPhysicalBinding.nativeRequest l P u) l.2 k).amplitude
      (ActualSignedPhysicalBinding.reference l) z = _
  rw [ActualSignedPhysicalBinding.dynamicCoefficients_eq]
  rw [ActualSignedPhysicalBinding.nativeCoefficients,
    ActualPeriodizedSignedRealization.coefficients_amplitude_at]
  simp only [ActualPeriodizedSignedRealization.nativeUnit,
    ActualSignedPhysicalBinding.nativeViews_map,
        ActualPeriodizedSignedRealization.referenceNativeUnit]
  rfl

theorem native_raw_pressure (k : Copy) (z : ActualSignedPhysicalBinding.Cylinder) :
    (ActualSignedPhysicalBinding.nativeCopies l P u).pressure
      (ActualSignedPhysicalBinding.reference l) k z =
      ActualPeriodizedSignedRealization.referenceScalar (ActualSignedPhysicalBinding.primary l)
        (ActualSignedPhysicalBinding.nativeRequest l P u) l.2
            (ActualSignedPhysicalBinding.reference l) z •
      ActualPeriodizedSignedRealization.homogeneousPressure
        ((ActualSignedPhysicalBinding.primary l).base.frequency
            (ActualSignedPhysicalBinding.reference l))
        ((ActualSignedPhysicalBinding.primary l).base.normal (ActualSignedPhysicalBinding.primary
            l).strip
          (ActualSignedPhysicalBinding.primary l).directions (ActualSignedPhysicalBinding.reference
              l) z)
        ((ActualSignedPhysicalBinding.primary l).normalMotion
            (ActualSignedPhysicalBinding.reference l) z)
        ((ActualSignedPhysicalBinding.primary l).action (ActualSignedPhysicalBinding.reference l) z)
        (ActualPeriodizedSignedRealization.referenceNativeUnit (ActualSignedPhysicalBinding.primary
            l)
          (ActualSignedPhysicalBinding.layout l) l.2 (ActualSignedPhysicalBinding.reference l) k z)
              := by
  change (ActualSignedPhysicalData.dynamicCoefficients slots outgoing.data.h_pos.le
    (ActualSignedPhysicalBinding.spatialLabel l) (ActualSignedPhysicalBinding.label_large l) 0
    (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.nativeViews l)
    (ActualSignedPhysicalBinding.nativeRequest l P u) l.2 k).pressure
      (ActualSignedPhysicalBinding.reference l) z = _
  rw [ActualSignedPhysicalBinding.dynamicCoefficients_eq]
  rw [ActualSignedPhysicalBinding.nativeCoefficients,
    ActualPeriodizedSignedRealization.coefficients_pressure_at]
  simp only [ActualPeriodizedSignedRealization.nativeUnit,
    ActualSignedPhysicalBinding.nativeViews_map,
        ActualPeriodizedSignedRealization.referenceNativeUnit]
  rfl

variable (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)

include H hp in
theorem localPotential_reference (k : Copy) (z : ActualSignedPhysicalBinding.Cylinder) :
    ActualSignedOutputBounds.localPotential (request (B := B) P u) l
        (ActualSignedPhysicalBinding.reference l) k
      (ActualSignedPhysicalBinding.toCommonCylinder l z) = nativePotentialCoefficient l P u k z :=
          by
  exact congrArg₂
    (fun N v => CurlClassBounds.inverseCarrier
      ((ActualSignedPhysicalBinding.primary l).base.frequency
          (ActualSignedPhysicalBinding.reference l)) •
        CurlClassBounds.normalCoefficient N v)
    (ActualSignedPhysicalBinding.primary_normal_reference l
      (ActualSignedPhysicalBinding.reference l) z).symm
    (ActualSignedPhysicalBinding.localized_amplitude_reference l P u H hp k z)

include H hp in
theorem localPressure_reference (k : Copy) (z : ActualSignedPhysicalBinding.Cylinder) :
    ((ActualSignedOutputBounds.copies (request (B := B) P u) l).localized k).pressure
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalBinding.toCommonCylinder l z) =
        nativePressureCoefficient l P u k z :=
  ActualSignedPhysicalBinding.localized_pressure_reference l P u H hp k z

end NativeCoefficients

section SingletonSources

variable (P : SignedStressPrimitive.Patch) (u : State LocalSignedRequest.Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)

theorem singleton_referenceRequest (l : Label B N0) :
    (((family P u H hp).singleton (ActualSignedExterior.nativeLabel l)).state
      ((family P u H hp).singletonLabel (ActualSignedExterior.nativeLabel l))).referenceRequest =
        ActualSignedPhysicalBinding.nativeRequest l P u := by
  erw [DependentSignedPhysicalFamily.Family.singleton_referenceRequest]
  exact (ActualSignedExterior.family_referenceRequest_nativeLabel
    (fun l : Label B N0 => ActualSignedPhysicalBinding.nativeStateData l P u H hp) l).trans
      (ActualSignedPhysicalBinding.nativeStateData_request_eq l P u H hp)

theorem singleton_rawPotential (l : Label B N0) (k : Copy)
    (z : ActualSignedPhysicalBinding.Cylinder) :
    ActualSignedPhysicalData.rawPotential slots outgoing.data.h_pos.le
      ((family P u H hp).singleton (ActualSignedExterior.nativeLabel l))
      ((family P u H hp).singletonLabel (ActualSignedExterior.nativeLabel l)) k z =
    ActualSignedPhysicalData.potentialMap
      ((ActualSignedPhysicalBinding.primary l).base.frequency
          (ActualSignedPhysicalBinding.reference l))
      ((ActualSignedPhysicalBinding.primary l).base.normal (ActualSignedPhysicalBinding.primary
          l).strip
        (ActualSignedPhysicalBinding.primary l).directions (ActualSignedPhysicalBinding.reference
            l) z)
      ((ActualSignedPhysicalBinding.nativeCopies l P u).amplitude
        (ActualSignedPhysicalBinding.reference l) k z) := by
  rw [native_raw_amplitude]
  simp only [ActualSignedPhysicalData.rawPotential, ActualSignedPhysicalData.rawSignedAmplitude,
      singleton_referenceRequest]
  dsimp only [DependentSignedPhysicalFamily.Family.singleton]
  simp only [family, ActualSignedExterior.family, ActualSignedExterior.actualLabel_nativeLabel]
  dsimp only [DependentSignedPhysicalFamily.Family.singletonLabel]
  erw [ActualSignedExterior.actualLabel_nativeLabel]
  rfl

theorem singleton_rawPressure (l : Label B N0) (k : Copy)
    (z : ActualSignedPhysicalBinding.Cylinder) :
    ActualSignedPhysicalData.rawPressure slots outgoing.data.h_pos.le
      ((family P u H hp).singleton (ActualSignedExterior.nativeLabel l))
      ((family P u H hp).singletonLabel (ActualSignedExterior.nativeLabel l)) k z =
      (ActualSignedPhysicalBinding.nativeCopies l P u).pressure
        (ActualSignedPhysicalBinding.reference l) k z := by
  rw [native_raw_pressure]
  simp only [ActualSignedPhysicalData.rawPressure, singleton_referenceRequest]
  dsimp only [DependentSignedPhysicalFamily.Family.singleton]
  simp only [family, ActualSignedExterior.family, ActualSignedExterior.actualLabel_nativeLabel]
  dsimp only [DependentSignedPhysicalFamily.Family.singletonLabel]
  erw [ActualSignedExterior.actualLabel_nativeLabel]
  rfl

theorem nativePotentialCoefficient_eq (l : Label B N0) (k : Copy)
    (z : ActualSignedPhysicalBinding.Cylinder) :
    nativePotentialCoefficient l P u k z =
      ActualSignedPhysicalData.waveMask slots (ActualSignedPhysicalBinding.spatialLabel l)
        ((ActualSignedPhysicalBinding.geometry l).coordinates k z.1.2.2) •
      ActualSignedPhysicalData.rawPotential slots outgoing.data.h_pos.le
        ((family P u H hp).singleton (ActualSignedExterior.nativeLabel l))
        ((family P u H hp).singletonLabel (ActualSignedExterior.nativeLabel l)) k z := by
  unfold nativePotentialCoefficient
  change ActualSignedPhysicalData.potentialMap _ _
    ((ActualSignedPhysicalBinding.nativeCopies l P u).cutoff (ActualSignedPhysicalBinding.reference
        l) k z •
      (ActualSignedPhysicalBinding.nativeCopies l P u).amplitude
        (ActualSignedPhysicalBinding.reference l) k z) = _
  rw [map_smul, native_cutoff, singleton_rawPotential]

theorem nativePressureCoefficient_eq (l : Label B N0) (k : Copy)
    (z : ActualSignedPhysicalBinding.Cylinder) :
    nativePressureCoefficient l P u k z =
      ActualSignedPhysicalData.waveMask slots (ActualSignedPhysicalBinding.spatialLabel l)
        ((ActualSignedPhysicalBinding.geometry l).coordinates k z.1.2.2) •
      ActualSignedPhysicalData.rawPressure slots outgoing.data.h_pos.le
        ((family P u H hp).singleton (ActualSignedExterior.nativeLabel l))
        ((family P u H hp).singletonLabel (ActualSignedExterior.nativeLabel l)) k z := by
  change (ActualSignedPhysicalBinding.nativeCopies l P u).cutoff
      (ActualSignedPhysicalBinding.reference l) k z •
    (ActualSignedPhysicalBinding.nativeCopies l P u).pressure
      (ActualSignedPhysicalBinding.reference l) k z = _
  rw [native_cutoff, singleton_rawPressure]

theorem potentialSource_on_label (l : Label B N0) (j : PhysicalWaveSum.Harmonic 1)
    (k : Copy) (n : ℕ) (y : Native) :
    potentialSource (N0 := N0) P u H hp
      ⟨ActualSignedExterior.bandLabel l, ((ActualSignedExterior.bandLabel l, j), k)⟩ n y =
      if j.val = 1 ∧ n = ActualSignedPhysicalBinding.reference l then
        nativePotentialCoefficient l P u k (ActualSignedPhysicalData.nativeCylinder y) else 0 := by
  classical
  change ((family P u H hp).potentialSource slots outgoing.data.h_pos.le
    (ActualSignedExterior.nativeLabel l)) ((ActualSignedExterior.bandLabel l, j), k) n y = _
  erw [DependentSignedPhysicalFamily.Family.potentialSource_active]
  have hm : ActualSignedExterior.bandLabel l ∈
      ((family P u H hp).singleton (ActualSignedExterior.nativeLabel l)).active :=
          Set.mem_singleton _
  have hband : (ActualSignedExterior.bandLabel l).val.1 = ActualSignedPhysicalBinding.reference l
      := rfl
  erw [ActualSignedPhysicalData.nativePotentialSource, dite_eq_left hm]
  simp only [hband]
  split_ifs with hj
  · exact (nativePotentialCoefficient_eq P u H hp l k (ActualSignedPhysicalData.nativeCylinder
      y)).symm
  · rfl

theorem pressureSource_on_label (l : Label B N0) (j : PhysicalWaveSum.Harmonic 1)
    (k : Copy) (n : ℕ) (y : Native) :
    pressureSource (N0 := N0) P u H hp
      ⟨ActualSignedExterior.bandLabel l, ((ActualSignedExterior.bandLabel l, j), k)⟩ n y =
      if j.val = 1 ∧ n = ActualSignedPhysicalBinding.reference l then
        nativePressureCoefficient l P u k (ActualSignedPhysicalData.nativeCylinder y) else 0 := by
  classical
  change ((family P u H hp).pressureSource slots outgoing.data.h_pos.le
    (ActualSignedExterior.nativeLabel l)) ((ActualSignedExterior.bandLabel l, j), k) n y = _
  erw [DependentSignedPhysicalFamily.Family.pressureSource_active]
  have hm : ActualSignedExterior.bandLabel l ∈
      ((family P u H hp).singleton (ActualSignedExterior.nativeLabel l)).active :=
          Set.mem_singleton _
  have hband : (ActualSignedExterior.bandLabel l).val.1 = ActualSignedPhysicalBinding.reference l
      := rfl
  erw [ActualSignedPhysicalData.nativePressureSource, dite_eq_left hm]
  simp only [hband]
  split_ifs with hj
  · exact (nativePressureCoefficient_eq P u H hp l k (ActualSignedPhysicalData.nativeCylinder
      y)).symm
  · rfl

end SingletonSources

/-! ## Joint selection, with literal zeros at every omitted index -/

/-- Selection as an element of `E`. -/
noncomputable def selection {E : Type*} [Zero E]
    (g : (Label B N0 × Copy) → ℕ → Native → E) (I : SourceIndex) (n : ℕ) (y : Native) : E := by
  classical
  exact if hL : I.1 ∈ ActualSignedExterior.labels B N0 then
    if I.2.1.1 = I.1 ∧ I.2.1.2.val = 1 then
      g (ActualSignedExterior.actualLabel ⟨I.1.val, I.1.property, hL⟩, I.2.2) n y
    else 0
  else 0

theorem selection_on_label {E : Type*} [Zero E]
    (g : (Label B N0 × Copy) → ℕ → Native → E) (l : Label B N0)
    (j : PhysicalWaveSum.Harmonic 1) (k : Copy) (n : ℕ) (y : Native) :
    selection g ⟨ActualSignedExterior.bandLabel l, ((ActualSignedExterior.bandLabel l, j), k)⟩ n y =
      if j.val = 1 then g (l, k) n y else 0 := by
  classical
  have hL : ActualSignedExterior.bandLabel l ∈ ActualSignedExterior.labels B N0 := ⟨l, rfl⟩
  simp only [selection, dite_eq_left hL, true_and]
  change (if j.val = 1 then g (ActualSignedExterior.actualLabel (ActualSignedExterior.nativeLabel
      l), k) n y
    else 0) = _
  erw [ActualSignedExterior.actualLabel_nativeLabel]

theorem selection_inactive {E : Type*} [Zero E]
    (g : (Label B N0 × Copy) → ℕ → Native → E) (L : PhysicalWaveSum.BandLabel)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) (y : Native)
    (hL : L ∉ ActualSignedExterior.labels B N0) : selection g ⟨L, I⟩ n y = 0 := by
  classical
  simp only [selection, dite_eq_right hL]

theorem selection_other_label {E : Type*} [Zero E]
    (g : (Label B N0 × Copy) → ℕ → Native → E) (L : PhysicalWaveSum.BandLabel)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) (y : Native) (hI : I.1.1 ≠ L) :
    selection g ⟨L, I⟩ n y = 0 := by
  classical
  by_cases hL : L ∈ ActualSignedExterior.labels B N0 <;> simp [selection, hL, hI]

theorem selection_active_function {E : Type*} [Zero E]
    (g : (Label B N0 × Copy) → ℕ → Native → E) (I : SourceIndex) (n : ℕ)
    (hL : I.1 ∈ ActualSignedExterior.labels B N0)
    (hI : I.2.1.1 = I.1 ∧ I.2.1.2.val = 1) :
    selection g I n = g (ActualSignedExterior.actualLabel ⟨I.1.val, I.1.property, hL⟩, I.2.2) n :=
        by
  classical
  funext y
  simp only [selection, dite_eq_left hL, ite_eq_left hI]

theorem selection_zero_function {E : Type*} [Zero E]
    (g : (Label B N0 × Copy) → ℕ → Native → E) (I : SourceIndex) (n : ℕ)
    (hz : I.1 ∉ ActualSignedExterior.labels B N0 ∨ ¬(I.2.1.1 = I.1 ∧ I.2.1.2.val = 1)) :
    selection g I n = fun _ => 0 := by
  classical
  funext y
  rcases hz with hL | hI
  · simp only [selection, dite_eq_right hL]
  · by_cases hL : I.1 ∈ ActualSignedExterior.labels B N0 <;> simp [selection, hL, hI]

theorem selection_uniform {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {g : (Label B N0 × Copy) → ℕ → Native → E}
    (hg : UniformClass ActualPrimaryBounds.strip
      (fun _ _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y)) α g) :
    UniformClass ActualPrimaryBounds.strip weight α (selection g) := by
  classical
  refine ⟨fun _ _ _ _ => Real.sqrt_nonneg _, ?_, ?_⟩
  · intro I n
    by_cases hL : I.1 ∈ ActualSignedExterior.labels B N0
    · by_cases hI : I.2.1.1 = I.1 ∧ I.2.1.2.val = 1
      · rw [selection_active_function g I n hL hI]
        exact hg.smooth _ n
      · rw [selection_zero_function g I n (Or.inr hI)]
        exact contDiffOn_const
    · rw [selection_zero_function g I n (Or.inl hL)]
      exact contDiffOn_const
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hg.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro I n y hy j hj
    have hz := majorant_nonneg ActualPrimaryBounds.strip (weight I) α hC p n y (Real.sqrt_nonneg _)
    by_cases hL : I.1 ∈ ActualSignedExterior.labels B N0
    · by_cases hI : I.2.1.1 = I.1 ∧ I.2.1.2.val = 1
      · rw [selection_active_function g I n hL hI]
        exact hb _ n y hy j hj
      · rw [selection_zero_function g I n (Or.inr hI)]
        simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hz
    · rw [selection_zero_function g I n (Or.inl hL)]
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hz

section SourceSelection

variable (P : SignedStressPrimitive.Patch) (u : State LocalSignedRequest.Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)

theorem potentialSource_inactive (L : PhysicalWaveSum.BandLabel)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) (y : Native)
    (hL : L ∉ ActualSignedExterior.labels B N0) :
    potentialSource (N0 := N0) P u H hp ⟨L, I⟩ n y = 0 := by
  change ((family (N0 := N0) P u H hp).valueAt
    (fun K => ActualSignedPhysicalData.nativePotentialSource slots outgoing.data.h_pos.le
      ((family P u H hp).singleton K)) L) I n y = 0
  rw [DependentSignedPhysicalFamily.Family.valueAt_inactive _ _ hL]
  rfl

theorem pressureSource_inactive (L : PhysicalWaveSum.BandLabel)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) (y : Native)
    (hL : L ∉ ActualSignedExterior.labels B N0) :
    pressureSource (N0 := N0) P u H hp ⟨L, I⟩ n y = 0 := by
  change ((family (N0 := N0) P u H hp).valueAt
    (fun K => ActualSignedPhysicalData.nativePressureSource slots outgoing.data.h_pos.le
      ((family P u H hp).singleton K)) L) I n y = 0
  rw [DependentSignedPhysicalFamily.Family.valueAt_inactive _ _ hL]
  rfl

theorem potentialSource_other_label (L : PhysicalWaveSum.BandLabel)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) (y : Native) (hI : I.1.1 ≠ L) :
    potentialSource (N0 := N0) P u H hp ⟨L, I⟩ n y = 0 := by
  classical
  change ((family (N0 := N0) P u H hp).valueAt
    (fun K => ActualSignedPhysicalData.nativePotentialSource slots outgoing.data.h_pos.le
      ((family P u H hp).singleton K)) L) I n y = 0
  by_cases hL : L ∈ (family (N0 := N0) P u H hp).active
  · simp only [DependentSignedPhysicalFamily.Family.valueAt, dite_eq_left hL]
    have hm : I.1.1 ∉ ((family P u H hp).singleton ⟨L.val, L.property, hL⟩).active := by
      simpa only [DependentSignedPhysicalFamily.Family.singleton_active, Set.mem_singleton_iff]
          using hI
    erw [ActualSignedPhysicalData.nativePotentialSource, dite_eq_right hm]
  · rw [DependentSignedPhysicalFamily.Family.valueAt_inactive _ _ hL]
    rfl

theorem pressureSource_other_label (L : PhysicalWaveSum.BandLabel)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) (y : Native) (hI : I.1.1 ≠ L) :
    pressureSource (N0 := N0) P u H hp ⟨L, I⟩ n y = 0 := by
  classical
  change ((family (N0 := N0) P u H hp).valueAt
    (fun K => ActualSignedPhysicalData.nativePressureSource slots outgoing.data.h_pos.le
      ((family P u H hp).singleton K)) L) I n y = 0
  by_cases hL : L ∈ (family (N0 := N0) P u H hp).active
  · simp only [DependentSignedPhysicalFamily.Family.valueAt, dite_eq_left hL]
    have hm : I.1.1 ∉ ((family P u H hp).singleton ⟨L.val, L.property, hL⟩).active := by
      simpa only [DependentSignedPhysicalFamily.Family.singleton_active, Set.mem_singleton_iff]
          using hI
    erw [ActualSignedPhysicalData.nativePressureSource, dite_eq_right hm]
  · rw [DependentSignedPhysicalFamily.Family.valueAt_inactive _ _ hL]
    rfl

theorem potentialSource_eq_selection :
    potentialSource (N0 := N0) P u H hp = selection
      (fun (i : Label B N0 × Copy) n y => ownPotential (request (B := B) P u) i n (nativeToCommon
          i.1 y)) := by
  funext I n y
  rcases I with ⟨L, ⟨⟨M, j⟩, k⟩⟩
  by_cases hL : L ∈ ActualSignedExterior.labels B N0
  · rcases hL with ⟨l, rfl⟩
    by_cases hM : M = ActualSignedExterior.bandLabel l
    · subst M
      rw [potentialSource_on_label, selection_on_label]
      by_cases hj : j.val = 1
      · simp only [hj, true_and, ite_true]
        by_cases hn : n = ActualSignedPhysicalBinding.reference l
        · subst n
          rw [ite_eq_left rfl]
          change _ = ActualSignedUnmaskedBounds.ownField _ (l, k)
            (ActualSignedUnmaskedBounds.reference l) (nativeToCommon l y)
          rw [ActualSignedUnmaskedBounds.ownField_reference
            (fun l k n => ActualSignedOutputBounds.localPotential (request (B := B) P u) l n k) (l,
                k),
            nativeToCommon_eq]
          exact (localPotential_reference l P u H hp k (ActualSignedPhysicalData.nativeCylinder
              y)).symm
        · rw [ite_eq_right hn]
          change _ = ActualSignedUnmaskedBounds.ownField _ (l, k) n (nativeToCommon l y)
          rw [ActualSignedUnmaskedBounds.ownField_other _ _ hn]
      · simp only [hj, false_and, ite_false]
    · rw [potentialSource_other_label P u H hp _ _ _ _ hM,
        selection_other_label _ _ _ _ _ hM]
  · rw [potentialSource_inactive P u H hp _ _ _ _ hL,
      selection_inactive _ _ _ _ _ hL]

theorem pressureSource_eq_selection :
    pressureSource (N0 := N0) P u H hp = selection
      (fun (i : Label B N0 × Copy) n y => ownPressure (request (B := B) P u) i n (nativeToCommon
          i.1 y)) := by
  funext I n y
  rcases I with ⟨L, ⟨⟨M, j⟩, k⟩⟩
  by_cases hL : L ∈ ActualSignedExterior.labels B N0
  · rcases hL with ⟨l, rfl⟩
    by_cases hM : M = ActualSignedExterior.bandLabel l
    · subst M
      rw [pressureSource_on_label, selection_on_label]
      by_cases hj : j.val = 1
      · simp only [hj, true_and, ite_true]
        by_cases hn : n = ActualSignedPhysicalBinding.reference l
        · subst n
          rw [ite_eq_left rfl]
          change _ = ActualSignedUnmaskedBounds.ownField _ (l, k)
            (ActualSignedUnmaskedBounds.reference l) (nativeToCommon l y)
          rw [ActualSignedUnmaskedBounds.ownField_reference
            (fun l k n => ((ActualSignedOutputBounds.copies (request (B := B) P u) l).localized
                k).pressure n) (l, k),
            nativeToCommon_eq]
          exact (localPressure_reference l P u H hp k (ActualSignedPhysicalData.nativeCylinder
              y)).symm
        · rw [ite_eq_right hn]
          change _ = ActualSignedUnmaskedBounds.ownField _ (l, k) n (nativeToCommon l y)
          rw [ActualSignedUnmaskedBounds.ownField_other _ _ hn]
      · simp only [hj, false_and, ite_false]
    · rw [pressureSource_other_label P u H hp _ _ _ _ hM,
        selection_other_label _ _ _ _ _ hM]
  · rw [pressureSource_inactive P u H hp _ _ _ _ hL,
      selection_inactive _ _ _ _ _ hL]

end SourceSelection

/-! ## Joint bounds for the literal sources -/

section Bounds

variable (P : SignedStressPrimitive.Patch) (u : State LocalSignedRequest.Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)

/-- One set of constants controls every outer label, inner label, harmonic,
reference band and lattice copy of the actual native sources. -/
theorem source_uniform {β : ℝ}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets ActualSignedStageControls.fullStrip
      (fun _ _ x => ActualSignedStageControls.fullStrip.zeta x) β
      (ActualSignedStageControls.phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request (B := B) P u n x q)) :
    UniformClass ActualPrimaryBounds.strip weight (β + 1)
      (potentialSource (N0 := N0) P u H hp) ∧
    UniformClass ActualPrimaryBounds.strip weight (β + 1)
      (pressureSource (N0 := N0) P u H hp) := by
  obtain ⟨hA, hpA⟩ := own_potential_pressure_uniform hR
  rw [potentialSource_eq_selection, pressureSource_eq_selection]
  exact ⟨selection_uniform (uniform_nativeToCommon hA),
    selection_uniform (uniform_nativeToCommon hpA)⟩

/-- The fixed native strip supplies the geometric components of the physical
source interface at every real exponent. -/
theorem native_source_bounds {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {f : I → ℕ → Native → E}
    (hf : UniformClass ActualPrimaryBounds.strip
      (fun _ _ x => Real.sqrt (ActualPrimaryBounds.strip.zeta x)) α f) :
    LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
      (fun _ _ x => Real.sqrt (ActualPrimaryBounds.strip.zeta x)) f := by
  refine ⟨hf, InitialPhysicalData.strip_flat_geometry, ⟨1 / 2, by norm_num, ?_⟩,
    fun _ => rfl, ⟨1, le_rfl, 1, ?_⟩⟩
  · intro l n x hx
    exact (Real.sqrt_eq_rpow _).le
  · intro n hn
    have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
    change max 1 (ChartScales.S n) ≤ 1 * ChartScales.S n ^ 1
    simp only [max_eq_right hS, pow_one, one_mul, le_refl]

theorem source_bounds {β : ℝ}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets ActualSignedStageControls.fullStrip
      (fun _ _ x => ActualSignedStageControls.fullStrip.zeta x) β
      (ActualSignedStageControls.phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request (B := B) P u n x q)) :
    LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h (β + 1) weight
      (potentialSource (N0 := N0) P u H hp) ∧
    LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h (β + 1) weight
      (pressureSource (N0 := N0) P u H hp) := by
  obtain ⟨hA, hpA⟩ := source_uniform P u H hp hR
  exact ⟨native_source_bounds hA, native_source_bounds hpA⟩

end Bounds

/-- The request premise can itself be discharged by the measured theta and
axial residual classes of this same reconstructed state. -/
theorem source_bounds_from_residuals
    (u : State LocalSignedRequest.Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b u.pressure)
    (hfixed : VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u = u)
    (hθ : MeanClass ActualInitialization.geometry.strip α (u.thetaResidual (commonContext B)))
    (hz : MeanClass ActualInitialization.geometry.strip α (u.axialResidual (commonContext B))) :
    LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α weight
      (potentialSource (N0 := N0) ActualInitialization.patch u H hp) ∧
    LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α weight
      (pressureSource (N0 := N0) ActualInitialization.patch u H hp) := by
  have hR := ActualSignedStageControls.fullRequest_jets_from_residuals
    ActualInitialization.geometry (commonContext B) u α H hfixed hθ hz
    (ActualSignedStageControls.phaseCell (B := B) (N0 := N0))
  simpa only [sub_add_cancel] using source_bounds ActualInitialization.patch u H hp hR

end NavierStokes.ActualSignedNativeBounds
