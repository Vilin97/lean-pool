/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedReferenceGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.GluedStageEstimates
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalBinding
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveRegularityData
import LeanPool.NavierStokesAndEuler.NavierStokes.InitialPhysicalData
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalCopyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedOutputBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedUnmaskedBounds

/-!
# Physical wave data for the actual signed cycle fields

The native family is the family in `ActualSignedExterior`. Geometry,
profiles and native source bounds are assembled before any physical
estimate is applied.
-/

section

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
    linarith [norm_nonneg y]
  have hY : |x.2| ≤ ‖y‖ := by
    rw [hy, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 14)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 14)).mpr
    have ha := abs_sub (3 * y.2) y.1
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at ha
    linarith [norm_nonneg y]
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

end
end

end

section

/-!
# Positive lift-time localization of actual copy amplitudes

The gate changes only the amplitude outside positive lift time.  The physical
common lift has positive time exactly before terminal time, so all physical
copy fields and their ambient jets agree there with the original fields.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.PositiveTimeCopyFamily

open Set Function Filter ProblemStatement PhysicalCopyBounds
open PhysicalWaveSum (WaveIndex commonLift preterminal)
open scoped Topology ContDiff BigOperators

/-- Lift point: an abbreviation for `PhysicalGraphBounds.LiftPoint`. -/
abbrev LiftPoint := PhysicalGraphBounds.LiftPoint

/-- Lift past, given by `{x | 0 < x.1.1}`. -/
def liftPast : Set LiftPoint := {x | 0 < x.1.1}

theorem liftPast_open : IsOpen liftPast :=
  isOpen_lt continuous_const continuous_fst.fst

/-- The carrier and gap are unchanged. Only the amplitude is extended by
zero outside positive native lift time. -/
noncomputable def gate {H : ℕ} {K : Type*} (f : CopyFamily H K) : CopyFamily H K := by
  classical
  exact {
    gap := f.gap
    carrier := f.carrier
    amplitude k I x := if x ∈ liftPast then f.amplitude k I x else 0 }

variable {H : ℕ} {K : Type*}

@[simp] theorem gate_gap (f : CopyFamily H K) : (gate f).gap = f.gap := rfl

@[simp] theorem gate_carrier (f : CopyFamily H K) : (gate f).carrier = f.carrier := rfl

theorem gate_amplitude_eq (f : CopyFamily H K) (k : K) (I : WaveIndex H)
    {x : LiftPoint} (hx : x ∈ liftPast) : (gate f).amplitude k I x = f.amplitude k I x := by
  simp only [gate, ite_eq_left hx]

theorem gate_amplitude_zero (f : CopyFamily H K) (k : K) (I : WaveIndex H)
    {x : LiftPoint} (hx : x ∉ liftPast) : (gate f).amplitude k I x = 0 := by
  simp only [gate, ite_eq_right hx]

theorem gate_amplitude_ne_zero_iff (f : CopyFamily H K) (k : K) (I : WaveIndex H)
    (x : LiftPoint) :
    (gate f).amplitude k I x ≠ 0 ↔ x ∈ liftPast ∧ f.amplitude k I x ≠ 0 := by
  classical
  by_cases hx : x ∈ liftPast <;> simp [gate, hx]

theorem gate_amplitude_germ (f : CopyFamily H K) (k : K) (I : WaveIndex H)
    {x : LiftPoint} (hx : x ∈ liftPast) :
    (gate f).amplitude k I =ᶠ[𝓝 x] f.amplitude k I := by
  filter_upwards [liftPast_open.mem_nhds hx] with y hy
  exact gate_amplitude_eq f k I hy

theorem gate_amplitude_jets (f : CopyFamily H K) (k : K) (I : WaveIndex H)
    {x : LiftPoint} (hx : x ∈ liftPast) (m : ℕ) :
    iteratedFDeriv ℝ m ((gate f).amplitude k I) x =
      iteratedFDeriv ℝ m (f.amplitude k I) x :=
  PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (gate_amplitude_germ f k I hx) m

theorem gate_amplitude_support_subset (f : CopyFamily H K) (k : K) (I : WaveIndex H) :
    support ((gate f).amplitude k I) ⊆ support (f.amplitude k I) :=
  fun x hx => ((gate_amplitude_ne_zero_iff f k I x).mp hx).2

/-- The original closed copy cells still contain the gated amplitude. -/
noncomputable def gateCells {f : CopyFamily H K} (hc : SupportCells f) : SupportCells (gate f) where
  cells := hc.cells
  support I k := (gate_amplitude_support_subset f k I).trans (hc.support I k)

@[simp] theorem gateCells_cells {f : CopyFamily H K} (hc : SupportCells f) :
    (gateCells hc).cells = hc.cells := rfl

/-- Carrier bounds refer to the same carrier and the same cells. -/
noncomputable def gateCarrier {f : CopyFamily H K} (hc : SupportCells f) {a b h r0 : ℝ}
    (hb : CarrierBounds f hc a b h r0) : CarrierBounds (gate f) (gateCells hc) a b h r0 where
  region := hb.region
  open_region := hb.open_region
  jets := hb.jets
  contains := hb.contains

@[simp] theorem gateCarrier_region {f : CopyFamily H K} (hc : SupportCells f) {a b h r0 : ℝ}
    (hb : CarrierBounds f hc a b h r0) : (gateCarrier hc hb).region = hb.region := rfl

theorem commonLift_time (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    (commonLift h n d w).1.1 = (1 - w.1) / ChartScales.Q n :=
  PhysicalGraphBounds.physicalChart_time h n w

/-- This identity also holds on the axis and for arbitrary cover gap. -/
theorem commonLift_mem_liftPast_iff (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    commonLift h n d w ∈ liftPast ↔ w ∈ preterminal := by
  change 0 < (commonLift h n d w).1.1 ↔ w.1 < 1
  rw [commonLift_time, div_pos_iff_of_pos_right (ChartScales.Q_pos n), sub_pos]

theorem commonLift_mem_liftPast (h : ℝ) (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal) :
    commonLift h n d w ∈ liftPast := (commonLift_mem_liftPast_iff h n d w).mpr hw

section PhysicalFields

variable (f : CopyFamily H K) (a h r0 : ℝ)

theorem term_eq (I : WaveIndex H) (k : K) {w : SpaceTime} (hw : w ∈ preterminal) :
    (gate f).term a h r0 I k w = f.term a h r0 I k w := by
  have hl := commonLift_mem_liftPast h I.1.val.1 (f.gap I.1) hw
  simp only [CopyFamily.term, CopyFamily.copy, PhysicalWaveSum.WaveFamily.term,
    PhysicalWaveSum.globalWave, PhysicalWaveSum.commonWave, gate, ite_eq_left hl]

theorem term_zero (I : WaveIndex H) (k : K) {w : SpaceTime} (hw : w ∉ preterminal) :
    (gate f).term a h r0 I k w = 0 := by
  apply PhysicalWaveSum.globalWave_eq_zero
  exact gate_amplitude_zero f k I (fun hl => hw ((commonLift_mem_liftPast_iff h
    I.1.val.1 (f.gap I.1) w).mp hl))

theorem term_germ (I : WaveIndex H) (k : K) {w : SpaceTime} (hw : w ∈ preterminal) :
    (gate f).term a h r0 I k =ᶠ[𝓝 w] f.term a h r0 I k := by
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds hw] with y hy
  exact term_eq f a h r0 I k hy

theorem term_jets (I : WaveIndex H) (k : K) {w : SpaceTime} (hw : w ∈ preterminal) (m : ℕ) :
    iteratedFDeriv ℝ m ((gate f).term a h r0 I k) w =
      iteratedFDeriv ℝ m (f.term a h r0 I k) w :=
  PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (term_germ f a h r0 I k hw) m

theorem term_support_subset (I : WaveIndex H) (k : K) :
    support ((gate f).term a h r0 I k) ⊆ support (f.term a h r0 I k) := by
  intro w hw
  by_cases ht : w ∈ preterminal
  · simpa only [mem_support, term_eq f a h r0 I k ht] using hw
  · exact (hw (term_zero f a h r0 I k ht)).elim

theorem term_tsupport_subset (I : WaveIndex H) (k : K) :
    tsupport ((gate f).term a h r0 I k) ⊆ tsupport (f.term a h r0 I k) :=
  closure_mono (term_support_subset f a h r0 I k)

theorem periodized_eq (I : WaveIndex H) {w : SpaceTime} (hw : w ∈ preterminal) :
    (gate f).periodized a h r0 I w = f.periodized a h r0 I w := by
  apply tsum_congr
  intro k
  exact term_eq f a h r0 I k hw

theorem periodized_zero (I : WaveIndex H) {w : SpaceTime} (hw : w ∉ preterminal) :
    (gate f).periodized a h r0 I w = 0 := by
  simp only [CopyFamily.periodized, term_zero f a h r0 I _ hw, tsum_zero]

theorem periodized_germ (I : WaveIndex H) {w : SpaceTime} (hw : w ∈ preterminal) :
    (gate f).periodized a h r0 I =ᶠ[𝓝 w] f.periodized a h r0 I := by
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds hw] with y hy
  exact periodized_eq f a h r0 I hy

theorem periodized_jets (I : WaveIndex H) {w : SpaceTime} (hw : w ∈ preterminal) (m : ℕ) :
    iteratedFDeriv ℝ m ((gate f).periodized a h r0 I) w =
      iteratedFDeriv ℝ m (f.periodized a h r0 I) w :=
  PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (periodized_germ f a h r0 I hw) m

theorem sum_eq {w : SpaceTime} (hw : w ∈ preterminal) :
    (gate f).sum a h r0 w = f.sum a h r0 w := by
  exact congrArg (fun g : WaveIndex H → ℂ => ∑ᶠ I, g I)
    (funext (fun I => periodized_eq f a h r0 I hw))

theorem sum_zero {w : SpaceTime} (hw : w ∉ preterminal) : (gate f).sum a h r0 w = 0 := by
  simp only [CopyFamily.sum, periodized_zero f a h r0 _ hw, finsum_zero]

theorem sum_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    (gate f).sum a h r0 =ᶠ[𝓝 w] f.sum a h r0 := by
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds hw] with y hy
  exact sum_eq f a h r0 hy

theorem sum_jets {w : SpaceTime} (hw : w ∈ preterminal) (m : ℕ) :
    iteratedFDeriv ℝ m ((gate f).sum a h r0) w = iteratedFDeriv ℝ m (f.sum a h r0) w :=
  PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (sum_germ f a h r0 hw) m

end PhysicalFields

section VectorFields

variable (f : Fin 3 → CopyFamily H K) (a h r0 : ℝ)

theorem vectorSum_eq {w : SpaceTime} (hw : w ∈ preterminal) :
    PhysicalCopyBounds.vectorSum (fun i => gate (f i)) a h r0 w =
      PhysicalCopyBounds.vectorSum f a h r0 w := by
  simp only [PhysicalCopyBounds.vectorSum, sum_eq (f _) a h r0 hw]

theorem vectorSum_zero {w : SpaceTime} (hw : w ∉ preterminal) :
    PhysicalCopyBounds.vectorSum (fun i => gate (f i)) a h r0 w = 0 := by
  simp only [PhysicalCopyBounds.vectorSum, sum_zero (f _) a h r0 hw, map_zero,
      Finset.sum_const_zero]

theorem vectorSum_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    PhysicalCopyBounds.vectorSum (fun i => gate (f i)) a h r0 =ᶠ[𝓝 w]
      PhysicalCopyBounds.vectorSum f a h r0 := by
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds hw] with y hy
  exact vectorSum_eq f a h r0 hy

theorem vectorSum_jets {w : SpaceTime} (hw : w ∈ preterminal) (m : ℕ) :
    iteratedFDeriv ℝ m (PhysicalCopyBounds.vectorSum (fun i => gate (f i)) a h r0) w =
      iteratedFDeriv ℝ m (PhysicalCopyBounds.vectorSum f a h r0) w :=
  PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (vectorSum_germ f a h r0 hw) m

end VectorFields

end NavierStokes.PositiveTimeCopyFamily

end
end

end

section

/-!
# Signed physical data from positive native time

The native signed sources are used only at positive native time.  Their
totalized formula need not vanish in the past of that domain.  This module
uses an explicit zero extension of the physical copy amplitudes outside
positive native time, while retaining the original masks, sources, and
carrier profiles on their genuine domains.
-/

section

/-!
# Localization of the actual signed inputs at positive native time

The fixed primary's mask and target localize its native point. Positive
native time is an explicit premise; no support assertion is made for the
totalized formulas outside that domain.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.PositiveTimeSignedLocalization

open Set Function
open CorrectionInitialization CorrectionInitialization.ActualPrimary

/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label`. -/
abbrev Label := ActualSignedPhysicalBinding.Label
/-- Native: an abbreviation for `ActualSignedPhysicalData.Native`. -/
abbrev Native := ActualSignedPhysicalData.Native

variable {B N0 : ℕ}

theorem profileRadius_eq (y : Native) :
    PrimaryTargetBounds.profileRadius h (ActualSignedPhysicalData.nativeSlow y) =
      y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) := by
  rw [PrimaryTargetBounds.profileRadius, BaseChartJets.normalizedCoordinates_eq]
  rfl

/-- The actual dyadic mask is supported strictly inside its two endpoints. -/
theorem mask_q_mem (l : Label B N0) (y : Native)
    (hm : (ActualSignedPhysicalBinding.primary l).mask
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0) :
    SimilarityCoordinates.coordinateQ (2 * h) y.2.1 ∈ Ioo (1 / 2 : ℝ) 2 := by
  exact spatialMask_q_range l.1 (ActualSignedPhysicalData.nativeSlow y) hm

/-- Positivity comes from the same chosen prepared carrier, without an
additional nondegeneracy premise on the signed output. -/
theorem mask_radius_pos (l : Label B N0) (y : Native) (hT : 0 < y.2.1.1)
    (hm : (ActualSignedPhysicalBinding.primary l).mask
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0) :
    0 < y.1 := by
  exact (choice B N0).prepared.radius_pos l.1 (ActualSignedPhysicalData.nativeSlow y)
    (spatialMask_carrier l.1 hT hm)

/-- Nonzero actual target forces the normalized radius into the open
nominal active annulus. The endpoint zeros are used exactly. -/
theorem normalized_radius_mem (l : Label B N0) (y : Native) (hT : 0 < y.2.1.1)
    (hm : (ActualSignedPhysicalBinding.primary l).mask
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0)
    (ht : (ActualSignedPhysicalBinding.primary l).target
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0) :
    y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) := by
  by_contra ho
  have hz := ActualWaveRegularityData.target_zero_outside
    (p := ActualSignedPhysicalData.nativeSlow y) hT (mask_radius_pos l y hT hm)
    (by simpa only [profileRadius_eq] using ho)
  apply ht
  change (fun j => PrimaryTargetBounds.actualTarget modulation
    (ActualSignedPhysicalData.nativeSlow y) j) = 0
  simp only [hz, WithLp.ofLp_zero, Pi.zero_apply]
  rfl

/-- The inequalities in the positive-time localization interface. -/
theorem normalized_bounds (l : Label B N0) (y : Native) (hT : 0 < y.2.1.1)
    (hm : (ActualSignedPhysicalBinding.primary l).mask
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0)
    (ht : (ActualSignedPhysicalBinding.primary l).target
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0) :
    1 / 2 ≤ SimilarityCoordinates.coordinateQ (2 * h) y.2.1 ∧
      SimilarityCoordinates.coordinateQ (2 * h) y.2.1 ≤ 2 ∧
      PrimaryTargetBounds.leftRadius nominal ≤
        y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ∧
      y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ≤
        PrimaryTargetBounds.rightRadius nominal :=
  ⟨(mask_q_mem l y hm).1.le, (mask_q_mem l y hm).2.le,
    (normalized_radius_mem l y hT hm ht).1.le, (normalized_radius_mem l y hT hm ht).2.le⟩

/-- Membership is in the actual moving strip, with the same fixed primary
annulus and slow region used by the native signed estimates. -/
theorem native_mem_strip (l : Label B N0) (y : Native) (hT : 0 < y.2.1.1)
    (hm : (ActualSignedPhysicalBinding.primary l).mask
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0)
    (ht : (ActualSignedPhysicalBinding.primary l).target
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0) :
    y ∈ ActualPrimaryBounds.strip.domain := by
  apply (BaseContextAssembly.nativeStrip_mem nominal ActualPrimaryBounds.region y).mpr
  refine ⟨⟨hT, mask_q_mem l y hm⟩, ?_⟩
  change PrimaryTargetBounds.profileRadius h (ActualSignedPhysicalData.nativeSlow y) ∈ _
  rw [profileRadius_eq]
  exact normalized_radius_mem l y hT hm ht

/-- The same selected mask pulls back to the literal physical label mask
at every preterminal Cartesian point. -/
theorem mask_pullback (l : Label B N0) (w : ProblemStatement.SpaceTime)
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    (ActualSignedPhysicalBinding.primary l).mask (ActualSignedPhysicalBinding.reference l)
        (ActualSignedPhysicalData.cylinderZero
          (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l) w)) =
      PhysicalWaveSum.physicalMask (CoordinateAlgebra.D h)
        (ActualSignedPhysicalBinding.spatialLabel l) (PhysicalWaveSum.physicalParams h w) := by
  have hm := InitialPhysicalData.spatialMask_physical (l.2, l.1) 0 hw
  rw [ActualSignedPhysicalData.commonLift_zero] at hm
  exact hm

end NavierStokes.PositiveTimeSignedLocalization

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.PositiveTimeSignedData

open Set Function Filter ProblemStatement HarmonicCalculus WeightedClasses
open ActualSignedPhysicalData
open scoped Topology ContDiff BigOperators

attribute [local instance] Classical.propDecidable

/-- The original mask and target localize the native source only where
native time is positive.  The time hypothesis is explicit in both fields. -/
structure PrimitiveLocalization {h : ℝ}
    {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (f : SignedFamily U)
    (a b : ℝ) (s : StripData Native) : Prop where
  normalized : ∀ (L : NativeLabel f.active) (y : Native), y ∈ nativePast → 0 ≤ y.1 →
    (f.primary L).mask L.val.1 (nativeCylinder y) ≠ 0 →
    (f.primary L).target L.val.1 (nativeCylinder y) ≠ 0 →
    1 / 2 ≤ SimilarityCoordinates.coordinateQ (2 * h) y.2.1 ∧
      SimilarityCoordinates.coordinateQ (2 * h) y.2.1 ≤ 2 ∧
      a ≤ y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ∧
      y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ≤ b
  domain : ∀ (L : NativeLabel f.active) (y : Native), y ∈ nativePast → 0 ≤ y.1 →
    (f.primary L).mask L.val.1 (nativeCylinder y) ≠ 0 →
    (f.primary L).target L.val.1 (nativeCylinder y) ≠ 0 → y ∈ s.domain
  mask_pullback : ∀ (L : NativeLabel f.active) (w : SpaceTime),
    w ∈ PhysicalWaveSum.preterminal →
    (f.primary L).mask L.val.1
        (cylinderZero (PhysicalGraphBounds.physicalLift h L.val.1 w)) =
      PhysicalWaveSum.physicalMask (CoordinateAlgebra.D h) L.val
        (PhysicalWaveSum.physicalParams h w)

section Localization

variable {h a b : ℝ} {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
  {f : SignedFamily U} {s : StripData Native}
  (hloc : PrimitiveLocalization (h := h) f a b s)

include hloc

/-- Positive-time primitive localization supplies the actual Cartesian
annulus and slow-coordinate bound. -/
theorem primitive_annulus (hh0 : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hb : 0 < b) (L : NativeLabel f.active) (x : LiftPoint)
    (hx : 0 < x.1.1)
    (hm : (f.primary L).mask L.val.1 (cylinderZero x) ≠ 0)
    (hT : (f.primary L).target L.val.1 (cylinderZero x) ≠ 0) :
    PhysicalGraphBounds.liftXY x ∈ PhysicalGraphBounds.annulus (a / 4) (2 * b) ∧
      ‖PhysicalGraphBounds.liftZT x‖ ≤ 2 := by
  let y := PhysicalClassBounds.cylindricalMap x
  have hy := hloc.normalized L y hx (Real.sqrt_nonneg _) hm hT
  have hq : 0 < SimilarityCoordinates.coordinateQ (2 * h) y.2.1 := by linarith [hy.1]
  have hs := Real.sqrt_pos.mpr hq
  have hslow := normalized_slow_norm hh0 hh1 hx hy.1 hy.2.1
  have hlo : 1 / 2 ≤ Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) :=
    (Real.le_sqrt (by norm_num) hq.le).mpr (by linarith [hy.1])
  have hhi : Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ≤ 2 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by linarith [hy.2.1])
  have hradlo := (le_div_iff₀ hs).mp hy.2.2.1
  have hradhi := (div_le_iff₀ hs).mp hy.2.2.2
  have hR : y.1 = PolarCharts.radius (PhysicalGraphBounds.liftXY x) := rfl
  rw [hR] at hradlo hradhi
  have hnorm : ‖PhysicalGraphBounds.liftXY x‖ ≤ 2 * b := by
    exact (PolarCharts.norm_le_radius _).trans (hradhi.trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hhi hb.le))
  have hnormlo : a / 4 ≤ ‖PhysicalGraphBounds.liftXY x‖ := by
    have hradius := PolarCharts.radius_le_two_norm (PhysicalGraphBounds.liftXY x)
    have hmul := mul_le_mul_of_nonneg_left hlo ha.le
    linarith
  constructor
  · exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm, hnormlo⟩
  · change max ‖x.1.2.2.2‖ ‖x.1.1‖ ≤ 2
    change max ‖x.1.1‖ ‖x.1.2.2.2‖ ≤ 2 at hslow
    simpa only [max_comm] using hslow

theorem primitive_domain (L : NativeLabel f.active) (x : LiftPoint)
    (hx : 0 < x.1.1)
    (hm : (f.primary L).mask L.val.1 (cylinderZero x) ≠ 0)
    (hT : (f.primary L).target L.val.1 (cylinderZero x) ≠ 0) :
    PhysicalClassBounds.cylindricalMap x ∈ s.domain :=
  hloc.domain L _ hx (Real.sqrt_nonneg _) hm hT

end Localization

section Copies

variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h
    ActualSignedGeometry.radialVector ActualSignedGeometry.temporalVector)
  (hh : 0 ≤ h) {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (f : SignedFamily U)

/-- Only the positive-time representative changes; the native potential
source and every carrier are the original ones. -/
noncomputable def potentialCopies (i : Fin 3) : PhysicalCopyBounds.CopyFamily 1 Frequency :=
  PositiveTimeCopyFamily.gate (ActualSignedPhysicalData.potentialFamily sys hh f i)

/-- Pressure copies, given by `PositiveTimeCopyFamily.gate
(ActualSignedPhysicalData.pressureFamily sys hh f)`. -/
noncomputable def pressureCopies : PhysicalCopyBounds.CopyFamily 1 Frequency :=
  PositiveTimeCopyFamily.gate (ActualSignedPhysicalData.pressureFamily sys hh f)

/-- Potential cells, given by `PositiveTimeCopyFamily.gateCells (localizedPotentialCells sys hh
f i)`. -/
noncomputable def potentialCells (i : Fin 3) :
    PhysicalCopyBounds.SupportCells (potentialCopies sys hh f i) :=
  PositiveTimeCopyFamily.gateCells (localizedPotentialCells sys hh f i)

/-- Pressure cells, given by `PositiveTimeCopyFamily.gateCells (localizedPressureCells sys hh
f)`. -/
noncomputable def pressureCells :
    PhysicalCopyBounds.SupportCells (pressureCopies sys hh f) :=
  PositiveTimeCopyFamily.gateCells (localizedPressureCells sys hh f)

variable {a b : ℝ} {s : StripData Native}
  (hloc : PrimitiveLocalization (h := h) f a b s)
  (G : ReferenceGeometry sys f) (hh0 : 0 < h) (hh1 : h < 1 / 2)
  (ha : 0 < a) (hb : 0 < b)

include hloc G hh0 hh1 ha hb

/-- The globally quantified support record is valid for the explicit
positive-time amplitude representative. -/
theorem potential_support (i : Fin 3) :
    LocalPhysicalCopyBounds.SupportData (potentialCopies sys hh f i)
      (a / 4) (2 * b) h sys.radius 2 0 where
  gap_le _ := le_rfl
  gap_native _ := Nat.zero_le _
  angular_integer k L := by
    by_cases hL : L ∈ f.active
    · refine ⟨(G.angular ⟨L.val, L.property, hL⟩).mode, ?_⟩
      simpa only [potentialCopies, PositiveTimeCopyFamily.gate,
        ActualSignedPhysicalData.potentialFamily, extendedCarrier, dite_eq_left hL] using
        angular_integer sys f G ⟨L.val, L.property, hL⟩ k
    · exact ⟨0, by simp [potentialCopies, PositiveTimeCopyFamily.gate,
        ActualSignedPhysicalData.potentialFamily, extendedCarrier, hL,
        ActualSignedPhysicalData.carrier]⟩
  geometry_support k I w hw := by
    obtain ⟨hpast, hraw⟩ := (PositiveTimeCopyFamily.gate_amplitude_ne_zero_iff
      (ActualSignedPhysicalData.potentialFamily sys hh f i) k I _).mp hw
    change 0 < (PhysicalWaveSum.commonLift h I.1.val.1 0 w).1.1 at hpast
    change (ActualSignedPhysicalData.potentialFamily sys hh f i).amplitude k I
      (PhysicalWaveSum.commonLift h I.1.val.1 0 w) ≠ 0 at hraw
    rw [commonLift_zero] at hpast hraw
    obtain ⟨hL, _, hm, ht⟩ := potential_amplitude_inputs sys hh f i k I _ hraw
    have hn := primitive_annulus hloc hh0 hh1 ha hb
      ⟨I.1.val, I.1.property, hL⟩ _ hpast hm ht
    refine ⟨?_, hn.2, ?_⟩
    · simpa only [PhysicalGraphBounds.liftXY_physicalLift] using hn.1
    · have hc := potential_amplitude_mem sys hh f i k I _ hraw
      have hwid := width_on_core sys I.1.val 0 k
        (PhysicalGraphBounds.physicalLift h I.1.val.1 w).2 hc
      change |PhysicalGraphBounds.etaCoordinate
        (PhysicalGraphBounds.nativeGraph h I.1.val.1 w -
          (extendedCarrier (h := h) f I.1 k).center)| ≤ sys.radius
      rw [extendedCarrier_center]
      exact hwid
  mask_support k I w hw hne := by
    have hraw := ((PositiveTimeCopyFamily.gate_amplitude_ne_zero_iff
      (ActualSignedPhysicalData.potentialFamily sys hh f i) k I _).mp hne).2
    change (ActualSignedPhysicalData.potentialFamily sys hh f i).amplitude k I
      (PhysicalWaveSum.commonLift h I.1.val.1 0 w) ≠ 0 at hraw
    rw [commonLift_zero] at hraw
    obtain ⟨hL, _, hm, _⟩ := potential_amplitude_inputs sys hh f i k I _ hraw
    rw [← hloc.mask_pullback ⟨I.1.val, I.1.property, hL⟩ w hw]
    exact hm

theorem pressure_support :
    LocalPhysicalCopyBounds.SupportData (pressureCopies sys hh f)
      (a / 4) (2 * b) h sys.radius 2 0 where
  gap_le _ := le_rfl
  gap_native _ := Nat.zero_le _
  angular_integer k L := by
    by_cases hL : L ∈ f.active
    · refine ⟨(G.angular ⟨L.val, L.property, hL⟩).mode, ?_⟩
      simpa only [pressureCopies, PositiveTimeCopyFamily.gate,
        ActualSignedPhysicalData.pressureFamily, extendedCarrier, dite_eq_left hL] using
        angular_integer sys f G ⟨L.val, L.property, hL⟩ k
    · exact ⟨0, by simp [pressureCopies, PositiveTimeCopyFamily.gate,
        ActualSignedPhysicalData.pressureFamily, extendedCarrier, hL,
        ActualSignedPhysicalData.carrier]⟩
  geometry_support k I w hw := by
    obtain ⟨hpast, hraw⟩ := (PositiveTimeCopyFamily.gate_amplitude_ne_zero_iff
      (ActualSignedPhysicalData.pressureFamily sys hh f) k I _).mp hw
    change 0 < (PhysicalWaveSum.commonLift h I.1.val.1 0 w).1.1 at hpast
    change (ActualSignedPhysicalData.pressureFamily sys hh f).amplitude k I
      (PhysicalWaveSum.commonLift h I.1.val.1 0 w) ≠ 0 at hraw
    rw [commonLift_zero] at hpast hraw
    obtain ⟨hL, _, hm, ht⟩ := pressure_amplitude_inputs sys hh f k I _ hraw
    have hn := primitive_annulus hloc hh0 hh1 ha hb
      ⟨I.1.val, I.1.property, hL⟩ _ hpast hm ht
    refine ⟨?_, hn.2, ?_⟩
    · simpa only [PhysicalGraphBounds.liftXY_physicalLift] using hn.1
    · have hc := pressure_amplitude_mem sys hh f k I _ hraw
      have hwid := width_on_core sys I.1.val 0 k
        (PhysicalGraphBounds.physicalLift h I.1.val.1 w).2 hc
      change |PhysicalGraphBounds.etaCoordinate
        (PhysicalGraphBounds.nativeGraph h I.1.val.1 w -
          (extendedCarrier (h := h) f I.1 k).center)| ≤ sys.radius
      rw [extendedCarrier_center]
      exact hwid
  mask_support k I w hw hne := by
    have hraw := ((PositiveTimeCopyFamily.gate_amplitude_ne_zero_iff
      (ActualSignedPhysicalData.pressureFamily sys hh f) k I _).mp hne).2
    change (ActualSignedPhysicalData.pressureFamily sys hh f).amplitude k I
      (PhysicalWaveSum.commonLift h I.1.val.1 0 w) ≠ 0 at hraw
    rw [commonLift_zero] at hraw
    obtain ⟨hL, _, hm, _⟩ := pressure_amplitude_inputs sys hh f k I _ hraw
    rw [← hloc.mask_pullback ⟨I.1.val, I.1.property, hL⟩ w hw]
    exact hm

omit hloc G hh0 hh1 hb in
/-- Potential carrier, constructed using `PositiveTimeCopyFamily.gateCarrier`. -/
noncomputable def potentialCarrier (hp : NativeProfiles (h := h) f) (i : Fin 3) :
    PhysicalCopyBounds.CarrierBounds (potentialCopies sys hh f i)
      (potentialCells sys hh f i) (a / 4) (2 * b) h sys.radius :=
  PositiveTimeCopyFamily.gateCarrier (localizedPotentialCells sys hh f i)
    (ActualSignedPhysicalData.potentialCarrier sys hh f ha hp i)

omit hloc G hh0 hh1 hb in
/-- Pressure carrier, given by `PositiveTimeCopyFamily.gateCarrier (localizedPressureCells sys
hh f) (ActualSignedPhysicalData.pressureCarrier sys hh f ha hp)`. -/
noncomputable def pressureCarrier (hp : NativeProfiles (h := h) f) :
    PhysicalCopyBounds.CarrierBounds (pressureCopies sys hh f)
      (pressureCells sys hh f) (a / 4) (2 * b) h sys.radius :=
  PositiveTimeCopyFamily.gateCarrier (localizedPressureCells sys hh f)
    (ActualSignedPhysicalData.pressureCarrier sys hh f ha hp)

omit hloc G hh0 hh1 hb in
theorem potential_amplitude_smooth (hn : NativeRegular sys hh f)
    (i : Fin 3) (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1) :
    ContDiffOn ℝ ∞ ((potentialCopies sys hh f i).amplitude k I) (liftedNativePast a b) := by
  apply (ActualSignedPhysicalData.potential_amplitude_smooth sys hh f ha hn i k I).congr
  intro x hx
  exact PositiveTimeCopyFamily.gate_amplitude_eq _ _ _ hx.2

omit hloc G hh0 hh1 hb in
theorem pressure_amplitude_smooth (hn : NativeRegular sys hh f)
    (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1) :
    ContDiffOn ℝ ∞ ((pressureCopies sys hh f).amplitude k I) (liftedNativePast a b) := by
  apply (ActualSignedPhysicalData.pressure_amplitude_smooth sys hh f ha hn k I).congr
  intro x hx
  exact PositiveTimeCopyFamily.gate_amplitude_eq _ _ _ hx.2

theorem potentialSmooth (hp : NativeProfiles (h := h) f) (hn : NativeRegular sys hh f)
    (i : Fin 3) :
    LocalPhysicalCopyBounds.SmoothData (potentialCopies sys hh f i) (a / 4) h sys.radius := by
  let hr := potential_support sys hh f hloc G hh0 hh1 ha hb i
  constructor
  · intro k I w hw ht
    exact LocalPhysicalCopyBounds.SmoothNear.of_open (liftedNativePast_open a b)
      (potential_amplitude_smooth sys hh f ha hn i k I)
      (commonLift_mem_liftedNativePast ha _ hw (hr.tsupport_geometry I k ht).1)
  · intro k I w hw ht j hj
    have hc := (potentialCells sys hh f i).term_tsupport_mem
      (div_pos ha (by norm_num)) I k (hr.tsupport_geometry I k ht).1 ht
    have hl := term_tsupport_labelRegion hr hh0 hh1 I k hw ht
    have hp' := hp.covers I.1 w hw hl
      (by simpa only [potentialCopies, PositiveTimeCopyFamily.gate,
        ActualSignedPhysicalData.potentialFamily, commonLift_zero] using hc.2)
    change LocalPhysicalCopyBounds.SmoothNear (extendedCarrier (h := h) f I.1 k).F
        (LocalPhysicalCopyBounds.slotSlow ((extendedCarrier (h := h) f I.1 k).withChart j) _ _ _ _
            _) ∧
      LocalPhysicalCopyBounds.SmoothNear (extendedCarrier (h := h) f I.1 k).G
        (LocalPhysicalCopyBounds.slotSlow ((extendedCarrier (h := h) f I.1 k).withChart j) _ _ _ _
            _)
    rw [slotSlow_eq_nativeSlow (div_pos ha (by norm_num)) _ _ _ _ _ _ hj]
    exact ⟨LocalPhysicalCopyBounds.SmoothNear.of_open (hp.region_open I.1)
      (hp.jets.smooth (k, I.1)).fst hp',
      LocalPhysicalCopyBounds.SmoothNear.of_open (hp.region_open I.1)
      (hp.jets.smooth (k, I.1)).snd hp'⟩

theorem pressureSmooth (hp : NativeProfiles (h := h) f) (hn : NativeRegular sys hh f) :
    LocalPhysicalCopyBounds.SmoothData (pressureCopies sys hh f) (a / 4) h sys.radius := by
  let hr := pressure_support sys hh f hloc G hh0 hh1 ha hb
  constructor
  · intro k I w hw ht
    exact LocalPhysicalCopyBounds.SmoothNear.of_open (liftedNativePast_open a b)
      (pressure_amplitude_smooth sys hh f ha hn k I)
      (commonLift_mem_liftedNativePast ha _ hw (hr.tsupport_geometry I k ht).1)
  · intro k I w hw ht j hj
    have hc := (pressureCells sys hh f).term_tsupport_mem
      (div_pos ha (by norm_num)) I k (hr.tsupport_geometry I k ht).1 ht
    have hl := term_tsupport_labelRegion hr hh0 hh1 I k hw ht
    have hp' := hp.covers I.1 w hw hl
      (by simpa only [pressureCopies, PositiveTimeCopyFamily.gate,
        ActualSignedPhysicalData.pressureFamily, commonLift_zero] using hc.2)
    change LocalPhysicalCopyBounds.SmoothNear (extendedCarrier (h := h) f I.1 k).F
        (LocalPhysicalCopyBounds.slotSlow ((extendedCarrier (h := h) f I.1 k).withChart j) _ _ _ _
            _) ∧
      LocalPhysicalCopyBounds.SmoothNear (extendedCarrier (h := h) f I.1 k).G
        (LocalPhysicalCopyBounds.slotSlow ((extendedCarrier (h := h) f I.1 k).withChart j) _ _ _ _
            _)
    rw [slotSlow_eq_nativeSlow (div_pos ha (by norm_num)) _ _ _ _ _ _ hj]
    exact ⟨LocalPhysicalCopyBounds.SmoothNear.of_open (hp.region_open I.1)
      (hp.jets.smooth (k, I.1)).fst hp',
      LocalPhysicalCopyBounds.SmoothNear.of_open (hp.region_open I.1)
      (hp.jets.smooth (k, I.1)).snd hp'⟩

end Copies

/-! ## Source charts confined to positive time -/

/-- The chart equality is asserted only on its actual open domain.  The
source remains the original source, including its unchanged totalization. -/
noncomputable def identitySourceChart {N : ℕ} {K I : Type}
    (f : PhysicalCopyBounds.CopyFamily N K) (cells : PhysicalCopyBounds.SupportCells f)
    {a b h r Z σ : ℝ} {gap : ℕ} (ha : 0 < a)
    (hs : LocalPhysicalCopyBounds.SupportData (PositiveTimeCopyFamily.gate f)
      a b h r Z gap)
    (s : StripData LiftPoint) (source : I → ℕ → LiftPoint → ℂ)
    (idx : K → PhysicalWaveSum.WaveIndex N → I)
    (he : ∀ k J x, f.amplitude k J x =
      ChartScales.Q J.1.val.1 ^ σ • source (idx k J) J.1.val.1 x)
    (hd : ∀ k J x, x ∈ PositiveTimeCopyFamily.liftPast →
      f.amplitude k J x ≠ 0 → x ∈ s.domain) :
    LocalPhysicalCopyBounds.CommonChart (PositiveTimeCopyFamily.gate f)
      (PositiveTimeCopyFamily.gateCells cells) a b h r σ source where
  sourceIndex := idx
  map _ _ := id
  domain _ _ := s.domain ∩ PositiveTimeCopyFamily.liftPast
  open_domain _ _ := s.isOpen_domain.inter PositiveTimeCopyFamily.liftPast_open
  smooth _ _ := contDiffOn_id
  positive_jets m := by
    refine ⟨1, le_rfl, 0, ?_⟩
    intro k J x hx j hj hjm
    simp only [pow_zero, mul_one]
    exact (PhysicalGraphBounds.norm_positive_jet_linear_le
      (ContinuousLinearMap.id ℝ LiftPoint) x hj).trans (by simp)
  amplitude_eq k J x hx :=
    (PositiveTimeCopyFamily.gate_amplitude_eq f k J hx.2).trans (he k J x)
  contains k J z _ _ _ _ hz := by
    have hrad := (hs.tsupport_geometry J k hz).1
    have hm := (PhysicalWaveSum.commonLift_smoothAt h J.1.val.1 (f.gap J.1)
      (PhysicalGraphBounds.scaledRadial_ne_zero
        (PhysicalGraphBounds.annulus_axisFree ha hrad))).continuousAt
    apply hm.continuousWithinAt.mem_closure hz
    intro y hy
    have hraw := (PositiveTimeCopyFamily.gate_amplitude_ne_zero_iff f k J _).mp
      (PhysicalWaveSum.globalWave_ne_zero_amp hy)
    exact ⟨hd k J _ hraw.1 hraw.2, hraw.1⟩

section WaveData

variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h
    ActualSignedGeometry.radialVector ActualSignedGeometry.temporalVector)
  (hh : 0 ≤ h) {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (f : SignedFamily U)
  {a b : ℝ} {s : StripData Native}
  (hloc : PrimitiveLocalization (h := h) f a b s)
  (G : ReferenceGeometry sys f) (hh0 : 0 < h) (hh1 : h < 1 / 2)
  (ha : 0 < a) (hb : 0 < b)

include hloc hh0 hh1 ha hb

theorem potential_source_domain (i : Fin 3) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) (x : LiftPoint)
    (hx : x ∈ PositiveTimeCopyFamily.liftPast)
    (hne : (ActualSignedPhysicalData.potentialFamily sys hh f i).amplitude k I x ≠ 0) :
    x ∈ (CartesianCopySource.pullStrip s (a / 4) (2 * b)
      (div_pos ha (by norm_num))).domain := by
  obtain ⟨hL, _, hm, ht⟩ := potential_amplitude_inputs sys hh f i k I x hne
  have hg := primitive_annulus hloc hh0 hh1 ha hb
    ⟨I.1.val, I.1.property, hL⟩ x hx hm ht
  refine ⟨?_, primitive_domain hloc ⟨I.1.val, I.1.property, hL⟩ x hx hm ht⟩
  have hu : ‖PhysicalGraphBounds.liftXY x‖ ≤ 2 * b := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hg.1.1
  have hl : a / 4 ≤ ‖PhysicalGraphBounds.liftXY x‖ := hg.1.2
  exact ⟨by change a / 4 / 2 < _; linarith, by change _ < 2 * b + 1; linarith⟩

theorem pressure_source_domain (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1)
    (x : LiftPoint) (hx : x ∈ PositiveTimeCopyFamily.liftPast)
    (hne : (ActualSignedPhysicalData.pressureFamily sys hh f).amplitude k I x ≠ 0) :
    x ∈ (CartesianCopySource.pullStrip s (a / 4) (2 * b)
      (div_pos ha (by norm_num))).domain := by
  obtain ⟨hL, _, hm, ht⟩ := pressure_amplitude_inputs sys hh f k I x hne
  have hg := primitive_annulus hloc hh0 hh1 ha hb
    ⟨I.1.val, I.1.property, hL⟩ x hx hm ht
  refine ⟨?_, primitive_domain hloc ⟨I.1.val, I.1.property, hL⟩ x hx hm ht⟩
  have hu : ‖PhysicalGraphBounds.liftXY x‖ ≤ 2 * b := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hg.1.1
  have hl : a / 4 ≤ ‖PhysicalGraphBounds.liftXY x‖ := hg.1.2
  exact ⟨by change a / 4 / 2 < _; linarith, by change _ < 2 * b + 1; linarith⟩

variable (hp : NativeProfiles (h := h) f) (hn : NativeRegular sys hh f)
  {P : ℝ} (hP : 1 ≤ P)
  (hf : ∀ L : NativeLabel f.active,
    |((f.primary L).pulse (f.column L)).phase.p L.val.1| ≤ P ∧
    |((f.primary L).pulse (f.column L)).phase.pz L.val.1| ≤ P ∧
    |((f.primary L).pulse (f.column L)).phase.x0 L.val.1| ≤ P)
  {α : ℝ} {w : SourceIndex → ℕ → Native → ℝ}

/-- A physical potential datum using the original source bounds and the
proved positive-time support.  No off-past localization is required. -/
noncomputable def potentialWaveData
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds s h α w
      (nativePotentialSource sys hh f)) :
    PhysicalStageBounds.WaveData h LiftPoint (Fin 3 × SourceIndex) Frequency (Fin 3) where
  lowerRadius := a / 4
  upperRadius := 2 * b
  nativeWidth := sys.radius
  slowBound := 2
  frequencyBound := P
  alpha := α
  shift := -h
  harmonics := 1
  gapBound := 0
  lower_pos := div_pos ha (by norm_num)
  width_nonneg := sys.radius_pos.le
  slow_nonneg := by norm_num
  frequency_one_le := hP
  strip := CartesianCopySource.pullStrip s (a / 4) (2 * b) (div_pos ha (by norm_num))
  weight I n x := w I.2 n (PhysicalClassBounds.cylindricalMap x)
  source I n x := CartesianCopySource.rotatedSource (nativePotentialSource sys hh f) I.2 n x I.1
  source_bounds := componentSourceBounds (CartesianCopySource.sourceBounds_rotated
    (b := 2 * b) (div_pos ha (by norm_num)) hs)
  copies := potentialCopies sys hh f
  cells := potentialCells sys hh f
  chart i := identitySourceChart _ _ (div_pos ha (by norm_num))
    (potential_support sys hh f hloc G hh0 hh1 ha hb i) _ _ (fun k I => (i, I, k))
    (potential_amplitude_eq_source sys hh f i)
    (potential_source_domain sys hh f hloc hh0 hh1 ha hb i)
  chart_maps _ _ _ := fun _ hx => hx.1
  carrier := potentialCarrier sys hh f ha hp
  support := potential_support sys hh f hloc G hh0 hh1 ha hb
  smooth := potentialSmooth sys hh f hloc G hh0 hh1 ha hb hp hn
  frequencies _ := carrier_frequencies f hP hf

/-- Pressure wave data, bundling `lowerRadius`, `upperRadius`, `nativeWidth`, `slowBound` and
the required compatibility proofs. -/
noncomputable def pressureWaveData
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds s h α w
      (nativePressureSource sys hh f)) :
    PhysicalStageBounds.WaveData h LiftPoint SourceIndex Frequency Unit where
  lowerRadius := a / 4
  upperRadius := 2 * b
  nativeWidth := sys.radius
  slowBound := 2
  frequencyBound := P
  alpha := α
  shift := -(2 * CoordinateAlgebra.A h)
  harmonics := 1
  gapBound := 0
  lower_pos := div_pos ha (by norm_num)
  width_nonneg := sys.radius_pos.le
  slow_nonneg := by norm_num
  frequency_one_le := hP
  strip := CartesianCopySource.pullStrip s (a / 4) (2 * b) (div_pos ha (by norm_num))
  weight I n x := w I n (PhysicalClassBounds.cylindricalMap x)
  source I n x := nativePressureSource sys hh f I n (PhysicalClassBounds.cylindricalMap x)
  source_bounds := CartesianCopySource.sourceBounds_pullback
    (b := 2 * b) (div_pos ha (by norm_num)) hs
  copies _ := pressureCopies sys hh f
  cells _ := pressureCells sys hh f
  chart _ := identitySourceChart _ _ (div_pos ha (by norm_num))
    (pressure_support sys hh f hloc G hh0 hh1 ha hb) _ _ (fun k I => (I, k))
    (pressure_amplitude_eq_source sys hh f)
    (pressure_source_domain sys hh f hloc hh0 hh1 ha hb)
  chart_maps _ _ _ := fun _ hx => hx.1
  carrier _ := pressureCarrier sys hh f ha hp
  support _ := pressure_support sys hh f hloc G hh0 hh1 ha hb
  smooth _ := pressureSmooth sys hh f hloc G hh0 hh1 ha hb hp hn
  frequencies _ := carrier_frequencies f hP hf

variable
  (hpotential : LocalPhysicalCopyBounds.LocalSourceBounds s h α w
    (nativePotentialSource sys hh f))
  (hpressure : LocalPhysicalCopyBounds.LocalSourceBounds s h α w
    (nativePressureSource sys hh f))

/-- Every preterminal potential germ is the germ of the original physical
copy sum, including all spatial and time derivatives. -/
theorem potentialWaveData_vector_germ {x : SpaceTime}
    (hx : x ∈ PhysicalWaveSum.preterminal) :
    (potentialWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpotential).vector
      =ᶠ[𝓝 x] PhysicalCopyBounds.vectorSum
        (ActualSignedPhysicalData.potentialFamily sys hh f) (a / 4) h sys.radius :=
  PositiveTimeCopyFamily.vectorSum_germ
    (ActualSignedPhysicalData.potentialFamily sys hh f) (a / 4) h sys.radius hx

theorem pressureWaveData_pressure_germ {x : SpaceTime}
    (hx : x ∈ PhysicalWaveSum.preterminal) :
    (pressureWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpressure).pressure
      =ᶠ[𝓝 x] fun y =>
        ((ActualSignedPhysicalData.pressureFamily sys hh f).sum (a / 4) h sys.radius y).re := by
  filter_upwards [PositiveTimeCopyFamily.sum_germ
    (ActualSignedPhysicalData.pressureFamily sys hh f) (a / 4) h sys.radius hx] with y hy
  exact congrArg Complex.re hy

include G hp hn hP hf hpotential in
/-- The physical estimate applies to the original preterminal potential,
not just to its chosen positive-time representative. -/
theorem potential_physical_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h x ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (PhysicalCopyBounds.vectorSum (ActualSignedPhysicalData.potentialFamily sys hh f)
          (a / 4) h sys.radius) x‖ ≤
        C * PhysicalWaveSum.physicalQ h x ^
          (h * α - PhysicalClassBounds.physicalLoss h (-h) m) := by
  obtain ⟨C, hC, hbound⟩ :=
    (potentialWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpotential).vector_bound
      hh0 hh1 m
  refine ⟨C, hC, fun x hx hq => ?_⟩
  rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
    (potentialWaveData_vector_germ sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpotential hx) m]
  exact hbound x hx hq

include G hp hn hP hf hpressure in
theorem pressure_physical_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h x ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (fun y => ((ActualSignedPhysicalData.pressureFamily sys hh f).sum
          (a / 4) h sys.radius y).re) x‖ ≤
        C * PhysicalWaveSum.physicalQ h x ^
          (h * α - PhysicalClassBounds.physicalLoss h (-(2 * CoordinateAlgebra.A h)) m) := by
  obtain ⟨C, hC, hbound⟩ :=
    (pressureWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpressure).pressure_bound
      hh0 hh1 m
  refine ⟨C, hC, fun x hx hq => ?_⟩
  rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
    (pressureWaveData_pressure_germ sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpressure hx) m]
  exact hbound x hx hq

end WaveData

/-! ## The actual dependent signed family -/

section Actual

open CorrectionInitialization

variable {B N0 : ℕ}
  (s : ∀ l : ActualSignedPhysicalBinding.Label B N0,
    (ActualSignedPhysicalBinding.nativeViews l).StateData)

/-- Every actual singleton supplies the positive-time primitive data.
Neither its current request nor any output support property is assumed. -/
theorem singletonLocalization
    (L : NativeLabel (ActualSignedExterior.family s).active) :
    PrimitiveLocalization (h := ActualPrimary.h)
      ((ActualSignedExterior.family s).singleton L)
      (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
      ActualPrimaryBounds.strip where
  normalized K y hy _ hm ht := by
    have hK := (ActualSignedExterior.family s).singleton_label_val L K
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).mask
      K.val.1 (nativeCylinder y) ≠ 0 at hm
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).target
      K.val.1 (nativeCylinder y) ≠ 0 at ht
    rw [hK, ← ActualSignedExterior.actualLabel_reference L] at hm ht
    exact PositiveTimeSignedLocalization.normalized_bounds
      (ActualSignedExterior.actualLabel L) y hy hm ht
  domain K y hy _ hm ht := by
    have hK := (ActualSignedExterior.family s).singleton_label_val L K
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).mask
      K.val.1 (nativeCylinder y) ≠ 0 at hm
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).target
      K.val.1 (nativeCylinder y) ≠ 0 at ht
    rw [hK, ← ActualSignedExterior.actualLabel_reference L] at hm ht
    exact PositiveTimeSignedLocalization.native_mem_strip
      (ActualSignedExterior.actualLabel L) y hy hm ht
  mask_pullback K x hx := by
    have hK := (ActualSignedExterior.family s).singleton_label_val L K
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).mask
      K.val.1 (cylinderZero (PhysicalGraphBounds.physicalLift ActualPrimary.h K.val.1 x)) = _
    rw [hK]
    have he := PositiveTimeSignedLocalization.mask_pullback
      (ActualSignedExterior.actualLabel L) x hx
    rw [ActualSignedExterior.actualLabel_reference L] at he
    have hl : ActualSignedPhysicalBinding.spatialLabel (ActualSignedExterior.actualLabel L) = L.val
        :=
      congrArg Subtype.val (ActualSignedExterior.bandLabel_actualLabel L)
    simpa only [hl] using he

end Actual

end NavierStokes.PositiveTimeSignedData

end
end

end

section

/-!
# The actual signed carrier profiles on their Prepared regions

The family keeps each label's genuine Prepared phase domain.  The closed
one-mesh mask support lies strictly inside the open two-mesh domain at
positive time.  This proves the physical closure-coverage condition without
extending the profile functions across a native domain boundary.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedNativeProfiles

open Set Function Filter WeightedClasses PhaseJetBounds
open CorrectionInitialization PhysicalWaveSum
open scoped ContDiff Topology

/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label`. -/
abbrev Label := ActualSignedPhysicalBinding.Label
/-- Native label: an abbreviation for `ActualSignedPhysicalData.NativeLabel
(ActualSignedExterior.labels B N0)`. -/
abbrev NativeLabel (B N0 : ℕ) :=
  ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.labels B N0)
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow
/-- Frequency: an abbreviation for `TorusInverse.Frequency`. -/
abbrev Frequency := TorusInverse.Frequency
/-- Lift point: an abbreviation for `PhysicalGraphBounds.LiftPoint`. -/
abbrev LiftPoint := PhysicalGraphBounds.LiftPoint

variable {B N0 : ℕ}

/-- No Prepared data is chosen for omitted physical labels. -/
noncomputable def region (B N0 : ℕ) (L : BandLabel) : Set Slow := by
  classical
  exact if hL : L ∈ ActualSignedExterior.labels B N0 then
    (ActualSignedPhysicalBinding.domain
      (ActualSignedExterior.actualLabel ⟨L.val,L.property,hL⟩)).carrier 0
  else ∅

theorem region_open (B N0 : ℕ) (L : BandLabel) : IsOpen (region B N0 L) := by
  classical
  unfold region
  split_ifs
  · exact (ActualSignedPhysicalBinding.domain _).isOpen _
  · exact isOpen_empty

theorem region_active (L : NativeLabel B N0) :
    region B N0 L = (ActualSignedPhysicalBinding.domain
      (ActualSignedExterior.actualLabel L)).carrier 0 := by
  classical
  simp only [region, dite_eq_left L.mem]

/-- Profile pair as an element of `ℝ × ℝ`. -/
noncomputable def profilePair (B : ℕ) (n : ℕ) (p : Slow) : ℝ × ℝ :=
  (PrimaryGeometryAssembly.frequency ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B n p,
    PrimaryGeometryAssembly.axial ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B n p)

/-- Profile domain, given by `PhysicalCopyBounds.copyBandDomain (fun (_ : Frequency) L => region
B N0 L) (fun _ L => region_open B N0 L)`. -/
noncomputable def profileDomain (B N0 : ℕ) : Domain (Frequency × BandLabel) Slow :=
  PhysicalCopyBounds.copyBandDomain (fun (_ : Frequency) L => region B N0 L)
    (fun _ L => region_open B N0 L)

/-- The constants come from the original joint Prepared family before
selecting a physical label or a lattice copy. -/
theorem profile_jets : PolynomialJets (profileDomain B N0)
    (fun I p => profilePair B I.2.val.1 p) := by
  classical
  have hfg := (ActualPrimary.choice B N0).prepared.frequency_jets.pair
    (ActualPrimary.choice B N0).prepared.axial_jets
  constructor
  · intro I
    by_cases hI : I.2 ∈ ActualSignedExterior.labels B N0
    · let L : NativeLabel B N0 := ⟨I.2.val,I.2.property,hI⟩
      have hb := ActualSignedExterior.actualLabel_reference L
      change BaseChartJets.cellBand (ActualSignedExterior.actualLabel L).1 = I.2.val.1 at hb
      have hs := hfg.smooth (ActualSignedExterior.actualLabel L).1
      simpa only [profileDomain, PhysicalCopyBounds.copyBandDomain, region, dite_eq_left hI,
        ActualSignedPhysicalBinding.domain, ActualParticularStageControls.reindexDomain,
        profilePair, hb, L] using hs
    · intro p hp
      have hempty : p ∈ (∅ : Set Slow) := by
        simpa only [profileDomain, PhysicalCopyBounds.copyBandDomain, region, dite_eq_right hI]
            using hp
      exact hempty.elim
  · intro N
    obtain ⟨C,hC,m,hm⟩ := hfg.bound N
    refine ⟨C,hC,m,?_⟩
    intro I j hj p hp
    by_cases hI : I.2 ∈ ActualSignedExterior.labels B N0
    · let L : NativeLabel B N0 := ⟨I.2.val,I.2.property,hI⟩
      have hb := ActualSignedExterior.actualLabel_reference L
      change BaseChartJets.cellBand (ActualSignedExterior.actualLabel L).1 = I.2.val.1 at hb
      have hp' : p ∈ (PrimaryGeometryAssembly.domain ActualPrimary.nominal
          (ActualPrimary.choice B N0).prepared.N).carrier (ActualSignedExterior.actualLabel L).1 :=
              by
        simpa only [profileDomain, PhysicalCopyBounds.copyBandDomain, region, dite_eq_left hI,
          ActualSignedPhysicalBinding.domain, ActualParticularStageControls.reindexDomain, L] using
              hp
      have hbound := hm (ActualSignedExterior.actualLabel L).1 j hj p hp'
      simpa only [profileDomain, PhysicalCopyBounds.copyBandDomain, profilePair,
        PrimaryGeometryAssembly.domain, PrimaryGeometryAssembly.cellDomain, hb] using hbound
    · simp only [profileDomain, PhysicalCopyBounds.copyBandDomain, region, dite_eq_right hI] at hp
      exact hp.elim

/-- Lifted slow, given by `(PolarCharts.radius (PhysicalGraphBounds.liftXY x),
PhysicalGraphBounds.liftZT x)`. -/
noncomputable def liftedSlow (x : LiftPoint) : Slow :=
  (PolarCharts.radius (PhysicalGraphBounds.liftXY x), PhysicalGraphBounds.liftZT x)

theorem liftedSlow_continuous : Continuous liftedSlow :=
  (PolarCharts.radius_continuous.comp PhysicalGraphBounds.liftXY.continuous).prodMk
    PhysicalGraphBounds.liftZT.continuous

theorem liftedSlow_physical (n : ℕ) (w : ProblemStatement.SpaceTime) :
    liftedSlow (PhysicalGraphBounds.physicalLift ActualPrimary.h n w) =
      ActualSignedPhysicalData.nativeSlow (PhysicalMeanJetBounds.graph ActualPrimary.h n 0 w) :=
  ActualSignedExterior.physicalLift_slow n w

variable (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)

theorem singleton_profiles (L : NativeLabel B N0) (K : BandLabel) (k : Frequency) (p : Slow) :
    ((ActualSignedPhysicalData.extendedCarrier (h := ActualPrimary.h)
        ((ActualSignedExterior.family s).singleton L) K k).F p,
      (ActualSignedPhysicalData.extendedCarrier (h := ActualPrimary.h)
        ((ActualSignedExterior.family s).singleton L) K k).G p) =
      if K = (L : BandLabel) then profilePair B K.val.1 p else 0 := by
  classical
  by_cases he : K = (L : BandLabel)
  · subst K
    have hm : (L : BandLabel) ∈ ((ActualSignedExterior.family s).singleton L).active :=
        Set.mem_singleton _
    simp only [ite_true, ActualSignedPhysicalData.extendedCarrier, dite_eq_left hm]
    have hb := ActualSignedExterior.actualLabel_reference L
    change BaseChartJets.cellBand (ActualSignedExterior.actualLabel L).1 = L.val.1 at hb
    change profilePair B (BaseChartJets.cellBand (ActualSignedExterior.actualLabel L).1) p =
      profilePair B L.val.1 p
    rw [hb]
  · have hm : K ∉ ((ActualSignedExterior.family s).singleton L).active := by
      change K ∉ {(L : BandLabel)}
      simpa only [Set.mem_singleton_iff] using he
    simp only [ite_eq_right he, ActualSignedPhysicalData.extendedCarrier, dite_eq_right hm,
      ActualSignedPhysicalData.carrier, Prod.zero_eq_mk]

/-- A single active branch uses the common joint constants; omitted
branches have identically zero carrier profiles. -/
theorem singleton_jets (L : NativeLabel B N0) :
    PolynomialJets (profileDomain B N0) (fun I p =>
      ((ActualSignedPhysicalData.extendedCarrier (h := ActualPrimary.h)
          ((ActualSignedExterior.family s).singleton L) I.2 I.1).F p,
        (ActualSignedPhysicalData.extendedCarrier (h := ActualPrimary.h)
          ((ActualSignedExterior.family s).singleton L) I.2 I.1).G p)) := by
  classical
  have he : (fun I p =>
      ((ActualSignedPhysicalData.extendedCarrier (h := ActualPrimary.h)
          ((ActualSignedExterior.family s).singleton L) I.2 I.1).F p,
        (ActualSignedPhysicalData.extendedCarrier (h := ActualPrimary.h)
          ((ActualSignedExterior.family s).singleton L) I.2 I.1).G p)) =
      (fun (I : Frequency × BandLabel) p => if I.2 = (L : BandLabel) then profilePair B I.2.val.1 p
          else 0) := by
    funext I p
    exact singleton_profiles s L I.2 I.1 p
  rw [he]
  constructor
  · intro I
    by_cases hI : I.2 = (L : BandLabel)
    · simpa only [hI, ite_true] using (profile_jets (B := B) (N0 := N0)).smooth I
    · simpa only [ite_eq_right hI] using (contDiffOn_const :
        ContDiffOn ℝ ∞ (fun _ : Slow => (0 : ℝ × ℝ)) ((profileDomain B N0).carrier I))
  · intro N
    obtain ⟨C,hC,m,hm⟩ := (profile_jets (B := B) (N0 := N0)).bound N
    refine ⟨C,hC,m,?_⟩
    intro I j hj p hp
    by_cases hI : I.2 = (L : BandLabel)
    · simpa only [ite_eq_left hI] using hm I j hj p hp
    · simp only [ite_eq_right hI, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (zero_le_one.trans hC)
        (pow_nonneg (zero_le_one.trans ((profileDomain B N0).one_le_scale I)) m)

theorem core_empty (L : NativeLabel B N0) {K : BandLabel} (hne : K ≠ (L : BandLabel)) :
    ActualSignedPhysicalData.primitiveCore ((ActualSignedExterior.family s).singleton L) K = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hK,_,_⟩
  exact hne (Set.mem_singleton_iff.mp hK)

theorem core_in_mask_support (L : NativeLabel B N0) :
    ActualSignedPhysicalData.primitiveCore ((ActualSignedExterior.family s).singleton L) L ⊆
      liftedSlow ⁻¹' tsupport (PrimaryRepresentatives.nativeMask
        (BaseChartJets.cellBand (ActualSignedExterior.actualLabel L).1)
        (PrimaryGeometryAssembly.label ActualPrimary.nominal (ActualSignedExterior.actualLabel
            L).1).2) := by
  rintro x ⟨hL,hm,_⟩
  exact ActualPrimary.spatialMask_native_support (ActualSignedExterior.actualLabel L).1 (liftedSlow
      x) hm

theorem closure_covers (L : NativeLabel B N0) (K : BandLabel) (w : ProblemStatement.SpaceTime)
    (hw : w ∈ preterminal)
    (hc : PhysicalGraphBounds.physicalLift ActualPrimary.h K.val.1 w ∈
      closure (ActualSignedPhysicalData.primitiveCore ((ActualSignedExterior.family s).singleton L)
          K)) :
    ActualSignedPhysicalData.nativeSlow (PhysicalMeanJetBounds.graph ActualPrimary.h K.val.1 0 w) ∈
      region B N0 K := by
  classical
  by_cases he : K = (L : BandLabel)
  · subst K
    rw [region_active L]
    have hclosure := closure_minimal (core_in_mask_support s L)
      ((isClosed_tsupport _).preimage liftedSlow_continuous)
    have hmask := hclosure hc
    rw [mem_preimage, liftedSlow_physical] at hmask
    exact PrimaryGeometryAssembly.native_support_in_carrier ActualPrimary.nominal
      (ActualSignedExterior.actualLabel L).1
      ⟨hmask, PhysicalMeanJetBounds.graph_time_pos ActualPrimary.h L.val.1 0 hw⟩
  · rw [core_empty s L he, closure_empty] at hc
    exact hc.elim

/-- The actual homogeneous singleton interface needed by the physical
factory, with no extension or output-bound assumptions. -/
noncomputable def nativeProfiles (L : NativeLabel B N0) :
    ActualSignedPhysicalData.NativeProfiles (h := ActualPrimary.h)
      ((ActualSignedExterior.family s).singleton L) where
  region := region B N0
  region_open := region_open B N0
  jets := singleton_jets s L
  covers K w hw _ hc := closure_covers s L K w hw hc

/-- The actual assembled potential carrier retains the joint Prepared
bound, including the copy index and every physical label. -/
theorem potential_profiles_jets (i : Fin 3) :
    PolynomialJets (profileDomain B N0) (fun I p =>
      ((((ActualSignedExterior.family s).potentialCopies ActualPrimary.slots
          ActualPrimary.outgoing.data.h_pos.le i).carrier I.1 I.2).F p,
        (((ActualSignedExterior.family s).potentialCopies ActualPrimary.slots
          ActualPrimary.outgoing.data.h_pos.le i).carrier I.1 I.2).G p)) := by
  classical
  apply (profile_jets (B := B) (N0 := N0)).congr
  intro I p hp
  by_cases hI : I.2 ∈ ActualSignedExterior.labels B N0
  · have hactive : I.2 ∈ (ActualSignedExterior.family s).active := hI
    have he := singleton_profiles s ⟨I.2.val,I.2.property,hI⟩ I.2 I.1 p
    simp only [ite_true] at he
    simp only [DependentSignedPhysicalFamily.Family.potentialCopies,
      DependentSignedPhysicalFamily.Family.assembled, DependentSignedPhysicalFamily.diagonal,
      DependentSignedPhysicalFamily.Family.copyAt, dite_eq_left hactive,
      ActualSignedPhysicalData.potentialFamily]
    exact he.symm
  · have hempty : p ∈ (∅ : Set Slow) := by
      simpa only [profileDomain, PhysicalCopyBounds.copyBandDomain, region, dite_eq_right hI] using
          hp
    exact hempty.elim

theorem pressure_profiles_jets :
    PolynomialJets (profileDomain B N0) (fun I p =>
      ((((ActualSignedExterior.family s).pressureCopies ActualPrimary.slots
          ActualPrimary.outgoing.data.h_pos.le).carrier I.1 I.2).F p,
        (((ActualSignedExterior.family s).pressureCopies ActualPrimary.slots
          ActualPrimary.outgoing.data.h_pos.le).carrier I.1 I.2).G p)) := by
  classical
  apply (profile_jets (B := B) (N0 := N0)).congr
  intro I p hp
  by_cases hI : I.2 ∈ ActualSignedExterior.labels B N0
  · have hactive : I.2 ∈ (ActualSignedExterior.family s).active := hI
    have he := singleton_profiles s ⟨I.2.val,I.2.property,hI⟩ I.2 I.1 p
    simp only [ite_true] at he
    simp only [DependentSignedPhysicalFamily.Family.pressureCopies,
      DependentSignedPhysicalFamily.Family.assembled, DependentSignedPhysicalFamily.diagonal,
      DependentSignedPhysicalFamily.Family.copyAt, dite_eq_left hactive,
      ActualSignedPhysicalData.pressureFamily]
    exact he.symm
  · have hempty : p ∈ (∅ : Set Slow) := by
      simpa only [profileDomain, PhysicalCopyBounds.copyBandDomain, region, dite_eq_right hI] using
          hp
    exact hempty.elim

end NavierStokes.ActualSignedNativeProfiles

end
end

end

section

/-!
# Support and local smoothness of the actual signed copy family

The aggregate retains the original singleton at each active label and is
zero at omitted labels.  Positive lift-time gating commutes with this
assembly.  The source-domain statements concern the original, ungated
amplitudes on positive lift time.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedFamilySupport

open Set Function Filter ProblemStatement CorrectionInitialization
open CorrectionInitialization.ActualPrimary PhysicalWaveSum PhysicalCopyBounds
open scoped Topology ContDiff

private theorem gate_zeroCopies {H : ℕ} {K : Type*} :
    PositiveTimeCopyFamily.gate
      (DependentSignedPhysicalFamily.zeroCopies : CopyFamily H K) =
        DependentSignedPhysicalFamily.zeroCopies := by
  simp only [PositiveTimeCopyFamily.gate, DependentSignedPhysicalFamily.zeroCopies, ite_self]

private theorem gate_copyAt {H : ℕ} {K : Type*}
    (f : DependentSignedPhysicalFamily.Family)
    (copies : ActualSignedPhysicalData.NativeLabel f.active → CopyFamily H K)
    (L : BandLabel) :
    PositiveTimeCopyFamily.gate (f.copyAt copies L) =
      f.copyAt (fun l => PositiveTimeCopyFamily.gate (copies l)) L := by
  classical
  by_cases hL : L ∈ f.active
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_left hL]
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_right hL, gate_zeroCopies]

private theorem gate_diagonal {H : ℕ} {K : Type*}
    (f : BandLabel → CopyFamily H K) :
    PositiveTimeCopyFamily.gate (DependentSignedPhysicalFamily.diagonal f) =
      DependentSignedPhysicalFamily.diagonal
        (fun L => PositiveTimeCopyFamily.gate (f L)) := rfl

private theorem gate_assembled {H : ℕ} {K : Type*}
    (f : DependentSignedPhysicalFamily.Family)
    (copies : ActualSignedPhysicalData.NativeLabel f.active → CopyFamily H K) :
    PositiveTimeCopyFamily.gate (f.assembled copies) =
      f.assembled (fun L => PositiveTimeCopyFamily.gate (copies L)) := by
  unfold DependentSignedPhysicalFamily.Family.assembled
  rw [gate_diagonal]
  congr 1
  funext L
  exact gate_copyAt f copies L

private theorem gated_assembled_support {H : ℕ} {K : Type*}
    (f : DependentSignedPhysicalFamily.Family)
    (copies : ActualSignedPhysicalData.NativeLabel f.active → CopyFamily H K)
    {a b h r Z : ℝ} {gap : ℕ}
    (hs : ∀ L, LocalPhysicalCopyBounds.SupportData
      (PositiveTimeCopyFamily.gate (copies L)) a b h r Z gap) :
    LocalPhysicalCopyBounds.SupportData
      (PositiveTimeCopyFamily.gate (f.assembled copies)) a b h r Z gap := by
  rw [gate_assembled]
  exact DependentSignedPhysicalFamily.diagonalSupport _ (f.branchSupport _ hs)

private theorem gated_assembled_smooth {H : ℕ} {K : Type*}
    (f : DependentSignedPhysicalFamily.Family)
    (copies : ActualSignedPhysicalData.NativeLabel f.active → CopyFamily H K)
    {a h r : ℝ}
    (hs : ∀ L, LocalPhysicalCopyBounds.SmoothData
      (PositiveTimeCopyFamily.gate (copies L)) a h r) :
    LocalPhysicalCopyBounds.SmoothData
      (PositiveTimeCopyFamily.gate (f.assembled copies)) a h r := by
  rw [gate_assembled]
  exact DependentSignedPhysicalFamily.diagonalSmooth _ (f.branchSmooth _ hs)

/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label`. -/
abbrev Label := ActualSignedPhysicalBinding.Label

variable {B N0 : ℕ}
  (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)

/-- The actual aggregate potential copies, with the sole positive-time gate. -/
noncomputable def potentialCopies (i : Fin 3) : CopyFamily 1 TorusInverse.Frequency :=
  PositiveTimeCopyFamily.gate
    ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i)

/-- The actual aggregate pressure copies, with the same gate. -/
noncomputable def pressureCopies : CopyFamily 1 TorusInverse.Frequency :=
  PositiveTimeCopyFamily.gate
    ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le)

variable
  (hgeo : ∀ L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active,
    ActualSignedPhysicalData.ReferenceGeometry slots ((ActualSignedExterior.family s).singleton L))

include hgeo

/-- Global support of the aggregate follows from the primitive masks and
targets of its selected singletons. -/
theorem potential_support (i : Fin 3) :
    LocalPhysicalCopyBounds.SupportData (potentialCopies s i)
      ActualPolarCoverage.inner ActualPolarCoverage.outer h slots.radius 2 0 := by
  apply gated_assembled_support
  intro L
  exact PositiveTimeSignedData.potential_support slots outgoing.data.h_pos.le
    ((ActualSignedExterior.family s).singleton L)
    (PositiveTimeSignedData.singletonLocalization s L) (hgeo L)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (PrimaryTargetBounds.rightRadius_pos nominal) i

theorem pressure_support :
    LocalPhysicalCopyBounds.SupportData (pressureCopies s)
      ActualPolarCoverage.inner ActualPolarCoverage.outer h slots.radius 2 0 := by
  apply gated_assembled_support
  intro L
  exact PositiveTimeSignedData.pressure_support slots outgoing.data.h_pos.le
    ((ActualSignedExterior.family s).singleton L)
    (PositiveTimeSignedData.singletonLocalization s L) (hgeo L)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (PrimaryTargetBounds.rightRadius_pos nominal)

variable
  (hn : ∀ L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active,
    ActualSignedPhysicalData.NativeRegular slots outgoing.data.h_pos.le
      ((ActualSignedExterior.family s).singleton L))

include hn

/-- Only the native regularity near actual copy support is used. -/
theorem potential_smooth (i : Fin 3) :
    LocalPhysicalCopyBounds.SmoothData (potentialCopies s i)
      ActualPolarCoverage.inner h slots.radius := by
  apply gated_assembled_smooth
  intro L
  exact PositiveTimeSignedData.potentialSmooth slots outgoing.data.h_pos.le
    ((ActualSignedExterior.family s).singleton L)
    (PositiveTimeSignedData.singletonLocalization s L) (hgeo L)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (PrimaryTargetBounds.rightRadius_pos nominal)
    (ActualSignedNativeProfiles.nativeProfiles s L) (hn L) i

theorem pressure_smooth :
    LocalPhysicalCopyBounds.SmoothData (pressureCopies s)
      ActualPolarCoverage.inner h slots.radius := by
  apply gated_assembled_smooth
  intro L
  exact PositiveTimeSignedData.pressureSmooth slots outgoing.data.h_pos.le
    ((ActualSignedExterior.family s).singleton L)
    (PositiveTimeSignedData.singletonLocalization s L) (hgeo L)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (PrimaryTargetBounds.rightRadius_pos nominal)
    (ActualSignedNativeProfiles.nativeProfiles s L) (hn L)

omit hgeo hn

/-- A nonzero original potential amplitude at positive lift time lies in
the actual source strip. No geometry or output estimate is assumed. -/
theorem potential_source_domain (i : Fin 3) (k : TorusInverse.Frequency)
    (I : WaveIndex 1) (x : PhysicalGraphBounds.LiftPoint)
    (hx : x ∈ PositiveTimeCopyFamily.liftPast)
    (hne : ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le
        i).amplitude
      k I x ≠ 0) :
    x ∈ (CartesianCopySource.pullStrip ActualPrimaryBounds.strip
      ActualPolarCoverage.inner ActualPolarCoverage.outer ActualPolarCoverage.inner_pos).domain :=
          by
  classical
  change ((ActualSignedExterior.family s).copyAt
    (fun L => ActualSignedPhysicalData.potentialFamily slots outgoing.data.h_pos.le
      ((ActualSignedExterior.family s).singleton L) i) I.1).amplitude k I x ≠ 0 at hne
  by_cases hI : I.1 ∈ (ActualSignedExterior.family s).active
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_left hI] at hne
    exact PositiveTimeSignedData.potential_source_domain slots outgoing.data.h_pos.le
      ((ActualSignedExterior.family s).singleton ⟨I.1.val, I.1.property, hI⟩)
      (PositiveTimeSignedData.singletonLocalization s ⟨I.1.val, I.1.property, hI⟩)
      outgoing.data.h_pos outgoing.data.h_lt_half
      (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.rightRadius_pos nominal) i k I x hx hne
  · exact (hne (by simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_right hI,
      DependentSignedPhysicalFamily.zeroCopies])).elim

theorem pressure_source_domain (k : TorusInverse.Frequency)
    (I : WaveIndex 1) (x : PhysicalGraphBounds.LiftPoint)
    (hx : x ∈ PositiveTimeCopyFamily.liftPast)
    (hne : ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le).amplitude
      k I x ≠ 0) :
    x ∈ (CartesianCopySource.pullStrip ActualPrimaryBounds.strip
      ActualPolarCoverage.inner ActualPolarCoverage.outer ActualPolarCoverage.inner_pos).domain :=
          by
  classical
  change ((ActualSignedExterior.family s).copyAt
    (fun L => ActualSignedPhysicalData.pressureFamily slots outgoing.data.h_pos.le
      ((ActualSignedExterior.family s).singleton L)) I.1).amplitude k I x ≠ 0 at hne
  by_cases hI : I.1 ∈ (ActualSignedExterior.family s).active
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_left hI] at hne
    exact PositiveTimeSignedData.pressure_source_domain slots outgoing.data.h_pos.le
      ((ActualSignedExterior.family s).singleton ⟨I.1.val, I.1.property, hI⟩)
      (PositiveTimeSignedData.singletonLocalization s ⟨I.1.val, I.1.property, hI⟩)
      outgoing.data.h_pos outgoing.data.h_lt_half
      (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.rightRadius_pos nominal) k I x hx hne
  · exact (hne (by simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_right hI,
      DependentSignedPhysicalFamily.zeroCopies])).elim

end NavierStokes.ActualSignedFamilySupport

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedWaveData

open Set Function Filter ProblemStatement CorrectionState CorrectionStep
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open PhysicalWaveSum PhysicalCopyBounds
open scoped Topology ContDiff BigOperators

/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label`. -/
abbrev Label := ActualSignedPhysicalBinding.Label
/-- Native: an abbreviation for `ActualSignedPhysicalData.Native`. -/
abbrev Native := ActualSignedPhysicalData.Native
/-- Source index: an abbreviation for `Σ (_ : BandLabel), ActualSignedPhysicalData.SourceIndex`. -/
abbrev SourceIndex := Σ (_ : BandLabel), ActualSignedPhysicalData.SourceIndex

variable {B N0 : ℕ}

/-- Native states, given by `ActualSignedPhysicalBinding.nativeStateData l P u H hp`. -/
noncomputable def nativeStates (P : SignedStressPrimitive.Patch) (u : State
    LocalSignedRequest.Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)
    (l : Label B N0) : (ActualSignedPhysicalBinding.nativeViews l).StateData :=
  ActualSignedPhysicalBinding.nativeStateData l P u H hp

/-- Family, given by `ActualSignedExterior.family (nativeStates (N0 := N0) P u H hp)`. -/
noncomputable def family (P : SignedStressPrimitive.Patch) (u : State LocalSignedRequest.Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure) :
    DependentSignedPhysicalFamily.Family :=
  ActualSignedExterior.family (nativeStates (N0 := N0) P u H hp)

section Geometry

variable (P : SignedStressPrimitive.Patch) (u : State LocalSignedRequest.Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)

/-- The physical geometry is derived from the same actual primary, views,
and current-state request; no representation assertion is assumed. -/
noncomputable def singletonGeometry
    (L : ActualSignedPhysicalData.NativeLabel (family (N0 := N0) P u H hp).active) :
    ActualSignedPhysicalData.ReferenceGeometry slots ((family P u H hp).singleton L) :=
  ActualSignedReferenceGeometry.singletonGeometry P u H hp L

/-- One actual bound works for every native label and both signs. -/
theorem singleton_frequencies
    (L : ActualSignedPhysicalData.NativeLabel (family (N0 := N0) P u H hp).active)
    (K : ActualSignedPhysicalData.NativeLabel ((family P u H hp).singleton L).active) :
    |((((family P u H hp).singleton L).primary K).pulse
        (((family P u H hp).singleton L).column K)).phase.p K.val.1| ≤
        ActualPhaseJetBounds.phaseSize B N0 ∧
    |((((family P u H hp).singleton L).primary K).pulse
        (((family P u H hp).singleton L).column K)).phase.pz K.val.1| ≤
        ActualPhaseJetBounds.phaseSize B N0 ∧
    |((((family P u H hp).singleton L).primary K).pulse
        (((family P u H hp).singleton L).column K)).phase.x0 K.val.1| ≤
        ActualPhaseJetBounds.phaseSize B N0 := by
  rw [ActualSignedReferenceGeometry.singleton_index_eq (family P u H hp) L K]
  exact ActualPhaseJetBounds.phase_constants_bound
    ((ActualSignedExterior.actualLabel L).2, (ActualSignedExterior.actualLabel L).1)

end Geometry

private theorem cells_mpr {H : ℕ} {K : Type*} {f g : CopyFamily H K}
    (he : f = g) (c : SupportCells g) (L : BandLabel) :
    (Eq.mpr (congrArg SupportCells he) c).cells L = c.cells L := by
  cases he
  rfl

private theorem branchCells_active (f : DependentSignedPhysicalFamily.Family)
    {H : ℕ} {K : Type*}
    (copies : ActualSignedPhysicalData.NativeLabel f.active → CopyFamily H K)
    (c : ∀ L, SupportCells (copies L))
    (L : ActualSignedPhysicalData.NativeLabel f.active) (M : BandLabel) :
    (f.branchCells copies c L).cells M = (c L).cells M := by
  classical
  simp only [DependentSignedPhysicalFamily.Family.branchCells, dite_eq_left L.mem]
  exact cells_mpr (f.copyAt_active copies L) (c L) M

private theorem branchCells_inactive (f : DependentSignedPhysicalFamily.Family)
    {H : ℕ} {K : Type*}
    (copies : ActualSignedPhysicalData.NativeLabel f.active → CopyFamily H K)
    (c : ∀ L, SupportCells (copies L)) (L M : BandLabel) (hL : L ∉ f.active) :
    (f.branchCells copies c L).cells M =
      (DependentSignedPhysicalFamily.zeroCells (H := H) (K := K)).cells M := by
  classical
  simp only [DependentSignedPhysicalFamily.Family.branchCells, dite_eq_right hL]
  exact cells_mpr (f.copyAt_inactive copies hL) DependentSignedPhysicalFamily.zeroCells M

section CopyFamilies

variable (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)

/-- Original potential cells, constructed using `DependentSignedPhysicalFamily.diagonalCells`. -/
noncomputable def originalPotentialCells (i : Fin 3) :
    SupportCells ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i) :=
  DependentSignedPhysicalFamily.diagonalCells _
    ((ActualSignedExterior.family s).branchCells
      (fun L => ActualSignedPhysicalData.potentialFamily slots outgoing.data.h_pos.le
        ((ActualSignedExterior.family s).singleton L) i)
      (fun L => ActualSignedPhysicalData.localizedPotentialCells slots outgoing.data.h_pos.le
        ((ActualSignedExterior.family s).singleton L) i))

/-- Original pressure cells, constructed using `DependentSignedPhysicalFamily.diagonalCells`. -/
noncomputable def originalPressureCells :
    SupportCells ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le) :=
  DependentSignedPhysicalFamily.diagonalCells _
    ((ActualSignedExterior.family s).branchCells
      (fun L => ActualSignedPhysicalData.pressureFamily slots outgoing.data.h_pos.le
        ((ActualSignedExterior.family s).singleton L))
      (fun L => ActualSignedPhysicalData.localizedPressureCells slots outgoing.data.h_pos.le
        ((ActualSignedExterior.family s).singleton L)))

theorem potentialCells_active (i : Fin 3)
    (L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.labels B N0)) :
    (originalPotentialCells s i).cells L =
      (ActualSignedPhysicalData.localizedPotentialCells slots outgoing.data.h_pos.le
        ((ActualSignedExterior.family s).singleton L) i).cells L := by
  exact branchCells_active (ActualSignedExterior.family s) _ _ L L

theorem pressureCells_active
    (L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.labels B N0)) :
    (originalPressureCells s).cells L =
      (ActualSignedPhysicalData.localizedPressureCells slots outgoing.data.h_pos.le
        ((ActualSignedExterior.family s).singleton L)).cells L := by
  exact branchCells_active (ActualSignedExterior.family s) _ _ L L

theorem potentialCells_inactive (i : Fin 3) {L : BandLabel}
    (hL : L ∉ ActualSignedExterior.labels B N0) :
    (originalPotentialCells s i).cells L =
      (DependentSignedPhysicalFamily.zeroCells (H := 1)).cells L := by
  exact branchCells_inactive (ActualSignedExterior.family s) _ _ L L hL

theorem pressureCells_inactive {L : BandLabel}
    (hL : L ∉ ActualSignedExterior.labels B N0) :
    (originalPressureCells s).cells L =
      (DependentSignedPhysicalFamily.zeroCells (H := 1)).cells L := by
  exact branchCells_inactive (ActualSignedExterior.family s) _ _ L L hL

/-- Original potential carrier, bundling `region`, `open_region`, `jets`, `contains` and the
required compatibility proofs. -/
noncomputable def originalPotentialCarrier (i : Fin 3) :
    CarrierBounds ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i)
      (originalPotentialCells s i) ActualPolarCoverage.inner ActualPolarCoverage.outer h
          slots.radius where
  region _ L := ActualSignedNativeProfiles.region B N0 L
  open_region _ := ActualSignedNativeProfiles.region_open B N0
  jets := ActualSignedNativeProfiles.potential_profiles_jets s i
  contains k I w hw _ _ hc j hj := by
    classical
    change LocalPhysicalCopyBounds.slotSlow
      (((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i).carrier k
          I.1
        |>.withChart j) ActualPolarCoverage.inner h I.1.val.1 slots.radius w ∈ _
    rw [ActualSignedPhysicalData.slotSlow_eq_nativeSlow
      ActualPolarCoverage.inner_pos _ h I.1.val.1 slots.radius j w hj]
    by_cases hL : I.1 ∈ ActualSignedExterior.labels B N0
    · let L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.labels B N0) :=
        ⟨I.1.val,I.1.property,hL⟩
      have he := potentialCells_active s i L
      change (originalPotentialCells s i).cells I.1 = _ at he
      rw [he, ActualSignedExterior.potential_gap, ActualSignedPhysicalData.commonLift_zero] at hc
      exact ActualSignedNativeProfiles.closure_covers s L I.1 w hw hc.2
    · rw [potentialCells_inactive s i hL] at hc
      exact hc.elim

/-- Original pressure carrier, bundling `region`, `open_region`, `jets`, `contains` and the
required compatibility proofs. -/
noncomputable def originalPressureCarrier :
    CarrierBounds ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le)
      (originalPressureCells s) ActualPolarCoverage.inner ActualPolarCoverage.outer h slots.radius
          where
  region _ L := ActualSignedNativeProfiles.region B N0 L
  open_region _ := ActualSignedNativeProfiles.region_open B N0
  jets := ActualSignedNativeProfiles.pressure_profiles_jets s
  contains k I w hw _ _ hc j hj := by
    classical
    change LocalPhysicalCopyBounds.slotSlow
      (((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le).carrier k I.1
        |>.withChart j) ActualPolarCoverage.inner h I.1.val.1 slots.radius w ∈ _
    rw [ActualSignedPhysicalData.slotSlow_eq_nativeSlow
      ActualPolarCoverage.inner_pos _ h I.1.val.1 slots.radius j w hj]
    by_cases hL : I.1 ∈ ActualSignedExterior.labels B N0
    · let L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.labels B N0) :=
        ⟨I.1.val,I.1.property,hL⟩
      have he := pressureCells_active s L
      change (originalPressureCells s).cells I.1 = _ at he
      rw [he, ActualSignedExterior.pressure_gap, ActualSignedPhysicalData.commonLift_zero] at hc
      exact ActualSignedNativeProfiles.closure_covers s L I.1 w hw hc.2
    · rw [pressureCells_inactive s hL] at hc
      exact hc.elim

/-- The actual assembled copies, extended by zero outside positive lift
time. Their fields agree with the original signed fields before t=1. -/
noncomputable def potentialCopies (i : Fin 3) : CopyFamily 1 TorusInverse.Frequency :=
  PositiveTimeCopyFamily.gate
    ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i)

/-- Pressure copies, given by `PositiveTimeCopyFamily.gate ((ActualSignedExterior.family
s).pressureCopies slots outgoing.data.h_pos.le)`. -/
noncomputable def pressureCopies : CopyFamily 1 TorusInverse.Frequency :=
  PositiveTimeCopyFamily.gate
    ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le)

/-- Potential cells, given by `PositiveTimeCopyFamily.gateCells (originalPotentialCells s i)`. -/
noncomputable def potentialCells (i : Fin 3) : SupportCells (potentialCopies s i) :=
  PositiveTimeCopyFamily.gateCells (originalPotentialCells s i)

/-- Pressure cells, given by `PositiveTimeCopyFamily.gateCells (originalPressureCells s)`. -/
noncomputable def pressureCells : SupportCells (pressureCopies s) :=
  PositiveTimeCopyFamily.gateCells (originalPressureCells s)

/-- Potential carrier, given by `PositiveTimeCopyFamily.gateCarrier (originalPotentialCells s i)
(originalPotentialCarrier s i)`. -/
noncomputable def potentialCarrier (i : Fin 3) :
    CarrierBounds (potentialCopies s i) (potentialCells s i)
      ActualPolarCoverage.inner ActualPolarCoverage.outer h slots.radius :=
  PositiveTimeCopyFamily.gateCarrier (originalPotentialCells s i) (originalPotentialCarrier s i)

/-- Pressure carrier, given by `PositiveTimeCopyFamily.gateCarrier (originalPressureCells s)
(originalPressureCarrier s)`. -/
noncomputable def pressureCarrier :
    CarrierBounds (pressureCopies s) (pressureCells s)
      ActualPolarCoverage.inner ActualPolarCoverage.outer h slots.radius :=
  PositiveTimeCopyFamily.gateCarrier (originalPressureCells s) (originalPressureCarrier s)

theorem potential_field_eq {w : SpaceTime} (hw : w ∈ preterminal) :
    vectorSum (potentialCopies s) ActualPolarCoverage.inner h slots.radius w =
      ActualSignedExterior.potential s w :=
  PositiveTimeCopyFamily.vectorSum_eq _ _ _ _ hw

theorem pressure_field_eq {w : SpaceTime} (hw : w ∈ preterminal) :
    ((pressureCopies s).sum ActualPolarCoverage.inner h slots.radius w).re =
      ActualSignedExterior.pressure s w :=
  congrArg Complex.re (PositiveTimeCopyFamily.sum_eq _ _ _ _ hw)

theorem potential_field_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    vectorSum (potentialCopies s) ActualPolarCoverage.inner h slots.radius =ᶠ[𝓝 w]
      ActualSignedExterior.potential s :=
  PositiveTimeCopyFamily.vectorSum_germ _ _ _ _ hw

theorem pressure_field_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    (fun w => ((pressureCopies s).sum ActualPolarCoverage.inner h slots.radius w).re) =ᶠ[𝓝 w]
      ActualSignedExterior.pressure s := by
  filter_upwards [PositiveTimeCopyFamily.sum_germ
    ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le)
    ActualPolarCoverage.inner h slots.radius hw] with y hy
  exact congrArg Complex.re hy

/-- The carrier coefficients remain jointly bounded after label selection
and the positive-time extension. -/
theorem singleton_frequencies_of_states
    (L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active)
    (K : ActualSignedPhysicalData.NativeLabel
      ((ActualSignedExterior.family s).singleton L).active) :
    |(((((ActualSignedExterior.family s).singleton L).primary K).pulse
      (((ActualSignedExterior.family s).singleton L).column K)).phase.p K.val.1)| ≤
      ActualPhaseJetBounds.phaseSize B N0 ∧
    |(((((ActualSignedExterior.family s).singleton L).primary K).pulse
      (((ActualSignedExterior.family s).singleton L).column K)).phase.pz K.val.1)| ≤
      ActualPhaseJetBounds.phaseSize B N0 ∧
    |(((((ActualSignedExterior.family s).singleton L).primary K).pulse
      (((ActualSignedExterior.family s).singleton L).column K)).phase.x0 K.val.1)| ≤
      ActualPhaseJetBounds.phaseSize B N0 := by
  rw [ActualSignedReferenceGeometry.singleton_index_eq (ActualSignedExterior.family s) L K]
  exact ActualPhaseJetBounds.phase_constants_bound
    ((ActualSignedExterior.actualLabel L).2, (ActualSignedExterior.actualLabel L).1)

theorem potential_frequencies (i : Fin 3) (k : TorusInverse.Frequency) (L : BandLabel) :
    |((potentialCopies s i).carrier k L).angular| ≤ ActualPhaseJetBounds.phaseSize B N0 ∧
    |((potentialCopies s i).carrier k L).axial| ≤ ActualPhaseJetBounds.phaseSize B N0 ∧
    |((potentialCopies s i).carrier k L).radial| ≤ ActualPhaseJetBounds.phaseSize B N0 := by
  classical
  have he : (potentialCopies s i).carrier k L =
      ((ActualSignedExterior.family s).copyAt
        (fun M => ActualSignedPhysicalData.potentialFamily slots outgoing.data.h_pos.le
          ((ActualSignedExterior.family s).singleton M) i) L).carrier k L := rfl
  rw [he]
  by_cases hL : L ∈ (ActualSignedExterior.family s).active
  · let M : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active :=
      ⟨L.val, L.property, hL⟩
    rw [DependentSignedPhysicalFamily.Family.copyAt_active _ _ M]
    exact ActualSignedPhysicalData.carrier_frequencies
      ((ActualSignedExterior.family s).singleton M) ActualPhaseJetBounds.one_le_phaseSize
      (singleton_frequencies_of_states s M) k L
  · rw [DependentSignedPhysicalFamily.Family.copyAt_inactive _ _ hL]
    have hP := zero_le_one.trans (ActualPhaseJetBounds.one_le_phaseSize (B := B) (N0 := N0))
    exact ⟨by simpa [DependentSignedPhysicalFamily.zeroCopies] using hP,
      by simpa [DependentSignedPhysicalFamily.zeroCopies] using hP,
      by simpa [DependentSignedPhysicalFamily.zeroCopies] using hP⟩

theorem pressure_frequencies (k : TorusInverse.Frequency) (L : BandLabel) :
    |((pressureCopies s).carrier k L).angular| ≤ ActualPhaseJetBounds.phaseSize B N0 ∧
    |((pressureCopies s).carrier k L).axial| ≤ ActualPhaseJetBounds.phaseSize B N0 ∧
    |((pressureCopies s).carrier k L).radial| ≤ ActualPhaseJetBounds.phaseSize B N0 := by
  classical
  have he : (pressureCopies s).carrier k L =
      ((ActualSignedExterior.family s).copyAt
        (fun M => ActualSignedPhysicalData.pressureFamily slots outgoing.data.h_pos.le
          ((ActualSignedExterior.family s).singleton M)) L).carrier k L := rfl
  rw [he]
  by_cases hL : L ∈ (ActualSignedExterior.family s).active
  · let M : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active :=
      ⟨L.val, L.property, hL⟩
    rw [DependentSignedPhysicalFamily.Family.copyAt_active _ _ M]
    exact ActualSignedPhysicalData.carrier_frequencies
      ((ActualSignedExterior.family s).singleton M) ActualPhaseJetBounds.one_le_phaseSize
      (singleton_frequencies_of_states s M) k L
  · rw [DependentSignedPhysicalFamily.Family.copyAt_inactive _ _ hL]
    have hP := zero_le_one.trans (ActualPhaseJetBounds.one_le_phaseSize (B := B) (N0 := N0))
    exact ⟨by simpa [DependentSignedPhysicalFamily.zeroCopies] using hP,
      by simpa [DependentSignedPhysicalFamily.zeroCopies] using hP,
      by simpa [DependentSignedPhysicalFamily.zeroCopies] using hP⟩

/-! ## The jointly indexed Cartesian sources -/

/-- Source strip, constructed using `CartesianCopySource.pullStrip`. -/
noncomputable def sourceStrip : WeightedClasses.StripData PhysicalGraphBounds.LiftPoint :=
  CartesianCopySource.pullStrip ActualPrimaryBounds.strip
    ActualPolarCoverage.inner ActualPolarCoverage.outer ActualPolarCoverage.inner_pos

/-- Potential source as an element of `(Fin 3 × SourceIndex) → ℕ → PhysicalGraphBounds.LiftPoint
→ ℂ`. -/
noncomputable def potentialSource :
    (Fin 3 × SourceIndex) → ℕ → PhysicalGraphBounds.LiftPoint → ℂ :=
  fun I n x => CartesianCopySource.rotatedSource
    (DependentSignedPhysicalFamily.jointSource
      ((ActualSignedExterior.family s).potentialSource slots outgoing.data.h_pos.le)) I.2 n x I.1

/-- Pressure source as an element of `SourceIndex → ℕ → PhysicalGraphBounds.LiftPoint → ℂ`. -/
noncomputable def pressureSource : SourceIndex → ℕ → PhysicalGraphBounds.LiftPoint → ℂ :=
  fun I n x => DependentSignedPhysicalFamily.jointSource
    ((ActualSignedExterior.family s).pressureSource slots outgoing.data.h_pos.le) I n
      (PhysicalClassBounds.cylindricalMap x)

/-- Source weight, given by `Real.sqrt (ActualPrimaryBounds.strip.zeta
(PhysicalClassBounds.cylindricalMap x))`. -/
noncomputable def sourceWeight (_ : SourceIndex) (_ : ℕ)
    (x : PhysicalGraphBounds.LiftPoint) : ℝ :=
  Real.sqrt (ActualPrimaryBounds.strip.zeta (PhysicalClassBounds.cylindricalMap x))

/-- Potential weight, given by `sourceWeight I.2 n x`. -/
noncomputable def potentialWeight (I : Fin 3 × SourceIndex) (n : ℕ)
    (x : PhysicalGraphBounds.LiftPoint) : ℝ := sourceWeight I.2 n x

theorem potential_amplitude_eq_source (i : Fin 3) (k : TorusInverse.Frequency)
    (I : WaveIndex 1) (x : PhysicalGraphBounds.LiftPoint) :
    ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i).amplitude k I
        x =
      ChartScales.Q I.1.val.1 ^ (-h) • potentialSource s (i, ⟨I.1, (I, k)⟩) I.1.val.1 x :=
  DependentSignedPhysicalFamily.Family.potential_amplitude_eq_source _ _ _ _ _ _ _

theorem pressure_amplitude_eq_source (k : TorusInverse.Frequency)
    (I : WaveIndex 1) (x : PhysicalGraphBounds.LiftPoint) :
    ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le).amplitude k I x =
      ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A h)) •
        pressureSource s ⟨I.1, (I, k)⟩ I.1.val.1 x :=
  DependentSignedPhysicalFamily.Family.pressure_amplitude_eq_source _ _ _ _ _ _

theorem potential_source_bounds {α : ℝ}
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
      (fun (_ : SourceIndex) _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y))
      (DependentSignedPhysicalFamily.jointSource
        ((ActualSignedExterior.family s).potentialSource slots outgoing.data.h_pos.le))) :
    LocalPhysicalCopyBounds.LocalSourceBounds sourceStrip h α potentialWeight (potentialSource s) :=
  ActualSignedPhysicalData.componentSourceBounds
    (CartesianCopySource.sourceBounds_rotated (b := ActualPolarCoverage.outer)
      ActualPolarCoverage.inner_pos hs)

theorem pressure_source_bounds {α : ℝ}
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
      (fun (_ : SourceIndex) _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y))
      (DependentSignedPhysicalFamily.jointSource
        ((ActualSignedExterior.family s).pressureSource slots outgoing.data.h_pos.le))) :
    LocalPhysicalCopyBounds.LocalSourceBounds sourceStrip h α sourceWeight (pressureSource s) :=
  CartesianCopySource.sourceBounds_pullback (b := ActualPolarCoverage.outer)
    ActualPolarCoverage.inner_pos hs

end CopyFamilies

section NativeAssembly

variable (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
  (hgeo : ∀ L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active,
    ActualSignedPhysicalData.ReferenceGeometry slots ((ActualSignedExterior.family s).singleton L))
  (hn : ∀ L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active,
    ActualSignedPhysicalData.NativeRegular slots outgoing.data.h_pos.le
      ((ActualSignedExterior.family s).singleton L))
  {α : ℝ}

/-- The physical potential datum is assembled once over all source labels.
The source estimate and profile constants are chosen before those labels. -/
noncomputable def potentialOfNative
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
      (fun (_ : SourceIndex) _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y))
      (DependentSignedPhysicalFamily.jointSource
        ((ActualSignedExterior.family s).potentialSource slots outgoing.data.h_pos.le))) :
    PhysicalStageBounds.WaveData h PhysicalGraphBounds.LiftPoint
      (Fin 3 × SourceIndex) TorusInverse.Frequency (Fin 3) where
  lowerRadius := ActualPolarCoverage.inner
  upperRadius := ActualPolarCoverage.outer
  nativeWidth := slots.radius
  slowBound := 2
  frequencyBound := ActualPhaseJetBounds.phaseSize B N0
  alpha := α
  shift := -h
  harmonics := 1
  gapBound := 0
  lower_pos := ActualPolarCoverage.inner_pos
  width_nonneg := slots.radius_pos.le
  slow_nonneg := by norm_num
  frequency_one_le := ActualPhaseJetBounds.one_le_phaseSize
  strip := sourceStrip
  weight := potentialWeight
  source := potentialSource s
  source_bounds := potential_source_bounds s hs
  copies := potentialCopies s
  cells := potentialCells s
  chart i := PositiveTimeSignedData.identitySourceChart _ (originalPotentialCells s i)
    ActualPolarCoverage.inner_pos (ActualSignedFamilySupport.potential_support s hgeo i)
    sourceStrip (potentialSource s) (fun k I => (i, ⟨I.1, (I, k)⟩))
    (potential_amplitude_eq_source s i)
    (ActualSignedFamilySupport.potential_source_domain s i)
  chart_maps _ _ _ := fun _ hx => hx.1
  carrier := potentialCarrier s
  support := ActualSignedFamilySupport.potential_support s hgeo
  smooth := ActualSignedFamilySupport.potential_smooth s hgeo hn
  frequencies := potential_frequencies s

/-- Pressure of native, bundling `lowerRadius`, `upperRadius`, `nativeWidth`, `slowBound` and
the required compatibility proofs. -/
noncomputable def pressureOfNative
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
      (fun (_ : SourceIndex) _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y))
      (DependentSignedPhysicalFamily.jointSource
        ((ActualSignedExterior.family s).pressureSource slots outgoing.data.h_pos.le))) :
    PhysicalStageBounds.WaveData h PhysicalGraphBounds.LiftPoint
      SourceIndex TorusInverse.Frequency Unit where
  lowerRadius := ActualPolarCoverage.inner
  upperRadius := ActualPolarCoverage.outer
  nativeWidth := slots.radius
  slowBound := 2
  frequencyBound := ActualPhaseJetBounds.phaseSize B N0
  alpha := α
  shift := -(2 * CoordinateAlgebra.A h)
  harmonics := 1
  gapBound := 0
  lower_pos := ActualPolarCoverage.inner_pos
  width_nonneg := slots.radius_pos.le
  slow_nonneg := by norm_num
  frequency_one_le := ActualPhaseJetBounds.one_le_phaseSize
  strip := sourceStrip
  weight := sourceWeight
  source := pressureSource s
  source_bounds := pressure_source_bounds s hs
  copies _ := pressureCopies s
  cells _ := pressureCells s
  chart _ := PositiveTimeSignedData.identitySourceChart _ (originalPressureCells s)
    ActualPolarCoverage.inner_pos (ActualSignedFamilySupport.pressure_support s hgeo)
    sourceStrip (pressureSource s) (fun k I => ⟨I.1, (I, k)⟩)
    (pressure_amplitude_eq_source s)
    (ActualSignedFamilySupport.pressure_source_domain s)
  chart_maps _ _ _ := fun _ hx => hx.1
  carrier _ := pressureCarrier s
  support _ := ActualSignedFamilySupport.pressure_support s hgeo
  smooth _ := ActualSignedFamilySupport.pressure_smooth s hgeo hn
  frequencies _ := pressure_frequencies s

variable
  (hpotential : LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
    (fun (_ : SourceIndex) _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y))
    (DependentSignedPhysicalFamily.jointSource
      ((ActualSignedExterior.family s).potentialSource slots outgoing.data.h_pos.le)))
  (hpressure : LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
    (fun (_ : SourceIndex) _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y))
    (DependentSignedPhysicalFamily.jointSource
      ((ActualSignedExterior.family s).pressureSource slots outgoing.data.h_pos.le)))

@[simp] theorem potentialOfNative_alpha :
    (potentialOfNative s hgeo hn hpotential).alpha = α := rfl

@[simp] theorem pressureOfNative_alpha :
    (pressureOfNative s hgeo hn hpressure).alpha = α := rfl

@[simp] theorem potentialOfNative_shift :
    (potentialOfNative s hgeo hn hpotential).shift = -h := rfl

@[simp] theorem pressureOfNative_shift :
    (pressureOfNative s hgeo hn hpressure).shift = -(2 * CoordinateAlgebra.A h) := rfl

theorem potentialOfNative_vector_eq {w : SpaceTime} (hw : w ∈ preterminal) :
    (potentialOfNative s hgeo hn hpotential).vector w = ActualSignedExterior.potential s w :=
  potential_field_eq s hw

theorem pressureOfNative_pressure_eq {w : SpaceTime} (hw : w ∈ preterminal) :
    (pressureOfNative s hgeo hn hpressure).pressure w = ActualSignedExterior.pressure s w :=
  pressure_field_eq s hw

theorem potentialOfNative_vector_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    (potentialOfNative s hgeo hn hpotential).vector =ᶠ[𝓝 w] ActualSignedExterior.potential s :=
  potential_field_germ s hw

theorem pressureOfNative_pressure_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    (pressureOfNative s hgeo hn hpressure).pressure =ᶠ[𝓝 w] ActualSignedExterior.pressure s :=
  pressure_field_germ s hw

end NativeAssembly

section ActualProducers

open WeightedClasses

variable (u : State LocalSignedRequest.Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b u.pressure)
  (α : ℝ)
  (hfixed : VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
    (commonContext B) u = u)
  (hθ : MeanClass ActualInitialization.geometry.strip α (u.thetaResidual (commonContext B)))
  (hz : MeanClass ActualInitialization.geometry.strip α (u.axialResidual (commonContext B)))

/-- Genuine primitive and measured residual data produce the entire
potential record. Native regularity and native output bounds are derived. -/
noncomputable def potentialFromResiduals :
    PhysicalStageBounds.WaveData h PhysicalGraphBounds.LiftPoint
      (Fin 3 × SourceIndex) TorusInverse.Frequency (Fin 3) :=
  potentialOfNative (α := α) (nativeStates (N0 := N0) ActualInitialization.patch u H hp)
    (singletonGeometry ActualInitialization.patch u H hp)
    (ActualSignedNativeRegularity.nativeRegular_from_residuals u H hp α hfixed hθ hz)
    (by
      have hb := ActualSignedNativeBounds.source_bounds ActualInitialization.patch u H hp
        (ActualSignedNativeRegularity.request_jets_from_residuals
          (N0 := N0) u α H hfixed hθ hz)
      have he := hb.1
      simp only [sub_add_cancel] at he
      exact he)

/-- Pressure from residuals, constructed using `pressureOfNative`. -/
noncomputable def pressureFromResiduals :
    PhysicalStageBounds.WaveData h PhysicalGraphBounds.LiftPoint
      SourceIndex TorusInverse.Frequency Unit :=
  pressureOfNative (α := α) (nativeStates (N0 := N0) ActualInitialization.patch u H hp)
    (singletonGeometry ActualInitialization.patch u H hp)
    (ActualSignedNativeRegularity.nativeRegular_from_residuals u H hp α hfixed hθ hz)
    (by
      have hb := ActualSignedNativeBounds.source_bounds ActualInitialization.patch u H hp
        (ActualSignedNativeRegularity.request_jets_from_residuals
          (N0 := N0) u α H hfixed hθ hz)
      have he := hb.2
      simp only [sub_add_cancel] at he
      exact he)

@[simp] theorem potentialFromResiduals_alpha :
    (potentialFromResiduals (N0 := N0) u H hp α hfixed hθ hz).alpha = α := rfl

@[simp] theorem pressureFromResiduals_alpha :
    (pressureFromResiduals (N0 := N0) u H hp α hfixed hθ hz).alpha = α := rfl

@[simp] theorem potentialFromResiduals_shift :
    (potentialFromResiduals (N0 := N0) u H hp α hfixed hθ hz).shift = -h := rfl

@[simp] theorem pressureFromResiduals_shift :
    (pressureFromResiduals (N0 := N0) u H hp α hfixed hθ hz).shift =
      -(2 * CoordinateAlgebra.A h) := rfl

end ActualProducers

section Cycle

variable {σ : ℝ} (x : CycleState (Label B N0))
  (R : ActualParticularMeanGain.Result x σ)

/-- The post-particular theorem supplies every analytic hypothesis; the
physical copies use its same reconstructed state and pressure primitive. -/
noncomputable def cyclePotentialData :
    PhysicalStageBounds.WaveData h PhysicalGraphBounds.LiftPoint
      (Fin 3 × SourceIndex) TorusInverse.Frequency (Fin 3) :=
  potentialFromResiduals (N0 := N0) (ActualParticularMeanGain.postParticular x) R.primitive
    (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive)
    (1 + σ - ChartScales.kappa) R.reconstructed R.theta R.axial

/-- Cycle pressure data, constructed using `pressureFromResiduals`. -/
noncomputable def cyclePressureData :
    PhysicalStageBounds.WaveData h PhysicalGraphBounds.LiftPoint
      SourceIndex TorusInverse.Frequency Unit :=
  pressureFromResiduals (N0 := N0) (ActualParticularMeanGain.postParticular x) R.primitive
    (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive)
    (1 + σ - ChartScales.kappa) R.reconstructed R.theta R.axial

@[simp] theorem cyclePotentialData_alpha :
    (cyclePotentialData x R).alpha = 1 + σ - ChartScales.kappa := rfl

@[simp] theorem cyclePressureData_alpha :
    (cyclePressureData x R).alpha = 1 + σ - ChartScales.kappa := rfl

@[simp] theorem cyclePotentialData_shift : (cyclePotentialData x R).shift = -h := rfl

@[simp] theorem cyclePressureData_shift :
    (cyclePressureData x R).shift = -(2 * CoordinateAlgebra.A h) := rfl

theorem cyclePotentialData_eq : EqOn (cyclePotentialData x R).vector
    (ActualSignedExterior.cyclePotential x R.primitive
      (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive)) preterminal :=
  fun _ hw => potential_field_eq _ hw

theorem cyclePressureData_eq : EqOn (cyclePressureData x R).pressure
    (ActualSignedExterior.cyclePressure x R.primitive
      (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive)) preterminal :=
  fun _ hw => pressure_field_eq _ hw

theorem cyclePotentialData_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    (cyclePotentialData x R).vector =ᶠ[𝓝 w]
      ActualSignedExterior.cyclePotential x R.primitive
        (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive) :=
  potential_field_germ _ hw

theorem cyclePressureData_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    (cyclePressureData x R).pressure =ᶠ[𝓝 w]
      ActualSignedExterior.cyclePressure x R.primitive
        (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive) :=
  pressure_field_germ _ hw

/-- A consequence for the original signed potential, including every
ambient time and spatial derivative. -/
theorem cyclePotential_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (ActualSignedExterior.cyclePotential x R.primitive
          (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive)) w‖ ≤
        C * physicalQ h w ^ (h * (1 + σ - ChartScales.kappa) -
          PhysicalClassBounds.physicalLoss h (-h) m) := by
  obtain ⟨C, hC, hb⟩ := (cyclePotentialData x R).vector_bound
    outgoing.data.h_pos outgoing.data.h_lt_half m
  refine ⟨C, hC, fun w hw hq => ?_⟩
  rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (cyclePotentialData_germ x R hw) m]
  exact hb w hw hq

theorem cyclePressure_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (ActualSignedExterior.cyclePressure x R.primitive
          (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive)) w‖ ≤
        C * physicalQ h w ^ (h * (1 + σ - ChartScales.kappa) -
          PhysicalClassBounds.physicalLoss h (-(2 * CoordinateAlgebra.A h)) m) := by
  obtain ⟨C, hC, hb⟩ := (cyclePressureData x R).pressure_bound
    outgoing.data.h_pos outgoing.data.h_lt_half m
  refine ⟨C, hC, fun w hw hq => ?_⟩
  rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (cyclePressureData_germ x R hw) m]
  exact hb w hw hq

end Cycle

/-! ## The actual infinite stage sequence -/

theorem stageResult (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ActualParticularMeanGain.Result (ActualCyclePreservation.state B N0 j)
      (ActualIterationLedger.sigma j) :=
  ActualParticularMeanGain.postParticular_gain
    (ActualCyclePreservation.state_invariant B N0 hN j)
    (ActualCyclePreservation.state_particularInputs B N0 hN j)
    (ActualIterationLedger.sigma_admissible j)

/-- The actual signed part of the schedule. There is no input WaveData,
physical bound or native output-regularity hypothesis. -/
noncomputable def signedInputs (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    GluedStageEstimates.SignedInputs PhysicalGraphBounds.LiftPoint SourceIndex
        TorusInverse.Frequency where
  potential j := cyclePotentialData (ActualCyclePreservation.state B N0 j) (stageResult B N0 hN j)
  pressure j := cyclePressureData (ActualCyclePreservation.state B N0 j) (stageResult B N0 hN j)
  potential_exponent j := by
    change 1 / 2 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
      1 + ActualIterationLedger.sigma j - ChartScales.kappa
    linarith
  pressure_exponent _ := le_rfl
  potential_shift _ := rfl
  pressure_shift _ := rfl

theorem signedInputs_potential_eq (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    EqOn ((signedInputs B N0 hN).potential j).vector
      (ActualSignedExterior.cyclePotential (ActualCyclePreservation.state B N0 j)
        (stageResult B N0 hN j).primitive
        (ActualSignedPhysicalBinding.afterParticular_pressure (ActualCyclePreservation.state B N0 j)
          (stageResult B N0 hN j).primitive)) preterminal :=
  cyclePotentialData_eq (ActualCyclePreservation.state B N0 j) (stageResult B N0 hN j)

theorem signedInputs_pressure_eq (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    EqOn ((signedInputs B N0 hN).pressure j).pressure
      (ActualSignedExterior.cyclePressure (ActualCyclePreservation.state B N0 j)
        (stageResult B N0 hN j).primitive
        (ActualSignedPhysicalBinding.afterParticular_pressure (ActualCyclePreservation.state B N0 j)
          (stageResult B N0 hN j).primitive)) preterminal :=
  cyclePressureData_eq (ActualCyclePreservation.state B N0 j) (stageResult B N0 hN j)

end NavierStokes.ActualSignedWaveData
