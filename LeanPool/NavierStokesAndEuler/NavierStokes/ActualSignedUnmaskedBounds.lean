/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalBinding
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedOutputBounds

@[expose] public section

/-!
# The actual signed coefficients with only the dyadic factor removed

The matrix, target, current request, normalized pulse and pressure operator
are unchanged. The spatial mask is replaced by its actual native grid factor.
All estimates are on the original native control cells.
-/

noncomputable section
open Set Function Filter
open scoped Topology ContDiff BigOperators

namespace NavierStokes.ActualSignedUnmaskedBounds

open WeightedClasses PhaseJetBounds PrimaryCopyBounds
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open ActualSignedStageControls


abbrev Label (B N0 : ℕ) := ActualSignedStageControls.SignedLabel B N0
abbrev Full := ActualSignedStageControls.FullPoint
abbrev Copy := TorusInverse.Frequency
abbrev CV := CurlClassBounds.ComplexVector

variable {B N0 : ℕ}

noncomputable def gridMask (l : Label B N0) (k : Copy) (n : ℕ) (x : Full) : ℝ :=
  PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand l.1)
    (PrimaryGeometryAssembly.label nominal l.1).2 (nativePoint l n k x).1

noncomputable def dyadicFactor (l : Label B N0) (k : Copy) (n : ℕ) (x : Full) : ℝ :=
  SquaredPartition.dyadicProfile (SimilarityCoordinates.coordinateQ (2 * h)
    ((nativePoint l n k x).1.2.2, (nativePoint l n k x).1.2.1))

theorem mask_factor (l : Label B N0) (k : Copy) (n : ℕ) (x : Full) :
    ActualSignedStageControls.mask l k n x = dyadicFactor l k n x * gridMask l k n x :=
  spatialMask_eq l.1 (nativePoint l n k x).1

/-- The actual signed solve, changing only its slow mask. -/
noncomputable def coefficients (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (k : Copy) : LinearWaveBounds.WaveCoefficients Full :=
  SignedWaveUpdate.coefficients (chartCoefficients l.2 l.1) fullStrip (directions B)
    (matrix l k) (target l k) request (gridMask l k) (fundamental l k)
    (normalMotion l k) (action l k) l.2

noncomputable def amplitude (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (k : Copy) (n : ℕ) (x : Full) : CV :=
  cutoff l k n x • (coefficients request l k).amplitude n x

noncomputable def pressure (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (k : Copy) (n : ℕ) (x : Full) : ℂ :=
  cutoff l k n x • (coefficients request l k).pressure n x

noncomputable def potential (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (k : Copy) (n : ℕ) (x : Full) : CV :=
  CurlClassBounds.inverseCarrier ((chartCoefficients l.2 l.1).frequency n) •
    CurlClassBounds.normalCoefficient
      ((chartCoefficients l.2 l.1).normal fullStrip (directions B) n x)
      (amplitude request l k n x)

theorem scalar_factor (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (k : Copy) (n : ℕ) (x : Full) :
    SignedWaveUpdate.signedScalar fullStrip (matrix l k) (target l k) request
      (ActualSignedStageControls.mask l k) l.2 n x =
      dyadicFactor l k n x * SignedWaveUpdate.signedScalar fullStrip (matrix l k)
        (target l k) request (gridMask l k) l.2 n x := by
  simp only [SignedWaveUpdate.signedScalar, mask_factor]
  ring

theorem raw_amplitude_factor (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (k : Copy) (n : ℕ) (x : Full) :
    (((parameters l).copyData ActualPrimaryBounds.strip request).raw k).amplitude n x =
      dyadicFactor l k n x • (coefficients request l k).amplitude n x := by
  rw [parameters_raw]
  change (SignedWaveUpdate.coefficients _ fullStrip _ _ _ _ _ _ _ _ _).amplitude n x = _
  rw [ActualPeriodizedSignedRealization.coefficients_amplitude_at]
  unfold coefficients
  rw [ActualPeriodizedSignedRealization.coefficients_amplitude_at, scalar_factor, mul_smul]

theorem raw_pressure_factor (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (k : Copy) (n : ℕ) (x : Full) :
    (((parameters l).copyData ActualPrimaryBounds.strip request).raw k).pressure n x =
      dyadicFactor l k n x • (coefficients request l k).pressure n x := by
  rw [parameters_raw]
  change (SignedWaveUpdate.coefficients _ fullStrip _ _ _ _ _ _ _ _ _).pressure n x = _
  rw [ActualPeriodizedSignedRealization.coefficients_pressure_at]
  unfold coefficients
  rw [ActualPeriodizedSignedRealization.coefficients_pressure_at, scalar_factor, mul_smul]

/-- The original once-localized velocity retains precisely one Gaussian. -/
theorem amplitude_factor (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (k : Copy) (n : ℕ) (x : Full) :
    (((parameters l).copyData ActualPrimaryBounds.strip request).localized k).amplitude n x =
      dyadicFactor l k n x • amplitude request l k n x := by
  change cutoff l k n x •
    (((parameters l).copyData ActualPrimaryBounds.strip request).raw k).amplitude n x = _
  rw [raw_amplitude_factor, smul_comm]
  rfl

theorem pressure_factor (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (k : Copy) (n : ℕ) (x : Full) :
    (((parameters l).copyData ActualPrimaryBounds.strip request).localized k).pressure n x =
      dyadicFactor l k n x • pressure request l k n x := by
  change cutoff l k n x •
    (((parameters l).copyData ActualPrimaryBounds.strip request).raw k).pressure n x = _
  rw [raw_pressure_factor, smul_comm]
  rfl

theorem potential_factor (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (k : Copy) (n : ℕ) (x : Full) :
    CurlClassBounds.inverseCarrier ((chartCoefficients l.2 l.1).frequency n) •
      CurlClassBounds.normalCoefficient ((chartCoefficients l.2 l.1).normal fullStrip (directions
        B) n x)
        ((((parameters l).copyData ActualPrimaryBounds.strip request).localized k).amplitude n x) =
      dyadicFactor l k n x • potential request l k n x := by
  rw [amplitude_factor]
  simp only [potential, CurlClassBounds.normalCoefficient, CurlClassBounds.normalCross_real_smul,
    smul_comm (dyadicFactor l k n x)]

theorem grid_native_jets (U : LocalSignedRequest.SlowRegion (2 * h)) :
    PolynomialJets (slowJetDomain (B := B) (N0 := N0) U).toDomain
      (fun l => PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand l.2)
        (PrimaryGeometryAssembly.label nominal l.2).2) :=
  PrimaryCopyBounds.nativeMask_jets (slowJetDomain (B := B) (N0 := N0) U).toDomain
    (fun l => BaseChartJets.cellBand l.2)
    (fun l => (PrimaryGeometryAssembly.label nominal l.2).2)
    (fun l => l.2.val.property.1) (fun _ => rfl)

/-- The native grid bound is independent of the dyadic profile, including
all of its derivatives. Its constants precede labels and copies. -/
theorem gridMask_local_jets :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ _ => 1) 0
      (phaseCell (B := B) (N0 := N0)) (fun l n k => gridMask l k n) := by
  have hm := (grid_native_jets (B := B) (N0 := N0) ActualPhaseDefect.paddedRegion).lift_slot
    (fun i => (phases B N0 i.1).V i.2) (fun i => (phases B N0 i.1).openV i.2)
  have hp := uniform_of_primary (w := fun _ _ _ => 1) (ActualPrimaryBounds.polynomial_on_control hm)
  apply ActualSignedControl.uniform_local_congr hp
  intro l n k x _ hc
  apply Filter.Eventually.of_forall
  intro y
  change PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand l.1)
      (PrimaryGeometryAssembly.label nominal l.1).2 (ActualPrimaryBounds.fullCopy (l.2, l.1) n k
        y).1 = _
  rw [← nativePoint_eq_fullCopy l n k hc.1.1]
  rfl

/-- Cramer's quotient and the actual normalized homogeneous pulse give
the unmasked amplitude and pressure bounds; no output bound is an input. -/
theorem raw_jets {β : ℝ} {request : ℕ → Full → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun (l : Label B N0) n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) (β + 1 / 2)
        phaseCell
      (fun l n k => (coefficients request l k).amplitude n) ∧
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun (l : Label B N0) n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) (β + 1) phaseCell
      (fun l n k => (coefficients request l k).pressure n) := by
  classical
  cases isEmpty_or_nonempty (Label B N0) with
  | inl h =>
      let := h
      constructor <;> refine ⟨fun l => isEmptyElim l, fun _ => ⟨0, le_rfl, 0, fun l => isEmptyElim
        l⟩⟩
  | inr h =>
      let := h
      have hw : ∀ l n x, x ∈ fullStrip.domain → 0 ≤ envelope (B := B) (N0 := N0) l n x :=
        fun l n x _ => ActualPrimaryBounds.fullEnvelope_nonneg (l.2, l.1) n x
      have hh (j : Fin 2) := SignedCopyBounds.uniform_coefficients_jets
        (a := fun (l : Label B N0) (_ : Copy) => chartCoefficients l.2 l.1)
        (d := fun (_ : Label B N0) (_ : Copy) => directions B)
        (R := fun (_ : Label B N0) (_ : Copy) => request)
        (H := matrix) (T := target) (mask := gridMask) (v := fundamental)
        (Ndot := normalMotion) (A := action) (W := envelope)
        (nativeCovariance B N0) hR gridMask_local_jets fundamental_local_jets hw
        normal_local_jets normalMotion_local_jets action_local_jets
        (ActualPrimaryBounds.normalFloor_pos B N0)
        (fun l n k x hx hc => (normal_range (l := l) (n := n) (k := k) (x := x) hx hc).1)
        (fun l n k x hx hc => (normal_range (l := l) (n := n) (k := k) (x := x) hx hc).2)
        inverse_frequency_uniform j
      have hweight l n x hx := mul_nonneg (Real.sqrt_nonneg (fullStrip.zeta x)) (hw l n x hx)
      exact ⟨uniform_select_two (fun j => (hh j).1) hweight,
        uniform_select_two (fun j => (hh j).2) hweight⟩

theorem localized_jets {β : ℝ} {request : ℕ → Full → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun (l : Label B N0) n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) (β + 1 / 2)
        phaseCell
      (fun l n k => amplitude request l k n) ∧
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun (l : Label B N0) n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) (β + 1) phaseCell
      (fun l n k => pressure request l k n) := by
  classical
  cases isEmpty_or_nonempty (Label B N0) with
  | inl h =>
      let := h
      constructor <;> refine ⟨fun l => isEmptyElim l, fun _ => ⟨0, le_rfl, 0, fun l => isEmptyElim
        l⟩⟩
  | inr h =>
      let := h
      have hw (l : Label B N0) n x (_ : x ∈ fullStrip.domain) := mul_nonneg (Real.sqrt_nonneg
        (fullStrip.zeta x))
        (ActualPrimaryBounds.fullEnvelope_nonneg (l.2, l.1) n x)
      exact ⟨SignedCopyBounds.uniform_smul cutoff_local_jets (raw_jets hR).1 hw,
        SignedCopyBounds.uniform_smul cutoff_local_jets (raw_jets hR).2 hw⟩

theorem potential_jets {β : ℝ} {request : ℕ → Full → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun (l : Label B N0) n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) (β + 1) phaseCell
      (fun l n k => potential request l k n) := by
  have ha := LocalizedWaveBounds.LocalClass.of_uniformLocalJets
    (fun (l : Label B N0) n x (_ : x ∈ fullStrip.domain) =>
      mul_nonneg (Real.sqrt_nonneg (fullStrip.zeta x))
        (ActualPrimaryBounds.fullEnvelope_nonneg (l.2, l.1) n x)) (localized_jets hR).1
  have hn := (ActualSignedOutputBounds.background_inputs (B := B) (N0 := N0) request).normal
  have hcross := (hn.map CurlClassBounds.complexify).bilinear ha CurlClassBounds.complexCrossLinear
  have hinv := (ActualSignedOutputBounds.background_inputs (B := B) (N0 := N0)
    request).normalInverse_class
    (ActualPrimaryBounds.normalFloor_pos B N0)
    (fun n i x hx hi => (ActualSignedOutputBounds.normal_range request i.1 n i.2 hx hi).1)
    (fun n i x hx hi => (ActualSignedOutputBounds.normal_range request i.1 n i.2 hx hi).2)
  have hc := LocalizedWaveBounds.unweighted_smul hinv hcross
  have hh := (LocalizedWaveBounds.unweighted_smul
    (ActualSignedOutputBounds.inverse_frequency request) hc).map
      (Complex.I • ContinuousLinearMap.id ℝ CV)
  have hp : LocalizedWaveBounds.LocalWave fullStrip
      (ActualSignedOutputBounds.jointCell (B := B) (N0 := N0))
      (fun n i x => envelope i.1 n x) (β + 1)
      (fun n i => potential request i.1 i.2 n) := by
    have hh' := hh
    simp only [one_mul, zero_add, show (1 / 2 : ℝ) + (β + 1 / 2) = β + 1 by ring] at hh'
    apply hh'.congr
    intro n i x
    ext j
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, Pi.smul_apply,
      Complex.real_smul, smul_eq_mul, potential, CurlClassBounds.normalCoefficient,
      CurlClassBounds.normalCross, CurlClassBounds.inverseCarrier]
    change Complex.I * (((1 / ((chartCoefficients i.1.2 i.1.1).frequency n) : ℝ) : ℂ) * _) =
      (Complex.I / (((chartCoefficients i.1.2 i.1.1).frequency n : ℝ) : ℂ)) * _
    push_cast
    ring_nf
    rfl
  exact hp.to_uniformLocalJets

/-! ## Removing the cutoff preserves the literal own-band zero germs -/

noncomputable def reference (l : Label B N0) : ℕ := BaseChartJets.cellBand l.1

theorem dyadicFactor_reference (l : Label B N0) (k : Copy) (x : Full) :
    dyadicFactor l k (reference l) x =
      SquaredPartition.dyadicProfile (SimilarityCoordinates.coordinateQ (2 * h) x.1.2.1) := by
  unfold dyadicFactor
  change SquaredPartition.dyadicProfile (SimilarityCoordinates.coordinateQ (2 * h)
    ((nativeSlow l.1 (toAbsolute (BaseChartJets.cellBand l.1) x.1)).2.2,
      (nativeSlow l.1 (toAbsolute (BaseChartJets.cellBand l.1) x.1)).2.1)) = _
  rw [nativeSlow_toAbsolute]
  rfl

theorem dyadic_reference_nonzero (l : Label B N0) (k : Copy) {x : Full}
    (hx : x ∈ ActualWaveRegularity.fullDomain standardRegion) :
    dyadicFactor l k (reference l) x ≠ 0 := by
  rw [dyadicFactor_reference]
  change SimilarityCoordinates.coordinateQ (2 * h) x.1.2.1 ∈ support SquaredPartition.dyadicProfile
  rw [SquaredPartition.dyadicProfile_support]
  exact hx.1.2

theorem dyadic_reference_nonzero_germ (l : Label B N0) (k : Copy) {x : Full}
    (hx : x ∈ fullStrip.domain) :
    ∀ᶠ y in 𝓝 x, dyadicFactor l k (reference l) y ≠ 0 := by
  filter_upwards [fullStrip.isOpen_domain.mem_nhds hx] with y hy
  exact dyadic_reference_nonzero l k (ActualWaveRegularityData.strip_subset_fullDomain hy)

theorem own_phaseCell_or_zero (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (k : Copy) {x : Full} (hx : x ∈ fullStrip.domain) :
    x ∈ phaseCell l (reference l) k ∨
      ((amplitude request l k (reference l) =ᶠ[𝓝 x] fun _ => 0) ∧
       (pressure request l k (reference l) =ᶠ[𝓝 x] fun _ => 0) ∧
       (potential request l k (reference l) =ᶠ[𝓝 x] fun _ => 0)) := by
  rcases ActualSignedOutputBounds.phaseCell_or_localized_zero request l (reference l) k hx with hc
    | ⟨ha, hp⟩
  · exact Or.inl hc
  · right
    have hne := dyadic_reference_nonzero_germ l k hx
    have hza : amplitude request l k (reference l) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [ha, hne] with y hy hn
      have he := amplitude_factor request l k (reference l) y
      rw [show (((parameters l).copyData ActualPrimaryBounds.strip request).localized k).amplitude
        (reference l) y = 0 from hy] at he
      exact (smul_eq_zero.mp he.symm).resolve_left hn
    refine ⟨hza, ?_, ?_⟩
    · filter_upwards [hp, hne] with y hy hn
      have he := pressure_factor request l k (reference l) y
      rw [show (((parameters l).copyData ActualPrimaryBounds.strip request).localized k).pressure
        (reference l) y = 0 from hy] at he
      exact (smul_eq_zero.mp he.symm).resolve_left hn
    · filter_upwards [hza] with y hy
      simp only [potential, hy, CurlClassBounds.normalCoefficient, CurlClassBounds.normalCross,
        map_zero, smul_zero]

/-- The band index is frozen only discretely, at the original label's own
reference. This is not an extension of a fixed reference to all bands. -/
noncomputable def ownField {E : Type} [Zero E]
    (f : Label B N0 → Copy → ℕ → Full → E)
    (i : Label B N0 × Copy) (n : ℕ) (x : Full) : E :=
  if n = reference i.1 then f i.1 i.2 n x else 0

theorem ownField_reference {E : Type} [Zero E]
    (f : Label B N0 → Copy → ℕ → Full → E) (i : Label B N0 × Copy) :
    ownField f i (reference i.1) = f i.1 i.2 (reference i.1) := by
  funext x
  exact ite_eq_left rfl

theorem ownField_other {E : Type} [Zero E]
    (f : Label B N0 → Copy → ℕ → Full → E) (i : Label B N0 × Copy)
    {n : ℕ} (hn : n ≠ reference i.1) : ownField f i n = fun _ => 0 := by
  funext x
  exact ite_eq_right hn

theorem ownField_uniform {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Label B N0 → Copy → ℕ → Full → E} {α : ℝ}
    {w : Label B N0 → ℕ → Full → ℝ}
    (hw : ∀ l n x, x ∈ fullStrip.domain → 0 ≤ w l n x)
    (hf : PeriodizedWaveBounds.UniformLocalJets fullStrip w α phaseCell (fun l n k => f l k n))
    (hc : ∀ l k x, x ∈ fullStrip.domain →
      x ∈ phaseCell l (reference l) k ∨ f l k (reference l) =ᶠ[𝓝 x] fun _ => 0) :
    LabelSumBounds.UniformClass fullStrip (fun i => w i.1) α (ownField f) := by
  classical
  refine ⟨fun i => hw i.1, ?_, ?_⟩
  · intro i n x hx
    by_cases hn : n = reference i.1
    · subst n
      rw [ownField_reference]
      rcases hc i.1 i.2 x hx with hcell | hz
      · exact (hf.smooth i.1 _ i.2 x hx hcell).contDiffWithinAt
      · have hh : ContDiffAt ℝ ∞ (f i.1 i.2 (reference i.1)) x :=
          contDiffAt_const.congr_of_eventuallyEq hz
        exact hh.contDiffWithinAt
    · rw [ownField_other f i hn]
      exact contDiffWithinAt_const
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro i n x hx j hj
    by_cases hn : n = reference i.1
    · subst n
      rw [ownField_reference]
      rcases hc i.1 i.2 x hx with hcell | hz
      · exact hb i.1 _ i.2 x hx hcell j hj
      · rw [PeriodizedWaveBounds.jets_eq_of_germ hz j]
        simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using
          majorant_nonneg fullStrip (w i.1) α hC p (reference i.1) x (hw i.1 _ x hx)
    · rw [ownField_other f i hn]
      simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact majorant_nonneg fullStrip (w i.1) α hC p n x (hw i.1 n x hx)

theorem own_potential_pressure_class {β : ℝ} {request : ℕ → Full → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) :
    LabelSumBounds.UniformClass fullStrip
      (fun (i : Label B N0 × Copy) n x => Real.sqrt (fullStrip.zeta x) * envelope i.1 n x) (β + 1)
      (ownField (potential request)) ∧
    LabelSumBounds.UniformClass fullStrip
      (fun (i : Label B N0 × Copy) n x => Real.sqrt (fullStrip.zeta x) * envelope i.1 n x) (β + 1)
      (ownField (pressure request)) := by
  have hw (l : Label B N0) n x (_ : x ∈ fullStrip.domain) :=
    mul_nonneg (Real.sqrt_nonneg (fullStrip.zeta x)) (ActualPrimaryBounds.fullEnvelope_nonneg (l.2,
      l.1) n x)
  refine ⟨ownField_uniform hw (potential_jets hR) ?_, ownField_uniform hw (localized_jets hR).2 ?_⟩
  · intro l k x hx
    exact (own_phaseCell_or_zero request l k hx).imp id (fun hh => hh.2.2)
  · intro l k x hx
    exact (own_phaseCell_or_zero request l k hx).imp id (fun hh => hh.2.1)

theorem own_zero_outside (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (l : Label B N0) (k : Copy) {x : Full}
    (hx : x ∈ ActualWaveRegularity.fullDomain standardRegion)
    (hout : ActualWaveRegularityData.radius x ∉ Ioo
      (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)) :
    amplitude request l k (reference l) x = 0 ∧ pressure request l k (reference l) x = 0 ∧
      potential request l k (reference l) x = 0 := by
  have hz := ActualWaveRegularityData.signed_raw_zero_outside l ActualPrimaryBounds.strip request
    (reference l) k hx hout
  have hne := dyadic_reference_nonzero l k hx
  have ha := raw_amplitude_factor request l k (reference l) x
  have hp := raw_pressure_factor request l k (reference l) x
  rw [show (((parameters l).copyData ActualPrimaryBounds.strip request).raw k).amplitude
    (reference l) x = 0 from hz.1] at ha
  rw [show (((parameters l).copyData ActualPrimaryBounds.strip request).raw k).pressure
    (reference l) x = 0 from hz.2] at hp
  have hza := (smul_eq_zero.mp ha.symm).resolve_left hne
  have hzp := (smul_eq_zero.mp hp.symm).resolve_left hne
  simp only [amplitude, pressure, potential, hza, hzp, CurlClassBounds.normalCoefficient,
    CurlClassBounds.normalCross, map_zero, smul_zero, and_self]

/-- The full-strip families supplied to radial continuation have literal
zero values outside the original open radial interval, in every band. -/
theorem ownFields_zero_outside (request : ℕ → Full → SignedWaveUpdate.Vec2)
    (i : Label B N0 × Copy) (n : ℕ) {x : Full}
    (hx : x ∈ ActualWaveRegularity.fullDomain standardRegion)
    (hout : ActualWaveRegularityData.radius x ∉ Ioo
      (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)) :
    ownField (amplitude request) i n x = 0 ∧
      ownField (pressure request) i n x = 0 ∧ ownField (potential request) i n x = 0 := by
  by_cases hn : n = reference i.1
  · subst n
    simp only [ownField_reference]
    exact own_zero_outside request i.1 i.2 hx hout
  · simp only [ownField_other _ i hn, and_self]

/-! ## The request is the measured current residual -/

/-- The actual residual-to-request construction supplies the unmasked
potential and pressure estimates. No bound for either output is assumed. -/
theorem actual_own_potential_pressure_class (G : SignedMeanGain.Geometry)
    (hs : G.strip = ActualPrimaryBounds.strip)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (hθ : MeanClass G.strip α (u.thetaResidual c))
    (hz : MeanClass G.strip α (u.axialResidual c)) :
    let request := LocalSignedRequest.fullRequest G.strip G.patch G.coord c u
    LabelSumBounds.UniformClass fullStrip
      (fun (i : Label B N0 × Copy) n x => Real.sqrt (fullStrip.zeta x) * envelope i.1 n x) α
      (ownField (potential request)) ∧
    LabelSumBounds.UniformClass fullStrip
      (fun (i : Label B N0 × Copy) n x => Real.sqrt (fullStrip.zeta x) * envelope i.1 n x) α
      (ownField (pressure request)) := by
  dsimp only
  have hr := fullRequest_jets_from_residuals G c u α H hfixed hθ hz
    (phaseCell (B := B) (N0 := N0))
  have hr' : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) (α - 1) (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => LocalSignedRequest.fullRequest G.strip G.patch G.coord c u n x q) := by
    simp only [hs] at hr ⊢
    exact hr
  simpa only [sub_add_cancel] using own_potential_pressure_class hr'

/-- In particular the literal reconstructed cycle invariant is sufficient;
the only analytic output used is its already measured residual class. -/
theorem invariant_own_potential_pressure_class {ι : Type} (G : SignedMeanGain.Geometry)
    (hs : G.strip = ActualPrimaryBounds.strip)
    (c : CorrectionState.Context Point) (primary : ι → CorrectionState.HarmonicBlock Point)
    (P : ι → ℕ → Point → ℝ) (labelCarrier : ι → ℕ → Set Point)
    (σ : ℝ) (u : CorrectionStep.CycleState ι)
    (H : CorrectionStep.CycleAnalyticInvariant G c primary P labelCarrier σ u) :
    let request := LocalSignedRequest.fullRequest G.strip G.patch G.coord c u.state
    LabelSumBounds.UniformClass fullStrip
      (fun (i : Label B N0 × Copy) n x => Real.sqrt (fullStrip.zeta x) * envelope i.1 n x) (1 + σ)
      (ownField (potential request)) ∧
    LabelSumBounds.UniformClass fullStrip
      (fun (i : Label B N0 × Copy) n x => Real.sqrt (fullStrip.zeta x) * envelope i.1 n x) (1 + σ)
      (ownField (pressure request)) :=
  actual_own_potential_pressure_class G hs c u.state (1 + σ) H.primitives H.reconstructed
    H.raw_mean_bounds.1 H.raw_mean_bounds.2

end NavierStokes.ActualSignedUnmaskedBounds
