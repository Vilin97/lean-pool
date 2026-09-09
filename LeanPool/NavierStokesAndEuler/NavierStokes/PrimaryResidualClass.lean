/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicWaveInteraction
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedWaveUpdate

/-!
# Initial primary residual classes

The primary coefficient and its Gaussian error are the actual cutoff/curl
construction. The improved nonlinear bound uses the exact divergence of that
curl, before projecting the literal residual into its finite harmonics.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PrimaryResidualClass

open Set Function Filter HarmonicCalculus HarmonicFields WeightedClasses
open CopyAngularInvariance
open scoped Topology ContDiff BigOperators ComplexConjugate


variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The context's literal graph directions lifted to the explicit angle. -/
noncomputable def directions (c : CorrectionState.Context D) :
    LinearWaveBounds.GraphDirections (D × ℝ) where
  radial := (c.operators.eR, 0)
  auxiliary := (c.operators.vR, 0)
  axial := (c.operators.eZ, 0)
  angular := (0, 1)
  slow := (c.operators.eT, 0)
  fast := (c.operators.vT, 0)
  radialScale := c.operators.radialFrequency
  fastScale := c.operators.fastCoefficient
  radialProfile := fun p => c.operators.radialProfile p.1

theorem directions_radial (c : CorrectionState.Context D) (n : ℕ) :
    (directions c).radialField n =
      HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial := by
  funext p
  simp [directions, LinearWaveBounds.GraphDirections.radialField,
    HarmonicResidual.liftDirection, HarmonicResidual.contextFrame, smul_smul]

theorem directions_axial (s : StripData D) (c : CorrectionState.Context D)
    (hε : s.epsilon = c.operators.epsilon) (n : ℕ) :
    (directions c).axialField (HarmonicWaveInteraction.productStrip s) n =
      HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial := by
  funext p
  simp [directions, LinearWaveBounds.GraphDirections.axialField,
    HarmonicResidual.liftDirection, HarmonicResidual.contextFrame,
    HarmonicWaveInteraction.productStrip, HarmonicWaveInteraction.pullbackStrip, hε]

theorem directions_time (s : StripData D) (c : CorrectionState.Context D)
    (hε : s.epsilon = c.operators.epsilon) (n : ℕ) :
    LinearWaveResidual.timeDirection ((HarmonicWaveInteraction.productStrip s).epsilon n)
      ((directions c).fastField n) (fun _ => (directions c).slow) =
        HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).time := by
  funext p
  simp [directions, LinearWaveBounds.GraphDirections.fastField, LinearWaveResidual.timeDirection,
    HarmonicResidual.liftDirection, HarmonicResidual.contextFrame,
    HarmonicWaveInteraction.productStrip, HarmonicWaveInteraction.pullbackStrip, hε]

/-- Matching concerns primitive fields, never a residual or a residual bound. -/
structure Matches (s : StripData D) (c : CorrectionState.Context D)
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) : Prop where
  epsilon : s.epsilon = c.operators.epsilon
  radius : a.radius = fun _ p => c.operators.radius p.1
  base : ∀ n, LinearWaveResidual.complexBase (a.radius n) (a.radialBase n)
    (a.frequencyBase n) (a.axialBase n) = fun p => HarmonicResidual.contextBase c n p.1

/-- Primitive angular translation data for one primary field. -/
structure AngularData (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (ψ : ℕ → D × ℝ → ℝ) : Prop where
  radius : ∀ n, Invariant ((0 : D), 1) (a.radius n)
  radialBase : ∀ n, Invariant ((0 : D), 1) (a.radialBase n)
  frequencyBase : ∀ n, Invariant ((0 : D), 1) (a.frequencyBase n)
  axialBase : ∀ n, Invariant ((0 : D), 1) (a.axialBase n)
  phase : ∀ n, ∃ m, AffinePhase ((0 : D), 1) m (a.phase n)
  amplitude : ∀ n, Invariant ((0 : D), 1) (a.amplitude n)
  pressure : ∀ n, Invariant ((0 : D), 1) (a.pressure n)
  cutoff : ∀ n, Invariant ((0 : D), 1) (ψ n)

theorem invariant_fst {E : Type} (f : D → E) :
    Invariant ((0 : D), 1) (fun p : D × ℝ => f p.1) := by
  intro p t
  simp

theorem directions_radial_invariant (c : CorrectionState.Context D) (n : ℕ) :
    Invariant ((0 : D), 1) ((directions c).radialField n) := by
  rw [directions_radial]
  exact invariant_fst (fun x => ((HarmonicResidual.contextFrame c n).radial x, (0 : ℝ)))

theorem AngularData.corrected_amplitude {a : LinearWaveBounds.WaveCoefficients (D × ℝ)}
    {ψ : ℕ → D × ℝ → ℝ} (ha : AngularData a ψ) (s : StripData D)
    (c : CorrectionState.Context D) (n : ℕ) :
    Invariant ((0 : D), 1)
      ((a.corrected (HarmonicWaveInteraction.productStrip s) (directions c) ψ).amplitude n) :=
  corrected_amplitude_invariant ψ ha.radius (directions_radial_invariant c)
    (fun _ => Invariant.const _) ha.phase ha.amplitude ha.cutoff n

theorem AngularData.corrected_pressure {a : LinearWaveBounds.WaveCoefficients (D × ℝ)}
    {ψ : ℕ → D × ℝ → ℝ} (ha : AngularData a ψ) (s : StripData D)
    (c : CorrectionState.Context D) (n : ℕ) :
    Invariant ((0 : D), 1)
      ((a.corrected (HarmonicWaveInteraction.productStrip s) (directions c) ψ).pressure n) :=
  corrected_pressure_invariant ψ ha.pressure ha.cutoff n

section InvariantOperators

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {θ : X} {R b F G : X → ℝ} {Vr Vθ Vz Vf Vs : X → X}
  {Φ : X → ℝ} {m : ℝ} {a : X → ComplexVector} {p : X → ℂ}

theorem principal_invariant (hR : Invariant θ R) (hF : Invariant θ F)
    (hG : Invariant θ G) (hr : Invariant θ Vr) (hθ : Invariant θ Vθ)
    (hz : Invariant θ Vz) (hf : Invariant θ Vf)
    (hΦ : AffinePhase θ m Φ) (ha : Invariant θ a) (hp : Invariant θ p)
    (ε k : ℝ) : Invariant θ (LinearWaveResidual.principal ε k R F G Vr Vθ Vz Vf Φ a p) := by
  have hN := phaseNormal_invariant hR hr hθ hz hΦ
  intro x t
  funext i
  simp only [LinearWaveResidual.principal, LinearWaveResidual.shear,
    (ha.component i).along hf x t, hF.along hr x t, hG.along hr x t,
    hN x t, hR x t, hF x t, ha x t, hp x t]

theorem remainder_invariant (hR : Invariant θ R) (hb : Invariant θ b)
    (hF : Invariant θ F) (hG : Invariant θ G) (hr : Invariant θ Vr)
    (hθ : Invariant θ Vθ) (hz : Invariant θ Vz) (hf : Invariant θ Vf)
    (hs : Invariant θ Vs) (hΦ : AffinePhase θ m Φ) (ha : Invariant θ a)
    (hp : Invariant θ p) (ε k : ℝ) :
    Invariant θ (LinearWaveResidual.remainder ε k R b F G Vr Vθ Vz Vf Vs Φ a p) := by
  have hN := phaseNormal_invariant hR hr hθ hz hΦ
  have hB := base_invariant hR hb hF hG
  have ht : Invariant θ (LinearWaveResidual.timeDirection ε Vf Vs) :=
    hf.map₂ hs (fun v w => v - ε • w)
  intro x t
  funext i
  simp only [LinearWaveResidual.remainder, LinearWaveResidual.slowTransport,
    LinearWaveResidual.materialPhaseDefect, LinearWaveResidual.baseDerivativeRemainder,
    LinearWaveResidual.strippedPressureGradient, LinearWaveResidual.viscousRemainder,
    (ha.component i).along hs x t, (ha.component i).along hr x t,
    (ha.component i).along hz x t, ((ha.component i).along hr).along hr x t,
    ((ha.component i).along hz).along hz x t, hΦ.along_invariant ht x t,
    hΦ.along_invariant hr x t, hΦ.along_invariant hθ x t, hΦ.along_invariant hz x t,
    hb.along hr x t, (hB.component i).along hz x t, hp.along hr x t, hp.along hz x t,
    (hN.map (fun N => N 0)).along hr x t, (hN.map (fun N => N 2)).along hz x t,
    hR x t, hb x t, hF x t, hG x t, hN x t, ha x t]

end InvariantOperators

theorem AngularData.constructedGood {a : LinearWaveBounds.WaveCoefficients (D × ℝ)}
    {ψ : ℕ → D × ℝ → ℝ} (ha : AngularData a ψ) (s : StripData D)
    (c : CorrectionState.Context D) (n : ℕ) :
    Invariant ((0 : D), 1)
      (a.constructedGood (HarmonicWaveInteraction.productStrip s) (directions c) ψ n) := by
  obtain ⟨m, hm⟩ := ha.phase n
  have hc : Invariant ((0 : D), 1)
      (((a.withCutoff ψ).curlCorrection (HarmonicWaveInteraction.productStrip s) (directions c)) n)
          :=
    curlRemainder_invariant (ha.radius n) (directions_radial_invariant c n)
      (Invariant.const _) (Invariant.const _)
      (coefficient_invariant (ha.radius n) (directions_radial_invariant c n)
        (Invariant.const _) (Invariant.const _) hm
        ((ha.cutoff n).map₂ (ha.amplitude n) (fun r v => r • v))) (a.frequency n)
  exact (principal_invariant (ha.radius n) (ha.frequencyBase n) (ha.axialBase n)
    (directions_radial_invariant c n) (Invariant.const _) (Invariant.const _)
    (Invariant.const _) hm hc (Invariant.const _) _ _).map₂
      (remainder_invariant (ha.radius n) (ha.radialBase n) (ha.frequencyBase n) (ha.axialBase n)
        (directions_radial_invariant c n) (Invariant.const _) (Invariant.const _)
        (Invariant.const _) (Invariant.const _) hm (ha.corrected_amplitude s c n)
        (ha.corrected_pressure s c n) _ _) (· + ·)

/-- Quantitative and geometric inputs concern the primitive primary wave.
In particular neither a good-residual class nor a residual identity is a field. -/
structure Inputs (s : StripData D) (P : ℕ → D → ℝ) (κ : ℝ)
    (c : CorrectionState.Context D) (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (ψ : ℕ → D × ℝ → ℝ) (kp : ℕ → ℤ) : Prop where
  matching : Matches s c a
  operators : MeanIncrementBounds.OperatorBounds s c.operators κ
  loss_le : κ ≤ 1 / 10
  coefficients : LinearWaveBounds.InputBounds (HarmonicWaveInteraction.productStrip s)
    (fun n p => P n p.1) (1 / 2) κ (directions c) a
  cutoff : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 ψ
  angular : AngularData a ψ
  phase_smooth : ∀ n, ContDiffOn ℝ ∞ (a.phase n) (HarmonicWaveInteraction.productStrip s).domain
  phase_split : ∀ n x θ, a.frequency n * a.phase n (x, θ) =
    a.frequency n * a.phase n (x, 0) + (kp n : ℝ) * θ
  frequency_ne : ∀ n, a.frequency n ≠ 0
  angular_ne : ∀ n, kp n ≠ 0
  normal_jets : PhaseJetBounds.PolynomialJets
    (CurlClassBounds.phaseDomain (HarmonicWaveInteraction.productStrip s))
    (a.normal (HarmonicWaveInteraction.productStrip s) (directions c))
  normal_bounds : ∃ b M : ℝ, 0 < b ∧
    (∀ n p, p.1 ∈ s.domain → b ≤ ‖a.normal (HarmonicWaveInteraction.productStrip s) (directions c)
        n p‖) ∧
    (∀ n p, p.1 ∈ s.domain → ‖a.normal (HarmonicWaveInteraction.productStrip s) (directions c) n p‖
        ≤ M)
  inverse_frequency : BandBound (HarmonicWaveInteraction.productStrip s) (1 / 2)
    (fun n => 1 / a.frequency n)
  geometry : ∀ n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip
      s).domain
    (a.radius n) ((directions c).radialField n) (fun _ => (directions c).angular)
    ((directions c).axialField (HarmonicWaveInteraction.productStrip s) n)
  tangent : ∀ n p, p.1 ∈ s.domain →
    normalDot (a.normal (HarmonicWaveInteraction.productStrip s) (directions c) n p) (a.amplitude n
        p) = 0
  principal_zero : ∀ n p, p.1 ∈ s.domain → ψ n p ≠ 0 →
    a.principal (HarmonicWaveInteraction.productStrip s) (directions c) n p = 0
  profile_nonneg : ∀ n x, x ∈ s.domain → 0 ≤ P n x
  profile_le_one : ∀ n x, x ∈ s.domain → P n x ≤ 1
  radius_pos : ∀ x ∈ s.domain, 0 < c.operators.radius x

/-- Corrected, given by `a.corrected (HarmonicWaveInteraction.productStrip s) (directions c) ψ`. -/
noncomputable def corrected (s : StripData D) (c : CorrectionState.Context D)
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) (ψ : ℕ → D × ℝ → ℝ) :=
  a.corrected (HarmonicWaveInteraction.productStrip s) (directions c) ψ

/-- Primary block, given by `SignedWaveUpdate.blockOfCoefficients (corrected s c a ψ) kp`. -/
noncomputable def primaryBlock (s : StripData D) (c : CorrectionState.Context D)
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) (ψ : ℕ → D × ℝ → ℝ) (kp : ℕ → ℤ) :=
  SignedWaveUpdate.blockOfCoefficients (corrected s c a ψ) kp

/-- Gaussian coefficients, defined pointwise by `ErrorHarmonics.conjugatePair 1 (fun x =>
LinearWaveBounds.excludedSlotError (directions c) ψ a.amplitude 0 n (x, 0) i)`. -/
noncomputable def gaussianCoefficients (c : CorrectionState.Context D)
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) (ψ : ℕ → D × ℝ → ℝ) :
    HarmonicResidual.BlockCoefficients D :=
  fun n i => ErrorHarmonics.conjugatePair 1
    (fun x => LinearWaveBounds.excludedSlotError (directions c) ψ a.amplitude 0 n (x, 0) i)

/-- Good coefficients, defined pointwise by `ErrorHarmonics.conjugatePair 1 (fun x =>
a.constructedGood (HarmonicWaveInteraction.productStrip s) (directions c) ψ n (x, 0) i)`. -/
noncomputable def goodCoefficients (s : StripData D) (c : CorrectionState.Context D)
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) (ψ : ℕ → D × ℝ → ℝ) :
    HarmonicResidual.BlockCoefficients D :=
  fun n i => ErrorHarmonics.conjugatePair 1
    (fun x => a.constructedGood (HarmonicWaveInteraction.productStrip s) (directions c) ψ n (x, 0)
        i)

theorem wave_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ} {f : ℕ → D × ℝ → E}
    (hf : WaveClass (HarmonicWaveInteraction.productStrip s) (fun n p => P n p.1) α f) :
    WaveClass s P α (fun n x => f n (x, 0)) :=
  HarmonicWaveInteraction.class_slice (s := s) (w := fun n x => Real.sqrt (s.zeta x) * P n x) hf

namespace Inputs

variable {s : StripData D} {P : ℕ → D → ℝ} {κ : ℝ} {c : CorrectionState.Context D}
  {a : LinearWaveBounds.WaveCoefficients (D × ℝ)} {ψ : ℕ → D × ℝ → ℝ} {kp : ℕ → ℤ}
  (h : Inputs s P κ c a ψ kp)

include h

theorem corrected_bounds : LinearWaveBounds.InputBounds (HarmonicWaveInteraction.productStrip s)
    (fun n p => P n p.1) (1 / 2) κ (directions c) (corrected s c a ψ) := by
  obtain ⟨b, M, hb, hlo, hhi⟩ := h.normal_bounds
  have hc := (h.coefficients.with_cutoff h.cutoff).curlCorrection_class h.matching.radius
    h.normal_jets hb hlo hhi h.inverse_frequency
  exact (h.coefficients.with_cutoff h.cutoff).add_curl_amplitude (by linarith [h.loss_le])
    (fun i => CurlClassBounds.class_component hc i)

theorem good_class : WaveClass (HarmonicWaveInteraction.productStrip s) (fun n p => P n p.1)
    (1 - 3 * κ) (a.constructedGood (HarmonicWaveInteraction.productStrip s) (directions c) ψ) := by
  obtain ⟨b, M, hb, hlo, hhi⟩ := h.normal_bounds
  have hg := h.coefficients.constructed_goodCoefficient_class (by linarith [h.loss_le]) h.cutoff
    h.matching.radius h.normal_jets hb hlo hhi h.inverse_frequency
  convert! hg using 1
  ring

theorem good_coefficients_class (j : ℤ) (i : Fin 3) : WaveClass s P (1 - 3 * κ)
    (fun n x => goodCoefficients s c a ψ n i j x) :=
  SignedWaveUpdate.conjugatePair_class
    (wave_slice (CurlClassBounds.class_component h.good_class i)) j

theorem primary_bounds : (primaryBlock s c a ψ kp).WaveBounds s P (1 / 2) := by
  intro i j _
  exact SignedWaveUpdate.conjugatePair_class
    (wave_slice (h.corrected_bounds.amplitude i)) j

theorem primary_pressure : (primaryBlock s c a ψ kp).PressureBounds s P 1 := by
  intro j _
  have hp := SignedWaveUpdate.conjugatePair_class
    (wave_slice h.corrected_bounds.pressure) j
  simp only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at hp
  exact hp

theorem exact_conditions : LinearWaveBounds.ExactConditions (HarmonicWaveInteraction.productStrip s)
    (directions c) (corrected s c a ψ) :=
  exactConditions_corrected_of_invariants ψ h.phase_smooth
    (fun n => (h.geometry n).radius_ne) (fun n => (h.geometry n).radial_radius)
    h.angular.radius h.angular.radialBase h.angular.frequencyBase h.angular.axialBase
    (directions_radial_invariant c) (fun _ => Invariant.const _) h.angular.phase
    h.angular.amplitude h.angular.pressure h.angular.cutoff

theorem normal_ne (n : ℕ) (p : D × ℝ) (hp : p.1 ∈ s.domain) :
    a.normal (HarmonicWaveInteraction.productStrip s) (directions c) n p ≠ 0 := by
  obtain ⟨b, M, hb, hlo, hhi⟩ := h.normal_bounds
  intro hn
  have := hlo n p hp
  rw [hn, norm_zero] at this
  linarith

theorem corrected_divergence (n : ℕ) (p : D × ℝ) (hp : p.1 ∈ s.domain) :
    cylindricalDivergence (a.radius n) ((directions c).radialField n)
      (fun _ => (directions c).angular) ((directions c).axialField
          (HarmonicWaveInteraction.productStrip s) n)
      (vectorMode (a.frequency n) (a.phase n) ((corrected s c a ψ).amplitude n)) p = 0 :=
  LinearWaveBounds.corrected_divergence h.coefficients h.cutoff n (h.geometry n)
    (h.frequency_ne n) (h.phase_smooth n) (h.normal_ne n) (h.tangent n) hp

theorem linear_identity (n : ℕ) (p : D × ℝ) (hp : p.1 ∈ s.domain) :
    (corrected s c a ψ).harmonicResidual (HarmonicWaveInteraction.productStrip s) (directions c) n
        p =
      vectorMode (a.frequency n) (a.phase n)
        (a.constructedGood (HarmonicWaveInteraction.productStrip s) (directions c) ψ n) p +
      vectorMode (a.frequency n) (a.phase n)
        (LinearWaveBounds.excludedSlotError (directions c) ψ a.amplitude 0 n) p := by
  obtain ⟨b, M, hb, hlo, hhi⟩ := h.normal_bounds
  let f := (a.withCutoff ψ).curlCorrection (HarmonicWaveInteraction.productStrip s) (directions c)
  have hf : WaveClass (HarmonicWaveInteraction.productStrip s) (fun n p => P n p.1)
      (1 / 2 + 1 / 2 - κ) f :=
    (h.coefficients.with_cutoff h.cutoff).curlCorrection_class h.matching.radius
      h.normal_jets hb hlo hhi h.inverse_frequency
  have hadd := (h.coefficients.with_cutoff h.cutoff).principal_add_curl
    (fun i => CurlClassBounds.class_component hf i) n hp
  have hcut := LinearWaveBounds.principal_cutoff h.coefficients ψ 0 n hp
    (((h.cutoff.smooth n).contDiffAt
      ((HarmonicWaveInteraction.productStrip s).isOpen_domain.mem_nhds hp)).differentiableAt (by
          simp))
  have hzero : ψ n p • a.principal (HarmonicWaveInteraction.productStrip s) (directions c) n p = 0
      := by
    by_cases hψ : ψ n p = 0
    · rw [hψ, zero_smul]
    · rw [h.principal_zero n p hp hψ, smul_zero]
  simp only [Pi.zero_apply, add_zero, hzero, zero_add] at hcut
  have he : (corrected s c a ψ).principal (HarmonicWaveInteraction.productStrip s) (directions c) n
      p +
      (corrected s c a ψ).remainder (HarmonicWaveInteraction.productStrip s) (directions c) n p =
      a.constructedGood (HarmonicWaveInteraction.productStrip s) (directions c) ψ n p +
        LinearWaveBounds.excludedSlotError (directions c) ψ a.amplitude 0 n p := by
    change ((a.withCutoff ψ).addAmplitude f).principal _ _ n p + _ = _
    rw [hadd, hcut]
    change _ + a.principalVelocity (HarmonicWaveInteraction.productStrip s) (directions c) f n p +
      ((a.withCutoff ψ).addAmplitude f).remainder _ _ n p =
      (a.principalVelocity (HarmonicWaveInteraction.productStrip s) (directions c) f n p +
        ((a.withCutoff ψ).addAmplitude f).remainder _ _ n p) + _
    abel
  rw [LinearWaveBounds.harmonicResidual_eq h.corrected_bounds h.exact_conditions n hp]
  ext i
  have hei := congrFun he i
  simp only [Pi.add_apply] at hei
  change ((_ + _) * carrier (a.frequency n) (a.phase n) p) = _
  rw [hei, add_mul]
  rfl

end Inputs

/-- Real projection, given by `Complex.ofRealCLM.comp Complex.reCLM`. -/
noncomputable def realProjection : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

@[simp] theorem realProjection_apply (z : ℂ) : realProjection z = (z.re : ℂ) := rfl

theorem divergence_map {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : ℂ →L[ℝ] ℂ) (R : X → ℝ) (Vr Vθ Vz : X → X)
    {v : X → ComplexVector} {x : X}
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    cylindricalDivergence R Vr Vθ Vz (fun y i => L (v y i)) x =
      L (cylindricalDivergence R Vr Vθ Vz v x) := by
  simp only [cylindricalDivergence, LinearWaveResidual.along_map L _ (hv _), map_add, map_smul]

theorem linearResidual_realProjection {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {U : Set X} (hU : IsOpen U) (ε : ℝ) (R : X → ℝ) {Vr Vθ Vz : X → X}
    (Vt : X → X) (hVr : ContDiffOn ℝ ∞ Vr U) (hVθ : ContDiffOn ℝ ∞ Vθ U)
    (hVz : ContDiffOn ℝ ∞ Vz U) {B : X → Fin 3 → ℝ} {v : X → ComplexVector} {p : X → ℂ}
    (hv : ∀ i, ContDiffOn ℝ ∞ (fun y => v y i) U) {x : X}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x)
    (hp : DifferentiableAt ℝ p x) (hx : x ∈ U) (i : Fin 3) :
    (LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt (LinearWaveResidual.realLift B)
      (fun y j => realProjection (v y j)) (fun y => realProjection (p y)) x i).re =
    (LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt (LinearWaveResidual.realLift B) v p x i).re
        := by
  have h0 := LinearWaveResidual.realMap_linearResidual Complex.reCLM ε R Vt hU hVr hVθ hVz
    hv hB hp hx
  have h1 := LinearWaveResidual.realMap_linearResidual Complex.reCLM ε R Vt hU hVr hVθ hVz
    (fun j => realProjection.contDiff.comp_contDiffOn (hv j)) hB
    (realProjection.differentiableAt.comp x hp) hx
  exact (congrFun h1 i).trans (by simpa using (congrFun h0 i).symm)

theorem pair_field_of_invariant {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X × ℝ → ℂ} {Φ : X × ℝ → ℝ} (k : ℝ) (kp : ℤ)
    (hf : Invariant ((0 : X), 1) f)
    (hΦ : ∀ x θ, k * Φ (x, θ) = k * Φ (x, 0) + (kp : ℝ) * θ) (p : X × ℝ) :
    field (ErrorHarmonics.conjugatePair 1 (fun x => f (x, 0))) k
      (fun x => Φ (x, 0)) kp p = realProjection (mode k Φ f p) := by
  rw [ErrorHarmonics.field_conjugatePair, ← hΦ p.1 p.2]
  have hc := character_eq_carrier 1 k Φ p
  simp only [Int.cast_one, mul_one] at hc
  rw [hc]
  change ((f (p.1, 0) * carrier k Φ p).re : ℂ) = ((f p * carrier k Φ p).re : ℂ)
  rw [invariant_eq_zeroSlice hf p.1 p.2]

theorem excluded_invariant {a : LinearWaveBounds.WaveCoefficients (D × ℝ)}
    {ψ : ℕ → D × ℝ → ℝ} (ha : AngularData a ψ) (c : CorrectionState.Context D) (n : ℕ) :
    Invariant ((0 : D), 1) (LinearWaveBounds.excludedSlotError (directions c) ψ a.amplitude 0 n) :=
        by
  have hf : Invariant ((0 : D), 1) ((directions c).fastField n) :=
    Invariant.const ((directions c).fastScale n • (directions c).fast)
  intro x t
  simp only [LinearWaveBounds.excludedSlotError, LinearWaveBounds.GraphDirections.Dfast,
    (ha.cutoff n).along hf x t, ha.cutoff n x t, ha.amplitude n x t,
    Pi.zero_apply]

namespace Inputs

variable {s : StripData D} {P : ℕ → D → ℝ} {κ : ℝ} {c : CorrectionState.Context D}
  {a : LinearWaveBounds.WaveCoefficients (D × ℝ)} {ψ : ℕ → D × ℝ → ℝ} {kp : ℕ → ℤ}
  (h : Inputs s P κ c a ψ kp)

include h

theorem primary_field (n : ℕ) (p : D × ℝ) (i : Fin 3) :
    field ((primaryBlock s c a ψ kp).velocity n i) (a.frequency n)
      (fun x => a.phase n (x, 0)) (kp n) p =
    realProjection (vectorMode (a.frequency n) (a.phase n) ((corrected s c a ψ).amplitude n) p i) :=
  pair_field_of_invariant _ _ ((h.angular.corrected_amplitude s c n).component i) (h.phase_split n)
      p

theorem pressure_field (n : ℕ) (p : D × ℝ) :
    field ((primaryBlock s c a ψ kp).pressure n) (a.frequency n)
      (fun x => a.phase n (x, 0)) (kp n) p =
    realProjection (mode (a.frequency n) (a.phase n) ((corrected s c a ψ).pressure n) p) :=
  pair_field_of_invariant _ _ (h.angular.corrected_pressure s c n) (h.phase_split n) p

theorem good_field (n : ℕ) (p : D × ℝ) (i : Fin 3) :
    field (goodCoefficients s c a ψ n i) (a.frequency n)
      (fun x => a.phase n (x, 0)) (kp n) p =
    realProjection (vectorMode (a.frequency n) (a.phase n)
      (a.constructedGood (HarmonicWaveInteraction.productStrip s) (directions c) ψ n) p i) :=
  pair_field_of_invariant _ _ ((h.angular.constructedGood s c n).component i) (h.phase_split n) p

theorem gaussian_field (n : ℕ) (p : D × ℝ) (i : Fin 3) :
    field (gaussianCoefficients c a ψ n i) (a.frequency n)
      (fun x => a.phase n (x, 0)) (kp n) p =
    realProjection (vectorMode (a.frequency n) (a.phase n)
      (LinearWaveBounds.excludedSlotError (directions c) ψ a.amplitude 0 n) p i) :=
  pair_field_of_invariant _ _ ((excluded_invariant h.angular c n).component i) (h.phase_split n) p

theorem phase_slow_smooth (n : ℕ) : ContDiffOn ℝ ∞ (fun x => a.phase n (x, 0)) s.domain :=
  (h.phase_smooth n).comp (HarmonicWaveInteraction.inclusion (D := D)).contDiff.contDiffOn
    (fun _ hx => hx)

theorem primary_smooth (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients s.domain ((primaryBlock s c a ψ kp).velocity n i) := by
  intro j
  exact (SignedWaveUpdate.conjugatePair_class
    (wave_slice (h.corrected_bounds.amplitude i)) j).smooth n

theorem pressure_smooth (n : ℕ) :
    HarmonicResidual.SmoothCoefficients s.domain ((primaryBlock s c a ψ kp).pressure n) := by
  intro j
  exact (SignedWaveUpdate.conjugatePair_class
    (wave_slice h.corrected_bounds.pressure) j).smooth n

theorem raw_velocity_smooth (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun p => vectorMode (a.frequency n) (a.phase n)
      ((corrected s c a ψ).amplitude n) p i) (HarmonicWaveInteraction.productStrip s).domain :=
  contDiffOn_mode _ (h.phase_smooth n) ((h.corrected_bounds.amplitude i).smooth n)

theorem raw_pressure_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (mode (a.frequency n) (a.phase n) ((corrected s c a ψ).pressure n))
      (HarmonicWaveInteraction.productStrip s).domain :=
  contDiffOn_mode _ (h.phase_smooth n) (h.corrected_bounds.pressure.smooth n)

end Inputs

/-- Linear coefficients as an element of `HarmonicResidual.BlockCoefficients D`. -/
noncomputable def linearCoefficients (s : StripData D) (c : CorrectionState.Context D)
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) (ψ : ℕ → D × ℝ → ℝ) (kp : ℕ → ℤ) :
    HarmonicResidual.BlockCoefficients D := fun n =>
  HarmonicResidual.linearResidual (HarmonicResidual.contextFrame c n) (a.frequency n)
    (fun x => a.phase n (x, 0)) (kp n) (HarmonicResidual.constantVector
        (HarmonicResidual.contextBase c n))
    (HarmonicMeanInteraction.blockAmplitude (primaryBlock s c a ψ kp) n)
    (HarmonicResidual.realCoefficients ((primaryBlock s c a ψ kp).pressure n))

namespace Inputs

variable {s : StripData D} {P : ℕ → D → ℝ} {κ : ℝ} {c : CorrectionState.Context D}
  {a : LinearWaveBounds.WaveCoefficients (D × ℝ)} {ψ : ℕ → D × ℝ → ℝ} {kp : ℕ → ℤ}
  (h : Inputs s P κ c a ψ kp)

include h

theorem base_smooth (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => HarmonicResidual.contextBase c n x i) s.domain := by
  have hs : ContDiffOn ℝ ∞ (fun p => LinearWaveResidual.complexBase
      (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase n) p i)
      (HarmonicWaveInteraction.productStrip s).domain := by
    apply Complex.ofRealCLM.contDiff.comp_contDiffOn
    fin_cases i
    · exact h.coefficients.radial_base.smooth n
    · exact (h.coefficients.radius.smooth n).mul (h.coefficients.frequency_base.smooth n)
    · exact h.coefficients.axial_base.smooth n
  rw [h.matching.base n] at hs
  exact hs.comp (HarmonicWaveInteraction.inclusion (D := D)).contDiff.contDiffOn (fun _ hx => hx)

theorem radial_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain :=
  (HarmonicMeanInteraction.slowGeometry c h.operators h.radius_pos).radial_class.smooth n

theorem axial_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).axial s.domain :=
  (HarmonicMeanInteraction.slowGeometry c h.operators h.radius_pos).axial_class.smooth n

omit h in
theorem primary_amplitude_real (n : ℕ) :
    HarmonicMeanInteraction.blockAmplitude (primaryBlock s c a ψ kp) n =
      (primaryBlock s c a ψ kp).velocity n := by
  funext i
  exact HarmonicResidual.realCoefficients_eq_self
    (ErrorHarmonics.conjugatePair_symmetric 1 (fun x => (corrected s c a ψ).amplitude n (x, 0) i))

omit h in
theorem primary_pressure_real (n : ℕ) :
    HarmonicResidual.realCoefficients ((primaryBlock s c a ψ kp).pressure n) =
      (primaryBlock s c a ψ kp).pressure n :=
  HarmonicResidual.realCoefficients_eq_self
    (ErrorHarmonics.conjugatePair_symmetric 1 (fun x => (corrected s c a ψ).pressure n (x, 0)))

theorem harmonicResidual_context (n : ℕ) :
    (corrected s c a ψ).harmonicResidual (HarmonicWaveInteraction.productStrip s) (directions c) n =
      LinearWaveResidual.linearResidual (c.operators.epsilon n)
        (fun p => c.operators.radius p.1)
        (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial)
        HarmonicResidual.angularDirection
        (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial)
        (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).time)
        (fun p => HarmonicResidual.contextBase c n p.1)
        (vectorMode (a.frequency n) (a.phase n) ((corrected s c a ψ).amplitude n))
        (mode (a.frequency n) (a.phase n) ((corrected s c a ψ).pressure n)) := by
  change LinearWaveResidual.linearResidual (s.epsilon n) (a.radius n)
    ((directions c).radialField n) (fun _ => (directions c).angular)
    ((directions c).axialField (HarmonicWaveInteraction.productStrip s) n)
    (LinearWaveResidual.timeDirection (s.epsilon n) ((directions c).fastField n) (fun _ =>
        (directions c).slow))
    (LinearWaveResidual.complexBase (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase
        n))
    _ _ = _
  have ht := directions_time s c h.matching.epsilon n
  change LinearWaveResidual.timeDirection (s.epsilon n) ((directions c).fastField n)
    (fun _ => (directions c).slow) = _ at ht
  rw [h.matching.base n, h.matching.radius, directions_radial,
    directions_axial s c h.matching.epsilon, ht]
  rw [h.matching.epsilon]
  rfl

theorem linear_field_re (n : ℕ) (p : D × ℝ) (hp : p.1 ∈ s.domain) (i : Fin 3) :
    (field (linearCoefficients s c a ψ kp n i) (a.frequency n)
      (fun x => a.phase n (x, 0)) (kp n) p).re =
    ((corrected s c a ψ).harmonicResidual (HarmonicWaveInteraction.productStrip s) (directions c) n
        p i).re := by
  have he := HarmonicResidual.field_linearResidual s.isOpen_domain
    (HarmonicResidual.contextFrame c n) (h.radial_smooth n) (h.axial_smooth n)
    (B := HarmonicResidual.constantVector (HarmonicResidual.contextBase c n))
    (fun j => HarmonicResidual.smoothCoefficients_constant (h.base_smooth n j))
    (h.primary_smooth n) (h.pressure_smooth n) (h.phase_slow_smooth n)
    (a.frequency n) (kp n) (p := p) ⟨hp, trivial⟩
  have hv : HarmonicResidual.vectorField ((primaryBlock s c a ψ kp).velocity n)
      (a.frequency n) (fun x => a.phase n (x, 0)) (kp n) =
        fun y j => realProjection (vectorMode (a.frequency n) (a.phase n)
          ((corrected s c a ψ).amplitude n) y j) := by
    funext y j
    exact h.primary_field n y j
  have hpr : field ((primaryBlock s c a ψ kp).pressure n)
      (a.frequency n) (fun x => a.phase n (x, 0)) (kp n) =
        fun y => realProjection (mode (a.frequency n) (a.phase n)
          ((corrected s c a ψ).pressure n) y) := by
    funext y
    exact h.pressure_field n y
  have hbase : HarmonicResidual.vectorField
      (HarmonicResidual.constantVector (HarmonicResidual.contextBase c n))
      (a.frequency n) (fun x => a.phase n (x, 0)) (kp n) =
        LinearWaveResidual.realLift (fun y j => (HarmonicResidual.contextBase c n y.1 j).re) := by
    funext y j
    rw [HarmonicResidual.vectorField_constantVector]
    fin_cases j <;> simp [HarmonicResidual.contextBase, LinearWaveResidual.realLift]
  rw [hv, hpr, hbase] at he
  have hd := linearResidual_realProjection
    (HarmonicWaveInteraction.productStrip s).isOpen_domain (c.operators.epsilon n)
    (fun y => c.operators.radius y.1)
    (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).time)
    (by simpa only [directions_radial] using (h.geometry n).radial_smooth)
    (h.geometry n).angular_smooth
    (by simpa only [directions_axial s c h.matching.epsilon] using (h.geometry n).axial_smooth)
    (B := fun (y : D × ℝ) j => (HarmonicResidual.contextBase c n y.1 j).re)
    (h.raw_velocity_smooth n)
    (fun j => (((Complex.reCLM.contDiff.comp_contDiffOn
      ((h.base_smooth n j).comp contDiffOn_fst (fun _ hx => hx))).contDiffAt
        ((HarmonicWaveInteraction.productStrip s).isOpen_domain.mem_nhds hp)).differentiableAt (by
            simp)))
    (((h.raw_pressure_smooth n).contDiffAt
      ((HarmonicWaveInteraction.productStrip s).isOpen_domain.mem_nhds hp)).differentiableAt (by
          simp)) hp i
  have hbase' : LinearWaveResidual.realLift (fun (y : D × ℝ) j => (HarmonicResidual.contextBase c n
      y.1 j).re) =
      fun y => HarmonicResidual.contextBase c n y.1 := by
    funext y j
    fin_cases j <;> simp [HarmonicResidual.contextBase, LinearWaveResidual.realLift]
  rw [hbase'] at he hd
  rw [linearCoefficients,
    primary_amplitude_real (s := s) (c := c) (a := a) (ψ := ψ) (kp := kp) n,
    primary_pressure_real (s := s) (c := c) (a := a) (ψ := ψ) (kp := kp) n]
  exact (congrArg Complex.re (congrFun he i)).trans (hd.trans (by
    rw [h.harmonicResidual_context n]
    rfl))

theorem linear_gaussian_coefficient (n : ℕ) (x : D) (hx : x ∈ s.domain) (i : Fin 3) (j : ℤ) :
    HarmonicResidual.realCoefficients
      (linearCoefficients s c a ψ kp n i - gaussianCoefficients c a ψ n i) j x =
        goodCoefficients s c a ψ n i j x := by
  apply HarmonicWaveInteraction.coefficient_eq_of_field_eq_at _ _ (a.frequency n)
    (fun y => a.phase n (y, 0)) (h.angular_ne n) j x
  intro θ
  rw [HarmonicResidual.field_realCoefficients, HarmonicResidual.field_sub, Complex.sub_re,
    h.linear_field_re n (x, θ) hx i, h.gaussian_field n (x, θ) i,
    h.good_field n (x, θ) i, h.linear_identity n (x, θ) hx]
  simp only [Pi.add_apply, Complex.add_re, realProjection_apply, Complex.ofReal_re,
    add_sub_cancel_right]

theorem full_primary_divergence (n : ℕ) (p : D × ℝ) (hp : p.1 ∈ s.domain) :
    cylindricalDivergence (fun q => c.operators.radius q.1)
      (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial)
      HarmonicResidual.angularDirection
      (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial)
      (fun q i => ((primaryBlock s c a ψ kp).oscillation n q i : ℂ)) p = 0 := by
  have he : (fun q i => ((primaryBlock s c a ψ kp).oscillation n q i : ℂ)) =
      fun q i => realProjection (vectorMode (a.frequency n) (a.phase n)
        ((corrected s c a ψ).amplitude n) q i) := by
    funext q i
    change ((field ((primaryBlock s c a ψ kp).velocity n i) (a.frequency n)
      (fun x => a.phase n (x, 0)) (kp n) q).re : ℂ) = _
    rw [h.primary_field]
    rfl
  rw [he, divergence_map realProjection _ _ _ _ (fun i =>
    ((h.raw_velocity_smooth n i).contDiffAt
      ((HarmonicWaveInteraction.productStrip s).isOpen_domain.mem_nhds hp)).differentiableAt (by
          simp))]
  have hd := h.corrected_divergence n p hp
  rw [h.matching.radius, directions_radial, directions_axial s c h.matching.epsilon] at hd
  change cylindricalDivergence _ _ HarmonicResidual.angularDirection _ _ p = 0 at hd
  rw [hd, map_zero]

theorem primary_modeSolenoidal :
    HarmonicWaveInteraction.ModeSolenoidal s c (primaryBlock s c a ψ kp) :=
  HarmonicWaveInteraction.modeSolenoidal_of_full c (primaryBlock s c a ψ kp)
    h.phase_slow_smooth h.angular_ne h.primary_smooth h.full_primary_divergence

omit h in
theorem primary_band : (primaryBlock s c a ψ kp).BandLimited 1 :=
  SignedWaveUpdate.coefficientBlock_band a.frequency (fun n x => a.phase n (x, 0)) kp
    (fun n x => (corrected s c a ψ).amplitude n (x, 0))
    (fun n x => (corrected s c a ψ).pressure n (x, 0))

omit h in
theorem primary_zeroMode : HarmonicWaveInteraction.ZeroMode (primaryBlock s c a ψ kp) :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient a.frequency (fun n x => a.phase n (x, 0)) kp
    (fun n x => (corrected s c a ψ).amplitude n (x, 0))
    (fun n x => (corrected s c a ψ).pressure n (x, 0))).1

theorem convection_class (j : ℤ) (i : Fin 3) :
    WaveClass s P (1 - κ) (fun n x =>
      HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
        (a.frequency n) (fun y => a.phase n (y, 0)) (kp n)
        (HarmonicMeanInteraction.blockAmplitude (primaryBlock s c a ψ kp) n)
        (HarmonicMeanInteraction.blockAmplitude (primaryBlock s c a ψ kp) n) i j x) := by
  have hc := HarmonicWaveInteraction.transport_wave_class c h.operators h.radius_pos
    h.primary_bounds h.primary_bounds
    (primary_zeroMode (s := s) (c := c) (a := a) (ψ := ψ) (kp := kp))
    (primary_zeroMode (s := s) (c := c) (a := a) (ψ := ψ) (kp := kp))
    (primary_band (s := s) (c := c) (a := a) (ψ := ψ) (kp := kp))
    h.phase_slow_smooth h.frequency_ne h.primary_modeSolenoidal h.profile_nonneg h.profile_le_one j
        i
  convert! hc using 1
  ring

theorem linear_good_class (j : ℤ) (i : Fin 3) :
    WaveClass s P (1 - 3 * κ) (fun n x => HarmonicResidual.realCoefficients
      (linearCoefficients s c a ψ kp n i - gaussianCoefficients c a ψ n i) j x) := by
  apply LinearWaveBounds.class_congr (h.good_coefficients_class j i)
  intro n x hx
  exact (h.linear_gaussian_coefficient n x hx i j).symm

/-- The actual extracted residual of the initial primary wave. The alias is
retained in the literal formula; its proved zero-mode property is used only
after the nonconstant coefficient is selected. -/
theorem initial_residual_class (u : CorrectionState.State D)
    (hmean : u.mean = ⟨0, 0, 0⟩) (A : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i j, j ≠ 0 → A n i j = 0) :
    (HarmonicResidual.residualBlock c u (primaryBlock s c a ψ kp)
      (gaussianCoefficients c a ψ) A).WaveBounds s P (7 / 10) := by
  intro i j hj
  have hl := (h.linear_good_class j i).mono_exponent (show (7 / 10 : ℝ) ≤ 1 - 3 * κ by
      linarith [h.loss_le])
  have hc (m : ℤ) := (h.convection_class m i).mono_exponent
    (show (7 / 10 : ℝ) ≤ 1 - κ by linarith [h.loss_le])
  have hcr := HarmonicMeanInteraction.realCoefficient_class
    (fun n => HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
      (a.frequency n) (fun y => a.phase n (y, 0)) (kp n)
      (HarmonicMeanInteraction.blockAmplitude (primaryBlock s c a ψ kp) n)
      (HarmonicMeanInteraction.blockAmplitude (primaryBlock s c a ψ kp) n) i)
    j (hc j) (hc (-j))
  apply LinearWaveBounds.class_congr (hl.add hcr)
  intro n x hx
  have hz : HarmonicResidual.stateMean u n = 0 := by
    funext y k
    fin_cases k <;> simp [HarmonicResidual.stateMean, hmean]
  change _ = HarmonicResidual.nonconstant
    ((HarmonicResidual.ofBlock (primaryBlock s c a ψ kp) (gaussianCoefficients c a ψ) A
        n).residualCoefficients
      (HarmonicResidual.contextFrame c n) (HarmonicResidual.contextBase c n)
          (HarmonicResidual.stateMean u n) i) j x
  rw [HarmonicMeanInteraction.nonconstant_apply_of_ne _ hj, hz,
      HarmonicResidual.LabelData.residualCoefficients]
  simp only [add_zero]
  let L := linearCoefficients s c a ψ kp n i
  let T := HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (fun y => a.phase n (y, 0)) (kp n)
    (HarmonicMeanInteraction.blockAmplitude (primaryBlock s c a ψ kp) n)
    (HarmonicMeanInteraction.blockAmplitude (primaryBlock s c a ψ kp) n) i
  change HarmonicResidual.realCoefficients (L - gaussianCoefficients c a ψ n i) j x +
    HarmonicResidual.realCoefficients T j x =
      HarmonicResidual.realCoefficients (L + T - gaussianCoefficients c a ψ n i - A n i) j x
  simp only [
    HarmonicResidual.realCoefficients_apply, HarmonicMeanInteraction.coeff_add,
    HarmonicMeanInteraction.coeff_sub, hA n i j hj, hA n i (-j) (neg_ne_zero.mpr hj),
    Pi.zero_apply, map_sub, map_add, sub_zero]
  ring

theorem initial_residual_class_of_zero_mode (u : CorrectionState.State D)
    (hmean : u.mean = ⟨0, 0, 0⟩) (A : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, HarmonicFields.BandLimited (A n i) 0) :
    (HarmonicResidual.residualBlock c u (primaryBlock s c a ψ kp)
      (gaussianCoefficients c a ψ) A).WaveBounds s P (7 / 10) := by
  apply h.initial_residual_class u hmean A
  intro n i j hj
  rw [HarmonicResidual.band_zero_eq_constant (hA n i)]
  simp [constantCoefficient, hj]

omit h in
theorem initial_residual_band (u : CorrectionState.State D)
    (A : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, HarmonicFields.BandLimited (A n i) 0) :
    (HarmonicResidual.residualBlock c u (primaryBlock s c a ψ kp)
      (gaussianCoefficients c a ψ) A).BandLimited 2 := by
  have hg : ∀ n i, HarmonicFields.BandLimited (gaussianCoefficients c a ψ n i) 1 :=
    fun n i => ErrorHarmonics.band_conjugatePair 1 _
  have ha : ∀ n i, HarmonicFields.BandLimited (A n i) 1 := fun n i => (hA n i).mono (by decide)
  simpa using HarmonicResidual.residualBlock_band c u (primaryBlock s c a ψ kp)
    (gaussianCoefficients c a ψ) A
    (primary_band (s := s) (c := c) (a := a) (ψ := ψ) (kp := kp)) hg ha

end Inputs

end NavierStokes.PrimaryResidualClass
