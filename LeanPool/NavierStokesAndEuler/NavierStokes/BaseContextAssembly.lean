/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalRankDefect
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalResidualTZ
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryTargetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseRadialJets
import LeanPool.NavierStokesAndEuler.NavierStokes.AllBandBaseJets
public import LeanPool.NavierStokesAndEuler.NavierStokes.LinearWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryPulseBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicWaveInteraction
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedWaveUpdate

/-!
# The correction context of the actual slow base

The native slow order is `(T,Z)`. The explicit linear map `slowCoordinates`
converts to the `(R,(Z,T))` order used by the physical base charts. Every
field below uses one fixed final profile, coefficient family, and schedule.
-/

section

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

end
end

end

section

/-!
# The actual primary material-phase defect

The large axial term in the phase is cancelled by its actual material
derivative before estimating any jets.  Only the slow coordinate map and
slot coordinate require polynomial bounds; the angular coordinate and
the unstripped phase itself need no such bound.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.PrimaryMaterialDefect

open Set WeightedClasses LinearWaveBounds
open scoped Topology ContDiff

/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow
/-- Slot: an abbreviation for `PhaseCalculus.Slot`. -/
abbrev Slot := PhaseCalculus.Slot

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First-order chart identities, including the direction annihilated by
the physical radial graph derivative.  No phase derivative is an input. -/
structure NativeCoordinates (s : StripData E) (d : GraphDirections E)
    (χ : ℕ → E → Slot) : Prop where
  differentiable : ∀ n x, x ∈ s.domain → DifferentiableAt ℝ (χ n) x
  radial : ∀ n x, x ∈ s.domain → fderiv ℝ (χ n) x d.radial = PhaseCalculus.eR
  auxiliary : ∀ n x, x ∈ s.domain → fderiv ℝ (χ n) x d.auxiliary = 0
  angular : ∀ n x, x ∈ s.domain → fderiv ℝ (χ n) x d.angular = PhaseCalculus.eTheta
  axial : ∀ n x, x ∈ s.domain → fderiv ℝ (χ n) x d.axial = PhaseCalculus.eZ
  fast : ∀ n x, x ∈ s.domain → fderiv ℝ (χ n) x (d.fastField n x) = PhaseCalculus.eV
  slow : ∀ n x, x ∈ s.domain → fderiv ℝ (χ n) x d.slow = PhaseCalculus.eT

namespace NativeCoordinates

variable {s : StripData E} {d : GraphDirections E} {χ : ℕ → E → Slot}
variable (hχ : NativeCoordinates s d χ)

include hχ

theorem radialField (n : ℕ) {x : E} (hx : x ∈ s.domain) :
    fderiv ℝ (χ n) x (d.radialField n x) = PhaseCalculus.eR := by
  simp only [GraphDirections.radialField, map_add, map_smul,
    hχ.radial n x hx, hχ.auxiliary n x hx, smul_zero, add_zero]

theorem axialField (n : ℕ) {x : E} (hx : x ∈ s.domain) :
    fderiv ℝ (χ n) x (d.axialField s n x) = s.epsilon n • PhaseCalculus.eZ := by
  simp only [GraphDirections.axialField, map_smul, hχ.axial n x hx]

theorem timeField (n : ℕ) {x : E} (hx : x ∈ s.domain) :
    fderiv ℝ (χ n) x
      (LinearWaveResidual.timeDirection (s.epsilon n) (d.fastField n) (fun _ => d.slow) x) =
      PhaseCalculus.eV - s.epsilon n • PhaseCalculus.eT := by
  simp only [LinearWaveResidual.timeDirection, map_sub, map_smul,
    hχ.fast n x hx, hχ.slow n x hx]

end NativeCoordinates

/-- For affine native/common coordinate maps, checking the six images is
linear algebra.  No differentiability premise is needed. -/
theorem affine_coordinates (s : StripData E) (d : GraphDirections E)
    (L : ℕ → E →L[ℝ] Slot) (c : ℕ → Slot)
    (hr : ∀ n, L n d.radial = PhaseCalculus.eR)
    (ha : ∀ n, L n d.auxiliary = 0)
    (hθ : ∀ n, L n d.angular = PhaseCalculus.eTheta)
    (hz : ∀ n, L n d.axial = PhaseCalculus.eZ)
    (hf : ∀ n, d.fastScale n • L n d.fast = PhaseCalculus.eV)
    (ht : ∀ n, L n d.slow = PhaseCalculus.eT) :
    NativeCoordinates s d (fun n x => L n x + c n) := by
  have hd n x : fderiv ℝ (fun y => L n y + c n) x = L n :=
    ((L n).hasFDerivAt.add_const (c n)).fderiv
  refine ⟨fun n _ _ => (L n).differentiableAt.add_const _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x _; rw [hd]; exact hr n
  · intro n x _; rw [hd]; exact ha n
  · intro n x _; rw [hd]; exact hθ n
  · intro n x _; rw [hd]; exact hz n
  · intro n x _; rw [hd]; simpa only [GraphDirections.fastField, map_smul] using hf n
  · intro n x _; rw [hd]; exact ht n

section CommonPullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- Differential matching for a change from a common chart to a native
chart.  It concerns the coordinate map, not the phase or its defect. -/
structure DirectionMatch (s : StripData E) (d : GraphDirections E)
    (s' : StripData E') (d' : GraphDirections E') (ψ : ℕ → E' → E) : Prop where
  maps : ∀ n, MapsTo (ψ n) s'.domain s.domain
  differentiable : ∀ n x, x ∈ s'.domain → DifferentiableAt ℝ (ψ n) x
  radial : ∀ n x, x ∈ s'.domain → fderiv ℝ (ψ n) x d'.radial = d.radial
  auxiliary : ∀ n x, x ∈ s'.domain → fderiv ℝ (ψ n) x d'.auxiliary = d.auxiliary
  angular : ∀ n x, x ∈ s'.domain → fderiv ℝ (ψ n) x d'.angular = d.angular
  axial : ∀ n x, x ∈ s'.domain → fderiv ℝ (ψ n) x d'.axial = d.axial
  fast : ∀ n x, x ∈ s'.domain → fderiv ℝ (ψ n) x (d'.fastField n x) = d.fastField n (ψ n x)
  slow : ∀ n x, x ∈ s'.domain → fderiv ℝ (ψ n) x d'.slow = d.slow

theorem NativeCoordinates.comp
    {s : StripData E} {d : GraphDirections E} {χ : ℕ → E → Slot}
    (hχ : NativeCoordinates s d χ)
    {s' : StripData E'} {d' : GraphDirections E'} {ψ : ℕ → E' → E}
    (hψ : DirectionMatch s d s' d' ψ) :
    NativeCoordinates s' d' (fun n => χ n ∘ ψ n) := by
  have hd n x hx := fderiv_comp x (hχ.differentiable n (ψ n x) (hψ.maps n hx))
    (hψ.differentiable n x hx)
  refine ⟨fun n x hx => (hχ.differentiable n (ψ n x) (hψ.maps n hx)).comp x
    (hψ.differentiable n x hx), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x hx; rw [hd n x hx, ContinuousLinearMap.comp_apply, hψ.radial n x hx]
    exact hχ.radial n _ (hψ.maps n hx)
  · intro n x hx; rw [hd n x hx, ContinuousLinearMap.comp_apply, hψ.auxiliary n x hx]
    exact hχ.auxiliary n _ (hψ.maps n hx)
  · intro n x hx; rw [hd n x hx, ContinuousLinearMap.comp_apply, hψ.angular n x hx]
    exact hχ.angular n _ (hψ.maps n hx)
  · intro n x hx; rw [hd n x hx, ContinuousLinearMap.comp_apply, hψ.axial n x hx]
    exact hχ.axial n _ (hψ.maps n hx)
  · intro n x hx; rw [hd n x hx, ContinuousLinearMap.comp_apply, hψ.fast n x hx]
    exact hχ.fast n _ (hψ.maps n hx)
  · intro n x hx; rw [hd n x hx, ContinuousLinearMap.comp_apply, hψ.slow n x hx]
    exact hχ.slow n _ (hψ.maps n hx)

end CommonPullback

theorem differentiableAt_phase (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q : Slot)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    DifferentiableAt ℝ (PhaseCalculus.phase ε p pz x0 F G) q := by
  have hi : DifferentiableAt ℝ (fun z : Slot => z) q := differentiableAt_id
  have hFl := hF.comp q hi.fst
  have hGl := hG.comp q hi.fst
  exact (((hi.snd.fst.const_mul p).add (hi.fst.snd.fst.const_mul (pz / ε))).add
    (hi.fst.fst.const_mul x0)).sub
      (hi.snd.snd.mul ((hFl.const_mul p).add (hGl.const_mul pz)))

/-- The algebraic expression after exact material cancellation. -/
noncomputable def expression (ε p pz x0 v b G FR GR FT GT FZ GZ : ℝ) : ℝ :=
  b * x0 - v * (b * (p * FR + pz * GR) - ε * (p * FT + pz * GT) +
    ε * G * (p * FZ + pz * GZ))

/-- A chart pullback of the actual phase has exactly the native backward
material derivative, using only the chart differential identities. -/
theorem material_pullback
    (χ : E → Slot) (ε p pz x0 : ℝ) (b F G : Slow → ℝ)
    (Vr Vθ Vz Vf Vs : E → E) {x : E}
    (hχ : DifferentiableAt ℝ χ x) (hε : ε ≠ 0) (hR : 0 < (χ x).1.1)
    (hF : DifferentiableAt ℝ F (χ x).1) (hG : DifferentiableAt ℝ G (χ x).1)
    (hr : fderiv ℝ χ x (Vr x) = PhaseCalculus.eR)
    (hθ : fderiv ℝ χ x (Vθ x) = PhaseCalculus.eTheta)
    (hz : fderiv ℝ χ x (Vz x) = ε • PhaseCalculus.eZ)
    (hf : fderiv ℝ χ x (Vf x) = PhaseCalculus.eV)
    (hs : fderiv ℝ χ x (Vs x) = PhaseCalculus.eT) :
    LinearWaveResidual.materialPhaseDefect (fun y => (χ y).1.1)
      (fun y => b (χ y).1) (fun y => F (χ y).1) (fun y => G (χ y).1)
      Vr Vθ Vz (LinearWaveResidual.timeDirection ε Vf Vs)
      (PhaseCalculus.phase ε p pz x0 F G ∘ χ) x =
    expression ε p pz x0 (χ x).2.2 (b (χ x).1) (G (χ x).1)
      (PhaseCalculus.slowR F (χ x).1) (PhaseCalculus.slowR G (χ x).1)
      (PhaseCalculus.slowT F (χ x).1) (PhaseCalculus.slowT G (χ x).1)
      (PhaseCalculus.slowZ F (χ x).1) (PhaseCalculus.slowZ G (χ x).1) := by
  have hΦ := differentiableAt_phase ε p pz x0 F G (χ x) hF hG
  have hd := fderiv_comp x hΦ hχ
  have hcancel : PhaseCalculus.baseV F (χ x).1 / (χ x).1.1 = F (χ x).1 := by
    unfold PhaseCalculus.baseV
    field_simp
  calc
    _ = PhaseCalculus.backwardMaterialOp ε b F G (PhaseCalculus.phase ε p pz x0 F G) (χ x) := by
      unfold LinearWaveResidual.materialPhaseDefect HarmonicCalculus.along
      simp only [hd, ContinuousLinearMap.comp_apply, LinearWaveResidual.timeDirection,
        map_sub, map_smul, hr, hθ, hz, hf, hs, smul_eq_mul]
      unfold PhaseCalculus.backwardMaterialOp PhaseCalculus.signedMaterialOp
      rw [hcancel]
      ring
    _ = _ := PhaseCalculus.backwardMaterialOp_phase ε p pz x0 b F G (χ x) hε hR hF hG

/-- Direct class estimate for the exact expression.  The six derivatives
here are scalar coefficient families; the primary specialization below
derives their classes from actual base-field jets. -/
theorem expression_class {s : StripData E}
    {p pz x0 v b G FR GR FT GT FZ GZ : ℕ → E → ℝ}
    (hp : UnweightedClass s 0 p) (hpz : UnweightedClass s 0 pz)
    (hx0 : UnweightedClass s 0 x0) (hv : UnweightedClass s 0 v)
    (hb : UnweightedClass s 1 b) (hG : UnweightedClass s 0 G)
    (hFR : UnweightedClass s 0 FR) (hGR : UnweightedClass s 0 GR)
    (hFT : UnweightedClass s 0 FT) (hGT : UnweightedClass s 0 GT)
    (hFZ : UnweightedClass s 0 FZ) (hGZ : UnweightedClass s 0 GZ) :
    UnweightedClass s 1 (fun n x => expression (s.epsilon n) (p n x) (pz n x)
      (x0 n x) (v n x) (b n x) (G n x) (FR n x) (GR n x)
      (FT n x) (GT n x) (FZ n x) (GZ n x)) := by
  have hR : UnweightedClass s 0 (fun n x => p n x * FR n x + pz n x * GR n x) := by
    simpa only [zero_add] using (unweighted_mul hp hFR).add (unweighted_mul hpz hGR)
  have hT : UnweightedClass s 0 (fun n x => p n x * FT n x + pz n x * GT n x) := by
    simpa only [zero_add] using (unweighted_mul hp hFT).add (unweighted_mul hpz hGT)
  have hZ : UnweightedClass s 0 (fun n x => p n x * FZ n x + pz n x * GZ n x) := by
    simpa only [zero_add] using (unweighted_mul hp hFZ).add (unweighted_mul hpz hGZ)
  have hbR : UnweightedClass s 1 (fun n x => b n x *
      (p n x * FR n x + pz n x * GR n x)) := by
    simpa only [add_zero] using unweighted_mul hb hR
  have heT : UnweightedClass s 1 (fun n x => s.epsilon n *
      (p n x * FT n x + pz n x * GT n x)) := by
    simpa only [zero_add, smul_eq_mul] using hT.band_smul (band_epsilon s)
  have heZ : UnweightedClass s 1 (fun n x => s.epsilon n * G n x *
      (p n x * FZ n x + pz n x * GZ n x)) := by
    simpa only [zero_add, smul_eq_mul, mul_assoc] using
      (unweighted_mul hG hZ).band_smul (band_epsilon s)
  have hinside := (class_sub hbR heT).add heZ
  have hfirst : UnweightedClass s 1 (fun n x => b n x * x0 n x) := by
    simpa only [add_zero] using unweighted_mul hb hx0
  have htail : UnweightedClass s 1 (fun n x => v n x *
      (b n x * (p n x * FR n x + pz n x * GR n x) -
        s.epsilon n * (p n x * FT n x + pz n x * GT n x) +
        s.epsilon n * G n x * (p n x * FZ n x + pz n x * GZ n x))) := by
    simpa only [zero_add] using unweighted_mul hv hinside
  exact class_sub hfirst htail

/-- Polynomial base jets compose with the actual slow coordinate map.
The angular coordinate is absent from this quantitative hypothesis. -/
theorem polynomial_comp_unweighted
    {s : StripData E} {U : PhaseJetBounds.Domain ℕ Slow}
    {f : ℕ → Slow → ℝ} (hf : PhaseJetBounds.PolynomialJets U f)
    {c : ℕ → E → Slow} (hc : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) c)
    (hscale : ∀ n, U.scale n = s.slow n)
    (hmap : ∀ n, MapsTo (c n) s.domain (U.carrier n)) :
    UnweightedClass s 0 (fun n x => f n (c n x)) :=
  ((PrimaryPulseBounds.EnvelopeJets.of_polynomial hf).comp hc hscale hmap).memClass s
    (fun _ => rfl) (fun _ => rfl)

/-- The same composition result allows polynomial inverse-edge losses in
the slow chart itself.  This is a quantitative chain-rule estimate, not
an assumption about the pulled-back base derivatives. -/
theorem polynomial_comp_with_edges
    {s : StripData E} {U : PhaseJetBounds.Domain ℕ Slow}
    {f : ℕ → Slow → ℝ} (hf : PhaseJetBounds.PolynomialJets U f)
    {c : ℕ → E → Slow} (hc : UnweightedClass s 0 c)
    (hscale : ∀ n, U.scale n = s.slow n)
    (hmap : ∀ n, MapsTo (c n) s.domain (U.carrier n)) :
    UnweightedClass s 0 (fun n x => f n (c n x)) := by
  refine ⟨fun _ _ _ => zero_le_one, fun n => (hf.smooth n).comp (hc.smooth n) (hmap n), ?_⟩
  intro N
  obtain ⟨A, hA, m, ha⟩ := hf.bound N
  obtain ⟨B, hB, k, hb⟩ := hc.bounds N
  refine ⟨(N.factorial : ℝ) * A * (B + 1) ^ N, by positivity, m + k * N, ?_⟩
  intro n x hx j hj
  have hg0 := s.growth_nonneg n x
  have hg1 := s.one_le_growth n x
  have hD : 1 ≤ (B + 1) * s.growth n x ^ k :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hg1)
  have hinner (a : ℕ) (haN : a ≤ N) :
      ‖iteratedFDeriv ℝ a (c n) x‖ ≤ (B + 1) * s.growth n x ^ k := by
    have hh := hb n x hx a haN
    simp only [majorant, Real.rpow_zero, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hg0 _))
  have houter (a : ℕ) (haN : a ≤ N) :
      ‖iteratedFDeriv ℝ a (f n) (c n x)‖ ≤ A * s.growth n x ^ m := by
    have hh := ha n a haN _ (hmap n hx)
    rw [hscale n] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) _)
      (zero_le_one.trans hA))
  have hn : (j : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  have hchain := norm_iteratedFDerivWithin_comp_le (hf.smooth n) (hc.smooth n) hn
    (U.isOpen n).uniqueDiffOn s.isOpen_domain.uniqueDiffOn (hmap n) hx
    (C := A * s.growth n x ^ m) (D := (B + 1) * s.growth n x ^ k)
    (fun a haj => ?_) (fun a ha1 haj => ?_)
  · rw [iteratedFDerivWithin_of_isOpen j s.isOpen_domain hx] at hchain
    simp only [majorant, Real.rpow_zero, mul_one]
    calc
      _ ≤ (j.factorial : ℝ) * (A * s.growth n x ^ m) * ((B + 1) * s.growth n x ^ k) ^ j := hchain
      _ ≤ (N.factorial : ℝ) * (A * s.growth n x ^ m) * ((B + 1) * s.growth n x ^ k) ^ N := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) (by positivity)
        · exact pow_le_pow_right₀ hD hj
        · positivity
        · positivity
      _ = _ := by rw [mul_pow, pow_add, pow_mul]; ring
  · rw [iteratedFDerivWithin_of_isOpen a (U.isOpen n) (hmap n hx)]
    exact houter a (haj.trans hj)
  · rw [iteratedFDerivWithin_of_isOpen a s.isOpen_domain hx]
    exact (hinner a (haj.trans hj)).trans (by simpa using pow_le_pow_right₀ hD ha1)

/-- The actual affine clock has polynomial jets from its value and linear
coefficient bounds.  This supplies the slot-coordinate class in either
native or common coordinates. -/
theorem affine_slot_class (s : StripData E) (L : ℕ → E →L[ℝ] ℝ) (c : ℕ → ℝ)
    {C : ℝ} {m : ℕ} (hC : 1 ≤ C)
    (hL : ∀ n, ‖L n‖ ≤ C * s.slow n ^ m)
    (hv : ∀ n x, x ∈ s.domain → |L n x + c n| ≤ C * s.slow n ^ m) :
    UnweightedClass s 0 (fun n x => L n x + c n) := by
  apply PrimaryPulseBounds.polynomial_memClass s
  refine ⟨fun n => (L n).contDiff.contDiffOn.add contDiffOn_const, fun _ => ⟨C, hC, m, ?_⟩⟩
  intro n j _ x hx
  have hd : fderiv ℝ (fun y => L n y + c n) = fun _ => L n := by
    funext y
    exact ((L n).hasFDerivAt.add_const (c n)).fderiv
  cases j with
  | zero =>
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, PrimaryPulseBounds.phaseDomain] using
          hv n x hx
  | succ j =>
      rw [← norm_iteratedFDeriv_fderiv, hd]
      cases j with
      | zero => simpa only [norm_iteratedFDeriv_zero, PrimaryPulseBounds.phaseDomain] using hL n
      | succ j =>
          rw [iteratedFDeriv_succ_const]
          simp only [Pi.zero_apply, norm_zero]
          exact mul_nonneg (zero_le_one.trans hC)
            (pow_nonneg (zero_le_one.trans (s.one_le_slow n)) _)

section Primary

variable {U : PhaseJetBounds.Domain ℕ Slow}

/-- Pulled phase, given by `PhaseCalculus.phase (P.phase.epsilon n) (P.phase.p n) (P.phase.pz n)
(P.phase.x0 n) (P.phase.F n) (P.phase.G n) (χ n x)`. -/
noncomputable def pulledPhase (P : PrimaryPulseBounds.PhaseConstruction U)
    (χ : ℕ → E → Slot) (n : ℕ) (x : E) : ℝ :=
  PhaseCalculus.phase (P.phase.epsilon n) (P.phase.p n) (P.phase.pz n) (P.phase.x0 n)
    (P.phase.F n) (P.phase.G n) (χ n x)

/-- Canonical raw geometry with arbitrary amplitude/pressure.  Those two
fields do not enter the material defect.  The angular base field here is
the frequency `F`, as required by `LinearWaveResidual`, not `R*F`. -/
noncomputable def coefficients (P : PrimaryPulseBounds.PhaseConstruction U)
    (b : ℕ → Slow → ℝ) (χ : ℕ → E → Slot)
    (amplitude : ℕ → E → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → E → ℂ) (frequency : ℕ → ℝ) : WaveCoefficients E where
  radius n x := (χ n x).1.1
  radialBase n x := b n (χ n x).1
  frequencyBase n x := P.phase.F n (χ n x).1
  axialBase n x := P.phase.G n (χ n x).1
  phase := pulledPhase P χ
  amplitude := amplitude
  pressure := pressure
  frequency := frequency

theorem defect_formula (P : PrimaryPulseBounds.PhaseConstruction U)
    (s : StripData E) (d : GraphDirections E) (χ : ℕ → E → Slot) (b : ℕ → Slow → ℝ)
    (amplitude : ℕ → E → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → E → ℂ) (frequency : ℕ → ℝ)
    (hχ : NativeCoordinates s d χ)
    (hmap : ∀ n, MapsTo (fun x => (χ n x).1) s.domain (U.carrier n))
    (heps : ∀ n, P.phase.epsilon n = s.epsilon n)
    (n : ℕ) {x : E} (hx : x ∈ s.domain) (hR : 0 < (χ n x).1.1) :
    (coefficients P b χ amplitude pressure frequency).defect s d n x =
      expression (s.epsilon n) (P.phase.p n) (P.phase.pz n) (P.phase.x0 n)
        (χ n x).2.2 (b n (χ n x).1) (P.phase.G n (χ n x).1)
        (PhaseCalculus.slowR (P.phase.F n) (χ n x).1)
        (PhaseCalculus.slowR (P.phase.G n) (χ n x).1)
        (PhaseCalculus.slowT (P.phase.F n) (χ n x).1)
        (PhaseCalculus.slowT (P.phase.G n) (χ n x).1)
        (PhaseCalculus.slowZ (P.phase.F n) (χ n x).1)
        (PhaseCalculus.slowZ (P.phase.G n) (χ n x).1) := by
  have hF := ((P.baseF.smooth n).contDiffAt ((U.isOpen n).mem_nhds (hmap n hx))).differentiableAt
      (by
      simp)
  have hG := ((P.baseG.smooth n).contDiffAt ((U.isOpen n).mem_nhds (hmap n hx))).differentiableAt
      (by
      simp)
  have hm := material_pullback (χ n) (s.epsilon n) (P.phase.p n) (P.phase.pz n) (P.phase.x0 n)
    (b n) (P.phase.F n) (P.phase.G n) (d.radialField n) (fun _ => d.angular)
    (d.axialField s n) (d.fastField n) (fun _ => d.slow)
    (hχ.differentiable n x hx) (s.epsilon_pos n).ne' hR hF hG
    (hχ.radialField n hx) (hχ.angular n x hx) (hχ.axialField n hx)
    (hχ.fast n x hx) (hχ.slow n x hx)
  have hpull : pulledPhase P χ n =
      PhaseCalculus.phase (s.epsilon n) (P.phase.p n) (P.phase.pz n) (P.phase.x0 n)
        (P.phase.F n) (P.phase.G n) ∘ χ n := by
    funext y
    simp only [pulledPhase, heps n, Function.comp_apply]
  simp only [WaveCoefficients.defect, coefficients]
  rw [hpull]
  exact hm

theorem frozen_classes (P : PrimaryPulseBounds.PhaseConstruction U) (s : StripData E) :
    UnweightedClass s 0 (fun n _ => P.phase.p n) ∧
    UnweightedClass s 0 (fun n _ => P.phase.pz n) ∧
    UnweightedClass s 0 (fun n _ => P.phase.x0 n) := by
  have hconst (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ P.M) :
      UnweightedClass s 0 (fun n _ => c n) := by
    apply PrimaryPulseBounds.polynomial_memClass s
    exact PhaseJetBounds.PolynomialJets.const_uniform c P.one_le_M
      (fun n => by simpa only [Real.norm_eq_abs] using hc n)
  exact ⟨hconst _ (fun n => (P.constants n).2.1),
    hconst _ (fun n => (P.constants n).2.2.1), hconst _ (fun n => (P.constants n).2.2.2)⟩

/-- Actual all-order defect bounds from base jets and primitive chart
data.  The six base-derivative classes are derived in the proof. -/
theorem defect_class (P : PrimaryPulseBounds.PhaseConstruction U)
    (s : StripData E) (d : GraphDirections E) (χ : ℕ → E → Slot) (b : ℕ → Slow → ℝ)
    (amplitude : ℕ → E → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → E → ℂ) (frequency : ℕ → ℝ)
    (hχ : NativeCoordinates s d χ)
    (hslow : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) (fun n x => (χ n
        x).1))
    (hslot : UnweightedClass s 0 (fun n x => (χ n x).2.2))
    (hscale : ∀ n, U.scale n = s.slow n)
    (hmap : ∀ n, MapsTo (fun x => (χ n x).1) s.domain (U.carrier n))
    (heps : ∀ n, P.phase.epsilon n = s.epsilon n)
    (hR : ∀ n x, x ∈ s.domain → 0 < (χ n x).1.1)
    (hb : UnweightedClass s 1 (fun n x => b n (χ n x).1)) :
    UnweightedClass s 1 ((coefficients P b χ amplitude pressure frequency).defect s d) := by
  obtain ⟨hp, hpz, hx0⟩ := frozen_classes P s
  have hG := polynomial_comp_unweighted P.baseG hslow hscale hmap
  have hFR := polynomial_comp_unweighted (P.baseF.directional (1, (0, 0))) hslow hscale hmap
  have hGR := polynomial_comp_unweighted (P.baseG.directional (1, (0, 0))) hslow hscale hmap
  have hFT := polynomial_comp_unweighted (P.baseF.directional (0, (0, 1))) hslow hscale hmap
  have hGT := polynomial_comp_unweighted (P.baseG.directional (0, (0, 1))) hslow hscale hmap
  have hFZ := polynomial_comp_unweighted (P.baseF.directional (0, (1, 0))) hslow hscale hmap
  have hGZ := polynomial_comp_unweighted (P.baseG.directional (0, (1, 0))) hslow hscale hmap
  have he := expression_class hp hpz hx0 hslot hb hG hFR hGR hFT hGT hFZ hGZ
  apply class_congr he
  intro n x hx
  exact (defect_formula P s d χ b amplitude pressure frequency hχ hmap heps n hx (hR n x hx)).symm

theorem defect_class_of_mean (P : PrimaryPulseBounds.PhaseConstruction U)
    (s : StripData E) (d : GraphDirections E) (χ : ℕ → E → Slot) (b : ℕ → Slow → ℝ)
    (amplitude : ℕ → E → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → E → ℂ) (frequency : ℕ → ℝ)
    (hχ : NativeCoordinates s d χ)
    (hslow : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) (fun n x => (χ n
        x).1))
    (hslot : UnweightedClass s 0 (fun n x => (χ n x).2.2))
    (hscale : ∀ n, U.scale n = s.slow n)
    (hmap : ∀ n, MapsTo (fun x => (χ n x).1) s.domain (U.carrier n))
    (heps : ∀ n, P.phase.epsilon n = s.epsilon n)
    (hR : ∀ n x, x ∈ s.domain → 0 < (χ n x).1.1)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hb : MeanClass s 1 (fun n x => b n (χ n x).1)) :
    UnweightedClass s 1 ((coefficients P b χ amplitude pressure frequency).defect s d) :=
  defect_class P s d χ b amplitude pressure frequency hχ hslow hslot hscale hmap heps hR
    (mean_unweighted hb hζ)

/-- Field matching binds an existing wave record to the exact phase.  It
does not assume equality or bounds of its material defect. -/
theorem defect_class_of_fields (P : PrimaryPulseBounds.PhaseConstruction U)
    (s : StripData E) (d : GraphDirections E) (χ : ℕ → E → Slot) (b : ℕ → Slow → ℝ)
    (a : WaveCoefficients E)
    (hχ : NativeCoordinates s d χ)
    (hslow : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) (fun n x => (χ n
        x).1))
    (hslot : UnweightedClass s 0 (fun n x => (χ n x).2.2))
    (hscale : ∀ n, U.scale n = s.slow n)
    (hmap : ∀ n, MapsTo (fun x => (χ n x).1) s.domain (U.carrier n))
    (heps : ∀ n, P.phase.epsilon n = s.epsilon n)
    (hR : ∀ n x, x ∈ s.domain → 0 < (χ n x).1.1)
    (hb : UnweightedClass s 1 (fun n x => b n (χ n x).1))
    (hbfield : a.radialBase = fun n x => b n (χ n x).1)
    (hFfield : a.frequencyBase = fun n x => P.phase.F n (χ n x).1)
    (hGfield : a.axialBase = fun n x => P.phase.G n (χ n x).1)
    (hphase : a.phase = pulledPhase P χ) : UnweightedClass s 1 (a.defect s d) := by
  have hd := defect_class P s d χ b a.amplitude a.pressure a.frequency
    hχ hslow hslot hscale hmap heps hR hb
  apply class_congr hd
  intro n x _
  simp only [WaveCoefficients.defect, LinearWaveResidual.materialPhaseDefect,
    coefficients, hbfield, hFfield, hGfield, hphase]

end Primary

/-- One finite-prefix constant and one polynomial degree work for every
band and point.  This is the explicit jet form of the order-one class. -/
theorem finite_jet_bounds {s : StripData E} {f : ℕ → E → ℝ}
    (hf : UnweightedClass s 1 f) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n x, x ∈ s.domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f n) x‖ ≤ C * s.epsilon n * s.growth n x ^ p := by
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun n x hx j hj => by
    simpa only [majorant, Real.rpow_one, mul_one] using hb n x hx j hj⟩

end NavierStokes.PrimaryMaterialDefect

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.BaseContextAssembly

open Set Function Filter WeightedClasses
open scoped ContDiff Topology BigOperators EuclideanSpace

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane
/-- Point: an abbreviation for `PressureStream.Lift Plane`. -/
abbrev Point := PressureStream.Lift Plane
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow

/-- Common index, given by `ChartScales.nativeIndex h n`. -/
noncomputable def commonIndex (h : ℝ) (n : ℕ) : ℕ := ChartScales.nativeIndex h n

/-- Slow scale, given by `max 1 (ChartScales.S n)`. -/
noncomputable def slowScale (n : ℕ) : ℝ := max 1 (ChartScales.S n)

theorem one_le_slowScale (n : ℕ) : 1 ≤ slowScale n := le_max_left _ _

/-- Reconstruction, bundling `exponent`, `inner`, `outer`, `inner_lt_outer` and the required
compatibility proofs. -/
noncomputable def reconstruction (h a b : ℝ) (hab : a < b) : CorrectionState.ReconstructionData
    where
  exponent := ChartScales.radialExponent h
  inner := a
  outer := b
  inner_lt_outer := hab
  frequency n := ChartScales.Lambda ^ commonIndex h n *
    ChartScales.Q n ^ (ChartScales.radialExponent h / 2)
  radialDirection := TorusInverse.vector .radial

/-- Operators, constructed using `CorrectionState.graphOperators`. -/
noncomputable def operators (h a b : ℝ) (hab : a < b) : MeanIncrementBounds.Operators Point :=
  CorrectionState.graphOperators (reconstruction h a b hab) (ChartScales.epsilon h)
    (fun n => ChartScales.Tg ^ commonIndex h n * ChartScales.Q n ^ (1 + h))
    ((0, 1), 0) ((1, 0), 0) (TorusInverse.vector .temporal)

@[simp] theorem operators_epsilon (h a b : ℝ) (hab : a < b) :
    (operators h a b hab).epsilon = ChartScales.epsilon h := rfl

@[simp] theorem operators_radialFrequency (h a b : ℝ) (hab : a < b) :
    (operators h a b hab).radialFrequency = ChartScales.radialCoefficient h := rfl

@[simp] theorem operators_fastCoefficient (h a b : ℝ) (hab : a < b) :
    (operators h a b hab).fastCoefficient = ChartScales.timeCoefficient h := rfl

@[simp] theorem operators_radius (h a b : ℝ) (hab : a < b) :
    (operators h a b hab).radius = Prod.fst := rfl

/-- The actual fixed `TZ -> ZT` permutation, discarding auxiliary variables. -/
noncomputable def slowCoordinates : Point →L[ℝ] Slow where
  toFun x := (x.1, (x.2.1.2, x.2.1.1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.prodMk (continuous_snd.fst.snd.prodMk continuous_snd.fst.fst)

@[simp] theorem slowCoordinates_apply (x : Point) :
    slowCoordinates x = (x.1, (x.2.1.2, x.2.1.1)) := rfl

theorem slowCoordinates_norm_le : ‖slowCoordinates‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [slowCoordinates_apply, one_mul, Prod.norm_def]
  exact max_le_max le_rfl ((max_comm _ _).le.trans (le_max_left _ _))

/-- Physical point, given by `BaseChartJets.bandPoint h (ChartScales.Q n) (slowCoordinates x)`. -/
noncomputable def physicalPoint (h : ℝ) (n : ℕ) (x : Point) : ProblemStatement.SpaceTime :=
  BaseChartJets.bandPoint h (ChartScales.Q n) (slowCoordinates x)

theorem physicalPoint_time (h : ℝ) (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    (physicalPoint h n x).1 < 1 := BaseChartJets.bandPoint_time (ChartScales.Q_pos n) hT

theorem physicalPoint_smooth (h : ℝ) (n : ℕ) : ContDiff ℝ ∞ (physicalPoint h n) := by
  change ContDiff ℝ ∞ (fun x : Point =>
    (1 - ChartScales.Q n * x.2.1.1,
      !₂[Real.sqrt (ChartScales.Q n) * x.1, 0,
        ChartScales.Q n ^ CoordinateAlgebra.D h * x.2.1.2]))
  apply ContDiff.prodMk
  · exact contDiff_const.sub (contDiff_const.mul contDiff_snd.fst.fst)
  · apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun x : Point => Real.sqrt (ChartScales.Q n) * x.1)
      exact contDiff_const.mul contDiff_fst
    · change ContDiff ℝ ∞ (fun _ : Point => (0 : ℝ))
      exact contDiff_const
    · change ContDiff ℝ ∞ (fun x : Point => ChartScales.Q n ^ CoordinateAlgebra.D h * x.2.1.2)
      exact contDiff_const.mul contDiff_snd.fst.snd

theorem operators_match_physical (h a b : ℝ) (hab : a < b) (n : ℕ) :
    PhysicalResidualTZ.MatchesAtTZ (operators h a b hab)
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (commonIndex h n)) n := by
  constructor <;> rfl

section OperatorBounds

theorem timeCoefficient_uniform (h : ℝ) (hh : 0 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n, ‖ChartScales.timeCoefficient h n‖ ≤ C := by
  let C := 1 + ∑ i ∈ Finset.range 4, ‖ChartScales.timeCoefficient h i‖
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  refine ⟨C, hC, fun n => ?_⟩
  by_cases hn : n < 4
  · have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.range 4) =>
      norm_nonneg (ChartScales.timeCoefficient h i)) (Finset.mem_range.mpr hn)
    exact hs.trans (by dsimp [C]; linarith)
  · have hSn : 1 ≤ ChartScales.S n := by
      have hn' : (4 : ℝ) ≤ n := by exact_mod_cast (le_of_not_gt hn)
      dsimp [ChartScales.S]
      nlinarith
    have ht := (ChartScales.timeCoefficient_bounds h hh (le_of_not_gt hn)).2
    rw [Real.norm_eq_abs, abs_of_pos (ChartScales.timeCoefficient_pos h n)]
    exact ht.trans ((one_div_le_one_div_of_le zero_lt_one hSn).trans (by simpa using hC))

theorem radialCoefficient_uniform (h : ℝ) (hh : 0 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n, ‖ChartScales.radialCoefficient h n‖ ≤
      C * ChartScales.epsilon h n ^ (-ChartScales.kappa) := by
  let C := 1 + ∑ i ∈ Finset.range 4, ‖ChartScales.radialCoefficient h i‖
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hpow (n : ℕ) : 1 ≤ ChartScales.epsilon h n ^ (-ChartScales.kappa) := by
    have he := Real.rpow_le_rpow_of_exponent_ge (ChartScales.epsilon_pos h n)
      (ChartScales.epsilon_le_one h hh n) (show -ChartScales.kappa ≤ (0 : ℝ) by
        norm_num [ChartScales.kappa])
    simpa only [Real.rpow_zero] using he
  refine ⟨C, hC, fun n => ?_⟩
  by_cases hn : n < 4
  · have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.range 4) =>
      norm_nonneg (ChartScales.radialCoefficient h i)) (Finset.mem_range.mpr hn)
    exact (hs.trans (by dsimp [C]; linarith)).trans
      (le_mul_of_one_le_right (zero_le_one.trans hC) (hpow n))
  · have hSn : 1 ≤ ChartScales.S n := by
      have hn' : (4 : ℝ) ≤ n := by exact_mod_cast (le_of_not_gt hn)
      dsimp [ChartScales.S]
      nlinarith
    have ht : ChartScales.timeCoefficient h n ≤ 1 :=
      ((ChartScales.timeCoefficient_bounds h hh (le_of_not_gt hn)).2).trans
        (by simpa using one_div_le_one_div_of_le zero_lt_one hSn)
    rw [Real.norm_eq_abs, abs_of_pos (ChartScales.radialCoefficient_pos h n),
      ChartScales.radialCoefficient_eq]
    exact (mul_le_of_le_one_right (Real.rpow_nonneg (ChartScales.epsilon_pos h n).le _)
      (Real.rpow_le_one (ChartScales.timeCoefficient_pos h n).le ht ChartScales.rho_pos.le)).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg (ChartScales.epsilon_pos h n).le _) hC)

/-- Moving strip, constructed using `LocalSignedRequest.movingStripData`. -/
noncomputable def movingStrip {h : ℝ} (hh : 0 ≤ h) (U : LocalSignedRequest.SlowRegion (2 * h))
    (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR) : StripData Point :=
  LocalSignedRequest.movingStripData U a b cL cR ha hcL hcR
    (ChartScales.epsilon h) slowScale (ChartScales.epsilon_pos h)
    (ChartScales.epsilon_le_one h hh) one_le_slowScale

theorem radial_unweighted {s : StripData Point} {a b : ℝ}
    (hr : ∀ x ∈ s.domain, x.1 ∈ Icc a b) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    UnweightedClass s 0 (fun _ x => g x.1) := by
  apply unweighted_of_finiteJetBounds _ _ (hg.comp contDiff_fst).contDiffOn
  intro m
  obtain ⟨C, _, hC⟩ := WeightedRadialPrimitive.cutoff_finiteJet_bound
    (E := Plane × Plane) a b g hg m
  exact ⟨C, fun j hj x hx => hC j hj x (hr x hx)⟩

theorem positive_radial_unweighted {s : StripData Point} {a b : ℝ} (ha : 0 < a)
    (hr : ∀ x ∈ s.domain, x.1 ∈ Icc a b) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) : UnweightedClass s 0 (fun _ x => g x.1) := by
  let ext : ℝ → ℝ := g ∘ TerminalEdgeFactor.positiveExtension a
  have hext : ContDiff ℝ ∞ ext := by
    apply contDiffOn_univ.mp
    exact hg.comp (TerminalEdgeFactor.positiveExtension_contDiff a).contDiffOn
      (fun x _ => TerminalEdgeFactor.positiveExtension_pos ha x)
  apply MeanIncrementBounds.class_congr (radial_unweighted hr hext)
  intro n x hx
  dsimp [ext]
  rw [TerminalEdgeFactor.positiveExtension_eq ha (hr x hx).1]

theorem movingStrip_radial_bounds {h : ℝ} (hh : 0 ≤ h)
    (U : LocalSignedRequest.SlowRegion (2 * h))
    (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    {x : Point} (hx : x ∈ (movingStrip hh U a b cL cR ha hcL hcR).domain) :
    x.1 ∈ Icc (Real.sqrt U.qlo * a) (Real.sqrt U.qhi * b) :=
  LocalSignedRequest.moving_radial_bounds U ha hx.1 hx.2.1

theorem operators_local {h a b : ℝ} (hab : a < b) (U : Set Plane) :
    LocalRankDefect.LocalOperators U (operators h a b hab) := by
  refine ⟨rfl, ?_⟩
  intro x hx
  change ContDiffWithinAt ℝ ∞ (fun y : Point =>
    ChartScales.radialExponent h * y.1 ^ (ChartScales.radialExponent h - 1)) _ x
  exact (contDiffAt_const.mul (contDiffAt_fst.rpow_const_of_ne hx.1.ne')).contDiffWithinAt

theorem operator_bounds {h : ℝ} (hh : 0 ≤ h) (U : LocalSignedRequest.SlowRegion (2 * h))
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR) :
    MeanIncrementBounds.OperatorBounds (movingStrip hh U a b cL cR ha hcL hcR)
      (operators h a b hab) ChartScales.kappa := by
  let s := movingStrip hh U a b cL cR ha hcL hcR
  have hmin : 0 < Real.sqrt U.qlo * a := mul_pos (Real.sqrt_pos.mpr U.qlo_pos) ha
  have hr : ∀ x ∈ s.domain, x.1 ∈ Icc (Real.sqrt U.qlo * a) (Real.sqrt U.qhi * b) :=
    fun _ hx => movingStrip_radial_bounds hh U a b cL cR ha hcL hcR hx
  refine ⟨rfl, ?_, ?_, ?_, ?_, by norm_num [ChartScales.kappa], ?_⟩
  · change UnweightedClass s 0 (fun _ x => RadialPullback.radialJacobian
      (ChartScales.radialExponent h) x.1)
    apply positive_radial_unweighted hmin hr
    intro x hx
    exact (contDiffAt_const.mul (contDiffAt_id.rpow_const_of_ne hx.ne')).contDiffWithinAt
  · apply positive_radial_unweighted hmin hr
    exact contDiffOn_id.inv (fun x hx => hx.ne')
  · obtain ⟨C, hC, hb⟩ := radialCoefficient_uniform h hh
    refine ⟨C, zero_le_one.trans hC, 0, fun n => ?_⟩
    simp only [pow_zero, mul_one]
    exact hb n
  · obtain ⟨C, hC, hb⟩ := timeCoefficient_uniform h hh
    refine ⟨C, zero_le_one.trans hC, 0, fun n => ?_⟩
    simp only [Real.rpow_zero, pow_zero, mul_one]
    exact hb n
  · intro x hx
    change WeightedRadialPrimitive.zeta cL cR _ _ ≤ 1
    unfold WeightedRadialPrimitive.zeta
    exact (mul_le_mul (WeightedRadialPrimitive.edge_le_one hcL.le _)
      (WeightedRadialPrimitive.edge_le_one hcR.le _) (FlatCutoff.edge_nonneg _ _)
          zero_le_one).trans_eq (by
          simp)

end OperatorBounds

section NativeGeometry

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

/-- Native strip, constructed using `movingStrip`. -/
noncomputable def nativeStrip (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) : StripData Point
    :=
  movingStrip F.data.h_pos.le U (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius
      W)
    (FinalSlowBase.edgeExponent W / 4) 1 (PrimaryTargetBounds.leftRadius_pos W)
    (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num)) zero_lt_one

theorem nativeStrip_mem (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (x : Point) :
    x ∈ (nativeStrip W U).domain ↔ x.2.1 ∈ U.carrier ∧
      PrimaryTargetBounds.profileRadius F.data.h (slowCoordinates x) ∈
        Ioo (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) := by
  rw [nativeStrip, movingStrip, LocalSignedRequest.movingStrip_domain]
  rw [PrimaryTargetBounds.profileRadius]
  change (_ ∧ _) ↔ (_ ∧ x.1 / Real.sqrt
    (BaseChartJets.normalizedCoordinates F.data.h (PrimaryTargetBounds.meanPoint x)).1 ∈ _)
  rw [PrimaryTargetBounds.meanPoint_scalar]
  rfl

theorem nativeStrip_radius (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {x : Point} (hx : x ∈ (nativeStrip W U).domain) : 0 < x.1 := by
  have hr := movingStrip_radial_bounds F.data.h_pos.le U _ _ _ _
    (PrimaryTargetBounds.leftRadius_pos W)
    (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num)) zero_lt_one hx
  exact (mul_pos (Real.sqrt_pos.mpr U.qlo_pos) (PrimaryTargetBounds.leftRadius_pos W)).trans_le hr.1

theorem nativeStrip_time (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {x : Point} (hx : x ∈ (nativeStrip W U).domain) : 0 < x.2.1.1 :=
  U.time_pos _ ((nativeStrip_mem W U x).mp hx).1

theorem nativeStrip_active (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {x : Point} (hx : x ∈ (nativeStrip W U).domain) :
    (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2 ∈ FinalSlowBase.annulus W
        := by
  have hT := nativeStrip_time W U hx
  have hr := ((nativeStrip_mem W U x).mp hx).2
  have hpos := PrimaryTargetBounds.profileRadius_pos (F := F) (p := slowCoordinates x)
    hT (nativeStrip_radius W U hx)
  have he := PrimaryTargetBounds.profileRadius_sq (F := F) (p := slowCoordinates x) hT
  have ha : (PrimaryTargetBounds.leftRadius W)^2 = 2 * NominalConeAssembly.activeLeft W :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W).le)
  have hb : (PrimaryTargetBounds.rightRadius W)^2 = 2 * NominalConeAssembly.activeRight W :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos W).le)
  have hls := sq_lt_sq' (by linarith [PrimaryTargetBounds.leftRadius_pos W]) hr.1
  have hrs := sq_lt_sq' (by linarith [PrimaryTargetBounds.rightRadius_pos W]) hr.2
  have heta := BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half
    (p := slowCoordinates x) hT
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · nlinarith
  · nlinarith
  · exact ⟨(abs_lt.mp heta).1.le, (abs_lt.mp heta).2.le⟩

theorem nativeStrip_weight (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {x : Point} (hx : x ∈ (nativeStrip W U).domain) :
    (nativeStrip W U).zeta x = FinalSlowBase.weight W
      (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2 := by
  change (LocalSignedRequest.movingStripData U _ _ _ _ _ _ _ _ _ _ _ _).zeta x = _
  rw [PrimaryTargetBounds.movingStripData_zeta]
  exact PrimaryTargetBounds.movingWeight_eq W (nativeStrip_time W U hx) (nativeStrip_radius W U hx)

/-- Insert zero auxiliary variables, retaining the explicit coordinate order. -/
noncomputable def insertSlow : Slow →L[ℝ] Point where
  toFun p := (p.1, ((p.2.2, p.2.1), 0))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  cont := continuous_fst.prodMk ((continuous_snd.snd.prodMk continuous_snd.fst).prodMk
      continuous_const)

theorem slowCoordinates_insert (p : Slow) : slowCoordinates (insertSlow p) = p := rfl

/-- Slow carrier, given by `insertSlow ⁻¹' (nativeStrip W U).domain`. -/
noncomputable def slowCarrier (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) : Set Slow :=
  insertSlow ⁻¹' (nativeStrip W U).domain

theorem slowCarrier_open (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    IsOpen (slowCarrier W U) := (nativeStrip W U).isOpen_domain.preimage insertSlow.continuous

/-- Phase domain, given by `BaseChartJets.oneDomain ι (fun _ => slowCarrier W U) (fun _ =>
slowCarrier_open W U)`. -/
noncomputable def phaseDomain (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    (ι : Type*) : PhaseJetBounds.Domain ι Slow :=
  BaseChartJets.oneDomain ι (fun _ => slowCarrier W U) (fun _ => slowCarrier_open W U)

theorem slowCoordinates_maps (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    MapsTo slowCoordinates (nativeStrip W U).domain (slowCarrier W U) := by
  intro x hx
  apply (nativeStrip_mem W U _).mpr
  exact (nativeStrip_mem W U x).mp hx

/-- Geometry radius, given by `Real.sqrt U.qlo * PrimaryTargetBounds.leftRadius W`. -/
noncomputable def geometryRadius (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) : ℝ :=
  Real.sqrt U.qlo * PrimaryTargetBounds.leftRadius W

/-- Geometry upper, given by `max 1 U.qhi + 1`. -/
noncomputable def geometryUpper (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) : ℝ :=
  max 1 U.qhi + 1

/-- Geometry bound, constructed using `max`. -/
noncomputable def geometryBound (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) : ℝ :=
  max 1 (max (Real.sqrt (max 1 U.qhi) * PrimaryTargetBounds.rightRadius W)
    (max ((max 1 U.qhi) ^ CoordinateAlgebra.D F.data.h) (max 1 U.qhi)))

theorem geometryRadius_pos (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    0 < geometryRadius W U := mul_pos (Real.sqrt_pos.mpr U.qlo_pos)
        (PrimaryTargetBounds.leftRadius_pos W)

theorem geometryUpper_pos (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    0 < geometryUpper U := by dsimp [geometryUpper]; linarith [le_max_left (1 : ℝ) U.qhi]

theorem one_le_geometryBound (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    1 ≤ geometryBound W U := le_max_left _ _

theorem native_geometry (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (ι : Type*) :
    BaseChartJets.GeometryBounds (phaseDomain W U ι) F.data.h (geometryRadius W U)
      (geometryBound W U) (U.qlo / 2) (geometryUpper U)
      (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) := by
  have hT {p : Slow} (hp : p ∈ slowCarrier W U) : 0 < p.2.2 := nativeStrip_time W U hp
  have hqm {p : Slow} (hp : p ∈ slowCarrier W U) :
      (BaseChartJets.normalizedCoordinates F.data.h p).1 ∈ Icc U.qlo U.qhi := by
    rw [BaseChartJets.normalizedCoordinates_eq]
    exact U.q_mem _ ((nativeStrip_mem W U _).mp hp).1
  have hr {p : Slow} (hp : p ∈ slowCarrier W U) :
      p.1 ∈ Icc (geometryRadius W U) (Real.sqrt U.qhi * PrimaryTargetBounds.rightRadius W) :=
    movingStrip_radial_bounds F.data.h_pos.le U _ _ _ _ (PrimaryTargetBounds.leftRadius_pos W)
      (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num)) zero_lt_one hp
  refine ⟨fun _ _ hp => hT hp, fun _ _ hp => (hr hp).1, ?_, ?_, ?_⟩
  · intro i p hp
    have ht := hT hp
    have hq := hqm hp
    have hqp := U.qlo_pos.trans_le hq.1
    have hqM := hq.2.trans (le_max_right (1 : ℝ) U.qhi)
    rw [BaseChartJets.normalizedCoordinates_eq] at hqp hqM
    have hD : 0 ≤ CoordinateAlgebra.D F.data.h := by
      unfold CoordinateAlgebra.D; linarith [F.data.h_lt_half]
    have heta := BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half ht
    rw [BaseChartJets.normalizedCoordinates_eq] at heta
    change |p.2.1 / SimilarityHomogeneity.chartQ F.data.h p ^ ((1-2*F.data.h)/2)| < 1 at heta
    have hd : (1 - 2 * F.data.h) / 2 = CoordinateAlgebra.D F.data.h := by
      unfold CoordinateAlgebra.D; ring
    rw [hd, abs_div, abs_of_pos (Real.rpow_pos_of_pos hqp _), div_lt_one (Real.rpow_pos_of_pos hqp
        _)] at heta
    have hz : |p.2.1| ≤ (max 1 U.qhi) ^ CoordinateAlgebra.D F.data.h :=
      heta.le.trans (Real.rpow_le_rpow hqp.le hqM hD)
    have hspec := SimilarityCoordinates.coordinateQ_spec (show 0 < 2*F.data.h by
        linarith [F.data.h_pos])
      (show 2*F.data.h < 1 by linarith [F.data.h_lt_half]) (p := (p.2.2,p.2.1)) ht
    have htq : p.2.2 ≤ SimilarityHomogeneity.chartQ F.data.h p := by
      have hn := mul_nonneg (sq_nonneg p.2.1) (Real.rpow_nonneg hspec.1.le (2*F.data.h))
      change p.2.2 ≤ SimilarityCoordinates.coordinateQ (2*F.data.h) (p.2.2,p.2.1)
      have he := hspec.2
      dsimp [SimilarityCoordinates.forwardScalar] at he
      linarith
    have hR := (hr hp).2.trans (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (le_max_right (1 : ℝ) U.qhi)) (PrimaryTargetBounds.rightRadius_pos W).le)
    change max |p.1| (max |p.2.1| |p.2.2|) ≤ geometryBound W U
    have hpR : 0 < p.1 := nativeStrip_radius W U hp
    rw [abs_of_pos hpR, abs_of_pos ht]
    exact (max_le_max hR (max_le_max hz (htq.trans hqM))).trans (le_max_right _ _)
  · intro i p hp
    have hq := hqm hp
    exact ⟨by
        linarith [U.qlo_pos, hq.1], by
            dsimp [geometryUpper]; linarith [hq.2, le_max_right (1 : ℝ) U.qhi]⟩
  · intro i p hp
    exact (nativeStrip_active W U hp).1

end NativeGeometry

theorem unweighted_polynomial_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : StripData Point) {D : PhaseJetBounds.Domain ℕ Slow} {f : ℕ → Slow → E}
    (hf : PhaseJetBounds.PolynomialJets (BaseChartJets.unitScale D) f)
    (hmap : ∀ n, MapsTo slowCoordinates s.domain (D.carrier n)) :
    UnweightedClass s 0 (fun n x => f n (slowCoordinates x)) := by
  refine ⟨fun _ _ _ => zero_le_one, fun n => (hf.smooth n).comp slowCoordinates.contDiff.contDiffOn
      (hmap n), ?_⟩
  intro m
  obtain ⟨C, hC, hb⟩ := BaseChartJets.polynomial_unit_bound hf m
  refine ⟨C, zero_le_one.trans hC, 0, fun n x hx j hj => ?_⟩
  have hjet := PhaseJetBounds.norm_jet_comp_linear (D.isOpen n) (hf.smooth n)
    slowCoordinates (hmap n hx) j
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f n) (slowCoordinates x)‖ * ‖slowCoordinates‖ ^ j := hjet
    _ ≤ C * 1 := mul_le_mul (hb n j hj _ (hmap n hx))
      (pow_le_one₀ (norm_nonneg _) slowCoordinates_norm_le) (by positivity) (zero_le_one.trans hC)
    _ = _ := by simp only [majorant, Real.rpow_zero, pow_zero, mul_one]

theorem envelope_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : StripData Point) {D : PhaseJetBounds.Domain ℕ Slow} {f : ℕ → Slow → E}
    {w : ℕ → ℝ} (hf : PrimaryPulseBounds.EnvelopeJets (BaseChartJets.unitScale D) (fun n _ => w n)
        f)
    (hmap : ∀ n, MapsTo slowCoordinates s.domain (D.carrier n)) {alpha : ℝ}
    (hw : ∀ n, w n = s.epsilon n ^ alpha) :
    UnweightedClass s alpha (fun n x => f n (slowCoordinates x)) := by
  refine ⟨fun _ _ _ => zero_le_one, fun n => (hf.smooth n).comp slowCoordinates.contDiff.contDiffOn
      (hmap n), ?_⟩
  intro m
  obtain ⟨C, hC, hb⟩ := BaseChartJets.envelope_unit_bound hf m
  refine ⟨C, zero_le_one.trans hC, 0, fun n x hx j hj => ?_⟩
  have hjet := PhaseJetBounds.norm_jet_comp_linear (D.isOpen n) (hf.smooth n)
    slowCoordinates (hmap n hx) j
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f n) (slowCoordinates x)‖ * ‖slowCoordinates‖ ^ j := hjet
    _ ≤ (C * w n) * 1 := mul_le_mul (hb n _ (hmap n hx) j hj)
      (pow_le_one₀ (norm_nonneg _) slowCoordinates_norm_le) (by positivity)
      (mul_nonneg (zero_le_one.trans hC) (hf.nonneg n _ (hmap n hx)))
    _ = _ := by simp only [majorant, pow_zero, mul_one, hw]

section ActualFields

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ)

/-- Radial base, given by `ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
FinalSlowBase.velocity H v upper B (physicalPoint F.data.h n x) 0`. -/
noncomputable def radialBase (n : ℕ) (x : Point) : ℝ :=
  ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
    FinalSlowBase.velocity H v upper B (physicalPoint F.data.h n x) 0

/-- Frequency base, constructed using `BaseChartJets.frequency`. -/
noncomputable def frequencyBase (n : ℕ) (x : Point) : ℝ :=
  BaseChartJets.frequency (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
    (FinalSlowBase.coefficients H v) (ChartScales.Q n) (slowCoordinates x)

/-- Axial base, constructed using `BaseChartJets.axial`. -/
noncomputable def axialBase (n : ℕ) (x : Point) : ℝ :=
  BaseChartJets.axial (FinalSlowBase.scales H v upper B) F.data.h
    (FinalSlowBase.coefficients H v) (ChartScales.Q n) (slowCoordinates x)

/-- Base, bundling `radial`, `angular`, `axial`. -/
noncomputable def base : MeanIncrementBounds.Triple Point where
  radial := radialBase H v upper B
  angular n x := x.1 * frequencyBase H v upper B n x
  axial := axialBase H v upper B

/-- Raw stress as an element of `ℝ × ℝ`. -/
noncomputable def rawStress (n : ℕ) (x : Point) : ℝ × ℝ :=
  let p := AxisymmetricFields.profilePoint (physicalPoint F.data.h n x).1
    (physicalPoint F.data.h n x).2
  ChartScales.Q n ^ (2 * CoordinateAlgebra.A F.data.h) •
    (SlowBorelBase.baseStressTheta (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
      (FinalSlowBase.coefficients H v) p,
     SlowBorelBase.baseStressAxial (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
      (FinalSlowBase.coefficients H v) p)

/-- The physical stress on positive radius, extended by zero to the other
half-line. Its actual inner zero region makes this extension smooth. -/
noncomputable def virtualStress (n : ℕ) (x : Point) : ℝ × ℝ :=
  if 0 < x.1 then rawStress H v upper B n x else 0

@[simp] theorem virtualStress_eq_raw (n : ℕ) {x : Point} (hR : 0 < x.1) :
    virtualStress H v upper B n x = rawStress H v upper B n x := by
  simp only [virtualStress, ite_eq_left hR]

@[simp] theorem virtualStress_eq_zero (n : ℕ) {x : Point} (hR : x.1 ≤ 0) :
    virtualStress H v upper B n x = 0 := by
  simp only [virtualStress, ite_eq_right (not_lt.mpr hR)]

/-- Context, bundling `operators`, `base`, `virtualTheta`, `virtualAxial`. -/
noncomputable def context (a b : ℝ) (hab : a < b) : CorrectionState.Context Point where
  operators := operators F.data.h a b hab
  base := base H v upper B
  virtualTheta n x := (virtualStress H v upper B n x).1
  virtualAxial n x := (virtualStress H v upper B n x).2

theorem axialBase_physical (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    axialBase H v upper B n x = ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (physicalPoint F.data.h n x) 2 :=
  BaseChartJets.axial_eq_normalized_velocity (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (ChartScales.Q_pos n) (FinalSlowBase.coefficients_smooth H v) hT

theorem angularBase_physical (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (hR : 0 < x.1) :
    (base H v upper B).angular n x = ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (physicalPoint F.data.h n x) 1 := by
  have he := BaseChartJets.frequency_eq_normalized_velocity
    (FinalSlowBase.scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half (ChartScales.Q_pos
        n)
    (FinalSlowBase.coefficients_smooth H v) (C := W.axis.normalization) (p := slowCoordinates x) hT
        hR
  change x.1 * BaseChartJets.frequency _ _ _ _ _ _ = _
  rw [he]
  change x.1 * (_ / x.1) = _
  simp only [FinalSlowBase.velocity, physicalPoint, slowCoordinates_apply]
  field_simp

theorem physicalComponent_smoothAt (n : ℕ) (i : Fin 3) {x : Point} (hT : 0 < x.2.1.1) :
    ContDiffAt ℝ ∞ (fun y => ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (physicalPoint F.data.h n y) i) x := by
  have hu := (FinalSlowBase.velocity_smooth H v upper B).contDiffAt
    (BaseResidual.past_isOpen.mem_nhds
      (show physicalPoint F.data.h n x ∈ BaseResidual.past from
        ⟨physicalPoint_time F.data.h n hT, mem_univ _⟩))
  exact contDiffAt_const.mul ((EuclideanSpace.proj i : ProblemStatement.Space →L[ℝ]
      ℝ).contDiff.contDiffAt.comp x
    (hu.comp x (physicalPoint_smooth F.data.h n).contDiffAt))

theorem base_smooth (U : Set Plane) (hT : ∀ p ∈ U, 0 < p.1) :
    MeanIncrementBounds.SmoothTriple (LocalRankDefect.positiveDomain U) (base H v upper B) := by
  have hs (n : ℕ) (i : Fin 3) :
      ContDiffOn ℝ ∞ (fun y => ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
        FinalSlowBase.velocity H v upper B (physicalPoint F.data.h n y) i)
        (LocalRankDefect.positiveDomain U) :=
    fun x hx => (physicalComponent_smoothAt H v upper B n i (hT x.2.1 hx.2)).contDiffWithinAt
  refine ⟨fun n => hs n 0, fun n => ?_, fun n => ?_⟩
  · exact (hs n 1).congr (fun x hx => angularBase_physical H v upper B n (hT x.2.1 hx.2) hx.1)
  · exact (hs n 2).congr (fun x hx => axialBase_physical H v upper B n (hT x.2.1 hx.2))

theorem native_estimates (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    BaseChartJets.Estimates (phaseDomain W U ℕ) ChartScales.Q (FinalSlowBase.scales H v upper B)
      F.data.h W.axis.normalization (FinalSlowBase.coefficients H v) :=
  AllBandBaseJets.final_estimates H v upper B (geometryRadius_pos W U) (one_le_geometryBound W U)
    (div_pos U.qlo_pos (by norm_num)) (geometryUpper_pos U) (NominalConeAssembly.activeLeft_pos W)
    (le_max_right _ _) (native_geometry W U ℕ) ChartScales.Q ChartScales.Q_pos ChartScales.Q_le_one

theorem frequencyBase_unweighted (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    UnweightedClass (nativeStrip W U) 0 (frequencyBase H v upper B) :=
  unweighted_polynomial_pullback (nativeStrip W U) (native_estimates H v upper B U).frequency_jets
    (fun _ => slowCoordinates_maps W U)

theorem axialBase_unweighted (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    UnweightedClass (nativeStrip W U) 0 (axialBase H v upper B) :=
  unweighted_polynomial_pullback (nativeStrip W U) (native_estimates H v upper B U).axial_jets
    (fun _ => slowCoordinates_maps W U)

theorem radialBase_unweighted (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    UnweightedClass (nativeStrip W U) 1 (radialBase H v upper B) := by
  have hr := AllBandBaseJets.final_radial_envelope H v upper B (geometryRadius_pos W U)
    (one_le_geometryBound W U) (div_pos U.qlo_pos (by norm_num)) (geometryUpper_pos U)
    (NominalConeAssembly.activeLeft_pos W) (le_max_right _ _) (native_geometry W U ℕ)
    ChartScales.Q ChartScales.Q_pos ChartScales.Q_le_one
  exact envelope_pullback (nativeStrip W U) hr (fun _ => slowCoordinates_maps W U)
    (fun n => by rw [Real.rpow_one]; rfl)

theorem base_bounds (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    MeanIncrementBounds.BaseBounds (nativeStrip W U) (base H v upper B) := by
  refine ⟨radialBase_unweighted H v upper B U, ?_, axialBase_unweighted H v upper B U⟩
  have hr : UnweightedClass (nativeStrip W U) 0 (fun _ (x : Point) => x.1) :=
    radial_unweighted (fun _ hx => movingStrip_radial_bounds F.data.h_pos.le U _ _ _ _
      (PrimaryTargetBounds.leftRadius_pos W)
      (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num)) zero_lt_one hx) contDiff_id
  have he := hr.mul (frequencyBase_unweighted H v upper B U)
  simp only [zero_add, mul_one] at he
  exact he

theorem rawStress_smooth (U : Set Plane) (hT : ∀ p ∈ U, 0 < p.1) (n : ℕ) :
    ContDiffOn ℝ ∞ (rawStress H v upper B n) (PhysicalMeanDomain.slowDomain U) := by
  let P : Point → SlowBorelBase.Chart := fun x => AxisymmetricFields.profilePoint
    (physicalPoint F.data.h n x).1 (physicalPoint F.data.h n x).2
  have hP : ContDiff ℝ ∞ P :=
    AxisymmetricFields.contDiff_profilePoint.comp (physicalPoint_smooth F.data.h n)
  intro x hx
  have ht : (P x).1 < 1 := physicalPoint_time F.data.h n (hT x.2.1 hx)
  have htheta := SlowBorelBase.physicalProfile_smoothAt (FinalSlowBase.scales_strictMono H v upper
      B)
    F.data.h_pos F.data.h_lt_half (SlowBorelBase.bundleComponent_smooth
      (FinalSlowBase.coefficients_smooth H v) W.axis.normalization 3) (-CoordinateAlgebra.A
          F.data.h - 1 / 2) ht
  have haxial := SlowBorelBase.physicalProfile_smoothAt (FinalSlowBase.scales_strictMono H v upper
      B)
    F.data.h_pos F.data.h_lt_half (SlowBorelBase.bundleComponent_smooth
      (FinalSlowBase.coefficients_smooth H v) W.axis.normalization 4) (-CoordinateAlgebra.A
          F.data.h - 1 / 2) ht
  exact ((contDiffAt_const (c := (ChartScales.Q n ^ (2 * CoordinateAlgebra.A F.data.h) : ℝ))).smul
      ((htheta.comp x hP.contDiffAt).prodMk
    (haxial.comp x hP.contDiffAt))).contDiffWithinAt

theorem rawStress_periodic (U : Set Plane) (n : ℕ) :
    PhysicalMeanDomain.PeriodicOn U (fun x => (rawStress H v upper B n x).1) ∧
    PhysicalMeanDomain.PeriodicOn U (fun x => (rawStress H v upper B n x).2) := by
  constructor <;> intro r s hs Y k <;> rfl

theorem rawStress_normalized (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    rawStress H v upper B n x =
      (ChartScales.epsilon F.data.h n *
        (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).1 ^
          (-CoordinateAlgebra.A F.data.h - 1 / 2)) •
      FinalSlowBase.normalizedStress H v upper B
        (SlowBorelBase.scaleMap (ChartScales.Q n)
          (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x))) := by
  have hq := BaseChartJets.normalizedCoordinates_q_pos F.data.h_pos F.data.h_lt_half
    (p := slowCoordinates x) hT
  have he := FinalSlowBase.physical_stress_eq_normalized H v upper B
    (p := AxisymmetricFields.profilePoint (physicalPoint F.data.h n x).1 (physicalPoint F.data.h n
        x).2)
    (physicalPoint_time F.data.h n hT)
  have hc := BaseChartJets.bandPoint_chart F.data.h_pos F.data.h_lt_half (ChartScales.Q_pos n)
    (p := slowCoordinates x) hT
  change SlowBorelBase.physicalChart F.data.h
    (AxisymmetricFields.profilePoint (physicalPoint F.data.h n x).1 (physicalPoint F.data.h n x).2)
        = _ at hc
  rw [hc] at he
  change ChartScales.Q n ^ (2 * CoordinateAlgebra.A F.data.h) • _ = _
  rw [he, smul_smul]
  congr 1
  simp only [SlowBorelBase.scaleMap_apply]
  rw [Real.mul_rpow (ChartScales.Q_pos n).le hq.le, ← mul_assoc,
    ← Real.rpow_add (ChartScales.Q_pos n)]
  have hex : 2 * CoordinateAlgebra.A F.data.h + (-CoordinateAlgebra.A F.data.h - 1 / 2) = F.data.h
      := by
    unfold CoordinateAlgebra.A
    ring
  rw [hex]
  rfl

theorem rawStress_zero_inner (n : ℕ) {x : Point} (hT : 0 < x.2.1.1)
    (hX : (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2.1 ≤
      NominalConeAssembly.activeLeft W) : rawStress H v upper B n x = 0 := by
  rw [rawStress_normalized H v upper B n hT]
  rw [show FinalSlowBase.normalizedStress H v upper B
      (SlowBorelBase.scaleMap (ChartScales.Q n)
        (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x))) = 0 from
    FinalSlowBase.normalizedStress_zero_left H v upper B _ hX, smul_zero]

theorem rawStress_zero_near_axis (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (hR : x.1 = 0) :
    rawStress H v upper B n =ᶠ[𝓝 x] 0 := by
  have hc := (BaseChartJets.normalizedCoordinates_smoothAt F.data.h_pos F.data.h_lt_half
    (p := slowCoordinates x) hT).comp x slowCoordinates.contDiff.contDiffAt
  have hzero : (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2.1 = 0 := by
    rw [BaseChartJets.normalizedCoordinates_eq]
    simp [SimilarityHomogeneity.chartX, SimilarityCoordinates.coordinateX,
      slowCoordinates_apply, hR]
  have hx : (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2.1 <
      NominalConeAssembly.activeLeft W := by rw [hzero]; exact NominalConeAssembly.activeLeft_pos W
  filter_upwards [(isOpen_lt continuous_const continuous_snd.fst.fst).mem_nhds hT,
    hc.snd.fst.continuousAt.eventually (Iio_mem_nhds hx)] with y hy hY
  exact rawStress_zero_inner H v upper B n hy hY.le

theorem virtualStress_smooth (U : Set Plane) (hT : ∀ p ∈ U, 0 < p.1) (n : ℕ) :
    ContDiffOn ℝ ∞ (virtualStress H v upper B n) (PhysicalMeanDomain.slowDomain U) := by
  intro x hx
  by_cases hR : 0 < x.1
  · have he : virtualStress H v upper B n =ᶠ[𝓝 x] rawStress H v upper B n := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hR] with y hy
      exact virtualStress_eq_raw H v upper B n hy
    exact (rawStress_smooth H v upper B U hT n x hx).congr_of_eventuallyEq
      (he.filter_mono nhdsWithin_le_nhds) he.self_of_nhds
  · have he : virtualStress H v upper B n =ᶠ[𝓝 x] 0 := by
      rcases lt_or_eq_of_le (le_of_not_gt hR) with hneg | hzero
      · filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hneg] with y hy
        exact virtualStress_eq_zero H v upper B n hy.le
      · filter_upwards [rawStress_zero_near_axis H v upper B n (hT x.2.1 hx) hzero] with y hy
        simp only [virtualStress]
        split_ifs <;> simp_all only [Pi.zero_apply]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

theorem virtualStress_periodic (U : Set Plane) (n : ℕ) :
    PhysicalMeanDomain.PeriodicOn U (fun x => (virtualStress H v upper B n x).1) ∧
    PhysicalMeanDomain.PeriodicOn U (fun x => (virtualStress H v upper B n x).2) := by
  constructor <;> intro r s hs Y k <;> rfl

theorem virtualStress_normalized (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (hR : 0 < x.1) :
    virtualStress H v upper B n x =
      (ChartScales.epsilon F.data.h n *
        (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).1 ^
          (-CoordinateAlgebra.A F.data.h - 1 / 2)) •
      FinalSlowBase.normalizedStress H v upper B
        (SlowBorelBase.scaleMap (ChartScales.Q n)
          (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x))) := by
  rw [virtualStress_eq_raw H v upper B n hR, rawStress_normalized H v upper B n hT]

theorem virtualStress_support (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    (n : ℕ) {x : Point} (hx : x.2.1 ∈ U.carrier) (hn : virtualStress H v upper B n x ≠ 0) :
    (LocalSignedRequest.profileMap (2 * F.data.h) x).1 ∈
      Icc (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) := by
  have hR : 0 < x.1 := by
    by_contra hh
    exact hn (virtualStress_eq_zero H v upper B n (le_of_not_gt hh))
  have hT := U.time_pos _ hx
  have hX : (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2.1 ∈
      Icc (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) := by
    by_contra hh
    apply hn
    rw [virtualStress_normalized H v upper B n hT hR]
    rw [show FinalSlowBase.normalizedStress H v upper B
        (SlowBorelBase.scaleMap (ChartScales.Q n)
          (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x))) = 0 from
      FinalSlowBase.normalizedStress_zero_outside H v upper B _ hh
        (let he := abs_lt.mp (BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half
          (p := slowCoordinates x) hT); ⟨he.1.le, he.2.le⟩), smul_zero]
  have hpos := PrimaryTargetBounds.profileRadius_pos (F := F) (p := slowCoordinates x) hT hR
  have he := PrimaryTargetBounds.profileRadius_sq (F := F) (p := slowCoordinates x) hT
  have ha : (PrimaryTargetBounds.leftRadius W)^2 = 2 * NominalConeAssembly.activeLeft W :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W).le)
  have hb : (PrimaryTargetBounds.rightRadius W)^2 = 2 * NominalConeAssembly.activeRight W :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos W).le)
  have hrad : PrimaryTargetBounds.profileRadius F.data.h (slowCoordinates x) ∈
      Icc (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) := by
    constructor
    · nlinarith [PrimaryTargetBounds.leftRadius_pos W, hX.1]
    · nlinarith [PrimaryTargetBounds.rightRadius_pos W, hX.2]
  change x.1 / Real.sqrt (MeanRankUpdate.chartQ (2 * F.data.h) x) ∈ _
  rw [← PrimaryTargetBounds.meanPoint_scalar (F := F) x]
  exact hrad

theorem virtualStress_movingSupport (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (n : ℕ) :
    LocalSignedRequest.MovingSupport (PrimaryTargetBounds.leftRadius W)
        (PrimaryTargetBounds.rightRadius W)
      (2 * F.data.h) U.carrier (fun x => (virtualStress H v upper B n x).1) ∧
    LocalSignedRequest.MovingSupport (PrimaryTargetBounds.leftRadius W)
        (PrimaryTargetBounds.rightRadius W)
      (2 * F.data.h) U.carrier (fun x => (virtualStress H v upper B n x).2) := by
  constructor <;> intro x hx hn <;> apply virtualStress_support H v upper B U n hx <;>
    intro he <;> simp only [he, Prod.fst_zero, Prod.snd_zero, ne_eq, not_true_eq_false] at hn

/-- Leading virtual stress, with branches according to `0 < x.1`. -/
noncomputable def leadingVirtualStress (n : ℕ) (x : Point) : ℝ × ℝ :=
  if 0 < x.1 then
    (ChartScales.epsilon F.data.h n *
      (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).1 ^
        (-CoordinateAlgebra.A F.data.h - 1/2)) •
      BaseResidual.stressPair (FinalSlowBase.coefficients H v) 0
        (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2
  else 0

theorem leadingVirtualStress_eq (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (hR : 0 < x.1) :
    leadingVirtualStress H v n x =
      (ChartScales.epsilon F.data.h n *
        (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).1 ^
          (-CoordinateAlgebra.A F.data.h - 1/2)) •
      FinalSlowBase.leadingStress v (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates
          x)).2 := by
  rw [leadingVirtualStress, ite_eq_left hR]
  congr 1
  apply FinalSlowBase.leading_stress_eq H v
  · have hp := PrimaryTargetBounds.profileRadius_sq (F := F) (p := slowCoordinates x) hT
    rw [← hp]
    positivity
  · exact (BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half
      (p := slowCoordinates x) hT).le

/-- Wave coefficients, bundling `radius`, `radialBase`, `frequencyBase`, `axialBase` and the
required compatibility proofs. -/
noncomputable def waveCoefficients (phase : ℕ → Point × ℝ → ℝ)
    (amplitude : ℕ → Point × ℝ → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → Point × ℝ → ℂ) (frequency : ℕ → ℝ) :
    LinearWaveBounds.WaveCoefficients (Point × ℝ) where
  radius _ x := x.1.1
  radialBase n x := radialBase H v upper B n x.1
  frequencyBase n x := frequencyBase H v upper B n x.1
  axialBase n x := axialBase H v upper B n x.1
  phase := phase
  amplitude := amplitude
  pressure := pressure
  frequency := frequency

theorem waveCoefficients_match (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (phase : ℕ → Point × ℝ → ℝ)
    (amplitude : ℕ → Point × ℝ → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → Point × ℝ → ℂ) (frequency : ℕ → ℝ) :
    PrimaryResidualClass.Matches (movingStrip F.data.h_pos.le U a b cL cR ha hcL hcR)
      (context H v upper B a b hab) (waveCoefficients H v upper B phase amplitude pressure
          frequency) := by
  refine ⟨rfl, rfl, ?_⟩
  intro n
  funext x i
  fin_cases i <;> rfl

/-- Radial slow, constructed using `BaseRadialJets.radial`. -/
noncomputable def radialSlow (n : ℕ) (p : Slow) : ℝ :=
  BaseRadialJets.radial (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
    (FinalSlowBase.coefficients H v) (ChartScales.Q n) p

/-- Frequency slow, constructed using `BaseChartJets.frequency`. -/
noncomputable def frequencySlow (n : ℕ) : Slow → ℝ :=
  BaseChartJets.frequency (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
    (FinalSlowBase.coefficients H v) (ChartScales.Q n)

/-- Axial slow, given by `BaseChartJets.axial (FinalSlowBase.scales H v upper B) F.data.h
(FinalSlowBase.coefficients H v) (ChartScales.Q n)`. -/
noncomputable def axialSlow (n : ℕ) : Slow → ℝ :=
  BaseChartJets.axial (FinalSlowBase.scales H v upper B) F.data.h
    (FinalSlowBase.coefficients H v) (ChartScales.Q n)

theorem radialSlow_pullback (n : ℕ) (x : Point) :
    radialSlow H v upper B n (slowCoordinates x) = radialBase H v upper B n x := rfl

theorem radialBase_stream (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    radialBase H v upper B n x = -(ChartScales.epsilon F.data.h n * x.1 / 2) *
      PhaseCalculus.slowZ (BaseRadialJets.normalizedStream (FinalSlowBase.scales H v upper B)
        F.data.h (FinalSlowBase.coefficients H v) (ChartScales.Q n)) (slowCoordinates x) :=
  BaseRadialJets.radial_eq_stream (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (ChartScales.Q_pos n) (FinalSlowBase.coefficients_smooth H v) hT

theorem radialSlow_smoothAt (n : ℕ) {p : Slow} (hp : 0 < p.2.2) :
    ContDiffAt ℝ ∞ (radialSlow H v upper B n) p := by
  exact (physicalComponent_smoothAt H v upper B n 0 (x := insertSlow p) hp).comp p
    insertSlow.contDiff.contDiffAt

/-- The slot clock can vary with the native construction. Its slow and
angular coordinates stay literal, so no phase estimate enters the binding. -/
noncomputable def nativeCoordinates (clock : ℕ → Point → ℝ) (n : ℕ) (x : Point × ℝ) :
    PhaseCalculus.Slot :=
  (slowCoordinates x.1, (x.2, clock n x.1))

theorem primaryCoefficients_match
    (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {D : PhaseJetBounds.Domain ℕ Slow} (P : PrimaryPulseBounds.PhaseConstruction D)
    (hF : P.phase.F = frequencySlow H v upper B)
    (hG : P.phase.G = axialSlow H v upper B)
    (chi : ℕ → Point × ℝ → PhaseCalculus.Slot)
    (hchi : ∀ n x, (chi n x).1 = slowCoordinates x.1)
    (amplitude : ℕ → Point × ℝ → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → Point × ℝ → ℂ) (frequency : ℕ → ℝ) :
    PrimaryResidualClass.Matches (nativeStrip W U)
      (context H v upper B (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)
        (PrimaryTargetBounds.radii_ordered W))
      (PrimaryMaterialDefect.coefficients P (radialSlow H v upper B) chi amplitude pressure
          frequency) := by
  refine ⟨rfl, ?_, ?_⟩
  · funext n x
    change (chi n x).1.1 = x.1.1
    rw [hchi]
    rfl
  · intro n
    funext x i
    simp only [PrimaryMaterialDefect.coefficients, LinearWaveResidual.complexBase,
      LinearWaveResidual.base, hchi, hF, hG, HarmonicResidual.contextBase, context, base,
      radialSlow_pullback]
    fin_cases i <;> rfl

theorem nativeCoefficients_match
    (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {D : PhaseJetBounds.Domain ℕ Slow} (P : PrimaryPulseBounds.PhaseConstruction D)
    (hF : P.phase.F = frequencySlow H v upper B)
    (hG : P.phase.G = axialSlow H v upper B)
    (clock : ℕ → Point → ℝ)
    (amplitude : ℕ → Point × ℝ → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → Point × ℝ → ℂ) (frequency : ℕ → ℝ) :
    PrimaryResidualClass.Matches (nativeStrip W U)
      (context H v upper B (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)
        (PrimaryTargetBounds.radii_ordered W))
      (PrimaryMaterialDefect.coefficients P (radialSlow H v upper B) (nativeCoordinates clock)
        amplitude pressure frequency) :=
  primaryCoefficients_match H v upper B U P hF hG (nativeCoordinates clock) (fun _ _ => rfl)
    amplitude pressure frequency

theorem radialSlow_productClass (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    (chi : ℕ → Point × ℝ → PhaseCalculus.Slot)
    (hchi : ∀ n x, (chi n x).1 = slowCoordinates x.1) :
    UnweightedClass (HarmonicWaveInteraction.productStrip (nativeStrip W U)) 1
      (fun n x => radialSlow H v upper B n (chi n x).1) := by
  apply MeanIncrementBounds.class_congr (HarmonicWaveInteraction.class_lift
    (radialBase_unweighted H v upper B U))
  intro n x hx
  change radialSlow H v upper B n (chi n x).1 = radialBase H v upper B n x.1
  rw [hchi, radialSlow_pullback]

/-- Native context, given by `context H v upper B (PrimaryTargetBounds.leftRadius W)
(PrimaryTargetBounds.rightRadius W) (PrimaryTargetBounds.radii_ordered W)`. -/
noncomputable def nativeContext : CorrectionState.Context Point :=
  context H v upper B (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)
    (PrimaryTargetBounds.radii_ordered W)

theorem native_operator_bounds (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    MeanIncrementBounds.OperatorBounds (nativeStrip W U) (nativeContext H v upper B).operators
      ChartScales.kappa :=
  operator_bounds F.data.h_pos.le U (PrimaryTargetBounds.leftRadius_pos W)
    (PrimaryTargetBounds.radii_ordered W) (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num))
    zero_lt_one

theorem native_base_bounds (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    MeanIncrementBounds.BaseBounds (nativeStrip W U) (nativeContext H v upper B).base :=
  base_bounds H v upper B U

theorem native_operators_local (U : Set Plane) :
    LocalRankDefect.LocalOperators U (nativeContext H v upper B).operators :=
  operators_local (PrimaryTargetBounds.radii_ordered W) U

theorem native_base_smooth (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    MeanIncrementBounds.SmoothTriple (LocalRankDefect.positiveDomain U.carrier)
      (nativeContext H v upper B).base := base_smooth H v upper B U.carrier U.time_pos

theorem native_radial_isSlow (U : Set Plane) :
    LocalRankDefect.IsSlowOn U (nativeContext H v upper B).base.radial := by
  intro n R p hp Y
  rfl

theorem native_angular_isSlow (U : Set Plane) :
    LocalRankDefect.IsSlowOn U (nativeContext H v upper B).base.angular := by
  intro n R p hp Y
  rfl

theorem native_axial_isSlow (U : Set Plane) :
    LocalRankDefect.IsSlowOn U (nativeContext H v upper B).base.axial := by
  intro n R p hp Y
  rfl

theorem native_matches_physical (n : ℕ) :
    PhysicalResidualTZ.MatchesAtTZ (nativeContext H v upper B).operators
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) F.data.h (commonIndex F.data.h n)) n :=
  operators_match_physical _ _ _ _ n

theorem native_stress_properties (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun x => ((nativeContext H v upper B).virtualTheta n x,
      (nativeContext H v upper B).virtualAxial n x)) (PhysicalMeanDomain.slowDomain U.carrier) ∧
    PhysicalMeanDomain.PeriodicOn U.carrier ((nativeContext H v upper B).virtualTheta n) ∧
    PhysicalMeanDomain.PeriodicOn U.carrier ((nativeContext H v upper B).virtualAxial n) ∧
    LocalSignedRequest.MovingSupport (PrimaryTargetBounds.leftRadius W)
        (PrimaryTargetBounds.rightRadius W)
      (2 * F.data.h) U.carrier ((nativeContext H v upper B).virtualTheta n) ∧
    LocalSignedRequest.MovingSupport (PrimaryTargetBounds.leftRadius W)
        (PrimaryTargetBounds.rightRadius W)
      (2 * F.data.h) U.carrier ((nativeContext H v upper B).virtualAxial n) :=
  ⟨virtualStress_smooth H v upper B U.carrier U.time_pos n,
    (virtualStress_periodic H v upper B U.carrier n).1,
    (virtualStress_periodic H v upper B U.carrier n).2,
    (virtualStress_movingSupport H v upper B U n).1,
    (virtualStress_movingSupport H v upper B U n).2⟩

end ActualFields

/-- Constructed context, given by `nativeContext FinalSlowBase.actualProfile.certificate
FinalSlowBase.actualProfile.modulation upper B`. -/
noncomputable def constructedContext (upper : ℝ) (B : ℕ) : CorrectionState.Context Point :=
  nativeContext FinalSlowBase.actualProfile.certificate FinalSlowBase.actualProfile.modulation
      upper B

theorem constructed_context_bounds (upper : ℝ) (B : ℕ)
    (U : LocalSignedRequest.SlowRegion (2 * FinalSlowBase.actualProfile.outgoing.data.h)) :
    MeanIncrementBounds.OperatorBounds (nativeStrip FinalSlowBase.actualProfile.nominal U)
      (constructedContext upper B).operators ChartScales.kappa ∧
    MeanIncrementBounds.BaseBounds (nativeStrip FinalSlowBase.actualProfile.nominal U)
      (constructedContext upper B).base ∧
    LocalRankDefect.LocalOperators U.carrier (constructedContext upper B).operators ∧
    MeanIncrementBounds.SmoothTriple (LocalRankDefect.positiveDomain U.carrier)
      (constructedContext upper B).base :=
  ⟨native_operator_bounds _ _ upper B U, native_base_bounds _ _ upper B U,
    native_operators_local _ _ upper B U.carrier, native_base_smooth _ _ upper B U⟩

end NavierStokes.BaseContextAssembly
