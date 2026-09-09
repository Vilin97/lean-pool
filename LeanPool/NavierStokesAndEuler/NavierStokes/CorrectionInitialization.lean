/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionState
public import LeanPool.NavierStokesAndEuler.NavierStokes.PartitionedCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.LinearWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.TemporalMeanUpdate
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanRankUpdate
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionStep
public import LeanPool.NavierStokesAndEuler.NavierStokes.IntegratedMeanBalances
public import LeanPool.NavierStokesAndEuler.NavierStokes.DefectIncrementBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.WaveInteractionBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.ErrorHarmonics
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryFieldAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.StateMomentBalances
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedWaveUpdate
public import LeanPool.NavierStokesAndEuler.NavierStokes.VariableGaugeMean
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryMaterialDefect
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryResidualClass
public import LeanPool.NavierStokesAndEuler.NavierStokes.LabelSumBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalRankDefect
public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformPrimaryWeights
public import LeanPool.NavierStokesAndEuler.NavierStokes.RankStateBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.MovingMomentBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeMassPreservation
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryTargetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseContextAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonBaseContext
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicPhaseAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseRankPatch
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.NativeBandExtension

@[expose] public section

/-!
# Construction of the initial correction fields

The operations in this file use the actual shifted pressure primitive, torus
inverse, stream potential, and five-row inverse.  The covariance identity is
also differentiated as an identity of functions, retaining all derivatives of
the squared partition.  Quantitative initialization is assembled below from
the estimates on these same operations.
-/

noncomputable section

namespace NavierStokes.CorrectionInitialization

open Set Filter MeasureTheory CorrectionState MovingMomentBounds
open scoped BigOperators ContDiff Topology InnerProductSpace

section Partition

open PartitionedCovariance

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {D h : ℝ} {vr vt : Plane}

/-- The actual leading covariance, including all physical partition factors. -/
noncomputable def primaryCovariance (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ)
    (P : X → (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (q : X → ℝ) (position : X → SlotColoring.Position) (target : X → Vec2)
    (i : Fin 2) (x : X) : ℝ :=
  doubleAverage (fun Y θ =>
    assembledRadial (P x) hdet (physicalOuter h N) (physicalViscosity h N)
      (chartTarget h (q x) N (target x)) (q x) (position x) Y θ *
    assembledTangent (P x) hdet (physicalOuter h N) (physicalViscosity h N)
      (chartTarget h (q x) N (target x)) (q x) (position x) i Y θ)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem primaryCovariance_eqOn (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : X → (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (q : X → ℝ) (position : X → SlotColoring.Position) (target : X → Vec2)
    {Ω : Set X} (hq : ∀ x ∈ Ω, 0 < q x) (hupper : ∀ x ∈ Ω, q x ≤ ChartScales.Q N)
    (hcone : ∀ x ∈ Ω, ∀ U, mask D (tailLabel N U) (q x) (position x) ≠ 0 →
      SmoothCovariance.StrictCone (P x U).matrix (chartTarget h (q x) N (target x) U))
    (i : Fin 2) :
    EqOn (primaryCovariance sys hdet N P q position target i)
      (fun x => q x ^ (-velocityExponent h - 1 / 2) * target x i) Ω := by
  intro x hx
  exact physical_primary_covariance sys hdet N hN (P x) (hq x hx) (hupper x hx)
    (position x) (target x) (hcone x hx) i

/-- In particular every derivative of every squared mask is included.
No commutation of a derivative with an infinite sum is assumed. -/
theorem primaryCovariance_jets (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : X → (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (q : X → ℝ) (position : X → SlotColoring.Position) (target : X → Vec2)
    {Ω : Set X} (hΩ : IsOpen Ω) (hq : ∀ x ∈ Ω, 0 < q x)
    (hupper : ∀ x ∈ Ω, q x ≤ ChartScales.Q N)
    (hcone : ∀ x ∈ Ω, ∀ U, mask D (tailLabel N U) (q x) (position x) ≠ 0 →
      SmoothCovariance.StrictCone (P x U).matrix (chartTarget h (q x) N (target x) U))
    (i : Fin 2) {x : X} (hx : x ∈ Ω) (k : ℕ) :
    iteratedFDeriv ℝ k (primaryCovariance sys hdet N P q position target i) x =
      iteratedFDeriv ℝ k
        (fun x => q x ^ (-velocityExponent h - 1 / 2) * target x i) x := by
  rw [← iteratedFDerivWithin_of_isOpen k hΩ hx,
    ← iteratedFDerivWithin_of_isOpen k hΩ hx]
  exact iteratedFDerivWithin_congr
    (primaryCovariance_eqOn sys hdet N hN P q position target hq hupper hcone i) hx k

end Partition

section Primary

open WeightedClasses LinearWaveBounds HarmonicCalculus

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The primitive data of one primary label.  Its velocity below is the
actual cutoff curl, and its pressure is the actual cutoff pressure mode. -/
structure PrimaryPiece (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  strip : StripData X
  directions : GraphDirections X
  coefficients : WaveCoefficients X
  cutoff : ℕ → X → ℝ

namespace PrimaryPiece

noncomputable def exactCoefficients (p : PrimaryPiece X) : WaveCoefficients X :=
  p.coefficients.corrected p.strip p.directions p.cutoff

noncomputable def velocity (p : PrimaryPiece X) : ℕ → X → Fin 3 → ℝ :=
  fun n x i => (vectorMode (p.coefficients.frequency n) (p.coefficients.phase n)
    (p.exactCoefficients.amplitude n) x i).re

noncomputable def tangentVelocity (p : PrimaryPiece X) : ℕ → X → Fin 3 → ℝ :=
  fun n x i => (vectorMode (p.coefficients.frequency n) (p.coefficients.phase n)
    ((p.coefficients.withCutoff p.cutoff).amplitude n) x i).re

noncomputable def pressure (p : PrimaryPiece X) : ℕ → X → ℝ :=
  fun n x => (mode (p.coefficients.frequency n) (p.coefficients.phase n)
    (p.exactCoefficients.pressure n) x).re

noncomputable def excluded (p : PrimaryPiece X) : ℕ → X → Fin 3 → ℝ :=
  fun n x i => (vectorMode (p.coefficients.frequency n) (p.coefficients.phase n)
    (excludedSlotError p.directions p.cutoff p.coefficients.amplitude 0 n) x i).re

noncomputable def linearGood (p : PrimaryPiece X) : ℕ → X → ComplexVector :=
  p.coefficients.constructedGood p.strip p.directions p.cutoff

noncomputable def linearGoodField (p : PrimaryPiece X) : ℕ → X → Fin 3 → ℝ :=
  fun n x i => (vectorMode (p.coefficients.frequency n) (p.coefficients.phase n)
    (p.linearGood n) x i).re

noncomputable def linearResidual (p : PrimaryPiece X) : ℕ → X → Fin 3 → ℝ :=
  fun n x i => (p.exactCoefficients.harmonicResidual p.strip p.directions n x i).re

/-- Primary linear residuals are evaluated on the same constructed curl
used by `velocity`; the Gaussian cutoff derivative remains explicit. -/
theorem linear_bound_and_identity (p : PrimaryPiece X) {P : ℕ → X → ℝ}
    (hp : InputBounds p.strip P (1 / 2) ChartScales.kappa p.directions p.coefficients)
    (hcut : UnweightedClass p.strip 0 p.cutoff) {R : X → ℝ}
    (hR : p.coefficients.radius = fun _ => R)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain p.strip)
      (p.coefficients.normal p.strip p.directions)) {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ n x, x ∈ p.strip.domain → b ≤ ‖p.coefficients.normal p.strip p.directions n x‖)
    (hhi : ∀ n x, x ∈ p.strip.domain → ‖p.coefficients.normal p.strip p.directions n x‖ ≤ M)
    (hK : BandBound p.strip (1 / 2) (fun n => 1 / p.coefficients.frequency n))
    (hsolve : ∀ n x, x ∈ p.strip.domain →
      p.coefficients.principal p.strip p.directions n x = 0)
    (hg : ExactConditions p.strip p.directions p.exactCoefficients) :
    WaveClass p.strip P (7 / 10) p.linearGood ∧
      ∀ n x, x ∈ p.strip.domain → ∀ i,
        p.linearResidual n x i = p.linearGoodField n x i + p.excluded n x i := by
  have hκ : ChartScales.kappa ≤ (1 / 2 : ℝ) := by norm_num [ChartScales.kappa]
  have hs : ∀ n x, x ∈ p.strip.domain →
      p.coefficients.principal p.strip p.directions n x = -(0 : ℕ → X → ComplexVector) n x := by
    simpa using hsolve
  obtain ⟨hgood, hexact⟩ := constructed_linear_wave_with_excluded hp hκ hcut hR hN hb hlo hhi hK hs
    hg
  refine ⟨hgood.mono_exponent (by norm_num [ChartScales.kappa]), ?_⟩
  intro n x hx i
  have hval := congrArg (fun z : ComplexVector => (z i).re) (hexact n x hx)
  simpa [linearResidual, linearGoodField, excluded, linearGood, exactCoefficients,
    vectorMode, mode, add_mul] using hval

/-- These are the cumulative primary bounds, proved from the tangent
coefficient and the actual curl remainder. -/
theorem cumulative_bounds (p : PrimaryPiece X) {P : ℕ → X → ℝ}
    (hp : InputBounds p.strip P (1 / 2) ChartScales.kappa p.directions p.coefficients)
    (hcut : UnweightedClass p.strip 0 p.cutoff) {R : X → ℝ}
    (hR : p.coefficients.radius = fun _ => R)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain p.strip)
      (p.coefficients.normal p.strip p.directions)) {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ n x, x ∈ p.strip.domain → b ≤ ‖p.coefficients.normal p.strip p.directions n x‖)
    (hhi : ∀ n x, x ∈ p.strip.domain → ‖p.coefficients.normal p.strip p.directions n x‖ ≤ M)
    (hK : BandBound p.strip (1 / 2) (fun n => 1 / p.coefficients.frequency n)) :
    (∀ i, WaveClass p.strip P (1 / 2) (fun n x => p.exactCoefficients.amplitude n x i)) ∧
    WaveClass p.strip P (17 / 25)
      (fun n x => p.exactCoefficients.amplitude n x -
        (p.coefficients.withCutoff p.cutoff).amplitude n x) ∧
    WaveClass p.strip P 1 p.exactCoefficients.pressure := by
  have hκ : ChartScales.kappa ≤ (1 / 2 : ℝ) := by norm_num [ChartScales.kappa]
  have hc := (hp.with_cutoff hcut).curlCorrection_class hR hN hb hlo hhi hK
  have hci i := CurlClassBounds.class_component hc i
  have hall := (hp.with_cutoff hcut).add_curl_amplitude hκ hci
  refine ⟨hall.amplitude, ?_, ?_⟩
  · have hdiff : (fun n x => p.exactCoefficients.amplitude n x -
        (p.coefficients.withCutoff p.cutoff).amplitude n x) =
      (p.coefficients.withCutoff p.cutoff).curlCorrection p.strip p.directions := by
      funext n x
      simp [exactCoefficients, WaveCoefficients.corrected, WaveCoefficients.addAmplitude]
    rw [hdiff]
    exact hc.mono_exponent (by norm_num [ChartScales.kappa])
  · convert! (hp.with_cutoff hcut).pressure using 1
    norm_num

end PrimaryPiece

end Primary

section PrimarySupport

open LinearWaveBounds HarmonicCalculus

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Taking the actual curl correction does not enlarge the closed support of
its amplitude. This also includes every derivative at a slot boundary. -/
theorem curlCorrection_tsupport_subset (a : WaveCoefficients X)
    (s : WeightedClasses.StripData X) (d : GraphDirections X) (n : ℕ) :
    tsupport (a.curlCorrection s d n) ⊆ tsupport (a.amplitude n) := by
  unfold WaveCoefficients.curlCorrection CurlClassBounds.curlRemainder
  exact (tsupport_smul_subset_right _ _).trans
    ((tsupport_smul_subset_right _ _).trans
      ((CurlClassBounds.cylindricalCurl_tsupport_subset _ _ _ _ _).trans
        (CurlClassBounds.coefficient_tsupport_subset _ _ _ _ _ _)))

namespace PrimaryPiece

theorem exactAmplitude_tsupport_subset_tangent (p : PrimaryPiece X) (n : ℕ) :
    tsupport (p.exactCoefficients.amplitude n) ⊆
      tsupport ((p.coefficients.withCutoff p.cutoff).amplitude n) :=
  (tsupport_add _ _).trans (union_subset subset_rfl (curlCorrection_tsupport_subset _ p.strip
    p.directions n))

theorem velocity_tsupport_subset_tangent (p : PrimaryPiece X) (n : ℕ) :
    tsupport (p.velocity n) ⊆ tsupport ((p.coefficients.withCutoff p.cutoff).amplitude n) := by
  apply Set.Subset.trans _ (p.exactAmplitude_tsupport_subset_tangent n)
  apply closure_mono
  intro x hx ha
  apply hx
  funext i
  simp [velocity, vectorMode, mode, ha]

theorem tangentVelocity_tsupport_subset (p : PrimaryPiece X) (n : ℕ) :
    tsupport (p.tangentVelocity n) ⊆ tsupport ((p.coefficients.withCutoff p.cutoff).amplitude n) :=
      by
  apply closure_mono
  intro x hx ha
  apply hx
  funext i
  simp [tangentVelocity, vectorMode, mode, ha]

theorem exactAmplitude_tsupport_subset (p : PrimaryPiece X) (n : ℕ) :
    tsupport (p.exactCoefficients.amplitude n) ⊆ tsupport (p.cutoff n) := by
  have hcut : tsupport ((p.coefficients.withCutoff p.cutoff).amplitude n) ⊆
      tsupport (p.cutoff n) := tsupport_smul_subset_left _ _
  exact (tsupport_add _ _).trans (union_subset hcut
    ((curlCorrection_tsupport_subset _ p.strip p.directions n).trans hcut))

theorem velocity_tsupport_subset (p : PrimaryPiece X) (n : ℕ) :
    tsupport (p.velocity n) ⊆ tsupport (p.cutoff n) := by
  apply Set.Subset.trans _ (p.exactAmplitude_tsupport_subset n)
  apply closure_mono
  intro x hx ha
  apply hx
  funext i
  simp [velocity, vectorMode, mode, ha]

theorem pressure_tsupport_subset (p : PrimaryPiece X) (n : ℕ) :
    tsupport (p.pressure n) ⊆ tsupport (p.cutoff n) := by
  apply closure_mono
  intro x hx hcut
  apply hx
  simp [pressure, exactCoefficients, WaveCoefficients.corrected,
    WaveCoefficients.addAmplitude, WaveCoefficients.withCutoff, mode, hcut]

theorem velocity_eq_zero_off_cutoff (p : PrimaryPiece X) (n : ℕ) {x : X}
    (hx : x ∉ tsupport (p.cutoff n)) : p.velocity n x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (p.velocity_tsupport_subset n h))

end PrimaryPiece

end PrimarySupport

namespace PrimaryConstruction

open WeightedClasses LinearWaveBounds

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The signed inverse quotient at twice the primary target is exactly the
positive primary square root; this identifies the two actual constructions. -/
theorem increment_twice_target {H : SmoothCovariance.Mat2} {T : SmoothCovariance.Vec2}
    (hc : SmoothCovariance.StrictCone H T) (j : Fin 2) :
    SignedCovariance.increment H T ((2 : ℝ) • T) j = SmoothCovariance.amplitudes H T j := by
  rw [SignedCovariance.increment, SmoothCovariance.inverse_formula _ _ hc.det_ne_zero,
    SignedWaveUpdate.weights_smul]
  apply (div_eq_iff (mul_ne_zero (by norm_num) (hc.amplitudes_pos j).ne')).mpr
  have hs : SmoothCovariance.amplitudes H T j ^ 2 = SmoothCovariance.weights H T j :=
    Real.sq_sqrt (hc.weights_pos j).le
  nlinarith

noncomputable def coefficients (a : WaveCoefficients X) (s : StripData X)
    (d : GraphDirections X) (H : ℕ → X → SmoothCovariance.Mat2)
    (T : ℕ → X → SmoothCovariance.Vec2) (mask : ℕ → X → ℝ)
    (v Ndot : ℕ → X → PrimaryODE.Space)
    (A : ℕ → X → PrimaryODE.Space →L[ℝ] PrimaryODE.Space) (j : Fin 2) :
    WaveCoefficients X :=
  SignedWaveUpdate.coefficients a s d H T (fun n x => (2 : ℝ) • T n x) mask v Ndot A j

noncomputable def piece (a : WaveCoefficients X) (s : StripData X)
    (d : GraphDirections X) (H : ℕ → X → SmoothCovariance.Mat2)
    (T : ℕ → X → SmoothCovariance.Vec2) (mask : ℕ → X → ℝ)
    (v Ndot : ℕ → X → PrimaryODE.Space)
    (A : ℕ → X → PrimaryODE.Space →L[ℝ] PrimaryODE.Space)
    (cutoff : ℕ → X → ℝ) (j : Fin 2) : PrimaryPiece X :=
  ⟨s, d, coefficients a s d H T mask v Ndot A j, cutoff⟩

theorem amplitude_eq_primary (a : WaveCoefficients X) (s : StripData X)
    (d : GraphDirections X) (H : ℕ → X → SmoothCovariance.Mat2)
    (T : ℕ → X → SmoothCovariance.Vec2) (mask : ℕ → X → ℝ)
    (v Ndot : ℕ → X → PrimaryODE.Space)
    (A : ℕ → X → PrimaryODE.Space →L[ℝ] PrimaryODE.Space) (j : Fin 2)
    (n : ℕ) (x : X) (hc : SmoothCovariance.StrictCone (H n x) (T n x)) :
    (coefficients a s d H T mask v Ndot A j).amplitude n x =
      PrimaryPulseBounds.primaryCoefficient s H T mask v j n x := by
  simp only [coefficients, SignedWaveUpdate.coefficients, SignedWaveUpdate.homogeneousCoefficients,
    SignedWaveUpdate.signedVector, SignedWaveUpdate.signedScalar, increment_twice_target hc,
    map_smul, PrimaryPulseBounds.primaryCoefficient, PartitionedCovariance.amplitude]

theorem twice_target_class {s : StripData X} {T : ℕ → X → SmoothCovariance.Vec2}
    (hT : ∀ i, MeanClass s 0 (fun n x => T n x i)) (i : Fin 2) :
    MeanClass s 0 (fun n x => ((2 : ℝ) • T n x) i) :=
  MeanIncrementBounds.Class.smul (hT i) 2

/-- The primary pressure and amplitude estimates come from their formulas;
the input record supplies only the fixed background geometry. -/
theorem inputBounds {s : StripData X} {d : GraphDirections X} {a : WaveCoefficients X}
    {P₀ P : ℕ → X → ℝ} {α₀ κ : ℝ} (hbase : InputBounds s P₀ α₀ κ d a)
    {H : ℕ → X → SmoothCovariance.Mat2} {T : ℕ → X → SmoothCovariance.Vec2}
    {mask : ℕ → X → ℝ} {v Ndot : ℕ → X → PrimaryODE.Space}
    {A : ℕ → X → PrimaryODE.Space →L[ℝ] PrimaryODE.Space}
    (hcov : SignedWaveUpdate.CovarianceControl s H T) (hm : UnweightedClass s 0 mask)
    (hv : MemClass s P 0 v)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    (hNdot : UnweightedClass s 0 Ndot) (hA : UnweightedClass s 0 A)
    {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hhi : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n)) (j : Fin 2) :
    InputBounds s P (1 / 2) κ d (coefficients a s d H T mask v Ndot A j) := by
  simpa only [coefficients, zero_add] using
    SignedWaveUpdate.coefficients_inputBounds hbase hcov (twice_target_class hcov.target_jets)
      hm hv hN hNdot hA hb hlo hhi hK j

/-- The only ODE used here is the constructed normalized primary fundamental.
In particular no principal equation for the output coefficient is assumed. -/
theorem phase_principal_zero {s : StripData X} {d : GraphDirections X}
    (a : WaveCoefficients X) {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (χ : ℕ → X → PhaseCalculus.Slow × ℝ)
    {T : ℕ → X → SmoothCovariance.Vec2} {mask : ℕ → X → ℝ}
    {Ndot : ℕ → X → PrimaryODE.Space}
    {A : ℕ → X → PrimaryODE.Space →L[ℝ] PrimaryODE.Space}
    (hscale : ∀ n, U.scale n = s.slow n)
    (hχ : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) χ)
    (hmap : ∀ n x, x ∈ s.domain → χ n x ∈ U.carrier n ×ˢ Ioo (0 : ℝ) 1)
    (hcov : SignedWaveUpdate.CovarianceControl s (SignedWaveUpdate.phaseMatrix F pref χ) T)
    (hm : UnweightedClass s 0 mask)
    (hHf : SignedWaveUpdate.FrozenAlong d.fast (SignedWaveUpdate.phaseMatrix F pref χ))
    (hTf : SignedWaveUpdate.FrozenAlong d.fast T) (hmf : SignedWaveUpdate.FrozenAlong d.fast mask)
    (hK : ∀ n, a.frequency n ≠ 0) (j : Fin 2)
    (hcoef : ∀ n, ContinuousOn (((F j).frame n).coefficient 1)
      (U.carrier n ×ˢ Icc 0 ((F j).L n)))
    (hkin : ∀ n x, x ∈ s.domain → ((F j).frame n).Kinematics (χ n x).1 (Icc 0 ((F j).L n)))
    (hclock : ∀ n x, x ∈ s.domain → ∀ t : ℝ,
      χ n (x + t • d.fastField n x) = ((χ n x).1, (χ n x).2 + t / (F j).L n))
    (hnormal : ∀ n x, x ∈ s.domain →
      ((F j).frame n).normal ((χ n x).1, (F j).L n * (χ n x).2) = a.normal s d n x)
    (hmotion : ∀ n x, x ∈ s.domain →
      ((F j).frame n).normalMotion ((χ n x).1, (F j).L n * (χ n x).2) = Ndot n x)
    (haction : ∀ n x, x ∈ s.domain → ∀ z : PrimaryODE.Space,
      MovingFrameODE.baseAction (((F j).frame n).F ((χ n x).1, (F j).L n * (χ n x).2))
        (((F j).frame n).shear ((χ n x).1, (F j).L n * (χ n x).2)) z = A n x z)
    (hdamp : ∀ n x, x ∈ s.domain →
      ((F j).frame n).viscosity ((χ n x).1, (F j).L n * (χ n x).2) =
        s.epsilon n * a.frequency n ^ 2 * ‖a.normal s d n x‖ ^ 2)
    (hphysical : ∀ n x, x ∈ s.domain →
      CurlClassBounds.complexify (A n x (SignedWaveUpdate.phaseFundamental F χ j n x)) =
      LinearWaveResidual.shear (a.radius n) (a.frequencyBase n) (a.axialBase n) (d.radialField n)
        (fun y => CurlClassBounds.complexify (SignedWaveUpdate.phaseFundamental F χ j n y)) x) :
    ∀ n x, x ∈ s.domain →
      (coefficients a s d (SignedWaveUpdate.phaseMatrix F pref χ) T mask
        (SignedWaveUpdate.phaseFundamental F χ j) Ndot A j).principal s d n x = 0 := by
  exact SignedWaveUpdate.phase_coefficients_principal_zero a F pref χ hscale hχ hmap hcov
    (twice_target_class hcov.target_jets) hm hHf hTf
    (fun n x t => congrArg (fun z : SmoothCovariance.Vec2 => (2 : ℝ) • z) (hTf n x t))
    hmf hK j hcoef hkin hclock hnormal hmotion haction hdamp hphysical

/-- The physical shear operator is built from the actual radial derivatives
of the two background profiles. -/
noncomputable def physicalAction (R F G : X → ℝ) (Vr : X → X) (x : X) :
    PrimaryODE.Space →L[ℝ] PrimaryODE.Space :=
  PrimaryCopyBridge.baseOperator (F x)
    !₂[R x * HarmonicCalculus.along Vr F x, HarmonicCalculus.along Vr G x]

theorem physicalAction_eq_shear (R F G : X → ℝ) (Vr : X → X)
    (v : X → PrimaryODE.Space) (x : X) :
    CurlClassBounds.complexify (physicalAction R F G Vr x (v x)) =
      LinearWaveResidual.shear R F G Vr (fun y => CurlClassBounds.complexify (v y)) x := by
  ext i
  fin_cases i <;>
    simp [physicalAction, PrimaryCopyBridge.baseOperator_apply, MovingFrameODE.baseAction,
      MovingFrameODE.pack, MovingFrameODE.tail, MovingFrameODE.unitTheta,
      CurlClassBounds.complexify, LinearWaveResidual.shear, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_neg] <;> ring

private theorem class_pair {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : StripData X} {w : ℕ → X → ℝ}
    {α : ℝ} {f : ℕ → X → E} {g : ℕ → X → F}
    (hf : MemClass s w α f) (hg : MemClass s w α g) :
    MemClass s w α (fun n x => (f n x, g n x)) := by
  simpa using (hf.map (ContinuousLinearMap.inl ℝ E F)).add
    (hg.map (ContinuousLinearMap.inr ℝ E F))

/-- The physical action has order zero because the fixed background is
independent of the radial fast variable. -/
theorem physicalAction_class {s : StripData X} {d : GraphDirections X}
    {a : WaveCoefficients X} {P : ℕ → X → ℝ} {α κ : ℝ}
    (h : InputBounds s P α κ d a) :
    UnweightedClass s 0 (fun n => physicalAction (a.radius n) (a.frequencyBase n)
      (a.axialBase n) (d.radialField n)) := by
  have hFr := d.Dr_base_mem h.frequency_base h.frequency_base_aux
  have hGr := d.Dr_base_mem h.axial_base h.axial_base_aux
  have hRFr : UnweightedClass s 0
      (fun n x => a.radius n x * d.Dr a.frequencyBase n x) := by
    simpa only [zero_add] using unweighted_mul h.radius hFr
  exact ((class_pair h.frequency_base ((class_pair hRFr hGr).map MovingFrameODE.pairCLM)).map
    PrimaryCopyBridge.baseOperatorFamily)

theorem normal_pullback (χ : X → PhaseCalculus.Slot) (ε p pz x0 : ℝ)
    (F G : PhaseCalculus.Slow → ℝ) (Vr Vθ Vz : X → X) {x : X}
    (hχ : DifferentiableAt ℝ χ x)
    (hF : DifferentiableAt ℝ F (χ x).1) (hG : DifferentiableAt ℝ G (χ x).1)
    (hr : fderiv ℝ χ x (Vr x) = PhaseCalculus.eR)
    (hθ : fderiv ℝ χ x (Vθ x) = PhaseCalculus.eTheta)
    (hz : fderiv ℝ χ x (Vz x) = ε • PhaseCalculus.eZ) :
    HarmonicCalculus.phaseNormal (fun y => (χ y).1.1) Vr Vθ Vz
      (PhaseCalculus.phase ε p pz x0 F G ∘ χ) x =
        PhaseCalculus.phaseNormal ε p pz x0 F G (χ x) := by
  have hd := fderiv_comp x (PrimaryMaterialDefect.differentiableAt_phase ε p pz x0 F G (χ x) hF hG)
    hχ
  ext i
  fin_cases i <;>
    simp [HarmonicCalculus.phaseNormal, PhaseCalculus.phaseNormal,
      HarmonicCalculus.along, hd, hr, hθ, hz]

theorem native_normal {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) (s : StripData X) (d : GraphDirections X)
    (χ : ℕ → X → PhaseCalculus.Slot) (b : ℕ → PhaseCalculus.Slow → ℝ)
    (amplitude : ℕ → X → HarmonicCalculus.ComplexVector) (pressure : ℕ → X → ℂ)
    (frequency : ℕ → ℝ) (hχ : PrimaryMaterialDefect.NativeCoordinates s d χ)
    (hmap : ∀ n, MapsTo (fun x => (χ n x).1) s.domain (U.carrier n))
    (heps : ∀ n, P.phase.epsilon n = s.epsilon n)
    (n : ℕ) {x : X} (hx : x ∈ s.domain) :
    (PrimaryMaterialDefect.coefficients P b χ amplitude pressure frequency).normal s d n x =
      P.phase.normal n ((χ n x).1, (χ n x).2.2) := by
  have hF := ((P.baseF.smooth n).contDiffAt ((U.isOpen n).mem_nhds (hmap n hx))).differentiableAt
    (by simp)
  have hG := ((P.baseG.smooth n).contDiffAt ((U.isOpen n).mem_nhds (hmap n hx))).differentiableAt
    (by simp)
  have hphase : PrimaryMaterialDefect.pulledPhase P χ n =
      PhaseCalculus.phase (s.epsilon n) (P.phase.p n) (P.phase.pz n) (P.phase.x0 n)
        (P.phase.F n) (P.phase.G n) ∘ χ n := by
    funext y
    simp [PrimaryMaterialDefect.pulledPhase, heps n]
  change HarmonicCalculus.phaseNormal (fun y => (χ n y).1.1) (d.radialField n)
    (fun _ => d.angular) (d.axialField s n) (PrimaryMaterialDefect.pulledPhase P χ n) x = _
  rw [hphase, normal_pullback (χ n) _ _ _ _ _ _ _ _ _ (hχ.differentiable n x hx)
    hF hG (hχ.radialField n hx) (hχ.angular n x hx) (hχ.axialField n hx)]
  simp only [PhaseJetBounds.PhaseFamily.normal, heps n]
  rw [PhaseCalculus.phaseNormal_formula _ _ _ _ _ _ (χ n x) (s.epsilon_pos n).ne' hF hG,
    PhaseCalculus.phaseNormal_formula _ _ _ _ _ _
      ((χ n x).1, P.phase.theta n, (χ n x).2.2) (s.epsilon_pos n).ne' hF hG]

theorem native_slow_derivative {s : StripData X} {d : GraphDirections X}
    {χ : ℕ → X → PhaseCalculus.Slot} (hχ : PrimaryMaterialDefect.NativeCoordinates s d χ)
    (F : ℕ → PhaseCalculus.Slow → ℝ) (n : ℕ) {x : X} (hx : x ∈ s.domain)
    (hF : DifferentiableAt ℝ (F n) (χ n x).1) :
    HarmonicCalculus.along (d.radialField n) (fun y => F n (χ n y).1) x =
      PhaseCalculus.slowR (F n) (χ n x).1 := by
  have hd := fderiv_comp x hF (hχ.differentiable n x hx).fst
  change (fderiv ℝ (F n ∘ fun y => (χ n y).1) x) (d.radialField n x) = _
  rw [hd, ContinuousLinearMap.comp_apply]
  have hs := congrArg Prod.fst (hχ.radialField n hx)
  change (fderiv ℝ (χ n) x (d.radialField n x)).1 = (1, 0) at hs
  rw [fderiv.fst (hχ.differentiable n x hx)]
  change (fderiv ℝ (F n) (χ n x).1) ((fderiv ℝ (χ n) x (d.radialField n x)).1) = _
  rw [hs]
  rfl

theorem native_slow_auxiliary {s : StripData X} {d : GraphDirections X}
    {χ : ℕ → X → PhaseCalculus.Slot} (hχ : PrimaryMaterialDefect.NativeCoordinates s d χ)
    (F : ℕ → PhaseCalculus.Slow → ℝ) (n : ℕ) {x : X} (hx : x ∈ s.domain)
    (hF : DifferentiableAt ℝ (F n) (χ n x).1) :
    fderiv ℝ (fun y => F n (χ n y).1) x d.auxiliary = 0 := by
  have hd := fderiv_comp x hF (hχ.differentiable n x hx).fst
  change (fderiv ℝ (F n ∘ fun y => (χ n y).1) x) d.auxiliary = _
  rw [hd, ContinuousLinearMap.comp_apply]
  have hs := congrArg Prod.fst (hχ.auxiliary n x hx)
  change (fderiv ℝ (χ n) x d.auxiliary).1 = 0 at hs
  rw [fderiv.fst (hχ.differentiable n x hx)]
  change (fderiv ℝ (F n) (χ n x).1) ((fderiv ℝ (χ n) x d.auxiliary).1) = _
  rw [hs, map_zero]

theorem native_normal_jets {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) (s : StripData X) (d : GraphDirections X)
    (χ : ℕ → X → PhaseCalculus.Slot) (b : ℕ → PhaseCalculus.Slow → ℝ)
    (amplitude : ℕ → X → HarmonicCalculus.ComplexVector) (pressure : ℕ → X → ℂ)
    (frequency : ℕ → ℝ) (hχ : PrimaryMaterialDefect.NativeCoordinates s d χ)
    (hcoords : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s)
      (fun n x => ((χ n x).1, (χ n x).2.2)))
    (hscale : ∀ n, U.scale n = s.slow n)
    (hmap : ∀ n x, x ∈ s.domain → (χ n x).1 ∈ U.carrier n ∧ (χ n x).2.2 ∈ P.V n)
    (heps : ∀ n, P.phase.epsilon n = s.epsilon n) :
    PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s)
      ((PrimaryMaterialDefect.coefficients P b χ amplitude pressure frequency).normal s d) := by
  have hn := ((PrimaryPulseBounds.EnvelopeJets.of_polynomial P.normal_jets).comp hcoords hscale
    hmap).to_polynomial (fun _ _ _ => le_rfl)
  apply hn.congr
  intro n x hx
  exact (native_normal P s d χ b amplitude pressure frequency hχ
    (fun n x hx => (hmap n x hx).1) heps n hx).symm

/-- A raw background record with zero wave and pressure is verified from
the actual phase, base jets and chart. Its material defect and phase-normal
bounds are derived here, not supplied as output estimates. -/
theorem native_background_bounds {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) (s : StripData X) (d : GraphDirections X)
    (χ : ℕ → X → PhaseCalculus.Slot) (b : ℕ → PhaseCalculus.Slow → ℝ)
    (frequency : ℕ → ℝ) {κ : ℝ}
    (hχ : PrimaryMaterialDefect.NativeCoordinates s d χ)
    (hcoords : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s)
      (fun n x => ((χ n x).1, (χ n x).2.2)))
    (hscale : ∀ n, U.scale n = s.slow n)
    (hmap : ∀ n x, x ∈ s.domain → (χ n x).1 ∈ U.carrier n ∧ (χ n x).2.2 ∈ P.V n)
    (heps : ∀ n, P.phase.epsilon n = s.epsilon n)
    (hR : ∀ n x, x ∈ s.domain → 0 < (χ n x).1.1)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hb : UnweightedClass s 1 (fun n x => b n (χ n x).1))
    (hbs : ∀ n, ContDiffOn ℝ ∞ (b n) (U.carrier n))
    (hκ : 0 ≤ κ) (hprofile : UnweightedClass s 0 (fun _ => d.radialProfile))
    (hradial : BandBound s (-κ) d.radialScale)
    (hfast : BandBound s 0 d.fastScale)
    (hfrequency : BandBound s (-(1 / 2 : ℝ)) frequency) :
    InputBounds s (fun _ _ => 1) 0 κ d
      (PrimaryMaterialDefect.coefficients P b χ 0 0 frequency) := by
  have hslow := hcoords.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ)
  have hslot := PrimaryPulseBounds.polynomial_memClass s
    (hcoords.clm (ContinuousLinearMap.snd ℝ PhaseCalculus.Slow ℝ))
  have hslowmap : ∀ n, MapsTo (fun x => (χ n x).1) s.domain (U.carrier n) :=
    fun n x hx => (hmap n x hx).1
  have hradius := hslow.clm (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
  have hinverse := hradius.inv P.r_pos
    (fun n x hx => (P.radius n _ (hslowmap n hx)).1)
    (fun n x hx => (P.radius n _ (hslowmap n hx)).2)
  have hF := PrimaryMaterialDefect.polynomial_comp_unweighted P.baseF hslow hscale hslowmap
  have hG := PrimaryMaterialDefect.polynomial_comp_unweighted P.baseG hslow hscale hslowmap
  have hnormal := native_normal_jets P s d χ b 0 0 frequency hχ hcoords hscale hmap heps
  have hw : ∀ (_n : ℕ) (x : X), x ∈ s.domain → 0 ≤ Real.sqrt (s.zeta x) * (1 : ℝ) :=
    fun _ _ _ => mul_nonneg (Real.sqrt_nonneg _) zero_le_one
  refine {
    loss_nonneg := hκ
    zeta_le_one := hζ
    radial_profile := hprofile
    radial_scale := hradial
    fast_scale := hfast
    frequency_scale := hfrequency
    radius := PrimaryPulseBounds.polynomial_memClass s hradius
    inverse_radius := PrimaryPulseBounds.polynomial_memClass s hinverse
    radial_base := hb
    frequency_base := hF
    axial_base := hG
    radial_base_aux := ?_
    frequency_base_aux := ?_
    axial_base_aux := ?_
    normal := ?_
    defect := PrimaryMaterialDefect.defect_class P s d χ b 0 0 frequency hχ
      hslow hslot hscale hslowmap heps hR hb
    amplitude := fun _ => MemClass.zero hw
    pressure := MemClass.zero hw }
  · intro n x hx
    exact native_slow_auxiliary hχ b n hx
      (((hbs n).contDiffAt ((U.isOpen n).mem_nhds (hslowmap n hx))).differentiableAt (by simp))
  · intro n x hx
    exact native_slow_auxiliary hχ P.phase.F n hx
      (((P.baseF.smooth n).contDiffAt ((U.isOpen n).mem_nhds (hslowmap n hx))).differentiableAt (by
        simp))
  · intro n x hx
    exact native_slow_auxiliary hχ P.phase.G n hx
      (((P.baseG.smooth n).contDiffAt ((U.isOpen n).mem_nhds (hslowmap n hx))).differentiableAt (by
        simp))
  · intro i
    exact PrimaryPulseBounds.polynomial_memClass s
      (hnormal.clm (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i))

theorem native_normal_range {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) (s : StripData X) (d : GraphDirections X)
    (χ : ℕ → X → PhaseCalculus.Slot) (b : ℕ → PhaseCalculus.Slow → ℝ)
    (amplitude : ℕ → X → HarmonicCalculus.ComplexVector) (pressure : ℕ → X → ℂ)
    (frequency : ℕ → ℝ) (hχ : PrimaryMaterialDefect.NativeCoordinates s d χ)
    (hmap : ∀ n x, x ∈ s.domain → (χ n x).1 ∈ U.carrier n ∧ (χ n x).2.2 ∈ P.V n)
    (heps : ∀ n, P.phase.epsilon n = s.epsilon n) (n : ℕ) {x : X} (hx : x ∈ s.domain) :
    P.b ≤ ‖(PrimaryMaterialDefect.coefficients P b χ amplitude pressure frequency).normal s d n x‖ ∧
      ‖(PrimaryMaterialDefect.coefficients P b χ amplitude pressure frequency).normal s d n x‖ ≤
        P.M ^ 2 + 3 * P.M := by
  rw [native_normal P s d χ b amplitude pressure frequency hχ (fun n x hx => (hmap n x hx).1) heps
    n hx]
  exact ⟨P.normal_range.1 n _ (hmap n x hx), P.normal_range.2 n _ (hmap n x hx)⟩

theorem frame_jets {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) :
    PhaseJetBounds.FrameJets (U.slot P.V P.openV) P.frame :=
  P.phase.frameData_jets_of_phase_comparison U P.V P.openV P.lam P.c0 P.u P.L
    P.viscosity P.B P.K P.slope P.error P.baseF P.baseG P.r_pos P.b_pos P.one_le_M
    P.constants P.epsilon_ne P.radius P.slot P.lam_bound P.c0_bound P.u_bound P.rate_bound
    P.viscosity_bound P.B_bound P.K_unit P.slope_bound P.error_small P.normal_close

theorem frame_coefficient_continuous {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) (n : ℕ) :
    ContinuousOn ((P.frame n).coefficient 1) (U.carrier n ×ˢ Icc 0 (P.L n)) :=
  (((frame_jets P).coefficient 1).smooth n).continuousOn.mono
    (fun _ hx => ⟨hx.1, P.interval n hx.2⟩)

theorem frame_tail_ne_zero {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) (n : ℕ)
    {z : PhaseCalculus.Slow × ℝ} (hz : z ∈ (U.slot P.V P.openV).carrier n) :
    MovingFrameODE.tail (P.phase.normal n z) ≠ 0 := by
  have hB : 0 < P.B n := lt_of_lt_of_le (by linarith [P.b_pos]) (P.B_bound n).1
  exact (PhaseEstimates.normal_lower_bounds hB (P.K_unit n)
    (P.error_small n z hz) (P.normal_close n z hz)).2.2.1

theorem frame_normal {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) (n : ℕ)
    {z : PhaseCalculus.Slow × ℝ} (hz : z ∈ (U.slot P.V P.openV).carrier n) :
    (P.frame n).normal z = P.phase.normal n z := by
  exact PrimaryODE.FrameData.ofNormalLocal_normal _ _ _ _ _ _ _ _ (frame_tail_ne_zero P n hz)

theorem frame_kinematics {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) (n : ℕ)
    {q : PhaseCalculus.Slow} (hq : q ∈ U.carrier n) :
    (P.frame n).Kinematics q (Icc 0 (P.L n)) := by
  have hF := ((P.baseF.smooth n).contDiffAt ((U.isOpen n).mem_nhds hq)).differentiableAt (by simp)
  have hG := ((P.baseG.smooth n).contDiffAt ((U.isOpen n).mem_nhds hq)).differentiableAt (by simp)
  apply PrimaryODE.FrameData.ofNormalLocal_kinematics
  · intro v _
    exact PhaseCalculus.hasDerivAt_phaseNormal_slot _ _ _ _ _ _ _ _ _ (P.epsilon_ne n) hF hG
  · intro v hv
    exact frame_tail_ne_zero P n ⟨hq, P.interval n hv⟩
  · intro v _
    exact PrimaryODE.referenceProfile_ne_zero
      (abs_pos.mp (lt_of_lt_of_le P.b_pos (P.c0_bound n).1)) _ _ _
  · intro v _
    exact PrimaryODE.hasDerivAt_referenceProfile (P.c0 n) (P.u n) (P.L n) v

theorem frame_normalMotion {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) (n : ℕ)
    {z : PhaseCalculus.Slow × ℝ} (hz : z ∈ (U.slot P.V P.openV).carrier n) :
    (P.frame n).normalMotion z = P.phase.velocity n z := by
  have hF := ((P.baseF.smooth n).contDiffAt ((U.isOpen n).mem_nhds hz.1)).differentiableAt (by simp)
  have hG := ((P.baseG.smooth n).contDiffAt ((U.isOpen n).mem_nhds hz.1)).differentiableAt (by simp)
  exact PrimaryODE.FrameData.ofNormalLocal_normalMotion _ _ _ _ _ _ _ _
    (PhaseCalculus.hasDerivAt_phaseNormal_slot _ _ _ _ _ _ _ _ _ (P.epsilon_ne n) hF hG)
    (frame_tail_ne_zero P n hz)

theorem native_frame_action {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) (s : StripData X) (d : GraphDirections X)
    (χ : ℕ → X → PhaseCalculus.Slot) (b : ℕ → PhaseCalculus.Slow → ℝ)
    (frequency : ℕ → ℝ) (hχ : PrimaryMaterialDefect.NativeCoordinates s d χ)
    (hmap : ∀ n, MapsTo (fun x => (χ n x).1) s.domain (U.carrier n))
    (n : ℕ) {x : X} (hx : x ∈ s.domain) (v : PrimaryODE.Space) :
    MovingFrameODE.baseAction ((P.frame n).F ((χ n x).1, (χ n x).2.2))
        ((P.frame n).shear ((χ n x).1, (χ n x).2.2)) v =
      physicalAction ((PrimaryMaterialDefect.coefficients P b χ 0 0 frequency).radius n)
        ((PrimaryMaterialDefect.coefficients P b χ 0 0 frequency).frequencyBase n)
        ((PrimaryMaterialDefect.coefficients P b χ 0 0 frequency).axialBase n)
        (d.radialField n) x v := by
  have hF := ((P.baseF.smooth n).contDiffAt ((U.isOpen n).mem_nhds (hmap n hx))).differentiableAt
    (by simp)
  have hG := ((P.baseG.smooth n).contDiffAt ((U.isOpen n).mem_nhds (hmap n hx))).differentiableAt
    (by simp)
  have hFr := native_slow_derivative hχ P.phase.F n hx hF
  have hGr := native_slow_derivative hχ P.phase.G n hx hG
  simp only [PrimaryPulseBounds.PhaseConstruction.frame, PhaseJetBounds.PhaseFamily.frameData,
    PrimaryODE.FrameData.ofNormalLocal, PhaseJetBounds.PhaseFamily.shear,
    PhaseEstimates.shearVector, PrimaryMaterialDefect.coefficients, physicalAction,
    PrimaryCopyBridge.baseOperator_apply, hFr, hGr]

noncomputable def pulseCoordinates {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) (χ : ℕ → X → PhaseCalculus.Slot) :
    ℕ → X → PhaseCalculus.Slow × ℝ :=
  fun n x => ((χ n x).1, (χ n x).2.2 / P.L n)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem pulseCoordinates_scaled {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction U) (χ : ℕ → X → PhaseCalculus.Slot)
    (n : ℕ) (x : X) : P.L n * (pulseCoordinates P χ n x).2 = (χ n x).2.2 := by
  dsimp only [pulseCoordinates]
  field_simp [(P.L_pos n).ne']

noncomputable def nativeCoefficients {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (s : StripData X) (d : GraphDirections X) (χ : ℕ → X → PhaseCalculus.Slot)
    (b : ℕ → PhaseCalculus.Slow → ℝ) (frequency : ℕ → ℝ)
    (T : ℕ → X → SmoothCovariance.Vec2) (mask : ℕ → X → ℝ) (j : Fin 2) :
    WaveCoefficients X :=
  let a := PrimaryMaterialDefect.coefficients (F j) b χ 0 0 frequency
  let ψ := pulseCoordinates (F j) χ
  coefficients a s d (SignedWaveUpdate.phaseMatrix F pref ψ) T mask
    (SignedWaveUpdate.phaseFundamental F ψ j)
    (fun n x => (F j).phase.velocity n ((χ n x).1, (χ n x).2.2))
    (fun n => physicalAction (a.radius n) (a.frequencyBase n) (a.axialBase n) (d.radialField n)) j

/-- The native coefficient has its actual primary pressure and satisfies
the principal equation by the constructed ODE. All matching assumptions
concern the chart, the scalar viscosity and the primitive slow inputs. -/
theorem native_principal_zero {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (s : StripData X) (d : GraphDirections X) (χ : ℕ → X → PhaseCalculus.Slot)
    (b : ℕ → PhaseCalculus.Slow → ℝ) (frequency : ℕ → ℝ)
    (T : ℕ → X → SmoothCovariance.Vec2) (mask : ℕ → X → ℝ) (j : Fin 2)
    (hχ : PrimaryMaterialDefect.NativeCoordinates s d χ)
    (hscale : ∀ n, U.scale n = s.slow n)
    (hcoords : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s)
      (pulseCoordinates (F j) χ))
    (hmap : ∀ n x, x ∈ s.domain → (χ n x).1 ∈ U.carrier n ∧
      (χ n x).2.2 ∈ Ioo (0 : ℝ) ((F j).L n))
    (heps : ∀ n, (F j).phase.epsilon n = s.epsilon n)
    (hν : ∀ n, (F j).viscosity n = s.epsilon n * frequency n ^ 2)
    (hcov : SignedWaveUpdate.CovarianceControl s
      (SignedWaveUpdate.phaseMatrix F pref (pulseCoordinates (F j) χ)) T)
    (hm : UnweightedClass s 0 mask)
    (hslow : ∀ n x (t : ℝ), (χ n (x + t • d.fast)).1 = (χ n x).1)
    (hTf : SignedWaveUpdate.FrozenAlong d.fast T) (hmf : SignedWaveUpdate.FrozenAlong d.fast mask)
    (hclock : ∀ n x, x ∈ s.domain → ∀ t : ℝ,
      χ n (x + t • d.fastField n x) = ((χ n x).1, (χ n x).2.1, (χ n x).2.2 + t))
    (hfrequency : ∀ n, frequency n ≠ 0) :
    ∀ n x, x ∈ s.domain → (nativeCoefficients F pref s d χ b frequency T mask j).principal s d n x
      = 0 := by
  let a := PrimaryMaterialDefect.coefficients (F j) b χ 0 0 frequency
  let ψ := pulseCoordinates (F j) χ
  have hψmap : ∀ n x, x ∈ s.domain → ψ n x ∈ U.carrier n ×ˢ Ioo (0 : ℝ) 1 := by
    intro n x hx
    exact ⟨(hmap n x hx).1, div_pos (hmap n x hx).2.1 ((F j).L_pos n),
      (div_lt_one ((F j).L_pos n)).mpr (hmap n x hx).2.2⟩
  have hV (n : ℕ) (x : X) (hx : x ∈ s.domain) :
      ((χ n x).1, (χ n x).2.2) ∈ (U.slot (F j).V (F j).openV).carrier n :=
    ⟨(hmap n x hx).1, (F j).interval n ⟨(hmap n x hx).2.1.le, (hmap n x hx).2.2.le⟩⟩
  have hHf : SignedWaveUpdate.FrozenAlong d.fast (SignedWaveUpdate.phaseMatrix F pref ψ) := by
    intro n x t
    simp only [SignedWaveUpdate.phaseMatrix, PrimaryPulseBounds.chartCovariance, ψ,
      pulseCoordinates, hslow]
  change ∀ n x, x ∈ s.domain →
    (coefficients a s d (SignedWaveUpdate.phaseMatrix F pref ψ) T mask
      (SignedWaveUpdate.phaseFundamental F ψ j)
      (fun n x => (F j).phase.velocity n ((χ n x).1, (χ n x).2.2))
      (fun n => physicalAction (a.radius n) (a.frequencyBase n) (a.axialBase n) (d.radialField n))
        j).principal s d n x = 0
  apply phase_principal_zero a F pref ψ hscale hcoords hψmap hcov hm hHf hTf hmf hfrequency j
  · exact frame_coefficient_continuous (F j)
  · intro n x hx
    exact frame_kinematics (F j) n (hmap n x hx).1
  · intro n x hx t
    simp only [ψ, pulseCoordinates, hclock n x hx t, add_div]
  · intro n x hx
    change ((F j).frame n).normal ((χ n x).1, (F j).L n * (pulseCoordinates (F j) χ n x).2) = _
    rw [pulseCoordinates_scaled, frame_normal (F j) n (hV n x hx)]
    exact (native_normal (F j) s d χ b 0 0 frequency hχ (fun n x hx => (hmap n x hx).1) heps n
      hx).symm
  · intro n x hx
    change ((F j).frame n).normalMotion ((χ n x).1, (F j).L n * (pulseCoordinates (F j) χ n x).2) =
      _
    rw [pulseCoordinates_scaled]
    exact frame_normalMotion (F j) n (hV n x hx)
  · intro n x hx v
    change MovingFrameODE.baseAction
      (((F j).frame n).F ((χ n x).1, (F j).L n * (pulseCoordinates (F j) χ n x).2))
      (((F j).frame n).shear ((χ n x).1, (F j).L n * (pulseCoordinates (F j) χ n x).2)) v = _
    rw [pulseCoordinates_scaled]
    exact native_frame_action (F j) s d χ b frequency hχ (fun n x hx => (hmap n x hx).1) n hx v
  · intro n x hx
    change (F j).viscosity n *
      ‖(F j).phase.normal n ((χ n x).1, (F j).L n * (pulseCoordinates (F j) χ n x).2)‖ ^ 2 = _
    rw [pulseCoordinates_scaled, hν, native_normal (F j) s d χ b 0 0 frequency hχ
      (fun n x hx => (hmap n x hx).1) heps n hx]
    rfl
  · intro n x _
    exact physicalAction_eq_shear _ _ _ _ _ x

/-- All primary coefficient and pressure estimates are derived from the
same native ODE and matrix. The background record has zero amplitude and
zero pressure, so no primary output estimate is an input. -/
theorem native_inputBounds {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (s : StripData X) (d : GraphDirections X) (χ : ℕ → X → PhaseCalculus.Slot)
    (b : ℕ → PhaseCalculus.Slow → ℝ) (frequency : ℕ → ℝ)
    (T : ℕ → X → SmoothCovariance.Vec2) (mask : ℕ → X → ℝ) (j : Fin 2) {κ : ℝ}
    (hχ : PrimaryMaterialDefect.NativeCoordinates s d χ)
    (hscale : ∀ n, U.scale n = s.slow n)
    (hnative : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s)
      (fun n x => ((χ n x).1, (χ n x).2.2)))
    (hcoords : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s)
      (pulseCoordinates (F j) χ))
    (hmap : ∀ n x, x ∈ s.domain → (χ n x).1 ∈ U.carrier n ∧
      (χ n x).2.2 ∈ Ioo (0 : ℝ) ((F j).L n))
    (heps : ∀ n, (F j).phase.epsilon n = s.epsilon n)
    (hR : ∀ n x, x ∈ s.domain → 0 < (χ n x).1.1)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hb : UnweightedClass s 1 (fun n x => b n (χ n x).1))
    (hbs : ∀ n, ContDiffOn ℝ ∞ (b n) (U.carrier n))
    (hκ : 0 ≤ κ) (hprofile : UnweightedClass s 0 (fun _ => d.radialProfile))
    (hradial : BandBound s (-κ) d.radialScale) (hfast : BandBound s 0 d.fastScale)
    (hfrequency : BandBound s (-(1 / 2 : ℝ)) frequency)
    (hK : BandBound s (1 / 2) (fun n => 1 / frequency n))
    (hcov : SignedWaveUpdate.CovarianceControl s
      (SignedWaveUpdate.phaseMatrix F pref (pulseCoordinates (F j) χ)) T)
    (hm : UnweightedClass s 0 mask) :
    InputBounds s (SignedWaveUpdate.phaseEnvelope F (pulseCoordinates (F j) χ) j)
      (1 / 2) κ d (nativeCoefficients F pref s d χ b frequency T mask j) := by
  let a := PrimaryMaterialDefect.coefficients (F j) b χ 0 0 frequency
  let ψ := pulseCoordinates (F j) χ
  have hV (n : ℕ) (x : X) (hx : x ∈ s.domain) :
      (χ n x).1 ∈ U.carrier n ∧ (χ n x).2.2 ∈ (F j).V n :=
    ⟨(hmap n x hx).1, (F j).interval n ⟨(hmap n x hx).2.1.le, (hmap n x hx).2.2.le⟩⟩
  have hψmap : ∀ n x, x ∈ s.domain → ψ n x ∈ U.carrier n ×ˢ Ioo (0 : ℝ) 1 := by
    intro n x hx
    exact ⟨(hmap n x hx).1, div_pos (hmap n x hx).2.1 ((F j).L_pos n),
      (div_lt_one ((F j).L_pos n)).mpr (hmap n x hx).2.2⟩
  have hbase := native_background_bounds (F j) s d χ b frequency hχ hnative hscale hV
    heps hR hζ hb hbs hκ hprofile hradial hfast hfrequency
  have hv := SignedWaveUpdate.phaseFundamental_class F ψ hscale hcoords hψmap j
  have hn := native_normal_jets (F j) s d χ b 0 0 frequency hχ hnative hscale hV heps
  have hdot := (F j).phase.polynomial_jets U (F j).V (F j).openV (F j).baseF (F j).baseG
    (F j).r_pos (F j).one_le_M (F j).constants (F j).epsilon_ne (F j).radius (F j).slot
  have hNdot : UnweightedClass s 0
      (fun n x => (F j).phase.velocity n ((χ n x).1, (χ n x).2.2)) :=
    ((PrimaryPulseBounds.EnvelopeJets.of_polynomial hdot.2.1).comp hnative hscale hV).memClass s
      (fun _ => rfl) (fun _ => rfl)
  exact inputBounds hbase hcov hm hv hn hNdot (physicalAction_class hbase) (F j).b_pos
    (fun n x hx => (native_normal_range (F j) s d χ b 0 0 frequency hχ hV heps n hx).1)
    (fun n x hx => (native_normal_range (F j) s d χ b 0 0 frequency hχ hV heps n hx).2) hK j

theorem native_amplitude_eq_uncut {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (s : StripData X) (d : GraphDirections X) (χ : ℕ → X → PhaseCalculus.Slot)
    (b : ℕ → PhaseCalculus.Slow → ℝ) (frequency : ℕ → ℝ)
    (T : ℕ → X → SmoothCovariance.Vec2) (mask : ℕ → X → ℝ) (j : Fin 2)
    (n : ℕ) (x : X)
    (hc : mask n x ≠ 0 → SmoothCovariance.StrictCone
      (SignedWaveUpdate.phaseMatrix F pref (pulseCoordinates (F j) χ) n x) (T n x)) :
    (nativeCoefficients F pref s d χ b frequency T mask j).amplitude n x =
      PrimaryPulseBounds.uncutPrimaryWave s pref (fun k => (F k).frame)
        (fun k => (F k).lam) (fun k => (F k).u) (fun k => (F k).L)
        (pulseCoordinates (F j) χ) T mask j n x := by
  by_cases hm : mask n x = 0
  · simp [nativeCoefficients, coefficients, SignedWaveUpdate.coefficients,
      SignedWaveUpdate.homogeneousCoefficients, SignedWaveUpdate.signedVector,
      SignedWaveUpdate.signedScalar, PrimaryPulseBounds.uncutPrimaryWave,
      PrimaryPulseBounds.primaryCoefficient, PartitionedCovariance.amplitude, hm]
  · exact amplitude_eq_primary _ _ _ _ _ _ _ _ _ j n x (hc hm)

/-- The canonical coefficient and the covariance pulse contain the same
Gaussian cutoff, applied exactly once. -/
theorem native_cutoff_amplitude {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (s : StripData X) (d : GraphDirections X) (χ : ℕ → X → PhaseCalculus.Slot)
    (b : ℕ → PhaseCalculus.Slow → ℝ) (frequency : ℕ → ℝ)
    (T : ℕ → X → SmoothCovariance.Vec2) (mask : ℕ → X → ℝ) (j : Fin 2)
    (n : ℕ) (x : X)
    (hc : mask n x ≠ 0 → SmoothCovariance.StrictCone
      (SignedWaveUpdate.phaseMatrix F pref (pulseCoordinates (F j) χ) n x) (T n x)) :
    ((nativeCoefficients F pref s d χ b frequency T mask j).withCutoff
      (fun n x => GaussianTailFlat.profile (pulseCoordinates (F j) χ n x).2)).amplitude n x =
        PrimaryPulseBounds.phaseWave s F pref (pulseCoordinates (F j) χ) T mask j n x := by
  change GaussianTailFlat.profile (pulseCoordinates (F j) χ n x).2 •
    (nativeCoefficients F pref s d χ b frequency T mask j).amplitude n x = _
  rw [native_amplitude_eq_uncut F pref s d χ b frequency T mask j n x hc]
  exact (PrimaryPulseBounds.primaryWave_eq_cutoff s pref (fun k => (F k).frame)
    (fun k => (F k).lam) (fun k => (F k).u) (fun k => (F k).L)
    (pulseCoordinates (F j) χ) T mask j n x).symm

theorem native_tangent {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (s : StripData X) (d : GraphDirections X) (χ : ℕ → X → PhaseCalculus.Slot)
    (b : ℕ → PhaseCalculus.Slow → ℝ) (frequency : ℕ → ℝ)
    (T : ℕ → X → SmoothCovariance.Vec2) (mask : ℕ → X → ℝ) (j : Fin 2)
    (hχ : PrimaryMaterialDefect.NativeCoordinates s d χ)
    (hmap : ∀ n x, x ∈ s.domain → (χ n x).1 ∈ U.carrier n ∧ (χ n x).2.2 ∈ (F j).V n)
    (heps : ∀ n, (F j).phase.epsilon n = s.epsilon n)
    (n : ℕ) {x : X} (hx : x ∈ s.domain) :
    HarmonicCalculus.normalDot ((nativeCoefficients F pref s d χ b frequency T mask j).normal s d n
      x)
      ((nativeCoefficients F pref s d χ b frequency T mask j).amplitude n x) = 0 := by
  apply SignedWaveUpdate.coefficients_tangent
  · intro m y hy
    have ht := SignedWaveUpdate.phaseFundamental_tangent F (pulseCoordinates (F j) χ) j m y
    change ⟪((F j).frame m).normal ((χ m y).1, (F j).L m * (pulseCoordinates (F j) χ m y).2),
      SignedWaveUpdate.phaseFundamental F (pulseCoordinates (F j) χ) j m y⟫_ℝ = 0 at ht
    rw [pulseCoordinates_scaled, frame_normal (F j) m (hmap m y hy)] at ht
    rw [native_normal (F j) s d χ b 0 0 frequency hχ (fun m y hy => (hmap m y hy).1) heps m hy]
    exact ht
  · exact hx

theorem physicalAction_invariant {θ : X} {R F G : X → ℝ} {Vr : X → X}
    (hR : CopyAngularInvariance.Invariant θ R) (hF : CopyAngularInvariance.Invariant θ F)
    (hG : CopyAngularInvariance.Invariant θ G) (hVr : CopyAngularInvariance.Invariant θ Vr) :
    CopyAngularInvariance.Invariant θ (physicalAction R F G Vr) := by
  intro x t
  simp only [physicalAction, hR x t, hF x t, hF.along hVr x t, hG.along hVr x t]

/-- Angular symmetry is derived from the coordinate translation and the
primitive slow data, including the actual reconstructed primary pressure. -/
theorem native_angularInputs {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (s : StripData X) (d : GraphDirections X) (χ : ℕ → X → PhaseCalculus.Slot)
    (b : ℕ → PhaseCalculus.Slow → ℝ) (frequency : ℕ → ℝ)
    (T : ℕ → X → SmoothCovariance.Vec2) (mask cutoff : ℕ → X → ℝ) (j : Fin 2)
    (hangle : ∀ n x (t : ℝ), χ n (x + t • d.angular) =
      ((χ n x).1, (χ n x).2.1 + t, (χ n x).2.2))
    (hc : ∀ n, ContDiffOn ℝ ∞ (χ n) s.domain)
    (hmap : ∀ n, MapsTo (fun x => (χ n x).1) s.domain (U.carrier n))
    (hT : SignedWaveUpdate.FrozenAlong d.angular T)
    (hm : SignedWaveUpdate.FrozenAlong d.angular mask)
    (hcut : SignedWaveUpdate.FrozenAlong d.angular cutoff)
    (hprofile : CopyAngularInvariance.Invariant d.angular d.radialProfile) :
    let a := PrimaryMaterialDefect.coefficients (F j) b χ 0 0 frequency
    let ψ := pulseCoordinates (F j) χ
    SignedWaveUpdate.AngularInputs s d a (SignedWaveUpdate.phaseMatrix F pref ψ) T
      (fun n x => (2 : ℝ) • T n x) mask (SignedWaveUpdate.phaseFundamental F ψ j)
      (fun n x => (F j).phase.velocity n ((χ n x).1, (χ n x).2.2))
      (fun n => physicalAction (a.radius n) (a.frequencyBase n) (a.axialBase n) (d.radialField n))
      cutoff (F j).phase.p := by
  let a := PrimaryMaterialDefect.coefficients (F j) b χ 0 0 frequency
  have hi (n : ℕ) (f : PhaseCalculus.Slow → ℝ) :
      CopyAngularInvariance.Invariant d.angular (fun x => f (χ n x).1) := by
    intro x t
    simp only [hangle]
  have hr (n : ℕ) : CopyAngularInvariance.Invariant d.angular (a.radius n) := by
    intro x t
    simp only [a, PrimaryMaterialDefect.coefficients, hangle]
  have hVr (n : ℕ) : CopyAngularInvariance.Invariant d.angular (d.radialField n) := by
    intro x t
    simp only [GraphDirections.radialField, hprofile x t]
  refine {
    radius := hr
    radial_base := fun n => hi n (b n)
    frequency_base := fun n => hi n ((F j).phase.F n)
    axial_base := fun n => hi n ((F j).phase.G n)
    radial_profile := hprofile
    phase := ?_
    phase_smooth := ?_
    matrix := ?_
    primary_target := hT
    signed_target := fun n x t => congrArg (fun v : SmoothCovariance.Vec2 => (2 : ℝ) • v) (hT n x t)
    mask := hm
    fundamental := ?_
    normal_motion := ?_
    action := fun n => physicalAction_invariant (hr n) (hi n ((F j).phase.F n))
      (hi n ((F j).phase.G n)) (hVr n)
    cutoff := hcut }
  · intro n x t
    simp only [PrimaryMaterialDefect.coefficients, PrimaryMaterialDefect.pulledPhase,
      PhaseCalculus.phase, hangle]
    ring
  · intro n
    have hF := ((F j).baseF.smooth n).comp (hc n).fst (hmap n)
    have hG := ((F j).baseG.smooth n).comp (hc n).fst (hmap n)
    exact (((contDiffOn_const.mul (hc n).snd.fst).add
      (contDiffOn_const.mul (hc n).fst.snd.fst)).add
      (contDiffOn_const.mul (hc n).fst.fst)).sub
      ((hc n).snd.snd.mul ((contDiffOn_const.mul hF).add (contDiffOn_const.mul hG)))
  · intro n x t
    simp only [SignedWaveUpdate.phaseMatrix, PrimaryPulseBounds.chartCovariance,
      pulseCoordinates, hangle]
  · intro n x t
    simp only [SignedWaveUpdate.phaseFundamental, pulseCoordinates, hangle]
  · intro n x t
    simp only [hangle]

section NativePair

open PartitionedCovariance

variable {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
  {d h : ℝ} {vr vt : Plane}

/-- Both physical columns are constructed from the same native primary
frames used above; continuity and kinematics are proved rather than stored
as fresh assumptions. -/
noncomputable def sourcePair (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (sys : SlotSystem d h vr vt) (label : UnsignedLabel) (n : ℕ)
    (q : PhaseCalculus.Slow) (hq : q ∈ U.carrier n)
    (stretch : Vec2) (hci : ∀ j, 0 < stretch j)
    (hfits : ∀ j, (F j).L n ≤ 2 * sys.radius / stretch j)
    (mode : Fin 2 → ℤ) (hmode : ∀ j, mode j ≠ 0) (phase : Fin 2 → Plane → ℝ) :
    PrimaryFieldAssembly.SourcePair PhaseCalculus.Slow sys label where
  domain := U.carrier n
  point := q
  point_mem := hq
  frame j := (F j).frame n
  lam j := (F j).lam n
  rate j := (F j).u n
  length j := (F j).L n
  length_pos j := (F j).L_pos n
  coefficient_continuous j := frame_coefficient_continuous (F j) n
  kinematics j := frame_kinematics (F j) n hq
  stretch := stretch
  stretch_pos := hci
  fits := hfits
  mode := mode
  mode_ne := hmode
  phase := phase

theorem sourcePair_matrix (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (sys : SlotSystem d h vr vt) (label : UnsignedLabel) (n : ℕ)
    (q : PhaseCalculus.Slow) (hq : q ∈ U.carrier n)
    (stretch : Vec2) (hci : ∀ j, 0 < stretch j)
    (hfits : ∀ j, (F j).L n ≤ 2 * sys.radius / stretch j)
    (mode : Fin 2 → ℤ) (hmode : ∀ j, mode j ≠ 0) (phase : Fin 2 → Plane → ℝ) :
    (sourcePair F sys label n q hq stretch hci hfits mode hmode phase).sourceMatrix =
      PrimaryPulseBounds.phaseCovariance F
        (fun j m => nativePrefactor vr vt sys.radius * stretch j * (F j).L m) n q := rfl

end NativePair

end PrimaryConstruction

section PrimaryExcluded

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

namespace PrimaryPiece

noncomputable def excludedBlock (p : PrimaryPiece (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) : HarmonicBlock D :=
  ErrorHarmonics.gaussianBlock p.directions p.cutoff p.coefficients.amplitude 0 1
    p.coefficients.frequency Φ kp

theorem excludedBlock_represents (p : PrimaryPiece (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (hcut : ∀ n, ContDiff ℝ ∞ (p.cutoff n))
    (hcutAngle : ErrorHarmonics.AngleIndependent p.cutoff)
    (ha : ErrorHarmonics.AngleIndependent p.coefficients.amplitude)
    (hphase : ∀ n x θ, p.coefficients.frequency n * p.coefficients.phase n (x, θ) =
      p.coefficients.frequency n * Φ n x + (kp n : ℝ) * θ) :
    (p.excludedBlock Φ kp).oscillation = p.excluded := by
  have he := ErrorHarmonics.gaussianBlock_represents p.directions 1 p.coefficients.frequency Φ
      p.coefficients.phase kp (source := (0 : ℕ → D × ℝ → HarmonicCalculus.ComplexVector))
      hcut hcutAngle ha (fun _ _ _ => rfl) hphase
  funext n x i
  simpa only [excludedBlock, ErrorHarmonics.gaussianField, Int.cast_one, mul_one, excluded] using
    congrArg (fun f : Oscillation D => f n x i) he

theorem excluded_angularContinuous (p : PrimaryPiece (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (hcut : ∀ n, ContDiff ℝ ∞ (p.cutoff n))
    (hcutAngle : ErrorHarmonics.AngleIndependent p.cutoff)
    (ha : ErrorHarmonics.AngleIndependent p.coefficients.amplitude)
    (hphase : ∀ n x θ, p.coefficients.frequency n * p.coefficients.phase n (x, θ) =
      p.coefficients.frequency n * Φ n x + (kp n : ℝ) * θ) :
    CorrectionStep.AngularContinuous p.excluded := by
  rw [← excludedBlock_represents p Φ kp hcut hcutAngle ha hphase]
  intro n x i
  exact Complex.continuous_re.comp (HarmonicFields.field_angular_continuous _ _ _ _ _)

/-- The retained primary Gaussian error is a genuine nonzero angular
harmonic, so its actual angular mean vanishes exactly. -/
theorem excluded_mean_zero (p : PrimaryPiece (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) (hkp : ∀ n, kp n ≠ 0)
    (hcut : ∀ n, ContDiff ℝ ∞ (p.cutoff n))
    (hcutAngle : ErrorHarmonics.AngleIndependent p.cutoff)
    (ha : ErrorHarmonics.AngleIndependent p.coefficients.amplitude)
    (hphase : ∀ n x θ, p.coefficients.frequency n * p.coefficients.phase n (x, θ) =
      p.coefficients.frequency n * Φ n x + (kp n : ℝ) * θ) :
    CorrectionStep.angularMeanVector p.excluded = 0 := by
  rw [← excludedBlock_represents p Φ kp hcut hcutAngle ha hphase]
  funext n x i
  change HarmonicResidual.realAngularMean (fun θ =>
    (HarmonicFields.field ((p.excludedBlock Φ kp).velocity n i)
      (p.coefficients.frequency n) (Φ n) (kp n) (x, θ)).re) = 0
  rw [HarmonicResidual.realAngularMean_field _ _ _ (hkp n) x]
  let a : D → ℂ := fun y => LinearWaveBounds.excludedSlotError p.directions p.cutoff
    p.coefficients.amplitude 0 n (y, 0) i / 2
  change ((Finsupp.single (1 : ℤ) a 0 x) +
    star (Finsupp.single (1 : ℤ) a (-0) x)).re = 0
  simp

end PrimaryPiece

end PrimaryExcluded

section Construction

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {ι : Type}

/-- Initial mean velocities vanish; the primary fields are actual finite
label sums of cutoff curls and their homogeneous pressure modes. -/
noncomputable def seed (labels : Finset ι) (pieces : ι → PrimaryPiece (D × ℝ))
    (baseError : Oscillation D) : State D where
  mean := ⟨0, 0, 0⟩
  pressure := 0
  oscillation := ∑ l ∈ labels, (pieces l).velocity
  oscillatoryPressure := ∑ l ∈ labels, (pieces l).pressure
  errors := ⟨baseError, ∑ l ∈ labels, (pieces l).excluded, 0⟩

/-- The active labels may depend on the chart band. No bound on their total
cardinality is inserted into the construction or its class estimates. -/
noncomputable def bandSeed (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (D × ℝ))
    (baseError : Oscillation D) : State D where
  mean := ⟨0, 0, 0⟩
  pressure := 0
  oscillation := LabelSumBounds.fieldSum labels (fun l => (pieces l).velocity)
  oscillatoryPressure := fun n p => ∑ l ∈ labels n, (pieces l).pressure n p
  errors := ⟨baseError, LabelSumBounds.fieldSum labels (fun l => (pieces l).excluded), 0⟩

theorem bandSeed_covariance (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (D × ℝ))
    (baseError : Oscillation D) (i j : Fin 3) :
    (bandSeed labels pieces baseError).covariance i j =
      bilinearCovariance (LabelSumBounds.fieldSum labels (fun l => (pieces l).velocity))
        (LabelSumBounds.fieldSum labels (fun l => (pieces l).velocity)) i j := rfl

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

noncomputable def primaryStage (p : ReconstructionData) (c : Context (Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S)) : State (Lift S) :=
  reconstructPressure p c (seed labels pieces baseError)

noncomputable def afterTemporal (p : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S)) : State (Lift S) :=
  temporalStage p h axial c (primaryStage p c labels pieces baseError)

noncomputable def afterRank (p : ReconstructionData) (r : RankData S) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S)) : State (Lift S) :=
  rankStage p r axial c (afterTemporal p h axial c labels pieces baseError)

/-- The current pressure alias is retained once, after the final pressure
reconstruction.  Earlier obsolete pressure aliases are not accumulated. -/
noncomputable def retainPressureAlias (p : ReconstructionData) (c : Context (Lift S))
    (u : State (Lift S)) : State (Lift S) :=
  { u with errors := ⟨u.errors.base, u.errors.gaussian,
      u.errors.aliasError + pressureAlias p c u⟩ }

noncomputable def initialized (p : ReconstructionData) (r : RankData S) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S)) : State (Lift S) :=
  retainPressureAlias p c (afterRank p r h axial c labels pieces baseError)

omit [FiniteDimensional ℝ S] in
theorem initialized_oscillation (p : ReconstructionData) (r : RankData S) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S)) :
    (initialized p r h axial c labels pieces baseError).oscillation =
      ∑ l ∈ labels, (pieces l).velocity := by
  simp [initialized, retainPressureAlias, afterRank, afterTemporal, primaryStage, seed,
    rankStage, temporalStage, reconstructPressure, State.addIncrement]

omit [FiniteDimensional ℝ S] in
theorem initialized_errors (p : ReconstructionData) (r : RankData S) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S)) :
    (initialized p r h axial c labels pieces baseError).errors.total =
      baseError + (∑ l ∈ labels, (pieces l).excluded) +
        temporalAlias p h c (primaryStage p c labels pieces baseError) +
        pressureAlias p c (afterRank p r h axial c labels pieces baseError) := by
  simp only [initialized, retainPressureAlias, ExcludedErrors.total]
  simp only [afterRank, rankStage, reconstructPressure, State.addIncrement,
    ExcludedErrors.add, ExcludedErrors.zero, afterTemporal, temporalStage,
    primaryStage, seed, add_zero, zero_add]
  abel

omit [FiniteDimensional ℝ S] in
theorem initialized_error_components (p : ReconstructionData) (r : RankData S) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S)) :
    (initialized p r h axial c labels pieces baseError).errors.base = baseError ∧
    (initialized p r h axial c labels pieces baseError).errors.gaussian =
      ∑ l ∈ labels, (pieces l).excluded ∧
    (initialized p r h axial c labels pieces baseError).errors.aliasError =
      temporalAlias p h c (primaryStage p c labels pieces baseError) +
        pressureAlias p c (afterRank p r h axial c labels pieces baseError) := by
  simp [initialized, retainPressureAlias, afterRank, afterTemporal, primaryStage, seed,
    rankStage, temporalStage, reconstructPressure, State.addIncrement, ExcludedErrors.add,
    ExcludedErrors.zero]

omit [FiniteDimensional ℝ S] in
theorem initialized_reconstructed (p : ReconstructionData) (r : RankData S) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S)) :
    reconstructPressure p c (initialized p r h axial c labels pieces baseError) =
      initialized p r h axial c labels pieces baseError := rfl

/-- The two actual integrated masses remain zero through both updates. -/
theorem initialized_zeroMasses (p : ReconstructionData) (r : RankData S) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S))
    (ha : 0 < p.inner) (hd : 0 < p.exponent)
    (hθ : ∀ n, ContDiff ℝ ∞ ((primaryStage p c labels pieces baseError).thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ ((primaryStage p c labels pieces baseError).axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift
      ((primaryStage p c labels pieces baseError).thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift
      ((primaryStage p c labels pieces baseError).axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported p.inner p.outer
      ((primaryStage p c labels pieces baseError).axialResidual c n))
    (hg : DefectIncrementBounds.RankGeometry p r c (afterTemporal p h axial c labels pieces
      baseError))
    (hm : DefectIncrementBounds.ShellTriple p.inner p.outer
      (afterTemporal p h axial c labels pieces baseError).mean)
    (hi : DefectIncrementBounds.ShellTriple p.inner p.outer
      (rankIncrement p r axial c (afterTemporal p h axial c labels pieces baseError))) :
    ZeroMasses (initialized p r h axial c labels pieces baseError) := by
  have hzero : ZeroMasses (primaryStage p c labels pieces baseError) := by
    constructor <;> funext n x <;>
      simp [primaryStage, reconstructPressure, seed, radialMoment, PressureStream.pressureMass,
        PressureStream.torusAverage, PressureStream.torusInner]
  obtain ⟨hθm, hzm⟩ := CorrectionStep.temporalStage_preserve_masses p h axial c
    (primaryStage p c labels pieces baseError) ha hd (fun _ => continuous_const)
    (fun _ => continuous_const) hθ hz hpθ hpz hsz
  have ht : ZeroMasses (afterTemporal p h axial c labels pieces baseError) :=
    ⟨hθm.trans hzero.1, hzm.trans hzero.2⟩
  exact hg.zeroMasses axial hm hi ht

omit [FiniteDimensional ℝ S] in
/-- The actual current pressure reconstruction controls the radial residual
by the computed pressure defect, with its exact alias retained. -/
theorem initialized_radial_residual (p : ReconstructionData) (r : RankData S) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S)) (ha : 0 < p.inner) (hd : 0 < p.exponent)
    (hoperator : ∀ f : ScalarField (Lift S), ∀ n x, c.operators.dr f n x =
      PressureStream.graphDr (PressureStream.physicalSpeed p.exponent (p.frequency n))
        (0, p.radialDirection) (f n) x)
    (hsmooth : ∀ n, ContDiff ℝ ∞ ((initialized p r h axial c labels pieces baseError).gr c n))
    (hsupport : ∀ n, RadialAlias.RadiallySupported p.inner p.outer
      ((initialized p r h axial c labels pieces baseError).gr c n))
    (n : ℕ) (x : Lift S) :
    (initialized p r h axial c labels pieces baseError).radialResidual c n x -
      pressureAlias p c (afterRank p r h axial c labels pieces baseError) n (x, 0) 0 =
      -PressureStream.rho p.inner p.outer p.inner_lt_outer x.1 *
        pressureDefect c (initialized p r h axial c labels pieces baseError) n x.2.1 := by
  have he := CorrectionStep.reconstructed_radial_minus_alias p ha hd c
    (initialized p r h axial c labels pieces baseError) hoperator hsmooth hsupport n x
  rw [initialized_reconstructed] at he
  exact he

end Construction

namespace GaugeInitialization

open VariableGaugeMean

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] {ι : Type}

/-- The physical-gauge pipeline uses the actual slow-variable-dependent
cutoff endpoints and an explicit common torus index at every step. -/
noncomputable def primaryStage (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) : State (PressureStream.Lift S) :=
  reconstructState g c (seed labels pieces baseError)

noncomputable def afterTemporal (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) : State (PressureStream.Lift S) :=
  temporalStageState g h index axial c (primaryStage g c labels pieces baseError)

noncomputable def afterRank (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) : State (PressureStream.Lift S) :=
  rankStageState g r axial c (afterTemporal g h index axial c labels pieces baseError)

noncomputable def retainPressureAlias (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : State (PressureStream.Lift S) :=
  { u with errors := ⟨u.errors.base, u.errors.gaussian,
      u.errors.aliasError + pressureAliasState g c u⟩ }

noncomputable def initialized (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) : State (PressureStream.Lift S) :=
  retainPressureAlias g c (afterRank g r h index axial c labels pieces baseError)

theorem initialized_oscillation (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) :
    (initialized g r h index axial c labels pieces baseError).oscillation =
      ∑ l ∈ labels, (pieces l).velocity := by
  simp [initialized, retainPressureAlias, afterRank, afterTemporal, primaryStage, seed,
    rankStageState, temporalStageState, reconstructState, State.addIncrement]

theorem initialized_error_components (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) :
    (initialized g r h index axial c labels pieces baseError).errors.base = baseError ∧
    (initialized g r h index axial c labels pieces baseError).errors.gaussian =
      ∑ l ∈ labels, (pieces l).excluded ∧
    (initialized g r h index axial c labels pieces baseError).errors.aliasError =
      temporalAliasState g h index c (primaryStage g c labels pieces baseError) +
        pressureAliasState g c (afterRank g r h index axial c labels pieces baseError) := by
  simp [initialized, retainPressureAlias, afterRank, afterTemporal, primaryStage, seed,
    rankStageState, temporalStageState, reconstructState, State.addIncrement,
    ExcludedErrors.add, ExcludedErrors.zero]

theorem initialized_errors (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) :
    (initialized g r h index axial c labels pieces baseError).errors.total =
      baseError + (∑ l ∈ labels, (pieces l).excluded) +
        temporalAliasState g h index c (primaryStage g c labels pieces baseError) +
        pressureAliasState g c (afterRank g r h index axial c labels pieces baseError) := by
  obtain ⟨hb, hgauss, ha⟩ := initialized_error_components g r h index axial c labels pieces
    baseError
  simp only [ExcludedErrors.total, hb, hgauss, ha]
  abel

theorem initialized_reconstructed (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) :
    reconstructState g c (initialized g r h index axial c labels pieces baseError) =
      initialized g r h index axial c labels pieces baseError := rfl

end GaugeInitialization

namespace GaugeInitialization

open VariableGaugeMean

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] {ι : Type}

noncomputable def primaryBands (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) : State (PressureStream.Lift S) :=
  reconstructState g c (bandSeed labels pieces baseError)

noncomputable def temporalBands (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) : State (PressureStream.Lift S) :=
  temporalStageState g h index axial c (primaryBands g c labels pieces baseError)

noncomputable def rankBands (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) : State (PressureStream.Lift S) :=
  rankStageState g r axial c (temporalBands g h index axial c labels pieces baseError)

noncomputable def initializedBands (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) : State (PressureStream.Lift S) :=
  retainPressureAlias g c (rankBands g r h index axial c labels pieces baseError)

theorem initializedBands_oscillation (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) :
    (initializedBands g r h index axial c labels pieces baseError).oscillation =
      LabelSumBounds.fieldSum labels (fun l => (pieces l).velocity) := by
  simp [initializedBands, retainPressureAlias, rankBands, temporalBands, primaryBands, bandSeed,
    rankStageState, temporalStageState, reconstructState, State.addIncrement]

theorem initializedBands_error_components (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) :
    (initializedBands g r h index axial c labels pieces baseError).errors.base = baseError ∧
    (initializedBands g r h index axial c labels pieces baseError).errors.gaussian =
      LabelSumBounds.fieldSum labels (fun l => (pieces l).excluded) ∧
    (initializedBands g r h index axial c labels pieces baseError).errors.aliasError =
      temporalAliasState g h index c (primaryBands g c labels pieces baseError) +
        pressureAliasState g c (rankBands g r h index axial c labels pieces baseError) := by
  simp [initializedBands, retainPressureAlias, rankBands, temporalBands, primaryBands, bandSeed,
    rankStageState, temporalStageState, reconstructState, State.addIncrement,
    ExcludedErrors.add, ExcludedErrors.zero]

theorem initializedBands_errors (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) :
    (initializedBands g r h index axial c labels pieces baseError).errors.total =
      baseError + LabelSumBounds.fieldSum labels (fun l => (pieces l).excluded) +
        temporalAliasState g h index c (primaryBands g c labels pieces baseError) +
        pressureAliasState g c (rankBands g r h index axial c labels pieces baseError) := by
  obtain ⟨hb, hgauss, ha⟩ := initializedBands_error_components g r h index axial c labels pieces
    baseError
  simp only [ExcludedErrors.total, hb, hgauss, ha]
  abel

theorem initializedBands_reconstructed (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) :
    reconstructState g c (initializedBands g r h index axial c labels pieces baseError) =
      initializedBands g r h index axial c labels pieces baseError := rfl

end GaugeInitialization

section InitializedExcludedMean

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {ι : Type}

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularMeanVector_sum (labels : Finset ι) (f : ι → Oscillation D)
    (hc : ∀ l ∈ labels, CorrectionStep.AngularContinuous (f l)) :
    CorrectionStep.angularMeanVector (∑ l ∈ labels, f l) =
      ∑ l ∈ labels, CorrectionStep.angularMeanVector (f l) := by
  funext n x i
  simpa only [CorrectionStep.angularMeanVector, angularAverage,
    HarmonicResidual.realAngularMean, HarmonicFields.period, Finset.sum_apply] using
    HarmonicResidual.realAngularMean_sum labels (fun l θ => f l n (x, θ) i)
      (fun l hl => hc l hl n x i)

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The stored base error cancels once. The primary Gaussian means vanish,
and the two literal alias fields remain with their actual signs. -/
theorem initialized_meanGood (p : ReconstructionData) (r : RankData S) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S))
    (hb : CorrectionStep.AngularContinuous baseError)
    (hg : ∀ l ∈ labels, CorrectionStep.AngularContinuous (pieces l).excluded)
    (hz : ∀ l ∈ labels, CorrectionStep.angularMeanVector (pieces l).excluded = 0) :
    (initialized p r h axial c labels pieces baseError).meanGoodResidual c =
      (initialized p r h axial c labels pieces baseError).reducedMeanResidual c -
        (fun n x => temporalAlias p h c (primaryStage p c labels pieces baseError) n (x, 0) +
          pressureAlias p c (afterRank p r h axial c labels pieces baseError) n (x, 0)) := by
  let u := initialized p r h axial c labels pieces baseError
  obtain ⟨hb', hg', ha'⟩ := initialized_error_components p r h axial c labels pieces baseError
  have hgc : CorrectionStep.AngularContinuous u.errors.gaussian := by
    rw [show u.errors.gaussian = ∑ l ∈ labels, (pieces l).excluded from hg']
    intro n x i
    simpa only [Finset.sum_apply] using
      continuous_finsetSum labels (fun l hl => hg l hl n x i)
  have hac : CorrectionStep.AngularContinuous u.errors.aliasError := by
    rw [show u.errors.aliasError = _ from ha']
    intro n x i
    change Continuous (fun _ : ℝ =>
      temporalAlias p h c (primaryStage p c labels pieces baseError) n (x, 0) i +
        pressureAlias p c (afterRank p r h axial c labels pieces baseError) n (x, 0) i)
    exact continuous_const
  have hgz : CorrectionStep.angularMeanVector u.errors.gaussian = 0 := by
    rw [show u.errors.gaussian = ∑ l ∈ labels, (pieces l).excluded from hg',
      angularMeanVector_sum labels (fun l => (pieces l).excluded) hg]
    exact Finset.sum_eq_zero hz
  have hbc : CorrectionStep.AngularContinuous u.errors.base := by rwa [show u.errors.base = _ from
    hb']
  rw [CorrectionStep.meanGoodResidual_exact_errors c u hbc hgc hac, hgz, sub_zero]
  congr 1
  funext n x i
  rw [show u.errors.aliasError = _ from ha']
  change HarmonicResidual.realAngularMean (fun _ : ℝ =>
    temporalAlias p h c (primaryStage p c labels pieces baseError) n (x, 0) i +
      pressureAlias p c (afterRank p r h axial c labels pieces baseError) n (x, 0) i) = _
  exact HarmonicResidual.realAngularMean_const _

end InitializedExcludedMean

section BandExcludedMean

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {ι : Type}

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularMeanVector_fieldSum (labels : ℕ → Finset ι) (f : ι → Oscillation D)
    (hc : ∀ n l, l ∈ labels n → ∀ x i, Continuous (fun θ : ℝ => f l n (x, θ) i)) :
    CorrectionStep.angularMeanVector (LabelSumBounds.fieldSum labels f) =
      fun n x i => ∑ l ∈ labels n, CorrectionStep.angularMeanVector (f l) n x i := by
  funext n x i
  simpa only [CorrectionStep.angularMeanVector, angularAverage,
    HarmonicResidual.realAngularMean, HarmonicFields.period, LabelSumBounds.fieldSum] using
    HarmonicResidual.realAngularMean_sum (labels n) (fun l θ => f l n (x, θ) i)
      (fun l hl => hc n l hl x i)

namespace GaugeInitialization

open VariableGaugeMean

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The band-dependent physical-gauge construction retains exactly the two
current aliases. The base error cancels once and each primary Gaussian has
zero actual angular mean. -/
theorem initializedBands_meanGood (g : GaugeData S) (r : RankData S) (h : ℝ)
    (index : ℕ → ℕ) (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S))
    (hb : CorrectionStep.AngularContinuous baseError)
    (hg : ∀ n l, l ∈ labels n → ∀ x i,
      Continuous (fun θ : ℝ => (pieces l).excluded n (x, θ) i))
    (hz : ∀ n l, l ∈ labels n → ∀ x,
      CorrectionStep.angularMeanVector (pieces l).excluded n x = 0) :
    (initializedBands g r h index axial c labels pieces baseError).meanGoodResidual c =
      (initializedBands g r h index axial c labels pieces baseError).reducedMeanResidual c -
        (fun n x => temporalAliasState g h index c (primaryBands g c labels pieces baseError) n (x,
          0) +
          pressureAliasState g c (rankBands g r h index axial c labels pieces baseError) n (x, 0))
            := by
  let u := initializedBands g r h index axial c labels pieces baseError
  obtain ⟨hb', hg', ha'⟩ := initializedBands_error_components g r h index axial c labels pieces
    baseError
  have hgc : CorrectionStep.AngularContinuous u.errors.gaussian := by
    rw [show u.errors.gaussian = _ from hg']
    intro n x i
    exact continuous_finsetSum (labels n) (fun l hl => hg n l hl x i)
  have hac : CorrectionStep.AngularContinuous u.errors.aliasError := by
    rw [show u.errors.aliasError = _ from ha']
    intro n x i
    change Continuous (fun _ : ℝ =>
      temporalAliasState g h index c (primaryBands g c labels pieces baseError) n (x, 0) i +
        pressureAliasState g c (rankBands g r h index axial c labels pieces baseError) n (x, 0) i)
    exact continuous_const
  have hgz : CorrectionStep.angularMeanVector u.errors.gaussian = 0 := by
    rw [show u.errors.gaussian = _ from hg',
      angularMeanVector_fieldSum labels (fun l => (pieces l).excluded) hg]
    funext n x i
    exact Finset.sum_eq_zero (fun l hl => congrFun (hz n l hl x) i)
  have hbc : CorrectionStep.AngularContinuous u.errors.base := by
    rwa [show u.errors.base = _ from hb']
  rw [CorrectionStep.meanGoodResidual_exact_errors c u hbc hgc hac, hgz, sub_zero]
  congr 1
  funext n x i
  rw [show u.errors.aliasError = _ from ha']
  change HarmonicResidual.realAngularMean (fun _ : ℝ =>
    temporalAliasState g h index c (primaryBands g c labels pieces baseError) n (x, 0) i +
      pressureAliasState g c (rankBands g r h index axial c labels pieces baseError) n (x, 0) i) = _
  exact HarmonicResidual.realAngularMean_const _

/-- Bookkeeping for the two tangential estimates after the actual rank
stage: no class estimate on either excluded alias is inserted. -/
theorem initializedBands_meanResidualBounds
    (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S))
    (hb : CorrectionStep.AngularContinuous baseError)
    (hg : ∀ n l, l ∈ labels n → ∀ x i,
      Continuous (fun θ : ℝ => (pieces l).excluded n (x, θ) i))
    (hz : ∀ n l, l ∈ labels n → ∀ x,
      CorrectionStep.angularMeanVector (pieces l).excluded n x = 0)
    {s : WeightedClasses.StripData (Lift S)} {σ : ℝ}
    (hθ : WeightedClasses.MeanClass s (1 + σ)
      ((rankBands g r h index axial c labels pieces baseError).thetaResidual c))
    (hz' : WeightedClasses.MeanClass s (1 + σ) (fun n x =>
      (rankBands g r h index axial c labels pieces baseError).axialResidual c n x -
        temporalAliasState g h index c (primaryBands g c labels pieces baseError) n (x, 0) 2)) :
    MeanResidualBounds s σ c (initializedBands g r h index axial c labels pieces baseError) := by
  have he := initializedBands_meanGood g r h index axial c labels pieces baseError hb hg hz
  constructor
  · apply MeanIncrementBounds.class_congr hθ
    intro n x hx
    rw [he]
    simp [State.reducedMeanResidual, temporalAliasState, pressureAliasState,
      initializedBands, retainPressureAlias]
    rfl
  · apply MeanIncrementBounds.class_congr hz'
    intro n x hx
    rw [he]
    simp [State.reducedMeanResidual, pressureAliasState, initializedBands, retainPressureAlias]
    rfl

end GaugeInitialization

end BandExcludedMean

namespace AngularRestriction

open WeightedClasses

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def insert : D →L[ℝ] D × ℝ :=
  (ContinuousLinearMap.id ℝ D).prod 0

@[simp] theorem insert_apply (x : D) : insert x = (x, 0) := rfl

theorem norm_insert_le : ‖insert (D := D)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp [Prod.norm_def]

/-- The actual coefficient domain on the angular slice. -/
noncomputable def strip (s : StripData (D × ℝ)) : StripData D where
  domain := {x | (x, 0) ∈ s.domain}
  isOpen_domain := s.isOpen_domain.preimage (insert (D := D)).continuous
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta := fun x => s.delta (x, 0)
  delta_pos := fun x hx => s.delta_pos (x, 0) hx
  zeta := fun x => s.zeta (x, 0)
  zeta_smooth := s.zeta_smooth.comp (insert (D := D)).contDiff.contDiffOn (fun _ hx => hx)
  zeta_nonneg := fun x hx => s.zeta_nonneg (x, 0) hx

/-- Restriction is a genuine linear pullback of every jet, with norm one. -/
theorem class_restrict {s : StripData (D × ℝ)} {w : ℕ → D × ℝ → ℝ} {α : ℝ}
    {f : ℕ → D × ℝ → E} (hf : MemClass s w α f) :
    MemClass (strip s) (fun n x => w n (x, 0)) α (fun n x => f n (x, 0)) := by
  refine ⟨fun n x hx => hf.weight_nonneg n (x, 0) hx,
    fun n => (hf.smooth n).comp (insert (D := D)).contDiff.contDiffOn (fun _ hx => hx), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have hl := PhysicalGraphBounds.norm_jet_comp_linear s.isOpen_domain (hf.smooth n)
    (insert (D := D)) hx j
  calc
    ‖iteratedFDeriv ℝ j (fun x => f n (x, 0)) x‖ ≤
        ‖iteratedFDeriv ℝ j (f n) (x, 0)‖ * ‖insert (D := D)‖ ^ j := hl
    _ ≤ ‖iteratedFDeriv ℝ j (f n) (x, 0)‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) norm_insert_le)
    _ ≤ _ := hb n (x, 0) hx j hj

theorem waveClass_restrict {s : StripData (D × ℝ)} {P : ℕ → D × ℝ → ℝ} {α : ℝ}
    {f : ℕ → D × ℝ → E} (hf : WaveClass s P α f) :
    WaveClass (strip s) (fun n x => P n (x, 0)) α (fun n x => f n (x, 0)) :=
  class_restrict hf

end AngularRestriction

namespace PrimaryHarmonics

open WeightedClasses HarmonicFields

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- A primary mode and its pressure, with the actual conjugate negative mode. -/
noncomputable def block (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) : HarmonicBlock D where
  velocity n i := ErrorHarmonics.conjugatePair 1 (fun x => a.amplitude n (x, 0) i)
  pressure n := ErrorHarmonics.conjugatePair 1 (fun x => a.pressure n (x, 0))
  frequency := a.frequency
  phase := Φ
  angularFrequency := kp

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem block_band (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) : (block a Φ kp).BandLimited 1 :=
  ⟨fun _ _ => ErrorHarmonics.band_conjugatePair 1 _,
    fun _ => ErrorHarmonics.band_conjugatePair 1 _⟩

theorem conjugatePair_class {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    (a : ℕ → D → ℂ) (ha : WaveClass s P α a) (j m : ℤ) :
    WaveClass s P α (fun n x => ErrorHarmonics.conjugatePair j (a n) m x) := by
  classical
  have hhalf : WaveClass s P α (fun n x => a n x / 2) := by
    apply WaveInteractionBounds.class_congr (WaveInteractionBounds.class_const_cmul ha (2 : ℂ)⁻¹)
    intro n x _
    simp only [div_eq_mul_inv, mul_comm]
  have hs (k : ℤ) : WaveClass s P α (fun n x =>
      (AddMonoidAlgebra.single j (fun x => a n x / 2) : Coefficients D) k x) := by
    change WaveClass s P α (fun n x => Finsupp.single j (fun x => a n x / 2) k x)
    by_cases hk : j = k
    · simpa [Finsupp.single_apply, hk] using hhalf
    · simpa [Finsupp.single_apply, hk] using
        (MemClass.zero ha.weight_nonneg : WaveClass s P α (fun _ _ => (0 : ℂ)))
  apply WaveInteractionBounds.class_congr ((hs m).add (WaveInteractionBounds.class_conj (hs (-m))))
  intro n x _
  rfl

theorem block_coefficient_class {s : StripData (D × ℝ)} {P : ℕ → D × ℝ → ℝ} {α : ℝ}
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (ha : ∀ i, WaveClass s P α (fun n x => a.amplitude n x i)) (i : Fin 3) (j : ℤ) :
    WaveClass (AngularRestriction.strip s) (fun n x => P n (x, 0)) α
      (fun n x => (block a Φ kp).velocity n i j x) :=
  conjugatePair_class _ (AngularRestriction.waveClass_restrict (ha i)) 1 j

theorem block_pressure_class {s : StripData (D × ℝ)} {P : ℕ → D × ℝ → ℝ} {α : ℝ}
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) (ha : WaveClass s P α a.pressure) (j : ℤ) :
    WaveClass (AngularRestriction.strip s) (fun n x => P n (x, 0)) α
      (fun n x => (block a Φ kp).pressure n j x) :=
  conjugatePair_class _ (AngularRestriction.waveClass_restrict ha) 1 j

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem block_velocity_represents (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (ha : ErrorHarmonics.AngleIndependent a.amplitude)
    (hphase : ∀ n x θ, a.frequency n * a.phase n (x, θ) =
      a.frequency n * Φ n x + (kp n : ℝ) * θ) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    (block a Φ kp).oscillation n x i =
      (HarmonicCalculus.vectorMode (a.frequency n) (a.phase n) (a.amplitude n) x i).re := by
  rw [HarmonicBlock.oscillation, block, ErrorHarmonics.field_conjugatePair, Complex.ofReal_re]
  change (a.amplitude n (x.1, 0) i * character 1
    (a.frequency n * Φ n x.1 + (kp n : ℝ) * x.2)).re = _
  have hc := character_eq_carrier 1 (a.frequency n) (a.phase n) x
  simp only [Int.cast_one, mul_one] at hc
  simp only [HarmonicCalculus.vectorMode, HarmonicCalculus.mode]
  rw [← hc, hphase n x.1 x.2, ha n x.1 x.2]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem block_pressure_represents (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (ha : ErrorHarmonics.AngleIndependent a.pressure)
    (hphase : ∀ n x θ, a.frequency n * a.phase n (x, θ) =
      a.frequency n * Φ n x + (kp n : ℝ) * θ) (n : ℕ) (x : D × ℝ) :
    (block a Φ kp).oscillatoryPressure n x =
      (HarmonicCalculus.mode (a.frequency n) (a.phase n) (a.pressure n) x).re := by
  rw [HarmonicBlock.oscillatoryPressure, block, ErrorHarmonics.field_conjugatePair,
    Complex.ofReal_re]
  change (a.pressure n (x.1, 0) * character 1
    (a.frequency n * Φ n x.1 + (kp n : ℝ) * x.2)).re = _
  have hc := character_eq_carrier 1 (a.frequency n) (a.phase n) x
  simp only [Int.cast_one, mul_one] at hc
  simp only [HarmonicCalculus.mode]
  rw [← hc, hphase n x.1 x.2, ha n x.1 x.2]

end PrimaryHarmonics

section PrimaryBlocks

open WeightedClasses LinearWaveBounds HarmonicCalculus

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

namespace PrimaryPiece

noncomputable def harmonicBlock (p : PrimaryPiece (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) : HarmonicBlock D :=
  PrimaryHarmonics.block p.exactCoefficients Φ kp

noncomputable def tangentBlock (p : PrimaryPiece (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) : HarmonicBlock D :=
  PrimaryHarmonics.block (p.coefficients.withCutoff p.cutoff) Φ kp

noncomputable def differenceCoefficients (p : PrimaryPiece (D × ℝ)) : WaveCoefficients (D × ℝ) :=
  { p.coefficients with
    amplitude := fun n x => p.exactCoefficients.amplitude n x -
      (p.coefficients.withCutoff p.cutoff).amplitude n x
    pressure := 0 }

noncomputable def differenceBlock (p : PrimaryPiece (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) : HarmonicBlock D :=
  PrimaryHarmonics.block p.differenceCoefficients Φ kp

theorem harmonicBlock_represents (p : PrimaryPiece (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (ha : ErrorHarmonics.AngleIndependent p.exactCoefficients.amplitude)
    (hp : ErrorHarmonics.AngleIndependent p.exactCoefficients.pressure)
    (hphase : ∀ n x θ, p.coefficients.frequency n * p.coefficients.phase n (x, θ) =
      p.coefficients.frequency n * Φ n x + (kp n : ℝ) * θ) :
    (p.harmonicBlock Φ kp).oscillation = p.velocity ∧
      (p.harmonicBlock Φ kp).oscillatoryPressure = p.pressure := by
  constructor
  · funext n x i
    exact PrimaryHarmonics.block_velocity_represents p.exactCoefficients Φ kp ha hphase n x i
  · funext n x
    exact PrimaryHarmonics.block_pressure_represents p.exactCoefficients Φ kp hp hphase n x

theorem differenceBlock_represents (p : PrimaryPiece (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (ha : ErrorHarmonics.AngleIndependent p.exactCoefficients.amplitude)
    (ht : ErrorHarmonics.AngleIndependent (p.coefficients.withCutoff p.cutoff).amplitude)
    (hphase : ∀ n x θ, p.coefficients.frequency n * p.coefficients.phase n (x, θ) =
      p.coefficients.frequency n * Φ n x + (kp n : ℝ) * θ) :
    (p.differenceBlock Φ kp).oscillation = p.velocity - p.tangentVelocity := by
  have hd : ErrorHarmonics.AngleIndependent p.differenceCoefficients.amplitude := by
    intro n x θ
    exact congrArg₂ (fun a b : ComplexVector => a - b) (ha n x θ) (ht n x θ)
  funext n x i
  rw [show (p.differenceBlock Φ kp).oscillation n x i = _ from
    PrimaryHarmonics.block_velocity_represents p.differenceCoefficients Φ kp hd hphase n x i]
  simp [differenceCoefficients, velocity, tangentVelocity, vectorMode, mode, sub_mul]

/-- The cumulative bounds belong to the actual finite harmonic blocks
representing the cutoff curl and its difference from the primary tangent. -/
theorem harmonic_cumulative_bounds (p : PrimaryPiece (D × ℝ))
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) {P : ℕ → D × ℝ → ℝ}
    (hp : InputBounds p.strip P (1 / 2) ChartScales.kappa p.directions p.coefficients)
    (hcut : UnweightedClass p.strip 0 p.cutoff) {R : D × ℝ → ℝ}
    (hR : p.coefficients.radius = fun _ => R)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain p.strip)
      (p.coefficients.normal p.strip p.directions)) {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ n x, x ∈ p.strip.domain → b ≤ ‖p.coefficients.normal p.strip p.directions n x‖)
    (hhi : ∀ n x, x ∈ p.strip.domain → ‖p.coefficients.normal p.strip p.directions n x‖ ≤ M)
    (hK : BandBound p.strip (1 / 2) (fun n => 1 / p.coefficients.frequency n)) :
    let s := AngularRestriction.strip p.strip
    let P0 := fun n x => P n (x, 0)
    (∀ i j, WaveClass s P0 (1 / 2) (fun n x => (p.harmonicBlock Φ kp).velocity n i j x)) ∧
    (∀ i j, WaveClass s P0 (17 / 25) (fun n x => (p.differenceBlock Φ kp).velocity n i j x)) ∧
    (∀ j, WaveClass s P0 1 (fun n x => (p.harmonicBlock Φ kp).pressure n j x)) := by
  obtain ⟨hamp, hdiff, hpressure⟩ := p.cumulative_bounds hp hcut hR hN hb hlo hhi hK
  exact ⟨fun i j => PrimaryHarmonics.block_coefficient_class p.exactCoefficients Φ kp hamp i j,
    fun i j => PrimaryHarmonics.block_coefficient_class p.differenceCoefficients Φ kp
      (fun i => CurlClassBounds.class_component hdiff i) i j,
    fun j => PrimaryHarmonics.block_pressure_class p.exactCoefficients Φ kp hpressure j⟩

end PrimaryPiece

end PrimaryBlocks


section ZeroMean

open MeanIncrementBounds WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

private theorem dr_zero (o : Operators D) : o.dr (0 : ScalarField D) = 0 := by
  funext n x
  simp [Operators.dr, graphDerivative]

private theorem dz_zero (o : Operators D) : o.dz (0 : ScalarField D) = 0 := by
  funext n x
  simp [Operators.dz]

private theorem time_zero (o : Operators D) : o.time (0 : ScalarField D) = 0 := by
  funext n x
  simp [Operators.time, Operators.slowTime, Operators.fastTime]

private theorem viscosity_zero (o : Operators D) (k : ℝ) :
    o.viscosity k (0 : ScalarField D) = 0 := by
  funext n x
  simp [Operators.viscosity, dr_zero, dz_zero]

theorem zeroMean_gr (c : Context D) (u : State D) (hm : u.mean = ⟨0, 0, 0⟩) :
    u.gr c = -(c.operators.radialDiv 1 (u.covariance 0 0) +
      c.operators.dz (u.covariance 2 0) - c.operators.invRadius * u.covariance 1 1) := by
  funext n x
  simp [State.gr, MeanIncrementBounds.gr, hm, radialRadial, axialRadial, radialAngular,
    time_zero, viscosity_zero]

theorem zeroMean_theta (c : Context D) (u : State D) (hm : u.mean = ⟨0, 0, 0⟩) :
    u.thetaResidual c = c.operators.radialDiv 2 (u.covariance 0 1) +
      c.operators.dz (u.covariance 2 1) - c.operators.radialDiv 2 c.virtualTheta := by
  funext n x
  simp [State.thetaResidual, MeanIncrementBounds.thetaResidual, hm, thetaRadial, thetaAxial,
    time_zero, viscosity_zero]

theorem zeroMean_axial (c : Context D) (u : State D) (hm : u.mean = ⟨0, 0, 0⟩) :
    u.axialResidual c = c.operators.radialDiv 1 (u.covariance 0 2) +
      c.operators.dz (u.covariance 2 2 + u.pressure) - c.operators.radialDiv 1 c.virtualAxial := by
  funext n x
  simp [State.axialResidual, MeanIncrementBounds.axialResidual, hm, axialRadial, axialAxial,
    time_zero, viscosity_zero]

theorem zeroMean_gr_mem {s : StripData D} {κ : ℝ} (c : Context D) (u : State D)
    (ho : OperatorBounds s c.operators κ) (hm : u.mean = ⟨0, 0, 0⟩)
    (hW : ∀ i j, MeanClass s 1 (u.covariance i j)) :
    MeanClass s (1 - κ) (u.gr c) := by
  rw [zeroMean_gr c u hm]
  exact Class.neg (Class.sub ((ho.radialDiv (hW 0 0) 1).add
    ((ho.dz (hW 2 0)).mono_exponent (by linarith [ho.kappa_nonneg])))
    ((ho.inv_mul (hW 1 1)).mono_exponent (by linarith [ho.kappa_nonneg])))

theorem zeroMean_theta_mem {s : StripData D} {κ : ℝ} (c : Context D) (u : State D)
    (ho : OperatorBounds s c.operators κ) (hm : u.mean = ⟨0, 0, 0⟩)
    (hW : ∀ i j, MeanClass s 1 (u.covariance i j))
    (hT : MeanClass s 1 c.virtualTheta) : MeanClass s (1 - κ) (u.thetaResidual c) := by
  rw [zeroMean_theta c u hm]
  exact Class.sub ((ho.radialDiv (hW 0 1) 2).add
    ((ho.dz (hW 2 1)).mono_exponent (by linarith [ho.kappa_nonneg])))
    (ho.radialDiv hT 2)

theorem zeroMean_axial_mem {s : StripData D} {κ : ℝ} (c : Context D) (u : State D)
    (ho : OperatorBounds s c.operators κ) (hm : u.mean = ⟨0, 0, 0⟩)
    (hW : ∀ i j, MeanClass s 1 (u.covariance i j))
    (hT : MeanClass s 1 c.virtualAxial) (hp : MeanClass s (1 - κ) u.pressure) :
    MeanClass s (1 - κ) (u.axialResidual c) := by
  rw [zeroMean_axial c u hm]
  have hflux := ((hW 2 2).mono_exponent (show 1 - κ ≤ 1 by linarith [ho.kappa_nonneg])).add hp
  exact Class.sub ((ho.radialDiv (hW 0 2) 1).add
    ((ho.dz hflux).mono_exponent (by linarith))) (ho.radialDiv hT 1)

end ZeroMean


section InitialMeanBounds

open MeanIncrementBounds WeightedClasses WeightedRadialPrimitive

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem zeroMean_gr_shell {a b : ℝ} (ha : 0 < a)
    (c : Context (Lift S)) (u : State (Lift S))
    (ho : DefectIncrementBounds.PositiveOperators c.operators)
    (hm : u.mean = ⟨0, 0, 0⟩)
    (hW : ∀ i j, DefectIncrementBounds.Shell a b (u.covariance i j)) :
    DefectIncrementBounds.Shell a b (u.gr c) := by
  rw [zeroMean_gr c u hm]
  exact (((hW 0 0).radialDiv ha ho 1).add ((hW 2 0).dz c.operators)).sub
    ((hW 1 1).inv_mul ha ho) |>.neg

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem zeroMean_thetaDefect (c : Context (Lift S)) (u : State (Lift S))
    (hm : u.mean = ⟨0, 0, 0⟩) :
    thetaDefect c u = radialMoment 2 (u.covariance 2 1) := by
  simp [thetaDefect, hm, thetaAxial]

theorem zeroMean_axialDefect (c : Context (Lift S)) (u : State (Lift S))
    (hm : u.mean = ⟨0, 0, 0⟩) :
    axialDefect c u = radialMoment 1 (u.covariance 2 2) -
      (1 / 2 : ℝ) • radialMoment 2 (u.gr c) := by
  simp [axialDefect, hm, axialAxial]

/-- Before the temporal update, the pressure is the actual compact
primitive of the radial equation. Its class is derived from the covariance. -/
theorem zeroMean_reconstructed_bounds [FiniteDimensional ℝ S]
    (r : ReconstructionData) (ha : 0 < r.inner) (hd : 0 < r.exponent)
    {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (c : Context (Lift S)) (u : State (Lift S))
    (ho : OperatorBounds (logStripData r.inner r.outer cL cR ha hcL hcR ε L hε hεone hL)
      c.operators ChartScales.kappa)
    (hop : DefectIncrementBounds.PositiveOperators c.operators)
    (hm : u.mean = ⟨0, 0, 0⟩)
    (hW : ∀ i j, MeanClass (logStripData r.inner r.outer cL cR ha hcL hcR ε L hε hεone hL)
      1 (u.covariance i j))
    (hWs : ∀ i j, DefectIncrementBounds.Shell r.inner r.outer (u.covariance i j))
    (hθ : MeanClass (logStripData r.inner r.outer cL cR ha hcL hcR ε L hε hεone hL)
      1 c.virtualTheta)
    (hz : MeanClass (logStripData r.inner r.outer cL cR ha hcL hcR ε L hε hεone hL)
      1 c.virtualAxial) :
    let s := logStripData r.inner r.outer cL cR ha hcL hcR ε L hε hεone hL
    MeanClass s (1 - ChartScales.kappa) ((reconstructPressure r c u).gr c) ∧
    MeanClass s (1 - ChartScales.kappa) (reconstructPressure r c u).pressure ∧
    MeanClass s (1 - ChartScales.kappa) ((reconstructPressure r c u).thetaResidual c) ∧
    MeanClass s (1 - ChartScales.kappa) ((reconstructPressure r c u).axialResidual c) ∧
    CorrectionState.CumulativeBounds s (reconstructPressure r c u) := by
  dsimp only
  have hg := zeroMean_gr_mem c u ho hm hW
  have hgs := zeroMean_gr_shell ha c u hop hm hWs
  have hp := meanClass_meanPressure ha r.inner_lt_outer hd hcL hcR ε L hε hεone hL
    hgs.smooth hgs.supported hg r.frequency (fun _ => r.radialDirection)
  have hm' : (reconstructPressure r c u).mean = ⟨0, 0, 0⟩ := hm
  refine ⟨hg, hp, zeroMean_theta_mem c (reconstructPressure r c u) ho hm' hW hθ,
    zeroMean_axial_mem c (reconstructPressure r c u) ho hm' hW hz hp, ?_⟩
  refine ⟨?_, hp.mono_exponent (by norm_num [ChartScales.kappa])⟩
  rw [hm']
  have hw := (logStripData (E := S × PressureStream.Plane)
    r.inner r.outer cL cR ha hcL hcR ε L hε hεone hL).zeta_nonneg
  exact ⟨MemClass.zero (fun _ => hw), MemClass.zero (fun _ => hw), MemClass.zero (fun _ => hw)⟩

/-- All three incoming debts are actual radial moments. No defect bound
is an input to this initial estimate. -/
theorem zeroMean_debt_mem
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (c : Context (Lift S)) (u : State (Lift S))
    (ho : OperatorBounds (logStripData a b cL cR ha hcL hcR ε L hε hεone hL)
      c.operators ChartScales.kappa)
    (hop : DefectIncrementBounds.PositiveOperators c.operators)
    (hm : u.mean = ⟨0, 0, 0⟩)
    (hW : ∀ i j, MeanClass (logStripData a b cL cR ha hcL hcR ε L hε hεone hL)
      1 (u.covariance i j))
    (hWs : ∀ i j, DefectIncrementBounds.Shell a b (u.covariance i j)) (i : Fin 3) :
    UnweightedClass (MeanMomentBounds.slowStripData (D := S) ε L hε hεone hL)
      (1 - ChartScales.kappa) (fun n x => debt c u n x i) := by
  have hg := zeroMean_gr_mem c u ho hm hW
  have hgs := zeroMean_gr_shell ha c u hop hm hWs
  have hP := DefectIncrementBounds.barMoment_mem ha hab hcL hcR ε L hε hεone hL hgs hg 0
  have hP2 := DefectIncrementBounds.barMoment_mem ha hab hcL hcR ε L hε hεone hL hgs hg 2
  have hθ := (DefectIncrementBounds.barMoment_mem ha hab hcL hcR ε L hε hεone hL
    (hWs 2 1) (hW 2 1) 2).mono_exponent
      (show 1 - ChartScales.kappa ≤ 1 by norm_num [ChartScales.kappa])
  have hz := (DefectIncrementBounds.barMoment_mem ha hab hcL hcR ε L hε hεone hL
    (hWs 2 2) (hW 2 2) 1).mono_exponent
      (show 1 - ChartScales.kappa ≤ 1 by norm_num [ChartScales.kappa])
  fin_cases i
  · exact hP
  · simpa only [debt, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ',
      zeroMean_thetaDefect c u hm, DefectIncrementBounds.barMoment] using hθ
  · have h := Class.sub hz (Class.smul hP2 (1 / 2))
    simp only [debt,
      Matrix.cons_val_zero', Matrix.cons_val_succ', zeroMean_axialDefect c u hm,
      DefectIncrementBounds.barMoment] at h ⊢
    exact h

end InitialMeanBounds

namespace AuxiliaryAverage

open StateMomentBalances.AuxiliaryAverage

open MeanIncrementBounds WeightedClasses WeightedRadialPrimitive

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem periodic_sub {f g : Lift S → ℝ} (hf : PressureStream.TorusPeriodicLift f)
    (hg : PressureStream.TorusPeriodicLift g) : PressureStream.TorusPeriodicLift (f - g) := by
  intro r s Y k
  change f (r, (s, Y + _)) - g (r, (s, Y + _)) = f (r, (s, Y)) - g (r, (s, Y))
  exact congrArg₂ (fun x y : ℝ => x - y) (hf r s Y k) (hg r s Y k)

/-- The actual torus average preserves the flat mean class. -/
theorem meanBar_mem {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    {α : ℝ} {f : ScalarField (Lift S)}
    (hf : MeanClass (logStripData a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε L hε hεone hL) α (StateMomentBalances.meanBar f)
      := by
  have hc := TemporalMeanUpdate.meanClass_centered ha hcL hcR ε L hε hεone hL hf hfc hp
  apply MeanIncrementBounds.class_congr (Class.sub hf hc)
  intro n x _
  simp [StateMomentBalances.meanBar, MeanMomentBounds.liftedTorusAverage,
    TemporalMeanUpdate.centered]

/-- Exact leading covariance cancellation transfers the curl-product and
higher-virtual-flux orders to the actual averaged radial flux. -/
theorem matched_flux_mem {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (R R0 T T0 : ScalarField (Lift S))
    (hR : ∀ n, ContDiff ℝ ∞ (R n)) (hR0 : ∀ n, ContDiff ℝ ∞ (R0 n))
    (hT : ∀ n, ContDiff ℝ ∞ (T n)) (hT0 : ∀ n, ContDiff ℝ ∞ (T0 n))
    (hpR : ∀ n, PressureStream.TorusPeriodicLift (R n))
    (hpR0 : ∀ n, PressureStream.TorusPeriodicLift (R0 n))
    (hpT : ∀ n, PressureStream.TorusPeriodicLift (T n))
    (hpT0 : ∀ n, PressureStream.TorusPeriodicLift (T0 n))
    (hcurl : MeanClass (logStripData a b cL cR ha hcL hcR ε L hε hεone hL)
      (3 / 2 - ChartScales.kappa) (R - R0))
    (hvirtual : MeanClass (logStripData a b cL cR ha hcL hcR ε L hε hεone hL) 2 (T - T0))
    (hmatch : Agree (logStripData a b cL cR ha hcL hcR ε L hε hεone hL).domain
      (StateMomentBalances.meanBar R0) (StateMomentBalances.meanBar T0)) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε L hε hεone hL)
      (3 / 2 - ChartScales.kappa) (StateMomentBalances.meanBar R - StateMomentBalances.meanBar T)
        := by
  have hRc := meanBar_mem ha hcL hcR ε L hε hεone hL hcurl
    (fun n => (hR n).sub (hR0 n)) (fun n => periodic_sub (hpR n) (hpR0 n))
  have hTc := (meanBar_mem ha hcL hcR ε L hε hεone hL hvirtual
    (fun n => (hT n).sub (hT0 n)) (fun n => periodic_sub (hpT n) (hpT0 n))).mono_exponent
      (show 3 / 2 - ChartScales.kappa ≤ (2 : ℝ) by norm_num [ChartScales.kappa])
  apply MeanIncrementBounds.class_congr (Class.sub hRc hTc)
  intro n x hx
  have hr := congrFun (congrFun (meanBar_sub R R0 hR hR0) n) x
  have ht := congrFun (congrFun (meanBar_sub T T0 hT hT0) n) x
  have hm := hmatch n hx
  simp only [Pi.sub_apply] at *
  linarith

/-- The initial bar exponent `1.49` follows from the actual averaged
flux balance, a curl covariance error, and the axial derivative gain. -/
theorem fluxBalance_mem {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (o : Operators (Lift S)) (hop : DefectIncrementBounds.PositiveOperators o)
    (ho : OperatorBounds (logStripData a b cL cR ha hcL hcR ε L hε hεone hL)
      o ChartScales.kappa)
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    (R A T : ScalarField (Lift S)) (c : ℝ)
    (hR : DefectIncrementBounds.Shell a b R) (hA : DefectIncrementBounds.Shell a b A)
    (hT : DefectIncrementBounds.Shell a b T)
    (hpR : ∀ n, PressureStream.TorusPeriodicLift (R n))
    (hpA : ∀ n, PressureStream.TorusPeriodicLift (A n))
    (hpT : ∀ n, PressureStream.TorusPeriodicLift (T n))
    (hflux : MeanClass (logStripData a b cL cR ha hcL hcR ε L hε hεone hL)
      (3 / 2 - ChartScales.kappa) (StateMomentBalances.meanBar R - StateMomentBalances.meanBar T))
    (haxial : MeanClass (logStripData a b cL cR ha hcL hcR ε L hε hεone hL)
      (1 - ChartScales.kappa) A) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε L hε hεone hL) (149 / 100)
      (StateMomentBalances.meanBar (o.radialDiv c R + o.dz A - o.radialDiv c T)) := by
  rw [meanBar_fluxBalance ha o hop hprofile R A T c hR hA hT hpR hpA hpT]
  have hrad := (ho.radialDiv hflux c).mono_exponent
    (show (149 / 100 : ℝ) ≤ 3 / 2 - ChartScales.kappa - ChartScales.kappa by norm_num
      [ChartScales.kappa])
  have hax := (ho.dz (meanBar_mem ha hcL hcR ε L hε hεone hL haxial hA.smooth hpA)).mono_exponent
    (show (149 / 100 : ℝ) ≤ 1 - ChartScales.kappa + 1 by norm_num [ChartScales.kappa])
  exact hrad.add hax

end AuxiliaryAverage

namespace MovingInitialization

open WeightedClasses MeanIncrementBounds VariableGaugeMean LocalSignedRequest

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The literal radial source retains the moving support of the actual
covariance, including every differentiated term. -/
theorem zeroMean_gr_supportedGauge {a b : ℝ} {V : Set S} (hV : IsOpen V)
    {ell : S → ℝ} (hell : ContinuousOn ell V)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (hm : u.mean = ⟨0, 0, 0⟩)
    (hW : ∀ i j n, SupportedGauge a b ell V (u.covariance i j n)) :
    ∀ n, SupportedGauge a b ell V (u.gr c n) := by
  intro n x hx hn
  by_contra hr
  have hz (i j : Fin 3) : u.covariance i j n x = 0 := by
    by_contra hn
    exact hr (hW i j n x hx hn)
  have hD (i j : Fin 3) (v : PressureStream.Lift S) :
      fderiv ℝ (u.covariance i j n) x v = 0 := by
    have hs := iteratedFDeriv_supportedGauge_fiber hV hell (hW i j n) hx 1
    have he : iteratedFDeriv ℝ 1 (u.covariance i j n) x = 0 := by
      by_contra hn'
      exact hr (hs hn')
    simpa only [iteratedFDeriv_one_apply, _root_.zero_apply] using
      congrArg (fun A : (PressureStream.Lift S) [×1]→L[ℝ] ℝ =>
        A (fun _ : Fin 1 => v)) he
  apply hn
  rw [zeroMean_gr c u hm]
  simp [Operators.radialDiv, Operators.dr, graphDerivative, Operators.dz, hz, hD]

/-- Smoothness on the full valid slow domain follows from a containing
annulus and the actual covariance support; no smooth extension of a
positive-time totalization is used. -/
theorem zeroMean_gr_smooth {coord a b : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b)
    (c : Context Point) (u : State Point)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hm : u.mean = ⟨0, 0, 0⟩)
    (hW : ∀ i j n, ContDiffOn ℝ ∞ (u.covariance i j n)
      (PhysicalMeanDomain.slowDomain U.carrier))
    (hWs : ∀ i j n, SupportedGauge a b (qLength coord) U.carrier (u.covariance i j n)) :
    ∀ n, ContDiffOn ℝ ∞ (u.gr c n) (PhysicalMeanDomain.slowDomain U.carrier) := by
  obtain ⟨a₀, b₀, L, ha₀, _, _, _, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  have hs (i j : Fin 3) : LocalRankDefect.LocalShell a₀ b₀ U.carrier (u.covariance i j) := by
    refine ⟨hW i j, ?_⟩
    intro n x hx hn
    exact ⟨(hleft _ hx).trans (hWs i j n x hx hn).1,
      (hWs i j n x hx hn).2.trans (hright _ hx)⟩
  have hgr : LocalRankDefect.LocalShell a₀ b₀ U.carrier (u.gr c) := by
    rw [zeroMean_gr c u hm]
    exact ((((hs 0 0).radialDiv ha₀ U.isOpen hop 1).add
      ((hs 2 0).dz U.isOpen c.operators)).sub ((hs 1 1).inv_mul ha₀ U.isOpen hop)).neg
  exact hgr.smooth

/-- Actual moving-gauge initial pressure and raw tangential residuals,
derived from the covariance and virtual stresses. -/
theorem zeroMean_reconstructed_bounds {coord cL cR : ℝ} (U : SlowRegion coord)
    (g : GaugeData PressureStream.Plane) (ha : 0 < g.radial.inner)
    (hd : 0 < g.radial.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)
    (c : Context Point) (u : State Point)
    (ho : OperatorBounds
      (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      c.operators ChartScales.kappa)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hm : u.mean = ⟨0, 0, 0⟩)
    (hW : ∀ i j, MeanClass
      (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      1 (u.covariance i j))
    (hWc : ∀ i j n, ContDiffOn ℝ ∞ (u.covariance i j n)
      (PhysicalMeanDomain.slowDomain U.carrier))
    (hWs : ∀ i j n, SupportedGauge g.radial.inner g.radial.outer (qLength coord)
      U.carrier (u.covariance i j n))
    (hθ : MeanClass
      (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      1 c.virtualTheta)
    (hz : MeanClass
      (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      1 c.virtualAxial) :
    let st := movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL
    MeanClass st (1 - ChartScales.kappa) (u.gr c) ∧
      MeanClass st (1 - ChartScales.kappa) (reconstructState g c u).pressure ∧
      MeanClass st (1 - ChartScales.kappa) ((reconstructState g c u).thetaResidual c) ∧
      MeanClass st (1 - ChartScales.kappa) ((reconstructState g c u).axialResidual c) ∧
      CorrectionState.CumulativeBounds st (reconstructState g c u) := by
  dsimp only
  have hgr := zeroMean_gr_mem c u ho hm hW
  have hgc := zeroMean_gr_smooth U ha g.radial.inner_lt_outer c u hop hm hWc hWs
  have hgauge := zeroMean_gr_supportedGauge U.isOpen
    (((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono
      (fun s hs => U.time_pos s hs)).continuousOn) c u hm hWs
  have hp : MeanClass
      (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      (1 - ChartScales.kappa) (reconstructState g c u).pressure := by
    simpa only [reconstructState, hell] using
      meanClass_meanPressure U ha hcL hcR ε L hε hεone hL g.radial.inner_lt_outer hd hgc hgauge hgr
        g.radial.frequency (fun _ => g.radial.radialDirection)
  have hm' : (reconstructState g c u).mean = ⟨0, 0, 0⟩ := hm
  refine ⟨hgr, hp, zeroMean_theta_mem c (reconstructState g c u) ho hm' hW hθ,
    zeroMean_axial_mem c (reconstructState g c u) ho hm' hW hz hp, ?_⟩
  refine ⟨?_, hp.mono_exponent (by norm_num [ChartScales.kappa])⟩
  rw [hm']
  have hw := (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone
    hL).zeta_nonneg
  exact ⟨MemClass.zero (fun _ => hw), MemClass.zero (fun _ => hw), MemClass.zero (fun _ => hw)⟩

section MovingMoments

variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

include hab

/-- All three incoming debts are measured from the same initial fields.
There is no assumed debt bound and no change to the moving edge weight. -/
theorem zeroMean_debt_mem (c : Context Point) (u : State Point)
    (ho : OperatorBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      c.operators ChartScales.kappa)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hm : u.mean = ⟨0, 0, 0⟩)
    (hW : ∀ i j, MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      1 (u.covariance i j))
    (hWc : ∀ i j n, ContDiffOn ℝ ∞ (u.covariance i j n)
      (PhysicalMeanDomain.slowDomain U.carrier))
    (hWs : ∀ i j n, SupportedGauge a b (qLength coord) U.carrier (u.covariance i j n))
    (i : Fin 3) :
    UnweightedClass
      (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL)
      (1 - ChartScales.kappa) (fun n x => debt c u n x i) := by
  have hgr := zeroMean_gr_mem c u ho hm hW
  have hgc := zeroMean_gr_smooth U ha hab c u hop hm hWc hWs
  have hgauge := zeroMean_gr_supportedGauge U.isOpen
    (((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono
      (fun s hs => U.time_pos s hs)).continuousOn) c u hm hWs
  have hP := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hgc hgauge hgr 0
  have hP2 := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hgc hgauge hgr 2
  have hθ := (radialMoment_mem U ha hab hcL hcR ε L hε hεone hL
    (hWc 2 1) (hWs 2 1) (hW 2 1) 2).mono_exponent
      (show 1 - ChartScales.kappa ≤ 1 by norm_num [ChartScales.kappa])
  have hz := (radialMoment_mem U ha hab hcL hcR ε L hε hεone hL
    (hWc 2 2) (hWs 2 2) (hW 2 2) 1).mono_exponent
      (show 1 - ChartScales.kappa ≤ 1 by norm_num [ChartScales.kappa])
  fin_cases i
  · exact hP
  · simpa only [debt, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ',
      zeroMean_thetaDefect c u hm] using hθ
  · have h := Class.sub hz (Class.smul hP2 (1 / 2))
    simp only [debt,
      Matrix.cons_val_zero', Matrix.cons_val_succ', zeroMean_axialDefect c u hm] at h ⊢
    exact h

end MovingMoments

namespace LocalAverage

open PhysicalMeanDomain StateMomentBalances
open StateMomentBalances.AuxiliaryAverage

variable {V : Set S}

omit [NormedSpace ℝ S] in
theorem continuous_slice {f : PressureStream.Lift S → ℝ}
    (hf : ContinuousOn f (slowDomain V)) {x : PressureStream.Lift S} (hx : x.2.1 ∈ V) :
    Continuous (fun Y : PressureStream.Plane => f (x.1, (x.2.1, Y))) :=
  hf.comp_continuous (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (fun _ => hx)

omit [NormedSpace ℝ S] in
theorem meanBar_add_on (f g : ScalarField (PressureStream.Lift S))
    (hf : ∀ n, ContinuousOn (f n) (slowDomain V))
    (hg : ∀ n, ContinuousOn (g n) (slowDomain V)) :
    Agree (slowDomain V) (meanBar (f + g)) (meanBar f + meanBar g) := by
  intro n x hx
  exact FourierAlias.torusMean_add (continuous_slice (hf n) hx) (continuous_slice (hg n) hx)

omit [NormedSpace ℝ S] in
theorem meanBar_sub_on (f g : ScalarField (PressureStream.Lift S))
    (hf : ∀ n, ContinuousOn (f n) (slowDomain V))
    (hg : ∀ n, ContinuousOn (g n) (slowDomain V)) :
    Agree (slowDomain V) (meanBar (f - g)) (meanBar f - meanBar g) := by
  intro n x hx
  exact FourierAlias.torusMean_sub (continuous_slice (hf n) hx) (continuous_slice (hg n) hx)

variable [FiniteDimensional ℝ S]

/-- Parameter differentiation of the actual torus average on the open
slow domain. The localization equals the original source on a whole fiber
germ, so its derivatives introduce no cutoff term. -/
theorem average_derivative_on (hV : IsOpen V) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain V)) (hp : PeriodicOn V f)
    (v x : PressureStream.Lift S) (hx : x.2.1 ∈ V) :
    PressureStream.torusAverage (fun y => fderiv ℝ f y v) (x.1, x.2.1) =
      fderiv ℝ (MeanMomentBounds.liftedTorusAverage f) x v := by
  obtain ⟨χ, _, hχs, hχf, he⟩ := exists_fiber_localization hV hx hf
  have hmean := average_derivative hχf (localize_periodic hχs hp) v x
  have hleft : PressureStream.torusAverage (fun y => fderiv ℝ (localize χ f) y v) (x.1, x.2.1) =
      PressureStream.torusAverage (fun y => fderiv ℝ f y v) (x.1, x.2.1) := by
    apply PressureStream.torusAverage_congr_slice
    intro Y
    rw [(he.eventuallyEq x.1 Y).fderiv_eq]
  have hright : fderiv ℝ (MeanMomentBounds.liftedTorusAverage (localize χ f)) x =
      fderiv ℝ (MeanMomentBounds.liftedTorusAverage f) x :=
    ((liftedTorusAverage_fiberLocal.germ he).eventuallyEq x.1 x.2.2).fderiv_eq
  rw [hleft, hright] at hmean
  exact hmean

theorem average_linear_on (hV : IsOpen V) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain V)) (hp : PeriodicOn V f)
    (v w : PressureStream.Lift S) (a b : ℝ × S → ℝ)
    (x : PressureStream.Lift S) (hx : x.2.1 ∈ V) :
    PressureStream.torusAverage (fun y => fderiv ℝ f y v +
      a (y.1, y.2.1) * fderiv ℝ f y w + b (y.1, y.2.1) * f y) (x.1, x.2.1) =
      fderiv ℝ (MeanMomentBounds.liftedTorusAverage f) x v +
        a (x.1, x.2.1) * fderiv ℝ (MeanMomentBounds.liftedTorusAverage f) x w +
        b (x.1, x.2.1) * MeanMomentBounds.liftedTorusAverage f x := by
  obtain ⟨χ, _, hχs, hχf, he⟩ := exists_fiber_localization hV hx hf
  have hmean := average_linear hχf (localize_periodic hχs hp) v w a b x
  have hleft : PressureStream.torusAverage (fun y => fderiv ℝ (localize χ f) y v +
      a (y.1, y.2.1) * fderiv ℝ (localize χ f) y w + b (y.1, y.2.1) * localize χ f y)
      (x.1, x.2.1) = PressureStream.torusAverage (fun y => fderiv ℝ f y v +
      a (y.1, y.2.1) * fderiv ℝ f y w + b (y.1, y.2.1) * f y) (x.1, x.2.1) := by
    apply PressureStream.torusAverage_congr_slice
    intro Y
    rw [(he.eventuallyEq x.1 Y).fderiv_eq, (he.eventuallyEq x.1 Y).self_of_nhds]
  have hbar := (liftedTorusAverage_fiberLocal.germ he).eventuallyEq x.1 x.2.2
  rw [hleft, hbar.fderiv_eq, hbar.self_of_nhds] at hmean
  exact hmean

theorem meanBar_dz_on (hV : IsOpen V) (o : Operators (PressureStream.Lift S))
    (f : ScalarField (PressureStream.Lift S))
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain V)) (hp : ∀ n, PeriodicOn V (f n)) :
    Agree (slowDomain V) (meanBar (o.dz f)) (o.dz (meanBar f)) := by
  intro n x hx
  change PressureStream.torusAverage (fun y => o.epsilon n * fderiv ℝ (f n) y o.eZ)
    (x.1, x.2.1) = _
  rw [AuxiliaryAverage.average_const_mul, average_derivative_on hV (hf n) (hp n) o.eZ x hx]
  rfl

theorem meanBar_radialDiv_on (hV : IsOpen V) (o : Operators (PressureStream.Lift S))
    (hradius : o.radius = Prod.fst)
    (hprofile : ∀ R s, s ∈ V → ∀ Y, o.radialProfile (R, (s, Y)) = o.radialProfile (R, (s, 0)))
    (f : ScalarField (PressureStream.Lift S))
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain V)) (hp : ∀ n, PeriodicOn V (f n))
    (c : ℝ) : Agree (slowDomain V) (meanBar (o.radialDiv c f)) (o.radialDiv c (meanBar f)) := by
  intro n x hx
  have he : PressureStream.torusAverage (o.radialDiv c f n) (x.1, x.2.1) =
      PressureStream.torusAverage (fun y => fderiv ℝ (f n) y o.eR +
        (o.radialFrequency n * o.radialProfile (y.1, (y.2.1, 0))) * fderiv ℝ (f n) y o.vR +
        (c * y.1⁻¹) * f n y) (x.1, x.2.1) := by
    apply PressureStream.torusAverage_congr_slice
    intro Y
    simp only [Operators.radialDiv, Operators.dr, graphDerivative, Operators.invRadius,
      hradius, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hprofile x.1 x.2.1 hx Y]
    ring
  change PressureStream.torusAverage (o.radialDiv c f n) (x.1, x.2.1) = _
  rw [he, average_linear_on hV (hf n) (hp n) o.eR o.vR
    (fun z => o.radialFrequency n * o.radialProfile (z.1, (z.2, 0))) (fun z => c * z.1⁻¹) x hx]
  simp only [Operators.radialDiv, Operators.dr, graphDerivative, Operators.invRadius,
    hradius, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [hprofile x.1 x.2.1 hx x.2.2]
  simp only [meanBar]
  ring

omit [FiniteDimensional ℝ S] in
theorem continuous_radialDiv_slice (hV : IsOpen V) (o : Operators (PressureStream.Lift S))
    (hradius : o.radius = Prod.fst)
    (hprofile : ∀ R s, s ∈ V → ∀ Y, o.radialProfile (R, (s, Y)) = o.radialProfile (R, (s, 0)))
    (f : ScalarField (PressureStream.Lift S))
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain V)) (c : ℝ)
    (n : ℕ) (x : PressureStream.Lift S) (hx : x.2.1 ∈ V) :
    Continuous (fun Y : PressureStream.Plane => o.radialDiv c f n (x.1, (x.2.1, Y))) := by
  have hd (v : PressureStream.Lift S) :=
    continuous_slice ((MeanIncrementBounds.SmoothOn.directional hf
      (slowDomain_open hV) v) n).continuousOn (x := x) hx
  have hh : Continuous (fun Y : PressureStream.Plane =>
    fderiv ℝ (f n) (x.1, (x.2.1, Y)) o.eR +
      (o.radialFrequency n * o.radialProfile (x.1, (x.2.1, 0))) *
        fderiv ℝ (f n) (x.1, (x.2.1, Y)) o.vR +
      (c * x.1⁻¹) * f n (x.1, (x.2.1, Y))) :=
    ((hd o.eR).add (continuous_const.mul (hd o.vR))).add
      (continuous_const.mul (continuous_slice (hf n).continuousOn (x := x) hx))
  apply hh.congr
  intro Y
  simp only [Operators.radialDiv, Operators.dr, graphDerivative, Operators.invRadius,
    hradius, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [hprofile x.1 x.2.1 hx Y]
  ring

theorem meanBar_fluxBalance_on (hV : IsOpen V) (o : Operators (PressureStream.Lift S))
    (hradius : o.radius = Prod.fst)
    (hprofile : ∀ R s, s ∈ V → ∀ Y, o.radialProfile (R, (s, Y)) = o.radialProfile (R, (s, 0)))
    (R A T : ScalarField (PressureStream.Lift S)) (c : ℝ)
    (hR : ∀ n, ContDiffOn ℝ ∞ (R n) (slowDomain V))
    (hA : ∀ n, ContDiffOn ℝ ∞ (A n) (slowDomain V))
    (hT : ∀ n, ContDiffOn ℝ ∞ (T n) (slowDomain V))
    (hpR : ∀ n, PeriodicOn V (R n)) (hpA : ∀ n, PeriodicOn V (A n))
    (hpT : ∀ n, PeriodicOn V (T n)) :
    Agree (slowDomain V) (meanBar (o.radialDiv c R + o.dz A - o.radialDiv c T))
      (o.radialDiv c (meanBar R - meanBar T) + o.dz (meanBar A)) := by
  intro n x hx
  have hRc := continuous_radialDiv_slice hV o hradius hprofile R hR c n x hx
  have hTc := continuous_radialDiv_slice hV o hradius hprofile T hT c n x hx
  have hAc : Continuous (fun Y : PressureStream.Plane => o.dz A n (x.1, (x.2.1, Y))) := by
    exact continuous_const.mul (continuous_slice ((MeanIncrementBounds.SmoothOn.directional hA
      (slowDomain_open hV) o.eZ) n).continuousOn hx)
  have hbars := FourierAlias.torusMean_sub (hRc.fun_add hAc) hTc
  rw [FourierAlias.torusMean_add hRc hAc] at hbars
  change meanBar (o.radialDiv c R + o.dz A - o.radialDiv c T) n x =
    meanBar (o.radialDiv c R) n x + meanBar (o.dz A) n x - meanBar (o.radialDiv c T) n x at hbars
  rw [meanBar_radialDiv_on hV o hradius hprofile R hR hpR c n hx,
    meanBar_dz_on hV o A hA hpA n hx,
    meanBar_radialDiv_on hV o hradius hprofile T hT hpT c n hx] at hbars
  rw [hbars]
  have hDR := ((liftedTorusAverage_contDiffOn hV (hR n)).contDiffAt
    ((slowDomain_open hV).mem_nhds hx)).differentiableAt (by simp)
  have hDT := ((liftedTorusAverage_contDiffOn hV (hT n)).contDiffAt
    ((slowDomain_open hV).mem_nhds hx)).differentiableAt (by simp)
  have hd := fderiv_fun_sub hDR hDT
  change fderiv ℝ (meanBar R n - meanBar T n) x = _ at hd
  simp only [Operators.radialDiv, Operators.dr, graphDerivative,
    Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hd,
    _root_.sub_apply]
  simp only [meanBar]
  ring

end LocalAverage

section MovingBarBounds

open StateMomentBalances

variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

/-- Exact leading covariance cancellation combines with the actual curl
covariance error and the higher virtual stress on the moving profile strip. -/
theorem matched_flux_mem (R R₀ T T₀ : ScalarField Point)
    (hR : ∀ n, ContDiffOn ℝ ∞ (R n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hR₀ : ∀ n, ContDiffOn ℝ ∞ (R₀ n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hT : ∀ n, ContDiffOn ℝ ∞ (T n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hT₀ : ∀ n, ContDiffOn ℝ ∞ (T₀ n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hcurl : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      (3 / 2 - ChartScales.kappa) (R - R₀))
    (hvirtual : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      2 (T - T₀))
    (hmatch : Agree (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL).domain
      (meanBar R₀) (meanBar T₀)) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      (3 / 2 - ChartScales.kappa) (meanBar R - meanBar T) := by
  have hRc := meanClass_liftedTorusAverage U a b cL cR ha hcL hcR ε L hε hεone hL
    (fun n => (hR n).sub (hR₀ n)) hcurl
  have hTc := (meanClass_liftedTorusAverage U a b cL cR ha hcL hcR ε L hε hεone hL
    (fun n => (hT n).sub (hT₀ n)) hvirtual).mono_exponent
      (show 3 / 2 - ChartScales.kappa ≤ (2 : ℝ) by norm_num [ChartScales.kappa])
  apply class_congr (Class.sub hRc hTc)
  intro n x hx
  have hslow := ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL x).mp hx).1
  have hr := LocalAverage.meanBar_sub_on R R₀ (fun n => (hR n).continuousOn)
    (fun n => (hR₀ n).continuousOn) n hslow
  have ht := LocalAverage.meanBar_sub_on T T₀ (fun n => (hT n).continuousOn)
    (fun n => (hT₀ n).continuousOn) n hslow
  have hm := hmatch n hx
  change meanBar (R - R₀) n x = _ at hr
  change meanBar (T - T₀) n x = _ at ht
  change (meanBar R - meanBar T) n x = (meanBar (R - R₀) - meanBar (T - T₀)) n x
  simp only [Pi.sub_apply] at *
  linarith

theorem fluxBalance_mem (o : Operators Point)
    (ho : OperatorBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      o ChartScales.kappa)
    (hradius : o.radius = Prod.fst)
    (hprofile : ∀ R s, s ∈ U.carrier → ∀ Y,
      o.radialProfile (R, (s, Y)) = o.radialProfile (R, (s, 0)))
    (R A T : ScalarField Point) (c : ℝ)
    (hR : ∀ n, ContDiffOn ℝ ∞ (R n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hA : ∀ n, ContDiffOn ℝ ∞ (A n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hT : ∀ n, ContDiffOn ℝ ∞ (T n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpR : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (R n))
    (hpA : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (A n))
    (hpT : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (T n))
    (hflux : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      (3 / 2 - ChartScales.kappa) (meanBar R - meanBar T))
    (haxial : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      (1 - ChartScales.kappa) A) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) (149 / 100)
      (meanBar (o.radialDiv c R + o.dz A - o.radialDiv c T)) := by
  have hrad := (ho.radialDiv hflux c).mono_exponent
    (show (149 / 100 : ℝ) ≤ 3 / 2 - ChartScales.kappa - ChartScales.kappa by norm_num
      [ChartScales.kappa])
  have hax := (ho.dz (meanClass_liftedTorusAverage U a b cL cR ha hcL hcR ε L hε hεone hL
    hA haxial)).mono_exponent
      (show (149 / 100 : ℝ) ≤ 1 - ChartScales.kappa + 1 by norm_num [ChartScales.kappa])
  apply class_congr (hrad.add hax)
  intro n x hx
  exact LocalAverage.meanBar_fluxBalance_on U.isOpen o hradius hprofile R A T c
    hR hA hT hpR hpA hpT n
    (((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL x).mp hx).1)

/-- The actual zero-mean state has both improved bar residuals, once the
two leading covariance identities have been applied. -/
theorem zeroMean_bar_bounds (c : Context Point) (u : State Point)
    (ho : OperatorBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      c.operators ChartScales.kappa)
    (hradius : c.operators.radius = Prod.fst)
    (hprofile : ∀ R s, s ∈ U.carrier → ∀ Y,
      c.operators.radialProfile (R, (s, Y)) = c.operators.radialProfile (R, (s, 0)))
    (hm : u.mean = ⟨0, 0, 0⟩)
    (hW : ∀ i j, MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      1 (u.covariance i j))
    (hWc : ∀ i j n, ContDiffOn ℝ ∞ (u.covariance i j n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hWp : ∀ i j n, PhysicalMeanDomain.PeriodicOn U.carrier (u.covariance i j n))
    (hp : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      (1 - ChartScales.kappa) u.pressure)
    (hpc : ∀ n, ContDiffOn ℝ ∞ (u.pressure n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.pressure n))
    (hθc : ∀ n, ContDiffOn ℝ ∞ (c.virtualTheta n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hθp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (c.virtualTheta n))
    (hzc : ∀ n, ContDiffOn ℝ ∞ (c.virtualAxial n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hzp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (c.virtualAxial n))
    (hθmatch : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      (3 / 2 - ChartScales.kappa) (meanBar (u.covariance 0 1) - meanBar c.virtualTheta))
    (hzmatch : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      (3 / 2 - ChartScales.kappa) (meanBar (u.covariance 0 2) - meanBar c.virtualAxial)) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) (149 / 100)
      (meanBar (u.thetaResidual c)) ∧
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) (149 / 100)
      (meanBar (u.axialResidual c)) := by
  have hW' (i j : Fin 3) := (hW i j).mono_exponent
    (show 1 - ChartScales.kappa ≤ 1 by norm_num [ChartScales.kappa])
  constructor
  · rw [zeroMean_theta c u hm]
    exact fluxBalance_mem U ha hcL hcR ε L hε hεone hL c.operators ho hradius hprofile
      (u.covariance 0 1) (u.covariance 2 1) c.virtualTheta 2
      (hWc 0 1) (hWc 2 1) hθc (hWp 0 1) (hWp 2 1) hθp hθmatch (hW' 2 1)
  · rw [zeroMean_axial c u hm]
    apply fluxBalance_mem U ha hcL hcR ε L hε hεone hL c.operators ho hradius hprofile
      (u.covariance 0 2) (u.covariance 2 2 + u.pressure) c.virtualAxial 1
      (hWc 0 2) (fun n => (hWc 2 2 n).add (hpc n)) hzc (hWp 0 2) ?_ hzp hzmatch
      ((hW' 2 2).add hp)
    intro n R s hs Y k
    exact congrArg₂ (· + ·) (hWp 2 2 n R s hs Y k) (hpp n R s hs Y k)

end MovingBarBounds

end MovingInitialization

namespace NativeResidual

open WeightedClasses LinearWaveBounds PrimaryConstruction

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}

noncomputable def piece (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (pref : Fin 2 → ℕ → ℝ) (s : StripData D) (c : Context D)
    (χ : ℕ → D × ℝ → PhaseCalculus.Slot) (b : ℕ → PhaseCalculus.Slow → ℝ)
    (frequency : ℕ → ℝ) (T : ℕ → D × ℝ → SmoothCovariance.Vec2)
    (mask cutoff : ℕ → D × ℝ → ℝ) (j : Fin 2) : PrimaryPiece (D × ℝ) where
  strip := HarmonicWaveInteraction.productStrip s
  directions := PrimaryResidualClass.directions c
  coefficients := nativeCoefficients F pref (HarmonicWaveInteraction.productStrip s)
    (PrimaryResidualClass.directions c) χ b frequency T mask j
  cutoff := cutoff

noncomputable def envelope (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (χ : ℕ → D × ℝ → PhaseCalculus.Slot) (j : Fin 2) : ℕ → D → ℝ :=
  fun n x => SignedWaveUpdate.phaseEnvelope F (pulseCoordinates (F j) χ) j n (x, 0)

/-- Native geometric and coefficient data. The principal equation, wave
amplitude bounds, homogeneous pressure bounds and nonlinear residual bound
are derived below rather than stored in this record. -/
structure Control (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (pref : Fin 2 → ℕ → ℝ) (s : StripData D) (c : Context D)
    (χ : ℕ → D × ℝ → PhaseCalculus.Slot) (b : ℕ → PhaseCalculus.Slow → ℝ)
    (frequency : ℕ → ℝ) (T : ℕ → D × ℝ → SmoothCovariance.Vec2)
    (mask cutoff : ℕ → D × ℝ → ℝ) (j : Fin 2) (kp : ℕ → ℤ) where
  operators : MeanIncrementBounds.OperatorBounds s c.operators ChartScales.kappa
  matching : PrimaryResidualClass.Matches s c
    (PrimaryMaterialDefect.coefficients (F j) b χ 0 0 frequency)
  coordinates : PrimaryMaterialDefect.NativeCoordinates (HarmonicWaveInteraction.productStrip s)
    (PrimaryResidualClass.directions c) χ
  scale : ∀ n, U.scale n = s.slow n
  native_jets : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain
    (HarmonicWaveInteraction.productStrip s))
    (fun n x => ((χ n x).1, (χ n x).2.2))
  normalized_jets : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain
    (HarmonicWaveInteraction.productStrip s))
    (pulseCoordinates (F j) χ)
  chart_smooth : ∀ n, ContDiffOn ℝ ∞ (χ n) (HarmonicWaveInteraction.productStrip s).domain
  chart_range : ∀ n x, x.1 ∈ s.domain → (χ n x).1 ∈ U.carrier n ∧
    (χ n x).2.2 ∈ Ioo (0 : ℝ) ((F j).L n)
  radius_pos : ∀ n x, x.1 ∈ s.domain → 0 < (χ n x).1.1
  epsilon : ∀ n, (F j).phase.epsilon n = s.epsilon n
  viscosity : ∀ n, (F j).viscosity n = s.epsilon n * frequency n ^ 2
  radial_base : UnweightedClass (HarmonicWaveInteraction.productStrip s) 1 (fun n x => b n (χ n
    x).1)
  radial_base_smooth : ∀ n, ContDiffOn ℝ ∞ (b n) (U.carrier n)
  frequency_bound : BandBound s (-(1 / 2 : ℝ)) frequency
  inverse_frequency : BandBound s (1 / 2) (fun n => 1 / frequency n)
  covariance : SignedWaveUpdate.CovarianceControl (HarmonicWaveInteraction.productStrip s)
    (SignedWaveUpdate.phaseMatrix F pref (pulseCoordinates (F j) χ)) T
  mask_bound : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 mask
  cutoff_bound : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 cutoff
  angle : ∀ n x (t : ℝ), χ n (x + t • ((0 : D), 1)) =
    ((χ n x).1, (χ n x).2.1 + t, (χ n x).2.2)
  target_angle : SignedWaveUpdate.FrozenAlong ((0 : D), 1) T
  mask_angle : SignedWaveUpdate.FrozenAlong ((0 : D), 1) mask
  cutoff_angle : SignedWaveUpdate.FrozenAlong ((0 : D), 1) cutoff
  slow_frozen : ∀ n x (t : ℝ),
    (χ n (x + t • (PrimaryResidualClass.directions c).fast)).1 = (χ n x).1
  target_frozen : SignedWaveUpdate.FrozenAlong (PrimaryResidualClass.directions c).fast T
  mask_frozen : SignedWaveUpdate.FrozenAlong (PrimaryResidualClass.directions c).fast mask
  clock : ∀ n x, x.1 ∈ s.domain → ∀ t : ℝ,
    χ n (x + t • (PrimaryResidualClass.directions c).fastField n x) =
      ((χ n x).1, (χ n x).2.1, (χ n x).2.2 + t)
  angular_frequency : ∀ n, frequency n * (F j).phase.p n = (kp n : ℝ)
  angular_ne : ∀ n, kp n ≠ 0
  geometry : ∀ n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip
    s).domain
    (fun x => (χ n x).1.1) ((PrimaryResidualClass.directions c).radialField n)
    (fun _ => ((0 : D), 1))
    ((PrimaryResidualClass.directions c).axialField (HarmonicWaveInteraction.productStrip s) n)

namespace Control

variable {F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U} {pref : Fin 2 → ℕ → ℝ}
    {s : StripData D} {c : Context D} {χ : ℕ → D × ℝ → PhaseCalculus.Slot}
    {b : ℕ → PhaseCalculus.Slow → ℝ} {frequency : ℕ → ℝ}
    {T : ℕ → D × ℝ → SmoothCovariance.Vec2} {mask cutoff : ℕ → D × ℝ → ℝ}
    {j : Fin 2} {kp : ℕ → ℤ}
    (C : Control F pref s c χ b frequency T mask cutoff j kp)

include C

theorem frequency_ne (n : ℕ) : frequency n ≠ 0 := by
  intro hz
  have h := C.angular_frequency n
  rw [hz, zero_mul] at h
  exact C.angular_ne n (by exact_mod_cast h.symm)

theorem envelope_eq : SignedWaveUpdate.phaseEnvelope F (pulseCoordinates (F j) χ) j =
    fun n p => envelope F χ j n p.1 := by
  funext n p
  have hi : CopyAngularInvariance.Invariant ((0 : D), 1)
      (SignedWaveUpdate.phaseEnvelope F (pulseCoordinates (F j) χ) j n) := by
    intro x t
    simp only [SignedWaveUpdate.phaseEnvelope, pulseCoordinates, C.angle]
  exact CopyAngularInvariance.invariant_eq_zeroSlice hi p.1 p.2

theorem inputBounds : InputBounds (HarmonicWaveInteraction.productStrip s)
    (fun n p => envelope F χ j n p.1) (1 / 2) ChartScales.kappa
    (PrimaryResidualClass.directions c) (piece F pref s c χ b frequency T mask cutoff
      j).coefficients := by
  have he := native_inputBounds F pref (HarmonicWaveInteraction.productStrip s)
    (PrimaryResidualClass.directions c) χ b frequency T mask j C.coordinates C.scale C.native_jets
    C.normalized_jets C.chart_range C.epsilon C.radius_pos
    (fun x hx => C.operators.weight_le_one x.1 hx) C.radial_base C.radial_base_smooth
    C.operators.kappa_nonneg (HarmonicWaveInteraction.class_lift C.operators.radialProfile)
    C.operators.radialFrequency C.operators.fastCoefficient C.frequency_bound C.inverse_frequency
    C.covariance C.mask_bound
  rw [C.envelope_eq] at he
  exact he

theorem inputs : PrimaryResidualClass.Inputs s (envelope F χ j) ChartScales.kappa c
    (piece F pref s c χ b frequency T mask cutoff j).coefficients cutoff kp := by
  let st := HarmonicWaveInteraction.productStrip s
  let dirs := PrimaryResidualClass.directions c
  let a := PrimaryMaterialDefect.coefficients (F j) b χ 0 0 frequency
  have hV (n : ℕ) (x : D × ℝ) (hx : x.1 ∈ s.domain) :
      (χ n x).1 ∈ U.carrier n ∧ (χ n x).2.2 ∈ (F j).V n :=
    ⟨(C.chart_range n x hx).1, (F j).interval n
      ⟨(C.chart_range n x hx).2.1.le, (C.chart_range n x hx).2.2.le⟩⟩
  have ha := native_angularInputs F pref st dirs χ b frequency T mask cutoff j C.angle
    C.chart_smooth (fun n x hx => (C.chart_range n x hx).1) C.target_angle C.mask_angle
    C.cutoff_angle (PrimaryResidualClass.invariant_fst c.operators.radialProfile)
  have hn := native_normal_jets (F j) st dirs χ b 0 0 frequency C.coordinates C.native_jets C.scale
    hV C.epsilon
  have hsolve := native_principal_zero F pref st dirs χ b frequency T mask j C.coordinates C.scale
    C.normalized_jets C.chart_range C.epsilon C.viscosity C.covariance C.mask_bound C.slow_frozen
    C.target_frozen C.mask_frozen C.clock C.frequency_ne
  refine {
    matching := ⟨C.matching.epsilon, C.matching.radius, C.matching.base⟩
    operators := C.operators
    loss_le := by norm_num [ChartScales.kappa]
    coefficients := C.inputBounds
    cutoff := C.cutoff_bound
    angular := {
      radius := ha.radius
      radialBase := ha.radial_base
      frequencyBase := ha.frequency_base
      axialBase := ha.axial_base
      phase := fun n => ⟨(F j).phase.p n, ha.phase n⟩
      amplitude := ha.amplitude j
      pressure := ha.pressure j
      cutoff := C.cutoff_angle }
    phase_smooth := ha.phase_smooth
    phase_split := ?_
    frequency_ne := C.frequency_ne
    angular_ne := C.angular_ne
    normal_jets := hn
    normal_bounds := ⟨(F j).b, (F j).M ^ 2 + 3 * (F j).M, (F j).b_pos, ?_, ?_⟩
    inverse_frequency := C.inverse_frequency
    geometry := C.geometry
    tangent := ?_
    principal_zero := fun n x hx _ => hsolve n x hx
    profile_nonneg := ?_
    profile_le_one := ?_
    radius_pos := ?_ }
  · intro n x θ
    have hh := CopyAngularInvariance.affinePhase_eq_zeroSlice (ha.phase n) x θ
    change frequency n * a.phase n (x, θ) = frequency n * a.phase n (x, 0) + _
    rw [hh, mul_add, ← mul_assoc, C.angular_frequency n]
  · intro n x hx
    exact (native_normal_range (F j) st dirs χ b 0 0 frequency C.coordinates hV C.epsilon n hx).1
  · intro n x hx
    exact (native_normal_range (F j) st dirs χ b 0 0 frequency C.coordinates hV C.epsilon n hx).2
  · intro n x hx
    exact native_tangent F pref st dirs χ b frequency T mask j C.coordinates hV C.epsilon n hx
  · intro n x hx
    exact (PrimaryPulseBounds.referenceP_pos _ _ _ _).le
  · intro n x hx
    change PrimaryPulseBounds.referenceP _ _ _ ((F j).L n * (pulseCoordinates (F j) χ n (x, 0)).2)
      ≤ 1
    rw [pulseCoordinates_scaled]
    exact PrimaryPulseBounds.referenceP_le_one ((F j).lam_pos n) ((F j).u_pos n) ((F j).L_pos n)
      ⟨(C.chart_range n (x, 0) hx).2.1.le, (C.chart_range n (x, 0) hx).2.2.le⟩
  · intro x hx
    have hr := congrArg (fun f : ℕ → D × ℝ → ℝ => f 0 (x, 0)) C.matching.radius
    change (χ 0 (x, 0)).1.1 = c.operators.radius x at hr
    rw [← hr]
    exact C.radius_pos 0 (x, 0) hx

/-- The nonlinear good residual belongs to the actual primary cutoff curl,
with its actual Gaussian error and any retained zero-mode alias. -/
theorem residual_bounds (u : State D) (hmean : u.mean = ⟨0, 0, 0⟩)
    (A : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, HarmonicFields.BandLimited (A n i) 0) :
    let p := piece F pref s c χ b frequency T mask cutoff j
    let Φ := fun n x => p.coefficients.phase n (x, 0)
    (HarmonicResidual.residualBlock c u (p.harmonicBlock Φ kp)
      (p.excludedBlock Φ kp).velocity A).WaveBounds s (envelope F χ j) (7 / 10) ∧
    (HarmonicResidual.residualBlock c u (p.harmonicBlock Φ kp)
      (p.excludedBlock Φ kp).velocity A).BandLimited 2 := by
  exact ⟨C.inputs.initial_residual_class_of_zero_mode u hmean A hA,
    PrimaryResidualClass.Inputs.initial_residual_band u A hA⟩

end Control

end NativeResidual

namespace AssembledPrimary

open WeightedClasses LabelSumBounds

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {ι : Type} [Countable ι] [Nonempty ι]

theorem conjugatePair_uniform {s : StripData D} {w : ι → ℕ → D → ℝ} {α : ℝ}
    {f : ι → ℕ → D → ℂ} (hf : UniformClass s w α f) (j : ℤ) :
    UniformClass s w α (fun l n x => ErrorHarmonics.conjugatePair 1 (f l n) j x) := by
  exact UniformPrimaryWeights.uniform_of_pull (UniformPrimaryWeights.enumeration_surjective ι)
    (SignedWaveUpdate.conjugatePair_class
      (UniformPrimaryWeights.pull_class hf (UniformPrimaryWeights.enumeration ι)) j)

theorem block_uniform {s : StripData D} {P : ι → ℕ → D → ℝ} {α : ℝ}
    (a : ι → LinearWaveBounds.WaveCoefficients (D × ℝ))
    (Φ : ι → ℕ → D → ℝ) (kp : ι → ℕ → ℤ)
    (ha : UniformWaveClass s P α (fun l n x => (a l).amplitude n (x, 0))) :
    ∀ i j, UniformWaveClass s P α
      (fun l n x => (PrimaryHarmonics.block (a l) (Φ l) (kp l)).velocity n i j x) :=
  fun i j => conjugatePair_uniform (UniformPrimaryWeights.component_class ha i) j

/-- Uniform coefficient bounds for the exact, tangent, and correction blocks. -/
private theorem primary_block_uniform_bounds {s : StripData D} {P : ι → ℕ → D → ℝ}
    (pieces : ι → PrimaryPiece (D × ℝ)) (Φ : ι → ℕ → D → ℝ) (kp : ι → ℕ → ℤ)
    (ht : UniformWaveClass s P (1 / 2)
      (fun l n x => ((pieces l).coefficients.withCutoff (pieces l).cutoff).amplitude n (x, 0)))
    (hc : UniformWaveClass s P (1 - ChartScales.kappa) (fun l n x =>
      ((pieces l).coefficients.withCutoff (pieces l).cutoff).curlCorrection
        (pieces l).strip (pieces l).directions n (x, 0))) :
    (∀ i j, UniformWaveClass s P (1 / 2)
      (fun l n x => ((pieces l).harmonicBlock (Φ l) (kp l)).velocity n i j x)) ∧
    (∀ i j, UniformWaveClass s P (1 / 2)
      (fun l n x => ((pieces l).tangentBlock (Φ l) (kp l)).velocity n i j x)) ∧
    (∀ i j, UniformWaveClass s P (1 - ChartScales.kappa)
      (fun l n x => ((pieces l).differenceBlock (Φ l) (kp l)).velocity n i j x)) := by
  have het : UniformWaveClass s P (1 / 2) (fun l n x => (pieces l).exactCoefficients.amplitude n
    (x, 0)) :=
    ht.add (hc.mono_exponent (by norm_num [ChartScales.kappa]))
  have hct : UniformWaveClass s P (1 - ChartScales.kappa)
      (fun l n x => (pieces l).differenceCoefficients.amplitude n (x, 0)) := by
    apply hc.congr
    intro l n x hx
    simp [PrimaryPiece.differenceCoefficients, PrimaryPiece.exactCoefficients,
      LinearWaveBounds.WaveCoefficients.corrected, LinearWaveBounds.WaveCoefficients.addAmplitude]
  have hA := block_uniform (fun l => (pieces l).exactCoefficients) Φ kp het
  have hT := block_uniform (fun l => (pieces l).coefficients.withCutoff (pieces l).cutoff) Φ kp ht
  have hC := block_uniform (fun l => (pieces l).differenceCoefficients) Φ kp hct
  exact ⟨hA, hT, hC⟩

omit [Countable ι] [Nonempty ι] in
/-- The concrete harmonic blocks have the required supports and finite sums. -/
private theorem primary_block_support_and_sums {s : StripData D}
    {d h : ℝ} {vr vt : TorusInverse.Plane}
    (sys : PartitionedCovariance.SlotSystem d h vr vt)
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (χ : ℕ → D → WindowPoint) (Y : ℕ → D → TorusInverse.Plane)
    (pieces : ι → PrimaryPiece (D × ℝ)) (baseError : Oscillation D)
    (Φ : ι → ℕ → D → ℝ) (kp : ι → ℕ → ℤ)
    (htAngle : ∀ l, ErrorHarmonics.AngleIndependent
      ((pieces l).coefficients.withCutoff (pieces l).cutoff).amplitude)
    (heAngle : ∀ l, ErrorHarmonics.AngleIndependent (pieces l).exactCoefficients.amplitude)
    (hphase : ∀ l n x θ, (pieces l).coefficients.frequency n * (pieces l).coefficients.phase n (x,
      θ) =
      (pieces l).coefficients.frequency n * Φ l n x + (kp l n : ℝ) * θ)
    (hsupport : ∀ l n x, x ∈ s.domain → ∀ θ,
      (x, θ) ∈ tsupport (((pieces l).coefficients.withCutoff (pieces l).cutoff).amplitude n) →
      χ n x ∈ closedWindow d (label n l) ∧
        Y n x ∈ SlotGeometry.liftedSupport (SlotColoring.nativeIndex h (label n l).1)
          (PartitionedCovariance.slotSet h sys.radius vr vt (label n l))) :
    SupportedOscillations sys label χ Y s.domain
      (fun l => ((pieces l).harmonicBlock (Φ l) (kp l)).oscillation) ∧
    SupportedOscillations sys label χ Y s.domain
      (fun l => ((pieces l).tangentBlock (Φ l) (kp l)).oscillation) ∧
    SupportedOscillations sys label χ Y s.domain
      (fun l => ((pieces l).differenceBlock (Φ l) (kp l)).oscillation) ∧
    fieldSum labels (fun l => ((pieces l).harmonicBlock (Φ l) (kp l)).oscillation) =
      (bandSeed labels pieces baseError).oscillation ∧
    fieldSum labels (fun l => ((pieces l).tangentBlock (Φ l) (kp l)).oscillation) =
      fieldSum labels (fun l => (pieces l).tangentVelocity) ∧
    fieldSum labels (fun l => ((pieces l).tangentBlock (Φ l) (kp l)).oscillation) +
      fieldSum labels (fun l => ((pieces l).differenceBlock (Φ l) (kp l)).oscillation) =
        (bandSeed labels pieces baseError).oscillation := by
  let A := fun l => (pieces l).harmonicBlock (Φ l) (kp l)
  let T := fun l => (pieces l).tangentBlock (Φ l) (kp l)
  let C := fun l => (pieces l).differenceBlock (Φ l) (kp l)
  have heq (l : ι) : (A l).oscillation = (pieces l).velocity := by
    funext n x i
    exact PrimaryHarmonics.block_velocity_represents (pieces l).exactCoefficients
      (Φ l) (kp l) (heAngle l) (hphase l) n x i
  have htq (l : ι) : (T l).oscillation = (pieces l).tangentVelocity := by
    funext n x i
    exact PrimaryHarmonics.block_velocity_represents
      ((pieces l).coefficients.withCutoff (pieces l).cutoff)
      (Φ l) (kp l) (htAngle l) (hphase l) n x i
  have hcq (l : ι) : (C l).oscillation = (pieces l).velocity - (pieces l).tangentVelocity :=
    (pieces l).differenceBlock_represents (Φ l) (kp l) (heAngle l) (htAngle l) (hphase l)
  have hsE : SupportedOscillations sys label χ Y s.domain (fun l => (pieces l).velocity) := by
    intro l n x hx θ i hn
    apply hsupport l n x hx θ
    apply (pieces l).velocity_tsupport_subset_tangent n
    apply subset_tsupport
    intro hz
    exact hn (congrFun hz i)
  have hsT : SupportedOscillations sys label χ Y s.domain (fun l => (pieces l).tangentVelocity) :=
    by
    intro l n x hx θ i hn
    apply hsupport l n x hx θ
    apply (pieces l).tangentVelocity_tsupport_subset n
    apply subset_tsupport
    intro hz
    exact hn (congrFun hz i)
  have hsA : SupportedOscillations sys label χ Y s.domain (fun l => (A l).oscillation) := by
    simpa only [heq] using hsE
  have hsB : SupportedOscillations sys label χ Y s.domain (fun l => (T l).oscillation) := by
    simpa only [htq] using hsT
  have hsC : SupportedOscillations sys label χ Y s.domain (fun l => (C l).oscillation) := by
    simpa only [hcq] using hsE.sub hsT
  have hAsum : fieldSum labels (fun l => (A l).oscillation) = (bandSeed labels pieces
    baseError).oscillation := by
    simp only [heq]
    rfl
  have hTsum : fieldSum labels (fun l => (T l).oscillation) = fieldSum labels (fun l => (pieces
    l).tangentVelocity) := by
    simp only [htq]
  have hsum : fieldSum labels (fun l => (T l).oscillation) + fieldSum labels (fun l => (C
    l).oscillation) =
      (bandSeed labels pieces baseError).oscillation := by
    funext n x i
    simp only [fieldSum, Pi.add_apply, hcq, htq, Pi.sub_apply, Finset.sum_sub_distrib, bandSeed]
    ring
  exact ⟨hsA, hsB, hsC, hAsum, hTsum, hsum⟩

omit [Countable ι] [Nonempty ι] in
/-- Transfer the generic harmonic covariance estimates along the sum identities. -/
private theorem covariance_bounds_of_blocks {s : StripData D} {P : ι → ℕ → D → ℝ}
    {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1)
    (χ : ℕ → D → WindowPoint) (hχ : ∀ n, ContinuousOn (χ n) s.domain)
    (Y : ℕ → D → TorusInverse.Plane)
    (A T C : ι → HarmonicBlock D)
    (hAband : ∀ l, (A l).BandLimited 1)
    (hTband : ∀ l, (T l).BandLimited 1)
    (hCband : ∀ l, (C l).BandLimited 1)
    (hcarrier : ∀ l, SameCarrier (T l) (C l))
    (hA : ∀ i j, UniformWaveClass s P (1 / 2) (fun l n x => (A l).velocity n i j x))
    (hT : ∀ i j, UniformWaveClass s P (1 / 2) (fun l n x => (T l).velocity n i j x))
    (hC : ∀ i j, UniformWaveClass s P (1 - ChartScales.kappa)
      (fun l n x => (C l).velocity n i j x))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hkpA : ∀ l n, (A l).angularFrequency n ≠ 0)
    (hkpT : ∀ l n, (T l).angularFrequency n ≠ 0)
    (hsA : SupportedOscillations sys label χ Y s.domain (fun l => (A l).oscillation))
    (hsT : SupportedOscillations sys label χ Y s.domain (fun l => (T l).oscillation))
    (hsC : SupportedOscillations sys label χ Y s.domain (fun l => (C l).oscillation))
    (u v : Oscillation D)
    (hAsum : fieldSum labels (fun l => (A l).oscillation) = u)
    (hTsum : fieldSum labels (fun l => (T l).oscillation) = v)
    (hsum : fieldSum labels (fun l => (T l).oscillation) +
      fieldSum labels (fun l => (C l).oscillation) = u) :
    (∀ i j, MeanClass s 1 (bilinearCovariance u u i j)) ∧
    (∀ i j, MeanClass s (3 / 2 - ChartScales.kappa) (fun n x =>
      bilinearCovariance u u i j n x - bilinearCovariance v v i j n x)) := by
  constructor
  · intro i j
    have hb := harmonic_covariance_sum_mem labels label hinj hlevel χ hχ Y A A 1
      hAband (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hA hA hP0 hP1 hkpA hsA hsA i j
    rw [hAsum] at hb
    rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at hb
    exact hb
  · intro i j
    have hb := harmonic_covariance_increment_sum_mem
      (by norm_num [ChartScales.kappa] : (1 / 2 : ℝ) ≤ 1 - ChartScales.kappa)
      labels label hinj hlevel χ hχ Y T C 1 hTband hCband hcarrier
      hT hC hP0 hP1 hkpT hsT hsC i j
    rw [show (1 / 2 : ℝ) + (1 - ChartScales.kappa) =
      3 / 2 - ChartScales.kappa by ring] at hb
    rw [hsum, hTsum] at hb
    exact hb

/-- The actual sum covariance and its tangent-to-curl error. The finite
active label set may grow; only the proved slot/window overlap enters the
estimate. The support input concerns the explicitly cut amplitude. -/
theorem covariance_bounds {s : StripData D} {P : ι → ℕ → D → ℝ}
    {d h : ℝ} {vr vt : TorusInverse.Plane}
    (sys : PartitionedCovariance.SlotSystem d h vr vt)
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1)
    (χ : ℕ → D → WindowPoint) (hχ : ∀ n, ContinuousOn (χ n) s.domain)
    (Y : ℕ → D → TorusInverse.Plane)
    (pieces : ι → PrimaryPiece (D × ℝ)) (baseError : Oscillation D)
    (Φ : ι → ℕ → D → ℝ) (kp : ι → ℕ → ℤ)
    (ht : UniformWaveClass s P (1 / 2)
      (fun l n x => ((pieces l).coefficients.withCutoff (pieces l).cutoff).amplitude n (x, 0)))
    (hc : UniformWaveClass s P (1 - ChartScales.kappa) (fun l n x =>
      ((pieces l).coefficients.withCutoff (pieces l).cutoff).curlCorrection
        (pieces l).strip (pieces l).directions n (x, 0)))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hkp : ∀ l n, kp l n ≠ 0)
    (htAngle : ∀ l, ErrorHarmonics.AngleIndependent
      ((pieces l).coefficients.withCutoff (pieces l).cutoff).amplitude)
    (heAngle : ∀ l, ErrorHarmonics.AngleIndependent (pieces l).exactCoefficients.amplitude)
    (hphase : ∀ l n x θ, (pieces l).coefficients.frequency n * (pieces l).coefficients.phase n (x,
      θ) =
      (pieces l).coefficients.frequency n * Φ l n x + (kp l n : ℝ) * θ)
    (hsupport : ∀ l n x, x ∈ s.domain → ∀ θ,
      (x, θ) ∈ tsupport (((pieces l).coefficients.withCutoff (pieces l).cutoff).amplitude n) →
      χ n x ∈ closedWindow d (label n l) ∧
        Y n x ∈ SlotGeometry.liftedSupport (SlotColoring.nativeIndex h (label n l).1)
          (PartitionedCovariance.slotSet h sys.radius vr vt (label n l))) :
    (∀ i j, MeanClass s 1 ((bandSeed labels pieces baseError).covariance i j)) ∧
    (∀ i j, MeanClass s (3 / 2 - ChartScales.kappa) (fun n x =>
      (bandSeed labels pieces baseError).covariance i j n x -
        bilinearCovariance (fieldSum labels (fun l => (pieces l).tangentVelocity))
          (fieldSum labels (fun l => (pieces l).tangentVelocity)) i j n x)) := by
  obtain ⟨hA, hT, hC⟩ := primary_block_uniform_bounds pieces Φ kp ht hc
  obtain ⟨hsA, hsT, hsC, hAsum, hTsum, hsum⟩ :=
    primary_block_support_and_sums sys labels label χ Y pieces baseError Φ kp
      htAngle heAngle hphase hsupport
  exact covariance_bounds_of_blocks labels label hinj hlevel χ hχ Y
    (fun l => (pieces l).harmonicBlock (Φ l) (kp l))
    (fun l => (pieces l).tangentBlock (Φ l) (kp l))
    (fun l => (pieces l).differenceBlock (Φ l) (kp l))
    (fun l => PrimaryHarmonics.block_band _ _ _)
    (fun l => PrimaryHarmonics.block_band _ _ _)
    (fun l => PrimaryHarmonics.block_band _ _ _)
    (fun _ => ⟨rfl, rfl, rfl⟩) hA hT hC hP0 hP1 hkp hkp hsA hsT hsC
    (bandSeed labels pieces baseError).oscillation
    (fieldSum labels (fun l => (pieces l).tangentVelocity)) hAsum hTsum hsum

end AssembledPrimary


namespace MovingInitialization

open Set Filter CorrectionState WeightedClasses MeanIncrementBounds VariableGaugeMean
  LocalSignedRequest
open scoped ContDiff Topology

namespace InitialRegularity

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem periodic_directional {V : Set S} (hV : IsOpen V)
    {f : PressureStream.Lift S → ℝ} (hp : PhysicalMeanDomain.PeriodicOn V f)
    (v : PressureStream.Lift S) :
    PhysicalMeanDomain.PeriodicOn V (fun x => fderiv ℝ f x v) := by
  intro R s hs Y k
  let a : PressureStream.Lift S := (0, (0, ((k.1 : ℝ), (k.2 : ℝ))))
  have he : (fun x : PressureStream.Lift S => f (x + a)) =ᶠ[𝓝 (R, (s, Y))] f := by
    filter_upwards [(PhysicalMeanDomain.slowDomain_open hV).mem_nhds hs] with x hx
    simpa only [a, Prod.add_def, add_zero] using hp x.1 x.2.1 hx x.2.2 k
  have hd : fderiv ℝ (fun x => f (x + a)) (R, (s, Y)) = fderiv ℝ f (R, (s, Y)) := he.fderiv_eq
  rw [fderiv_comp_add_right] at hd
  simpa only [a, Prod.add_def, add_zero] using
    congrArg (fun L : PressureStream.Lift S →L[ℝ] ℝ => L v) hd

theorem periodic_radialDiv {V : Set S} (hV : IsOpen V)
    (o : Operators (PressureStream.Lift S)) (hR : o.radius = Prod.fst)
    (hprofile : ∀ R s, s ∈ V → ∀ Y,
      o.radialProfile (R, (s, Y)) = o.radialProfile (R, (s, 0)))
    {f : ScalarField (PressureStream.Lift S)} (hp : ∀ n, PhysicalMeanDomain.PeriodicOn V (f n))
    (c : ℝ) : ∀ n, PhysicalMeanDomain.PeriodicOn V (o.radialDiv c f n) := by
  intro n R s hs Y k
  simp only [Operators.radialDiv, Operators.dr, graphDerivative, Operators.invRadius,
    hR, periodic_directional hV (hp n) o.eR R s hs Y k,
    periodic_directional hV (hp n) o.vR R s hs Y k,
    hp n R s hs Y k, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  rw [hprofile R s hs _, hprofile R s hs Y]

theorem periodic_dz {V : Set S} (hV : IsOpen V)
    (o : Operators (PressureStream.Lift S))
    {f : ScalarField (PressureStream.Lift S)} (hp : ∀ n, PhysicalMeanDomain.PeriodicOn V (f n)) :
    ∀ n, PhysicalMeanDomain.PeriodicOn V (o.dz f n) := by
  intro n R s hs Y k
  simp only [Operators.dz, periodic_directional hV (hp n) o.eZ R s hs Y k]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem value_zero_off_gauge {a b : ℝ} {V : Set S} {ell : S → ℝ}
    {f : PressureStream.Lift S → ℝ} (hf : SupportedGauge a b ell V f)
    {x : PressureStream.Lift S} (hx : x.2.1 ∈ V)
    (hr : x.1 ∉ Icc (ell x.2.1 * a) (ell x.2.1 * b)) : f x = 0 := by
  by_contra hn
  exact hr (hf x hx hn)

theorem deriv_zero_off_gauge {a b : ℝ} {V : Set S} (hV : IsOpen V) {ell : S → ℝ}
    (hell : ContinuousOn ell V) {f : PressureStream.Lift S → ℝ}
    (hf : SupportedGauge a b ell V f) {x : PressureStream.Lift S} (hx : x.2.1 ∈ V)
    (hr : x.1 ∉ Icc (ell x.2.1 * a) (ell x.2.1 * b)) (v : PressureStream.Lift S) :
    fderiv ℝ f x v = 0 :=
  value_zero_off_gauge (fderiv_apply_supportedGauge hV hell hf (fun _ => v)) hx hr

end InitialRegularity

section RawRegularity

variable {coord : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hell : ∀ n, g.length n = qLength coord)
    (c : Context Point) (u : State Point)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hprofile : ∀ R s, s ∈ U.carrier → ∀ Y,
      c.operators.radialProfile (R, (s, Y)) = c.operators.radialProfile (R, (s, 0)))
    (hm : u.mean = ⟨0, 0, 0⟩)
    (hWc : ∀ i j n, ContDiffOn ℝ ∞ (u.covariance i j n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hWp : ∀ i j n, PhysicalMeanDomain.PeriodicOn U.carrier (u.covariance i j n))
    (hWs : ∀ i j n, SupportedGauge g.radial.inner g.radial.outer (qLength coord)
      U.carrier (u.covariance i j n))

include hop hprofile hm hWp in
theorem zeroMean_gr_periodic : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.gr c n) := by
  rw [zeroMean_gr c u hm]
  intro n R s hs Y k
  simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
    InitialRegularity.periodic_radialDiv U.isOpen c.operators hop.radius_eq hprofile (hWp 0 0) 1 n
      R s hs Y k,
    InitialRegularity.periodic_dz U.isOpen c.operators (hWp 2 0) n R s hs Y k,
    Operators.invRadius, hop.radius_eq, hWp 1 1 n R s hs Y k]

include ha hd hell hop hm hWc hWs in
theorem zeroMean_pressure_regular :
    (∀ n, ContDiffOn ℝ ∞ ((reconstructState g c u).pressure n) (PhysicalMeanDomain.slowDomain
      U.carrier)) ∧
    (∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      ((reconstructState g c u).pressure n)) := by
  have hgc := zeroMean_gr_smooth U ha g.radial.inner_lt_outer c u hop hm hWc hWs
  have hgs := zeroMean_gr_supportedGauge U.isOpen
    (((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun s hs => U.time_pos s
      hs)).continuousOn)
    c u hm hWs
  constructor <;> intro n
  · simpa only [reconstructState, hell] using meanPressure_q_contDiffOn U ha
      g.radial.inner_lt_outer hd (g.radial.frequency n) g.radial.radialDirection (hgc n) (hgs n)
  · simpa only [reconstructState, hell] using meanPressure_q_supportedGauge U ha
      g.radial.inner_lt_outer hd (g.radial.frequency n) g.radial.radialDirection (hgc n) (hgs n)

include hell hop hprofile hm hWp in
theorem zeroMean_pressure_periodic :
    ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((reconstructState g c u).pressure n) := by
  intro n
  simpa only [reconstructState, hell] using meanPressure_periodicOn g.radial.inner_lt_outer
    g.radial.exponent (g.radial.frequency n) (qLength coord) g.radial.radialDirection
    (zeroMean_gr_periodic U c u hop hprofile hm hWp n)

include ha hd hell hop hm hWc hWs in
theorem zeroMean_raw_smooth
    (hθc : ∀ n, ContDiffOn ℝ ∞ (c.virtualTheta n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hzc : ∀ n, ContDiffOn ℝ ∞ (c.virtualAxial n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hθs : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      (c.virtualTheta n))
    (hzs : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      (c.virtualAxial n)) :
    (∀ n, ContDiffOn ℝ ∞ ((reconstructState g c u).thetaResidual c n)
      (PhysicalMeanDomain.slowDomain U.carrier)) ∧
    (∀ n, ContDiffOn ℝ ∞ ((reconstructState g c u).axialResidual c n)
      (PhysicalMeanDomain.slowDomain U.carrier)) := by
  obtain ⟨a₀, b₀, L₀, ha₀, _, _, _, hleft, hright, _⟩ :=
    qLength_reference_bounds U ha g.radial.inner_lt_outer
  have hshell (f : ScalarField Point)
      (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
      (hs : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier (f n)) :
      LocalRankDefect.LocalShell a₀ b₀ U.carrier f := by
    refine ⟨hf, ?_⟩
    intro n x hx hn
    exact ⟨(hleft _ hx).trans (hs n x hx hn).1, (hs n x hx hn).2.trans (hright _ hx)⟩
  have hW := fun i j => hshell (u.covariance i j) (hWc i j) (hWs i j)
  have hθ := hshell c.virtualTheta hθc hθs
  have hz := hshell c.virtualAxial hzc hzs
  obtain ⟨hpc, hps⟩ := zeroMean_pressure_regular U g ha hd hell c u hop hm hWc hWs
  have hp := hshell (reconstructState g c u).pressure hpc hps
  have hm' : (reconstructState g c u).mean = ⟨0, 0, 0⟩ := hm
  constructor
  · rw [zeroMean_theta c (reconstructState g c u) hm']
    exact ((((hW 0 1).radialDiv ha₀ U.isOpen hop 2).add
      ((hW 2 1).dz U.isOpen c.operators)).sub (hθ.radialDiv ha₀ U.isOpen hop 2)).smooth
  · rw [zeroMean_axial c (reconstructState g c u) hm']
    exact ((((hW 0 2).radialDiv ha₀ U.isOpen hop 1).add
      (((hW 2 2).add hp).dz U.isOpen c.operators)).sub (hz.radialDiv ha₀ U.isOpen hop 1)).smooth

include ha hd hell hop hm hWc hWs in
theorem zeroMean_raw_supported
    (hθs : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      (c.virtualTheta n))
    (hzs : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      (c.virtualAxial n)) :
    (∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      ((reconstructState g c u).thetaResidual c n)) ∧
    (∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      ((reconstructState g c u).axialResidual c n)) := by
  classical
  have hL : ContinuousOn (qLength coord) U.carrier :=
    ((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun s hs => U.time_pos s
      hs)).continuousOn
  obtain ⟨hpc, hps⟩ := zeroMean_pressure_regular U g ha hd hell c u hop hm hWc hWs
  have hm' : (reconstructState g c u).mean = ⟨0, 0, 0⟩ := hm
  have hr (f : ScalarField Point)
      (hs : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier (f n))
      (k : ℝ) (n : ℕ) (x : Point) (hx : x.2.1 ∈ U.carrier)
      (h : x.1 ∉ Icc (qLength coord x.2.1 * g.radial.inner) (qLength coord x.2.1 * g.radial.outer))
        :
      c.operators.radialDiv k f n x = 0 := by
    have hv := InitialRegularity.value_zero_off_gauge (hs n) hx h
    have hd := InitialRegularity.deriv_zero_off_gauge U.isOpen hL (hs n) hx h
    simp [Operators.radialDiv, Operators.dr, graphDerivative, hv, hd]
  have hz (f : ScalarField Point)
      (hs : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier (f n))
      (n : ℕ) (x : Point) (hx : x.2.1 ∈ U.carrier)
      (h : x.1 ∉ Icc (qLength coord x.2.1 * g.radial.inner) (qLength coord x.2.1 * g.radial.outer))
        :
      c.operators.dz f n x = 0 := by
    simp [Operators.dz, InitialRegularity.deriv_zero_off_gauge U.isOpen hL (hs n) hx h]
  constructor
  · intro n x hx hn
    by_contra h
    apply hn
    rw [zeroMean_theta c (reconstructState g c u) hm']
    simp only [Pi.sub_apply, Pi.add_apply]
    change c.operators.radialDiv 2 (u.covariance 0 1) n x +
      c.operators.dz (u.covariance 2 1) n x - c.operators.radialDiv 2 c.virtualTheta n x = 0
    rw [hr _ (hWs 0 1) 2 n x hx h, hz _ (hWs 2 1) n x hx h, hr _ hθs 2 n x hx h]
    ring
  · intro n x hx hn
    by_contra h
    apply hn
    rw [zeroMean_axial c (reconstructState g c u) hm']
    have hsum : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.covariance 2 2 n + (reconstructState g c u).pressure n) := by
      intro n y hy hne
      by_contra hr'
      exact hne (by simp [InitialRegularity.value_zero_off_gauge (hWs 2 2 n) hy hr',
        InitialRegularity.value_zero_off_gauge (hps n) hy hr'])
    simp only [Pi.sub_apply, Pi.add_apply]
    change c.operators.radialDiv 1 (u.covariance 0 2) n x +
      c.operators.dz (u.covariance 2 2 + (reconstructState g c u).pressure) n x -
        c.operators.radialDiv 1 c.virtualAxial n x = 0
    rw [hr _ (hWs 0 2) 1 n x hx h,
      hz (u.covariance 2 2 + (reconstructState g c u).pressure) hsum n x hx h,
      hr _ hzs 1 n x hx h]
    ring

include hell hop hprofile hm hWp in
theorem zeroMean_raw_periodic
    (hθp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (c.virtualTheta n))
    (hzp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (c.virtualAxial n)) :
    (∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((reconstructState g c u).thetaResidual c n)) ∧
    (∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((reconstructState g c u).axialResidual c n)) :=
      by
  have hp := zeroMean_pressure_periodic U g hell c u hop hprofile hm hWp
  have hm' : (reconstructState g c u).mean = ⟨0, 0, 0⟩ := hm
  have hsum : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier
      (u.covariance 2 2 n + (reconstructState g c u).pressure n) := by
    intro n R s hs Y k
    exact congrArg₂ (· + ·) (hWp 2 2 n R s hs Y k) (hp n R s hs Y k)
  constructor
  · rw [zeroMean_theta c (reconstructState g c u) hm']
    intro n R s hs Y k
    exact congrArg₂ (· - ·)
      (congrArg₂ (· + ·)
        (InitialRegularity.periodic_radialDiv U.isOpen c.operators hop.radius_eq hprofile (hWp 0 1)
          2 n R s hs Y k)
        (InitialRegularity.periodic_dz U.isOpen c.operators (hWp 2 1) n R s hs Y k))
      (InitialRegularity.periodic_radialDiv U.isOpen c.operators hop.radius_eq hprofile hθp 2 n R s
        hs Y k)
  · rw [zeroMean_axial c (reconstructState g c u) hm']
    intro n R s hs Y k
    exact congrArg₂ (· - ·)
      (congrArg₂ (· + ·)
        (InitialRegularity.periodic_radialDiv U.isOpen c.operators hop.radius_eq hprofile (hWp 0 2)
          1 n R s hs Y k)
        (InitialRegularity.periodic_dz U.isOpen c.operators hsum n R s hs Y k))
      (InitialRegularity.periodic_radialDiv U.isOpen c.operators hop.radius_eq hprofile hzp 1 n R s
        hs Y k)

end RawRegularity

section TemporalBounds

variable {coord cL cR : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)

include hd hell in
/-- The first temporal increment is bounded by applying the actual moving
torus inverse and stream to the residual of the constructed primary state. -/
theorem zeroMean_temporal_increment_bounds
    {h : ℝ} (hh : 0 ≤ h) (hscale : ∀ n, ChartScales.S n ≤ L n)
    (index : ℕ → ℕ) (D : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point)
    (ho : OperatorBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
      hεone hL)
      c.operators ChartScales.kappa)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hprofile : ∀ R s, s ∈ U.carrier → ∀ Y,
      c.operators.radialProfile (R, (s, Y)) = c.operators.radialProfile (R, (s, 0)))
    (hm : u.mean = ⟨0, 0, 0⟩)
    (hW : ∀ i j, MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
      hεone hL)
      1 (u.covariance i j))
    (hWc : ∀ i j n, ContDiffOn ℝ ∞ (u.covariance i j n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hWp : ∀ i j n, PhysicalMeanDomain.PeriodicOn U.carrier (u.covariance i j n))
    (hWs : ∀ i j n, SupportedGauge g.radial.inner g.radial.outer (qLength coord)
      U.carrier (u.covariance i j n))
    (hθ : MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone
      hL)
      1 c.virtualTheta)
    (hz : MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone
      hL)
      1 c.virtualAxial)
    (hθc : ∀ n, ContDiffOn ℝ ∞ (c.virtualTheta n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hzc : ∀ n, ContDiffOn ℝ ∞ (c.virtualAxial n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hθp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (c.virtualTheta n))
    (hzp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (c.virtualAxial n))
    (hθs : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      (c.virtualTheta n))
    (hzs : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
      (c.virtualAxial n)) :
    IncrementBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone
      hL)
      (1 - ChartScales.kappa) (temporalIncrementState g h index axial c (reconstructState g c u))
        := by
  obtain ⟨_, _, hcθ, hcz, _⟩ := zeroMean_reconstructed_bounds U g ha hd hcL hcR ε L hε hεone hL
    hell c u ho hop hm hW hWc hWs hθ hz
  obtain ⟨hscθ, hscz⟩ := zeroMean_raw_smooth U g ha hd hell c u hop hm hWc hWs hθc hzc hθs hzs
  obtain ⟨hspθ, hspz⟩ := zeroMean_raw_periodic U g hell c u hop hprofile hm hWp hθp hzp
  obtain ⟨_, hssz⟩ := zeroMean_raw_supported U g ha hd hell c u hop hm hWc hWs hθs hzs
  obtain ⟨hβ, hϑ, hγ⟩ := temporalIncrementState_classes U g ha hd hcL hcR ε L hε hεone hL hell
    hh hscale index D hgap axial c (reconstructState g c u) ho.epsilon_eq
    hscθ hscz hspθ hspz hssz hcθ hcz
  exact ⟨hβ, hϑ, hγ⟩

end TemporalBounds

end MovingInitialization


namespace MovingInitialization

open Set Filter CorrectionState WeightedClasses MeanIncrementBounds VariableGaugeMean
  LocalSignedRequest
open scoped ContDiff Topology

section DebtAfterMean

variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

include hab in
/-- The measured debt after a mean update is controlled by actual source
and flux bounds. Its smoothness and support follow from the primitive mean
and covariance fields. -/
theorem state_debt_mem (c : Context Point) (u : State Point) {H : ℝ} (hH : 0 ≤ H)
    (ho : OperatorBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      c.operators ChartScales.kappa)
    (hb : BaseBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) c.base)
    (hm : IncrementBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H u.mean)
    (hgr : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H (u.gr c))
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbc : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hmc : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : CorrectionStep.GaugeSupportedTriple a b (qLength coord) U.carrier u.mean)
    (hW : ∀ i j, MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL)
      H (u.covariance i j))
    (hWc : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, CorrectionStep.GaugeSupported a b (qLength coord) U.carrier (u.covariance i j))
    (i : Fin 3) :
    UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL)
      H (fun n x => debt c u n x i) := by
  have hθ : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H
      (thetaAxial c.base u.mean + u.covariance 2 1) := by
    have h1 := (Class.coefficient_mul hb.axial hm.angular).mono_exponent (by linarith : H ≤ 0 + H)
    have h2 := (Class.coefficient_mul hb.angular hm.axial).mono_exponent (by linarith : H ≤ 0 + H)
    have h3 := (Class.product hm.axial hm.angular ho.weight_le_one).mono_exponent (by linarith : H
      ≤ H + H)
    exact ((h1.add h2).add h3).add (hW 2 1)
  have hz : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H
      (axialAxial c.base u.mean + u.covariance 2 2) := by
    have h1 := (Class.coefficient_mul hb.axial hm.axial).mono_exponent (by linarith : H ≤ 0 + H)
    have h2 := (Class.product hm.axial hm.axial ho.weight_le_one).mono_exponent (by linarith : H ≤
      H + H)
    exact ((Class.smul h1 2).add h2).add (hW 2 2)
  obtain ⟨hgc, hgs⟩ := CorrectionStep.state_gr_moving_regular U ha hab c u hop hbc hmc hms hWc hWs
  obtain ⟨a₀, b₀, L₀, ha₀, _, _, _, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  have hfixed {f : ScalarField Point}
      (hs : CorrectionStep.GaugeSupported a b (qLength coord) U.carrier f) :
      ∀ n, PhysicalMeanDomain.SupportedOn a₀ b₀ U.carrier (f n) := by
    intro n x hx hn
    exact ⟨(hleft _ hx).trans (hs n x hx hn).1, (hs n x hx hn).2.trans (hright _ hx)⟩
  have hml : LocalRankDefect.LocalTriple a₀ b₀ U.carrier u.mean :=
    ⟨⟨hmc.radial, hfixed hms.radial⟩, ⟨hmc.angular, hfixed hms.angular⟩,
      ⟨hmc.axial, hfixed hms.axial⟩⟩
  have hwl (i j : Fin 3) : LocalRankDefect.LocalShell a₀ b₀ U.carrier (u.covariance i j) :=
    ⟨hWc i j, hfixed (hWs i j)⟩
  have hθc := ((LocalRankDefect.thetaAxial_localShell ha₀ U.isOpen hbc hml).add (hwl 2 1)).smooth
  have hzc := ((LocalRankDefect.axialAxial_localShell ha₀ U.isOpen hbc hml).add (hwl 2 2)).smooth
  have hθs : CorrectionStep.GaugeSupported a b (qLength coord) U.carrier
      (thetaAxial c.base u.mean + u.covariance 2 1) :=
    (((hms.angular.mul_left c.base.axial).add (hms.axial.mul_left c.base.angular)).add
      (hms.axial.mul_right u.mean.angular)).add (hWs 2 1)
  have hzs : CorrectionStep.GaugeSupported a b (qLength coord) U.carrier
      (axialAxial c.base u.mean + u.covariance 2 2) :=
    (((hms.axial.mul_left c.base.axial).smul 2).add (hms.axial.mul_right u.mean.axial)).add (hWs 2
      2)
  have hP := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hgc hgs hgr 0
  have hP2 := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hgc hgs hgr 2
  have hJθ := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hθc hθs hθ 2
  have hJz := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hzc hzs hz 1
  fin_cases i
  · exact hP
  · exact hJθ
  · exact Class.sub hJz (Class.smul hP2 (1 / 2))

end DebtAfterMean

section TemporalSource

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The literal source of the updated state, including the leading radial
term. No source estimate for the output state is an input. -/
theorem temporal_gr_mem {s : StripData (PressureStream.Lift D)}
    (g : GaugeData D) (h : ℝ) (index : ℕ → ℕ) (axial : D × PressureStream.Plane)
    (c : Context (PressureStream.Lift D)) (u : State (PressureStream.Lift D)) {H κ : ℝ}
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hm : MeanIncrementBounds.CumulativeBounds s u.mean)
    (hi : IncrementBounds s H (temporalIncrementState g h index axial c u))
    (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)
    (hW : ∀ i j, SmoothOn s.domain (u.covariance i j))
    (hgr : MeanClass s H (u.gr c)) :
    MeanClass s H ((temporalStageState g h index axial c u).gr c) := by
  have hdelta := gr_change_mem ho hb hm hi hH u.covariance hW hκ
  have hnew : (temporalStageState g h index axial c u).gr c =
      MeanIncrementBounds.gr c.operators c.base
        (updated u.mean (temporalIncrementState g h index axial c u)) u.covariance := by
    change MeanIncrementBounds.gr c.operators c.base _ _ = _
    rw [CorrectionStep.gaugeTemporalStage_covariance]
    rfl
  apply class_congr (hgr.add hdelta)
  intro n x hx
  rw [hnew]
  change _ = u.gr c n x + (_ - u.gr c n x)
  ring

end TemporalSource

section InitialRank

variable {coord A B cL cR : ℝ} (U : SlowRegion coord)
    (g : GaugeData PressureStream.Plane) (r : RankData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

/-- The first rank correction is obtained from the measured debt of the
actual temporal stage. Its velocity bound is derived through the five-row
inverse and the moving-support stream estimate. -/
theorem temporal_rank_increment_bounds
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point) {H : ℝ} (hH : 9 / 10 ≤ H)
    (ho : OperatorBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
      hεone hL)
      c.operators ChartScales.kappa)
    (hb : BaseBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone
      hL) c.base)
    (hm : u.mean = ⟨0, 0, 0⟩)
    (hi : IncrementBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
      hεone hL)
      H (temporalIncrementState g h index axial c u))
    (hgr : MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone
      hL)
      H (u.gr c))
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbc : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hic : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier)
      (temporalIncrementState g h index axial c u))
    (his : CorrectionStep.GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord)
      U.carrier
      (temporalIncrementState g h index axial c u))
    (hW : ∀ i j, MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
      hεone hL)
      H (u.covariance i j))
    (hWc : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, CorrectionStep.GaugeSupported g.radial.inner g.radial.outer (qLength coord)
      U.carrier (u.covariance i j))
    (hg : LocalRankDefect.RankGeometry g r U.carrier c (temporalStageState g h index axial c u))
    (hparam : RankStateBounds.NormalizedParameters coord A B r U.carrier) (hB : B ≠ 0)
    (hleft : g.radial.inner < r.inner) (hright : r.outer < g.radial.outer) :
    IncrementBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone
      hL)
      H (rankIncrementState g r axial c (temporalStageState g h index axial c u)) := by
  let st := movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL
  let v := temporalStageState g h index axial c u
  have hmean : v.mean = temporalIncrementState g h index axial c u := by
    change updated u.mean (temporalIncrementState g h index axial c u) = _
    rw [hm]
    simp only [updated, zero_add]
  have hcov : v.covariance = u.covariance := CorrectionStep.gaugeTemporalStage_covariance g h index
    axial c u
  have hm0 : MeanIncrementBounds.CumulativeBounds st u.mean := by
    rw [hm]
    exact ⟨MemClass.zero (fun _ => st.zeta_nonneg), MemClass.zero (fun _ => st.zeta_nonneg),
      MemClass.zero (fun _ => st.zeta_nonneg)⟩
  have hgv := temporal_gr_mem g h index axial c u ho hb hm0 hi hH
    (by norm_num [ChartScales.kappa]) (fun i j => (hW i j).smooth) hgr
  have hdebt := state_debt_mem U ha g.radial.inner_lt_outer hcL hcR ε L hε hεone hL
    c v (by linarith : 0 ≤ H) ho hb (by simpa only [hmean] using hi) hgv hop hbc
    (by simpa only [hmean] using hic) (by simpa only [hmean] using his)
    (by simpa only [hcov] using hW) (by simpa only [hcov] using hWc)
    (by simpa only [hcov] using hWs)
  have heps : BandBound st 1 c.operators.epsilon := by
    rw [ho.epsilon_eq]
    simpa only [Real.rpow_one] using bandBound_rpow st 1
  exact RankStateBounds.rankIncrementState_bounds_of_components U g r ha hcL hcR ε L hε hεone hL
    c v hg hparam hB hleft hright axial heps hdebt

end InitialRank

end MovingInitialization

namespace MovingInitialization

open Set Filter CorrectionState WeightedClasses MeanIncrementBounds VariableGaugeMean
  LocalSignedRequest
open scoped ContDiff Topology

section PrimaryMeanData

variable {coord cL cR : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

local notation "st" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL

/-- Data of the base, actual primary covariance, and virtual stress. No
bound on the pressure, residual, temporal increment, or rank output is a field. -/
structure PrimaryMeanData (c : Context Point) (u : State Point) : Prop where
  exponent_pos : 0 < g.radial.exponent
  gauge_length : ∀ n, g.length n = qLength coord
  operators : OperatorBounds st c.operators ChartScales.kappa
  base : BaseBounds st c.base
  localOperators : LocalRankDefect.LocalOperators U.carrier c.operators
  base_smooth : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base
  profile : ∀ R s, s ∈ U.carrier → ∀ Y,
    c.operators.radialProfile (R, (s, Y)) = c.operators.radialProfile (R, (s, 0))
  mean_zero : u.mean = ⟨0, 0, 0⟩
  covariance : ∀ i j, MeanClass st 1 (u.covariance i j)
  covariance_smooth : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j)
  covariance_periodic : ∀ i j n, PhysicalMeanDomain.PeriodicOn U.carrier (u.covariance i j n)
  covariance_support : ∀ i j, CorrectionStep.GaugeSupported g.radial.inner g.radial.outer
    (qLength coord) U.carrier (u.covariance i j)
  theta : MeanClass st 1 c.virtualTheta
  axial : MeanClass st 1 c.virtualAxial
  theta_smooth : SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) c.virtualTheta
  axial_smooth : SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) c.virtualAxial
  theta_periodic : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (c.virtualTheta n)
  axial_periodic : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (c.virtualAxial n)
  theta_support : CorrectionStep.GaugeSupported g.radial.inner g.radial.outer (qLength coord)
    U.carrier c.virtualTheta
  axial_support : CorrectionStep.GaugeSupported g.radial.inner g.radial.outer (qLength coord)
    U.carrier c.virtualAxial

/-- All fields are properties of the literal first temporal stage. -/
structure TemporalStateBounds (h : ℝ) (index : ℕ → ℕ)
    (axial : PressureStream.Plane × PressureStream.Plane) (c : Context Point) (u : State Point) :
      Prop where
  increment : IncrementBounds st (1 - ChartScales.kappa)
    (temporalIncrementState g h index axial c (reconstructState g c u))
  increment_smooth : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier)
    (temporalIncrementState g h index axial c (reconstructState g c u))
  increment_support : CorrectionStep.GaugeSupportedTriple g.radial.inner g.radial.outer
    (qLength coord) U.carrier (temporalIncrementState g h index axial c (reconstructState g c u))
  pressure_change : MeanClass st (1 - ChartScales.kappa)
    (CorrectionStep.gaugeTemporalPressureChange g h index axial c (reconstructState g c u))
  cumulative : CorrectionState.CumulativeBounds st (temporalStageState g h index axial c
    (reconstructState g c u))
  theta : MeanClass st (149 / 100) ((temporalStageState g h index axial c (reconstructState g c
    u)).thetaResidual c)
  axial : MeanClass st (149 / 100) (fun n x =>
    (temporalStageState g h index axial c (reconstructState g c u)).axialResidual c n x -
      temporalAliasState g h index c (reconstructState g c u) n (x, 0) 2)

namespace PrimaryMeanData

variable {U g ha hcL hcR ε L hε hεone hL} {c : Context Point} {u : State Point}
    (d : PrimaryMeanData U g ha hcL hcR ε L hε hεone hL c u)

include d

theorem temporal_bounds {h : ℝ} (hh : 0 ≤ h) (hscale : ∀ n, ChartScales.S n ≤ L n)
    (index : ℕ → ℕ) (D : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (axial : PressureStream.Plane × PressureStream.Plane)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n = ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 +
      h))
    (hθmatch : MeanClass st (3 / 2 - ChartScales.kappa)
      (StateMomentBalances.meanBar (u.covariance 0 1) - StateMomentBalances.meanBar c.virtualTheta))
    (hzmatch : MeanClass st (3 / 2 - ChartScales.kappa)
      (StateMomentBalances.meanBar (u.covariance 0 2) - StateMomentBalances.meanBar
        c.virtualAxial)) :
    TemporalStateBounds U g ha hcL hcR ε L hε hεone hL h index axial c u := by
  let p := reconstructState g c u
  have hpm : p.mean = ⟨0, 0, 0⟩ := d.mean_zero
  obtain ⟨hgr, hp, hθ, hz, hcum⟩ := zeroMean_reconstructed_bounds U g ha d.exponent_pos
    hcL hcR ε L hε hεone hL d.gauge_length c u d.operators d.localOperators d.mean_zero
    d.covariance d.covariance_smooth d.covariance_support d.theta d.axial
  obtain ⟨hθc, hzc⟩ := zeroMean_raw_smooth U g ha d.exponent_pos d.gauge_length c u
    d.localOperators d.mean_zero d.covariance_smooth d.covariance_support
    d.theta_smooth d.axial_smooth d.theta_support d.axial_support
  obtain ⟨hθp, hzp⟩ := zeroMean_raw_periodic U g d.gauge_length c u d.localOperators d.profile
    d.mean_zero d.covariance_periodic d.theta_periodic d.axial_periodic
  obtain ⟨hθs, hzs⟩ := zeroMean_raw_supported U g ha d.exponent_pos d.gauge_length c u
    d.localOperators d.mean_zero d.covariance_smooth d.covariance_support d.theta_support
      d.axial_support
  have hi := zeroMean_temporal_increment_bounds U g ha d.exponent_pos hcL hcR ε L hε hεone hL
    d.gauge_length hh hscale index D hgap axial c u d.operators d.localOperators d.profile
      d.mean_zero
    d.covariance d.covariance_smooth d.covariance_periodic d.covariance_support d.theta d.axial
    d.theta_smooth d.axial_smooth d.theta_periodic d.axial_periodic d.theta_support d.axial_support
  have hic := CorrectionStep.gaugeTemporalIncrement_smooth U g ha d.exponent_pos d.gauge_length
    h index axial c p hθc hzc hθp hzp hzs
  have his : CorrectionStep.GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord)
    U.carrier
      (temporalIncrementState g h index axial c p) := by
    have hs := temporalIncrementState_supportedGauge U g ha d.exponent_pos d.gauge_length c p h
      index axial
    exact ⟨fun n => (hs n (hzc n) (hzp n) (hzs n) (hθs n)).1,
      fun n => (hs n (hzc n) (hzp n) (hzs n) (hθs n)).2.1,
      fun n => (hs n (hzc n) (hzp n) (hzs n) (hθs n)).2.2⟩
  have hmc : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) p.mean := by
    rw [hpm]
    exact ⟨fun _ => contDiffOn_const, fun _ => contDiffOn_const, fun _ => contDiffOn_const⟩
  have hms : CorrectionStep.GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord)
    U.carrier p.mean := by
    rw [hpm]
    exact ⟨CorrectionStep.GaugeSupported.zero, CorrectionStep.GaugeSupported.zero,
      CorrectionStep.GaugeSupported.zero⟩
  have hpc := (zeroMean_pressure_regular U g ha d.exponent_pos d.gauge_length c u
    d.localOperators d.mean_zero d.covariance_smooth d.covariance_support).1
  have hpp := zeroMean_pressure_periodic U g d.gauge_length c u d.localOperators d.profile
    d.mean_zero d.covariance_periodic
  have hdp := CorrectionStep.gaugeTemporalStage_pressure_change_mem U g ha d.exponent_pos
    hcL hcR ε L hε hεone hL d.gauge_length h index axial c p rfl
    (by norm_num [ChartScales.kappa] : (9 / 10 : ℝ) ≤ 1 - ChartScales.kappa)
    (by norm_num [ChartScales.kappa]) d.operators d.base hcum hi d.localOperators d.base_smooth
    hmc hic hms his d.covariance_smooth d.covariance_support
  obtain ⟨hbθ, hbz⟩ := zeroMean_bar_bounds U ha hcL hcR ε L hε hεone hL c p d.operators
    d.localOperators.radius_eq d.profile hpm d.covariance d.covariance_smooth d.covariance_periodic
    hp hpc hpp d.theta_smooth d.theta_periodic d.axial_smooth d.axial_periodic hθmatch hzmatch
  have hres := CorrectionStep.gaugeTemporalStage_mean_gain U.isOpen
    (fun x hx => ((movingStrip_domain U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone
      hL x).mp hx).1)
    g h index axial c p hv hfast d.operators d.base hcum hi hdp
    (fun i j => (d.covariance i j).smooth) hbθ hbz hθc hzc hθp hzp
    (by norm_num [ChartScales.kappa]) (by norm_num [ChartScales.kappa])
  exact ⟨hi, hic, his, hdp,
    CorrectionStep.gaugeTemporalStage_cumulative g h index axial c p hcum hi hdp (by norm_num
      [ChartScales.kappa]),
    hres.1, hres.2⟩

end PrimaryMeanData

end PrimaryMeanData


end MovingInitialization

namespace MovingInitialization

open Set Filter CorrectionState WeightedClasses MeanIncrementBounds VariableGaugeMean
  LocalSignedRequest
open scoped ContDiff Topology

section RankComposition

variable {coord cL cR : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

local notation "st" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL
local notation "slowSt" => PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL

/-- The estimates refer to the actual rank inverse and recomputed pressure.
The defect estimate is obtained after the five-row cancellation. -/
structure InitialRankBounds (r : RankData PressureStream.Plane) (h : ℝ) (index : ℕ → ℕ)
    (axial : PressureStream.Plane × PressureStream.Plane) (c : Context Point) (u : State Point) :
      Prop where
  increment : IncrementBounds st (1 - ChartScales.kappa)
    (rankIncrementState g r axial c (temporalStageState g h index axial c (reconstructState g c u)))
  pressure_change : MeanClass st (1 - ChartScales.kappa)
    (CorrectionStep.gaugeRankPressureChange g r axial c (temporalStageState g h index axial c
      (reconstructState g c u)))
  cumulative : CorrectionState.CumulativeBounds st
    (rankStageState g r axial c (temporalStageState g h index axial c (reconstructState g c u)))
  mean_smooth : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier)
    (rankStageState g r axial c (temporalStageState g h index axial c (reconstructState g c
      u))).mean
  mean_support : CorrectionStep.GaugeSupportedTriple g.radial.inner g.radial.outer
    (qLength coord) U.carrier
    (rankStageState g r axial c (temporalStageState g h index axial c (reconstructState g c
      u))).mean
  theta : MeanClass st (149 / 100)
    ((rankStageState g r axial c (temporalStageState g h index axial c (reconstructState g c
      u))).thetaResidual c)
  axial_residual : MeanClass st (149 / 100) (fun n x =>
    (rankStageState g r axial c (temporalStageState g h index axial c (reconstructState g c
      u))).axialResidual c n x -
      temporalAliasState g h index c (reconstructState g c u) n (x, 0) 2)
  defects : DefectBounds slowSt (1 / 5) c
    (rankStageState g r axial c (temporalStageState g h index axial c (reconstructState g c u)))

namespace PrimaryMeanData

variable {U g ha hcL hcR ε L hε hεone hL} {c : Context Point} {u : State Point}
    (d : PrimaryMeanData U g ha hcL hcR ε L hε hεone hL c u)
    {h : ℝ} {index : ℕ → ℕ} {axial : PressureStream.Plane × PressureStream.Plane}
    (t : TemporalStateBounds U g ha hcL hcR ε L hε hεone hL h index axial c u)

include d t

theorem temporal_debt_bounds :
    UnweightedClass slowSt (1 - ChartScales.kappa)
      (debt c (temporalStageState g h index axial c (reconstructState g c u))) := by
  let p := reconstructState g c u
  let v := temporalStageState g h index axial c p
  have hmean : v.mean = temporalIncrementState g h index axial c p := by
    change updated u.mean _ = _
    rw [d.mean_zero]
    simp only [updated, zero_add]
  have hcov : v.covariance = u.covariance := CorrectionStep.gaugeTemporalStage_covariance g h index
    axial c p
  obtain ⟨hgr, _, _, _, hcum⟩ := zeroMean_reconstructed_bounds U g ha d.exponent_pos
    hcL hcR ε L hε hεone hL d.gauge_length c u d.operators d.localOperators d.mean_zero
    d.covariance d.covariance_smooth d.covariance_support d.theta d.axial
  have hgv := temporal_gr_mem g h index axial c p d.operators d.base hcum.velocity t.increment
    (by norm_num [ChartScales.kappa]) (by norm_num [ChartScales.kappa])
    (fun i j => (d.covariance i j).smooth) hgr
  apply RankStateBounds.debtClass_of_components
  exact state_debt_mem U ha g.radial.inner_lt_outer hcL hcR ε L hε hεone hL c v
    (by norm_num [ChartScales.kappa]) d.operators d.base
    (by simpa only [hmean] using t.increment) hgv d.localOperators d.base_smooth
    (by simpa only [hmean] using t.increment_smooth)
    (by simpa only [hmean] using t.increment_support)
    (fun i j => by rw [hcov]; exact (d.covariance i j).mono_exponent (by norm_num
      [ChartScales.kappa]))
    (by simpa only [hcov] using d.covariance_smooth)
    (by simpa only [hcov] using d.covariance_support)

theorem rank_bounds (r : RankData PressureStream.Plane) {A B : ℝ}
    (hg : LocalRankDefect.RankGeometry g r U.carrier c
      (temporalStageState g h index axial c (reconstructState g c u)))
    (hparam : RankStateBounds.NormalizedParameters coord A B r U.carrier) (hB : B ≠ 0)
    (hleft : g.radial.inner < r.inner) (hright : r.outer < g.radial.outer)
    (hfast : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hV : LocalRankDefect.IsSlowOn U.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn U.carrier c.base.axial) :
    InitialRankBounds U g ha hcL hcR ε L hε hεone hL r h index axial c u := by
  let p := reconstructState g c u
  let v := temporalStageState g h index axial c p
  have hmean : v.mean = temporalIncrementState g h index axial c p := by
    change updated u.mean _ = _
    rw [d.mean_zero]
    simp only [updated, zero_add]
  have hmc : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) v.mean := by
    simpa only [hmean] using t.increment_smooth
  have hms : CorrectionStep.GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord)
    U.carrier v.mean := by
    simpa only [hmean] using t.increment_support
  have hcov : v.covariance = u.covariance := CorrectionStep.gaugeTemporalStage_covariance g h index
    axial c p
  have hWc : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (v.covariance i j) := by
    simpa only [hcov] using d.covariance_smooth
  have hWs : ∀ i j, CorrectionStep.GaugeSupported g.radial.inner g.radial.outer (qLength coord)
    U.carrier (v.covariance i j) := by
    simpa only [hcov] using d.covariance_support
  obtain ⟨hi, hp, hc, hmc', hms', hθ, hz⟩ := CorrectionStep.gaugeRankStage_constructed U g r ha
    d.exponent_pos
    hcL hcR ε L hε hεone hL d.gauge_length axial c v hg hparam hB hleft hright
    (by norm_num [ChartScales.kappa] : (9 / 10 : ℝ) ≤ 1 - ChartScales.kappa)
    (by norm_num [ChartScales.kappa]) (by norm_num [ChartScales.kappa]) hfast rfl
    d.operators d.base t.cumulative d.localOperators d.base_smooth hmc hms hWc hWs
    (d.temporal_debt_bounds t) (fun n x => temporalAliasState g h index c p n (x, 0) 2)
    t.theta t.axial
  have hdef := MovingMomentBounds.rankStage_defectBounds U g r ha hcL hcR ε L hε hεone hL
    d.gauge_length axial c v hg d.localOperators d.base_smooth hmc
    ⟨hms.radial, hms.angular, hms.axial⟩ hWc hWs hV hG d.operators d.base t.cumulative.velocity hi
    (by norm_num [ChartScales.kappa])
    (by norm_num [ChartScales.kappa] : (1 : ℝ) + 1 / 5 ≤ (1 - ChartScales.kappa) + 9 / 10 - 2 *
      ChartScales.kappa)
  exact ⟨hi, hp, hc, hmc', hms', hθ, hz, hdef⟩

omit t in
theorem temporal_zeroMasses :
    GaugeMassPreservation.ZeroMassesOn U.carrier
      (temporalStageState g h index axial c (reconstructState g c u)) := by
  let p := reconstructState g c u
  have hpm : p.mean = ⟨0, 0, 0⟩ := d.mean_zero
  obtain ⟨hθc, hzc⟩ := zeroMean_raw_smooth U g ha d.exponent_pos d.gauge_length c u
    d.localOperators d.mean_zero d.covariance_smooth d.covariance_support
    d.theta_smooth d.axial_smooth d.theta_support d.axial_support
  obtain ⟨hθp, hzp⟩ := zeroMean_raw_periodic U g d.gauge_length c u d.localOperators d.profile
    d.mean_zero d.covariance_periodic d.theta_periodic d.axial_periodic
  obtain ⟨_, hzs⟩ := zeroMean_raw_supported U g ha d.exponent_pos d.gauge_length c u
    d.localOperators d.mean_zero d.covariance_smooth d.covariance_support d.theta_support
      d.axial_support
  have hcont : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) p.mean := by
    rw [hpm]
    exact ⟨fun _ => contDiffOn_const, fun _ => contDiffOn_const, fun _ => contDiffOn_const⟩
  apply GaugeMassPreservation.temporalStage_zeroMassesOn U g ha d.exponent_pos d.gauge_length
    h index axial c p (fun n => (hcont.angular n).continuousOn) (fun n => (hcont.axial
      n).continuousOn)
    hθc hzc hθp hzp hzs
  intro n x hx
  change radialMoment 2 p.mean.angular n x = 0 ∧ radialMoment 1 p.mean.axial n x = 0
  rw [hpm]
  simp [radialMoment, PressureStream.pressureMass, PressureStream.torusAverage,
    PressureStream.torusInner]

theorem rank_zeroMasses (r : RankData PressureStream.Plane)
    (hg : LocalRankDefect.RankGeometry g r U.carrier c
      (temporalStageState g h index axial c (reconstructState g c u))) :
    GaugeMassPreservation.ZeroMassesOn U.carrier
      (rankStageState g r axial c (temporalStageState g h index axial c (reconstructState g c u)))
        := by
  let p := reconstructState g c u
  let v := temporalStageState g h index axial c p
  have hmean : v.mean = temporalIncrementState g h index axial c p := by
    change updated u.mean _ = _
    rw [d.mean_zero]
    simp only [updated, zero_add]
  obtain ⟨a₀, b₀, R₀, ha₀, hab₀, _, _, hleft, hright, _⟩ :=
    qLength_reference_bounds U ha g.radial.inner_lt_outer
  have hl (n : ℕ) (x : PressureStream.Plane) (hx : x ∈ U.carrier) : a₀ ≤ r.length n x * r.inner :=
    by
    have hh := hg.gauge_left n x hx
    rw [d.gauge_length n] at hh
    exact (hleft x hx).trans hh
  have hr (n : ℕ) (x : PressureStream.Plane) (hx : x ∈ U.carrier) : r.length n x * r.outer ≤ b₀ :=
    by
    have hh := hg.gauge_right n x hx
    rw [d.gauge_length n] at hh
    exact hh.trans (hright x hx)
  have hfixed {f : ScalarField Point}
      (hs : CorrectionStep.GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier
        f) :
      ∀ n, PhysicalMeanDomain.SupportedOn a₀ b₀ U.carrier (f n) := by
    intro n x hx hn
    exact ⟨(hleft _ hx).trans (hs n x hx hn).1, (hs n x hx hn).2.trans (hright _ hx)⟩
  have hml : LocalRankDefect.LocalTriple a₀ b₀ U.carrier v.mean := by
    rw [hmean]
    exact ⟨⟨t.increment_smooth.radial, hfixed t.increment_support.radial⟩,
      ⟨t.increment_smooth.angular, hfixed t.increment_support.angular⟩,
      ⟨t.increment_smooth.axial, hfixed t.increment_support.axial⟩⟩
  intro n x hx
  have he := hg.preserve_masses ha₀ hab₀ U.isOpen hl hr axial hml n hx
  have hz := d.temporal_zeroMasses (h := h) (index := index) (axial := axial) n x hx
  exact ⟨he.1.trans hz.1, he.2.trans hz.2⟩

end PrimaryMeanData

end RankComposition

section InitialMeanConclusion

variable {coord cL cR : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (r : RankData PressureStream.Plane) (ha : 0 < g.radial.inner) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    {ι : Type} (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (Point × ℝ))
    (baseError : Oscillation Point) (c : Context Point)
    (d : PrimaryMeanData U g ha hcL hcR ε L hε hεone hL c (bandSeed labels pieces baseError))

local notation "st" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL
local notation "slowSt" => PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL

include d in
/-- The actual pressure, temporal, rank, and alias-retention stages meet
all mean and defect bounds at sigma=1/5, from primitive primary mean data. -/
theorem initializedBands_mean_defects {h A B : ℝ} (hh : 0 ≤ h)
    (hscale : ∀ n, ChartScales.S n ≤ L n) (index : ℕ → ℕ) (D : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (axial : PressureStream.Plane × PressureStream.Plane)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n = ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 +
      h))
    (hθmatch : MeanClass st (3 / 2 - ChartScales.kappa)
      (StateMomentBalances.meanBar ((bandSeed labels pieces baseError).covariance 0 1) -
        StateMomentBalances.meanBar c.virtualTheta))
    (hzmatch : MeanClass st (3 / 2 - ChartScales.kappa)
      (StateMomentBalances.meanBar ((bandSeed labels pieces baseError).covariance 0 2) -
        StateMomentBalances.meanBar c.virtualAxial))
    (hrank : LocalRankDefect.RankGeometry g r U.carrier c
      (GaugeInitialization.temporalBands g h index axial c labels pieces baseError))
    (hparam : RankStateBounds.NormalizedParameters coord A B r U.carrier) (hB : B ≠ 0)
    (hleft : g.radial.inner < r.inner) (hright : r.outer < g.radial.outer)
    (hV : LocalRankDefect.IsSlowOn U.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn U.carrier c.base.axial)
    (hb : CorrectionStep.AngularContinuous baseError)
    (hg : ∀ n l, l ∈ labels n → ∀ x i, Continuous (fun θ : ℝ => (pieces l).excluded n (x, θ) i))
    (hz : ∀ n l, l ∈ labels n → ∀ x, CorrectionStep.angularMeanVector (pieces l).excluded n x = 0) :
    CorrectionState.CumulativeBounds st (GaugeInitialization.initializedBands g r h index axial c
      labels pieces baseError) ∧
    MeanResidualBounds st (1 / 5) c (GaugeInitialization.initializedBands g r h index axial c
      labels pieces baseError) ∧
    DefectBounds slowSt (1 / 5) c (GaugeInitialization.initializedBands g r h index axial c labels
      pieces baseError) ∧
    GaugeMassPreservation.ZeroMassesOn U.carrier (GaugeInitialization.initializedBands g r h index
      axial c labels pieces baseError) := by
  have ht := d.temporal_bounds hh hscale index D hgap axial hv hfast hθmatch hzmatch
  have hr := d.rank_bounds ht r hrank hparam hB hleft hright hv hV hG
  have hmean := GaugeInitialization.initializedBands_meanResidualBounds g r h index axial c labels
    pieces baseError
    hb hg hz (hr.theta.mono_exponent (by norm_num : (1 : ℝ) + 1 / 5 ≤ 149 / 100))
    (hr.axial_residual.mono_exponent (by norm_num : (1 : ℝ) + 1 / 5 ≤ 149 / 100))
  exact ⟨⟨hr.cumulative.velocity, hr.cumulative.pressure⟩, hmean, hr.defects, d.rank_zeroMasses ht
    r hrank⟩

end InitialMeanConclusion

end MovingInitialization

namespace CommonWindow

open Set Function

noncomputable def levels (n : ℕ) : Finset ℕ :=
  insert n (Finset.Icc (max 1 (n - 2)) (n + 2))

theorem self_mem (n : ℕ) : n ∈ levels n := Finset.mem_insert_self _ _

theorem levels_nonempty (n : ℕ) : (levels n).Nonempty := ⟨n, self_mem n⟩

theorem distance {n m : ℕ} (hm : m ∈ levels n) : n ≤ m + 4 ∧ m ≤ n + 4 := by
  rcases Finset.mem_insert.mp hm with rfl | hm
  · omega
  · have he := Finset.mem_Icc.mp hm
    omega

theorem positive {n m : ℕ} (hn : 1 ≤ n) (hm : m ∈ levels n) : 1 ≤ m := by
  rcases Finset.mem_insert.mp hm with rfl | hm
  · exact hn
  · exact (le_max_left _ _).trans (Finset.mem_Icc.mp hm).1

noncomputable def index (h : ℝ) (n : ℕ) : ℕ :=
  ((levels n).image (ChartScales.nativeIndex h)).min' ((levels_nonempty n).image _)

theorem index_le {h : ℝ} {n m : ℕ} (hm : m ∈ levels n) : index h n ≤ ChartScales.nativeIndex h m :=
  by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)

theorem index_le_native (h : ℝ) (n : ℕ) : index h n ≤ ChartScales.nativeIndex h n :=
  index_le (self_mem n)

noncomputable def gap (h : ℝ) : ℕ := SlotColoring.nativeGap h + ChartScales.nativeIndex h 0

theorem native_le_index_add (h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    ChartScales.nativeIndex h n ≤ index h n + gap h := by
  by_cases hn : 1 ≤ n
  · obtain ⟨m, hm, he⟩ := Finset.mem_image.mp
      (Finset.min'_mem ((levels n).image (ChartScales.nativeIndex h)) ((levels_nonempty n).image _))
    have hd := distance hm
    have hg := (SlotColoring.nativeIndex_gap h hh hn (positive hn hm) hd.1 hd.2).1
    change ChartScales.nativeIndex h m = index h n at he
    change ChartScales.nativeIndex h n ≤ ChartScales.nativeIndex h m + SlotColoring.nativeGap h at
      hg
    rw [he] at hg
    exact hg.trans (Nat.add_le_add_left (Nat.le_add_right _ _) _)
  · have hn0 : n = 0 := by omega
    subst n
    dsimp [gap]
    omega

theorem gap_le (h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    ChartScales.nativeIndex h n - index h n ≤ gap h := by
  have hn := native_le_index_add h hh n
  omega

/-- The same finite level window contains every actual closed dyadic
support meeting the standard chart range. Endpoints are retained. -/
theorem active_level_mem {D q : ℝ} {n : ℕ} {L : SlotColoring.Label}
    (hq : 0 < q) (hlo : ChartScales.Q n / 2 ≤ q) (hhi : q ≤ 2 * ChartScales.Q n)
    (hL : 1 ≤ L.1) {x : SlotColoring.Position}
    (hs : (q, x) ∈ PhysicalWaveSum.labelRegion D L) : L.1 ∈ levels n := by
  have hn := PhysicalWaveSum.logCoordinate_in_band hq hlo hhi
  have hm := PhysicalWaveSum.logCoordinate_in_band hq
    (PhysicalWaveSum.labelRegion_band hs).1 (PhysicalWaveSum.labelRegion_band hs).2
  have hnm : n ≤ L.1 + 2 := by
    have he : (n : ℝ) ≤ (L.1 : ℝ) + 2 := by linarith [hn.1, hm.2]
    exact_mod_cast he
  have hmn : L.1 ≤ n + 2 := by
    have he : (L.1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [hm.1, hn.2]
    exact_mod_cast he
  apply Finset.mem_insert_of_mem
  exact Finset.mem_Icc.mpr ⟨max_le hL (by omega), hmn⟩

theorem index_le_active {h D q : ℝ} {n : ℕ} {L : SlotColoring.Label}
    (hq : 0 < q) (hlo : ChartScales.Q n / 2 ≤ q) (hhi : q ≤ 2 * ChartScales.Q n)
    (hL : 1 ≤ L.1) {x : SlotColoring.Position}
    (hs : (q, x) ∈ PhysicalWaveSum.labelRegion D L) :
    index h n ≤ ChartScales.nativeIndex h L.1 :=
  index_le (active_level_mem hq hlo hhi hL hs)

noncomputable def gridRadius (D M : ℝ) (m : ℕ) (j : Fin 3) : ℤ :=
  ⌈M / SlotColoring.width D j m + 2⌉

noncomputable def grids (D M : ℝ) (m : ℕ) : Finset SlotColoring.Grid :=
  Fintype.piFinset (fun j => Finset.Icc (-gridRadius D M m j) (gridRadius D M m j))

noncomputable def labels (D M : ℝ) (n : ℕ) : Finset (ℕ × SlotColoring.Grid) :=
  (levels n).biUnion (fun m => (grids D M m).image (fun k => (m, k)))

theorem grid_mem_of_box {D M : ℝ} {m : ℕ} (hm : 1 ≤ m) {k : SlotColoring.Grid}
    {x : SlotColoring.Position} (hM : ∀ j, |x j| ≤ M)
    (hx : x ∈ SlotColoring.physicalBox D (m, k, false)) : k ∈ grids D M m := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have hw := SlotColoring.width_pos D j hm
  have hb := hx j
  have ha : |SlotColoring.width D j m * (k j : ℝ)| ≤ M + 2 * SlotColoring.width D j m := by
    calc
      _ = |x j - (x j - SlotColoring.width D j m * (k j : ℝ))| := by congr 1; ring
      _ ≤ |x j| + |x j - SlotColoring.width D j m * (k j : ℝ)| := abs_sub _ _
      _ ≤ M + 2 * SlotColoring.width D j m := add_le_add (hM j) hb
  rw [abs_mul, abs_of_pos hw] at ha
  have hk : |(k j : ℝ)| ≤ M / SlotColoring.width D j m + 2 := by
    calc
      _ ≤ (M + 2 * SlotColoring.width D j m) / SlotColoring.width D j m :=
        (le_div_iff₀ hw).mpr (by nlinarith [ha])
      _ = M / SlotColoring.width D j m + 2 := by field_simp
  have hc : |(k j : ℝ)| ≤ (gridRadius D M m j : ℝ) := hk.trans (Int.le_ceil _)
  have hlo : -gridRadius D M m j ≤ k j := by exact_mod_cast (abs_le.mp hc).1
  have hhi : k j ≤ gridRadius D M m j := by exact_mod_cast (abs_le.mp hc).2
  exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩

/-- Every actual label whose closed mask support meets the bounded chart
is in the explicit finite family. This is separate from the overlap bound. -/
theorem active_label_mem {D M q : ℝ} {n : ℕ} {l : SlotColoring.Label}
    (hq : 0 < q) (hlo : ChartScales.Q n / 2 ≤ q) (hhi : q ≤ 2 * ChartScales.Q n)
    (hl : 1 ≤ l.1) {x : SlotColoring.Position} (hM : ∀ j, |x j| ≤ M)
    (hs : (q, x) ∈ PhysicalWaveSum.labelRegion D l) : (l.1, l.2.1) ∈ labels D M n := by
  apply Finset.mem_biUnion.mpr
  refine ⟨l.1, active_level_mem hq hlo hhi hl hs, Finset.mem_image.mpr ⟨l.2.1, ?_, rfl⟩⟩
  apply grid_mem_of_box hl hM
  exact SquaredPartition.physicalSlowMask_tsupport_subset_physicalBox D hl l.2.1 false hs.2

theorem indexBounds (h : ℝ) (hh : 0 ≤ h) :
    CommonBaseContext.IndexBounds h (index h) (gap h) :=
  ⟨index_le_native h, gap_le h hh⟩

end CommonWindow

namespace ActualPrimary

open Set Function
open scoped ContDiff Topology

abbrev profile := FinalSlowBase.actualProfile
abbrev outgoing := profile.outgoing
abbrev nominal := profile.nominal
abbrev h := outgoing.data.h
abbrev certificate := profile.certificate
abbrev modulation := profile.modulation

noncomputable def radialVector : TorusInverse.Plane := TorusInverse.vector .radial
noncomputable def temporalVector : TorusInverse.Plane := TorusInverse.vector .temporal

theorem vectors_det : radialVector.1 * temporalVector.2 - radialVector.2 * temporalVector.1 ≠ 0 :=
  by
  dsimp [radialVector, temporalVector, TorusInverse.vector]
  nlinarith [sq_nonneg (Real.sqrt 2 - 1)]

noncomputable def slots : PartitionedCovariance.SlotSystem (CoordinateAlgebra.D h) h radialVector
  temporalVector :=
  PartitionedCovariance.constructedSlotSystem (CoordinateAlgebra.D h) h outgoing.data.h_pos.le
    radialVector temporalVector

noncomputable def upper : ℝ := 2 * NominalConeAssembly.activeRight nominal

/-- These are selected outputs of the actual same-profile geometry and
covariance construction. No matrix or phase estimate is a constructor input. -/
structure Choice (B N0 : ℕ) where
  prepared : PrimaryGeometryAssembly.Prepared certificate modulation upper B slots.radius N0
  detGap : ℝ
  entryBound : ℝ
  inverseLower : ℝ
  detGap_pos : 0 < detGap
  entryBound_ge_one : 1 ≤ entryBound
  inverseLower_pos : 0 < inverseLower
  covariance : ∀ (L : PrimaryGeometryAssembly.Index nominal prepared.N) (p : PhaseCalculus.Slow),
    p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet nominal) →
    p ∈ (PrimaryGeometryAssembly.domain nominal prepared.N).carrier L →
    PrimaryCovarianceBounds.ZeroOrderBounds (Real.sqrt (ChartScales.S (BaseChartJets.cellBand L)))
      detGap entryBound inverseLower (PrimaryTargetBounds.movingWeight nominal p)
      (PrimaryTargetBounds.preparedCovariance certificate modulation prepared radialVector
        temporalVector L p)
      (fun j => PrimaryTargetBounds.actualTarget modulation p j)

theorem choice_nonempty (B N0 : ℕ) : Nonempty (Choice B N0) := by
  obtain ⟨a, dg, eb, il, hdg, heb, hil, hb⟩ := PrimaryTargetBounds.exists_constructed_bounds
    certificate modulation profile.fullTrueCone upper B slots.radius slots.radius_pos
    (le_max_left _ _) N0 radialVector temporalVector vectors_det
  exact ⟨⟨a, dg, eb, il, hdg, heb, hil, hb⟩⟩

noncomputable def choice (B N0 : ℕ) : Choice B N0 := Classical.choice (choice_nonempty B N0)

abbrev Label (B N0 : ℕ) := PrimaryGeometryAssembly.Index nominal (choice B N0).prepared.N

noncomputable def phases (B N0 : ℕ) : Fin 2 →
    PrimaryPulseBounds.PhaseConstruction (PrimaryGeometryAssembly.domain nominal (choice B
      N0).prepared.N) :=
  PrimaryGeometryAssembly.construction certificate modulation (choice B N0).prepared
    slots.radius_pos

noncomputable def covariance (B N0 : ℕ) : Label B N0 → PhaseCalculus.Slow → SmoothCovariance.Mat2 :=
  PrimaryTargetBounds.preparedCovariance certificate modulation (choice B N0).prepared radialVector
    temporalVector

noncomputable def prefactor {B N0 : ℕ} (_j : Fin 2) (L : Label B N0) : ℝ :=
  PartitionedCovariance.nativePrefactor radialVector temporalVector slots.radius *
    ChartScales.timeCoefficient h (BaseChartJets.cellBand L) *
      ChartScales.slotLength slots.radius h (BaseChartJets.cellBand L)

theorem covariance_eq_integral (B N0 : ℕ) : covariance B N0 =
    PrimaryPulseBounds.primaryCovariance prefactor
      (fun j => (phases B N0 j).frame) (fun j => (phases B N0 j).lam)
      (fun j => (phases B N0 j).u) (fun j => (phases B N0 j).L) := by
  exact PrimaryTargetBounds.preparedCovariance_eq_construction certificate modulation (choice B
    N0).prepared
    radialVector temporalVector slots.radius_pos

noncomputable def nativeContext (B : ℕ) : CorrectionState.Context LocalSignedRequest.Point :=
  BaseContextAssembly.nativeContext certificate modulation upper B

noncomputable def gauge : VariableGaugeMean.GaugeData TorusInverse.Plane where
  radial := BaseContextAssembly.reconstruction h (PrimaryTargetBounds.leftRadius nominal)
    (PrimaryTargetBounds.rightRadius nominal) (PrimaryTargetBounds.radii_ordered nominal)
  length _ := VariableGaugeMean.qLength (2 * h)

@[simp] theorem gauge_length (n : ℕ) : gauge.length n = VariableGaugeMean.qLength (2 * h) := rfl

/-- The physical source and every primary phase use exactly the same
profile, repaired coefficients, and Borel scale sequence. -/
theorem phase_frequency (B N0 : ℕ) (j : Fin 2) (L : Label B N0) :
    (phases B N0 j).phase.F L = BaseContextAssembly.frequencySlow certificate modulation upper B
      (BaseChartJets.cellBand L) := rfl

theorem phase_axial (B N0 : ℕ) (j : Fin 2) (L : Label B N0) :
    (phases B N0 j).phase.G L = BaseContextAssembly.axialSlow certificate modulation upper B
      (BaseChartJets.cellBand L) := rfl

theorem threshold (B N0 : ℕ) : N0 ≤ (choice B N0).prepared.N := (choice B N0).prepared.threshold

theorem covariance_bounds (B N0 : ℕ) (L : Label B N0) (p : PhaseCalculus.Slow)
    (hp : p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet nominal))
    (hL : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L) :
    PrimaryCovarianceBounds.ZeroOrderBounds (Real.sqrt (ChartScales.S (BaseChartJets.cellBand L)))
      (choice B N0).detGap (choice B N0).entryBound (choice B N0).inverseLower
      (PrimaryTargetBounds.movingWeight nominal p) (covariance B N0 L p)
      (fun j => PrimaryTargetBounds.actualTarget modulation p j) :=
  (choice B N0).covariance L p hp hL

section NativeFields

variable {B N0 : ℕ}

noncomputable def position (L : Label B N0) (p : PhaseCalculus.Slow) : SlotColoring.Position :=
  ![Real.sqrt (ChartScales.Q (BaseChartJets.cellBand L)) * p.1,
    ChartScales.Q (BaseChartJets.cellBand L) ^ (CoordinateAlgebra.D h) * p.2.1,
    ChartScales.Q (BaseChartJets.cellBand L) * p.2.2]

noncomputable def similarityScale (L : Label B N0) (p : PhaseCalculus.Slow) : ℝ :=
  ChartScales.Q (BaseChartJets.cellBand L) *
    SimilarityCoordinates.coordinateQ (2 * h) (p.2.2, p.2.1)

noncomputable def spatialMask (L : Label B N0) (p : PhaseCalculus.Slow) : ℝ :=
  PartitionedCovariance.mask (CoordinateAlgebra.D h) (PrimaryGeometryAssembly.label nominal L)
    (similarityScale L p) (position L p)

noncomputable def pulseCoordinates (L : Label B N0) (x : PhaseCalculus.Slow × TorusInverse.Plane) :
    PhaseCalculus.Slow × ℝ :=
  (x.1, x.2.2 / (phases B N0 0).L L)

noncomputable def rawVelocity (j : Fin 2) (L : Label B N0)
    (x : PhaseCalculus.Slow × TorusInverse.Plane) : ProblemStatement.Space :=
  PartitionedCovariance.amplitude (ChartScales.epsilon h (BaseChartJets.cellBand L))
    (spatialMask L x.1 * PartitionedCovariance.cutoff slots.radius x.2.1)
    (covariance B N0 L x.1) (fun k => PrimaryTargetBounds.actualTarget modulation x.1 k) j •
    PrimaryPulseBounds.normalizedPulse ((phases B N0 j).frame L) ((phases B N0 j).lam L)
      ((phases B N0 j).u L) ((phases B N0 j).L L) (pulseCoordinates L x)

noncomputable def gaussian (L : Label B N0) (x : PhaseCalculus.Slow × TorusInverse.Plane) : ℝ :=
  GaussianTailFlat.profile (pulseCoordinates L x).2

noncomputable def cutVelocity (j : Fin 2) (L : Label B N0)
    (x : PhaseCalculus.Slow × TorusInverse.Plane) : ProblemStatement.Space :=
  gaussian L x • rawVelocity j L x

noncomputable def phasePoint (_L : Label B N0) (x : PhaseCalculus.Slow × TorusInverse.Plane) :
    PhaseCalculus.Slow × ℝ := (x.1, x.2.2)

noncomputable def rawPressure (j : Fin 2) (L : Label B N0) :
    PhaseCalculus.Slow × TorusInverse.Plane → ℂ :=
  ParticularWaveBounds.projectedPressure (ChartScales.carrier h (BaseChartJets.cellBand L))
    (fun x => (phases B N0 j).phase.normal L (phasePoint L x))
    (fun x => (phases B N0 j).phase.velocity L (phasePoint L x))
    (rawVelocity j L)
    (fun x => PrimaryCopyBridge.baseOperator ((phases B N0 j).phase.F L x.1)
      ((phases B N0 j).phase.shear L (phasePoint L x)) (rawVelocity j L x))
    (fun _ => 0)

noncomputable def cutPressure (j : Fin 2) (L : Label B N0)
    (x : PhaseCalculus.Slow × TorusInverse.Plane) : ℂ :=
  gaussian L x • rawPressure j L x

noncomputable def geometry (j : Fin 2) (L : Label B N0) : CommonCoverSolve.Geometry where
  gap := ChartScales.nativeIndex h (BaseChartJets.cellBand L)
  basis := (TorusAverages.transverseChart (ChartScales.timeCoefficient h (BaseChartJets.cellBand L))
    (ChartScales.timeCoefficient_pos h (BaseChartJets.cellBand L)).ne').trans
      (TorusAverages.slotChart radialVector temporalVector vectors_det)
  center := PartitionedCovariance.slotCenter h
    (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j) -
      slots.radius • temporalVector

noncomputable def clockWindow (L : Label B N0) : PeriodicPhaseAssembly.ClockWindow where
  lower := (-slots.radius, 0)
  upper := (slots.radius, (phases B N0 0).L L)
  padding := min slots.radius ((phases B N0 0).L L) / 16
  padding_pos := div_pos (lt_min slots.radius_pos ((phases B N0 0).L_pos L)) (by norm_num)

noncomputable def periodicPhase (j : Fin 2) (L : Label B N0)
    (p : PhaseCalculus.Slow) (Y : TorusInverse.Plane) : ℝ :=
  (phases B N0 j).phase.pz L / (phases B N0 j).phase.epsilon L * p.2.1 +
    (phases B N0 j).phase.x0 L * p.1 -
      PeriodicPhaseAssembly.periodicClock (geometry j L) (clockWindow L).cutoff Y *
        ((phases B N0 j).phase.p L * (phases B N0 j).phase.F L p +
          (phases B N0 j).phase.pz L * (phases B N0 j).phase.G L p)

noncomputable def commonVelocity (j : Fin 2) (L : Label B N0)
    (p : PhaseCalculus.Slow) (Y : TorusInverse.Plane) : ProblemStatement.Space :=
  ∑' k : TorusInverse.Frequency, cutVelocity j L (p, (geometry j L).coordinates k Y)

noncomputable def commonPressure (j : Fin 2) (L : Label B N0)
    (p : PhaseCalculus.Slow) (Y : TorusInverse.Plane) : ℂ :=
  ∑' k : TorusInverse.Frequency, cutPressure j L (p, (geometry j L).coordinates k Y)

/-- Both signs use the identical physical slot length. -/
theorem length_sign (j : Fin 2) (L : Label B N0) :
    (phases B N0 j).L L = (phases B N0 0).L L := rfl

/-- The Gaussian cutoff is present exactly once in the common coefficient. -/
theorem commonVelocity_eq (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow) (Y :
  TorusInverse.Plane) :
    commonVelocity j L p Y = ∑' k : TorusInverse.Frequency,
      gaussian L (p, (geometry j L).coordinates k Y) • rawVelocity j L (p, (geometry j
        L).coordinates k Y) := by
  rfl

end NativeFields

section NativePair

variable {B N0 : ℕ}

noncomputable def sourcePair (L : Label B N0) (p : PhaseCalculus.Slow)
    (hp : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L) :
    PrimaryFieldAssembly.SourcePair PhaseCalculus.Slow slots (PrimaryGeometryAssembly.label nominal
      L) where
  domain := (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L
  point := p
  point_mem := hp
  frame j := (phases B N0 j).frame L
  lam j := (phases B N0 j).lam L
  rate j := (phases B N0 j).u L
  length j := (phases B N0 j).L L
  length_pos j := (phases B N0 j).L_pos L
  coefficient_continuous j := by
    let a := (choice B N0).prepared
    exact PrimaryTargetBounds.coefficient_continuous
      (PrimaryGeometryAssembly.family certificate modulation a j) outgoing.data.h_pos.le
        slots.radius_pos
      a.one_le_M a.u_pos a.u_le a.length_bound a.slot_bound
      (fun L => a.large (BaseChartJets.cellBand L) L.property) L
  kinematics j := by
    let a := (choice B N0).prepared
    exact (PrimaryGeometryAssembly.family certificate modulation a j).kinematics
      outgoing.data.h_pos.le slots.radius_pos a.one_le_M
      (by simpa only [abs_of_pos a.u_pos] using a.u_le) a.length_bound a.slot_bound L
      (a.large (BaseChartJets.cellBand L) L.property) hp
  stretch _ := ChartScales.timeCoefficient h (BaseChartJets.cellBand L)
  stretch_pos _ := ChartScales.timeCoefficient_pos h (BaseChartJets.cellBand L)
  fits _ := le_rfl
  mode j := PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared j L
  mode_ne j := PrimaryGeometryAssembly.angularMode_ne_zero certificate modulation (choice B
    N0).prepared j L
  phase j Y := ChartScales.carrier h (BaseChartJets.cellBand L) * periodicPhase j L p Y

/-- The pair used by the physical partition is the same primary ODE pair
whose actual integral matrix was bounded above. -/
theorem sourcePair_matrix (L : Label B N0) (p : PhaseCalculus.Slow)
    (hp : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L) :
    (sourcePair L p hp).sourceMatrix = covariance B N0 L p := by
  rw [covariance_eq_integral]
  rfl

end NativePair

section Coordinates

variable {B N0 : ℕ}

noncomputable def unstretchedCoordinates (j : Fin 2) (L : Label B N0)
    (k : TorusInverse.Frequency) (Y : TorusInverse.Plane) : TorusInverse.Plane :=
  (TorusAverages.slotChart radialVector temporalVector vectors_det).symm
    (CommonCoverSolve.coverPower (ChartScales.nativeIndex h (BaseChartJets.cellBand L)) Y -
      PartitionedCovariance.slotCenter h
        (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j) -
      TorusAverages.latticePoint k)

theorem coordinates_eq (j : Fin 2) (L : Label B N0) (k : TorusInverse.Frequency) (Y :
  TorusInverse.Plane) :
    (geometry j L).coordinates k Y =
      ((unstretchedCoordinates j L k Y).1,
        ((unstretchedCoordinates j L k Y).2 + slots.radius) /
          ChartScales.timeCoefficient h (BaseChartJets.cellBand L)) := by
  let z := unstretchedCoordinates j L k Y
  have hz : (TorusAverages.slotChart radialVector temporalVector vectors_det) z =
      CommonCoverSolve.coverPower (ChartScales.nativeIndex h (BaseChartJets.cellBand L)) Y -
        PartitionedCovariance.slotCenter h
          (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j) -
        TorusAverages.latticePoint k := ContinuousLinearEquiv.apply_symm_apply _ _
  apply (geometry j L).basis.injective
  rw [show (geometry j L).basis ((geometry j L).coordinates k Y) =
    CommonCoverSolve.coverPower (geometry j L).gap Y - (geometry j L).center -
      TorusAverages.latticePoint k from
      ContinuousLinearEquiv.apply_symm_apply _ _]
  change _ = (TorusAverages.slotChart radialVector temporalVector vectors_det)
    ((TorusAverages.transverseChart (ChartScales.timeCoefficient h (BaseChartJets.cellBand L))
      (ChartScales.timeCoefficient_pos h _).ne') (z.1, (z.2 + slots.radius) / _))
  rw [TorusAverages.transverseChart_apply]
  rw [mul_div_cancel₀ _ (ChartScales.timeCoefficient_pos h _).ne']
  have he : (z.1, z.2 + slots.radius) = z + (0, slots.radius) := by ext <;> simp
  rw [he, map_add, hz, TorusAverages.slotChart_apply]
  simp only [zero_smul, zero_add]
  dsimp only [geometry]
  abel

theorem periodicPhase_periodic (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (Y : TorusInverse.Plane) (k : TorusInverse.Frequency) :
    periodicPhase j L p (Y + TorusAverages.latticePoint k) = periodicPhase j L p Y := by
  unfold periodicPhase
  rw [PeriodicPhaseAssembly.periodicClock_periodic]

theorem commonVelocity_periodic (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (Y : TorusInverse.Plane) (k : TorusInverse.Frequency) :
    commonVelocity j L p (Y + TorusAverages.latticePoint k) = commonVelocity j L p Y := by
  change PeriodizedWaveBounds.copySum (fun l (Z : TorusInverse.Plane) => cutVelocity j L (p,
    (geometry j L).coordinates l Z)) (Y + TorusAverages.latticePoint k) =
    PeriodizedWaveBounds.copySum (fun l (Z : TorusInverse.Plane) => cutVelocity j L (p, (geometry j
      L).coordinates l Z)) Y
  apply PeriodizedWaveBounds.copySum_translate _ (fun Z => Z + TorusAverages.latticePoint k)
    (Equiv.addRight (CommonCoverSolve.coverIndex (geometry j L).gap k))
  intro l Z
  exact congrArg (fun z => cutVelocity j L (p, z)) ((geometry j L).coordinates_deck l k Z)

theorem commonPressure_periodic (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (Y : TorusInverse.Plane) (k : TorusInverse.Frequency) :
    commonPressure j L p (Y + TorusAverages.latticePoint k) = commonPressure j L p Y := by
  change PeriodizedWaveBounds.copySum (fun l (Z : TorusInverse.Plane) => cutPressure j L (p,
    (geometry j L).coordinates l Z)) (Y + TorusAverages.latticePoint k) =
    PeriodizedWaveBounds.copySum (fun l (Z : TorusInverse.Plane) => cutPressure j L (p, (geometry j
      L).coordinates l Z)) Y
  apply PeriodizedWaveBounds.copySum_translate _ (fun Z => Z + TorusAverages.latticePoint k)
    (Equiv.addRight (CommonCoverSolve.coverIndex (geometry j L).gap k))
  intro l Z
  exact congrArg (fun z => cutPressure j L (p, z)) ((geometry j L).coordinates_deck l k Z)

end Coordinates

section AmplitudeIdentity

variable {B N0 : ℕ}

noncomputable def commonAmplitude (j : Fin 2) (L : Label B N0)
    (p : PhaseCalculus.Slow) (Y : TorusInverse.Plane) : HarmonicCalculus.ComplexVector :=
  ∑' k : TorusInverse.Frequency, CurlClassBounds.complexify (cutVelocity j L (p, (geometry j
    L).coordinates k Y))

theorem cutVelocity_eq_localProfile (j : Fin 2) (L : Label B N0)
    (p : PhaseCalculus.Slow) (z : TorusInverse.Plane) :
    cutVelocity j L (p, z) =
      PartitionedCovariance.amplitude (ChartScales.epsilon h (BaseChartJets.cellBand L))
        (spatialMask L p) (covariance B N0 L p) (fun k => PrimaryTargetBounds.actualTarget
          modulation p k) j •
      PrimaryPulseBounds.localPrimaryProfile ((phases B N0 j).frame L) ((phases B N0 j).lam L)
        ((phases B N0 j).u L) ((phases B N0 j).L L) slots.radius p z := by
  ext i
  simp only [cutVelocity, gaussian, rawVelocity, pulseCoordinates,
    PrimaryPulseBounds.localPrimaryProfile,
    PrimaryPulseBounds.cutoffPulse, length_sign, PiLp.smul_apply,
    smul_eq_mul, PartitionedCovariance.amplitude]
  ring

theorem nativeCoefficient_eq (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (hp : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (Z : TorusInverse.Plane) :
    (sourcePair L p hp).nativeCoefficient vectors_det 1 (ChartScales.epsilon h
      (BaseChartJets.cellBand L))
      (fun k => PrimaryTargetBounds.actualTarget modulation p k) (similarityScale L p) (position L
        p) j Z =
      CurlClassBounds.complexify (cutVelocity j L (p,
        let z := (TorusAverages.slotChart radialVector temporalVector vectors_det).symm
          (Z - PartitionedCovariance.slotCenter h
            (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j))
        (z.1, (z.2 + slots.radius) / ChartScales.timeCoefficient h (BaseChartJets.cellBand L)))) :=
          by
  unfold PrimaryFieldAssembly.SourcePair.nativeCoefficient
  rw [sourcePair_matrix, cutVelocity_eq_localProfile]
  funext i
  simp only [ spatialMask, PrimaryFieldAssembly.SourcePair.nativeSource, sourcePair,
    TorusAverages.nativeField, TorusAverages.transverseStretch, CurlClassBounds.complexify_apply,
      PiLp.smul_apply, smul_eq_mul, one_mul]

theorem commonAmplitude_eq_source (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (hp : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (Y : TorusInverse.Plane) :
    commonAmplitude j L p Y =
      (sourcePair L p hp).actualAmplitude vectors_det 1 (ChartScales.epsilon h
        (BaseChartJets.cellBand L))
        (fun k => PrimaryTargetBounds.actualTarget modulation p k) (similarityScale L p) (position
          L p) j Y := by
  unfold commonAmplitude PrimaryFieldAssembly.SourcePair.actualAmplitude TorusAverages.periodize
  rw [← (Equiv.neg TorusInverse.Frequency).tsum_eq]
  apply tsum_congr
  intro k
  rw [nativeCoefficient_eq, coordinates_eq]
  have he : CommonCoverSolve.coverPower (ChartScales.nativeIndex h (BaseChartJets.cellBand L)) Y -
        PartitionedCovariance.slotCenter h (PartitionedCovariance.signedLabel
          (PrimaryGeometryAssembly.label nominal L) j) -
        TorusAverages.latticePoint (-k) =
      TorusAverages.latticePoint k + ((SlotGeometry.cover ^ SlotColoring.nativeIndex h
        (PrimaryGeometryAssembly.label nominal L).1) Y) -
        PartitionedCovariance.slotCenter h (PartitionedCovariance.signedLabel
          (PrimaryGeometryAssembly.label nominal L) j) := by
    have hneg : TorusAverages.latticePoint (-k) = -TorusAverages.latticePoint k := by
      ext <;> simp [TorusAverages.latticePoint]
    rw [CommonCoverSolve.coverPower_apply, hneg]
    dsimp only [ChartScales.nativeIndex, BaseChartJets.cellBand, PrimaryGeometryAssembly.label]
    abel
  simp only [unstretchedCoordinates, Equiv.neg_apply, he]

end AmplitudeIdentity


noncomputable def commonContext (B : ℕ) : CorrectionState.Context LocalSignedRequest.Point :=
  CommonBaseContext.context certificate modulation upper B (CommonWindow.index h)

noncomputable def commonGauge : VariableGaugeMean.GaugeData TorusInverse.Plane where
  radial := CommonBaseContext.reconstruction h (CommonWindow.index h)
    (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
    (PrimaryTargetBounds.radii_ordered nominal)
  length _ := VariableGaugeMean.qLength (2 * h)

@[simp] theorem commonGauge_length (n : ℕ) :
    commonGauge.length n = VariableGaugeMean.qLength (2 * h) := rfl

section ActualMask

variable {B N0 : ℕ}

theorem position_normalized (L : Label B N0) (p : PhaseCalculus.Slow) :
    PrimaryRepresentatives.normalizedSlow (CoordinateAlgebra.D h) (BaseChartJets.cellBand L)
      (position L p) = p := by
  have hq := (ChartScales.Q_pos (BaseChartJets.cellBand L)).ne'
  have hqd := (Real.rpow_pos_of_pos (ChartScales.Q_pos (BaseChartJets.cellBand L))
    (CoordinateAlgebra.D h)).ne'
  have hqs := (Real.sqrt_pos.mpr (ChartScales.Q_pos (BaseChartJets.cellBand L))).ne'
  ext <;> simp [PrimaryRepresentatives.normalizedSlow, PrimaryRepresentatives.slow,
    SquaredPartition.slowCoordinates, SlotColoring.axisExponent, position, hq, hqd]
  rw [show ChartScales.Q (BaseChartJets.cellBand L) ^ (2 : ℝ)⁻¹ =
    Real.sqrt (ChartScales.Q (BaseChartJets.cellBand L)) by rw [Real.sqrt_eq_rpow]; norm_num]
  exact mul_div_cancel_left₀ _ hqs

theorem spatialMask_eq (L : Label B N0) (p : PhaseCalculus.Slow) :
    spatialMask L p =
      SquaredPartition.dyadicProfile (SimilarityCoordinates.coordinateQ (2 * h) (p.2.2, p.2.1)) *
        PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand L)
          (PrimaryGeometryAssembly.label nominal L).2 p := by
  unfold spatialMask
  rw [PrimaryRepresentatives.physicalMask_nativeMask]
  change SquaredPartition.dyadicMask (BaseChartJets.cellBand L : ℤ) (similarityScale L p) *
    PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand L) _
      (PrimaryRepresentatives.normalizedSlow _ (BaseChartJets.cellBand L) (position L p)) = _
  rw [position_normalized]
  congr 1
  unfold SquaredPartition.dyadicMask similarityScale
  rw [SquaredPartition.integerQ_nat]
  exact congrArg SquaredPartition.dyadicProfile (mul_div_cancel_left₀ _ (ChartScales.Q_pos _).ne')

theorem spatialMask_native_support (L : Label B N0) (p : PhaseCalculus.Slow)
    (hm : spatialMask L p ≠ 0) :
    p ∈ tsupport (PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand L)
      (PrimaryGeometryAssembly.label nominal L).2) := by
  rw [spatialMask_eq] at hm
  exact subset_closure (right_ne_zero_of_mul hm)

theorem spatialMask_q_range (L : Label B N0) (p : PhaseCalculus.Slow)
    (hm : spatialMask L p ≠ 0) :
    SimilarityCoordinates.coordinateQ (2 * h) (p.2.2, p.2.1) ∈ Ioo (1 / 2 : ℝ) 2 := by
  rw [spatialMask_eq] at hm
  have hs : SimilarityCoordinates.coordinateQ (2 * h) (p.2.2, p.2.1) ∈
      Function.support SquaredPartition.dyadicProfile := left_ne_zero_of_mul hm
  simpa only [SquaredPartition.dyadicProfile_support] using hs

theorem spatialMask_carrier (L : Label B N0) {p : PhaseCalculus.Slow}
    (hT : 0 < p.2.2) (hm : spatialMask L p ≠ 0) :
    p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L :=
  PrimaryGeometryAssembly.native_support_in_carrier nominal L
    ⟨spatialMask_native_support L p hm, hT⟩

theorem spatialMask_reference (L : Label B N0) {p : PhaseCalculus.Slow}
    (hT : 0 < p.2.2) (hR : 0 ≤ p.1)
    (hX : (BaseChartJets.normalizedCoordinates h p).2.1 ∈
      Icc (NominalConeAssembly.activeLeft nominal) (NominalConeAssembly.activeRight nominal))
    (hm : spatialMask L p ≠ 0) :
    p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet nominal) := by
  refine ⟨subset_closure ?_, hT⟩
  have hs := SimilarityCoordinates.coordinateQ_spec (show 0 < 2 * h by linarith
    [outgoing.data.h_pos])
    (show 2 * h < 1 by linarith [outgoing.data.h_lt_half]) (p := (p.2.2, p.2.1)) hT
  refine ⟨hR, hT.le, SimilarityCoordinates.coordinateQ (2 * h) (p.2.2, p.2.1),
    ⟨(spatialMask_q_range L p hm).1.le, (spatialMask_q_range L p hm).2.le⟩, hs.2, ?_⟩
  simpa only [BaseChartJets.normalizedCoordinates_eq, SimilarityHomogeneity.chartX,
    SimilarityCoordinates.coordinateX, SimilarityHomogeneity.chartQ, div_div] using hX


end ActualMask

noncomputable def rankInner : ℝ :=
  ReservedPatches.radialSupportLeft outgoing nominal.controls.radius .mean
noncomputable def rankOuter : ℝ :=
  ReservedPatches.radialSupportRight outgoing nominal.controls.radius .mean
noncomputable def rankAmplitude : ℝ :=
  ReservedPatches.radialAmplitude outgoing nominal.controls.radius 0
noncomputable def rankData : CorrectionState.RankData TorusInverse.Plane :=
  RankStateBounds.normalizedData (2 * h) (CoordinateAlgebra.A h) rankAmplitude
    outgoing.data.core.lam rankInner rankOuter

theorem rankInner_pos : 0 < rankInner :=
  ReservedPatches.radialSupportLeft_pos outgoing nominal.controls.radius
    nominal.controls.radius_pos .mean

theorem rank_radii_ordered : rankInner < rankOuter :=
  (ReservedPatches.radial_support_margins outgoing nominal.controls.radius
    nominal.controls.radius_pos .mean).2.1

theorem rankAmplitude_pos : 0 < rankAmplitude :=
  ReservedPatches.radialAmplitude_pos outgoing nominal.controls.radius 0

theorem active_left_before_rank : PrimaryTargetBounds.leftRadius nominal < rankInner := by
  have hc : 0 < ReservedPatches.leftClock outgoing .mean :=
    outgoing.data.core.holdStart_pos.trans (ReservedPatches.clock_inside_wait outgoing .mean).1
  have hX : NominalConeAssembly.activeLeft nominal <
      ReservedPatches.left outgoing nominal.controls.radius .mean := by
    calc
      _ < NominalProfile.Xi := NominalConeAssembly.activeLeft_lt_Xi nominal
      _ < nominal.controls.heatJoin := nominal.controls.Xi_lt_heatJoin nominal.separated
      _ < nominal.controls.radius := nominal.controls.heatJoin_lt_radius
      _ < ReservedPatches.left outgoing nominal.controls.radius .mean := by
        change nominal.controls.radius < nominal.controls.radius * Real.exp _
        exact lt_mul_of_one_lt_right nominal.controls.radius_pos (Real.one_lt_exp_iff.mpr hc)
  exact (Real.sqrt_lt_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos
    nominal).le)
    (mul_lt_mul_of_pos_left hX (by norm_num))).trans
      (ReservedPatches.radial_support_margins outgoing nominal.controls.radius
        nominal.controls.radius_pos .mean).1

theorem rank_before_active_right : rankOuter < PrimaryTargetBounds.rightRadius nominal := by
  have hc : ReservedPatches.rightClock outgoing .mean < OutgoingTail.tailEnd outgoing.data := by
    have hp : outgoing.data.core.pulseStart < outgoing.data.core.endpoint := by
      dsimp [OutgoingSchedule.Parameters.endpoint]
      linarith [outgoing.data.core.pulseLength_pos]
    have h1 := OutgoingTail.flattenEnd_gt_core outgoing.data
    have h2 := OutgoingTail.releaseStart_gt_flattenEnd outgoing.data
    have h3 := OutgoingTail.tailStart_gt_release outgoing.data
    have h4 := (ReservedPatches.clock_inside_wait outgoing .mean).2
    dsimp [OutgoingTail.tailEnd]
    linarith
  have hX : ReservedPatches.right outgoing nominal.controls.radius .mean <
      NominalConeAssembly.activeRight nominal :=
    mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hc) nominal.controls.radius_pos
  exact (ReservedPatches.radial_support_margins outgoing nominal.controls.radius
    nominal.controls.radius_pos .mean).2.2.trans
    (Real.sqrt_lt_sqrt (mul_nonneg (by norm_num) (ReservedPatches.right_pos outgoing
      nominal.controls.radius nominal.controls.radius_pos .mean).le)
      (mul_lt_mul_of_pos_left hX (by norm_num)))

theorem rankData_parameters (U : Set TorusInverse.Plane) :
    RankStateBounds.NormalizedParameters (2 * h) (CoordinateAlgebra.A h) rankAmplitude rankData U :=
  RankStateBounds.normalizedData_parameters _ _ _ _ _ _ _

theorem rank_geometry (U : LocalSignedRequest.SlowRegion (2 * h)) (B : ℕ)
    (u : CorrectionState.State LocalSignedRequest.Point)
    (hdebt : ∀ n, ContDiffOn ℝ ∞ (CorrectionState.debt (commonContext B) u n) U.carrier) :
    LocalRankDefect.RankGeometry commonGauge rankData U.carrier (commonContext B) u := by
  have hsm := BaseRankPatch.rank_parameters_smooth outgoing nominal.controls.radius
  have hsub : U.carrier ⊆ {s : TorusInverse.Plane | 0 < s.1} := U.time_pos
  refine {
    primitive_inner_pos := PrimaryTargetBounds.leftRadius_pos nominal
    exponent_pos := ChartScales.radialExponent_pos h outgoing.data.h_pos.le
    lambda_pos := outgoing.data.core.lam_pos
    inner_pos := rankInner_pos
    inner_lt_outer := rank_radii_ordered
    coefficient_ne := ?_
    length_pos := ?_
    velocity_ne := ?_
    coefficient_smooth := ?_
    length_smooth := ?_
    velocity_smooth := ?_
    debt_smooth := hdebt
    gauge_length_pos := ?_
    gauge_left := ?_
    gauge_right := ?_
    angular_model := ?_
    axial_model := ?_ }
  · intro n x hx
    exact (BaseRankPatch.rankCoefficient_pos outgoing nominal.controls.radius x).ne'
  · intro n x hx
    exact BaseRankPatch.rankLength_pos outgoing.data.h_pos outgoing.data.h_lt_half (U.time_pos x hx)
  · intro n x hx
    exact (BaseRankPatch.rankVelocity_pos outgoing.data.h_pos outgoing.data.h_lt_half (U.time_pos x
      hx)).ne'
  · intro n
    exact hsm.1.mono hsub
  · intro n
    exact hsm.2.1.mono hsub
  · intro n
    exact hsm.2.2.mono hsub
  · intro n x hx
    exact BaseRankPatch.rankLength_pos outgoing.data.h_pos outgoing.data.h_lt_half (U.time_pos x hx)
  · intro n x hx
    exact mul_le_mul_of_nonneg_left active_left_before_rank.le
      (BaseRankPatch.rankLength_pos outgoing.data.h_pos outgoing.data.h_lt_half (U.time_pos x
        hx)).le
  · intro n x hx
    exact mul_le_mul_of_nonneg_left rank_before_active_right.le
      (BaseRankPatch.rankLength_pos outgoing.data.h_pos outgoing.data.h_lt_half (U.time_pos x
        hx)).le
  · intro n x hx R hR
    exact (BaseRankPatch.rank_fields certificate modulation upper B (ChartScales.Q n) (U.time_pos x
      hx) hR).1
  · intro n x hx R hR
    exact (BaseRankPatch.rank_fields certificate modulation upper B (ChartScales.Q n) (U.time_pos x
      hx) hR).2


section ChosenNativeBounds

open PhaseJetBounds PrimaryPulseBounds PrimaryCopyBounds

noncomputable def nativeChart (B N0 : ℕ) :=
  ActualSignedGeometry.preparedChart certificate modulation (choice B N0).prepared slots.radius_pos

noncomputable def nativeReferenceBounds (B N0 : ℕ) :=
  (nativeChart B N0).referenceBounds profile.fullTrueCone slots.radius_pos radialVector
    temporalVector
    (choice B N0).detGap (choice B N0).entryBound (choice B N0).inverseLower
    (choice B N0).detGap_pos (choice B N0).entryBound_ge_one (choice B N0).inverseLower_pos
    (choice B N0).covariance

noncomputable def nativeBaseVelocity (B N0 : ℕ) (j : Fin 2) :
    Label B N0 → ActualSignedGeometry.Native → ProblemStatement.Space :=
  PrimaryCopyBounds.primaryVelocity (phases B N0) prefactor (nativeChart B N0).coordinate
    (fun L => ChartScales.epsilon h (BaseChartJets.cellBand L))
    (nativeChart B N0).target (nativeChart B N0).mask j

noncomputable def nativeEnvelope (B N0 : ℕ) (j : Fin 2) : Label B N0 → ActualSignedGeometry.Native
  → ℝ :=
  fun L x => Real.sqrt ((nativeChart B N0).weight L x) *
    PrimaryCopyBounds.pulseEnvelope (phases B N0) (nativeChart B N0).coordinate j L x

theorem nativeBaseVelocity_jets (B N0 : ℕ) (j : Fin 2) :
    PrimaryCopyBounds.NativeJets (nativeChart B N0).native
      (fun L x => Real.sqrt (ChartScales.epsilon h (BaseChartJets.cellBand L)) * nativeEnvelope B
        N0 j L x)
      (nativeBaseVelocity B N0 j) := by
  let H := nativeReferenceBounds B N0
  exact PrimaryCopyBounds.primaryVelocity_jets (phases B N0) prefactor (nativeChart B N0).coordinate
    (fun L => ChartScales.epsilon h (BaseChartJets.cellBand L))
    (nativeChart B N0).target (nativeChart B N0).mask (nativeChart B N0).weight
    H.scale H.coordinate_jets H.coordinate_mem H.prefactor_jets H.target_jets H.mask_jets
      H.weight_pos
    H.gap_pos H.entry_one H.lower_pos H.zero_order j

noncomputable def nativeFactors (B N0 : ℕ) : Label B N0 → ActualSignedGeometry.Native → ℝ :=
  fun _ x => SquaredPartition.dyadicProfile (SimilarityCoordinates.coordinateQ (2 * h) (x.1.2.2,
    x.1.2.1)) *
    PartitionedCovariance.cutoff slots.radius x.2.1

theorem nativeFactors_jets (B N0 : ℕ) :
    PolynomialJets (nativeChart B N0).native.toDomain (nativeFactors B N0) := by
  let c := nativeChart B N0
  have hc := BaseChartJets.polynomial_of_unit (BaseChartJets.normalizedCoordinates_polynomial
    outgoing.data.h_pos outgoing.data.h_lt_half c.q_pos c.geometry)
  have hq := hc.clm (ContinuousLinearMap.fst ℝ ℝ SlowBorelBase.Inner)
  have hdy : PolynomialJets c.slow.toDomain (fun _ p =>
      SquaredPartition.dyadicProfile (BaseChartJets.normalizedCoordinates h p).1) := by
    apply hq.compact_comp isOpen_univ SquaredPartition.dyadicProfile_smooth.contDiffOn
      (isCompact_Icc : IsCompact (Icc c.qLower c.qUpper)) (subset_univ _)
    intro L p hp
    exact ⟨(c.geometry.q_range L p hp).1.le, (c.geometry.q_range L p hp).2.le⟩
  have hs := c.coordinate_jets.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ)
  have hdc := ((EnvelopeJets.of_polynomial hdy).comp hs (fun _ => rfl) c.slow_maps).to_polynomial
    (fun _ _ _ => le_rfl)
  have hu : PolynomialJets c.native.toDomain (fun _ (x : ActualSignedGeometry.Native) => x.2.1) :=
    by
    have hh := PolynomialJets.affine (D := c.native.toDomain)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ PhaseCalculus.Slow
        TorusInverse.Plane))
      (fun _ => 0) (C := max 1 slots.radius) (m := 0) (le_max_left _ _) ?_
    · simpa only [add_zero, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd'] using hh
    intro L x hx
    have hv : |x.2.1| ≤ slots.radius := abs_le.mpr ⟨hx.2.1.1.le, hx.2.1.2.le⟩
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', add_zero, pow_zero, mul_one, Real.norm_eq_abs] using
      hv.trans (le_max_right 1 slots.radius)
  have ht : PolynomialJets c.native.toDomain (fun _ (x : ActualSignedGeometry.Native) =>
      PartitionedCovariance.cutoff slots.radius x.2.1) := by
    apply hu.compact_comp isOpen_univ (SquaredPartition.gridMask_smooth slots.radius 0).contDiffOn
      (isCompact_Icc : IsCompact (Icc (-slots.radius) slots.radius)) (subset_univ _)
    intro L x hx
    exact ⟨hx.2.1.1.le, hx.2.1.2.le⟩
  have he := hdc.mul ht
  simp only [ BaseChartJets.normalizedCoordinates_eq,
    SimilarityHomogeneity.chartQ] at he ⊢
  exact he

theorem rawVelocity_eq_native (B N0 : ℕ) (j : Fin 2) (L : Label B N0)
    (x : ActualSignedGeometry.Native) :
    rawVelocity j L x = nativeFactors B N0 L x • nativeBaseVelocity B N0 j L x := by
  unfold rawVelocity
  rw [covariance_eq_integral, spatialMask_eq]
  change _ = nativeFactors B N0 L x •
    (PartitionedCovariance.amplitude (ChartScales.epsilon h (BaseChartJets.cellBand L))
      (PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand L)
        (PrimaryGeometryAssembly.label nominal L).2 x.1)
      (PrimaryPulseBounds.primaryCovariance prefactor (fun j => (phases B N0 j).frame)
        (fun j => (phases B N0 j).lam) (fun j => (phases B N0 j).u)
        (fun j => (phases B N0 j).L) L x.1)
      (fun k => PrimaryTargetBounds.actualTarget modulation x.1 k) j •
      PrimaryPulseBounds.normalizedPulse ((phases B N0 j).frame L) ((phases B N0 j).lam L)
        ((phases B N0 j).u L) ((phases B N0 j).L L) (pulseCoordinates L x))
  simp only [nativeFactors, PartitionedCovariance.amplitude, smul_smul]
  congr 1
  ring

theorem rawVelocity_jets (B N0 : ℕ) (j : Fin 2) :
    PrimaryCopyBounds.NativeJets (nativeChart B N0).native
      (fun L x => Real.sqrt (ChartScales.epsilon h (BaseChartJets.cellBand L)) * nativeEnvelope B
        N0 j L x)
      (fun L => rawVelocity j L) := by
  apply ((nativeBaseVelocity_jets B N0 j).polynomial_smul (nativeFactors_jets B N0)).congr
  intro L x hx
  exact (rawVelocity_eq_native B N0 j L x).symm

theorem native_phasePoint_eq (B N0 : ℕ) (j : Fin 2) (L : Label B N0)
    (x : ActualSignedGeometry.Native) :
    PrimaryCopyBounds.phasePoint (phases B N0 j) (nativeChart B N0).coordinate L x = phasePoint L x
      := by
  apply Prod.ext
  · rfl
  · change ((phases B N0 j).L L) * (x.2.2 / (phases B N0 0).L L) = x.2.2
    rw [length_sign j L, mul_div_cancel₀ _ ((phases B N0 0).L_pos L).ne']

theorem phasePressure_eq_raw (B N0 : ℕ) (j : Fin 2) (L : Label B N0)
    (x : ActualSignedGeometry.Native) :
    PrimaryCopyBounds.phasePressure (phases B N0 j) (nativeChart B N0).coordinate
      (fun L => (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ))
      (fun L => rawVelocity j L) L x = rawPressure j L x := by
  simp only [PrimaryCopyBounds.phasePressure, rawPressure, ParticularWaveBounds.projectedPressure,
    native_phasePoint_eq]
  rfl

theorem rawPressure_jets (B N0 : ℕ) (j : Fin 2) :
    PrimaryCopyBounds.NativeJets (nativeChart B N0).native
      (fun L x => ChartScales.epsilon h (BaseChartJets.cellBand L) * nativeEnvelope B N0 j L x)
      (fun L => rawPressure j L) := by
  let c := nativeChart B N0
  have hp := PrimaryCopyBounds.phasePressure_carrier_jets (phases B N0 j) c.coordinate
    c.scale c.coordinate_jets c.maps (rawVelocity_jets B N0 j) h outgoing.data.h_pos.le
      BaseChartJets.cellBand
  have he : (fun L x => Real.sqrt (ChartScales.epsilon h (BaseChartJets.cellBand L)) *
      (Real.sqrt (ChartScales.epsilon h (BaseChartJets.cellBand L)) * nativeEnvelope B N0 j L x)) =
      (fun L x => ChartScales.epsilon h (BaseChartJets.cellBand L) * nativeEnvelope B N0 j L x) :=
        by
    funext L x
    rw [← mul_assoc, Real.mul_self_sqrt (ChartScales.epsilon_pos h _).le]
  rw [he] at hp
  exact hp.congr (fun L x _ => phasePressure_eq_raw B N0 j L x)

theorem gaussian_jets (B N0 : ℕ) :
    PolynomialJets (nativeChart B N0).native.toDomain (fun L => gaussian L) :=
  (nativeReferenceBounds B N0).cutoff_jets

theorem cutVelocity_jets (B N0 : ℕ) (j : Fin 2) :
    PrimaryCopyBounds.NativeJets (nativeChart B N0).native
      (fun L x => Real.sqrt (ChartScales.epsilon h (BaseChartJets.cellBand L)) * nativeEnvelope B
        N0 j L x)
      (fun L => cutVelocity j L) :=
  (rawVelocity_jets B N0 j).polynomial_smul (gaussian_jets B N0)

theorem cutPressure_jets (B N0 : ℕ) (j : Fin 2) :
    PrimaryCopyBounds.NativeJets (nativeChart B N0).native
      (fun L x => ChartScales.epsilon h (BaseChartJets.cellBand L) * nativeEnvelope B N0 j L x)
      (fun L => cutPressure j L) :=
  (rawPressure_jets B N0 j).polynomial_smul (gaussian_jets B N0)


end ChosenNativeBounds

section ActualTangentCovariance

open PartitionedCovariance PrimaryFieldAssembly

variable {B N0 : ℕ}

noncomputable def tangentMode (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (Y : TorusInverse.Plane) (theta : ℝ) : Fin 3 → ℝ :=
  fun i => (HarmonicCalculus.vectorMode 1
    (fun z : TorusInverse.Plane × ℝ =>
      (PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared j L : ℝ) *
        z.2 +
        ChartScales.carrier h (BaseChartJets.cellBand L) * periodicPhase j L p z.1)
    (fun z => commonAmplitude j L p z.1) (Y, theta) i).re

theorem tangentMode_eq_source (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (hp : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (Y : TorusInverse.Plane) (theta : ℝ) :
    tangentMode j L p Y theta =
      (sourcePair L p hp).actualVelocity vectors_det 1 (ChartScales.epsilon h
        (BaseChartJets.cellBand L))
        (fun k => PrimaryTargetBounds.actualTarget modulation p k) (similarityScale L p) (position
          L p) j Y theta := by
  funext i
  simp only [tangentMode, SourcePair.actualVelocity, HarmonicCalculus.vectorMode,
    HarmonicCalculus.mode,
    commonAmplitude_eq_source j L p hp]
  rfl

theorem sourcePair_strictCone (L : Label B N0) (p : PhaseCalculus.Slow)
    (hp : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (hK : p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet nominal))
    (hw : 0 < PrimaryTargetBounds.movingWeight nominal p) :
    SmoothCovariance.StrictCone (sourcePair L p hp).pairData.matrix
      (fun k => PrimaryTargetBounds.actualTarget modulation p k) := by
  rw [← SourcePair.sourceMatrix_eq, sourcePair_matrix]
  exact (covariance_bounds B N0 L p hK hp).strictCone
    (Real.sqrt_pos.mpr (ChartScales.S_pos L.val.property.1)) (choice B N0).inverseLower_pos hw

theorem tangentMode_diagonal_covariance (L : Label B N0) (p : PhaseCalculus.Slow)
    (hp : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (hK : p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet nominal))
    (hw : 0 < PrimaryTargetBounds.movingWeight nominal p) (i : Fin 2) :
    (∑ j : Fin 2, doubleAverage (fun Y theta =>
      tangentMode j L p Y theta 0 * tangentMode j L p Y theta i.succ)) =
      ChartScales.epsilon h (BaseChartJets.cellBand L) * spatialMask L p ^ 2 *
        PrimaryTargetBounds.actualTarget modulation p i := by
  simp_rw [tangentMode_eq_source _ L p hp, SourcePair.actualVelocity_eq,
    slotVelocity_zero, slotVelocity_succ]
  have he := (sourcePair L p hp).pairData.diagonal_pair_reconstruct vectors_det 1
    (ChartScales.epsilon h (BaseChartJets.cellBand L)) (ChartScales.epsilon_pos h _).le
    (sourcePair_strictCone L p hp hK hw) (similarityScale L p) (position L p) i
  simpa only [one_pow, one_mul, spatialMask] using he

noncomputable def physicalTangentMode (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (Y : TorusInverse.Plane) (theta : ℝ) : Fin 3 → ℝ :=
  ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h) • tangentMode j L p Y theta

theorem physicalTangentMode_diagonal_covariance (L : Label B N0) (p : PhaseCalculus.Slow)
    (hp : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (hK : p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet nominal))
    (hw : 0 < PrimaryTargetBounds.movingWeight nominal p) (i : Fin 2) :
    (∑ j : Fin 2, doubleAverage (fun Y theta =>
      physicalTangentMode j L p Y theta 0 * physicalTangentMode j L p Y theta i.succ)) =
      (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h)) ^ 2 *
        ChartScales.epsilon h (BaseChartJets.cellBand L) * spatialMask L p ^ 2 *
          PrimaryTargetBounds.actualTarget modulation p i := by
  simp only [physicalTangentMode, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ j Y theta, (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h) *
      tangentMode j L p Y theta 0) * (ChartScales.Q (BaseChartJets.cellBand L) ^
        (-CoordinateAlgebra.A h) *
      tangentMode j L p Y theta i.succ) =
      (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h)) ^ 2 *
        (tangentMode j L p Y theta 0 * tangentMode j L p Y theta i.succ) from by intros; ring]
  simp_rw [doubleAverage_const_mul]
  rw [← Finset.mul_sum, tangentMode_diagonal_covariance L p hp hK hw i]
  ring

theorem tangentMode_pair_covariance (L : Label B N0) (p : PhaseCalculus.Slow)
    (hp : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (hK : p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet nominal))
    (hw : 0 < PrimaryTargetBounds.movingWeight nominal p) (i : Fin 2) :
    doubleAverage (fun Y theta =>
      (∑ j : Fin 2, tangentMode j L p Y theta 0) *
      (∑ j : Fin 2, tangentMode j L p Y theta i.succ)) =
      ChartScales.epsilon h (BaseChartJets.cellBand L) * spatialMask L p ^ 2 *
        PrimaryTargetBounds.actualTarget modulation p i := by
  let P := (sourcePair L p hp).pairData
  have hq : 0 < similarityScale L p := by
    apply mul_pos (ChartScales.Q_pos _)
    exact (SimilarityCoordinates.coordinateQ_spec
      (show 0 < 2*h by linarith [outgoing.data.h_pos])
      (show 2*h < 1 by linarith [outgoing.data.h_lt_half]) (p := (p.2.2,p.2.1)) hK.2).1
  have hv := slots.finite_wave_covariance (Finset.univ : Finset (Fin 2))
    (signedLabel (PrimaryGeometryAssembly.label nominal L))
    (signedLabel_injective _).injOn (fun _ _ => L.val.property.1)
    (P.rawRadial vectors_det) (fun j => P.rawTangent vectors_det j i)
    (fun j _ => P.rawRadial_support vectors_det j)
    (fun j _ => P.rawTangent_support vectors_det j i)
    (fun j _ => P.rawRadial_continuous vectors_det j)
    (fun j _ => P.rawRadial_compact vectors_det j)
    (fun j _ => P.rawTangent_continuous vectors_det j i)
    (fun j _ => P.rawTangent_compact vectors_det j i)
    P.modes (fun j _ => P.modes_ne j) P.phases
    (fun j => (1 : ℝ) * Real.sqrt (ChartScales.epsilon h (BaseChartJets.cellBand L)) *
      SmoothCovariance.amplitudes P.matrix (fun k => PrimaryTargetBounds.actualTarget modulation p
        k) j)
    hq (position L p)
  have hdiag : doubleAverage (fun Y theta =>
      (∑ j : Fin 2, tangentMode j L p Y theta 0) *
      (∑ j : Fin 2, tangentMode j L p Y theta i.succ)) =
      ∑ j : Fin 2, doubleAverage (fun Y theta =>
        tangentMode j L p Y theta 0 * tangentMode j L p Y theta i.succ) := by
    simp_rw [tangentMode_eq_source _ L p hp, SourcePair.actualVelocity_eq,
      slotVelocity_zero, slotVelocity_succ]
    simp only [P, PairData.radialWave, PairData.tangentWave, amplitude,
      physicalMask_signedLabel, mul_assoc] at hv ⊢
    exact hv
  rw [hdiag, tangentMode_diagonal_covariance L p hp hK hw i]

theorem physical_covariance_factor (L : Label B N0) (p : PhaseCalculus.Slow)
    (hT : 0 < p.2.2) (i : Fin 2) :
    (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h)) ^ 2 *
      ChartScales.epsilon h (BaseChartJets.cellBand L) * PrimaryTargetBounds.actualTarget
        modulation p i =
      similarityScale L p ^ (-CoordinateAlgebra.A h - 1/2) *
        ProfileSpectralCone.stressVector modulation.profiles h (BaseChartJets.normalizedCoordinates
          h p).2 i := by
  have hq := ChartScales.Q_pos (BaseChartJets.cellBand L)
  have hr := BaseChartJets.normalizedCoordinates_q_pos outgoing.data.h_pos outgoing.data.h_lt_half
    hT
  have he : (-CoordinateAlgebra.A h) * (2 : ℕ) + h = -CoordinateAlgebra.A h - 1/2 := by
    unfold CoordinateAlgebra.A
    norm_num
    ring
  have hscale : similarityScale L p = ChartScales.Q (BaseChartJets.cellBand L) *
      (BaseChartJets.normalizedCoordinates h p).1 := by
    rw [BaseChartJets.normalizedCoordinates_eq]
    rfl
  rw [PrimaryTargetBounds.actualTarget, PiLp.smul_apply, smul_eq_mul, ChartScales.epsilon,
    ← Real.rpow_mul_natCast hq.le, ← Real.rpow_add hq, he, hscale, Real.mul_rpow hq.le hr.le]
  ring


end ActualTangentCovariance

section ActualPhysicalCharts

open Set Function
open scoped ContDiff Topology

abbrev AbsolutePoint := PhaseCalculus.Slow × TorusInverse.Plane

noncomputable def toAbsolute (n : ℕ) (x : LocalSignedRequest.Point) : AbsolutePoint :=
  ((Real.sqrt (ChartScales.Q n) * x.1,
    (ChartScales.Q n ^ CoordinateAlgebra.D h * x.2.1.2, ChartScales.Q n * x.2.1.1)),
      (CommonCoverSolve.coverPower (CommonWindow.index h n)).symm x.2.2)

noncomputable def fromAbsolute (n : ℕ) (x : AbsolutePoint) : LocalSignedRequest.Point :=
  (x.1.1 / Real.sqrt (ChartScales.Q n),
    ((x.1.2.2 / ChartScales.Q n, x.1.2.1 / ChartScales.Q n ^ CoordinateAlgebra.D h),
      CommonCoverSolve.coverPower (CommonWindow.index h n) x.2))

theorem toAbsolute_fromAbsolute (n : ℕ) (x : AbsolutePoint) :
    toAbsolute n (fromAbsolute n x) = x := by
  have hq := (ChartScales.Q_pos n).ne'
  have hs := (Real.sqrt_pos.mpr (ChartScales.Q_pos n)).ne'
  have hd := (Real.rpow_pos_of_pos (ChartScales.Q_pos n) (CoordinateAlgebra.D h)).ne'
  apply Prod.ext
  · apply Prod.ext
    · exact mul_div_cancel₀ _ hs
    · exact Prod.ext (mul_div_cancel₀ _ hd) (mul_div_cancel₀ _ hq)
  · exact (CommonCoverSolve.coverPower (CommonWindow.index h n)).symm_apply_apply x.2

theorem fromAbsolute_toAbsolute (n : ℕ) (x : LocalSignedRequest.Point) :
    fromAbsolute n (toAbsolute n x) = x := by
  have hq := (ChartScales.Q_pos n).ne'
  have hs := (Real.sqrt_pos.mpr (ChartScales.Q_pos n)).ne'
  have hd := (Real.rpow_pos_of_pos (ChartScales.Q_pos n) (CoordinateAlgebra.D h)).ne'
  simp [toAbsolute, fromAbsolute, hq, hs, hd]

theorem toAbsolute_smooth (n : ℕ) : ContDiff ℝ ∞ (toAbsolute n) :=
  ((contDiff_const.mul contDiff_fst).prodMk
    ((contDiff_const.mul contDiff_snd.fst.snd).prodMk
      (contDiff_const.mul contDiff_snd.fst.fst))).prodMk
    ((CommonCoverSolve.coverPower (CommonWindow.index h n)).symm.contDiff.comp contDiff_snd.snd)

theorem fromAbsolute_smooth (n : ℕ) : ContDiff ℝ ∞ (fromAbsolute n) :=
  (contDiff_fst.fst.div_const _).prodMk
    (((contDiff_fst.snd.snd.div_const _).prodMk (contDiff_fst.snd.fst.div_const _)).prodMk
      ((CommonCoverSolve.coverPower (CommonWindow.index h n)).contDiff.comp contDiff_snd))

variable {B N0 : ℕ}

noncomputable def chartGeometry (n : ℕ) (j : Fin 2) (L : Label B N0) : CommonCoverSolve.Geometry :=
  { geometry j L with gap := ChartScales.nativeIndex h (BaseChartJets.cellBand L) -
    CommonWindow.index h n }

theorem chartGeometry_coordinates (n : ℕ) (j : Fin 2) (L : Label B N0)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (Y : TorusInverse.Plane) :
    (geometry j L).coordinates k ((CommonCoverSolve.coverPower (CommonWindow.index h n)).symm Y) =
      (chartGeometry n j L).coordinates k Y := by
  have he : ChartScales.nativeIndex h (BaseChartJets.cellBand L) =
      (ChartScales.nativeIndex h (BaseChartJets.cellBand L) - CommonWindow.index h n) +
        CommonWindow.index h n := by omega
  simp only [CommonCoverSolve.Geometry.coordinates, chartGeometry, geometry]
  rw [he, CopySolveCompatibility.coverPower_add, ContinuousLinearEquiv.apply_symm_apply]
  simp only [Nat.add_sub_cancel]

theorem chartGeometry_coordinates_active (n : ℕ) (j : Fin 2) (L : Label B N0)
    (hL : BaseChartJets.cellBand L ∈ CommonWindow.levels n)
    (k : TorusInverse.Frequency) (Y : TorusInverse.Plane) :
    (geometry j L).coordinates k ((CommonCoverSolve.coverPower (CommonWindow.index h n)).symm Y) =
      (chartGeometry n j L).coordinates k Y :=
  chartGeometry_coordinates n j L (CommonWindow.index_le hL) k Y

end ActualPhysicalCharts

section ActualPeriodization

open Set Function Filter
open scoped ContDiff Topology BigOperators

variable {B N0 : ℕ}

noncomputable def outerRawVelocity (j : Fin 2) (L : Label B N0)
    (x : ActualSignedGeometry.Native) : ProblemStatement.Space :=
  PrimaryCopyBounds.outerCutoff (pulseCoordinates L x).2 • rawVelocity j L x

noncomputable def attachedRawVelocity (j : Fin 2) (L : Label B N0) :
    ActualSignedGeometry.Native → ProblemStatement.Space :=
  WaveEdgeExtension.nativeExtension nominal (outerRawVelocity j L)

noncomputable def uncutAmplitude (j : Fin 2) (L : Label B N0)
    (p : PhaseCalculus.Slow) (Y : TorusInverse.Plane) : HarmonicCalculus.ComplexVector :=
  ∑' k : TorusInverse.Frequency,
    CurlClassBounds.complexify (attachedRawVelocity j L (p, (geometry j L).coordinates k Y))

noncomputable def periodicGaussian (j : Fin 2) (L : Label B N0) (Y : TorusInverse.Plane) : ℝ :=
  GaussianTailFlat.profile
    (PeriodicPhaseAssembly.periodicClock (geometry j L) (clockWindow L).cutoff Y / (phases B N0
      0).L L)

theorem periodicGaussian_smooth (j : Fin 2) (L : Label B N0) :
    ContDiff ℝ ∞ (periodicGaussian j L) :=
  GaussianTailFlat.profile_contDiff.comp
    ((PeriodicPhaseAssembly.periodicClock_contDiff (geometry j L) (clockWindow L)).div_const _)

theorem periodicGaussian_periodic (j : Fin 2) (L : Label B N0) (Y : TorusInverse.Plane)
    (k : TorusInverse.Frequency) :
    periodicGaussian j L (Y + TorusAverages.latticePoint k) = periodicGaussian j L Y := by
  unfold periodicGaussian
  rw [PeriodicPhaseAssembly.periodicClock_periodic]

theorem uncutAmplitude_periodic (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (Y : TorusInverse.Plane) (k : TorusInverse.Frequency) :
    uncutAmplitude j L p (Y + TorusAverages.latticePoint k) = uncutAmplitude j L p Y := by
  change PeriodizedWaveBounds.copySum
    (fun l (Z : TorusInverse.Plane) => CurlClassBounds.complexify (attachedRawVelocity j L (p,
      (geometry j L).coordinates l Z)))
    (Y + TorusAverages.latticePoint k) = _
  apply PeriodizedWaveBounds.copySum_translate _ (fun Z => Z + TorusAverages.latticePoint k)
    (Equiv.addRight (CommonCoverSolve.coverIndex (geometry j L).gap k))
  intro l Z
  exact congrArg (fun z => CurlClassBounds.complexify (attachedRawVelocity j L (p, z)))
    ((geometry j L).coordinates_deck l k Z)

theorem clockWindow_injective (j : Fin 2) (L : Label B N0) :
    InjOn TorusAverages.quotientPoint
      ((fun z => (geometry j L).center + (geometry j L).basis z) '' (clockWindow L).outer) := by
  have hn := ((choice B N0).prepared.large (BaseChartJets.cellBand L) L.property).four_le
  exact ActualSignedGeometry.clockWindow_injective slots vectors_det
    (l := PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j)
    outgoing.data.h_pos.le hn (ChartScales.nativeIndex h (BaseChartJets.cellBand L))

theorem rawVelocity_transverse (j : Fin 2) (L : Label B N0) (x : ActualSignedGeometry.Native)
    (hx : rawVelocity j L x ≠ 0) : x.2.1 ∈ Ioo (-slots.radius) slots.radius := by
  have hc : PartitionedCovariance.cutoff slots.radius x.2.1 ≠ 0 := by
    intro hz
    apply hx
    simp [rawVelocity, PartitionedCovariance.amplitude, hz]
  rw [← PartitionedCovariance.cutoff_support slots.radius_pos]
  exact hc

theorem outerRawVelocity_core (j : Fin 2) (L : Label B N0) (x : ActualSignedGeometry.Native)
    (hx : outerRawVelocity j L x ≠ 0) : x.2 ∈ (clockWindow L).core := by
  have hu : rawVelocity j L x ≠ 0 := by
    intro hz
    apply hx
    simp [outerRawVelocity, hz]
  have ho : PrimaryCopyBounds.outerCutoff (pulseCoordinates L x).2 ≠ 0 := by
    intro hz
    apply hx
    simp [outerRawVelocity, hz]
  have hs := PrimaryCopyBounds.outerCutoff_support (subset_tsupport _ ho)
  have hτ : (pulseCoordinates L x).2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have ht := rawVelocity_transverse j L x hu
  have hL := (phases B N0 0).L_pos L
  refine ⟨⟨ht.1.le, ht.2.le⟩, ?_⟩
  change x.2.2 ∈ Icc 0 ((phases B N0 0).L L)
  constructor
  · have hh := (lt_div_iff₀ hL).mp hτ.1
    simpa only [zero_mul] using hh.le
  · exact ((div_lt_one hL).mp hτ.2).le

theorem cutVelocity_eq_outer (j : Fin 2) (L : Label B N0) (x : ActualSignedGeometry.Native) :
    cutVelocity j L x = gaussian L x • outerRawVelocity j L x := by
  simp only [cutVelocity, gaussian, outerRawVelocity, smul_smul,
    PrimaryCopyBounds.profile_mul_outerCutoff]

theorem periodicGaussian_eq_on_core (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (Y : TorusInverse.Plane) (k : TorusInverse.Frequency)
    (hcore : (geometry j L).coordinates k Y ∈ (clockWindow L).core) :
    periodicGaussian j L Y = gaussian L (p, (geometry j L).coordinates k Y) := by
  have hg := PeriodicPhaseAssembly.periodicClock_germ (P := PhaseCalculus.Slow)
    (geometry (B := B) (N0 := N0) j L) (clockWindow (B := B) (N0 := N0) L)
    (clockWindow_injective (B := B) (N0 := N0) j L) k (z := (p, Y)) hcore
  have hc := hg.self_of_nhds
  dsimp only at hc
  unfold periodicGaussian gaussian pulseCoordinates
  rw [hc]

theorem periodicGaussian_outerRaw (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (Y : TorusInverse.Plane) (k : TorusInverse.Frequency) :
    periodicGaussian j L Y • outerRawVelocity j L (p, (geometry j L).coordinates k Y) =
      cutVelocity j L (p, (geometry j L).coordinates k Y) := by
  rw [cutVelocity_eq_outer]
  by_cases hz : outerRawVelocity j L (p, (geometry j L).coordinates k Y) = 0
  · simp [hz]
  · rw [periodicGaussian_eq_on_core j L p Y k
      (outerRawVelocity_core (B := B) (N0 := N0) j L (p, (geometry j L).coordinates k Y) hz)]

theorem periodic_cutoff_amplitude (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (hp : PrimaryTargetBounds.profileRadius h p ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal))
    (Y : TorusInverse.Plane) :
    periodicGaussian j L Y • uncutAmplitude j L p Y = commonAmplitude j L p Y := by
  unfold uncutAmplitude commonAmplitude
  rw [← tsum_const_smul'']
  apply tsum_congr
  intro k
  rw [attachedRawVelocity, WaveEdgeExtension.nativeExtension_inside _ _ hp, ← map_smul,
    periodicGaussian_outerRaw]

noncomputable def outerRawPressure (j : Fin 2) (L : Label B N0)
    (x : ActualSignedGeometry.Native) : ℂ :=
  PrimaryCopyBounds.outerCutoff (pulseCoordinates L x).2 • rawPressure j L x

noncomputable def attachedRawPressure (j : Fin 2) (L : Label B N0) :
    ActualSignedGeometry.Native → ℂ :=
  WaveEdgeExtension.nativeExtension nominal (outerRawPressure j L)

noncomputable def uncutPressure (j : Fin 2) (L : Label B N0)
    (p : PhaseCalculus.Slow) (Y : TorusInverse.Plane) : ℂ :=
  ∑' k : TorusInverse.Frequency, attachedRawPressure j L (p, (geometry j L).coordinates k Y)

theorem rawPressure_zero_of_velocity_zero (j : Fin 2) (L : Label B N0)
    (x : ActualSignedGeometry.Native) (hz : rawVelocity j L x = 0) : rawPressure j L x = 0 := by
  unfold rawPressure ParticularWaveBounds.projectedPressure
  dsimp only
  rw [hz, map_zero]
  simp [TangentProjection.pressureCoefficient]

theorem outerRawPressure_core (j : Fin 2) (L : Label B N0) (x : ActualSignedGeometry.Native)
    (hx : outerRawPressure j L x ≠ 0) : x.2 ∈ (clockWindow L).core := by
  have hu : rawVelocity j L x ≠ 0 := by
    intro hz
    have hp := rawPressure_zero_of_velocity_zero j L x hz
    exact hx (by simp [outerRawPressure, hp])
  have ho : PrimaryCopyBounds.outerCutoff (pulseCoordinates L x).2 ≠ 0 := by
    intro hz
    exact hx (by simp [outerRawPressure, hz])
  exact outerRawVelocity_core j L x (smul_ne_zero ho hu)

theorem cutPressure_eq_outer (j : Fin 2) (L : Label B N0) (x : ActualSignedGeometry.Native) :
    cutPressure j L x = gaussian L x • outerRawPressure j L x := by
  simp only [cutPressure, gaussian, outerRawPressure, smul_smul,
    PrimaryCopyBounds.profile_mul_outerCutoff]

theorem periodicGaussian_outerPressure (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (Y : TorusInverse.Plane) (k : TorusInverse.Frequency) :
    periodicGaussian j L Y • outerRawPressure j L (p, (geometry j L).coordinates k Y) =
      cutPressure j L (p, (geometry j L).coordinates k Y) := by
  rw [cutPressure_eq_outer]
  by_cases hz : outerRawPressure j L (p, (geometry j L).coordinates k Y) = 0
  · simp [hz]
  · rw [periodicGaussian_eq_on_core j L p Y k
      (outerRawPressure_core (B := B) (N0 := N0) j L (p, (geometry j L).coordinates k Y) hz)]

theorem periodic_cutoff_pressure (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (hp : PrimaryTargetBounds.profileRadius h p ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal))
    (Y : TorusInverse.Plane) :
    periodicGaussian j L Y • uncutPressure j L p Y = commonPressure j L p Y := by
  unfold uncutPressure commonPressure
  rw [← tsum_const_smul'']
  apply tsum_congr
  intro k
  rw [attachedRawPressure, WaveEdgeExtension.nativeExtension_inside _ _ hp,
    periodicGaussian_outerPressure]


noncomputable def closedMargins (B N0 : ℕ) :
    NativeBandExtension.ClosedMargins certificate modulation (choice B N0).prepared radialVector
      temporalVector where
  gap := (choice B N0).detGap
  entry := (choice B N0).entryBound
  lower := (choice B N0).inverseLower
  gap_pos := (choice B N0).detGap_pos
  entry_one := (choice B N0).entryBound_ge_one
  lower_pos := (choice B N0).inverseLower_pos
  covariance := (choice B N0).covariance

theorem preOuterVelocity_eq (j : Fin 2) (L : Label B N0) (x : ActualSignedGeometry.Native) :
    NativeBandExtension.preOuterVelocity certificate modulation (choice B N0).prepared
      slots.radius_pos radialVector temporalVector j L x = rawVelocity j L x := by
  rw [rawVelocity_eq_native]
  rfl

theorem preOuterPressure_eq (j : Fin 2) (L : Label B N0) (x : ActualSignedGeometry.Native) :
    NativeBandExtension.preOuterPressure certificate modulation (choice B N0).prepared
      slots.radius_pos radialVector temporalVector j L x = rawPressure j L x := by
  rw [NativeBandExtension.preOuterPressure_eq_phasePressure]
  have hf : NativeBandExtension.preOuterVelocity certificate modulation (choice B N0).prepared
      slots.radius_pos radialVector temporalVector j = (fun L => rawVelocity j L) := by
    funext L x
    exact preOuterVelocity_eq j L x
  rw [hf]
  exact phasePressure_eq_raw B N0 j L x

theorem bandVelocity_eq (j : Fin 2) (L : Label B N0) :
    NativeBandExtension.bandVelocity certificate modulation (choice B N0).prepared
      slots.radius_pos radialVector temporalVector j L = outerRawVelocity j L := by
  funext x
  rw [NativeBandExtension.bandVelocity_eq_outer, preOuterVelocity_eq]
  rfl

theorem bandPressure_eq (j : Fin 2) (L : Label B N0) :
    NativeBandExtension.bandPressure certificate modulation (choice B N0).prepared
      slots.radius_pos radialVector temporalVector j L = outerRawPressure j L := by
  funext x
  rw [NativeBandExtension.bandPressure_eq_outer, preOuterPressure_eq]
  rfl

theorem preOuterVelocity_jets (B N0 : ℕ) (j : Fin 2) :
    PrimaryCopyBounds.NativeJets
      (ActualSignedGeometry.nativeDomain certificate modulation (choice B N0).prepared)
      (NativeBandExtension.velocityWeight certificate modulation (choice B N0).prepared
        slots.radius_pos j)
      (NativeBandExtension.preOuterVelocity certificate modulation (choice B N0).prepared
        slots.radius_pos radialVector temporalVector j) := by
  have hf : NativeBandExtension.preOuterVelocity certificate modulation (choice B N0).prepared
      slots.radius_pos radialVector temporalVector j = (fun L => rawVelocity j L) := by
    funext L x
    exact preOuterVelocity_eq j L x
  rw [hf]
  change PrimaryCopyBounds.NativeJets (nativeChart B N0).native
    (fun L x => Real.sqrt (ChartScales.epsilon h (BaseChartJets.cellBand L)) *
      Real.sqrt ((nativeChart B N0).weight L x) *
        PrimaryCopyBounds.pulseEnvelope (phases B N0) (nativeChart B N0).coordinate j L x)
    (fun L => rawVelocity j L)
  simpa only [nativeEnvelope, mul_assoc] using rawVelocity_jets B N0 j

theorem preOuterPressure_jets (B N0 : ℕ) (j : Fin 2) :
    PrimaryCopyBounds.NativeJets
      (ActualSignedGeometry.nativeDomain certificate modulation (choice B N0).prepared)
      (NativeBandExtension.pressureWeight certificate modulation (choice B N0).prepared
        slots.radius_pos j)
      (NativeBandExtension.preOuterPressure certificate modulation (choice B N0).prepared
        slots.radius_pos radialVector temporalVector j) := by
  have hf : NativeBandExtension.preOuterPressure certificate modulation (choice B N0).prepared
      slots.radius_pos radialVector temporalVector j = (fun L => rawPressure j L) := by
    funext L x
    exact preOuterPressure_eq j L x
  rw [hf]
  change PrimaryCopyBounds.NativeJets (nativeChart B N0).native
    (fun L x => ChartScales.epsilon h (BaseChartJets.cellBand L) *
      Real.sqrt ((nativeChart B N0).weight L x) *
        PrimaryCopyBounds.pulseEnvelope (phases B N0) (nativeChart B N0).coordinate j L x)
    (fun L => rawPressure j L)
  simpa only [nativeEnvelope, mul_assoc] using rawPressure_jets B N0 j

theorem attachedPair_regular (B N0 : ℕ) (j : Fin 2) (L : Label B N0) :
    WaveEdgeExtension.NativeRegularity nominal (outerRawVelocity j L) ∧
      WaveEdgeExtension.NativeRegularity nominal (outerRawPressure j L) := by
  have hr := NativeBandExtension.band_pair_native_regular_of_raw_jets certificate modulation
    (choice B N0).prepared slots.radius_pos radialVector temporalVector (closedMargins B N0) j
    (preOuterVelocity_jets B N0 j) (preOuterPressure_jets B N0 j) L
  simpa only [bandVelocity_eq, bandPressure_eq] using hr

theorem attachedRawVelocity_smooth (B N0 : ℕ) (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (attachedRawVelocity j L) WaveEdgeExtension.nativeSlowDomain :=
  (attachedPair_regular B N0 j L).1.smooth

theorem attachedRawPressure_smooth (B N0 : ℕ) (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (attachedRawPressure j L) WaveEdgeExtension.nativeSlowDomain :=
  (attachedPair_regular B N0 j L).2.smooth

theorem attachedPair_band_edge_jets (j : Fin 2) (L : Label B N0) {x : ActualSignedGeometry.Native}
    (hT : 0 < x.1.2.2)
    (he : SimilarityCoordinates.coordinateQ (2 * h) (x.1.2.2, x.1.2.1) = 1 / 2 ∨
      SimilarityCoordinates.coordinateQ (2 * h) (x.1.2.2, x.1.2.1) = 2) (n : ℕ) :
    iteratedFDeriv ℝ n (attachedRawVelocity j L) x = 0 ∧
      iteratedFDeriv ℝ n (attachedRawPressure j L) x = 0 := by
  have hr := NativeBandExtension.attached_pair_band_edge_jets certificate modulation
    (choice B N0).prepared slots.radius_pos radialVector temporalVector (closedMargins B N0) j
    (preOuterVelocity_jets B N0 j) (preOuterPressure_jets B N0 j) L hT he n
  simpa only [bandVelocity_eq, bandPressure_eq, attachedRawVelocity, attachedRawPressure] using hr


theorem attachedRawVelocity_core (j : Fin 2) (L : Label B N0) (x : ActualSignedGeometry.Native)
    (hx : attachedRawVelocity j L x ≠ 0) : x.2 ∈ (clockWindow L).core := by
  apply outerRawVelocity_core j L x
  intro hz
  apply hx
  simp [attachedRawVelocity, WaveEdgeExtension.nativeExtension, WaveEdgeExtension.extension, hz]

theorem attachedRawPressure_core (j : Fin 2) (L : Label B N0) (x : ActualSignedGeometry.Native)
    (hx : attachedRawPressure j L x ≠ 0) : x.2 ∈ (clockWindow L).core := by
  apply outerRawPressure_core j L x
  intro hz
  apply hx
  simp [attachedRawPressure, WaveEdgeExtension.nativeExtension, WaveEdgeExtension.extension, hz]

noncomputable def copyCells (j : Fin 2) (L : Label B N0) :
    PeriodizedWaveBounds.Cells ActualSignedGeometry.Native TorusInverse.Frequency :=
  PeriodizedWaveBounds.nativeCells (fun _ => geometry j L) (fun _ => (clockWindow L).core)
    (fun _ => (clockWindow L).core_compact)
    (fun _ => (clockWindow_injective j L).mono (Set.image_mono (clockWindow L).core_subset_outer))

theorem nativeCopySum_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Fin 2) (L : Label B N0) (f : ActualSignedGeometry.Native → E)
    (hf : ContDiffOn ℝ ∞ f WaveEdgeExtension.nativeSlowDomain)
    (hs : ∀ x, f x ≠ 0 → x.2 ∈ (clockWindow L).core) :
    ContDiffOn ℝ ∞ (fun x : ActualSignedGeometry.Native =>
      ∑' k : TorusInverse.Frequency, f (x.1, (geometry j L).coordinates k x.2))
      WaveEdgeExtension.nativeSlowDomain := by
  classical
  let F : TorusInverse.Frequency → ActualSignedGeometry.Native → E :=
    fun k x => f (x.1, (geometry j L).coordinates k x.2)
  have hF : ∀ k, support (F k) ⊆ (copyCells j L).carrier 0 k := by
    intro k x hx
    exact hs (x.1, (geometry j L).coordinates k x.2) hx
  intro x hx
  obtain ⟨J, hJ⟩ := PeriodizedWaveBounds.copySum_eventually_finite (copyCells j L) 0 F hF x
  have hsm : ContDiffAt ℝ ∞ (fun y => ∑ k ∈ J, F k y) x := by
    apply ContDiffAt.sum
    intro k hk
    have hmem : (x.1, (geometry j L).coordinates k x.2) ∈ WaveEdgeExtension.nativeSlowDomain := hx
    exact (hf.contDiffAt (WaveEdgeExtension.nativeSlowDomain_open.mem_nhds hmem)).comp x
      (contDiff_fst.prodMk ((geometry j L).coordinates_contDiff k |>.comp contDiff_snd)).contDiffAt
  exact (hsm.congr_of_eventuallyEq hJ).contDiffWithinAt

theorem uncutAmplitude_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (fun x : ActualSignedGeometry.Native => uncutAmplitude j L x.1 x.2)
      WaveEdgeExtension.nativeSlowDomain := by
  apply nativeCopySum_smooth j L
    (fun x => CurlClassBounds.complexify (attachedRawVelocity j L x))
  · exact CurlClassBounds.complexify.contDiff.comp_contDiffOn (attachedRawVelocity_smooth B N0 j L)
  · intro x hx
    apply attachedRawVelocity_core j L x
    intro hz
    exact hx (by rw [hz, map_zero])

theorem uncutPressure_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (fun x : ActualSignedGeometry.Native => uncutPressure j L x.1 x.2)
      WaveEdgeExtension.nativeSlowDomain :=
  nativeCopySum_smooth j L (attachedRawPressure j L) (attachedRawPressure_smooth B N0 j L)
    (attachedRawPressure_core j L)

theorem uncutPressure_periodic (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (Y : TorusInverse.Plane) (k : TorusInverse.Frequency) :
    uncutPressure j L p (Y + TorusAverages.latticePoint k) = uncutPressure j L p Y := by
  change PeriodizedWaveBounds.copySum
    (fun l (Z : TorusInverse.Plane) => attachedRawPressure j L (p, (geometry j L).coordinates l Z))
    (Y + TorusAverages.latticePoint k) = _
  apply PeriodizedWaveBounds.copySum_translate _ (fun Z => Z + TorusAverages.latticePoint k)
    (Equiv.addRight (CommonCoverSolve.coverIndex (geometry j L).gap k))
  intro l Z
  exact congrArg (fun z => attachedRawPressure j L (p, z)) ((geometry j L).coordinates_deck l k Z)

end ActualPeriodization

section ActualFiniteFamily

open Set Function
open scoped ContDiff Topology BigOperators
variable {B N0 : ℕ}

noncomputable def standardRegion : LocalSignedRequest.SlowRegion (2 * h) :=
  ActualSignedGeometry.standardSlowRegion outgoing.data.h_pos outgoing.data.h_lt_half

noncomputable def physicalPosition (n : ℕ) (x : LocalSignedRequest.Point) : SlotColoring.Position :=
  ![Real.sqrt (ChartScales.Q n) * x.1, ChartScales.Q n ^ CoordinateAlgebra.D h * x.2.1.2,
    ChartScales.Q n * x.2.1.1]

noncomputable def physicalScale (n : ℕ) (x : LocalSignedRequest.Point) : ℝ :=
  ChartScales.Q n * SimilarityCoordinates.coordinateQ (2 * h) x.2.1

noncomputable def activeLabels (U : LocalSignedRequest.SlowRegion (2 * h)) (B N0 n : ℕ) :
    Finset (Label B N0 × Fin 2) := by
  classical
  exact ((CommonWindow.labels (CoordinateAlgebra.D h) (BaseContextAssembly.geometryBound nominal U)
    n).preimage
    (PrimaryGeometryAssembly.label nominal) (PrimaryGeometryAssembly.label_injective
      nominal).injOn).product Finset.univ

theorem mem_activeLabels (U : LocalSignedRequest.SlowRegion (2 * h)) (n : ℕ)
    (L : Label B N0) (j : Fin 2) :
    (L, j) ∈ activeLabels U B N0 n ↔ PrimaryGeometryAssembly.label nominal L ∈
      CommonWindow.labels (CoordinateAlgebra.D h) (BaseContextAssembly.geometryBound nominal U) n
        := by
  classical
  simp [activeLabels]

theorem physicalPosition_bound (U : LocalSignedRequest.SlowRegion (2 * h)) (n : ℕ)
    {x : LocalSignedRequest.Point} (hx : x ∈ (BaseContextAssembly.nativeStrip nominal U).domain) :
    ∀ j, |physicalPosition n x j| ≤ BaseContextAssembly.geometryBound nominal U := by
  have hb := (BaseContextAssembly.native_geometry nominal U Unit).bounded ()
    (BaseContextAssembly.slowCoordinates x) (BaseContextAssembly.slowCoordinates_maps nominal U hx)
  have hR : |x.1| ≤ BaseContextAssembly.geometryBound nominal U := by
    exact (norm_fst_le (BaseContextAssembly.slowCoordinates x)).trans hb
  have hZ : |x.2.1.2| ≤ BaseContextAssembly.geometryBound nominal U := by
    exact (norm_fst_le (BaseContextAssembly.slowCoordinates x).2).trans
      ((norm_snd_le (BaseContextAssembly.slowCoordinates x)).trans hb)
  have hT : |x.2.1.1| ≤ BaseContextAssembly.geometryBound nominal U := by
    exact (norm_snd_le (BaseContextAssembly.slowCoordinates x).2).trans
      ((norm_snd_le (BaseContextAssembly.slowCoordinates x)).trans hb)
  have hs : Real.sqrt (ChartScales.Q n) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (ChartScales.Q_le_one n)
  have hD : 0 ≤ CoordinateAlgebra.D h := by
    unfold CoordinateAlgebra.D
    linarith [outgoing.data.h_lt_half]
  have hd := Real.rpow_le_one (ChartScales.Q_pos n).le (ChartScales.Q_le_one n) hD
  intro j
  fin_cases j
  · change |Real.sqrt (ChartScales.Q n) * x.1| ≤ _
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_of_le_one_left (abs_nonneg x.1) hs).trans hR
  · change |ChartScales.Q n ^ CoordinateAlgebra.D h * x.2.1.2| ≤ _
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)]
    exact (mul_le_of_le_one_left (abs_nonneg x.2.1.2) hd).trans hZ
  · change |ChartScales.Q n * x.2.1.1| ≤ _
    rw [abs_mul, abs_of_pos (ChartScales.Q_pos n)]
    exact (mul_le_of_le_one_left (abs_nonneg x.2.1.1) (ChartScales.Q_le_one n)).trans hT

theorem activeLabels_cover (n : ℕ) {x : LocalSignedRequest.Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
    (L : Label B N0) (j : Fin 2)
    (hm : (physicalScale n x, physicalPosition n x) ∈
      PhysicalWaveSum.labelRegion (CoordinateAlgebra.D h)
        (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j)) :
    (L, j) ∈ activeLabels standardRegion B N0 n := by
  apply (mem_activeLabels standardRegion n L j).mpr
  have hr := (BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp hx
  have hq := standardRegion.q_mem x.2.1 hr.1
  change SimilarityCoordinates.coordinateQ (2 * h) x.2.1 ∈ Icc (1 / 2 : ℝ) 2 at hq
  have hl : ChartScales.Q n / 2 ≤ physicalScale n x := by
    dsimp only [physicalScale]
    have hh := mul_le_mul_of_nonneg_left hq.1 (ChartScales.Q_pos n).le
    convert! hh using 1; ring
  have hu : physicalScale n x ≤ 2 * ChartScales.Q n := by
    have hh := mul_le_mul_of_nonneg_left hq.2 (ChartScales.Q_pos n).le
    simpa only [physicalScale, standardRegion, ActualSignedGeometry.standardSlowRegion, mul_comm]
      using hh
  have hp : 0 < physicalScale n x := lt_of_lt_of_le (div_pos (ChartScales.Q_pos n) (by norm_num)) hl
  exact CommonWindow.active_label_mem hp hl hu L.val.property.1 (physicalPosition_bound
    standardRegion n hx) hm

end ActualFiniteFamily

section ActualCoefficients

open Set Function Filter
open scoped ContDiff Topology BigOperators

variable {B N0 : ℕ}

abbrev FullPoint := LocalSignedRequest.Point × ℝ

noncomputable def nativeSlow (L : Label B N0) (x : AbsolutePoint) : PhaseCalculus.Slow :=
  (x.1.1 / Real.sqrt (ChartScales.Q (BaseChartJets.cellBand L)),
    (x.1.2.1 / ChartScales.Q (BaseChartJets.cellBand L) ^ CoordinateAlgebra.D h,
      x.1.2.2 / ChartScales.Q (BaseChartJets.cellBand L)))

theorem nativeSlow_smooth (L : Label B N0) : ContDiff ℝ ∞ (nativeSlow L) :=
  (contDiff_fst.fst.div_const _).prodMk
    ((contDiff_fst.snd.fst.div_const _).prodMk (contDiff_fst.snd.snd.div_const _))

theorem nativeSlow_toAbsolute (L : Label B N0) (x : LocalSignedRequest.Point) :
    nativeSlow L (toAbsolute (BaseChartJets.cellBand L) x) = BaseContextAssembly.slowCoordinates x
      := by
  have hq := (ChartScales.Q_pos (BaseChartJets.cellBand L)).ne'
  have hs := (Real.sqrt_pos.mpr (ChartScales.Q_pos (BaseChartJets.cellBand L))).ne'
  have hd := (Real.rpow_pos_of_pos (ChartScales.Q_pos (BaseChartJets.cellBand L))
    (CoordinateAlgebra.D h)).ne'
  simp [nativeSlow, toAbsolute, BaseContextAssembly.slowCoordinates_apply, hq, hs, hd]

noncomputable def absoluteAmplitude (j : Fin 2) (L : Label B N0) (x : AbsolutePoint) :
    HarmonicCalculus.ComplexVector :=
  ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h) •
    uncutAmplitude j L (nativeSlow L x) x.2

noncomputable def absolutePressure (j : Fin 2) (L : Label B N0) (x : AbsolutePoint) : ℂ :=
  ChartScales.Q (BaseChartJets.cellBand L) ^ (-(2 * CoordinateAlgebra.A h)) •
    uncutPressure j L (nativeSlow L x) x.2

noncomputable def absolutePhase (j : Fin 2) (L : Label B N0) (x : AbsolutePoint × ℝ) : ℝ :=
  (PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared j L : ℝ) * x.2
    +
    ChartScales.carrier h (BaseChartJets.cellBand L) * periodicPhase j L (nativeSlow L x.1) x.1.2

noncomputable def chartCoefficients (j : Fin 2) (L : Label B N0) :
    LinearWaveBounds.WaveCoefficients FullPoint where
  radius _ x := x.1.1
  radialBase n x := BaseContextAssembly.radialBase certificate modulation upper B n x.1
  frequencyBase n x := BaseContextAssembly.frequencyBase certificate modulation upper B n x.1
  axialBase n x := BaseContextAssembly.axialBase certificate modulation upper B n x.1
  phase n x := absolutePhase j L (toAbsolute n x.1, x.2) / ChartScales.carrier h n
  amplitude n x := ChartScales.Q n ^ CoordinateAlgebra.A h • absoluteAmplitude j L (toAbsolute n
    x.1)
  pressure n x := ChartScales.Q n ^ (2 * CoordinateAlgebra.A h) • absolutePressure j L (toAbsolute
    n x.1)
  frequency n := (ChartScales.carrier h n : ℝ)

noncomputable def chartCutoff (j : Fin 2) (L : Label B N0) (n : ℕ) (x : FullPoint) : ℝ :=
  periodicGaussian j L (toAbsolute n x.1).2

noncomputable def piece (U : LocalSignedRequest.SlowRegion (2 * h)) (j : Fin 2) (L : Label B N0) :
    PrimaryPiece FullPoint where
  strip := HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)
  directions := PrimaryResidualClass.directions (commonContext B)
  coefficients := chartCoefficients j L
  cutoff := chartCutoff j L

theorem chartCoefficients_frequency_pos (j : Fin 2) (L : Label B N0) (n : ℕ) :
    0 < (chartCoefficients j L).frequency n :=
  Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h n)

theorem chartCoefficients_phase (j : Fin 2) (L : Label B N0) (n : ℕ) (x : FullPoint) :
    (chartCoefficients j L).frequency n * (chartCoefficients j L).phase n x =
      absolutePhase j L (toAbsolute n x.1, x.2) := by
  exact mul_div_cancel₀ _ (chartCoefficients_frequency_pos j L n).ne'

theorem chartCoefficients_matches (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) :
    PrimaryResidualClass.Matches (BaseContextAssembly.nativeStrip nominal U) (commonContext B)
      (chartCoefficients j L) := by
  refine ⟨rfl, rfl, ?_⟩
  intro n
  funext x i
  fin_cases i <;> rfl

theorem chartCoefficients_angular (j : Fin 2) (L : Label B N0) :
    PrimaryResidualClass.AngularData (chartCoefficients j L) (chartCutoff j L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp only [chartCoefficients, chartCutoff]
    exact PrimaryResidualClass.invariant_fst (D := LocalSignedRequest.Point) _
  · intro n
    dsimp only [chartCoefficients, chartCutoff]
    exact PrimaryResidualClass.invariant_fst (D := LocalSignedRequest.Point) _
  · intro n
    dsimp only [chartCoefficients, chartCutoff]
    exact PrimaryResidualClass.invariant_fst (D := LocalSignedRequest.Point) _
  · intro n
    dsimp only [chartCoefficients, chartCutoff]
    exact PrimaryResidualClass.invariant_fst (D := LocalSignedRequest.Point) _
  · intro n
    refine ⟨(PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared j L
      : ℝ) /
      ChartScales.carrier h n, ?_⟩
    intro x t
    simp only [chartCoefficients, absolutePhase, Prod.fst_add, Prod.smul_fst, smul_zero, add_zero,
      Prod.snd_add, Prod.smul_snd,
      smul_eq_mul, mul_one]
    ring
  · intro n x t
    simp only [chartCoefficients, Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]
  · intro n x t
    simp only [chartCoefficients, Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]
  · intro n x t
    simp only [chartCutoff, Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]

theorem chartCoefficients_carrier (j : Fin 2) (L : Label B N0) (n : ℕ) (x : FullPoint) :
    HarmonicCalculus.carrier ((chartCoefficients j L).frequency n) ((chartCoefficients j L).phase
      n) x =
      HarmonicCalculus.carrier 1 (absolutePhase j L) (toAbsolute n x.1, x.2) := by
  unfold HarmonicCalculus.carrier HarmonicCalculus.phaseFactor
  congr 1
  have he := congrArg Complex.ofReal (chartCoefficients_phase j L n x)
  push_cast at he
  calc
    _ = ((chartCoefficients j L).frequency n : ℂ) * ((chartCoefficients j L).phase n x : ℂ) *
      Complex.I := by ring
    _ = _ := by rw [he]; simp; ring

noncomputable def absoluteTangent (j : Fin 2) (L : Label B N0) (x : AbsolutePoint × ℝ) : Fin 3 → ℝ
  :=
  fun i => (HarmonicCalculus.vectorMode 1 (absolutePhase j L)
    (fun z => periodicGaussian j L z.1.2 • absoluteAmplitude j L z.1) x i).re

noncomputable def absolutePressureMode (j : Fin 2) (L : Label B N0) (x : AbsolutePoint × ℝ) : ℝ :=
  (HarmonicCalculus.mode 1 (absolutePhase j L)
    (fun z => periodicGaussian j L z.1.2 • absolutePressure j L z.1) x).re

theorem piece_tangent_representation (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) (x : FullPoint) :
    (piece U j L).tangentVelocity n x =
      ChartScales.Q n ^ CoordinateAlgebra.A h • absoluteTangent j L (toAbsolute n x.1, x.2) := by
  funext i
  simp only [PrimaryPiece.tangentVelocity, piece, HarmonicCalculus.vectorMode,
    HarmonicCalculus.mode,
    LinearWaveBounds.WaveCoefficients.withCutoff]
  rw [chartCoefficients_carrier]
  simp only [absoluteTangent, HarmonicCalculus.vectorMode, HarmonicCalculus.mode,
    chartCutoff, chartCoefficients, Pi.smul_apply, Complex.real_smul, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem piece_pressure_representation (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) (x : FullPoint) :
    (piece U j L).pressure n x =
      ChartScales.Q n ^ (2 * CoordinateAlgebra.A h) * absolutePressureMode j L (toAbsolute n x.1,
        x.2) := by
  simp only [PrimaryPiece.pressure, PrimaryPiece.exactCoefficients, piece,
    LinearWaveBounds.WaveCoefficients.corrected, LinearWaveBounds.WaveCoefficients.addAmplitude,
    LinearWaveBounds.WaveCoefficients.withCutoff, HarmonicCalculus.mode]
  rw [chartCoefficients_carrier]
  simp only [absolutePressureMode, HarmonicCalculus.mode, chartCutoff, chartCoefficients,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem absoluteTangent_eq (j : Fin 2) (L : Label B N0) (x : AbsolutePoint × ℝ)
    (hx : PrimaryTargetBounds.profileRadius h (nativeSlow L x.1) ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)) :
    absoluteTangent j L x = physicalTangentMode j L (nativeSlow L x.1) x.1.2 x.2 := by
  funext i
  simp only [absoluteTangent, absoluteAmplitude, HarmonicCalculus.vectorMode, HarmonicCalculus.mode,
    physicalTangentMode, tangentMode, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  have hc := congrFun (periodic_cutoff_amplitude j L (nativeSlow L x.1) hx x.1.2) i
  simp only [Pi.smul_apply, Complex.real_smul] at hc
  unfold absolutePhase
  rw [mul_left_comm, hc]
  simp [Complex.mul_re, HarmonicCalculus.carrier]
  ring


theorem nativeSlow_toAbsolute_eq_slowChange (L : Label B N0) (n : ℕ)
    (x : LocalSignedRequest.Point) :
    nativeSlow L (toAbsolute n x) =
      ActualSignedGeometry.slowChange h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand L))
        (BaseContextAssembly.slowCoordinates x) := by
  simp only [nativeSlow, toAbsolute, ActualSignedGeometry.slowChange_apply,
    PhysicalParticularWave.ratioPower, Real.rpow_one, ← Real.sqrt_eq_rpow,
    BaseContextAssembly.slowCoordinates_apply]
  ext <;> ring

theorem periodicClock_toAbsolute (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (Y : TorusInverse.Plane) :
    PeriodicPhaseAssembly.periodicClock (geometry j L) (clockWindow L).cutoff
      ((CommonCoverSolve.coverPower (CommonWindow.index h n)).symm Y) =
    PeriodicPhaseAssembly.periodicClock
      (ActualSignedGeometry.slotGeometry slots vectors_det
        (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j) 0)
      (clockWindow L).cutoff
      (CommonCoverSolve.coverPower (ChartScales.nativeIndex h (BaseChartJets.cellBand L) -
        CommonWindow.index h n) Y) := by
  have hg : geometry j L = CopySolveCompatibility.refineGeometry
      (ActualSignedGeometry.slotGeometry slots vectors_det
        (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j) 0)
      (ChartScales.nativeIndex h (BaseChartJets.cellBand L)) := by
    rw [ActualSignedGeometry.slotGeometry_refine]
    rfl
  rw [hg, PeriodicPhaseAssembly.periodicClock_refine]
  congr 1
  have he : ChartScales.nativeIndex h (BaseChartJets.cellBand L) =
      (ChartScales.nativeIndex h (BaseChartJets.cellBand L) - CommonWindow.index h n) +
        CommonWindow.index h n := by omega
  rw [he, CopySolveCompatibility.coverPower_add, ContinuousLinearEquiv.apply_symm_apply]
  simp only [Nat.add_sub_cancel]

theorem chartCoefficients_phase_view (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (x : FullPoint) :
    (chartCoefficients j L).phase n x =
      ActualSignedGeometry.preparedViewPhase certificate modulation slots (choice B N0).prepared
        j L n (CommonWindow.index h n) (PhysicalResidualTZ.swapCylinder x) := by
  have hp := PrimaryGeometryAssembly.carrier_mul_phase_p certificate modulation (choice B
    N0).prepared
    slots.radius_pos j L
  change (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ) *
    (phases B N0 j).phase.p L = _ at hp
  have hs := nativeSlow_toAbsolute_eq_slowChange L n x.1
  dsimp only [chartCoefficients, absolutePhase, periodicPhase]
  rw [hs]
  change (_ + (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ) *
    (_ + _ - PeriodicPhaseAssembly.periodicClock (geometry j L) (clockWindow L).cutoff
      ((CommonCoverSolve.coverPower (CommonWindow.index h n)).symm x.1.2.2) * _)) /
      (ChartScales.carrier h n : ℝ) = _
  rw [periodicClock_toAbsolute j L n hi]
  rw [← hp]
  simp only [ActualSignedGeometry.preparedViewPhase, ActualSignedGeometry.preparedPhase,
    ActualSignedGeometry.periodicPhase, PhaseCalculus.phase,
    PhysicalParticularWave.cylinderChange_apply, PhysicalParticularWave.chartChange_apply,
    PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply,
    ActualSignedGeometry.slowChange_apply]
  change _ = ((ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ) / (ChartScales.carrier h n :
    ℝ)) *
    ((phases B N0 j).phase.p L * x.2 +
      ((phases B N0 j).phase.pz L / (phases B N0 j).phase.epsilon L) * _ +
      (phases B N0 j).phase.x0 L * _ -
      PeriodicPhaseAssembly.periodicClock
        (ActualSignedGeometry.slotGeometry slots vectors_det
          (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j) 0)
        (clockWindow L).cutoff
        (CommonCoverSolve.coverPower (ChartScales.nativeIndex h (BaseChartJets.cellBand L) -
          CommonWindow.index h n) x.1.2.2) * _)
  simp only [phases, BaseContextAssembly.slowCoordinates_apply]
  ring


theorem chart_nativePoint (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : LocalSignedRequest.Point) :
    (nativeSlow L (toAbsolute n x), (geometry j L).coordinates k (toAbsolute n x).2) =
      ActualSignedGeometry.copyPoint slots vectors_det
        (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j)
        n (CommonWindow.index h n) k (ActualSignedGeometry.meanEquiv.symm x) := by
  apply Prod.ext
  · exact nativeSlow_toAbsolute_eq_slowChange L n x
  · exact chartGeometry_coordinates n j L hi k x.2.2

theorem chartCoefficients_amplitude_copies (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (x : FullPoint) :
    (chartCoefficients j L).amplitude n x =
      (ChartScales.Q n ^ CoordinateAlgebra.A h *
        ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h)) •
      (∑' k : TorusInverse.Frequency, CurlClassBounds.complexify (attachedRawVelocity j L
        (ActualSignedGeometry.copyPoint slots vectors_det
          (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j)
          n (CommonWindow.index h n) k (ActualSignedGeometry.meanEquiv.symm x.1)))) := by
  simp only [chartCoefficients, absoluteAmplitude, uncutAmplitude, smul_smul]
  congr 1
  apply tsum_congr
  intro k
  rw [chart_nativePoint j L n hi]

theorem chartCoefficients_pressure_copies (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (x : FullPoint) :
    (chartCoefficients j L).pressure n x =
      (ChartScales.Q n ^ (2 * CoordinateAlgebra.A h) *
        ChartScales.Q (BaseChartJets.cellBand L) ^ (-(2 * CoordinateAlgebra.A h))) •
      (∑' k : TorusInverse.Frequency, attachedRawPressure j L
        (ActualSignedGeometry.copyPoint slots vectors_det
          (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j)
          n (CommonWindow.index h n) k (ActualSignedGeometry.meanEquiv.symm x.1))) := by
  simp only [chartCoefficients, absolutePressure, uncutPressure, smul_smul]
  congr 1
  apply tsum_congr
  intro k
  rw [chart_nativePoint j L n hi]

end ActualCoefficients

section SharedFactorization

open Set Function
open scoped BigOperators
variable {B N0 : ℕ}

/-- The same periodic cutoff identity applies to a primary or signed native
coefficient; only the actual native support is used. -/
theorem periodic_cutoff_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow) (Y : TorusInverse.Plane)
    (f : TorusInverse.Frequency → E)
    (hs : ∀ k, f k ≠ 0 → (geometry j L).coordinates k Y ∈ (clockWindow L).core) :
    periodicGaussian j L Y • (∑' k, f k) =
      ∑' k, gaussian L (p, (geometry j L).coordinates k Y) • f k := by
  rw [← tsum_const_smul'']
  apply tsum_congr
  intro k
  by_cases hz : f k = 0
  · simp only [hz, smul_zero]
  · rw [periodicGaussian_eq_on_core j L p Y k (hs k hz)]

/-- A shared signed scalar stays outside the genuine lattice sum. It may
be the current-state request evaluated at the common chart point. -/
theorem periodic_cutoff_scalar_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow) (Y : TorusInverse.Plane)
    (a : ℝ) (f : TorusInverse.Frequency → E)
    (hs : ∀ k, f k ≠ 0 → (geometry j L).coordinates k Y ∈ (clockWindow L).core) :
    periodicGaussian j L Y • (a • (∑' k, f k)) =
      ∑' k, a • (gaussian L (p, (geometry j L).coordinates k Y) • f k) := by
  rw [smul_comm, periodic_cutoff_sum j L p Y f hs, ← tsum_const_smul'']

end SharedFactorization

end ActualPrimary

end NavierStokes.CorrectionInitialization
