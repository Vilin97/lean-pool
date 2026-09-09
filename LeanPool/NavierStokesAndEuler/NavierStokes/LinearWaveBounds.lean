/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LinearWaveResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.CurlClassBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.GaussianTailFlat

/-!
# Weighted bounds for the actual linear wave remainder

The classes in this file bound `iteratedFDeriv` of the actual stripped
coefficients uniformly in the band.  Radial graph differentiation, axial
rescaling, and the fast direction are kept explicit.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.LinearWaveBounds

open WeightedClasses HarmonicCalculus Set Filter
open scoped ContDiff Topology BigOperators


variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem class_congr {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f g : ℕ → D → E} (hf : MemClass s w α f)
    (he : ∀ n, EqOn (f n) (g n) s.domain) : MemClass s w α g := by
  refine ⟨hf.weight_nonneg, fun n => (hf.smooth n).congr (he n).symm, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have hlocal : f n =ᶠ[𝓝 x] g n := eventually_of_mem (s.isOpen_domain.mem_nhds hx) (he n)
  have hlocal' : f n =ᶠ[𝓝[univ] x] g n := by simpa only [nhdsWithin_univ] using hlocal
  have hjet := hlocal'.iteratedFDerivWithin_eq (𝕜 := ℝ) hlocal.self_of_nhds j
  simp only [iteratedFDerivWithin_univ] at hjet
  rw [← hjet]
  exact hb n x hx j hj

theorem class_neg {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {f : ℕ → D → E}
    (hf : MemClass s w α f) : MemClass s w α (fun n x => -f n x) := by
  simpa using hf.map (-ContinuousLinearMap.id ℝ E)

theorem class_sub {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {f g : ℕ → D → E}
    (hf : MemClass s w α f) (hg : MemClass s w α g) :
    MemClass s w α (fun n x => f n x - g n x) := by
  simpa only [sub_eq_add_neg] using hf.add (class_neg hg)

theorem unweighted_mul {s : StripData D} {α β : ℝ} {f g : ℕ → D → ℝ}
    (hf : UnweightedClass s α f) (hg : UnweightedClass s β g) :
    UnweightedClass s (α + β) (fun n x => f n x * g n x) := by
  simpa only [UnweightedClass, one_mul] using MemClass.mul hf hg

theorem unweighted_smul {s : StripData D} {w : ℕ → D → ℝ} {α β : ℝ}
    {f : ℕ → D → ℝ} {g : ℕ → D → E}
    (hf : UnweightedClass s α f) (hg : MemClass s w β g) :
    MemClass s w (α + β) (fun n x => f n x • g n x) := by
  simpa only [UnweightedClass, one_mul] using MemClass.smul hf hg

theorem real_mul_complex {s : StripData D} {w : ℕ → D → ℝ} {α β : ℝ}
    {f : ℕ → D → ℝ} {g : ℕ → D → ℂ}
    (hf : UnweightedClass s α f) (hg : MemClass s w β g) :
    MemClass s w (α + β) (fun n x => (f n x : ℂ) * g n x) := by
  simpa only [Complex.real_smul] using unweighted_smul hf hg

theorem complex_mul_real {s : StripData D} {w : ℕ → D → ℝ} {α β : ℝ}
    {f : ℕ → D → ℂ} {g : ℕ → D → ℝ}
    (hf : MemClass s w α f) (hg : UnweightedClass s β g) :
    MemClass s w (α + β) (fun n x => f n x * (g n x : ℂ)) := by
  simpa only [add_comm β α, mul_comm] using real_mul_complex hg hf

theorem constant_complex_mul {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → ℂ} (hf : MemClass s w α f) (c : ℂ) :
    MemClass s w α (fun n x => c * f n x) := by
  exact hf.map ((ContinuousLinearMap.mul ℝ ℂ) c)

theorem constant_real_mul {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → ℝ} (hf : MemClass s w α f) (c : ℝ) :
    MemClass s w α (fun n x => c * f n x) := by
  simpa only [_root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    using hf.map (c • ContinuousLinearMap.id ℝ ℝ)

theorem band_epsilon (s : StripData D) : BandBound s 1 s.epsilon := by
  simpa only [Real.rpow_one] using bandBound_rpow s 1

theorem mean_unweighted {s : StripData D} {α : ℝ} {f : ℕ → D → E}
    (hf : MeanClass s α f) (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) :
    UnweightedClass s α f :=
  hf.mono_weight (fun _ _ _ => zero_le_one) (fun _ x hx => hζ x hx)

/-- Raw direction data. Its numerical and class hypotheses are separate. -/
structure GraphDirections (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] where
  /-- Radial of `GraphDirections`, of type `D`. -/
  radial : D
  /-- Auxiliary of `GraphDirections`, of type `D`. -/
  auxiliary : D
  /-- Axial of `GraphDirections`, of type `D`. -/
  axial : D
  /-- Angular of `GraphDirections`, of type `D`. -/
  angular : D
  /-- Slow of `GraphDirections`, of type `D`. -/
  slow : D
  /-- Fast of `GraphDirections`, of type `D`. -/
  fast : D
  /-- Radial scale of `GraphDirections`, of type `ℕ → ℝ`. -/
  radialScale : ℕ → ℝ
  /-- Fast scale of `GraphDirections`, of type `ℕ → ℝ`. -/
  fastScale : ℕ → ℝ
  /-- Radial profile of `GraphDirections`, of type `D → ℝ`. -/
  radialProfile : D → ℝ

namespace GraphDirections

/-- Radial field, given by `d.radial + d.radialScale n • (d.radialProfile x • d.auxiliary)`. -/
noncomputable def radialField (d : GraphDirections D) (n : ℕ) (x : D) : D :=
  d.radial + d.radialScale n • (d.radialProfile x • d.auxiliary)

/-- Axial field, given by `s.epsilon n • d.axial`. -/
noncomputable def axialField (d : GraphDirections D) (s : StripData D) (n : ℕ) (_ : D) : D :=
  s.epsilon n • d.axial

/-- Fast field, given by `d.fastScale n • d.fast`. -/
noncomputable def fastField (d : GraphDirections D) (n : ℕ) (_ : D) : D :=
  d.fastScale n • d.fast

/-- Dr, defined pointwise by `along (d.radialField n) (f n)`. -/
noncomputable def Dr (d : GraphDirections D) (f : ℕ → D → E) : ℕ → D → E :=
  fun n => along (d.radialField n) (f n)

/-- Dz, defined pointwise by `along (d.axialField s n) (f n)`. -/
noncomputable def Dz (d : GraphDirections D) (s : StripData D) (f : ℕ → D → E) : ℕ → D → E :=
  fun n => along (d.axialField s n) (f n)

/-- Dt, defined pointwise by `along (fun _ => d.slow) (f n)`. -/
noncomputable def Dt (d : GraphDirections D) (f : ℕ → D → E) : ℕ → D → E :=
  fun n => along (fun _ => d.slow) (f n)

/-- Dfast, defined pointwise by `along (d.fastField n) (f n)`. -/
noncomputable def Dfast (d : GraphDirections D) (f : ℕ → D → E) : ℕ → D → E :=
  fun n => along (d.fastField n) (f n)

theorem Dr_eq (d : GraphDirections D) (f : ℕ → D → E) :
    d.Dr f = graphDerivative d.radialScale d.radialProfile d.radial d.auxiliary f := by
  funext n x
  exact (graphDerivative_eq_along _ _ _ _ _ n x).symm

theorem Dr_mem {s : StripData D} {w : ℕ → D → ℝ} {α κ : ℝ}
    (d : GraphDirections D) {f : ℕ → D → E} (hf : MemClass s w α f)
    (hρ : UnweightedClass s 0 (fun _ => d.radialProfile))
    (hM : BandBound s (-κ) d.radialScale) (hκ : 0 ≤ κ) :
    MemClass s w (α - κ) (d.Dr f) := by
  rw [d.Dr_eq]
  exact hf.graphDerivative hρ hM hκ d.radial d.auxiliary

theorem Dz_mem {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    (d : GraphDirections D) {f : ℕ → D → E} (hf : MemClass s w α f) :
    MemClass s w (α + 1) (d.Dz s f) := by
  have hh := (hf.directional d.axial).band_smul (band_epsilon s)
  unfold Dz axialField along
  simpa only [map_smul] using hh

theorem Dt_mem {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    (d : GraphDirections D) {f : ℕ → D → E} (hf : MemClass s w α f) :
    MemClass s w α (d.Dt f) := hf.directional d.slow

theorem Dfast_mem {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    (d : GraphDirections D) {f : ℕ → D → E} (hf : MemClass s w α f)
    (hfast : BandBound s 0 d.fastScale) : MemClass s w α (d.Dfast f) := by
  have hh := (hf.directional d.fast).band_smul hfast
  unfold Dfast fastField along
  simpa only [map_smul, add_zero] using hh

/-- Base fields independent of the auxiliary coordinate incur no graph loss. -/
theorem Dr_base_mem {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    (d : GraphDirections D) {f : ℕ → D → E} (hf : MemClass s w α f)
    (haux : ∀ n x, x ∈ s.domain → fderiv ℝ (f n) x d.auxiliary = 0) :
    MemClass s w α (d.Dr f) := by
  apply class_congr (hf.directional d.radial)
  intro n x hx
  simp [Dr, radialField, along, haux n x hx]

end GraphDirections

theorem frequency_mul {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → ℂ} {kfreq : ℕ → ℝ} (hf : MemClass s w α f)
    (hkfreq : BandBound s (-(1 / 2 : ℝ)) kfreq) :
    MemClass s w (α - 1 / 2) (fun n x => phaseFactor (kfreq n) * f n x) := by
  have hh := (constant_complex_mul hf Complex.I).band_smul hkfreq
  simpa only [sub_eq_add_neg, Complex.real_smul, phaseFactor, mul_assoc] using hh

/-- Families of actual phase, base, velocity, and pressure coefficients. -/
structure WaveCoefficients (D : Type*) where
  /-- Radius of `WaveCoefficients`, of type `ℕ → D → ℝ`. -/
  radius : ℕ → D → ℝ
  /-- Radial base of `WaveCoefficients`, of type `ℕ → D → ℝ`. -/
  radialBase : ℕ → D → ℝ
  /-- Frequency base of `WaveCoefficients`, of type `ℕ → D → ℝ`. -/
  frequencyBase : ℕ → D → ℝ
  /-- Axial base of `WaveCoefficients`, of type `ℕ → D → ℝ`. -/
  axialBase : ℕ → D → ℝ
  /-- Phase of `WaveCoefficients`, of type `ℕ → D → ℝ`. -/
  phase : ℕ → D → ℝ
  /-- Amplitude of `WaveCoefficients`, of type `ℕ → D → ComplexVector`. -/
  amplitude : ℕ → D → ComplexVector
  /-- Pressure field of `WaveCoefficients`, of type `ℕ → D → ℂ`. -/
  pressure : ℕ → D → ℂ
  /-- Frequency of `WaveCoefficients`, of type `ℕ → ℝ`. -/
  frequency : ℕ → ℝ

namespace WaveCoefficients

/-- Normal, given by `phaseNormal (a.radius n) (d.radialField n) (fun _ => d.angular)
(d.axialField s n) (a.phase n)`. -/
noncomputable def normal (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (n : ℕ) : D → EuclideanSpace ℝ (Fin 3) :=
  phaseNormal (a.radius n) (d.radialField n) (fun _ => d.angular) (d.axialField s n) (a.phase n)

/-- Defect, constructed using `LinearWaveResidual.materialPhaseDefect`. -/
noncomputable def defect (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (n : ℕ) : D → ℝ :=
  LinearWaveResidual.materialPhaseDefect (a.radius n) (a.radialBase n) (a.frequencyBase n)
    (a.axialBase n) (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (LinearWaveResidual.timeDirection (s.epsilon n) (d.fastField n) (fun _ => d.slow)) (a.phase n)

/-- Remainder, constructed using `LinearWaveResidual.remainder`. -/
noncomputable def remainder (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (n : ℕ) : D → ComplexVector :=
  LinearWaveResidual.remainder (s.epsilon n) (a.frequency n) (a.radius n) (a.radialBase n)
    (a.frequencyBase n) (a.axialBase n) (d.radialField n) (fun _ => d.angular)
    (d.axialField s n) (d.fastField n) (fun _ => d.slow) (a.phase n) (a.amplitude n) (a.pressure n)

/-- Principal, constructed using `LinearWaveResidual.principal`. -/
noncomputable def principal (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (n : ℕ) : D → ComplexVector :=
  LinearWaveResidual.principal (s.epsilon n) (a.frequency n) (a.radius n) (a.frequencyBase n)
    (a.axialBase n) (d.radialField n) (fun _ => d.angular) (d.axialField s n) (d.fastField n)
    (a.phase n) (a.amplitude n) (a.pressure n)

/-- Principal velocity, constructed using `LinearWaveResidual.principal`. -/
noncomputable def principalVelocity (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections
    D)
    (f : ℕ → D → ComplexVector) (n : ℕ) : D → ComplexVector :=
  LinearWaveResidual.principal (s.epsilon n) (a.frequency n) (a.radius n) (a.frequencyBase n)
    (a.axialBase n) (d.radialField n) (fun _ => d.angular) (d.axialField s n) (d.fastField n)
    (a.phase n) (f n) (fun _ => 0)

/-- Add amplitude, given by `{a with amplitude := fun n x => a.amplitude n x + f n x}`. -/
noncomputable def addAmplitude (a : WaveCoefficients D) (f : ℕ → D → ComplexVector) :
    WaveCoefficients D := {a with amplitude := fun n x => a.amplitude n x + f n x}

/-- With cutoff, given by `{ a with amplitude := fun n x => ψ n x • a.amplitude n x pressure :=
fun n x => (ψ n x : ℂ) * a.pressure n x }`. -/
noncomputable def withCutoff (a : WaveCoefficients D) (ψ : ℕ → D → ℝ) : WaveCoefficients D :=
  { a with
    amplitude := fun n x => ψ n x • a.amplitude n x
    pressure := fun n x => (ψ n x : ℂ) * a.pressure n x }

/-- The retained coefficient after cutoff and exact-curl correction.
The two slot tails are not included in this definition. -/
noncomputable def goodCoefficient (a : WaveCoefficients D) (s : StripData D)
    (d : GraphDirections D) (ψ : ℕ → D → ℝ) (f : ℕ → D → ComplexVector)
    (n : ℕ) (x : D) : ComplexVector :=
  a.principalVelocity s d f n x + ((a.withCutoff ψ).addAmplitude f).remainder s d n x

/-- Harmonic residual, constructed using `LinearWaveResidual.linearResidual`. -/
noncomputable def harmonicResidual (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections
    D)
    (n : ℕ) : D → ComplexVector :=
  LinearWaveResidual.linearResidual (s.epsilon n) (a.radius n) (d.radialField n) (fun _ =>
      d.angular)
    (d.axialField s n) (LinearWaveResidual.timeDirection (s.epsilon n) (d.fastField n) (fun _ =>
        d.slow))
    (LinearWaveResidual.complexBase (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase
        n))
    (vectorMode (a.frequency n) (a.phase n) (a.amplitude n))
    (mode (a.frequency n) (a.phase n) (a.pressure n))

end WaveCoefficients

namespace WaveCoefficients

/-- The actual coefficient error from taking the curl of the normalized
harmonic vector potential. -/
noncomputable def curlCorrection (a : WaveCoefficients D) (s : StripData D)
    (d : GraphDirections D) (n : ℕ) : D → ComplexVector :=
  CurlClassBounds.curlRemainder (a.frequency n) (a.radius n) (d.radialField n)
    (fun _ => d.angular) (d.axialField s n)
    (CurlClassBounds.coefficient (a.radius n) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) (a.phase n) (a.amplitude n))

/-- Curl potential, constructed using `CurlClassBounds.vectorPotential`. -/
noncomputable def curlPotential (a : WaveCoefficients D) (s : StripData D)
    (d : GraphDirections D) (n : ℕ) : D → ComplexVector :=
  CurlClassBounds.vectorPotential (a.frequency n) (a.radius n) (d.radialField n)
    (fun _ => d.angular) (d.axialField s n) (a.phase n) (a.amplitude n)

/-- Corrected, given by `(a.withCutoff ψ).addAmplitude ((a.withCutoff ψ).curlCorrection s d)`. -/
noncomputable def corrected (a : WaveCoefficients D) (s : StripData D)
    (d : GraphDirections D) (ψ : ℕ → D → ℝ) : WaveCoefficients D :=
  (a.withCutoff ψ).addAmplitude ((a.withCutoff ψ).curlCorrection s d)

/-- Constructed good, given by `a.goodCoefficient s d ψ ((a.withCutoff ψ).curlCorrection s d)`. -/
noncomputable def constructedGood (a : WaveCoefficients D) (s : StripData D)
    (d : GraphDirections D) (ψ : ℕ → D → ℝ) : ℕ → D → ComplexVector :=
  a.goodCoefficient s d ψ ((a.withCutoff ψ).curlCorrection s d)

end WaveCoefficients

/-- Only primitive coefficient classes and scale bounds are inputs.
No remainder or residual bound occurs in this structure. -/
structure InputBounds (s : StripData D) (P : ℕ → D → ℝ) (α κ : ℝ)
    (d : GraphDirections D) (a : WaveCoefficients D) : Prop where
  loss_nonneg : 0 ≤ κ
  zeta_le_one : ∀ x ∈ s.domain, s.zeta x ≤ 1
  radial_profile : UnweightedClass s 0 (fun _ => d.radialProfile)
  radial_scale : BandBound s (-κ) d.radialScale
  fast_scale : BandBound s 0 d.fastScale
  frequency_scale : BandBound s (-(1 / 2 : ℝ)) a.frequency
  radius : UnweightedClass s 0 a.radius
  inverse_radius : UnweightedClass s 0 (fun n x => (a.radius n x)⁻¹)
  radial_base : UnweightedClass s 1 a.radialBase
  frequency_base : UnweightedClass s 0 a.frequencyBase
  axial_base : UnweightedClass s 0 a.axialBase
  radial_base_aux : ∀ n x, x ∈ s.domain → fderiv ℝ (a.radialBase n) x d.auxiliary = 0
  frequency_base_aux : ∀ n x, x ∈ s.domain → fderiv ℝ (a.frequencyBase n) x d.auxiliary = 0
  axial_base_aux : ∀ n x, x ∈ s.domain → fderiv ℝ (a.axialBase n) x d.auxiliary = 0
  normal : ∀ i, UnweightedClass s 0 (fun n x => a.normal s d n x i)
  defect : UnweightedClass s 1 (a.defect s d)
  amplitude : ∀ i, WaveClass s P α (fun n x => a.amplitude n x i)
  pressure : WaveClass s P (α + 1 / 2) a.pressure

/-- Insert component, given by `ContinuousLinearMap.pi fun j => if j = i then
ContinuousLinearMap.id ℝ ℂ else 0`. -/
noncomputable def insertComponent (i : Fin 3) : ℂ →L[ℝ] ComplexVector :=
  ContinuousLinearMap.pi fun j => if j = i then ContinuousLinearMap.id ℝ ℂ else 0

theorem component_classes {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → ComplexVector} (hf : ∀ i, MemClass s w α (fun n x => f n x i)) :
    MemClass s w α f := by
  have hh := MemClass.sum (s := s) Finset.univ
    (fun i n x => insertComponent i (f n x i)) (hf 0).weight_nonneg
    (fun i _ => (hf i).map (insertComponent i))
  apply class_congr hh
  intro n x _
  ext i
  fin_cases i <;> simp [insertComponent, Fin.sum_univ_three]

theorem angular_classes {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → ComplexVector} (hf : ∀ i, MemClass s w α (fun n x => f n x i)) :
    ∀ i, MemClass s w α (fun n x => angularGenerator (f n x) i) := by
  intro i
  fin_cases i
  · simpa [angularGenerator] using class_neg (hf 1)
  · simpa [angularGenerator] using hf 0
  · simpa [angularGenerator] using (MemClass.zero (α := α) (E := ℂ) (hf 0).weight_nonneg)

namespace InputBounds

variable {s : StripData D} {P : ℕ → D → ℝ} {α κ : ℝ}
  {d : GraphDirections D} {a : WaveCoefficients D}

theorem b_unweighted (h : InputBounds s P α κ d a) :
    UnweightedClass s 1 a.radialBase := h.radial_base

theorem inverse_radius_sq (h : InputBounds s P α κ d a) :
    UnweightedClass s 0 (fun n x => ((a.radius n x) ^ 2)⁻¹) := by
  simpa only [zero_add, pow_two, mul_inv_rev] using unweighted_mul h.inverse_radius h.inverse_radius

theorem base_components (h : InputBounds s P α κ d a) (i : Fin 3) :
    UnweightedClass s 0 (fun n x =>
      LinearWaveResidual.base (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase n) x
          i) := by
  fin_cases i
  · simpa [LinearWaveResidual.base] using h.b_unweighted.mono_exponent (by norm_num : (0 : ℝ) ≤ 1)
  · simpa [LinearWaveResidual.base] using unweighted_mul h.radius h.frequency_base
  · simpa [LinearWaveResidual.base] using h.axial_base

theorem slowTransport_mem (h : InputBounds s P α κ d a) (i : Fin 3) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (fun n x =>
      LinearWaveResidual.slowTransport (s.epsilon n) (a.radialBase n) (a.axialBase n)
        (fun _ => d.slow) (d.radialField n) (d.axialField s n) (a.amplitude n) x i) := by
  have ht := class_neg ((d.Dt_mem (h.amplitude i)).band_smul (band_epsilon s))
  have hr := real_mul_complex h.b_unweighted
    (d.Dr_mem (h.amplitude i) h.radial_profile h.radial_scale h.loss_nonneg)
  have hz := real_mul_complex h.axial_base (d.Dz_mem (h.amplitude i))
  have ht' := ht.mono_exponent (show α + 1 / 2 - 3 * κ ≤ α + 1 by linarith [h.loss_nonneg])
  have hr' := hr.mono_exponent (show α + 1 / 2 - 3 * κ ≤ 1 + (α - κ) by linarith [h.loss_nonneg])
  have hz' := hz.mono_exponent (show α + 1 / 2 - 3 * κ ≤ 0 + (α + 1) by linarith [h.loss_nonneg])
  simpa only [LinearWaveResidual.slowTransport, GraphDirections.Dt, GraphDirections.Dr,
    GraphDirections.Dz, Complex.real_smul, neg_mul] using (ht'.add hr').add hz'

theorem phaseDefect_mem (h : InputBounds s P α κ d a) (i : Fin 3) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (fun n x =>
      phaseFactor (a.frequency n) * Complex.ofReal (a.defect s d n x) * a.amplitude n x i) := by
  have hh := frequency_mul (real_mul_complex h.defect (h.amplitude i)) h.frequency_scale
  have hh' := hh.mono_exponent
    (show α + 1 / 2 - 3 * κ ≤ (1 + α) - 1 / 2 by linarith [h.loss_nonneg])
  simpa only [mul_assoc] using hh'

theorem baseDerivativeRemainder_mem (h : InputBounds s P α κ d a) (i : Fin 3) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (fun n x =>
      LinearWaveResidual.baseDerivativeRemainder (a.radius n) (a.radialBase n)
        (a.frequencyBase n) (a.axialBase n) (d.radialField n) (d.axialField s n)
        (a.amplitude n) x i) := by
  have hbr := d.Dr_base_mem h.b_unweighted h.radial_base_aux
  have h0 := (complex_mul_real (h.amplitude 0) hbr).mono_exponent
    (show α + 1 / 2 - 3 * κ ≤ α + 1 by linarith [h.loss_nonneg])
  have hbinv := unweighted_mul h.b_unweighted h.inverse_radius
  have h1 := (real_mul_complex hbinv (h.amplitude 1)).mono_exponent
    (show α + 1 / 2 - 3 * κ ≤ (1 + 0) + α by linarith [h.loss_nonneg])
  have hz (j : Fin 3) := (complex_mul_real (h.amplitude 2) (d.Dz_mem (h.base_components
      j))).mono_exponent
    (show α + 1 / 2 - 3 * κ ≤ α + (0 + 1) by linarith [h.loss_nonneg])
  fin_cases i
  · simpa [LinearWaveResidual.baseDerivativeRemainder, GraphDirections.Dr, GraphDirections.Dz]
      using h0.add (hz 0)
  · simpa [LinearWaveResidual.baseDerivativeRemainder, GraphDirections.Dz, div_eq_mul_inv]
      using h1.add (hz 1)
  · simpa [LinearWaveResidual.baseDerivativeRemainder, GraphDirections.Dz] using hz 2

theorem pressureGradient_mem (h : InputBounds s P α κ d a) (i : Fin 3) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (fun n x =>
      LinearWaveResidual.strippedPressureGradient (d.radialField n) (d.axialField s n)
        (a.pressure n) x i) := by
  fin_cases i
  · have hh := (d.Dr_mem h.pressure h.radial_profile h.radial_scale h.loss_nonneg).mono_exponent
      (show α + 1 / 2 - 3 * κ ≤ (α + 1 / 2) - κ by linarith [h.loss_nonneg])
    simp only [one_div, Fin.zero_eta, Fin.isValue] at hh ⊢
    exact hh
  · simpa [LinearWaveResidual.strippedPressureGradient] using
      (MemClass.zero (α := α + 1 / 2 - 3 * κ) (E := ℂ) (h.amplitude 0).weight_nonneg)
  · have hh := (d.Dz_mem h.pressure).mono_exponent
      (show α + 1 / 2 - 3 * κ ≤ (α + 1 / 2) + 1 by linarith [h.loss_nonneg])
    simp only [one_div, Fin.reduceFinMk, Fin.isValue] at hh ⊢
    exact hh

theorem viscousRemainder_mem (h : InputBounds s P α κ d a) (i : Fin 3) :
    WaveClass s P (α - 1 / 2 - 3 * κ) (fun n x =>
      LinearWaveResidual.viscousRemainder (a.radius n) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) (a.frequency n) (a.phase n) (a.amplitude n) x i) := by
  have hAi := h.amplitude i
  have hDr := d.Dr_mem hAi h.radial_profile h.radial_scale h.loss_nonneg
  have hDrr := d.Dr_mem hDr h.radial_profile h.radial_scale h.loss_nonneg
  have hDz := d.Dz_mem hAi
  have hDzz := d.Dz_mem hDz
  have hri := real_mul_complex h.inverse_radius hDr
  have hJ := angular_classes h.amplitude
  have hJJ := angular_classes hJ
  have hjj := real_mul_complex h.inverse_radius_sq (hJJ i)
  have hcrossr := real_mul_complex (h.normal 0) hDr
  have hcrossz := real_mul_complex (h.normal 2) hDz
  have hcrossr' : WaveClass s P (α - κ) (fun n x =>
      Complex.ofReal (a.normal s d n x 0) * d.Dr (fun n x => a.amplitude n x i) n x) := by
    simpa only [zero_add] using hcrossr
  have hcrossz' := hcrossz.mono_exponent
    (show α - κ ≤ 0 + (α + 1) by linarith [h.loss_nonneg])
  have hcross := constant_complex_mul
    (frequency_mul (hcrossr'.add hcrossz') h.frequency_scale) 2
  have hNr := d.Dr_mem (h.normal 0) h.radial_profile h.radial_scale h.loss_nonneg
  have hNi := unweighted_mul (h.normal 0) h.inverse_radius
  have hNz := d.Dz_mem (h.normal 2)
  have hNr' : UnweightedClass s (-κ) (d.Dr (fun n x => a.normal s d n x 0)) := by
    simpa only [zero_sub] using hNr
  have hNi' := hNi.mono_exponent (show -κ ≤ 0 + 0 by linarith [h.loss_nonneg])
  have hNz' := hNz.mono_exponent (show -κ ≤ 0 + 1 by linarith [h.loss_nonneg])
  have hdiv := frequency_mul (real_mul_complex ((hNr'.add hNi').add hNz') hAi) h.frequency_scale
  have htheta := constant_complex_mul
    (frequency_mul (real_mul_complex (unweighted_mul (h.normal 1) h.inverse_radius) (hJ i))
      h.frequency_scale) 2
  have hDrr' := hDrr.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ (α - κ) - κ by linarith [h.loss_nonneg])
  have hri' := hri.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ 0 + (α - κ) by linarith [h.loss_nonneg])
  have hDzz' := hDzz.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ (α + 1) + 1 by linarith [h.loss_nonneg])
  have hjj' := hjj.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ 0 + α by linarith [h.loss_nonneg])
  have hcross' := hcross.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ (α - κ) - 1 / 2 by linarith [h.loss_nonneg])
  have hdiv' := hdiv.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ (-κ + α) - 1 / 2 by linarith [h.loss_nonneg])
  have htheta' := htheta.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ ((0 + 0) + α) - 1 / 2 by linarith [h.loss_nonneg])
  have hh := (((((hDrr'.add hri').add hDzz').add hjj').add hcross').add hdiv').add htheta'
  simpa only [LinearWaveResidual.viscousRemainder, GraphDirections.Dr, GraphDirections.Dz,
    WaveCoefficients.normal, Complex.real_smul, div_eq_mul_inv, Complex.ofReal_mul,
    Complex.ofReal_inv, mul_assoc] using hh

theorem viscousPart_mem (h : InputBounds s P α κ d a) (i : Fin 3) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (fun n x => (s.epsilon n : ℂ) *
      LinearWaveResidual.viscousRemainder (a.radius n) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) (a.frequency n) (a.phase n) (a.amplitude n) x i) := by
  have hh := (h.viscousRemainder_mem i).band_smul (band_epsilon s)
  have he : (α - 1 / 2 - 3 * κ) + 1 = α + 1 / 2 - 3 * κ := by ring
  rw [he] at hh
  simpa only [Complex.real_smul] using hh

/-- Every concrete term of (31), including the two frame corrections, has
the claimed all-jet weighted bound. -/
theorem remainder_components (h : InputBounds s P α κ d a) (i : Fin 3) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (fun n x => a.remainder s d n x i) := by
  have hh := class_sub
    ((((h.slowTransport_mem i).add (h.phaseDefect_mem i)).add
      (h.baseDerivativeRemainder_mem i)).add (h.pressureGradient_mem i)) (h.viscousPart_mem i)
  simpa only [WaveCoefficients.remainder, WaveCoefficients.defect, LinearWaveResidual.remainder]
      using hh

theorem remainder_class (h : InputBounds s P α κ d a) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (a.remainder s d) :=
  component_classes h.remainder_components

theorem normal_norm_sq (h : InputBounds s P α κ d a) :
    UnweightedClass s 0 (fun n x => ‖a.normal s d n x‖ ^ 2) := by
  have hsq (i : Fin 3) : UnweightedClass s 0 (fun n x => (a.normal s d n x i) ^ 2) := by
    simpa only [zero_add, pow_two] using unweighted_mul (h.normal i) (h.normal i)
  apply class_congr (((hsq 0).add (hsq 1)).add (hsq 2))
  intro n x _
  exact (PhaseCalculus.vec3_norm_sq (a.normal s d n x)).symm

theorem shear_mem (h : InputBounds s P α κ d a) {β : ℝ} {f : ℕ → D → ComplexVector}
    (hf : ∀ i, WaveClass s P β (fun n x => f n x i)) (i : Fin 3) :
    WaveClass s P β (fun n x =>
      LinearWaveResidual.shear (a.radius n) (a.frequencyBase n) (a.axialBase n)
        (d.radialField n) (f n) x i) := by
  have hFr := d.Dr_base_mem h.frequency_base h.frequency_base_aux
  have hGr := d.Dr_base_mem h.axial_base h.axial_base_aux
  have htheta : UnweightedClass s 0 (fun n x =>
      2 * a.frequencyBase n x + a.radius n x * d.Dr a.frequencyBase n x) := by
    have hprod : UnweightedClass s 0 (fun n x => a.radius n x * d.Dr a.frequencyBase n x) := by
      simpa only [zero_add] using unweighted_mul h.radius hFr
    exact (constant_real_mul h.frequency_base 2).add hprod
  fin_cases i
  · simpa [LinearWaveResidual.shear, mul_assoc] using
      constant_complex_mul (real_mul_complex h.frequency_base (hf 1)) (-2)
  · have h := real_mul_complex htheta (hf 0)
    simp only [LinearWaveResidual.shear,
      GraphDirections.Dr, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, zero_add]
          at h ⊢
    exact h
  · simpa [LinearWaveResidual.shear, GraphDirections.Dr] using real_mul_complex hGr (hf 0)

/-- The velocity principal operator has no negative epsilon exponent:
the fast derivative is stripped and `epsilon * frequency²` has order zero. -/
theorem principalVelocity_components (h : InputBounds s P α κ d a) {β : ℝ}
    {f : ℕ → D → ComplexVector} (hf : ∀ i, WaveClass s P β (fun n x => f n x i)) (i : Fin 3) :
    WaveClass s P β (fun n x => a.principalVelocity s d f n x i) := by
  have hfast := d.Dfast_mem (hf i) h.fast_scale
  have hK := h.shear_mem hf i
  have hn : WaveClass s P β (fun n x => (‖a.normal s d n x‖ ^ 2 : ℝ) • f n x i) := by
    simpa only [zero_add] using unweighted_smul h.normal_norm_sq (hf i)
  have hd := ((hn.band_smul h.frequency_scale).band_smul h.frequency_scale).band_smul (band_epsilon
      s)
  have he : ((β + -(1 / 2 : ℝ)) + -(1 / 2 : ℝ)) + 1 = β := by ring
  rw [he] at hd
  have hds : WaveClass s P β (fun n x =>
      Complex.ofReal (s.epsilon n * (a.frequency n) ^ 2 * ‖a.normal s d n x‖ ^ 2) * f n x i) := by
    simpa only [smul_smul, Complex.real_smul, Complex.ofReal_mul, pow_two, mul_assoc] using hd
  simpa only [WaveCoefficients.principalVelocity, LinearWaveResidual.principal,
    GraphDirections.Dfast, WaveCoefficients.normal, mul_zero, add_zero] using (hfast.add hK).add hds

theorem principalVelocity_class (h : InputBounds s P α κ d a) {β : ℝ}
    {f : ℕ → D → ComplexVector} (hf : ∀ i, WaveClass s P β (fun n x => f n x i)) :
    WaveClass s P β (a.principalVelocity s d f) :=
  component_classes (h.principalVelocity_components hf)

/-- A curl coefficient remainder retains its gain under the principal operator. -/
theorem curl_principal_gain (h : InputBounds s P α κ d a)
    {f : ℕ → D → ComplexVector}
    (hf : ∀ i, WaveClass s P (α + 1 / 2 - κ) (fun n x => f n x i)) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (a.principalVelocity s d f) :=
  (h.principalVelocity_class hf).mono_exponent (by linarith [h.loss_nonneg])

/-- Adding the actual curl coefficient difference preserves the input wave class. -/
theorem add_curl_amplitude (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2)
    {f : ℕ → D → ComplexVector}
    (hf : ∀ i, WaveClass s P (α + 1 / 2 - κ) (fun n x => f n x i)) :
    InputBounds s P α κ d (a.addAmplitude f) := by
  exact { h with amplitude := fun i =>
    (h.amplitude i).add ((hf i).mono_exponent (by linarith)) }

theorem with_cutoff (h : InputBounds s P α κ d a) {ψ : ℕ → D → ℝ}
    (hψ : UnweightedClass s 0 ψ) : InputBounds s P α κ d (a.withCutoff ψ) := by
  refine { h with amplitude := ?_, pressure := ?_ }
  · intro i
    simpa only [WaveCoefficients.withCutoff, Pi.smul_apply, zero_add] using
      unweighted_smul hψ (h.amplitude i)
  · simpa only [WaveCoefficients.withCutoff, zero_add] using real_mul_complex hψ h.pressure

theorem goodCoefficient_class (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2)
    {ψ : ℕ → D → ℝ} (hψ : UnweightedClass s 0 ψ) {f : ℕ → D → ComplexVector}
    (hf : ∀ i, WaveClass s P (α + 1 / 2 - κ) (fun n x => f n x i)) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (a.goodCoefficient s d ψ f) := by
  exact (h.curl_principal_gain hf).add (((h.with_cutoff hψ).add_curl_amplitude hκ
      hf).remainder_class)

/-- The preceding principal estimate now uses the constructed curl error,
whose class follows from primitive normal and amplitude jets. -/
theorem curlCorrection_class (h : InputBounds s P α κ d a) {R : D → ℝ}
    (hR : a.radius = fun _ => R)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n)) :
    WaveClass s P (α + 1 / 2 - κ) (a.curlCorrection s d) := by
  have hN' : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s)
      (fun n => phaseNormal R (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) (a.phase n)) := by
    unfold WaveCoefficients.normal at hN
    simpa only [hR] using hN
  have hr := CurlClassBounds.graphVector_class h.radial_profile h.radial_scale
    h.loss_nonneg d.radial d.auxiliary
  have hz := CurlClassBounds.axialVector_class s d.axial
  have hRi : UnweightedClass s 0 (fun _ x => (R x)⁻¹) := by
    simpa only [hR] using h.inverse_radius
  have hlo : ∀ n x, x ∈ s.domain → b ≤
      ‖phaseNormal R (d.radialField n) (fun _ => d.angular) (d.axialField s n) (a.phase n) x‖ := by
    simpa only [WaveCoefficients.normal, hR] using hlower
  have hhi : ∀ n x, x ∈ s.domain →
      ‖phaseNormal R (d.radialField n) (fun _ => d.angular) (d.axialField s n) (a.phase n) x‖ ≤ M
          := by
    simpa only [WaveCoefficients.normal, hR] using hupper
  have hc := CurlClassBounds.curlRemainder_waveClass hN' (component_classes h.amplitude)
    hb hlo hhi h.loss_nonneg hr (unweighted_const s d.angular) hz hRi hK
  unfold WaveCoefficients.curlCorrection
  simpa only [hR, GraphDirections.radialField, GraphDirections.axialField] using hc

theorem constructed_goodCoefficient_class (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2)
    {ψ : ℕ → D → ℝ} (hψ : UnweightedClass s 0 ψ) {R : D → ℝ}
    (hR : a.radius = fun _ => R)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n)) :
    WaveClass s P (α + 1 / 2 - 3 * κ)
      (a.goodCoefficient s d ψ ((a.withCutoff ψ).curlCorrection s d)) := by
  have hc := (h.with_cutoff hψ).curlCorrection_class hR hN hb hlower hupper hK
  exact h.goodCoefficient_class hκ hψ (fun i => CurlClassBounds.class_component hc i)

/-- Exact additivity in the supplied coefficient, while retaining the same
projected pressure. It does not replace a curl coefficient by a tangent one. -/
theorem principal_add_curl (h : InputBounds s P α κ d a) {β : ℝ}
    {f : ℕ → D → ComplexVector} (hf : ∀ i, WaveClass s P β (fun n x => f n x i))
    (n : ℕ) {x : D} (hx : x ∈ s.domain) :
    (a.addAmplitude f).principal s d n x =
      a.principal s d n x + a.principalVelocity s d f n x := by
  have haD i := (((h.amplitude i).smooth n).contDiffAt (s.isOpen_domain.mem_nhds
      hx)).differentiableAt (by
      simp)
  have hfD i := (((hf i).smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by
      simp)
  ext i
  change LinearWaveResidual.principal _ _ _ _ _ _ _ _ _ _ (fun y => a.amplitude n y + f n y) _ x i
      = _
  unfold LinearWaveResidual.principal
  rw [show along (d.fastField n) (fun y => (a.amplitude n y + f n y) i) x =
      along (d.fastField n) (fun y => a.amplitude n y i) x +
      along (d.fastField n) (fun y => f n y i) x from along_add _ (haD i) (hfD i)]
  fin_cases i <;>
    simp [WaveCoefficients.principal, WaveCoefficients.principalVelocity,
        LinearWaveResidual.principal,
      WaveCoefficients.addAmplitude, LinearWaveResidual.shear, Pi.add_apply] <;> ring

/-- After the actual principal equation is solved for the tangent coefficient,
the corrected coefficient's remaining source has the claimed class. -/
theorem corrected_good_coefficient (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2)
    {f source : ℕ → D → ComplexVector}
    (hf : ∀ i, WaveClass s P (α + 1 / 2 - κ) (fun n x => f n x i))
    (hsolve : ∀ n x, x ∈ s.domain → a.principal s d n x = -source n x) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (fun n x =>
      (a.addAmplitude f).principal s d n x + (a.addAmplitude f).remainder s d n x + source n x) :=
          by
  have hrem := (h.add_curl_amplitude hκ hf).remainder_class
  have hp := h.curl_principal_gain hf
  apply class_congr (hp.add hrem)
  intro n x hx
  dsimp only
  rw [h.principal_add_curl hf n hx, hsolve n x hx]
  abel

end InputBounds

/-- These hypotheses are the actual local geometric and angular conditions
needed to apply the exact differential identity. -/
structure ExactConditions (s : StripData D) (d : GraphDirections D) (a : WaveCoefficients D) : Prop
    where
  phase_smooth : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain
  radius_nonzero : ∀ n x, x ∈ s.domain → a.radius n x ≠ 0
  radial_radius : ∀ n x, x ∈ s.domain → along (d.radialField n) (a.radius n) x = 1
  base_angular : ∀ n x, x ∈ s.domain → ∀ i,
    along (fun _ => d.angular) (fun y =>
      LinearWaveResidual.base (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase n) y
          i) x = 0
  amplitude_angular : ∀ n i, EqOn
    (along (fun _ => d.angular) (fun y => a.amplitude n y i)) (fun _ => 0) s.domain
  phase_angular : ∀ n, ∃ p : ℝ, EqOn (along (fun _ => d.angular) (a.phase n)) (fun _ => p) s.domain
  pressure_angular : ∀ n x, x ∈ s.domain → along (fun _ => d.angular) (a.pressure n) x = 0

theorem harmonicResidual_eq {s : StripData D} {P : ℕ → D → ℝ} {α κ : ℝ}
    {d : GraphDirections D} {a : WaveCoefficients D}
    (h : InputBounds s P α κ d a) (hg : ExactConditions s d a) (n : ℕ) {x : D}
    (hx : x ∈ s.domain) :
    a.harmonicResidual s d n x = fun i =>
      (a.principal s d n x i + a.remainder s d n x i) * carrier (a.frequency n) (a.phase n) x := by
  obtain ⟨pθ, hpθ⟩ := hg.phase_angular n
  have hr : ContDiffOn ℝ ∞ (d.radialField n) s.domain :=
    contDiffOn_const.add (((h.radial_profile.smooth n).smul contDiffOn_const).const_smul
        (d.radialScale n))
  exact LinearWaveResidual.linearResidual_mode_split (s.epsilon n) (a.frequency n)
    (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase n)
    (d.fastField n) (fun _ => d.slow) s.isOpen_domain hr contDiffOn_const contDiffOn_const
    (hg.phase_smooth n) (fun i => (h.amplitude i).smooth n)
    (((h.radius.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp))
    (((h.b_unweighted.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by
        simp))
    (((h.frequency_base.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by
        simp))
    (((h.axial_base.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp))
    (hg.radius_nonzero n x hx) (hg.radial_radius n x hx) (hg.base_angular n x hx)
    (hg.amplitude_angular n) hpθ
    (((h.pressure.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp))
    (hg.pressure_angular n x hx) hx

/-- The correction used in the estimates is realized by an actual curl. -/
theorem curlPotential_realizes {s : StripData D} {P : ℕ → D → ℝ} {α κ : ℝ}
    {d : GraphDirections D} {a : WaveCoefficients D}
    (h : InputBounds s P α κ d a) (n : ℕ)
    (G : CurlClassBounds.CylindricalGeometry s.domain (a.radius n) (d.radialField n)
      (fun _ => d.angular) (d.axialField s n))
    (hK : a.frequency n ≠ 0) (hΦ : ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hn : ∀ x ∈ s.domain, a.normal s d n x ≠ 0)
    (ht : ∀ x ∈ s.domain, normalDot (a.normal s d n x) (a.amplitude n x) = 0)
    {x : D} (hx : x ∈ s.domain) :
    CurlClassBounds.cylindricalCurl (a.radius n) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) (a.curlPotential s d n) x =
      vectorMode (a.frequency n) (a.phase n)
        ((a.addAmplitude (a.curlCorrection s d)).amplitude n) x := by
  exact CurlClassBounds.cylindricalCurl_vectorPotential G hK hΦ
    ((component_classes h.amplitude).smooth n) hn ht hx

theorem curlCorrection_divergence {s : StripData D} {P : ℕ → D → ℝ} {α κ : ℝ}
    {d : GraphDirections D} {a : WaveCoefficients D}
    (h : InputBounds s P α κ d a) (n : ℕ)
    (G : CurlClassBounds.CylindricalGeometry s.domain (a.radius n) (d.radialField n)
      (fun _ => d.angular) (d.axialField s n))
    (hK : a.frequency n ≠ 0) (hΦ : ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hn : ∀ x ∈ s.domain, a.normal s d n x ≠ 0)
    (ht : ∀ x ∈ s.domain, normalDot (a.normal s d n x) (a.amplitude n x) = 0)
    {x : D} (hx : x ∈ s.domain) :
    cylindricalDivergence (a.radius n) (d.radialField n) (fun _ => d.angular) (d.axialField s n)
      (vectorMode (a.frequency n) (a.phase n)
        ((a.addAmplitude (a.curlCorrection s d)).amplitude n)) x = 0 := by
  exact CurlClassBounds.realizedCoefficient_divergence G hK hΦ
    ((component_classes h.amplitude).smooth n) hn ht hx

theorem cutoff_tangent {s : StripData D} {d : GraphDirections D} {a : WaveCoefficients D}
    (ψ : ℕ → D → ℝ) (n : ℕ)
    (ht : ∀ x ∈ s.domain, normalDot (a.normal s d n x) (a.amplitude n x) = 0) :
    ∀ x ∈ s.domain, normalDot ((a.withCutoff ψ).normal s d n x)
      ((a.withCutoff ψ).amplitude n x) = 0 := by
  intro x hx
  change normalDot (a.normal s d n x) (ψ n x • a.amplitude n x) = 0
  calc
    _ = (ψ n x : ℂ) * normalDot (a.normal s d n x) (a.amplitude n x) := by
      simp only [normalDot, Pi.smul_apply, Complex.real_smul]
      ring
    _ = 0 := by rw [ht x hx, mul_zero]

/-- Under the nondegeneracy and tangency hypotheses, the actual cutoff
potential realizes the same corrected velocity whose residual is estimated. -/
theorem corrected_realizes_curl {s : StripData D} {P : ℕ → D → ℝ} {α κ : ℝ}
    {d : GraphDirections D} {a : WaveCoefficients D}
    (h : InputBounds s P α κ d a) {ψ : ℕ → D → ℝ} (hψ : UnweightedClass s 0 ψ) (n : ℕ)
    (G : CurlClassBounds.CylindricalGeometry s.domain (a.radius n) (d.radialField n)
      (fun _ => d.angular) (d.axialField s n))
    (hK : a.frequency n ≠ 0) (hΦ : ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hn : ∀ x ∈ s.domain, a.normal s d n x ≠ 0)
    (ht : ∀ x ∈ s.domain, normalDot (a.normal s d n x) (a.amplitude n x) = 0)
    {x : D} (hx : x ∈ s.domain) :
    CurlClassBounds.cylindricalCurl (a.radius n) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) ((a.withCutoff ψ).curlPotential s d n) x =
      vectorMode (a.frequency n) (a.phase n) ((a.corrected s d ψ).amplitude n) x :=
  curlPotential_realizes (h.with_cutoff hψ) n G hK hΦ hn (cutoff_tangent ψ n ht) hx

theorem corrected_divergence {s : StripData D} {P : ℕ → D → ℝ} {α κ : ℝ}
    {d : GraphDirections D} {a : WaveCoefficients D}
    (h : InputBounds s P α κ d a) {ψ : ℕ → D → ℝ} (hψ : UnweightedClass s 0 ψ) (n : ℕ)
    (G : CurlClassBounds.CylindricalGeometry s.domain (a.radius n) (d.radialField n)
      (fun _ => d.angular) (d.axialField s n))
    (hK : a.frequency n ≠ 0) (hΦ : ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hn : ∀ x ∈ s.domain, a.normal s d n x ≠ 0)
    (ht : ∀ x ∈ s.domain, normalDot (a.normal s d n x) (a.amplitude n x) = 0)
    {x : D} (hx : x ∈ s.domain) :
    cylindricalDivergence (a.radius n) (d.radialField n) (fun _ => d.angular) (d.axialField s n)
      (vectorMode (a.frequency n) (a.phase n) ((a.corrected s d ψ).amplitude n)) x = 0 :=
  curlCorrection_divergence (h.with_cutoff hψ) n G hK hΦ hn (cutoff_tangent ψ n ht) hx

/-- The two excluded slot terms remain explicit fields. Their Gaussian
flatness is a separate analytic theorem, never an instruction to set them to zero. -/
noncomputable def excludedSlotError (d : GraphDirections D) (ψ : ℕ → D → ℝ)
    (a source : ℕ → D → ComplexVector) : ℕ → D → ComplexVector := fun n x =>
  d.Dfast ψ n x • a n x + (1 - ψ n x) • source n x

theorem principal_cutoff {s : StripData D} {P : ℕ → D → ℝ} {α κ : ℝ}
    {d : GraphDirections D} {a : WaveCoefficients D} (h : InputBounds s P α κ d a)
    (ψ : ℕ → D → ℝ) (source : ℕ → D → ComplexVector) (n : ℕ) {x : D}
    (hx : x ∈ s.domain) (hψ : DifferentiableAt ℝ (ψ n) x) :
    (a.withCutoff ψ).principal s d n x + source n x =
      ψ n x • (a.principal s d n x + source n x) + excludedSlotError d ψ a.amplitude source n x :=
          by
  have haD i := (((h.amplitude i).smooth n).contDiffAt (s.isOpen_domain.mem_nhds
      hx)).differentiableAt (by
      simp)
  have hψC : DifferentiableAt ℝ (fun y => (ψ n y : ℂ)) x :=
    (Complex.ofRealCLM.hasFDerivAt.comp x hψ.hasFDerivAt).differentiableAt
  have hD (i : Fin 3) :
      along (d.fastField n) (fun y => (a.withCutoff ψ).amplitude n y i) x =
        Complex.ofReal (d.Dfast ψ n x) * a.amplitude n x i +
          (ψ n x : ℂ) * along (d.fastField n) (fun y => a.amplitude n y i) x := by
    change along (d.fastField n) (fun y => (ψ n y : ℂ) * a.amplitude n y i) x = _
    rw [along_mul _ hψC (haD i), along_ofReal _ hψ]
    rfl
  ext i
  simp only [WaveCoefficients.principal, LinearWaveResidual.principal, Pi.add_apply]
  rw [hD i]
  fin_cases i <;>
    simp [WaveCoefficients.withCutoff, LinearWaveResidual.principal,
      LinearWaveResidual.shear, excludedSlotError,
      Pi.add_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_sub] <;> ring

theorem principal_cutoff_of_solve {s : StripData D} {P : ℕ → D → ℝ} {α κ : ℝ}
    {d : GraphDirections D} {a : WaveCoefficients D} (h : InputBounds s P α κ d a)
    (ψ : ℕ → D → ℝ) (source : ℕ → D → ComplexVector) (n : ℕ) {x : D}
    (hx : x ∈ s.domain) (hψ : DifferentiableAt ℝ (ψ n) x)
    (hsolve : a.principal s d n x = -source n x) :
    (a.withCutoff ψ).principal s d n x + source n x = excludedSlotError d ψ a.amplitude source n x
        := by
  rw [principal_cutoff h ψ source n hx hψ, hsolve]
  simp

/-- The entire stripped source, with both cutoff tails still present as an
explicit additive field. The curl correction is supplied to the actual operator. -/
theorem corrected_coefficient_eq_good_add_excluded {s : StripData D}
    {P : ℕ → D → ℝ} {α κ : ℝ} {d : GraphDirections D} {a : WaveCoefficients D}
    (h : InputBounds s P α κ d a) {ψ : ℕ → D → ℝ} (hψ : UnweightedClass s 0 ψ)
    {f source : ℕ → D → ComplexVector} {β : ℝ}
    (hf : ∀ i, WaveClass s P β (fun n x => f n x i)) (n : ℕ) {x : D}
    (hx : x ∈ s.domain) (hsolve : a.principal s d n x = -source n x) :
    ((a.withCutoff ψ).addAmplitude f).principal s d n x +
        ((a.withCutoff ψ).addAmplitude f).remainder s d n x + source n x =
      a.goodCoefficient s d ψ f n x + excludedSlotError d ψ a.amplitude source n x := by
  have hp := (h.with_cutoff hψ).principal_add_curl hf n hx
  have hc := principal_cutoff_of_solve h ψ source n hx
    (((hψ.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)) hsolve
  have he : (a.withCutoff ψ).principalVelocity s d f n x = a.principalVelocity s d f n x := rfl
  rw [hp, he, WaveCoefficients.goodCoefficient, ← hc]
  abel

/-- Actual harmonic linearization, including the source, equals the proved
good coefficient plus the explicitly retained slot error, times the carrier. -/
theorem harmonicResidual_eq_good_add_excluded {s : StripData D}
    {P : ℕ → D → ℝ} {α κ : ℝ} {d : GraphDirections D} {a : WaveCoefficients D}
    (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2)
    {ψ : ℕ → D → ℝ} (hψ : UnweightedClass s 0 ψ) {f source : ℕ → D → ComplexVector}
    (hf : ∀ i, WaveClass s P (α + 1 / 2 - κ) (fun n x => f n x i))
    (hg : ExactConditions s d ((a.withCutoff ψ).addAmplitude f))
    (n : ℕ) {x : D} (hx : x ∈ s.domain) (hsolve : a.principal s d n x = -source n x) :
    ((a.withCutoff ψ).addAmplitude f).harmonicResidual s d n x +
        (fun i => source n x i * carrier (a.frequency n) (a.phase n) x) =
      (fun i => (a.goodCoefficient s d ψ f n x i +
        excludedSlotError d ψ a.amplitude source n x i) * carrier (a.frequency n) (a.phase n) x) :=
            by
  rw [harmonicResidual_eq (((h.with_cutoff hψ).add_curl_amplitude hκ hf)) hg n hx]
  have he := corrected_coefficient_eq_good_add_excluded h hψ hf n hx hsolve
  ext i
  have hei := congrFun he i
  simp only [Pi.add_apply] at hei ⊢
  change (_ + _) * carrier (a.frequency n) (a.phase n) x +
      source n x i * carrier (a.frequency n) (a.phase n) x = _
  rw [← add_mul, hei]

theorem linear_wave_bound_with_excluded_error {s : StripData D}
    {P : ℕ → D → ℝ} {α κ : ℝ} {d : GraphDirections D} {a : WaveCoefficients D}
    (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2)
    {ψ : ℕ → D → ℝ} (hψ : UnweightedClass s 0 ψ) {f source : ℕ → D → ComplexVector}
    (hf : ∀ i, WaveClass s P (α + 1 / 2 - κ) (fun n x => f n x i))
    (hsolve : ∀ n x, x ∈ s.domain → a.principal s d n x = -source n x) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (a.goodCoefficient s d ψ f) ∧
      ∀ n x, x ∈ s.domain →
        ((a.withCutoff ψ).addAmplitude f).principal s d n x +
            ((a.withCutoff ψ).addAmplitude f).remainder s d n x + source n x =
          a.goodCoefficient s d ψ f n x + excludedSlotError d ψ a.amplitude source n x :=
  ⟨h.goodCoefficient_class hκ hψ hf,
    fun n x hx => corrected_coefficient_eq_good_add_excluded h hψ hf n hx (hsolve n x hx)⟩

/-- The complete exact identity and good class for the constructed curl
coefficient. Every estimate on the correction is obtained from primitive jets. -/
theorem constructed_linear_wave_with_excluded {s : StripData D}
    {P : ℕ → D → ℝ} {α κ : ℝ} {d : GraphDirections D} {a : WaveCoefficients D}
    (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2)
    {ψ : ℕ → D → ℝ} (hψ : UnweightedClass s 0 ψ) {R : D → ℝ}
    (hR : a.radius = fun _ => R)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n))
    {source : ℕ → D → ComplexVector}
    (hsolve : ∀ n x, x ∈ s.domain → a.principal s d n x = -source n x)
    (hg : ExactConditions s d (a.corrected s d ψ)) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (a.constructedGood s d ψ) ∧
      ∀ n x, x ∈ s.domain →
        (a.corrected s d ψ).harmonicResidual s d n x +
            (fun i => source n x i * carrier (a.frequency n) (a.phase n) x) =
          (fun i => (a.constructedGood s d ψ n x i +
              excludedSlotError d ψ a.amplitude source n x i) *
            carrier (a.frequency n) (a.phase n) x) := by
  have hc := (h.with_cutoff hψ).curlCorrection_class hR hN hb hlower hupper hK
  have hci i := CurlClassBounds.class_component hc i
  exact ⟨h.constructed_goodCoefficient_class hκ hψ hR hN hb hlower hupper hK,
    fun n x hx => harmonicResidual_eq_good_add_excluded h hκ hψ hci hg n hx (hsolve n x hx)⟩

/-- The cutoff error in the differential identity is precisely the field
whose Gaussian estimates are proved in `GaussianTailFlat`. -/
theorem excludedSlotError_eq_gaussianError {s : StripData D}
    (g : GaussianTailFlat.SlotFamily s) (d : GraphDirections D)
    (hfast : ∀ n, g.linear n (d.fastScale n • d.fast) = (g.length n)⁻¹)
    (a source : ℕ → D → ComplexVector) :
    excludedSlotError d g.cutoff a source = g.error a source := by
  funext n x
  exact (g.error_eq_directional a source n x (d.fastScale n • d.fast) (hfast n)).symm

theorem excludedSlotError_all_gains {s : StripData D}
    (g : GaussianTailFlat.SlotFamily s) (d : GraphDirections D)
    (hfast : ∀ n, g.linear n (d.fastScale n • d.fast) = (g.length n)⁻¹)
    (edges : GaussianTailFlat.FlatEdges s) (scales : GaussianTailFlat.BandScaleControl s)
    {P : ℕ → D → ℝ} {α c : ℝ} {a source : ℕ → D → ComplexVector}
    (ha : WaveClass s P α a) (hf : WaveClass s P α source) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (N : ℝ) : UnweightedClass s N (excludedSlotError d g.cutoff a source) := by
  rw [excludedSlotError_eq_gaussianError g d hfast]
  exact g.error_all_gains edges scales ha hf hc hP N

/-- All actual stripped jets of the retained error decay to arbitrary order,
uniformly including approach to the flat spatial support edges. -/
theorem excludedSlotError_stripped_bound {s : StripData D}
    (g : GaussianTailFlat.SlotFamily s) (d : GraphDirections D)
    (hfast : ∀ n, g.linear n (d.fastScale n • d.fast) = (g.length n)⁻¹)
    (edges : GaussianTailFlat.FlatEdges s) (scales : GaussianTailFlat.BandScaleControl s)
    {P : ℕ → D → ℝ} {α c : ℝ} {a source : ℕ → D → ComplexVector}
    (ha : WaveClass s P α a) (hf : WaveClass s P α source) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (m : ℕ) (N : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ s.domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (excludedSlotError d g.cutoff a source n) x‖ ≤
        C * ChartScales.Q n ^ N := by
  rw [excludedSlotError_eq_gaussianError g d hfast]
  exact g.error_stripped_bound edges scales ha hf hc hP m N

/-- Proposition 9.3 at the coefficient level: the actual harmonic residual
has the proved good class plus an explicitly proved all-order flat error. -/
theorem constructed_linear_wave_with_flat_error {s : StripData D}
    {P : ℕ → D → ℝ} {α κ : ℝ} {d : GraphDirections D} {a : WaveCoefficients D}
    (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2)
    (g : GaussianTailFlat.SlotFamily s)
    (hfast : ∀ n, g.linear n (d.fastScale n • d.fast) = (g.length n)⁻¹)
    (edges : GaussianTailFlat.FlatEdges s) (scales : GaussianTailFlat.BandScaleControl s)
    {source : ℕ → D → ComplexVector} (hsource : WaveClass s P α source)
    {c : ℝ} (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    {R : D → ℝ} (hR : a.radius = fun _ => R)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n))
    (hsolve : ∀ n x, x ∈ s.domain → a.principal s d n x = -source n x)
    (hg : ExactConditions s d (a.corrected s d g.cutoff)) :
    WaveClass s P (α + 1 / 2 - 3 * κ) (a.constructedGood s d g.cutoff) ∧
      (∀ N : ℝ, UnweightedClass s N (excludedSlotError d g.cutoff a.amplitude source)) ∧
      ∀ n x, x ∈ s.domain →
        (a.corrected s d g.cutoff).harmonicResidual s d n x +
            (fun i => source n x i * carrier (a.frequency n) (a.phase n) x) =
          (fun i => (a.constructedGood s d g.cutoff n x i +
              excludedSlotError d g.cutoff a.amplitude source n x i) *
            carrier (a.frequency n) (a.phase n) x) := by
  obtain ⟨hgood, hexact⟩ := constructed_linear_wave_with_excluded h hκ g.cutoff_memClass
    hR hN hb hlower hupper hK hsolve hg
  exact ⟨hgood, fun N => excludedSlotError_all_gains g d hfast edges scales
    (component_classes h.amplitude) hsource hc hP N, hexact⟩

open PhysicalGraphBounds in
/-- The retained error remains flat after multiplication by the actual
rounded harmonic carrier and restriction to the physical graph. -/
theorem excludedSlotError_carrier_physical_bound {s : StripData LiftPoint}
    (g : GaussianTailFlat.SlotFamily s) (d : GraphDirections LiftPoint)
    (hfast : ∀ n, g.linear n (d.fastScale n • d.fast) = (g.length n)⁻¹)
    (edges : GaussianTailFlat.FlatEdges s) (scales : GaussianTailFlat.BandScaleControl s)
    {P : ℕ → LiftPoint → ℝ} {α c : ℝ} {a source : ℕ → LiftPoint → ComplexVector}
    (ha : WaveClass s P α a) (hf : WaveClass s P α source) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (ha_smooth : ∀ n, ContDiffOn ℝ ∞ (a n) {x | g.coordinate n x ∈ Ioo 0 1})
    (hf_smooth : ∀ n, ContDiff ℝ ∞ (source n))
    {h rLower rUpper B e H : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hrLower : 0 < rLower)
    (hB : 1 ≤ B) (he : 0 ≤ e) (hH : 0 ≤ H) (i : Fin 3) (m : ℕ) (N : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : ProblemStatement.SpaceTime,
      scaledRadial n p ∈ annulus rLower rUpper → |p.1| ≤ 1 → physicalLift h n p ∈ s.domain →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ (Φ : LiftPoint → ℝ) (j : ℤ), ContDiff ℝ ∞ Φ → |(j : ℝ)| ≤ H →
      (∀ k ≤ m, ‖iteratedFDeriv ℝ k Φ (physicalLift h n p)‖ ≤
        B * ChartScales.S n ^ e * ChartScales.Q n ^ (-1 : ℝ)) →
      ‖iteratedFDeriv ℝ m
        ((fun y => excludedSlotError d g.cutoff a source n y i *
            character ((ChartScales.carrier h n : ℝ) * (j : ℝ)) (Φ y)) ∘
          physicalLift h n) p‖ ≤ C * q ^ N := by
  have hai (n : ℕ) : ContDiffOn ℝ ∞ (fun x => a n x i) {x | g.coordinate n x ∈ Ioo 0 1} :=
    (ContinuousLinearMap.proj i : ComplexVector →L[ℝ] ℂ).contDiff.comp_contDiffOn (ha_smooth n)
  have hfi (n : ℕ) : ContDiff ℝ ∞ (fun x => source n x i) :=
    (ContinuousLinearMap.proj i : ComplexVector →L[ℝ] ℂ).contDiff.comp (hf_smooth n)
  have herr : (fun n x => excludedSlotError d g.cutoff a source n x i) =
      g.error (fun n x => a n x i) (fun n x => source n x i) := by
    funext n x
    rw [excludedSlotError_eq_gaussianError g d hfast]
    rfl
  have hb := g.error_carrier_physical_bound edges scales
    (CurlClassBounds.class_component ha i) (CurlClassBounds.class_component hf i) hc hP hai hfi
    (b := rUpper) hh hh1 hrLower hB he hH m N
  simpa only [← herr] using hb

end NavierStokes.LinearWaveBounds
