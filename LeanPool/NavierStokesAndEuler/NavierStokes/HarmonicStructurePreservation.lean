/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicWaveInteraction

@[expose] public section

/-!
# Structure preserved by actual harmonic block addition

The carrier-retaining sum is the actual `HarmonicWaveInteraction.addBlock`.
Smoothness of its input coefficient functions justifies linearity of the
Fréchet derivatives in the cylindrical divergence. No output divergence
condition, nonzero frequency, or nonzero angular frequency is assumed.
-/

noncomputable section

namespace NavierStokes.HarmonicStructurePreservation

open Set
open HarmonicCalculus HarmonicFields WeightedClasses HarmonicWaveInteraction
open scoped Topology ContDiff

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem amplitude_addBlock (a b : CorrectionState.HarmonicBlock D) (j : ℤ) (n : ℕ) :
    amplitude (addBlock a b) j n = amplitude a j n + amplitude b j n := by
  funext x i
  simp only [amplitude, blockAmplitude_addBlock, Pi.add_apply, HarmonicMeanInteraction.coeff_add]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem amplitude_withCarrier (a b : CorrectionState.HarmonicBlock D) (j : ℤ) (n : ℕ) :
    amplitude (withCarrier a b) j n = amplitude b j n := rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- The complex single Fourier fields add before any real projection or
differentiation. This identity also holds at harmonic zero. -/
theorem singleMode_addBlock (a b : CorrectionState.HarmonicBlock D) (j : ℤ) (n : ℕ) :
    singleMode (addBlock a b) j n = singleMode a j n + singleMode (withCarrier a b) j n := by
  funext p i
  simp only [singleMode, HarmonicResidual.vectorField, field, evaluate_single, Pi.add_apply]
  rw [amplitude_addBlock, amplitude_withCarrier]
  simp only [addBlock, withCarrier, Pi.add_apply, add_mul]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem withCarrier_eq {a b : CorrectionState.HarmonicBlock D}
    (hfrequency : b.frequency = a.frequency) (hphase : b.phase = a.phase)
    (hangular : b.angularFrequency = a.angularFrequency) : withCarrier a b = b := by
  cases a
  cases b
  simp only [withCarrier] at *
  cases hfrequency
  cases hphase
  cases hangular
  rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem singleMode_addBlock_of_sameCarrier {a b : CorrectionState.HarmonicBlock D}
    (hfrequency : b.frequency = a.frequency) (hphase : b.phase = a.phase)
    (hangular : b.angularFrequency = a.angularFrequency) (j : ℤ) (n : ℕ) :
    singleMode (addBlock a b) j n = singleMode a j n + singleMode b j n := by
  rw [singleMode_addBlock, withCarrier_eq hfrequency hphase hangular]

theorem amplitude_contDiffOn {U : Set D} {b : CorrectionState.HarmonicBlock D}
    (hb : ∀ n i, HarmonicResidual.SmoothCoefficients U (b.velocity n i))
    (j : ℤ) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => amplitude b j n x i) U :=
  (hb n i).realCoefficients j

theorem singleMode_contDiffOn {U : Set D} {b : CorrectionState.HarmonicBlock D}
    (hb : ∀ n i, HarmonicResidual.SmoothCoefficients U (b.velocity n i))
    (hphase : ∀ n, ContDiffOn ℝ ∞ (b.phase n) U)
    (j : ℤ) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun p => singleMode b j n p i) (HarmonicResidual.liftDomain U) := by
  apply HarmonicResidual.field_smoothOn (Φ := b.phase n) _ (hphase n)
  intro l
  change ContDiffOn ℝ ∞ ((Finsupp.single j (fun x => amplitude b j n x i)) l) U
  by_cases hlj : j = l
  · subst l
    simpa only [Finsupp.single_eq_same] using amplitude_contDiffOn hb j n i
  · rw [Finsupp.single_eq_of_ne (Ne.symm hlj)]
    exact contDiffOn_const

/-- Additivity uses actual differentiability of all components at the
evaluation point. The geometric direction fields need no derivatives. -/
theorem cylindricalDivergence_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E → ℝ) (Vr Vθ Vz : E → E) {a b : E → ComplexVector} {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b y i) x) :
    cylindricalDivergence R Vr Vθ Vz (a + b) x =
      cylindricalDivergence R Vr Vθ Vz a x + cylindricalDivergence R Vr Vθ Vz b x := by
  simp only [cylindricalDivergence, Pi.add_apply,
    along_add _ (ha 0) (hb 0), along_add _ (ha 1) (hb 1), along_add _ (ha 2) (hb 2),
    smul_add]
  abel

theorem velocity_smooth_addBlock {U : Set D} {a b : CorrectionState.HarmonicBlock D}
    (ha : ∀ n i, HarmonicResidual.SmoothCoefficients U (a.velocity n i))
    (hb : ∀ n i, HarmonicResidual.SmoothCoefficients U (b.velocity n i)) :
    ∀ n i, HarmonicResidual.SmoothCoefficients U ((addBlock a b).velocity n i) :=
  fun n i => (ha n i).add (hb n i)

theorem pressure_smooth_addBlock {U : Set D} {a b : CorrectionState.HarmonicBlock D}
    (ha : ∀ n, HarmonicResidual.SmoothCoefficients U (a.pressure n))
    (hb : ∀ n, HarmonicResidual.SmoothCoefficients U (b.pressure n)) :
    ∀ n, HarmonicResidual.SmoothCoefficients U ((addBlock a b).pressure n) :=
  fun n => (ha n).add (hb n)

theorem phase_smooth_addBlock {U : Set D} {a b : CorrectionState.HarmonicBlock D}
    (ha : ∀ n, ContDiffOn ℝ ∞ (a.phase n) U) :
    ∀ n, ContDiffOn ℝ ∞ ((addBlock a b).phase n) U := ha

/-- The carrier-retaining sum preserves modewise solenoidality when the
second input is interpreted on the retained carrier. -/
theorem modeSolenoidal_addBlock_withCarrier {s : StripData D}
    {c : CorrectionState.Context D} {a b : CorrectionState.HarmonicBlock D}
    (ha : ∀ n i, HarmonicResidual.SmoothCoefficients s.domain (a.velocity n i))
    (hb : ∀ n i, HarmonicResidual.SmoothCoefficients s.domain (b.velocity n i))
    (hphase : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hda : ModeSolenoidal s c a) (hdb : ModeSolenoidal s c (withCarrier a b)) :
    ModeSolenoidal s c (addBlock a b) := by
  intro j hj n p hp
  have hmem : p ∈ HarmonicResidual.liftDomain s.domain := ⟨hp, mem_univ _⟩
  have hnb := (HarmonicResidual.liftDomain_open s.isOpen_domain).mem_nhds hmem
  have hsa (i : Fin 3) : DifferentiableAt ℝ (fun q => singleMode a j n q i) p :=
    ((singleMode_contDiffOn ha hphase j n i).contDiffAt hnb).differentiableAt (by simp)
  have hsb (i : Fin 3) : DifferentiableAt ℝ (fun q => singleMode (withCarrier a b) j n q i) p :=
    ((singleMode_contDiffOn (b := withCarrier a b) hb hphase j n i).contDiffAt
      hnb).differentiableAt (by simp)
  rw [singleMode_addBlock, cylindricalDivergence_add _ _ _ _ hsa hsb,
    hda j hj n p hp, hdb j hj n p hp, add_zero]

/-- Actual addition of two smooth solenoidal blocks on a common carrier
preserves the same primitive solenoidality condition on the same strip. -/
theorem modeSolenoidal_addBlock {s : StripData D}
    {c : CorrectionState.Context D} {a b : CorrectionState.HarmonicBlock D}
    (hfrequency : b.frequency = a.frequency) (hphase_eq : b.phase = a.phase)
    (hangular : b.angularFrequency = a.angularFrequency)
    (ha : ∀ n i, HarmonicResidual.SmoothCoefficients s.domain (a.velocity n i))
    (hb : ∀ n i, HarmonicResidual.SmoothCoefficients s.domain (b.velocity n i))
    (hphase : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hda : ModeSolenoidal s c a) (hdb : ModeSolenoidal s c b) :
    ModeSolenoidal s c (addBlock a b) := by
  apply modeSolenoidal_addBlock_withCarrier ha hb hphase hda
  rw [withCarrier_eq hfrequency hphase_eq hangular]
  exact hdb

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- The velocity zero-mode condition is preserved coefficientwise, as an
identity of actual coefficient functions. -/
theorem zeroMode_addBlock {a b : CorrectionState.HarmonicBlock D}
    (ha : ZeroMode a) (hb : ZeroMode b) : ZeroMode (addBlock a b) := by
  intro n i
  change (a.velocity n i + b.velocity n i) 0 = 0
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha n i, hb n i, add_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Pressure has the same algebraic preservation without any derivative
or regularity assumptions. -/
theorem zeroPressure_addBlock {a b : CorrectionState.HarmonicBlock D}
    (ha : ∀ n, a.pressure n 0 = 0) (hb : ∀ n, b.pressure n 0 = 0) :
    ∀ n, (addBlock a b).pressure n 0 = 0 := by
  intro n
  change (a.pressure n + b.pressure n) 0 = 0
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha n, hb n, add_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem zeroMode_withCarrier {a b : CorrectionState.HarmonicBlock D}
    (hb : ZeroMode b) : ZeroMode (withCarrier a b) := hb

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem zeroPressure_withCarrier {a b : CorrectionState.HarmonicBlock D}
    (hb : ∀ n, b.pressure n 0 = 0) : ∀ n, (withCarrier a b).pressure n 0 = 0 := hb

end NavierStokes.HarmonicStructurePreservation
