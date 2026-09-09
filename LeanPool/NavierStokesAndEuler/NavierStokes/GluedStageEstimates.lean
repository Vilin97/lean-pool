/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualStageEstimates
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualValidBandWaves
public import LeanPool.NavierStokesAndEuler.NavierStokes.InitialPhysicalData
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentParticularBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.CurrentParticularLabelBounds

/-!
# Stage estimates with the current-band particular fields

The signed waves and mean increments retain their actual native inputs.
The particular contribution is an independently constructed physical field,
with no physical copy-family representation imposed on it.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.GluedStageEstimates

open Set Function Filter ProblemStatement CorrectionState CorrectionStep
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open ActualPhysicalStageBounds
open scoped ContDiff Topology BigOperators


/-- Bound type used in glued stage estimates. -/
abbrev Bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (qbig : ℝ) (f : SpaceTime → E) (m : ℕ) (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
    PhysicalWaveSum.physicalQ h w ≤ 1 →
    ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r

/-- These are the original native signed-wave data, without an unrelated
particular copy-family field. -/
structure SignedInputs (D : Type) [NormedAddCommGroup D] [NormedSpace ℝ D]
    (I K : Type*) where
  /-- Potential of `SignedInputs`, of type `ℕ → PhysicalStageBounds.WaveData h D (Fin 3 × I) K
  (Fin 3)`. -/
  potential : ℕ → PhysicalStageBounds.WaveData h D (Fin 3 × I) K (Fin 3)
  /-- Pressure field of `SignedInputs`, of type `ℕ → PhysicalStageBounds.WaveData h D I K Unit`. -/
  pressure : ℕ → PhysicalStageBounds.WaveData h D I K Unit
  potential_exponent : ∀ j, 1 / 2 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
    (potential j).alpha
  pressure_exponent : ∀ j, 1 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
    (pressure j).alpha
  potential_shift : ∀ j, (potential j).shift = -h
  pressure_shift : ∀ j, (pressure j).shift = -(2 * CoordinateAlgebra.A h)

section FixedRun

variable {B N0 N : ℕ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*}
  (R : ActualStageEstimates.RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : SignedInputs D I K)

/-- Signed mean potential as an element of `VelocityField`. -/
noncomputable def signedMeanPotential (j : ℕ) : VelocityField := fun w =>
  (W.potential j).vector w +
    (ActualStageEstimates.temporalInput R M hN j).family.angularField w +
    (ActualStageEstimates.rankInput R M hN j).family.angularField w

/-- Signed mean pressure, defined pointwise by `(W.pressure j).pressure w +
(ActualStageEstimates.pressureInput R M hN j).family.field w`. -/
noncomputable def signedMeanPressure (j : ℕ) : PressureField := fun w =>
  (W.pressure j).pressure w +
    (ActualStageEstimates.pressureInput R M hN j).family.field w

/-- Direct, given by `(ActualStageEstimates.angularInput R M hN j).family.angularField`. -/
noncomputable def direct (j : ℕ) : VelocityField :=
  (ActualStageEstimates.angularInput R M hN j).family.angularField

theorem signedMeanPotential_smooth {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j : ℕ) :
    ContDiffOn ℝ ∞ (signedMeanPotential R M hN W j)
      (CutStageEstimates.physicalSublevel h qbig) :=
  (((W.potential j).vector_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono
    inter_subset_left).add
      ((ActualStageEstimates.temporalInput R M hN j).angular_smooth
        outgoing.data.h_pos outgoing.data.h_lt_half hq) |>.add
      ((ActualStageEstimates.rankInput R M hN j).angular_smooth
        outgoing.data.h_pos outgoing.data.h_lt_half hq)

theorem signedMeanPressure_smooth {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j : ℕ) :
    ContDiffOn ℝ ∞ (signedMeanPressure R M hN W j)
      (CutStageEstimates.physicalSublevel h qbig) :=
  (((W.pressure j).pressure_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono
    inter_subset_left).add
      ((ActualStageEstimates.pressureInput R M hN j).field_smooth
        outgoing.data.h_pos outgoing.data.h_lt_half hq)

theorem direct_smooth {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j : ℕ) :
    ContDiffOn ℝ ∞ (direct R M hN j) (CutStageEstimates.physicalSublevel h qbig) :=
  (ActualStageEstimates.angularInput R M hN j).angular_smooth
    outgoing.data.h_pos outgoing.data.h_lt_half hq

private theorem potential_gain (j : ℕ) :
    ActualIterationLedger.gain h (j + 1) ≤
      h * (W.potential j).alpha + (W.potential j).shift + h := by
  have hg := ActualIterationLedger.gain_le_wave outgoing.data.h_pos.le
    ActualCyclePreservation.kappa_small (Nat.succ_pos j)
  rw [← ActualStageEstimates.nativePotential_eq_ledger j] at hg
  have ha := mul_le_mul_of_nonneg_left (W.potential_exponent j) outgoing.data.h_pos.le
  rw [W.potential_shift]
  linarith

private theorem pressure_gain (j : ℕ) :
    ActualIterationLedger.gain h (j + 1) ≤
      h * (W.pressure j).alpha + (W.pressure j).shift + 2 * CoordinateAlgebra.A h := by
  have hg := ActualIterationLedger.gain_le_wavePressure outgoing.data.h_pos.le
    ActualCyclePreservation.kappa_small (Nat.succ_pos j)
  rw [← ActualStageEstimates.nativePressure_eq_ledger j] at hg
  have ha := mul_le_mul_of_nonneg_left (W.pressure_exponent j) outgoing.data.h_pos.le
  rw [W.pressure_shift]
  linarith

private theorem mean_gain (j : ℕ) :
    ActualIterationLedger.gain h (j + 1) ≤
      h * (1 + ActualIterationLedger.sigma j - 2 * ChartScales.kappa) + 0 := by
  simpa only [← ActualStageEstimates.nativeMean_eq_ledger, add_zero] using
    ActualIterationLedger.gain_le_mean outgoing.data.h_pos.le
      ActualCyclePreservation.kappa_small (Nat.succ_pos j)

theorem signedMeanPotential_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    Bound qbig (signedMeanPotential R M hN W j) m
      (ActualIterationLedger.gain h (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m) := by
  have hs0 := (W.potential j).vector_bound_with_gain
    outgoing.data.h_pos outgoing.data.h_lt_half (potential_gain W j) m
  have hs := weaken_bound (qbig := qbig)
    (s := ActualIterationLedger.gain h (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (sub_le_sub_left (le_max_left _ _) _) (by
      obtain ⟨C, hC, hb⟩ := hs0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have ht := weaken_bound
    (s := ActualIterationLedger.gain h (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_left (le_max_right _ _) _)
    ((ActualStageEstimates.temporalInput R M hN j).angular_bound_with_gain
      outgoing.data.h_pos outgoing.data.h_lt_half hq (mean_gain j) m)
  have hr := weaken_bound
    (s := ActualIterationLedger.gain h (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_left (le_max_right _ _) _)
    ((ActualStageEstimates.rankInput R M hN j).angular_bound_with_gain
      outgoing.data.h_pos outgoing.data.h_lt_half hq (mean_gain j) m)
  have ss : ContDiffOn ℝ ∞ (W.potential j).vector
      (CutStageEstimates.physicalSublevel h qbig) :=
    ((W.potential j).vector_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono
      inter_subset_left
  have st := (ActualStageEstimates.temporalInput R M hN j).angular_smooth
    outgoing.data.h_pos outgoing.data.h_lt_half hq
  exact add_bounds outgoing.data.h_pos outgoing.data.h_lt_half (ss.add st)
    ((ActualStageEstimates.rankInput R M hN j).angular_smooth
      outgoing.data.h_pos outgoing.data.h_lt_half hq)
    (add_bounds outgoing.data.h_pos outgoing.data.h_lt_half ss st hs ht) hr

theorem signedMeanPressure_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    Bound qbig (signedMeanPressure R M hN W j) m
      (ActualIterationLedger.gain h (j + 1) -
        PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m) := by
  have hs0 := (W.pressure j).pressure_bound_with_gain
    outgoing.data.h_pos outgoing.data.h_lt_half (pressure_gain W j) m
  have hs := weaken_bound (qbig := qbig)
    (s := ActualIterationLedger.gain h (j + 1) -
      PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (sub_le_sub_left (le_max_left _ _) _) (by
      obtain ⟨C, hC, hb⟩ := hs0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have hm := weaken_bound
    (s := ActualIterationLedger.gain h (j + 1) -
      PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_left (le_max_right _ _) _)
    ((ActualStageEstimates.pressureInput R M hN j).field_bound_with_gain
      outgoing.data.h_pos outgoing.data.h_lt_half hq (mean_gain j) m)
  exact add_bounds outgoing.data.h_pos outgoing.data.h_lt_half
    (((W.pressure j).pressure_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono
      inter_subset_left)
    ((ActualStageEstimates.pressureInput R M hN j).field_smooth
      outgoing.data.h_pos outgoing.data.h_lt_half hq) hs hm

theorem direct_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    Bound qbig (direct R M hN j) m
      (ActualIterationLedger.gain h (j + 1) - PhysicalStageBounds.directLoss h 0 m) :=
  (ActualStageEstimates.angularInput R M hN j).angular_bound_with_gain
    outgoing.data.h_pos outgoing.data.h_lt_half hq (mean_gain j) m

end FixedRun

/-! ## A physical particular contribution and the same mixed sequence -/

/-- Potential loss, given by `max (L m) (PhysicalStageBounds.potentialLoss h h 0 m)`. -/
noncomputable def potentialLoss (L : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (L m) (PhysicalStageBounds.potentialLoss h h 0 m)

/-- Pressure loss, given by `max (L m) (PhysicalStageBounds.pressureLoss h (2 *
CoordinateAlgebra.A h) 0 m)`. -/
noncomputable def pressureLoss (L : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (L m) (PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m)

/-- Background loss, constructed using `MixedFiniteBackground.initialBackgroundLoss`. -/
noncomputable def backgroundLoss (L : ℕ → ℝ) (waveAlpha waveShift : ℝ) : ℕ → ℝ :=
  MixedFiniteBackground.initialBackgroundLoss
    (InitializedPhysicalBackground.initialLoss h waveAlpha waveShift
      (1 - ChartScales.kappa) (9 / 10))
    (potentialLoss L) (PhysicalStageBounds.directLoss h 0)

section MixedSequence

variable {B N0 N : ℕ} {D DA0 DP0 : Type}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup DA0] [NormedSpace ℝ DA0]
  [NormedAddCommGroup DP0] [NormedSpace ℝ DP0]
  {I K IA0 KA0 IP0 KP0 : Type*}
  (R : ActualStageEstimates.RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : SignedInputs D I K)
  (particularA : ℕ → VelocityField) (particularP : ℕ → PressureField)

/-- The four literal contributions use the same order as the physical
sequence construction. -/
noncomputable def potential (j : ℕ) : VelocityField := fun w =>
  particularA j w + (W.potential j).vector w +
    (ActualStageEstimates.temporalInput R M hN j).family.angularField w +
    (ActualStageEstimates.rankInput R M hN j).family.angularField w

/-- Pressure, defined pointwise by `particularP j w + (W.pressure j).pressure w +
(ActualStageEstimates.pressureInput R M hN j).family.field w`. -/
noncomputable def pressure (j : ℕ) : PressureField := fun w =>
  particularP j w + (W.pressure j).pressure w +
    (ActualStageEstimates.pressureInput R M hN j).family.field w

theorem potential_eq (j : ℕ) :
    potential R M hN W particularA j =
      fun w => particularA j w + signedMeanPotential R M hN W j w := by
  funext w
  simp only [potential, signedMeanPotential, add_assoc]

theorem pressure_eq (j : ℕ) :
    pressure R M hN W particularP j =
      fun w => particularP j w + signedMeanPressure R M hN W j w := by
  funext w
  simp only [pressure, signedMeanPressure, add_assoc]

variable {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)

include hq in
theorem potential_smooth
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (j : ℕ) :
    ContDiffOn ℝ ∞ (potential R M hN W particularA j)
      (CutStageEstimates.physicalSublevel h qbig) := by
  rw [potential_eq]
  exact (hs j).add (signedMeanPotential_smooth R M hN W hq j)

include hq in
theorem pressure_smooth
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (j : ℕ) :
    ContDiffOn ℝ ∞ (pressure R M hN W particularP j)
      (CutStageEstimates.physicalSublevel h qbig) := by
  rw [pressure_eq]
  exact (hs j).add (signedMeanPressure_smooth R M hN W hq j)

include hq in
theorem potential_bound {L : ℕ → ℝ}
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ j m, Bound qbig (particularA j) m (ActualIterationLedger.gain h (j + 1) - L m))
    (j m : ℕ) :
    Bound qbig (potential R M hN W particularA j) m
      (ActualIterationLedger.gain h (j + 1) - potentialLoss L m) := by
  rw [potential_eq]
  apply add_bounds outgoing.data.h_pos outgoing.data.h_lt_half (hs j)
    (signedMeanPotential_smooth R M hN W hq j)
  · exact weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half
      (sub_le_sub_left (le_max_left _ _) _) (hb j m)
  · exact weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half
      (sub_le_sub_left (le_max_right _ _) _) (signedMeanPotential_bound R M hN W hq j m)

include hq in
theorem pressure_bound {L : ℕ → ℝ}
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ j m, Bound qbig (particularP j) m (ActualIterationLedger.gain h (j + 1) - L m))
    (j m : ℕ) :
    Bound qbig (pressure R M hN W particularP j) m
      (ActualIterationLedger.gain h (j + 1) - pressureLoss L m) := by
  rw [pressure_eq]
  apply add_bounds outgoing.data.h_pos outgoing.data.h_lt_half (hs j)
    (signedMeanPressure_smooth R M hN W hq j)
  · exact weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half
      (sub_le_sub_left (le_max_left _ _) _) (hb j m)
  · exact weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half
      (sub_le_sub_left (le_max_right _ _) _) (signedMeanPressure_bound R M hN W hq j m)

variable
  (WA : PhysicalStageBounds.WaveData h DA0 IA0 KA0 (Fin 3))
  (WP : PhysicalStageBounds.WaveData h DP0 IP0 KP0 Unit)
  (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField)

/-- Six field identities on the common open sublevel.  Their only content
is identification of the actual sequence and its physical components. -/
structure Representations : Prop where
  potential_zero : EqOn (A 0)
    (initialPotential certificate modulation upper B WA
      (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN))
    (CutStageEstimates.physicalSublevel h qbig)
  direct_zero : EqOn (Bdirect 0) (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField
    (CutStageEstimates.physicalSublevel h qbig)
  pressure_zero : EqOn (P 0)
    (fun w => FinalSlowBase.pressure certificate modulation upper B w +
      initialPressureIncrement WP (actualInitialPressureInput B N0 N hN) w)
    (CutStageEstimates.physicalSublevel h qbig)
  potential_succ : ∀ j, EqOn (potential R M hN W particularA j) (A (j + 1))
    (CutStageEstimates.physicalSublevel h qbig)
  direct_succ : ∀ j, EqOn (direct R M hN j) (Bdirect (j + 1))
    (CutStageEstimates.physicalSublevel h qbig)
  pressure_succ : ∀ j, EqOn (pressure R M hN W particularP j) (P (j + 1))
    (CutStageEstimates.physicalSublevel h qbig)

variable {A Bdirect P}
  (e : Representations R M hN W particularA particularP WA WP A Bdirect P (qbig := qbig))

include e hq

theorem Representations.potential_smooth
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (j : ℕ) : ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbig) := by
  cases j with
  | zero =>
    exact (initialPotential_smooth certificate modulation upper B WA
      (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN) hq hq).congr
      (fun _ hw => e.potential_zero hw)
  | succ j =>
    exact (GluedStageEstimates.potential_smooth R M hN W particularA hq hs j).congr
      (fun _ hw => (e.potential_succ j hw).symm)

theorem Representations.direct_smooth (j : ℕ) :
    ContDiffOn ℝ ∞ (Bdirect j) (CutStageEstimates.physicalSublevel h qbig) := by
  cases j with
  | zero =>
    exact ((actualInitialAngularInput B N0 N hN).angular_smooth
      outgoing.data.h_pos outgoing.data.h_lt_half hq).congr (fun _ hw => e.direct_zero hw)
  | succ j =>
    exact (GluedStageEstimates.direct_smooth R M hN hq j).congr
      (fun _ hw => (e.direct_succ j hw).symm)

theorem Representations.pressure_smooth
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (j : ℕ) : ContDiffOn ℝ ∞ (P j) (CutStageEstimates.physicalSublevel h qbig) := by
  cases j with
  | zero =>
    have hb : ContDiffOn ℝ ∞ (FinalSlowBase.pressure certificate modulation upper B)
        (CutStageEstimates.physicalSublevel h qbig) :=
      (FinalSlowBase.pressure_smooth certificate modulation upper B).mono
        (fun _ hw => ⟨hw.1, mem_univ _⟩)
    exact (hb.add (initialPressureIncrement_smooth WP (actualInitialPressureInput B N0 N hN)
      outgoing.data.h_pos outgoing.data.h_lt_half hq)).congr (fun _ hw => e.pressure_zero hw)
  | succ j =>
    exact (GluedStageEstimates.pressure_smooth R M hN W particularP hq hs j).congr
      (fun _ hw => (e.pressure_succ j hw).symm)

/-- The algebraic consumer of the separate current-particular estimates.
The fixed-run native inputs derive all signed and mean estimates here. -/
theorem represented_raw_bounds {LA LP : ℕ → ℝ}
    (hsA : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (hsP : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (hbA : ∀ j m, Bound qbig (particularA j) m (ActualIterationLedger.gain h (j + 1) - LA m))
    (hbP : ∀ j m, Bound qbig (particularP j) m (ActualIterationLedger.gain h (j + 1) - LP m)) :
    ∃ CA CB CP : ℕ → ℕ → ℝ,
      (∀ j m, 0 ≤ CA j m ∧ 0 ≤ CB j m ∧ 0 ≤ CP j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A (ActualIterationLedger.gain
          h)
        (potentialLoss LA) CA (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) Bdirect
          (ActualIterationLedger.gain h)
        (PhysicalStageBounds.directLoss h 0) CB (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P (ActualIterationLedger.gain
          h)
        (pressureLoss LP) CP (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  obtain ⟨CA, hCA, ha⟩ := raw_of_positive_bounds (fun j m =>
    bound_congr outgoing.data.h_pos outgoing.data.h_lt_half (e.potential_succ j)
      (potential_bound R M hN W particularA hq hsA hbA j m))
  obtain ⟨CB, hCB, hb⟩ := raw_of_positive_bounds (fun j m =>
    bound_congr outgoing.data.h_pos outgoing.data.h_lt_half (e.direct_succ j)
      (direct_bound R M hN hq j m))
  obtain ⟨CP, hCP, hp⟩ := raw_of_positive_bounds (fun j m =>
    bound_congr outgoing.data.h_pos outgoing.data.h_lt_half (e.pressure_succ j)
      (pressure_bound R M hN W particularP hq hsP hbP j m))
  exact ⟨CA, CB, CP, fun j m => ⟨hCA j m, hCB j m, hCP j m⟩, ha, hb, hp⟩

/-- The residual floor is fixed to the next band.  Only exact physical
realizations of finite prefixes enter the residual part of the proof. -/
noncomputable def stageEstimatesOfComponentBounds {LA LP : ℕ → ℝ}
    (hsA : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (hsP : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (hbA : ∀ j m, Bound qbig (particularA j) m (ActualIterationLedger.gain h (j + 1) - LA m))
    (hbP : ∀ j m, Bound qbig (particularP j) m (ActualIterationLedger.gain h (j + 1) - LP m))
    (hqbig : 0 < qbig) (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B (N + 1)
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    MixedCandidateAssembly.StageEstimates h qbig A Bdirect P := by
  let hr := represented_raw_bounds R M hN W particularA particularP hq WA WP e hsA hsP hbA hbP
  let CA := hr.choose
  let CB := hr.choose_spec.choose
  let CP := hr.choose_spec.choose_spec.choose
  have hc := hr.choose_spec.choose_spec.choose_spec
  have hsa := e.potential_smooth R M hN W particularA particularP hq WA WP hsA
  have hsb := e.direct_smooth R M hN W particularA particularP hq WA WP
  have hsp := e.pressure_smooth R M hN W particularA particularP hq WA WP hsP
  refine {
    potential_smooth := hsa
    direct_smooth := hsb
    pressure_smooth := hsp
    gain := ActualIterationLedger.gain h
    gain_zero := ActualIterationLedger.gain_nonneg outgoing.data.h_pos.le 0
    gain_pos := fun _ hj => ActualIterationLedger.gain_pos outgoing.data.h_pos hj
    gain_mono := ActualIterationLedger.gain_monotone outgoing.data.h_pos.le
    gain_top := ActualIterationLedger.gain_tendsto_atTop outgoing.data.h_pos
    potentialLoss := potentialLoss LA
    directLoss := PhysicalStageBounds.directLoss h 0
    pressureLoss := pressureLoss LP
    potentialConstant := CA
    directConstant := CB
    pressureConstant := CP
    potentialLog := fun _ _ => 0
    directLog := fun _ _ => 0
    pressureLog := fun _ _ => 0
    potential_bound := hc.2.1
    direct_bound := hc.2.2.1
    pressure_bound := hc.2.2.2
    backgroundLoss := backgroundLoss LA WA.alpha WA.shift
    residualLoss := ActualCycleResidualBounds.fixedLoss
    finite_background := ?_
    finite_residual := ?_ }
  · have hU := CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half
      qbig
    have hlU := InitializedPhysicalBackground.endpoint_sublevel
      outgoing.data.h_pos outgoing.data.h_lt_half hqbig
    apply MixedFiniteBackground.mixed_background_from_initial hU hlU
      (ActualBaseVelocityBounds.endpoint_past.and hlU)
      (ActualBaseVelocityBounds.endpoint_q_small outgoing.data.h_pos outgoing.data.h_lt_half)
      hsa hsb hc.2.1 hc.2.2.1 (fun j _ => ActualIterationLedger.gain_nonneg outgoing.data.h_pos.le
          j)
    intro m
    simpa only [actualInitialTemporalInput, actualInitialRankInput,
      actualInitialAngularInput, MeanInput.ofMoving, min_self] using
      represented_initial_rate certificate modulation upper B WA
        (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN)
        (actualInitialAngularInput B N0 N hN) hU hlU e.potential_zero e.direct_zero m
  · exact ActualCycleResidualBounds.finite_residual_rates hGeom (by omega)
      (fun _ => ActualCycleParameters.fixedParameters B N0)
      (fun J => MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (fun J => DiagonalJetBounds.uncutPrefix P (J + 1))
      (fun J => ActualCyclePreservation.broad_invariant (R.invariant J)) d

end MixedSequence

/-! ## The literal fields and native source data of the fixed run -/

/-- Current potential, given by `ActualValidBandWaves.gluedPotential
(ActualCyclePreservation.state B N0 j) N`. -/
noncomputable def currentPotential (B N0 N : ℕ) (j : ℕ) : VelocityField :=
  ActualValidBandWaves.gluedPotential (ActualCyclePreservation.state B N0 j) N

/-- Current pressure, given by `ActualValidBandWaves.gluedPressure
(ActualCyclePreservation.state B N0 j) N`. -/
noncomputable def currentPressure (B N0 N : ℕ) (j : ℕ) : PressureField :=
  ActualValidBandWaves.gluedPressure (ActualCyclePreservation.state B N0 j) N

/-- Transfer a uniform estimate on comparable current bands to their
actual glued representative.  The bound has no factor counting charts. -/
theorem glued_bound_of_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {f : ℕ → SpaceTime → E} {qbig r : ℝ} (m : ℕ)
    (hf : ValidDyadicBandCover.Compatible h N f) (hq : qbig ≤ ChartScales.Q N)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, N ≤ n → ∀ w ∈ ValidDyadicBandCover.band h n,
      PhysicalWaveSum.physicalQ h w ≤ ChartScales.Q n → PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (f n) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r) :
    Bound qbig (ValidDyadicBandCover.field h N f) m r := by
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨C, hC, fun w hw hqw => ?_⟩
  exact ValidDyadicBandCover.field_jet_bound_at outgoing.data.h_pos outgoing.data.h_lt_half
    hf hw.1 (hw.2.le.trans hq) m
    (fun n hn hband hcomp => hb n hn w hband hcomp hqw)

private theorem choose_mode_constants {P : ℤ → ℝ → Prop}
    (hP : ∀ k, k ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧ P k C) :
    ∃ C : ℤ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ k, k ≠ 0 → P k (C k) := by
  classical
  have hs (k : ℤ) : ∃ C : ℝ, 0 ≤ C ∧ (k ≠ 0 → P k C) := by
    by_cases hk : k = 0
    · exact ⟨0, le_rfl, fun hn => (hn hk).elim⟩
    · obtain ⟨C, hC, hc⟩ := hP k hk
      exact ⟨C, hC, fun _ => hc⟩
  choose C hC hc using hs
  exact ⟨C, hC, hc⟩

section HarmonicSums

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (ActualInitialization.Index B N0)}
  (H : ActualParticularCycleData.Invariant σ x)
  (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)

include H hGeom

/-- The actual finite harmonic sum keeps the geometric factor 2250.
The harmonic constants are summed before the band and point are chosen. -/
theorem localPotential_bound_of_modes (m : ℕ) {r : ℝ}
    (hb : ∀ k : ℤ, k ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (l : ActualParticularStageControls.Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l k n) w‖ ≤
          C * PhysicalWaveSum.physicalQ h w ^ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ w ∈ ValidDyadicBandCover.band h n,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualValidBandWaves.localPotential x n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ r := by
  classical
  obtain ⟨C, hC, hc⟩ := choose_mode_constants hb
  refine ⟨2250 * ∑ k ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, C k,
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun k _ => hC k)), ?_⟩
  intro n hn w hw hq
  have hq0 := (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1).le
  have he := CurrentParticularLabelBounds.localPotential_jet_bound_of_invariant H hGeom n m hw
    (fun k => C k * PhysicalWaveSum.physicalQ h w ^ r)
    (fun k _ => mul_nonneg (hC k) (Real.rpow_nonneg hq0 r))
    (fun l _ k hk _ => hc k ((ParticularWaveAssembly.mem_modes _ _).mp hk).1 l n hn w hw hq)
  exact he.trans_eq (by rw [← Finset.sum_mul, mul_assoc])

theorem localPressure_bound_of_modes (m : ℕ) {r : ℝ}
    (hb : ∀ k : ℤ, k ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (l : ActualParticularStageControls.Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l k n) w‖ ≤
          C * PhysicalWaveSum.physicalQ h w ^ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ w ∈ ValidDyadicBandCover.band h n,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualValidBandWaves.localPressure x n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ r := by
  classical
  obtain ⟨C, hC, hc⟩ := choose_mode_constants hb
  refine ⟨2250 * ∑ k ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, C k,
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun k _ => hC k)), ?_⟩
  intro n hn w hw hq
  have hq0 := (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1).le
  have he := CurrentParticularLabelBounds.localPressure_jet_bound_of_invariant H hGeom n m hw
    (fun k => C k * PhysicalWaveSum.physicalQ h w ^ r)
    (fun k _ => mul_nonneg (hC k) (Real.rpow_nonneg hq0 r))
    (fun l _ k hk _ => hc k ((ParticularWaveAssembly.mem_modes _ _).mp hk).1 l n hn w hw hq)
  exact he.trans_eq (by rw [← Finset.sum_mul, mul_assoc])

end HarmonicSums

section ActualRun

variable {B N0 N : ℕ} (R : ActualStageEstimates.RunData B N0)

include R

theorem current_preservesCarriers (j : ℕ) :
    ActualParticularStageControls.PreservesCarriers
      (ActualCycleParameters.particularState (ActualCyclePreservation.state B N0 j)) :=
  ActualParticularCycleData.preservesCarriers (R.invariant j)

theorem current_inputSupport (j : ℕ) :
    ActualParticularStageControls.InputSupport
      (ActualCycleParameters.particularState (ActualCyclePreservation.state B N0 j)) :=
  ActualParticularCycleData.native_inputSupport (R.invariant j)

/-- The source class is derived from the stored residual invariant and
the actual label/coordinate reindexing. -/
theorem current_source_class (j : ℕ) (k : ℤ) (hk : k ≠ 0) :
    LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
          ActualParticularStageControls.slowStrip))
      ActualParticularStageControls.nativeEnvelope (1 / 2 + ActualIterationLedger.sigma j)
      (ActualParticularStageControls.currentSource
        (ActualCycleParameters.particularState (ActualCyclePreservation.state B N0 j)) k) :=
  ActualParticularCycleData.native_source_class (R.invariant j) k hk

theorem current_compatible
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0) (j N : ℕ) :
    ValidDyadicBandCover.Compatible h N
        (ActualValidBandWaves.localPotential (ActualCyclePreservation.state B N0 j)) ∧
      ValidDyadicBandCover.Compatible h N
        (ActualValidBandWaves.localPressure (ActualCyclePreservation.state B N0 j)) :=
  ActualValidBandWaves.compatible (R.invariant j) (C j) hGeom
    ActualCoreSupport.refinedCarrier_closed (fun _ _ => subset_rfl) N

theorem current_fields_smooth
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j : ℕ) :
    ContDiffOn ℝ ∞ (currentPotential B N0 N j) (CutStageEstimates.physicalSublevel h qbig) ∧
      ContDiffOn ℝ ∞ (currentPressure B N0 N j) (CutStageEstimates.physicalSublevel h qbig) :=
  ActualValidBandWaves.fields_smooth (R.invariant j) (C j) hGeom
    ActualCoreSupport.refinedCarrier_closed (fun _ _ => subset_rfl) hq

omit R in
theorem current_label_mem (j n : ℕ) (l : ActualParticularStageControls.Label B N0) :
    l ∈ (ActualCycleParameters.particularState
      (ActualCyclePreservation.state B N0 j)).coefficients.labels n ↔
      (l.2, l.1) ∈ activeLabels standardRegion B N0 n := by
  have hlabels : (ActualCyclePreservation.state B N0 j).coefficients.labels =
      activeLabels standardRegion B N0 := ActualCycleCoherence.state_labels B N0 j
  simpa only [ActualCycleParameters.swap_apply, hlabels] using
    ActualCycleParameters.particularState_mem (ActualCyclePreservation.state B N0 j) n (l.2, l.1)

omit R in
theorem gain_le_current_exponent (j : ℕ) :
    ActualIterationLedger.gain h (j + 1) ≤ h * ((1 / 2 + ActualIterationLedger.sigma j) + 1 / 2) :=
        by
  have hg := ActualIterationLedger.gain_le_wave outgoing.data.h_pos.le
    ActualCyclePreservation.kappa_small (Nat.succ_pos j)
  rw [← ActualStageEstimates.nativePotential_eq_ledger j] at hg
  apply hg.trans
  apply mul_le_mul_of_nonneg_left _ outgoing.data.h_pos.le
  have hk : 0 ≤ ChartScales.kappa := by norm_num [ChartScales.kappa]
  linarith

omit R in
/-- The current-phase loss fits inside the original physical wave loss.
The inequality uses the fixed condition `h < 1/2`. -/
theorem current_loss_le_wave (degree : ℝ) (m : ℕ) :
    degree + (2 * h) * (m : ℝ) + PhysicalGraphBounds.graphLoss m + 1 ≤
      PhysicalGraphBounds.waveLoss h m + degree := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hh : 0 ≤ 2 - 3 * h := by linarith [outgoing.data.h_lt_half]
  have hb := mul_nonneg hh hm
  unfold PhysicalGraphBounds.waveLoss
  nlinarith

omit R in
theorem current_potential_loss_le (m : ℕ) :
    h + (2 * h) * (m : ℝ) + PhysicalGraphBounds.graphLoss m + 1 ≤
      PhysicalStageBounds.potentialLoss h h 0 m :=
  (current_loss_le_wave h m).trans (le_max_left _ _)

omit R in
theorem current_pressure_loss_le (m : ℕ) :
    2 * CoordinateAlgebra.A h + (2 * h) * (m : ℝ) + PhysicalGraphBounds.graphLoss m + 1 ≤
      PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m :=
  (current_loss_le_wave (2 * CoordinateAlgebra.A h) m).trans (le_max_left _ _)

theorem current_potential_bound
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hN : 4 ≤ N) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    Bound qbig (currentPotential B N0 N j) m
      (ActualIterationLedger.gain h (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m) := by
  obtain ⟨K, hK, hb⟩ := localPotential_bound_of_modes (R.invariant j) hGeom m
    (fun k hk => ActualCurrentParticularBounds.current_potential_mode_bound
      (R.invariant j) hGeom k hk m)
  have hg : Bound qbig (currentPotential B N0 N j) m
      (h * ((1 / 2 + ActualIterationLedger.sigma j) + 1 / 2) -
        ActualCurrentParticularBounds.currentLoss h (2 * h) m) :=
    glued_bound_of_local m (current_compatible R C hGeom j N).1 hq
      ⟨K, hK, fun n hn w hw _ hqw => hb n (hN.trans hn) w hw hqw⟩
  apply weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half _ hg
  have hgain := gain_le_current_exponent j
  have hloss := current_potential_loss_le m
  unfold ActualCurrentParticularBounds.currentLoss
  linarith

theorem current_pressure_bound
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hN : 4 ≤ N) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    Bound qbig (currentPressure B N0 N j) m
      (ActualIterationLedger.gain h (j + 1) -
        PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m) := by
  obtain ⟨K, hK, hb⟩ := localPressure_bound_of_modes (R.invariant j) hGeom m
    (fun k hk => ActualCurrentParticularBounds.current_pressure_mode_bound
      (R.invariant j) hGeom k hk m)
  have hg : Bound qbig (currentPressure B N0 N j) m
      (h * ((1 / 2 + ActualIterationLedger.sigma j) + 1 / 2) -
        ActualCurrentParticularBounds.currentLoss (2 * CoordinateAlgebra.A h) (2 * h) m) :=
    glued_bound_of_local m (current_compatible R C hGeom j N).2 hq
      ⟨K, hK, fun n hn w hw _ hqw => hb n (hN.trans hn) w hw hqw⟩
  apply weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half _ hg
  have hgain := gain_le_current_exponent j
  have hloss := current_pressure_loss_le m
  unfold ActualCurrentParticularBounds.currentLoss
  linarith

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : SignedInputs D I K)

/-- The representation record specialized to the exact glued particular
fields and the constructed initial primary wave data. -/
abbrev ActualRepresentations (qbig : ℝ)
    (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField) : Prop :=
  Representations R M hN W (currentPotential B N0 N) (currentPressure B N0 N)
    (InitialPhysicalData.potentialWaveData B N0) (InitialPhysicalData.pressureWaveData B N0)
    A Bdirect P (qbig := qbig)

/-- The actual glued current-band rates, native signed/mean data, and
exact finite-prefix realizations supply the complete mixed-stage record.
No physical derivative estimate is a premise of this constructor. -/
noncomputable def actualStageEstimates
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (hqbig : 0 < qbig)
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField)
    (e : ActualRepresentations R M hN W qbig A Bdirect P)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B (N + 1)
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    MixedCandidateAssembly.StageEstimates h qbig A Bdirect P := by
  let E := stageEstimatesOfComponentBounds R M hN W
    (currentPotential B N0 N) (currentPressure B N0 N) hq
    (InitialPhysicalData.potentialWaveData B N0) (InitialPhysicalData.pressureWaveData B N0) e
    (fun j => (current_fields_smooth R C hGeom hq j).1)
    (fun j => (current_fields_smooth R C hGeom hq j).2)
    (current_potential_bound R C hGeom hN hq)
    (current_pressure_bound R C hGeom hN hq) hqbig hGeom d
  have hA : E.potentialLoss = PhysicalStageBounds.potentialLoss h h 0 := by
    funext m
    exact max_self _
  have hP : E.pressureLoss = PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 := by
    funext m
    exact max_self _
  have hBg : E.backgroundLoss = ActualStageEstimates.backgroundLoss 1 (-h) := by
    change backgroundLoss (PhysicalStageBounds.potentialLoss h h 0) 1 (-h) = _
    funext m
    simp only [backgroundLoss, ActualStageEstimates.backgroundLoss,
      MixedFiniteBackground.initialBackgroundLoss, potentialLoss, max_self]
  refine { E with
    potentialLoss := PhysicalStageBounds.potentialLoss h h 0
    pressureLoss := PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0
    backgroundLoss := ActualStageEstimates.backgroundLoss 1 (-h)
    potential_bound := ?_
    pressure_bound := ?_
    finite_background := ?_ }
  · rw [← hA]
    exact E.potential_bound
  · rw [← hP]
    exact E.pressure_bound
  · rw [← hBg]
    exact E.finite_background

theorem actualStageEstimates_ledger
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (hqbig : 0 < qbig)
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField)
    (e : ActualRepresentations R M hN W qbig A Bdirect P)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B (N + 1)
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    let E := actualStageEstimates R M hN W C hq hqbig hGeom A Bdirect P e d
    E.gain = ActualIterationLedger.gain h ∧
      E.potentialLoss = PhysicalStageBounds.potentialLoss h h 0 ∧
      E.directLoss = PhysicalStageBounds.directLoss h 0 ∧
      E.pressureLoss = PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 ∧
      E.backgroundLoss = ActualStageEstimates.backgroundLoss 1 (-h) ∧
      E.residualLoss = ActualCycleResidualBounds.fixedLoss :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end ActualRun

end NavierStokes.GluedStageEstimates
