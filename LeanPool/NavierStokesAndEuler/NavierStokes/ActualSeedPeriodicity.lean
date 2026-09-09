/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialization
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveRegularityData

/-!
# Torus periodicity of the actual seed coefficients

The common cover is required to precede the fixed physical label's native
cover. Under this ordering, the actual exact-curl velocity, pressure, and
retained Gaussian coefficients are invariant under every torus deck shift.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualSeedPeriodicity

open CorrectionInitialization HarmonicCalculus

/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point

variable {B N0 : ℕ}

/-- The deck shift on the full free lift, leaving radius and slow variables
unchanged. This is definitionally the shift used by the seed continuation. -/
noncomputable def pointDeck (k : TorusInverse.Frequency) : Point :=
  (ActualPrimaryCoherence.chartDeck k).1

theorem pointDeck_eq (k : TorusInverse.Frequency) :
    pointDeck k = (0, (0, TorusAverages.latticePoint k)) := rfl

theorem zeroSlice_add_deck (k : TorusInverse.Frequency) (x : Point) :
    (x + pointDeck k, (0 : ℝ)) = (x, 0) + ActualPrimaryCoherence.chartDeck k := by
  simp [pointDeck, ActualPrimaryCoherence.chartDeck]

theorem conjugatePair_periodic {E : Type} [NormedAddCommGroup E]
    (f : E → ℂ) (w : E)
    (hf : ∀ x, f (x + w) = f x) (j : ℤ) (x : E) :
    ErrorHarmonics.conjugatePair 1 f j (x + w) =
      ErrorHarmonics.conjugatePair 1 f j x := by
  simp only [SignedWaveUpdate.conjugatePair_apply, hf]

/-- The stored phase uses the same ordered common cover. -/
theorem phase_periodic (l : ActualInitialization.Index B N0) (n : ℕ)
    (hn : ActualWaveRegularityData.Ordered l n) (k : TorusInverse.Frequency)
    (x : Point) :
    ActualInitialization.phase l n (x + pointDeck k) =
      ActualInitialization.phase l n x := by
  simpa only [ActualInitialization.phase, ActualInitialization.primaryPiece,
    ActualPrimary.piece, ← zeroSlice_add_deck] using
    ActualPrimaryCoherence.chart_phase_periodic l.2 l.1 n hn k (x, 0)

/-- Every harmonic coefficient of the actual exact-curl seed velocity is
periodic, including the conjugate mode. -/
theorem primary_velocity_periodic (l : ActualInitialization.Index B N0) (n : ℕ)
    (hn : ActualWaveRegularityData.Ordered l n) (i : Fin 3) (j : ℤ)
    (k : TorusInverse.Frequency) (x : Point) :
    (ActualInitialization.primaryBlock l).velocity n i j (x + pointDeck k) =
      (ActualInitialization.primaryBlock l).velocity n i j x := by
  change ErrorHarmonics.conjugatePair 1
    (fun y => (ActualInitialization.primaryPiece l).exactCoefficients.amplitude n (y, 0) i)
      j (x + pointDeck k) = _
  apply conjugatePair_periodic
  intro y
  simpa only [ActualInitialization.primaryPiece, ← zeroSlice_add_deck] using
    congrFun (ActualPrimaryCoherence.piece_exactAmplitude_periodic
      ActualPrimary.standardRegion l.2 l.1 n hn k (y, 0)) i

/-- The pressure coefficient contains the actual cutoff and the same
conjugate-pair normalization as the seed. -/
theorem primary_pressure_periodic (l : ActualInitialization.Index B N0) (n : ℕ)
    (hn : ActualWaveRegularityData.Ordered l n) (j : ℤ)
    (k : TorusInverse.Frequency) (x : Point) :
    (ActualInitialization.primaryBlock l).pressure n j (x + pointDeck k) =
      (ActualInitialization.primaryBlock l).pressure n j x := by
  change ErrorHarmonics.conjugatePair 1
    (fun y => (ActualInitialization.primaryPiece l).exactCoefficients.pressure n (y, 0))
      j (x + pointDeck k) = _
  apply conjugatePair_periodic
  intro y
  change (ActualPrimary.chartCutoff l.2 l.1 n (y + pointDeck k, 0) : ℂ) *
      (ActualPrimary.chartCoefficients l.2 l.1).pressure n (y + pointDeck k, 0) = _
  have hcut := ActualPrimaryCoherence.chart_cutoff_periodic l.2 l.1 n hn k (y, 0)
  have hp := ActualPrimaryCoherence.chart_pressure_periodic l.2 l.1 n hn k (y, 0)
  have he := congrArg₂ (fun (a : ℝ) (b : ℂ) => (a : ℂ) * b) hcut hp
  simp only [← zeroSlice_add_deck] at he
  exact he

/-- The Gaussian error is kept as its differentiated cutoff coefficient.
Its invariance follows by translating that derivative, not by deleting it. -/
theorem gaussian_velocity_periodic (l : ActualInitialization.Index B N0) (n : ℕ)
    (hn : ActualWaveRegularityData.Ordered l n) (i : Fin 3) (j : ℤ)
    (k : TorusInverse.Frequency) (x : Point) :
    (ActualInitialization.gaussianBlock l).velocity n i j (x + pointDeck k) =
      (ActualInitialization.gaussianBlock l).velocity n i j x := by
  change ErrorHarmonics.conjugatePair 1
    (fun y => LinearWaveBounds.excludedSlotError
      (ActualInitialization.primaryPiece l).directions
      (ActualInitialization.primaryPiece l).cutoff
      (ActualInitialization.primaryPiece l).coefficients.amplitude 0 n (y, 0) i)
      j (x + pointDeck k) = _
  apply conjugatePair_periodic
  intro y
  have hd := ActualPrimaryCoherence.along_translate (ActualPrimaryCoherence.chartDeck k)
    (ActualPrimaryCoherence.chart_cutoff_periodic l.2 l.1 n hn k)
    (show ∀ z, (ActualInitialization.primaryPiece l).directions.fastField n
        (z + ActualPrimaryCoherence.chartDeck k) =
      (ActualInitialization.primaryPiece l).directions.fastField n z from fun _ => rfl) (y, 0)
  have ha := ActualPrimaryCoherence.chart_amplitude_periodic l.2 l.1 n hn k (y, 0)
  simp only [← zeroSlice_add_deck] at hd ha
  change ((along ((ActualInitialization.primaryPiece l).directions.fastField n)
      (ActualPrimary.chartCutoff l.2 l.1 n) (y + pointDeck k, 0) •
      (ActualPrimary.chartCoefficients l.2 l.1).amplitude n (y + pointDeck k, 0) +
        (1 - ActualPrimary.chartCutoff l.2 l.1 n (y + pointDeck k, 0)) •
          (0 : ComplexVector)) i) = _
  rw [hd, ha]
  simp only [LinearWaveBounds.excludedSlotError, Pi.zero_apply, smul_zero, add_zero]
  rfl

end NavierStokes.ActualSeedPeriodicity
