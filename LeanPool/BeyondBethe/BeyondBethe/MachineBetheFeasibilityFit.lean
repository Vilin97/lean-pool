/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineScheduledStateEncodingBound
import Mathlib.Tactic

/-!
# The canonical Bethe feasibility run always fits its finite-word ruler

The determinant and magnitude invariants of the fixed schedule imply a single
ordinary-binary bound for every state reachable during the bounded run.  This
discharges the last side condition in the program-correctness theorem for the
feasibility machine.
-/

namespace BeyondBethe

def scheduledFeasibilityStateCodeBound (d L K T : ℕ) : ℕ :=
  rationalEllipsoidMachineCodeBound d
    (K + T * (6 + 3 * d))
    (roundedEllipsoidPrecisionSchedule d L K T + 10 + 4 * d)

def explicitBallFeasibilityStateCodeBound (d T : ℕ) (R : ℚ) : ℕ :=
  scheduledFeasibilityStateCodeBound d
    (explicitBallInitialDetExponent d R)
    (explicitBallInitialMagnitudeExponent d R) T

theorem MachineBetheFeasibilityFits.of_invariant
    {m L K T t iterations : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (oraclePrecision : ℕ) (delta upper : RawRat)
    {Target : (Fin (m * m + 1) → ℝ) → Prop}
    (hvalid : RationalCentralOracleValid Target
      (scannedBetheBoundedEpigraphOracle
        tau A oraclePrecision delta upper))
    (E : RationalEllipsoidState (m * m + 1))
    (hE : ScheduledEllipsoidInvariant (m * m + 1) L K t E)
    (hbudget : t + iterations ≤ T) :
    MachineBetheFeasibilityFits tau A oraclePrecision delta upper
      (roundedEllipsoidPrecisionSchedule (m * m + 1) L K T)
      (scheduledFeasibilityStateCodeBound (m * m + 1) L K T)
      iterations E := by
  let d := m * m + 1
  have hd : 0 < d := by
    dsimp only [d]
    omega
  induction iterations generalizing t E with
  | zero => trivial
  | succ iterations ih =>
      rw [MachineBetheFeasibilityFits]
      cases hresponse : scannedBetheBoundedEpigraphOracle
          tau A oraclePrecision delta upper E with
      | accept => trivial
      | cut a =>
          have ha : a ≠ 0 := (hvalid E a hresponse).1
          have hpulled : rationalPulledBackNormal E a ≠ 0 :=
            rationalPulledBackNormal_ne_zero_of_det_ne_zero
              E a hE.det_ne_zero ha
          have htT : t ≤ T := by omega
          let p := roundedEllipsoidPrecisionSchedule d L K T
          let E₁ := scheduledRoundedEllipsoidCentralUpdate p E a
          have hadvance := hE.advance hd a hpulled htT
          have hE₁ : ScheduledEllipsoidInvariant d L K (t + 1) E₁ := by
            simpa only [d, p, E₁] using! hadvance.2
          constructor
          · have hexponent : K + (t + 1) * (6 + 3 * d) ≤
                K + T * (6 + 3 * d) := by
              gcongr
              omega
            have hpow : (2 : ℚ) ^ (K + (t + 1) * (6 + 3 * d)) ≤
                (2 : ℚ) ^ (K + T * (6 + 3 * d)) := by
              exact pow_le_pow_right₀ (by norm_num) hexponent
            have hM : rationalStateAbsBound E₁ ≤
                (2 : ℚ) ^ (K + T * (6 + 3 * d)) :=
              hE₁.magnitude.trans hpow
            have hcode :=
              scheduledRoundedEllipsoidCentralUpdate_stateCode_length_le
                hd E a hM
            simpa only [d, p, E₁,
              scheduledFeasibilityStateCodeBound] using! hcode
          · have hbudget' : (t + 1) + iterations ≤ T := by omega
            exact ih (t := t + 1) (E := E₁) hE₁ hbudget'

theorem explicitBallMachineBetheFeasibilityFits
    {m : ℕ} (hm : 0 < m)
    {tau : ℚ} (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hA : ∀ i j, 0 < A i j)
    (oraclePrecision : ℕ) {delta : RawRat}
    (hdelta : 0 < delta.value) (upper : RawRat)
    (budget : ℕ) {R : ℚ} (hR : 0 < R) :
    MachineBetheFeasibilityFits tau A oraclePrecision delta upper
      (explicitBallFeasibilityPrecision (m * m + 1) budget R)
      (explicitBallFeasibilityStateCodeBound (m * m + 1) budget R)
      budget (rationalBallEllipsoid (m * m + 1) 0 R) := by
  let d := m * m + 1
  let L := explicitBallInitialDetExponent d R
  let K := explicitBallInitialMagnitudeExponent d R
  have hInv : ScheduledEllipsoidInvariant d L K 0
      (rationalBallEllipsoid d 0 R) := by
    simpa only [d, L, K] using! explicitBallInitialInvariant hR
  have hvalid := scannedBetheBoundedEpigraphOracle_valid
    hm htau0 htau1 hA hdelta oraclePrecision upper
  have hfit := MachineBetheFeasibilityFits.of_invariant
    (L := L) (K := K) (T := budget) (t := 0) (iterations := budget)
    tau A oraclePrecision delta upper hvalid
    (rationalBallEllipsoid d 0 R) hInv (by omega)
  simpa only [d, L, K, explicitBallFeasibilityPrecision,
    explicitBallFeasibilityStateCodeBound] using! hfit

theorem machineExplicitBallBetheFeasibilityResultCode_encode
    {m : ℕ} (hm : 0 < m)
    {tau : ℚ} (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hA : ∀ i j, 0 < A i j)
    (oraclePrecision : ℕ) {delta : RawRat}
    (hdelta : 0 < delta.value) (upper : RawRat)
    (budget : ℕ) {R : ℚ} (hR : 0 < R) :
    machineBetheFeasibilityResultCode
        (machineBetheFeasibilityCanonicalWord tau A oraclePrecision
          delta upper
          (explicitBallFeasibilityPrecision (m * m + 1) budget R)
          budget
          (explicitBallFeasibilityStateCodeBound (m * m + 1) budget R)
          (rationalBallEllipsoid (m * m + 1) 0 R)) =
      rationalFeasibilityResultBinaryCode
        (runExplicitBallRationalFeasibility
          (scannedBetheBoundedEpigraphOracle
            tau A oraclePrecision delta upper) budget R) := by
  rw [runExplicitBallRationalFeasibility]
  exact machineBetheFeasibilityResultCode_encode tau A oraclePrecision
    delta upper
    (explicitBallFeasibilityPrecision (m * m + 1) budget R)
    budget (explicitBallFeasibilityStateCodeBound (m * m + 1) budget R)
    (rationalBallEllipsoid (m * m + 1) 0 R)
    (explicitBallMachineBetheFeasibilityFits hm htau0 htau1 hA
      oraclePrecision hdelta upper budget hR)

end BeyondBethe
