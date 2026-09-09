/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionBudgetRestriction
public import LeanPool.NavierStokesAndEuler.Euler.SobolevDriftNorm

/-! Genuine correction data with separate full-velocity and transport-drift bounds. -/

@[expose] public section


noncomputable section

namespace EulerDriftCorrectionBudget

open Set EulerCorrectionOperators EulerCorrectionEnergyData EulerQuadraticSource
  EulerSobolevDriftNorm EulerFunctionalVelocity EulerSobolevTransport
  EulerCylinderSobolevSpace EulerSobolevGevreyOperators

variable (period : ℝ) [Fact (0 < period)]

/-- The full coefficient budget is retained, while the actual small drift has its own envelope. -/
structure Budget {q : ℕ} {T : ℝ} (hq : 6 ≤ q + 1)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (N : ℕ) (R : C(Icc (0 : ℝ) T, ℝ)) where
  /-- All full-velocity and coefficient norms, including the residual, are actual data bounds. -/
  full : SpatialBudget period hq D N R
  /-- The smaller bound used in the shrinking-radius slope. -/
  drift : ℝ
  /-- A norm envelope is nonnegative. -/
  drift_nonneg : 0 ≤ drift
  /-- The weighted norm of the actual four-component background drift. -/
  drift_bound : ∀ t, weightedDriftNorm period 6 N (R t)
    (velocityMap (velocityComponents D.κ D.direction)) (D.approximation t) ≤ drift

/-- Restricting the time interval preserves both actual norm bounds and all constants. -/
def Budget.restrict {q : ℕ} {T S : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) S)}
    {N : ℕ} {R : C(Icc (0 : ℝ) S, ℝ)}
    (B : Budget period hq D N R) (hTS : T ≤ S) :
    Budget period hq (D.comp period (timeInclusion hTS)) N (R.comp (timeInclusion hTS)) where
  full := EulerCorrectionBudgetRestriction.SpatialBudget.restrict period B.full hTS
  drift := B.drift
  drift_nonneg := B.drift_nonneg
  drift_bound t := B.drift_bound (timeInclusion hTS t)

/-- Only the correction field uses the coarse drift-to-velocity comparison. -/
theorem Budget.total_drift_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
    {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (B : Budget period hq D N R) (hN : N + 6 ≤ (q + 1) + 1)
    (t : Icc (0 : ℝ) T) (e : SobolevSpace period ((q + 1) + 1)) :
    weightedDriftNorm period 6 N (R t)
        (velocityMap (velocityComponents D.κ D.direction)) (D.approximation t+e) ≤
      4 * (B.drift + weightedNorm period 6 N (R t) e) := by
  have he := weightedDriftNorm_velocityMap_le period 6 N (R t) (B.full.radius_pos t)
    (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) e
  have h := (weightedDriftNorm_add_le period 6 N hN (R t) (B.full.radius_pos t)
    (velocityMap (velocityComponents D.κ D.direction)) (D.approximation t) e).trans
    (add_le_add (B.drift_bound t) he)
  nlinarith only [h, B.drift_nonneg]

end EulerDriftCorrectionBudget
