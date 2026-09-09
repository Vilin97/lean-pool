/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentParticularPhysical

/-!
# Removing the native scales from the current particular modes

The native potential and pressure transformation laws imply equality of
their actual physical modes. The angle and Cartesian rotation are the same
at both bands, so the native scale cancels before applying either map.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.CurrentParticularPhysicalCoherence

open ProblemStatement CorrectionState CorrectionStep
open ActualCurrentParticularPhysical

variable {B N0 : ℕ}

/-- Cancel a positive native scale before applying a physical coordinate
map. No regularity or linearity of that later map is required. -/
theorem unscale_of_ratioPower {E : Type*} [MulAction ℝ E]
    {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a : ℝ)
    {v vr : E} (hv : v = PhysicalParticularWave.ratioPower Q Qr a • vr) :
    Q ^ (-a) • v = Qr ^ (-a) • vr := by
  rw [hv, smul_smul, mul_comm (Q ^ (-a)),
    PhysicalParticularWave.ratioPower_cancel hQ hQr]

/-- The actual current-band vector potential becomes independent of the
band once its native transformation law is supplied. -/
theorem localPotentialMode_eq_of_native
    (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) (n m : ℕ)
    (w : SpaceTime)
    (hpot : nativePotential x l j n (nativePoint n w) =
      PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m)
        CorrectionInitialization.ActualPrimary.h •
          nativePotential x l j m (nativePoint m w)) :
    localPotentialMode x l j n w = localPotentialMode x l j m w := by
  have hv := unscale_of_ratioPower (ChartScales.Q_pos n) (ChartScales.Q_pos m)
    CorrectionInitialization.ActualPrimary.h hpot
  change PhysicalCurlCovariance.realVector
      (CartesianCopySource.rotationMap (PhysicalGraphBounds.radialProjection w)
        ((ChartScales.Q n) ^ (-CorrectionInitialization.ActualPrimary.h) •
          nativePotential x l j n (nativePoint n w))) =
    PhysicalCurlCovariance.realVector
      (CartesianCopySource.rotationMap (PhysicalGraphBounds.radialProjection w)
        ((ChartScales.Q m) ^ (-CorrectionInitialization.ActualPrimary.h) •
          nativePotential x l j m (nativePoint m w)))
  rw [hv]

/-- The pressure weight cancels the physical factor with exponent `-2A`.
The real part is taken only after cancelling the complex native modes. -/
theorem localPressureMode_eq_of_native
    (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) (n m : ℕ)
    (w : SpaceTime)
    (hp : nativePressure x l j n (nativePoint n w) =
      PhysicalParticularWave.pressureWeight CorrectionInitialization.ActualPrimary.h
        (ChartScales.Q n) (ChartScales.Q m) •
          nativePressure x l j m (nativePoint m w)) :
    localPressureMode x l j n w = localPressureMode x l j m w := by
  have hv := unscale_of_ratioPower (ChartScales.Q_pos n) (ChartScales.Q_pos m)
    (2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) hp
  change (ChartScales.Q n) ^ (-2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) *
      (nativePressure x l j n (nativePoint n w)).re =
    (ChartScales.Q m) ^ (-2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) *
      (nativePressure x l j m (nativePoint m w)).re
  simpa only [Complex.smul_re, smul_eq_mul, neg_mul] using congrArg Complex.re hv

end NavierStokes.CurrentParticularPhysicalCoherence
