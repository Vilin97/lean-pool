/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.CertificateMagnitude
import LeanPool.BeyondBethe.BeyondBethe.ExecutableScannedBetheOptimizer

/-!
# Certificate magnitude for the row-major executable optimizer
-/

namespace BeyondBethe

theorem executableOptimizerCertificateLog_abs_le
    (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ)
    (hBpos : ∀ i j, 0 < B i j)
    (hBupper : ∀ i j, B i j ≤ 1) :
    abs ((explicitDirectedCertificateLog
        (executableScannedBetheOptimizerMatrix (m := m + 1) B)
        (executableScannedBetheOptimizerRowPotential (m := m + 1) B)
        (executableScannedBetheOptimizerColumnPotential (m := m + 1) B) : ℚ) : ℝ) ≤
      explicitCertificateMagnitudeBudget B := by
  let X := executableScannedBetheOptimizerMatrix (m := m + 1) B
  let R := executableScannedBetheOptimizerRowPotential (m := m + 1) B
  let C := executableScannedBetheOptimizerColumnPotential (m := m + 1) B
  have hpoint := executableScannedBetheOptimizerPoint_spec (m := m + 1)
    (by omega) B hBpos hBupper
  have hX : IsDoublyStochastic (fun i j ↦ ((X i j : ℚ) : ℝ)) := by
    simpa only [X] using hpoint.2.1
  have hXlo : ∀ i j, (explicitOptimizerFloor B : ℝ) ≤ (X i j : ℝ) := by
    simpa only [X] using hpoint.2.2.1
  have hfloor : 0 < (explicitOptimizerFloor B : ℝ) :=
    Rat.cast_pos.mpr (explicitOptimizerFloor_pos B)
  have hXpos : ∀ i j, 0 < (X i j : ℝ) := fun i j ↦
    hfloor.trans_le (hXlo i j)
  have happrox := executableScannedBetheOptimizer_hasApproximateLogKKT
    (m := m + 1) (by omega) B hBpos hBupper
  simpa only [X, R, C] using
    certificateLog_abs_le_of_feasibleApproximateKKT
      m B X R C hBpos hBupper hX hXpos
      (by simpa only [X, R, C] using happrox)

end BeyondBethe
