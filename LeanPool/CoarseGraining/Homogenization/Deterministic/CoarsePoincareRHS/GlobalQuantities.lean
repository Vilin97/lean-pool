/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.NoteConstants

/-! # Global Quantities -/

namespace Homogenization

noncomputable section

/-- The natural-depth scale weight used to pass from `R_n` to `S_n`. -/
noncomputable def coarsePoincareRHSDepthWeight (s : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) (-s * (n : ℝ))

/-- Natural-depth version of the note's averaged `R_n` quantity. -/
noncomputable def coarsePoincareRHSRn {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (n : ℕ) : ℝ :=
  descendantsAverage Q n fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2

@[simp] theorem coarsePoincareRHSRn_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) :
    coarsePoincareRHSRn Q s u 0 =
      (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 := by
  simp [coarsePoincareRHSRn, descendantsAverage]

/-- Natural-depth version of the note's scaled `S_n` quantity. -/
noncomputable def coarsePoincareRHSSn {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (n : ℕ) : ℝ :=
  coarsePoincareRHSDepthWeight s n * coarsePoincareRHSRn Q s u n

@[simp] theorem coarsePoincareRHSDepthWeight_zero (s : ℝ) :
    coarsePoincareRHSDepthWeight s 0 = 1 := by
  simp [coarsePoincareRHSDepthWeight]

@[simp] theorem coarsePoincareRHSSn_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) :
    coarsePoincareRHSSn Q s u 0 =
      (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 := by
  simp [coarsePoincareRHSSn]

/-- Averaged intrinsic local error appearing in the absorbed `R_n` recurrence. -/
noncomputable def coarsePoincareRHSIntrinsicAbsorbedErrorAverage {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g u : Vec d → Vec d)
    (s η : ℝ) (n : ℕ) : ℝ :=
  descendantsAverage Q n fun R => coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η

/-- Averaged intrinsic local energy piece in the absorbed `R_n` recurrence. -/
noncomputable def coarsePoincareRHSIntrinsicEnergyErrorAverage {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s : ℝ) (n : ℕ) : ℝ :=
  descendantsAverage Q n fun R => coarsePoincareRHSIntrinsicLocalEnergyError R a u s

/-- Averaged intrinsic local forcing piece in the absorbed `R_n` recurrence. -/
noncomputable def coarsePoincareRHSIntrinsicForceErrorAverage {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s : ℝ) (n : ℕ) : ℝ :=
  descendantsAverage Q n fun R => coarsePoincareRHSIntrinsicLocalForceError R a g s

/-- Intrinsic localized one-step error after absorption and parent coefficient localization. -/
noncomputable def coarsePoincareRHSIntrinsicLocalizedEnergyForceError {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s CE CF : ℝ) (B : ℕ → ℝ) (n : ℕ) : ℝ :=
  CE *
      (2 * coarsePoincareRHSParentHalfCoeff Q a s n *
        cubeAverage Q (coefficientEnergyDensity a u)) +
    CF * ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s n) ^ 2 * B n)

/-- Finite weighted intrinsic localized-error sum produced by iterating the localized recurrence. -/
noncomputable def coarsePoincareRHSIntrinsicWeightedLocalizedEnergyForceErrorSum {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s θ CE CF : ℝ) (B : ℕ → ℝ) (m N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    θ ^ k * coarsePoincareRHSIntrinsicLocalizedEnergyForceError Q a u s CE CF B (m + k)

/-- Scaled intrinsic localized-error sum produced by the localized `S_n` recurrence. -/
noncomputable def coarsePoincareRHSSIntrinsicWeightedLocalizedEnergyForceErrorSum {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s θ CE CF : ℝ) (B : ℕ → ℝ) (m N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    (coarsePoincareRHSScaledStepCoeff s θ) ^ k *
      (coarsePoincareRHSDepthWeight s (m + k) *
        coarsePoincareRHSIntrinsicLocalizedEnergyForceError Q a u s CE CF B (m + k))

/-- Intrinsic energy part of the scaled localized global-force error sum. -/
noncomputable def coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s θ CE : ℝ) (m N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    (coarsePoincareRHSScaledStepCoeff s θ) ^ k *
      (coarsePoincareRHSDepthWeight s (m + k) *
        (CE *
          (2 * coarsePoincareRHSParentHalfCoeff Q a s (m + k) *
            cubeAverage Q (coefficientEnergyDensity a u))))

/-- The `k = 0` intrinsic energy coefficient for the scaled global-force finite sum. -/
noncomputable def coarsePoincareRHSSIntrinsicGlobalEnergyBase {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s CE : ℝ) (m : ℕ) : ℝ :=
  coarsePoincareRHSDepthWeight s m *
    (CE *
      (2 * coarsePoincareRHSParentHalfCoeff Q a s m *
        cubeAverage Q (coefficientEnergyDensity a u)))

/-- Intrinsic force part of the scaled localized global-force error sum. -/
noncomputable def coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s θ CF : ℝ) (m N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    (coarsePoincareRHSScaledStepCoeff s θ) ^ k *
      (coarsePoincareRHSDepthWeight s (m + k) *
        (CF *
          ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s (m + k)) ^ 2 *
            coarsePoincareRHSGlobalForceBound Q g s (m + k))))

/-- The `k = 0` intrinsic force coefficient for the scaled global-force finite sum. -/
noncomputable def coarsePoincareRHSSIntrinsicGlobalForceBase {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s CF : ℝ) (m : ℕ) : ℝ :=
  coarsePoincareRHSDepthWeight s m *
    (CF *
      ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s m) ^ 2 *
        coarsePoincareRHSGlobalForceBound Q g s m))

theorem coarsePoincareRHSSIntrinsicWeightedLocalizedEnergyForceErrorSum_global_eq_energy_add_force
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) (s θ CE CF : ℝ) (m N : ℕ) :
    coarsePoincareRHSSIntrinsicWeightedLocalizedEnergyForceErrorSum Q a u s θ CE CF
        (fun n => coarsePoincareRHSGlobalForceBound Q g s n) m N =
      coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum Q a u s θ CE m N +
        coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum Q a g s θ CF m N := by
  unfold coarsePoincareRHSSIntrinsicWeightedLocalizedEnergyForceErrorSum
    coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum
    coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum
    coarsePoincareRHSIntrinsicLocalizedEnergyForceError
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  ring


end

end Homogenization
