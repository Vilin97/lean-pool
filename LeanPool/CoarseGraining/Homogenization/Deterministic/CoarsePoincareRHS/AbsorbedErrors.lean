/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.GlobalBaseBounds

/-! # Absorbed Errors -/

@[expose] public section

namespace Homogenization

noncomputable section


theorem coarsePoincareRHSDepthWeight_mul_intrinsicWeightedLocalizedEnergyForceErrorSum_eq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (u : Vec d → Vec d) (s θ CE CF : ℝ) (B : ℕ → ℝ) (m N : ℕ) :
    coarsePoincareRHSDepthWeight s m *
      coarsePoincareRHSIntrinsicWeightedLocalizedEnergyForceErrorSum Q a u s θ CE CF B m N =
        coarsePoincareRHSSIntrinsicWeightedLocalizedEnergyForceErrorSum Q a u s θ CE CF B m N := by
  unfold coarsePoincareRHSIntrinsicWeightedLocalizedEnergyForceErrorSum
    coarsePoincareRHSSIntrinsicWeightedLocalizedEnergyForceErrorSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [← mul_assoc,
    coarsePoincareRHSDepthWeight_mul_theta_pow_eq_scaledStepCoeff_mul s θ m k]
  ring

theorem coarsePoincareRHSIntrinsicAbsorbedLocalError_eq_components
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) (s η : ℝ) :
    coarsePoincareRHSIntrinsicAbsorbedLocalError Q a g u s η =
      coarsePoincareRHSAbsorbedEnergyCoeff η *
          coarsePoincareRHSIntrinsicLocalEnergyError Q a u s +
        coarsePoincareRHSAbsorbedRnCoeff η *
          (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 +
        coarsePoincareRHSAbsorbedForceCoeff η *
          coarsePoincareRHSIntrinsicLocalForceError Q a g s := by
  let A : ℝ := coarsePoincareRHSIntrinsicLocalEnergyError Q a u s
  let K : ℝ := coarsePoincareRHSIntrinsicLocalForceMultiplier Q a s
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s
    (fun x => g x - cubeAverageVec Q g)
  let U : ℝ := cubeBesovNegativeVectorSeminormTwo Q s u
  change
    A + η * U ^ 2 +
        η * ((1 - η)⁻¹ * (A + η * U ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2))) +
        2 * η⁻¹ * ((K * G) ^ 2) =
        (1 + η * (1 - η)⁻¹) * A +
        (η + η ^ 2 * (1 - η)⁻¹) * U ^ 2 +
        (2 * η * (1 - η)⁻¹ * η⁻¹ + 2 * η⁻¹) * ((K * G) ^ 2)
  ring

theorem coarsePoincareRHSIntrinsicAbsorbedErrorAverage_eq_componentAverages
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) (s η : ℝ) (n : ℕ) :
    coarsePoincareRHSIntrinsicAbsorbedErrorAverage Q a g u s η n =
      coarsePoincareRHSAbsorbedEnergyCoeff η *
          coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n +
        coarsePoincareRHSAbsorbedRnCoeff η *
          coarsePoincareRHSRn Q s u n +
        coarsePoincareRHSAbsorbedForceCoeff η *
          coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n := by
  let A : TriadicCube d → ℝ := fun R => coarsePoincareRHSIntrinsicLocalEnergyError R a u s
  let U : TriadicCube d → ℝ := fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2
  let F : TriadicCube d → ℝ := fun R => coarsePoincareRHSIntrinsicLocalForceError R a g s
  let cA : ℝ := coarsePoincareRHSAbsorbedEnergyCoeff η
  let cU : ℝ := coarsePoincareRHSAbsorbedRnCoeff η
  let cF : ℝ := coarsePoincareRHSAbsorbedForceCoeff η
  have hpoint :
      (fun R : TriadicCube d => coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η) =
        fun R => cA * A R + cU * U R + cF * F R := by
    funext R
    simp [A, U, F, cA, cU, cF,
      coarsePoincareRHSIntrinsicAbsorbedLocalError_eq_components R a g u s η, add_assoc]
  calc
    coarsePoincareRHSIntrinsicAbsorbedErrorAverage Q a g u s η n
        = descendantsAverage Q n (fun R => cA * A R + cU * U R + cF * F R) := by
            simp [coarsePoincareRHSIntrinsicAbsorbedErrorAverage, hpoint]
    _ =
        cA * descendantsAverage Q n A +
          cU * descendantsAverage Q n U +
          cF * descendantsAverage Q n F := by
            rw [descendantsAverage_add Q n (fun R => cA * A R + cU * U R)
              (fun R => cF * F R)]
            rw [descendantsAverage_add Q n (fun R => cA * A R) (fun R => cU * U R)]
            rw [← descendantsAverage_smul Q n cA A]
            rw [← descendantsAverage_smul Q n cU U]
            rw [← descendantsAverage_smul Q n cF F]
    _ =
        coarsePoincareRHSAbsorbedEnergyCoeff η *
            coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n +
          coarsePoincareRHSAbsorbedRnCoeff η *
            coarsePoincareRHSRn Q s u n +
          coarsePoincareRHSAbsorbedForceCoeff η *
            coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n := by
            simp [A, U, F, cA, cU, cF, coarsePoincareRHSIntrinsicEnergyErrorAverage,
              coarsePoincareRHSRn, coarsePoincareRHSIntrinsicForceErrorAverage]


theorem coarsePoincareRHSRn_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (n : ℕ) :
    0 ≤ coarsePoincareRHSRn Q s u n := by
  unfold coarsePoincareRHSRn
  exact descendantsAverage_nonneg Q n _
    fun R hR => sq_nonneg (cubeBesovNegativeVectorSeminormTwo R s u)

theorem coarsePoincareRHSSn_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (n : ℕ) :
    0 ≤ coarsePoincareRHSSn Q s u n := by
  unfold coarsePoincareRHSSn coarsePoincareRHSDepthWeight
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (coarsePoincareRHSRn_nonneg Q s u n)



end

end Homogenization
