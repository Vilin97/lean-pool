/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.AveragedLocal.DescendantsAverage

/-! # Component Bounds Basic -/

namespace Homogenization

noncomputable section

theorem coarsePoincareRHSRn_le_discount_next_add_intrinsicAbsorbedErrorAverage_of_localBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) (s η : ℝ) (n : ℕ)
    (hlocal :
      ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η) :
    coarsePoincareRHSRn Q s u n ≤
      coarsePoincareRHSDiscount s * coarsePoincareRHSRn Q s u (n + 1) +
        coarsePoincareRHSIntrinsicAbsorbedErrorAverage Q a g u s η n := by
  have hlocal' :
      ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S => (cubeBesovNegativeVectorSeminormTwo S s u) ^ 2) +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η := by
    intro R hR
    simpa [coarsePoincareRHSDiscount, coarsePoincareRHSRn] using hlocal R hR
  simpa [coarsePoincareRHSDiscount, coarsePoincareRHSRn,
    coarsePoincareRHSIntrinsicAbsorbedErrorAverage] using
      descendantsAverage_sq_cubeBesovNegativeVectorSeminormTwo_le_discount_next_add_error_of_localBound
        Q s u n (fun R => coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η)
        hlocal'

theorem coarsePoincareRHSRn_le_intrinsicComponentErrors_of_localBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) (s η : ℝ) (n : ℕ)
    (hlocal :
      ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η) :
    coarsePoincareRHSRn Q s u n ≤
      coarsePoincareRHSDiscount s * coarsePoincareRHSRn Q s u (n + 1) +
        (coarsePoincareRHSAbsorbedEnergyCoeff η *
            coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n +
          coarsePoincareRHSAbsorbedRnCoeff η *
            coarsePoincareRHSRn Q s u n +
          coarsePoincareRHSAbsorbedForceCoeff η *
            coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n) := by
  have hmain :=
    coarsePoincareRHSRn_le_discount_next_add_intrinsicAbsorbedErrorAverage_of_localBound
      Q a g u s η n hlocal
  calc
    coarsePoincareRHSRn Q s u n
        ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn Q s u (n + 1) +
            coarsePoincareRHSIntrinsicAbsorbedErrorAverage Q a g u s η n := hmain
    _ =
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn Q s u (n + 1) +
            (coarsePoincareRHSAbsorbedEnergyCoeff η *
                coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n +
              coarsePoincareRHSAbsorbedRnCoeff η *
                coarsePoincareRHSRn Q s u n +
              coarsePoincareRHSAbsorbedForceCoeff η *
                coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n) := by
                rw [coarsePoincareRHSIntrinsicAbsorbedErrorAverage_eq_componentAverages]

theorem coarsePoincareRHSRn_intrinsicAbsorptionReady_le_of_localBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) (s η : ℝ) (n : ℕ)
    (hlocal :
      ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η) :
    (1 - coarsePoincareRHSAbsorbedRnCoeff η) *
        coarsePoincareRHSRn Q s u n ≤
      coarsePoincareRHSDiscount s * coarsePoincareRHSRn Q s u (n + 1) +
        coarsePoincareRHSAbsorbedEnergyCoeff η *
          coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n +
        coarsePoincareRHSAbsorbedForceCoeff η *
          coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n := by
  have hsplit :=
    coarsePoincareRHSRn_le_intrinsicComponentErrors_of_localBound
      Q a g u s η n hlocal
  linarith

theorem coarsePoincareRHSRn_le_invAbsorptionCoeff_mul_intrinsicErrors_of_localBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) (s η : ℝ) (n : ℕ)
    (habs :
      0 < 1 - coarsePoincareRHSAbsorbedRnCoeff η)
    (hlocal :
      ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η) :
    coarsePoincareRHSRn Q s u n ≤
      (1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
        (coarsePoincareRHSDiscount s * coarsePoincareRHSRn Q s u (n + 1) +
          coarsePoincareRHSAbsorbedEnergyCoeff η *
            coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n +
          coarsePoincareRHSAbsorbedForceCoeff η *
            coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n) := by
  let B : ℝ :=
    coarsePoincareRHSDiscount s * coarsePoincareRHSRn Q s u (n + 1) +
      coarsePoincareRHSAbsorbedEnergyCoeff η *
        coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n +
      coarsePoincareRHSAbsorbedForceCoeff η *
        coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n
  have hready :
      (1 - coarsePoincareRHSAbsorbedRnCoeff η) *
          coarsePoincareRHSRn Q s u n ≤ B := by
    simpa [B, add_assoc] using
      coarsePoincareRHSRn_intrinsicAbsorptionReady_le_of_localBound
        Q a g u s η n hlocal
  exact (le_inv_mul_iff₀ habs).mpr hready

theorem coarsePoincareRHSRn_le_intrinsicComponentBounds_of_localBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) (s η : ℝ) (n : ℕ)
    {θ CE CF : ℝ}
    (habs :
      0 < 1 - coarsePoincareRHSAbsorbedRnCoeff η)
    (hθ :
      (1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
          coarsePoincareRHSDiscount s ≤ θ)
    (hEcoeff :
      (1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
          coarsePoincareRHSAbsorbedEnergyCoeff η ≤ CE)
    (hFcoeff :
      (1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
          coarsePoincareRHSAbsorbedForceCoeff η ≤ CF)
    (hnext_nonneg : 0 ≤ coarsePoincareRHSRn Q s u (n + 1))
    (hE_nonneg : 0 ≤ coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n)
    (hF_nonneg : 0 ≤ coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n)
    (hlocal :
      ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η) :
    coarsePoincareRHSRn Q s u n ≤
      θ * coarsePoincareRHSRn Q s u (n + 1) +
        CE * coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n +
        CF * coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n := by
  have hbase :=
    coarsePoincareRHSRn_le_invAbsorptionCoeff_mul_intrinsicErrors_of_localBound
      Q a g u s η n habs hlocal
  calc
    coarsePoincareRHSRn Q s u n
        ≤
          (1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
            (coarsePoincareRHSDiscount s * coarsePoincareRHSRn Q s u (n + 1) +
              coarsePoincareRHSAbsorbedEnergyCoeff η *
                coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n +
              coarsePoincareRHSAbsorbedForceCoeff η *
                coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n) := hbase
    _ =
          ((1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
              coarsePoincareRHSDiscount s) *
            coarsePoincareRHSRn Q s u (n + 1) +
          ((1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
              coarsePoincareRHSAbsorbedEnergyCoeff η) *
            coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n +
          ((1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
              coarsePoincareRHSAbsorbedForceCoeff η) *
            coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n := by
              ring
    _ ≤
          θ * coarsePoincareRHSRn Q s u (n + 1) +
            CE * coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n +
            CF * coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n := by
              exact
                add_le_add
                  (add_le_add
                    (mul_le_mul_of_nonneg_right hθ hnext_nonneg)
                    (mul_le_mul_of_nonneg_right hEcoeff hE_nonneg))
                  (mul_le_mul_of_nonneg_right hFcoeff hF_nonneg)

end

end Homogenization
