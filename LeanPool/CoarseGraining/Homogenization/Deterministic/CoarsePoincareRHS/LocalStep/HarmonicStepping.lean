/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.LocalCorrector

/-! # Harmonic Stepping -/

namespace Homogenization

noncomputable section

namespace ZeroTraceDirichletCorrectorData

variable {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_harmonic_zero
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (N : ℕ) (s : ℝ) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
      (cubeBesovNegativeVectorPartialSeminormTwo Q s 0 (fun x => w.toH1.grad x)) ^ 2 := by
  have hwavg :
      cubeAverageVec Q u = cubeAverageVec Q (fun x => w.toH1.grad x) :=
    ρ.cubeAverageVec_eq_of_eq_add_grad_on_cubeSet huw w.toH1.grad_memVectorL2
  rw [sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_eq_top_add_descendantsAverage]
  have htop :
      vecNormSq (cubeAverageVec Q u) ≤
        (cubeBesovNegativeVectorPartialSeminormTwo Q s 0 (fun x => w.toH1.grad x)) ^ 2 := by
    rw [hwavg, sq_cubeBesovNegativeVectorPartialSeminormTwo]
    simp [sq_cubeBesovNegativeVectorDepthSeminorm_depth_zero]
  calc
    vecNormSq (cubeAverageVec Q u) +
        Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2)
        ≤
          (cubeBesovNegativeVectorPartialSeminormTwo Q s 0 (fun x => w.toH1.grad x)) ^ 2 +
            Real.rpow (3 : ℝ) (-2 * s) *
              descendantsAverage Q 1
                (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) := by
                  exact add_le_add htop le_rfl
    _ =
        Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
          (cubeBesovNegativeVectorPartialSeminormTwo Q s 0 (fun x => w.toH1.grad x)) ^ 2 := by
            ring

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_harmonic_energy
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (s : ℝ) (hs : 0 < s) (N : ℕ) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hgrad : CubeAverageGradientEnergyControl Q a (fun x => w.toH1.grad x) energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
      (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹ *
        cubeAverage Q energy := by
  have hsplit :=
    ρ.sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_harmonic_zero
      (u := u) w huw N s
  have hharmonic :=
    sq_coarsePoincare_gradient_qtwo_partial_of_cubeAverageEnergyControl
      Q a s hs (fun x => w.toH1.grad x) energy 0
      henergy_nonneg henergy_int hgrad hsum
  have hstep :
      Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
        (cubeBesovNegativeVectorPartialSeminormTwo Q s 0 (fun x => w.toH1.grad x)) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
        (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹ *
          cubeAverage Q energy := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (add_le_add_right hharmonic
        (Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2)))
  exact le_trans hsplit hstep


/-- Coefficient-energy version of the elementary split estimate
`w = u - grad rho`.

This is the local algebraic replacement for the older Euclidean
`vecNormSq` split.  The ellipticity hypotheses only certify that the
symmetric coefficient quadratic form is non-negative/integrable; the estimate
itself has the universal constant `2`. -/
theorem cubeAverage_coefficientEnergyDensity_harmonic_le_two_mul_add
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hu : MemVectorL2 (cubeSet Q) u) :
    cubeAverage Q (coefficientEnergyDensity a (fun x => w.toH1.grad x)) ≤
      2 * cubeAverage Q (coefficientEnergyDensity a u) +
        2 * cubeAverage Q
          (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) := by
  let ρgrad : Vec d → Vec d := fun x => ρ.toH10.toH1Function.grad x
  have hwEnergy_int :
      MeasureTheory.IntegrableOn
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)) (cubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
      w.toH1.grad_memVectorL2
  have huEnergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hu
  have hρEnergy_int :
      MeasureTheory.IntegrableOn
        (coefficientEnergyDensity a ρgrad) (cubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
      ρ.toH10.toH1Function.grad_memVectorL2
  have hpoint :
      ∀ x ∈ cubeSet Q,
        coefficientEnergyDensity a (fun y => w.toH1.grad y) x ≤
          2 *
            (coefficientEnergyDensity a u x +
              coefficientEnergyDensity a ρgrad x) := by
    intro x hx
    have hwsub : w.toH1.grad x = u x - ρgrad x := by
      ext i
      change w.toH1.grad x i = u x i - ρ.toH10.toH1Function.grad x i
      have hcoord : u x i = w.toH1.grad x i + ρ.toH10.toH1Function.grad x i := by
        simpa using congrArg (fun z => z i) (huw x hx)
      linarith
    have hsub :=
      coefficientEnergyDensity_sub_le_two_mul_add_of_isEllipticFieldOn
        hEll u ρgrad x hx
    have hEq :
        coefficientEnergyDensity a (fun y => w.toH1.grad y) x =
          coefficientEnergyDensity a (fun y => u y - ρgrad y) x := by
      simp [coefficientEnergyDensity, hwsub]
    exact hEq.trans_le hsub
  have havg_raw :
      cubeAverage Q (coefficientEnergyDensity a (fun x => w.toH1.grad x)) ≤
        cubeAverage Q
          (fun x =>
            2 *
              (coefficientEnergyDensity a u x +
                coefficientEnergyDensity a ρgrad x)) := by
    unfold cubeAverage
    have hvol_inv_nonneg : 0 ≤ (cubeVolume Q)⁻¹ := by
      exact inv_nonneg.mpr (le_of_lt (cubeVolume_pos Q))
    refine mul_le_mul_of_nonneg_left ?_ hvol_inv_nonneg
    exact
      MeasureTheory.integral_mono_ae hwEnergy_int
        ((huEnergy_int.add hρEnergy_int).const_mul (2 : ℝ))
        ((MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
          Filter.Eventually.of_forall fun x hx => hpoint x hx)
  have hsplit :
      cubeAverage Q
          (fun x =>
            2 *
              (coefficientEnergyDensity a u x +
                coefficientEnergyDensity a ρgrad x)) =
        2 * cubeAverage Q (coefficientEnergyDensity a u) +
          2 * cubeAverage Q (coefficientEnergyDensity a ρgrad) := by
    unfold cubeAverage
    have hfun :
        (fun x =>
          2 *
            (coefficientEnergyDensity a u x +
              coefficientEnergyDensity a ρgrad x)) =
          (fun x =>
            2 * coefficientEnergyDensity a u x +
              2 * coefficientEnergyDensity a ρgrad x) := by
      funext x
      ring
    rw [hfun, MeasureTheory.integral_add (huEnergy_int.const_mul (2 : ℝ))
      (hρEnergy_int.const_mul (2 : ℝ))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    ring
  exact havg_raw.trans_eq hsplit

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_uCoeffEnergy_add_correctorCoeffEnergy
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ} (s : ℝ) (hs : 0 < s) (N : ℕ)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : MemVectorL2 (cubeSet Q) u)
    (hgrad :
      CubeAverageGradientEnergyControl Q a (fun x => w.toH1.grad x)
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
          cubeAverage Q (coefficientEnergyDensity a u) +
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
          cubeAverage Q
            (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) := by
  have hharmonic :=
    ρ.sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_harmonic_energy
      (u := u) w s hs N (coefficientEnergyDensity a (fun x => w.toH1.grad x))
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll (fun x => w.toH1.grad x))
      (integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
        w.toH1.grad_memVectorL2)
      hgrad hsum huw
  have hwavg :=
    ρ.cubeAverage_coefficientEnergyDensity_harmonic_le_two_mul_add
      (u := u) w hEll huw hu
  have hs2 : 0 < s * (2 : ℝ) := by nlinarith
  have hlambda_nonneg : 0 ≤ lambdaSq Q s (.finite 2) a := by
    exact multiscale_ellipticity_lambdaSq_finite_nonneg Q s 2 a (by norm_num)
      (by nlinarith [hs])
  let C : ℝ := (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2)))
      (inv_nonneg.mpr hlambda_nonneg)
  calc
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2
        ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
            C * cubeAverage Q (coefficientEnergyDensity a (fun x => w.toH1.grad x)) := by
              simpa [C] using hharmonic
    _ ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
            C *
              (2 * cubeAverage Q (coefficientEnergyDensity a u) +
                2 * cubeAverage Q
                  (coefficientEnergyDensity a
                    (fun x => ρ.toH10.toH1Function.grad x))) := by
              have hmul :
                  C * cubeAverage Q (coefficientEnergyDensity a (fun x => w.toH1.grad x)) ≤
                    C *
                      (2 * cubeAverage Q (coefficientEnergyDensity a u) +
                        2 * cubeAverage Q
                          (coefficientEnergyDensity a
                            (fun x => ρ.toH10.toH1Function.grad x))) :=
                mul_le_mul_of_nonneg_left hwavg hC_nonneg
              simpa [add_comm, add_left_comm, add_assoc] using
                (add_le_add_right hmul
                  (Real.rpow (3 : ℝ) (-2 * s) *
                    descendantsAverage Q 1
                      (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2)))
    _ =
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
            2 * C * cubeAverage Q (coefficientEnergyDensity a u) +
            2 * C *
              cubeAverage Q
                (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) := by
              ring
    _ =
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
            2 *
              ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
                cubeAverage Q (coefficientEnergyDensity a u) +
            2 *
              ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
                cubeAverage Q
                  (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) := by
              simp [C]

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_uCoeffEnergy_of_correctorCoeffEnergyBound
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ} (s : ℝ) (hs : 0 < s) (N : ℕ)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : MemVectorL2 (cubeSet Q) u)
    (hgrad :
      CubeAverageGradientEnergyControl Q a (fun x => w.toH1.grad x)
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    {Eρ : ℝ}
    (hρenergy :
      cubeAverage Q
          (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) ≤ Eρ) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
          cubeAverage Q (coefficientEnergyDensity a u) +
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) * Eρ := by
  have hpre :=
    ρ.sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_uCoeffEnergy_add_correctorCoeffEnergy
      (u := u) w s hs N hEll hu hgrad hsum huw
  have hs2 : 0 < s * (2 : ℝ) := by nlinarith
  have hlambda_nonneg : 0 ≤ lambdaSq Q s (.finite 2) a := by
    exact multiscale_ellipticity_lambdaSq_finite_nonneg Q s 2 a (by norm_num)
      (by nlinarith [hs])
  have hC_nonneg :
      0 ≤ 2 * ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) := by
    refine mul_nonneg (by norm_num) ?_
    exact mul_nonneg
      (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2)))
      (inv_nonneg.mpr hlambda_nonneg)
  calc
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2
        ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
            2 *
              ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
                cubeAverage Q (coefficientEnergyDensity a u) +
            2 *
              ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
                cubeAverage Q
                  (coefficientEnergyDensity a
                    (fun x => ρ.toH10.toH1Function.grad x)) := hpre
    _ ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
            2 *
              ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
                cubeAverage Q (coefficientEnergyDensity a u) +
            2 *
              ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) * Eρ := by
          gcongr


end ZeroTraceDirichletCorrectorData

end

end Homogenization
