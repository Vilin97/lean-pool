/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.QTwo
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesQTwo
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.NeumannCorrector

/-! # Flux Stepping -/

namespace Homogenization

noncomputable section

namespace MeanZeroNeumannCorrectorData

variable {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}

/-- Flux version of the elementary local step: after subtracting the centered
Neumann corrector, the top-scale flux average is the harmonic remainder's flux
average. -/
theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_flux_succ_le_descendantsAverage_add_harmonic_zero
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_mem : MemVectorL2 (cubeSet Q) u)
    (hg : MemVectorL2 (cubeSet Q) g)
    (N : ℕ) (s : ℝ) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1)
        (fun x => matVecMul (a x) (u x))) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R =>
            (cubeBesovNegativeVectorPartialSeminormTwo R s N
              (fun x => matVecMul (a x) (u x))) ^ 2) +
      (cubeBesovNegativeVectorPartialSeminormTwo Q s 0
        (fun x => matVecMul (a x) (w.toH1.grad x))) ^ 2 := by
  have hwavg :
      cubeAverageVec Q (fun x => matVecMul (a x) (u x)) =
        cubeAverageVec Q (fun x => matVecMul (a x) (w.toH1.grad x)) :=
    ω.cubeAverageVec_flux_eq_harmonicRemainderFlux_of_centered_rhs
      w huw hEll hu_mem hg
  rw [sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_eq_top_add_descendantsAverage]
  have htop :
      vecNormSq (cubeAverageVec Q (fun x => matVecMul (a x) (u x))) ≤
        (cubeBesovNegativeVectorPartialSeminormTwo Q s 0
          (fun x => matVecMul (a x) (w.toH1.grad x))) ^ 2 := by
    rw [hwavg, sq_cubeBesovNegativeVectorPartialSeminormTwo]
    simp [sq_cubeBesovNegativeVectorDepthSeminorm_depth_zero]
  calc
    vecNormSq (cubeAverageVec Q (fun x => matVecMul (a x) (u x))) +
        Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R =>
              (cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => matVecMul (a x) (u x))) ^ 2)
        ≤
          (cubeBesovNegativeVectorPartialSeminormTwo Q s 0
              (fun x => matVecMul (a x) (w.toH1.grad x))) ^ 2 +
            Real.rpow (3 : ℝ) (-2 * s) *
              descendantsAverage Q 1
                (fun R =>
                  (cubeBesovNegativeVectorPartialSeminormTwo R s N
                    (fun x => matVecMul (a x) (u x))) ^ 2) := by
          exact add_le_add htop le_rfl
    _ =
        Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R =>
              (cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => matVecMul (a x) (u x))) ^ 2) +
          (cubeBesovNegativeVectorPartialSeminormTwo Q s 0
            (fun x => matVecMul (a x) (w.toH1.grad x))) ^ 2 := by
            ring

/-- Flux local step with the harmonic top-scale term bounded by the `q = 2`
flux coarse Poincare energy control. -/
theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_flux_succ_le_descendantsAverage_add_harmonic_energy
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (s : ℝ) (hs : 0 < s) (N : ℕ) (energy : Vec d → ℝ)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_mem : MemVectorL2 (cubeSet Q) u)
    (hg : MemVectorL2 (cubeSet Q) g)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hflux :
      CubeAverageFluxEnergyControl Q a
        (fun x => matVecMul (a x) (w.toH1.grad x)) energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1)
        (fun x => matVecMul (a x) (u x))) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R =>
            (cubeBesovNegativeVectorPartialSeminormTwo R s N
              (fun x => matVecMul (a x) (u x))) ^ 2) +
      (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
        cubeAverage Q energy := by
  have hsplit :=
    ω.sq_cubeBesovNegativeVectorPartialSeminormTwo_flux_succ_le_descendantsAverage_add_harmonic_zero
      (u := u) w huw hEll hu_mem hg N s
  have hharmonic :=
    sq_coarsePoincare_flux_qtwo_partial_of_cubeAverageEnergyControl
      Q a s hs (fun x => matVecMul (a x) (w.toH1.grad x)) energy 0
      henergy_nonneg henergy_int hflux hsum
  have hstep :
      Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R =>
              (cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => matVecMul (a x) (u x))) ^ 2) +
        (cubeBesovNegativeVectorPartialSeminormTwo Q s 0
          (fun x => matVecMul (a x) (w.toH1.grad x))) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R =>
              (cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => matVecMul (a x) (u x))) ^ 2) +
        (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
          cubeAverage Q energy := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (add_le_add_right hharmonic
        (Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R =>
              (cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => matVecMul (a x) (u x))) ^ 2)))
  exact le_trans hsplit hstep

end MeanZeroNeumannCorrectorData

end

end Homogenization
