/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.ForceLocalization

/-! # Local Corrector -/

namespace Homogenization

noncomputable section

namespace ZeroTraceDirichletCorrectorData

variable {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}

theorem cubeAverageVec_eq_of_eq_add_grad_on_cubeSet
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u v : Vec d → Vec d}
    (huv : ∀ x ∈ cubeSet Q, u x = v x + ρ.toH10.toH1Function.grad x)
    (hv : MemVectorL2 (cubeSet Q) v) :
    cubeAverageVec Q u = cubeAverageVec Q v := by
  funext i
  have hui :
      cubeAverage Q (fun x => u x i) =
        cubeAverage Q (fun x => v x i + ρ.toH10.toH1Function.grad x i) := by
    apply cubeAverage_eq_of_eq_on_cubeSet
    intro x hx
    simpa using congrArg (fun z => z i) (huv x hx)
  show cubeAverage Q (fun x => u x i) = cubeAverage Q (fun x => v x i)
  rw [hui]
  unfold cubeAverage
  have hvi :
      MeasureTheory.MemLp (fun x => v x i) (2 : ENNReal)
        (volumeMeasureOn (cubeSet Q)) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hv
  have hvi_int :
      MeasureTheory.Integrable (fun x => v x i) (volumeMeasureOn (cubeSet Q)) :=
    hvi.integrable (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
  have hρi_int :
      MeasureTheory.Integrable (fun x => ρ.toH10.toH1Function.grad x i)
        (volumeMeasureOn (cubeSet Q)) :=
    (ρ.toH10.toH1Function.grad_memL2 i).integrable
      (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
  have hzero :
      (fun i => ∫ x in cubeSet Q, ρ.toH10.toH1Function.grad x i ∂MeasureTheory.volume) = 0 :=
    IsPotentialZeroTraceOn.integral_eq_zero ρ.toH10.isPotentialZeroTraceOn
  have hzeroi : ∫ x in cubeSet Q, ρ.toH10.toH1Function.grad x i ∂MeasureTheory.volume = 0 := by
    simpa using congrFun hzero i
  rw [MeasureTheory.integral_add hvi_int hρi_int, hzeroi]
  simp [volumeMeasureOn]

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_two_mul_add
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hu : MemVectorL2 (cubeSet Q) u)
    (s : ℝ) (N : ℕ) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ρ.toH10.toH1Function.grad x)) ^ 2 ≤
      2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 +
        2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x)) ^ 2 := by
  have hEq :
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => ρ.toH10.toH1Function.grad x) =
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => u x - w.toH1.grad x) := by
    apply cubeBesovNegativeVectorPartialSeminormTwo_eq_of_eq_on_cubeSet s N
    intro x hx
    ext i
    change ρ.toH10.toH1Function.grad x i = u x i - w.toH1.grad x i
    have hcoord : u x i = w.toH1.grad x i + ρ.toH10.toH1Function.grad x i := by
      simpa using congrArg (fun z => z i) (huw x hx)
    linarith
  rw [hEq]
  exact
    sq_cubeBesovNegativeVectorPartialSeminormTwo_sub_le_two_mul_add
      Q s u (fun x => w.toH1.grad x) hu w.toH1.grad_memVectorL2 N

theorem cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_sqrtTwo_mul_add
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hu : MemVectorL2 (cubeSet Q) u)
    (s : ℝ) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ρ.toH10.toH1Function.grad x) ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N
            (fun x => w.toH1.grad x)) := by
  have hsq :=
    ρ.sq_cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_two_mul_add
      (u := u) w huw hu s N
  have hρ_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ρ.toH10.toH1Function.grad x) :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N
      (fun x => ρ.toH10.toH1Function.grad x)
  have hu_nonneg : 0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N u :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N u
  have hw_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => w.toH1.grad x) :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N
      (fun x => w.toH1.grad x)
  have hsum_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
        cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => w.toH1.grad x) :=
    add_nonneg hu_nonneg hw_nonneg
  have hsq_bound :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => ρ.toH10.toH1Function.grad x)) ^ 2 ≤
        (Real.sqrt 2 *
          (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
            cubeBesovNegativeVectorPartialSeminormTwo Q s N
              (fun x => w.toH1.grad x))) ^ 2 := by
    calc
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => ρ.toH10.toH1Function.grad x)) ^ 2
          ≤
        2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 +
          2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N
            (fun x => w.toH1.grad x)) ^ 2 := hsq
      _ ≤ 2 *
          (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
            cubeBesovNegativeVectorPartialSeminormTwo Q s N
              (fun x => w.toH1.grad x)) ^ 2 := by
            nlinarith
      _ = (Real.sqrt 2 *
            (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
              cubeBesovNegativeVectorPartialSeminormTwo Q s N
                (fun x => w.toH1.grad x))) ^ 2 := by
            have hsqrt2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
              nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
            calc
              2 *
                  (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
                    cubeBesovNegativeVectorPartialSeminormTwo Q s N
                      (fun x => w.toH1.grad x)) ^ 2
                  =
                (Real.sqrt 2) ^ 2 *
                  (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
                    cubeBesovNegativeVectorPartialSeminormTwo Q s N
                      (fun x => w.toH1.grad x)) ^ 2 := by
                        rw [hsqrt2]
              _ =
                (Real.sqrt 2 *
                  (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
                    cubeBesovNegativeVectorPartialSeminormTwo Q s N
                      (fun x => w.toH1.grad x))) ^ 2 := by
                        ring
  have hright_nonneg :
      0 ≤ Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N
            (fun x => w.toH1.grad x)) := by
    exact mul_nonneg (Real.sqrt_nonneg _) hsum_nonneg
  nlinarith

theorem cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_sqrtTwo_mul_add_of_bounds
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hu : MemVectorL2 (cubeSet Q) u)
    (s : ℝ) {Bu Bw : ℝ}
    (huB : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤ Bu)
    (hwB : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => w.toH1.grad x) ≤ Bw) :
    ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => ρ.toH10.toH1Function.grad x) ≤
        Real.sqrt 2 * (Bu + Bw) := by
  intro N
  calc
    cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ρ.toH10.toH1Function.grad x)
        ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N
            (fun x => w.toH1.grad x)) := by
              exact
                ρ.cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_sqrtTwo_mul_add
                  (u := u) w huw hu s N
    _ ≤ Real.sqrt 2 * (Bu + Bw) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add (huB N) (hwB N)) (Real.sqrt_nonneg _)

theorem cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_sqrtTwo_mul_add_of_bddAbove
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hu : MemVectorL2 (cubeSet Q) u)
    (s : ℝ)
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x))) :
    ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => ρ.toH10.toH1Function.grad x) ≤
        Real.sqrt 2 *
          (cubeBesovNegativeVectorSeminormTwo Q s u +
            cubeBesovNegativeVectorSeminormTwo Q s
              (fun x => w.toH1.grad x)) := by
  exact
    ρ.cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_sqrtTwo_mul_add_of_bounds
      (u := u) w huw hu s
      (Bu := cubeBesovNegativeVectorSeminormTwo Q s u)
      (Bw := cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x))
      (fun N =>
        cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
          Q s u huBdd N)
      (fun N =>
        cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
          Q s (fun x => w.toH1.grad x) hwBdd N)



end ZeroTraceDirichletCorrectorData

end

end Homogenization
