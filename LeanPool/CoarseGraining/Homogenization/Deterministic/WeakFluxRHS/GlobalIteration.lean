/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.DepthWeightAlgebra
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AveragedStepping

/-! # Global Iteration -/

namespace Homogenization

noncomputable section

open scoped BigOperators

/-- Averaged squared `q = 2` weak-flux seminorm at descendant depth `j`. -/
noncomputable def weakFluxRHSAveragedSeminormSq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (j : ℕ) : ℝ :=
  descendantsAverage Q j
    (fun R =>
      (cubeBesovNegativeVectorSeminormTwo R s
        (fun x => matVecMul (a x) (u x))) ^ 2)

@[simp] theorem weakFluxRHSAveragedSeminormSq_zero {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) :
    weakFluxRHSAveragedSeminormSq Q a s u 0 =
      (cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (u x))) ^ 2 := by
  simp [weakFluxRHSAveragedSeminormSq, descendantsAverage]

theorem weakFluxRHSAveragedSeminormSq_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (j : ℕ) :
    0 ≤ weakFluxRHSAveragedSeminormSq Q a s u j := by
  exact descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _

/-- Finite weighted error sum produced by iterating the weak-flux recurrence. -/
noncomputable def weakFluxRHSAveragedErrorSum {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (E : TriadicCube d → ℝ)
    (m N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    (Real.rpow (3 : ℝ) (-2 * s)) ^ k * descendantsAverage Q (m + k) E

/-- Manuscript `T_n`-style scaled averaged weak-flux quantity. -/
noncomputable def weakFluxRHSScaledAveragedSeminormSq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (j : ℕ) : ℝ :=
  coarsePoincareRHSDepthWeight s j *
    weakFluxRHSAveragedSeminormSq Q a s u j

@[simp] theorem weakFluxRHSScaledAveragedSeminormSq_zero {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) :
    weakFluxRHSScaledAveragedSeminormSq Q a s u 0 =
      (cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (u x))) ^ 2 := by
  simp [weakFluxRHSScaledAveragedSeminormSq]

theorem weakFluxRHSScaledAveragedSeminormSq_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (j : ℕ) :
    0 ≤ weakFluxRHSScaledAveragedSeminormSq Q a s u j := by
  unfold weakFluxRHSScaledAveragedSeminormSq coarsePoincareRHSDepthWeight
  exact mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (weakFluxRHSAveragedSeminormSq_nonneg Q a s u j)

/-- Finite weighted error sum for the scaled weak-flux recurrence. -/
noncomputable def weakFluxRHSScaledAveragedErrorSum {d : ℕ}
    (Q : TriadicCube d) (s θ : ℝ) (E : TriadicCube d → ℝ)
    (m N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    (coarsePoincareRHSScaledStepCoeff s θ) ^ k *
      (coarsePoincareRHSDepthWeight s (m + k) *
        descendantsAverage Q (m + k) E)

theorem weakFluxRHSScaledStepCoeff_eq (s : ℝ) :
    coarsePoincareRHSScaledStepCoeff s (Real.rpow (3 : ℝ) (-2 * s)) =
      Real.rpow (3 : ℝ) (-s) := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  unfold coarsePoincareRHSScaledStepCoeff
  calc
    Real.rpow (3 : ℝ) (-2 * s) * Real.rpow (3 : ℝ) s =
        Real.rpow (3 : ℝ) ((-2 * s) + s) := by
          exact (Real.rpow_add h3 (-2 * s) s).symm
    _ = Real.rpow (3 : ℝ) (-s) := by
          congr 1
          ring

/-- A uniform base bound on the weighted averaged error terms controls the
finite scaled weak-flux error sum by a geometric tail. -/
theorem weakFluxRHSScaledAveragedErrorSum_le_base_mul_inv_one_sub
    {d : ℕ} (Q : TriadicCube d) (s θ : ℝ) (E : TriadicCube d → ℝ)
    (m N : ℕ) {B : ℝ}
    (hr_nonneg : 0 ≤ coarsePoincareRHSScaledStepCoeff s θ)
    (hr_lt_one : coarsePoincareRHSScaledStepCoeff s θ < 1)
    (hB_nonneg : 0 ≤ B)
    (hterm :
      ∀ k ∈ Finset.range N,
        coarsePoincareRHSDepthWeight s (m + k) *
          descendantsAverage Q (m + k) E ≤ B) :
    weakFluxRHSScaledAveragedErrorSum Q s θ E m N ≤
      B * (1 - coarsePoincareRHSScaledStepCoeff s θ)⁻¹ := by
  unfold weakFluxRHSScaledAveragedErrorSum
  calc
    ∑ k ∈ Finset.range N,
        (coarsePoincareRHSScaledStepCoeff s θ) ^ k *
          (coarsePoincareRHSDepthWeight s (m + k) *
            descendantsAverage Q (m + k) E)
        ≤
          ∑ k ∈ Finset.range N,
            (coarsePoincareRHSScaledStepCoeff s θ) ^ k * B := by
            refine Finset.sum_le_sum ?_
            intro k hk
            exact mul_le_mul_of_nonneg_left (hterm k hk)
              (pow_nonneg hr_nonneg k)
    _ =
          B *
            ∑ k ∈ Finset.range N,
              (coarsePoincareRHSScaledStepCoeff s θ) ^ k := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k hk
            ring
    _ ≤ B * (1 - coarsePoincareRHSScaledStepCoeff s θ)⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (geom_sum_range_le_of_lt_one hr_nonneg hr_lt_one) hB_nonneg

/-- Note-facing form of the scaled weak-flux error summation: after the
natural `T_n` scaling the one-step ratio is `3^{-s}`. -/
theorem weakFluxRHSScaledAveragedErrorSum_le_base_mul_inv_one_sub_weakFlux
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (E : TriadicCube d → ℝ)
    (m N : ℕ) {B : ℝ}
    (hs : 0 < s) (hB_nonneg : 0 ≤ B)
    (hterm :
      ∀ k ∈ Finset.range N,
        coarsePoincareRHSDepthWeight s (m + k) *
          descendantsAverage Q (m + k) E ≤ B) :
    weakFluxRHSScaledAveragedErrorSum Q s (Real.rpow (3 : ℝ) (-2 * s)) E m N ≤
      B * (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
  have hr_nonneg :
      0 ≤ coarsePoincareRHSScaledStepCoeff s (Real.rpow (3 : ℝ) (-2 * s)) := by
    rw [weakFluxRHSScaledStepCoeff_eq]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hr_lt_one :
      coarsePoincareRHSScaledStepCoeff s (Real.rpow (3 : ℝ) (-2 * s)) < 1 := by
    rw [weakFluxRHSScaledStepCoeff_eq]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 3) (by linarith)
  have hsum :=
    weakFluxRHSScaledAveragedErrorSum_le_base_mul_inv_one_sub
      Q s (Real.rpow (3 : ℝ) (-2 * s)) E m N
      hr_nonneg hr_lt_one hB_nonneg hterm
  rwa [weakFluxRHSScaledStepCoeff_eq] at hsum

/-- The localized `ℓ²` flux-defect average used by the Section 3.3 black boxes
is the square root of the averaged squared weak-flux quantity. -/
@[simp] theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_eq_sqrt_weakFluxRHSAveragedSeminormSq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (j : ℕ) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) j =
      Real.sqrt (weakFluxRHSAveragedSeminormSq Q a s u j) := by
  rfl

/-- Square-root extraction from a bound on the averaged squared weak-flux
quantity. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_weakFluxRHSAveragedSeminormSq_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (j : ℕ) {B : ℝ}
    (hB :
      weakFluxRHSAveragedSeminormSq Q a s u j ≤ B) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) j ≤
      Real.sqrt B := by
  simpa using Real.sqrt_le_sqrt hB

/-- Square-root extraction from a square bound on the averaged weak-flux
quantity. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_of_weakFluxRHSAveragedSeminormSq_le_sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (j : ℕ) {B : ℝ}
    (hB_nonneg : 0 ≤ B)
    (hB :
      weakFluxRHSAveragedSeminormSq Q a s u j ≤ B ^ 2) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) j ≤ B := by
  simpa using (Real.sqrt_le_iff).2 ⟨hB_nonneg, hB⟩

/-- Finite-scale iteration of the averaged weak-flux recurrence.  This is the
direct Lean form of manuscript Section 3.2.3, Step 4, before the error terms
are localized and summed with the final constants. -/
theorem weakFluxRHSAveragedSeminormSq_iterate_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (E : TriadicCube d → ℝ)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          E R)
    (m N : ℕ) :
    weakFluxRHSAveragedSeminormSq Q a s u m ≤
      (Real.rpow (3 : ℝ) (-2 * s)) ^ N *
        weakFluxRHSAveragedSeminormSq Q a s u (m + N) +
      weakFluxRHSAveragedErrorSum Q s E m N := by
  let γ : ℝ := Real.rpow (3 : ℝ) (-2 * s)
  let Rseq : ℕ → ℝ := fun j => weakFluxRHSAveragedSeminormSq Q a s u j
  let Eseq : ℕ → ℝ := fun j => descendantsAverage Q j E
  have hγ_nonneg : 0 ≤ γ := by
    dsimp [γ]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hstep : ∀ j : ℕ, Rseq j ≤ γ * Rseq (j + 1) + Eseq j := by
    intro j
    simpa [Rseq, Eseq, γ, weakFluxRHSAveragedSeminormSq] using
      descendantsAverage_sq_cubeBesovNegativeVectorSeminormTwo_flux_le_discount_next_add_error_of_localBound
        (Q := Q) (a := a) (s := s) (u := u) (j := j) (E := E)
        (hlocal j)
  simpa [Rseq, Eseq, γ, weakFluxRHSAveragedSeminormSq,
    weakFluxRHSAveragedErrorSum] using
    real_forward_recurrence_iterate_le
      (R := Rseq) (E := Eseq) hγ_nonneg hstep m N

/-- Finite-scale iteration of the manuscript `T_n`-scaled averaged weak-flux
recurrence.  The one-step coefficient becomes `3^{-s}` after multiplying by
the natural depth weight. -/
theorem weakFluxRHSScaledAveragedSeminormSq_iterate_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (E : TriadicCube d → ℝ)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          E R)
    (m N : ℕ) :
    weakFluxRHSScaledAveragedSeminormSq Q a s u m ≤
      (coarsePoincareRHSScaledStepCoeff s (Real.rpow (3 : ℝ) (-2 * s))) ^ N *
        weakFluxRHSScaledAveragedSeminormSq Q a s u (m + N) +
      weakFluxRHSScaledAveragedErrorSum Q s (Real.rpow (3 : ℝ) (-2 * s)) E m N := by
  let γ : ℝ := Real.rpow (3 : ℝ) (-2 * s)
  let Sseq : ℕ → ℝ := fun j => weakFluxRHSScaledAveragedSeminormSq Q a s u j
  let Eseq : ℕ → ℝ := fun j =>
    coarsePoincareRHSDepthWeight s j * descendantsAverage Q j E
  have hγ_nonneg : 0 ≤ γ := by
    dsimp [γ]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hscaled_nonneg : 0 ≤ coarsePoincareRHSScaledStepCoeff s γ := by
    unfold coarsePoincareRHSScaledStepCoeff
    exact mul_nonneg hγ_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hstep : ∀ j : ℕ,
      Sseq j ≤ coarsePoincareRHSScaledStepCoeff s γ * Sseq (j + 1) + Eseq j := by
    intro j
    have hR :
        weakFluxRHSAveragedSeminormSq Q a s u j ≤
          γ * weakFluxRHSAveragedSeminormSq Q a s u (j + 1) +
            descendantsAverage Q j E := by
      simpa [γ, weakFluxRHSAveragedSeminormSq] using
        descendantsAverage_sq_cubeBesovNegativeVectorSeminormTwo_flux_le_discount_next_add_error_of_localBound
          (Q := Q) (a := a) (s := s) (u := u) (j := j) (E := E)
          (hlocal j)
    have hweight_nonneg : 0 ≤ coarsePoincareRHSDepthWeight s j := by
      unfold coarsePoincareRHSDepthWeight
      exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    have hmul :
        coarsePoincareRHSDepthWeight s j * weakFluxRHSAveragedSeminormSq Q a s u j ≤
          coarsePoincareRHSDepthWeight s j *
            (γ * weakFluxRHSAveragedSeminormSq Q a s u (j + 1) +
              descendantsAverage Q j E) :=
      mul_le_mul_of_nonneg_left hR hweight_nonneg
    have hweight :
        coarsePoincareRHSDepthWeight s j * γ =
          coarsePoincareRHSScaledStepCoeff s γ * coarsePoincareRHSDepthWeight s (j + 1) := by
      simpa using
        (coarsePoincareRHSDepthWeight_mul_theta_pow_eq_scaledStepCoeff_mul
          s γ j 1)
    calc
      Sseq j
          =
            coarsePoincareRHSDepthWeight s j *
              weakFluxRHSAveragedSeminormSq Q a s u j := by
              rfl
      _ ≤
            coarsePoincareRHSDepthWeight s j *
              (γ * weakFluxRHSAveragedSeminormSq Q a s u (j + 1) +
                descendantsAverage Q j E) := hmul
      _ =
            coarsePoincareRHSScaledStepCoeff s γ * Sseq (j + 1) + Eseq j := by
              calc
                coarsePoincareRHSDepthWeight s j *
                    (γ * weakFluxRHSAveragedSeminormSq Q a s u (j + 1) +
                      descendantsAverage Q j E)
                    =
                      (coarsePoincareRHSDepthWeight s j * γ) *
                          weakFluxRHSAveragedSeminormSq Q a s u (j + 1) +
                        coarsePoincareRHSDepthWeight s j *
                          descendantsAverage Q j E := by
                          ring
                _ =
                      (coarsePoincareRHSScaledStepCoeff s γ *
                          coarsePoincareRHSDepthWeight s (j + 1)) *
                          weakFluxRHSAveragedSeminormSq Q a s u (j + 1) +
                        coarsePoincareRHSDepthWeight s j *
                          descendantsAverage Q j E := by
                          rw [hweight]
                _ =
                      coarsePoincareRHSScaledStepCoeff s γ * Sseq (j + 1) +
                        Eseq j := by
                          simp [Sseq, Eseq, weakFluxRHSScaledAveragedSeminormSq,
                            mul_assoc]
  simpa [Sseq, Eseq, γ, weakFluxRHSScaledAveragedSeminormSq,
    weakFluxRHSScaledAveragedErrorSum] using
    real_forward_recurrence_iterate_le
      (R := Sseq) (E := Eseq) hscaled_nonneg hstep m N

/-- The scaled weak-flux terminal term vanishes under boundedness and `s > 0`. -/
theorem weakFluxRHSScaledAveragedSeminormSq_terminal_tendsto_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (m : ℕ)
    (hs : 0 < s)
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n)) :
    Filter.Tendsto
      (fun N : ℕ =>
        (coarsePoincareRHSScaledStepCoeff s (Real.rpow (3 : ℝ) (-2 * s))) ^ N *
          weakFluxRHSScaledAveragedSeminormSq Q a s u (m + N))
      Filter.atTop (nhds 0) := by
  have hshift_bdd :
      BddAbove (Set.range fun N : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u (m + N)) := by
    rcases hBdd with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact hB ⟨m + N, rfl⟩
  exact
    tendsto_pow_mul_of_nonneg_bddAbove
      (r := coarsePoincareRHSScaledStepCoeff s (Real.rpow (3 : ℝ) (-2 * s)))
      (F := fun N : ℕ => weakFluxRHSScaledAveragedSeminormSq Q a s u (m + N))
      (by
        rw [weakFluxRHSScaledStepCoeff_eq]
        exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (by
        rw [weakFluxRHSScaledStepCoeff_eq]
        exact Real.rpow_lt_one_of_one_lt_of_neg
          (by norm_num : (1 : ℝ) < 3) (by linarith))
      (fun N => weakFluxRHSScaledAveragedSeminormSq_nonneg Q a s u (m + N))
      hshift_bdd

/-- Infinite-depth terminal passage for the scaled weak-flux recurrence. -/
theorem weakFluxRHSScaledAveragedSeminormSq_le_of_terminal_tendsto
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (E : TriadicCube d → ℝ)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          E R)
    (m : ℕ) {B : ℝ}
    (hterminal :
      Filter.Tendsto
        (fun N : ℕ =>
          (coarsePoincareRHSScaledStepCoeff s (Real.rpow (3 : ℝ) (-2 * s))) ^ N *
            weakFluxRHSScaledAveragedSeminormSq Q a s u (m + N))
        Filter.atTop (nhds 0))
    (hError :
      ∀ N : ℕ,
        weakFluxRHSScaledAveragedErrorSum Q s (Real.rpow (3 : ℝ) (-2 * s)) E m N ≤ B) :
    weakFluxRHSScaledAveragedSeminormSq Q a s u m ≤ B := by
  refine real_le_of_forall_le_add_of_tendsto_zero hterminal ?_
  intro N
  have hiter :=
    weakFluxRHSScaledAveragedSeminormSq_iterate_le Q a s u E hlocal m N
  calc
    weakFluxRHSScaledAveragedSeminormSq Q a s u m
        ≤
          (coarsePoincareRHSScaledStepCoeff s (Real.rpow (3 : ℝ) (-2 * s))) ^ N *
            weakFluxRHSScaledAveragedSeminormSq Q a s u (m + N) +
          weakFluxRHSScaledAveragedErrorSum Q s (Real.rpow (3 : ℝ) (-2 * s)) E m N :=
        hiter
    _ ≤
          (coarsePoincareRHSScaledStepCoeff s (Real.rpow (3 : ℝ) (-2 * s))) ^ N *
            weakFluxRHSScaledAveragedSeminormSq Q a s u (m + N) +
          B := by
        exact add_le_add_right (hError N) _

/-- Infinite-depth scaled weak-flux bound using boundedness to discharge the
terminal term. -/
theorem weakFluxRHSScaledAveragedSeminormSq_le_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (E : TriadicCube d → ℝ)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          E R)
    (m : ℕ) {B : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hError :
      ∀ N : ℕ,
        weakFluxRHSScaledAveragedErrorSum Q s (Real.rpow (3 : ℝ) (-2 * s)) E m N ≤ B) :
    weakFluxRHSScaledAveragedSeminormSq Q a s u m ≤ B :=
  weakFluxRHSScaledAveragedSeminormSq_le_of_terminal_tendsto
    Q a s u E hlocal m
    (weakFluxRHSScaledAveragedSeminormSq_terminal_tendsto_of_bddAbove
      Q a s u m hs hBdd)
    hError

/-- Bounded-tail scaled weak-flux iteration with the finite error sums closed
by a uniform geometric base bound. -/
theorem weakFluxRHSScaledAveragedSeminormSq_le_base_mul_inv_one_sub_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (E : TriadicCube d → ℝ)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          E R)
    (m : ℕ) {B : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hB_nonneg : 0 ≤ B)
    (hterm :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          descendantsAverage Q (m + k) E ≤ B) :
    weakFluxRHSScaledAveragedSeminormSq Q a s u m ≤
      B * (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
  exact
    weakFluxRHSScaledAveragedSeminormSq_le_of_bddAbove
      Q a s u E hs hlocal m hBdd
      (fun N =>
        weakFluxRHSScaledAveragedErrorSum_le_base_mul_inv_one_sub_weakFlux
          Q s E m N hs hB_nonneg fun k hk => hterm k)

/-- Convert a scaled `T_m` bound back to the unscaled averaged weak-flux
quantity. -/
theorem weakFluxRHSAveragedSeminormSq_le_inv_depthWeight_mul_of_scaled_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (m : ℕ) {B : ℝ}
    (hB : weakFluxRHSScaledAveragedSeminormSq Q a s u m ≤ B) :
    weakFluxRHSAveragedSeminormSq Q a s u m ≤
      (coarsePoincareRHSDepthWeight s m)⁻¹ * B := by
  have hweight_pos : 0 < coarsePoincareRHSDepthWeight s m := by
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
  calc
    weakFluxRHSAveragedSeminormSq Q a s u m
        =
          (coarsePoincareRHSDepthWeight s m)⁻¹ *
            (coarsePoincareRHSDepthWeight s m *
              weakFluxRHSAveragedSeminormSq Q a s u m) := by
          field_simp [hweight_pos.ne']
    _ ≤ (coarsePoincareRHSDepthWeight s m)⁻¹ * B := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [weakFluxRHSScaledAveragedSeminormSq] using hB)
            (inv_nonneg.mpr hweight_pos.le)

/-- Localized flux-defect handoff from a scaled averaged weak-flux bound. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_weakFluxRHSScaledAveragedSeminormSq_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (m : ℕ) {B : ℝ}
    (hB : weakFluxRHSScaledAveragedSeminormSq Q a s u m ≤ B) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) m ≤
      Real.sqrt ((coarsePoincareRHSDepthWeight s m)⁻¹ * B) := by
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_weakFluxRHSAveragedSeminormSq_le
      Q a s u m
      (weakFluxRHSAveragedSeminormSq_le_inv_depthWeight_mul_of_scaled_le
        Q a s u m hB)

/-- Localized flux-defect form of the scaled bounded-tail weak-flux iteration. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (E : TriadicCube d → ℝ)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          E R)
    (m : ℕ) {B : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hError :
      ∀ N : ℕ,
        weakFluxRHSScaledAveragedErrorSum Q s (Real.rpow (3 : ℝ) (-2 * s)) E m N ≤ B) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) m ≤
      Real.sqrt ((coarsePoincareRHSDepthWeight s m)⁻¹ * B) := by
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_weakFluxRHSScaledAveragedSeminormSq_le
      Q a s u m
      (weakFluxRHSScaledAveragedSeminormSq_le_of_bddAbove
        Q a s u E hs hlocal m hBdd hError)

/-- Localized flux-defect form of the scaled bounded-tail weak-flux iteration
after closing the finite error sums by a uniform geometric base bound. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_base_mul_inv_one_sub_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (E : TriadicCube d → ℝ)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          E R)
    (m : ℕ) {B : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hB_nonneg : 0 ≤ B)
    (hterm :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          descendantsAverage Q (m + k) E ≤ B) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          (B * (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_weakFluxRHSScaledAveragedSeminormSq_le
      Q a s u m
      (weakFluxRHSScaledAveragedSeminormSq_le_base_mul_inv_one_sub_of_bddAbove
        Q a s u E hs hlocal m hBdd hB_nonneg hterm)

/-- The discounted terminal term vanishes if the averaged weak-flux seminorms
are bounded above and `s > 0`. -/
theorem weakFluxRHSAveragedSeminormSq_terminal_tendsto_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (m : ℕ)
    (hs : 0 < s)
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSAveragedSeminormSq Q a s u n)) :
    Filter.Tendsto
      (fun N : ℕ =>
        (Real.rpow (3 : ℝ) (-2 * s)) ^ N *
          weakFluxRHSAveragedSeminormSq Q a s u (m + N))
      Filter.atTop (nhds 0) := by
  have hshift_bdd :
      BddAbove (Set.range fun N : ℕ =>
        weakFluxRHSAveragedSeminormSq Q a s u (m + N)) := by
    rcases hBdd with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact hB ⟨m + N, rfl⟩
  exact
    tendsto_pow_mul_of_nonneg_bddAbove
      (r := Real.rpow (3 : ℝ) (-2 * s))
      (F := fun N : ℕ => weakFluxRHSAveragedSeminormSq Q a s u (m + N))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 3) (by nlinarith [hs]))
      (fun N => by
        exact descendantsAverage_nonneg Q (m + N) _ fun R hR => sq_nonneg _)
      hshift_bdd

/-- Infinite-depth terminal passage for the averaged weak-flux recurrence.  Once
the terminal term tends to zero, any uniform bound on the finite weighted error
sums bounds the initial averaged seminorm. -/
theorem weakFluxRHSAveragedSeminormSq_le_of_terminal_tendsto
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (E : TriadicCube d → ℝ)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          E R)
    (m : ℕ) {B : ℝ}
    (hterminal :
      Filter.Tendsto
        (fun N : ℕ =>
          (Real.rpow (3 : ℝ) (-2 * s)) ^ N *
            weakFluxRHSAveragedSeminormSq Q a s u (m + N))
        Filter.atTop (nhds 0))
    (hError : ∀ N : ℕ, weakFluxRHSAveragedErrorSum Q s E m N ≤ B) :
    weakFluxRHSAveragedSeminormSq Q a s u m ≤ B := by
  refine real_le_of_forall_le_add_of_tendsto_zero hterminal ?_
  intro N
  have hiter :=
    weakFluxRHSAveragedSeminormSq_iterate_le Q a s u E hlocal m N
  calc
    weakFluxRHSAveragedSeminormSq Q a s u m
        ≤
          (Real.rpow (3 : ℝ) (-2 * s)) ^ N *
            weakFluxRHSAveragedSeminormSq Q a s u (m + N) +
          weakFluxRHSAveragedErrorSum Q s E m N := hiter
    _ ≤
          (Real.rpow (3 : ℝ) (-2 * s)) ^ N *
            weakFluxRHSAveragedSeminormSq Q a s u (m + N) +
          B := by
        exact add_le_add_right (hError N) _

/-- Infinite-depth weak-flux bound using boundedness of the averaged seminorm
sequence to discharge the terminal term. -/
theorem weakFluxRHSAveragedSeminormSq_le_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (E : TriadicCube d → ℝ)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          E R)
    (m : ℕ) {B : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSAveragedSeminormSq Q a s u n))
    (hError : ∀ N : ℕ, weakFluxRHSAveragedErrorSum Q s E m N ≤ B) :
    weakFluxRHSAveragedSeminormSq Q a s u m ≤ B :=
  weakFluxRHSAveragedSeminormSq_le_of_terminal_tendsto
    Q a s u E hlocal m
    (weakFluxRHSAveragedSeminormSq_terminal_tendsto_of_bddAbove
      Q a s u m hs hBdd)
    hError

/-- Localized flux-defect form of the bounded-tail weak-flux iteration. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (E : TriadicCube d → ℝ)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          E R)
    (m : ℕ) {B : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSAveragedSeminormSq Q a s u n))
    (hError : ∀ N : ℕ, weakFluxRHSAveragedErrorSum Q s E m N ≤ B) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) m ≤
      Real.sqrt B := by
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_weakFluxRHSAveragedSeminormSq_le
      Q a s u m
      (weakFluxRHSAveragedSeminormSq_le_of_bddAbove
        Q a s u E hs hlocal m hBdd hError)

end

end Homogenization
