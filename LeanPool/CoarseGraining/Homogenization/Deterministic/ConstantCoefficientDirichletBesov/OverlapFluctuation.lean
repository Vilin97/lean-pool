/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapCenters

/-! # Overlap Fluctuation -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

/-- Average over the overlapping centers at a fixed depth. -/
noncomputable def overlapCentersAverage {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ) : ℝ :=
  let D := overlapCentersAtDepth Q j
  ((D.card : ℝ)⁻¹) * D.sum F

theorem overlapCentersAverage_add {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F G : TriadicCube d → ℝ) :
    overlapCentersAverage Q j (fun S => F S + G S) =
      overlapCentersAverage Q j F + overlapCentersAverage Q j G := by
  classical
  let D := overlapCentersAtDepth Q j
  change (↑D.card)⁻¹ * D.sum (fun S => F S + G S) =
    (↑D.card)⁻¹ * D.sum F + (↑D.card)⁻¹ * D.sum G
  rw [Finset.sum_add_distrib, left_distrib]

theorem overlapCentersAverage_mul_left {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (c : ℝ) (F : TriadicCube d → ℝ) :
    overlapCentersAverage Q j (fun S => c * F S) =
      c * overlapCentersAverage Q j F := by
  classical
  let D := overlapCentersAtDepth Q j
  calc
    overlapCentersAverage Q j (fun S => c * F S)
        = ((D.card : ℝ)⁻¹) * D.sum (fun S => c * F S) := by
          rfl
    _ = ((D.card : ℝ)⁻¹) * (c * D.sum F) := by
          rw [← Finset.mul_sum]
    _ = c * overlapCentersAverage Q j F := by
          unfold overlapCentersAverage
          ring

theorem overlapCentersAverage_le_overlapCentersAverage {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) {F G : TriadicCube d → ℝ}
    (hFG : ∀ S ∈ overlapCentersAtDepth Q j, F S ≤ G S) :
    overlapCentersAverage Q j F ≤ overlapCentersAverage Q j G := by
  classical
  unfold overlapCentersAverage
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum hFG)
    (inv_nonneg.mpr (by positivity))

theorem overlapCentersAverage_const_eq {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (c : ℝ)
    (hD : (overlapCentersAtDepth Q j).Nonempty) :
    overlapCentersAverage Q j (fun _ => c) = c := by
  classical
  let D := overlapCentersAtDepth Q j
  change ((D.card : ℝ)⁻¹) * D.sum (fun _ => c) = c
  have hD' : D.Nonempty := by
    simpa [D] using hD
  have hcard : (((D.card : ℕ) : ℝ) ≠ 0) := by
    exact_mod_cast (Finset.card_ne_zero.mpr hD')
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem overlapCentersAverage_const {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (c : ℝ) :
    overlapCentersAverage Q j (fun _ => c) = c :=
  overlapCentersAverage_const_eq Q j c (overlapCentersAtDepth_nonempty Q j)

theorem overlapCentersAverage_nonneg {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ)
    (hF : ∀ S ∈ overlapCentersAtDepth Q j, 0 ≤ F S) :
    0 ≤ overlapCentersAverage Q j F := by
  unfold overlapCentersAverage
  exact mul_nonneg (inv_nonneg.mpr (by positivity))
    (Finset.sum_nonneg hF)

theorem overlapCentersAverage_L2_sum_le_sum_overlapCentersAverage_L2
    {d : ℕ} {ι : Type*}
    (Q : TriadicCube d) (j : ℕ) (s : Finset ι) (A : TriadicCube d → ι → ℝ)
    (hA : ∀ S ∈ overlapCentersAtDepth Q j, ∀ i ∈ s, 0 ≤ A S i) :
    (overlapCentersAverage Q j (fun S => (∑ i ∈ s, A S i) ^ 2)) ^ (1 / 2 : ℝ) ≤
      ∑ i ∈ s, (overlapCentersAverage Q j (fun S => (A S i) ^ 2)) ^ (1 / 2 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [overlapCentersAverage]
  | @insert a s ha ih =>
      let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
      let c : ℝ := ((D.card : ℝ)⁻¹)
      have hc : 0 ≤ c := by
        dsimp [c]
        exact inv_nonneg.mpr (by positivity)
      have hsum_nonneg : ∀ S ∈ D, 0 ≤ ∑ i ∈ s, A S i := by
        intro S hS
        exact Finset.sum_nonneg fun i hi =>
          hA S (by simpa [D] using hS) i (Finset.mem_insert_of_mem hi)
      have hsum_sq_nonneg : 0 ≤ ∑ S ∈ D, (∑ i ∈ s, A S i) ^ 2 := by
        exact Finset.sum_nonneg fun S hS => sq_nonneg _
      have hsingle_sq_nonneg : 0 ≤ ∑ S ∈ D, (A S a) ^ 2 := by
        exact Finset.sum_nonneg fun S hS => sq_nonneg _
      have hinsert_sq_nonneg : 0 ≤ ∑ S ∈ D, (∑ i ∈ insert a s, A S i) ^ 2 := by
        exact Finset.sum_nonneg fun S hS => sq_nonneg _
      have hLp :
          (∑ S ∈ D, (A S a + ∑ i ∈ s, A S i) ^ 2) ^ (1 / 2 : ℝ) ≤
            (∑ S ∈ D, (A S a) ^ 2) ^ (1 / 2 : ℝ) +
              (∑ S ∈ D, (∑ i ∈ s, A S i) ^ 2) ^ (1 / 2 : ℝ) := by
        simpa using
          (Real.Lp_add_le_of_nonneg
            (s := D)
            (f := fun S => A S a)
            (g := fun S => ∑ i ∈ s, A S i)
            (p := (2 : ℝ))
            (by norm_num)
            (fun S hS => hA S (by simpa [D] using hS) a (by simp [ha]))
            hsum_nonneg)
      calc
        (overlapCentersAverage Q j (fun S => (∑ i ∈ insert a s, A S i) ^ 2)) ^
            (1 / 2 : ℝ)
            = c ^ (1 / 2 : ℝ) *
                (∑ S ∈ D, (A S a + ∑ i ∈ s, A S i) ^ 2) ^ (1 / 2 : ℝ) := by
                have hmul :
                    (c * ∑ S ∈ D, (∑ i ∈ insert a s, A S i) ^ 2) ^ (1 / 2 : ℝ) =
                      c ^ (1 / 2 : ℝ) *
                        (∑ S ∈ D, (∑ i ∈ insert a s, A S i) ^ 2) ^
                          (1 / 2 : ℝ) :=
                  Real.mul_rpow hc hinsert_sq_nonneg
                simpa [overlapCentersAverage, D, c, Finset.sum_insert, ha] using hmul
        _ ≤ c ^ (1 / 2 : ℝ) * (∑ S ∈ D, (A S a) ^ 2) ^ (1 / 2 : ℝ) +
              c ^ (1 / 2 : ℝ) * (∑ S ∈ D, (∑ i ∈ s, A S i) ^ 2) ^ (1 / 2 : ℝ) := by
              have hc_rpow : 0 ≤ c ^ (1 / 2 : ℝ) := Real.rpow_nonneg hc _
              have hmul := mul_le_mul_of_nonneg_left hLp hc_rpow
              simpa [mul_add] using hmul
        _ = (overlapCentersAverage Q j (fun S => (A S a) ^ 2)) ^ (1 / 2 : ℝ) +
              c ^ (1 / 2 : ℝ) *
                (∑ S ∈ D, (∑ i ∈ s, A S i) ^ 2) ^ (1 / 2 : ℝ) := by
              rw [← Real.mul_rpow hc hsingle_sq_nonneg]
              simp [overlapCentersAverage, D, c]
        _ = (overlapCentersAverage Q j (fun S => (A S a) ^ 2)) ^ (1 / 2 : ℝ) +
              (overlapCentersAverage Q j (fun S => (∑ i ∈ s, A S i) ^ 2)) ^
                (1 / 2 : ℝ) := by
              rw [← Real.mul_rpow hc hsum_sq_nonneg]
              simp [overlapCentersAverage, D, c]
        _ ≤ (overlapCentersAverage Q j (fun S => (A S a) ^ 2)) ^ (1 / 2 : ℝ) +
              ∑ i ∈ s,
                (overlapCentersAverage Q j (fun S => (A S i) ^ 2)) ^ (1 / 2 : ℝ) := by
              exact add_le_add le_rfl
                (ih (fun S hS i hi => hA S hS i (Finset.mem_insert_of_mem hi)))
        _ = ∑ i ∈ insert a s,
              (overlapCentersAverage Q j (fun S => (A S i) ^ 2)) ^ (1 / 2 : ℝ) := by
              simp [Finset.sum_insert, ha]

theorem overlapCentersAverage_lintegral_rpow_enorm_two_le {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (Q : TriadicCube d) (j : ℕ) (R : Vec d → E)
    (hR : MeasureTheory.MemLp R (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hRloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp R (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCentersAverage Q j
        (fun S => (∫⁻ x, ‖R x‖ₑ ^ (2 : ℝ)
          ∂ normalizedOverlapCubeMeasure S).toReal)
      ≤ (3 ^ d : ℝ) *
          (∫⁻ x, ‖R x‖ₑ ^ (2 : ℝ) ∂ normalizedCubeMeasure Q).toReal := by
  classical
  let D := overlapCentersAtDepth Q j
  let I : TriadicCube d → ℝ≥0∞ :=
    fun S => ∫⁻ x, ‖R x‖ₑ ^ (2 : ℝ) ∂ normalizedOverlapCubeMeasure S
  let IQ : ℝ≥0∞ := ∫⁻ x, ‖R x‖ₑ ^ (2 : ℝ) ∂ normalizedCubeMeasure Q
  have hfQ :
      AEMeasurable (fun x => ‖R x‖ₑ ^ (2 : ℝ))
        (MeasureTheory.volume.restrict (cubeSet Q)) := by
    have hnorm :
        AEMeasurable (fun x => ‖R x‖ₑ ^ (2 : ℝ))
          (normalizedCubeMeasure Q) :=
      hR.1.aemeasurable.enorm.pow_const (2 : ℝ)
    have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (cubeVolume_pos Q))
    simpa [normalizedCubeMeasure, cubeMeasure] using
      (aemeasurable_smul_measure_iff
        (μ := MeasureTheory.volume.restrict (cubeSet Q))
        (f := fun x => ‖R x‖ₑ ^ (2 : ℝ)) hc).1 hnorm
  have hfS :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable (fun x => ‖R x‖ₑ ^ (2 : ℝ))
          (MeasureTheory.volume.restrict (overlapCubeSet S)) := by
    intro S hS
    have hnorm :
        AEMeasurable (fun x => ‖R x‖ₑ ^ (2 : ℝ))
          (normalizedOverlapCubeMeasure S) :=
      (hRloc S hS).1.aemeasurable.enorm.pow_const (2 : ℝ)
    have hc : ENNReal.ofReal ((overlapCubeVolume S)⁻¹) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (overlapCubeVolume_pos S))
    simpa [normalizedOverlapCubeMeasure, overlapCubeMeasure] using
      (aemeasurable_smul_measure_iff
        (μ := MeasureTheory.volume.restrict (overlapCubeSet S))
        (f := fun x => ‖R x‖ₑ ^ (2 : ℝ)) hc).1 hnorm
  have hle_enn :
      (((D.card : ℝ≥0∞)⁻¹) * (∑ S ∈ D, I S)) ≤
        (3 ^ d : ℝ≥0∞) * IQ := by
    simpa [D, I, IQ] using
      overlapCentersAtDepth_average_lintegral_normalizedOverlapCubeMeasure_le
        (Q := Q) (j := j) (f := fun x => ‖R x‖ₑ ^ (2 : ℝ)) hfQ hfS
  have hIQ_lt_top : IQ < ∞ := by
    simpa [IQ] using
      (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (p := (2 : ℝ≥0∞)) (μ := normalizedCubeMeasure Q) (f := R)
        (by norm_num) (by norm_num)).1 hR.2
  have hIQ_ne_top : IQ ≠ ∞ := ne_of_lt hIQ_lt_top
  have hI_ne_top : ∀ S ∈ D, I S ≠ ∞ := by
    intro S hS
    have hSlt : I S < ∞ := by
      simpa [I] using
        (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
          (p := (2 : ℝ≥0∞)) (μ := normalizedOverlapCubeMeasure S) (f := R)
          (by norm_num) (by norm_num)).1 (hRloc S (by simpa [D] using hS)).2
    exact ne_of_lt hSlt
  have hright_ne_top : (3 ^ d : ℝ≥0∞) * IQ ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (by norm_num : (3 : ℝ≥0∞) ≠ ∞)) hIQ_ne_top
  have htoReal :
      ((((D.card : ℝ≥0∞)⁻¹) * (∑ S ∈ D, I S)).toReal) ≤
        (((3 ^ d : ℝ≥0∞) * IQ).toReal) :=
    ENNReal.toReal_mono hright_ne_top hle_enn
  have hleft_toReal :
      ((((D.card : ℝ≥0∞)⁻¹) * (∑ S ∈ D, I S)).toReal) =
        ((D.card : ℝ)⁻¹) * ∑ S ∈ D, (I S).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum hI_ne_top]
  have hright_toReal :
      (((3 ^ d : ℝ≥0∞) * IQ).toReal) = (3 ^ d : ℝ) * IQ.toReal := by
    simp [ENNReal.toReal_mul]
  rw [hleft_toReal, hright_toReal] at htoReal
  simpa [overlapCentersAverage, D, I, IQ] using htoReal

/-- Vector fluctuation around the overlapping-cube average. -/
noncomputable def overlapCubeFluctuationVec {d : ℕ}
    (S : TriadicCube d) (u : Vec d → Vec d) : Vec d → Vec d :=
  fun x => u x - overlapCubeAverageVec S u

@[simp] theorem overlapCubeFluctuationVec_zero {d : ℕ}
    (S : TriadicCube d) :
    overlapCubeFluctuationVec S (0 : Vec d → Vec d) = 0 := by
  have havg : overlapCubeAverageVec S (0 : Vec d → Vec d) = 0 := by
    change overlapCubeAverageVec S (fun _ : Vec d => (0 : Vec d)) = 0
    simp
  funext x
  simp [overlapCubeFluctuationVec, havg]

theorem overlapCentersAtDepth_average_lintegral_ofReal_vecNormSq_fluctuation_le
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (h : Vec d → Vec d) :
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            ∫⁻ x,
              ENNReal.ofReal
                (vecNormSq (h x - overlapCubeAverageVec S h))
              ∂ normalizedOverlapCubeMeasure S)
      ≤
        (Fintype.card (Fin d) : ℝ≥0∞) *
          ((((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
            (overlapCentersAtDepth Q j).sum
              (fun S =>
                ∫⁻ x,
                  ‖overlapCubeFluctuationVec S h x‖ₑ ^ (2 : ℝ)
                  ∂ normalizedOverlapCubeMeasure S)) := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let cardDim : ℝ≥0∞ := Fintype.card (Fin d)
  let I : TriadicCube d → ℝ≥0∞ :=
    fun S =>
      ∫⁻ x,
        ENNReal.ofReal (vecNormSq (h x - overlapCubeAverageVec S h))
        ∂ normalizedOverlapCubeMeasure S
  let J : TriadicCube d → ℝ≥0∞ :=
    fun S =>
      ∫⁻ x,
        ‖overlapCubeFluctuationVec S h x‖ₑ ^ (2 : ℝ)
        ∂ normalizedOverlapCubeMeasure S
  have hIJ : ∀ S ∈ D, I S ≤ cardDim * J S := by
    intro S _hS
    calc
      I S
          ≤
            ∫⁻ x,
              cardDim * (‖overlapCubeFluctuationVec S h x‖ₑ ^ (2 : ℝ))
              ∂ normalizedOverlapCubeMeasure S := by
            refine MeasureTheory.lintegral_mono ?_
            intro x
            simpa [cardDim, overlapCubeFluctuationVec] using
              ofReal_vecNormSq_le_card_mul_enorm_rpow_two
                (h x - overlapCubeAverageVec S h)
      _ ≤ cardDim * J S := by
            rw [MeasureTheory.lintegral_const_mul'
              (r := cardDim)
              (f := fun x =>
                ‖overlapCubeFluctuationVec S h x‖ₑ ^ (2 : ℝ))]
            simp [cardDim]
  have hsum : D.sum I ≤ D.sum (fun S => cardDim * J S) :=
    Finset.sum_le_sum hIJ
  calc
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            ∫⁻ x,
              ENNReal.ofReal
                (vecNormSq (h x - overlapCubeAverageVec S h))
              ∂ normalizedOverlapCubeMeasure S)
        =
          ((D.card : ℝ≥0∞)⁻¹) * D.sum I := by
          rfl
    _ ≤ ((D.card : ℝ≥0∞)⁻¹) *
          D.sum (fun S => cardDim * J S) := by
          exact mul_le_mul_of_nonneg_left hsum (zero_le)
    _ = ((D.card : ℝ≥0∞)⁻¹) * (cardDim * D.sum J) := by
          congr 1
          rw [Finset.mul_sum]
    _ = cardDim * (((D.card : ℝ≥0∞)⁻¹) * D.sum J) := by
          ac_rfl
    _ =
        (Fintype.card (Fin d) : ℝ≥0∞) *
          ((((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
            (overlapCentersAtDepth Q j).sum
              (fun S =>
                ∫⁻ x,
                  ‖overlapCubeFluctuationVec S h x‖ₑ ^ (2 : ℝ)
                  ∂ normalizedOverlapCubeMeasure S)) := by
          rfl

theorem overlapCubeAverage_add_of_memLp_two {d : ℕ}
    (S : TriadicCube d) {f g : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeAverage S (fun x => f x + g x) =
      overlapCubeAverage S f + overlapCubeAverage S g := by
  have hf_int :
      MeasureTheory.Integrable f (normalizedOverlapCubeMeasure S) :=
    hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
  have hg_int :
      MeasureTheory.Integrable g (normalizedOverlapCubeMeasure S) :=
    hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
  repeat rw [overlapCubeAverage_eq_integral_normalizedOverlapCubeMeasure]
  rw [MeasureTheory.integral_add hf_int hg_int]

theorem overlapCubeAverageVec_add_of_memLp_two {d : ℕ}
    (S : TriadicCube d) {u v : Vec d → Vec d}
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeAverageVec S (fun x => u x + v x) =
      overlapCubeAverageVec S u + overlapCubeAverageVec S v := by
  funext i
  have hui : MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hvi : MeasureTheory.MemLp (fun x => v x i) (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hv
  show overlapCubeAverage S (fun x => (u x + v x) i) =
    overlapCubeAverage S (fun x => u x i) +
      overlapCubeAverage S (fun x => v x i)
  have hfun : (fun x => (u x + v x) i) =
      fun x => u x i + v x i := by
    funext x
    simp
  rw [hfun]
  exact overlapCubeAverage_add_of_memLp_two S hui hvi

theorem memLp_overlapCubeFluctuationVec {d : ℕ}
    (S : TriadicCube d) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    MeasureTheory.MemLp (overlapCubeFluctuationVec S u) (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S) := by
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => overlapCubeAverageVec S u)
        (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) :=
    MeasureTheory.memLp_const (overlapCubeAverageVec S u)
  simpa [overlapCubeFluctuationVec] using! hu.sub hconst

theorem overlapCubeFluctuationVec_add_of_memLp_two {d : ℕ}
    (S : TriadicCube d) {u v : Vec d → Vec d}
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeFluctuationVec S (fun x => u x + v x) =
      fun x => overlapCubeFluctuationVec S u x +
        overlapCubeFluctuationVec S v x := by
  have havg : overlapCubeAverageVec S (fun x => u x + v x) =
      overlapCubeAverageVec S u + overlapCubeAverageVec S v :=
    overlapCubeAverageVec_add_of_memLp_two S hu hv
  funext x i
  simp [overlapCubeFluctuationVec, havg]
  ring

theorem overlapCubeLpNorm_two_overlapCubeFluctuationVec_le_two_mul_overlapCubeLpNorm_two
    {d : ℕ} (S : TriadicCube d) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S u) ≤
      2 * overlapCubeLpNorm S (2 : ℝ≥0∞) u := by
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => -overlapCubeAverageVec S u)
        (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) :=
    MeasureTheory.memLp_const (-overlapCubeAverageVec S u)
  have hadd :
      overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S u) ≤
        overlapCubeLpNorm S (2 : ℝ≥0∞) u +
          overlapCubeLpNorm S (2 : ℝ≥0∞)
            (fun _ : Vec d => -overlapCubeAverageVec S u) := by
    have hfun :
        overlapCubeFluctuationVec S u =
          fun x => u x + (fun _ : Vec d => -overlapCubeAverageVec S u) x := by
      funext x
      simp [overlapCubeFluctuationVec, sub_eq_add_neg]
    rw [hfun]
    exact overlapCubeLpNorm_add_le S (2 : ℝ≥0∞) u
      (fun _ : Vec d => -overlapCubeAverageVec S u) hu hconst (by norm_num)
  calc
    overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S u)
        ≤ overlapCubeLpNorm S (2 : ℝ≥0∞) u +
            overlapCubeLpNorm S (2 : ℝ≥0∞)
              (fun _ : Vec d => -overlapCubeAverageVec S u) := hadd
    _ = overlapCubeLpNorm S (2 : ℝ≥0∞) u + ‖overlapCubeAverageVec S u‖ := by
          rw [overlapCubeLpNorm_const (S := S) (p := (2 : ℝ≥0∞))
            (c := -overlapCubeAverageVec S u) (by norm_num)]
          simp
    _ ≤ overlapCubeLpNorm S (2 : ℝ≥0∞) u +
          overlapCubeLpNorm S (2 : ℝ≥0∞) u := by
          gcongr
          exact norm_overlapCubeAverageVec_le_overlapCubeLpNorm_two S u hu
    _ = 2 * overlapCubeLpNorm S (2 : ℝ≥0∞) u := by ring

theorem sq_overlapCubeLpNorm_two_overlapCubeFluctuationVec_le_four_mul_of_forall_overlapCubeSet_vecNormSq_le
    {d : ℕ} {S : TriadicCube d} {u : Vec d → Vec d} {B : ℝ}
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hB : 0 ≤ B)
    (hpoint : ∀ x ∈ overlapCubeSet S, vecNormSq (u x) ≤ B) :
    (overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S u)) ^ 2 ≤
      4 * B := by
  have hfluct :
      overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S u) ≤
        2 * overlapCubeLpNorm S (2 : ℝ≥0∞) u :=
    overlapCubeLpNorm_two_overlapCubeFluctuationVec_le_two_mul_overlapCubeLpNorm_two
      S u hu
  have hnorm :
      (overlapCubeLpNorm S (2 : ℝ≥0∞) u) ^ 2 ≤ B :=
    overlapCubeLpNorm_two_sq_le_of_forall_overlapCubeSet_vecNormSq_le
      (S := S) (F := u) hB hpoint
  have hsq :
      (overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S u)) ^ 2 ≤
        (2 * overlapCubeLpNorm S (2 : ℝ≥0∞) u) ^ 2 := by
    exact (sq_le_sq₀
      (overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S u))
      (mul_nonneg (by norm_num) (overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞) u))).mpr
      hfluct
  calc
    (overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S u)) ^ 2
        ≤ (2 * overlapCubeLpNorm S (2 : ℝ≥0∞) u) ^ 2 := hsq
    _ = 4 * (overlapCubeLpNorm S (2 : ℝ≥0∞) u) ^ 2 := by ring
    _ ≤ 4 * B := by
          exact mul_le_mul_of_nonneg_left hnorm (by norm_num)

/-- Depth-`j` overlapping positive `q = 2` square average. -/
noncomputable def cubeBesovOverlappingPositiveVectorDepthAverage {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ) : ℝ :=
  overlapCentersAverage Q j fun S =>
    (overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S u)) ^ 2

theorem cubeBesovOverlappingPositiveVectorDepthAverage_nonneg {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ) :
    0 ≤ cubeBesovOverlappingPositiveVectorDepthAverage Q u j := by
  unfold cubeBesovOverlappingPositiveVectorDepthAverage
  exact overlapCentersAverage_nonneg Q j _ fun S _hS => sq_nonneg _

theorem toReal_overlapCentersAtDepth_average_lintegral_fluctuation_eq_depthAverage
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ)
    (hfin :
      ∀ S ∈ overlapCentersAtDepth Q j,
        (∫⁻ x,
          ‖overlapCubeFluctuationVec S u x‖ₑ ^ (2 : ℝ)
          ∂ normalizedOverlapCubeMeasure S) ≠ ∞) :
    ((((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            ∫⁻ x,
              ‖overlapCubeFluctuationVec S u x‖ₑ ^ (2 : ℝ)
              ∂ normalizedOverlapCubeMeasure S)).toReal =
      cubeBesovOverlappingPositiveVectorDepthAverage Q u j := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let I : TriadicCube d → ℝ≥0∞ :=
    fun S =>
      ∫⁻ x,
        ‖overlapCubeFluctuationVec S u x‖ₑ ^ (2 : ℝ)
        ∂ normalizedOverlapCubeMeasure S
  have hleft_toReal :
      ((((D.card : ℝ≥0∞)⁻¹) * D.sum I).toReal) =
        ((D.card : ℝ)⁻¹) * D.sum (fun S => (I S).toReal) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum]
    intro S hS
    exact hfin S (by simpa [D] using hS)
  calc
    ((((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            ∫⁻ x,
              ‖overlapCubeFluctuationVec S u x‖ₑ ^ (2 : ℝ)
              ∂ normalizedOverlapCubeMeasure S)).toReal
        =
          ((D.card : ℝ)⁻¹) * D.sum (fun S => (I S).toReal) := by
          simpa [D, I] using hleft_toReal
    _ = cubeBesovOverlappingPositiveVectorDepthAverage Q u j := by
          unfold cubeBesovOverlappingPositiveVectorDepthAverage
          unfold overlapCentersAverage
          change ((D.card : ℝ)⁻¹) * D.sum (fun S => (I S).toReal) =
            ((D.card : ℝ)⁻¹) *
              D.sum
                (fun S =>
                  (overlapCubeLpNorm S (2 : ℝ≥0∞)
                    (overlapCubeFluctuationVec S u)) ^ 2)
          congr 1
          refine Finset.sum_congr rfl ?_
          intro S _hS
          exact (overlapCubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal
            (E := Vec d) S (overlapCubeFluctuationVec S u)).symm

theorem lintegral_overlapCubeFluctuationVec_rpow_enorm_two_ne_top
    {d : ℕ} (S : TriadicCube d) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S)) :
    (∫⁻ x,
      ‖overlapCubeFluctuationVec S u x‖ₑ ^ (2 : ℝ)
      ∂ normalizedOverlapCubeMeasure S) ≠ ∞ := by
  have hfluct :
      MeasureTheory.MemLp (overlapCubeFluctuationVec S u)
        (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) :=
    memLp_overlapCubeFluctuationVec S u hu
  have hlt :
      (∫⁻ x,
        ‖overlapCubeFluctuationVec S u x‖ₑ ^ (2 : ℝ)
        ∂ normalizedOverlapCubeMeasure S) < ∞ := by
    simpa using
      (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (p := (2 : ℝ≥0∞))
        (μ := normalizedOverlapCubeMeasure S)
        (f := overlapCubeFluctuationVec S u)
        (by norm_num) (by norm_num)).1 hfluct.2
  exact ne_of_lt hlt

theorem overlapCentersAtDepth_average_lintegral_fluctuation_ne_top
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ)
    (hu :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp u (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          ∫⁻ x,
            ‖overlapCubeFluctuationVec S u x‖ₑ ^ (2 : ℝ)
            ∂ normalizedOverlapCubeMeasure S)) ≠ ∞ := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let I : TriadicCube d → ℝ≥0∞ :=
    fun S =>
      ∫⁻ x,
        ‖overlapCubeFluctuationVec S u x‖ₑ ^ (2 : ℝ)
        ∂ normalizedOverlapCubeMeasure S
  have hI : ∀ S ∈ D, I S ≠ ∞ := by
    intro S hS
    exact lintegral_overlapCubeFluctuationVec_rpow_enorm_two_ne_top S u
      (hu S (by simpa [D] using hS))
  have hD_nonempty : D.Nonempty := by
    simpa [D] using overlapCentersAtDepth_nonempty Q j
  have hcoeff_ne_top : ((D.card : ℝ≥0∞)⁻¹) ≠ ∞ := by
    have hcard_ne : D.card ≠ 0 := Finset.card_ne_zero.mpr hD_nonempty
    simp [hcard_ne]
  simpa [D, I] using
    ENNReal.mul_ne_top
      hcoeff_ne_top
      (ENNReal.sum_ne_top.2 hI)

theorem overlapCentersAtDepth_average_lintegral_ofReal_vecNormSq_fluctuation_ne_top
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ)
    (hu :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp u (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          ∫⁻ x,
            ENNReal.ofReal
              (vecNormSq (u x - overlapCubeAverageVec S u))
            ∂ normalizedOverlapCubeMeasure S)) ≠ ∞ := by
  let A : ℝ≥0∞ :=
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          ∫⁻ x,
            ENNReal.ofReal
              (vecNormSq (u x - overlapCubeAverageVec S u))
            ∂ normalizedOverlapCubeMeasure S))
  let B : ℝ≥0∞ :=
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          ∫⁻ x,
            ‖overlapCubeFluctuationVec S u x‖ₑ ^ (2 : ℝ)
            ∂ normalizedOverlapCubeMeasure S))
  have hle : A ≤ (Fintype.card (Fin d) : ℝ≥0∞) * B := by
    simpa [A, B] using
      overlapCentersAtDepth_average_lintegral_ofReal_vecNormSq_fluctuation_le
        Q j u
  have hB_ne : B ≠ ∞ := by
    simpa [B] using
      overlapCentersAtDepth_average_lintegral_fluctuation_ne_top Q u j hu
  have hright_ne : (Fintype.card (Fin d) : ℝ≥0∞) * B ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hB_ne
  exact ne_top_of_le_ne_top hright_ne hle

theorem residualEuclideanOverlapBound_ne_top_of_memLp_overlap
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j M : ℕ)
    (hu :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp u (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ((M : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
      (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            ∫⁻ x,
              ENNReal.ofReal
                (vecNormSq (u x - overlapCubeAverageVec S u))
              ∂ normalizedOverlapCubeMeasure S))) ≠ ∞ := by
  have havg :
      (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            ∫⁻ x,
              ENNReal.ofReal
                (vecNormSq (u x - overlapCubeAverageVec S u))
              ∂ normalizedOverlapCubeMeasure S)) ≠ ∞ :=
    overlapCentersAtDepth_average_lintegral_ofReal_vecNormSq_fluctuation_ne_top
      Q u j hu
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by simp : (M : ℝ≥0∞) ≠ ∞)
      (by simp : (3 ^ d : ℝ≥0∞) ≠ ∞))
    havg


end

end Homogenization
