/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.SeminormRecurrence
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoliLocalBridge
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.NeumannCorrector

/-! # Corrector Energy -/

namespace Homogenization

noncomputable section

namespace MeanZeroNeumannCorrectorData

variable {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_two_mul_add
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    (hu : MemVectorL2 (cubeSet Q) u)
    (s : ℝ) (N : ℕ) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ω.toH1MeanZero.toH1Function.grad x)) ^ 2 ≤
      2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 +
        2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x)) ^ 2 := by
  have hEq :
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => ω.toH1MeanZero.toH1Function.grad x) =
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => u x - w.toH1.grad x) := by
    apply cubeBesovNegativeVectorPartialSeminormTwo_eq_of_eq_on_cubeSet s N
    intro x hx
    ext i
    change ω.toH1MeanZero.toH1Function.grad x i = u x i - w.toH1.grad x i
    have hcoord :
        u x i = w.toH1.grad x i + ω.toH1MeanZero.toH1Function.grad x i := by
      simpa using congrArg (fun z => z i) (huw x hx)
    linarith
  rw [hEq]
  exact
    sq_cubeBesovNegativeVectorPartialSeminormTwo_sub_le_two_mul_add
      Q s u (fun x => w.toH1.grad x) hu w.toH1.grad_memVectorL2 N

theorem cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_sqrtTwo_mul_add
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    (hu : MemVectorL2 (cubeSet Q) u)
    (s : ℝ) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ω.toH1MeanZero.toH1Function.grad x) ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N
            (fun x => w.toH1.grad x)) := by
  have hsq :=
    ω.sq_cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_two_mul_add
      (u := u) w huw hu s N
  have hω_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ω.toH1MeanZero.toH1Function.grad x) :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N
      (fun x => ω.toH1MeanZero.toH1Function.grad x)
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
          (fun x => ω.toH1MeanZero.toH1Function.grad x)) ^ 2 ≤
        (Real.sqrt 2 *
          (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
            cubeBesovNegativeVectorPartialSeminormTwo Q s N
              (fun x => w.toH1.grad x))) ^ 2 := by
    calc
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => ω.toH1MeanZero.toH1Function.grad x)) ^ 2
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
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    (hu : MemVectorL2 (cubeSet Q) u)
    (s : ℝ) {Bu Bw : ℝ}
    (huB : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤ Bu)
    (hwB : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => w.toH1.grad x) ≤ Bw) :
    ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => ω.toH1MeanZero.toH1Function.grad x) ≤
        Real.sqrt 2 * (Bu + Bw) := by
  intro N
  calc
    cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ω.toH1MeanZero.toH1Function.grad x)
        ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N
            (fun x => w.toH1.grad x)) := by
              exact
                ω.cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_sqrtTwo_mul_add
                  (u := u) w huw hu s N
    _ ≤ Real.sqrt 2 * (Bu + Bw) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add (huB N) (hwB N)) (Real.sqrt_nonneg _)

theorem cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_sqrtTwo_mul_add_of_bddAbove
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
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
          (fun x => ω.toH1MeanZero.toH1Function.grad x) ≤
        Real.sqrt 2 *
          (cubeBesovNegativeVectorSeminormTwo Q s u +
            cubeBesovNegativeVectorSeminormTwo Q s
              (fun x => w.toH1.grad x)) := by
  exact
    ω.cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_sqrtTwo_mul_add_of_bounds
      (u := u) w huw hu s
      (Bu := cubeBesovNegativeVectorSeminormTwo Q s u)
      (Bw := cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x))
      (fun N =>
        cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
          Q s u huBdd N)
      (fun N =>
        cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
          Q s (fun x => w.toH1.grad x) hwBdd N)

/-- Corrector energy bound from the centered Neumann energy identity and the
componentwise `q = 2` Besov pairing estimate.

This is the Lean counterpart of manuscript Section 3.2.3, Step 2, before the
remaining average term for `grad omega` is absorbed into a local negative
Besov bound. -/
theorem coefficientEnergy_average_le_note_terms_of_partialBounds_centered_two_two
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    (s : ℝ) {Bω Bg : ℝ}
    (hs : 0 < s)
    (hg_mem : MemVectorL2 (cubeSet Q) g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hgradω : MeasureTheory.MemLp
      (fun x => ω.toH1MeanZero.toH1Function.grad x)
      (2 : ENNReal) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ω.toH1MeanZero.toH1Function.grad x) ≤ Bω)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => g x - cubeAverageVec Q g) ≤ Bg) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ω.toH1MeanZero.toH1Function.grad x)) ≤
      ∑ i : Fin d, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bω) +
        cubeBesovScaleWeight s Q *
          ‖cubeAverage Q
            (fun x => ω.toH1MeanZero.toH1Function.grad x i)‖) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  let ωgrad : Vec d → Vec d := fun x => ω.toH1MeanZero.toH1Function.grad x
  let gCentered : Vec d → Vec d := fun x => g x - cubeAverageVec Q g
  have hg_centered :
      MeasureTheory.MemLp gCentered (2 : ENNReal) (normalizedCubeMeasure Q) := by
    have hconst :
        MeasureTheory.MemLp (fun _ : Vec d => cubeAverageVec Q g)
          (2 : ENNReal) (normalizedCubeMeasure Q) :=
      MeasureTheory.memLp_const (cubeAverageVec Q g)
    simpa [gCentered] using! hg.sub hconst
  have havg_g : cubeAverageVec Q gCentered = 0 := by
    simpa [gCentered] using cubeAverageVec_centered_eq_zero Q g hg_mem
  have hpair :
      cubeAverage Q (coefficientEnergyDensity a ωgrad) =
        cubeAverage Q (fun x => vecDot (ωgrad x) (gCentered x)) := by
    calc
      cubeAverage Q (coefficientEnergyDensity a ωgrad)
          =
            cubeAverage Q
              (fun x => vecDot (gCentered x) (ωgrad x)) := by
              simpa [ωgrad, gCentered] using
                ω.cubeAverage_coefficientEnergyDensity_eq_centered_rhs_pairing
      _ =
            cubeAverage Q (fun x => vecDot (ωgrad x) (gCentered x)) := by
              unfold cubeAverage
              refine congrArg (fun t : ℝ => (cubeVolume Q)⁻¹ * t) ?_
              refine MeasureTheory.integral_congr_ae ?_
              exact Filter.Eventually.of_forall fun x => vecDot_comm _ _
  have hnote :
      |cubeAverage Q (fun x => vecDot (ωgrad x) (gCentered x))| ≤
        ∑ i : Fin d, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bω) +
          cubeBesovScaleWeight s Q *
            ‖cubeAverage Q (fun x => ωgrad x i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := by
    exact
      abs_cubeAverage_vecDot_le_note_terms_of_partialBounds_of_cubeAverageVec_eq_zero_two_two
        Q s ωgrad gCentered hs hgradω hg_centered hBg havg_g hneg
        (by simpa [gCentered] using hpos)
  calc
    cubeAverage Q (coefficientEnergyDensity a ωgrad)
        =
          cubeAverage Q (fun x => vecDot (ωgrad x) (gCentered x)) := hpair
    _ ≤ |cubeAverage Q (fun x => vecDot (ωgrad x) (gCentered x))| :=
          le_abs_self _
    _ ≤
        ∑ i : Fin d, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bω) +
          cubeBesovScaleWeight s Q *
            ‖cubeAverage Q (fun x => ω.toH1MeanZero.toH1Function.grad x i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := by
          simpa [ωgrad] using hnote

/-- Sharp corrector energy bound from the centered Neumann energy identity and
the componentwise `q = 2` Besov pairing estimate. -/
theorem coefficientEnergy_average_le_sharp_note_terms_of_partialBounds_centered_two_two
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    (s : ℝ) {Bω Bg : ℝ}
    (hs : 0 < s)
    (hg_mem : MemVectorL2 (cubeSet Q) g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hgradω : MeasureTheory.MemLp
      (fun x => ω.toH1MeanZero.toH1Function.grad x)
      (2 : ENNReal) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ω.toH1MeanZero.toH1Function.grad x) ≤ Bω)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => g x - cubeAverageVec Q g) ≤ Bg) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ω.toH1MeanZero.toH1Function.grad x)) ≤
      (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bω)) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  let ωgrad : Vec d → Vec d := fun x => ω.toH1MeanZero.toH1Function.grad x
  let gCentered : Vec d → Vec d := fun x => g x - cubeAverageVec Q g
  have hg_centered :
      MeasureTheory.MemLp gCentered (2 : ENNReal) (normalizedCubeMeasure Q) := by
    have hconst :
        MeasureTheory.MemLp (fun _ : Vec d => cubeAverageVec Q g)
          (2 : ENNReal) (normalizedCubeMeasure Q) :=
      MeasureTheory.memLp_const (cubeAverageVec Q g)
    simpa [gCentered] using! hg.sub hconst
  have havg_g : cubeAverageVec Q gCentered = 0 := by
    simpa [gCentered] using cubeAverageVec_centered_eq_zero Q g hg_mem
  have hpair :
      cubeAverage Q (coefficientEnergyDensity a ωgrad) =
        cubeAverage Q (fun x => vecDot (ωgrad x) (gCentered x)) := by
    calc
      cubeAverage Q (coefficientEnergyDensity a ωgrad)
          =
            cubeAverage Q
              (fun x => vecDot (gCentered x) (ωgrad x)) := by
              simpa [ωgrad, gCentered] using
                ω.cubeAverage_coefficientEnergyDensity_eq_centered_rhs_pairing
      _ =
            cubeAverage Q (fun x => vecDot (ωgrad x) (gCentered x)) := by
              unfold cubeAverage
              refine congrArg (fun t : ℝ => (cubeVolume Q)⁻¹ * t) ?_
              refine MeasureTheory.integral_congr_ae ?_
              exact Filter.Eventually.of_forall fun x => vecDot_comm _ _
  have hsharp :
      |cubeAverage Q (fun x => vecDot (ωgrad x) (gCentered x))| ≤
        (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bω)) *
          (cubeBesovScaleWeight s Q * Bg)) := by
    exact
      abs_cubeAverage_vecDot_le_sharp_note_terms_of_partialBounds_of_cubeAverageVec_eq_zero_two_two
        Q s ωgrad gCentered hs hgradω hg_centered hBg havg_g hneg
        (by simpa [gCentered] using hpos)
  calc
    cubeAverage Q (coefficientEnergyDensity a ωgrad)
        =
          cubeAverage Q (fun x => vecDot (ωgrad x) (gCentered x)) := hpair
    _ ≤ |cubeAverage Q (fun x => vecDot (ωgrad x) (gCentered x))| :=
          le_abs_self _
    _ ≤ (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bω)) *
        (cubeBesovScaleWeight s Q * Bg)) := hsharp

/-- Collapsed sharp corrector energy bound with the opposite scale weights
canceled. -/
theorem coefficientEnergy_average_le_collapsed_note_term_centered_two_two
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    (s : ℝ) {Bω Bg : ℝ}
    (hs : 0 < s)
    (hg_mem : MemVectorL2 (cubeSet Q) g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hgradω : MeasureTheory.MemLp
      (fun x => ω.toH1MeanZero.toH1Function.grad x)
      (2 : ENNReal) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ω.toH1MeanZero.toH1Function.grad x) ≤ Bω)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => g x - cubeAverageVec Q g) ≤ Bg) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ω.toH1MeanZero.toH1Function.grad x)) ≤
      (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Bω * Bg) := by
  have hsharp :=
    ω.coefficientEnergy_average_le_sharp_note_terms_of_partialBounds_centered_two_two
      s hs hg_mem hg hgradω hBg hneg hpos
  have hterm :
      (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bω)) *
        (cubeBesovScaleWeight s Q * Bg)) =
        (3 : ℝ) ^ ((d : ℝ) + s) * Bω * Bg := by
    calc
      (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bω)) *
        (cubeBesovScaleWeight s Q * Bg))
          =
            (cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q) *
              ((3 : ℝ) ^ ((d : ℝ) + s) * Bω * Bg) := by
              ring
      _ = (3 : ℝ) ^ ((d : ℝ) + s) * Bω * Bg := by
            rw [cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight, one_mul]
  simpa [hterm] using hsharp

end MeanZeroNeumannCorrectorData

end

end Homogenization
