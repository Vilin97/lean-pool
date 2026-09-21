/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoliLocalBridge
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Correctors

/-! # Coarse Caccioppoli Local Gradient Bridge -/

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem abs_cubeAverage_vecDot_grad_le_note_terms_of_partialBounds_of_h10OnCube
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (φ : H10Function (cubeSet Q)) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgrad : MeasureTheory.MemLp (fun x => φ.toH1Function.grad x)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N u ≤ Bu)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => φ.toH1Function.grad x) ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (φ.toH1Function.grad x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  apply abs_cubeAverage_vecDot_le_note_terms_of_partialBounds_of_cubeAverageVec_eq_zero
    Q s u (fun x => φ.toH1Function.grad x) hs hu hgrad hBg
  · exact cubeAverageVec_grad_eq_zero_of_h10OnCube Q φ
  · exact hneg
  · exact hpos

namespace ZeroTraceDirichletCorrectorData

theorem cubeAverage_energy_identity_sub_const
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q))]
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (hmem : MemVectorL2 (cubeSet Q) g) (c : Vec d) :
    cubeAverage Q
        (fun x =>
          vecDot (ρ.toH10.toH1Function.grad x)
            (matVecMul (a x) (ρ.toH10.toH1Function.grad x))) =
      cubeAverage Q (fun x => vecDot (g x - c) (ρ.toH10.toH1Function.grad x)) := by
  unfold cubeAverage
  rw [ρ.weakSolution.energy_identity_sub_const hmem c]

/-- Corrector identity averaged in the intrinsic coefficient energy. -/
theorem cubeAverage_coefficientEnergy_identity_sub_const
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q))]
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (hmem : MemVectorL2 (cubeSet Q) g) (c : Vec d) :
    cubeAverage Q
        (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) =
      cubeAverage Q (fun x => vecDot (g x - c) (ρ.toH10.toH1Function.grad x)) := by
  unfold cubeAverage
  rw [ρ.weakSolution.coefficientEnergy_identity_sub_const hmem c]

theorem coefficientEnergy_average_le_note_terms_of_partialBounds_sub_const
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (s : ℝ) (c : Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hmem : MemVectorL2 (cubeSet Q) g)
    (hu : MeasureTheory.MemLp (fun x => g x - c) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgrad : MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N (fun x => g x - c) ≤ Bu)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => ρ.toH10.toH1Function.grad x) ≤ Bg) :
    cubeAverage Q (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => (g x - c) i)‖) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  have hpair :
      cubeAverage Q (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) =
        cubeAverage Q (fun x => vecDot (g x - c) (ρ.toH10.toH1Function.grad x)) :=
    ρ.cubeAverage_coefficientEnergy_identity_sub_const hmem c
  have hnote :
      |cubeAverage Q (fun x => vecDot (g x - c) (ρ.toH10.toH1Function.grad x))| ≤
        ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => (g x - c) i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := by
    simpa using
      abs_cubeAverage_vecDot_grad_le_note_terms_of_partialBounds_of_h10OnCube
        Q s (fun x => g x - c) ρ.toH10 hs hu hgrad hBg hneg hpos
  calc
    cubeAverage Q (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x))
        =
          cubeAverage Q (fun x => vecDot (g x - c) (ρ.toH10.toH1Function.grad x)) := hpair
    _ ≤ |cubeAverage Q (fun x => vecDot (g x - c) (ρ.toH10.toH1Function.grad x))| :=
          le_abs_self _
    _ ≤
        ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => (g x - c) i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := hnote

theorem abs_cubeAverage_vecDot_grad_le_note_terms_of_partialBounds_of_h10OnCube_two_two
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (φ : H10Function (cubeSet Q)) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgrad : MeasureTheory.MemLp (fun x => φ.toH1Function.grad x)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤ Bu)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => φ.toH1Function.grad x) ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (φ.toH1Function.grad x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  apply abs_cubeAverage_vecDot_le_note_terms_of_partialBounds_of_cubeAverageVec_eq_zero_two_two
    Q s u (fun x => φ.toH1Function.grad x) hs hu hgrad hBg
  · exact cubeAverageVec_grad_eq_zero_of_h10OnCube Q φ
  · exact hneg
  · exact hpos

theorem coefficientEnergy_average_le_note_terms_of_partialBounds_sub_const_two_two
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (s : ℝ) (c : Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hmem : MemVectorL2 (cubeSet Q) g)
    (hu : MeasureTheory.MemLp (fun x => g x - c) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgrad : MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => g x - c) ≤ Bu)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => ρ.toH10.toH1Function.grad x) ≤ Bg) :
    cubeAverage Q (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => (g x - c) i)‖) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  have hpair :
      cubeAverage Q (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) =
        cubeAverage Q (fun x => vecDot (g x - c) (ρ.toH10.toH1Function.grad x)) :=
    ρ.cubeAverage_coefficientEnergy_identity_sub_const hmem c
  have hnote :
      |cubeAverage Q (fun x => vecDot (g x - c) (ρ.toH10.toH1Function.grad x))| ≤
        ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => (g x - c) i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := by
    simpa using
      abs_cubeAverage_vecDot_grad_le_note_terms_of_partialBounds_of_h10OnCube_two_two
        Q s (fun x => g x - c) ρ.toH10 hs hu hgrad hBg hneg hpos
  calc
    cubeAverage Q (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x))
        =
          cubeAverage Q (fun x => vecDot (g x - c) (ρ.toH10.toH1Function.grad x)) := hpair
    _ ≤ |cubeAverage Q (fun x => vecDot (g x - c) (ρ.toH10.toH1Function.grad x))| :=
          le_abs_self _
    _ ≤
        ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => (g x - c) i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := hnote

theorem coefficientEnergy_average_le_collapsed_note_term_centered_two_two
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (s : ℝ) {Bρ Bg : ℝ}
    (hs : 0 < s)
    (hmem : MemVectorL2 (cubeSet Q) g)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgrad : MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ρ.toH10.toH1Function.grad x) ≤ Bρ)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => g x - cubeAverageVec Q g) ≤ Bg) :
    cubeAverage Q (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) ≤
      (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Bρ * Bg) := by
  have hcentered :
      MeasureTheory.MemLp (fun x => g x - cubeAverageVec Q g) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    have hconst :
        MeasureTheory.MemLp (fun _ : Vec d => cubeAverageVec Q g) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) :=
      MeasureTheory.memLp_const (cubeAverageVec Q g)
    simpa using! hg.sub hconst
  have havg_g :
      cubeAverageVec Q (fun x => g x - cubeAverageVec Q g) = 0 := by
    rw [cubeAverageVec_sub_const Q g (cubeAverageVec Q g) hg]
    simp
  have hnote_raw :
      |cubeAverage Q
          (fun x => vecDot (ρ.toH10.toH1Function.grad x)
            (g x - cubeAverageVec Q g))| ≤
        ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bρ) +
          cubeBesovScaleWeight s Q *
            ‖cubeAverage Q (fun x => ρ.toH10.toH1Function.grad x i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := by
    exact
      abs_cubeAverage_vecDot_le_note_terms_of_partialBounds_of_cubeAverageVec_eq_zero_two_two
        Q s (fun x => ρ.toH10.toH1Function.grad x)
        (fun x => g x - cubeAverageVec Q g)
        hs hgrad hcentered hBg havg_g hneg hpos
  have havg_ρ :
      cubeAverageVec Q (fun x => ρ.toH10.toH1Function.grad x) = 0 :=
    cubeAverageVec_grad_eq_zero_of_h10OnCube Q ρ.toH10
  have hsum_zero :
      ∑ i : Fin d, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bρ) +
        cubeBesovScaleWeight s Q *
          ‖cubeAverage Q (fun x => ρ.toH10.toH1Function.grad x i)‖) *
        (cubeBesovScaleWeight s Q * Bg)) =
      ∑ i : Fin d, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bρ)) *
          (cubeBesovScaleWeight s Q * Bg)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi0 : cubeAverage Q (fun x => ρ.toH10.toH1Function.grad x i) = 0 := by
      simpa [cubeAverageVec] using congrFun havg_ρ i
    rw [hi0]
    simp
  have hcollapse :
      ∑ i : Fin d, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bρ)) *
          (cubeBesovScaleWeight s Q * Bg)) =
        (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Bρ * Bg) := by
    have hterm :
        (((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bρ)) *
            (cubeBesovScaleWeight s Q * Bg)) =
          (3 : ℝ) ^ ((d : ℝ) + s) * Bρ * Bg := by
      calc
        (((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bρ)) *
            (cubeBesovScaleWeight s Q * Bg))
            =
          (cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q) *
            ((3 : ℝ) ^ ((d : ℝ) + s) * Bρ * Bg) := by
              ring
        _ = (3 : ℝ) ^ ((d : ℝ) + s) * Bρ * Bg := by
              rw [cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight, one_mul]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, hterm]
  have hnote :
      |cubeAverage Q
          (fun x => vecDot (ρ.toH10.toH1Function.grad x)
            (g x - cubeAverageVec Q g))| ≤
        (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Bρ * Bg) := by
    rw [hsum_zero] at hnote_raw
    rw [hcollapse] at hnote_raw
    exact hnote_raw
  have hpair :
      cubeAverage Q (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) =
        cubeAverage Q
          (fun x => vecDot (ρ.toH10.toH1Function.grad x)
            (g x - cubeAverageVec Q g)) := by
    calc
      cubeAverage Q (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x))
          =
            cubeAverage Q
              (fun x => vecDot (g x - cubeAverageVec Q g)
                (ρ.toH10.toH1Function.grad x)) := by
                exact ρ.cubeAverage_coefficientEnergy_identity_sub_const
                  hmem (cubeAverageVec Q g)
      _ =
            cubeAverage Q
              (fun x => vecDot (ρ.toH10.toH1Function.grad x)
                (g x - cubeAverageVec Q g)) := by
                unfold cubeAverage
                refine congrArg (fun t : ℝ => (cubeVolume Q)⁻¹ * t) ?_
                refine MeasureTheory.integral_congr_ae ?_
                exact Filter.Eventually.of_forall fun x => vecDot_comm _ _
  calc
    cubeAverage Q (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x))
        =
          cubeAverage Q
            (fun x => vecDot (ρ.toH10.toH1Function.grad x)
              (g x - cubeAverageVec Q g)) := hpair
    _ ≤
        |cubeAverage Q
          (fun x => vecDot (ρ.toH10.toH1Function.grad x)
            (g x - cubeAverageVec Q g))| := le_abs_self _
    _ ≤ (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Bρ * Bg) := hnote

end ZeroTraceDirichletCorrectorData

end

end Homogenization
