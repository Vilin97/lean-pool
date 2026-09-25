/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.HarmonicGradient
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.LocalPairing

/-! # Centered Product -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem cubeL2ScalarPartialSeminormTwo_le_note_rhs_of_meanZero_projectedDualMeanZeroPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (v g : Vec d → ℝ) {C : ℝ}
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C v g N)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (havg : cubeAverage Q v = 0) (hs : s < 1) (hC : 0 ≤ C) :
    cubeL2ScalarPartialSeminormTwo Q (s - 1) N v ≤
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g) := by
  have hs_neg : s - 1 < 0 := by linarith
  have hfactor_nonneg :
      0 ≤ Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) := by
    exact Real.sqrt_nonneg _
  calc
    cubeL2ScalarPartialSeminormTwo Q (s - 1) N v
        ≤ Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            cubeLpNorm Q (2 : ℝ≥0∞) v := by
              exact cubeL2ScalarPartialSeminormTwo_le_geometric_mul_cubeLpNorm_two_of_neg
                Q (s - 1) N v hv hs_neg
    _ ≤ Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g) := by
          exact mul_le_mul_of_nonneg_left
            (cubeLpNorm_two_le_note_rhs_of_meanZero_projectedDualMeanZeroPoincareEstimate
              Q N v g hv hproj hg havg hC) hfactor_nonneg

theorem cubeL2ScalarPartialSeminormTwo_fluctuation_le_note_rhs_of_projectedDualMeanZeroPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u g : Vec d → ℝ) {C : ℝ}
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs : s < 1) (hC : 0 ≤ C) :
    cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u) ≤
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g) := by
  exact
    cubeL2ScalarPartialSeminormTwo_le_note_rhs_of_meanZero_projectedDualMeanZeroPoincareEstimate
      Q s N (cubeFluctuation Q u) g
      (hu.sub (MeasureTheory.memLp_const (cubeAverage Q u)))
      hproj hg (cubeAverage_cubeFluctuation Q u) hs hC

theorem cubeLpNorm_two_le_note_rhs_of_meanZero_projectedDualMeanZeroVectorPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (N : ℕ) (v : Vec d → ℝ) (G : Vec d → Vec d)
    {C Bcirc : ℝ}
    (hproj : CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C v G N)
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (havg : cubeAverage Q v = 0) (hC : 0 ≤ C)
    (hGcirc : ∀ i : Fin d,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc) :
    cubeLpNorm Q (2 : ℝ≥0∞) v ≤
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((Fintype.card (Fin d) : ℝ) * Bcirc) := by
  have hlocal := hproj.to_localEstimate hG hC
  have hQ : Q ∈ descendantsAtDepth Q 0 := by
    simp [descendantsAtDepth_zero]
  have hosc := hlocal 0 (by simp) Q hQ
  have hsum :
      ∑ i : Fin d,
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => G x i) ≤
        (Fintype.card (Fin d) : ℝ) * Bcirc := by
    calc
      ∑ i : Fin d,
          cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (fun x => G x i)
          ≤ ∑ _i : Fin d, Bcirc := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact hGcirc i
      _ = (Fintype.card (Fin d) : ℝ) * Bcirc := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hK_nonneg :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  have hosc_bound :
      cubeBesovOscillation Q (2 : ℝ≥0∞) v ≤
        ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc) := by
    exact le_trans hosc (mul_le_mul_of_nonneg_left hsum hK_nonneg)
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) v
        = cubeBesovOscillation Q (2 : ℝ≥0∞) v := by
            have hfluct_eq : cubeFluctuation Q v = v := by
              funext x
              simp [cubeFluctuation, havg]
            simp [cubeBesovOscillation, hfluct_eq]
    _ ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc) := hosc_bound

/-- Full-dual replacement for
`cubeLpNorm_two_le_note_rhs_of_meanZero_projectedDualMeanZeroVectorPoincareEstimate`.

The corrected full-dual Poincare estimate controls constant gradient modes.
Uniform finite-depth circ bounds turn the full circ norm into the same
note-shaped component budget used by the projected corridor. -/
theorem cubeLpNorm_two_le_note_rhs_of_meanZero_dualFullVectorPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (N : ℕ) (v : Vec d → ℝ) (G : Vec d → Vec d)
    {C Bcirc : ℝ}
    (hfull : CubeDescendantDualFullVectorPoincareEstimate Q C v G N)
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (havg : cubeAverage Q v = 0) (hC : 0 ≤ C) (hBcirc : 0 ≤ Bcirc)
    (hGcirc : ∀ i : Fin d, ∀ M : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => G x i) ≤ Bcirc) :
    cubeLpNorm Q (2 : ℝ≥0∞) v ≤
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((Fintype.card (Fin d) : ℝ) * Bcirc) := by
  have hQ : Q ∈ descendantsAtDepth Q 0 := by
    simp [descendantsAtDepth_zero]
  have hosc := hfull 0 (by simp) Q hQ
  have hnote_nonneg : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + 1) :=
    Real.rpow_nonneg (by positivity) _
  have hcoord :
      ∀ i : Fin d,
        cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) ≤
          (3 / 2 : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) * Bcirc := by
    intro i
    have hdual_le_circ :
        cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) ≤
          (3 : ℝ) ^ ((d : ℝ) + 1) *
            cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => G x i) := by
      simpa using
        cubeBesovDualFullNorm_le_note_constant_mul_cubeBesovCircNorm
          (Q := Q) (s := 1) (p := (2 : ℝ≥0∞)) (q := (1 : ℝ≥0∞))
          (u := fun x => G x i)
          (by norm_num) (hG i) (by norm_num) (by norm_num)
          (by
            have hconj_eq :
                cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
              simpa [cubeBesovConjExponent] using
                (ENNReal.HolderConjugate.conjExponent_eq
                  (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
            simp [hconj_eq])
          (by norm_num)
    have hcirc_le :
        cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) ≤ Bcirc :=
      cubeBesovCircNorm_le_of_forall_partialNorm_le
        Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i)
        (by norm_num) (hGcirc i)
    have hmain :
        cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) ≤
          (3 : ℝ) ^ ((d : ℝ) + 1) * Bcirc := by
      exact hdual_le_circ.trans
        (mul_le_mul_of_nonneg_left hcirc_le hnote_nonneg)
    have hraw_nonneg : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + 1) * Bcirc :=
      mul_nonneg hnote_nonneg hBcirc
    calc
      cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i)
          ≤ (3 : ℝ) ^ ((d : ℝ) + 1) * Bcirc := hmain
      _ ≤ (3 / 2 : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + 1) * Bcirc) := by
            exact le_mul_of_one_le_left hraw_nonneg (by norm_num)
      _ = (3 / 2 : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) * Bcirc := by ring
  have hsum :
      ∑ i : Fin d,
          cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) ≤
        ∑ _i : Fin d,
          (3 / 2 : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) * Bcirc := by
    exact Finset.sum_le_sum (fun i _ => hcoord i)
  have hsum_eq :
      ∑ _i : Fin d,
          (3 / 2 : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) * Bcirc =
        (Fintype.card (Fin d) : ℝ) *
          ((3 / 2 : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) * Bcirc) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hK_nonneg : 0 ≤ C := hC
  have hosc_bound :
      cubeBesovOscillation Q (2 : ℝ≥0∞) v ≤
        C * ((Fintype.card (Fin d) : ℝ) *
          ((3 / 2 : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) * Bcirc)) := by
    exact hosc.trans
      (mul_le_mul_of_nonneg_left (hsum.trans (le_of_eq hsum_eq)) hK_nonneg)
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) v
        = cubeBesovOscillation Q (2 : ℝ≥0∞) v := by
            have hfluct_eq : cubeFluctuation Q v = v := by
              funext x
              simp [cubeFluctuation, havg]
            simp [cubeBesovOscillation, hfluct_eq]
    _ ≤ C * ((Fintype.card (Fin d) : ℝ) *
          ((3 / 2 : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) * Bcirc)) := hosc_bound
    _ = ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc) := by ring

theorem cubeL2ScalarPartialSeminormTwo_fluctuation_le_note_rhs_of_projectedDualMeanZeroVectorPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) {C Bcirc : ℝ}
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hproj :
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs : s < 1) (hC : 0 ≤ C)
    (hGcirc : ∀ i : Fin d,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc) :
    cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u) ≤
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc)) := by
  have hs_neg : s - 1 < 0 := by linarith
  have hfactor_nonneg :
      0 ≤ Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) := by
    exact Real.sqrt_nonneg _
  have huFluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  calc
    cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u)
        ≤ Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) := by
              exact cubeL2ScalarPartialSeminormTwo_le_geometric_mul_cubeLpNorm_two_of_neg
                Q (s - 1) N (cubeFluctuation Q u) huFluct hs_neg
    _ ≤ Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc)) := by
          exact mul_le_mul_of_nonneg_left
            (cubeLpNorm_two_le_note_rhs_of_meanZero_projectedDualMeanZeroVectorPoincareEstimate
              Q N (cubeFluctuation Q u) G hproj hG
              (cubeAverage_cubeFluctuation Q u) hC hGcirc) hfactor_nonneg

/-- Full-dual replacement for the `L²` partial-seminorm estimate used in the
centered cutoff-product term. -/
theorem cubeL2ScalarPartialSeminormTwo_fluctuation_le_note_rhs_of_dualFullVectorPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) {C Bcirc : ℝ}
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfull :
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs : s < 1) (hC : 0 ≤ C) (hBcirc : 0 ≤ Bcirc)
    (hGcirc : ∀ i : Fin d, ∀ M : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => G x i) ≤ Bcirc) :
    cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u) ≤
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc)) := by
  have hs_neg : s - 1 < 0 := by linarith
  have hfactor_nonneg :
      0 ≤ Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) := by
    exact Real.sqrt_nonneg _
  have huFluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  calc
    cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u)
        ≤ Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) := by
              exact cubeL2ScalarPartialSeminormTwo_le_geometric_mul_cubeLpNorm_two_of_neg
                Q (s - 1) N (cubeFluctuation Q u) huFluct hs_neg
    _ ≤ Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc)) := by
          exact mul_le_mul_of_nonneg_left
            (cubeLpNorm_two_le_note_rhs_of_meanZero_dualFullVectorPoincareEstimate
              Q N (cubeFluctuation Q u) G hfull hG
              (cubeAverage_cubeFluctuation Q u) hC hBcirc hGcirc) hfactor_nonneg

theorem
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_average_note_terms_of_partialBounds_of_projectedDualMeanZeroPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u g : Vec d → ℝ) (ξ : Vec d → Vec d) {Bu Bg Bavg Bcirc1 C : ℝ}
    (hs : 0 < s)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => (u x - cubeAverage Q u) • ξ x) ≤ Bg)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hneg1 : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ Bcirc1) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * Bavg) *
          (cubeBesovScaleWeight s Q * Bg))) := by
  have huFluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  have hmain :=
    abs_cubeAverage_vecDot_scalar_smul_le_collapsed_average_note_terms_of_partialBounds
      Q s flux (cubeFluctuation Q u) ξ hs hflux huFluct hξLp hBg hBavg havg hneg
      (by
        intro N
        simpa [cubeFluctuation] using hpos N)
  have hnote1_nonneg :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  have hfluctL2 :
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1 := by
    calc
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)
          ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) 0 g := by
            exact
              cubeLpNorm_two_le_note_rhs_of_meanZero_projectedDualMeanZeroPoincareEstimate
                Q 0 (cubeFluctuation Q u) g huFluct (hproj 0) hg
                (cubeAverage_cubeFluctuation Q u) hC
      _ ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1 := by
            exact mul_le_mul_of_nonneg_left (hneg1 0) hnote1_nonneg
  have havgInner :
      cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1) := by
    exact mul_le_mul_of_nonneg_left hfluctL2 (cubeLpNorm_nonneg Q ∞ ξ)
  have havgTerm :
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)))
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1))) := by
    have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    have hinner :
        Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))
          ≤
        Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) := by
      exact mul_le_mul_of_nonneg_left havgInner hBavg
    exact mul_le_mul_of_nonneg_left hinner hd_nonneg
  calc
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))|
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
            cubeBesovScaleWeight s Q * Bavg) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              simpa [cubeFluctuation] using hmain
    _ ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
            cubeBesovScaleWeight s Q * Bavg) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              exact add_le_add havgTerm le_rfl

theorem
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_sharp_average_note_terms_of_partialBounds_of_projectedDualMeanZeroPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u g : Vec d → ℝ) (ξ : Vec d → Vec d) {Bu Bg Bavg Bcirc1 C : ℝ}
    (hs : 0 < s)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => (u x - cubeAverage Q u) • ξ x) ≤ Bg)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hneg1 : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ Bcirc1) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
          (cubeBesovScaleWeight s Q * Bg))) := by
  have huFluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  have hmain :=
    abs_cubeAverage_vecDot_scalar_smul_le_collapsed_sharp_average_note_terms_of_partialBounds
      Q s flux (cubeFluctuation Q u) ξ hs hflux huFluct hξLp hBg hBavg havg hneg
      (by
        intro N
        simpa [cubeFluctuation] using hpos N)
  have hnote1_nonneg :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  have hfluctL2 :
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1 := by
    calc
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)
          ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) 0 g := by
            exact
              cubeLpNorm_two_le_note_rhs_of_meanZero_projectedDualMeanZeroPoincareEstimate
                Q 0 (cubeFluctuation Q u) g huFluct (hproj 0) hg
                (cubeAverage_cubeFluctuation Q u) hC
      _ ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1 := by
            exact mul_le_mul_of_nonneg_left (hneg1 0) hnote1_nonneg
  have havgInner :
      cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1) := by
    exact mul_le_mul_of_nonneg_left hfluctL2 (cubeLpNorm_nonneg Q ∞ ξ)
  have havgTerm :
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)))
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1))) := by
    have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    have hinner :
        Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))
          ≤
        Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) := by
      exact mul_le_mul_of_nonneg_left havgInner hBavg
    exact mul_le_mul_of_nonneg_left hinner hd_nonneg
  calc
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))|
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              simpa [cubeFluctuation] using hmain
    _ ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              exact add_le_add havgTerm le_rfl

theorem
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_average_note_terms_of_partialBounds_of_projectedDualMeanZeroVectorPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (ξ : Vec d → Vec d)
    {Bu Bg Bavg Bcirc1 C : ℝ}
    (hs : 0 < s)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => (u x - cubeAverage Q u) • ξ x) ≤ Bg)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc1) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * Bavg) *
          (cubeBesovScaleWeight s Q * Bg))) := by
  have huFluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  have hmain :=
    abs_cubeAverage_vecDot_scalar_smul_le_collapsed_average_note_terms_of_partialBounds
      Q s flux (cubeFluctuation Q u) ξ hs hflux huFluct hξLp hBg hBavg havg hneg
      (by
        intro N
        simpa [cubeFluctuation] using hpos N)
  have hfluctL2 :
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc1) := by
    exact
      cubeLpNorm_two_le_note_rhs_of_meanZero_projectedDualMeanZeroVectorPoincareEstimate
        Q 0 (cubeFluctuation Q u) G (hproj 0) hG
        (cubeAverage_cubeFluctuation Q u) hC (fun i => hGcirc1 i 0)
  have havgInner :
      cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)) := by
    exact mul_le_mul_of_nonneg_left hfluctL2 (cubeLpNorm_nonneg Q ∞ ξ)
  have havgTerm :
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)))
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) := by
    have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    have hinner :
        Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))
          ≤
        Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1))) := by
      exact mul_le_mul_of_nonneg_left havgInner hBavg
    exact mul_le_mul_of_nonneg_left hinner hd_nonneg
  calc
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))|
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
            cubeBesovScaleWeight s Q * Bavg) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              simpa [cubeFluctuation] using hmain
    _ ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
            cubeBesovScaleWeight s Q * Bavg) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              exact add_le_add havgTerm le_rfl

theorem
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_sharp_average_note_terms_of_partialBounds_of_projectedDualMeanZeroVectorPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (ξ : Vec d → Vec d)
    {Bu Bg Bavg Bcirc1 C : ℝ}
    (hs : 0 < s)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => (u x - cubeAverage Q u) • ξ x) ≤ Bg)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc1) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
          (cubeBesovScaleWeight s Q * Bg))) := by
  have huFluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  have hmain :=
    abs_cubeAverage_vecDot_scalar_smul_le_collapsed_sharp_average_note_terms_of_partialBounds
      Q s flux (cubeFluctuation Q u) ξ hs hflux huFluct hξLp hBg hBavg havg hneg
      (by
        intro N
        simpa [cubeFluctuation] using hpos N)
  have hfluctL2 :
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc1) := by
    exact
      cubeLpNorm_two_le_note_rhs_of_meanZero_projectedDualMeanZeroVectorPoincareEstimate
        Q 0 (cubeFluctuation Q u) G (hproj 0) hG
        (cubeAverage_cubeFluctuation Q u) hC (fun i => hGcirc1 i 0)
  have havgInner :
      cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)) := by
    exact mul_le_mul_of_nonneg_left hfluctL2 (cubeLpNorm_nonneg Q ∞ ξ)
  have havgTerm :
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)))
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) := by
    have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    have hinner :
        Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))
          ≤
        Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1))) := by
      exact mul_le_mul_of_nonneg_left havgInner hBavg
    exact mul_le_mul_of_nonneg_left hinner hd_nonneg
  calc
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))|
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              simpa [cubeFluctuation] using hmain
    _ ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              exact add_le_add havgTerm le_rfl

theorem cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_poincare_cutoff_terms
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    {B C : ℝ} (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs : s < 1) (hC : 0 ≤ C) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N
      (fun x => (u x - cubeAverage Q u) • ξ x) ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)) +
        cubeLpNorm Q ∞ ξ *
          cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u)) := by
  have hraw :
      cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u) ≤
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g) :=
    cubeL2ScalarPartialSeminormTwo_fluctuation_le_note_rhs_of_projectedDualMeanZeroPoincareEstimate
      Q s N u g hu hproj hg hs hC
  have hcoeff_nonneg : 0 ≤ cubeScaleFactor Q * B := by
    exact mul_nonneg (cubeScaleFactor_nonneg Q) hB
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => (u x - cubeAverage Q u) • ξ x)
        ≤
      2 * (cubeScaleFactor Q * B *
          cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u) +
        cubeLpNorm Q ∞ ξ *
          cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u)) := by
            simpa [cubeFluctuation] using!
              cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
                Q s N u ξ hB hu hξLp hξ hderiv
    _ ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)) +
        cubeLpNorm Q ∞ ξ *
          cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact add_le_add
              (mul_le_mul_of_nonneg_left hraw hcoeff_nonneg) le_rfl

theorem cubeBesovPositiveVectorSeminormTwo_centered_scalar_smul_le_poincare_cutoff_terms
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    {B C Bcirc Bpos : ℝ} (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs : s < 1) (hC : 0 ≤ C)
    (hneg : ∀ N : ℕ, cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ Bcirc)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u) ≤ Bpos) :
    cubeBesovPositiveVectorSeminormTwo Q s (fun x => (u x - cubeAverage Q u) • ξ x) ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc)) +
        cubeLpNorm Q ∞ ξ * Bpos) := by
  refine cubeBesovPositiveVectorSeminormTwo_le_of_partialBound (Q := Q) (s := s)
    (u := fun x => (u x - cubeAverage Q u) • ξ x) ?_
  intro N
  have hpartial :=
    cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_poincare_cutoff_terms
      Q s N u g ξ hB hu (hproj N) hg hξLp hξ hderiv hs hC
  have hcoeff_nonneg : 0 ≤ cubeScaleFactor Q * B := by
    exact mul_nonneg (cubeScaleFactor_nonneg Q) hB
  have hterm1 :
      cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))
        ≤
      cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc)) := by
    refine mul_le_mul_of_nonneg_left ?_ hcoeff_nonneg
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left (hneg N) ?_
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  have hterm2 :
      cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u) ≤
        cubeLpNorm Q ∞ ξ * Bpos := by
    exact mul_le_mul_of_nonneg_left (hpos N) (cubeLpNorm_nonneg Q ∞ ξ)
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => (u x - cubeAverage Q u) • ξ x)
        ≤ 2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)) +
        cubeLpNorm Q ∞ ξ *
          cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u)) := hpartial
    _ ≤ 2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc)) +
        cubeLpNorm Q ∞ ξ * Bpos) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)

theorem cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_note_poincare_cutoff_terms
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    {B C : ℝ} (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) (hC : 0 ≤ C) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N
      (fun x => (u x - cubeAverage Q u) • ξ x) ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))) := by
  have hpartial :=
    cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_poincare_cutoff_terms
      Q s N u g ξ hB hu hproj hg hξLp hξ hderiv hs1 hC
  have hpos :=
    hproj.fluctuation_positiveScalarPartialSeminormTwo_le_note_rhs
      (u := u) (hg := hg) hs0 hC
  have hterm2 :
      cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u) ≤
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)) := by
    exact mul_le_mul_of_nonneg_left hpos (cubeLpNorm_nonneg Q ∞ ξ)
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => (u x - cubeAverage Q u) • ξ x)
        ≤ 2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)) +
        cubeLpNorm Q ∞ ξ *
          cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u)) := hpartial
    _ ≤ 2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))) := by
          exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hterm2) (by norm_num)

theorem cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_note_vector_poincare_cutoff_terms
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (ξ : Vec d → Vec d) {B C Bcirc1 BcircS : ℝ}
    (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hproj :
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hBcircS : 0 ≤ BcircS)
    (hGcirc1 : ∀ i : Fin d,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc1)
    (hGcircS : ∀ i : Fin d,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ BcircS) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N
      (fun x => (u x - cubeAverage Q u) • ξ x) ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS)))) := by
  have hpartial :=
    cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
      Q s N u ξ hB hu hξLp hξ hderiv
  have hraw :
      cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u) ≤
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)) :=
    cubeL2ScalarPartialSeminormTwo_fluctuation_le_note_rhs_of_projectedDualMeanZeroVectorPoincareEstimate
      Q s N u G hu hproj hG hs1 hC hGcirc1
  have hpos :=
    CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate.fluctuation_positiveScalarPartialSeminormTwo_le_note_rhs_of_component_bound
      (Q := Q) (s := s) (C := C) (Bcirc := BcircS) (u := u) (G := G)
      (M := N) hproj hG hs0 hC hBcircS hGcircS
  have hcoeff_nonneg : 0 ≤ cubeScaleFactor Q * B := by
    exact mul_nonneg (cubeScaleFactor_nonneg Q) hB
  have hterm1 :
      cubeScaleFactor Q * B *
          cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u)
        ≤
      cubeScaleFactor Q * B *
        (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1))) :=
    mul_le_mul_of_nonneg_left hraw hcoeff_nonneg
  have hterm2 :
      cubeLpNorm Q ∞ ξ *
          cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u)
        ≤
      cubeLpNorm Q ∞ ξ *
        (cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) *
            ((Fintype.card (Fin d) : ℝ) * BcircS))) :=
    mul_le_mul_of_nonneg_left hpos (cubeLpNorm_nonneg Q ∞ ξ)
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => (u x - cubeAverage Q u) • ξ x)
        ≤
      2 * (cubeScaleFactor Q * B *
          cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u) +
        cubeLpNorm Q ∞ ξ *
          cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u)) := by
            simpa [cubeFluctuation] using! hpartial
    _ ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS)))) := by
            exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)

theorem cubeBesovPositiveVectorSeminormTwo_centered_scalar_smul_le_note_poincare_cutoff_terms
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    {B C Bcirc1 BcircS : ℝ} (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hneg1 : ∀ N : ℕ, cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ Bcirc1)
    (hnegS : ∀ N : ℕ, cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ BcircS) :
    cubeBesovPositiveVectorSeminormTwo Q s (fun x => (u x - cubeAverage Q u) • ξ x) ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * BcircS))) := by
  refine cubeBesovPositiveVectorSeminormTwo_le_of_partialBound (Q := Q) (s := s)
    (u := fun x => (u x - cubeAverage Q u) • ξ x) ?_
  intro N
  have hpartial :=
    cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_note_poincare_cutoff_terms
      Q s N u g ξ hB hu (hproj N) hg hξLp hξ hderiv hs0 hs1 hC
  have hcoeff_nonneg : 0 ≤ cubeScaleFactor Q * B := by
    exact mul_nonneg (cubeScaleFactor_nonneg Q) hB
  have hterm1 :
      cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))
        ≤
      cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) := by
    refine mul_le_mul_of_nonneg_left ?_ hcoeff_nonneg
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left (hneg1 N) ?_
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  have hnoteS_nonneg :
      0 ≤ (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) := by
    have hr_lt_one : (3 : ℝ) ^ (-s) < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _))
      (inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le))
  have hterm2inner :
      cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
            cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)
        ≤
      cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
            BcircS) := by
    refine mul_le_mul_of_nonneg_left ?_ (cubeBesovScaleWeight_nonneg (-s) Q)
    exact mul_le_mul_of_nonneg_left (hnegS N) hnoteS_nonneg
  have hterm2 :
      cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
              cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))
        ≤
      cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
              BcircS)) := by
    exact mul_le_mul_of_nonneg_left hterm2inner (cubeLpNorm_nonneg Q ∞ ξ)
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => (u x - cubeAverage Q u) • ξ x)
        ≤ 2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))) := hpartial
    _ ≤ 2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * BcircS))) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)


end

end Homogenization
