/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Positive.ExactOverlap
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.BesovLeGagliardo
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.GagliardoLeBesov

/-!
# Exact scalar overlap Besov–Gagliardo comparison

This module identifies the square of the exact `ENNReal` overlap Besov
seminorm at `p = q = 2` with the supremum of the established finite-depth
scalar overlap seminorm squares.  It then transports the two existing
finite-depth Besov–Gagliardo comparisons to the exact infinite-depth kernel.

The only analytic input used by the identification is concrete parent-cube
`L²` membership.  It supplies both the root integrability and every enlarged
overlap-cube integrability certificate required by the exact kernel.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

/-- Exact scalar overlap parameters at `p = q = 2` and fractional order
`0 < s < 1`. -/
noncomputable def exactOverlapScalarTwoParameters (s : Set.Ioo (0 : ℝ) 1) :
    ExactOverlapFiniteParameters where
  s := s.1
  p := 2
  q := 2
  admissible := ⟨s.2.1, s.2.2, by norm_num, by norm_num⟩

private theorem cubeScaleFactor_div_pow_eq_sourceZPow_scalarComparison {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    cubeScaleFactor Q / (3 : ℝ) ^ j = (3 : ℝ) ^ (Q.scale - (j : ℤ)) := by
  unfold cubeScaleFactor
  rw [zpow_sub₀]
  · simp [div_eq_mul_inv]
  · norm_num

private theorem exactOverlapDepthWeight_eq_ofReal_scalarComparison {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    exactOverlapDepthWeight Q s j =
      ENNReal.ofReal (cubeBesovOverlapDepthWeight Q s j) := by
  unfold exactOverlapDepthWeight cubeBesovOverlapDepthWeight cubeBesovDepthWeight
  rw [cubeScaleFactor_div_pow_eq_sourceZPow_scalarComparison]
  rw [← Real.rpow_intCast (3 : ℝ) (Q.scale - (j : ℤ)),
    ← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
  rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : 0 < (3 : ℝ))]
  congr 1
  · norm_num
  · change -(((Q.scale - (j : ℤ) : ℤ) : ℝ)) * s =
      ((Q.scale - (j : ℤ) : ℤ) : ℝ) * -s
    ring

private theorem exactOverlapScalarTwoIntegrableOfMemLp {d : ℕ} (Q : TriadicCube d)
    {u : Vec d → ℝ}
    (hmem : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ExactOverlapIntegrable Q u where
  root := hmem.integrable (by norm_num)
  overlap := fun _ _ hS =>
    (Gagliardo.memLp_overlap_of_memLp hmem hS).integrable (by norm_num)

private theorem exactOverlapLocalOscillation_two_eq_ofReal {d : ℕ}
    (S : TriadicCube d) (u : Vec d → ℝ)
    (hu : Integrable u (ScalarOverlap.normalizedCubeMeasure S))
    (hmem : MemLp u (2 : ℝ≥0∞) (ScalarOverlap.normalizedCubeMeasure S)) :
    exactOverlapLocalOscillation S (ENNReal.ofReal 2) u hu =
      ENNReal.ofReal (cubeBesovOverlapOscillation S (2 : ℝ≥0∞) u) := by
  have hmean : exactOverlapLocalMean S u hu = ScalarOverlap.cubeAverage S u := by
    rw [exactOverlapLocalMean_eq,
      ScalarOverlap.cubeAverage_eq_integral_normalizedCubeMeasure]
  have hsub : MemLp (fun x => u x - exactOverlapLocalMean S u hu) (2 : ℝ≥0∞)
      (ScalarOverlap.normalizedCubeMeasure S) :=
    hmem.sub (memLp_const (exactOverlapLocalMean S u hu))
  rw [exactOverlapLocalOscillation_eq,
    show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num]
  rw [← ENNReal.ofReal_toReal hsub.eLpNorm_ne_top]
  unfold cubeBesovOverlapOscillation ScalarOverlap.cubeLpNorm
  rw [hmean]

private theorem exactOverlapDepthAverage_two_eq_ofReal {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ)
    (hmem : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) (j : ℕ) :
    exactOverlapDepthAverage Q 2 u (exactOverlapScalarTwoIntegrableOfMemLp Q hmem) j =
      ENNReal.ofReal (cubeBesovOverlapDepthAverage Q (2 : ℝ≥0∞) u j) := by
  have hcard : (0 : ℝ) < ((ScalarOverlap.centersAtDepth Q j).card : ℝ) := by
    exact_mod_cast ScalarOverlap.centersAtDepth_card_pos Q j
  rw [exactOverlapDepthAverage_eq]
  unfold cubeBesovOverlapDepthAverage ScalarOverlap.centersAverage
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcard.le)]
  rw [ENNReal.ofReal_inv_of_pos hcard, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    calc
      (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
          exactOverlapLocalOscillation S.1 (ENNReal.ofReal 2) u
              ((exactOverlapScalarTwoIntegrableOfMemLp Q hmem).overlap j S.1 S.2) ^
                (2 : ℝ)) =
          (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
            ENNReal.ofReal
              (cubeBesovOverlapOscillation S.1 (2 : ℝ≥0∞) u ^ (2 : ℝ))) := by
            apply Finset.sum_congr rfl
            intro S _
            rw [← ENNReal.ofReal_rpow_of_nonneg
              (cubeBesovOverlapOscillation_nonneg S.1 (2 : ℝ≥0∞) u) (by norm_num)]
            rw [exactOverlapLocalOscillation_two_eq_ofReal S.1 u
              ((exactOverlapScalarTwoIntegrableOfMemLp Q hmem).overlap j S.1 S.2)
              (Gagliardo.memLp_overlap_of_memLp hmem S.2)]
      _ = (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
            ENNReal.ofReal
              (cubeBesovOverlapOscillation S (2 : ℝ≥0∞) u ^ (2 : ℝ))) := by
          let D := ScalarOverlap.centersAtDepth Q j
          let f : TriadicCube d → ℝ≥0∞ := fun S =>
            ENNReal.ofReal
              (cubeBesovOverlapOscillation S (2 : ℝ≥0∞) u ^ (2 : ℝ))
          change D.attach.sum (fun S => f S.1) = D.sum f
          exact Finset.sum_attach D f
  · intro S _
    exact Real.rpow_nonneg
      (cubeBesovOverlapOscillation_nonneg S (2 : ℝ≥0∞) u) _

private theorem exactOverlapDepthTerm_two_eq_ofReal {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → ℝ)
    (hmem : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) (j : ℕ) :
    exactOverlapDepthTerm Q s 2 u (exactOverlapScalarTwoIntegrableOfMemLp Q hmem) j =
      ENNReal.ofReal
        (cubeBesovOverlapDepthSeminorm Q s (2 : ℝ≥0∞) u j) := by
  rw [exactOverlapDepthTerm_eq,
    exactOverlapDepthWeight_eq_ofReal_scalarComparison,
    exactOverlapDepthAverage_two_eq_ofReal Q u hmem j]
  unfold cubeBesovOverlapDepthSeminorm
  rw [ENNReal.ofReal_mul (cubeBesovOverlapDepthWeight_nonneg Q s j)]
  rw [← ENNReal.ofReal_rpow_of_nonneg
    (cubeBesovOverlapDepthAverage_nonneg Q (2 : ℝ≥0∞) u j) (by norm_num)]
  norm_num

private theorem exactOverlapScalarSeminormTwo_sq_eq_iSup_partialSeminorm_canonical
    {d : ℕ} (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d) (u : Vec d → ℝ)
    (hmem : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    (exactOverlapFiniteSeminorm (exactOverlapScalarTwoParameters s) Q u
      (exactOverlapScalarTwoIntegrableOfMemLp Q hmem)) ^ 2 =
      ⨆ N : ℕ, (ENNReal.ofReal
        (cubeBesovOverlapPartialSeminorm Q s.1 (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u)) ^ 2 := by
  have htsum :
      (∑' j : ℕ, (ENNReal.ofReal
        (cubeBesovOverlapDepthSeminorm Q s.1 (2 : ℝ≥0∞) u j)) ^ 2) =
      ⨆ N : ℕ, (ENNReal.ofReal
        (cubeBesovOverlapPartialSeminorm Q s.1 (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u)) ^ 2 := by
    rw [ENNReal.tsum_eq_iSup_nat' (N := fun i => i + 1)
      (Filter.tendsto_add_atTop_nat 1)]
    apply iSup_congr
    intro N
    calc
      ∑ j ∈ Finset.range (N + 1),
          (ENNReal.ofReal
            (cubeBesovOverlapDepthSeminorm Q s.1 (2 : ℝ≥0∞) u j)) ^ 2 =
          ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal
            ((cubeBesovOverlapDepthSeminorm Q s.1 (2 : ℝ≥0∞) u j) ^ 2) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [ENNReal.ofReal_pow
                (cubeBesovOverlapDepthSeminorm_nonneg Q s.1 (2 : ℝ≥0∞) u j)]
      _ = ENNReal.ofReal
          ((cubeBesovOverlapPartialSeminorm Q s.1 (2 : ℝ≥0∞)
            (2 : ℝ≥0∞) N u) ^ 2) := by
              simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
                (Gagliardo.ofReal_partialSeminorm_rpow_eq Q s.1
                  (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) N u).symm
      _ = (ENNReal.ofReal
          (cubeBesovOverlapPartialSeminorm Q s.1 (2 : ℝ≥0∞)
            (2 : ℝ≥0∞) N u)) ^ 2 :=
              ENNReal.ofReal_pow
                (cubeBesovOverlapPartialSeminorm_nonneg Q s.1
                  (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u) 2
  calc
    (exactOverlapFiniteSeminorm (exactOverlapScalarTwoParameters s) Q u
        (exactOverlapScalarTwoIntegrableOfMemLp Q hmem)) ^ 2 =
        ∑' j : ℕ, (exactOverlapDepthTerm Q s.1 2 u
          (exactOverlapScalarTwoIntegrableOfMemLp Q hmem) j) ^ (2 : ℝ) := by
      rw [exactOverlapFiniteSeminorm_eq]
      change (((∑' j : ℕ, (exactOverlapDepthTerm Q s.1 2 u
        (exactOverlapScalarTwoIntegrableOfMemLp Q hmem) j) ^ (2 : ℝ)) ^
          ((2 : ℝ)⁻¹)) ^ (2 : ℕ)) = _
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ = ∑' j : ℕ, (ENNReal.ofReal
          (cubeBesovOverlapDepthSeminorm Q s.1 (2 : ℝ≥0∞) u j)) ^ 2 := by
      apply tsum_congr
      intro j
      rw [exactOverlapDepthTerm_two_eq_ofReal Q s.1 u hmem j,
        ENNReal.rpow_two]
    _ = _ := htsum

/-- Under concrete parent-cube `L²` membership, the square of the exact
`p = q = 2` scalar overlap seminorm is the supremum of the embedded squares
of all finite-depth scalar overlap seminorms. -/
theorem exactOverlapScalarSeminormTwo_sq_eq_iSup_partialSeminorm {d : ℕ}
    (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d) (u : Vec d → ℝ)
    (hu : ExactOverlapIntegrable Q u)
    (hmem : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    (exactOverlapFiniteSeminorm (exactOverlapScalarTwoParameters s) Q u hu) ^ 2 =
      ⨆ N : ℕ, (ENNReal.ofReal
        (cubeBesovOverlapPartialSeminorm Q s.1 (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u)) ^ 2 := by
  rw [exactOverlapFiniteSeminorm_congr_ae (exactOverlapScalarTwoParameters s) Q hu
    (exactOverlapScalarTwoIntegrableOfMemLp Q hmem)
    (fun _ _ _ => Filter.EventuallyEq.rfl)]
  exact exactOverlapScalarSeminormTwo_sq_eq_iSup_partialSeminorm_canonical
    s Q u hmem

/-- Exact scalar overlap Besov-to-Gagliardo comparison at `p = q = 2`, with
the finite dimensional constant from the established finite-depth estimate. -/
theorem exactOverlapScalarSeminormTwo_sq_le_gagliardo {d : ℕ} [NeZero d]
    (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d) (u : Vec d → ℝ)
    (hu : ExactOverlapIntegrable Q u) (humeas : Measurable u)
    (hmem : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    (exactOverlapFiniteSeminorm (exactOverlapScalarTwoParameters s) Q u hu) ^ 2 ≤
      2 * 3 ^ d * Gagliardo.cubeGagliardoESeminorm Q s.1 (2 : ℝ≥0∞) u ^ 2 := by
  rw [exactOverlapScalarSeminormTwo_sq_eq_iSup_partialSeminorm s Q u hu hmem]
  refine iSup_le fun N => ?_
  rw [← ENNReal.ofReal_pow
    (cubeBesovOverlapPartialSeminorm_nonneg Q s.1
      (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u)]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, ENNReal.rpow_two] using
    Gagliardo.ofReal_partialSeminorm_rpow_le_gagliardo Q s.2.1.le
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) humeas hmem N

/-- Gagliardo-to-exact-scalar-overlap comparison at `p = q = 2`, with the
finite dimensional constant from the established shell estimate. -/
theorem gagliardo_sq_le_exactOverlapScalarSeminormTwo {d : ℕ} [NeZero d]
    (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d) (u : Vec d → ℝ)
    (hu : ExactOverlapIntegrable Q u) (humeas : Measurable u)
    (hmem : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    Gagliardo.cubeGagliardoESeminorm Q s.1 (2 : ℝ≥0∞) u ^ 2 ≤
      (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) *
        (exactOverlapFiniteSeminorm (exactOverlapScalarTwoParameters s) Q u hu) ^ 2 := by
  have hiSup :
      (⨆ N : ℕ, ENNReal.ofReal
        ((cubeBesovOverlapPartialSeminorm Q s.1 (2 : ℝ≥0∞)
          (2 : ℝ≥0∞) N u) ^ 2)) =
      ⨆ N : ℕ, (ENNReal.ofReal
        (cubeBesovOverlapPartialSeminorm Q s.1 (2 : ℝ≥0∞)
          (2 : ℝ≥0∞) N u)) ^ 2 := by
    apply iSup_congr
    intro N
    exact ENNReal.ofReal_pow
      (cubeBesovOverlapPartialSeminorm_nonneg Q s.1
        (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u) 2
  calc
    Gagliardo.cubeGagliardoESeminorm Q s.1 (2 : ℝ≥0∞) u ^ 2 ≤
        (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) *
          ⨆ N : ℕ, ENNReal.ofReal
            ((cubeBesovOverlapPartialSeminorm Q s.1 (2 : ℝ≥0∞)
              (2 : ℝ≥0∞) N u) ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, ENNReal.rpow_two] using
        Gagliardo.gagliardo_rpow_le_iSup_partialSeminorm Q s.2.1.le s.2.2.le
          (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) humeas hmem
    _ = (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) *
          ⨆ N : ℕ, (ENNReal.ofReal
            (cubeBesovOverlapPartialSeminorm Q s.1 (2 : ℝ≥0∞)
              (2 : ℝ≥0∞) N u)) ^ 2 := by
      rw [hiSup]
    _ = (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) *
        (exactOverlapFiniteSeminorm (exactOverlapScalarTwoParameters s) Q u hu) ^ 2 := by
      rw [← exactOverlapScalarSeminormTwo_sq_eq_iSup_partialSeminorm s Q u hu hmem]

end Homogenization
