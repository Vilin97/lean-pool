/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Positive.ExactOverlap
public import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapScalarComparison

/-!
# Exact scalar overlap aggregation at arbitrary finite `p`

This additive finite-`p` module identifies the diagonal `q = p` exact overlap
seminorm with the complete source depth-energy series and with the established
finite-depth scalar-overlap truncations.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace FiniteLpExponent

private theorem one_le (p : FiniteLpExponent) : 1 ≤ p.exponent :=
  p.one_lt.le

private theorem ne_zero (p : FiniteLpExponent) : p.exponent ≠ 0 :=
  (zero_lt_one.trans p.one_lt).ne'

private theorem ne_top (p : FiniteLpExponent) : p.exponent ≠ ∞ :=
  p.lt_top.ne

private theorem toReal_pos (p : FiniteLpExponent) : 0 < p.exponent.toReal :=
  ENNReal.toReal_pos p.ne_zero p.ne_top

private theorem one_le_toReal (p : FiniteLpExponent) : 1 ≤ p.exponent.toReal := by
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_le_toReal (by norm_num) p.ne_top).mpr p.one_le

end FiniteLpExponent

/-- Exact scalar-overlap parameters in the diagonal finite case `q = p`. -/
noncomputable def exactOverlapScalarPParameters (s : FractionalOrder)
    (p : FiniteLpExponent) : ExactOverlapFiniteParameters where
  s := s.1
  p := p.exponent.toReal
  q := p.exponent.toReal
  admissible := by exact ⟨s.2.1, s.2.2, p.one_le_toReal, p.one_le_toReal⟩

private theorem exactOverlapScalarPIntegrableOfMemLp {d : ℕ} (Q : TriadicCube d)
    (p : FiniteLpExponent) {u : Vec d → ℝ}
    (hmem : MemLp u p.exponent (normalizedCubeMeasure Q)) :
    ExactOverlapIntegrable Q u where
  root := hmem.integrable p.one_le
  overlap := fun _ _ hS =>
    (Gagliardo.memLp_overlap_of_memLp hmem hS).integrable p.one_le

private theorem cubeScaleFactor_div_pow_eq_sourceZPow_scalarP {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    cubeScaleFactor Q / (3 : ℝ) ^ j = (3 : ℝ) ^ (Q.scale - (j : ℤ)) := by
  unfold cubeScaleFactor
  rw [zpow_sub₀]
  · simp [div_eq_mul_inv]
  · norm_num

private theorem exactOverlapDepthWeight_eq_ofReal_scalarP {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    exactOverlapDepthWeight Q s j =
      ENNReal.ofReal (cubeBesovOverlapDepthWeight Q s j) := by
  unfold exactOverlapDepthWeight cubeBesovOverlapDepthWeight cubeBesovDepthWeight
  rw [cubeScaleFactor_div_pow_eq_sourceZPow_scalarP]
  rw [← Real.rpow_intCast (3 : ℝ) (Q.scale - (j : ℤ)),
    ← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
  rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : 0 < (3 : ℝ))]
  congr 1
  · norm_num
  · change -(((Q.scale - (j : ℤ) : ℤ) : ℝ)) * s =
      ((Q.scale - (j : ℤ) : ℤ) : ℝ) * -s
    ring

private theorem exactOverlapLocalOscillation_p_eq_ofReal {d : ℕ}
    (S : TriadicCube d) (p : FiniteLpExponent) (u : Vec d → ℝ)
    (hu : Integrable u (ScalarOverlap.normalizedCubeMeasure S))
    (hmem : MemLp u p.exponent (ScalarOverlap.normalizedCubeMeasure S)) :
    exactOverlapLocalOscillation S p.exponent u hu =
      ENNReal.ofReal (cubeBesovOverlapOscillation S p.exponent u) := by
  have hmean : exactOverlapLocalMean S u hu = ScalarOverlap.cubeAverage S u := by
    rw [exactOverlapLocalMean_eq,
      ScalarOverlap.cubeAverage_eq_integral_normalizedCubeMeasure]
  have hsub : MemLp (fun x => u x - exactOverlapLocalMean S u hu) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S) :=
    hmem.sub (memLp_const (exactOverlapLocalMean S u hu))
  rw [exactOverlapLocalOscillation_eq, ← ENNReal.ofReal_toReal hsub.eLpNorm_ne_top]
  unfold cubeBesovOverlapOscillation ScalarOverlap.cubeLpNorm
  rw [hmean] at hsub ⊢
  rw [Gagliardo.integralLpSeminorm_eq_eLpNorm _ _ _ hsub.aestronglyMeasurable]

private theorem exactOverlapDepthAverage_p_eq_ofReal {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (u : Vec d → ℝ)
    (hmem : MemLp u p.exponent (normalizedCubeMeasure Q)) (j : ℕ) :
    exactOverlapDepthAverage Q p.exponent.toReal u
      (exactOverlapScalarPIntegrableOfMemLp Q p hmem) j =
      ENNReal.ofReal (cubeBesovOverlapDepthAverage Q p.exponent u j) := by
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
          exactOverlapLocalOscillation S.1 (ENNReal.ofReal p.exponent.toReal) u
              ((exactOverlapScalarPIntegrableOfMemLp Q p hmem).overlap j S.1 S.2) ^
                p.exponent.toReal) =
          (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
            ENNReal.ofReal
              (cubeBesovOverlapOscillation S.1 p.exponent u ^ p.exponent.toReal)) := by
            apply Finset.sum_congr rfl
            intro S _
            rw [← ENNReal.ofReal_rpow_of_nonneg
              (cubeBesovOverlapOscillation_nonneg S.1 p.exponent u) p.toReal_pos.le]
            rw [ENNReal.ofReal_toReal p.ne_top,
              exactOverlapLocalOscillation_p_eq_ofReal S.1 p u
                ((exactOverlapScalarPIntegrableOfMemLp Q p hmem).overlap j S.1 S.2)
                (Gagliardo.memLp_overlap_of_memLp hmem S.2)]
      _ = (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
            ENNReal.ofReal
              (cubeBesovOverlapOscillation S p.exponent u ^ p.exponent.toReal)) := by
          let D := ScalarOverlap.centersAtDepth Q j
          let f : TriadicCube d → ℝ≥0∞ := fun S =>
            ENNReal.ofReal
              (cubeBesovOverlapOscillation S p.exponent u ^ p.exponent.toReal)
          change D.attach.sum (fun S => f S.1) = D.sum f
          exact Finset.sum_attach D f
  · intro S _
    exact Real.rpow_nonneg (cubeBesovOverlapOscillation_nonneg S p.exponent u) _

private theorem exactOverlapDepthTerm_p_eq_ofReal {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (u : Vec d → ℝ) (hmem : MemLp u p.exponent (normalizedCubeMeasure Q))
    (j : ℕ) :
    exactOverlapDepthTerm Q s.1 p.exponent.toReal u
      (exactOverlapScalarPIntegrableOfMemLp Q p hmem) j =
      ENNReal.ofReal (cubeBesovOverlapDepthSeminorm Q s.1 p.exponent u j) := by
  rw [exactOverlapDepthTerm_eq, exactOverlapDepthWeight_eq_ofReal_scalarP,
    exactOverlapDepthAverage_p_eq_ofReal Q p u hmem j]
  unfold cubeBesovOverlapDepthSeminorm
  rw [ENNReal.ofReal_mul (cubeBesovOverlapDepthWeight_nonneg Q s.1 j)]
  simp only [one_div]
  rw [ENNReal.ofReal_rpow_of_nonneg
    (cubeBesovOverlapDepthAverage_nonneg Q p.exponent u j)
    (inv_nonneg.mpr p.toReal_pos.le)]

/-- The diagonal exact scalar seminorm has no hidden root inside its depth
energies: its `p`-th power is the complete weighted depth-energy series. -/
theorem exactOverlapScalarPSeminorm_rpow_eq_tsum_depthEnergy {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q u hu) ^
        p.exponent.toReal =
      ∑' j : ℕ, (exactOverlapDepthWeight Q s.1 j) ^ p.exponent.toReal *
        exactOverlapDepthAverage Q p.exponent.toReal u hu j := by
  rw [exactOverlapFiniteSeminorm_eq]
  change ((∑' j : ℕ, (exactOverlapDepthTerm Q s.1 p.exponent.toReal u hu j) ^
      p.exponent.toReal) ^ (p.exponent.toReal)⁻¹) ^ p.exponent.toReal = _
  rw [ENNReal.rpow_inv_rpow p.toReal_pos.ne']
  apply tsum_congr
  intro j
  rw [exactOverlapDepthTerm_eq,
    ENNReal.mul_rpow_of_nonneg _ _ p.toReal_pos.le,
    ENNReal.rpow_inv_rpow p.toReal_pos.ne']

private theorem exactOverlapScalarPSeminorm_rpow_eq_iSup_partial_canonical {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hmem : MemLp u p.exponent (normalizedCubeMeasure Q)) :
    (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q u
      (exactOverlapScalarPIntegrableOfMemLp Q p hmem)) ^ p.exponent.toReal =
      ⨆ N : ℕ, (ENNReal.ofReal
        (cubeBesovOverlapPartialSeminorm Q s.1 p.exponent p.exponent N u)) ^
          p.exponent.toReal := by
  have htsum :
      (∑' j : ℕ, (ENNReal.ofReal
        (cubeBesovOverlapDepthSeminorm Q s.1 p.exponent u j)) ^
          p.exponent.toReal) =
      ⨆ N : ℕ, (ENNReal.ofReal
        (cubeBesovOverlapPartialSeminorm Q s.1 p.exponent p.exponent N u)) ^
          p.exponent.toReal := by
    rw [ENNReal.tsum_eq_iSup_nat' (N := fun i => i + 1)
      (Filter.tendsto_add_atTop_nat 1)]
    apply iSup_congr
    intro N
    calc
      ∑ j ∈ Finset.range (N + 1), (ENNReal.ofReal
          (cubeBesovOverlapDepthSeminorm Q s.1 p.exponent u j)) ^
            p.exponent.toReal =
          ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal
            (cubeBesovOverlapDepthSeminorm Q s.1 p.exponent u j ^
              p.exponent.toReal) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [ENNReal.ofReal_rpow_of_nonneg
                (cubeBesovOverlapDepthSeminorm_nonneg Q s.1 p.exponent u j)
                p.toReal_pos.le]
      _ = ENNReal.ofReal
          (cubeBesovOverlapPartialSeminorm Q s.1 p.exponent p.exponent N u ^
            p.exponent.toReal) := by
              simpa only using
                (Gagliardo.ofReal_partialSeminorm_rpow_eq Q s.1 p.ne_zero
                  p.ne_top N u).symm
      _ = (ENNReal.ofReal
          (cubeBesovOverlapPartialSeminorm Q s.1 p.exponent p.exponent N u)) ^
            p.exponent.toReal := by
              exact (ENNReal.ofReal_rpow_of_nonneg
                (cubeBesovOverlapPartialSeminorm_nonneg Q s.1 p.exponent
                  p.exponent N u) p.toReal_pos.le).symm
  calc
    (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q u
        (exactOverlapScalarPIntegrableOfMemLp Q p hmem)) ^ p.exponent.toReal =
        ∑' j : ℕ, (exactOverlapDepthTerm Q s.1 p.exponent.toReal u
          (exactOverlapScalarPIntegrableOfMemLp Q p hmem) j) ^
            p.exponent.toReal := by
      rw [exactOverlapFiniteSeminorm_eq]
      change ((∑' j : ℕ, (exactOverlapDepthTerm Q s.1 p.exponent.toReal u
        (exactOverlapScalarPIntegrableOfMemLp Q p hmem) j) ^
          p.exponent.toReal) ^ (p.exponent.toReal)⁻¹) ^
            p.exponent.toReal = _
      exact ENNReal.rpow_inv_rpow p.toReal_pos.ne' _
    _ = ∑' j : ℕ, (ENNReal.ofReal
          (cubeBesovOverlapDepthSeminorm Q s.1 p.exponent u j)) ^
            p.exponent.toReal := by
      apply tsum_congr
      intro j
      rw [exactOverlapDepthTerm_p_eq_ofReal Q s p u hmem j]
    _ = _ := htsum

/-- Under parent-cube `L^p` membership, the exact diagonal scalar-overlap
seminorm is the supremum of all finite-depth partial scalar-overlap
seminorms after taking the exact `p`-th power. -/
theorem exactOverlapScalarPSeminorm_rpow_eq_iSup_partial {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u)
    (hmem : MemLp u p.exponent (normalizedCubeMeasure Q)) :
    (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q u hu) ^
        p.exponent.toReal =
      ⨆ N : ℕ, (ENNReal.ofReal
        (cubeBesovOverlapPartialSeminorm Q s.1 p.exponent p.exponent N u)) ^
          p.exponent.toReal := by
  rw [exactOverlapFiniteSeminorm_congr_ae (exactOverlapScalarPParameters s p) Q hu
    (exactOverlapScalarPIntegrableOfMemLp Q p hmem)
    (fun _ _ _ => Filter.EventuallyEq.rfl)]
  exact exactOverlapScalarPSeminorm_rpow_eq_iSup_partial_canonical s p Q u hmem

end

end Homogenization
