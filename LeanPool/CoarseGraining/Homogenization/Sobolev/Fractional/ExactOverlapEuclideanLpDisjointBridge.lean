/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.PositiveOverlapBridge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePAveraging

/-!
# Disjoint-to-exact-overlap finite-`p` bridge

This file keeps the only localization step needed by the finite-`p`
coarse-graining forcing argument in the disjoint lane.  It compares the
resulting parent disjoint series to the canonical exact overlap series; it
does not assert localization of the overlap seminorm itself.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The unrooted Euclidean oscillation average over ordinary triadic
descendants at one depth. -/
noncomputable def cubeEuclideanPositiveBesovDisjointDepthPower {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d) (j : ℕ) : ℝ≥0∞ :=
  ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
    (descendantsAtDepth Q j).attach.sum (fun R =>
      (eLpNorm (fun x => HilbertVec.ofVec (F x - cubeAverageVec R.1 F))
        p.exponent (normalizedCubeMeasure R.1)) ^ p.exponent.toReal)

/-- The literal running-scale disjoint positive-Besov power series used only
internally before the parent overlap bridge. -/
noncomputable def cubeEuclideanPositiveBesovDisjointPowerEnergy {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  ∑' j : ℕ,
    ENNReal.ofReal
      (Real.rpow 3
        (-(s.1 * p.exponent.toReal * (((Q.scale - (j : ℤ) : ℤ) : ℝ))))) *
      cubeEuclideanPositiveBesovDisjointDepthPower Q p F j

private theorem disjoint_residual_eq_overlap_middleChild {d : ℕ}
    (R : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d) :
    eLpNorm (fun x => HilbertVec.ofVec (F x - cubeAverageVec R F))
        p.exponent (normalizedCubeMeasure R) =
      eLpNorm (fun x => HilbertVec.ofVec
        (F x - ScalarOverlap.cubeAverageVec (ScalarOverlap.middleChildCube R) F))
        p.exponent (ScalarOverlap.normalizedCubeMeasure (ScalarOverlap.middleChildCube R)) := by
  have hmean : ScalarOverlap.cubeAverageVec (ScalarOverlap.middleChildCube R) F = cubeAverageVec R F := by
    funext i
    simp only [ScalarOverlap.cubeAverageVec, cubeAverageVec]
    rw [ScalarOverlap.cubeAverage_middleChildCube]
  rw [hmean, ScalarOverlap.normalizedCubeMeasure_middleChildCube]

/-- At a fixed depth, the ordinary disjoint Euclidean oscillation average is
controlled by the exact overlap average.  The only loss is the dimension-only
middle-child cardinality factor. -/
theorem cubeEuclideanPositiveBesovDisjointDepthPower_le_overlap {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d) (j : ℕ) :
    cubeEuclideanPositiveBesovDisjointDepthPower Q p F j ≤
      (3 ^ d : ℝ≥0∞) *
        (cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j) ^
          p.exponent.toReal := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let O : Finset (TriadicCube d) := ScalarOverlap.centersAtDepth Q j
  let G : TriadicCube d → ℝ≥0∞ := fun S =>
    (eLpNorm (fun x => HilbertVec.ofVec
      (F x - ScalarOverlap.cubeAverageVec S F))
      p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal
  have hD0 : (D.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (by
      simpa [D] using descendantsAtDepth_nonempty Q j))
  have hO0 : (O.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (by
      simpa [O] using ScalarOverlap.centersAtDepth_nonempty Q j))
  have hDtop : (D.card : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hOtop : (O.card : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have himage : D.image ScalarOverlap.middleChildCube ⊆ O := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨R, hR, rfl⟩
    exact ScalarOverlap.middleChildCube_mem_centersAtDepth_of_mem_descendantsAtDepth
      (by simpa [D] using hR)
  have hsum_image : (D.image ScalarOverlap.middleChildCube).sum G ≤ O.sum G :=
    Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => bot_le)
  have hsum_eq :
      D.attach.sum (fun R =>
        (eLpNorm (fun x => HilbertVec.ofVec (F x - cubeAverageVec R.1 F))
          p.exponent (normalizedCubeMeasure R.1)) ^ p.exponent.toReal) =
      (D.image ScalarOverlap.middleChildCube).sum G := by
    calc
      D.attach.sum (fun R =>
          (eLpNorm (fun x => HilbertVec.ofVec (F x - cubeAverageVec R.1 F))
            p.exponent (normalizedCubeMeasure R.1)) ^ p.exponent.toReal) =
          D.sum (fun R =>
            (eLpNorm (fun x => HilbertVec.ofVec (F x - cubeAverageVec R F))
              p.exponent (normalizedCubeMeasure R)) ^ p.exponent.toReal) :=
        Finset.sum_attach D (fun R =>
          (eLpNorm (fun x => HilbertVec.ofVec (F x - cubeAverageVec R F))
            p.exponent (normalizedCubeMeasure R)) ^ p.exponent.toReal)
      _ = (D.image ScalarOverlap.middleChildCube).sum G := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro R hR
          simpa [G] using congrArg (fun z : ℝ≥0∞ => z ^ p.exponent.toReal)
            (disjoint_residual_eq_overlap_middleChild R p F)
        · intro R _ S _ hRS
          exact ScalarOverlap.middleChildCube_injective hRS
  have hcard : (O.card : ℝ≥0∞) ≤ (3 ^ d : ℝ≥0∞) * (D.card : ℝ≥0∞) := by
    exact_mod_cast (by
      simpa [D, O] using
        ScalarOverlap.centersAtDepth_card_le_three_pow_mul_descendantsAtDepth_card Q j)
  have hratio : (D.card : ℝ≥0∞)⁻¹ ≤
      (3 ^ d : ℝ≥0∞) * (O.card : ℝ≥0∞)⁻¹ := by
    suffices h : (D.card : ℝ≥0∞)⁻¹ ≤
        (3 ^ d : ℝ≥0∞) / (O.card : ℝ≥0∞) by
      simpa only [ENNReal.div_eq_inv_mul, mul_comm] using h
    apply (ENNReal.le_div_iff_mul_le (Or.inl hO0) (Or.inl hOtop)).2
    calc
      (D.card : ℝ≥0∞)⁻¹ * (O.card : ℝ≥0∞) ≤
          (D.card : ℝ≥0∞)⁻¹ *
            ((3 ^ d : ℝ≥0∞) * (D.card : ℝ≥0∞)) :=
        mul_le_mul_right hcard _
      _ = (3 ^ d : ℝ≥0∞) * ((D.card : ℝ≥0∞)⁻¹ * (D.card : ℝ≥0∞)) := by
        ring
      _ = (3 ^ d : ℝ≥0∞) := by
        rw [ENNReal.inv_mul_cancel hD0 hDtop, mul_one]
  rw [cubeEuclideanPositiveBesovOverlapDepthENorm_rpow]
  change (D.card : ℝ≥0∞)⁻¹ * D.attach.sum _ ≤
    (3 ^ d : ℝ≥0∞) * ((O.card : ℝ≥0∞)⁻¹ * O.attach.sum _)
  have hOattach : O.attach.sum (fun S =>
      (eLpNorm (fun x => HilbertVec.ofVec
        (F x - ScalarOverlap.cubeAverageVec S.1 F))
        p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ p.exponent.toReal) =
      O.sum G := by
    exact Finset.sum_attach O G
  rw [hsum_eq, hOattach]
  calc
    (D.card : ℝ≥0∞)⁻¹ * (D.image ScalarOverlap.middleChildCube).sum G ≤
        (D.card : ℝ≥0∞)⁻¹ * O.sum G :=
      mul_le_mul_right hsum_image _
    _ ≤ ((3 ^ d : ℝ≥0∞) * (O.card : ℝ≥0∞)⁻¹) * O.sum G :=
      mul_le_mul_left hratio _
    _ = (3 ^ d : ℝ≥0∞) * ((O.card : ℝ≥0∞)⁻¹ * O.sum G) := by
      ring

/-- The complete disjoint forcing power series is controlled by the literal
parent overlap power energy with a dimension-only factor. -/
theorem cubeEuclideanPositiveBesovDisjointPowerEnergy_le_overlap {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    cubeEuclideanPositiveBesovDisjointPowerEnergy Q s p F ≤
      (3 ^ d : ℝ≥0∞) * cubeEuclideanPositiveBesovOverlapPowerEnergy Q s p F := by
  rw [cubeEuclideanPositiveBesovOverlapPowerEnergy_eq_tsum_depthENorm]
  unfold cubeEuclideanPositiveBesovDisjointPowerEnergy
  let weight : ℕ → ℝ≥0∞ := fun j =>
    ENNReal.ofReal
      (Real.rpow 3
        (-(s.1 * p.exponent.toReal * (((Q.scale - (j : ℤ) : ℤ) : ℝ)))))
  calc
    (∑' j : ℕ, weight j * cubeEuclideanPositiveBesovDisjointDepthPower Q p F j) ≤
        ∑' j : ℕ, (3 ^ d : ℝ≥0∞) *
          (weight j * (cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j) ^
            p.exponent.toReal) := by
      apply ENNReal.tsum_le_tsum
      intro j
      calc
        weight j * cubeEuclideanPositiveBesovDisjointDepthPower Q p F j ≤
            weight j * ((3 ^ d : ℝ≥0∞) *
              (cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j) ^
                p.exponent.toReal) :=
          mul_le_mul_right
            (cubeEuclideanPositiveBesovDisjointDepthPower_le_overlap Q p F j) _
        _ = (3 ^ d : ℝ≥0∞) *
            (weight j * (cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j) ^
              p.exponent.toReal) := by
          ring
    _ = (3 ^ d : ℝ≥0∞) * ∑' j : ℕ,
        weight j * (cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j) ^
          p.exponent.toReal := ENNReal.tsum_mul_left

/-- For `p ≥ 2`, rooting the disjoint forcing power energy preserves a
dimension-only bridge constant. -/
theorem cubeEuclideanPositiveBesovDisjointPowerEnergy_root_le_overlap {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (F : Vec d → Vec d) :
    (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s p F) ^
        (p.exponent.toReal)⁻¹ ≤
      (3 ^ d : ℝ≥0∞) * cubeEuclideanPositiveBesovOverlapESeminorm Q s p F := by
  let r : ℝ := p.exponent.toReal
  let A : ℝ≥0∞ := cubeEuclideanPositiveBesovDisjointPowerEnergy Q s p F
  let B : ℝ≥0∞ := cubeEuclideanPositiveBesovOverlapPowerEnergy Q s p F
  let C : ℝ≥0∞ := (3 ^ d : ℝ≥0∞)
  have hr_pos : 0 < r := by
    dsimp [r]
    exact ENNReal.toReal_pos (zero_lt_one.trans p.one_lt).ne' p.lt_top.ne
  have hr_one : 1 ≤ r := by
    have hr_two : 2 ≤ r := by
      dsimp [r]
      exact ENNReal.toReal_mono p.lt_top.ne hp
    linarith
  have hr_inv : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr_one
  have hC_one : 1 ≤ C := by
    dsimp [C]
    exact one_le_pow₀ (by norm_num)
  have hCroot : C ^ r⁻¹ ≤ C := by
    calc
      C ^ r⁻¹ ≤ C ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le hC_one hr_inv
      _ = C := ENNReal.rpow_one C
  have hpower : A ≤ C * B := by
    dsimp [A, B, C]
    exact cubeEuclideanPositiveBesovDisjointPowerEnergy_le_overlap Q s p F
  have hroot : B ^ r⁻¹ = cubeEuclideanPositiveBesovOverlapESeminorm Q s p F := by
    dsimp [B]
    rw [← cubeEuclideanPositiveBesovOverlapESeminorm_rpow_eq_powerEnergy]
    exact ENNReal.rpow_rpow_inv hr_pos.ne' _
  calc
    A ^ r⁻¹ ≤ (C * B) ^ r⁻¹ :=
      ENNReal.rpow_le_rpow hpower (inv_nonneg.mpr hr_pos.le)
    _ = C ^ r⁻¹ * B ^ r⁻¹ :=
      ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hr_pos.le)
    _ ≤ C * B ^ r⁻¹ := mul_le_mul_left hCroot _
    _ = C * cubeEuclideanPositiveBesovOverlapESeminorm Q s p F := by rw [hroot]

end

end Homogenization
