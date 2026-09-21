/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.PartitionDerivatives

/-! # Partition Weights -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

/-- Raw relative overlap weight before normalization.  It is only meant to be
used for retained centers; off the retained set it is exactly zero so that
later finite sums can range over all cubes without changing values. -/
noncomputable def rawOverlapWeight {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (S : TriadicCube d) (x : Vec d) : ℝ :=
  if S ∈ overlapCentersAtDepth Q j then
    ∏ i : Fin d,
      lowerOverlapTransition Q S i x * upperOverlapTransition Q S i x
  else
    0

theorem rawOverlapWeight_zero_of_not_mem {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∉ overlapCentersAtDepth Q j) :
    ∀ x : Vec d, rawOverlapWeight Q j S x = 0 := by
  intro x
  simp [rawOverlapWeight, hS]

theorem contDiff_rawOverlapWeight {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (S : TriadicCube d) :
    ContDiff ℝ (⊤ : ℕ∞) (rawOverlapWeight Q j S) := by
  unfold rawOverlapWeight
  split
  · exact contDiff_prod fun i _ =>
      (contDiff_lowerOverlapTransition Q S i).mul
        (contDiff_upperOverlapTransition Q S i)
  · exact contDiff_const

theorem rawOverlapWeight_nonneg {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (S : TriadicCube d) (x : Vec d) :
    0 ≤ rawOverlapWeight Q j S x := by
  unfold rawOverlapWeight
  split
  · exact Finset.prod_nonneg fun i _ =>
      mul_nonneg
        (lowerOverlapTransition_nonneg Q S i x)
        (upperOverlapTransition_nonneg Q S i x)
  · norm_num

theorem rawOverlapWeight_le_one {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (S : TriadicCube d) (x : Vec d) :
    rawOverlapWeight Q j S x ≤ 1 := by
  unfold rawOverlapWeight
  split
  · exact Finset.prod_le_one
      (fun i _ =>
        mul_nonneg
          (lowerOverlapTransition_nonneg Q S i x)
          (upperOverlapTransition_nonneg Q S i x))
      (fun i _ =>
        mul_le_one₀
          (lowerOverlapTransition_le_one Q S i x)
          (upperOverlapTransition_nonneg Q S i x)
          (upperOverlapTransition_le_one Q S i x))
  · norm_num

theorem rawOverlapWeight_support_subset {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hxQ : x ∈ openCubeSet Q)
    (hne : rawOverlapWeight Q j S x ≠ 0) :
    x ∈ openOverlapCubeSet S := by
  rw [mem_openOverlapCubeSet_iff_coord_bounds]
  intro i
  have hprod :
      (∏ k : Fin d,
        lowerOverlapTransition Q S k x * upperOverlapTransition Q S k x) ≠ 0 := by
    simpa [rawOverlapWeight, hS] using hne
  have hfactor :
      lowerOverlapTransition Q S i x * upperOverlapTransition Q S i x ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  have hlower_ne : lowerOverlapTransition Q S i x ≠ 0 :=
    left_ne_zero_of_mul hfactor
  have hupper_ne : upperOverlapTransition Q S i x ≠ 0 :=
    right_ne_zero_of_mul hfactor
  exact ⟨lowerOverlapTransition_ne_zero_coord_lt hxQ hlower_ne,
    upperOverlapTransition_ne_zero_coord_lt hxQ hupper_ne⟩

theorem rawOverlapWeight_support_subset_overlapCubeSet {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hxQ : x ∈ openCubeSet Q)
    (hne : rawOverlapWeight Q j S x ≠ 0) :
    x ∈ overlapCubeSet S :=
  openOverlapCubeSet_subset_overlapCubeSet S
    (rawOverlapWeight_support_subset hS hxQ hne)

theorem rawOverlapWeight_eq_zero_of_not_mem_overlapCubeSet {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hxQ : x ∈ openCubeSet Q)
    (hxS : x ∉ overlapCubeSet S) :
    rawOverlapWeight Q j S x = 0 := by
  by_contra hne
  exact hxS (rawOverlapWeight_support_subset_overlapCubeSet hS hxQ hne)

theorem exists_coord_le_or_upper_le_of_not_mem_overlapCubeSet {d : ℕ}
    {S : TriadicCube d} {x : Vec d}
    (hxS : x ∉ overlapCubeSet S) :
    ∃ i : Fin d,
      x i ≤ overlapCoordLower S i ∨ overlapCoordUpper S i ≤ x i := by
  have hnot :
      ¬ ∀ i : Fin d,
        overlapCoordLower S i ≤ x i ∧ x i < overlapCoordUpper S i := by
    intro hx
    exact hxS (mem_overlapCubeSet_iff_coord_bounds.2 hx)
  rcases not_forall.mp hnot with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  by_cases hlo : overlapCoordLower S i ≤ x i
  · right
    have hnot_upper : ¬ x i < overlapCoordUpper S i := by
      intro hupper
      exact hi ⟨hlo, hupper⟩
    exact le_of_not_gt hnot_upper
  · left
    exact le_of_not_ge hlo

theorem rawOverlapWeight_fderiv_eq_zero_of_not_mem_overlapCubeSet {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hxQ : x ∈ openCubeSet Q)
    (hxS : x ∉ overlapCubeSet S) :
    fderiv ℝ (rawOverlapWeight Q j S) x = 0 := by
  classical
  rcases exists_coord_le_or_upper_le_of_not_mem_overlapCubeSet hxS with
    ⟨a, ha⟩
  let factor : Fin d → Vec d → ℝ :=
    fun i y => lowerOverlapTransition Q S i y * upperOverlapTransition Q S i y
  have hfactor_zero : factor a x = 0 := by
    rcases ha with hlo | hhi
    · exact overlapTransitionFactor_eq_zero_of_lower_coord_le hxQ hlo
    · exact overlapTransitionFactor_eq_zero_of_upper_coord_le hxQ hhi
  have hfactor_deriv_zero : fderiv ℝ (factor a) x = 0 := by
    rcases ha with hlo | hhi
    · exact fderiv_overlapTransitionFactor_eq_zero_of_lower_coord_le hxQ hlo
    · exact fderiv_overlapTransitionFactor_eq_zero_of_upper_coord_le hxQ hhi
  have hfactor_diff :
      ∀ i : Fin d, DifferentiableAt ℝ (factor i) x := by
    intro i
    exact
      ((contDiff_lowerOverlapTransition Q S i).mul
        (contDiff_upperOverlapTransition Q S i)).differentiable (by simp) x
  have hraw_fun :
      rawOverlapWeight Q j S =
        fun y : Vec d => ∏ i : Fin d, factor i y := by
    funext y
    simp [rawOverlapWeight, hS, factor]
  rw [hraw_fun]
  rw [fderiv_finsetProd (u := (Finset.univ : Finset (Fin d)))
    (g := fun i y => factor i y)]
  · apply Finset.sum_eq_zero
    intro i _hi
    by_cases hia : i = a
    · subst i
      simp [hfactor_deriv_zero]
    · have hprod_zero :
          (∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, factor j x) = 0 := by
        have ha_mem : a ∈ (Finset.univ : Finset (Fin d)).erase i := by
          rw [Finset.mem_erase]
          exact ⟨fun hai => hia hai.symm, Finset.mem_univ a⟩
        exact Finset.prod_eq_zero ha_mem hfactor_zero
      simp [hprod_zero]
  · intro i _hi
    exact hfactor_diff i

theorem norm_fderiv_rawOverlapWeight_le {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    ‖fderiv ℝ (rawOverlapWeight Q j S) x‖ ≤
      (Fintype.card (Fin d) : ℝ) *
        (2 * smoothTransitionProfile.derivBound * (cubeScaleFactor S)⁻¹) := by
  classical
  let factor : Fin d → Vec d → ℝ :=
    fun i y => lowerOverlapTransition Q S i y * upperOverlapTransition Q S i y
  have hfactor_diff :
      ∀ i : Fin d, DifferentiableAt ℝ (factor i) x := by
    intro i
    exact
      ((contDiff_lowerOverlapTransition Q S i).mul
        (contDiff_upperOverlapTransition Q S i)).differentiable (by simp) x
  have hraw_fun :
      rawOverlapWeight Q j S =
        fun y : Vec d => ∏ i : Fin d, factor i y := by
    funext y
    simp [rawOverlapWeight, hS, factor]
  rw [hraw_fun]
  rw [fderiv_finsetProd (u := (Finset.univ : Finset (Fin d)))
    (g := fun i y => factor i y)]
  · calc
      ‖∑ i ∈ (Finset.univ : Finset (Fin d)),
          (∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, factor j x) •
            fderiv ℝ (factor i) x‖
          ≤
            ∑ i ∈ (Finset.univ : Finset (Fin d)),
              ‖(∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, factor j x) •
                fderiv ℝ (factor i) x‖ := by
            simpa using
              norm_sum_le
                (s := (Finset.univ : Finset (Fin d)))
                (f := fun i =>
                  (∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, factor j x) •
                    fderiv ℝ (factor i) x)
      _ ≤
            ∑ _i ∈ (Finset.univ : Finset (Fin d)),
              2 * smoothTransitionProfile.derivBound * (cubeScaleFactor S)⁻¹ := by
            apply Finset.sum_le_sum
            intro i _hi
            rw [norm_smul]
            have hprod_nonneg :
                0 ≤ ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, factor j x :=
              Finset.prod_nonneg fun j _hj =>
                overlapTransitionFactor_nonneg Q S j x
            have hprod_le_one :
                (∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, factor j x) ≤ 1 :=
              Finset.prod_le_one
                (fun j _hj => overlapTransitionFactor_nonneg Q S j x)
                (fun j _hj => overlapTransitionFactor_le_one Q S j x)
            have hprod_norm_le :
                ‖∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, factor j x‖ ≤ 1 := by
              rw [Real.norm_eq_abs, abs_of_nonneg hprod_nonneg]
              exact hprod_le_one
            have hbound :
                ‖fderiv ℝ (factor i) x‖ ≤
                  2 * smoothTransitionProfile.derivBound * (cubeScaleFactor S)⁻¹ := by
              simpa [factor] using norm_fderiv_overlapTransitionFactor_le Q S i x
            calc
              ‖∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, factor j x‖ *
                  ‖fderiv ℝ (factor i) x‖
                  ≤
                    1 *
                      (2 * smoothTransitionProfile.derivBound *
                        (cubeScaleFactor S)⁻¹) :=
                mul_le_mul hprod_norm_le hbound
                  (norm_nonneg _)
                  (by norm_num)
              _ = 2 * smoothTransitionProfile.derivBound *
                    (cubeScaleFactor S)⁻¹ := by
                ring
      _ =
            (Fintype.card (Fin d) : ℝ) *
              (2 * smoothTransitionProfile.derivBound * (cubeScaleFactor S)⁻¹) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  · intro i _hi
    exact hfactor_diff i

theorem abs_rawOverlapWeight_coordDeriv_le {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (i : Fin d)
    (hS : S ∈ overlapCentersAtDepth Q j) :
    |euclideanCoordDeriv i (rawOverlapWeight Q j S) x| ≤
      (Fintype.card (Fin d) : ℝ) *
        (2 * smoothTransitionProfile.derivBound * (cubeScaleFactor S)⁻¹) := by
  have happly :
      ‖(fderiv ℝ (rawOverlapWeight Q j S) x) (basisVec i)‖ ≤
        ‖fderiv ℝ (rawOverlapWeight Q j S) x‖ * ‖basisVec i‖ :=
    (fderiv ℝ (rawOverlapWeight Q j S) x).le_opNorm (basisVec i)
  calc
    |euclideanCoordDeriv i (rawOverlapWeight Q j S) x|
        = ‖(fderiv ℝ (rawOverlapWeight Q j S) x) (basisVec i)‖ := by
          simp [euclideanCoordDeriv, Real.norm_eq_abs]
    _ ≤ ‖fderiv ℝ (rawOverlapWeight Q j S) x‖ * ‖basisVec i‖ := happly
    _ = ‖fderiv ℝ (rawOverlapWeight Q j S) x‖ := by
          rw [norm_basisVec, mul_one]
    _ ≤ (Fintype.card (Fin d) : ℝ) *
        (2 * smoothTransitionProfile.derivBound * (cubeScaleFactor S)⁻¹) :=
          norm_fderiv_rawOverlapWeight_le hS

theorem abs_rawOverlapWeight_coordDeriv_le_depthScale {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (i : Fin d)
    (hS : S ∈ overlapCentersAtDepth Q j) :
    |euclideanCoordDeriv i (rawOverlapWeight Q j S) x| ≤
      (Fintype.card (Fin d) : ℝ) *
        (2 * smoothTransitionProfile.derivBound *
          (3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹)) := by
  simpa [inv_cubeScaleFactor_eq_three_mul_inv_depthScale_of_mem_overlapCentersAtDepth hS]
    using abs_rawOverlapWeight_coordDeriv_le i hS

theorem rawOverlapWeight_coordDeriv_eq_zero_of_not_mem_overlapCubeSet {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (i : Fin d)
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hxQ : x ∈ openCubeSet Q)
    (hxS : x ∉ overlapCubeSet S) :
    euclideanCoordDeriv i (rawOverlapWeight Q j S) x = 0 := by
  unfold euclideanCoordDeriv
  rw [rawOverlapWeight_fderiv_eq_zero_of_not_mem_overlapCubeSet hS hxQ hxS]
  simp

theorem lowerOverlapTransition_pos_of_mem_openOverlap {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hxS : x ∈ openOverlapCubeSet S) :
    0 < lowerOverlapTransition Q S i x := by
  by_cases hboundary : overlapCoordLower S i ≤ cubeCoordLower Q i
  · simp [lowerOverlapTransition, hboundary]
  · have hx_lower := (mem_openOverlapCubeSet_iff_coord_bounds.mp hxS i).1
    have hscale : 0 < cubeScaleFactor S := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) S.scale)
    have harg :
        0 < (x i - overlapCoordLower S i) / cubeScaleFactor S := by
      exact div_pos (sub_pos.mpr hx_lower) hscale
    simpa [lowerOverlapTransition, hboundary] using
      smoothTransitionProfile.pos_of_pos harg

theorem upperOverlapTransition_pos_of_mem_openOverlap {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hxS : x ∈ openOverlapCubeSet S) :
    0 < upperOverlapTransition Q S i x := by
  by_cases hboundary : cubeCoordUpper Q i ≤ overlapCoordUpper S i
  · simp [upperOverlapTransition, hboundary]
  · have hx_upper := (mem_openOverlapCubeSet_iff_coord_bounds.mp hxS i).2
    have hscale : 0 < cubeScaleFactor S := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) S.scale)
    have harg :
        0 < (overlapCoordUpper S i - x i) / cubeScaleFactor S := by
      exact div_pos (sub_pos.mpr hx_upper) hscale
    simpa [upperOverlapTransition, hboundary] using
      smoothTransitionProfile.pos_of_pos harg

theorem rawOverlapWeight_pos_of_mem_openOverlap {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hxS : x ∈ openOverlapCubeSet S) :
    0 < rawOverlapWeight Q j S x := by
  simp only [rawOverlapWeight, if_pos hS]
  exact Finset.prod_pos fun i _ =>
    mul_pos
      (lowerOverlapTransition_pos_of_mem_openOverlap (Q := Q) hxS)
      (upperOverlapTransition_pos_of_mem_openOverlap (Q := Q) hxS)

theorem rawOverlapWeight_plateauChildCube_eq_one {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} {x : Vec d}
    (hR : R ∈ descendantsAtDepth Q j) (hxR : x ∈ cubeSet R) :
    rawOverlapWeight Q j (plateauChildCube Q R x) x = 1 := by
  have hS : plateauChildCube Q R x ∈ overlapCentersAtDepth Q j :=
    plateauChildCube_mem_overlapCentersAtDepth hR
  have hprod :
      (∏ i : Fin d,
        lowerOverlapTransition Q (plateauChildCube Q R x) i x *
          upperOverlapTransition Q (plateauChildCube Q R x) i x) = 1 := by
    simp [lowerOverlapTransition_plateauChildCube_eq_one hxR,
      upperOverlapTransition_plateauChildCube_eq_one hxR]
  simp [rawOverlapWeight, hS, hprod]

/-- Denominator of the normalized overlap partition planned for Stage 7. -/
noncomputable def rawOverlapWeightDenom {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (x : Vec d) : ℝ :=
  (overlapCentersAtDepth Q j).sum fun S => rawOverlapWeight Q j S x

theorem rawOverlapWeightDenom_nonneg {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (x : Vec d) :
    0 ≤ rawOverlapWeightDenom Q j x := by
  dsimp [rawOverlapWeightDenom]
  exact Finset.sum_nonneg fun S _ => rawOverlapWeight_nonneg Q j S x

theorem contDiff_rawOverlapWeightDenom {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (rawOverlapWeightDenom Q j) := by
  unfold rawOverlapWeightDenom
  exact ContDiff.sum fun S _hS => contDiff_rawOverlapWeight Q j S

theorem rawOverlapWeightDenom_coordDeriv_eq_sum {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (x : Vec d) (i : Fin d) :
    euclideanCoordDeriv i (rawOverlapWeightDenom Q j) x =
      (overlapCentersAtDepth Q j).sum
        (fun S => euclideanCoordDeriv i (rawOverlapWeight Q j S) x) := by
  unfold euclideanCoordDeriv rawOverlapWeightDenom
  rw [fderiv_fun_sum]
  · simp
  · intro S _hS
    exact (contDiff_rawOverlapWeight Q j S).differentiable (by simp) x

theorem abs_rawOverlapWeightDenom_coordDeriv_le {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q) (i : Fin d) :
    |euclideanCoordDeriv i (rawOverlapWeightDenom Q j) x| ≤
      (3 ^ d : ℝ) *
        ((Fintype.card (Fin d) : ℝ) *
          (2 * smoothTransitionProfile.derivBound *
            (3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹))) := by
  classical
  let A : TriadicCube d → ℝ :=
    fun S => euclideanCoordDeriv i (rawOverlapWeight Q j S) x
  let B : ℝ :=
    (Fintype.card (Fin d) : ℝ) *
      (2 * smoothTransitionProfile.derivBound *
        (3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹))
  have hB_nonneg : 0 ≤ B := by
    have hdepth_pos : 0 < cubeScaleFactor Q / (3 : ℝ) ^ j := by
      exact div_pos (cubeScaleFactor_pos' Q) (pow_pos (by norm_num : (0 : ℝ) < 3) j)
    dsimp [B]
    exact mul_nonneg
      (by positivity)
      (mul_nonneg
        (mul_nonneg (by norm_num) smoothTransitionProfile.derivBound_nonneg)
        (mul_nonneg (by norm_num) (inv_nonneg.mpr hdepth_pos.le)))
  have hsum_abs :
      (overlapCentersAtDepth Q j).sum (fun S => |A S|) =
        (overlapCentersAtDepthContaining Q j x).sum (fun S => |A S|) := by
    symm
    apply Finset.sum_subset
    · intro S hS
      exact (mem_overlapCentersAtDepthContaining_iff.mp hS).1
    · intro S hSD hSnot
      have hxS : x ∉ overlapCubeSet S := by
        intro hxS
        exact hSnot (mem_overlapCentersAtDepthContaining_iff.2 ⟨hSD, hxS⟩)
      have hzero :
          A S = 0 := by
        dsimp [A]
        exact rawOverlapWeight_coordDeriv_eq_zero_of_not_mem_overlapCubeSet
          i hSD hxQ hxS
      simp [hzero]
  have hactive_bound :
      (overlapCentersAtDepthContaining Q j x).sum (fun S => |A S|) ≤
        ((overlapCentersAtDepthContaining Q j x).card : ℝ) * B := by
    have hsum :=
      Finset.sum_le_card_nsmul
        (overlapCentersAtDepthContaining Q j x)
        (fun S => |A S|)
        B
        (by
          intro S hS
          have hS_center : S ∈ overlapCentersAtDepth Q j :=
            (mem_overlapCentersAtDepthContaining_iff.mp hS).1
          dsimp [A, B]
          exact abs_rawOverlapWeight_coordDeriv_le_depthScale i hS_center)
    simpa [nsmul_eq_mul] using hsum
  have hcard :
      ((overlapCentersAtDepthContaining Q j x).card : ℝ) ≤ (3 ^ d : ℝ) := by
    exact_mod_cast overlapCentersAtDepthContaining_card_le_pow Q j x
  calc
    |euclideanCoordDeriv i (rawOverlapWeightDenom Q j) x|
        =
          |(overlapCentersAtDepth Q j).sum
            (fun S => euclideanCoordDeriv i (rawOverlapWeight Q j S) x)| := by
          rw [rawOverlapWeightDenom_coordDeriv_eq_sum Q j x i]
    _ ≤ (overlapCentersAtDepth Q j).sum (fun S => |A S|) := by
          simpa [A] using
            Finset.abs_sum_le_sum_abs
              (fun S => euclideanCoordDeriv i (rawOverlapWeight Q j S) x)
              (overlapCentersAtDepth Q j)
    _ =
          (overlapCentersAtDepthContaining Q j x).sum (fun S => |A S|) := hsum_abs
    _ ≤ ((overlapCentersAtDepthContaining Q j x).card : ℝ) * B := hactive_bound
    _ ≤ (3 ^ d : ℝ) * B :=
          mul_le_mul_of_nonneg_right hcard hB_nonneg
    _ =
      (3 ^ d : ℝ) *
        ((Fintype.card (Fin d) : ℝ) *
          (2 * smoothTransitionProfile.derivBound *
            (3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹))) := by
          rfl

theorem rawOverlapWeightDenom_pos_of_exists_openOverlap {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {x : Vec d}
    (hcover :
      ∃ S ∈ overlapCentersAtDepth Q j, x ∈ openOverlapCubeSet S) :
    0 < rawOverlapWeightDenom Q j x := by
  rcases hcover with ⟨S, hS, hxS⟩
  dsimp [rawOverlapWeightDenom]
  exact Finset.sum_pos'
      (fun T _ => rawOverlapWeight_nonneg Q j T x)
      ⟨S, hS, rawOverlapWeight_pos_of_mem_openOverlap hS hxS⟩

theorem one_le_rawOverlapWeightDenom_of_mem_openCubeSet {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q) :
    1 ≤ rawOverlapWeightDenom Q j x := by
  have hxQ_closed : x ∈ cubeSet Q := openCubeSet_subset_cubeSet Q hxQ
  rcases exists_mem_descendantsAtDepth_of_mem_cubeSet j hxQ_closed with
    ⟨R, hR, hxR⟩
  let S : TriadicCube d := plateauChildCube Q R x
  have hS : S ∈ overlapCentersAtDepth Q j := by
    simpa [S] using plateauChildCube_mem_overlapCentersAtDepth hR
  have hraw : rawOverlapWeight Q j S x = 1 := by
    simpa [S] using rawOverlapWeight_plateauChildCube_eq_one hR hxR
  dsimp [rawOverlapWeightDenom]
  calc
    1 = rawOverlapWeight Q j S x := hraw.symm
    _ ≤ (overlapCentersAtDepth Q j).sum fun T => rawOverlapWeight Q j T x :=
        Finset.single_le_sum
          (fun T _hT => rawOverlapWeight_nonneg Q j T x)
          hS

theorem rawOverlapWeightDenom_pos_of_mem_openCubeSet {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q) :
    0 < rawOverlapWeightDenom Q j x :=
  lt_of_lt_of_le zero_lt_one (one_le_rawOverlapWeightDenom_of_mem_openCubeSet hxQ)

noncomputable def overlapWeightDenomSafe {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (x : Vec d) : ℝ :=
  rawOverlapWeightDenom Q j x +
    smoothTransitionProfile (1 - rawOverlapWeightDenom Q j x)

theorem overlapWeightDenomSafe_eq_raw_of_mem_openCubeSet {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q) :
    overlapWeightDenomSafe Q j x = rawOverlapWeightDenom Q j x := by
  have hD : 1 ≤ rawOverlapWeightDenom Q j x :=
    one_le_rawOverlapWeightDenom_of_mem_openCubeSet hxQ
  have harg : 1 - rawOverlapWeightDenom Q j x ≤ 0 := by
    linarith
  simp [overlapWeightDenomSafe, smoothTransitionProfile.zero_of_nonpos harg]

theorem overlapWeightDenomSafe_pos {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (x : Vec d) :
    0 < overlapWeightDenomSafe Q j x := by
  by_cases hD : 1 ≤ rawOverlapWeightDenom Q j x
  · have harg : 1 - rawOverlapWeightDenom Q j x ≤ 0 := by
      linarith
    simp [overlapWeightDenomSafe, smoothTransitionProfile.zero_of_nonpos harg]
    exact lt_of_lt_of_le zero_lt_one hD
  · have hDlt : rawOverlapWeightDenom Q j x < 1 := lt_of_not_ge hD
    have harg_pos : 0 < 1 - rawOverlapWeightDenom Q j x := by
      linarith
    have hraw_nonneg : 0 ≤ rawOverlapWeightDenom Q j x :=
      rawOverlapWeightDenom_nonneg Q j x
    have hprofile_pos :
        0 < smoothTransitionProfile (1 - rawOverlapWeightDenom Q j x) :=
      smoothTransitionProfile.pos_of_pos harg_pos
    dsimp [overlapWeightDenomSafe]
    linarith

theorem contDiff_overlapWeightDenomSafe {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (overlapWeightDenomSafe Q j) := by
  unfold overlapWeightDenomSafe
  exact (contDiff_rawOverlapWeightDenom Q j).add
    (smoothTransitionProfile.smooth.comp
      (contDiff_const.sub (contDiff_rawOverlapWeightDenom Q j)))

theorem overlapWeightDenomSafe_coordDeriv_eq_raw_of_mem_openCubeSet {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q) (i : Fin d) :
    euclideanCoordDeriv i (overlapWeightDenomSafe Q j) x =
      euclideanCoordDeriv i (rawOverlapWeightDenom Q j) x := by
  have heq :
      overlapWeightDenomSafe Q j =ᶠ[nhds x] rawOverlapWeightDenom Q j :=
    ((isOpen_openCubeSet Q).eventually_mem hxQ).mono fun y hy => by
      exact overlapWeightDenomSafe_eq_raw_of_mem_openCubeSet (Q := Q) (j := j) (x := y) hy
  unfold euclideanCoordDeriv
  rw [Filter.EventuallyEq.fderiv_eq heq]

theorem abs_inv_overlapWeightDenomSafe_coordDeriv_le {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q) (i : Fin d) :
    |euclideanCoordDeriv i
        (fun y : Vec d => (overlapWeightDenomSafe Q j y)⁻¹) x| ≤
      |euclideanCoordDeriv i (rawOverlapWeightDenom Q j) x| := by
  let D : Vec d → ℝ := overlapWeightDenomSafe Q j
  have hD_diff : DifferentiableAt ℝ D x :=
    (contDiff_overlapWeightDenomSafe Q j).differentiable (by simp) x
  have hD_ge : 1 ≤ D x := by
    have hsafe : D x = rawOverlapWeightDenom Q j x := by
      simpa [D] using overlapWeightDenomSafe_eq_raw_of_mem_openCubeSet hxQ
    rw [hsafe]
    exact one_le_rawOverlapWeightDenom_of_mem_openCubeSet hxQ
  have hD_pos : 0 < D x := lt_of_lt_of_le zero_lt_one hD_ge
  have hD_ne : D x ≠ 0 := ne_of_gt hD_pos
  have hcoord :
      euclideanCoordDeriv i (fun y : Vec d => (D y)⁻¹) x =
        -((D x) ^ 2)⁻¹ * euclideanCoordDeriv i D x := by
    unfold euclideanCoordDeriv
    rw [fderiv_fun_comp (x := x) (differentiableAt_inv hD_ne) hD_diff]
    rw [fderiv_inv]
    simp [ContinuousLinearMap.comp_apply, smul_eq_mul, mul_comm]
  have hdraw :
      euclideanCoordDeriv i D x =
        euclideanCoordDeriv i (rawOverlapWeightDenom Q j) x := by
    simpa [D] using overlapWeightDenomSafe_coordDeriv_eq_raw_of_mem_openCubeSet hxQ i
  have hcoeff_le : |-((D x) ^ 2)⁻¹| ≤ 1 := by
    have hsq_ge : 1 ≤ (D x) ^ 2 := by
      nlinarith
    rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (D x)))]
    exact inv_le_one_of_one_le₀ hsq_ge
  rw [hcoord, hdraw, abs_mul]
  calc
    |-((D x) ^ 2)⁻¹| *
        |euclideanCoordDeriv i (rawOverlapWeightDenom Q j) x|
        ≤ 1 * |euclideanCoordDeriv i (rawOverlapWeightDenom Q j) x| :=
          mul_le_mul_of_nonneg_right hcoeff_le (abs_nonneg _)
    _ = |euclideanCoordDeriv i (rawOverlapWeightDenom Q j) x| := by
          ring

noncomputable def overlapPartitionWeight {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (S : TriadicCube d) (x : Vec d) : ℝ :=
  rawOverlapWeight Q j S x / overlapWeightDenomSafe Q j x

theorem contDiff_overlapPartitionWeight {d : ℕ}
    (Q S : TriadicCube d) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (overlapPartitionWeight Q j S) := by
  unfold overlapPartitionWeight
  exact (contDiff_rawOverlapWeight Q j S).div
    (contDiff_overlapWeightDenomSafe Q j)
    (fun x => ne_of_gt (overlapWeightDenomSafe_pos Q j x))

theorem contDiffOn_overlapPartitionWeight_openCubeSet {d : ℕ}
    (Q S : TriadicCube d) (j : ℕ) :
    ContDiffOn ℝ 1 (overlapPartitionWeight Q j S) (openCubeSet Q) := by
  exact (contDiff_overlapPartitionWeight Q S j).of_le (by simp) |>.contDiffOn

theorem overlapPartitionWeight_coordDeriv_eq {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d} (i : Fin d) :
    euclideanCoordDeriv i (overlapPartitionWeight Q j S) x =
      rawOverlapWeight Q j S x *
          euclideanCoordDeriv i
            (fun y : Vec d => (overlapWeightDenomSafe Q j y)⁻¹) x +
        (overlapWeightDenomSafe Q j x)⁻¹ *
          euclideanCoordDeriv i (rawOverlapWeight Q j S) x := by
  let R : Vec d → ℝ := rawOverlapWeight Q j S
  let I : Vec d → ℝ := fun y : Vec d => (overlapWeightDenomSafe Q j y)⁻¹
  have hR_diff : DifferentiableAt ℝ R x :=
    (contDiff_rawOverlapWeight Q j S).differentiable (by simp) x
  have hD_diff : DifferentiableAt ℝ (overlapWeightDenomSafe Q j) x :=
    (contDiff_overlapWeightDenomSafe Q j).differentiable (by simp) x
  have hD_ne : overlapWeightDenomSafe Q j x ≠ 0 :=
    ne_of_gt (overlapWeightDenomSafe_pos Q j x)
  have hI_diff : DifferentiableAt ℝ I x := by
    dsimp [I]
    exact hD_diff.inv hD_ne
  have hfun :
      overlapPartitionWeight Q j S = fun y : Vec d => R y * I y := by
    funext y
    simp [overlapPartitionWeight, R, I, div_eq_mul_inv]
  unfold euclideanCoordDeriv
  rw [hfun, fderiv_fun_mul hR_diff hI_diff]
  simp [R, I]

theorem abs_overlapPartitionWeight_coordDeriv_le {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (i : Fin d)
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hxQ : x ∈ openCubeSet Q) :
    |euclideanCoordDeriv i (overlapPartitionWeight Q j S) x| ≤
      (Fintype.card (Fin d) : ℝ) *
        (2 * smoothTransitionProfile.derivBound *
          (3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹)) +
        (3 ^ d : ℝ) *
          ((Fintype.card (Fin d) : ℝ) *
            (2 * smoothTransitionProfile.derivBound *
              (3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹))) := by
  let B : ℝ :=
    (Fintype.card (Fin d) : ℝ) *
      (2 * smoothTransitionProfile.derivBound *
        (3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹))
  let E : ℝ := (3 ^ d : ℝ) * B
  have hdepth_pos : 0 < cubeScaleFactor Q / (3 : ℝ) ^ j := by
    exact div_pos (cubeScaleFactor_pos' Q) (pow_pos (by norm_num : (0 : ℝ) < 3) j)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (by positivity)
      (mul_nonneg
        (mul_nonneg (by norm_num) smoothTransitionProfile.derivBound_nonneg)
        (mul_nonneg (by norm_num) (inv_nonneg.mpr hdepth_pos.le)))
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (by positivity) hB_nonneg
  let R : ℝ := rawOverlapWeight Q j S x
  let D : ℝ := overlapWeightDenomSafe Q j x
  let dR : ℝ := euclideanCoordDeriv i (rawOverlapWeight Q j S) x
  let dI : ℝ :=
    euclideanCoordDeriv i
      (fun y : Vec d => (overlapWeightDenomSafe Q j y)⁻¹) x
  have hR_abs_le : |R| ≤ 1 := by
    dsimp [R]
    rw [abs_of_nonneg (rawOverlapWeight_nonneg Q j S x)]
    exact rawOverlapWeight_le_one Q j S x
  have hD_ge : 1 ≤ D := by
    dsimp [D]
    have hsafe :
        overlapWeightDenomSafe Q j x = rawOverlapWeightDenom Q j x :=
      overlapWeightDenomSafe_eq_raw_of_mem_openCubeSet hxQ
    rw [hsafe]
    exact one_le_rawOverlapWeightDenom_of_mem_openCubeSet hxQ
  have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one hD_ge
  have hD_inv_abs_le : |D⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr hD_pos.le)]
    exact inv_le_one_of_one_le₀ hD_ge
  have hdR_le : |dR| ≤ B := by
    dsimp [dR, B]
    exact abs_rawOverlapWeight_coordDeriv_le_depthScale i hS
  have hdI_le : |dI| ≤ E := by
    dsimp [dI, E, B]
    exact
      (abs_inv_overlapWeightDenomSafe_coordDeriv_le hxQ i).trans
        (abs_rawOverlapWeightDenom_coordDeriv_le hxQ i)
  have hcoord :
      euclideanCoordDeriv i (overlapPartitionWeight Q j S) x =
        R * dI + D⁻¹ * dR := by
    dsimp [R, D, dR, dI]
    exact overlapPartitionWeight_coordDeriv_eq (Q := Q) (S := S) (j := j) (x := x) i
  calc
    |euclideanCoordDeriv i (overlapPartitionWeight Q j S) x|
        = |R * dI + D⁻¹ * dR| := by rw [hcoord]
    _ ≤ |R * dI| + |D⁻¹ * dR| := abs_add_le _ _
    _ = |R| * |dI| + |D⁻¹| * |dR| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * E + 1 * B := by
          exact add_le_add
            (mul_le_mul hR_abs_le hdI_le (abs_nonneg _) (by norm_num))
            (mul_le_mul hD_inv_abs_le hdR_le (abs_nonneg _) (by norm_num))
    _ = B + E := by ring
    _ =
      (Fintype.card (Fin d) : ℝ) *
        (2 * smoothTransitionProfile.derivBound *
          (3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹)) +
        (3 ^ d : ℝ) *
          ((Fintype.card (Fin d) : ℝ) *
            (2 * smoothTransitionProfile.derivBound *
              (3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹))) := by
          rfl

noncomputable def smoothOverlapPartitionDerivativeConstant (d : ℕ) : ℝ :=
  (Fintype.card (Fin d) : ℝ) *
      (2 * smoothTransitionProfile.derivBound * 3) +
    (3 ^ d : ℝ) *
      ((Fintype.card (Fin d) : ℝ) *
        (2 * smoothTransitionProfile.derivBound * 3))

theorem smoothOverlapPartitionDerivativeConstant_nonneg (d : ℕ) :
    0 ≤ smoothOverlapPartitionDerivativeConstant d := by
  unfold smoothOverlapPartitionDerivativeConstant
  exact add_nonneg
    (mul_nonneg
      (by positivity)
      (mul_nonneg
        (mul_nonneg (by norm_num) smoothTransitionProfile.derivBound_nonneg)
        (by norm_num)))
    (mul_nonneg
      (by positivity)
      (mul_nonneg
        (by positivity)
        (mul_nonneg
          (mul_nonneg (by norm_num) smoothTransitionProfile.derivBound_nonneg)
          (by norm_num))))

theorem abs_overlapPartitionWeight_coordDeriv_le_depthScale {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (i : Fin d)
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hxQ : x ∈ openCubeSet Q) :
    |euclideanCoordDeriv i (overlapPartitionWeight Q j S) x| ≤
      smoothOverlapPartitionDerivativeConstant d /
        (cubeScaleFactor Q / (3 : ℝ) ^ j) := by
  have hdepth_pos : 0 < cubeScaleFactor Q / (3 : ℝ) ^ j := by
    exact div_pos (cubeScaleFactor_pos' Q) (pow_pos (by norm_num : (0 : ℝ) < 3) j)
  calc
    |euclideanCoordDeriv i (overlapPartitionWeight Q j S) x|
        ≤
          (Fintype.card (Fin d) : ℝ) *
            (2 * smoothTransitionProfile.derivBound *
              (3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹)) +
            (3 ^ d : ℝ) *
              ((Fintype.card (Fin d) : ℝ) *
                (2 * smoothTransitionProfile.derivBound *
                  (3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹))) :=
          abs_overlapPartitionWeight_coordDeriv_le i hS hxQ
    _ =
      smoothOverlapPartitionDerivativeConstant d /
        (cubeScaleFactor Q / (3 : ℝ) ^ j) := by
          dsimp [smoothOverlapPartitionDerivativeConstant]
          field_simp [ne_of_gt hdepth_pos]

theorem overlapPartitionWeight_nonneg_of_mem_openCubeSet {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (_hxQ : x ∈ openCubeSet Q) :
    0 ≤ overlapPartitionWeight Q j S x := by
  exact div_nonneg
    (rawOverlapWeight_nonneg Q j S x)
    (overlapWeightDenomSafe_pos Q j x).le

theorem overlapPartitionWeight_zero_of_not_mem {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∉ overlapCentersAtDepth Q j) :
    ∀ x : Vec d, overlapPartitionWeight Q j S x = 0 := by
  intro x
  simp [overlapPartitionWeight, rawOverlapWeight_zero_of_not_mem hS x]

theorem overlapPartitionWeight_support_subset {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hxQ : x ∈ openCubeSet Q)
    (hne : overlapPartitionWeight Q j S x ≠ 0) :
    x ∈ openOverlapCubeSet S := by
  have hraw_ne : rawOverlapWeight Q j S x ≠ 0 := by
    intro hraw
    apply hne
    simp [overlapPartitionWeight, hraw]
  exact rawOverlapWeight_support_subset hS hxQ hraw_ne

theorem overlapPartitionWeight_fderiv_eq_zero_of_not_mem_overlapCubeSet {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d}
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hxQ : x ∈ openCubeSet Q)
    (hxS : x ∉ overlapCubeSet S) :
    fderiv ℝ (overlapPartitionWeight Q j S) x = 0 := by
  have hraw_zero :
      rawOverlapWeight Q j S x = 0 :=
    rawOverlapWeight_eq_zero_of_not_mem_overlapCubeSet hS hxQ hxS
  have hraw_deriv_zero :
      fderiv ℝ (rawOverlapWeight Q j S) x = 0 :=
    rawOverlapWeight_fderiv_eq_zero_of_not_mem_overlapCubeSet hS hxQ hxS
  have hraw_diff :
      DifferentiableAt ℝ (rawOverlapWeight Q j S) x :=
    (contDiff_rawOverlapWeight Q j S).differentiable (by simp) x
  have hden_diff :
      DifferentiableAt ℝ (overlapWeightDenomSafe Q j) x :=
    (contDiff_overlapWeightDenomSafe Q j).differentiable (by simp) x
  have hden_ne : overlapWeightDenomSafe Q j x ≠ 0 :=
    ne_of_gt (overlapWeightDenomSafe_pos Q j x)
  have hden_inv_diff :
      DifferentiableAt ℝ (fun y : Vec d => (overlapWeightDenomSafe Q j y)⁻¹) x :=
    hden_diff.inv hden_ne
  have hfun :
      overlapPartitionWeight Q j S =
        fun y : Vec d =>
          rawOverlapWeight Q j S y * (overlapWeightDenomSafe Q j y)⁻¹ := by
    funext y
    rw [overlapPartitionWeight, div_eq_mul_inv]
  rw [hfun]
  rw [fderiv_fun_mul hraw_diff hden_inv_diff]
  simp [hraw_zero, hraw_deriv_zero]

theorem overlapPartitionWeight_coordDeriv_zero_of_not_mem_overlap {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d} (i : Fin d)
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hxQ : x ∈ openCubeSet Q)
    (hxS : x ∉ overlapCubeSet S) :
    euclideanCoordDeriv i (overlapPartitionWeight Q j S) x = 0 := by
  unfold euclideanCoordDeriv
  rw [overlapPartitionWeight_fderiv_eq_zero_of_not_mem_overlapCubeSet hS hxQ hxS]
  simp

theorem overlapPartitionWeight_sum_eq_one {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q) :
    (overlapCentersAtDepth Q j).sum
        (fun S => overlapPartitionWeight Q j S x) = 1 := by
  have hden_ne : rawOverlapWeightDenom Q j x ≠ 0 :=
    ne_of_gt (rawOverlapWeightDenom_pos_of_mem_openCubeSet hxQ)
  have hsafe : overlapWeightDenomSafe Q j x = rawOverlapWeightDenom Q j x :=
    overlapWeightDenomSafe_eq_raw_of_mem_openCubeSet hxQ
  calc
    (overlapCentersAtDepth Q j).sum
        (fun S => overlapPartitionWeight Q j S x)
        =
          (overlapCentersAtDepth Q j).sum
            (fun S => rawOverlapWeight Q j S x / rawOverlapWeightDenom Q j x) := by
          simp [overlapPartitionWeight, hsafe]
    _ =
          rawOverlapWeightDenom Q j x / rawOverlapWeightDenom Q j x := by
          rw [← Finset.sum_div]
          rfl
    _ = 1 := div_self hden_ne

theorem overlapPartitionWeight_coordDeriv_sum_eq_zero {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q) (i : Fin d) :
    (overlapCentersAtDepth Q j).sum
        (fun S => euclideanCoordDeriv i (overlapPartitionWeight Q j S) x) = 0 := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let F : Vec d → ℝ :=
    fun y => ∑ S ∈ D, overlapPartitionWeight Q j S y
  have hsum :
      fderiv ℝ F x =
        ∑ S ∈ D, fderiv ℝ (overlapPartitionWeight Q j S) x := by
    dsimp [F]
    rw [fderiv_fun_sum]
    intro S _hS
    exact (contDiff_overlapPartitionWeight Q S j).differentiable (by simp) x
  have hF_eventually : F =ᶠ[nhds x] fun _ : Vec d => (1 : ℝ) := by
    exact ((isOpen_openCubeSet Q).eventually_mem hxQ).mono fun y hy => by
      simpa [F, D] using
        overlapPartitionWeight_sum_eq_one (Q := Q) (j := j) (x := y) hy
  have hF_deriv_zero : fderiv ℝ F x = 0 := by
    have hconst : fderiv ℝ (fun _ : Vec d => (1 : ℝ)) x = 0 := by
      simp
    rw [Filter.EventuallyEq.fderiv_eq hF_eventually, hconst]
  have happly :
      (∑ S ∈ D, fderiv ℝ (overlapPartitionWeight Q j S) x) (basisVec i) = 0 := by
    rw [← hsum, hF_deriv_zero]
    simp
  calc
    (overlapCentersAtDepth Q j).sum
        (fun S => euclideanCoordDeriv i (overlapPartitionWeight Q j S) x)
        =
          ∑ S ∈ D,
            (fderiv ℝ (overlapPartitionWeight Q j S) x) (basisVec i) := by
          rfl
    _ =
          (∑ S ∈ D, fderiv ℝ (overlapPartitionWeight Q j S) x) (basisVec i) := by
          simp
    _ = 0 := happly

theorem rawOverlapWeight_active_card_bound {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q) :
    ((overlapCentersAtDepth Q j).filter
      (fun S => rawOverlapWeight Q j S x ≠ 0)).card ≤ 3 ^ d := by
  refine
    (Finset.card_le_card ?_).trans
      (overlapCentersAtDepthContaining_card_le_pow Q j x)
  intro S hS
  rw [Finset.mem_filter] at hS
  rw [mem_overlapCentersAtDepthContaining_iff]
  exact ⟨hS.1,
    rawOverlapWeight_support_subset_overlapCubeSet hS.1 hxQ hS.2⟩

theorem overlapPartitionWeight_active_card_bound {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q) :
    ((overlapCentersAtDepth Q j).filter
      (fun S => overlapPartitionWeight Q j S x ≠ 0)).card ≤ 3 ^ d := by
  refine
    (Finset.card_le_card ?_).trans
      (rawOverlapWeight_active_card_bound (Q := Q) (j := j) hxQ)
  intro S hS
  rw [Finset.mem_filter] at hS ⊢
  refine ⟨hS.1, ?_⟩
  intro hraw
  exact hS.2 (by simp [overlapPartitionWeight, hraw])


end

end Homogenization
