/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.PartitionGeometry

/-! # Partition Derivatives -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

theorem norm_fderiv_lowerOverlapArgument_le {d : ℕ}
    (S : TriadicCube d) (i : Fin d) (x : Vec d) :
    ‖fderiv ℝ
      (fun y : Vec d => (y i - overlapCoordLower S i) / cubeScaleFactor S) x‖
      ≤ (cubeScaleFactor S)⁻¹ := by
  let c : Vec d := fun _ => overlapCoordLower S i
  have hfun :
      (fun y : Vec d => (y i - overlapCoordLower S i) / cubeScaleFactor S) =
        fun y : Vec d => (cubeScaleFactor S)⁻¹ * (y i - c i) := by
    funext y
    dsimp [c]
    field_simp [(cubeScaleFactor_pos' S).ne']
  rw [hfun]
  rw [fderiv_const_mul]
  · calc
      ‖(cubeScaleFactor S)⁻¹ •
          fderiv ℝ (fun y : Vec d => y i - c i) x‖
          = ‖(cubeScaleFactor S)⁻¹‖ *
              ‖fderiv ℝ (fun y : Vec d => y i - c i) x‖ := norm_smul _ _
      _ ≤ ‖(cubeScaleFactor S)⁻¹‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (norm_fderiv_coord_sub_const_le_one i c x)
            (norm_nonneg _)
      _ = (cubeScaleFactor S)⁻¹ := by
          rw [mul_one, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (cubeScaleFactor_pos' S).le)]
  · fun_prop

theorem norm_fderiv_upperOverlapArgument_le {d : ℕ}
    (S : TriadicCube d) (i : Fin d) (x : Vec d) :
    ‖fderiv ℝ
      (fun y : Vec d => (overlapCoordUpper S i - y i) / cubeScaleFactor S) x‖
      ≤ (cubeScaleFactor S)⁻¹ := by
  let c : Vec d := fun _ => overlapCoordUpper S i
  have hfun :
      (fun y : Vec d => (overlapCoordUpper S i - y i) / cubeScaleFactor S) =
        fun y : Vec d => -((cubeScaleFactor S)⁻¹) * (y i - c i) := by
    funext y
    dsimp [c]
    field_simp [(cubeScaleFactor_pos' S).ne']
    ring
  rw [hfun]
  rw [fderiv_const_mul]
  · calc
      ‖(-((cubeScaleFactor S)⁻¹)) •
          fderiv ℝ (fun y : Vec d => y i - c i) x‖
          = ‖-((cubeScaleFactor S)⁻¹)‖ *
              ‖fderiv ℝ (fun y : Vec d => y i - c i) x‖ := norm_smul _ _
      _ ≤ ‖-((cubeScaleFactor S)⁻¹)‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (norm_fderiv_coord_sub_const_le_one i c x)
            (norm_nonneg _)
      _ = (cubeScaleFactor S)⁻¹ := by
          rw [mul_one, norm_neg, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (cubeScaleFactor_pos' S).le)]
  · fun_prop

theorem norm_fderiv_lowerOverlapTransition_le {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) (x : Vec d) :
    ‖fderiv ℝ (lowerOverlapTransition Q S i) x‖ ≤
      smoothTransitionProfile.derivBound * (cubeScaleFactor S)⁻¹ := by
  by_cases hboundary : overlapCoordLower S i ≤ cubeCoordLower Q i
  · have hfun : lowerOverlapTransition Q S i = fun _ : Vec d => (1 : ℝ) := by
      funext y
      simp [lowerOverlapTransition, hboundary]
    rw [hfun]
    simp
    exact mul_nonneg smoothTransitionProfile.derivBound_nonneg
      (inv_nonneg.mpr (cubeScaleFactor_pos' S).le)
  · have harg_diff :
        DifferentiableAt ℝ
          (fun y : Vec d => (y i - overlapCoordLower S i) / cubeScaleFactor S) x := by
      fun_prop
    have hfun :
        lowerOverlapTransition Q S i =
          fun y : Vec d =>
            smoothTransitionProfile ((y i - overlapCoordLower S i) / cubeScaleFactor S) := by
      funext y
      simp [lowerOverlapTransition, hboundary]
    rw [hfun]
    exact
      (norm_fderiv_profile_comp_le smoothTransitionProfile.quantitativeProfile
          harg_diff).trans
        (mul_le_mul_of_nonneg_left
          (norm_fderiv_lowerOverlapArgument_le S i x)
          smoothTransitionProfile.derivBound_nonneg)

theorem norm_fderiv_upperOverlapTransition_le {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) (x : Vec d) :
    ‖fderiv ℝ (upperOverlapTransition Q S i) x‖ ≤
      smoothTransitionProfile.derivBound * (cubeScaleFactor S)⁻¹ := by
  by_cases hboundary : cubeCoordUpper Q i ≤ overlapCoordUpper S i
  · have hfun : upperOverlapTransition Q S i = fun _ : Vec d => (1 : ℝ) := by
      funext y
      simp [upperOverlapTransition, hboundary]
    rw [hfun]
    simp
    exact mul_nonneg smoothTransitionProfile.derivBound_nonneg
      (inv_nonneg.mpr (cubeScaleFactor_pos' S).le)
  · have harg_diff :
        DifferentiableAt ℝ
          (fun y : Vec d => (overlapCoordUpper S i - y i) / cubeScaleFactor S) x := by
      fun_prop
    have hfun :
        upperOverlapTransition Q S i =
          fun y : Vec d =>
            smoothTransitionProfile ((overlapCoordUpper S i - y i) / cubeScaleFactor S) := by
      funext y
      simp [upperOverlapTransition, hboundary]
    rw [hfun]
    exact
      (norm_fderiv_profile_comp_le smoothTransitionProfile.quantitativeProfile
          harg_diff).trans
        (mul_le_mul_of_nonneg_left
          (norm_fderiv_upperOverlapArgument_le S i x)
          smoothTransitionProfile.derivBound_nonneg)

theorem norm_fderiv_overlapTransitionFactor_le {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) (x : Vec d) :
    ‖fderiv ℝ
      (fun y : Vec d =>
        lowerOverlapTransition Q S i y * upperOverlapTransition Q S i y) x‖ ≤
      2 * smoothTransitionProfile.derivBound * (cubeScaleFactor S)⁻¹ := by
  have hl_diff :
      DifferentiableAt ℝ (lowerOverlapTransition Q S i) x :=
    (contDiff_lowerOverlapTransition Q S i).differentiable (by simp) x
  have hu_diff :
      DifferentiableAt ℝ (upperOverlapTransition Q S i) x :=
    (contDiff_upperOverlapTransition Q S i).differentiable (by simp) x
  rw [fderiv_fun_mul hl_diff hu_diff]
  have hD_nonneg : 0 ≤ smoothTransitionProfile.derivBound :=
    smoothTransitionProfile.derivBound_nonneg
  have hscale_inv_nonneg : 0 ≤ (cubeScaleFactor S)⁻¹ :=
    inv_nonneg.mpr (cubeScaleFactor_pos' S).le
  have hl_nonneg : 0 ≤ lowerOverlapTransition Q S i x :=
    lowerOverlapTransition_nonneg Q S i x
  have hu_nonneg : 0 ≤ upperOverlapTransition Q S i x :=
    upperOverlapTransition_nonneg Q S i x
  have hl_abs_le : ‖lowerOverlapTransition Q S i x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hl_nonneg]
    exact lowerOverlapTransition_le_one Q S i x
  have hu_abs_le : ‖upperOverlapTransition Q S i x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hu_nonneg]
    exact upperOverlapTransition_le_one Q S i x
  calc
    ‖lowerOverlapTransition Q S i x • fderiv ℝ (upperOverlapTransition Q S i) x +
        upperOverlapTransition Q S i x • fderiv ℝ (lowerOverlapTransition Q S i) x‖
        ≤
          ‖lowerOverlapTransition Q S i x •
              fderiv ℝ (upperOverlapTransition Q S i) x‖ +
            ‖upperOverlapTransition Q S i x •
              fderiv ℝ (lowerOverlapTransition Q S i) x‖ := norm_add_le _ _
    _ =
          ‖lowerOverlapTransition Q S i x‖ *
              ‖fderiv ℝ (upperOverlapTransition Q S i) x‖ +
            ‖upperOverlapTransition Q S i x‖ *
              ‖fderiv ℝ (lowerOverlapTransition Q S i) x‖ := by
          rw [norm_smul, norm_smul]
    _ ≤
          1 * (smoothTransitionProfile.derivBound * (cubeScaleFactor S)⁻¹) +
            1 * (smoothTransitionProfile.derivBound * (cubeScaleFactor S)⁻¹) := by
          exact add_le_add
            (mul_le_mul hl_abs_le
              (norm_fderiv_upperOverlapTransition_le Q S i x)
              (norm_nonneg _)
              (by norm_num))
            (mul_le_mul hu_abs_le
              (norm_fderiv_lowerOverlapTransition_le Q S i x)
              (norm_nonneg _)
              (by norm_num))
    _ = 2 * smoothTransitionProfile.derivBound * (cubeScaleFactor S)⁻¹ := by
          ring

theorem norm_basisVec {d : ℕ} (i : Fin d) :
    ‖basisVec i‖ = 1 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2 ?_
    intro j
    by_cases h : j = i
    · subst h
      simp [basisVec]
    · simp [basisVec, h]
  · have hi : ‖basisVec i i‖ ≤ ‖basisVec i‖ := norm_le_pi_norm (basisVec i) i
    simpa [basisVec] using hi

theorem lowerOverlapTransition_eq_one_of_add_scale_le {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hle : overlapCoordLower S i + cubeScaleFactor S ≤ x i) :
    lowerOverlapTransition Q S i x = 1 := by
  by_cases hboundary : overlapCoordLower S i ≤ cubeCoordLower Q i
  · simp [lowerOverlapTransition, hboundary]
  · have hscale : 0 < cubeScaleFactor S := cubeScaleFactor_pos' S
    have hnum : cubeScaleFactor S ≤ x i - overlapCoordLower S i := by
      linarith
    have harg :
        1 ≤ (x i - overlapCoordLower S i) / cubeScaleFactor S := by
      exact (le_div_iff₀ hscale).2 (by simpa using hnum)
    simpa [lowerOverlapTransition, hboundary] using
      smoothTransitionProfile.one_of_one_le harg

theorem upperOverlapTransition_eq_one_of_add_scale_le {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hle : x i + cubeScaleFactor S ≤ overlapCoordUpper S i) :
    upperOverlapTransition Q S i x = 1 := by
  by_cases hboundary : cubeCoordUpper Q i ≤ overlapCoordUpper S i
  · simp [upperOverlapTransition, hboundary]
  · have hscale : 0 < cubeScaleFactor S := cubeScaleFactor_pos' S
    have hnum : cubeScaleFactor S ≤ overlapCoordUpper S i - x i := by
      linarith
    have harg :
        1 ≤ (overlapCoordUpper S i - x i) / cubeScaleFactor S := by
      exact (le_div_iff₀ hscale).2 (by simpa using hnum)
    simpa [upperOverlapTransition, hboundary] using
      smoothTransitionProfile.one_of_one_le harg

theorem lowerOverlapTransition_plateauChildCube_eq_one {d : ℕ}
    {Q R : TriadicCube d} {x : Vec d} (hxR : x ∈ cubeSet R)
    (i : Fin d) :
    lowerOverlapTransition Q (plateauChildCube Q R x) i x = 1 := by
  classical
  let digits : Fin d → Fin 3 := plateauChildDigit Q R x
  let S : TriadicCube d := plateauChildCube Q R x
  have hxRi := (mem_cubeSet_iff_coord_bounds.mp hxR i)
  have hSscale : cubeScaleFactor S = cubeScaleFactor R / 3 := by
    simp [S, plateauChildCube, digits, cubeScaleFactor_childCube R digits]
  have hSlower :
      overlapCoordLower S i =
        cubeCoordLower R i +
          ((((digits i : ℤ) : ℝ) - 1) * cubeScaleFactor S) := by
    simpa [S, plateauChildCube, digits] using
      overlapCoordLower_child R digits i
  change lowerOverlapTransition Q S i x = 1
  by_cases hboundary : overlapCoordLower S i ≤ cubeCoordLower Q i
  · simp [lowerOverlapTransition, hboundary]
  · refine lowerOverlapTransition_eq_one_of_add_scale_le ?_
    by_cases hleft : x i < cubeCoordLower R i + cubeScaleFactor R / 3
    · by_cases hlower : cubeCoordLower R i = cubeCoordLower Q i
      · exfalso
        have hdigit : (((digits i : ℤ) : ℝ)) = 1 := by
          have hfin : digits i = (1 : Fin 3) := by
            have hleftQ :
                x i < cubeCoordLower Q i + cubeScaleFactor R / 3 := by
              simpa [hlower] using hleft
            simp [digits, plateauChildDigit, hleftQ, hlower]
          rw [hfin]
          norm_num
        have hface : overlapCoordLower S i = cubeCoordLower Q i := by
          rw [hSlower]
          nlinarith [hdigit, hlower]
        exact hboundary (le_of_eq hface)
      · have hdigit : (((digits i : ℤ) : ℝ)) = 0 := by
          have hfin : digits i = (0 : Fin 3) := by
            simp [digits, plateauChildDigit, hleft, hlower]
          rw [hfin]
          norm_num
        rw [hSlower]
        nlinarith [hxRi.1, hdigit]
    · by_cases hmid : x i < cubeCoordLower R i + 2 * cubeScaleFactor R / 3
      · have hleft_le :
            cubeCoordLower R i + cubeScaleFactor R / 3 ≤ x i :=
          le_of_not_gt hleft
        have hdigit : (((digits i : ℤ) : ℝ)) = 1 := by
          have hfin : digits i = (1 : Fin 3) := by
            simp [digits, plateauChildDigit, hleft, hmid]
          rw [hfin]
          norm_num
        rw [hSlower, hSscale]
        nlinarith [hleft_le, hdigit]
      · have hmid_le :
            cubeCoordLower R i + 2 * cubeScaleFactor R / 3 ≤ x i :=
          le_of_not_gt hmid
        by_cases hupper : cubeCoordUpper R i = cubeCoordUpper Q i
        · have hdigit : (((digits i : ℤ) : ℝ)) = 1 := by
            have hfin : digits i = (1 : Fin 3) := by
              simp [digits, plateauChildDigit, hleft, hmid, hupper]
            rw [hfin]
            norm_num
          rw [hSlower, hSscale]
          nlinarith [hmid_le, hdigit, cubeScaleFactor_pos' R]
        · have hdigit : (((digits i : ℤ) : ℝ)) = 2 := by
            have hfin : digits i = (2 : Fin 3) := by
              simp [digits, plateauChildDigit, hleft, hmid, hupper]
            rw [hfin]
            norm_num
          rw [hSlower, hSscale]
          nlinarith [hmid_le, hdigit]

theorem upperOverlapTransition_plateauChildCube_eq_one {d : ℕ}
    {Q R : TriadicCube d} {x : Vec d} (hxR : x ∈ cubeSet R)
    (i : Fin d) :
    upperOverlapTransition Q (plateauChildCube Q R x) i x = 1 := by
  classical
  let digits : Fin d → Fin 3 := plateauChildDigit Q R x
  let S : TriadicCube d := plateauChildCube Q R x
  have hxRi := (mem_cubeSet_iff_coord_bounds.mp hxR i)
  have hSscale : cubeScaleFactor S = cubeScaleFactor R / 3 := by
    simp [S, plateauChildCube, digits, cubeScaleFactor_childCube R digits]
  have hSupper :
      overlapCoordUpper S i =
        cubeCoordUpper R i +
          ((((digits i : ℤ) : ℝ) - 1) * cubeScaleFactor S) := by
    simpa [S, plateauChildCube, digits] using
      overlapCoordUpper_child R digits i
  have hRupper : cubeCoordUpper R i = cubeCoordLower R i + cubeScaleFactor R :=
    cubeCoordUpper_eq_lower_add_scale R i
  change upperOverlapTransition Q S i x = 1
  by_cases hboundary : cubeCoordUpper Q i ≤ overlapCoordUpper S i
  · simp [upperOverlapTransition, hboundary]
  · refine upperOverlapTransition_eq_one_of_add_scale_le ?_
    by_cases hleft : x i < cubeCoordLower R i + cubeScaleFactor R / 3
    · by_cases hlower : cubeCoordLower R i = cubeCoordLower Q i
      · have hdigit : (((digits i : ℤ) : ℝ)) = 1 := by
          have hfin : digits i = (1 : Fin 3) := by
            have hleftQ :
                x i < cubeCoordLower Q i + cubeScaleFactor R / 3 := by
              simpa [hlower] using hleft
            simp [digits, plateauChildDigit, hleftQ, hlower]
          rw [hfin]
          norm_num
        rw [hSupper, hSscale]
        nlinarith [hleft, hRupper, hdigit, cubeScaleFactor_pos' R]
      · have hdigit : (((digits i : ℤ) : ℝ)) = 0 := by
          have hfin : digits i = (0 : Fin 3) := by
            simp [digits, plateauChildDigit, hleft, hlower]
          rw [hfin]
          norm_num
        rw [hSupper, hSscale]
        nlinarith [hleft, hRupper, hdigit]
    · by_cases hmid : x i < cubeCoordLower R i + 2 * cubeScaleFactor R / 3
      · have hdigit : (((digits i : ℤ) : ℝ)) = 1 := by
          have hfin : digits i = (1 : Fin 3) := by
            simp [digits, plateauChildDigit, hleft, hmid]
          rw [hfin]
          norm_num
        rw [hSupper, hSscale]
        nlinarith [hmid, hRupper, hdigit, cubeScaleFactor_pos' R]
      · by_cases hupper : cubeCoordUpper R i = cubeCoordUpper Q i
        · exfalso
          have hdigit : (((digits i : ℤ) : ℝ)) = 1 := by
            have hfin : digits i = (1 : Fin 3) := by
              simp [digits, plateauChildDigit, hleft, hmid, hupper]
            rw [hfin]
            norm_num
          have hface : overlapCoordUpper S i = cubeCoordUpper Q i := by
            rw [hSupper]
            nlinarith [hdigit, hupper]
          exact hboundary (le_of_eq hface.symm)
        · have hdigit : (((digits i : ℤ) : ℝ)) = 2 := by
            have hfin : digits i = (2 : Fin 3) := by
              simp [digits, plateauChildDigit, hleft, hmid, hupper]
            rw [hfin]
            norm_num
          rw [hSupper]
          nlinarith [hxRi.2, hdigit]

theorem lowerOverlapTransition_ne_zero_coord_lt {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q)
    (hne : lowerOverlapTransition Q S i x ≠ 0) :
    overlapCoordLower S i < x i := by
  by_cases hboundary : overlapCoordLower S i ≤ cubeCoordLower Q i
  · have hx := (mem_openCubeSet_iff_coord_bounds.mp hxQ i).1
    exact lt_of_le_of_lt hboundary hx
  · have hne' :
        smoothTransitionProfile ((x i - overlapCoordLower S i) / cubeScaleFactor S) ≠ 0 := by
      simpa [lowerOverlapTransition, hboundary] using hne
    have harg_pos :
        0 < (x i - overlapCoordLower S i) / cubeScaleFactor S := by
      by_contra hnot
      have hnonpos : (x i - overlapCoordLower S i) / cubeScaleFactor S ≤ 0 :=
        not_lt.mp hnot
      exact hne' (smoothTransitionProfile.zero_of_nonpos hnonpos)
    have hscale : 0 < cubeScaleFactor S := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) S.scale)
    have hmul :
        0 < x i - overlapCoordLower S i := by
      rwa [div_pos_iff_of_pos_right hscale] at harg_pos
    linarith

theorem upperOverlapTransition_ne_zero_coord_lt {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q)
    (hne : upperOverlapTransition Q S i x ≠ 0) :
    x i < overlapCoordUpper S i := by
  by_cases hboundary : cubeCoordUpper Q i ≤ overlapCoordUpper S i
  · have hx := (mem_openCubeSet_iff_coord_bounds.mp hxQ i).2
    exact lt_of_lt_of_le hx hboundary
  · have hne' :
        smoothTransitionProfile ((overlapCoordUpper S i - x i) / cubeScaleFactor S) ≠ 0 := by
      simpa [upperOverlapTransition, hboundary] using hne
    have harg_pos :
        0 < (overlapCoordUpper S i - x i) / cubeScaleFactor S := by
      by_contra hnot
      have hnonpos : (overlapCoordUpper S i - x i) / cubeScaleFactor S ≤ 0 :=
        not_lt.mp hnot
      exact hne' (smoothTransitionProfile.zero_of_nonpos hnonpos)
    have hscale : 0 < cubeScaleFactor S := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) S.scale)
    have hmul :
        0 < overlapCoordUpper S i - x i := by
      rwa [div_pos_iff_of_pos_right hscale] at harg_pos
    linarith


end

end Homogenization
