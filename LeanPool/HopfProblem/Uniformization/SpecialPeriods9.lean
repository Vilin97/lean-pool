/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyLattice
import all LeanPool.HopfProblem.Foundations.TriangleRegularBaseFundamentalGroup
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen1
import all LeanPool.HopfProblem.Foundations.TwoOpenTransition
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods8
import all LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyLattice

/-!
# Hopf problem: uniformization · special periods 9

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private def SpecialPeriods.Triangle.outerCircleValue (R t : ℝ) : ℂ :=
  circleMap (1 / 2 : ℂ) R (-Real.pi / 2 + 2 * Real.pi * t)

@[fun_prop]
private theorem SpecialPeriods.Triangle.continuous_outerCircleValue (R : ℝ) :
    Continuous (outerCircleValue R) := by
  unfold outerCircleValue circleMap
  fun_prop

@[simp]
private theorem SpecialPeriods.Triangle.outerCircleValue_zero (R : ℝ) :
    outerCircleValue R 0 = (1 / 2 : ℂ) - (R : ℂ) * Complex.I := by
  simpa only [outerCircleValue, MulZeroClass.mul_zero, add_zero] using
    circleMap_neg_pi_div_two (1 / 2 : ℂ) R

@[simp]
private theorem SpecialPeriods.Triangle.outerCircleValue_one (R : ℝ) :
    outerCircleValue R 1 = (1 / 2 : ℂ) - (R : ℂ) * Complex.I := by
  unfold outerCircleValue
  rw [mul_one, periodic_circleMap (1 / 2 : ℂ) R (-Real.pi / 2)]
  exact circleMap_neg_pi_div_two (1 / 2 : ℂ) R

private theorem
    SpecialPeriods.Triangle.outerCircleValue_norm_sub_center (R : ℝ) (hR : 2 ≤ R) (t : ℝ) :
    ‖outerCircleValue R t - (1 / 2 : ℂ)‖ = R := by
  simp only [outerCircleValue, circleMap_sub_center, norm_circleMap_zero]
  exact abs_of_nonneg (by linarith)

private theorem
    SpecialPeriods.Triangle.outerCircleValue_avoids_punctures (R : ℝ) (hR : 2 ≤ R) (t : ℝ) :
    outerCircleValue R t ≠ 0 ∧ outerCircleValue R t ≠ 1 := by
  have hn := outerCircleValue_norm_sub_center R hR t
  constructor
  · intro h
    rw [h] at hn
    norm_num [norm_div] at hn
    linarith
  · intro h
    rw [h, show (1 : ℂ) - 1 / 2 = 1 / 2 by ring] at hn
    norm_num [norm_div] at hn
    linarith

private def
    SpecialPeriods.Triangle.outerCircleBasepoint (R : ℝ) (hR : 2 ≤ R) : TwicePuncturedPlane :=
  ⟨(1 / 2 : ℂ) - (R : ℂ) * Complex.I,
    by
    rw [← outerCircleValue_zero R]
    exact outerCircleValue_avoids_punctures R hR 0⟩

private def SpecialPeriods.Triangle.outerPositiveCircle (R : ℝ) (hR : 2 ≤ R) :
    Path (outerCircleBasepoint R hR) (outerCircleBasepoint R hR)
    where
  toFun t := ⟨outerCircleValue R t, outerCircleValue_avoids_punctures R hR t⟩
  continuous_toFun := ((continuous_outerCircleValue R).comp continuous_subtype_val).subtype_mk _
  source' := Subtype.ext (outerCircleValue_zero R)
  target' := Subtype.ext (outerCircleValue_one R)

@[simp]
private theorem
    SpecialPeriods.Triangle.outerPositiveCircle_coe (R : ℝ) (hR : 2 ≤ R) (t : unitInterval) :
    (outerPositiveCircle R hR t : ℂ) =
      circleMap (1 / 2 : ℂ) R (-Real.pi / 2 + 2 * Real.pi * (t : ℝ)) :=
  rfl

private theorem SpecialPeriods.Triangle.outerPositiveCircle_norm_sub_center (R : ℝ) (hR : 2 ≤ R)
    (t : unitInterval) : ‖(outerPositiveCircle R hR t : ℂ) - (1 / 2 : ℂ)‖ = R :=
  outerCircleValue_norm_sub_center R hR t

private def SpecialPeriods.Triangle.outerTailValue (R t : ℝ) : ℂ :=
  (1 / 2 : ℂ) - ((R * t : ℝ) : ℂ) * Complex.I

@[simp]
private theorem
    SpecialPeriods.Triangle.outerTailValue_re (R t : ℝ) : (outerTailValue R t).re = 1 / 2 := by
  simp [outerTailValue, Complex.mul_re]

private theorem SpecialPeriods.Triangle.outerTailValue_mem_slitPlanes (R t : ℝ) :
    outerTailValue R t ∈ upperSlitPlane ∩ lowerSlitPlane := by
  have hx : (outerTailValue R t).re ≠ 0 ∧ (outerTailValue R t).re ≠ 1 := by
    rw [outerTailValue_re]
    norm_num
  exact ⟨Or.inr hx, Or.inr hx⟩

private def SpecialPeriods.Triangle.outerMeridianTail (R : ℝ) (hR : 2 ≤ R) :
    Path meridianBasepoint (outerCircleBasepoint R hR)
    where
  toFun
    t :=
    ⟨outerTailValue R t, upperSlitPlane_subset_punctured (outerTailValue_mem_slitPlanes R t).1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold outerTailValue
    fun_prop
  source' := Subtype.ext (by simp [outerTailValue, meridianBasepoint])
  target' := Subtype.ext (by simp [outerTailValue, outerCircleBasepoint])

private theorem SpecialPeriods.Triangle.outerMeridianTail_mem_lowerSlitPlane (R : ℝ) (hR : 2 ≤ R)
    (t : unitInterval) : (outerMeridianTail R hR t : ℂ) ∈ lowerSlitPlane :=
  (outerTailValue_mem_slitPlanes R t).2

private def SpecialPeriods.Triangle.outerQuarter : unitInterval :=
  ⟨1 / 4, by norm_num⟩

private def SpecialPeriods.Triangle.outerThreeQuarters : unitInterval :=
  ⟨3 / 4, by norm_num⟩

private theorem SpecialPeriods.Triangle.outerCircleValue_quarter (R : ℝ) :
    outerCircleValue R (1 / 4) = (1 / 2 : ℂ) + (R : ℂ) := by
  unfold outerCircleValue
  rw [show -Real.pi / 2 + 2 * Real.pi * (1 / 4) = 0 by ring]
  simp [circleMap]

private theorem SpecialPeriods.Triangle.outerCircleValue_threeQuarters (R : ℝ) :
    outerCircleValue R (3 / 4) = (1 / 2 : ℂ) - (R : ℂ) := by
  unfold outerCircleValue
  rw [show -Real.pi / 2 + 2 * Real.pi * (3 / 4) = Real.pi by ring]
  simp [circleMap, Complex.exp_pi_mul_I, sub_eq_add_neg]

private theorem SpecialPeriods.Triangle.outerCircleValue_im (R t : ℝ) :
    (outerCircleValue R t).im = R * Real.sin (-Real.pi / 2 + 2 * Real.pi * t) := by
  simpa [outerCircleValue, circleMap] using circleMap_zero_im R (-Real.pi / 2 + 2 * Real.pi * t)

private theorem
    SpecialPeriods.Triangle.outerCircleValue_mem_lowerSlitPlane (R : ℝ) (hR : 2 ≤ R) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht : t ≤ 1 / 4 ∨ 3 / 4 ≤ t) :
    outerCircleValue R t ∈ lowerSlitPlane := by
  by_cases hquarter : t = 1 / 4
  · rw [hquarter, outerCircleValue_quarter]
    norm_num [lowerSlitPlane]
    constructor <;> linarith
  by_cases hthree : t = 3 / 4
  · rw [hthree, outerCircleValue_threeQuarters]
    norm_num [lowerSlitPlane]
    constructor <;> linarith
  apply Or.inl
  rw [outerCircleValue_im]
  have hRpos : 0 < R := by linarith
  apply mul_neg_of_pos_of_neg hRpos
  rcases ht with ht | ht
  · have htlt : t < 1 / 4 := lt_of_le_of_ne ht hquarter
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  · have htlt : 3 / 4 < t := lt_of_le_of_ne ht (Ne.symm hthree)
    have hsin : 0 < Real.sin ((-Real.pi / 2 + 2 * Real.pi * t) - Real.pi) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    rw [Real.sin_sub_pi] at hsin
    linarith

private theorem
    SpecialPeriods.Triangle.outerCircleValue_mem_upperSlitPlane (R : ℝ) (hR : 2 ≤ R) (t : ℝ)
    (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 3 / 4) : outerCircleValue R t ∈ upperSlitPlane := by
  by_cases hquarter : t = 1 / 4
  · rw [hquarter, outerCircleValue_quarter]
    norm_num [upperSlitPlane]
    constructor <;> linarith
  by_cases hthree : t = 3 / 4
  · rw [hthree, outerCircleValue_threeQuarters]
    norm_num [upperSlitPlane]
    constructor <;> linarith
  apply Or.inl
  rw [outerCircleValue_im]
  have hRpos : 0 < R := by linarith
  apply mul_pos hRpos
  have ht0lt : 1 / 4 < t := lt_of_le_of_ne ht0 (Ne.symm hquarter)
  have ht1lt : t < 3 / 4 := lt_of_le_of_ne ht1 hthree
  apply Real.sin_pos_of_pos_of_lt_pi
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

private theorem SpecialPeriods.Triangle.outerPositiveCircle_quarter (R : ℝ) (hR : 2 ≤ R) :
    (outerPositiveCircle R hR outerQuarter : ℂ) = (1 / 2 : ℂ) + (R : ℂ) :=
  outerCircleValue_quarter R

private theorem SpecialPeriods.Triangle.outerPositiveCircle_threeQuarters (R : ℝ) (hR : 2 ≤ R) :
    (outerPositiveCircle R hR outerThreeQuarters : ℂ) = (1 / 2 : ℂ) - (R : ℂ) :=
  outerCircleValue_threeQuarters R

private theorem SpecialPeriods.Triangle.outerPositiveCircle_mem_lowerSlitPlane (R : ℝ) (hR : 2 ≤ R)
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ (t : ℝ)) :
    (outerPositiveCircle R hR t : ℂ) ∈ lowerSlitPlane :=
  outerCircleValue_mem_lowerSlitPlane R hR t t.property.1 t.property.2 ht

private theorem SpecialPeriods.Triangle.outerPositiveCircle_mem_upperSlitPlane (R : ℝ) (hR : 2 ≤ R)
    (t : unitInterval) (ht0 : 1 / 4 ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ 3 / 4) :
    (outerPositiveCircle R hR t : ℂ) ∈ upperSlitPlane :=
  outerCircleValue_mem_upperSlitPlane R hR t ht0 ht1

private theorem SpecialPeriods.Triangle.outerPositiveCircle_quarter_re_gt_one (R : ℝ) (hR : 2 ≤ R) :
    1 < (outerPositiveCircle R hR outerQuarter : ℂ).re := by
  rw [outerPositiveCircle_quarter]
  norm_num
  linarith

private theorem SpecialPeriods.Triangle.outerPositiveCircle_threeQuarters_re_lt_zero (R : ℝ)
    (hR : 2 ≤ R) : (outerPositiveCircle R hR outerThreeQuarters : ℂ).re < 0 := by
  rw [outerPositiveCircle_threeQuarters]
  norm_num
  linarith

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem
    SpecialPeriods.Triangle.meridianFreeWordHom_lower_upper_lower {c d : TwicePuncturedPlane}
    (hc : c ∈ (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V)
    (hd : d ∈ (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V)
    (α : Path meridianBasepoint c) (β : Path c d) (γ : Path d meridianBasepoint)
    (hα : ∀ s, α s ∈ freeGroupCover.V) (hβ : ∀ s, β s ∈ freeGroupCover.U)
    (hγ : ∀ s, γ s ∈ freeGroupCover.V) :
    meridianFreeWordHom (.mk (α.trans (β.trans γ))) =
      (freeGroupTransition d)⁻¹ * freeGroupTransition c := by
  have hm :
    freeGroupCover.isCoveringMap.monodromy (.mk (α.trans (β.trans γ)))
        (freeGroupCover.fiberPointU meridianBasepoint 1) =
      freeGroupCover.fiberPointU meridianBasepoint
        ((freeGroupTransition c)⁻¹ * freeGroupTransition d) := by
    rw [Path.Homotopic.Quotient.mk_trans, freeGroupCover.isCoveringMap.monodromy_trans_apply,
      freeGroupCover.fiberPointU_eq_fiberPointV meridianBasepoint 1 freeGroupCover_basepoint_mem,
      freeGroupCover.monodromy_of_path_V α hα, freeGroupCover.fiberPointV_eq_fiberPointU c _ hc,
      Path.Homotopic.Quotient.mk_trans, freeGroupCover.isCoveringMap.monodromy_trans_apply,
      freeGroupCover.monodromy_of_path_U β hβ, freeGroupCover.fiberPointU_eq_fiberPointV d _ hd,
      freeGroupCover.monodromy_of_path_V γ hγ,
      freeGroupCover.fiberPointV_eq_fiberPointU meridianBasepoint _ freeGroupCover_basepoint_mem]
    simp only [freeGroupCover_transition, freeGroupTransition_basepoint, one_mul, inv_one,
      mul_one]
  have hop :
    freeGroupCover.fundamentalGroupToMulOpposite meridianBasepoint freeGroupCover_basepoint_mem.1
        (.mk (α.trans (β.trans γ))) =
      MulOpposite.op ((freeGroupTransition c)⁻¹ * freeGroupTransition d) := by
    apply (freeGroupCover.isQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
    have hm' := congrArg Subtype.val hm
    simpa only [MulOpposite.unop_op, TwoOpenTransition.basepointU_eq_fiberPointU,
      TwoOpenTransition.fiberPointU_val, TwoOpenTransition.smul_pointU, mul_one] using hm'.symm
  change
    (MulEquiv.inv' (FreeGroup Bool)).symm
        (freeGroupCover.fundamentalGroupToMulOpposite meridianBasepoint
          freeGroupCover_basepoint_mem.1 (.mk (α.trans (β.trans γ)))) =
      _
  rw [hop]
  change ((freeGroupTransition c)⁻¹ * freeGroupTransition d)⁻¹ = _
  simp only [mul_inv_rev, inv_inv]

private theorem SpecialPeriods.Triangle.three_subpaths_homotopic_mo1973_26253 {X : Type*}
    [TopologicalSpace X] {x : X} (C : Path x x) (a c : unitInterval) :
    (((C.subpath 0 a).trans ((C.subpath a c).trans (C.subpath c 1))).cast C.source.symm
          C.target.symm).Homotopic
      C := by
  have h :
    ((C.subpath 0 a).trans ((C.subpath a c).trans (C.subpath c 1))).Homotopic (C.subpath 0 1) :=
    ((Path.Homotopic.refl _).hcomp ⟨Path.Homotopy.subpathTransSubpath C a c 1⟩).trans
      ⟨Path.Homotopy.subpathTransSubpath C 0 a 1⟩
  have hcast : (C.cast C.source C.target).cast C.source.symm C.target.symm = C := by
    ext s
    rfl
  simpa only [Path.subpath_zero_one, hcast] using h.pathCast C.source.symm C.target.symm

public
theorem SpecialPeriods.Triangle.basedLoop_subpaths_mo1973_26254 {X : Type*}
    [TopologicalSpace X] {x b : X} (τ : Path b x) (C : Path x x) (a c : unitInterval) :
    Path.Homotopic.Quotient.mk ((τ.trans C).trans τ.symm) =
      Path.Homotopic.Quotient.mk
        ((τ.trans ((C.subpath 0 a).cast C.source.symm rfl)).trans
          ((C.subpath a c).trans (((C.subpath c 1).cast rfl C.target.symm).trans τ.symm))) := by
  have h :
    Path.Homotopic.Quotient.mk C =
      Path.Homotopic.Quotient.mk
        (((C.subpath 0 a).cast C.source.symm rfl).trans
          ((C.subpath a c).trans ((C.subpath c 1).cast rfl C.target.symm))) := by
    apply Path.Homotopic.Quotient.eq.mpr
    exact (three_subpaths_homotopic_mo1973_26253 C a c).symm
  simp only [Path.Homotopic.Quotient.mk_trans]
  rw [h]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]

private def SpecialPeriods.Triangle.positiveOuterMeridian (R : ℝ) (hR : 2 ≤ R) :
    Path meridianBasepoint meridianBasepoint :=
  ((outerMeridianTail R hR).trans (outerPositiveCircle R hR)).trans (outerMeridianTail R hR).symm

private theorem
    SpecialPeriods.Triangle.positiveOuterMeridian_eq_tail_circle_tail (R : ℝ) (hR : 2 ≤ R) :
    positiveOuterMeridian R hR =
      ((outerMeridianTail R hR).trans (outerPositiveCircle R hR)).trans
        (outerMeridianTail R hR).symm :=
  rfl

private def SpecialPeriods.Triangle.outerLowerStart (R : ℝ) (hR : 2 ≤ R) :
    Path meridianBasepoint (outerPositiveCircle R hR outerQuarter) :=
  (outerMeridianTail R hR).trans
    (((outerPositiveCircle R hR).subpath 0 outerQuarter).cast
      (outerPositiveCircle R hR).source.symm rfl)

private def SpecialPeriods.Triangle.outerUpperCross (R : ℝ) (hR : 2 ≤ R) :
    Path (outerPositiveCircle R hR outerQuarter) (outerPositiveCircle R hR outerThreeQuarters) :=
  (outerPositiveCircle R hR).subpath outerQuarter outerThreeQuarters

private def SpecialPeriods.Triangle.outerLowerFinish (R : ℝ) (hR : 2 ≤ R) :
    Path (outerPositiveCircle R hR outerThreeQuarters) meridianBasepoint :=
  (((outerPositiveCircle R hR).subpath outerThreeQuarters 1).cast rfl
        (outerPositiveCircle R hR).target.symm).trans
    (outerMeridianTail R hR).symm

private theorem SpecialPeriods.Triangle.positiveOuterMeridian_subdivision (R : ℝ) (hR : 2 ≤ R) :
    Path.Homotopic.Quotient.mk (positiveOuterMeridian R hR) =
      Path.Homotopic.Quotient.mk
        ((outerLowerStart R hR).trans ((outerUpperCross R hR).trans (outerLowerFinish R hR))) :=
  basedLoop_subpaths_mo1973_26254 (outerMeridianTail R hR) (outerPositiveCircle R hR) outerQuarter
    outerThreeQuarters

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem SpecialPeriods.Triangle.outerLowerStart_mem_lower (R : ℝ) (hR : 2 ≤ R)
    (t : unitInterval) : outerLowerStart R hR t ∈ freeGroupCover.V := by
  apply SimplyConnectedCover.trans_mem
  · exact outerMeridianTail_mem_lowerSlitPlane R hR
  · intro s
    change (outerPositiveCircle R hR).subpath 0 outerQuarter s ∈ freeGroupCover.V
    apply
      FundamentalGroupVanKampen.subpath_mem_of_mem_Icc (outerPositiveCircle R hR)
        (show (0 : unitInterval) ≤ outerQuarter from bot_le) _ s
    intro u hu
    exact outerPositiveCircle_mem_lowerSlitPlane R hR u (Or.inl hu.2)

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem SpecialPeriods.Triangle.outerUpperCross_mem_upper (R : ℝ) (hR : 2 ≤ R)
    (t : unitInterval) : outerUpperCross R hR t ∈ freeGroupCover.U := by
  apply
    FundamentalGroupVanKampen.subpath_mem_of_mem_Icc (outerPositiveCircle R hR)
      (show outerQuarter ≤ outerThreeQuarters by norm_num [outerQuarter, outerThreeQuarters]) _ t
  intro u hu
  exact outerPositiveCircle_mem_upperSlitPlane R hR u hu.1 hu.2

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem SpecialPeriods.Triangle.outerLowerFinish_mem_lower (R : ℝ) (hR : 2 ≤ R)
    (t : unitInterval) : outerLowerFinish R hR t ∈ freeGroupCover.V := by
  apply SimplyConnectedCover.trans_mem
  · intro s
    change (outerPositiveCircle R hR).subpath outerThreeQuarters 1 s ∈ freeGroupCover.V
    apply
      FundamentalGroupVanKampen.subpath_mem_of_mem_Icc (outerPositiveCircle R hR)
        (show outerThreeQuarters ≤ (1 : unitInterval) from le_top) _ s
    intro u hu
    exact outerPositiveCircle_mem_lowerSlitPlane R hR u (Or.inr hu.1)
  · exact fun s => outerMeridianTail_mem_lowerSlitPlane R hR (unitInterval.symm s)

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem SpecialPeriods.Triangle.outerQuarter_mem_overlap (R : ℝ) (hR : 2 ≤ R) :
    outerPositiveCircle R hR outerQuarter ∈
      (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V := by
  change (outerPositiveCircle R hR outerQuarter : ℂ) ∈ upperSlitPlane ∩ lowerSlitPlane
  rw [slitPlanes_inter]
  have h := outerPositiveCircle_quarter_re_gt_one R hR
  exact ⟨ne_of_gt (lt_trans zero_lt_one h), ne_of_gt h⟩

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem SpecialPeriods.Triangle.outerThreeQuarters_mem_overlap (R : ℝ) (hR : 2 ≤ R) :
    outerPositiveCircle R hR outerThreeQuarters ∈
      (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V := by
  change (outerPositiveCircle R hR outerThreeQuarters : ℂ) ∈ upperSlitPlane ∩ lowerSlitPlane
  rw [slitPlanes_inter]
  have h := outerPositiveCircle_threeQuarters_re_lt_zero R hR
  exact ⟨ne_of_lt h, ne_of_lt (lt_trans h zero_lt_one)⟩

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
@[simp]
private theorem SpecialPeriods.Triangle.freeGroupTransition_outerQuarter (R : ℝ) (hR : 2 ≤ R) :
    freeGroupTransition (outerPositiveCircle R hR outerQuarter) = FreeGroup.of Bool.true := by
  have h := outerPositiveCircle_quarter_re_gt_one R hR
  have hzero : ¬(outerPositiveCircle R hR outerQuarter : ℂ).re < 0 := by linarith
  have hone : ¬(outerPositiveCircle R hR outerQuarter : ℂ).re < 1 := not_lt.mpr h.le
  simp only [freeGroupTransition, ite_eq_right hzero, ite_eq_right hone]

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
@[simp]
private theorem
    SpecialPeriods.Triangle.freeGroupTransition_outerThreeQuarters (R : ℝ) (hR : 2 ≤ R) :
    freeGroupTransition (outerPositiveCircle R hR outerThreeQuarters) =
      (FreeGroup.of Bool.false)⁻¹ := by
  simp only [freeGroupTransition, ite_eq_left (outerPositiveCircle_threeQuarters_re_lt_zero R hR)]

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem
    SpecialPeriods.Triangle.meridianFreeWordHom_positiveOuterMeridian (R : ℝ) (hR : 2 ≤ R) :
    meridianFreeWordHom (.mk (positiveOuterMeridian R hR)) =
      FreeGroup.of Bool.false * FreeGroup.of Bool.true := by
  rw [positiveOuterMeridian_subdivision]
  rw [meridianFreeWordHom_lower_upper_lower (outerQuarter_mem_overlap R hR)
      (outerThreeQuarters_mem_overlap R hR) (outerLowerStart R hR) (outerUpperCross R hR)
      (outerLowerFinish R hR) (outerLowerStart_mem_lower R hR) (outerUpperCross_mem_upper R hR)
      (outerLowerFinish_mem_lower R hR)]
  rw [freeGroupTransition_outerThreeQuarters, freeGroupTransition_outerQuarter, inv_inv]

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem SpecialPeriods.Triangle.positiveOuterMeridian_class_eq (R : ℝ) (hR : 2 ≤ R) :
    (.mk (positiveOuterMeridian R hR) : FundamentalGroup TwicePuncturedPlane meridianBasepoint) =
      meridianClass Bool.false * meridianClass Bool.true := by
  apply twicePuncturedFundamentalGroupFreeEquiv.injective
  change
    meridianFreeWordHom (.mk (positiveOuterMeridian R hR)) =
      meridianFreeWordHom (meridianClass Bool.false * meridianClass Bool.true)
  rw [meridianFreeWordHom_positiveOuterMeridian, map_mul, meridianFreeWordHom_meridianClass,
    meridianFreeWordHom_meridianClass]

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem SpecialPeriods.Triangle.outerPositiveCircle_norm_lower_bound (R : ℝ) (hR : 2 ≤ R)
    (t : unitInterval) : R - 1 / 2 ≤ ‖(outerPositiveCircle R hR t : ℂ)‖ := by
  have h := norm_sub_le (outerPositiveCircle R hR t : ℂ) (1 / 2 : ℂ)
  rw [outerPositiveCircle_norm_sub_center] at h
  norm_num [norm_div] at h
  change R - 1 / 2 ≤ ‖circleMap (1 / 2 : ℂ) R (-Real.pi / 2 + 2 * Real.pi * (t : ℝ))‖
  linarith

end Mathoverflow1973

end
