/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Foundations.TriangleRegularBaseFundamentalGroup
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Foundations.TwoOpenTransition
import all LeanPool.HopfProblem.Elliptic.Core5

/-!
# Hopf problem: uniformization · special periods 8

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

private def SpecialPeriods.Triangle.twicePuncturedPlaneDomain : TopologicalSpace.Opens ℂ :=
  ⟨{z | z ≠ 0 ∧ z ≠ 1}, isOpen_ne.inter isOpen_ne⟩

private abbrev SpecialPeriods.Triangle.TwicePuncturedPlane : Type :=
  twicePuncturedPlaneDomain

@[simp]
private theorem SpecialPeriods.Triangle.mem_twicePuncturedPlaneDomain (z : ℂ) :
    z ∈ twicePuncturedPlaneDomain ↔ z ≠ 0 ∧ z ≠ 1 :=
  Iff.rfl

private theorem SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph_regular_iff
    (q : SpecialPeriods.TriangleOrbitSpace) :
    q ∈ SpecialPeriods.triangleOrbitRegularDomain ↔
      trianglePlaneUniformizationHomeomorph q ∈ twicePuncturedPlaneDomain := by
  rw [SpecialPeriods.triangleOrbitRegularDomain_mem_iff, mem_twicePuncturedPlaneDomain, ←
    trianglePlaneUniformizationHomeomorph_centerOne, ←
    trianglePlaneUniformizationHomeomorph_centerTwo]
  simp only [ne_eq, trianglePlaneUniformizationHomeomorph.injective.eq_iff]

private def SpecialPeriods.Triangle.triangleRegularDomainPlaneHomeomorph :
    SpecialPeriods.triangleOrbitRegularDomain ≃ₜ TwicePuncturedPlane :=
  trianglePlaneUniformizationHomeomorph.subtype trianglePlaneUniformizationHomeomorph_regular_iff

private def SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph :
    SpecialPeriods.TriangleRegularQuotient ≃ₜ TwicePuncturedPlane :=
  SpecialPeriods.triangleRegularOrbitHomeomorph.trans triangleRegularDomainPlaneHomeomorph

@[simp]
private theorem SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph_project
    (z : SpecialPeriods.TriangleRegularPoint) :
    (triangleRegularPlaneHomeomorph (SpecialPeriods.triangleRegularProject z) : ℂ) =
      trianglePlaneUniformizationHomeomorph (SpecialPeriods.triangleOrbitProjection z.val) :=
  rfl

private def SpecialPeriods.Triangle.upperSlitPlane : Set ℂ :=
  {z | 0 < z.im ∨ (z.re ≠ 0 ∧ z.re ≠ 1)}

private def SpecialPeriods.Triangle.lowerSlitPlane : Set ℂ :=
  {z | z.im < 0 ∨ (z.re ≠ 0 ∧ z.re ≠ 1)}

private theorem SpecialPeriods.Triangle.upperSlitPlane_isOpen : IsOpen upperSlitPlane :=
  (isOpen_lt continuous_const Complex.continuous_im).union
    ((isOpen_ne_fun Complex.continuous_re continuous_const).inter
      (isOpen_ne_fun Complex.continuous_re continuous_const))

private theorem SpecialPeriods.Triangle.lowerSlitPlane_isOpen : IsOpen lowerSlitPlane :=
  (isOpen_lt Complex.continuous_im continuous_const).union
    ((isOpen_ne_fun Complex.continuous_re continuous_const).inter
      (isOpen_ne_fun Complex.continuous_re continuous_const))

private theorem SpecialPeriods.Triangle.upperSlitPlane_subset_punctured :
    upperSlitPlane ⊆ {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  intro z hz
  constructor
  · rintro rfl
    simp [upperSlitPlane] at hz
  · rintro rfl
    simp [upperSlitPlane] at hz

private theorem SpecialPeriods.Triangle.lowerSlitPlane_subset_punctured :
    lowerSlitPlane ⊆ {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  intro z hz
  constructor
  · rintro rfl
    simp [lowerSlitPlane] at hz
  · rintro rfl
    simp [lowerSlitPlane] at hz

private theorem SpecialPeriods.Triangle.slitPlanes_union :
    upperSlitPlane ∪ lowerSlitPlane = {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact upperSlitPlane_subset_punctured hz
    · exact lowerSlitPlane_subset_punctured hz
  · rintro ⟨hzero, hone⟩
    by_cases hp : 0 < z.im
    · exact Or.inl (Or.inl hp)
    by_cases hn : z.im < 0
    · exact Or.inr (Or.inl hn)
    have hi : z.im = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
    apply Or.inl
    apply Or.inr
    constructor
    · intro hr
      apply hzero
      apply Complex.ext <;> simp_all
    · intro hr
      apply hone
      apply Complex.ext <;> simp_all

private theorem SpecialPeriods.Triangle.slitPlanes_inter :
    upperSlitPlane ∩ lowerSlitPlane = {z : ℂ | z.re ≠ 0 ∧ z.re ≠ 1} := by
  ext z
  constructor
  · rintro ⟨hp | hx, hn | hx'⟩
    · linarith
    · exact hx'
    · exact hx
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, Or.inr hx⟩

private def SpecialPeriods.Triangle.meridianHalfCircle (t : ℝ) : ℂ :=
  circleMap 0 (1 / 2) (Real.pi * t)

@[fun_prop]
private theorem
    SpecialPeriods.Triangle.continuous_meridianHalfCircle : Continuous meridianHalfCircle := by
  unfold meridianHalfCircle circleMap
  fun_prop

@[simp]
private theorem
    SpecialPeriods.Triangle.meridianHalfCircle_zero : meridianHalfCircle 0 = (1 / 2 : ℂ) := by
  simp [meridianHalfCircle, circleMap]

@[simp]
private theorem
    SpecialPeriods.Triangle.meridianHalfCircle_one : meridianHalfCircle 1 = (-1 / 2 : ℂ) := by
  simp [meridianHalfCircle, circleMap, Complex.exp_pi_mul_I]
  ring

private theorem
    SpecialPeriods.Triangle.meridianHalfCircle_im_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < (meridianHalfCircle t).im := by
  rw [meridianHalfCircle, circleMap_zero_im]
  apply mul_pos (by norm_num)
  exact Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht0) (by nlinarith [Real.pi_pos])

private theorem SpecialPeriods.Triangle.meridianHalfCircle_mem_upperSlitPlane (t : unitInterval) :
    meridianHalfCircle t ∈ upperSlitPlane := by
  by_cases ht0 : (t : ℝ) = 0
  · rw [ht0, meridianHalfCircle_zero]
    norm_num [upperSlitPlane]
  by_cases ht1 : (t : ℝ) = 1
  · rw [ht1, meridianHalfCircle_one]
    norm_num [upperSlitPlane]
  apply Or.inl
  apply meridianHalfCircle_im_pos
  · have := t.property.1
    exact lt_of_le_of_ne this (Ne.symm ht0)
  · have := t.property.2
    exact lt_of_le_of_ne this ht1

private theorem SpecialPeriods.Triangle.conj_mem_lowerSlitPlane_iff_mo1973_23420 (z : ℂ) :
    conj z ∈ lowerSlitPlane ↔ z ∈ upperSlitPlane := by simp [lowerSlitPlane, upperSlitPlane]

private theorem SpecialPeriods.Triangle.one_sub_mem_upperSlitPlane_iff_mo1973_23421 (z : ℂ) :
    1 - z ∈ upperSlitPlane ↔ z ∈ lowerSlitPlane := by
  simp [upperSlitPlane, lowerSlitPlane, ne_comm, and_comm, eq_sub_iff_add_eq]

private theorem SpecialPeriods.Triangle.one_sub_mem_lowerSlitPlane_iff_mo1973_23422 (z : ℂ) :
    1 - z ∈ lowerSlitPlane ↔ z ∈ upperSlitPlane := by
  simp [upperSlitPlane, lowerSlitPlane, ne_comm, and_comm, eq_sub_iff_add_eq]

private def SpecialPeriods.Triangle.upperZeroArc : Path (1 / 2 : ℂ) (-1 / 2) :=
  Path.ofLine continuous_meridianHalfCircle.continuousOn meridianHalfCircle_zero
    meridianHalfCircle_one

private def SpecialPeriods.Triangle.lowerZeroArc : Path (1 / 2 : ℂ) (-1 / 2) :=
  Path.ofLine (f := fun t : ℝ => conj (meridianHalfCircle t)) (by fun_prop) (by simp [map_ofNat])
    (by simp [map_ofNat])

private def SpecialPeriods.Triangle.upperOneArc : Path (1 / 2 : ℂ) (3 / 2) :=
  Path.ofLine (f := fun t : ℝ => 1 - conj (meridianHalfCircle t)) (by fun_prop)
    (by norm_num [map_ofNat]) (by norm_num [map_ofNat])

private def SpecialPeriods.Triangle.lowerOneArc : Path (1 / 2 : ℂ) (3 / 2) :=
  Path.ofLine (f := fun t : ℝ => 1 - meridianHalfCircle t) (by fun_prop) (by norm_num)
    (by norm_num)

@[simp]
private theorem SpecialPeriods.Triangle.upperZeroArc_apply (t : unitInterval) :
    upperZeroArc t = (1 / 2 : ℂ) * Complex.exp ((Real.pi : ℂ) * Complex.I * (t : ℝ)) := by
  change meridianHalfCircle t = _
  unfold meridianHalfCircle
  rw [circleMap_zero]
  push_cast
  congr 1
  congr 1
  ring

@[simp]
private theorem SpecialPeriods.Triangle.lowerZeroArc_apply (t : unitInterval) :
    lowerZeroArc t = (1 / 2 : ℂ) * Complex.exp (-((Real.pi : ℂ) * Complex.I * (t : ℝ))) := by
  change conj (upperZeroArc t) = _
  rw [upperZeroArc_apply]
  simp only [map_mul, map_div₀, map_one, map_ofNat, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1
  congr 1
  ring

@[simp]
private theorem SpecialPeriods.Triangle.upperOneArc_apply (t : unitInterval) :
    upperOneArc t = 1 - (1 / 2 : ℂ) * Complex.exp (-((Real.pi : ℂ) * Complex.I * (t : ℝ))) := by
  change 1 - lowerZeroArc t = _
  rw [lowerZeroArc_apply]

@[simp]
private theorem SpecialPeriods.Triangle.lowerOneArc_apply (t : unitInterval) :
    lowerOneArc t = 1 - (1 / 2 : ℂ) * Complex.exp ((Real.pi : ℂ) * Complex.I * (t : ℝ)) := by
  change 1 - upperZeroArc t = _
  rw [upperZeroArc_apply]

private theorem SpecialPeriods.Triangle.upperZeroArc_mem_upperSlitPlane (t : unitInterval) :
    upperZeroArc t ∈ upperSlitPlane :=
  meridianHalfCircle_mem_upperSlitPlane t

private theorem SpecialPeriods.Triangle.lowerZeroArc_mem_lowerSlitPlane (t : unitInterval) :
    lowerZeroArc t ∈ lowerSlitPlane :=
  (conj_mem_lowerSlitPlane_iff_mo1973_23420 _).mpr (meridianHalfCircle_mem_upperSlitPlane t)

private theorem SpecialPeriods.Triangle.upperOneArc_mem_upperSlitPlane (t : unitInterval) :
    upperOneArc t ∈ upperSlitPlane :=
  (one_sub_mem_upperSlitPlane_iff_mo1973_23421 _).mpr (lowerZeroArc_mem_lowerSlitPlane t)

private theorem SpecialPeriods.Triangle.lowerOneArc_mem_lowerSlitPlane (t : unitInterval) :
    lowerOneArc t ∈ lowerSlitPlane :=
  (one_sub_mem_lowerSlitPlane_iff_mo1973_23422 _).mpr (upperZeroArc_mem_upperSlitPlane t)

private theorem SpecialPeriods.Triangle.upperZeroArc_avoids_punctures (t : unitInterval) :
    upperZeroArc t ≠ 0 ∧ upperZeroArc t ≠ 1 :=
  upperSlitPlane_subset_punctured (upperZeroArc_mem_upperSlitPlane t)

private theorem SpecialPeriods.Triangle.lowerZeroArc_avoids_punctures (t : unitInterval) :
    lowerZeroArc t ≠ 0 ∧ lowerZeroArc t ≠ 1 :=
  lowerSlitPlane_subset_punctured (lowerZeroArc_mem_lowerSlitPlane t)

private theorem SpecialPeriods.Triangle.upperOneArc_avoids_punctures (t : unitInterval) :
    upperOneArc t ≠ 0 ∧ upperOneArc t ≠ 1 :=
  upperSlitPlane_subset_punctured (upperOneArc_mem_upperSlitPlane t)

private theorem SpecialPeriods.Triangle.lowerOneArc_avoids_punctures (t : unitInterval) :
    lowerOneArc t ≠ 0 ∧ lowerOneArc t ≠ 1 :=
  lowerSlitPlane_subset_punctured (lowerOneArc_mem_lowerSlitPlane t)

public
theorem SpecialPeriods.Triangle.trans_symm_exp_apply_mo1973_23439 {x y : ℂ}
    (a b : Path x y) (c r : ℂ)
    (ha : ∀ t : unitInterval, a t = c + r * Complex.exp ((Real.pi : ℂ) * Complex.I * (t : ℝ)))
    (hb : ∀ t : unitInterval, b t = c + r * Complex.exp (-((Real.pi : ℂ) * Complex.I * (t : ℝ))))
    (t : unitInterval) :
    (a.trans b.symm) t = c + r * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (t : ℝ)) := by
  rw [Path.trans_apply]
  split_ifs with ht
  · rw [ha]
    apply congrArg (fun u : ℂ => c + r * Complex.exp u)
    push_cast
    ring
  · rw [Path.symm_apply, Function.comp_apply, hb]
    simp only [unitInterval.coe_symm_eq]
    have he :
      -((Real.pi : ℂ) * Complex.I * ((1 - (2 * (t : ℝ) - 1) : ℝ) : ℂ)) =
        (2 * Real.pi : ℂ) * Complex.I * (t : ℝ) - 2 * Real.pi * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_periodic.sub_eq]

private def SpecialPeriods.Triangle.meridianZeroComplex : Path (1 / 2 : ℂ) (1 / 2) :=
  upperZeroArc.trans lowerZeroArc.symm

private def SpecialPeriods.Triangle.meridianOneComplex : Path (1 / 2 : ℂ) (1 / 2) :=
  lowerOneArc.trans upperOneArc.symm

@[simp]
private theorem SpecialPeriods.Triangle.meridianZeroComplex_apply (t : unitInterval) :
    meridianZeroComplex t = (1 / 2 : ℂ) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (t : ℝ)) :=
  by
  simpa only [meridianZeroComplex, zero_add] using
    trans_symm_exp_apply_mo1973_23439 upperZeroArc lowerZeroArc 0 (1 / 2)
      (fun s => by simpa only [zero_add] using upperZeroArc_apply s)
      (fun s => by simpa only [zero_add] using lowerZeroArc_apply s) t

@[simp]
private theorem SpecialPeriods.Triangle.meridianOneComplex_apply (t : unitInterval) :
    meridianOneComplex t =
      1 - (1 / 2 : ℂ) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (t : ℝ)) := by
  simpa only [meridianOneComplex, neg_mul, ← sub_eq_add_neg] using
    trans_symm_exp_apply_mo1973_23439 lowerOneArc upperOneArc 1 (-(1 / 2))
      (fun s => by simpa only [neg_mul, ← sub_eq_add_neg] using lowerOneArc_apply s)
      (fun s => by simpa only [neg_mul, ← sub_eq_add_neg] using upperOneArc_apply s) t

private theorem SpecialPeriods.Triangle.meridianZeroComplex_eq_circleMap (t : unitInterval) :
    meridianZeroComplex t = circleMap 0 (1 / 2) (2 * Real.pi * (t : ℝ)) := by
  rw [meridianZeroComplex_apply, circleMap_zero]
  push_cast
  apply congrArg (fun u : ℂ => (1 / 2 : ℂ) * Complex.exp u)
  ring

private def SpecialPeriods.Triangle.meridianBasepoint : TwicePuncturedPlane :=
  ⟨(1 / 2 : ℂ), by norm_num⟩

private def SpecialPeriods.Triangle.meridianLeftPoint : TwicePuncturedPlane :=
  ⟨(-1 / 2 : ℂ), by norm_num⟩

private def SpecialPeriods.Triangle.meridianRightPoint : TwicePuncturedPlane :=
  ⟨(3 / 2 : ℂ), by norm_num⟩

private def SpecialPeriods.Triangle.liftPuncturedPath_mo1973_23454 {x y : TwicePuncturedPlane}
    (γ : Path (x : ℂ) (y : ℂ)) (hγ : ∀ t : unitInterval, γ t ∈ twicePuncturedPlaneDomain) :
    Path x y where
  toFun t := ⟨γ t, hγ t⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

private def SpecialPeriods.Triangle.upperZeroPath : Path meridianBasepoint meridianLeftPoint :=
  liftPuncturedPath_mo1973_23454 upperZeroArc upperZeroArc_avoids_punctures

private def SpecialPeriods.Triangle.lowerZeroPath : Path meridianBasepoint meridianLeftPoint :=
  liftPuncturedPath_mo1973_23454 lowerZeroArc lowerZeroArc_avoids_punctures

private def SpecialPeriods.Triangle.upperOnePath : Path meridianBasepoint meridianRightPoint :=
  liftPuncturedPath_mo1973_23454 upperOneArc upperOneArc_avoids_punctures

private def SpecialPeriods.Triangle.lowerOnePath : Path meridianBasepoint meridianRightPoint :=
  liftPuncturedPath_mo1973_23454 lowerOneArc lowerOneArc_avoids_punctures

private theorem SpecialPeriods.Triangle.upperZeroPath_mem_upperSlitPlane (t : unitInterval) :
    (upperZeroPath t : ℂ) ∈ upperSlitPlane :=
  upperZeroArc_mem_upperSlitPlane t

private theorem SpecialPeriods.Triangle.lowerZeroPath_mem_lowerSlitPlane (t : unitInterval) :
    (lowerZeroPath t : ℂ) ∈ lowerSlitPlane :=
  lowerZeroArc_mem_lowerSlitPlane t

private theorem SpecialPeriods.Triangle.upperOnePath_mem_upperSlitPlane (t : unitInterval) :
    (upperOnePath t : ℂ) ∈ upperSlitPlane :=
  upperOneArc_mem_upperSlitPlane t

private theorem SpecialPeriods.Triangle.lowerOnePath_mem_lowerSlitPlane (t : unitInterval) :
    (lowerOnePath t : ℂ) ∈ lowerSlitPlane :=
  lowerOneArc_mem_lowerSlitPlane t

@[simp]
private theorem SpecialPeriods.Triangle.upperZeroPath_map_coe :
    upperZeroPath.map continuous_subtype_val = upperZeroArc := by
  ext t
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.lowerZeroPath_map_coe :
    lowerZeroPath.map continuous_subtype_val = lowerZeroArc := by
  ext t
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.upperOnePath_map_coe :
    upperOnePath.map continuous_subtype_val = upperOneArc := by
  ext t
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.lowerOnePath_map_coe :
    lowerOnePath.map continuous_subtype_val = lowerOneArc := by
  ext t
  rfl

private def
    SpecialPeriods.Triangle.positiveMeridianZero : Path meridianBasepoint meridianBasepoint :=
  upperZeroPath.trans lowerZeroPath.symm

private def
    SpecialPeriods.Triangle.positiveMeridianOne : Path meridianBasepoint meridianBasepoint :=
  lowerOnePath.trans upperOnePath.symm

@[simp]
private theorem SpecialPeriods.Triangle.positiveMeridianZero_map_coe :
    positiveMeridianZero.map continuous_subtype_val = meridianZeroComplex := by
  change
    (upperZeroPath.trans lowerZeroPath.symm).map continuous_subtype_val =
      upperZeroArc.trans lowerZeroArc.symm
  rw [Path.map_trans, ← Path.map_symm, upperZeroPath_map_coe, lowerZeroPath_map_coe]
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.positiveMeridianOne_map_coe :
    positiveMeridianOne.map continuous_subtype_val = meridianOneComplex := by
  change
    (lowerOnePath.trans upperOnePath.symm).map continuous_subtype_val =
      lowerOneArc.trans upperOneArc.symm
  rw [Path.map_trans, ← Path.map_symm, lowerOnePath_map_coe, upperOnePath_map_coe]
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.positiveMeridianZero_coe (t : unitInterval) :
    (positiveMeridianZero t : ℂ) = meridianZeroComplex t :=
  congrArg (fun γ : Path (1 / 2 : ℂ) (1 / 2) => γ t) positiveMeridianZero_map_coe

@[simp]
private theorem SpecialPeriods.Triangle.positiveMeridianOne_coe (t : unitInterval) :
    (positiveMeridianOne t : ℂ) = meridianOneComplex t :=
  congrArg (fun γ : Path (1 / 2 : ℂ) (1 / 2) => γ t) positiveMeridianOne_map_coe

private theorem SpecialPeriods.Triangle.positiveMeridianZero_apply (t : unitInterval) :
    (positiveMeridianZero t : ℂ) =
      (1 / 2 : ℂ) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (t : ℝ)) := by
  rw [positiveMeridianZero_coe, meridianZeroComplex_apply]

private theorem SpecialPeriods.Triangle.positiveMeridianOne_apply (t : unitInterval) :
    (positiveMeridianOne t : ℂ) =
      1 - (1 / 2 : ℂ) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (t : ℝ)) := by
  rw [positiveMeridianOne_coe, meridianOneComplex_apply]

private theorem SpecialPeriods.Triangle.positiveMeridianZero_eq_circleMap (t : unitInterval) :
    (positiveMeridianZero t : ℂ) = circleMap 0 (1 / 2) (2 * Real.pi * (t : ℝ)) := by
  rw [positiveMeridianZero_coe, meridianZeroComplex_eq_circleMap]

private def SpecialPeriods.Triangle.upperSlitBasepoint : upperSlitPlane :=
  ⟨Complex.I, Or.inl (by simp)⟩

private def SpecialPeriods.Triangle.upperSlitHeightMap : C(upperSlitPlane, upperSlitPlane)
    where
  toFun z := ⟨(z.val.re : ℂ) + Complex.I, Or.inl (by simp)⟩
  continuous_toFun := by fun_prop

private theorem SpecialPeriods.Triangle.upperSlit_vertical_mem_mo1973_23539 (t : unitInterval)
    (z : upperSlitPlane) :
    (z.val.re : ℂ) + (((1 - t.val) * z.val.im + t.val : ℝ) : ℂ) * Complex.I ∈ upperSlitPlane := by
  simp only [upperSlitPlane, Set.mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, MulZeroClass.mul_zero, add_zero,
    zero_add, Complex.add_re, Complex.mul_re, sub_zero]
  rcases z.property with hz | hz
  · left
    by_cases ht : t.val = 1
    · simp [ht]
    · have hp : 0 < 1 - t.val := sub_pos.mpr ((lt_or_eq_of_le t.property.2).resolve_right ht)
      exact add_pos_of_pos_of_nonneg (mul_pos hp hz) t.property.1
  · exact Or.inr hz

private def SpecialPeriods.Triangle.upperSlitVerticalHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id upperSlitPlane) upperSlitHeightMap
    where
  toFun
    p :=
    ⟨(p.2.val.re : ℂ) + (((1 - p.1.val) * p.2.val.im + p.1.val : ℝ) : ℂ) * Complex.I,
      upperSlit_vertical_mem_mo1973_23539 p.1 p.2⟩
  continuous_toFun := by fun_prop
  map_zero_left
    z := by
    apply Subtype.ext
    simp
  map_one_left
    z := by
    apply Subtype.ext
    simp [upperSlitHeightMap]

private def SpecialPeriods.Triangle.upperSlitHorizontalHomotopy :
    ContinuousMap.Homotopy upperSlitHeightMap
      (ContinuousMap.const upperSlitPlane upperSlitBasepoint)
    where
  toFun p := ⟨(((1 - p.1.val) * p.2.val.re : ℝ) : ℂ) + Complex.I, Or.inl (by simp)⟩
  continuous_toFun := by fun_prop
  map_zero_left
    z := by
    apply Subtype.ext
    simp [upperSlitHeightMap]
  map_one_left
    z := by
    apply Subtype.ext
    simp [upperSlitBasepoint]

private def SpecialPeriods.Triangle.upperSlitContraction :
    ContinuousMap.Homotopy (ContinuousMap.id upperSlitPlane)
      (ContinuousMap.const upperSlitPlane upperSlitBasepoint) :=
  upperSlitVerticalHomotopy.trans upperSlitHorizontalHomotopy

private instance SpecialPeriods.Triangle.upperSlitPlane_contractibleSpace :
    ContractibleSpace upperSlitPlane :=
  (contractible_iff_id_nullhomotopic upperSlitPlane).mpr
    ⟨upperSlitBasepoint, ⟨upperSlitContraction⟩⟩

private def SpecialPeriods.Triangle.slitConjugation : upperSlitPlane ≃ₜ lowerSlitPlane
    where
  toFun z := ⟨conj (z : ℂ), by simpa [upperSlitPlane, lowerSlitPlane] using z.property⟩
  invFun z := ⟨conj (z : ℂ), by simpa [upperSlitPlane, lowerSlitPlane] using z.property⟩
  left_inv z := Subtype.ext (Complex.conj_conj _)
  right_inv z := Subtype.ext (Complex.conj_conj _)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private instance SpecialPeriods.Triangle.lowerSlitPlane_contractibleSpace :
    ContractibleSpace lowerSlitPlane :=
  slitConjugation.symm.contractibleSpace

private def SpecialPeriods.Triangle.overlapStrip : Fin 3 → Set ℂ
  | 0 => {z | z.re < 0}
  | 1 => {z | 0 < z.re ∧ z.re < 1}
  | 2 => {z | 1 < z.re}

private def SpecialPeriods.Triangle.overlapStripBasepoint : Fin 3 → ℂ
  | 0 => -1
  | 1 => ((1 / 2 : ℝ) : ℂ)
  | 2 => 2

private theorem SpecialPeriods.Triangle.overlapStrip_basepoint_mem (i : Fin 3) :
    overlapStripBasepoint i ∈ overlapStrip i := by
  fin_cases i <;> norm_num [overlapStripBasepoint, overlapStrip]

private def SpecialPeriods.Triangle.overlapStripPoint (i : Fin 3) : overlapStrip i :=
  ⟨overlapStripBasepoint i, overlapStrip_basepoint_mem i⟩

private theorem
    SpecialPeriods.Triangle.overlapStrip_nonempty (i : Fin 3) : (overlapStrip i).Nonempty :=
  ⟨overlapStripBasepoint i, overlapStrip_basepoint_mem i⟩

private theorem
    SpecialPeriods.Triangle.overlapStrip_isOpen (i : Fin 3) : IsOpen (overlapStrip i) := by
  fin_cases i
  · exact isOpen_lt Complex.continuous_re continuous_const
  · exact
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
  · exact isOpen_lt continuous_const Complex.continuous_re

private theorem
    SpecialPeriods.Triangle.overlapStrip_convex (i : Fin 3) : Convex ℝ (overlapStrip i) := by
  fin_cases i
  · exact convex_halfSpace_re_lt 0
  · exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  · exact convex_halfSpace_re_gt 1

private theorem SpecialPeriods.Triangle.overlapStrip_isPathConnected (i : Fin 3) :
    IsPathConnected (overlapStrip i) :=
  (overlapStrip_convex i).isPathConnected (overlapStrip_nonempty i)

private theorem SpecialPeriods.Triangle.overlapStrip_isConnected (i : Fin 3) :
    IsConnected (overlapStrip i) :=
  (overlapStrip_isPathConnected i).isConnected

private instance SpecialPeriods.Triangle.overlapStrip_contractibleSpace (i : Fin 3) :
    ContractibleSpace (overlapStrip i) :=
  (overlapStrip_convex i).contractibleSpace (overlapStrip_nonempty i)

private theorem SpecialPeriods.Triangle.overlapStrip_joinedIn (i : Fin 3) {z w : ℂ}
    (hz : z ∈ overlapStrip i) (hw : w ∈ overlapStrip i) : JoinedIn (overlapStrip i) z w :=
  JoinedIn.of_segment_subset ((overlapStrip_convex i).segment_subset hz hw)

private theorem SpecialPeriods.Triangle.overlapStrip_pairwise_disjoint :
    Pairwise (fun i j : Fin 3 => Disjoint (overlapStrip i) (overlapStrip j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  fin_cases i <;> fin_cases j <;> simp_all [overlapStrip] <;> linarith

private theorem SpecialPeriods.Triangle.overlapStrip_iUnion :
    (⋃ i : Fin 3, overlapStrip i) = upperSlitPlane ∩ lowerSlitPlane := by
  rw [slitPlanes_inter]
  ext z
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp only [overlapStrip, Set.mem_ofPred_eq] at hi ⊢ <;> constructor <;>
        intro heq <;>
      linarith
  · rintro ⟨hzero, hone⟩
    rcases lt_or_gt_of_ne hzero with hneg | hpos
    · exact ⟨0, hneg⟩
    · rcases lt_or_gt_of_ne hone with hlt | hgt
      · exact ⟨1, hpos, hlt⟩
      · exact ⟨2, hgt⟩

private theorem SpecialPeriods.Triangle.overlapStrip_subset_overlap (i : Fin 3) :
    overlapStrip i ⊆ upperSlitPlane ∩ lowerSlitPlane := by
  rw [← overlapStrip_iUnion]
  exact Set.subset_iUnion overlapStrip i

private theorem SpecialPeriods.Triangle.overlapStrip_connectedComponentIn (i : Fin 3) {z : ℂ}
    (hz : z ∈ overlapStrip i) :
    connectedComponentIn (upperSlitPlane ∩ lowerSlitPlane) z = overlapStrip i := by
  let R : Set ℂ := ⋃ j : Fin 3, ⋃ (_ : j ≠ i), overlapStrip j
  have hRopen : IsOpen R := isOpen_iUnion fun j => isOpen_iUnion fun _ => overlapStrip_isOpen j
  have hdisj : Disjoint (overlapStrip i) R := by
    apply Set.disjoint_iUnion_right.mpr
    intro j
    apply Set.disjoint_iUnion_right.mpr
    intro hji
    exact overlapStrip_pairwise_disjoint hji.symm
  have hcover : upperSlitPlane ∩ lowerSlitPlane ⊆ overlapStrip i ∪ R := by
    rw [← overlapStrip_iUnion]
    intro w hw
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hw
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨j, hji, hj⟩)
  apply subset_antisymm
  · have hc : IsPreconnected (connectedComponentIn (upperSlitPlane ∩ lowerSlitPlane) z) :=
      isPreconnected_connectedComponentIn
    exact
      hc.subset_left_of_subset_union (overlapStrip_isOpen i) hRopen hdisj
        ((connectedComponentIn_subset _ _).trans hcover)
        ⟨z, mem_connectedComponentIn (overlapStrip_subset_overlap i hz), hz⟩
  · exact
      (overlapStrip_isConnected i).isPreconnected.subset_connectedComponentIn hz
        (overlapStrip_subset_overlap i)

private theorem SpecialPeriods.Triangle.overlapStrip_pathComponentIn (i : Fin 3) {z : ℂ}
    (hz : z ∈ overlapStrip i) :
    pathComponentIn (upperSlitPlane ∩ lowerSlitPlane) z = overlapStrip i := by
  have hzO := overlapStrip_subset_overlap i hz
  apply subset_antisymm
  · calc
      pathComponentIn (upperSlitPlane ∩ lowerSlitPlane) z ⊆
          connectedComponentIn (upperSlitPlane ∩ lowerSlitPlane) z :=
        (isPathConnected_pathComponentIn
              hzO).isConnected.isPreconnected.subset_connectedComponentIn
          (mem_pathComponentIn_self hzO) pathComponentIn_subset
      _ = overlapStrip i := overlapStrip_connectedComponentIn i hz
  · exact
      (overlapStrip_isPathConnected i).subset_pathComponentIn hz (overlapStrip_subset_overlap i)

private theorem SpecialPeriods.Triangle.overlap_joinedIn_iff {z w : ℂ} :
    JoinedIn (upperSlitPlane ∩ lowerSlitPlane) z w ↔
      ∃ i : Fin 3, z ∈ overlapStrip i ∧ w ∈ overlapStrip i := by
  constructor
  · intro h
    have hz : z ∈ ⋃ i : Fin 3, overlapStrip i := by
      rw [overlapStrip_iUnion]
      exact h.source_mem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    refine ⟨i, hi, ?_⟩
    have hm : w ∈ pathComponentIn (upperSlitPlane ∩ lowerSlitPlane) z := h
    rwa [overlapStrip_pathComponentIn i hi] at hm
  · rintro ⟨i, hz, hw⟩
    exact (overlapStrip_joinedIn i hz hw).mono (overlapStrip_subset_overlap i)

private def SpecialPeriods.Triangle.upperSlit : TopologicalSpace.Opens TwicePuncturedPlane :=
  ⟨{z | (z : ℂ) ∈ upperSlitPlane}, upperSlitPlane_isOpen.preimage continuous_subtype_val⟩

private def SpecialPeriods.Triangle.lowerSlit : TopologicalSpace.Opens TwicePuncturedPlane :=
  ⟨{z | (z : ℂ) ∈ lowerSlitPlane}, lowerSlitPlane_isOpen.preimage continuous_subtype_val⟩

private theorem SpecialPeriods.Triangle.mem_upperSlit_or_lowerSlit (z : TwicePuncturedPlane) :
    z ∈ upperSlit ∨ z ∈ lowerSlit := by
  have hz : (z : ℂ) ∈ ({w : ℂ | w ≠ 0 ∧ w ≠ 1}) := z.property
  rwa [← slitPlanes_union] at hz

private theorem SpecialPeriods.Triangle.upperSlit_union_lowerSlit :
    (upperSlit : Set TwicePuncturedPlane) ∪ lowerSlit = Set.univ :=
  Set.eq_univ_of_forall mem_upperSlit_or_lowerSlit

private def SpecialPeriods.Triangle.upperSlitHomeomorph : upperSlit ≃ₜ upperSlitPlane
    where
  toFun z := ⟨z.val.val, z.property⟩
  invFun z := ⟨⟨z.val, upperSlitPlane_subset_punctured z.property⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def SpecialPeriods.Triangle.lowerSlitHomeomorph : lowerSlit ≃ₜ lowerSlitPlane
    where
  toFun z := ⟨z.val.val, z.property⟩
  invFun z := ⟨⟨z.val, lowerSlitPlane_subset_punctured z.property⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private instance
    SpecialPeriods.Triangle.upperSlit_contractibleSpace : ContractibleSpace upperSlit :=
  upperSlitHomeomorph.contractibleSpace

private instance
    SpecialPeriods.Triangle.lowerSlit_contractibleSpace : ContractibleSpace lowerSlit :=
  lowerSlitHomeomorph.contractibleSpace

private theorem
    SpecialPeriods.Triangle.upperSlit_simplyConnectedSpace : SimplyConnectedSpace upperSlit :=
  inferInstance

private theorem
    SpecialPeriods.Triangle.lowerSlit_simplyConnectedSpace : SimplyConnectedSpace lowerSlit :=
  inferInstance

private def SpecialPeriods.Triangle.slitOverlapStrip (i : Fin 3) :
    TopologicalSpace.Opens TwicePuncturedPlane :=
  ⟨{z | (z : ℂ) ∈ overlapStrip i}, (overlapStrip_isOpen i).preimage continuous_subtype_val⟩

private def SpecialPeriods.Triangle.slitOverlapStripHomeomorph (i : Fin 3) :
    slitOverlapStrip i ≃ₜ overlapStrip i
    where
  toFun z := ⟨z.val.val, z.property⟩
  invFun
    z :=
    ⟨⟨z.val, upperSlitPlane_subset_punctured ((overlapStrip_subset_overlap i z.property).1)⟩,
      z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private instance SpecialPeriods.Triangle.slitOverlapStrip_contractibleSpace (i : Fin 3) :
    ContractibleSpace (slitOverlapStrip i) :=
  (slitOverlapStripHomeomorph i).contractibleSpace

private theorem SpecialPeriods.Triangle.slitOverlapStrip_isPathConnected (i : Fin 3) :
    IsPathConnected (slitOverlapStrip i : Set TwicePuncturedPlane) := by
  let : ContractibleSpace (slitOverlapStrip i : Set TwicePuncturedPlane) :=
    slitOverlapStrip_contractibleSpace i
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

private theorem SpecialPeriods.Triangle.slitOverlapStrip_subset_overlap (i : Fin 3) :
    (slitOverlapStrip i : Set TwicePuncturedPlane) ⊆
      (upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit :=
  fun _ hz => overlapStrip_subset_overlap i hz

private def SpecialPeriods.Triangle.slitOverlapStripPoint (i : Fin 3) : slitOverlapStrip i :=
  (slitOverlapStripHomeomorph i).symm (overlapStripPoint i)

private theorem SpecialPeriods.Triangle.slitOverlapStrip_pairwise_disjoint :
    Pairwise fun i j : Fin 3 =>
      Disjoint (slitOverlapStrip i : Set TwicePuncturedPlane) (slitOverlapStrip j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  exact Set.disjoint_left.mp (overlapStrip_pairwise_disjoint hij) hi hj

private theorem SpecialPeriods.Triangle.slitOverlapStrip_iUnion :
    (⋃ i : Fin 3, (slitOverlapStrip i : Set TwicePuncturedPlane)) =
      (upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact slitOverlapStrip_subset_overlap i hi
  · intro hz
    have hc : (z : ℂ) ∈ (⋃ i : Fin 3, overlapStrip i) := by
      rw [overlapStrip_iUnion]
      exact hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hc
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

private theorem SpecialPeriods.Triangle.slitOverlap_joinedIn_iff {z w : TwicePuncturedPlane} :
    JoinedIn ((upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit) z w ↔
      ∃ i : Fin 3, z ∈ slitOverlapStrip i ∧ w ∈ slitOverlapStrip i := by
  constructor
  · intro h
    have hc :
      JoinedIn
        (((↑) : TwicePuncturedPlane → ℂ) '' ((upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit))
        (z : ℂ) (w : ℂ) :=
      h.map continuous_subtype_val
    have hs :
      ((↑) : TwicePuncturedPlane → ℂ) '' ((upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit) ⊆
        upperSlitPlane ∩ lowerSlitPlane := by
      rintro x ⟨y, hy, rfl⟩
      exact hy
    exact overlap_joinedIn_iff.mp (hc.mono hs)
  · rintro ⟨i, hz, hw⟩
    exact
      ((slitOverlapStrip_isPathConnected i).joinedIn z hz w hw).mono
        (slitOverlapStrip_subset_overlap i)

private def SpecialPeriods.Triangle.meridianClass (b : Bool) :
    FundamentalGroup TwicePuncturedPlane meridianBasepoint :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (if b then positiveMeridianOne else positiveMeridianZero))

private def SpecialPeriods.Triangle.meridianWordMap :
    FreeGroup Bool →* FundamentalGroup TwicePuncturedPlane meridianBasepoint :=
  FreeGroup.lift meridianClass

@[simp]
private theorem SpecialPeriods.Triangle.meridianWordMap_of (b : Bool) :
    meridianWordMap (FreeGroup.of b) = meridianClass b :=
  FreeGroup.lift_apply_of

private theorem SpecialPeriods.Triangle.base_mem_upper_mo1973_23596 :
    meridianBasepoint ∈ upperSlit := by
  change (meridianBasepoint : ℂ) ∈ upperSlitPlane
  simpa using upperZeroPath_mem_upperSlitPlane 0

private theorem SpecialPeriods.Triangle.base_mem_lower_mo1973_23597 :
    meridianBasepoint ∈ lowerSlit := by
  change (meridianBasepoint : ℂ) ∈ lowerSlitPlane
  simpa using lowerZeroPath_mem_lowerSlitPlane 0

private theorem SpecialPeriods.Triangle.left_mem_upper_mo1973_23598 :
    meridianLeftPoint ∈ upperSlit := by
  change (meridianLeftPoint : ℂ) ∈ upperSlitPlane
  simpa using upperZeroPath_mem_upperSlitPlane 1

private theorem SpecialPeriods.Triangle.left_mem_lower_mo1973_23599 :
    meridianLeftPoint ∈ lowerSlit := by
  change (meridianLeftPoint : ℂ) ∈ lowerSlitPlane
  simpa using lowerZeroPath_mem_lowerSlitPlane 1

private theorem SpecialPeriods.Triangle.right_mem_upper_mo1973_23600 :
    meridianRightPoint ∈ upperSlit := by
  change (meridianRightPoint : ℂ) ∈ upperSlitPlane
  simpa using upperOnePath_mem_upperSlitPlane 1

private theorem SpecialPeriods.Triangle.right_mem_lower_mo1973_23601 :
    meridianRightPoint ∈ lowerSlit := by
  change (meridianRightPoint : ℂ) ∈ lowerSlitPlane
  simpa using lowerOnePath_mem_lowerSlitPlane 1

private def SpecialPeriods.Triangle.meridianSlitCover :
    TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover TwicePuncturedPlane
    where
  U := upperSlit
  V := lowerSlit
  cover := upperSlit_union_lowerSlit
  simplyU := upperSlit_simplyConnectedSpace
  simplyV := lowerSlit_simplyConnectedSpace
  base := meridianBasepoint
  baseU := base_mem_upper_mo1973_23596
  baseV := base_mem_lower_mo1973_23597

private theorem SpecialPeriods.Triangle.switch_left_mo1973_23603 :
    meridianSlitCover.switchClass meridianLeftPoint left_mem_upper_mo1973_23598
        left_mem_lower_mo1973_23599 =
      meridianClass Bool.false :=
  meridianSlitCover.switchClass_eq_of_paths left_mem_upper_mo1973_23598
    left_mem_lower_mo1973_23599 upperZeroPath lowerZeroPath upperZeroPath_mem_upperSlitPlane
    lowerZeroPath_mem_lowerSlitPlane

private theorem SpecialPeriods.Triangle.switch_right_mo1973_23604 :
    meridianSlitCover.switchClass meridianRightPoint right_mem_upper_mo1973_23600
        right_mem_lower_mo1973_23601 =
      (meridianClass Bool.true)⁻¹ := by
  rw [meridianSlitCover.switchClass_eq_of_paths right_mem_upper_mo1973_23600
      right_mem_lower_mo1973_23601 upperOnePath lowerOnePath upperOnePath_mem_upperSlitPlane
      lowerOnePath_mem_lowerSlitPlane]
  change
    Path.Homotopic.Quotient.mk (upperOnePath.trans lowerOnePath.symm) =
      Path.Homotopic.Quotient.mk (lowerOnePath.trans upperOnePath.symm).symm
  rw [Path.trans_symm, Path.symm_symm]

private def SpecialPeriods.Triangle.overlapRepresentative_mo1973_23605 :
    Fin 3 → TwicePuncturedPlane
  | 0 => meridianLeftPoint
  | 1 => meridianBasepoint
  | 2 => meridianRightPoint

private theorem SpecialPeriods.Triangle.overlapRepresentative_mem_mo1973_23606 (i : Fin 3) :
    overlapRepresentative_mo1973_23605 i ∈ slitOverlapStrip i := by
  fin_cases i <;>
    norm_num [overlapRepresentative_mo1973_23605, slitOverlapStrip, overlapStrip,
      meridianLeftPoint, meridianBasepoint, meridianRightPoint]

private theorem SpecialPeriods.Triangle.overlapRepresentative_mem_upper_mo1973_23607 (i : Fin 3) :
    overlapRepresentative_mo1973_23605 i ∈ meridianSlitCover.U :=
  (slitOverlapStrip_subset_overlap i (overlapRepresentative_mem_mo1973_23606 i)).1

private theorem SpecialPeriods.Triangle.overlapRepresentative_mem_lower_mo1973_23608 (i : Fin 3) :
    overlapRepresentative_mo1973_23605 i ∈ meridianSlitCover.V :=
  (slitOverlapStrip_subset_overlap i (overlapRepresentative_mem_mo1973_23606 i)).2

private theorem SpecialPeriods.Triangle.every_overlap_point_joined_mo1973_23609
    (x : TwicePuncturedPlane) (hxU : x ∈ meridianSlitCover.U) (hxV : x ∈ meridianSlitCover.V) :
    ∃ i : Fin 3,
      JoinedIn ((meridianSlitCover.U : Set TwicePuncturedPlane) ∩ meridianSlitCover.V)
        (overlapRepresentative_mo1973_23605 i) x := by
  have hx : x ∈ ⋃ i : Fin 3, (slitOverlapStrip i : Set TwicePuncturedPlane) := by
    rw [slitOverlapStrip_iUnion]
    exact ⟨hxU, hxV⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨i, slitOverlap_joinedIn_iff.mpr ⟨i, overlapRepresentative_mem_mo1973_23606 i, hi⟩⟩

private theorem SpecialPeriods.Triangle.meridianWordMap_surjective :
    Function.Surjective meridianWordMap := by
  apply MonoidHom.range_eq_top.mp
  apply meridianSlitCover.subgroup_eq_top_of_switchClass_mem
  intro x hxU hxV
  obtain ⟨i, hi⟩ := every_overlap_point_joined_mo1973_23609 x hxU hxV
  rw [←
    meridianSlitCover.switchClass_eq_of_joinedIn (overlapRepresentative_mem_upper_mo1973_23607 i)
      (overlapRepresentative_mem_lower_mo1973_23608 i) hxU hxV hi]
  fin_cases i
  · change meridianSlitCover.switchClass meridianLeftPoint _ _ ∈ meridianWordMap.range
    rw [switch_left_mo1973_23603]
    exact ⟨FreeGroup.of Bool.false, meridianWordMap_of Bool.false⟩
  · change meridianSlitCover.switchClass meridianSlitCover.base _ _ ∈ meridianWordMap.range
    rw [meridianSlitCover.switchClass_base]
    exact meridianWordMap.range.one_mem
  · change meridianSlitCover.switchClass meridianRightPoint _ _ ∈ meridianWordMap.range
    rw [switch_right_mo1973_23604]
    exact meridianWordMap.range.inv_mem ⟨FreeGroup.of Bool.true, meridianWordMap_of Bool.true⟩

@[instance_reducible]
private def SpecialPeriods.Triangle.discreteFreeGroup : TopologicalSpace (FreeGroup Bool) :=
  ⊥

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private instance
    SpecialPeriods.Triangle.discreteFreeGroup_discrete : DiscreteTopology (FreeGroup Bool) :=
  ⟨rfl⟩

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private def SpecialPeriods.Triangle.freeGroupTransitionValue : Fin 3 → FreeGroup Bool
  | 0 => (FreeGroup.of Bool.false)⁻¹
  | 1 => 1
  | 2 => FreeGroup.of Bool.true

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private def
    SpecialPeriods.Triangle.freeGroupTransition (z : TwicePuncturedPlane) : FreeGroup Bool :=
  if (z : ℂ).re < 0 then (FreeGroup.of Bool.false)⁻¹
  else if (z : ℂ).re < 1 then 1 else FreeGroup.of Bool.true

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem SpecialPeriods.Triangle.freeGroupTransition_eqOn_strip (i : Fin 3) :
    Set.EqOn freeGroupTransition (fun _ => freeGroupTransitionValue i)
      (slitOverlapStrip i : Set TwicePuncturedPlane) := by
  intro z hz
  fin_cases i
  · have hneg : (z : ℂ).re < 0 := hz
    simp only [freeGroupTransition, ite_eq_left hneg, freeGroupTransitionValue]
  · have hmid : 0 < (z : ℂ).re ∧ (z : ℂ).re < 1 := hz
    simp only [freeGroupTransition, ite_eq_right (not_lt.mpr hmid.1.le), ite_eq_left hmid.2,
      freeGroupTransitionValue]
  · have hpos : 1 < (z : ℂ).re := hz
    have hnonneg : ¬(z : ℂ).re < 0 := by linarith
    simp only [freeGroupTransition, ite_eq_right hnonneg, ite_eq_right (not_lt.mpr hpos.le),
      freeGroupTransitionValue]

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem SpecialPeriods.Triangle.freeGroupTransition_continuousOn :
    ContinuousOn freeGroupTransition ((upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit) := by
  apply continuousOn_of_locally_continuousOn
  intro z hz
  have hz' : z ∈ ⋃ i : Fin 3, (slitOverlapStrip i : Set TwicePuncturedPlane) := by
    rw [slitOverlapStrip_iUnion]
    exact hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz'
  refine ⟨slitOverlapStrip i, (slitOverlapStrip i).isOpen, hi, ?_⟩
  apply (continuousOn_const (c := freeGroupTransitionValue i)).congr
  intro w hw
  exact freeGroupTransition_eqOn_strip i hw.2

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private def SpecialPeriods.Triangle.freeGroupCover :
    TwoOpenTransition TwicePuncturedPlane (FreeGroup Bool)
    where
  U := upperSlit
  V := lowerSlit
  cover := upperSlit_union_lowerSlit
  transition := freeGroupTransition
  continuousOn_transition := freeGroupTransition_continuousOn

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
@[simp]
private theorem SpecialPeriods.Triangle.freeGroupCover_transition :
    freeGroupCover.transition = freeGroupTransition :=
  rfl

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
@[simp]
private theorem SpecialPeriods.Triangle.freeGroupTransition_basepoint :
    freeGroupTransition meridianBasepoint = 1 := by
  norm_num [freeGroupTransition, meridianBasepoint]

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
@[simp]
private theorem SpecialPeriods.Triangle.freeGroupTransition_leftPoint :
    freeGroupTransition meridianLeftPoint = (FreeGroup.of Bool.false)⁻¹ := by
  norm_num [freeGroupTransition, meridianLeftPoint]

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
@[simp]
private theorem SpecialPeriods.Triangle.freeGroupTransition_rightPoint :
    freeGroupTransition meridianRightPoint = FreeGroup.of Bool.true := by
  norm_num [freeGroupTransition, meridianRightPoint]

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem SpecialPeriods.Triangle.freeGroupCover_basepoint_mem :
    meridianBasepoint ∈ (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V := by
  change (meridianBasepoint : ℂ) ∈ upperSlitPlane ∩ lowerSlitPlane
  rw [slitPlanes_inter]
  norm_num [meridianBasepoint]

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem SpecialPeriods.Triangle.freeGroupCover_leftPoint_mem :
    meridianLeftPoint ∈ (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V := by
  change (meridianLeftPoint : ℂ) ∈ upperSlitPlane ∩ lowerSlitPlane
  rw [slitPlanes_inter]
  norm_num [meridianLeftPoint]

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private theorem SpecialPeriods.Triangle.freeGroupCover_rightPoint_mem :
    meridianRightPoint ∈ (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V := by
  change (meridianRightPoint : ℂ) ∈ upperSlitPlane ∩ lowerSlitPlane
  rw [slitPlanes_inter]
  norm_num [meridianRightPoint]

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
private def SpecialPeriods.Triangle.meridianFreeWordHom :
    FundamentalGroup TwicePuncturedPlane meridianBasepoint →* FreeGroup Bool :=
  (MulEquiv.inv' (FreeGroup Bool)).symm.toMonoidHom.comp
    (freeGroupCover.fundamentalGroupToMulOpposite meridianBasepoint
      freeGroupCover_basepoint_mem.1)

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
@[simp]
private theorem SpecialPeriods.Triangle.meridianFreeWordHom_positiveMeridianZero :
    meridianFreeWordHom (.mk positiveMeridianZero) = FreeGroup.of Bool.false := by
  have hzero :=
    freeGroupCover.fundamentalGroupToMulOpposite_trans_U_V freeGroupCover_basepoint_mem
      freeGroupCover_leftPoint_mem upperZeroPath lowerZeroPath.symm
      (fun s => upperZeroPath_mem_upperSlitPlane s)
      (fun s => lowerZeroPath_mem_lowerSlitPlane (unitInterval.symm s))
  change
    (MulEquiv.inv' (FreeGroup Bool)).symm
        (freeGroupCover.fundamentalGroupToMulOpposite meridianBasepoint
          freeGroupCover_basepoint_mem.1 (.mk (upperZeroPath.trans lowerZeroPath.symm))) =
      _
  rw [hzero]
  change (freeGroupTransition meridianLeftPoint * (freeGroupTransition meridianBasepoint)⁻¹)⁻¹ = _
  simp

attribute [local instance] SpecialPeriods.Triangle.discreteFreeGroup in
@[simp]
private theorem SpecialPeriods.Triangle.meridianFreeWordHom_positiveMeridianOne :
    meridianFreeWordHom (.mk positiveMeridianOne) = FreeGroup.of Bool.true := by
  have hone :=
    freeGroupCover.fundamentalGroupToMulOpposite_trans_U_V freeGroupCover_basepoint_mem
      freeGroupCover_rightPoint_mem upperOnePath lowerOnePath.symm
      (fun s => upperOnePath_mem_upperSlitPlane s)
      (fun s => lowerOnePath_mem_lowerSlitPlane (unitInterval.symm s))
  have hword :
    meridianFreeWordHom (.mk (upperOnePath.trans lowerOnePath.symm)) =
      (FreeGroup.of Bool.true)⁻¹ := by
    change
      (MulEquiv.inv' (FreeGroup Bool)).symm
          (freeGroupCover.fundamentalGroupToMulOpposite meridianBasepoint
            freeGroupCover_basepoint_mem.1 (.mk (upperOnePath.trans lowerOnePath.symm))) =
        _
    rw [hone]
    change
      (freeGroupTransition meridianRightPoint * (freeGroupTransition meridianBasepoint)⁻¹)⁻¹ = _
    simp
  let q : FundamentalGroup TwicePuncturedPlane meridianBasepoint :=
    .mk (upperOnePath.trans lowerOnePath.symm)
  have hpath :
    (.mk positiveMeridianOne : FundamentalGroup TwicePuncturedPlane meridianBasepoint) = q⁻¹ := by
    rw [FundamentalGroup.inv_def]
    change
      .mk positiveMeridianOne =
        (Path.Homotopic.Quotient.mk (upperOnePath.trans lowerOnePath.symm)).symm
    rw [← Path.Homotopic.Quotient.mk_symm, Path.trans_symm, Path.symm_symm]
    rfl
  rw [hpath, map_inv]
  change (meridianFreeWordHom (.mk (upperOnePath.trans lowerOnePath.symm)))⁻¹ = _
  rw [hword, inv_inv]

@[simp]
private theorem SpecialPeriods.Triangle.meridianFreeWordHom_meridianClass (b : Bool) :
    meridianFreeWordHom (meridianClass b) = FreeGroup.of b := by
  cases b
  · exact meridianFreeWordHom_positiveMeridianZero
  · exact meridianFreeWordHom_positiveMeridianOne

private theorem SpecialPeriods.Triangle.meridianFreeWordHom_comp_wordMap :
    meridianFreeWordHom.comp meridianWordMap = MonoidHom.id (FreeGroup Bool) := by
  apply FreeGroup.ext_hom
  intro b
  simp only [MonoidHom.comp_apply, meridianWordMap_of, meridianFreeWordHom_meridianClass,
    MonoidHom.id_apply]

@[simp]
private theorem SpecialPeriods.Triangle.meridianFreeWordHom_wordMap (w : FreeGroup Bool) :
    meridianFreeWordHom (meridianWordMap w) = w :=
  DFunLike.congr_fun meridianFreeWordHom_comp_wordMap w

@[simp]
private theorem SpecialPeriods.Triangle.meridianWordMap_freeWordHom
    (γ : FundamentalGroup TwicePuncturedPlane meridianBasepoint) :
    meridianWordMap (meridianFreeWordHom γ) = γ := by
  obtain ⟨w, rfl⟩ := meridianWordMap_surjective γ
  rw [meridianFreeWordHom_wordMap]

private def SpecialPeriods.Triangle.twicePuncturedFundamentalGroupFreeEquiv :
    FundamentalGroup TwicePuncturedPlane meridianBasepoint ≃* FreeGroup Bool
    where
  __ := meridianFreeWordHom
  invFun := meridianWordMap
  left_inv := meridianWordMap_freeWordHom
  right_inv := meridianFreeWordHom_wordMap

@[simp]
private theorem SpecialPeriods.Triangle.twicePuncturedFundamentalGroupFreeEquiv_symm_of (b : Bool) :
    twicePuncturedFundamentalGroupFreeEquiv.symm (FreeGroup.of b) = meridianClass b :=
  meridianWordMap_of b

end Mathoverflow1973

end
