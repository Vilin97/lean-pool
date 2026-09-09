/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ConstantCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.NonlinearEnergyConstants

/-! An explicit positive amplitude puts any finite Gevrey datum and
quadratic residual envelope in the all-order correction regime. The
growth constant belongs to the identity-metric equation, not to an
assumed solution. -/

@[expose] public section


noncomputable section

namespace EulerSmallCorrection

open Set EulerConstantCorrection EulerNonlinearEnergyConstants

variable (P : ℝ) [Fact (0 < P)]

/-- Growth, given by `energyConstant P 0 0 1 1 pressureBound 1 1 0 0 1`. -/
def growth : ℝ := energyConstant P 0 0 1 1 pressureBound 1 1 0 0 1

theorem growth_pos : 0 < growth P :=
  energyConstant_pos P 0 0 1 1 pressureBound 1 1 0 0 1 le_rfl le_rfl
    zero_le_one zero_le_one (zero_le_one.trans pressureBound_one_le)
    zero_le_one zero_le_one le_rfl le_rfl zero_lt_one

/-- Initial radius, given by `1/(2*(R+1))`. -/
def initialRadius (R : ℝ) : ℝ := 1/(2*(R+1))

theorem initialRadius_pos (R : ℝ) (hR : 0 ≤ R) : 0 < initialRadius R := by
  unfold initialRadius
  positivity

theorem initialRadius_mul (R : ℝ) (hR : 0 ≤ R) : initialRadius R*R ≤ 1/2 := by
  unfold initialRadius
  have hd : 0 < 2*(R+1) := by positivity
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ = R/(R+1) := by field_simp
    _ ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)

/-- These are scalar smallness inequalities, obtained explicitly below. -/
structure Scale (C R E : ℝ) where
  /-- Value of `Scale`, of type `ℝ`. -/
  value : ℝ
  positive : 0 < value
  one : value ≤ 1
  background : 2*value*C ≤ 1
  derivative : 12*value*C*R ≤ 1
  shrink : 2*growth P*(8*value*C+value) ≤ initialRadius R/2
  residual : 2*(value^2*E)*Real.exp (3*growth P) ≤ value/2

/-- Scale as an element of `Scale P C R E`. -/
def scale (C R E : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hE : 0 < E) : Scale P C R E := by
  let a := 1/(2*C+1)
  let b := 1/(12*C*R+1)
  let c := initialRadius R/(4*growth P*(8*C+1)+1)
  let d := 1/(4*E*Real.exp (3*growth P)+1)
  let v := min 1 (min a (min b (min c d)))
  have hG := growth_pos P
  have hr := initialRadius_pos R hR
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hv : 0 < v := lt_min zero_lt_one (lt_min ha (lt_min hb (lt_min hc hd)))
  have h1 : v ≤ 1 := min_le_left _ _
  have h2 : v ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : v ≤ b := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : v ≤ c := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have h5 : v ≤ d := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have ha' : v*(2*C+1) ≤ 1 := (le_div_iff₀ (by positivity)).mp h2
  have hb' : v*(12*C*R+1) ≤ 1 := (le_div_iff₀ (by positivity)).mp h3
  have hc' : v*(4*growth P*(8*C+1)+1) ≤ initialRadius R :=
    (le_div_iff₀ (by positivity)).mp h4
  have hd' : v*(4*E*Real.exp (3*growth P)+1) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp h5
  refine ⟨v,hv,h1,?_,?_,?_,?_⟩
  · nlinarith only [ha',hv]
  · nlinarith only [hb',hv]
  · nlinarith only [hc',hv]
  · have hh := mul_le_mul_of_nonneg_left hd' hv.le
    nlinarith only [hh,sq_nonneg v]

/-- Radius as an element of `C(Icc (0 : ℝ) 1,ℝ)`. -/
def Scale.radius {C R E : ℝ} (S : Scale P C R E) : C(Icc (0 : ℝ) 1,ℝ) :=
  ⟨fun t => initialRadius R-2*growth P*(8*S.value*C+S.value)*t.val,
    continuous_const.sub (continuous_const.mul continuous_subtype_val)⟩

theorem Scale.radius_bounds {C R E : ℝ} (S : Scale P C R E) (hC : 0 ≤ C)
    (t : Icc (0 : ℝ) 1) :
    initialRadius R/2 ≤ S.radius P t ∧ S.radius P t ≤ initialRadius R := by
  have hG := growth_pos P
  have hv := S.positive
  have ha : 0 ≤ 2*growth P*(8*S.value*C+S.value) := by positivity
  have hb := mul_le_mul_of_nonneg_left t.property.2 ha
  have hc := mul_nonneg ha t.property.1
  have hd := S.shrink
  change initialRadius R/2 ≤ initialRadius R-2*growth P*(8*S.value*C+S.value)*t.val ∧
    initialRadius R-2*growth P*(8*S.value*C+S.value)*t.val ≤ initialRadius R
  constructor <;> linarith only [hb,hc,hd]

theorem Scale.radius_positive {C R E : ℝ} (S : Scale P C R E) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (t : Icc (0 : ℝ) 1) : 0 < S.radius P t :=
  (half_pos (initialRadius_pos R hR)).trans_le (S.radius_bounds P hC t).1

theorem Scale.radius_small {C R E : ℝ} (S : Scale P C R E) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (t : Icc (0 : ℝ) 1) : S.radius P t*R ≤ 1/2 :=
  (mul_le_mul_of_nonneg_right (S.radius_bounds P hC t).2 hR).trans (initialRadius_mul R hR)

end EulerSmallCorrection
