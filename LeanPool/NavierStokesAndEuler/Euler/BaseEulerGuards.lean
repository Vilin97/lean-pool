/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketScaledBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketRestriction
public import LeanPool.NavierStokesAndEuler.Euler.PacketFirstPressureSign

@[expose] public section

/-! The genuine base parent can be restricted to one explicit positive
time on which the low-order source guards hold. The constants depend
only on its fixed label envelope; the initial core is empty. -/

noncomputable section

namespace EulerBaseEulerGuards

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerParentPacketFrames EulerPacketParentLabelBounds EulerGevrey
  EulerPacketFirstPressureSign EulerTimeIntervalRestriction

def coefficientCost (K : ℝ) : ℝ := 27*(frameAmplitude K)^2*gradientAmplitude K

theorem coefficientCost_nonneg (K : ℝ) : 0 ≤ coefficientCost K := by
  unfold coefficientCost
  positivity [gradientAmplitude_nonneg K]

def guardTime (T K : ℝ) : ℝ :=
  min T (min 1 (1/(4*(1+coefficientCost K+
    firstSignRate (coefficientCost K) (coefficientCost K)))))

theorem guardTime_pos (T K : ℝ) (hT : 0 < T) : 0 < guardTime T K := by
  have hC := coefficientCost_nonneg K
  have hr : 0 ≤ firstSignRate (coefficientCost K) (coefficientCost K) := by
    unfold firstSignRate
    positivity
  unfold guardTime
  positivity

theorem guardTime_le (T K : ℝ) : guardTime T K ≤ T := min_le_left _ _

theorem guardTime_le_one (T K : ℝ) : guardTime T K ≤ 1 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem guardTime_small (T K : ℝ) :
    coefficientCost K*guardTime T K ≤ 1/4 ∧
      firstSignRate (coefficientCost K) (coefficientCost K)*guardTime T K ≤ 1/4 := by
  let C := coefficientCost K
  let R := firstSignRate C C
  have hC : 0 ≤ C := coefficientCost_nonneg K
  have hR : 0 ≤ R := by dsimp [R,firstSignRate]; positivity
  have hd : 0 < 4*(1+C+R) := by positivity
  have ht : guardTime T K ≤ 1/(4*(1+C+R)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hc := mul_le_mul_of_nonneg_left ht hC
  have hr := mul_le_mul_of_nonneg_left ht hR
  have hc' : C*(1/(4*(1+C+R))) ≤ 1/4 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hr' : R*(1/(4*(1+C+R))) ≤ 1/4 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  exact ⟨hc.trans hc',hr.trans hr'⟩

theorem inner_bounds_of_norm (A : Space →L[ℝ] Space) (C : ℝ)
    (hA : ‖A‖ ≤ C) (v : Space) :
    -C*‖v‖^2 ≤ ⟪A v,v⟫_ℝ ∧ ⟪A v,v⟫_ℝ ≤ C*‖v‖^2 := by
  have hn : ‖A v‖ ≤ C*‖v‖ :=
    (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hi : |⟪A v,v⟫_ℝ| ≤ C*‖v‖^2 := by
    calc
      _ ≤ ‖A v‖*‖v‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (A v) v
      _ ≤ (C*‖v‖)*‖v‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = _ := by ring
  constructor
  · nlinarith [(abs_le.mp hi).1]
  · exact (abs_le.mp hi).2

variable {G : Parent} (L : LabelData G)

theorem strain_norm (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖G.strain.field t x‖ ≤ coefficientCost L.K := by
  have h := L.strain_scaled_bound 0 t x
  simpa only [coefficientCost,norm_iteratedFDeriv_zero,majorant,Nat.zero_add,
    Nat.factorial_zero,Nat.cast_one,pow_zero,one_pow,mul_one] using h

theorem curvature_norm (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖G.curvature.field t x‖ ≤ coefficientCost L.K := by
  have h := L.curvature_scaled_bound 0 t x
  simpa only [coefficientCost,norm_iteratedFDeriv_zero,majorant,Nat.zero_add,
    Nat.factorial_zero,Nat.cast_one,pow_zero,one_pow,mul_one] using h

theorem initialStrain_norm (x : Space) :
    ‖G.initialStrain.field x‖ ≤ coefficientCost L.K := by
  have he : G.strain.field G.zeroTime x=G.initialStrain.field x := by
    apply ContinuousLinearMap.ext
    intro v
    rw [G.strain_apply,comp_apply,G.inverse_initial,G.initialStrain_apply]
  rw [← he]
  exact strain_norm L G.zeroTime x

def lowBoundsOn (S : ℝ) (hS : 0 < S) (hST : S ≤ G.T)
    (hSone : S ≤ 1) (hsmall : coefficientCost L.K*S ≤ 1/4) :
    LowBounds (G.restrictTime S hS hST) where
  Be := coefficientCost L.K
  Bc := 0
  L := 0
  r := 0
  K := coefficientCost L.K
  Be_nonneg := coefficientCost_nonneg L.K
  Bc_nonneg := le_rfl
  L_lower := by simp
  r_nonneg := le_rfl
  r_le_quarter := by norm_num
  K_nonneg := coefficientCost_nonneg L.K
  exterior_lower x _ v := by
    rw [G.restrictTime_initialStrain]
    exact (inner_bounds_of_norm _ _ (initialStrain_norm L x) v).1
  core_lower x hx _ := by
    exact False.elim ((not_lt_of_ge (norm_nonneg _)) hx)
  curvature_upper t x v := by
    erw [G.restrictTime_curvature]
    exact (inner_bounds_of_norm _ _ (curvature_norm L (initialInclusion G.T S hST t) x) v).2
  small := by
    change coefficientCost L.K*(S^2/2)+coefficientCost L.K*S+_ ≤ 1/2
    simp only [mul_zero,zero_mul,zero_pow (by decide : 3 ≠ 0),add_zero]
    have hsquare : S^2 ≤ S := by nlinarith [mul_nonneg hS.le (sub_nonneg.mpr hSone)]
    have hc := mul_le_mul_of_nonneg_left hsquare (coefficientCost_nonneg L.K)
    nlinarith

def lowBounds : LowBounds
    (G.restrictTime (guardTime G.T L.K) (guardTime_pos G.T L.K G.T_pos)
      (guardTime_le G.T L.K)) :=
  lowBoundsOn L _ _ _ (guardTime_le_one G.T L.K) (guardTime_small G.T L.K).1

end EulerBaseEulerGuards
