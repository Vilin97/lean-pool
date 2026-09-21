/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.AboveTwo

/-!
# Scalar two-level geometric amortization for the guarded controller

These lemmas are deliberately independent of the executable controller.  They
are the numerical engine used below: an inner radius-doubling geometric sum is
paid by its last radius, and the outer scale-doubling sum is paid by its last
scale.  In particular no estimate of the form "number of trials times the
last trial" occurs.
-/

namespace O3

/-- Abstract properties shared by the three source cost envelopes. -/
structure DoublingWeight (w : ℝ → ℝ) (ratio : ℝ) : Prop where
  ratio_gt_one : 1 < ratio
  nonneg : ∀ {x}, 0 ≤ x → 0 ≤ w x
  mono : MonotoneOn w (Set.Ici 0)
  doubling : ∀ {x}, 0 ≤ x → ratio * w x ≤ w (2 * x)

/-- The exponent in all three wrapper regimes is strictly positive. -/
noncomputable def WrapperExponent (p : ℝ) : ℝ :=
  if p ≤ 2 then (1 / 2 : ℝ) else aboveAlpha p

theorem wrapperExponent_pos {p : ℝ} (hp : 1 < p) :
    0 < WrapperExponent p := by
  unfold WrapperExponent
  split_ifs with h
  · norm_num
  · exact aboveAlpha_pos (lt_of_not_ge h)

/-- A convenient geometric-amortization coefficient. -/
noncomputable def geometricAmortizationConstant (a : ℝ) : ℝ :=
  (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)

theorem two_rpow_gt_one {a : ℝ} (ha : 0 < a) :
    1 < (2 : ℝ) ^ a := by
  exact (Real.one_lt_rpow (by norm_num) ha)

theorem geometricAmortizationConstant_pos {a : ℝ} (ha : 0 < a) :
    0 < geometricAmortizationConstant a := by
  unfold geometricAmortizationConstant
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (sub_pos.mpr (two_rpow_gt_one ha))

/-- Exact finite inner geometric summation, expressed through its endpoint. -/
theorem radius_geometric_sum_le_endpoint {a beta : ℝ}
    (ha : 0 < a) (hbeta : 0 ≤ beta) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j * beta) ^ a ≤
      geometricAmortizationConstant a * (((2 : ℝ) ^ J * beta) ^ a) := by
  by_cases hb : beta = 0
  · subst beta
    simp [Real.zero_rpow ha.ne']
  have hbetaPos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hb)
  have hratio : 1 < (2 : ℝ) ^ a := two_rpow_gt_one ha
  have hbetaPow : 0 ≤ beta ^ a := Real.rpow_nonneg hbeta _
  have hrewrite :
      ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j * beta) ^ a =
        ∑ j ∈ Finset.range (J + 1), beta ^ a * ((2 : ℝ) ^ a) ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.mul_rpow (pow_nonneg (by norm_num) _) hbeta]
    rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) a j]
    ring
  rw [hrewrite]
  have hgeom := aboveGeometricSum_le hbetaPow hratio (J + 1)
  have hend : (((2 : ℝ) ^ J * beta) ^ a) =
      beta ^ a * ((2 : ℝ) ^ a) ^ J := by
    rw [Real.mul_rpow (pow_nonneg (by norm_num) _) hbeta]
    rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) a J]
    ring
  unfold geometricAmortizationConstant
  rw [hend]
  calc
    ∑ j ∈ Finset.range (J + 1), beta ^ a * ((2 : ℝ) ^ a) ^ j
        ≤ beta ^ a * ((2 : ℝ) ^ a) ^ (J + 1) /
            ((2 : ℝ) ^ a - 1) := hgeom
    _ = (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) *
          (beta ^ a * ((2 : ℝ) ^ a) ^ J) := by rw [pow_succ]; ring

/-- The same genuine geometric sum across scale epochs. -/
theorem scale_geometric_sum_le_endpoint {a k0 : ℝ}
    (ha : 0 < a) (hk0 : 0 ≤ k0) (S : ℕ) :
    ∑ s ∈ Finset.range (S + 1), (((2 : ℝ) ^ s * k0) ^ a) ≤
      geometricAmortizationConstant a * (((2 : ℝ) ^ S * k0) ^ a) :=
  radius_geometric_sum_le_endpoint ha hk0 S

noncomputable def euclideanWrapperWeight (x : ℝ) : ℝ := Real.sqrt x
noncomputable def aboveWrapperWeight (a x : ℝ) : ℝ := x ^ a
noncomputable def belowWrapperWeight (x : ℝ) : ℝ :=
  Real.sqrt x * Real.log (Real.exp 1 + x)

theorem euclideanWrapperWeight_doubling :
    DoublingWeight euclideanWrapperWeight (Real.sqrt 2) := by
  have hsqrt : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  refine ⟨hsqrt, ?_, ?_, ?_⟩
  · intro x hx
    exact Real.sqrt_nonneg _
  · intro x hx y hy hxy
    exact Real.sqrt_le_sqrt hxy
  · intro x hx
    unfold euclideanWrapperWeight
    rw [show 2 * x = 2 * x by rfl, Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]

theorem aboveWrapperWeight_doubling {a : ℝ} (ha : 0 < a) :
    DoublingWeight (aboveWrapperWeight a) ((2 : ℝ) ^ a) := by
  refine ⟨two_rpow_gt_one ha, ?_, ?_, ?_⟩
  · intro x hx
    exact Real.rpow_nonneg hx _
  · intro x hx y hy hxy
    exact Real.rpow_le_rpow hx hxy ha.le
  · intro x hx
    unfold aboveWrapperWeight
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx]

theorem belowWrapperWeight_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ belowWrapperWeight x := by
  unfold belowWrapperWeight
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by
    have : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith))

theorem belowWrapperWeight_mono :
    MonotoneOn belowWrapperWeight (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  unfold belowWrapperWeight
  have hpx : 0 < Real.exp 1 + x := add_pos_of_pos_of_nonneg (Real.exp_pos 1) hx
  have hpy : 0 < Real.exp 1 + y := add_pos_of_pos_of_nonneg (Real.exp_pos 1) hy
  have hsum : Real.exp 1 + x ≤ Real.exp 1 + y := by linarith
  have hlog : Real.log (Real.exp 1 + x) ≤ Real.log (Real.exp 1 + y) :=
    Real.strictMonoOn_log.monotoneOn hpx hpy hsum
  apply mul_le_mul (Real.sqrt_le_sqrt hxy)
  · exact hlog
  · exact Real.log_nonneg (by
      have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
      linarith)
  · exact Real.sqrt_nonneg _

theorem belowWrapperWeight_doubling :
    DoublingWeight belowWrapperWeight (Real.sqrt 2) := by
  have hsqrt : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  refine ⟨hsqrt, @belowWrapperWeight_nonneg, ?_, ?_⟩
  · exact belowWrapperWeight_mono
  · intro x hx
    unfold belowWrapperWeight
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hp1 : 0 < Real.exp 1 + x := add_pos_of_pos_of_nonneg (Real.exp_pos 1) hx
    have hp2 : 0 < Real.exp 1 + 2 * x :=
      add_pos_of_pos_of_nonneg (Real.exp_pos 1) (mul_nonneg (by norm_num) hx)
    have hlog : Real.log (Real.exp 1 + x) ≤ Real.log (Real.exp 1 + 2 * x) := by
      exact Real.strictMonoOn_log.monotoneOn hp1 hp2 (by linarith)
    have hfac : 0 ≤ Real.sqrt 2 * Real.sqrt x :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith

end O3
