/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.W1p.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The ball Poincare inequality for representative-level `W^{1,p}` functions

The proof uses interior mollification on compactly contained balls and then
exhausts the original ball.
-/

public section

open Function Set Filter MeasureTheory Topology
open scoped ENNReal Convolution Pointwise

namespace CKN

noncomputable section

lemma opNorm_eq_sum_abs_basis (L : Vec 3 →L[ℝ] ℝ) :
    ‖L‖ = ∑ i : Fin 3, |L (basisVec i)| := by
  have hdecomp (x : Vec 3) :
      x = x 0 • basisVec 0 + x 1 • basisVec 1 + x 2 • basisVec 2 := by
    simpa only [Fin.sum_univ_three] using (sum_smul_basisVec x).symm
  have hupper : ‖L‖ ≤ ∑ i : Fin 3, |L (basisVec i)| := by
    apply ContinuousLinearMap.opNorm_le_bound L (by positivity)
    intro x
    have hxL : L x = L (x 0 • basisVec 0) + L (x 1 • basisVec 1) +
        L (x 2 • basisVec 2) := by
      calc
        L x = L (x 0 • basisVec 0 + x 1 • basisVec 1 + x 2 • basisVec 2) :=
          congrArg L (hdecomp x)
        _ = _ := by simp only [map_add, map_smul]
    rw [hxL, Real.norm_eq_abs]
    have hcalc :
        |L (x 0 • basisVec 0) + L (x 1 • basisVec 1) +
            L (x 2 • basisVec 2)| ≤
          ‖x‖ * (|L (basisVec 0)| + |L (basisVec 1)| +
            |L (basisVec 2)|) := by
      calc
        |L (x 0 • basisVec 0) + L (x 1 • basisVec 1) +
            L (x 2 • basisVec 2)| ≤
            |L (x 0 • basisVec 0)| + |L (x 1 • basisVec 1)| +
              |L (x 2 • basisVec 2)| := by
          calc
            |L (x 0 • basisVec 0) + L (x 1 • basisVec 1) +
                L (x 2 • basisVec 2)| ≤
                |L (x 0 • basisVec 0) + L (x 1 • basisVec 1)| +
                  |L (x 2 • basisVec 2)| := abs_add_le _ _
            _ ≤ |L (x 0 • basisVec 0)| + |L (x 1 • basisVec 1)| +
                  |L (x 2 • basisVec 2)| := by
              calc
                |L (x 0 • basisVec 0) + L (x 1 • basisVec 1)| +
                    |L (x 2 • basisVec 2)| ≤
                    (|L (x 0 • basisVec 0)| + |L (x 1 • basisVec 1)|) +
                      |L (x 2 • basisVec 2)| :=
                  add_le_add_left (abs_add_le _ _) _
                _ = _ := by ring
        _ = |x 0| * |L (basisVec 0)| + |x 1| * |L (basisVec 1)| +
            |x 2| * |L (basisVec 2)| := by
          simp only [map_smul, smul_eq_mul, abs_mul]
        _ ≤ ‖x‖ * (|L (basisVec 0)| + |L (basisVec 1)| +
            |L (basisVec 2)|) := by
          calc
            |x 0| * |L (basisVec 0)| + |x 1| * |L (basisVec 1)| +
                |x 2| * |L (basisVec 2)| ≤
                ‖x‖ * |L (basisVec 0)| + ‖x‖ * |L (basisVec 1)| +
                  ‖x‖ * |L (basisVec 2)| := by
              gcongr <;> exact norm_le_pi_norm x _
            _ = _ := by ring
    simpa only [Fin.sum_univ_three, mul_comm] using hcalc
  have hlower : (∑ i : Fin 3, |L (basisVec i)|) ≤ ‖L‖ := by
    let hsign : Vec 3 := fun i => if 0 ≤ L (basisVec i) then 1 else -1
    have hnorm : ‖hsign‖ = 1 := by
      apply le_antisymm
      · apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
        intro i
        by_cases hi : 0 ≤ L (basisVec i) <;> simp [hsign, hi]
      · calc
          1 = ‖hsign 0‖ := by
            by_cases h : 0 ≤ L (basisVec 0) <;> simp [hsign, h]
          _ ≤ ‖hsign‖ := norm_le_pi_norm _ 0
    have hvalue : L hsign = ∑ i : Fin 3, |L (basisVec i)| := by
      rw [← sum_smul_basisVec hsign, map_sum]
      simp only [Fin.sum_univ_three, map_smul]
      simp only [hsign, smul_eq_mul]
      have hterm (i : Fin 3) :
          (if 0 ≤ L (basisVec i) then 1 else -1) * L (basisVec i) =
            |L (basisVec i)| := by
        by_cases hi : 0 ≤ L (basisVec i)
        · simp [hi, abs_of_nonneg]
        · simp [hi, abs_of_neg (lt_of_not_ge hi)]
      rw [hterm 0, hterm 1, hterm 2]
    have hle := ContinuousLinearMap.le_opNorm L hsign
    have hsum_nonneg : 0 ≤ ∑ i : Fin 3, |L (basisVec i)| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    rw [hvalue, hnorm, mul_one, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg] at hle
    exact hle
  exact le_antisymm hupper hlower

/-- The native coordinate-gradient norm used by the scalar `W^{1,p}` result. -/
@[expose]
def w1pGradientNorm {U : Set (Vec 3)} {p : ℝ≥0∞}
    (u : W1pFunction U p) : Vec 3 → ℝ :=
  fun x => ∑ i : Fin 3, |u.grad x i|


end
end CKN
