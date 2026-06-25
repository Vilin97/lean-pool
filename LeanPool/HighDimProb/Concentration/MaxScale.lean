/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Init

/-!
# Finite max-scale and variance-proxy helpers

Verified Wikipedia references:
* Bernstein inequalities: https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
* Variance: https://en.wikipedia.org/wiki/Variance

Note: Wikipedia does not provide a dedicated finite `maxScale` or
`varianceProxy` page; these helpers package the scales used by Bernstein-type
bounds.

This file contains the small deterministic vocabulary needed by the
subExponential/Bernstein branch.  The max scale is exposed as a real number,
but is implemented through a finite supremum in `NNReal` so the empty finite
case has a canonical value.
-/

namespace HighDimProb

noncomputable section

open scoped BigOperators NNReal

/--
Finite maximum scale for a real-valued finite family.

Negative entries are clipped at zero by `Real.toNNReal`; the intended
probability use supplies nonnegative, usually positive, scale parameters.
-/
def maxScale {ι : Type*} [Fintype ι] (K : ι -> Real) : Real :=
  ((Finset.univ.sup (fun i => Real.toNNReal (K i)) : NNReal) : Real)

/-- Variance proxy for a finite family of subExponential scales. -/
def varianceProxy {ι : Type*} [Fintype ι] (K : ι -> Real) : Real :=
  ∑ i : ι, (K i) ^ 2

/-- Weighted variance proxy `sum_i c_i^2 * K_i^2`. -/
def weightedVarianceProxy {ι : Type*} [Fintype ι] (c K : ι -> Real) : Real :=
  ∑ i : ι, (c i) ^ 2 * (K i) ^ 2

/-- Weighted max scale `max_i |c_i| * K_i`, implemented through `maxScale`. -/
def weightedMaxScale {ι : Type*} [Fintype ι] (c K : ι -> Real) : Real :=
  maxScale (fun i => |c i| * K i)

/-- Each nonnegative scale is bounded by the finite max scale. -/
theorem le_maxScale {ι : Type*} [Fintype ι] (K : ι -> Real) (i : ι)
    (hKi : 0 <= K i) :
    K i <= maxScale K := by
  have hsup :
      Real.toNNReal (K i) <= Finset.univ.sup (fun j => Real.toNNReal (K j)) :=
    Finset.le_sup (f := fun j => Real.toNNReal (K j)) (Finset.mem_univ i)
  have hcoe :
      K i = ((Real.toNNReal (K i) : NNReal) : Real) := by
    rw [Real.coe_toNNReal (K i) hKi]
  rw [hcoe, maxScale]
  exact_mod_cast hsup

/-- The finite max scale is nonnegative. -/
theorem maxScale_nonneg {ι : Type*} [Fintype ι] (K : ι -> Real) :
    0 <= maxScale K := by
  rw [maxScale]
  exact NNReal.coe_nonneg _

/-- The weighted finite max scale is nonnegative. -/
theorem weightedMaxScale_nonneg {ι : Type*} [Fintype ι] (c K : ι -> Real) :
    0 <= weightedMaxScale c K := by
  exact maxScale_nonneg (fun i => |c i| * K i)

/-- A positive member makes the finite max scale positive. -/
theorem maxScale_pos_of_exists_pos {ι : Type*} [Fintype ι] (K : ι -> Real)
    (hpos : ∃ i : ι, 0 < K i) :
    0 < maxScale K := by
  rcases hpos with ⟨i, hi⟩
  have hsup :
      Real.toNNReal (K i) <= Finset.univ.sup (fun j => Real.toNNReal (K j)) :=
    Finset.le_sup (f := fun j => Real.toNNReal (K j)) (Finset.mem_univ i)
  have hofReal_pos : 0 < (Real.toNNReal (K i) : NNReal) := by
    exact Real.toNNReal_pos.mpr hi
  have hsup_pos : 0 < Finset.univ.sup (fun j => Real.toNNReal (K j)) :=
    lt_of_lt_of_le hofReal_pos hsup
  exact_mod_cast hsup_pos

/--
The max-scale lambda domain implies each individual local-MGF domain, once the
individual positive scale is known to be below the max scale.
-/
theorem abs_le_inv_of_le_inv_maxScale {ι : Type*} [Fintype ι]
    (K : ι -> Real) (i : ι) {lambda : Real}
    (hKi : 0 < K i) (hKle : K i <= maxScale K)
    (hlambda : |lambda| <= 1 / maxScale K) :
    |lambda| <= 1 / K i :=
  hlambda.trans (one_div_le_one_div_of_le hKi hKle)

/-- The variance proxy is nonnegative. -/
theorem varianceProxy_nonneg {ι : Type*} [Fintype ι] (K : ι -> Real) :
    0 <= varianceProxy K := by
  exact Finset.sum_nonneg (fun i _hi => sq_nonneg (K i))

/-- The weighted variance proxy is nonnegative. -/
theorem weightedVarianceProxy_nonneg {ι : Type*} [Fintype ι] (c K : ι -> Real) :
    0 <= weightedVarianceProxy c K := by
  exact
    Finset.sum_nonneg
      (fun i _hi => mul_nonneg (sq_nonneg (c i)) (sq_nonneg (K i)))

/-- Each nonnegative weighted scale is bounded by the weighted finite max scale. -/
theorem le_weightedMaxScale {ι : Type*} [Fintype ι] (c K : ι -> Real) (i : ι)
    (hKi : 0 <= K i) :
    |c i| * K i <= weightedMaxScale c K := by
  exact
    le_maxScale (fun j => |c j| * K j) i
      (mul_nonneg (abs_nonneg (c i)) hKi)

/--
The weighted max-scale lambda domain implies the individual domain
`|lambda * c_i| <= 1 / K_i`.  The proof keeps the zero-weight case explicit.
-/
theorem abs_mul_le_inv_of_le_weightedMaxScale {ι : Type*} [Fintype ι]
    (c K : ι -> Real) (i : ι) {lambda : Real}
    (hKi : 0 < K i)
    (hlambda : |lambda| <= 1 / weightedMaxScale c K) :
    |lambda * c i| <= 1 / K i := by
  by_cases hc : c i = 0
  · rw [hc, mul_zero, abs_zero]
    exact one_div_nonneg.mpr hKi.le
  · have hc_abs_pos : 0 < |c i| := abs_pos.mpr hc
    have hscale_pos : 0 < |c i| * K i := mul_pos hc_abs_pos hKi
    have hscale_le : |c i| * K i <= weightedMaxScale c K :=
      le_weightedMaxScale c K i hKi.le
    have hlambda_scale : |lambda| <= 1 / (|c i| * K i) := by
      exact
        abs_le_inv_of_le_inv_maxScale (fun j => |c j| * K j) i
          hscale_pos hscale_le (by simpa [weightedMaxScale] using hlambda)
    rw [abs_mul]
    calc
      |lambda| * |c i| <= (1 / (|c i| * K i)) * |c i| :=
        mul_le_mul_of_nonneg_right hlambda_scale (abs_nonneg (c i))
      _ = 1 / K i := by
        field_simp [hc_abs_pos.ne', hKi.ne']

/-- A positive scale makes the variance proxy positive. -/
theorem varianceProxy_pos_of_exists_pos {ι : Type*} [Fintype ι] (K : ι -> Real)
    (hpos : ∃ i : ι, 0 < K i) :
    0 < varianceProxy K := by
  rcases hpos with ⟨i, hi⟩
  have hsq_pos : 0 < (K i) ^ 2 := sq_pos_of_pos hi
  have hle : (K i) ^ 2 <= varianceProxy K := by
    exact Finset.single_le_sum (fun j _hj => sq_nonneg (K j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le hsq_pos hle

/-- Each squared scale is bounded by the variance proxy. -/
theorem sq_le_varianceProxy {ι : Type*} [Fintype ι] (K : ι -> Real) (i : ι) :
    (K i) ^ 2 <= varianceProxy K := by
  exact Finset.single_le_sum (fun j _hj => sq_nonneg (K j)) (Finset.mem_univ i)

end

end HighDimProb
