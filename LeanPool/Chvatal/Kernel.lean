/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/
module

public import LeanPool.Chvatal.Auxiliary
public import LeanPool.Chvatal.Counting

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# The auxiliary kernel and Bessel lower bound

This file proves the kernel calculation (8) and the lower bound (14) in the proof
of Theorem 1.4. All sums are finite and the normalization is made explicit.
-/

public section

open scoped BigOperators symmDiff

noncomputable section

namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The function `H_y` from Section 3.1, with a general spectral multiplier `q`.
The paper takes `q = g - t`. -/
def auxiliaryKernel (F : Family ι) (q : Finset ι → ℝ) (y x : Finset ι) : ℝ :=
  if x ∈ F then (Fintype.card (Finset ι) : ℝ) * fourier q (x ∆ y) else 0

/-- The convolution calculation preceding equation (8), before imposing the
physical support condition on the auxiliary function. -/
theorem sum_mul_fourier_translate (h q : Finset ι → ℝ) (y : Finset ι) :
    (∑ x, h x * fourier q (x ∆ y)) =
      ∑ S, q S * fourier h S * walsh S y := by
  simp only [fourier, cubeMean, mul_div_assoc, Finset.mul_sum, Finset.sum_div,
    Finset.sum_mul, walsh_symmDiff_left]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro x _
  rw [walsh_comm x S, walsh_comm y S]
  ring

/-- The physical support restriction cancels the indicator and the normalization
in the inner product with `H_y`, as in the first line preceding equation (8). -/
theorem auxiliaryKernel_inner_sum (F : Family ι) (q h : Finset ι → ℝ)
    (y : Finset ι) (hh : ∀ x, x ∉ F → h x = 0) :
    uniformInner h (auxiliaryKernel F q y) = ∑ x, h x * fourier q (x ∆ y) := by
  have heq (x : Finset ι) :
      h x * auxiliaryKernel F q y x =
        (Fintype.card (Finset ι) : ℝ) * (h x * fourier q (x ∆ y)) := by
    by_cases hx : x ∈ F
    · simp only [auxiliaryKernel, ite_eq_left hx]; ring
    · simp [auxiliaryKernel, hx, hh x hx]
  simp only [uniformInner, heq, ← Finset.mul_sum]
  exact mul_div_cancel_left₀ _ (ne_of_gt (cube_card_pos (ι := ι)))

/-- The spectral form of the inner product calculation in Section 3.1. -/
theorem auxiliaryKernel_inner_fourier (F : Family ι) (q h : Finset ι → ℝ)
    (y : Finset ι) (hh : ∀ x, x ∉ F → h x = 0) :
    uniformInner h (auxiliaryKernel F q y) =
      ∑ S, q S * fourier h S * walsh S y := by
  rw [auxiliaryKernel_inner_sum F q h y hh, sum_mul_fourier_translate]

/-- Equation (8) in its general form: a constant spectral multiplier on the
Fourier support of `h` makes `h` an eigenfunction of the kernel. -/
theorem auxiliaryKernel_inner_eigenvalue (F : Family ι) (q h : Finset ι → ℝ)
    (y : Finset ι) (hh : ∀ x, x ∉ F → h x = 0) (c : ℝ)
    (hc : ∀ S, q S * fourier h S = c * fourier h S) :
    uniformInner h (auxiliaryKernel F q y) = c * h y := by
  rw [auxiliaryKernel_inner_fourier F q h y hh]
  simp_rw [hc, mul_assoc]
  rw [← Finset.mul_sum, fourier_inversion]

/-- Equation (8), first case: Fourier support outside `G` gives eigenvalue `-t`. -/
theorem auxiliaryKernel_inner_outside (F G : Family ι) (h : Finset ι → ℝ)
    (y : Finset ι) (t : ℝ) (hh : h ∈ supportSubspace F Gᶜ) :
    uniformInner h (auxiliaryKernel F (fun S => G.indicator S - t) y) = -t * h y := by
  apply auxiliaryKernel_inner_eigenvalue F _ h y hh.1 (-t)
  intro S
  by_cases hS : S ∈ G
  · rw [hh.2 S (by simpa using hS), mul_zero, mul_zero]
  · simp [Family.indicator, hS]

/-- Equation (8), second case: Fourier support inside `G` gives eigenvalue `1-t`. -/
theorem auxiliaryKernel_inner_inside (F G : Family ι) (h : Finset ι → ℝ)
    (y : Finset ι) (t : ℝ) (hh : h ∈ supportSubspace F G) :
    uniformInner h (auxiliaryKernel F (fun S => G.indicator S - t) y) =
      (1 - t) * h y := by
  apply auxiliaryKernel_inner_eigenvalue F _ h y hh.1 (1 - t)
  intro S
  by_cases hS : S ∈ G
  · simp [Family.indicator, hS]
  · rw [hh.2 S hS, mul_zero, mul_zero]

/-- Equation (7), pointwise norm calculation for the auxiliary kernel. -/
theorem auxiliaryKernel_norm_sq (F : Family ι) (q : Finset ι → ℝ) (y : Finset ι) :
    uniformInner (auxiliaryKernel F q y) (auxiliaryKernel F q y) =
      (Fintype.card (Finset ι) : ℝ) * ∑ x ∈ F, (fourier q (x ∆ y)) ^ 2 := by
  have heq (x : Finset ι) :
      auxiliaryKernel F q y x * auxiliaryKernel F q y x =
        (Fintype.card (Finset ι) : ℝ) ^ 2 *
          (if x ∈ F then (fourier q (x ∆ y)) ^ 2 else 0) := by
    by_cases hx : x ∈ F <;> simp [auxiliaryKernel, hx]
    ring
  simp only [uniformInner, heq, ← Finset.mul_sum]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]
  rw [pow_two, mul_assoc, mul_div_cancel_left₀ _ (ne_of_gt (cube_card_pos (ι := ι)))]

/-- Equation (7): the squared Fourier kernel on `F × F` is the average,
with factor `2^{-n}`, of the squared norms of the auxiliary kernels. -/
theorem auxiliaryKernel_energy_identity (F : Family ι) (q : Finset ι → ℝ) :
    (∑ x ∈ F, ∑ y ∈ F, fourier q (x ∆ y) ^ 2) =
      (∑ y ∈ F, uniformInner (auxiliaryKernel F q y) (auxiliaryKernel F q y)) /
        Fintype.card (Finset ι) := by
  simp_rw [auxiliaryKernel_norm_sq]
  rw [← Finset.mul_sum,
    mul_div_cancel_left₀ _ (ne_of_gt (cube_card_pos (ι := ι))), Finset.sum_comm]

omit [DecidableEq ι] in
/-- A probability-unit function supported on `F` has unnormalized squared sum
`2^n` on `F`, as used immediately before equation (14). -/
theorem sum_sq_of_supported_unit (F : Family ι) (h : Finset ι → ℝ)
    (hh : ∀ x, x ∉ F → h x = 0) (hunit : uniformInner h h = 1) :
    ∑ x ∈ F, h x ^ 2 = (Fintype.card (Finset ι) : ℝ) := by
  have hsum : (∑ x ∈ F, h x ^ 2) = ∑ x, h x ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ F)
    intro x _ hx
    simp [hh x hx]
  rw [hsum]
  simp only [uniformInner, ← pow_two] at hunit
  exact (div_eq_one_iff_eq (ne_of_gt (cube_card_pos (ι := ι)))).mp hunit

/-- Equation (14): Bessel's inequality applied to the two auxiliary families
gives the sharp lower bound on the squared Fourier kernel restricted to `F × F`.
No positivity assumptions on `t` or nonemptiness assumptions on the families
are needed. -/
theorem auxiliaryKernel_bessel_bound (F G : Family ι)
    (hF : F.IsIncreasing) (hG : G.IsIncreasing) (t : ℝ) :
    t ^ 2 * (F \ G).card + (1 - t) ^ 2 * (F \ G.dual).card ≤
      ∑ x ∈ F, ∑ y ∈ F, (fourier (fun S => G.indicator S - t) (x ∆ y)) ^ 2 := by
  classical
  obtain ⟨u, v, huv, humem, hvmem⟩ := auxiliary_orthonormal_system F G hF hG
  have huunit (i) : uniformInner (u i) (u i) = 1 := by
    simpa using huv (Sum.inl i) (Sum.inl i)
  have hvunit (j) : uniformInner (v j) (v j) = 1 := by
    simpa using huv (Sum.inr j) (Sum.inr j)
  have hu_sq (i) : ∑ y ∈ F, u i y ^ 2 = (Fintype.card (Finset ι) : ℝ) :=
    sum_sq_of_supported_unit F _ (humem i).1 (huunit i)
  have hv_sq (j) : ∑ y ∈ F, v j y ^ 2 = (Fintype.card (Finset ι) : ℝ) :=
    sum_sq_of_supported_unit F _ (hvmem j).1 (hvunit j)
  have hpoint (y : Finset ι) :
      t ^ 2 * (∑ i, u i y ^ 2) + (1 - t) ^ 2 * (∑ j, v j y ^ 2) ≤
        (Fintype.card (Finset ι) : ℝ) *
          ∑ x ∈ F, (fourier (fun S => G.indicator S - t) (x ∆ y)) ^ 2 := by
    have hb := bessel_inequality (Sum.elim u v) huv
      (auxiliaryKernel F (fun S => G.indicator S - t) y)
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      auxiliaryKernel_inner_outside F G _ y t (humem _),
      auxiliaryKernel_inner_inside F G _ y t (hvmem _),
      mul_pow, neg_sq, ← Finset.mul_sum, auxiliaryKernel_norm_sq] at hb
    exact hb
  have hsum := Finset.sum_le_sum (fun y (_hy : y ∈ F) => hpoint y)
  have hleft :
      (∑ y ∈ F, (t ^ 2 * (∑ i, u i y ^ 2) + (1 - t) ^ 2 * (∑ j, v j y ^ 2))) =
        (Fintype.card (Finset ι) : ℝ) *
          (t ^ 2 * (F \ G).card + (1 - t) ^ 2 * (F \ G.dual).card) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_comm (s := F), Finset.sum_comm (s := F)]
    simp only [hu_sq, hv_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul]
    ring
  rw [hleft, ← Finset.mul_sum, Finset.sum_comm (s := F)] at hsum
  exact le_of_mul_le_mul_left hsum (cube_card_pos (ι := ι))

end Chvatal
