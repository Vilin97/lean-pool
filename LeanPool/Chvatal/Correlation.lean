/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/
module

public import LeanPool.Chvatal.Boolean
public import LeanPool.Chvatal.Counting
public import LeanPool.Chvatal.Kernel

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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
# The quadratic correlation inequality

This file follows Section 3.2 of arXiv:2609.19123: spectral flip energy is written
as a boundary sum, a constant is subtracted from the second function, and the
auxiliary orthonormal system bounds the resulting interior sum.
-/

public section

open scoped BigOperators symmDiff

noncomputable section

namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Summing against a family indicator restricts a sum to that family, as in (11). -/
theorem sum_indicator_mul (F : Family ι) (h : Finset ι → ℝ) :
    (∑ x, F.indicator x * h x) = ∑ x ∈ F, h x := by
  simp [Family.indicator, ite_mul]

/-- Summing a symmetric kernel against the squared change of an indicator counts
each boundary pair twice. This is the Boolean step in equation (11). -/
theorem indicator_boundary_sum (F : Family ι) (k : Finset ι → Finset ι → ℝ)
    (hk : ∀ x y, k x y = k y x) :
    (∑ x, ∑ y, (F.indicator x - F.indicator y) ^ 2 * k x y) =
      2 * ∑ x ∈ F, ∑ y ∈ Fᶜ, k x y := by
  have hpoint (x y : Finset ι) :
      (F.indicator x - F.indicator y) ^ 2 * k x y =
        F.indicator x * Fᶜ.indicator y * k x y +
          F.indicator y * Fᶜ.indicator x * k y x := by
    rw [hk y x]
    by_cases hx : x ∈ F <;> by_cases hy : y ∈ F <;>
      simp [Family.indicator, hx, hy]
  have hcross : (∑ x, ∑ y, F.indicator x * Fᶜ.indicator y * k x y) =
      ∑ x ∈ F, ∑ y ∈ Fᶜ, k x y := by
    simp_rw [mul_assoc, ← Finset.mul_sum, sum_indicator_mul]
  have hcross' : (∑ x, ∑ y, F.indicator y * Fᶜ.indicator x * k y x) =
      ∑ x ∈ F, ∑ y ∈ Fᶜ, k x y := by
    rw [Finset.sum_comm]
    exact hcross
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [hcross, hcross']
  ring

/-- Equation (11), its first equality: the odd-intersection spectral sum is one
half of the Fourier-weighted flip energy. -/
theorem two_spectral_eq_weighted_flip (f g : Finset ι → ℝ) :
    2 * (∑ T, ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
      fourier f S ^ 2 * fourier g T ^ 2) =
      (1 / 2 : ℝ) * ∑ T, fourier g T ^ 2 *
        cubeMean (fun x => (f x - f (x ∆ T)) ^ 2) := by
  simp_rw [flip_energy_odd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro S hS
  ring

/-- Equation (11), the boundary formula for a family indicator. -/
theorem two_spectral_eq_boundary (F : Family ι) (g : Finset ι → ℝ) :
    2 * (∑ T, ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
      fourier F.indicator S ^ 2 * fourier g T ^ 2) =
      (∑ x ∈ F, ∑ y ∈ Fᶜ, fourier g (x ∆ y) ^ 2) /
        Fintype.card (Finset ι) := by
  rw [two_spectral_eq_weighted_flip, weighted_flip_energy, cubeMean,
    indicator_boundary_sum F (fun x y => fourier g (x ∆ y) ^ 2)
      (fun x y => by rw [symmDiff_comm])]
  ring

/-- Equation (12): the Fourier kernel across a family boundary is unchanged
when a constant is subtracted from the function. -/
theorem boundary_sub_const (F : Family ι) (g : Finset ι → ℝ) (t : ℝ) :
    (∑ x ∈ F, ∑ y ∈ Fᶜ, fourier g (x ∆ y) ^ 2) =
      ∑ x ∈ F, ∑ y ∈ Fᶜ, fourier (fun z => g z - t) (x ∆ y) ^ 2 := by
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  have hne : x ∆ y ≠ ∅ := by
    intro h
    have hxy : x = y := (show x ∆ y = ∅ ↔ x = y from symmDiff_eq_bot).mp h
    subst y
    exact (Finset.mem_compl.mp hy) hx
  rw [fourier_sub, fourier_const, ite_eq_right hne, sub_zero]

/-- Reindexing the squared Fourier kernel gives the Parseval norm, the first
step in equation (13). -/
theorem sum_fourier_kernel_sq (g : Finset ι → ℝ) (x : Finset ι) :
    (∑ y, fourier g (x ∆ y) ^ 2) = cubeMean (fun z => g z ^ 2) := by
  rw [parseval]
  exact (show Function.Involutive (fun y : Finset ι => x ∆ y) from
    fun y => symmDiff_symmDiff_cancel_left x y).bijective.sum_comp
      (fun y => fourier g y ^ 2)

/-- Equation (13): boundary energy equals total energy minus interior energy. -/
theorem boundary_eq_total_sub_interior (F : Family ι) (g : Finset ι → ℝ) :
    (∑ x ∈ F, ∑ y ∈ Fᶜ, fourier g (x ∆ y) ^ 2) =
      F.card * cubeMean (fun z => g z ^ 2) -
        ∑ x ∈ F, ∑ y ∈ F, fourier g (x ∆ y) ^ 2 := by
  have hsplit (x : Finset ι) :
      (∑ y ∈ Fᶜ, fourier g (x ∆ y) ^ 2) +
        (∑ y ∈ F, fourier g (x ∆ y) ^ 2) = cubeMean (fun z => g z ^ 2) := by
    rw [Finset.sum_compl_add_sum, sum_fourier_kernel_sq]
  have h := congrArg (fun h : Finset ι → ℝ => ∑ x ∈ F, h x) (funext hsplit)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h
  linarith

omit [DecidableEq ι] in
/-- A shifted Boolean function's squared norm, used after equation (14). -/
theorem boolean_sub_const_norm {g : Finset ι → ℝ} (hg : IsBoolean g) (t : ℝ) :
    cubeMean (fun z => (g z - t) ^ 2) =
      (1 - t) ^ 2 * cubeMean g + t ^ 2 * (1 - cubeMean g) := by
  have hp (z : Finset ι) : (g z - t) ^ 2 =
      (1 - t) ^ 2 * g z + t ^ 2 * (1 - g z) := by
    rcases hg z with hz | hz <;> rw [hz] <;> ring
  simp_rw [hp]
  rw [cubeMean_add, cubeMean_mul_left, cubeMean_mul_left, cubeMean_sub, cubeMean_const]

/-- The density of a family difference is the difference of the corresponding
indicator means, used to convert equation (14) into covariance. -/
theorem card_sdiff_div_cube (F G : Family ι) :
    ((F \ G).card : ℝ) / Fintype.card (Finset ι) =
      cubeMean F.indicator - cubeMean (fun x => F.indicator x * G.indicator x) := by
  rw [← Family.indicator_inter, Family.cubeMean_indicator, Family.cubeMean_indicator,
    ← sub_div]
  congr 1
  have h : ((F \ G).card : ℝ) + (F ∩ G).card = F.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter F G
  linarith

/-- The final algebra in Section 3.2: the total shifted norm minus the two
auxiliary-family dimensions equals a quadratic combination of covariances. -/
theorem shifted_dimension_covariance (F G : Family ι) (t : ℝ) :
    (F.card * cubeMean (fun z => (G.indicator z - t) ^ 2) -
      (t ^ 2 * (F \ G).card + (1 - t) ^ 2 * (F \ G.dual).card)) /
        Fintype.card (Finset ι) =
      t ^ 2 * covariance F.indicator G.indicator +
        (1 - t) ^ 2 * covariance F.indicator (dual G.indicator) := by
  rw [boolean_sub_const_norm (Family.isBoolean_indicator G)]
  simp only [sub_div, add_div]
  simp_rw [mul_div_assoc]
  rw [card_sdiff_div_cube, card_sdiff_div_cube, Family.indicator_dual]
  have he (a : ℝ) : (F.card : ℝ) * (a / Fintype.card (Finset ι)) =
      cubeMean F.indicator * a := by
    rw [Family.cubeMean_indicator]
    ring
  rw [he]
  unfold covariance
  rw [cubeMean_dual]
  ring

/-- The last step of Section 3.2, isolating how the interior-kernel estimate (14)
combines with the boundary identities (11)–(13). -/
theorem two_spectral_le_of_interior_bound (F G : Family ι) (t : ℝ)
    (hinterior : t ^ 2 * (F \ G).card + (1 - t) ^ 2 * (F \ G.dual).card ≤
      ∑ x ∈ F, ∑ y ∈ F, fourier (fun z => G.indicator z - t) (x ∆ y) ^ 2) :
    2 * (∑ T, ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
      fourier F.indicator S ^ 2 * fourier G.indicator T ^ 2) ≤
      t ^ 2 * covariance F.indicator G.indicator +
        (1 - t) ^ 2 * covariance F.indicator (dual G.indicator) := by
  rw [two_spectral_eq_boundary, boundary_sub_const F G.indicator t,
    boundary_eq_total_sub_interior, ← shifted_dimension_covariance]
  exact div_le_div_of_nonneg_right (sub_le_sub_left hinterior _)
    (le_of_lt (cube_card_pos (ι := ι)))

/-- Theorem 1.4, equation (3): for every real `t`, twice the odd-intersection
Fourier energy is bounded by the indicated quadratic combination of covariances.
The proof includes empty supports and an empty coordinate type. -/
theorem two_spectral_le_quadratic_covariance {f g : Finset ι → ℝ}
    (hf : IsBoolean f) (hmf : Monotone f) (hg : IsBoolean g) (hmg : Monotone g)
    (t : ℝ) :
    2 * (∑ T, ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
      fourier f S ^ 2 * fourier g T ^ 2) ≤
      t ^ 2 * covariance f g + (1 - t) ^ 2 * covariance f (dual g) := by
  have h := two_spectral_le_of_interior_bound (Family.oneSupport f) (Family.oneSupport g) t
    (auxiliaryKernel_bessel_bound (Family.oneSupport f) (Family.oneSupport g)
      (Family.isIncreasing_oneSupport hf hmf) (Family.isIncreasing_oneSupport hg hmg) t)
  simpa only [Family.indicator_oneSupport hf, Family.indicator_oneSupport hg] using h

end Chvatal
