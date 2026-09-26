/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvatal formalization contributors
-/
module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import Mathlib.Tactic.NormNum

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
# Fourier–Walsh analysis on the finite Boolean cube

This file develops the normalized Fourier–Walsh conventions used in Section 2 of
arXiv:2609.19123. A point of the cube is its set of coordinates equal to one.
-/

public section

open scoped BigOperators symmDiff

noncomputable section

namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Uniform expectation on the Boolean cube, as in the preliminaries of the paper. -/
@[expose] def cubeMean (f : Finset ι → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card (Finset ι)

/-- The Walsh character indexed by `S`, denoted `χ_S` in the paper. -/
def walsh (S x : Finset ι) : ℝ := (-1 : ℝ) ^ (S ∩ x).card

/-- The normalized Fourier coefficient `f̂(S)` of Section 2. -/
@[expose] def fourier (f : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  cubeMean (fun x => f x * walsh S x)

/-- Covariance with respect to uniform measure, as used in the main theorem. -/
@[expose] def covariance (f g : Finset ι → ℝ) : ℝ :=
  cubeMean (fun x => f x * g x) - cubeMean f * cubeMean g

/-- The dual Boolean function `f*(x) = 1 - f(1-x)` in the paper. -/
@[expose] def dual (f : Finset ι → ℝ) (x : Finset ι) : ℝ := 1 - f xᶜ

omit [DecidableEq ι] in
/-- The cube has positive cardinality, including when its coordinate set is empty. -/
theorem cube_card_pos : (0 : ℝ) < Fintype.card (Finset ι) := by
  exact_mod_cast Fintype.card_pos

omit [DecidableEq ι] in
/-- Uniform expectation preserves constants; this fixes the normalization in Section 2. -/
@[simp] theorem cubeMean_const (c : ℝ) : cubeMean (fun _ : Finset ι => c) = c := by
  simp [cubeMean]

omit [DecidableEq ι] in
/-- Additivity of the expectation used throughout the Fourier calculations. -/
theorem cubeMean_add (f g : Finset ι → ℝ) :
    cubeMean (fun x => f x + g x) = cubeMean f + cubeMean g := by
  simp [cubeMean, Finset.sum_add_distrib, add_div]

omit [DecidableEq ι] in
/-- Subtractivity of the expectation used throughout the Fourier calculations. -/
theorem cubeMean_sub (f g : Finset ι → ℝ) :
    cubeMean (fun x => f x - g x) = cubeMean f - cubeMean g := by
  simp [cubeMean, Finset.sum_sub_distrib, sub_div]

omit [DecidableEq ι] in
/-- Scalar linearity of expectation, used for the Fourier identities in Section 2. -/
theorem cubeMean_mul_left (c : ℝ) (f : Finset ι → ℝ) :
    cubeMean (fun x => c * f x) = c * cubeMean f := by
  simp [cubeMean, ← Finset.mul_sum, mul_div_assoc]

omit [DecidableEq ι] in
/-- Right scalar linearity of expectation, a companion to `cubeMean_mul_left`. -/
theorem cubeMean_mul_right (f : Finset ι → ℝ) (c : ℝ) :
    cubeMean (fun x => f x * c) = cubeMean f * c := by
  simpa [mul_comm] using cubeMean_mul_left c f

omit [DecidableEq ι] in
/-- Negation commutes with expectation, as used in Fourier coefficient calculations. -/
@[simp] theorem cubeMean_neg (f : Finset ι → ℝ) :
    cubeMean (fun x => -f x) = -cubeMean f := by
  simpa using cubeMean_mul_left (-1) f

omit [DecidableEq ι] in
/-- Expectation commutes with finite sums; this is used in Fourier inversion. -/
theorem cubeMean_sum {κ : Type*} (s : Finset κ) (f : κ → Finset ι → ℝ) :
    cubeMean (fun x => ∑ k ∈ s, f k x) = ∑ k ∈ s, cubeMean (f k) := by
  simp only [cubeMean, Finset.sum_div]
  exact Finset.sum_comm

/-- The uniform cube distribution is invariant under translation by symmetric difference. -/
theorem cubeMean_symmDiff (f : Finset ι → ℝ) (S : Finset ι) :
    cubeMean (fun x => f (x ∆ S)) = cubeMean f := by
  unfold cubeMean
  congr 1
  apply Function.Bijective.sum_comp
  exact (show Function.Involutive (fun x : Finset ι => x ∆ S) from
    fun x => symmDiff_symmDiff_cancel_right S x).bijective

/-- Complementation preserves uniform expectation; used in the duality identities. -/
theorem cubeMean_compl (f : Finset ι → ℝ) :
    cubeMean (fun x => f xᶜ) = cubeMean f := by
  unfold cubeMean
  congr 1
  exact (show Function.Involutive (fun x : Finset ι => xᶜ) from compl_compl).bijective.sum_comp f

/-- The mean of the dual function, recorded in the paper's preliminaries. -/
@[simp] theorem cubeMean_dual (f : Finset ι → ℝ) :
    cubeMean (dual f) = 1 - cubeMean f := by
  unfold dual
  rw [cubeMean_sub, cubeMean_const, cubeMean_compl]

omit [Fintype ι] in
/-- The empty Walsh character is the constant one function (Section 2). -/
@[simp] theorem walsh_empty (x : Finset ι) : walsh ∅ x = 1 := by simp [walsh]

omit [Fintype ι] in
/-- Evaluating a character at the origin gives one (Section 2). -/
@[simp] theorem walsh_apply_empty (S : Finset ι) : walsh S ∅ = 1 := by simp [walsh]

omit [Fintype ι] in
/-- The symmetry of the Walsh kernel allows inversion to use the same transform. -/
theorem walsh_comm (S x : Finset ι) : walsh S x = walsh x S := by
  simp [walsh, Finset.inter_comm]

/-- The empty Fourier coefficient is the uniform mean, in the convention of Section 2. -/
@[simp] theorem fourier_empty (f : Finset ι → ℝ) : fourier f ∅ = cubeMean f := by
  simp [fourier]

omit [Fintype ι] in
/-- Inserting a coordinate multiplies a Walsh character by that coordinate's sign. -/
theorem walsh_insert {i : ι} {S : Finset ι} (hi : i ∉ S) (x : Finset ι) :
    walsh (insert i S) x = (if i ∈ x then -1 else 1) * walsh S x := by
  by_cases hx : i ∈ x
  · simp [walsh, Finset.insert_inter_of_mem hx, Finset.card_insert_of_notMem,
      hi, hx, pow_succ, mul_comm]
  · simp [walsh, Finset.insert_inter_of_notMem hx, hx]

omit [Fintype ι] in
/-- The character multiplication law in the cube variable, used in Section 2. -/
theorem walsh_symmDiff_right (S x y : Finset ι) :
    walsh S (x ∆ y) = walsh S x * walsh S y := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [walsh_insert hi, walsh_insert hi, walsh_insert hi, ih]
    by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;>
      simp [Finset.mem_symmDiff, hx, hy]

omit [Fintype ι] in
/-- The product of characters is indexed by symmetric difference, as in Section 2. -/
theorem walsh_symmDiff_left (S T x : Finset ι) :
    walsh (S ∆ T) x = walsh S x * walsh T x := by
  simpa only [walsh_comm] using walsh_symmDiff_right x S T

omit [Fintype ι] in
/-- Every Walsh character has square one, as needed for Parseval's identity. -/
@[simp] theorem walsh_sq (S x : Finset ι) : walsh S x ^ 2 = 1 := by
  rw [pow_two, ← walsh_symmDiff_left]
  simp

omit [Fintype ι] in
/-- A singleton character is the sign of its single cube coordinate. -/
theorem walsh_singleton (i : ι) (x : Finset ι) :
    walsh {i} x = if i ∈ x then -1 else 1 := by
  simpa using walsh_insert (S := ∅) (by simp) x

omit [Fintype ι] in
/-- Toggling a coordinate in a character's support reverses its sign. -/
theorem walsh_toggle {S : Finset ι} {i : ι} (hi : i ∈ S) (x : Finset ι) :
    walsh S (x ∆ {i}) = -walsh S x := by
  rw [walsh_symmDiff_right, walsh_comm S {i}, walsh_singleton]
  simp [hi]

/-- Every nonconstant Walsh character has mean zero, the orthogonality input of Section 2. -/
theorem cubeMean_walsh_of_nonempty {S : Finset ι} (hS : S.Nonempty) :
    cubeMean (walsh S) = 0 := by
  obtain ⟨i, hi⟩ := hS
  have h := cubeMean_symmDiff (walsh S) {i}
  simp only [walsh_toggle hi, cubeMean_neg] at h
  linarith

/-- The uniform mean of a Walsh character is the Kronecker delta at the empty set. -/
theorem cubeMean_walsh (S : Finset ι) :
    cubeMean (walsh S) = if S = ∅ then 1 else 0 := by
  by_cases hS : S = ∅
  · subst S; simp [cubeMean, walsh]
  · simp [hS, cubeMean_walsh_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hS)]

/-- Orthogonality of the Walsh basis, stated in the paper's normalized inner product. -/
theorem walsh_orthogonality (S T : Finset ι) :
    cubeMean (fun x => walsh S x * walsh T x) = if S = T then 1 else 0 := by
  simp_rw [← walsh_symmDiff_left]
  rw [cubeMean_walsh]
  have h : S ∆ T = ∅ ↔ S = T := symmDiff_eq_bot
  simp only [h]

/-- Multiplying by a character shifts the Fourier index, as used in Lemma 2.2. -/
theorem fourier_mul_walsh (f : Finset ι → ℝ) (S T : Finset ι) :
    fourier (fun x => f x * walsh T x) S = fourier f (S ∆ T) := by
  unfold fourier
  congr 1
  funext x
  rw [walsh_symmDiff_left]
  ring

/-- A function independent of coordinate `i` has no Fourier coefficient containing `i`.
This is the support argument for the monomials in Lemma 2.2. -/
theorem fourier_eq_zero_of_invariant (f : Finset ι → ℝ) {S : Finset ι} {i : ι}
    (hi : i ∈ S) (hf : ∀ x, f (x ∆ {i}) = f x) : fourier f S = 0 := by
  have h := cubeMean_symmDiff (fun x => f x * walsh S x) {i}
  simp only [hf, walsh_toggle hi, mul_neg, cubeMean_neg] at h
  unfold fourier
  linarith

/-- Summing the Walsh kernel gives a scaled Kronecker delta, the inversion kernel. -/
theorem sum_walsh_kernel (x y : Finset ι) :
    (∑ S, walsh S x * walsh S y) =
      if x = y then (Fintype.card (Finset ι) : ℝ) else 0 := by
  have h := walsh_orthogonality x y
  unfold cubeMean at h
  rw [div_eq_iff (ne_of_gt (cube_card_pos (ι := ι)))] at h
  simpa only [walsh_comm, ite_mul, one_mul, zero_mul] using h

/-- Fourier inversion on the Boolean cube, the expansion used throughout Section 2. -/
theorem fourier_inversion (f : Finset ι → ℝ) (x : Finset ι) :
    (∑ S, fourier f S * walsh S x) = f x := by
  calc
    (∑ S, fourier f S * walsh S x) =
        (∑ y, f y * ∑ S, walsh S y * walsh S x) /
          Fintype.card (Finset ι) := by
      simp only [fourier, cubeMean, div_mul_eq_mul_div, Finset.sum_div,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ = f x := by
      simp_rw [sum_walsh_kernel]
      simp [mul_ite]

/-- Parseval's identity for two real cube functions, as recalled in Section 2. -/
theorem parseval_inner (f g : Finset ι → ℝ) :
    cubeMean (fun x => f x * g x) = ∑ S, fourier f S * fourier g S := by
  calc
    cubeMean (fun x => f x * g x) =
        cubeMean (fun x => ∑ S, fourier g S * (f x * walsh S x)) := by
      congr 1
      funext x
      rw [← fourier_inversion g x, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ = ∑ S, fourier f S * fourier g S := by
      rw [cubeMean_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [cubeMean_mul_left]
      exact mul_comm (fourier g S) (fourier f S)

/-- The sum-of-squares form of Parseval's identity in Section 2. -/
theorem parseval (f : Finset ι → ℝ) :
    cubeMean (fun x => f x ^ 2) = ∑ S, fourier f S ^ 2 := by
  simpa only [pow_two] using parseval_inner f f

/-- The transform preserves addition, used in the constant-coefficient adjustment. -/
theorem fourier_add (f g : Finset ι → ℝ) (S : Finset ι) :
    fourier (fun x => f x + g x) S = fourier f S + fourier g S := by
  simp only [fourier, add_mul, cubeMean_add]

/-- The transform preserves subtraction, used in the constant-coefficient adjustment. -/
theorem fourier_sub (f g : Finset ι → ℝ) (S : Finset ι) :
    fourier (fun x => f x - g x) S = fourier f S - fourier g S := by
  simp only [fourier, sub_mul, cubeMean_sub]

/-- A constant has only its empty Fourier coefficient, as in the Section 2 convention. -/
theorem fourier_const (c : ℝ) (S : Finset ι) :
    fourier (fun _ : Finset ι => c) S = if S = ∅ then c else 0 := by
  rw [fourier, cubeMean_mul_left, cubeMean_walsh]
  split_ifs <;> simp

/-- Subtracting the mean removes exactly the constant Fourier coefficient. -/
theorem fourier_sub_mean (f : Finset ι → ℝ) (S : Finset ι) :
    fourier (fun x => f x - cubeMean f) S =
      if S = ∅ then 0 else fourier f S := by
  rw [fourier_sub, fourier_const]
  split_ifs with h
  · subst S; simp
  · simp

/-- The Fourier transform is injective, a direct consequence of the inversion formula. -/
theorem fourier_injective : Function.Injective (fourier (ι := ι)) := by
  intro f g h
  funext x
  rw [← fourier_inversion f x, ← fourier_inversion g x, h]

/-- Complementation multiplies a Walsh character by the parity of its index. -/
theorem walsh_compl (S x : Finset ι) :
    walsh S xᶜ = (-1 : ℝ) ^ S.card * walsh S x := by
  have hx : xᶜ = x ∆ Finset.univ := by
    ext i
    simp [Finset.mem_symmDiff]
  rw [hx, walsh_symmDiff_right]
  simp [walsh, mul_comm]

/-- Complementing the argument multiplies Fourier coefficients by index parity. -/
theorem fourier_compl (f : Finset ι → ℝ) (S : Finset ι) :
    fourier (fun x => f xᶜ) S = (-1 : ℝ) ^ S.card * fourier f S := by
  have h := cubeMean_compl (fun x => f x * walsh S xᶜ)
  simp only [compl_compl] at h
  unfold fourier
  rw [h]
  simp_rw [walsh_compl, ← mul_assoc, mul_comm (f _), mul_assoc]
  rw [cubeMean_mul_left]
  simp [mul_comm]

/-- The nonconstant Fourier coefficients of the dual, recalled in Section 2. -/
theorem fourier_dual_of_nonempty (f : Finset ι → ℝ) {S : Finset ι}
    (hS : S.Nonempty) :
    fourier (dual f) S = -((-1 : ℝ) ^ S.card * fourier f S) := by
  unfold dual
  rw [fourier_sub, fourier_const, fourier_compl]
  simp [hS.ne_empty]

/-- Covariance is the sum of the products of the nonconstant Fourier coefficients. -/
theorem covariance_fourier (f g : Finset ι → ℝ) :
    covariance f g = ∑ S ∈ Finset.univ.erase ∅, fourier f S * fourier g S := by
  rw [covariance, parseval_inner]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset ι)))
    (fun S => fourier f S * fourier g S) (by simp : (∅ : Finset ι) ∈ Finset.univ)
  simp only [fourier_empty] at h
  linarith

/-- The alternating Fourier expression for covariance with the dual, used in Theorem 1.2. -/
theorem covariance_dual_fourier (f : Finset ι → ℝ) :
    covariance f (dual f) = ∑ S ∈ Finset.univ.erase ∅,
      -(-1 : ℝ) ^ S.card * fourier f S ^ 2 := by
  rw [covariance_fourier]
  apply Finset.sum_congr rfl
  intro S hS
  rw [fourier_dual_of_nonempty f
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1)]
  ring

omit [DecidableEq ι] in
/-- Pointwise nonnegativity implies nonnegative uniform expectation. -/
theorem cubeMean_nonneg {f : Finset ι → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cubeMean f := by
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x)
    (le_of_lt (cube_card_pos (ι := ι)))

omit [DecidableEq ι] in
/-- Pointwise comparison implies comparison of uniform expectations. -/
theorem cubeMean_mono {f g : Finset ι → ℝ} (h : ∀ x, f x ≤ g x) :
    cubeMean f ≤ cubeMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x)
    (le_of_lt (cube_card_pos (ι := ι)))

/-- Translating a cube function multiplies each Fourier coefficient by the character
of the translation vector; this is the spectral step in equation (10). -/
theorem fourier_symmDiff (f : Finset ι → ℝ) (S T : Finset ι) :
    fourier (fun x => f (x ∆ T)) S = walsh S T * fourier f S := by
  have h := cubeMean_symmDiff (fun x => f x * walsh S (x ∆ T)) T
  simp only [symmDiff_symmDiff_cancel_right] at h
  unfold fourier
  rw [h]
  simp_rw [walsh_symmDiff_right, ← mul_assoc]
  rw [cubeMean_mul_right]
  ring

/-- Equation (10), first equality: the energy of a simultaneous coordinate flip
is the Fourier energy weighted by the squared character difference. -/
theorem flip_energy_fourier (f : Finset ι → ℝ) (T : Finset ι) :
    cubeMean (fun x => (f x - f (x ∆ T)) ^ 2) =
      ∑ S, (1 - walsh S T) ^ 2 * fourier f S ^ 2 := by
  rw [parseval]
  apply Finset.sum_congr rfl
  intro S hS
  rw [fourier_sub, fourier_symmDiff]
  ring

omit [Fintype ι] in
/-- The elementary parity computation behind equation (10). -/
theorem walsh_flip_factor (S T : Finset ι) :
    (1 - walsh S T) ^ 2 = if Odd (S ∩ T).card then 4 else 0 := by
  unfold walsh
  by_cases h : Odd (S ∩ T).card
  · norm_num [h, h.neg_one_pow]
  · have he : Even (S ∩ T).card := Nat.not_odd_iff_even.mp h
    simp [h, he.neg_one_pow]

/-- Equation (10), second equality: only Fourier sets meeting the flipped set
in an odd number of coordinates contribute to the flip energy. -/
theorem flip_energy_odd (f : Finset ι → ℝ) (T : Finset ι) :
    cubeMean (fun x => (f x - f (x ∆ T)) ^ 2) =
      4 * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
        fourier f S ^ 2 := by
  rw [flip_energy_fourier, Finset.mul_sum]
  simp_rw [walsh_flip_factor, Finset.sum_filter, ite_mul, zero_mul]

/-- The change of variables `y = x ∆ T` in equation (11), before specializing
`f` to an indicator. Both sides retain the paper's factor of one half. -/
theorem weighted_flip_energy (f g : Finset ι → ℝ) :
    (1 / 2 : ℝ) * ∑ T, fourier g T ^ 2 *
      cubeMean (fun x => (f x - f (x ∆ T)) ^ 2) =
    (1 / 2 : ℝ) * cubeMean (fun x =>
      ∑ y, (f x - f y) ^ 2 * fourier g (x ∆ y) ^ 2) := by
  congr 1
  simp_rw [← cubeMean_mul_left]
  rw [← cubeMean_sum]
  congr 1
  funext x
  calc
    (∑ T, fourier g T ^ 2 * (f x - f (x ∆ T)) ^ 2) =
        ∑ T, (f x - f (x ∆ T)) ^ 2 * fourier g (x ∆ (x ∆ T)) ^ 2 := by
      simp only [symmDiff_symmDiff_cancel_left, mul_comm]
    _ = ∑ y, (f x - f y) ^ 2 * fourier g (x ∆ y) ^ 2 := by
      exact (show Function.Involutive (fun y : Finset ι => x ∆ y) from
        fun y => symmDiff_symmDiff_cancel_left x y).bijective.sum_comp
        (fun y => (f x - f y) ^ 2 * fourier g (x ∆ y) ^ 2)

end Chvatal
