/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvatal formalization contributors
-/
module

public import LeanPool.Chvatal.Fourier
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
# Boolean functions and coordinate influences

This file formalizes the influence convention in Section 2, equation (6), and the
influence comparison of Lemma 3.3 of Chang–Liu–Liu, arXiv:2609.19123v1.
Boolean functions are real-valued functions with an explicit `IsBoolean` hypothesis;
this makes their Fourier transforms ordinary real-valued transforms. Increasing
functions use mathlib's `Monotone` predicate on finite subsets ordered by inclusion.
-/

public section

open scoped BigOperators symmDiff

noncomputable section

namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Section 2: a real-valued cube function is Boolean when every value is zero or one. -/
@[expose] def IsBoolean (f : Finset ι → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

/-- The sign `2xᵢ - 1` used in the influence identity (6). -/
@[expose] def coordinateSign (i : ι) (x : Finset ι) : ℝ := if i ∈ x then 1 else -1

/-- Section 2: influence, written as mean squared change under a single-coordinate flip.
For Boolean functions this is the probability that the value changes; see
`influence_eq_mean_indicator`. -/
@[expose] def influence (f : Finset ι → ℝ) (i : ι) : ℝ :=
  cubeMean (fun x => (f x - f (x ∆ {i})) ^ 2)

/-- The Boolean duality operation of Section 2 preserves Boolean values. -/
theorem IsBoolean.dual {f : Finset ι → ℝ} (hf : IsBoolean f) : IsBoolean (dual f) := by
  intro x
  rcases hf xᶜ with h | h
  · right; simp [Chvatal.dual, h]
  · left; simp [Chvatal.dual, h]

/-- The duality operation of Section 2 preserves monotonicity. -/
theorem monotone_dual {f : Finset ι → ℝ} (hf : Monotone f) : Monotone (dual f) := by
  intro x y hxy
  exact sub_le_sub_left (hf (compl_le_compl hxy)) 1

omit [Fintype ι] [DecidableEq ι] in
/-- Boolean values lie in the unit interval; used in the pointwise estimates of Section 3. -/
theorem IsBoolean.nonneg {f : Finset ι → ℝ} (hf : IsBoolean f) (x : Finset ι) :
    0 ≤ f x := by rcases hf x with h | h <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
/-- Squaring a Boolean value leaves it unchanged, as used in Parseval's variance formula. -/
theorem IsBoolean.sq {f : Finset ι → ℝ} (hf : IsBoolean f) (x : Finset ι) :
    f x ^ 2 = f x := by rcases hf x with h | h <;> simp [h]

/-- For Boolean functions the squared-change definition equals the probability definition
of influence in Section 2. -/
theorem influence_eq_mean_indicator {f : Finset ι → ℝ} (hf : IsBoolean f) (i : ι) :
    influence f i = cubeMean (fun x => if f x ≠ f (x ∆ {i}) then 1 else 0) := by
  unfold influence
  congr 1
  funext x
  rcases hf x with h | h <;> rcases hf (x ∆ {i}) with k | k <;> simp [h, k]

/-- Influences are nonnegative, including in the degenerate cases of Theorem 1.2. -/
theorem influence_nonneg (f : Finset ι → ℝ) (i : ι) : 0 ≤ influence f i :=
  cubeMean_nonneg fun _ => sq_nonneg _

omit [Fintype ι] in
/-- Flipping a set containing `i` reverses `2xᵢ - 1`, as in the proof of Lemma 3.3. -/
theorem coordinateSign_symmDiff {T : Finset ι} {i : ι} (hi : i ∈ T) (x : Finset ι) :
    coordinateSign i (x ∆ T) = -coordinateSign i x := by
  by_cases hx : i ∈ x <;> simp [coordinateSign, Finset.mem_symmDiff, hi, hx]

/-- The change of variables in the proof of Lemma 3.3 negates the signed mean. -/
theorem signed_mean_flip {T : Finset ι} {i : ι} (hi : i ∈ T) (f : Finset ι → ℝ) :
    cubeMean (fun x => coordinateSign i x * f (x ∆ T)) =
      -cubeMean (fun x => coordinateSign i x * f x) := by
  calc
    _ = cubeMean (fun x => coordinateSign i (x ∆ T) * f ((x ∆ T) ∆ T)) :=
      (cubeMean_symmDiff (fun x => coordinateSign i x * f (x ∆ T)) T).symm
    _ = -cubeMean (fun x => coordinateSign i x * f x) := by
      simp_rw [coordinateSign_symmDiff hi, symmDiff_symmDiff_cancel_right, neg_mul]
      exact cubeMean_neg _

/-- The signed difference formula in the proof of Lemma 3.3, before using Boolean values. -/
theorem signed_mean_difference {T : Finset ι} {i : ι} (hi : i ∈ T)
    (f : Finset ι → ℝ) :
    cubeMean (fun x => coordinateSign i x * (f x - f (x ∆ T))) =
      2 * cubeMean (fun x => coordinateSign i x * f x) := by
  simp_rw [mul_sub]
  rw [cubeMean_sub, signed_mean_flip hi]
  ring

omit [Fintype ι] in
/-- Equation (6), pointwise form: monotonicity fixes the sign of a single-coordinate change. -/
theorem flip_sq_eq_signed_difference {f : Finset ι → ℝ} (hf : IsBoolean f)
    (hm : Monotone f) (i : ι) (x : Finset ι) :
    (f x - f (x ∆ {i})) ^ 2 = coordinateSign i x * (f x - f (x ∆ {i})) := by
  by_cases hi : i ∈ x
  · have hs : x ∆ {i} ⊆ x := by
      intro j hj
      simp only [Finset.mem_symmDiff, Finset.mem_singleton] at hj
      rcases hj with h | h
      · exact h.1
      · exact h.1 ▸ hi
    have hle := hm hs
    rcases hf x with h | h <;> rcases hf (x ∆ {i}) with k | k <;>
      simp_all [coordinateSign]
    linarith
  · have hs : x ⊆ x ∆ {i} := by
      intro j hj
      simp only [Finset.mem_symmDiff, Finset.mem_singleton]
      exact Or.inl ⟨hj, fun h => hi (h ▸ hj)⟩
    have hle := hm hs
    rcases hf x with h | h <;> rcases hf (x ∆ {i}) with k | k <;>
      simp_all [coordinateSign]
    linarith

/-- Equation (6): influence of an increasing Boolean function equals twice its signed mean. -/
theorem influence_eq_signed_mean {f : Finset ι → ℝ} (hf : IsBoolean f)
    (hm : Monotone f) (i : ι) :
    influence f i = 2 * cubeMean (fun x => coordinateSign i x * f x) := by
  unfold influence
  simp_rw [flip_sq_eq_signed_difference hf hm]
  exact signed_mean_difference (Finset.mem_singleton_self i) f

omit [Fintype ι] in
/-- The pointwise Boolean estimate in Lemma 3.3: a signed change is at most its square. -/
theorem signed_difference_le_sq {f : Finset ι → ℝ} (hf : IsBoolean f)
    (i : ι) (x y : Finset ι) :
    coordinateSign i x * (f x - f y) ≤ (f x - f y) ^ 2 := by
  rcases hf x with h | h <;> rcases hf y with k | k <;>
    by_cases hi : i ∈ x <;> simp [coordinateSign, h, k, hi]

/-- Lemma 3.3, inequality in (15), for each coordinate in the flipped set.
Taking the maximum over these coordinates gives exactly the paper's formulation. -/
theorem influence_le_flip_energy {f : Finset ι → ℝ} (hf : IsBoolean f)
    (hm : Monotone f) {T : Finset ι} {i : ι} (hi : i ∈ T) :
    influence f i ≤ cubeMean (fun x => (f x - f (x ∆ T)) ^ 2) := by
  rw [influence_eq_signed_mean hf hm, ← signed_mean_difference hi]
  exact cubeMean_mono fun x => signed_difference_le_sq hf i x _

/-- Corollary 1.3: an antipodal Boolean function has mean one half. -/
theorem mean_eq_half_of_antipodal {g : Finset ι → ℝ} (hg : dual g = g) :
    cubeMean g = 1 / 2 := by
  have h := cubeMean_dual g
  rw [hg] at h
  linarith

/-- Corollary 1.3: an antipodal Boolean function has variance one quarter. -/
theorem variance_eq_quarter_of_antipodal {g : Finset ι → ℝ} (hb : IsBoolean g)
    (hg : dual g = g) : covariance g g = 1 / 4 := by
  have hs : (fun x => g x * g x) = g := by
    funext x
    simpa [pow_two] using hb.sq x
  rw [covariance, hs, mean_eq_half_of_antipodal hg]
  norm_num

end Chvatal
