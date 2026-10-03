/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvatal formalization contributors
-/
module

public import LeanPool.Chvatal.Boolean
public import LeanPool.Chvatal.Optimization
public import Mathlib.Data.Finset.Max

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
# Ordered influence weights in the sharp correlation inequality

This file defines the left-hand side `𝒲(f,g)` of Theorem 1.2 and proves the
comparison (16) from Lemma 3.3. It also records the variance argument in
Corollary 1.3. The parameter optimization is in `Chvatal.Optimization`.
-/

public section

open scoped BigOperators symmDiff

noncomputable section

namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The largest influence over a Fourier index, as in Theorem 1.2.
The empty index is assigned zero so that sums can run over the entire cube. -/
def maxInfluence (f : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  if h : S.Nonempty then S.sup' h (influence f) else 0

/-- The empty Fourier index makes no contribution to Theorem 1.2. -/
@[simp] theorem maxInfluence_empty (f : Finset ι → ℝ) : maxInfluence f ∅ = 0 := by
  simp [maxInfluence]

/-- On a nonempty index, the influence weight is the ordinary finite maximum. -/
theorem maxInfluence_of_nonempty (f : Finset ι → ℝ) {S : Finset ι} (hS : S.Nonempty) :
    maxInfluence f S = S.sup' hS (influence f) := by simp [maxInfluence, hS]

/-- Every coordinate in an index is bounded by its maximum influence. -/
theorem influence_le_maxInfluence (f : Finset ι → ℝ) {S : Finset ι} {i : ι}
    (hi : i ∈ S) : influence f i ≤ maxInfluence f S := by
  rw [maxInfluence_of_nonempty f ⟨i, hi⟩]
  exact Finset.le_sup' (influence f) hi

/-- The spectral weights in Theorem 1.2 are nonnegative. -/
theorem maxInfluence_nonneg (f : Finset ι → ℝ) (S : Finset ι) : 0 ≤ maxInfluence f S := by
  by_cases hS : S.Nonempty
  · obtain ⟨i, hi⟩ := hS
    exact (influence_nonneg f i).trans (influence_le_maxInfluence f hi)
  · simp [maxInfluence, hS]

/-- Lemma 3.3 in its stated maximum-over-coordinates form. -/
theorem maxInfluence_le_flip_energy {f : Finset ι → ℝ} (hf : IsBoolean f)
    (hm : Monotone f) (T : Finset ι) :
    maxInfluence f T ≤ cubeMean (fun x => (f x - f (x ∆ T)) ^ 2) := by
  by_cases hT : T.Nonempty
  · rw [maxInfluence_of_nonempty f hT, Finset.sup'_le_iff]
    intro i hi
    exact influence_le_flip_energy hf hm hi
  · rw [maxInfluence, dite_eq_right hT]
    exact cubeMean_nonneg fun _ => sq_nonneg _

/-- Lemma 3.3, equation (15): maximum influence is bounded by the odd-intersection
Fourier energy. The formula also holds for the empty index under our zero convention. -/
theorem maxInfluence_le_odd_spectral {f : Finset ι → ℝ} (hf : IsBoolean f)
    (hm : Monotone f) (T : Finset ι) :
    maxInfluence f T ≤ 4 * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
      fourier f S ^ 2 := by
  rw [← flip_energy_odd]
  exact maxInfluence_le_flip_energy hf hm T

/-- The spectral expression `𝒲(f,g)` in Theorem 1.2 and Section 5.
Its empty-index term vanishes by `maxInfluence_empty`. -/
def spectralWeight (f g : Finset ι → ℝ) : ℝ :=
  ∑ S, fourier g S ^ 2 * maxInfluence f S

/-- The expression `spectralWeight` agrees with the paper's sum over nonempty indices. -/
theorem spectralWeight_eq_sum_nonempty (f g : Finset ι → ℝ) :
    spectralWeight f g = ∑ S ∈ Finset.univ.erase (∅ : Finset ι),
      fourier g S ^ 2 * maxInfluence f S := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (Finset ι))
    (fun S => fourier g S ^ 2 * maxInfluence f S) (Finset.mem_univ (∅ : Finset ι))
  simp only [maxInfluence_empty, mul_zero, add_zero] at h
  exact h.symm

/-- Nonnegativity of the left side of Theorem 1.2, used when a covariance vanishes. -/
theorem spectralWeight_nonneg (f g : Finset ι → ℝ) : 0 ≤ spectralWeight f g := by
  exact Finset.sum_nonneg fun S _ => mul_nonneg (sq_nonneg _) (maxInfluence_nonneg f S)

/-- Equation (16): multiply Lemma 3.3 by the squared Fourier coefficient and sum. -/
theorem spectralWeight_le_four_spectral {f : Finset ι → ℝ} (hf : IsBoolean f)
    (hm : Monotone f) (g : Finset ι → ℝ) :
    spectralWeight f g ≤ 4 * ∑ T,
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
        fourier f S ^ 2 * fourier g T ^ 2 := by
  unfold spectralWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T _
  calc
    fourier g T ^ 2 * maxInfluence f T ≤
        fourier g T ^ 2 * (4 * ∑ S ∈ Finset.univ.filter
          (fun S : Finset ι => Odd (S ∩ T).card), fourier f S ^ 2) :=
      mul_le_mul_of_nonneg_left (maxInfluence_le_odd_spectral hf hm T) (sq_nonneg _)
    _ = 4 * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
        fourier f S ^ 2 * fourier g T ^ 2 := by
      rw [← Finset.sum_mul]
      ring

/-- The Parseval computation in Corollary 1.3: nonconstant Fourier coefficients
of an antipodal Boolean function have total squared mass one quarter. -/
theorem fourier_mass_of_antipodal {g : Finset ι → ℝ} (hb : IsBoolean g)
    (hg : dual g = g) :
    (∑ S ∈ Finset.univ.erase (∅ : Finset ι), fourier g S ^ 2) = 1 / 4 := by
  simpa [covariance_fourier, pow_two] using variance_eq_quarter_of_antipodal hb hg

/-- The lower bound on `𝒲(f,g)` used in Corollary 1.3. Any common lower bound
on the coordinate influences is weighted by the variance `1/4`. -/
theorem quarter_le_spectralWeight {f g : Finset ι → ℝ} {m : ℝ}
    (hb : IsBoolean g) (hg : dual g = g) (hm : ∀ i, m ≤ influence f i) :
    m / 4 ≤ spectralWeight f g := by
  calc
    m / 4 = (∑ S ∈ Finset.univ.erase (∅ : Finset ι), fourier g S ^ 2) * m := by
      rw [fourier_mass_of_antipodal hb hg]
      ring
    _ = ∑ S ∈ Finset.univ.erase (∅ : Finset ι), fourier g S ^ 2 * m :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ S ∈ Finset.univ.erase (∅ : Finset ι),
        fourier g S ^ 2 * maxInfluence f S := by
      apply Finset.sum_le_sum
      intro S hS
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1
      exact mul_le_mul_of_nonneg_left ((hm i).trans (influence_le_maxInfluence f hi))
        (sq_nonneg _)
    _ = spectralWeight f g := (spectralWeight_eq_sum_nonempty f g).symm

end Chvatal
