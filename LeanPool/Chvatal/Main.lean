/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvatal formalization contributors
-/
module

public import LeanPool.Chvatal.Correlation
public import LeanPool.Chvatal.Spectral

import Mathlib.Tactic.Linarith
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
# Chvátal's conjecture and the sharp correlation inequality

The main results of Chang–Liu–Liu, arXiv:2609.19123v1:

* `sharp_correlation`: Theorem 1.2, the sharp harmonic-mean bound.
* `antipodal_correlation`: Corollary 1.3, the minimum-influence bound.
* `chvatal`: Theorem 1.1, the star bound for hereditary families.

Theorem 1.4 is `two_spectral_le_quadratic_covariance` in `Chvatal.Correlation`.
The analytic statements allow an empty coordinate type. Statements involving a
minimum coordinate or a star center explicitly require a nonempty coordinate type.
-/

public section

open scoped BigOperators

noncomputable section

namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Nonnegativity of covariance for increasing Boolean functions, recalled after
Theorem 1.2. Here it follows directly by setting `t = 1` in Theorem 1.4. -/
theorem covariance_nonneg {f g : Finset ι → ℝ} (hf : IsBoolean f) (hmf : Monotone f)
    (hg : IsBoolean g) (hmg : Monotone g) : 0 ≤ covariance f g := by
  classical
  have hs : 0 ≤ 2 * (∑ T, ∑ S ∈ Finset.univ.filter
      (fun S : Finset ι => Odd (S ∩ T).card), fourier f S ^ 2 * fourier g T ^ 2) := by
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun T _ =>
      Finset.sum_nonneg fun S _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have h := two_spectral_le_quadratic_covariance hf hmf hg hmg 1
  norm_num at h
  exact hs.trans h

/-- Theorem 1.2, equation (1): the sharp correlation inequality.
The denominator-zero convention in the paper agrees with Lean's real division. -/
theorem sharp_correlation {f g : Finset ι → ℝ} (hf : IsBoolean f) (hmf : Monotone f)
    (hg : IsBoolean g) (hmg : Monotone g) :
    spectralWeight f g ≤
      2 * covariance f g * covariance f (dual g) /
        (covariance f g + covariance f (dual g)) := by
  apply le_harmonic_of_spectral_bound
    (covariance_nonneg hf hmf hg hmg)
    (covariance_nonneg hf hmf hg.dual (monotone_dual hmg))
    (c := 2 * ∑ T, ∑ S ∈ Finset.univ.filter
      (fun S : Finset ι => Odd (S ∩ T).card), fourier f S ^ 2 * fourier g T ^ 2)
  · have h := spectralWeight_le_four_spectral hf hmf g
    linarith
  · exact two_spectral_le_quadratic_covariance hf hmf hg hmg

/-- The antipodal specialization of Theorem 1.2 used in Corollary 1.3 and Proposition 5.3. -/
theorem antipodal_spectral_bound {f g : Finset ι → ℝ} (hf : IsBoolean f)
    (hmf : Monotone f) (hg : IsBoolean g) (hmg : Monotone g) (hdual : dual g = g) :
    spectralWeight f g ≤ covariance f g := by
  have h := sharp_correlation hf hmf hg hmg
  rwa [hdual, harmonic_self] at h

/-- The minimum coordinate influence appearing in Corollary 1.3.
A nonempty coordinate type is required to choose a minimum. -/
def minInfluence [Nonempty ι] (f : Finset ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (influence f)

/-- The minimum influence is no larger than any coordinate influence. -/
theorem minInfluence_le [Nonempty ι] (f : Finset ι → ℝ) (i : ι) :
    minInfluence f ≤ influence f i :=
  Finset.inf'_le (influence f) (Finset.mem_univ i)

/-- Corollary 1.3, equation (2): the Friedgut–Kahn–Kalai–Keller correlation bound. -/
theorem antipodal_correlation [Nonempty ι] {f g : Finset ι → ℝ} (hf : IsBoolean f)
    (hmf : Monotone f) (hg : IsBoolean g) (hmg : Monotone g) (hdual : dual g = g) :
    minInfluence f / 4 ≤ covariance f g :=
  (quarter_le_spectralWeight hg hdual (minInfluence_le f)).trans
    (antipodal_spectral_bound hf hmf hg hmg hdual)

/-- Corollary 1.3 in the existential coordinate form used by the Section 4 counting reduction. -/
theorem antipodal_correlation_bound [Nonempty ι] : AntipodalCorrelationBound ι := by
  intro f g hf hmf hg hmg hdual
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ (influence f) Finset.univ_nonempty
  have h := (quarter_le_spectralWeight hg hdual (fun j => hi j (Finset.mem_univ j))).trans
    (antipodal_spectral_bound hf hmf hg hmg hdual)
  exact ⟨i, by linarith⟩

omit [Fintype ι] in
/-- Theorem 1.1: every intersecting subfamily of a hereditary family is bounded
in cardinality by a star of that hereditary family. -/
theorem chvatal [Finite ι] [Nonempty ι] {D A : Family ι} (hD : D.IsHereditary)
    (hAD : A ⊆ D) (hA : A.IsIntersecting) :
    ∃ i : ι, A.card ≤ (D.star i).card := by
  let : Fintype ι := Fintype.ofFinite ι
  exact chvatal_of_antipodal_correlation antipodal_correlation_bound hD A hAD hA

omit [Fintype ι] in
/-- The abstract's formulation of Theorem 1.1: a single star is a largest
intersecting subfamily of the given hereditary family. -/
theorem exists_largest_intersecting_star [Finite ι] [Nonempty ι] {D : Family ι}
    (hD : D.IsHereditary) :
    ∃ i : ι, (D.star i).IsIntersecting ∧
      ∀ A : Family ι, A ⊆ D → A.IsIntersecting → A.card ≤ (D.star i).card := by
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : ι => (D.star i).card) Finset.univ_nonempty
  refine ⟨i, Family.star_isIntersecting D i, ?_⟩
  intro A hAD hA
  obtain ⟨j, hj⟩ := chvatal hD hAD hA
  exact hj.trans (hi j (Finset.mem_univ j))

end Chvatal
