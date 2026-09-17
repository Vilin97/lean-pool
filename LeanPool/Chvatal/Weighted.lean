/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvatal formalization contributors
-/
module

public import LeanPool.Chvatal.Counting
public import LeanPool.Chvatal.Main
public import LeanPool.Chvatal.LayerCake

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
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
# The spectral coefficients in the weighted star inequality

This file formalizes Proposition 5.3 of arXiv:2609.19123. The paper assigns each
nonempty Fourier set to its largest coordinate in a fixed total order. The
arguments below allow any fixed selector belonging to that set, a slightly
stronger formulation which includes the paper's choice.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Proposition 5.3's coefficients `λ_i`: four times the nonconstant Fourier
mass assigned to coordinate `i`. The selector is fixed independently of the
weight or hereditary family under consideration. -/
def spectralWeights (g : Finset ι → ℝ) (select : Finset ι → ι) (i : ι) : ℝ :=
  4 * ∑ S ∈ Finset.univ.erase ∅, if select S = i then fourier g S ^ 2 else 0

/-- Nonnegativity of every coefficient in Proposition 5.3. -/
theorem spectralWeights_nonneg (g : Finset ι → ℝ) (select : Finset ι → ι) (i : ι) :
    0 ≤ spectralWeights g select i := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun S _ => by split_ifs <;> positivity

/-- Regrouping Fourier sets according to their selected coordinate, the
partition-of-mass step in Proposition 5.3. -/
theorem sum_spectralWeights_mul (g : Finset ι → ℝ) (select : Finset ι → ι)
    (a : ι → ℝ) :
    (∑ i, spectralWeights g select i * a i) =
      4 * ∑ S ∈ Finset.univ.erase ∅, fourier g S ^ 2 * a (select S) := by
  simp only [spectralWeights, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  simp [mul_assoc, mul_ite, ite_mul]

/-- The coefficients in Proposition 5.3 sum to one, by Parseval and the
variance-one-quarter identity for an antipodal Boolean function. -/
theorem sum_spectralWeights {g : Finset ι → ℝ} (hg : IsBoolean g)
    (hdual : dual g = g) (select : Finset ι → ι) :
    ∑ i, spectralWeights g select i = 1 := by
  have hsum := sum_spectralWeights_mul g select (fun _ => 1)
  simp only [mul_one] at hsum
  have hmass : (∑ S ∈ Finset.univ.erase ∅, fourier g S ^ 2) = covariance g g := by
    rw [covariance_fourier]
    simp only [pow_two]
  rw [hmass, variance_eq_quarter_of_antipodal hg hdual] at hsum
  norm_num at hsum ⊢
  exact hsum

/-- A fixed total order gives the selector `max_≺ S` used in Proposition 5.3.
The value at the empty set is irrelevant because the coefficients omit it. -/
def orderedSelector [LinearOrder ι] [Nonempty ι] (S : Finset ι) : ι :=
  if hS : S.Nonempty then S.max' hS else Classical.choice inferInstance

omit [Fintype ι] [DecidableEq ι] in
/-- The ordered selector lies in each nonempty set, the property of the
paper's `max_≺` used in the weighted argument. -/
theorem orderedSelector_mem [LinearOrder ι] [Nonempty ι] {S : Finset ι}
    (hS : S.Nonempty) : orderedSelector S ∈ S := by
  simp only [orderedSelector, dite_eq_left hS]
  exact Finset.max'_mem _ _

/-- The hereditary-family inequality in the proof of Proposition 5.3, deduced
from the selected-coordinate spectral lower bound. This hypothesis is explicit
so the counting reduction is independent of the analytic proof. -/
theorem hereditary_bound_of_selected_correlation {g : Finset ι → ℝ}
    (hg : IsBoolean g) (hdual : dual g = g) (select : Finset ι → ι)
    (hcor : ∀ f : Finset ι → ℝ, IsBoolean f → Monotone f →
      (∑ S ∈ Finset.univ.erase ∅, fourier g S ^ 2 * influence f (select S)) ≤
        covariance f g)
    {D : Family ι} (hD : D.IsHereditary) :
    ((D ∩ Family.oneSupport g).card : ℝ) ≤
      ∑ i, spectralWeights g select i * (D.star i).card := by
  let B := Family.oneSupport g
  have hgB : B.indicator = g := Family.indicator_oneSupport hg
  have hanti : B.IsAntipodal := by
    rw [Family.isAntipodal_iff_dual_indicator, hgB]
    exact hdual
  have hsum := sum_spectralWeights hg hdual select
  have hbound := hcor (fun x => 1 - D.indicator x)
    (Family.isBoolean_one_sub_indicator D) hD.monotone_one_sub_indicator
  have hweighted : (∑ i, spectralWeights g select i *
      influence (fun x => 1 - D.indicator x) i) ≤
      4 * covariance (fun x => 1 - D.indicator x) g := by
    rw [sum_spectralWeights_mul]
    linarith
  have hcount : (∑ i, spectralWeights g select i *
      influence (fun x => 1 - D.indicator x) i) =
      (2 * (D.card : ℝ) - 4 * ∑ i, spectralWeights g select i * (D.star i).card) /
        Fintype.card (Finset ι) := by
    calc
      _ = (∑ i, ((2 * (D.card : ℝ)) * spectralWeights g select i -
          4 * (spectralWeights g select i * (D.star i).card))) /
          Fintype.card (Finset ι) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Family.influence_one_sub_indicator hD]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
        ring
  have hcov := Family.covariance_one_sub_indicator (D := D) hanti
  rw [hgB] at hcov
  rw [hcount, hcov] at hweighted
  have hN := cube_card_pos (ι := ι)
  have hnum := (div_le_div_iff_of_pos_right hN).mp
    (show (2 * (D.card : ℝ) - 4 * ∑ i, spectralWeights g select i * (D.star i).card) /
        Fintype.card (Finset ι) ≤
      (4 * ((D.card : ℝ) / 2 - (D ∩ B).card)) / Fintype.card (Finset ι) by
      simpa only [mul_div_assoc] using hweighted)
  dsimp [B] at hnum
  linarith

/-- The fractional star function `q(x) = ∑_i λ_i x_i` from the proof of
Proposition 5.3. -/
def starMixture (weights : ι → ℝ) (x : Finset ι) : ℝ :=
  ∑ i, if i ∈ x then weights i else 0

/-- Counting the fractional star function on a family gives the corresponding
weighted combination of its star cardinalities (Proposition 5.3). -/
theorem sum_starMixture (weights : ι → ℝ) (D : Family ι) :
    (∑ x ∈ D, starMixture weights x) =
      ∑ i, weights i * (D.star i).card := by
  unfold starMixture
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Family.star, ← Finset.sum_filter, mul_comm]

omit [Fintype ι] in
/-- Summing a family indicator over another family counts their intersection,
the second counting step for the defect in Proposition 5.3. -/
theorem sum_indicator_on_family (B D : Family ι) :
    (∑ x ∈ D, B.indicator x) = ((D ∩ B).card : ℝ) := by
  simp [Family.indicator]

/-- The mean-zero defect in Proposition 5.3, summed on a hereditary family.
The identity itself holds for every family. -/
theorem sum_starMixture_sub_indicator (weights : ι → ℝ) (B D : Family ι) :
    (∑ x ∈ D, (starMixture weights x - B.indicator x)) =
      (∑ i, weights i * (D.star i).card) - (D ∩ B).card := by
  rw [Finset.sum_sub_distrib, sum_starMixture, sum_indicator_on_family]

/-- The weighted form of the same defect, obtained by interchanging finite
sums. This is the finite counterpart of the layer-cake calculation in (18). -/
theorem sum_defect_mul (weights : ι → ℝ) (B : Family ι) (ω : Finset ι → ℝ) :
    (∑ x, (starMixture weights x - B.indicator x) * ω x) =
      (∑ i, weights i * ∑ x ∈ Family.star Finset.univ i, ω x) - ∑ x ∈ B, ω x := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  · unfold starMixture
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Family.star, Finset.sum_filter, Finset.mul_sum, ite_mul]
  · simp [Family.indicator, ite_mul]

/-- Finite layer-cake lifting in Proposition 5.3: domination on every
hereditary family implies domination for every nonnegative decreasing weight. -/
theorem weighted_bound_of_hereditary_bound (weights : ι → ℝ) (B : Family ι)
    (hbound : ∀ D : Family ι, D.IsHereditary →
      ((D ∩ B).card : ℝ) ≤ ∑ i, weights i * (D.star i).card)
    (ω : Finset ι → ℝ) (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    (∑ x ∈ B, ω x) ≤ ∑ i, weights i * ∑ x ∈ Family.star Finset.univ i, ω x := by
  have h := sum_mul_antitone_nonneg_of_lowerSets
    (fun x => starMixture weights x - B.indicator x)
    (fun D hD => by
      rw [sum_starMixture_sub_indicator]
      exact sub_nonneg.mpr (hbound D hD)) ω hω hanti
  rw [sum_defect_mul] at h
  exact sub_nonneg.mp h

/-- The selected-coordinate expression in Proposition 5.3 is bounded by the
spectral expression in Theorem 1.2, because the selector belongs to its set. -/
theorem selected_spectral_le (f g : Finset ι → ℝ) (select : Finset ι → ι)
    (hselect : ∀ S : Finset ι, S.Nonempty → select S ∈ S) :
    (∑ S ∈ Finset.univ.erase ∅, fourier g S ^ 2 * influence f (select S)) ≤
      spectralWeight f g := by
  rw [spectralWeight_eq_sum_nonempty]
  apply Finset.sum_le_sum
  intro S hS
  exact mul_le_mul_of_nonneg_left (influence_le_maxInfluence f
    (hselect S (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1)))
    (sq_nonneg _)

/-- The first inequality of Proposition 5.3 deduced from the antipodal spectral
bound, keeping the analytic dependency explicit. -/
theorem weighted_bound_of_spectral_bound [Nonempty ι] {B : Family ι}
    (hB : B.IsMaximalIntersecting) (select : Finset ι → ι)
    (hselect : ∀ S : Finset ι, S.Nonempty → select S ∈ S)
    (hspectral : ∀ f : Finset ι → ℝ, IsBoolean f → Monotone f →
      spectralWeight f B.indicator ≤ covariance f B.indicator)
    (ω : Finset ι → ℝ) (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    (∑ x ∈ B, ω x) ≤
      ∑ i, spectralWeights B.indicator select i * ∑ x ∈ Family.star Finset.univ i, ω x := by
  apply weighted_bound_of_hereditary_bound _ B ?_ ω hω hanti
  intro D hD
  have hsupport : Family.oneSupport B.indicator = B := by
    ext x
    by_cases hx : x ∈ B <;> simp [Family.indicator, hx]
  have h := hereditary_bound_of_selected_correlation (Family.isBoolean_indicator B)
    hB.isAntipodal.dual_indicator select
    (fun f hf hm => (selected_spectral_le f B.indicator select hselect).trans
      (hspectral f hf hm)) hD
  simpa only [hsupport] using h

/-- Proposition 5.3's first inequality, proved from the antipodal case of
Theorem 1.2. It holds for any fixed selector belonging to each nonempty index. -/
theorem weighted_star_mixture_bound [Nonempty ι] {B : Family ι}
    (hB : B.IsMaximalIntersecting) (select : Finset ι → ι)
    (hselect : ∀ S : Finset ι, S.Nonempty → select S ∈ S)
    (ω : Finset ι → ℝ) (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    (∑ x ∈ B, ω x) ≤
      ∑ i, spectralWeights B.indicator select i * ∑ x ∈ Family.star Finset.univ i, ω x :=
  weighted_bound_of_spectral_bound hB select hselect
    (fun _ hf hmf => antipodal_spectral_bound hf hmf (Family.isBoolean_indicator B)
      hB.isIncreasing.monotone_indicator hB.isAntipodal.dual_indicator) ω hω hanti

/-- A convex combination of star weights is at most their maximum, the second
inequality in equation (18). -/
theorem star_mixture_le_max [Nonempty ι] (weights : ι → ℝ)
    (hweights : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i = 1)
    (ω : Finset ι → ℝ) :
    (∑ i, weights i * ∑ x ∈ Family.star Finset.univ i, ω x) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => ∑ x ∈ Family.star Finset.univ i, ω x) := by
  let M := Finset.univ.sup' Finset.univ_nonempty
    (fun i => ∑ x ∈ Family.star Finset.univ i, ω x)
  calc
    _ ≤ ∑ i, weights i * M := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hweights i)
      exact Finset.le_sup' (fun j : ι => ∑ x ∈ Family.star Finset.univ j, ω x)
        (Finset.mem_univ i)
    _ = M := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Proposition 5.3 in the paper's exact ordered-selector formulation: the
spectral coefficients are nonnegative, sum to one, and satisfy both inequalities
in equation (18). The total order represents the paper's fixed permutation. -/
theorem kleitman_weighted_bound [LinearOrder ι] [Nonempty ι] {B : Family ι}
    (hB : B.IsMaximalIntersecting) (ω : Finset ι → ℝ)
    (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    (∀ i, 0 ≤ spectralWeights B.indicator orderedSelector i) ∧
    (∑ i, spectralWeights B.indicator orderedSelector i) = 1 ∧
    (∑ x ∈ B, ω x) ≤
      (∑ i, spectralWeights B.indicator orderedSelector i *
        ∑ x ∈ Family.star Finset.univ i, ω x) ∧
    (∑ i, spectralWeights B.indicator orderedSelector i *
        ∑ x ∈ Family.star Finset.univ i, ω x) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => ∑ x ∈ Family.star Finset.univ i, ω x) := by
  have hweights := spectralWeights_nonneg B.indicator orderedSelector
  have hsum := sum_spectralWeights (Family.isBoolean_indicator B)
    hB.isAntipodal.dual_indicator orderedSelector
  exact ⟨hweights, hsum,
    weighted_star_mixture_bound hB orderedSelector (fun _ => orderedSelector_mem) ω hω hanti,
    star_mixture_le_max _ hweights hsum ω⟩

/-- The final conclusion of Proposition 5.3 for one intersecting family:
its total nonnegative decreasing weight is bounded by some full-cube star. -/
theorem exists_weighted_star_bound [Nonempty ι] {A : Family ι}
    (hA : A.IsIntersecting) (ω : Finset ι → ℝ)
    (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    ∃ i : ι, (∑ x ∈ A, ω x) ≤ ∑ x ∈ Family.star Finset.univ i, ω x := by
  classical
  obtain ⟨B, hAB, hB⟩ := hA.exists_maximal_extension
  let select : Finset ι → ι := fun S =>
    if hS : S.Nonempty then hS.choose else Classical.choice inferInstance
  have hselect : ∀ S : Finset ι, S.Nonempty → select S ∈ S := by
    intro S hS
    simp only [select, dite_eq_left hS]
    exact hS.choose_spec
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => ∑ x ∈ Family.star Finset.univ i, ω x) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  calc
    (∑ x ∈ A, ω x) ≤ ∑ x ∈ B, ω x :=
      Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x _ _ => hω x)
    _ ≤ ∑ j, spectralWeights B.indicator select j *
        ∑ x ∈ Family.star Finset.univ j, ω x :=
      weighted_star_mixture_bound hB select hselect ω hω hanti
    _ ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun j => ∑ x ∈ Family.star Finset.univ j, ω x) :=
      star_mixture_le_max _ (spectralWeights_nonneg _ _)
        (sum_spectralWeights (Family.isBoolean_indicator B) hB.isAntipodal.dual_indicator
          select) ω
    _ ≤ ∑ x ∈ Family.star Finset.univ i, ω x := Finset.sup'_le _ _ hi

/-- The final maximum-attainment statement of Proposition 5.3: one star
simultaneously dominates every intersecting family for a fixed nonnegative
decreasing weight, and that star is itself intersecting. -/
theorem exists_largest_weighted_intersecting_star [Nonempty ι]
    (ω : Finset ι → ℝ) (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    ∃ i : ι, (Family.star (Finset.univ : Family ι) i).IsIntersecting ∧
      ∀ A : Family ι, A.IsIntersecting →
        (∑ x ∈ A, ω x) ≤ ∑ x ∈ Family.star Finset.univ i, ω x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => ∑ x ∈ Family.star Finset.univ i, ω x) Finset.univ_nonempty
  refine ⟨i, Family.star_isIntersecting Finset.univ i, ?_⟩
  intro A hA
  obtain ⟨j, hj⟩ := exists_weighted_star_bound hA ω hω hanti
  exact hj.trans (hi j (Finset.mem_univ j))

end Chvatal
