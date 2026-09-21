/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.PWOSumset
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Berarducci's convolution formula for germs

Berarducci, Lemma 7.5(2): the germ of a product at `γ` is the finite sum of the products of the
germs of the factors over all pairs of exponents summing to `γ`. The index set
`Berarducci.convolutionIndex` is the finite set of first coordinates of points of the two closed
supports on the line of sum `γ`; it is finite by the well-ordering estimate proved with the
sumset lemmas.

The proof has two halves. `coeff_translatedTruncation_mul` reindexes the coefficient of a product
    of two
germ truncations as a sum over the pairs of the original supports on the line of sum `β + ξ + δ`
that lie weakly below `(β, ξ)`; this is a translation bijection and needs no hypotheses. The
remaining half is Berarducci, Lemma 7.4: for `γ + δ` below and sufficiently close to `γ`, each
such pair is dominated by exactly one index, so summing the reindexed coefficients over the index
set recovers the full antidiagonal sum, which is the coefficient of the product.

Equality of germs is equality on some interval `(η, γ]`; `η` is exactly the cutoff supplied by
Lemma 7.4.
-/

universe v

public noncomputable section

open HahnSeries Filter Topology

namespace Berarducci

variable {K : Type v} [Field K]

private theorem mem_support_translatedTruncation {b : K⟦ℝ⟧} {β u : ℝ} :
    u ∈ ((translatedTruncation b β : Series K) : K⟦ℝ⟧).support ↔
      u ≤ 0 ∧ β + u ∈ b.support := by
  rw [HahnSeries.mem_support, coeff_translatedTruncation]
  by_cases hu : u ≤ 0
  · simp [hu, HahnSeries.mem_support]
  · simp [hu]

theorem coeff_translatedTruncation_mul (b c : K⟦ℝ⟧) (β ξ δ : ℝ) :
    ((translatedTruncation b β * translatedTruncation c ξ : Series K) : K⟦ℝ⟧).coeff δ =
      ∑ pq ∈ (Finset.addAntidiagonal b.isPWO_support c.isPWO_support (β + ξ + δ)).filter
        (fun pq ↦ pq.1 ≤ β ∧ pq.2 ≤ ξ), b.coeff pq.1 * c.coeff pq.2 := by
  rw [Subring.coe_mul, HahnSeries.coeff_mul]
  refine Finset.sum_nbij' (i := fun uv ↦ (β + uv.1, ξ + uv.2))
    (j := fun pq ↦ (pq.1 - β, pq.2 - ξ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ huv
    rw [Finset.mem_addAntidiagonal] at huv
    obtain ⟨hu, hv, huv⟩ := huv
    rw [mem_support_translatedTruncation] at hu
    rw [mem_support_translatedTruncation] at hv
    simp only [Finset.mem_filter, Finset.mem_addAntidiagonal]
    refine ⟨⟨hu.2, hv.2, by linarith⟩, by linarith [hu.1], by linarith [hv.1]⟩
  · rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_addAntidiagonal] at hpq
    obtain ⟨⟨hp, hq, hsum⟩, hpβ, hqξ⟩ := hpq
    rw [Finset.mem_addAntidiagonal]
    refine ⟨?_, ?_, by linarith⟩
    · rw [mem_support_translatedTruncation]
      exact ⟨by linarith, by simpa using hp⟩
    · rw [mem_support_translatedTruncation]
      exact ⟨by linarith, by simpa using hq⟩
  · rintro ⟨u, v⟩ _
    simp
  · rintro ⟨p, q⟩ _
    simp
  · rintro ⟨u, v⟩ huv
    rw [Finset.mem_addAntidiagonal] at huv
    obtain ⟨hu, hv, -⟩ := huv
    rw [mem_support_translatedTruncation] at hu
    rw [mem_support_translatedTruncation] at hv
    rw [coeff_translatedTruncation, coeff_translatedTruncation, if_pos hu.1, if_pos hv.1]

/-- The finite index set of Berarducci's convolution formula: the first coordinates of the points
of the closed supports lying on the line of sum `γ`. -/
def convolutionIndex (b c : K⟦ℝ⟧) (γ : ℝ) : Finset ℝ :=
  (Set.IsPWO.finite_sub_mem (Set.isPWO_closure b.isPWO_support)
    (Set.isPWO_closure c.isPWO_support) γ).toFinset

@[simp]
theorem mem_convolutionIndex {b c : K⟦ℝ⟧} {γ β : ℝ} :
    β ∈ convolutionIndex b c γ ↔
      β ∈ closure b.support ∧ γ - β ∈ closure c.support := by
  simp [convolutionIndex]

/-- The convolution formula for germs of a product, valid at every real cutoff. -/
@[blueprint "lem:convolution-formula"
  (phase := "Ordinal value and degree")
  (title := "Convolution formula for translated truncations")
  (statement := /--
    Let $K$ be a field. For $b,c\in K((\mathbb R))$ and $\gamma\in\mathbb R$,
    \[
     \trunc{(bc)}\gamma\equiv\sum_{\xi+\zeta=\gamma}\trunc b\xi\trunc c\zeta
     \bmod J .
    \]
  -/)
  (proof := /--
  For a cutoff $\gamma$, only finitely many pairs of points in the two closed
  supports can sum to $\gamma$.  Below a sufficiently small neighbourhood of
  zero, every support pair contributing to the coefficient of $bc$ is dominated
  by a unique such boundary pair.  Regrouping the convolution product by that pair
  identifies the coefficients of $(bc)^{|\gamma}$ with the finite sum of
  $b^{|\xi}c^{|\zeta}$; equality near zero is precisely congruence modulo $J$.
  This is the proof of \cite[Lemma~7.5(2)]{Ber00}; its argument does not use
  $\gamma\le 0$, so it gives the displayed formula at every real cutoff.
  -/)]
theorem germAt_mul (b c : K⟦ℝ⟧) (γ : ℝ) :
    germAt (b * c) γ = ∑ β ∈ convolutionIndex b c γ, germAt b β * germAt c (γ - β) := by
  classical
  have hB := Set.isPWO_closure b.isPWO_support
  have hC := Set.isPWO_closure c.isPWO_support
  have hev := Set.IsPWO.eventually_existsUnique_dominating hB hC
    isClosed_closure isClosed_closure γ
  obtain ⟨η₀, hη₀, hsub⟩ := mem_nhdsLE_iff_exists_Ioc_subset.mp hev
  rw [Set.mem_Iio] at hη₀
  have hRHS : ∑ β ∈ convolutionIndex b c γ, germAt b β * germAt c (γ - β) =
      toGerm (∑ β ∈ convolutionIndex b c γ,
        translatedTruncation b β * translatedTruncation c (γ - β)) := by
    rw [map_sum]
    simp only [germAt_apply, map_mul]
  rw [germAt_apply, hRHS, toGerm_eq_toGerm_iff_exists_coeff_eq]
  refine ⟨η₀ - γ, by linarith, fun δ hδlow hδ0 ↦ ?_⟩
  have hγδ : γ + δ ∈ Set.Ioc η₀ γ := ⟨by linarith, by linarith⟩
  have hunique := hsub hγδ
  rw [coeff_translatedTruncation, if_pos hδ0]
  set A := Finset.addAntidiagonal b.isPWO_support c.isPWO_support (γ + δ) with hA
  rw [HahnSeries.coeff_mul]
  have hcoeSum : ((∑ β ∈ convolutionIndex b c γ,
        translatedTruncation b β * translatedTruncation c (γ - β) : Series K) : K⟦ℝ⟧).coeff δ =
      ∑ β ∈ convolutionIndex b c γ,
        ((translatedTruncation b β * translatedTruncation c (γ - β) : Series K) : K⟦ℝ⟧).coeff δ :=
            by
    rw [AddSubmonoidClass.coe_finsetSum, HahnSeries.coeff_sum]
  rw [hcoeSum]
  have hterm : ∀ β ∈ convolutionIndex b c γ,
      ((translatedTruncation b β * translatedTruncation c (γ - β) : Series K) : K⟦ℝ⟧).coeff δ =
        ∑ pq ∈ A.filter (fun pq ↦ pq.1 ≤ β ∧ pq.2 ≤ γ - β),
          b.coeff pq.1 * c.coeff pq.2 := by
    intro β _
    have hidx : β + (γ - β) + δ = γ + δ := by ring
    rw [coeff_translatedTruncation_mul b c β (γ - β) δ, hidx, ← hA]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun pq hpq ↦ ?_).symm
  rw [Finset.mem_addAntidiagonal] at hpq
  obtain ⟨hp, hq, hsum⟩ := hpq
  obtain ⟨β₀, hβ₀, hβ₀uniq⟩ :=
    hunique pq.1 (subset_closure hp) pq.2 (subset_closure hq) hsum
  refine (Finset.sum_eq_single β₀ ?_ ?_).trans ?_
  · intro β hβ hne
    refine if_neg fun hdom ↦ hne ?_
    exact hβ₀uniq β ⟨(mem_convolutionIndex.mp hβ).1, (mem_convolutionIndex.mp hβ).2,
      hdom.1, hdom.2⟩
  · intro hnot
    exact absurd (mem_convolutionIndex.mpr ⟨hβ₀.1, hβ₀.2.1⟩) hnot
  · exact if_pos ⟨hβ₀.2.2.1, hβ₀.2.2.2⟩

/-- Berarducci, Lemma 7.5(2), the convolution formula at a nonpositive cutoff. -/
theorem germAt_mul_of_nonpos (b c : K⟦ℝ⟧) (γ : ℝ) (_hγ : γ ≤ 0) :
    germAt (b * c) γ = ∑ β ∈ convolutionIndex b c γ, germAt b β * germAt c (γ - β) :=
  germAt_mul b c γ

end Berarducci
