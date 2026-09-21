/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — the mean of the Bonferroni correction

The upper half of the safe-degree sandwich (`LeanPool.AsymptoticTrianglePacking.Internal.safeDegree_add_coverWeight_le`) pays the
Bonferroni correction `pairWeight H v C = ∑_{e ∋ v} C(|(e∖v) ∩ C|, 2)`.  This file bounds its mean.

* `sum_pair_ind_nat` — the ordered-pair count `∑_{u ∈ D} ∑_{u' ∈ D∖u} 1[u ∈ C]1[u' ∈ C]` equals
  `k(k−1)` with `k = |D ∩ C|`, hence dominates `C(k,2)`;
* `pairWeight_le_pairCount` — pathwise, `pairWeight ≤ pairCount`, the ordered-pair count of the
  covering indicators;
* `integral_pairCount_le` — `𝔼[pairCount] ≤ deg(v)·(r−1)²·ε_pair`, where `ε_pair` bounds the joint
  covering probability of two distinct vertices (`prob_two_vertices_covered_le` gives
  `ε_pair = Δ²p² + κp`).

In the nibble regime this is `O(deg(v)·r²(γ² + μγ))` — second order against the first-order loss
`deg(v)·(r−1)q ≈ deg(v)·γ`, so Markov's inequality makes it negligible for all but a tiny fraction
of the vertices.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverWeightMoments
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## The ordered-pair count -/

/-- The ordered-pair count of a finite set against `C`. -/
theorem sum_pair_ind_nat (D C : Finset V) :
    ∑ u ∈ D, ∑ u' ∈ D.erase u, (if u ∈ C then 1 else 0) * (if u' ∈ C then (1 : ℕ) else 0)
      = (D ∩ C).card * ((D ∩ C).card - 1) := by
  classical
  have hinner : ∀ u ∈ D,
      ∑ u' ∈ D.erase u, (if u ∈ C then 1 else 0) * (if u' ∈ C then (1 : ℕ) else 0)
        = (if u ∈ C then 1 else 0) * ((D.erase u ∩ C).card) := by
    intro u _
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.card_filter (fun a => a ∈ C) (D.erase u) |>.symm, Finset.filter_mem_eq_inter]
  rw [Finset.sum_congr rfl hinner]
  have hfil : ∑ u ∈ D, (if u ∈ C then 1 else 0) * ((D.erase u ∩ C).card)
      = ∑ u ∈ D.filter (fun u => u ∈ C), ((D.erase u ∩ C).card) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun u _ => by split_ifs <;> simp)
  rw [hfil, Finset.filter_mem_eq_inter]
  have hcards : ∀ u ∈ D ∩ C, (D.erase u ∩ C).card = (D ∩ C).card - 1 := by
    intro u hu
    have h1 : D.erase u ∩ C = (D ∩ C).erase u := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_erase]
      tauto
    rw [h1, Finset.card_erase_of_mem hu]
  rw [Finset.sum_congr rfl hcards, Finset.sum_const, smul_eq_mul]

/-- `C(k,2)` is dominated by the ordered-pair count. -/
theorem choose_two_le_sum_pair_ind (D C : Finset V) :
    Nat.choose ((D ∩ C).card) 2
      ≤ ∑ u ∈ D, ∑ u' ∈ D.erase u, (if u ∈ C then 1 else 0) * (if u' ∈ C then (1 : ℕ) else 0) := by
  rw [sum_pair_ind_nat, Nat.choose_two_right]
  exact Nat.div_le_self _ 2

/-! ## The pair count as a random variable -/

/-- The ordered-pair count of covering indicators at `v`. -/
noncomputable def pairCount {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (ω : Ω) : ℝ :=
  ∑ e ∈ H.filter (fun e => v ∈ e), ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
    coverInd ρ u ω * coverInd ρ u' ω

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Pathwise, the Bonferroni correction is dominated by the pair count. -/
theorem pairWeight_le_pairCount {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (ω : Ω) :
    (pairWeight H v (covered (retainedSet H ρ ω)) : ℝ) ≤ pairCount ρ v ω := by
  classical
  set C := covered (retainedSet H ρ ω) with hC
  rw [pairWeight, pairCount, Nat.cast_sum]
  refine Finset.sum_le_sum (fun e _ => ?_)
  have hnat := choose_two_le_sum_pair_ind (e.erase v) C
  have hcast : ((∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
      (if u ∈ C then 1 else 0) * (if u' ∈ C then (1 : ℕ) else 0) : ℕ) : ℝ)
      = ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u, coverInd ρ u ω * coverInd ρ u' ω := by
    push_cast [coverInd]
    rw [hC]
  rw [← hcast]
  exact_mod_cast hnat

theorem integrable_pairCount {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    Integrable (pairCount ρ v) (ℙ : Measure Ω) := by
  have h : pairCount ρ v = fun ω => ∑ e ∈ H.filter (fun e => v ∈ e),
      ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u, coverInd ρ u ω * coverInd ρ u' ω := rfl
  rw [h]
  exact integrable_finset_sum _ (fun e _ => integrable_finset_sum _ (fun u _ =>
    integrable_finset_sum _ (fun u' _ => integrable_coverInd_mul ρ u u')))

/-- **The mean of the pair count.** -/
theorem integral_pairCount_le {H : Finset (Finset V)} {p : ℝ} {r : ℕ} {εpair : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hr : IsUniform H r) (hr1 : 1 ≤ r)
    (hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
        ∩ {ω | u' ∈ covered (retainedSet H ρ ω)}) ≤ εpair) (hε0 : 0 ≤ εpair) (v : V) :
    ∫ ω, pairCount ρ v ω ∂(ℙ : Measure Ω) ≤ (degree H v : ℝ) * ((r : ℝ) - 1) ^ 2 * εpair := by
  classical
  have h : pairCount ρ v = fun ω => ∑ e ∈ H.filter (fun e => v ∈ e),
      ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u, coverInd ρ u ω * coverInd ρ u' ω := rfl
  rw [h, integral_finset_sum _ (fun e _ => integrable_finset_sum _ (fun u _ =>
    integrable_finset_sum _ (fun u' _ => integrable_coverInd_mul ρ u u')))]
  have hterm : ∀ e ∈ H.filter (fun e => v ∈ e),
      ∫ ω, (∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
          coverInd ρ u ω * coverInd ρ u' ω) ∂(ℙ : Measure Ω)
        ≤ ((r : ℝ) - 1) ^ 2 * εpair := by
    intro e he
    have hve : v ∈ e := (Finset.mem_filter.mp he).2
    have hcard : (e.erase v).card = r - 1 := by
      rw [Finset.card_erase_of_mem hve, hr e (Finset.mem_filter.mp he).1]
    have hcastc : ((e.erase v).card : ℝ) = (r : ℝ) - 1 := by
      rw [hcard, Nat.cast_sub hr1, Nat.cast_one]
    rw [integral_finset_sum _ (fun u _ => integrable_finset_sum _
      (fun u' _ => integrable_coverInd_mul ρ u u'))]
    calc ∑ u ∈ e.erase v, ∫ ω, (∑ u' ∈ (e.erase v).erase u,
            coverInd ρ u ω * coverInd ρ u' ω) ∂(ℙ : Measure Ω)
        ≤ ∑ _u ∈ e.erase v, (((e.erase v).card : ℝ) * εpair) := by
          refine Finset.sum_le_sum (fun u hu => ?_)
          rw [integral_finset_sum _ (fun u' _ => integrable_coverInd_mul ρ u u')]
          calc ∑ u' ∈ (e.erase v).erase u,
                ∫ ω, coverInd ρ u ω * coverInd ρ u' ω ∂(ℙ : Measure Ω)
              ≤ ∑ _u' ∈ (e.erase v).erase u, εpair := by
                refine Finset.sum_le_sum (fun u' hu' => ?_)
                rw [integral_coverInd_mul ρ u u']
                exact hpair u u' (Ne.symm (Finset.mem_erase.mp hu').1)
            _ = (((e.erase v).erase u).card : ℝ) * εpair := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ((e.erase v).card : ℝ) * εpair := by
                refine mul_le_mul_of_nonneg_right ?_ hε0
                exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
      _ = ((e.erase v).card : ℝ) * (((e.erase v).card : ℝ) * εpair) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((r : ℝ) - 1) ^ 2 * εpair := by rw [hcastc]; ring
  calc ∑ e ∈ H.filter (fun e => v ∈ e),
        ∫ ω, (∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
          coverInd ρ u ω * coverInd ρ u' ω) ∂(ℙ : Measure Ω)
      ≤ ∑ _e ∈ H.filter (fun e => v ∈ e), (((r : ℝ) - 1) ^ 2 * εpair) :=
        Finset.sum_le_sum hterm
    _ = (degree H v : ℝ) * (((r : ℝ) - 1) ^ 2 * εpair) := by
        rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ = (degree H v : ℝ) * ((r : ℝ) - 1) ^ 2 * εpair := by ring

end LeanPool.AsymptoticTrianglePacking.Internal
