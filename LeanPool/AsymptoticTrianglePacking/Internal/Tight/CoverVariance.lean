/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.TightRound
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.PairExcessCodegree
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the VARIANCE of the covered count, and Chebyshev for
the coverage

`LeanPool.AsymptoticTrianglePacking.Internal.exists_tight_round_on` controls the coverage of a
nibble round by MARKOV applied to the
number of *uncovered* vertices.  That is extremely lossy: it only gives

  `ℙ(covered ≤ N·q/2) ≤ 1 − q/2`,

so the competing badness event has to have probability `< q/2 ≈ γ/2`, and the Markov bound on the
badness then forces the deviation tolerances `t, s` to be of the same order as the whole per-round
degree drop `γΔ` — a band far too wide to be iterated over `≍ γ^{-1}log(1/β)` rounds.

This file removes that bottleneck.  The covered count `Cov = ∑_v 1[v covered]` is a sum of
indicators whose pair covariances are exactly the pair excesses controlled by
`LeanPool.AsymptoticTrianglePacking.Internal.pair_excess_le_codegree`, so

  `Var(Cov) ≤ N·q_hi + N²·ε₂`,     (`coveredCount_variance_le`)

with `ε₂` the (codegree-controlled) pair excess.  Chebyshev then gives a coverage failure
probability `≤ 4·Var/Q²`, which in the nibble regime `Q ≈ Nγ`, `ε₂ ≈ μγ` is

  `4/(Nγ) + 4μ/γ`,

i.e. `≤ 1/2` as soon as `N ≥ 16/γ` and `μ ≤ γ/16` — INDEPENDENTLY of the deviation tolerances.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The centred covered count is the sum of the centred covering indicators. -/
theorem coveredCount_sub_mean_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (ω : Ω) :
    ((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v
      = ∑ v : V, coverIndC ρ v ω := by
  rw [coveredCount_eq_sum ρ ω, ← Finset.sum_sub_distrib]
  rfl

/-- The centred covered count is square integrable. -/
theorem integrable_sq_centered_coveredCount {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) :
    Integrable (fun ω => (((covered (retainedSet H ρ ω)).card : ℝ)
      - ∑ v : V, coverRate H p v) ^ 2) (ℙ : Measure Ω) := by
  have hexp : (fun ω => (((covered (retainedSet H ρ ω)).card : ℝ)
        - ∑ v : V, coverRate H p v) ^ 2)
      = fun ω => ∑ u : V, ∑ u' : V, coverIndC ρ u ω * coverIndC ρ u' ω := by
    funext ω
    rw [coveredCount_sub_mean_eq ρ ω, sq, Finset.sum_mul_sum]
  rw [hexp]
  exact integrable_finsetSum _
    (fun u _ => integrable_finsetSum _ (fun u' _ => integrable_coverIndC_mul ρ u u'))

/-- **The variance of the covered count, as an exact double sum of pair excesses.** -/
theorem integral_sq_centered_coveredCount {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ ω, (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2
        ∂(ℙ : Measure Ω)
      = ∑ u : V, ∑ u' : V,
          ((ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
              ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
            - coverRate H p u * coverRate H p u') := by
  have hexp : ∀ ω, (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2
      = ∑ u : V, ∑ u' : V, coverIndC ρ u ω * coverIndC ρ u' ω := by
    intro ω
    rw [coveredCount_sub_mean_eq ρ ω, sq, Finset.sum_mul_sum]
  simp only [hexp]
  rw [integral_finsetSum _
    (fun u _ => integrable_finsetSum _ (fun u' _ => integrable_coverIndC_mul ρ u u'))]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [integral_finsetSum _ (fun u' _ => integrable_coverIndC_mul ρ u u')]
  exact Finset.sum_congr rfl (fun u' _ => integral_coverIndC_mul ρ hp0 hp1 u u')

/-- **The variance bound for the covered count.**  With covering rates at most `q_hi` and pair
excesses at most `ε₂`, the covered count has variance at most `N·q_hi + N²·ε₂`. -/
theorem coveredCount_variance_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {qhi ε₂ : ℝ} (hq : ∀ u : V, coverRate H p u ≤ qhi) (hε0 : 0 ≤ ε₂)
    (hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u' ≤ ε₂) :
    ∫ ω, (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2
        ∂(ℙ : Measure Ω)
      ≤ (Fintype.card V : ℝ) * qhi + (Fintype.card V : ℝ) ^ 2 * ε₂ := by
  classical
  rw [integral_sq_centered_coveredCount ρ hp0 hp1]
  have hterm : ∀ u : V, ∀ u' : V,
      ((ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u')
      ≤ (if u = u' then qhi else 0) + ε₂ := by
    intro u u'
    by_cases huu' : u = u'
    · subst huu'
      have hself : ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u ∈ covered (retainedSet H ρ ω)}) = {ω | u ∈ covered (retainedSet H ρ ω)} :=
        Set.inter_self _
      rw [hself, prob_vertex_covered_eq ρ hp0 hp1 u, ite_eq_left rfl]
      have hqu0 : 0 ≤ coverRate H p u := coverRate_nonneg hp0 hp1 u
      nlinarith [hq u, mul_nonneg hqu0 hqu0]
    · rw [ite_eq_right huu']
      linarith only [hpair u u' huu']
  calc ∑ u : V, ∑ u' : V,
        ((ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
            ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
          - coverRate H p u * coverRate H p u')
      ≤ ∑ u : V, ∑ u' : V, ((if u = u' then qhi else 0) + ε₂) :=
        Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun u' _ => hterm u u'))
    _ = (Fintype.card V : ℝ) * qhi + (Fintype.card V : ℝ) ^ 2 * ε₂ := by
        have hinner : ∀ u : V, ∑ u' : V, ((if u = u' then qhi else 0) + ε₂)
            = qhi + (Fintype.card V : ℝ) * ε₂ := by
          intro u
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          congr 1
          rw [Finset.sum_ite_eq (Finset.univ : Finset V) u (fun _ => qhi),
            ite_eq_left (Finset.mem_univ u)]
        rw [Finset.sum_congr rfl (fun u _ => hinner u), Finset.sum_const, nsmul_eq_mul,
          Finset.card_univ]
        ring

/-- **Chebyshev for the coverage.**  If the mean coverage is at least `Q > 0` and the variance is at
most `Cvar`, the probability that the covered count deviates by `Q/2` or more is at most
`Cvar/(Q/2)²`. -/
theorem prob_coverage_deviation_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {Q Cvar : ℝ} (hQ : 0 < Q)
    (hvar : ∫ ω, (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2
        ∂(ℙ : Measure Ω) ≤ Cvar) :
    (ℙ : Measure Ω).real
        {ω | (Q / 2) ^ 2
          ≤ (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2}
      ≤ Cvar / (Q / 2) ^ 2 := by
  have hpos : (0 : ℝ) < (Q / 2) ^ 2 := by positivity
  refine le_trans (measureReal_ge_le_integral_div (fun ω => sq_nonneg _)
    (integrable_sq_centered_coveredCount ρ) hpos) ?_
  exact (div_le_div_iff_of_pos_right hpos).mpr hvar

end LeanPool.AsymptoticTrianglePacking.Internal
