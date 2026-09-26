/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverVariance
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the tight round with a CHEBYSHEV coverage guarantee

`LeanPool.AsymptoticTrianglePacking.Internal.exists_tight_round_on` extracts a good outcome by
making two failure probabilities add up to
less than one:

* "too many bad vertices", controlled by Markov, probability `≤ N(Vb/t² + Pb/s)/a`;
* "too little coverage", controlled by Markov applied to the UNCOVERED count, probability
  `≤ 1 − q/2`.

Because the second bound is only `1 − q/2`, the first has to be `< q/2 ≈ γ/2`; with `a = θN` this
forces `Vb/t² + Pb/s ≤ θγ`, hence (since `Pb ≈ Δγ²`) `s ≳ γΔ/θ`.  A band of width `≍ γΔ` cannot be
iterated: over the `≍ γ^{-1}log(1/β)` rounds of a nibble it accumulates to a relative error
`≍ log(1/β)/θ ≫ 1`.

Here the coverage is instead controlled by CHEBYSHEV, using the variance bound
`LeanPool.AsymptoticTrianglePacking.Internal.coveredCount_variance_le`. The coverage failure
probability becomes `4·Var/Q²`, which is
`≤ 1/2` under hypotheses on the vertex count and the codegree ALONE.  The badness budget is then a
constant rather than `γ`, so `Vb/t² + Pb/s ≤ θ/2` suffices and one may take

  `s ≍ Δγ²/θ`  and  `t ≍ γ²Δ`,

i.e. deviations of relative size `γ²`, whose accumulation over `γ^{-1}log(1/β)` rounds is
`≍ γ·log(1/β) → 0`.  This is the form of the round the iteration needs.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The deterministic band.**  If the loss weight of `v` is within `t` of its mean and the pair
count of `v` is below `s`, then the safe degree of `v` lies in the two-sided band of width `2t + s`
around `deg(v) − 𝔼[loss(v)]`. -/
theorem safeDegree_band_of_tolerances {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (ω : Ω) {t s : ℝ}
    (hloss : |lossWeight ρ v ω - lossWeightMean H p v| < t)
    (hpair : pairCount ρ v ω < s) :
    (degree H v : ℝ) - lossWeightMean H p v - t
        ≤ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
      ∧ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
        ≤ (degree H v : ℝ) - lossWeightMean H p v + t + s := by
  have habs := abs_lt.mp hloss
  have hlow := degree_le_safeDegree_add_coverWeight H v (covered (retainedSet H ρ ω))
  have hup := safeDegree_add_coverWeight_le H v (covered (retainedSet H ρ ω))
  have hlowR : (degree H v : ℝ)
      ≤ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
        + (coverWeight H v (covered (retainedSet H ρ ω)) : ℝ) := by exact_mod_cast hlow
  have hupR : (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
      + (coverWeight H v (covered (retainedSet H ρ ω)) : ℝ)
      ≤ (degree H v : ℝ) + (pairWeight H v (covered (retainedSet H ρ ω)) : ℝ) := by
    exact_mod_cast hup
  have hcw : (coverWeight H v (covered (retainedSet H ρ ω)) : ℝ) = lossWeight ρ v ω :=
    lossWeight_eq' ρ v ω
  have hpw : (pairWeight H v (covered (retainedSet H ρ ω)) : ℝ) ≤ pairCount ρ v ω :=
    pairWeight_le_pairCount ρ v ω
  rw [hcw] at hlowR hupR
  exact ⟨by linarith [habs.2], by linarith [habs.1]⟩

/-- **The tight round with Chebyshev coverage.**

There is an outcome of the nibble round which

* leaves fewer than `a` vertices outside the two-sided safe-degree band of width `2t + s` around
  `deg(v) − 𝔼[loss(v)]`, and
* covers more than `Q/2` vertices,

provided the Markov badness bound `N(Vb/t² + Pb/s)/a` and the Chebyshev coverage bound
`Cvar/(Q/2)²` add up to less than `1`.

Compared with `LeanPool.AsymptoticTrianglePacking.Internal.exists_tight_round_on`, the coverage
failure probability is `Cvar/(Q/2)²`
instead of `1 − q/2`: the badness budget is a constant instead of `O(q)`. -/
theorem exists_tight_round_cheb {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p)
    {t s a Vb Pb Q Cvar : ℝ} (ht : 0 < t) (hs : 0 < s) (ha : 0 < a) (hQ : 0 < Q)
    (hVb : ∀ v : V, ∫ ω, (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 ∂(ℙ : Measure Ω) ≤ Vb)
    (hPb : ∀ v : V, ∫ ω, pairCount ρ v ω ∂(ℙ : Measure Ω) ≤ Pb)
    (hmean : Q ≤ ∑ v : V, coverRate H p v)
    (hvar : ∫ ω, (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2
        ∂(ℙ : Measure Ω) ≤ Cvar)
    (hsmall : ((Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s)) / a + Cvar / (Q / 2) ^ 2 < 1) :
    ∃ ω : Ω, ∃ B : Finset V, (B.card : ℝ) < a ∧
      (∀ v ∉ B,
        (degree H v : ℝ) - lossWeightMean H p v - t
            ≤ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
          ∧ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
            ≤ (degree H v : ℝ) - lossWeightMean H p v + t + s)
      ∧ Q / 2 < ((covered (retainedSet H ρ ω)).card : ℝ) := by
  classical
  -- Markov for the badness event
  have hP1 : (ℙ : Measure Ω).real {ω | a ≤ tightBad ρ t s ω}
      ≤ ((Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s)) / a := by
    refine le_trans (measureReal_ge_le_integral_div
      (fun ω => tightBad_nonneg ρ ht hs ω) (integrable_tightBad ρ t s) ha) ?_
    exact (div_le_div_iff_of_pos_right ha).mpr (integral_tightBad_le ρ ht hs hVb hPb)
  -- Chebyshev for the coverage event
  have hP2 := prob_coverage_deviation_le ρ hQ hvar
  have hsum : (ℙ : Measure Ω).real {ω | a ≤ tightBad ρ t s ω}
      + (ℙ : Measure Ω).real
        {ω | (Q / 2) ^ 2
          ≤ (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2} < 1 := by
    linarith
  obtain ⟨ω, hω1, hω2⟩ := exists_notMem_of_measureReal_add_lt_one hsum
  refine ⟨ω, Finset.univ.filter (fun v : V =>
    t ≤ |lossWeight ρ v ω - lossWeightMean H p v| ∨ s ≤ pairCount ρ v ω), ?_, ?_, ?_⟩
  · have h1 := card_tightBadSet_le ρ ht hs ω
    have h2 : tightBad ρ t s ω < a := by
      by_contra hc
      push Not at hc
      exact hω1 hc
    linarith
  · intro v hv
    have hnot : ¬ (t ≤ |lossWeight ρ v ω - lossWeightMean H p v| ∨ s ≤ pairCount ρ v ω) := by
      intro h
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
    push Not at hnot
    exact safeDegree_band_of_tolerances ρ v ω hnot.1 hnot.2
  · have h2 : ¬ ((Q / 2) ^ 2
        ≤ (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2) := hω2
    push Not at h2
    by_contra hc
    push Not at hc
    nlinarith only [h2, hmean, hc, hQ]

end LeanPool.AsymptoticTrianglePacking.Internal
