/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — the round with a DIRECT safe-degree Chebyshev band

`LeanPool.AsymptoticTrianglePacking.Internal.exists_tight_round_cheb` controls the safe degree indirectly, through the loss weight
(second moment, tolerance `t`) and the pair count (first moment, tolerance `s`).  The pair count has
mean `≍ Δγ²` and can only be handled by Markov, forcing `s ≳ Δγ²/θ`; combined with the junk budget
that the round schedule can afford, this is not summable over the `≍ γ^{-1}log(1/β)` rounds.

Here the safe degree is controlled DIRECTLY by its own variance
(`LeanPool.AsymptoticTrianglePacking.Internal.safeDegree_variance_le_codegree`), so a single symmetric tolerance `t` replaces the pair
`(t, s)` and no first-moment (Markov) term survives:

  `#{v : |safeDeg(v) − 𝔼safeDeg(v)| ≥ t} ≤ ∑_v (safeDeg(v) − 𝔼)²/t²`,

whose mean is `N·Vs/t²`.  Combined with the Chebyshev coverage bound
(`LeanPool.AsymptoticTrianglePacking.Internal.prob_coverage_deviation_le`) one obtains `exists_safe_round_cheb`: an outcome with

* fewer than `a` exceptional vertices, every other vertex having its safe degree within `t` of its
  mean, and
* at least `Q/2` covered vertices,

as soon as `N·Vs/(t²a) + Cvar/(Q/2)² < 1`.  With the codegree-tightened variance
`Vs ≈ 2γ³Δ²` (`LeanPool.AsymptoticTrianglePacking.Internal.safeDegree_variance_le_codegree`) the tolerance `t ≍ γ^{3/2}Δ` already
suffices, which is a factor `√γ` below the first-order per-round gain `≍ γΔ/8`.

This removes the `pairCount` bottleneck, but it is NOT yet enough to iterate: a schedule covering a
`c ≍ γ/(8r)` fraction per round needs the exceptional fraction `a/N ≈ Vs/(εγΔ)² ≈ 2γ/ε²` to be
`≪ c`, a constant-factor condition that no choice of `γ` satisfies.  See the caveat on
`LeanPool.AsymptoticTrianglePacking.Internal.safeDegree_variance_le_codegree`: closing that gap needs a third-order Bonferroni estimate,
which would turn `Vs ≈ 2γ³Δ²` into `Vs = O(γ⁴Δ²)`.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SafeDegreeVariance
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverVariance
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.Selection
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## The aggregated safe-degree badness -/

/-- The aggregated safe-degree badness of an outcome: `∑_v (safeDeg_v − 𝔼safeDeg_v)²/t²`.
It dominates the number of vertices whose safe degree deviates by `t` or more. -/
noncomputable def safeBad {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ v : V, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2 / t ^ 2

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem safeBad_nonneg {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (t : ℝ) (ω : Ω) : 0 ≤ safeBad ρ t ω :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem integrable_safeBad {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (t : ℝ) :
    Integrable (safeBad ρ t) (ℙ : Measure Ω) := by
  have h : safeBad ρ t = fun ω => ∑ v : V,
      ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2 / t ^ 2 := rfl
  rw [h]
  exact integrable_finset_sum _ fun v _ => (integrable_sq_centered_safeDegree ρ v).div_const _

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The number of vertices whose safe degree deviates by at least `t` is at most the aggregated
safe-degree badness. -/
theorem card_safeBadSet_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {t : ℝ} (ht : 0 < t) (ω : Ω) :
    ((Finset.univ.filter (fun v : V =>
        t ≤ |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v|)).card : ℝ)
      ≤ safeBad ρ t ω := by
  classical
  set f : V → ℝ := fun v =>
    ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2 / t ^ 2 with hf
  have hf0 : ∀ v : V, 0 ≤ f v := fun v => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hone : ∀ v ∈ Finset.univ.filter (fun v : V =>
      t ≤ |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v|),
      (1 : ℝ) ≤ f v := by
    intro v hv
    have hcase := (Finset.mem_filter.mp hv).2
    have h1 : t ^ 2
        ≤ ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2 := by
      rw [← sq_abs ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v)]
      exact pow_le_pow_left₀ ht.le hcase 2
    exact (one_le_div (by positivity)).mpr h1
  calc ((Finset.univ.filter (fun v : V =>
          t ≤ |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v|)).card : ℝ)
      = ∑ _v ∈ Finset.univ.filter (fun v : V =>
          t ≤ |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v|), (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v : V =>
          t ≤ |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v|), f v :=
        Finset.sum_le_sum hone
    _ ≤ ∑ v : V, f v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun v _ _ => hf0 v)

/-- The mean of the aggregated safe-degree badness, from the per-vertex variance bound. -/
theorem integral_safeBad_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {t Vs : ℝ} (ht : 0 < t)
    (hVs : ∀ v : V, ∫ ω, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2
        ∂(ℙ : Measure Ω) ≤ Vs) :
    ∫ ω, safeBad ρ t ω ∂(ℙ : Measure Ω) ≤ (Fintype.card V : ℝ) * (Vs / t ^ 2) := by
  simp only [safeBad]
  rw [integral_finset_sum _
    (fun v _ => (integrable_sq_centered_safeDegree ρ v).div_const _)]
  calc ∑ v : V, ∫ ω,
        ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2 / t ^ 2
          ∂(ℙ : Measure Ω)
      ≤ ∑ _v : V, Vs / t ^ 2 := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [integral_div]
        exact (div_le_div_iff_of_pos_right (by positivity)).mpr (hVs v)
    _ = (Fintype.card V : ℝ) * (Vs / t ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-! ## The round -/

/-- **The round with a direct safe-degree band.**  If the per-vertex safe-degree variance is at
most `Vs`, the covered-count variance at most `Cvar`, the expected coverage at least `Q > 0`, and

  `N·(Vs/t²)/a + Cvar/(Q/2)² < 1`,

then there is an outcome with fewer than `a` exceptional vertices, all remaining vertices having
their safe degree within `t` of its mean, and at least `Q/2` covered vertices. -/
theorem exists_safe_round_cheb {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p)
    {t a Q Vs Cvar : ℝ} (ht : 0 < t) (ha : 0 < a) (hQ : 0 < Q)
    (hVs : ∀ v : V, ∫ ω, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2
        ∂(ℙ : Measure Ω) ≤ Vs)
    (hmean : Q ≤ ∑ v : V, coverRate H p v)
    (hvar : ∫ ω, (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2
        ∂(ℙ : Measure Ω) ≤ Cvar)
    (hsmall : ((Fintype.card V : ℝ) * (Vs / t ^ 2)) / a + Cvar / (Q / 2) ^ 2 < 1) :
    ∃ ω : Ω, ∃ B : Finset V, (B.card : ℝ) < a ∧
      (∀ v ∉ B,
        |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v| < t)
      ∧ Q / 2 < ((covered (retainedSet H ρ ω)).card : ℝ) := by
  classical
  have hP1 : (ℙ : Measure Ω).real {ω | a ≤ safeBad ρ t ω}
      ≤ ((Fintype.card V : ℝ) * (Vs / t ^ 2)) / a := by
    refine le_trans (measureReal_ge_le_integral_div
      (fun ω => safeBad_nonneg ρ t ω) (integrable_safeBad ρ t) ha) ?_
    exact (div_le_div_iff_of_pos_right ha).mpr (integral_safeBad_le ρ ht hVs)
  have hP2 := prob_coverage_deviation_le ρ hQ hvar
  have hsum : (ℙ : Measure Ω).real {ω | a ≤ safeBad ρ t ω}
      + (ℙ : Measure Ω).real
        {ω | (Q / 2) ^ 2
          ≤ (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2} < 1 := by
    linarith
  obtain ⟨ω, hω1, hω2⟩ := exists_notMem_of_measureReal_add_lt_one hsum
  refine ⟨ω, Finset.univ.filter (fun v : V =>
    t ≤ |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v|), ?_, ?_, ?_⟩
  · have h1 := card_safeBadSet_le ρ ht ω
    have h2 : safeBad ρ t ω < a := by
      by_contra hc
      push_neg at hc
      exact hω1 hc
    linarith
  · intro v hv
    by_contra hc
    push_neg at hc
    exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
  · have h2 : ¬ ((Q / 2) ^ 2
        ≤ (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2) := hω2
    push_neg at h2
    by_contra hc
    push_neg at hc
    nlinarith only [h2, hmean, hc, hQ]

end LeanPool.AsymptoticTrianglePacking.Internal
