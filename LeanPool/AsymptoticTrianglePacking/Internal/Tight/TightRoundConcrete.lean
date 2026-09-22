/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.TightRound
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.LossVariance
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the tight round with CONCRETE parameters

`LeanPool.AsymptoticTrianglePacking.Internal.exists_tight_round` (in
`LeanPool.AsymptoticTrianglePacking.Internal.Tight.TightRound`) is stated with abstract moment
bounds
`Vb`, `Pb` and an abstract coverage rate `qlo`.  Here those abstract data are instantiated in terms
of the hypergraph parameters only:

* `r`   — the uniformity,
* `Δ`   — a global degree ceiling,
* `δ`   — a global degree floor,
* `κ`   — a codegree ceiling,
* `p`   — the retention probability.

The resulting statement `LeanPool.AsymptoticTrianglePacking.Internal.exists_tight_round_of_params`
is the tight nibble round in the form
in which the iteration consumes it: one round, one outcome, a two-sided band around the SAME centre
for all but `a` vertices, and a guaranteed coverage fraction.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## Concrete moment bounds -/

omit [Fintype V] in
/-- The uniform pair bound: two vertices are simultaneously covered with probability at most
`Δ²p² + κp`. -/
theorem prob_two_covered_le_params {H : Finset (Finset V)} {p : ℝ} {Δ κ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p)
    (hΔ : ∀ y : V, degree H y ≤ Δ) (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ)
    (u u' : V) (huu' : u ≠ u') :
    (ℙ : Measure Ω).real
        ({ω | u ∈ covered (retainedSet H ρ ω)} ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
      ≤ (Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p := by
  refine le_trans (prob_two_vertices_covered_le ρ hp0 u u') ?_
  have h1 : (degree H u : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u
  have h2 : (degree H u' : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u'
  have h3 : (codegree H u u' : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ u u' huu'
  have hd1 : (0 : ℝ) ≤ (degree H u : ℝ) := Nat.cast_nonneg _
  have hd2 : (0 : ℝ) ≤ (degree H u' : ℝ) := Nat.cast_nonneg _
  have hsq : (0 : ℝ) ≤ p ^ 2 := sq_nonneg p
  have hprod : (degree H u : ℝ) * (degree H u' : ℝ) ≤ (Δ : ℝ) * (Δ : ℝ) :=
    mul_le_mul h1 h2 hd2 (le_trans hd1 h1)
  linarith only [mul_le_mul_of_nonneg_right hprod hsq, mul_le_mul_of_nonneg_right h3 hp0]

/-- The variance of the loss weight in terms of the hypergraph parameters. -/
theorem centered_second_moment_le_params {H : Finset (Finset V)} {p : ℝ} {r Δ κ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ y : V, degree H y ≤ Δ)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) (v : V) :
    ∫ ω, (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 ∂(ℙ : Measure Ω)
      ≤ (κ : ℝ) * (((r : ℝ) - 1) * (Δ : ℝ)) * ((Δ : ℝ) * p)
        + ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) * (((r : ℝ) - 1) * (Δ : ℝ)) ^ 2 := by
  classical
  set εp : ℝ := (Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p with hεp
  have hε0 : 0 ≤ εp := by
    have : (0 : ℝ) ≤ (κ : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
    have h2 : (0 : ℝ) ≤ (Δ : ℝ) ^ 2 * p ^ 2 := by positivity
    rw [hεp]; linarith
  have hq : ∀ u : V, coverRate H p u ≤ (Δ : ℝ) * p := by
    intro u
    refine le_trans (coverRate_le hp0 hp1 u) ?_
    have : (degree H u : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u
    exact mul_le_mul_of_nonneg_right this hp0
  have hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u' ≤ εp := by
    intro u u' huu'
    have h1 := prob_two_covered_le_params ρ hp0 hΔ hκ u u' huu'
    have h2 : 0 ≤ coverRate H p u * coverRate H p u' :=
      mul_nonneg (coverRate_nonneg hp0 hp1 u) (coverRate_nonneg hp0 hp1 u')
    rw [hεp]; linarith
  have hκv : ∀ u : V, u ≠ v → codegree H v u ≤ κ := fun u hu => hκ v u (fun h => hu h.symm)
  have hmain := centered_second_moment_le ρ hp0 hp1 v hκv hq hε0 hpair
  -- rewrite the codegree sum
  have hsum : ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ)
      = ((r : ℝ) - 1) * (degree H v : ℝ) := by
    have h := sum_codegree_erase_eq hr v
    have hcast : ((∑ u ∈ (Finset.univ : Finset V).erase v, codegree H v u : ℕ) : ℝ)
        = ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) := by push_cast; ring
    rw [← hcast, h]
    push_cast [Nat.cast_sub hr1]
    ring
  rw [hsum] at hmain
  refine le_trans hmain ?_
  have hdv : (degree H v : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ v
  have hdv0 : (0 : ℝ) ≤ (degree H v : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    linarith
  have hA : ((r : ℝ) - 1) * (degree H v : ℝ) ≤ ((r : ℝ) - 1) * (Δ : ℝ) :=
    mul_le_mul_of_nonneg_left hdv hr0
  have hA0 : (0 : ℝ) ≤ ((r : ℝ) - 1) * (degree H v : ℝ) := mul_nonneg hr0 hdv0
  have hκ0 : (0 : ℝ) ≤ (κ : ℝ) := Nat.cast_nonneg _
  have hqhi0 : (0 : ℝ) ≤ (Δ : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
  have hsq : (((r : ℝ) - 1) * (degree H v : ℝ)) ^ 2 ≤ (((r : ℝ) - 1) * (Δ : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ hA0 hA 2
  have ht1 : (κ : ℝ) * (((r : ℝ) - 1) * (degree H v : ℝ)) * ((Δ : ℝ) * p)
      ≤ (κ : ℝ) * (((r : ℝ) - 1) * (Δ : ℝ)) * ((Δ : ℝ) * p) := by
    have := mul_le_mul_of_nonneg_left hA hκ0
    exact mul_le_mul_of_nonneg_right this hqhi0
  have ht2 : εp * (((r : ℝ) - 1) * (degree H v : ℝ)) ^ 2
      ≤ εp * (((r : ℝ) - 1) * (Δ : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left hsq hε0
  rw [hεp] at ht2 ⊢
  linarith

omit [Fintype V] in
/-- The mean of the pair count in terms of the hypergraph parameters. -/
theorem integral_pairCount_le_params {H : Finset (Finset V)} {p : ℝ} {r Δ κ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ y : V, degree H y ≤ Δ)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) (v : V) :
    ∫ ω, pairCount ρ v ω ∂(ℙ : Measure Ω)
      ≤ (Δ : ℝ) * ((r : ℝ) - 1) ^ 2 * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
  have hε0 : (0 : ℝ) ≤ (Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p := by
    have h1 : (0 : ℝ) ≤ (κ : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
    have h2 : (0 : ℝ) ≤ (Δ : ℝ) ^ 2 * p ^ 2 := by positivity
    linarith
  refine le_trans (integral_pairCount_le ρ hr hr1
    (fun u u' huu' => prob_two_covered_le_params ρ hp0 hΔ hκ u u' huu') hε0 v) ?_
  have hdv : (degree H v : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ v
  have hsq : (0 : ℝ) ≤ ((r : ℝ) - 1) ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_right hdv hsq
  exact mul_le_mul_of_nonneg_right this hε0

/-! ## The tight round with concrete parameters -/

/-- **The tight nibble round, concrete form.**

For an `r`-uniform hypergraph whose degrees lie in `[δ, Δ]` and whose codegrees are at most `κ`,
one Bernoulli round with retention probability `p` admits an outcome which

* covers more than a `qlo/2`-fraction of the vertex set, where `qlo = δ·p·(1−p)^{rΔ}`, and
* leaves every vertex outside an exceptional set of size `< a` with its safe degree inside the
  two-sided band `deg(v) − 𝔼[loss(v)] ± (t, t+s)`.

All the moment data are explicit functions of `r, Δ, κ, p`; the only requirement is the smallness
condition `hsmall`, which in the nibble regime `p = γ/Δ` is satisfied for `t ≍ ξ γ Δ`,
`s ≍ ξ γ Δ` and `a = θ·|V|` once `γ` is small. -/
theorem exists_tight_round_of_params {H : Finset (Finset V)} {p : ℝ} {r Δ δ κ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ y : V, degree H y ≤ Δ) (hδ : ∀ y : V, δ ≤ degree H y)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ)
    {t s a : ℝ} (ht : 0 < t) (hs : 0 < s) (ha : 0 < a) (hN : 0 < Fintype.card V)
    (hsmall :
      ((Fintype.card V : ℝ) *
          (((κ : ℝ) * (((r : ℝ) - 1) * (Δ : ℝ)) * ((Δ : ℝ) * p)
              + ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) * (((r : ℝ) - 1) * (Δ : ℝ)) ^ 2) / t ^ 2
            + ((Δ : ℝ) * ((r : ℝ) - 1) ^ 2 * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p)) / s))
        * (2 - (δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
      < a * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ)))) :
    ∃ ω : Ω, ∃ B : Finset V, (B.card : ℝ) < a ∧
      (∀ v ∉ B,
        (degree H v : ℝ) - lossWeightMean H p v - t
            ≤ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
          ∧ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
            ≤ (degree H v : ℝ) - lossWeightMean H p v + t + s)
      ∧ (Fintype.card V : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) / 2
          < ((covered (retainedSet H ρ ω)).card : ℝ) := by
  classical
  obtain ⟨v0⟩ := Fintype.card_pos_iff.mp hN
  -- the coverage floor
  have hqlo : ∀ v : V, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) ≤ coverRate H p v := by
    intro v
    refine le_trans ?_ (coverRate_ge hp0 hp1 hr hΔ v)
    have hd : (δ : ℝ) ≤ (degree H v : ℝ) := by exact_mod_cast hδ v
    have hfac : (0 : ℝ) ≤ p * (1 - p) ^ (r * Δ) :=
      mul_nonneg hp0 (pow_nonneg (by linarith) _)
    exact mul_le_mul_of_nonneg_right hd hfac
  have hqlo1 : (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) ≤ 1 := by
    refine le_trans (hqlo v0) ?_
    rw [← prob_vertex_covered_eq ρ hp0 hp1 v0]
    exact measureReal_le_one
  exact exists_tight_round ρ hp0 hp1 ht hs ha
    (fun v => centered_second_moment_le_params ρ hp0 hp1 hr1 hr hΔ hκ v)
    (fun v => integral_pairCount_le_params ρ hp0 hr1 hr hΔ hκ v)
    hqlo1 hqlo hN hsmall

end LeanPool.AsymptoticTrianglePacking.Internal
