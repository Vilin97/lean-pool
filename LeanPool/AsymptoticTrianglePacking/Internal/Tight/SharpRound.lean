/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.Pruning
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude
public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Survival
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverVariance
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.TightRound
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.LossVariance


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

public section

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

end





/-!
# LeanPool.AsymptoticTrianglePacking.Internal — one round preserves a TIGHT degree band on the
residual

`LeanPool.AsymptoticTrianglePacking.Internal.exists_tight_round_of_params` produces, for one
Bernoulli round, an outcome whose SAFE
degrees sit in a two-sided band around `deg(v) − 𝔼[loss(v)]`.  Here that is converted into the form
the iteration needs: a bound on the DEGREES OF THE RESIDUAL HYPERGRAPH, valid for every uncovered
vertex outside a small exceptional set, with the band expressed purely in the parameters
`r, Δ, δ, κ, p`.

The two ingredients are

* `LeanPool.AsymptoticTrianglePacking.Internal.lossWeightMean_le` /
  `LeanPool.AsymptoticTrianglePacking.Internal.lossWeightMean_ge` — the mean loss is squeezed
  between
  `(r−1)·δ·q_lo` and `(r−1)·Δ·q_hi`, so the centre of the band is itself pinned down; and
* `LeanPool.AsymptoticTrianglePacking.Internal.safeDegree_eq_residual_degree_of_not_covered` — on
  the event that `v` survives the round,
  its safe degree IS its residual degree.

The resulting band has width `(Δ − δ) + ((r−1)Δq_hi − (r−1)δq_lo) + 2t + s`.  In the nibble regime
`p = γ/Δ`, `Δ ≤ (1+μ)δ` with `μ, γ → 0` this is `(1 + o(1))` times the new mean degree — i.e. the
round MAINTAINS near-regularity, which is exactly what the refuted wide-band (`U/L ≤ 8`) peeling
cannot do.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## Squeezing the mean loss -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The mean loss is at most `(r−1)·deg(v)·q_hi`. -/
theorem lossWeightMean_le {H : Finset (Finset V)} {p : ℝ} {r : ℕ} {qhi : ℝ}
    (hr : IsUniform H r) (hr1 : 1 ≤ r) (hqhi : ∀ u : V, coverRate H p u ≤ qhi) (v : V) :
    lossWeightMean H p v ≤ ((r : ℝ) - 1) * (degree H v : ℝ) * qhi := by
  classical
  have hsum : ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ)
      = ((r : ℝ) - 1) * (degree H v : ℝ) := by
    have h := sum_codegree_erase_eq hr v
    have hcast : ((∑ u ∈ (Finset.univ : Finset V).erase v, codegree H v u : ℕ) : ℝ)
        = ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) := by push_cast; ring
    rw [← hcast, h]
    push_cast [Nat.cast_sub hr1]
    ring
  calc lossWeightMean H p v
      = ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * coverRate H p u := rfl
    _ ≤ ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * qhi :=
        Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hqhi u) (Nat.cast_nonneg _))
    _ = (∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ)) * qhi := by
        rw [Finset.sum_mul]
    _ = ((r : ℝ) - 1) * (degree H v : ℝ) * qhi := by rw [hsum]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The mean loss is at least `(r−1)·deg(v)·q_lo`. -/
theorem lossWeightMean_ge {H : Finset (Finset V)} {p : ℝ} {r : ℕ} {qlo : ℝ}
    (hr : IsUniform H r) (hr1 : 1 ≤ r) (hqlo : ∀ u : V, qlo ≤ coverRate H p u) (v : V) :
    ((r : ℝ) - 1) * (degree H v : ℝ) * qlo ≤ lossWeightMean H p v := by
  classical
  have hsum : ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ)
      = ((r : ℝ) - 1) * (degree H v : ℝ) := by
    have h := sum_codegree_erase_eq hr v
    have hcast : ((∑ u ∈ (Finset.univ : Finset V).erase v, codegree H v u : ℕ) : ℝ)
        = ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) := by push_cast; ring
    rw [← hcast, h]
    push_cast [Nat.cast_sub hr1]
    ring
  calc ((r : ℝ) - 1) * (degree H v : ℝ) * qlo
      = (∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ)) * qlo := by rw [hsum]
    _ = ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * qlo := by
        rw [Finset.sum_mul]
    _ ≤ ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * coverRate H p u :=
        Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hqlo u) (Nat.cast_nonneg _))
    _ = lossWeightMean H p v := rfl

/-! ## The residual band -/

/-- **One round maintains a tight degree band.**

For an `r`-uniform hypergraph with degrees in `[δ, Δ]` and codegrees `≤ κ`, there is a retained
subfamily `R' ⊆ H` (an outcome of the Bernoulli round) and an exceptional set `B` of size `< a`
such that every vertex that is left uncovered and lies outside `B` has its degree in the RESIDUAL
hypergraph inside the explicit band

`δ − (r−1)Δq_hi − t  ≤  deg_res(v)  ≤  Δ − (r−1)δq_lo + t + s`,

with `q_hi = Δp` and `q_lo = δp(1−p)^{rΔ}`; moreover the round covers more than a `q_lo/2`-fraction
of the vertex set. -/
theorem exists_round_residual_band {H : Finset (Finset V)} {p : ℝ} {r Δ δ κ : ℕ}
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
    ∃ R' : Finset (Finset V), R' ⊆ H ∧ ∃ B : Finset V, (B.card : ℝ) < a ∧
      (∀ v ∉ B, v ∉ covered R' →
        (δ : ℝ) - ((r : ℝ) - 1) * (Δ : ℝ) * ((Δ : ℝ) * p) - t
            ≤ (degree (Hypergraph.residual H R') v : ℝ)
          ∧ (degree (Hypergraph.residual H R') v : ℝ)
            ≤ (Δ : ℝ) - ((r : ℝ) - 1) * (δ : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
                + t + s)
      ∧ (Fintype.card V : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) / 2
          < ((covered R').card : ℝ) := by
  classical
  obtain ⟨ω, B, hBcard, hband, hcov⟩ :=
    exists_tight_round_of_params ρ hp0 hp1 hr1 hr hΔ hδ hκ ht hs ha hN hsmall
  refine ⟨retainedSet H ρ ω, Finset.filter_subset _ _, B, hBcard, ?_, hcov⟩
  intro v hv hvc
  obtain ⟨hlo, hup⟩ := hband v hv
  -- the safe degree is the residual degree for an uncovered vertex
  rw [safeDegree_eq_residual_degree_of_not_covered hvc] at hlo hup
  -- squeeze the mean loss
  have hqhi : ∀ u : V, coverRate H p u ≤ (Δ : ℝ) * p := by
    intro u
    refine le_trans (coverRate_le hp0 hp1 u) ?_
    have : (degree H u : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u
    exact mul_le_mul_of_nonneg_right this hp0
  have hqlo : ∀ u : V, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) ≤ coverRate H p u := by
    intro u
    refine le_trans ?_ (coverRate_ge hp0 hp1 hr hΔ u)
    have hd : (δ : ℝ) ≤ (degree H u : ℝ) := by exact_mod_cast hδ u
    have hfac : (0 : ℝ) ≤ p * (1 - p) ^ (r * Δ) := mul_nonneg hp0 (pow_nonneg (by linarith) _)
    exact mul_le_mul_of_nonneg_right hd hfac
  have hmeanle := lossWeightMean_le hr hr1 hqhi v
  have hmeange := lossWeightMean_ge hr hr1 hqlo v
  have hdvΔ : (degree H v : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ v
  have hdvδ : (δ : ℝ) ≤ (degree H v : ℝ) := by exact_mod_cast hδ v
  have hr0 : (0 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    linarith only [this]
  have hqhi0 : (0 : ℝ) ≤ (Δ : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
  have hqlo0 : (0 : ℝ) ≤ (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hp0 (pow_nonneg (by linarith) _))
  -- the centre is pinned between the two explicit values
  have hupper : lossWeightMean H p v ≤ ((r : ℝ) - 1) * (Δ : ℝ) * ((Δ : ℝ) * p) := by
    refine le_trans hmeanle ?_
    have := mul_le_mul_of_nonneg_left hdvΔ hr0
    exact mul_le_mul_of_nonneg_right this hqhi0
  have hlower : ((r : ℝ) - 1) * (δ : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
      ≤ lossWeightMean H p v := by
    refine le_trans ?_ hmeange
    have := mul_le_mul_of_nonneg_left hdvδ hr0
    exact mul_le_mul_of_nonneg_right this hqlo0
  constructor
  · linarith only [hlo, hdvδ, hupper]
  · linarith only [hup, hdvΔ, hlower]

end LeanPool.AsymptoticTrianglePacking.Internal

end



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

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the Chebyshev tight round in explicit hypergraph
parameters

This file instantiates `LeanPool.AsymptoticTrianglePacking.Internal.exists_tight_round_cheb` with
the codegree-tightened moment data of
`LeanPool.AsymptoticTrianglePacking.Internal.Tight.PairExcessCodegree` and converts it into the form
the iteration consumes: a bound on
the DEGREES OF THE RESIDUAL hypergraph for every uncovered vertex outside a small exceptional set,
together with a coverage guarantee.

Writing `N = |V|`, `q_lo = δ·p(1−p)^{rΔ}`, `q_hi = Δp` and

  `ε₂ = κp + 4r²κΔ²p³`,
  `Vb = κ(r−1)Δ·Δp + ε₂·((r−1)Δ)²`,
  `Pb = Δ(r−1)²(Δ²p² + κp)`,
  `Cvar = N·q_hi + N²·ε₂`,

the single hypothesis is

  `N(Vb/t² + Pb/s)/a + Cvar/(N q_lo/2)² < 1`.

In the nibble regime `p = γ/((r−1)Δ)`, `κ = μΔ`, `Δ ≍ δ ≍ d`, `a = θN`, `t = s = γ²d`:

* `Vb ≈ C_r μγ d²`, so `N·Vb/t²/a = Vb/(θ t²) ≈ C_r μ/(θγ³)`;
* `Pb ≈ C_r γ² d`, so `N·Pb/s/a = Pb/(θ s) ≈ C_r/(θ d)`;
* `Cvar/(N q_lo/2)² ≈ 4/(N γ) + 4 C_r μ/γ`.

All four terms are `< 1/4` once `μ ≤ c(r)θγ³`, `d ≥ d₀(r, θ)` and `N ≥ 16/γ` — and the tolerances
`t = s = γ²d` are SECOND order in `γ`, hence summable over the `≍ γ^{-1}log(1/β)` rounds of a
nibble. This is exactly what the Markov-coverage round
`LeanPool.AsymptoticTrianglePacking.Internal.exists_round_residual_band` cannot
provide (there `s ≳ γd/θ`, first order in `γ`).

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **The Chebyshev tight round in explicit parameters.**  For an `r`-uniform hypergraph with
degrees in `[δ, Δ]` and codegrees `≤ κ`, one Bernoulli round with retention probability `p` has an
outcome covering more than `N·q_lo/2` vertices and leaving all but `< a` vertices with a safe degree
in the band `deg(v) − 𝔼[loss(v)] ± (t, t+s)`. -/
theorem exists_tight_round_cheb_of_params {H : Finset (Finset V)} {p : ℝ} {r Δ δ κ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 < p) (hp1 : p < 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ y : V, degree H y ≤ Δ) (hδ : ∀ y : V, δ ≤ degree H y)
    (hδ0 : 0 < δ) (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ)
    {t s a : ℝ} (ht : 0 < t) (hs : 0 < s) (ha : 0 < a) (hN : 0 < Fintype.card V)
    (hsmall :
      ((Fintype.card V : ℝ) *
          (((κ : ℝ) * (((r : ℝ) - 1) * (Δ : ℝ)) * ((Δ : ℝ) * p)
              + ((κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3)
                * (((r : ℝ) - 1) * (Δ : ℝ)) ^ 2) / t ^ 2
            + ((Δ : ℝ) * ((r : ℝ) - 1) ^ 2 * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p)) / s)) / a
        + ((Fintype.card V : ℝ) * ((Δ : ℝ) * p)
            + (Fintype.card V : ℝ) ^ 2
              * ((κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3))
          / ((Fintype.card V : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) / 2) ^ 2
        < 1) :
    ∃ ω : Ω, ∃ B : Finset V, (B.card : ℝ) < a ∧
      (∀ v ∉ B,
        (degree H v : ℝ) - lossWeightMean H p v - t
            ≤ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
          ∧ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
            ≤ (degree H v : ℝ) - lossWeightMean H p v + t + s)
      ∧ (Fintype.card V : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) / 2
          < ((covered (retainedSet H ρ ω)).card : ℝ) := by
  classical
  have hp0' : (0 : ℝ) ≤ p := hp0.le
  have hp1' : p ≤ 1 := hp1.le
  have hN0 : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hN
  -- the covering-rate floor
  have hqlo : ∀ v : V, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) ≤ coverRate H p v := by
    intro v
    refine le_trans ?_ (coverRate_ge hp0' hp1' hr hΔ v)
    have hd : (δ : ℝ) ≤ (degree H v : ℝ) := by exact_mod_cast hδ v
    have hfac : (0 : ℝ) ≤ p * (1 - p) ^ (r * Δ) :=
      mul_nonneg hp0' (pow_nonneg (by linarith) _)
    exact mul_le_mul_of_nonneg_right hd hfac
  have hqlo0 : (0 : ℝ) < (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) := by
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    have : (0 : ℝ) < (1 - p) ^ (r * Δ) := pow_pos (by linarith) _
    positivity
  have hQ : (0 : ℝ) < (Fintype.card V : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) :=
    mul_pos hN0 hqlo0
  have hmean : (Fintype.card V : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
      ≤ ∑ v : V, coverRate H p v := by
    calc (Fintype.card V : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
        = ∑ _v : V, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ ∑ v : V, coverRate H p v := Finset.sum_le_sum (fun v _ => hqlo v)
  -- the covering-rate ceiling
  have hqhi : ∀ u : V, coverRate H p u ≤ (Δ : ℝ) * p := by
    intro u
    refine le_trans (coverRate_le hp0' hp1' u) ?_
    have : (degree H u : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u
    exact mul_le_mul_of_nonneg_right this hp0'
  -- the pair excess
  have hε0 : (0 : ℝ) ≤ (κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 := by
    have h1 : (0 : ℝ) ≤ (κ : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0'
    have h2 : (0 : ℝ) ≤ 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 :=
      mul_nonneg (by positivity) (pow_nonneg hp0' 3)
    linarith
  have hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u'
      ≤ (κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 :=
    fun u u' huu' => pair_excess_le_codegree ρ hp0' hp1' hr hr1 hΔ hκ huu'
  have hvar := coveredCount_variance_le ρ hp0' hp1' hqhi hε0 hpair
  exact exists_tight_round_cheb ρ ht hs ha hQ
    (fun v => centered_second_moment_le_codegree ρ hp0' hp1' hr1 hr hΔ hκ v)
    (fun v => integral_pairCount_le_params ρ hp0' hr1 hr hΔ hκ v)
    hmean hvar hsmall

/-- **One Chebyshev round maintains a tight degree band on the residual.**

Every vertex left uncovered and outside an exceptional set of size `< a` has its residual degree in
the band

  `δ − (r−1)Δq_hi − t  ≤  deg_res(v)  ≤  Δ − (r−1)δq_lo + t + s`,

and the round covers more than `N·q_lo/2` vertices. -/
theorem exists_round_residual_band_cheb {H : Finset (Finset V)} {p : ℝ} {r Δ δ κ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 < p) (hp1 : p < 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ y : V, degree H y ≤ Δ) (hδ : ∀ y : V, δ ≤ degree H y)
    (hδ0 : 0 < δ) (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ)
    {t s a : ℝ} (ht : 0 < t) (hs : 0 < s) (ha : 0 < a) (hN : 0 < Fintype.card V)
    (hsmall :
      ((Fintype.card V : ℝ) *
          (((κ : ℝ) * (((r : ℝ) - 1) * (Δ : ℝ)) * ((Δ : ℝ) * p)
              + ((κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3)
                * (((r : ℝ) - 1) * (Δ : ℝ)) ^ 2) / t ^ 2
            + ((Δ : ℝ) * ((r : ℝ) - 1) ^ 2 * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p)) / s)) / a
        + ((Fintype.card V : ℝ) * ((Δ : ℝ) * p)
            + (Fintype.card V : ℝ) ^ 2
              * ((κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3))
          / ((Fintype.card V : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) / 2) ^ 2
        < 1) :
    ∃ R' : Finset (Finset V), R' ⊆ H ∧ ∃ B : Finset V, (B.card : ℝ) < a ∧
      (∀ v ∉ B, v ∉ covered R' →
        (δ : ℝ) - ((r : ℝ) - 1) * (Δ : ℝ) * ((Δ : ℝ) * p) - t
            ≤ (degree (Hypergraph.residual H R') v : ℝ)
          ∧ (degree (Hypergraph.residual H R') v : ℝ)
            ≤ (Δ : ℝ) - ((r : ℝ) - 1) * (δ : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
                + t + s)
      ∧ (Fintype.card V : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) / 2
          < ((covered R').card : ℝ) := by
  classical
  have hp0' : (0 : ℝ) ≤ p := hp0.le
  have hp1' : p ≤ 1 := hp1.le
  obtain ⟨ω, B, hBcard, hband, hcov⟩ :=
    exists_tight_round_cheb_of_params ρ hp0 hp1 hr1 hr hΔ hδ hδ0 hκ ht hs ha hN hsmall
  refine ⟨retainedSet H ρ ω, Finset.filter_subset _ _, B, hBcard, ?_, hcov⟩
  intro v hv hvc
  obtain ⟨hlo, hup⟩ := hband v hv
  rw [safeDegree_eq_residual_degree_of_not_covered hvc] at hlo hup
  have hqhi : ∀ u : V, coverRate H p u ≤ (Δ : ℝ) * p := by
    intro u
    refine le_trans (coverRate_le hp0' hp1' u) ?_
    have : (degree H u : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u
    exact mul_le_mul_of_nonneg_right this hp0'
  have hqlo : ∀ u : V, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) ≤ coverRate H p u := by
    intro u
    refine le_trans ?_ (coverRate_ge hp0' hp1' hr hΔ u)
    have hd : (δ : ℝ) ≤ (degree H u : ℝ) := by exact_mod_cast hδ u
    have hfac : (0 : ℝ) ≤ p * (1 - p) ^ (r * Δ) := mul_nonneg hp0' (pow_nonneg (by linarith) _)
    exact mul_le_mul_of_nonneg_right hd hfac
  have hmeanle := lossWeightMean_le hr hr1 hqhi v
  have hmeange := lossWeightMean_ge hr hr1 hqlo v
  have hdvΔ : (degree H v : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ v
  have hdvδ : (δ : ℝ) ≤ (degree H v : ℝ) := by exact_mod_cast hδ v
  have hr0 : (0 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    linarith
  have hqhi0 : (0 : ℝ) ≤ (Δ : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0'
  have hqlo0 : (0 : ℝ) ≤ (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hp0' (pow_nonneg (by linarith) _))
  have hupper : lossWeightMean H p v ≤ ((r : ℝ) - 1) * (Δ : ℝ) * ((Δ : ℝ) * p) := by
    refine le_trans hmeanle ?_
    have := mul_le_mul_of_nonneg_left hdvΔ hr0
    exact mul_le_mul_of_nonneg_right this hqhi0
  have hlower : ((r : ℝ) - 1) * (δ : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
      ≤ lossWeightMean H p v := by
    refine le_trans ?_ hmeange
    have := mul_le_mul_of_nonneg_left hdvδ hr0
    exact mul_le_mul_of_nonneg_right this hqlo0
  exact ⟨by linarith, by linarith⟩

end LeanPool.AsymptoticTrianglePacking.Internal

end



/-!
# LeanPool.AsymptoticTrianglePacking.Internal — existence of a Bernoulli retention space

Standalone, Mathlib-only. The measure-theoretic prerequisite for the nibble iteration (step 2):
for any finite hypergraph `H` on a finite vertex type and any retention probability `p ∈ [0,1]`,
there EXISTS a probability space carrying a `BernoulliRetention` on `H` at `p` — an independent
family of events `A e` (`e` retained) each of probability `p`.

Standard construction: `Ω := Finset V → Bool` (finite, since `V` is a `Fintype`) with the product
Bernoulli(`p`) measure `Measure.pi (fun _ => (Bernoulli) p)`; `A e := {ω | ω e = true}`. The
coordinate events are independent (product measure) and each has probability `p`.

Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LeanPool.AsymptoticTrianglePacking.Internal

universe u

/-- **Existence of a Bernoulli retention.** For any finite hypergraph `H` on a finite vertex type
and any `p ∈ [0,1]`, there is a probability space carrying a `BernoulliRetention` on `H` at `p`. -/
theorem exists_bernoulliRetention {V : Type u} [Finite V] [DecidableEq V]
    (H : Finset (Finset V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ (Ω : Type u) (mΩ : MeasureSpace Ω),
      IsProbabilityMeasure (@MeasureSpace.volume Ω mΩ) ∧
        Nonempty (@BernoulliRetention V _ Ω mΩ H p) := by
  let _ : Fintype V := Fintype.ofFinite V
  let t : unitInterval := ⟨p, hp0, hp1⟩
  let μ : Measure Bool := bernoulliMeasure true false t
  let Ω := Finset V → Bool
  let mΩ : MeasureSpace Ω := ⟨Measure.pi (fun _ => μ)⟩
  refine ⟨Ω, mΩ, ?_, ?_⟩
  · let _ : MeasureSpace Ω := mΩ
    exact Measure.pi.instIsProbabilityMeasure (fun _ : Finset V => μ)
  · let _ : MeasureSpace Ω := mΩ
    let A : Finset V → Set Ω := fun e => {ω | ω e = true}
    have hmeas : ∀ e, MeasurableSet (A e) := by
      intro e
      change MeasurableSet ((fun ω : Ω => ω e) ⁻¹' ({true} : Set Bool))
      exact (measurable_pi_apply e) (measurableSet_singleton true)
    have hfun : iIndepFun (fun e (ω : Ω) => ω e)
        (Measure.pi (fun _ : Finset V => μ)) := by
      simpa only [id_eq] using
        (iIndepFun_pi (μ := fun _ : Finset V => μ) (X := fun _ => id)
          (fun _ => measurable_id.aemeasurable))
    have hpred : iIndepFun (fun e (ω : Ω) => ω e = true)
        (Measure.pi (fun _ : Finset V => μ)) := by
      change iIndepFun (fun e => (fun b => b = true) ∘ fun ω : Ω => ω e)
        (Measure.pi (fun _ : Finset V => μ))
      exact hfun.comp (fun _ b => b = true) (fun _ => Measurable.of_discrete)
    have hind : iIndepSet A (Measure.pi (fun _ : Finset V => μ)) := by
      rw [← iIndep_comap_mem_iff]
      apply (iIndepFun_iff_iIndep _ _ _).1
      simpa [A] using hpred
    refine ⟨⟨A, hmeas, ?_, ?_⟩⟩
    · change iIndepSet A (Measure.pi (fun _ : Finset V => μ))
      exact hind
    · intro e he
      rw [show (ℙ : Measure Ω) = Measure.pi (fun _ : Finset V => μ) by rfl]
      rw [show A e = Function.eval e ⁻¹' ({true} : Set Bool) by rfl]
      rw [← Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton true)]
      rw [Measure.pi_map_eval]
      have hμuniv : μ Set.univ = 1 := measure_univ
      rw [show ∏ j ∈ Finset.univ.erase e, μ Set.univ = 1 by
        exact Finset.prod_eq_one (fun _ _ => hμuniv)]
      rw [one_smul]
      change bernoulliMeasure true false t {true} = ENNReal.ofReal p
      rw [bernoulliMeasure_apply t (measurableSet_singleton true)]
      simpa [t] using ENNReal.coe_nnreal_eq (unitInterval.toNNReal t)

end LeanPool.AsymptoticTrianglePacking.Internal

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — a nibble round with FULLY EXPLICIT parameters

`LeanPool.AsymptoticTrianglePacking.Internal.exists_round_residual_band_cheb` produces a good round
outcome under one smallness
hypothesis relating the tolerances `t, s`, the exceptional budget `a` and the moment data.  Here
that hypothesis is DISCHARGED for a concrete parameter choice, giving an unconditional round.

For a round parameter `γ ∈ (0, 1/2]` and an exceptional fraction `θ ∈ (0,1]` put

  `p = γ/(rΔ)`,   `t = γ²Δ`,   `s = 16γ²Δ/θ`,   `a = θN`.

If the hypergraph is `r`-uniform (`r ≥ 2`) with degrees in `[δ, Δ]`, `1 ≤ δ`, `Δ ≤ 2δ`, codegrees at
most `κ ≤ θγ³Δ/(1280 r)` and `N = |V| ≥ 512r/γ`, then the Markov badness bound and the Chebyshev
coverage bound add up to at most `3/4` (`cheb_smallness_explicit`), so one round leaves all but
`< θN` of the surviving vertices with residual degree in

  `[δ − γΔ − γ²Δ,  Δ − (r−1)δγ/(4r) + γ²Δ + 16γ²Δ/θ]`

while covering more than `Nγ/(8r)` vertices (`exists_round_explicit`).

The point is that BOTH tolerances are of second order in `γ` (`γ²Δ`, up to the constant `16/θ`),
whereas the first-order drop is `≍ γΔ`.  That is what makes the round iterable: over the
`≍ γ^{-1}log(1/β)` rounds of a nibble the tolerances accumulate to `≍ γ·log(1/β)/θ → 0`, while with
the Markov-coverage round (`LeanPool.AsymptoticTrianglePacking.Internal.exists_round_residual_band`)
the tolerance `s` is necessarily
first order in `γ` and the accumulation does not vanish.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

universe u

/-! ## The arithmetic core

All the estimates below are inequalities between real numbers; `R` is the uniformity, `D` the
degree ceiling, `dd` the degree floor, `k` the codegree ceiling, `N` the number of vertices and
`L = (1−p)^{rΔ}` the conflict factor of the covering rate. -/

private theorem auxS {R γ : ℝ} (hR : 2 ≤ R) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) :
    (R - 1) + (1 + 4 * γ ^ 2) * (R - 1) ^ 2 ≤ 3 * R ^ 2 := by
  have h1 : (1 + 4 * γ ^ 2) ≤ 2 := by nlinarith
  have h2 : (R - 1) ^ 2 ≤ R ^ 2 := by nlinarith
  have h3 : (R - 1) ≤ R ^ 2 := by nlinarith
  nlinarith [sq_nonneg (R - 1)]

private theorem auxA1 {R D k γ θ : ℝ} (hR : 2 ≤ R) (hD : 1 ≤ D) (hk0 : 0 ≤ k) (hγ0 : 0 < γ)
    (hF4 : k * (1280 * R) ≤ θ * γ ^ 3 * D) :
    k * γ * D * (3 * R ^ 2) ≤ θ / 8 * ((γ ^ 2 * D) ^ 2 * R) := by
  have hRpos : (0:ℝ) < R := by linarith
  have hDpos : (0:ℝ) < D := by linarith
  have key : (0:ℝ) ≤ θ * γ ^ 3 * D - 24 * k * R := by nlinarith
  nlinarith only [mul_nonneg (by positivity : (0:ℝ) ≤ γ * D * R / 8) key]

private theorem auxPb {R D k γ : ℝ} (hR : 2 ≤ R) (hD : 1 ≤ D) (hk0 : 0 ≤ k) (hγ0 : 0 < γ)
    (hkR : 512 * k * R ≤ γ * D) :
    (R - 1) ^ 2 * γ * (D * γ + k * R) ≤ 2 * D * γ ^ 2 * R ^ 2 := by
  have hRpos : (0:ℝ) < R := by linarith
  have hDpos : (0:ℝ) < D := by linarith
  have h3 : D * γ + k * R ≤ 2 * (γ * D) := by nlinarith
  calc (R - 1) ^ 2 * γ * (D * γ + k * R) ≤ (R - 1) ^ 2 * γ * (2 * (γ * D)) := by
        apply mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ R ^ 2 * γ * (2 * (γ * D)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [hγ0.le]
    _ = 2 * D * γ ^ 2 * R ^ 2 := by ring

private theorem auxNum1 {R N γ : ℝ} (hR : 2 ≤ R) (hγ0 : 0 < γ) (hNpos : 0 < N)
    (hNγ : 512 * R ≤ N * γ) :
    N * (γ / R) ≤ 1 / 4 * (N ^ 2 * γ ^ 2 / (64 * R ^ 2)) := by
  have hRpos : (0:ℝ) < R := by linarith
  have key : 1 / 4 * (N ^ 2 * γ ^ 2 / (64 * R ^ 2)) - N * (γ / R)
      = N * γ * (N * γ - 256 * R) / (256 * R ^ 2) := by field_simp; ring
  have h0 : 0 ≤ N * γ * (N * γ - 256 * R) / (256 * R ^ 2) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by positivity) (by linarith)
  linarith

private theorem auxNum2 {R D k γ : ℝ} (hR : 2 ≤ R) (hD : 1 ≤ D) (hγ0 : 0 < γ)
    (hkR : 512 * k * R ≤ γ * D) :
    2 * k * γ / (R * D) ≤ γ ^ 2 / (256 * R ^ 2) := by
  have hRpos : (0:ℝ) < R := by linarith
  have hDpos : (0:ℝ) < D := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [mul_nonneg (mul_nonneg hγ0.le hRpos.le)
    (by linarith : (0 : ℝ) ≤ γ * D - 512 * k * R)]

private theorem auxkR {R D k γ θ : ℝ} (hR : 2 ≤ R) (hD : 1 ≤ D) (hk0 : 0 ≤ k) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1 / 2) (hθ1 : θ ≤ 1)
    (hF4 : k * (1280 * R) ≤ θ * γ ^ 3 * D) : 512 * k * R ≤ γ * D := by
  have hDpos : (0:ℝ) < D := by linarith
  have hγ2 : γ ^ 2 ≤ 1 := by nlinarith
  have hγ3 : γ ^ 3 ≤ γ := by nlinarith only [mul_le_mul_of_nonneg_left hγ2 hγ0.le]
  have ha : θ * γ ^ 3 * D ≤ γ ^ 3 * D := by
    nlinarith [mul_nonneg (pow_nonneg hγ0.le 3) hDpos.le]
  have hb : γ ^ 3 * D ≤ γ * D := by nlinarith [hDpos.le]
  have hkR0 : (0:ℝ) ≤ k * R := mul_nonneg hk0 (by linarith)
  linarith

private theorem auxEps {R D k γ : ℝ} (hR : 2 ≤ R) (hD : 1 ≤ D) (hk0 : 0 ≤ k) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1 / 2) : k * γ * (1 + 4 * γ ^ 2) * (R * D) ≤ 2 * k * γ * (R * D) := by
  have hRD : (0:ℝ) ≤ R * D := by nlinarith
  have h1 : (1 : ℝ) + 4 * γ ^ 2 ≤ 2 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hk0 hγ0.le) hRD]

/-- **The covering-rate floor for the explicit parameters:** `δ·p·L ≥ γ/(4r)`. -/
theorem cheb_qlo_explicit {R D dd γ L p : ℝ} (hR : 2 ≤ R) (hD : 1 ≤ D) (hdd1 : 1 ≤ dd)
    (hDdd : D ≤ 2 * dd) (hγ0 : 0 < γ) (hL0 : 1 / 2 ≤ L) (hp : p = γ / (R * D)) :
    γ / (4 * R) ≤ dd * (p * L) := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hDpos : (0 : ℝ) < D := by linarith
  have hppos : 0 < p := by rw [hp]; positivity
  have hEDp : D * p = γ / R := by rw [hp]; field_simp
  have h1 : (D / 2) * (p * (1 / 2)) ≤ dd * (p * L) := by
    apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left (by linarith) hppos.le)
      (by positivity) (by linarith)
  have h2 : (D / 2) * (p * (1 / 2)) = (D * p) / 4 := by ring
  have h3 : (D * p) / 4 = γ / (4 * R) := by rw [hEDp]; field_simp
  rw [h2, h3] at h1
  exact h1
/-- **The smallness condition of the Chebyshev round holds for the explicit parameter choice.**
The Markov badness bound is at most `1/4` and the Chebyshev coverage bound at most `1/2`. -/
theorem cheb_smallness_explicit {R D dd k N γ θ L p t s a : ℝ}
    (hR : 2 ≤ R) (hD : 1 ≤ D) (hdd1 : 1 ≤ dd) (hDdd : D ≤ 2 * dd)
    (hk0 : 0 ≤ k) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hL0 : 1 / 2 ≤ L)
    (hk : k ≤ θ * γ ^ 3 * D / (1280 * R)) (hN : 512 * R / γ ≤ N)
    (hp : p = γ / (R * D)) (ht : t = γ ^ 2 * D) (hs : s = 16 * γ ^ 2 * D / θ) (ha : a = θ * N) :
    (N * ((k * ((R - 1) * D) * (D * p)
            + (k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3) * ((R - 1) * D) ^ 2) / t ^ 2
          + (D * (R - 1) ^ 2 * (D ^ 2 * p ^ 2 + k * p)) / s)) / a
      + (N * (D * p) + N ^ 2 * (k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3))
        / (N * (dd * (p * L)) / 2) ^ 2 < 1 := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hDpos : (0 : ℝ) < D := by linarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hppos : 0 < p := by rw [hp]; positivity
  have hNγ : 512 * R ≤ N * γ := by rw [div_le_iff₀ hγ0] at hN; linarith
  have hF4 : k * (1280 * R) ≤ θ * γ ^ 3 * D := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 1280 * R)] at hk; linarith
  have hkR : 512 * k * R ≤ γ * D := auxkR hR hD hk0 hγ0 hγ1 hθ1 hF4
  have hEDp : D * p = γ / R := by rw [hp]; field_simp
  have hEVb : k * ((R - 1) * D) * (D * p)
      + (k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3) * ((R - 1) * D) ^ 2
      = k * γ * D * ((R - 1) + (1 + 4 * γ ^ 2) * (R - 1) ^ 2) / R := by rw [hp]; field_simp
  have hEPb : D * (R - 1) ^ 2 * (D ^ 2 * p ^ 2 + k * p)
      = (R - 1) ^ 2 * γ * (D * γ + k * R) / R ^ 2 := by rw [hp]; field_simp
  have hEε : k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3 = k * γ * (1 + 4 * γ ^ 2) / (R * D) := by
    rw [hp]; field_simp
  have hε0 : 0 ≤ k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3 := by rw [hEε]; positivity
  have hεle : k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3 ≤ 2 * k * γ / (R * D) := by
    rw [hEε, div_le_div_iff₀ (by positivity) (by positivity)]
    exact auxEps hR hD hk0 hγ0 hγ1
  have hA1 : (k * ((R - 1) * D) * (D * p)
      + (k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3) * ((R - 1) * D) ^ 2) / t ^ 2 ≤ θ / 8 := by
    rw [hEVb, ht, div_div, div_le_iff₀ (by positivity)]
    have h1 : k * γ * D * ((R - 1) + (1 + 4 * γ ^ 2) * (R - 1) ^ 2) ≤ k * γ * D * (3 * R ^ 2) :=
      mul_le_mul_of_nonneg_left (auxS hR hγ0 hγ1) (by positivity)
    have h2 := auxA1 hR hD hk0 hγ0 hF4
    linarith
  have hA2 : (D * (R - 1) ^ 2 * (D ^ 2 * p ^ 2 + k * p)) / s ≤ θ / 8 := by
    have hspos : (0:ℝ) < s := by rw [hs]; positivity
    rw [hEPb, div_le_iff₀ hspos, hs]
    have heq : θ / 8 * (16 * γ ^ 2 * D / θ) = 2 * γ ^ 2 * D := by field_simp; ring
    rw [heq, div_le_iff₀ (by positivity : (0:ℝ) < R ^ 2)]
    linarith only [auxPb hR hD hk0 hγ0 hkR]
  have hA : (N * ((k * ((R - 1) * D) * (D * p)
            + (k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3) * ((R - 1) * D) ^ 2) / t ^ 2
          + (D * (R - 1) ^ 2 * (D ^ 2 * p ^ 2 + k * p)) / s)) / a ≤ 1 / 4 := by
    rw [ha, div_le_iff₀ (by positivity)]
    calc N * ((k * ((R - 1) * D) * (D * p)
            + (k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3) * ((R - 1) * D) ^ 2) / t ^ 2
          + (D * (R - 1) ^ 2 * (D ^ 2 * p ^ 2 + k * p)) / s)
        ≤ N * (θ / 8 + θ / 8) := mul_le_mul_of_nonneg_left (by linarith) hNpos.le
      _ = 1 / 4 * (θ * N) := by ring
  have hqlo : γ / (4 * R) ≤ dd * (p * L) := cheb_qlo_explicit hR hD hdd1 hDdd hγ0 hL0 hp
  have hDenLowPos : (0:ℝ) < (N * (γ / (4 * R)) / 2) ^ 2 := by positivity
  have hDenLow : (N * (γ / (4 * R)) / 2) ^ 2 ≤ (N * (dd * (p * L)) / 2) ^ 2 := by
    have h1 : N * (γ / (4 * R)) / 2 ≤ N * (dd * (p * L)) / 2 := by
      have := mul_le_mul_of_nonneg_left hqlo hNpos.le; linarith
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hNum0 : 0 ≤ N * (D * p) + N ^ 2 * (k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3) := by
    have h1 : 0 ≤ N * (D * p) := by positivity
    have h2 := mul_nonneg (sq_nonneg N) hε0
    linarith
  have hNumB : N * (D * p) + N ^ 2 * (k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3)
      ≤ 1 / 2 * (N * (γ / (4 * R)) / 2) ^ 2 := by
    have hden : (N * (γ / (4 * R)) / 2) ^ 2 = N ^ 2 * γ ^ 2 / (64 * R ^ 2) := by
      field_simp; ring
    rw [hden, hEDp]
    have hone := auxNum1 hR hγ0 hNpos hNγ
    have htwo : N ^ 2 * (k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3)
        ≤ 1 / 4 * (N ^ 2 * γ ^ 2 / (64 * R ^ 2)) := by
      have hstep : N ^ 2 * (k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3)
          ≤ N ^ 2 * (2 * k * γ / (R * D)) := mul_le_mul_of_nonneg_left hεle (sq_nonneg N)
      have hfin : N ^ 2 * (2 * k * γ / (R * D)) ≤ N ^ 2 * (γ ^ 2 / (256 * R ^ 2)) :=
        mul_le_mul_of_nonneg_left (auxNum2 hR hD hγ0 hkR) (sq_nonneg N)
      have heq : N ^ 2 * (γ ^ 2 / (256 * R ^ 2)) = 1 / 4 * (N ^ 2 * γ ^ 2 / (64 * R ^ 2)) := by
        field_simp; ring
      rw [heq] at hfin
      linarith
    linarith
  have hB : (N * (D * p) + N ^ 2 * (k * p + 4 * R ^ 2 * k * D ^ 2 * p ^ 3))
      / (N * (dd * (p * L)) / 2) ^ 2 ≤ 1 / 2 := by
    refine le_trans (div_le_div_of_nonneg_left hNum0 hDenLowPos hDenLow) ?_
    rw [div_le_iff₀ hDenLowPos]
    linarith only [hNumB]
  linarith only [hA, hB]

/-! ## The round -/
/-- **A nibble round with explicit parameters.**

For `r ≥ 2`, `γ ∈ (0,1/2]`, `θ ∈ (0,1]`, an `r`-uniform hypergraph with degrees in `[δ, Δ]`,
`1 ≤ δ`, `Δ ≤ 2δ`, codegrees `≤ κ ≤ θγ³Δ/(1280r)` and `|V| ≥ 512r/γ`, there is a retained subfamily
`R' ⊆ H` and an exceptional set `B` of fewer than `θ|V|` vertices such that

* every vertex outside `B` that the round leaves uncovered has residual degree in
  `[δ − γΔ − γ²Δ, Δ − (r−1)δγ/(4r) + γ²Δ + 16γ²Δ/θ]`, and
* the round covers more than `|V|γ/(8r)` vertices. -/
theorem exists_round_explicit {V : Type u} [Fintype V] [DecidableEq V]
    {H : Finset (Finset V)} {r Δ δ κ : ℕ} {γ θ : ℝ}
    (hr2 : 2 ≤ r) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ y : V, degree H y ≤ Δ) (hδ : ∀ y : V, δ ≤ degree H y)
    (hδ1 : 1 ≤ δ) (hΔδ : (Δ : ℝ) ≤ 2 * (δ : ℝ))
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ)
    (hκsmall : (κ : ℝ) ≤ θ * γ ^ 3 * (Δ : ℝ) / (1280 * (r : ℝ)))
    (hNbig : 512 * (r : ℝ) / γ ≤ (Fintype.card V : ℝ)) :
    ∃ R' : Finset (Finset V), R' ⊆ H ∧ ∃ B : Finset V,
      (B.card : ℝ) < θ * (Fintype.card V : ℝ) ∧
      (∀ v ∉ B, v ∉ covered R' →
        (δ : ℝ) - γ * (Δ : ℝ) - γ ^ 2 * (Δ : ℝ) ≤ (degree (Hypergraph.residual H R') v : ℝ)
          ∧ (degree (Hypergraph.residual H R') v : ℝ)
            ≤ (Δ : ℝ) - ((r : ℝ) - 1) * (δ : ℝ) * (γ / (4 * (r : ℝ)))
                + γ ^ 2 * (Δ : ℝ) + 16 * γ ^ 2 * (Δ : ℝ) / θ)
      ∧ (Fintype.card V : ℝ) * γ / (8 * (r : ℝ)) < ((covered R').card : ℝ) := by
  classical
  -- basic numerics
  have hR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hRpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) := lt_of_lt_of_le (by positivity) hNbig
  have hNcard : 0 < Fintype.card V := by exact_mod_cast hNpos
  obtain ⟨v0⟩ := Fintype.card_pos_iff.mp hNcard
  have hδΔ : δ ≤ Δ := le_trans (hδ v0) (hΔ v0)
  have hδ0 : 0 < δ := hδ1
  have hdd1 : (1 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ1
  have hD : (1 : ℝ) ≤ (Δ : ℝ) := by
    have : (δ : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hδΔ
    linarith
  have hDpos : (0 : ℝ) < (Δ : ℝ) := by linarith
  set p : ℝ := γ / ((r : ℝ) * (Δ : ℝ)) with hpdef
  have hppos : 0 < p := by rw [hpdef]; positivity
  have hrΔp : ((r * Δ : ℕ) : ℝ) * p = γ := by
    rw [hpdef]; push_cast; field_simp
  have hplt : p < 1 := by
    have h1 : p ≤ γ := by
      rw [hpdef, div_le_iff₀ (by positivity)]
      linarith only [mul_nonneg hγ0.le
        (show (0:ℝ) ≤ (r : ℝ) * (Δ : ℝ) - 1 by nlinarith only [hR, hD])]
    linarith
  -- the conflict factor `L = (1−p)^{rΔ}`
  set L : ℝ := (1 - p) ^ (r * Δ) with hLdef
  have hL1 : L ≤ 1 := by
    rw [hLdef]; exact pow_le_one₀ (by linarith) (by linarith)
  have hL0 : 1 / 2 ≤ L := by
    have hbern : 1 + ((r * Δ : ℕ) : ℝ) * (-p) ≤ (1 + (-p)) ^ (r * Δ) :=
      one_add_mul_le_pow (by linarith) (r * Δ)
    have h1 : 1 + ((r * Δ : ℕ) : ℝ) * (-p) = 1 - γ := by
      have : ((r * Δ : ℕ) : ℝ) * (-p) = -(((r * Δ : ℕ) : ℝ) * p) := by ring
      rw [this, hrΔp]; ring
    have h2 : (1 + (-p)) ^ (r * Δ) = L := by rw [hLdef]; ring_nf
    rw [h1, h2] at hbern
    linarith
  -- the smallness condition
  have hsmall := cheb_smallness_explicit (R := (r : ℝ)) (D := (Δ : ℝ)) (dd := (δ : ℝ))
    (k := (κ : ℝ)) (N := (Fintype.card V : ℝ)) (γ := γ) (θ := θ) (L := L) (p := p)
    (t := γ ^ 2 * (Δ : ℝ)) (s := 16 * γ ^ 2 * (Δ : ℝ) / θ) (a := θ * (Fintype.card V : ℝ))
    hR hD hdd1 hΔδ (Nat.cast_nonneg _) hγ0 hγ1 hθ0 hθ1 hL0 hκsmall hNbig hpdef rfl rfl rfl
  -- the round
  obtain ⟨Ω, mΩ, hprob, ⟨ρ⟩⟩ := exists_bernoulliRetention (V := V) H hppos.le hplt.le
  let _ : MeasureSpace Ω := mΩ
  have _ : IsProbabilityMeasure (ℙ : Measure Ω) := hprob
  obtain ⟨R', hR'H, B, hBcard, hband, hcov⟩ :=
    exists_round_residual_band_cheb (H := H) (p := p) (r := r) (Δ := Δ) (δ := δ) (κ := κ) ρ
      hppos hplt (by omega) hr hΔ hδ hδ0 hκ (by positivity) (by positivity) (by positivity)
      hNcard hsmall
  refine ⟨R', hR'H, B, hBcard, ?_, ?_⟩
  · intro v hv hvc
    obtain ⟨hlo, hup⟩ := hband v hv hvc
    have hqlo : γ / (4 * (r : ℝ)) ≤ (δ : ℝ) * (p * L) :=
      cheb_qlo_explicit hR hD hdd1 hΔδ hγ0 hL0 hpdef
    have hlow' : (δ : ℝ) - γ * (Δ : ℝ) - γ ^ 2 * (Δ : ℝ)
        ≤ (δ : ℝ) - ((r : ℝ) - 1) * (Δ : ℝ) * ((Δ : ℝ) * p) - γ ^ 2 * (Δ : ℝ) := by
      have hDp : (Δ : ℝ) * p = γ / (r : ℝ) := by rw [hpdef]; field_simp
      have : ((r : ℝ) - 1) * (Δ : ℝ) * ((Δ : ℝ) * p) ≤ γ * (Δ : ℝ) := by
        rw [hDp]
        have hfrac : ((r : ℝ) - 1) * (Δ : ℝ) * (γ / (r : ℝ)) = γ * (Δ : ℝ) * (((r : ℝ) - 1) / r) :=
          by field_simp
        rw [hfrac]
        have hle : ((r : ℝ) - 1) / (r : ℝ) ≤ 1 := by rw [div_le_one hRpos]; linarith
        linarith only [mul_le_mul_of_nonneg_left hle (mul_nonneg hγ0.le hDpos.le)]
      linarith
    have hup' : (Δ : ℝ) - ((r : ℝ) - 1) * (δ : ℝ) * ((δ : ℝ) * (p * L))
          + γ ^ 2 * (Δ : ℝ) + 16 * γ ^ 2 * (Δ : ℝ) / θ
        ≤ (Δ : ℝ) - ((r : ℝ) - 1) * (δ : ℝ) * (γ / (4 * (r : ℝ)))
          + γ ^ 2 * (Δ : ℝ) + 16 * γ ^ 2 * (Δ : ℝ) / θ := by
      have hmul : ((r : ℝ) - 1) * (δ : ℝ) * (γ / (4 * (r : ℝ)))
          ≤ ((r : ℝ) - 1) * (δ : ℝ) * ((δ : ℝ) * (p * L)) :=
        mul_le_mul_of_nonneg_left hqlo
          (mul_nonneg (by linarith : (0:ℝ) ≤ (r : ℝ) - 1) (by positivity))
      linarith
    exact ⟨by linarith, by linarith⟩
  · have hqlo : γ / (4 * (r : ℝ)) ≤ (δ : ℝ) * (p * L) :=
      cheb_qlo_explicit hR hD hdd1 hΔδ hγ0 hL0 hpdef
    have h2 : (Fintype.card V : ℝ) * (γ / (4 * (r : ℝ))) / 2
        ≤ (Fintype.card V : ℝ) * ((δ : ℝ) * (p * L)) / 2 := by
      have := mul_le_mul_of_nonneg_left hqlo hNpos.le
      linarith
    have heq : (Fintype.card V : ℝ) * (γ / (4 * (r : ℝ))) / 2
        = (Fintype.card V : ℝ) * γ / (8 * (r : ℝ)) := by field_simp; ring
    rw [heq] at h2
    linarith [hcov]

end LeanPool.AsymptoticTrianglePacking.Internal

end


/-!
# Iterable tight-band round

This module establishes the one-round estimates used by the finite near-regular hypergraph nibble.
It packages retention, concentration, degree-band, codegree, and cover-rate bounds in a form that
can be iterated by the schedule.
-/

public section

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-- **The iterable (sharp) nibble round.**

For uniformity `r ≥ 2` and free parameters

* `γ` — the round rate (retention `p = γ/(rΔ)`),
* `ε` — the relative tolerance: both band tolerances are `ε·γΔ`, a factor `ε` below the first-order
  per-round gain `≍ γΔ`,
* `θ` — the exceptional fraction: at most `θ|V|` vertices leave the band,
* `α` — the guaranteed relative size of the live set `A`,

there are a degree threshold `D₀` and a codegree factor `c₀` such that every `r`-uniform hypergraph
`K` with

* a GLOBAL degree ceiling `Δ`,
* a degree floor `δ` on the live set `A`, with `Δ ≤ 2δ`,
* codegrees at most `κ ≤ c₀Δ`,
* `Δ ≥ D₀`, `|V| ≥ D₀` and `|A| ≥ α|V|`,

admits a retained set `R' ⊆ K` and an exceptional set `B`, `|B| ≤ θ|V|`, such that

* every live, uncovered `v ∉ B` has residual degree at least `δ − ((r−1)/r)γΔ − εγΔ` and at most
  `Δ − ((r−1)/r)·γ·(δ − lost(v))·δ·(1−γ)/Δ + εγΔ`, where `lost(v) = lostDegree K Aᶜ v` counts the
  edges at `v` leaving `A`, and
* the round covers at least a `γ/(8r)` fraction of `A`. -/
@[expose] def SharpRoundFor (r : ℕ) (γ ε θ α D₀ c₀ : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (K : Finset (Finset V)) (A : Finset V)
    (δ Δ κ : ℝ),
    IsUniform K r →
    (∀ v : V, (degree K v : ℝ) ≤ Δ) →
    (∀ v ∈ A, δ ≤ (degree K v : ℝ)) →
    (∀ x y : V, x ≠ y → (codegree K x y : ℝ) ≤ κ) →
    0 ≤ κ → κ ≤ c₀ * Δ → D₀ ≤ Δ → Δ ≤ 2 * δ →
    D₀ ≤ (Fintype.card V : ℝ) → α * (Fintype.card V : ℝ) ≤ (A.card : ℝ) →
    ∃ R' : Finset (Finset V), R' ⊆ K ∧ ∃ B : Finset V,
      (B.card : ℝ) ≤ θ * (Fintype.card V : ℝ) ∧
      (∀ v ∈ A, v ∉ B → v ∉ covered R' →
        δ - ((r : ℝ) - 1) / r * γ * Δ - ε * γ * Δ
            ≤ (degree (Hypergraph.residual K R') v : ℝ)
        ∧ (degree (Hypergraph.residual K R') v : ℝ)
            ≤ Δ - ((r : ℝ) - 1) / r * γ * (δ - (lostDegree K Aᶜ v : ℝ)) * δ * (1 - γ) / Δ
                + ε * γ * Δ) ∧
      γ / (8 * (r : ℝ)) * (A.card : ℝ) ≤ ((covered R').card : ℝ)

/-- **The iterable (sharp) nibble round**, packaged: for every uniformity and every choice of the
four free parameters there are a degree threshold `D₀` and a codegree factor `c₀` for which
`LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundFor` holds. -/
def SharpRoundHyp : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (γ ε θ α : ℝ), 0 < γ → γ ≤ 1 / 2 → 0 < ε → ε ≤ 1 →
      0 < θ → θ ≤ 1 → 0 < α → α ≤ 1 →
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ SharpRoundFor r γ ε θ α D₀ c₀

end LeanPool.AsymptoticTrianglePacking.Internal
