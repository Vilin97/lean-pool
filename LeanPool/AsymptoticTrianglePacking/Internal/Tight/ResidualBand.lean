/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.TightRoundConcrete
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

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
  have hsafe : safeDegree H (covered (retainedSet H ρ ω)) v
      = degree (Hypergraph.residual H (retainedSet H ρ ω)) v :=
    safeDegree_eq_residual_degree_of_not_covered hvc
  rw [hsafe] at hlo hup
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
