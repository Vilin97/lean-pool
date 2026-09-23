/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.TwoEdgeMatch
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.ConflictCount
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.LossVariance
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the CODEGREE-tightened pair excess and loss variance

`LeanPool.AsymptoticTrianglePacking.Internal.pair_excess_le` bounds the pair excess

  `ℙ(u, u' covered) − q_u q_{u'}  ≤  2 r Δ³ p³ + κ p`

by trading the crude product bound `deg(u)·deg(u')·p²` against the exact rates.  Its `Δ³p³` term is
too lossy for the nibble: fed into
`LeanPool.AsymptoticTrianglePacking.Internal.centered_second_moment_le` it contributes
`(r−1)²Δ² · 2rΔ³p³ ≈ Δ² γ³` to the variance of the loss weight (with `p = γ/((r−1)Δ)`), i.e. a
standard deviation of order `γ^{3/2}Δ`, whose Chebyshev failure probability at the natural scale
`t = ξγΔ` is `≈ γ/ξ²` — of the same order as the per-round covering rate `≈ γ`, hence useless for
an exceptional set that must be a *small* fraction of the coverage.

This file replaces that term by a CODEGREE-controlled one:

  `ℙ(u, u' covered) − q_u q_{u'}  ≤  κ p + 4 r² κ Δ² p³`     (`pair_excess_le_codegree`)

for distinct `u, u'`.  The proof is the exact edge-pair decomposition, not a union bound:

* `{u covered} ∩ {u' covered} = ⋃_{f ∋ u} ⋃_{g ∋ u'} (M_f ∩ M_g)` with `M_f` the event that `f`
  enters the round matching;
* for `f ≠ g` the joint matching probability differs from the product `q_f q_g` by at most
  `|conflicts f ∩ conflicts g|·p³`
  (`LeanPool.AsymptoticTrianglePacking.Internal.prob_two_matched_le` — zero when `f` and `g` meet);
* the diagonal `f = g` occurs for at most `codeg(u,u') ≤ κ` edges, each contributing at most `p`;
* `LeanPool.AsymptoticTrianglePacking.Internal.sum_conflicts_inter_card_le` sums the conflict
  overlaps to `4 r² κ Δ²`.

Consequently (`centered_second_moment_le_codegree`)

  `𝔼[(loss − 𝔼loss)²] ≤ κ·(r−1)Δ·(Δp) + (κp + 4r²κΔ²p³)·((r−1)Δ)²`,

which in the nibble regime `p = γ/((r−1)Δ)`, `κ = μΔ` is `O(r μ γ Δ²)` — a factor `μ` (the relative
codegree, which the nibble hypothesis lets us choose as small as we like) below the previous
`O(rγ³Δ²/(r−1))`, and it is the bound whose Chebyshev failure probability at scale `t = ξγΔ` is
`O(rμ/(ξ²γ))`, i.e. arbitrarily small compared with the covering rate `γ`.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [Fintype V] in
/-- The matching event of a single edge has probability `p·(1−p)^{c(e)}`. -/
theorem prob_matchingEvent {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {e : Finset V} (he : e ∈ H) :
    (ℙ : Measure Ω).real {ω | e ∈ roundMatching (retainedSet H ρ ω)}
      = p * (1 - p) ^ (conflicts H e).card := by
  rw [measureReal_def, matchingEvent_eq ρ he, edge_survives_prob ρ hp0 hp1 he,
    ENNReal.toReal_ofReal (mul_nonneg hp0 (pow_nonneg (by linarith) _))]

omit [Fintype V] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The joint covering event of two vertices is the union of the joint matching events of the edge
pairs through them. -/
theorem twoCovered_eq_biUnion {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (u u' : V) :
    ({ω | u ∈ covered (retainedSet H ρ ω)} ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
      = ⋃ f ∈ H.filter (fun f => u ∈ f), ⋃ g ∈ H.filter (fun g => u' ∈ g),
          ({ω | f ∈ roundMatching (retainedSet H ρ ω)}
            ∩ {ω | g ∈ roundMatching (retainedSet H ρ ω)}) := by
  rw [vertexCovered_eq_biUnion ρ u, vertexCovered_eq_biUnion ρ u']
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨⟨f, hf, hfω⟩, ⟨g, hg, hgω⟩⟩
    exact ⟨f, hf, g, hg, hfω, hgω⟩
  · rintro ⟨f, hf, g, hg, hfω, hgω⟩
    exact ⟨⟨f, hf, hfω⟩, ⟨g, hg, hgω⟩⟩

omit [Fintype V] in
/-- **The codegree-tightened joint covering bound.**  For distinct `u, u'`,
`ℙ(u,u' covered) ≤ q_u q_{u'} + codeg(u,u')·p + (∑_{f ∋ u} ∑_{g ∋ u'} |conf f ∩ conf g|)·p³`. -/
theorem prob_two_vertices_covered_le_sum {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u u' : V) :
    (ℙ : Measure Ω).real
        ({ω | u ∈ covered (retainedSet H ρ ω)} ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
      ≤ coverRate H p u * coverRate H p u' + (codegree H u u' : ℝ) * p
        + (∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
            ((conflicts H f ∩ conflicts H g).card : ℝ)) * p ^ 3 := by
  classical
  set Su := H.filter (fun f => u ∈ f) with hSu
  set Su' := H.filter (fun g => u' ∈ g) with hSu'
  -- term-by-term bound on the joint matching probabilities
  have hterm : ∀ f ∈ Su, ∀ g ∈ Su',
      (ℙ : Measure Ω).real ({ω | f ∈ roundMatching (retainedSet H ρ ω)}
          ∩ {ω | g ∈ roundMatching (retainedSet H ρ ω)})
        ≤ (p * (1 - p) ^ (conflicts H f).card) * (p * (1 - p) ^ (conflicts H g).card)
          + (if f = g then p else 0)
          + ((conflicts H f ∩ conflicts H g).card : ℝ) * p ^ 3 := by
    intro f hf g hg
    have hfH : f ∈ H := (Finset.mem_filter.mp hf).1
    have hgH : g ∈ H := (Finset.mem_filter.mp hg).1
    by_cases hfg : f = g
    · subst hfg
      have hself : ({ω | f ∈ roundMatching (retainedSet H ρ ω)}
          ∩ {ω | f ∈ roundMatching (retainedSet H ρ ω)})
          = {ω | f ∈ roundMatching (retainedSet H ρ ω)} := Set.inter_self _
      rw [hself, prob_matchingEvent ρ hp0 hp1 hfH, ite_eq_left rfl]
      have h1 : p * (1 - p) ^ (conflicts H f).card ≤ p := by
        have : (1 - p) ^ (conflicts H f).card ≤ 1 :=
          pow_le_one₀ (by linarith) (by linarith)
        nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ 1 - p) (conflicts H f).card]
      have h2 : 0 ≤ (p * (1 - p) ^ (conflicts H f).card) * (p * (1 - p) ^ (conflicts H f).card) :=
        mul_nonneg (mul_nonneg hp0 (pow_nonneg (by linarith) _))
          (mul_nonneg hp0 (pow_nonneg (by linarith) _))
      have h3 : 0 ≤ ((conflicts H f ∩ conflicts H f).card : ℝ) * p ^ 3 :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 3)
      linarith
    · rw [ite_eq_right hfg]
      have := prob_two_matched_le ρ hp0 hp1 hfH hgH hfg
      linarith
  -- sum the bounds
  have hmeas : (ℙ : Measure Ω).real
      ({ω | u ∈ covered (retainedSet H ρ ω)} ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
      ≤ ∑ f ∈ Su, ∑ g ∈ Su', (ℙ : Measure Ω).real
          ({ω | f ∈ roundMatching (retainedSet H ρ ω)}
            ∩ {ω | g ∈ roundMatching (retainedSet H ρ ω)}) := by
    rw [twoCovered_eq_biUnion ρ u u']
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    exact Finset.sum_le_sum (fun f _ => measureReal_biUnion_finset_le _ _)
  refine le_trans hmeas ?_
  refine le_trans (Finset.sum_le_sum (fun f hf => Finset.sum_le_sum (fun g hg =>
    hterm f hf g hg))) ?_
  -- split the three contributions
  have hsplit : ∑ f ∈ Su, ∑ g ∈ Su',
        ((p * (1 - p) ^ (conflicts H f).card) * (p * (1 - p) ^ (conflicts H g).card)
          + (if f = g then p else 0)
          + ((conflicts H f ∩ conflicts H g).card : ℝ) * p ^ 3)
      = (∑ f ∈ Su, ∑ g ∈ Su',
            (p * (1 - p) ^ (conflicts H f).card) * (p * (1 - p) ^ (conflicts H g).card))
        + (∑ f ∈ Su, ∑ g ∈ Su', (if f = g then p else 0))
        + (∑ f ∈ Su, ∑ g ∈ Su', ((conflicts H f ∩ conflicts H g).card : ℝ) * p ^ 3) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun f _ => by rw [← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib])
  rw [hsplit]
  have h1 : (∑ f ∈ Su, ∑ g ∈ Su',
        (p * (1 - p) ^ (conflicts H f).card) * (p * (1 - p) ^ (conflicts H g).card))
      = coverRate H p u * coverRate H p u' := by
    rw [coverRate, coverRate, ← hSu, ← hSu', Finset.sum_mul_sum]
  have h2 : (∑ f ∈ Su, ∑ g ∈ Su', (if f = g then p else 0)) = (codegree H u u' : ℝ) * p := by
    have hin : ∀ f ∈ Su, (∑ g ∈ Su', (if f = g then p else 0))
        = if f ∈ Su' then p else 0 := by
      intro f _
      by_cases hf' : f ∈ Su'
      · rw [Finset.sum_ite_eq Su' f (fun _ => p), ite_eq_left hf']
      · rw [ite_eq_right hf']
        refine Finset.sum_eq_zero (fun g hg => ?_)
        rw [ite_eq_right (fun h => hf' (by rw [h]; exact hg))]
    rw [Finset.sum_congr rfl hin, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard : (Su ∩ Su').card = codegree H u u' := by
      have hset : Su ∩ Su' = H.filter (fun e => u ∈ e ∧ u' ∈ e) := by
        rw [hSu, hSu']
        ext e
        simp only [Finset.mem_inter, Finset.mem_filter]
        tauto
      rw [hset]; rfl
    rw [hcard]
  have h3 : (∑ f ∈ Su, ∑ g ∈ Su', ((conflicts H f ∩ conflicts H g).card : ℝ) * p ^ 3)
      = (∑ f ∈ Su, ∑ g ∈ Su', ((conflicts H f ∩ conflicts H g).card : ℝ)) * p ^ 3 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun f _ => by rw [Finset.sum_mul])
  rw [h1, h2, h3]

omit [Fintype V] in
/-- **The codegree-tightened pair excess.**  For distinct `u, u'`,

  `ℙ(u,u' covered) − q_u q_{u'} ≤ κ p + 4 r² κ Δ² p³`.

Both summands carry the codegree bound `κ`; in the nibble regime `κ = μΔ`, `p = γ/((r−1)Δ)` this is
`O(rμγ/(r−1))`, whereas `LeanPool.AsymptoticTrianglePacking.Internal.pair_excess_le` gives only
`O(rγ³/(r−1)³ + μγ/(r−1))`. -/
theorem pair_excess_le_codegree {H : Finset (Finset V)} {p : ℝ} {r Δ κ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hr1 : 1 ≤ r) (hΔ : ∀ y, degree H y ≤ Δ)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) {u u' : V} (huu' : u ≠ u') :
    (ℙ : Measure Ω).real
        ({ω | u ∈ covered (retainedSet H ρ ω)} ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u'
      ≤ (κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 := by
  classical
  have hmain := prob_two_vertices_covered_le_sum ρ hp0 hp1 u u'
  have hcod : ((codegree H u u' : ℕ) : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ u u' huu'
  have hcodp : (codegree H u u' : ℝ) * p ≤ (κ : ℝ) * p := mul_le_mul_of_nonneg_right hcod hp0
  have hsumnat := sum_conflicts_inter_card_le hr hr1 hΔ hκ huu'
  have hsum : (∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
      ((conflicts H f ∩ conflicts H g).card : ℝ))
      ≤ 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 := by
    have hcast : (∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
        ((conflicts H f ∩ conflicts H g).card : ℝ))
        = ((∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
            (conflicts H f ∩ conflicts H g).card : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    have := (Nat.cast_le (α := ℝ)).mpr hsumnat
    calc ((∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
          (conflicts H f ∩ conflicts H g).card : ℕ) : ℝ)
        ≤ ((4 * r ^ 2 * κ * Δ ^ 2 : ℕ) : ℝ) := this
      _ = 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 := by push_cast; ring
  have hp3 : (0 : ℝ) ≤ p ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_right hsum hp3
  linarith

/-- **The codegree-tightened variance of the loss weight.**

  `𝔼[(loss − 𝔼loss)²] ≤ κ·(r−1)Δ·(Δp) + (κp + 4r²κΔ²p³)·((r−1)Δ)²`.

Compare `LeanPool.AsymptoticTrianglePacking.Internal.centered_second_moment_le_params`, whose second
factor is `Δ²p² + κp`: the term
`Δ²p²` (of order `γ²` with `p = γ/((r−1)Δ)`) is replaced by `4r²κΔ²p³` (of order `r²μγ³`), so the
whole bound acquires the codegree factor `κ`. -/
theorem centered_second_moment_le_codegree {H : Finset (Finset V)} {p : ℝ} {r Δ κ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ y : V, degree H y ≤ Δ)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) (v : V) :
    ∫ ω, (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 ∂(ℙ : Measure Ω)
      ≤ (κ : ℝ) * (((r : ℝ) - 1) * (Δ : ℝ)) * ((Δ : ℝ) * p)
        + ((κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3)
          * (((r : ℝ) - 1) * (Δ : ℝ)) ^ 2 := by
  classical
  set εp : ℝ := (κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 with hεp
  have hε0 : 0 ≤ εp := by
    have h1 : (0 : ℝ) ≤ (κ : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
    have h2 : (0 : ℝ) ≤ 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 :=
      mul_nonneg (by positivity) (pow_nonneg hp0 3)
    rw [hεp]; linarith
  have hq : ∀ x : V, coverRate H p x ≤ (Δ : ℝ) * p := by
    intro x
    refine le_trans (coverRate_le hp0 hp1 x) ?_
    have : (degree H x : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ x
    exact mul_le_mul_of_nonneg_right this hp0
  have hpair : ∀ x y : V, x ≠ y →
      (ℙ : Measure Ω).real ({ω | x ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | y ∈ covered (retainedSet H ρ ω)})
        - coverRate H p x * coverRate H p y ≤ εp := by
    intro x y hxy
    exact pair_excess_le_codegree ρ hp0 hp1 hr hr1 hΔ hκ hxy
  have hκv : ∀ x : V, x ≠ v → codegree H v x ≤ κ := fun x hx => hκ v x (fun h => hx h.symm)
  have hmain := centered_second_moment_le ρ hp0 hp1 v hκv hq hε0 hpair
  have hsum : ∑ x ∈ (Finset.univ : Finset V).erase v, (codegree H v x : ℝ)
      = ((r : ℝ) - 1) * (degree H v : ℝ) := by
    have h := sum_codegree_erase_eq hr v
    have hcast : ((∑ x ∈ (Finset.univ : Finset V).erase v, codegree H v x : ℕ) : ℝ)
        = ∑ x ∈ (Finset.univ : Finset V).erase v, (codegree H v x : ℝ) := by push_cast; ring
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
  have hsq : (((r : ℝ) - 1) * (degree H v : ℝ)) ^ 2 ≤ (((r : ℝ) - 1) * (Δ : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hA0 hA 2
  have ht1 : (κ : ℝ) * (((r : ℝ) - 1) * (degree H v : ℝ)) * ((Δ : ℝ) * p)
      ≤ (κ : ℝ) * (((r : ℝ) - 1) * (Δ : ℝ)) * ((Δ : ℝ) * p) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hκ0) hqhi0
  have ht2 : εp * (((r : ℝ) - 1) * (degree H v : ℝ)) ^ 2
      ≤ εp * (((r : ℝ) - 1) * (Δ : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left hsq hε0
  rw [hεp] at ht2 ⊢
  linarith

end LeanPool.AsymptoticTrianglePacking.Internal
