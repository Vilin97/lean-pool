/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverWeightMoments
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the variance of the loss weight

Quantitative form of `LeanPool.AsymptoticTrianglePacking.Internal.integral_sq_centered_lossWeight`.
Two ingredients:

* `pair_excess_le` — the *pair excess* `ℙ(u,u' covered) − q_u q_{u'}` is at most
  `2rΔ³p³ + κp`.  Both summands are genuinely of higher order than `q ≈ Δp`: the first because it
  carries an extra factor `rΔp ≈ γ`, the second because it carries the CODEGREE `κ`.  (The exact
  covering rate `q_u` is bounded below by `deg(u)·p(1−p)^{rΔ}`, `coverRate_ge`, which is what lets
  the crude second-moment bound `deg·deg·p²` of `prob_two_vertices_covered_le` be traded against the
  product `q_u q_{u'}`.)
* `sum_codegree_erase_eq` — `∑_{u ≠ v} codeg(v,u) = (r−1)·deg(v)`, the total weight of the linear
  form.

Together they give `centered_second_moment_le`:

  `𝔼[(loss − 𝔼 loss)²] ≤ κ·A·q_hi + ε₂·A²`,  `A = (r−1)·deg(v)`,

which in the nibble regime `p = γ/(rΔ)`, `κ = μΔ` is `O(μΔ²γ + Δ²(γ³/r² + μγ)) = o(Δ²)`.  This is
the concentration that the residual degree does not have.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [Fintype V] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **Lower bound on the exact covering rate.** -/
theorem coverRate_ge {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ y, degree H y ≤ Δ) (x : V) :
    (degree H x : ℝ) * (p * (1 - p) ^ (r * Δ)) ≤ coverRate H p x := by
  classical
  have hq0 : (0 : ℝ) ≤ 1 - p := by linarith
  rw [coverRate]
  calc (degree H x : ℝ) * (p * (1 - p) ^ (r * Δ))
      = ∑ _f ∈ H.filter (fun f => x ∈ f), p * (1 - p) ^ (r * Δ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ ∑ f ∈ H.filter (fun f => x ∈ f), p * (1 - p) ^ (conflicts H f).card := by
        refine Finset.sum_le_sum (fun f hf => ?_)
        refine mul_le_mul_of_nonneg_left ?_ hp0
        exact pow_le_pow_of_le_one hq0 (by linarith)
          (conflicts_card_le_of_uniform hr hΔ (Finset.mem_filter.mp hf).1)

omit [Fintype V] in
/-- **The pair excess.**  For `x ≠ y`, `ℙ(x,y covered) − q_x q_y ≤ 2rΔ³p³ + κp`. -/
theorem pair_excess_le {H : Finset (Finset V)} {p : ℝ} {r Δ κ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ y, degree H y ≤ Δ)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) {x y : V} (hxy : x ≠ y) :
    (ℙ : Measure Ω).real
        ({ω | x ∈ covered (retainedSet H ρ ω)} ∩ {ω | y ∈ covered (retainedSet H ρ ω)})
        - coverRate H p x * coverRate H p y
      ≤ 2 * (r : ℝ) * (Δ : ℝ) ^ 3 * p ^ 3 + (κ : ℝ) * p := by
  have hq0 : (0 : ℝ) ≤ 1 - p := by linarith
  have hcrude := prob_two_vertices_covered_le ρ hp0 x y
  have hcod : ((codegree H x y : ℕ) : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ x y hxy
  -- lower bounds on the two covering rates
  have hgx := coverRate_ge (H := H) (p := p) (r := r) (Δ := Δ) hp0 hp1 hr hΔ x
  have hgy := coverRate_ge (H := H) (p := p) (r := r) (Δ := Δ) hp0 hp1 hr hΔ y
  have hnn : ∀ z : V, (0 : ℝ) ≤ (degree H z : ℝ) * (p * (1 - p) ^ (r * Δ)) := by
    intro z; positivity
  -- the product of the two lower bounds
  have hprod : (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2 * ((1 - p) ^ (r * Δ)) ^ 2
      ≤ coverRate H p x * coverRate H p y := by
    have := mul_le_mul hgx hgy (hnn y) (le_trans (hnn x) hgx)
    calc (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2 * ((1 - p) ^ (r * Δ)) ^ 2
        = ((degree H x : ℝ) * (p * (1 - p) ^ (r * Δ)))
          * ((degree H y : ℝ) * (p * (1 - p) ^ (r * Δ))) := by ring
      _ ≤ coverRate H p x * coverRate H p y := this
  -- Bernoulli: 1 − (1−p)^{2rΔ} ≤ 2rΔ p
  have hbern : 1 - 2 * (r : ℝ) * (Δ : ℝ) * p ≤ ((1 - p) ^ (r * Δ)) ^ 2 := by
    have h1 := one_add_mul_le_pow (a := -p) (by linarith) (2 * (r * Δ))
    have h2 : ((1 : ℝ) + -p) ^ (2 * (r * Δ)) = ((1 - p) ^ (r * Δ)) ^ 2 := by
      rw [show (2 : ℕ) * (r * Δ) = (r * Δ) * 2 by ring, pow_mul]
      ring_nf
    rw [h2] at h1
    have h3 : ((2 * (r * Δ) : ℕ) : ℝ) = 2 * (r : ℝ) * (Δ : ℝ) := by push_cast; ring
    calc 1 - 2 * (r : ℝ) * (Δ : ℝ) * p = 1 + ((2 * (r * Δ) : ℕ) : ℝ) * (-p) := by
          rw [h3]; ring
      _ ≤ ((1 - p) ^ (r * Δ)) ^ 2 := h1
  -- degrees bounded by Δ
  have hdx : (degree H x : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ x
  have hdy : (degree H y : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ y
  have hdx0 : (0 : ℝ) ≤ (degree H x : ℝ) := Nat.cast_nonneg _
  have hdy0 : (0 : ℝ) ≤ (degree H y : ℝ) := Nat.cast_nonneg _
  have hpow0 : (0 : ℝ) ≤ ((1 - p) ^ (r * Δ)) ^ 2 := by positivity
  have hpow1 : ((1 - p) ^ (r * Δ)) ^ 2 ≤ 1 := by
    have : (1 - p) ^ (r * Δ) ≤ 1 := pow_le_one₀ hq0 (by linarith)
    nlinarith [pow_nonneg hq0 (r * Δ)]
  -- the deficit of the crude bound against the product
  have hdef : (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2
      - (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2 * ((1 - p) ^ (r * Δ)) ^ 2
      ≤ 2 * (r : ℝ) * (Δ : ℝ) ^ 3 * p ^ 3 := by
    have hbase : (0 : ℝ) ≤ (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2 := by positivity
    have hxy2 : (degree H x : ℝ) * (degree H y : ℝ) ≤ (Δ : ℝ) * (Δ : ℝ) :=
      mul_le_mul hdx hdy hdy0 (le_trans hdx0 hdx)
    have hcap : (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2 ≤ (Δ : ℝ) ^ 2 * p ^ 2 := by
      calc (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2
          ≤ ((Δ : ℝ) * (Δ : ℝ)) * p ^ 2 := mul_le_mul_of_nonneg_right hxy2 (sq_nonneg p)
        _ = (Δ : ℝ) ^ 2 * p ^ 2 := by ring
    have hstep : (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2
        - (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2 * ((1 - p) ^ (r * Δ)) ^ 2
        ≤ ((degree H x : ℝ) * (degree H y : ℝ) * p ^ 2) * (2 * (r : ℝ) * (Δ : ℝ) * p) := by
      nlinarith only [hbase, hbern]
    have hrp : (0 : ℝ) ≤ 2 * (r : ℝ) * (Δ : ℝ) * p := by positivity
    calc (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2
        - (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2 * ((1 - p) ^ (r * Δ)) ^ 2
        ≤ ((degree H x : ℝ) * (degree H y : ℝ) * p ^ 2) * (2 * (r : ℝ) * (Δ : ℝ) * p) := hstep
      _ ≤ ((Δ : ℝ) ^ 2 * p ^ 2) * (2 * (r : ℝ) * (Δ : ℝ) * p) :=
          mul_le_mul_of_nonneg_right hcap hrp
      _ = 2 * (r : ℝ) * (Δ : ℝ) ^ 3 * p ^ 3 := by ring
  have hcodp : (codegree H x y : ℝ) * p ≤ (κ : ℝ) * p :=
    mul_le_mul_of_nonneg_right hcod hp0
  linarith

/-- The total weight of the linear form: `∑_{u ≠ v} codeg(v,u) = (r−1)·deg(v)`. -/
theorem sum_codegree_erase_eq {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r) (v : V) :
    ∑ u ∈ (Finset.univ : Finset V).erase v, codegree H v u = (r - 1) * degree H v := by
  classical
  have h := coverWeight_eq_sum H v (Finset.univ : Finset V)
  rw [coverWeight] at h
  rw [h]
  have hall : ∀ e ∈ H.filter (fun e => v ∈ e),
      (e.erase v ∩ (Finset.univ : Finset V)).card = r - 1 :=
    fun e he => by
      rw [Finset.inter_univ, Finset.card_erase_of_mem (Finset.mem_filter.mp he).2,
        hr e (Finset.mem_filter.mp he).1]
  rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, mul_comm]
  rfl

/-- **The quantitative variance bound for the loss weight.** -/
theorem centered_second_moment_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V)
    {κ : ℕ} {qhi ε₂ : ℝ}
    (hκ : ∀ u : V, u ≠ v → codegree H v u ≤ κ)
    (hq : ∀ u : V, coverRate H p u ≤ qhi) (hε0 : 0 ≤ ε₂)
    (hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u' ≤ ε₂) :
    ∫ ω, (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 ∂(ℙ : Measure Ω)
      ≤ (κ : ℝ) * (∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ)) * qhi
        + ε₂ * (∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ)) ^ 2 := by
  classical
  set S := (Finset.univ : Finset V).erase v with hS
  set A : ℝ := ∑ u ∈ S, (codegree H v u : ℝ) with hA
  rw [integral_sq_centered_lossWeight ρ hp0 hp1 v]
  -- term-by-term bound
  have hterm : ∀ u ∈ S, ∀ u' ∈ S,
      (codegree H v u : ℝ) * (codegree H v u' : ℝ)
          * ((ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
              ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
            - coverRate H p u * coverRate H p u')
        ≤ (if u = u' then (codegree H v u : ℝ) * (κ : ℝ) * qhi else 0)
          + (codegree H v u : ℝ) * (codegree H v u' : ℝ) * ε₂ := by
    intro u hu u' hu'
    have ha0 : (0 : ℝ) ≤ (codegree H v u : ℝ) := Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ (codegree H v u' : ℝ) := Nat.cast_nonneg _
    by_cases huu' : u = u'
    · subst huu'
      have hself : ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u ∈ covered (retainedSet H ρ ω)}) = {ω | u ∈ covered (retainedSet H ρ ω)} :=
        Set.inter_self _
      rw [hself, prob_vertex_covered_eq ρ hp0 hp1 u, ite_eq_left rfl]
      have hqu0 : 0 ≤ coverRate H p u := coverRate_nonneg hp0 hp1 u
      have haκ : (codegree H v u : ℝ) ≤ (κ : ℝ) := by
        exact_mod_cast hκ u (Finset.mem_erase.mp hu).1
      have h1 : (codegree H v u : ℝ) * (codegree H v u : ℝ)
          * (coverRate H p u - coverRate H p u * coverRate H p u)
          ≤ (codegree H v u : ℝ) * (κ : ℝ) * qhi := by
        have hstep : (codegree H v u : ℝ) * (codegree H v u : ℝ)
            * (coverRate H p u - coverRate H p u * coverRate H p u)
            ≤ (codegree H v u : ℝ) * (codegree H v u : ℝ) * coverRate H p u := by
          nlinarith only [mul_nonneg ha0 ha0, mul_nonneg hqu0 hqu0]
        have hκ0 : (0 : ℝ) ≤ (κ : ℝ) := Nat.cast_nonneg _
        have hstep2 : (codegree H v u : ℝ) * (codegree H v u : ℝ) * coverRate H p u
            ≤ (codegree H v u : ℝ) * (κ : ℝ) * qhi := by
          calc (codegree H v u : ℝ) * (codegree H v u : ℝ) * coverRate H p u
              ≤ (codegree H v u : ℝ) * (κ : ℝ) * coverRate H p u := by
                nlinarith only [mul_nonneg (mul_nonneg ha0 hqu0) (sub_nonneg.mpr haκ)]
            _ ≤ (codegree H v u : ℝ) * (κ : ℝ) * qhi := by
                nlinarith only [mul_nonneg (mul_nonneg ha0 hκ0) (sub_nonneg.mpr (hq u))]
        linarith
      linarith [mul_nonneg (mul_nonneg ha0 ha0) hε0]
    · rw [ite_eq_right huu']
      have hp2 := hpair u u' huu'
      nlinarith only [mul_nonneg (mul_nonneg ha0 hb0) (sub_nonneg.mpr hp2)]
  calc ∑ u ∈ S, ∑ u' ∈ S,
        (codegree H v u : ℝ) * (codegree H v u' : ℝ)
          * ((ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
              ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
            - coverRate H p u * coverRate H p u')
      ≤ ∑ u ∈ S, ∑ u' ∈ S, ((if u = u' then (codegree H v u : ℝ) * (κ : ℝ) * qhi else 0)
          + (codegree H v u : ℝ) * (codegree H v u' : ℝ) * ε₂) :=
        Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun u' hu' => hterm u hu u' hu'))
    _ = (κ : ℝ) * A * qhi + ε₂ * A ^ 2 := by
        have hinner : ∀ u ∈ S,
            ∑ u' ∈ S, ((if u = u' then (codegree H v u : ℝ) * (κ : ℝ) * qhi else 0)
              + (codegree H v u : ℝ) * (codegree H v u' : ℝ) * ε₂)
            = (codegree H v u : ℝ) * (κ : ℝ) * qhi
              + (codegree H v u : ℝ) * ε₂ * (∑ u' ∈ S, (codegree H v u' : ℝ)) := by
          intro u hu
          rw [Finset.sum_add_distrib,
            Finset.sum_ite_eq S u (fun _ => (codegree H v u : ℝ) * (κ : ℝ) * qhi), ite_eq_left hu]
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun u' _ => by ring)
        rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
        have e1 : ∑ u ∈ S, (codegree H v u : ℝ) * (κ : ℝ) * qhi = (κ : ℝ) * A * qhi := by
          rw [hA, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun u _ => by ring)
        have e2 : ∑ u ∈ S, (codegree H v u : ℝ) * ε₂ * (∑ u' ∈ S, (codegree H v u' : ℝ))
            = ε₂ * A ^ 2 := by
          rw [hA, sq]
          rw [show ε₂ * ((∑ u ∈ S, (codegree H v u : ℝ)) * (∑ u ∈ S, (codegree H v u : ℝ)))
              = (∑ u ∈ S, (codegree H v u : ℝ)) * (ε₂ * (∑ u ∈ S, (codegree H v u : ℝ))) by ring,
            Finset.sum_mul]
          exact Finset.sum_congr rfl (fun u _ => by ring)
        rw [e1, e2]

end LeanPool.AsymptoticTrianglePacking.Internal
