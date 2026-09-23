/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.TightRoundCheb
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.TightRoundConcrete
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.ResidualBand
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

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

@[expose] public section

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
