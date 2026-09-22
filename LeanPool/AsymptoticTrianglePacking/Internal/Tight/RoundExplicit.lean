/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.ResidualBandCheb
import LeanPool.AsymptoticTrianglePacking.Internal.BernoulliSpace
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

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
