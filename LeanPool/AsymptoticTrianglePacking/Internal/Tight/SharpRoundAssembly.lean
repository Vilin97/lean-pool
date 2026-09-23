/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRoundProof
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — assembling the sharp round

`LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundFor`
(`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound`) is proved here in the regime `2γ ≤
ε`, from

* `LeanPool.AsymptoticTrianglePacking.Internal.exists_sharp_round_band` — the probabilistic content
  (sharp Efron–Stein variance +
  Chebyshev on the safe degree, cover variance on the active set), and
* `LeanPool.AsymptoticTrianglePacking.Internal.Exp_safeDegCube_ge` /
  `LeanPool.AsymptoticTrianglePacking.Internal.Exp_safeDegCube_le` — the two deterministic estimates
  of the
  MEAN safe degree (union bound and second Bonferroni inequality).

The retention is `p = γ/(r⌊Δ⌋₊)`, the tolerance `t = εγ⌊Δ⌋₊/16`, the exceptional budget `a = θ|V|`,
the degree threshold `D₀ = 256r/(α²γ) + 96/ε + 4` and the codegree factor `c₀ = θε²γα²/(16384r)`.

The hypothesis `2γ ≤ ε` is what pays for the SECOND-ORDER error of the mean safe degree: the
Bonferroni residue is `Θ(γ²Δ)` per vertex, while `SharpRoundFor` allows only `εγΔ`, so a hypothesis
of the shape `γ = O(ε)` is unavoidable for a round built from the uniform retention `p = γ/(rΔ)`.
The CONSTANT, however, is not: the exact requirement is that the residue

  `Δ⌊·⌋(r−1)(r−2)(Δ²p² + κp) ≤ γ²Δ`  (mean ceiling, Bonferroni)

together with the Chebyshev tolerance `t`, the codegree term `rκγ`, and the rounding/`(1−p)^{rΔ}`
discrepancy `γ³Δ + O(1)` fit inside `εγΔ`.  Charging `γ²Δ ≤ εγΔ/2`, `γ³Δ ≤ εγΔ/4`,
`t ≤ εγΔ/16` and the two `O(1)`-terms `εγΔ/32` each leaves `28/32` of the budget used, so `2γ ≤ ε`
suffices. This is exactly the regime the tight-band schedule uses:
`LeanPool.AsymptoticTrianglePacking.Internal.exists_tightParams`
sets `ε = 4aγ` with `a = (r−1)/r ≥ 1/2`, hence `ε ≥ 2γ`.

The discrepancy `γ³Δ + O(1)` (rather than the `γ²Δ + O(1)` of the earlier bookkeeping) comes from
the sharp upper bound `(1−p)^{rΔ} ≤ 1 − γ + γ²/2`
(`LeanPool.AsymptoticTrianglePacking.Internal.one_sub_pow_le_quadratic`), which cancels
the `(1−γ)` factor carried by the ceiling drop that `SharpRoundFor` requests.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem lostDegree_le_degree (K : Finset (Finset V)) (B : Finset V) (v : V) :
    lostDegree K B v ≤ degree K v := by
  classical
  refine Finset.card_le_card ?_
  intro e he
  rw [Finset.mem_filter] at he ⊢
  exact ⟨he.1, he.2.1⟩

/-- **Second-order upper bound for `(1 − p)^m`.**  For `0 ≤ p ≤ 1`,
`(1 − p)^m ≤ 1 − mp + (mp)²/2`; at `mp = γ` this is `1 − γ + γ²/2`, the bound that cancels the
`(1 − γ)` factor of the requested ceiling drop. -/
theorem one_sub_pow_le_quadratic {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    (1 - p) ^ m ≤ 1 - (m : ℝ) * p + ((m : ℝ) * p) ^ 2 / 2 := by
  induction m with
  | zero => simp
  | succ n ih =>
      have hmul : (1 - p) ^ (n + 1) ≤ (1 - (n : ℝ) * p + ((n : ℝ) * p) ^ 2 / 2) * (1 - p) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right ih (by linarith)
      have hstep : (1 - (n : ℝ) * p + ((n : ℝ) * p) ^ 2 / 2) * (1 - p)
          ≤ 1 - ((n : ℝ) + 1) * p + (((n : ℝ) + 1) * p) ^ 2 / 2 := by
        linarith only [sq_nonneg p, mul_nonneg (sq_nonneg ((n : ℝ) * p)) hp0]
      push_cast
      linarith only [hmul, hstep]

/-- **The rounding/`(1−p)^{rΔ}` discrepancy of the ceiling drop.**  With `dn = ⌈δ⌉₊`, `Dn = ⌊Δ⌋₊`
and `L = (1−p)^{rDn} ≤ 1 − γ + γ²/2`, the achieved relative drop `dn·L/Dn` exceeds the requested one
`δ(1−γ)/Δ` by at most `γ²  + 3/Δ` in relative terms — i.e. `Δ·(dn L/Dn) ≤ δ(1−γ) + γ²Δ + 3`. -/
theorem sharp_drop_ratio_le (γ δ Δ Dn dn L : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hδ2 : 2 ≤ δ) (hδΔ : δ ≤ Δ)
    (hDn3 : 3 ≤ Dn) (hΔDn : Δ < Dn + 1)
    (hδdn : δ ≤ dn) (hdnδ : dn < δ + 1) (hL0 : 0 < L) (hLu : L ≤ 1 - γ + γ ^ 2 / 2) :
    Δ * (dn * L / Dn) ≤ δ * (1 - γ) + γ ^ 2 * Δ + 3 := by
  have hDn0 : (0 : ℝ) < Dn := by linarith only [hDn3]
  have hΔ0 : (0 : ℝ) < Δ := by linarith only [hδ2, hδΔ]
  have hquad : (0 : ℝ) ≤ 1 - γ + γ ^ 2 / 2 := by linarith only [hγ1, sq_nonneg γ]
  have hs1 : dn * L ≤ (δ + 1) * (1 - γ + γ ^ 2 / 2) :=
    mul_le_mul (by linarith) hLu hL0.le (by linarith)
  have hs2 : Δ * (dn * L) ≤ (Dn + 1) * ((δ + 1) * (1 - γ + γ ^ 2 / 2)) :=
    mul_le_mul (by linarith) hs1 (mul_nonneg (by linarith) hL0.le) (by linarith)
  have hb1 : Dn * ((δ + 1) * γ ^ 2 / 2) ≤ Dn * (γ ^ 2 * Δ) := by
    linarith only [mul_nonneg (mul_nonneg hDn0.le (sq_nonneg γ))
      (show (0 : ℝ) ≤ Δ - (δ + 1) / 2 by linarith only [hδΔ, hδ2])]
  have hb3 : (δ + 1) * (1 - γ + γ ^ 2 / 2) ≤ 2 * Dn := by
    linarith only [hδΔ, hΔDn, hDn3,
      mul_nonneg (show (0 : ℝ) ≤ δ + 1 by linarith only [hδ2])
        (show (0 : ℝ) ≤ γ - γ ^ 2 / 2 by
          linarith only [hγ0.le,
            mul_nonneg hγ0.le (show (0 : ℝ) ≤ 1 / 2 - γ by linarith only [hγ1])])]
  have hs3 : (Dn + 1) * ((δ + 1) * (1 - γ + γ ^ 2 / 2))
      ≤ (δ * (1 - γ) + γ ^ 2 * Δ + 3) * Dn := by
    linarith only [hb1, hb3, mul_nonneg hDn0.le hγ0.le]
  rw [show Δ * (dn * L / Dn) = Δ * (dn * L) / Dn by ring, div_le_iff₀ hDn0]
  linarith only [hs2, hs3]

/-- **The survival factor of one round.**  For `m·p = γ` with `0 ≤ p ≤ 1`, Bernoulli and
`LeanPool.AsymptoticTrianglePacking.Internal.one_sub_pow_le_quadratic` pin `(1 − p)^m` between `1 −
γ` and `1 − γ + γ²/2`. -/
theorem sharp_survival_bounds {p γ : ℝ} {m : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hpγ : (m : ℝ) * p = γ) :
    1 - γ ≤ (1 - p) ^ m ∧ (1 - p) ^ m ≤ 1 - γ + γ ^ 2 / 2 := by
  refine ⟨?_, ?_⟩
  · have h := one_add_mul_le_pow (a := -p) (by linarith) m
    have h2 : (1 : ℝ) + (m : ℝ) * (-p) = 1 - γ := by rw [← hpγ]; ring
    have h3 : (1 : ℝ) + -p = 1 - p := by ring
    rw [h2, h3] at h
    exact h
  · have h := one_sub_pow_le_quadratic hp0 hp1 m
    rw [hpγ] at h
    exact h

/-- **The mean ceiling is monotone in the degree.**  Replacing the degree `D` of a vertex by the
global ceiling `Dn` and its floor by `dn` can only increase the mean safe degree estimate. -/
theorem sharp_mean_ceiling_arith {D Dn dn l W C X : ℝ} (hW : 0 ≤ W) (hC : 0 ≤ C) (hX : 0 ≤ X)
    (h1 : D ≤ Dn) (h2 : dn ≤ D) :
    D - (D - l) * W + D * C * X ≤ Dn - (dn - l) * W + Dn * C * X := by
  have e1 : (dn - l) * W ≤ (D - l) * W := mul_le_mul_of_nonneg_right (by linarith) hW
  have e2 : D * C * X ≤ Dn * C * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hC) hX
  linarith

/-- **The cover rate of one round.**  With `p = γ/(rD)`, a floor `dn ≥ D/2` and a survival factor
`L ≥ 1/2`, each active vertex is matched with probability at least `γ/(8r)`. -/
theorem sharp_cover_rate_le {rr γ Dn dn p L : ℝ} (hR0 : 0 < rr) (hDn0 : 0 < Dn)
    (hdnhalf : Dn / 2 ≤ dn) (hLhalf : 1 / 2 ≤ L) (hp0 : 0 < p) (hpγ : rr * Dn * p = γ) :
    γ / (8 * rr) ≤ dn * (p * L) / 2 := by
  have hLpos : (0 : ℝ) < L := by linarith only [hLhalf]
  have hdnL : Dn / 4 ≤ dn * L := by
    linarith only [mul_le_mul_of_nonneg_right hdnhalf hLpos.le,
      mul_le_mul_of_nonneg_left hLhalf (show (0 : ℝ) ≤ Dn / 2 by linarith only [hDn0])]
  rw [div_le_iff₀ (by positivity)]
  linarith only [mul_le_mul_of_nonneg_left hdnL
    (show (0 : ℝ) ≤ 4 * rr * p by positivity), hpγ]

/-- **The second-order (Bonferroni) error of the mean safe degree.**  With `p = γ/(rD)` the residue
`D(r−1)(r−2)(D²p² + κp)` is at most `Δγ² + rκγ`. -/
theorem sharp_bonferroni_error_le {rr γ Δ Dn kn p Err : ℝ} (hR2 : 2 ≤ rr) (hDn0 : 0 ≤ Dn)
    (hkn0 : 0 ≤ kn) (hp0 : 0 < p) (hpγ : rr * Dn * p = γ) (hDn_le : Dn ≤ Δ)
    (hErrdef : Err = Dn * ((rr - 1) * (rr - 2)) * (Dn ^ 2 * p ^ 2 + kn * p)) :
    Err ≤ Δ * γ ^ 2 + rr * kn * γ := by
  have hXnn : (0 : ℝ) ≤ Dn ^ 2 * p ^ 2 + kn * p :=
    add_nonneg (by positivity) (mul_nonneg hkn0 hp0.le)
  have hC : (rr - 1) * (rr - 2) ≤ rr ^ 2 := by linarith only [hR2]
  have h1 : Err ≤ Dn * rr ^ 2 * (Dn ^ 2 * p ^ 2 + kn * p) := by
    rw [hErrdef]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hDn0) hXnn
  have h2 : Dn * rr ^ 2 * (Dn ^ 2 * p ^ 2 + kn * p)
      = Dn * (rr * Dn * p) ^ 2 + rr * kn * (rr * Dn * p) := by ring
  rw [h2, hpγ] at h1
  linarith only [h1, mul_le_mul_of_nonneg_right hDn_le (sq_nonneg γ)]

/-- **The codegree share of the tolerance budget.**  At `κ ≤ θε²γα²D/(8192r)` the codegree term
`rκγ` of the ceiling drop uses at most a `1/32` of the budget `εγΔ`. -/
theorem sharp_codegree_tolerance_le {rr γ ε θ α Δ Dn kn : ℝ} (hR0 : 0 < rr) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hDn0 : 0 ≤ Dn) (hDn_le : Dn ≤ Δ)
    (hkn3 : kn ≤ θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * rr)) :
    rr * kn * γ ≤ ε * γ * Δ / 32 := by
  have s1 : rr * kn * γ ≤ rr * (θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * rr)) * γ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkn3 hR0.le) hγ0.le
  have s2 : rr * (θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * rr)) * γ
      = θ * ε ^ 2 * γ ^ 2 * α ^ 2 * Dn / 8192 := by field_simp
  rw [s2] at s1
  have hεγΔ : (0 : ℝ) ≤ ε * γ * Δ :=
    mul_nonneg (mul_nonneg hε0.le hγ0.le) (le_trans hDn0 hDn_le)
  have c0 : θ * α ^ 2 ≤ 1 := by nlinarith only [hθ0.le, hθ1, hα0.le, hα1]
  have c2 : (ε * γ) ^ 2 ≤ ε * γ := by
    nlinarith only [mul_nonneg hε0.le hγ0.le,
      mul_le_mul hε1 hγ1 hγ0.le (by norm_num : (0:ℝ) ≤ 1)]
  have c1 : θ * ε ^ 2 * γ ^ 2 * α ^ 2 ≤ ε * γ := by
    linarith only [mul_le_mul_of_nonneg_right c0 (show (0 : ℝ) ≤ (ε * γ) ^ 2 by positivity), c2]
  have b1 : θ * ε ^ 2 * γ ^ 2 * α ^ 2 * Dn ≤ ε * γ * Δ :=
    mul_le_mul c1 hDn_le hDn0 (by positivity)
  linarith only [s1, b1, hεγΔ]

/-- **The ceiling clause of the round, in arithmetic form.** The mean ceiling `Dn − Sγ(dn−l)d + Err`
produced by the Chebyshev band, plus the tolerance `t`, still fits below the requested ceiling
`Δ − Sγ(δ−l)c + εγΔ`, where `c = δ(1−γ)/Δ` is the requested relative drop and `d = dn·L/Dn` the
achieved one: the five error terms use `1/2 + 1/4 + 1/16 + 1/32 + 1/32 < 1` of the budget. -/
theorem sharp_ceiling_clause_arith {S γ ε δ dn Δ Dn l c d Err t x e : ℝ}
    (hSnn : 0 ≤ S) (hS1 : S ≤ 1) (hγ0 : 0 < γ) (hΔ0 : 0 < Δ) (hδ2 : 2 ≤ δ) (hδdn : δ ≤ dn)
    (hlΔ : l ≤ Δ) (hcd : c ≤ d) (hd0 : 0 ≤ d) (hΔc : Δ * c = δ * (1 - γ))
    (hΔd : Δ * d ≤ δ * (1 - γ) + γ ^ 2 * Δ + 3) (hDn_le : Dn ≤ Δ)
    (hb2 : x ≤ Dn - S * γ * ((dn - l) * d) + Err + t)
    (hErrle : Err ≤ Δ * γ ^ 2 + e) (ht2 : t ≤ ε * γ * Δ / 16) (hg2 : Δ * γ ^ 2 ≤ ε * γ * Δ / 2)
    (hg3 : γ * (γ ^ 2 * Δ) ≤ ε * γ * Δ / 4) (hg4 : 3 * γ ≤ ε * γ * Δ / 32)
    (he : e ≤ ε * γ * Δ / 32) (hεγΔ : 0 ≤ ε * γ * Δ) :
    x ≤ Δ - S * γ * ((δ - l) * c) + ε * γ * Δ := by
  have hΔdc : Δ * (d - c) ≤ γ ^ 2 * Δ + 3 := by linarith only [hΔd, hΔc]
  have hbr : (δ - l) * c - (dn - l) * d ≤ Δ * (d - c) := by
    have hid : Δ * (d - c) - ((δ - l) * c - (dn - l) * d)
        = (d - c) * (Δ + δ - l) + (dn - δ) * d := by ring
    have q1 : (0 : ℝ) ≤ (d - c) * (Δ + δ - l) :=
      mul_nonneg (by linarith only [hcd]) (by linarith only [hlΔ, hδ2])
    have q2 : (0 : ℝ) ≤ (dn - δ) * d := mul_nonneg (by linarith only [hδdn]) hd0
    linarith only [hid, q1, q2]
  have hγΔ3 : (0 : ℝ) ≤ γ ^ 2 * Δ + 3 := by
    linarith only [mul_nonneg (sq_nonneg γ) hΔ0.le]
  have hSbr : S * γ * ((δ - l) * c) - S * γ * ((dn - l) * d) ≤ γ * (γ ^ 2 * Δ) + 3 * γ := by
    have hbr2 : (δ - l) * c - (dn - l) * d ≤ γ ^ 2 * Δ + 3 := le_trans hbr hΔdc
    rcases le_or_gt 0 ((δ - l) * c - (dn - l) * d) with h | h
    · linarith only [mul_nonneg hγ0.le (sub_nonneg.mpr hbr2),
        mul_nonneg (mul_nonneg hγ0.le h) (sub_nonneg.mpr hS1)]
    · linarith only [mul_nonneg (mul_nonneg hSnn hγ0.le)
        (show (0 : ℝ) ≤ -((δ - l) * c - (dn - l) * d) by linarith only [h]),
        mul_nonneg hγ0.le hγΔ3]
  linarith only [hb2, hSbr, hErrle, ht2, hg2, hg3, hg4, he, hDn_le, hεγΔ]

/-- The numeric smallness condition consumed by
`LeanPool.AsymptoticTrianglePacking.Internal.exists_sharp_round_band`, at the
parameters of `LeanPool.AsymptoticTrianglePacking.Internal.sharpRoundFor_of_two_gamma_le_eps`
(tolerance `t = εγDn/16`, codegree
`kn ≤ θε²γα²Dn/(8192r)`). -/
theorem sharp_smallness_numeric (r : ℕ) (hr2 : 2 ≤ r) (γ ε θ α N Dn dn kn Ac p L t : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hN256' : 256 * (r : ℝ) ≤ N * (α ^ 2 * γ)) (hN4 : 4 ≤ N)
    (hDn3 : 3 ≤ Dn) (hdnhalf : Dn / 2 ≤ dn) (hkn0 : 0 ≤ kn)
    (hkn3 : kn ≤ θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * (r : ℝ)))
    (hp0 : 0 < p) (hpγ : (r : ℝ) * Dn * p = γ) (hLhalf : 1 / 2 ≤ L)
    (htdef : t = ε * γ * Dn / 16) (hAN : α * N ≤ Ac) :
    (N * ((2 * p * ((r : ℝ) ^ 2 * kn * Dn ^ 2)
          * (1 + p * (r : ℝ) * Dn + (p * (r : ℝ) * Dn) ^ 2)) / t ^ 2)) / (θ * N)
      + (N * (Dn * p) + N ^ 2 * (kn * p + 4 * (r : ℝ) ^ 2 * kn * Dn ^ 2 * p ^ 3))
        / (Ac * (dn * (p * L)) / 2) ^ 2 < 1 := by
  have hR2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hR0 : (0 : ℝ) < (r : ℝ) := by linarith only [hR2]
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hR0
  have hDnpos : (0 : ℝ) < Dn := by linarith only [hDn3]
  have hNpos : (0 : ℝ) < N := by linarith only [hN4]
  have hAcpos : (0 : ℝ) < Ac := lt_of_lt_of_le (mul_pos hα0 hNpos) hAN
  have hLpos : (0 : ℝ) < L := by linarith only [hLhalf]
  have ht0 : 0 < t := by rw [htdef]; positivity
  have hprd : p * (r : ℝ) * Dn = γ := by rw [← hpγ]; ring
  have e1 : Dn * p = γ / (r : ℝ) := by
    rw [eq_div_iff hrne, ← hpγ]; ring
  -- the cover rate
  have hkey : γ / (8 * (r : ℝ)) ≤ dn * (p * L) / 2 :=
    sharp_cover_rate_le hR0 hDnpos hdnhalf hLhalf hp0 hpγ
  have hQ2ge : α * N * γ / (8 * (r : ℝ)) ≤ Ac * (dn * (p * L)) / 2 := by
    have s1 : Ac * (γ / (8 * (r : ℝ))) ≤ Ac * (dn * (p * L) / 2) :=
      mul_le_mul_of_nonneg_left hkey hAcpos.le
    have s2 : α * N * (γ / (8 * (r : ℝ))) ≤ Ac * (γ / (8 * (r : ℝ))) :=
      mul_le_mul_of_nonneg_right hAN (by positivity)
    have q1 : α * N * γ / (8 * (r : ℝ)) = α * N * (γ / (8 * (r : ℝ))) := by ring
    have q2 : Ac * (dn * (p * L) / 2) = Ac * (dn * (p * L)) / 2 := by ring
    rw [q1, ← q2]; linarith only [s1, s2]
  -- Chebyshev term
  have hVs_le : 2 * p * ((r : ℝ) ^ 2 * kn * Dn ^ 2)
        * (1 + p * (r : ℝ) * Dn + (p * (r : ℝ) * Dn) ^ 2)
      ≤ 4 * γ * (r : ℝ) * kn * Dn := by
    rw [hprd, show 2 * p * ((r : ℝ) ^ 2 * kn * Dn ^ 2)
        = 2 * kn * Dn * (r : ℝ) * ((r : ℝ) * Dn * p) by ring, hpγ]
    linarith only [mul_le_mul_of_nonneg_left
      (show 1 + γ + γ ^ 2 ≤ 2 by
        linarith only [hγ1, mul_nonneg hγ0.le (show (0 : ℝ) ≤ 1 / 2 - γ by linarith only [hγ1])])
      (show (0 : ℝ) ≤ 2 * kn * Dn * (r : ℝ) * γ by positivity)]
  have hVt : (2 * p * ((r : ℝ) ^ 2 * kn * Dn ^ 2)
        * (1 + p * (r : ℝ) * Dn + (p * (r : ℝ) * Dn) ^ 2)) / t ^ 2 ≤ θ / 4 := by
    rw [div_le_iff₀ (by positivity), htdef,
      show (ε * γ * Dn / 16) ^ 2 = ε ^ 2 * γ ^ 2 * Dn ^ 2 / 256 by ring]
    refine le_trans hVs_le ?_
    have hstep : 4 * γ * (r : ℝ) * kn * Dn
        ≤ 4 * γ * (r : ℝ) * (θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * (r : ℝ))) * Dn :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkn3 (by positivity)) hDnpos.le
    refine le_trans hstep ?_
    rw [show 4 * γ * (r : ℝ) * (θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * (r : ℝ))) * Dn
        = θ * ε ^ 2 * γ ^ 2 * α ^ 2 * Dn ^ 2 / 2048 by field_simp; ring]
    linarith only [mul_le_mul_of_nonneg_left
        (show α ^ 2 ≤ 1 by nlinarith only [hα0.le, hα1])
        (show (0 : ℝ) ≤ θ * ε ^ 2 * γ ^ 2 * Dn ^ 2 by positivity),
      show (0 : ℝ) ≤ θ * ε ^ 2 * γ ^ 2 * Dn ^ 2 by positivity]
  have hT1 : (N * ((2 * p * ((r : ℝ) ^ 2 * kn * Dn ^ 2)
          * (1 + p * (r : ℝ) * Dn + (p * (r : ℝ) * Dn) ^ 2)) / t ^ 2)) / (θ * N) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [mul_le_mul_of_nonneg_left hVt hNpos.le]
  -- cover-variance term
  have e3 : 4 * (r : ℝ) ^ 2 * kn * Dn ^ 2 * p ^ 3 = 4 * γ ^ 2 * (kn * p) := by
    rw [← hpγ]; ring
  have hknp : kn * p ≤ θ * ε ^ 2 * γ ^ 2 * α ^ 2 / (8192 * (r : ℝ) ^ 2) := by
    calc kn * p ≤ (θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * (r : ℝ))) * p :=
          mul_le_mul_of_nonneg_right hkn3 hp0.le
      _ = θ * ε ^ 2 * γ * α ^ 2 * (Dn * p) / (8192 * (r : ℝ)) := by ring
      _ = θ * ε ^ 2 * γ ^ 2 * α ^ 2 / (8192 * (r : ℝ) ^ 2) := by rw [e1]; field_simp
  rw [le_div_iff₀ (by positivity)] at hknp
  have hknp0 : (0 : ℝ) ≤ kn * p := mul_nonneg hkn0 hp0.le
  have hA1 : N * (Dn * p) ≤ α ^ 2 * N ^ 2 * γ ^ 2 / (256 * (r : ℝ) ^ 2) := by
    rw [e1, le_div_iff₀ (by positivity),
      show N * (γ / (r : ℝ)) * (256 * (r : ℝ) ^ 2) = 256 * (r : ℝ) * (N * γ) by
        field_simp]
    linarith only [mul_le_mul_of_nonneg_right hN256' (show (0 : ℝ) ≤ N * γ by positivity)]
  have hA2 : 2 * N ^ 2 * (kn * p) ≤ α ^ 2 * N ^ 2 * γ ^ 2 / (256 * (r : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [mul_le_mul_of_nonneg_left hknp (show (0 : ℝ) ≤ N ^ 2 by positivity),
      mul_le_mul_of_nonneg_left
        (show θ * ε ^ 2 ≤ 1 by nlinarith only [hθ0.le, hθ1, hε0.le, hε1])
        (show (0 : ℝ) ≤ N ^ 2 * γ ^ 2 * α ^ 2 by positivity),
      show (0 : ℝ) ≤ α ^ 2 * N ^ 2 * γ ^ 2 by positivity]
  have hnum : N * (Dn * p) + N ^ 2 * (kn * p + 4 * (r : ℝ) ^ 2 * kn * Dn ^ 2 * p ^ 3)
      ≤ α ^ 2 * N ^ 2 * γ ^ 2 / (128 * (r : ℝ) ^ 2) := by
    rw [e3]
    have hmid : N ^ 2 * (kn * p + 4 * γ ^ 2 * (kn * p)) ≤ 2 * N ^ 2 * (kn * p) := by
      linarith only [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ N ^ 2 by positivity) hknp0)
        (show (0 : ℝ) ≤ 1 - 4 * γ ^ 2 by nlinarith only [hγ0.le, hγ1])]
    have hsplit : α ^ 2 * N ^ 2 * γ ^ 2 / (256 * (r : ℝ) ^ 2)
        + α ^ 2 * N ^ 2 * γ ^ 2 / (256 * (r : ℝ) ^ 2)
        = α ^ 2 * N ^ 2 * γ ^ 2 / (128 * (r : ℝ) ^ 2) := by ring
    linarith only [hA1, hA2, hmid, hsplit]
  have hQ2pos : (0 : ℝ) < Ac * (dn * (p * L)) / 2 :=
    lt_of_lt_of_le (by positivity) hQ2ge
  have hQ2sq : α ^ 2 * N ^ 2 * γ ^ 2 / (64 * (r : ℝ) ^ 2) ≤ (Ac * (dn * (p * L)) / 2) ^ 2 := by
    have hsq := mul_self_le_mul_self
      (show (0 : ℝ) ≤ α * N * γ / (8 * (r : ℝ)) by positivity) hQ2ge
    calc α ^ 2 * N ^ 2 * γ ^ 2 / (64 * (r : ℝ) ^ 2)
        = (α * N * γ / (8 * (r : ℝ))) * (α * N * γ / (8 * (r : ℝ))) := by field_simp; ring
      _ ≤ (Ac * (dn * (p * L)) / 2) * (Ac * (dn * (p * L)) / 2) := hsq
      _ = (Ac * (dn * (p * L)) / 2) ^ 2 := (pow_two _).symm
  have hT2 : (N * (Dn * p) + N ^ 2 * (kn * p + 4 * (r : ℝ) ^ 2 * kn * Dn ^ 2 * p ^ 3))
        / (Ac * (dn * (p * L)) / 2) ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hd : α ^ 2 * N ^ 2 * γ ^ 2 / (128 * (r : ℝ) ^ 2)
        = (1 / 2) * (α ^ 2 * N ^ 2 * γ ^ 2 / (64 * (r : ℝ) ^ 2)) := by ring
    linarith only [hnum, hQ2sq, hd]
  linarith only [hT1, hT2]

/-- **The sharp LeanPool.AsymptoticTrianglePacking.Internal round, assembled**, in the regime `2γ ≤
ε` — the regime the tight-band
schedule `LeanPool.AsymptoticTrianglePacking.Internal.exists_tightParams` actually uses (`ε =
4((r−1)/r)γ ≥ 2γ`). -/
theorem sharpRoundFor_of_two_gamma_le_eps (r : ℕ) (hr2 : 2 ≤ r) (γ ε θ α : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hε1 : ε ≤ 1) (hγε : 2 * γ ≤ ε)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    SharpRoundFor r γ ε θ α (256 * r / (α ^ 2 * γ) + 96 / ε + 4)
      (θ * ε ^ 2 * γ * α ^ 2 / (16384 * r)) := by
  classical
  have hε0 : 0 < ε := by linarith only [hγ0, hγε]
  have hR2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hR0 : (0 : ℝ) < (r : ℝ) := by linarith only [hR2]
  set c₀ : ℝ := θ * ε ^ 2 * γ * α ^ 2 / (16384 * r) with hc₀def
  have hc₀0 : 0 < c₀ := by rw [hc₀def]; positivity
  intro V _ _ K A δ Δ κ hr hΔle hδA hκle hκ0 hκc hDΔ hΔδ hDN hAN
  set N : ℝ := (Fintype.card V : ℝ) with hNdef
  -- threshold consequences
  have hpos1 : (0 : ℝ) < 256 * (r : ℝ) / (α ^ 2 * γ) := by positivity
  have hpos2 : (0 : ℝ) < 96 / ε := by positivity
  have hΔ4 : (4 : ℝ) ≤ Δ := by linarith only [hDΔ, hpos1, hpos2]
  have hN4 : (4 : ℝ) ≤ N := by linarith only [hDN, hpos1, hpos2]
  have hΔ96 : 96 / ε ≤ Δ := by linarith only [hDΔ, hpos1]
  have hN256 : 256 * (r : ℝ) / (α ^ 2 * γ) ≤ N := by linarith only [hDN, hpos2]
  have hN256' : 256 * (r : ℝ) ≤ N * (α ^ 2 * γ) := by
    rw [div_le_iff₀ (by positivity)] at hN256; linarith only [hN256]
  -- integer versions of the parameters
  set Δn : ℕ := ⌊Δ⌋₊ with hΔndef
  set δn : ℕ := ⌈δ⌉₊ with hδndef
  set κn : ℕ := ⌊κ⌋₊ with hκndef
  have hDn_le : (Δn : ℝ) ≤ Δ := Nat.floor_le (by linarith)
  have hDn_gt : Δ < (Δn : ℝ) + 1 := Nat.lt_floor_add_one Δ
  have hδ_le_dn : δ ≤ (δn : ℝ) := Nat.le_ceil δ
  have hδ2 : (2 : ℝ) ≤ δ := by linarith only [hΔδ, hΔ4]
  have hdn_lt : (δn : ℝ) < δ + 1 := Nat.ceil_lt_add_one (by linarith)
  have hkn_le : (κn : ℝ) ≤ κ := Nat.floor_le hκ0
  have hkn0 : (0 : ℝ) ≤ (κn : ℝ) := Nat.cast_nonneg _
  have hΔnat : ∀ v : V, degree K v ≤ Δn := fun v => Nat.le_floor (hΔle v)
  have hδnat : ∀ v ∈ A, δn ≤ degree K v := fun v hv => Nat.ceil_le.mpr (hδA v hv)
  have hκnat : ∀ x y : V, x ≠ y → codegree K x y ≤ κn := fun x y h => Nat.le_floor (hκle x y h)
  have hΔn3 : 3 ≤ Δn := Nat.le_floor (by push_cast; linarith)
  have hDn3 : (3 : ℝ) ≤ (Δn : ℝ) := by exact_mod_cast hΔn3
  have hDnpos : (0 : ℝ) < (Δn : ℝ) := by linarith only [hDn3]
  -- the active set is nonempty
  have hAc0 : (0 : ℝ) < (A.card : ℝ) :=
    lt_of_lt_of_le (mul_pos hα0 (by linarith : (0 : ℝ) < N)) hAN
  have hAcardN : 0 < A.card := by exact_mod_cast hAc0
  obtain ⟨v0, hv0⟩ := Finset.card_pos.mp hAcardN
  have hdn_le_Dn : δn ≤ Δn := le_trans (hδnat v0 hv0) (hΔnat v0)
  have hdnDn : (δn : ℝ) ≤ (Δn : ℝ) := by exact_mod_cast hdn_le_Dn
  have hdnΔ : (δn : ℝ) ≤ Δ := le_trans hdnDn hDn_le
  have hδ_le_Δ : δ ≤ Δ := le_trans hδ_le_dn hdnΔ
  have hdn1 : 0 < δn := by
    have : (0 : ℝ) < (δn : ℝ) := by linarith only [hδ_le_dn, hδ2]
    exact_mod_cast this
  -- the retention
  set p : ℝ := γ / ((r : ℝ) * (Δn : ℝ)) with hpdef
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hpγ : (r : ℝ) * (Δn : ℝ) * p = γ := by rw [hpdef]; field_simp
  have hp1 : p < 1 := by
    rw [hpdef, div_lt_one (by positivity)]
    nlinarith only [hγ1, hγ0.le, hR2, hDn3]
  set L : ℝ := (1 - p) ^ (r * Δn) with hLdef
  have hLbounds := sharp_survival_bounds (m := r * Δn) (γ := γ) hp0.le hp1.le
    (by push_cast; exact hpγ)
  have hLge : 1 - γ ≤ L := by rw [hLdef]; exact hLbounds.1
  have hLu : L ≤ 1 - γ + γ ^ 2 / 2 := by rw [hLdef]; exact hLbounds.2
  have hLle : L ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hLpos : (0 : ℝ) < L := pow_pos (by linarith) _
  -- the band parameters
  set t : ℝ := ε * γ * (Δn : ℝ) / 16 with htdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  set S : ℝ := ((r : ℝ) - 1) / (r : ℝ) with hSdef
  have hSnn : (0 : ℝ) ≤ S := by rw [hSdef]; apply div_nonneg <;> linarith
  have hS1 : S ≤ 1 := by rw [hSdef, div_le_one hR0]; linarith
  set mlo : ℝ := (δn : ℝ) * (1 - ((r : ℝ) - 1) * ((Δn : ℝ) * p)) with hmlodef
  set Err : ℝ :=
    (Δn : ℝ) * (((r : ℝ) - 1) * ((r : ℝ) - 2)) * ((Δn : ℝ) ^ 2 * p ^ 2 + (κn : ℝ) * p) with hErrdef
  set mhi : V → ℝ := fun v =>
    (Δn : ℝ) - ((δn : ℝ) - (lostDegree K Aᶜ v : ℝ)) * (((r : ℝ) - 1) * (δn : ℝ) * (p * L))
      + Err with hmhidef
  clear_value mhi Err mlo S t L p κn δn Δn c₀
  -- the mean estimates
  have hlo : ∀ v ∈ A, mlo ≤ Cube.Exp p (safeDegCube K v) := by
    intro v hv
    refine le_trans ?_ (Exp_safeDegCube_ge hp0.le hp1.le (by omega) hr hΔnat v)
    have hd : (δn : ℝ) ≤ (degree K v : ℝ) := by exact_mod_cast hδnat v hv
    have hfac : (0 : ℝ) ≤ 1 - ((r : ℝ) - 1) * ((Δn : ℝ) * p) := by
      have : (Δn : ℝ) * p = γ / (r : ℝ) := by rw [hpdef]; field_simp
      rw [this, show ((r : ℝ) - 1) * (γ / (r : ℝ)) = ((r : ℝ) - 1) * γ / (r : ℝ) by ring,
        sub_nonneg, div_le_one hR0]
      linarith only [hR0,
        mul_le_mul_of_nonneg_left hγ1 (show (0:ℝ) ≤ (r:ℝ) - 1 by linarith only [hR2])]
    rw [hmlodef]
    exact mul_le_mul_of_nonneg_right hd hfac
  have hhi : ∀ v ∈ A, Cube.Exp p (safeDegCube K v) ≤ mhi v := by
    intro v hv
    refine le_trans (Exp_safeDegCube_le A hp0.le hp1.le hr2 hr hΔnat hδnat hκnat v) ?_
    rw [← hLdef, hmhidef, hErrdef]
    simp only
    exact sharp_mean_ceiling_arith
      (mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (mul_nonneg hp0.le hLpos.le))
      (by nlinarith only [hR2])
      (add_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) hp0.le))
      (by exact_mod_cast hΔnat v) (by exact_mod_cast hδnat v hv)
  -- codegree bound in integer form
  have hkn3 : (κn : ℝ) ≤ θ * ε ^ 2 * γ * α ^ 2 * (Δn : ℝ) / (8192 * (r : ℝ)) := by
    have hΔ2Dn : Δ ≤ 2 * (Δn : ℝ) := by linarith
    have : (κn : ℝ) ≤ c₀ * (2 * (Δn : ℝ)) := by
      refine le_trans hkn_le (le_trans hκc ?_)
      exact mul_le_mul_of_nonneg_left hΔ2Dn hc₀0.le
    rw [hc₀def] at this
    calc (κn : ℝ) ≤ θ * ε ^ 2 * γ * α ^ 2 / (16384 * (r : ℝ)) * (2 * (Δn : ℝ)) := this
      _ = θ * ε ^ 2 * γ * α ^ 2 * (Δn : ℝ) / (8192 * (r : ℝ)) := by field_simp; ring
  -- the cover rate on the active set
  have hkey : γ / (8 * (r : ℝ)) ≤ (δn : ℝ) * (p * L) / 2 :=
    sharp_cover_rate_le hR0 hDnpos (by linarith) (by linarith) hp0 hpγ
  -- the smallness condition
  have hsmall :
      (N * ((2 * p * ((r : ℝ) ^ 2 * (κn : ℝ) * (Δn : ℝ) ^ 2)
            * (1 + p * (r : ℝ) * (Δn : ℝ) + (p * (r : ℝ) * (Δn : ℝ)) ^ 2)) / t ^ 2)) / (θ * N)
        + (N * ((Δn : ℝ) * p)
            + N ^ 2 * ((κn : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κn : ℝ) * (Δn : ℝ) ^ 2 * p ^ 3))
          / ((A.card : ℝ) * ((δn : ℝ) * (p * (1 - p) ^ (r * Δn))) / 2) ^ 2 < 1 := by
    rw [← hLdef]
    exact sharp_smallness_numeric r hr2 γ ε θ α N (Δn : ℝ) (δn : ℝ) (κn : ℝ) (A.card : ℝ) p L t
      hγ0 hγ1 hε0 hε1 hθ0 hθ1 hα0 hα1 hN256' hN4 hDn3 (by linarith) hkn0 hkn3 hp0 hpγ
      (by linarith) htdef hAN
  obtain ⟨R', hR'sub, B, hBcard, hband, hcov⟩ :=
    exists_sharp_round_band (K := K) A (r := r) (Δ := Δn) (δ := δn) (κ := κn)
      (p := p) (t := t) (a := θ * N) (mlo := mlo) (mhi := mhi)
      hp0 hp1 (by omega) hr hΔnat hδnat hκnat ht0 (by positivity) hdn1 hAcardN hlo hhi hsmall
  have hΔpos : (0 : ℝ) < Δ := by linarith
  have hεΔ : (96 : ℝ) ≤ ε * Δ := by rw [div_le_iff₀ hε0] at hΔ96; linarith
  have ht2 : t ≤ ε * γ * Δ / 16 := by
    rw [htdef]
    linarith only [mul_le_mul_of_nonneg_left hDn_le (show (0 : ℝ) ≤ ε * γ by positivity)]
  -- the four pieces of the tolerance budget `εγΔ`
  have hg2 : Δ * γ ^ 2 ≤ ε * γ * Δ / 2 := by
    linarith only [mul_le_mul_of_nonneg_right hγε (mul_nonneg hγ0.le hΔpos.le)]
  have hg3 : γ * (γ ^ 2 * Δ) ≤ ε * γ * Δ / 4 := by
    linarith only [mul_le_mul_of_nonneg_left hg2 hγ0.le,
      mul_le_mul_of_nonneg_right hγ1 (show (0 : ℝ) ≤ ε * γ * Δ by positivity)]
  have hg4 : 3 * γ ≤ ε * γ * Δ / 32 := by
    linarith only [mul_le_mul_of_nonneg_left hεΔ hγ0.le]
  have hkn4 : (r : ℝ) * (κn : ℝ) * γ ≤ ε * γ * Δ / 32 :=
    sharp_codegree_tolerance_le hR0 hγ0 hγ1 hε0 hε1 hθ0 hθ1 hα0 hα1 (Nat.cast_nonneg _) hDn_le hkn3
  refine ⟨R', hR'sub, B, hBcard.le, ?_, ?_⟩
  · intro v hvA hvB hvc
    obtain ⟨hb1, hb2⟩ := hband v hvA hvB hvc
    have hDp : (Δn : ℝ) * p = γ / (r : ℝ) := by rw [hpdef]; field_simp
    constructor
    · have hmloeq : mlo = (δn : ℝ) - (δn : ℝ) * S * γ := by
        rw [hmlodef, hSdef, hDp]; field_simp; try ring
      have h1 : (δn : ℝ) * S * γ ≤ S * γ * Δ := by
        have h := mul_le_mul_of_nonneg_left hdnΔ (mul_nonneg hSnn hγ0.le)
        linarith only [h]
      linarith only [hb1, hδ_le_dn, hmloeq, h1, ht2,
        mul_nonneg (mul_nonneg hε0.le hγ0.le) hΔpos.le]
    · simp only [hmhidef] at hb2
      set lo : ℝ := (lostDegree K Aᶜ v : ℝ) with hlodef
      have hlo0 : (0 : ℝ) ≤ lo := Nat.cast_nonneg _
      have hloΔ : lo ≤ Δ := by
        have h' : (lostDegree K Aᶜ v : ℝ) ≤ (degree K v : ℝ) := by
          exact_mod_cast lostDegree_le_degree K Aᶜ v
        have h'' := hΔle v
        rw [hlodef]
        linarith only [h', h'']
      clear_value lo
      set c : ℝ := δ * (1 - γ) / Δ with hcdef
      set d : ℝ := (δn : ℝ) * L / (Δn : ℝ) with hddef
      have hdnLnn : (0 : ℝ) ≤ (δn : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hLpos.le
      have hc0 : (0 : ℝ) ≤ c :=
        div_nonneg (mul_nonneg (by linarith only [hδ2]) (by linarith only [hγ1])) hΔpos.le
      have hcd : c ≤ d := by
        rw [hcdef, hddef, div_le_iff₀ hΔpos, div_mul_eq_mul_div, le_div_iff₀ hDnpos]
        have hnum : δ * (1 - γ) ≤ (δn : ℝ) * L :=
          mul_le_mul hδ_le_dn hLge (by linarith only [hγ1]) (Nat.cast_nonneg _)
        linarith only [mul_le_mul_of_nonneg_right hnum hDnpos.le,
          mul_le_mul_of_nonneg_left hDn_le hdnLnn]
      have hd0 : (0 : ℝ) ≤ d := le_trans hc0 hcd
      have hΔc : Δ * c = δ * (1 - γ) := by rw [hcdef]; field_simp
      have hΔd : Δ * d ≤ δ * (1 - γ) + γ ^ 2 * Δ + 3 := by
        rw [hddef]
        exact sharp_drop_ratio_le γ δ Δ (Δn : ℝ) (δn : ℝ) L hγ0 hγ1 hδ2 hδ_le_Δ hDn3 hDn_gt
          hδ_le_dn hdn_lt hLpos hLu
      clear_value c d
      have hDropT : S * γ * (δ - lo) * δ * (1 - γ) / Δ = S * γ * ((δ - lo) * c) := by
        rw [hcdef]; field_simp; try ring
      have hDropO : ((δn : ℝ) - lo) * (((r : ℝ) - 1) * (δn : ℝ) * (p * L))
          = S * γ * (((δn : ℝ) - lo) * d) := by
        rw [hddef, hSdef, hpdef]; field_simp; try ring
      have hErrle : Err ≤ Δ * γ ^ 2 + (r : ℝ) * (κn : ℝ) * γ :=
        sharp_bonferroni_error_le hR2 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hp0 hpγ hDn_le
          hErrdef
      rw [hDropT]
      rw [hDropO] at hb2
      exact sharp_ceiling_clause_arith hSnn hS1 hγ0 hΔpos hδ2 hδ_le_dn hloΔ hcd hd0 hΔc hΔd
        hDn_le hb2 hErrle ht2 hg2 hg3 hg4 hkn4
        (mul_nonneg (mul_nonneg hε0.le hγ0.le) hΔpos.le)
  · rw [← hLdef] at hcov
    have s1 : (A.card : ℝ) * (γ / (8 * (r : ℝ)))
        ≤ (A.card : ℝ) * ((δn : ℝ) * (p * L) / 2) := mul_le_mul_of_nonneg_left hkey hAc0.le
    have e2 : (A.card : ℝ) * ((δn : ℝ) * (p * L) / 2)
        = (A.card : ℝ) * ((δn : ℝ) * (p * L)) / 2 := by ring
    linarith only [hcov, s1, e2]

/-- **`LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundHyp` in the regime `2γ ≤ ε`.**

This is exactly the body of `LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundHyp` with the
extra hypothesis `2 * γ ≤ ε`; the
witnesses are `D₀ = 256r/(α²γ) + 96/ε + 4` and `c₀ = θε²γα²/(16384r)`.

The restriction is not an artefact of the bookkeeping: the mean safe degree of a vertex genuinely
carries a second-order term of size `Θ(γ²Δ)` (the pairs of neighbours of `v` inside a single edge
that are covered simultaneously), while `SharpRoundFor` allows an absolute error of only `εγΔ`.  So
some hypothesis of the form `γ = O(ε)` is necessary for a round built from the uniform retention
`p = γ/(rΔ)`. The constant `2` is below the schedule's own ratio:
`LeanPool.AsymptoticTrianglePacking.Internal.exists_tightParams`
sets `ε = 4((r−1)/r)γ ≥ 2γ`. -/
theorem sharpRoundHyp_of_two_gamma_le_eps (r : ℕ) (hr2 : 2 ≤ r) (γ ε θ α : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hε1 : ε ≤ 1) (hγε : 2 * γ ≤ ε)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ SharpRoundFor r γ ε θ α D₀ c₀ := by
  have hε0 : 0 < ε := by linarith only [hγ0, hγε]
  have hR0 : (0 : ℝ) < (r : ℝ) := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    linarith only [this]
  exact ⟨256 * r / (α ^ 2 * γ) + 96 / ε + 4, by positivity,
    θ * ε ^ 2 * γ * α ^ 2 / (16384 * r), by positivity,
    sharpRoundFor_of_two_gamma_le_eps r hr2 γ ε θ α hγ0 hγ1 hε1 hγε hθ0 hθ1 hα0 hα1⟩

/-- **`LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundHyp` in the regime `8γ ≤ ε`**, a
special case of
`LeanPool.AsymptoticTrianglePacking.Internal.sharpRoundHyp_of_two_gamma_le_eps`. -/
theorem sharpRoundHyp_of_gamma_le_eps (r : ℕ) (hr2 : 2 ≤ r) (γ ε θ α : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hε1 : ε ≤ 1) (hγε : 8 * γ ≤ ε)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ SharpRoundFor r γ ε θ α D₀ c₀ :=
  sharpRoundHyp_of_two_gamma_le_eps r hr2 γ ε θ α hγ0 hγ1 hε1 (by linarith) hθ0 hθ1 hα0 hα1

end LeanPool.AsymptoticTrianglePacking.Internal
