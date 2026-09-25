/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.TightAssembly

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — existence of the tight-band schedule

`LeanPool.AsymptoticTrianglePacking.Internal.exists_tightParams`: for every uniformity `r ≥ 2` and
every target `β ∈ (0,1)` there is a
`LeanPool.AsymptoticTrianglePacking.Internal.TightParams r β`, i.e. a complete choice of

* the round rate `γ`, the relative tolerance `ε`, the exceptional fractions `θ` (per round) and `η`
  (initial), the number of rounds `T`,
* the relative degree band `[lo k, hi k]` after `k` rounds and the exceptional budget `sig k`,

satisfying every inequality that `LeanPool.AsymptoticTrianglePacking.Internal.tight_round_step` and
`LeanPool.AsymptoticTrianglePacking.Internal.hasRoundOracle_of_scheduled_invariant` consume.

The schedule is the classical one.  With `a = (r−1)/r ∈ [1/2, 1)`:

* `γ = min (1/8) (exp(−8M−1)/32)` where `M = 16rL + 1` and `L = log(1/β)`, `n₀ = 8γ`, `ε = 4aγ`;
* `q = 1 − aγ`, `n k = n₀(1 + 8aγ)^k`, `lo k = q^k(1 − n k)`, `hi k = q^k(1 + n k)`;
* `T = ⌈M/γ⌉`, so `γT ∈ [M, M + γ]`.  Then `(1 − γ/(16r))^T ≤ exp(−M/(16r)) ≤ exp(−L) = β`, while
  `n T ≤ n₀ exp(8γT) ≤ 8γ·exp(8M+1) ≤ 1/4` — the point being that `γT ≈ M` is INDEPENDENT of `γ`, so
  making `γ` small really does shrink the total band widening.
* `sig k = 2θ(2G)^k` with `G = (2 + r/(εγ))²` the per-round exceptional growth factor and
  `η = θ = β/(8(2G)^T)`, so `sig k ≤ β/4`.

The two per-round band inequalities reduce to the polynomial cores
`LeanPool.AsymptoticTrianglePacking.Internal.tight_band_step_lo_core` and
`LeanPool.AsymptoticTrianglePacking.Internal.tight_band_step_hi_core`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open Finset

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-! ## The two polynomial cores of the band step -/

/-- **Floor step (polynomial core).**  With `ε = 4aγ` and `8γ ≤ n ≤ 1/4`, the quantity by which the
new floor `q(1 − n(1+8aγ))` falls short of the guaranteed drop is `aγ(6n − 8γ − 8γn − 8aγn) ≥ 0`. -/
theorem tight_band_step_lo_core {a gam n : ℝ} (ha2 : a ≤ 1)
    (hgam : 0 < gam) (_hgam8 : gam ≤ 1 / 8) (hn : 8 * gam ≤ n) (hn4 : n ≤ 1 / 4) :
    0 ≤ 6 * n - 8 * gam - 8 * gam * n - 8 * a * gam * n := by
  have hn0 : (0 : ℝ) ≤ n := by linarith only [hgam, hn]
  have h1 : 8 * gam * n ≤ n * n := by nlinarith only [hn, hn0]
  have h2 : 8 * a * gam * n ≤ 8 * gam * n := by
    linarith only [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a) (mul_nonneg hgam.le hn0)]
  nlinarith only [hn, hn4, hn0, h2]

/-- **Ceiling step (polynomial core).**  With `ε = 4aγ` and `8γ ≤ n ≤ 1/4`, the first-order gain
`4an + 8an²` of the ceiling dominates all the correction terms. -/
theorem tight_band_step_hi_core {a gam n : ℝ} (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 1)
    (hgam : 0 < gam) (_hgam8 : gam ≤ 1 / 8) (hn : 8 * gam ≤ n) (hn4 : n ≤ 1 / 4) :
    0 ≤ 4 * a * n + 8 * a * n ^ 2 - a * gam * (1 - n) ^ 2 - 8 * a ^ 2 * gam * n * (1 + n)
        - (4 * a * gam) * (1 + n) ^ 2
        - a * (4 * a * gam) * gam * (1 + n) * (1 - n) * (1 - gam) := by
  have hn0 : (0 : ℝ) ≤ n := by linarith only [hgam, hn]
  have ha0 : (0 : ℝ) ≤ a := by linarith only [ha1]
  have hgn : gam ≤ n / 8 := by linarith only [hn]
  have han : (0 : ℝ) ≤ a * n := mul_nonneg ha0 hn0
  have h1 : a * gam * (1 - n) ^ 2 ≤ a * n / 8 := by
    calc a * gam * (1 - n) ^ 2 ≤ a * (n / 8) * 1 := by gcongr; nlinarith only [hn4, hn0]
      _ = a * n / 8 := by ring
  have h2 : 8 * a ^ 2 * gam * n * (1 + n) ≤ a * n / 2 := by
    have hb : 8 * a * gam * (1 + n) ≤ 1 / 2 := by
      calc
        8 * a * gam * (1 + n) ≤ 8 * 1 * (1 / 32) * (1 + 1 / 4) :=
          by gcongr; linarith only [hn4, hgn]
        _ ≤ 1 / 2 := by norm_num
    calc 8 * a ^ 2 * gam * n * (1 + n) = (a * n) * (8 * a * gam * (1 + n)) := by ring
      _ ≤ (a * n) * (1 / 2) := mul_le_mul_of_nonneg_left hb han
      _ = a * n / 2 := by ring
  have h3 : (4 * a * gam) * (1 + n) ^ 2 ≤ a * n := by
    calc (4 * a * gam) * (1 + n) ^ 2 ≤ (4 * a * (n / 8)) * (1 + 1 / 4) ^ 2 := by
          gcongr
      _ ≤ a * n := by linarith only [han]
  have h4 : a * (4 * a * gam) * gam * (1 + n) * (1 - n) * (1 - gam) ≤ a * n / 8 := by
    calc a * (4 * a * gam) * gam * (1 + n) * (1 - n) * (1 - gam)
        ≤ 1 * (4 * 1 * (n / 8)) * (n / 8) * (1 + 1 / 4) * 1 * 1 := by gcongr <;> nlinarith
      _ ≤ a * n / 8 := by nlinarith only [ha1, hgam, hn, hn4]
  nlinarith [mul_nonneg ha0 (mul_nonneg hn0 hn0)]

/-- **Floor step (scaled).** The polynomial core
`LeanPool.AsymptoticTrianglePacking.Internal.tight_band_step_lo_core`, multiplied by
the common factor `q^k` carried by both ends of the band. -/
theorem tight_band_step_lo_scaled {a gam eps q qk n : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 1)
    (hgam : 0 < gam) (hgam8 : gam ≤ 1 / 8) (hn : 8 * gam ≤ n) (hn4 : n ≤ 1 / 4)
    (hqk : 0 < qk) (heps : eps = 4 * a * gam) (hq : q = 1 - a * gam) :
    qk * q * (1 - n * (1 + 8 * a * gam))
      ≤ qk * (1 - n) - a * gam * (qk * (1 + n)) - 2 * eps * gam * (qk * (1 + n)) := by
  have hcore := tight_band_step_lo_core ha2 hgam hgam8 hn hn4
  have hprod : 0 ≤ a * gam * (6 * n - 8 * gam - 8 * gam * n - 8 * a * gam * n) :=
    mul_nonneg (mul_nonneg ha0 hgam.le) hcore
  have hscal : q * (1 - n * (1 + 8 * a * gam)) ≤ (1 - n) - (a + 2 * eps) * gam * (1 + n) := by
    rw [hq, heps]
    linarith only [hprod]
  have hmul : qk * (q * (1 - n * (1 + 8 * a * gam)))
      ≤ qk * ((1 - n) - (a + 2 * eps) * gam * (1 + n)) :=
    mul_le_mul_of_nonneg_left hscal hqk.le
  linarith only [hmul]

/-- **Ceiling step (scaled).** The polynomial core
`LeanPool.AsymptoticTrianglePacking.Internal.tight_band_step_hi_core`, after clearing
the denominator `1 + n` and multiplying by the common factor `q^k` carried by both ends of the
band. -/
theorem tight_band_step_hi_scaled {a gam eps q qk n : ℝ} (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 1)
    (hgam : 0 < gam) (hgam8 : gam ≤ 1 / 8) (hn : 8 * gam ≤ n) (hn4 : n ≤ 1 / 4)
    (hqk : 0 < qk) (heps : eps = 4 * a * gam) (hq : q = 1 - a * gam) :
    qk * (1 + n) - a * gam * (qk * (1 - n) - eps * gam * (qk * (1 + n))) * (qk * (1 - n))
          * (1 - gam) / (qk * (1 + n)) + eps * gam * (qk * (1 + n))
      ≤ qk * q * (1 + n * (1 + 8 * a * gam)) := by
  have hn0 : (0 : ℝ) ≤ n := by linarith only [hgam, hn]
  have h1n : (0 : ℝ) < 1 + n := by linarith only [hn0]
  have hcore := tight_band_step_hi_core ha1 ha2 hgam hgam8 hn hn4
  have hinner : 0 ≤ 4 * a * n + 8 * a * n ^ 2 - a * gam * (1 - n) ^ 2
      - 8 * a ^ 2 * gam * n * (1 + n) - eps * (1 + n) ^ 2
      - a * eps * gam * (1 + n) * (1 - n) * (1 - gam) := by
    rw [heps]; linarith only [hcore]
  have hprod : 0 ≤ gam * (4 * a * n + 8 * a * n ^ 2 - a * gam * (1 - n) ^ 2
      - 8 * a ^ 2 * gam * n * (1 + n) - eps * (1 + n) ^ 2
      - a * eps * gam * (1 + n) * (1 - n) * (1 - gam)) :=
    mul_nonneg hgam.le hinner
  have hexpand : ((1 + n)
        - a * gam * ((1 - n - eps * gam * (1 + n)) * (1 - n) * (1 - gam)) / (1 + n)
        + eps * gam * (1 + n)) * (1 + n)
      = (1 + n) ^ 2 + eps * gam * (1 + n) ^ 2
        - a * gam * ((1 - n - eps * gam * (1 + n)) * (1 - n) * (1 - gam)) := by
    field_simp
    ring
  have hpoly : (1 + n) ^ 2 + eps * gam * (1 + n) ^ 2
        - a * gam * ((1 - n - eps * gam * (1 + n)) * (1 - n) * (1 - gam))
      ≤ (q * (1 + n * (1 + 8 * a * gam))) * (1 + n) := by
    rw [hq]; linarith only [hprod]
  have hscal : (1 + n)
        - a * gam * ((1 - n - eps * gam * (1 + n)) * (1 - n) * (1 - gam)) / (1 + n)
        + eps * gam * (1 + n)
      ≤ q * (1 + n * (1 + 8 * a * gam)) := by
    refine le_of_mul_le_mul_right ?_ h1n
    rw [hexpand]
    exact hpoly
  have hLHS : qk * (1 + n) - a * gam * (qk * (1 - n) - eps * gam * (qk * (1 + n)))
        * (qk * (1 - n)) * (1 - gam) / (qk * (1 + n)) + eps * gam * (qk * (1 + n))
      = qk * ((1 + n)
        - a * gam * ((1 - n - eps * gam * (1 + n)) * (1 - n) * (1 - gam)) / (1 + n)
        + eps * gam * (1 + n)) := by
    field_simp
  rw [hLHS]
  calc qk * ((1 + n)
        - a * gam * ((1 - n - eps * gam * (1 + n)) * (1 - n) * (1 - gam)) / (1 + n)
        + eps * gam * (1 + n))
      ≤ qk * (q * (1 + n * (1 + 8 * a * gam))) := mul_le_mul_of_nonneg_left hscal hqk.le
    _ = qk * q * (1 + n * (1 + 8 * a * gam)) := by ring

/-- **The band width stays below `1/4`.**  With `γ ≤ exp(−8M−1)/32` and `γT ≤ M + γ`, the relative
width `n k = 8γ(1 + 8aγ)^k` never exceeds `1/4` before the last round. -/
theorem tight_band_width_le_quarter {a gam M : ℝ} {T k : ℕ} (ha0 : 0 ≤ a) (ha2 : a ≤ 1)
    (hgam : 0 < gam) (hgam8 : gam ≤ 1 / 8) (hgamE : gam ≤ Real.exp (-(8 * M) - 1) / 32)
    (hM0 : 0 < M) (hgamT_ub : gam * (T : ℝ) ≤ M + gam) (hk : k ≤ T) :
    8 * gam * (1 + 8 * a * gam) ^ k ≤ 1 / 4 := by
  have hbase1 : (1 : ℝ) ≤ 1 + 8 * a * gam := by
    linarith only [mul_nonneg ha0 hgam.le]
  have hp1 : (1 + 8 * a * gam) ^ k ≤ (1 + 8 * a * gam) ^ T := pow_le_pow_right₀ hbase1 hk
  have hexpb : 1 + 8 * a * gam ≤ Real.exp (8 * a * gam) := by
    linarith only [Real.add_one_le_exp (8 * a * gam)]
  have hp2 : (1 + 8 * a * gam) ^ T ≤ Real.exp (8 * a * gam) ^ T :=
    pow_le_pow_left₀ (by linarith) hexpb T
  have hp3 : Real.exp (8 * a * gam) ^ T = Real.exp ((T : ℝ) * (8 * a * gam)) :=
    (Real.exp_nat_mul _ _).symm
  have hle : (T : ℝ) * (8 * a * gam) ≤ 8 * M + 1 := by
    have h1 : (T : ℝ) * (8 * a * gam) = 8 * a * (gam * (T : ℝ)) := by ring
    have h3 : (0 : ℝ) ≤ gam * (T : ℝ) := by positivity
    linarith only [h1, hgam8,
      mul_le_mul_of_nonneg_left hgamT_ub (show (0 : ℝ) ≤ 8 * a by linarith only [ha0]),
      mul_le_mul_of_nonneg_right ha2 (show (0 : ℝ) ≤ M + gam by linarith only [hM0, hgam])]
  have hp4 : Real.exp ((T : ℝ) * (8 * a * gam)) ≤ Real.exp (8 * M + 1) :=
    Real.exp_le_exp.mpr hle
  have hchain : (1 + 8 * a * gam) ^ k ≤ Real.exp (8 * M + 1) := by
    calc (1 + 8 * a * gam) ^ k ≤ (1 + 8 * a * gam) ^ T := hp1
      _ ≤ Real.exp (8 * a * gam) ^ T := hp2
      _ = Real.exp ((T : ℝ) * (8 * a * gam)) := hp3
      _ ≤ Real.exp (8 * M + 1) := hp4
  have hexpprod : Real.exp (-(8 * M) - 1) * Real.exp (8 * M + 1) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hEpos : (0 : ℝ) < Real.exp (8 * M + 1) := Real.exp_pos _
  calc 8 * gam * (1 + 8 * a * gam) ^ k
      ≤ 8 * gam * Real.exp (8 * M + 1) := by
        linarith only [mul_le_mul_of_nonneg_left hchain
          (show (0 : ℝ) ≤ 8 * gam by linarith only [hgam])]
    _ ≤ 8 * (Real.exp (-(8 * M) - 1) / 32) * Real.exp (8 * M + 1) := by
        linarith only [mul_le_mul_of_nonneg_right hgamE hEpos.le]
    _ = (Real.exp (-(8 * M) - 1) * Real.exp (8 * M + 1)) / 4 := by ring
    _ = 1 / 4 := by rw [hexpprod]

/-- **The total decay of the schedule.**  `γT ≥ M = 16rL + 1` with `L = log(1/β)` gives
`(1 − γ/(16r))^T ≤ exp(−L) = β`. -/
theorem tight_schedule_decay_le {gam L M β : ℝ} {r T : ℕ} (hrR : (2 : ℝ) ≤ (r : ℝ))
    (hgam : 0 < gam) (hgam8 : gam ≤ 1 / 8) (hβ0 : 0 < β)
    (hLdef : L = -Real.log β) (hMdef : M = 16 * (r : ℝ) * L + 1) (hgamT_lb : M ≤ gam * (T : ℝ)) :
    (1 - gam / (16 * r)) ^ T ≤ β := by
  have hcsmall : gam / (16 * r) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith only [hgam8, hrR]
  have h1 : (1 : ℝ) - gam / (16 * r) ≤ Real.exp (-(gam / (16 * r))) := by
    linarith only [Real.add_one_le_exp (-(gam / (16 * r)))]
  have h2 : (0 : ℝ) ≤ 1 - gam / (16 * r) := by linarith only [hcsmall]
  have h3 : (1 - gam / (16 * r)) ^ T ≤ Real.exp (-(gam / (16 * r))) ^ T :=
    pow_le_pow_left₀ h2 h1 T
  have h4 : Real.exp (-(gam / (16 * r))) ^ T = Real.exp ((T : ℝ) * -(gam / (16 * r))) :=
    (Real.exp_nat_mul _ _).symm
  have h5 : (T : ℝ) * -(gam / (16 * r)) ≤ -L := by
    have hML : L ≤ M / (16 * (r : ℝ)) := by
      rw [le_div_iff₀ (by linarith), hMdef]
      linarith only []
    have h6 : M / (16 * (r : ℝ)) ≤ gam * (T : ℝ) / (16 * (r : ℝ)) :=
      div_le_div_of_nonneg_right hgamT_lb (by linarith)
    have h7 : (T : ℝ) * -(gam / (16 * r)) = -(gam * (T : ℝ) / (16 * (r : ℝ))) := by
      field_simp
    rw [h7]
    linarith only [hML, h6]
  have h8 : Real.exp ((T : ℝ) * -(gam / (16 * r))) ≤ Real.exp (-L) := Real.exp_le_exp.mpr h5
  have h9 : Real.exp (-L) = β := by rw [hLdef, neg_neg]; exact Real.exp_log hβ0
  calc (1 - gam / (16 * r)) ^ T ≤ Real.exp (-(gam / (16 * r))) ^ T := h3
    _ = Real.exp ((T : ℝ) * -(gam / (16 * r))) := h4
    _ ≤ Real.exp (-L) := h8
    _ = β := h9

/-! ## The schedule -/

/-- **The tight-band schedule exists.** -/
theorem exists_tightParams (r : ℕ) (hr : 2 ≤ r) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Nonempty (TightParams r β) := by
  classical
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith only [hrR]
  -- the drop constant
  obtain ⟨a, hadef⟩ : ∃ x : ℝ, x = ((r : ℝ) - 1) / r := ⟨_, rfl⟩
  have ha1 : (1 : ℝ) / 2 ≤ a := by rw [hadef, le_div_iff₀ hr0]; linarith only [hrR]
  have ha2 : a ≤ 1 := by rw [hadef, div_le_one hr0]; linarith only []
  have ha0 : (0 : ℝ) ≤ a := by linarith only [ha1]
  -- the logarithmic scale
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = -Real.log β := ⟨_, rfl⟩
  have hLpos : 0 < L := by rw [hLdef]; have := Real.log_neg hβ0 hβ1; linarith only [this]
  obtain ⟨M, hMdef⟩ : ∃ x : ℝ, x = 16 * (r : ℝ) * L + 1 := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith only [mul_pos hr0 hLpos]
  have hM0 : (0 : ℝ) < M := by linarith only [hM1]
  -- the round rate
  obtain ⟨gam, hgdef⟩ : ∃ x : ℝ, x = min (1 / 8) (Real.exp (-(8 * M) - 1) / 32) := ⟨_, rfl⟩
  have hgam8 : gam ≤ 1 / 8 := by rw [hgdef]; exact min_le_left _ _
  have hgamE : gam ≤ Real.exp (-(8 * M) - 1) / 32 := by rw [hgdef]; exact min_le_right _ _
  have hgam : 0 < gam := by
    rw [hgdef]; exact lt_min (by norm_num) (by positivity)
  -- the derived parameters
  obtain ⟨eps, hepsdef⟩ : ∃ x : ℝ, x = 4 * a * gam := ⟨_, rfl⟩
  have hagam : (0 : ℝ) < a * gam := mul_pos (by linarith only [ha1]) hgam
  have hagam8 : a * gam ≤ 1 * (1 / 8) :=
    mul_le_mul ha2 hgam8 hgam.le (by norm_num)
  have hepspos : 0 < eps := by rw [hepsdef]; linarith only [hagam]
  have hepsle : eps ≤ 1 := by rw [hepsdef]; linarith only [hagam8]
  obtain ⟨q, hqdef⟩ : ∃ x : ℝ, x = 1 - a * gam := ⟨_, rfl⟩
  have hqpos : 0 < q := by rw [hqdef]; linarith only [hagam8]
  have hq1 : q ≤ 1 := by rw [hqdef]; linarith only [hagam]
  obtain ⟨T, hTdef⟩ : ∃ m : ℕ, m = ⌈M / gam⌉₊ := ⟨_, rfl⟩
  have hgamT_lb : M ≤ gam * (T : ℝ) := by
    have h := Nat.le_ceil (M / gam)
    rw [← hTdef] at h
    rw [div_le_iff₀ hgam] at h
    linarith only [h]
  have hgamT_ub : gam * (T : ℝ) ≤ M + gam := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ M / gam by positivity)
    rw [← hTdef] at h
    have h2 : (T : ℝ) * gam < (M / gam + 1) * gam :=
      mul_lt_mul_of_pos_right h hgam
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hgam)] at h2
    linarith only [h2]
  -- the band
  obtain ⟨nf, hnfdef⟩ : ∃ f : ℕ → ℝ, f = fun k => 8 * gam * (1 + 8 * a * gam) ^ k := ⟨_, rfl⟩
  have hnfa : ∀ k, nf k = 8 * gam * (1 + 8 * a * gam) ^ k := by intro k; rw [hnfdef]
  have hbase1 : (1 : ℝ) ≤ 1 + 8 * a * gam := by linarith only [hagam]
  have hnf_lb : ∀ k, 8 * gam ≤ nf k := by
    intro k
    rw [hnfa k]
    have : (1 : ℝ) ≤ (1 + 8 * a * gam) ^ k := one_le_pow₀ hbase1
    linarith only [mul_nonneg hgam.le (sub_nonneg.mpr this)]
  have hnf_ub : ∀ k, k ≤ T → nf k ≤ 1 / 4 := by
    intro k hk
    rw [hnfa k]
    exact tight_band_width_le_quarter ha0 ha2 hgam hgam8 hgamE hM0 hgamT_ub hk
  obtain ⟨lo, hlodef⟩ : ∃ f : ℕ → ℝ, f = fun k => q ^ k * (1 - nf k) := ⟨_, rfl⟩
  obtain ⟨hi, hhidef⟩ : ∃ f : ℕ → ℝ, f = fun k => q ^ k * (1 + nf k) := ⟨_, rfl⟩
  have hloa : ∀ k, lo k = q ^ k * (1 - nf k) := by intro k; rw [hlodef]
  have hhia : ∀ k, hi k = q ^ k * (1 + nf k) := by intro k; rw [hhidef]
  have hqk : ∀ k : ℕ, (0 : ℝ) < q ^ k := fun k => pow_pos hqpos k
  -- the exceptional budget
  obtain ⟨Gg, hGdef⟩ : ∃ x : ℝ, x = (2 + (r : ℝ) / (eps * gam)) ^ 2 := ⟨_, rfl⟩
  have hGge : (4 : ℝ) ≤ Gg := by
    rw [hGdef]
    have hpos : (0 : ℝ) < (r : ℝ) / (eps * gam) := by positivity
    nlinarith only [hpos]
  have hGpow : ∀ k : ℕ, (1 : ℝ) ≤ (2 * Gg) ^ k := by
    intro k; exact one_le_pow₀ (by linarith)
  have hGpowpos : ∀ k : ℕ, (0 : ℝ) < (2 * Gg) ^ k := fun k => lt_of_lt_of_le one_pos (hGpow k)
  obtain ⟨exc, hexcdef⟩ : ∃ x : ℝ, x = β / (8 * (2 * Gg) ^ T) := ⟨_, rfl⟩
  have hexcpos : 0 < exc := by
    rw [hexcdef]; exact div_pos hβ0 (by linarith only [hGpowpos T])
  have hexcle : exc ≤ 1 := by
    rw [hexcdef, div_le_one (by linarith only [hGpowpos T])]
    linarith only [hGpow T, hβ1]
  obtain ⟨sig, hsigdef⟩ : ∃ f : ℕ → ℝ, f = fun k => 2 * exc * (2 * Gg) ^ k := ⟨_, rfl⟩
  have hsiga : ∀ k, sig k = 2 * exc * (2 * Gg) ^ k := by intro k; rw [hsigdef]
  refine ⟨{
    gam := gam
    eps := eps
    exc := exc
    eta := exc
    wid := 8 * gam
    lomin := 3 / 4 * q ^ T
    T := T
    lo := lo
    hi := hi
    sig := sig
    gam_pos := hgam
    gam_le := by linarith only [hgam8]
    eps_pos := hepspos
    eps_le := hepsle
    two_gam_le_eps := by
      rw [hepsdef]
      linarith only [mul_nonneg (show (0 : ℝ) ≤ 4 * a - 2 by linarith only [ha1]) hgam.le]
    exc_pos := hexcpos
    exc_le := hexcle
    eta_pos := hexcpos
    wid_pos := by linarith only [hgam]
    lomin_pos := by positivity
    lomin_le := ?_
    hi_le_two_lo := ?_
    lo_le_hi := ?_
    init_lo := ?_
    init_hi := ?_
    step_lo := ?_
    step_hi := ?_
    sig_init := ?_
    sig_step := ?_
    sig_le := ?_
    decay := ?_ }⟩
  · -- `lomin ≤ lo k`
    intro k hk
    rw [hloa k]
    have h1 : q ^ T ≤ q ^ k := pow_le_pow_of_le_one hqpos.le hq1 hk
    have h2 : nf k ≤ 1 / 4 := hnf_ub k hk
    linarith only [h1, mul_le_mul_of_nonneg_left h2 (hqk k).le]
  · -- `hi k ≤ 2 lo k`
    intro k hk
    rw [hloa k, hhia k]
    have h2 : nf k ≤ 1 / 4 := hnf_ub k hk
    linarith only [mul_le_mul_of_nonneg_left h2 (hqk k).le, (hqk k).le]
  · -- `lo k ≤ hi k`
    intro k _
    rw [hloa k, hhia k]
    have h0 : (0 : ℝ) ≤ nf k := le_trans (by positivity) (hnf_lb k)
    linarith only [mul_nonneg (hqk k).le h0]
  · -- `lo 0 ≤ 1 - wid`
    rw [hloa 0, hnfa 0]
    norm_num
  · -- `1 + wid ≤ hi 0`
    rw [hhia 0, hnfa 0]
    norm_num
  · -- the floor step
    intro k hk
    have hsucc : nf (k + 1) = nf k * (1 + 8 * a * gam) := by
      rw [hnfa (k + 1), hnfa k, pow_succ]; ring
    rw [hloa (k + 1), hloa k, hhia k, hsucc, pow_succ, ← hadef]
    exact tight_band_step_lo_scaled ha0 ha2 hgam hgam8 (hnf_lb k) (hnf_ub k (le_of_lt hk))
      (hqk k) hepsdef hqdef
  · -- the ceiling step
    intro k hk
    have hsucc : nf (k + 1) = nf k * (1 + 8 * a * gam) := by
      rw [hnfa (k + 1), hnfa k, pow_succ]; ring
    rw [hhia (k + 1), hhia k, hloa k, hsucc, pow_succ, ← hadef]
    exact tight_band_step_hi_scaled ha1 ha2 hgam hgam8 (hnf_lb k) (hnf_ub k (le_of_lt hk))
      (hqk k) hepsdef hqdef
  · -- `eta ≤ sig 0`
    rw [hsiga 0, pow_zero]
    linarith only [hexcpos]
  · -- the exceptional growth
    intro k _
    rw [hsiga k, hsiga (k + 1), ← hGdef]
    have h1 : (1 : ℝ) ≤ (2 * Gg) ^ k := hGpow k
    have hpow : (2 * Gg) ^ (k + 1) = 2 * Gg * (2 * Gg) ^ k := by rw [pow_succ]; ring
    rw [hpow]
    linarith only [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ Gg by linarith only [hGge])
        hexcpos.le) (show (0 : ℝ) ≤ (2 * Gg) ^ k - 1 by linarith only [h1]),
      mul_nonneg (show (0 : ℝ) ≤ Gg by linarith only [hGge]) hexcpos.le]
  · -- `sig k ≤ β/2`
    intro k hk
    rw [hsiga k, hexcdef]
    have h1 : (2 * Gg) ^ k ≤ (2 * Gg) ^ T := pow_le_pow_right₀ (by linarith) hk
    have hTpos : (0 : ℝ) < (2 * Gg) ^ T := hGpowpos T
    have hrw : 2 * (β / (8 * (2 * Gg) ^ T)) * (2 * Gg) ^ k
        = β * (2 * Gg) ^ k / (4 * (2 * Gg) ^ T) := by
      field_simp
      ring
    rw [hrw, div_le_iff₀ (by linarith : (0 : ℝ) < 4 * (2 * Gg) ^ T)]
    linarith only [mul_le_mul_of_nonneg_left h1 hβ0.le, mul_nonneg hβ0.le hTpos.le]
  · -- the decay
    exact tight_schedule_decay_le hrR hgam hgam8 hβ0 hLdef hMdef hgamT_lb

end LeanPool.AsymptoticTrianglePacking.Internal
