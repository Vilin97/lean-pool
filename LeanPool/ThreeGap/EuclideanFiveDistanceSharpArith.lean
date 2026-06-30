/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/
import LeanPool.ThreeGap.EuclideanFiveDistanceSharp

/-!
# Toward arithmetic sharpness of `g₂ ≤ 5`: five distances are attained (dynamics-free route)

`nnDistE_count_le_five` proves the **upper** bound (≤ 5 distinct nearest-neighbour distances).
**Sharpness** — that 5 distinct distances are actually *attained* — is, in Haynes–Marklof, a
homogeneous-dynamics (equidistribution) statement. This file develops an **elementary, dynamics-free
route** to a concrete witness, discovered by unfolding the repo's own definitions.

## The structural bypass

`nnDistE α N q = inf_{1 ≤ d ≤ max(q, N−q)} deltaN (euclNorm 2) α d` (`= gapVal (deltaE α) N q`,
already in the repo). This prefix-minimum is non-increasing in the cutoff `D = max(q, N−q)`, which
ranges over `[⌈N/2⌉, N]` as `q` ranges over `{0,…,N}`. It drops *exactly* at the best-approximation
records (whose defects strictly decrease). Hence

> **number of distinct distances `= 1 + #{record denominators in (⌈N/2⌉, N]}`.**

So sharpness ↔ **four record denominators in the doubling window `(⌈N/2⌉, N]`** — the extremal case
of
the proven growth `2qₙ ≤ q_{n+4}` (`euclidean_growth_four`). No dynamics.

## The concrete witness (verified numerically; integer/modular, exactly certifiable)

`α* = (3/29, 8/29)`, `N = 11`. Because `ℤ²` is a product and the norm is Euclidean,
`deltaN (euclNorm 2) α* d = √(r(3d)² + r(8d)²) / 29`, where `r(m)` is the balanced residue of `m`
mod `29` (in `[−14,14]`) — coordinatewise, **no 2-D lattice search**. The squared scaled defects
`K_d = r(3d)² + r(8d)²` for `d = 1,…,11` are

`[73, 205, 106, 153, 317, 221, 68, 61, 200, 50, 17]`,

with record minima at `d = 1, 7, 8, 10, 11` (values `73 > 68 > 61 > 50 > 17`). The records inside
`(⌈11/2⌉, 11] = (6, 11]` are `7, 8, 10, 11` — **four** — giving the **five** distinct distances
`√73, √68, √61, √50, √17` all over `29`, realized at `q = 5, 4, 3, 1, 0` (cutoffs `D =
6,7,8,10,11`).

## Remaining atoms (each elementary, no research gap)

* **R4.** `deltaN α* d = √(r(3d)²+r(8d)²)/29` and the four strict drops, via per-coordinate integer
  facts: upper bound by `deltaN_le` at the rounding `p`; lower bound by `le_ciInf` + `|m − 29k| ≥
  |r(m)|`. All comparisons are between integers `K_d`.
* **R5.** rational → irrational: each strict drop `deltaN α a < deltaN α b` is Lipschitz in `α`
  (`deltaN · d` is `d`-Lipschitz, `dist(·,ℤ²)` being 1-Lipschitz), with explicit integer slack at
  `α*`; perturb one coordinate to an irrational inside that slack. Then `count ≥ 5` (this file's
  `five_le_card_image_of_strictAnti_chain`) and `count ≤ 5` (`nnDistE_count_le_five`) give `= 5`.

`five_le_card_image_of_strictAnti_chain` below is the foundational R3 step (axiom-clean).
-/

namespace ThreeGap.EuclideanRecords

open scoped Real
open ThreeGap.SimApprox ThreeGap.Chevallier

/-- **Per-coordinate integer minimum (R4 crux).** If `r` is the balanced residue of `a` mod `m`
(`m ∣ a − r` and `2|r| ≤ m`), then `r²` is the minimum of `(a − m·k)²` over all integers `k` — the
nearest multiple of `m` to `a` is at distance `|r|`. This is the coordinatewise core of the defect
lower bound `deltaN α* d ≥ √(r(3d)²+r(8d)²)/29`: since `ℤ²` is a product and the norm Euclidean, the
nearest lattice point is coordinatewise nearest. -/
theorem sq_residue_le (m r a : ℤ) (hm : 0 < m) (h2r : 2 * |r| ≤ m) (hcong : m ∣ (a - r)) :
    ∀ k : ℤ, r ^ 2 ≤ (a - m * k) ^ 2 := by
  intro k
  obtain ⟨c, hc⟩ := hcong
  have hj : a - m * k = r + m * (c - k) := by linarith [hc]
  rw [hj]
  set j := c - k with hjdef
  have h2r' : |2 * r| ≤ m := by rw [abs_mul, abs_of_pos (by norm_num : (0:ℤ) < 2)]; exact h2r
  rcases abs_le.mp h2r' with ⟨hr1, hr2⟩
  rcases lt_trichotomy j 0 with hj0 | hj0 | hj0
  · have h1 : 0 ≤ -j := by omega
    have h2 : 0 ≤ -j - 1 := by omega
    nlinarith [mul_nonneg (show (0:ℤ) ≤ m - 2 * r by linarith) (mul_nonneg hm.le h1),
      mul_nonneg (mul_nonneg hm.le hm.le) (mul_nonneg h1 h2)]
  · simp [hj0]
  · have h1 : 0 ≤ j := by omega
    have h2 : 0 ≤ j - 1 := by omega
    nlinarith [mul_nonneg (show (0:ℤ) ≤ 2 * r + m by linarith) (mul_nonneg hm.le h1),
      mul_nonneg (mul_nonneg hm.le hm.le) (mul_nonneg h1 h2)]

/-- The rational witness `α* = (3/29, 8/29)`. -/
noncomputable def astar : Fin 2 → ℝ := ![3 / 29, 8 / 29]

/-- `euclNorm 2` of an explicit plane vector is `√(x₀² + x₁²)`. -/
theorem euclNorm_two (x : Fin 2 → ℝ) : euclNorm 2 x = Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by
  rw [euclNorm, EuclideanSpace.norm_eq]; congr 1
  rw [Fin.sum_univ_two]; simp [Real.norm_eq_abs, sq_abs]

/-- **Defect by attainment + lower bound.** If some translate realizes value `c` and `c` bounds all
translates below, the defect equals `c`. -/
theorem deltaN_eq_of (α : Fin 2 → ℝ) (q : ℤ) (c : ℝ)
    (hattain : ∃ p, euclNorm 2 (rem α q p) = c) (hlb : ∀ p, c ≤ euclNorm 2 (rem α q p)) :
    deltaN (euclNorm 2) α q = c := by
  refine le_antisymm ?_ (le_ciInf hlb)
  obtain ⟨p, hp⟩ := hattain
  exact (deltaN_le (euclNorm 2) euclNorm_nonneg α q p).trans hp.le

/-- **The witness defect is coordinatewise-exact (R4b).** With `α* = (3/29, 8/29)`, balanced
residues `3d ≡ r₀`, `8d ≡ r₁ (mod 29)` give `deltaN α* d = √(r₀² + r₁²)/29`. Upper bound at the
rounding `(n₀,n₁)`; lower bound coordinatewise via `sq_residue_le`. -/
theorem deltaN_astar (d : ℤ) (n₀ n₁ r₀ r₁ : ℤ)
    (hr0 : 3 * d = r₀ + 29 * n₀) (hr1 : 8 * d = r₁ + 29 * n₁)
    (hb0 : 2 * |r₀| ≤ 29) (hb1 : 2 * |r₁| ≤ 29) :
    deltaN (euclNorm 2) astar d = Real.sqrt ((r₀ : ℝ) ^ 2 + (r₁ : ℝ) ^ 2) / 29 := by
  have hcoord : ∀ p : Fin 2 → ℤ, euclNorm 2 (rem astar d p)
      = Real.sqrt ((3 * d - 29 * (p 0) : ℝ) ^ 2 + (8 * d - 29 * (p 1) : ℝ) ^ 2) / 29 := by
    intro p
    rw [euclNorm_two, show (rem astar d p 0) ^ 2 + (rem astar d p 1) ^ 2
        = (((3 * d - 29 * (p 0) : ℝ) ^ 2 + (8 * d - 29 * (p 1) : ℝ) ^ 2) / 29 ^ 2) from by
      simp only [rem, astar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      ring]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 29)]
  apply deltaN_eq_of
  · refine ⟨![n₀, n₁], ?_⟩
    rw [hcoord]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have h0 : (3 * (d : ℝ)) = (r₀ : ℝ) + 29 * (n₀ : ℝ) := by exact_mod_cast hr0
    have h1 : (8 * (d : ℝ)) = (r₁ : ℝ) + 29 * (n₁ : ℝ) := by exact_mod_cast hr1
    rw [show (3 * (d : ℝ) - 29 * (n₀ : ℝ)) = (r₀ : ℝ) by linarith,
        show (8 * (d : ℝ) - 29 * (n₁ : ℝ)) = (r₁ : ℝ) by linarith]
  · intro p
    rw [hcoord, div_eq_mul_inv, div_eq_mul_inv]
    have e0 := sq_residue_le 29 r₀ (3 * d) (by norm_num) hb0 ⟨n₀, by linarith [hr0]⟩ (p 0)
    have e1 := sq_residue_le 29 r₁ (8 * d) (by norm_num) hb1 ⟨n₁, by linarith [hr1]⟩ (p 1)
    have e0' : (r₀ : ℝ) ^ 2 ≤ (3 * d - 29 * (p 0) : ℝ) ^ 2 := by exact_mod_cast e0
    have e1' : (r₁ : ℝ) ^ 2 ≤ (8 * d - 29 * (p 1) : ℝ) ^ 2 := by exact_mod_cast e1
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (by norm_num)

/-- The eleven witness defects `deltaN α* d = √(K_d)/29`, `d = 1,…,11`, with
`K_d = [73,205,106,153,317,221,68,61,200,50,17]` — verified by `deltaN_astar` at the balanced
residues of `3d, 8d` mod 29. -/
theorem dstar1 : deltaN (euclNorm 2) astar 1 = Real.sqrt 73 / 29 := by
  rw [deltaN_astar 1 0 0 3 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
theorem dstar2 : deltaN (euclNorm 2) astar 2 = Real.sqrt 205 / 29 := by
  rw [deltaN_astar 2 0 1 6 (-13) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
theorem dstar3 : deltaN (euclNorm 2) astar 3 = Real.sqrt 106 / 29 := by
  rw [deltaN_astar 3 0 1 9 (-5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
theorem dstar4 : deltaN (euclNorm 2) astar 4 = Real.sqrt 153 / 29 := by
  rw [deltaN_astar 4 0 1 12 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
theorem dstar5 : deltaN (euclNorm 2) astar 5 = Real.sqrt 317 / 29 := by
  rw [deltaN_astar 5 1 1 (-14) 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
theorem dstar6 : deltaN (euclNorm 2) astar 6 = Real.sqrt 221 / 29 := by
  rw [deltaN_astar 6 1 2 (-11) (-10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num
theorem dstar7 : deltaN (euclNorm 2) astar 7 = Real.sqrt 68 / 29 := by
  rw [deltaN_astar 7 1 2 (-8) (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)];
    norm_num
theorem dstar8 : deltaN (euclNorm 2) astar 8 = Real.sqrt 61 / 29 := by
  rw [deltaN_astar 8 1 2 (-5) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
theorem dstar9 : deltaN (euclNorm 2) astar 9 = Real.sqrt 200 / 29 := by
  rw [deltaN_astar 9 1 2 (-2) 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
theorem dstar10 : deltaN (euclNorm 2) astar 10 = Real.sqrt 50 / 29 := by
  rw [deltaN_astar 10 1 3 1 (-7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
theorem dstar11 : deltaN (euclNorm 2) astar 11 = Real.sqrt 17 / 29 := by
  rw [deltaN_astar 11 1 3 4 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- Comparison of two `√K/29` defects reduces to comparing the integers `K`. -/
theorem sqrt_div_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Real.sqrt a / 29 < Real.sqrt b / 29 := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_right (Real.sqrt_lt_sqrt ha hab) (by norm_num)

/-- **The record chain** `deltaN α* 1 > deltaN α* 7 > deltaN α* 8 > deltaN α* 10 > deltaN α* 11`
(`√73 > √68 > √61 > √50 > √17`, all over 29) — the four record drops giving five distances. -/
theorem dstar_chain :
    deltaN (euclNorm 2) astar 11 < deltaN (euclNorm 2) astar 10 ∧
    deltaN (euclNorm 2) astar 10 < deltaN (euclNorm 2) astar 8 ∧
    deltaN (euclNorm 2) astar 8 < deltaN (euclNorm 2) astar 7 ∧
    deltaN (euclNorm 2) astar 7 < deltaN (euclNorm 2) astar 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [dstar11, dstar10]; exact sqrt_div_lt (by norm_num) (by norm_num)
  · rw [dstar10, dstar8]; exact sqrt_div_lt (by norm_num) (by norm_num)
  · rw [dstar8, dstar7]; exact sqrt_div_lt (by norm_num) (by norm_num)
  · rw [dstar7, dstar1]; exact sqrt_div_lt (by norm_num) (by norm_num)

/-- **Five strictly-decreasing sample values force ≥ 5 distinct images.** If `f` takes five values
`f q₀ > f q₁ > f q₂ > f q₃ > f q₄` at points of `Finset.range (N+1)`, then the image of
`Finset.range (N+1)` under `f` has at least five elements. The combinatorial heart of arithmetic
sharpness: exhibiting five strictly-decreasing nearest-neighbour distances. -/
theorem five_le_card_image_of_strictAnti_chain {N : ℕ} (f : ℕ → ℝ) {q₀ q₁ q₂ q₃ q₄ : ℕ}
    (m₀ : q₀ ∈ Finset.range (N + 1)) (m₁ : q₁ ∈ Finset.range (N + 1))
    (m₂ : q₂ ∈ Finset.range (N + 1)) (m₃ : q₃ ∈ Finset.range (N + 1))
    (m₄ : q₄ ∈ Finset.range (N + 1))
    (h01 : f q₁ < f q₀) (h12 : f q₂ < f q₁) (h23 : f q₃ < f q₂) (h34 : f q₄ < f q₃) :
    5 ≤ ((Finset.range (N + 1)).image f).card := by
  have a02 : f q₂ < f q₀ := lt_trans h12 h01
  have a03 : f q₃ < f q₀ := lt_trans h23 a02
  have a04 : f q₄ < f q₀ := lt_trans h34 a03
  have a13 : f q₃ < f q₁ := lt_trans h23 h12
  have a14 : f q₄ < f q₁ := lt_trans h34 a13
  have a24 : f q₄ < f q₂ := lt_trans h34 h23
  have e1 : f q₀ ∉ ({f q₁, f q₂, f q₃, f q₄} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_gt h01, ne_of_gt a02, ne_of_gt a03, ne_of_gt a04⟩
  have e2 : f q₁ ∉ ({f q₂, f q₃, f q₄} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_gt h12, ne_of_gt a13, ne_of_gt a14⟩
  have e3 : f q₂ ∉ ({f q₃, f q₄} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨ne_of_gt h23, ne_of_gt a24⟩
  have e4 : f q₃ ∉ ({f q₄} : Finset ℝ) := by
    simp only [Finset.mem_singleton]; exact ne_of_gt h34
  have hcard : ({f q₀, f q₁, f q₂, f q₃, f q₄} : Finset ℝ).card = 5 := by
    rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
      Finset.card_insert_of_notMem e3, Finset.card_insert_of_notMem e4, Finset.card_singleton]
  have hsub : ({f q₀, f q₁, f q₂, f q₃, f q₄} : Finset ℝ) ⊆ (Finset.range (N + 1)).image f := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact Finset.mem_image_of_mem f ‹_›
  calc 5 = _ := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **`nnDistE` as a prefix-minimum of the defect.** `nnDistE α 11 q` is the infimum of
`deltaN (euclNorm 2) α d` over `d ∈ [1, max(q, 11−q)]` (via the repo's `gapVal_eq_nnDistC`). -/
theorem nnDistE_eq_inf (α : Fin 2 → ℝ) {q : ℕ} (hq : q ≤ 11)
    (hne : (Finset.Icc 1 (max q (11 - q))).Nonempty) :
    nnDistE α 11 q = (Finset.Icc 1 (max q (11 - q))).inf' hne
      (fun n => deltaN (euclNorm 2) α (n : ℤ)) := by
  unfold nnDistE
  rw [← gapVal_eq_nnDistC (deltaN (euclNorm 2) α)
    (deltaN_neg (euclNorm 2) euclNorm_nonneg euclNorm_neg α) (by norm_num) hq, gapVal, dif_pos hne]

/-- A strictly larger prefix has a strictly smaller infimum once a new element `m` beats the whole
shorter prefix. -/
theorem inf_lt_inf (f : ℕ → ℝ) {a b : ℕ} (m : ℕ) (hm : m ∈ Finset.Icc 1 b)
    (hnea : (Finset.Icc 1 a).Nonempty) (hneb : (Finset.Icc 1 b).Nonempty)
    (hlt : ∀ n ∈ Finset.Icc 1 a, f m < f n) :
    (Finset.Icc 1 b).inf' hneb f < (Finset.Icc 1 a).inf' hnea f :=
  lt_of_le_of_lt (Finset.inf'_le f hm) ((Finset.lt_inf'_iff hnea).mpr hlt)

/-- **`card ≥ 5` from the four record drops (R4b-finish).** If the defect drops strictly below the
whole preceding prefix at `d = 7, 8, 10, 11`, then the five `nnDistE α 11 q` at `q = 5,4,3,1,0` are
strictly decreasing, so the image has `≥ 5` elements. -/
theorem card_ge_five (α : Fin 2 → ℝ)
    (H1 : ∀ n ∈ Finset.Icc (1 : ℕ) 6, deltaN (euclNorm 2) α 7 < deltaN (euclNorm 2) α (n : ℤ))
    (H2 : ∀ n ∈ Finset.Icc (1 : ℕ) 7, deltaN (euclNorm 2) α 8 < deltaN (euclNorm 2) α (n : ℤ))
    (H3 : ∀ n ∈ Finset.Icc (1 : ℕ) 8, deltaN (euclNorm 2) α 10 < deltaN (euclNorm 2) α (n : ℤ))
    (H4 : ∀ n ∈ Finset.Icc (1 : ℕ) 10, deltaN (euclNorm 2) α 11 < deltaN (euclNorm 2) α (n : ℤ)) :
    5 ≤ ((Finset.range 12).image (nnDistE α 11)).card := by
  have ne6 : (Finset.Icc 1 6).Nonempty := ⟨1, by decide⟩
  have ne7 : (Finset.Icc 1 7).Nonempty := ⟨1, by decide⟩
  have ne8 : (Finset.Icc 1 8).Nonempty := ⟨1, by decide⟩
  have ne10 : (Finset.Icc 1 10).Nonempty := ⟨1, by decide⟩
  have ne11 : (Finset.Icc 1 11).Nonempty := ⟨1, by decide⟩
  have v5 : nnDistE α 11 5 = (Finset.Icc 1 6).inf' ne6 (fun n => deltaN (euclNorm 2) α n) :=
    nnDistE_eq_inf α (by norm_num) ne6
  have v4 : nnDistE α 11 4 = (Finset.Icc 1 7).inf' ne7 (fun n => deltaN (euclNorm 2) α n) :=
    nnDistE_eq_inf α (by norm_num) ne7
  have v3 : nnDistE α 11 3 = (Finset.Icc 1 8).inf' ne8 (fun n => deltaN (euclNorm 2) α n) :=
    nnDistE_eq_inf α (by norm_num) ne8
  have v1 : nnDistE α 11 1 = (Finset.Icc 1 10).inf' ne10 (fun n => deltaN (euclNorm 2) α n) :=
    nnDistE_eq_inf α (by norm_num) ne10
  have v0 : nnDistE α 11 0 = (Finset.Icc 1 11).inf' ne11 (fun n => deltaN (euclNorm 2) α n) :=
    nnDistE_eq_inf α (by norm_num) ne11
  refine five_le_card_image_of_strictAnti_chain (nnDistE α 11)
    (q₀ := 5) (q₁ := 4) (q₂ := 3) (q₃ := 1) (q₄ := 0) (by decide) (by decide) (by decide)
        (by decide) (by decide) ?_ ?_ ?_ ?_
  · rw [v4, v5]
    refine inf_lt_inf (fun n => deltaN (euclNorm 2) α (n : ℤ)) 7 (by decide) ne6 ne7 (fun n hn =>
      ?_)
    change deltaN (euclNorm 2) α (7 : ℤ) < deltaN (euclNorm 2) α (n : ℤ); exact H1 n hn
  · rw [v3, v4]
    refine inf_lt_inf (fun n => deltaN (euclNorm 2) α (n : ℤ)) 8 (by decide) ne7 ne8 (fun n hn =>
      ?_)
    change deltaN (euclNorm 2) α (8 : ℤ) < deltaN (euclNorm 2) α (n : ℤ); exact H2 n hn
  · rw [v1, v3]
    refine inf_lt_inf (fun n => deltaN (euclNorm 2) α (n : ℤ)) 10 (by decide) ne8 ne10 (fun n hn =>
      ?_)
    change deltaN (euclNorm 2) α (10 : ℤ) < deltaN (euclNorm 2) α (n : ℤ); exact H3 n hn
  · rw [v0, v1]
    refine inf_lt_inf (fun n => deltaN (euclNorm 2) α (n : ℤ)) 11 (by decide) ne10 ne11 (fun n hn =>
      ?_)
    change deltaN (euclNorm 2) α (11 : ℤ) < deltaN (euclNorm 2) α (n : ℤ); exact H4 n hn

/-- **The witness realizes ≥ 5 distinct distances (R4b complete, rational `α*`).** The orbit of
`α* = (3/29, 8/29)` to `N = 11` has at least five distinct Euclidean nearest-neighbour distances —
the four record drops of `card_ge_five` discharged by the `dstar` defect values. -/
theorem card_ge_five_astar :
    5 ≤ ((Finset.range 12).image (nnDistE astar 11)).card := by
  refine card_ge_five astar ?_ ?_ ?_ ?_ <;>
  · intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;>
      simp only [Nat.cast_ofNat, Nat.cast_one, dstar1, dstar2, dstar3, dstar4, dstar5, dstar6,
        dstar7, dstar8, dstar9, dstar10, dstar11] <;>
      exact sqrt_div_lt (by norm_num) (by norm_num)

/-! ### R5: rational → irrational upgrade by Lipschitz-openness -/

/-- **`deltaN · d` is `|d|`-Lipschitz in `α`.** (Both are distances to the lattice; perturbing `α`
by
`α − β` moves `d·α` by `d·(α−β)`.) -/
theorem deltaN_sub_le (α β : Fin 2 → ℝ) (d : ℤ) :
    deltaN (euclNorm 2) α d ≤ deltaN (euclNorm 2) β d + |(d : ℝ)| * euclNorm 2 (α - β) := by
  have hC : ∀ p : Fin 2 → ℤ, deltaN (euclNorm 2) α d
      ≤ euclNorm 2 (rem β d p) + |(d : ℝ)| * euclNorm 2 (α - β) := by
    intro p
    have h1 : deltaN (euclNorm 2) α d ≤ euclNorm 2 (rem α d p) :=
      deltaN_le _ euclNorm_nonneg α d p
    have hdiff : rem α d p - rem β d p = (d : ℝ) • (α - β) := by
      simp only [rem, smul_sub]; ring
    have he : rem β d p + (d : ℝ) • (α - β) = rem α d p := by rw [← hdiff]; ring
    have h2 : euclNorm 2 (rem α d p) ≤ euclNorm 2 (rem β d p) + euclNorm 2 ((d : ℝ) • (α - β)) := by
      have := euclNorm_tri (rem β d p) ((d : ℝ) • (α - β)); rwa [he] at this
    rw [euclNorm_smul] at h2; linarith
  have hkey : deltaN (euclNorm 2) α d - |(d : ℝ)| * euclNorm 2 (α - β) ≤ deltaN (euclNorm 2) β d :=
    le_ciInf (fun p => by linarith [hC p])
  linarith

/-- The perturbed witness `α* + (s, 0) = (3/29 + s, 8/29)`. -/
noncomputable def aprt (s : ℝ) : Fin 2 → ℝ := ![3 / 29 + s, 8 / 29]

theorem eucl_aprt (s : ℝ) (hs : 0 ≤ s) : euclNorm 2 (aprt s - astar) = s := by
  rw [euclNorm_two,
    show (aprt s - astar) 0 = s by simp [aprt, astar],
    show (aprt s - astar) 1 = 0 by simp [aprt, astar]]
  rw [show s ^ 2 + (0:ℝ) ^ 2 = s ^ 2 by ring, Real.sqrt_sq hs]

theorem eucl_aprt' (s : ℝ) (hs : 0 ≤ s) : euclNorm 2 (astar - aprt s) = s := by
  rw [euclNorm_two,
    show (astar - aprt s) 0 = -s by simp [aprt, astar],
    show (astar - aprt s) 1 = 0 by simp [aprt, astar]]
  rw [show (-s) ^ 2 + (0:ℝ) ^ 2 = s ^ 2 by ring, Real.sqrt_sq hs]

theorem aprt_irrational {s : ℝ} (hs : Irrational s) : Irrational (aprt s 0) := by
  have h : aprt s 0 = ((3 / 29 : ℚ) : ℝ) + s := by
    rw [show ((3 / 29 : ℚ) : ℝ) = 3 / 29 by norm_num]; simp [aprt]
  rw [h]; exact hs.ratCast_add _

/-- A uniform gap between two distinct square roots in `[0, 317]`: `√b − √a ≥ 1/(2√317)`, in the
clearing-denominators form `1 ≤ (√b − √a)·2√317`. -/
theorem sqrt_gap (a b : ℝ) (ha : 0 ≤ a) (h1 : a + 1 ≤ b) (hb : b ≤ 317) :
    1 ≤ (Real.sqrt b - Real.sqrt a) * (2 * Real.sqrt 317) := by
  have hbnn : 0 ≤ b := by linarith
  have hsa : Real.sqrt a ≤ Real.sqrt 317 := Real.sqrt_le_sqrt (by linarith)
  have hsb : Real.sqrt b ≤ Real.sqrt 317 := Real.sqrt_le_sqrt hb
  have hdiff : 0 ≤ Real.sqrt b - Real.sqrt a := by
    have := Real.sqrt_le_sqrt (show a ≤ b by linarith); linarith
  have hprod : (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a) = b - a := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hbnn]
  calc (1 : ℝ) ≤ b - a := by linarith
    _ = (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a) := hprod.symm
    _ ≤ (Real.sqrt b - Real.sqrt a) * (2 * Real.sqrt 317) :=
        mul_le_mul_of_nonneg_left (by linarith) hdiff

/-- The gap inequality `29·(c·s) < √Kn − √Km` holds once `s` is small (`1276·s·√317 < 1`), for any
coefficient `c ≤ 22` and integer gap `Km + 1 ≤ Kn ≤ 317`. -/
theorem gap_ok (c Km Kn s : ℝ) (hs0 : 0 ≤ s) (hc : c ≤ 22)
    (hKa : 0 ≤ Km) (hK : Km + 1 ≤ Kn) (hKb : Kn ≤ 317)
    (hsmall : 1276 * s * Real.sqrt 317 < 1) :
    29 * (c * s) < Real.sqrt Kn - Real.sqrt Km := by
  have hkey := sqrt_gap Km Kn hKa hK hKb
  have h317 : 0 < Real.sqrt 317 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [hkey, hsmall, h317, mul_nonneg hs0 h317.le,
    mul_nonneg (sub_nonneg.mpr hc) (mul_nonneg hs0 h317.le)]

/-- **Transport an inequality from `α*` to the perturbed witness.** -/
theorem transport (s : ℝ) (hs0 : 0 ≤ s) (m n : ℤ) (Km Kn : ℝ)
    (hm : deltaN (euclNorm 2) astar m = Real.sqrt Km / 29)
    (hn : deltaN (euclNorm 2) astar n = Real.sqrt Kn / 29)
    (hgap : 29 * ((|(m : ℝ)| + |(n : ℝ)|) * s) < Real.sqrt Kn - Real.sqrt Km) :
    deltaN (euclNorm 2) (aprt s) m < deltaN (euclNorm 2) (aprt s) n := by
  have hd1 := deltaN_sub_le (aprt s) astar m
  have hd2 := deltaN_sub_le astar (aprt s) n
  rw [eucl_aprt s hs0, hm] at hd1
  rw [eucl_aprt' s hs0, hn] at hd2
  have hexp : 29 * ((|(m : ℝ)| + |(n : ℝ)|) * s) = 29 * (|(m : ℝ)| * s) + 29 * (|(n : ℝ)| * s) := by
    ring
  rw [hexp] at hgap
  obtain ⟨U, hUdef⟩ : ∃ U, |(m : ℝ)| * s = U := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, |(n : ℝ)| * s = V := ⟨_, rfl⟩
  rw [hUdef] at hd1 hgap
  rw [hVdef] at hd2 hgap
  linarith [hd1, hd2, hgap]

/-- Bundles `transport` + `gap_ok` for the perturbed witness: a defect comparison transports from
`α*` once `s` is small. -/
theorem Hpair (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 1276 * s * Real.sqrt 317 < 1)
    (m n : ℤ) (Km Kn : ℝ) (hm : deltaN (euclNorm 2) astar m = Real.sqrt Km / 29)
    (hn : deltaN (euclNorm 2) astar n = Real.sqrt Kn / 29) (hc : |(m : ℝ)| + |(n : ℝ)| ≤ 22)
    (hKa : 0 ≤ Km) (hK : Km + 1 ≤ Kn) (hKb : Kn ≤ 317) :
    deltaN (euclNorm 2) (aprt s) m < deltaN (euclNorm 2) (aprt s) n :=
  transport s hs0 m n Km Kn hm hn
    (gap_ok (|(m : ℝ)| + |(n : ℝ)|) Km Kn s hs0 hc hKa hK hKb hsmall)

theorem H1_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 1276 * s * Real.sqrt 317 < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 6,
      deltaN (euclNorm 2) (aprt s) 7 < deltaN (euclNorm 2) (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 7 1 68 73 dstar7 dstar1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 7 2 68 205 dstar7 dstar2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 7 3 68 106 dstar7 dstar3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 7 4 68 153 dstar7 dstar4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 7 5 68 317 dstar7 dstar5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 7 6 68 221 dstar7 dstar6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

theorem H2_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 1276 * s * Real.sqrt 317 < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 7,
      deltaN (euclNorm 2) (aprt s) 8 < deltaN (euclNorm 2) (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 8 1 61 73 dstar8 dstar1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 8 2 61 205 dstar8 dstar2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 8 3 61 106 dstar8 dstar3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 8 4 61 153 dstar8 dstar4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 8 5 61 317 dstar8 dstar5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 8 6 61 221 dstar8 dstar6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 8 7 61 68 dstar8 dstar7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

theorem H3_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 1276 * s * Real.sqrt 317 < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 8,
      deltaN (euclNorm 2) (aprt s) 10 < deltaN (euclNorm 2) (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 10 1 50 73 dstar10 dstar1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 10 2 50 205 dstar10 dstar2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 10 3 50 106 dstar10 dstar3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 10 4 50 153 dstar10 dstar4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 10 5 50 317 dstar10 dstar5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 10 6 50 221 dstar10 dstar6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 10 7 50 68 dstar10 dstar7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 10 8 50 61 dstar10 dstar8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

theorem H4_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 1276 * s * Real.sqrt 317 < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 10,
      deltaN (euclNorm 2) (aprt s) 11 < deltaN (euclNorm 2) (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 11 1 17 73 dstar11 dstar1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 11 2 17 205 dstar11 dstar2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 11 3 17 106 dstar11 dstar3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 11 4 17 153 dstar11 dstar4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 11 5 17 317 dstar11 dstar5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 11 6 17 221 dstar11 dstar6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 11 7 17 68 dstar11 dstar7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 11 8 17 61 dstar11 dstar8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 11 9 17 200 dstar11 dstar9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact Hpair s hs0 hsmall 11 10 17 50 dstar11 dstar10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

/-- **Arithmetic sharpness of `g₂ ≤ 5` (R5 / final).** There is a Kronecker vector `α` with an
irrational coordinate and an `N ≥ 2` for which the orbit `{0, α, …, Nα}` on `𝕋²` realizes **exactly
five** distinct Euclidean nearest-neighbour distances — so the bound `nnDistE_count_le_five` is
sharp.
The witness is `α = (3/29 + s, 8/29)` for a small irrational `s`: `card ≥ 5` transports from the
rational `α*` (Lipschitz), `card ≤ 5` is the five-distance theorem itself. -/
theorem sharp_attained : ∃ α : Fin 2 → ℝ, (∃ k, Irrational (α k)) ∧
    ∃ N, 2 ≤ N ∧ ((Finset.range (N + 1)).image (nnDistE α N)).card = 5 := by
  obtain ⟨s, hs_irr, hs_pos, hs_lt⟩ :=
    exists_irrational_btwn (show (0 : ℝ) < 1 / (1276 * Real.sqrt 317) by positivity)
  have hsmall : 1276 * s * Real.sqrt 317 < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hs_lt; nlinarith [hs_lt]
  refine ⟨aprt s, ⟨0, aprt_irrational hs_irr⟩, 11, by norm_num, le_antisymm ?_ ?_⟩
  · exact nnDistE_count_le_five (aprt s) (k₀ := 0) (aprt_irrational hs_irr) (by norm_num)
  · exact card_ge_five (aprt s) (H1_aprt s hs_pos.le hsmall) (H2_aprt s hs_pos.le hsmall)
      (H3_aprt s hs_pos.le hsmall) (H4_aprt s hs_pos.le hsmall)

end ThreeGap.EuclideanRecords
