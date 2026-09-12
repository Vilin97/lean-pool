/-
Copyright (c) 2026 Juan Pablo Traverso Giannini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Giannini, Aristotle
-/
import LeanPool.MinimumDegreeMatching.BKLOSelection
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# BKLO Lemma 10.7 for matchings

This file proves the `r = 2` specialization of the simultaneous factor-selection step in
Lemma 10.7 of Barber--Kühn--Lo--Osthus, *Edge-decompositions of graphs with high minimum degree*,
Adv. Math. 288 (2016), 337--385.

In the configuration used here, each `x ∈ U` indexes the induced graph on its neighbourhood in
`W`. Under the parity, minimum-degree, codegree, and incidence hypotheses below, these graphs admit
perfect matchings whose edge sets are pairwise disjoint. The published argument uses a randomized
greedy process. The formal proof instead uses the deterministic pessimistic-estimator sweep in
`BKLOSelection`.
-/

open Finset

namespace BKLOK2

/-! ### A largeness threshold -/

/-- For any `a > 0` and `k ≥ 1`, the exponential `exp (a (n / k - 1))` eventually dominates
`n²`. -/
theorem exists_threshold_sq_le_exp {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 0 < k) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ((n : ℝ)) ^ 2 ≤ Real.exp (a * ((n : ℝ) / (k : ℝ) - 1)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set b : ℝ := a / (3 * k) with hb
  have hbpos : 0 < b := by positivity
  have hbk : 3 * (b * (k : ℝ)) = a := by rw [hb]; field_simp
  refine ⟨⌈Real.exp a / b ^ 3⌉₊ + 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnge : Real.exp a / b ^ 3 ≤ (n : ℝ) := by
    have h1 : Real.exp a / b ^ 3 ≤ (⌈Real.exp a / b ^ 3⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp a / b ^ 3⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (Nat.le_succ _) hn
    linarith
  have hbn : Real.exp a ≤ b ^ 3 * n := by
    rw [div_le_iff₀ (by positivity)] at hnge
    linarith
  have hcube : (b * n) ^ 3 ≤ Real.exp (a * (n : ℝ) / k) := by
    have h1 : b * n ≤ Real.exp (b * n) := by
      have := Real.add_one_le_exp (b * (n : ℝ)); linarith
    have h2 : (b * n) ^ 3 ≤ (Real.exp (b * (n : ℝ))) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    have h3 : (Real.exp (b * (n : ℝ))) ^ 3 = Real.exp (a * (n : ℝ) / k) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
      push_cast
      nlinarith only [hbk]
    linarith only [h3 ▸ h2]
  have hexp : Real.exp (a * ((n : ℝ) / k - 1)) = Real.exp (a * (n : ℝ) / k) / Real.exp a := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hexp, le_div_iff₀ (Real.exp_pos a)]
  have h4 : (n : ℝ) ^ 2 * Real.exp a ≤ (n : ℝ) ^ 2 * (b ^ 3 * n) :=
    mul_le_mul_of_nonneg_left hbn (by positivity)
  have heq : (n : ℝ) ^ 2 * (b ^ 3 * n) = (b * n) ^ 3 := by ring
  linarith [hcube]

/-! ### Parameter bookkeeping -/

/-- With `q = 2√ρ/(9k)`, the codegree hypothesis fits the spread-selection budget. -/
theorem codeg_budget_of_hyps {V : Type} [DecidableEq V] {ρ t q : ℝ} {k s₂ : ℕ}
    {H : Finset (Sym2 V)} {U W : Finset V}
    (hkR : (0 : ℝ) < k) (hqpos : 0 < q)
    (hst : Real.sqrt ρ * t = ρ ^ 2) (hq : q = 2 * Real.sqrt ρ / (9 * k))
    (hs₂ : s₂ = ⌊9 * (k : ℝ) * t * (W.card : ℝ)⌋₊)
    (hiii : ∀ x ∈ U, ∀ x' ∈ U, x ≠ x' →
      (codegTo H x x' W : ℝ) ≤ 2 * ρ ^ 2 * (W.card : ℝ)) :
    ∀ x ∈ U, ∀ x' ∈ U, x ≠ x' → (codegTo H x x' W : ℝ) ≤ q * ((s₂ : ℝ) + 1) := by
  intro x hx x' hx' hne
  have h1 : 9 * (k : ℝ) * t * (W.card : ℝ) < (s₂ : ℝ) + 1 := by
    rw [hs₂]
    exact Nat.lt_floor_add_one _
  have h2 : q * (9 * (k : ℝ) * t * (W.card : ℝ)) = 2 * ρ ^ 2 * (W.card : ℝ) := by
    rw [hq]
    field_simp
    nlinarith only [hst]
  have h3 := hiii x hx x' hx' hne
  have h4 : q * (9 * (k : ℝ) * t * (W.card : ℝ)) ≤ q * ((s₂ : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left h1.le hqpos.le
  linarith

/-- The empty-state pessimistic potential is smaller than the available matching supply. -/
theorem pot_empty_lt_of_hyps {V : Type} [DecidableEq V] {ρ t q : ℝ} {k s : ℕ}
    {H : Finset (Sym2 V)} {S U W : Finset V}
    (hkR : (0 : ℝ) < k) (hk1 : (1 : ℝ) ≤ (k : ℝ))
    (hqpos : 0 < q) (htpos : 0 < t)
    (hts : t = ρ * Real.sqrt ρ) (hq : q = 2 * Real.sqrt ρ / (9 * k))
    (hs : s = ⌊9 * (k : ℝ) * t * (W.card : ℝ)⌋₊)
    (hUS : U ⊆ S) (hWS : W ⊆ S)
    (hiv : ∀ y ∈ W, (degTo H y U : ℝ) ≤ 2 * (k : ℝ) * ρ * (W.card : ℝ))
    (hSsq : ((S.card : ℝ)) ^ 2 ≤ Real.exp (t * (W.card : ℝ))) :
    pot H W q ∅ U < 2 ^ (s + 1) := by
  have hWnn : (0 : ℝ) ≤ (W.card : ℝ) := by positivity
  have hTW : 0 ≤ t * (W.card : ℝ) := by positivity
  set E : ℝ := Real.exp (4 * (t * (W.card : ℝ)) / 9) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hterm : ∀ x ∈ U, ∀ y ∈ nbhdIn H x W,
      (2 : ℝ) ^ usedCnt H W ∅ x y * (1 + q) ^ degTo H y U ≤ E := by
    intro x hx y hy
    have h0 : usedCnt H W ∅ x y = 0 := by simp [usedCnt, edgesIn, edeg]
    rw [h0, pow_zero, one_mul]
    have hle : 1 + q ≤ Real.exp q := by linarith only [Real.add_one_le_exp q]
    have h1 : (1 + q) ^ degTo H y U ≤ (Real.exp q) ^ degTo H y U :=
      pow_le_pow_left₀ (by linarith) hle _
    have h2 : (Real.exp q) ^ degTo H y U = Real.exp (q * (degTo H y U : ℝ)) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    have h3 : q * (degTo H y U : ℝ) ≤ 4 * (t * (W.card : ℝ)) / 9 := by
      have hyW : y ∈ W := nbhdIn_subset H x W hy
      have hd := hiv y hyW
      have hqe : q * (2 * (k : ℝ) * ρ * (W.card : ℝ)) = 4 * (t * (W.card : ℝ)) / 9 := by
        rw [hq, hts]
        field_simp
        ring
      nlinarith [hqpos]
    calc
      (1 + q) ^ degTo H y U ≤ Real.exp (q * (degTo H y U : ℝ)) := by rw [← h2]; exact h1
      _ ≤ E := by rw [hE]; exact Real.exp_le_exp.2 h3
  have hbound : pot H W q ∅ U ≤ ((S.card : ℝ)) ^ 2 * E := by
    have hinner : ∀ x ∈ U,
        ∑ y ∈ nbhdIn H x W, (2 : ℝ) ^ usedCnt H W ∅ x y * (1 + q) ^ degTo H y U
          ≤ (S.card : ℝ) * E := by
      intro x hx
      have h1 : ∑ y ∈ nbhdIn H x W,
          (2 : ℝ) ^ usedCnt H W ∅ x y * (1 + q) ^ degTo H y U ≤
          ∑ _y ∈ nbhdIn H x W, E := Finset.sum_le_sum (fun y hy => hterm x hx y hy)
      have h2 : ∑ _y ∈ nbhdIn H x W, E = (nbhdIn H x W).card * E := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have h3 : ((nbhdIn H x W).card : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_le_card ((nbhdIn_subset H x W).trans hWS)
      nlinarith [hEpos]
    have h6 : (U.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hUS
    calc
      pot H W q ∅ U ≤ ∑ _x ∈ U, (S.card : ℝ) * E := Finset.sum_le_sum hinner
      _ = (U.card : ℝ) * ((S.card : ℝ) * E) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (S.card : ℝ) * ((S.card : ℝ) * E) := mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = ((S.card : ℝ)) ^ 2 * E := by ring
  have hlog : (0.6931 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hfloor : 9 * (k : ℝ) * t * (W.card : ℝ) < (s : ℝ) + 1 := by
    rw [hs]
    exact_mod_cast Nat.lt_floor_add_one (9 * (k : ℝ) * t * (W.card : ℝ))
  have h2s : (2 : ℝ) ^ (s + 1) = Real.exp (((s : ℝ) + 1) * Real.log 2) := by
    rw [show ((s : ℝ) + 1) = ((s + 1 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hkey : 1.5 * (t * (W.card : ℝ)) < ((s : ℝ) + 1) * Real.log 2 := by
    have hA : 9 * (k : ℝ) * t * (W.card : ℝ) * Real.log 2 <
        ((s : ℝ) + 1) * Real.log 2 := mul_lt_mul_of_pos_right hfloor (by linarith)
    have hkl : (1.5 : ℝ) ≤ 9 * (k : ℝ) * Real.log 2 := by nlinarith only [hlog, hk1]
    have hB : 1.5 * (t * (W.card : ℝ)) ≤
        (9 * (k : ℝ) * Real.log 2) * (t * (W.card : ℝ)) :=
      mul_le_mul_of_nonneg_right hkl hTW
    have hC2 : (9 * (k : ℝ) * Real.log 2) * (t * (W.card : ℝ)) =
        9 * (k : ℝ) * t * (W.card : ℝ) * Real.log 2 := by ring
    linarith
  have hfin : ((S.card : ℝ)) ^ 2 * E < 2 ^ (s + 1) := by
    have hE' : E ≤ Real.exp (0.5 * (t * (W.card : ℝ))) := by
      rw [hE]
      exact Real.exp_le_exp.2 (by nlinarith only [hTW])
    have hA : ((S.card : ℝ)) ^ 2 * E ≤
        Real.exp (t * (W.card : ℝ)) * Real.exp (0.5 * (t * (W.card : ℝ))) :=
      mul_le_mul hSsq hE' hEpos.le (Real.exp_pos _).le
    have hB : Real.exp (t * (W.card : ℝ)) * Real.exp (0.5 * (t * (W.card : ℝ))) =
        Real.exp (1.5 * (t * (W.card : ℝ))) := by rw [← Real.exp_add]; ring_nf
    rw [h2s]
    calc
      ((S.card : ℝ)) ^ 2 * E ≤ Real.exp (1.5 * (t * (W.card : ℝ))) := by rw [← hB]; exact hA
      _ < Real.exp (((s : ℝ) + 1) * Real.log 2) := Real.exp_lt_exp.2 hkey
  linarith

/-! ### The `r = 2` simultaneous factor theorem -/

/-- **BKLO Lemma 10.7, specialized to `r = 2` and indexed by apex neighbourhoods.**

For all sufficiently large configurations, the neighbourhood graph associated with each apex
`x ∈ U` has a perfect matching, and all the chosen matching edge sets are pairwise disjoint.
The four substantive assumptions are parity, a Dirac condition with quantitative slack, a pairwise
codegree bound, and a vertex-incidence bound. -/
theorem lemma107K2_holds :
    ∀ (ρ : ℝ) (k : ℕ), 0 < ρ → ρ < 1 → 0 < k → ∃ n₀ : ℕ,
      ∀ {V : Type} [DecidableEq V] (H : Finset (Sym2 V)) (S U W : Finset V),
        n₀ ≤ S.card → (∀ e ∈ H, ¬ e.IsDiag) → H ⊆ cliqueEdges S → U ⊆ S → W ⊆ S →
        Disjoint U W → (S.card : ℝ) / (k : ℝ) - 1 ≤ (W.card : ℝ) →
        (∀ x ∈ U, 2 ∣ degTo H x W) →
        (∀ x ∈ U, ∀ y ∈ nbhdIn H x W,
          (1 / 2 : ℝ) * (degTo H x W : ℝ) +
              18 * (k : ℝ) * Real.sqrt ρ ^ 3 * (W.card : ℝ) ≤
            (degTo H y (nbhdIn H x W) : ℝ)) →
        (∀ x ∈ U, ∀ x' ∈ U, x ≠ x' →
          (codegTo H x x' W : ℝ) ≤ 2 * ρ ^ 2 * (W.card : ℝ)) →
        (∀ y ∈ W, (degTo H y U : ℝ) ≤ 2 * (k : ℝ) * ρ * (W.card : ℝ)) →
        ∃ Mx : V → Finset (Finset V),
          (∀ x ∈ U, GoodMatching H W x (Mx x)) ∧
          (U : Set V).Pairwise (fun x y => Disjoint (famEdges (Mx x)) (famEdges (Mx y))) := by
  intro ρ k hρ hρ1 hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsq : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  set t : ℝ := Real.sqrt ρ ^ 3 with ht
  have htpos : 0 < t := by positivity
  have hts : t = ρ * Real.sqrt ρ := by
    rw [ht, pow_succ, pow_two, Real.mul_self_sqrt hρ.le]
  have hst : Real.sqrt ρ * t = ρ ^ 2 := by
    rw [hts]
    nlinarith only [Real.mul_self_sqrt hρ.le]
  obtain ⟨n₀, hn₀⟩ := exists_threshold_sq_le_exp (a := t) htpos hk
  refine ⟨n₀, ?_⟩
  intro V _ H S U W hS hloop hHS hUS hWS hUW hWcard hdvd hii hiii hiv
  classical
  set q : ℝ := 2 * Real.sqrt ρ / (9 * k) with hq
  have hqpos : 0 < q := by positivity
  set s : ℕ := ⌊9 * (k : ℝ) * t * (W.card : ℝ)⌋₊ with hs
  have hEven : ∀ x ∈ U, Even (nbhdIn H x W).card :=
    fun x hx => (even_iff_two_dvd).2 (hdvd x hx)
  have hmindeg : ∀ x ∈ U, ∀ v ∈ nbhdIn H x W,
      (nbhdIn H x W).card / 2 + s + s ≤ edeg (edgesIn H (nbhdIn H x W)) v := by
    intro x hx v hvN
    have h1 := hii x hx v hvN
    have h2 : degTo H v (nbhdIn H x W) ≤ edeg (edgesIn H (nbhdIn H x W)) v :=
      degTo_le_edeg_edgesIn hvN
    have h3 : (((nbhdIn H x W).card / 2 : ℕ) : ℝ) ≤
        ((nbhdIn H x W).card : ℝ) / 2 := Nat.cast_div_le
    have h4 : (s : ℝ) ≤ 9 * (k : ℝ) * t * (W.card : ℝ) := by
      rw [hs]
      exact Nat.floor_le (by positivity)
    have h5 : (((nbhdIn H x W).card / 2 + s + s : ℕ) : ℝ) ≤
        (edeg (edgesIn H (nbhdIn H x W)) v : ℝ) := by
      push_cast
      have h6 : (degTo H v (nbhdIn H x W) : ℝ) ≤
          (edeg (edgesIn H (nbhdIn H x W)) v : ℝ) := by exact_mod_cast h2
      rw [degTo] at h1
      linarith
    exact_mod_cast h5
  have hcodeg := codeg_budget_of_hyps (U := U) (W := W) hkR hqpos hst hq hs hiii
  have hSsq : ((S.card : ℝ)) ^ 2 ≤ Real.exp (t * (W.card : ℝ)) := by
    refine (hn₀ S.card hS).trans (Real.exp_le_exp.2 ?_)
    nlinarith only [htpos, hWcard]
  have hpot : pot H W q ∅ U < 2 ^ (s + 1) :=
    pot_empty_lt_of_hyps hkR hk1 hqpos htpos hts hq hs hUS hWS hiv hSsq
  exact exists_matchings_of_spread hqpos.le hloop hUW hEven hmindeg hcodeg hpot

end BKLOK2
