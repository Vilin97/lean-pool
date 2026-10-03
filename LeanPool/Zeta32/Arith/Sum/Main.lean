/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import LeanPool.Zeta32.Arith.Sum.Windows
public import LeanPool.Zeta32.Arith.Sum.Numerics

/-! `arith_sum`: the prime sum behind the arithmetic constant (the proof notes, §8,
the proof notes, §8.5, finite-piece route).

The primes `p ≤ 5n` are split as
* `p ≤ n/20`: `p ≤ n^{2/3}` by the crude bound `h0` (total `o(n²)`), `n^{2/3} < p ≤ n/20` by
`h1` and
  `psiL x ≤ tailConst` on `x ≤ 1/20`, total `tailConst · n · θ(n/20)`;
* `n/20 < p ≤ 7n/3`: `h1`, and on each of the 196 pieces `n psiL(p/n) = a n + b p − (25/4) n²/p`;
* `7n/3 < p ≤ 5n`: `h2`, four linear pieces of `phiL`;
* the additive constants `3/4` and `5` cost at most `(13/2) θ(5n) = O(n)`.
The normalised main part tends to `tailConst/20 + midRat + 35/36 − (25/4) log(140/3) < 283/50`. -/

public section

open Finset Filter Topology

namespace Zeta32.ArithSum
noncomputable section
open PrimeSums

/-! ### Real piece data -/

/-- Real breakpoint for the relaxed arithmetic profile. -/
def tR (i : ℕ) : ℝ := (ub i : ℝ)
/-- Real breakpoint for the outer-prime profile. -/
def tO (i : ℕ) : ℝ := (vb i : ℝ)

lemma tR_pos (i : ℕ) : 0 < tR i := by unfold tR; exact_mod_cast ub_pos i
lemma tR_lt (i : ℕ) : tR i < tR (i + 1) := by unfold tR; exact_mod_cast ub_lt_succ i
lemma tR_zero : tR 0 = 3 / 7 := by rw [tR, ub_zero]; push_cast; ring
lemma tR_196 : tR 196 = 20 := by rw [tR, ub_196]; push_cast; ring
lemma tO_zero : tO 0 = 1 / 5 := by simp only [tO, vb]; push_cast; ring
lemma tO_four : tO 4 = 3 / 7 := by simp only [tO, vb]; push_cast; ring
lemma tO_pos (i : ℕ) : 0 < tO i := by
  unfold tO vb; split <;> norm_num
lemma tO_lt (i : ℕ) (hi : i < 4) : tO i < tO (i + 1) := by
  unfold tO; exact_mod_cast vb_lt_succ i hi

lemma floor_bounds {n k : ℕ} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hk : k ∈ Ioc ⌊(n : ℝ) / t⌋₊ ⌊(n : ℝ) / s⌋₊) :
    0 < k ∧ s ≤ (n : ℝ) / k ∧ (n : ℝ) / k < t := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hk
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  refine ⟨hk0, ?_, ?_⟩
  · have h := (Nat.le_floor_iff (by positivity)).mp h2
    rw [le_div_iff₀ hs] at h
    rw [le_div_iff₀ hkR]
    linarith
  · have h := (Nat.floor_lt (by positivity)).mp h1
    rw [div_lt_iff₀ ht] at h
    rw [div_lt_iff₀ hkR]
    linarith

/-! ### The three limits -/

theorem relaxed_tendsto :
    Tendsto (fun n : ℕ => (∑ k ∈ Ioc ⌊(n : ℝ) / 20⌋₊ ⌊(n : ℝ) / (3 / 7)⌋₊,
        (n : ℝ) * psiL ((k : ℝ) / (n : ℝ)) * cPrime k) / (n : ℝ) ^ 2) atTop
      (𝓝 ((midRat : ℝ) - 25 / 4 * Real.log (140 / 3))) := by
  have h := window_tendsto (fun n k => (n : ℝ) * psiL ((k : ℝ) / (n : ℝ))) tR (fun i => (pa i : ℝ))
    (fun i => (pb i : ℝ)) (fun _ => -25 / 4) 196 (tR_pos 0) (fun i _ => tR_lt i) ?_
  · have hv : ∑ i ∈ Finset.range 196,
        pieceLim (pa i : ℝ) (pb i : ℝ) (-25 / 4) (tR i) (tR (i + 1)) =
        (midRat : ℝ) - 25 / 4 * Real.log (140 / 3) := by
      have e1 : ∀ i, pieceLim (pa i : ℝ) (pb i : ℝ) (-25 / 4) (tR i) (tR (i + 1)) =
          ((pieceRat i : ℚ) : ℝ) + (-25 / 4) * (Real.log (tR (i + 1)) - Real.log (tR i)) := by
        intro i
        unfold pieceLim
        rw [Real.log_div (tR_pos (i + 1)).ne' (tR_pos i).ne']
        unfold pieceRat tR
        push_cast
        ring
      rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_range_sub (fun i => Real.log (tR i)), ← Rat.cast_sum, sum_pieceRat, tR_196,
        tR_zero, show Real.log 20 - Real.log (3 / 7) = Real.log (140 / 3) by
          rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num]
      ring
    rw [hv, tR_196, tR_zero] at h
    exact h
  · intro n hn i _ k hk
    obtain ⟨hk0, h1, h2⟩ := floor_bounds (tR_pos i) (tR_pos (i + 1)) hk
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hx : (0 : ℝ) < (k : ℝ) / n := div_pos hkR hn'
    have e : 1 / ((k : ℝ) / n) = n / k := by field_simp
    have hp := psiL_piece i hx (by rw [e]; exact h1) (by rw [e]; exact h2)
    rw [hp]
    congr 1
    field_simp
    ring

theorem outer_tendsto :
    Tendsto (fun n : ℕ => (∑ k ∈ Ioc ⌊(n : ℝ) / (3 / 7)⌋₊ ⌊(n : ℝ) / (1 / 5)⌋₊,
        (n : ℝ) * phiL ((k : ℝ) / (n : ℝ)) * cPrime k) / (n : ℝ) ^ 2) atTop (𝓝 (35 / 36)) := by
  have h := window_tendsto (fun n k => (n : ℝ) * phiL ((k : ℝ) / (n : ℝ))) tO (fun i => (vc i : ℝ))
    (fun i => (vd i : ℝ)) (fun _ => 0) 4 (by rw [tO_zero]; norm_num) (fun i hi => tO_lt i hi) ?_
  · have hv : ∑ i ∈ Finset.range 4, pieceLim (vc i : ℝ) (vd i : ℝ) 0 (tO i) (tO (i + 1)) = 35 /
    36 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pieceLim, tO, vb, vc, vd]
      push_cast
      norm_num
    rw [hv, tO_four, tO_zero] at h
    exact h
  · intro n hn i hi k hk
    obtain ⟨hk0, h1, h2⟩ := floor_bounds (tO_pos i) (tO_pos (i + 1)) hk
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hx : (0 : ℝ) < (k : ℝ) / n := div_pos hkR hn'
    have e : 1 / ((k : ℝ) / n) = n / k := by field_simp
    have hp := phiL_piece i hi hx (by rw [e]; exact h1) (by rw [e]; exact h2)
    rw [hp]
    congr 1
    field_simp
    ring

theorem tail_tendsto :
    Tendsto (fun n : ℕ => (tailConst : ℝ) * n * Chebyshev.theta ((n : ℝ) / 20) / (n : ℝ) ^ 2) atTop
      (𝓝 ((tailConst : ℝ) / 20)) := by
  have h := ((theta_scaled_tendsto (c := 1 / 20) (by norm_num)).comp
    tendsto_natCast_atTop_atTop).const_mul (tailConst : ℝ)
  rw [show (tailConst : ℝ) * (1 / 20) = tailConst / 20 by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp]
  rw [show (1 / 20 * (n : ℝ)) = n / 20 by ring]
  field_simp

/-! ### Elementary bounds -/

lemma cPrime_log_eq {k : ℕ} (hk : k.Prime) : cPrime k = Real.log k := by simp [cPrime, hk]
lemma cPrime_zero_of {k : ℕ} (hk : ¬ k.Prime) : cPrime k = 0 := by simp [cPrime, hk]

-- adapted from mo271/Zeta5@f19a196:Apery/Growth/Assembly1.lean (`log_mul_natLog_le`)
lemma natLog_mul_log_le {k Z : ℕ} (hk : 2 ≤ k) (hZ : 1 ≤ Z) :
    (Nat.log k Z : ℝ) * Real.log k ≤ Real.log Z := by
  have h := Nat.pow_log_le_self k (show Z ≠ 0 by omega)
  have h' : ((k ^ Nat.log k Z : ℕ) : ℝ) ≤ (Z : ℝ) := by exact_mod_cast h
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [← Real.log_pow]
  push_cast at h'
  exact Real.log_le_log (pow_pos hk0 _) h'

lemma padicValNat_mul_log_le {k d : ℕ} (hk : k.Prime) (hd : 0 < d) :
    (padicValNat k d : ℝ) * Real.log k ≤ Real.log d := by
  have := Fact.mk hk
  have hdvd : k ^ padicValNat k d ∣ d := pow_padicValNat_dvd
  have hle := Nat.le_of_dvd hd hdvd
  have h' : ((k ^ padicValNat k d : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hle
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.pos
  rw [← Real.log_pow]
  push_cast at h'
  exact Real.log_le_log (pow_pos hk0 _) h'

lemma sum_ite_le (M : ℕ) {y B : ℝ} (hy : 0 ≤ y) (hB : 0 ≤ B) :
    ∑ k ∈ Ioc 0 M, (if (k : ℝ) ≤ y then B else 0) ≤ y * B := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hB
  have hsub : (Ioc 0 M).filter (fun k : ℕ => (k : ℝ) ≤ y) ⊆ Icc 1 ⌊y⌋₊ := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1.1, Nat.le_floor hk.2⟩
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
  calc (((Ioc 0 M).filter fun k : ℕ => (k : ℝ) ≤ y).card : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ y := Nat.floor_le hy

lemma sum_filter_prime_eq (F : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, F p * Real.log p =
      ∑ k ∈ Ioc 0 N, F k * cPrime k := by
  have hs : (Finset.range (N + 1)).filter Nat.Prime = (Ioc 0 N).filter Nat.Prime := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨by omega, h3⟩
  rw [hs, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k.Prime
  · simp only [hk, ↓reduceIte, cPrime_log_eq hk]
  · simp only [hk, ↓reduceIte, cPrime_zero_of hk, mul_zero]

lemma sum_cPrime_le {a b c : ℕ} (hbc : b ≤ c) :
    ∑ k ∈ Ioc a b, cPrime k ≤ ∑ k ∈ Ioc 0 c, cPrime k :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc (Nat.zero_le a) hbc)
    (fun k _ _ => cPrime_nonneg k)

/-- `n^{2/3} ≤ n/20` and the crude small-prime total is `≤ δ n²`, eventually. -/
lemma rpow_facts (δ C : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (2 / 3 : ℝ) ≤ n / 20 ∧
      (n : ℝ) ^ (2 / 3 : ℝ) * (9 * n * Real.log (10 * n + 2) + 3 * n * C) ≤ δ * (n : ℝ) ^ 2 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hη : (0 : ℝ) < δ / 54 := by positivity
  have hlog := ht.eventually (Real.isLittleO_log_id_atTop.bound hη)
  have hT := ht.eventually (eventually_ge_atTop (max 20 (2 * (9 * Real.log 12 + 3 * C) / δ)))
  filter_upwards [hlog, hT, eventually_ge_atTop 1] with n hl hTn hn1
  simp only [id, Real.norm_eq_abs] at hl hTn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set t := (n : ℝ) ^ (1 / 3 : ℝ) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hn0 _
  have ht2 : (n : ℝ) ^ (2 / 3 : ℝ) = t ^ 2 := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have ht3 : (n : ℝ) = t ^ 3 := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hlogn : Real.log n = 3 * Real.log t := by
    rw [htdef, Real.log_rpow hn0]; ring
  have hl' : Real.log t ≤ δ / 54 * t := by
    rw [abs_of_pos ht0] at hl
    exact (le_abs_self _).trans hl
  have hT20 : 20 ≤ t := le_trans (le_max_left _ _) hTn
  have hT2 : 2 * (9 * Real.log 12 + 3 * C) / δ ≤ t := le_trans (le_max_right _ _) hTn
  have hT2' : 2 * (9 * Real.log 12 + 3 * C) ≤ t * δ := (div_le_iff₀ hδ).mp hT2
  have h10 : Real.log (10 * n + 2) ≤ Real.log 12 + Real.log n := by
    rw [← Real.log_mul (by norm_num) hn0.ne']
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    exact Real.log_le_log (by positivity) (by linarith)
  have hkey : 9 * Real.log (10 * n + 2) + 3 * C ≤ δ * t := by
    nlinarith [hlogn, h10, hl', hT2']
  constructor
  · rw [ht2]
    have h := mul_le_mul_of_nonneg_right hT20 (sq_nonneg t)
    have : (n : ℝ) / 20 = t ^ 3 / 20 := by rw [← ht3]
    rw [this]
    nlinarith
  · rw [ht2]
    have hA : 0 ≤ t ^ 2 * (n : ℝ) := by positivity
    calc t ^ 2 * (9 * n * Real.log (10 * n + 2) + 3 * n * C)
        = t ^ 2 * n * (9 * Real.log (10 * n + 2) + 3 * C) := by ring
      _ ≤ t ^ 2 * n * (δ * t) := mul_le_mul_of_nonneg_left hkey hA
      _ = δ * n * t ^ 3 := by ring
      _ = δ * (n : ℝ) ^ 2 := by rw [← ht3]; ring

/-! ### The three ranges at a fixed `n` -/

lemma tail_range_bound (cost : ℕ → ℕ → ℝ) (den : ℕ) (hden : 0 < den) (n : ℕ)
    (h0 : ∀ p : ℕ, p.Prime → cost n p ≤ 9*n*Nat.log p (10*n+2) + 3*n*padicValNat p den)
    (hh1 : ∀ p : ℕ, p.Prime → (n:ℝ)^(2/3:ℝ) < p → 3*p ≤ 7*n →
      cost n p ≤ n * psiL ((p:ℝ)/(n:ℝ)) + 3/4) :
    ∑ k ∈ Ioc 0 ⌊(n : ℝ) / 20⌋₊, cost n k * cPrime k ≤
      ((n : ℝ) * tailConst + 3 / 4) * Chebyshev.theta ((n : ℝ) / 20) +
        (n : ℝ) ^ (2 / 3 : ℝ) * (9 * n * Real.log (10 * n + 2) + 3 * n * Real.log den) := by
  set B : ℝ := 9 * n * Real.log (10 * n + 2) + 3 * n * Real.log den with hB
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hB0 : 0 ≤ B := by
    have h1 : 0 ≤ Real.log (10 * (n : ℝ) + 2) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log (den : ℝ) := Real.log_nonneg (by exact_mod_cast hden)
    positivity
  have htc : (0 : ℝ) ≤ tailConst := by norm_num [tailConst]
  have hA0 : 0 ≤ (n : ℝ) * tailConst + 3 / 4 := by positivity
  have hterm : ∀ k ∈ Ioc 0 ⌊(n : ℝ) / 20⌋₊, cost n k * cPrime k ≤
      ((n : ℝ) * tailConst + 3 / 4) * cPrime k + (if (k : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) then B else
        0) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.mp hk
    have hkn : (k : ℝ) ≤ (n : ℝ) / 20 := (Nat.le_floor_iff (by positivity)).mp hk2
    have hE0 : 0 ≤ (if (k : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) then B else 0) := by
      split_ifs <;> linarith
    by_cases hp : k.Prime
    · rw [cPrime_log_eq hp]
      have hlog0 : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
      by_cases hsm : (k : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ)
      · simp only [hsm, ↓reduceIte]
        have h := mul_le_mul_of_nonneg_right (h0 k hp) hlog0
        have e1 := natLog_mul_log_le hp.two_le (show 1 ≤ 10 * n + 2 by omega)
        have e2 := padicValNat_mul_log_le hp hden
        push_cast at e1
        have f1 := mul_le_mul_of_nonneg_left e1 hn0
        have f2 := mul_le_mul_of_nonneg_left e2 hn0
        have f3 := mul_nonneg hA0 hlog0
        nlinarith
      · simp only [hsm, ↓reduceIte, add_zero]
        have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
        have hnpos : (0 : ℝ) < n := by linarith
        have h3 : 3 * k ≤ 7 * n := by
          have : (3 * k : ℝ) ≤ 7 * n := by linarith
          exact_mod_cast this
        have hc1 := hh1 k hp (lt_of_not_ge hsm) h3
        have hx : (0 : ℝ) < (k : ℝ) / n := div_pos (by linarith) hnpos
        have ht := psiL_le_tail hx
        have hc : cost n k ≤ n * tailConst + 3 / 4 := by
          calc cost n k ≤ n * psiL ((k : ℝ) / n) + 3 / 4 := hc1
            _ ≤ n * (33 / 5 + 121 / 100 * ((k : ℝ) / n)) + 3 / 4 := by gcongr
            _ = 33 / 5 * n + 121 / 100 * k + 3 / 4 := by field_simp
            _ ≤ n * tailConst + 3 / 4 := by
              simp only [tailConst]; push_cast; linarith
        exact mul_le_mul_of_nonneg_right hc hlog0
    · rw [cPrime_zero_of hp, mul_zero, mul_zero, zero_add]
      exact hE0
  calc ∑ k ∈ Ioc 0 ⌊(n : ℝ) / 20⌋₊, cost n k * cPrime k
      ≤ ∑ k ∈ Ioc 0 ⌊(n : ℝ) / 20⌋₊, (((n : ℝ) * tailConst + 3 / 4) * cPrime k +
          (if (k : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) then B else 0)) := Finset.sum_le_sum hterm
    _ = ((n : ℝ) * tailConst + 3 / 4) * Chebyshev.theta ((n : ℝ) / 20) +
          ∑ k ∈ Ioc 0 ⌊(n : ℝ) / 20⌋₊, (if (k : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) then B else 0) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← theta_eq_sum_cPrime]
    _ ≤ ((n : ℝ) * tailConst + 3 / 4) * Chebyshev.theta ((n : ℝ) / 20) +
          (n : ℝ) ^ (2 / 3 : ℝ) * B := by
      gcongr
      exact sum_ite_le _ (by positivity) hB0

lemma relaxed_range_bound (cost : ℕ → ℕ → ℝ) (n : ℕ) (hpow : (n : ℝ) ^ (2 / 3 : ℝ) ≤ n / 20)
    (hh1 : ∀ p : ℕ, p.Prime → (n:ℝ)^(2/3:ℝ) < p → 3*p ≤ 7*n →
      cost n p ≤ n * psiL ((p:ℝ)/(n:ℝ)) + 3/4) :
    ∑ k ∈ Ioc ⌊(n : ℝ) / 20⌋₊ ⌊(n : ℝ) / (3 / 7)⌋₊, cost n k * cPrime k ≤
      ∑ k ∈ Ioc ⌊(n : ℝ) / 20⌋₊ ⌊(n : ℝ) / (3 / 7)⌋₊, (n : ℝ) * psiL ((k : ℝ) / (n : ℝ)) *
        cPrime k +
        3 / 4 * ∑ k ∈ Ioc ⌊(n : ℝ) / 20⌋₊ ⌊(n : ℝ) / (3 / 7)⌋₊, cPrime k := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.mp hk
  by_cases hp : k.Prime
  · have hlt : (n : ℝ) / 20 < k := (Nat.floor_lt (by positivity)).mp hk1
    have hle : (k : ℝ) ≤ n / (3 / 7) := (Nat.le_floor_iff (by positivity)).mp hk2
    rw [le_div_iff₀ (by norm_num)] at hle
    have h3 : 3 * k ≤ 7 * n := by
      have : (3 * k : ℝ) ≤ 7 * n := by linarith
      exact_mod_cast this
    have h := mul_le_mul_of_nonneg_right (hh1 k hp (by linarith) h3) (cPrime_nonneg k)
    rw [add_mul] at h
    linarith
  · simp [cPrime_zero_of hp]

lemma outer_range_bound (cost : ℕ → ℕ → ℝ) (n : ℕ)
    (hh2 : ∀ p : ℕ, p.Prime → 7*n < 3*p → p ≤ 5*n →
      cost n p ≤ n * phiL ((p:ℝ)/(n:ℝ)) + 5) :
    ∑ k ∈ Ioc ⌊(n : ℝ) / (3 / 7)⌋₊ ⌊(n : ℝ) / (1 / 5)⌋₊, cost n k * cPrime k ≤
      ∑ k ∈ Ioc ⌊(n : ℝ) / (3 / 7)⌋₊ ⌊(n : ℝ) / (1 / 5)⌋₊, (n : ℝ) * phiL ((k : ℝ) / (n : ℝ)) *
        cPrime k +
        5 * ∑ k ∈ Ioc ⌊(n : ℝ) / (3 / 7)⌋₊ ⌊(n : ℝ) / (1 / 5)⌋₊, cPrime k := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.mp hk
  by_cases hp : k.Prime
  · have hlt : (n : ℝ) / (3 / 7) < k := (Nat.floor_lt (by positivity)).mp hk1
    have hle : (k : ℝ) ≤ n / (1 / 5) := (Nat.le_floor_iff (by positivity)).mp hk2
    rw [div_lt_iff₀ (by norm_num)] at hlt
    rw [le_div_iff₀ (by norm_num)] at hle
    have h7 : 7 * n < 3 * k := by
      have : (7 * n : ℝ) < 3 * k := by linarith
      exact_mod_cast this
    have h5 : k ≤ 5 * n := by
      have : (k : ℝ) ≤ 5 * n := by linarith
      exact_mod_cast this
    have h := mul_le_mul_of_nonneg_right (hh2 k hp h7 h5) (cPrime_nonneg k)
    rw [add_mul] at h
    linarith
  · simp [cPrime_zero_of hp]

/-! ### The theorem -/

theorem arith_sum (cost : ℕ → ℕ → ℝ) (den : ℕ) (hden : 0 < den)
    (h0 : ∀ (n p : ℕ), p.Prime → cost n p ≤ 9 * n * Nat.log p (10 * n + 2) + 3 * n *
      padicValNat p den)
    (h1 : ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (p : ℕ), p.Prime → (n : ℝ) ^ (2 / 3 : ℝ) < p → 3 * p
      ≤ 7 * n →
      cost n p ≤ n * psiL ((p : ℝ) / (n : ℝ)) + 3 / 4)
    (h2 : ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (p : ℕ), p.Prime → 7 * n < 3 * p → p ≤ 5 * n →
      cost n p ≤ n * phiL ((p : ℝ) / (n : ℝ)) + 5) :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop,
      ∑ p ∈ (Finset.range (5*n+1)).filter Nat.Prime, cost n p * Real.log p ≤ (283/50 + ε) * n^2
        := by
  intro ε hε
  set L : ℝ := (tailConst : ℝ) / 20 + midRat + 35 / 36 - 25 / 4 * Real.log (140 / 3) with hLdef
  have hL : L < 283 / 50 := constant_lt
  have hM := (tail_tendsto.add relaxed_tendsto).add outer_tendsto
  have hlim : (tailConst : ℝ) / 20 + ((midRat : ℝ) - 25 / 4 * Real.log (140 / 3)) + 35 / 36 <
      L + ε / 3 := by rw [hLdef]; linarith
  have hMe := hM.eventually (eventually_le_nhds hlim)
  have hsmall := rpow_facts (ε / 3) (Real.log den) (by linarith)
  have hconst : ∀ᶠ n : ℕ in atTop, 46 * (n : ℝ) ≤ ε / 3 * (n : ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop ⌈138 / ε⌉₊] with n hn
    have e1 : 138 / ε ≤ n := Nat.ceil_le.mp hn
    have e2 : 138 ≤ n * ε := (div_le_iff₀ hε).mp e1
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  filter_upwards [h1, h2, hMe, hsmall, hconst, eventually_ge_atTop 1] with n hh1 hh2 hMn hsm hcn hn1
  obtain ⟨hpow, hE⟩ := hsm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  -- the main part, un-normalised
  have hMn' : (tailConst : ℝ) * n * Chebyshev.theta ((n : ℝ) / 20) +
      ∑ k ∈ Ioc ⌊(n : ℝ) / 20⌋₊ ⌊(n : ℝ) / (3 / 7)⌋₊, (n : ℝ) * psiL ((k : ℝ) / (n : ℝ)) *
        cPrime k +
      ∑ k ∈ Ioc ⌊(n : ℝ) / (3 / 7)⌋₊ ⌊(n : ℝ) / (1 / 5)⌋₊, (n : ℝ) * phiL ((k : ℝ) / (n : ℝ)) *
        cPrime k
        ≤ (L + ε / 3) * (n : ℝ) ^ 2 := by
    rw [← add_div, ← add_div, div_le_iff₀ hn2] at hMn
    exact hMn
  -- splitting the range
  have hc : ⌊(n : ℝ) / (1 / 5)⌋₊ = 5 * n := by
    rw [show (n : ℝ) / (1 / 5) = ((5 * n : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hab : ⌊(n : ℝ) / 20⌋₊ ≤ ⌊(n : ℝ) / (3 / 7)⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_left hn0.le (by norm_num) (by norm_num))
  have hbc : ⌊(n : ℝ) / (3 / 7)⌋₊ ≤ ⌊(n : ℝ) / (1 / 5)⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_left hn0.le (by norm_num) (by norm_num))
  rw [sum_filter_prime_eq (cost n) (5 * n), ← hc,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hbc,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hab]
  have hT := tail_range_bound cost den hden n (h0 n) hh1
  have hR := relaxed_range_bound cost n hpow hh1
  have hO := outer_range_bound cost n hh2
  -- the constants
  have hS5 : ∑ k ∈ Ioc 0 ⌊(n : ℝ) / (1 / 5)⌋₊, cPrime k ≤ 7 * n := by
    rw [hc, show (5 * n : ℕ) = ⌊((5 * n : ℕ) : ℝ)⌋₊ from (Nat.floor_natCast _).symm,
      ← theta_eq_sum_cPrime]
    have h := Chebyshev.theta_le_log4_mul_x (x := ((5 * n : ℕ) : ℝ)) (Nat.cast_nonneg _)
    have hl4 : Real.log 4 < 7 / 5 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9
      push_cast
      linarith
    push_cast at h ⊢
    nlinarith
  have hθ20 : Chebyshev.theta ((n : ℝ) / 20) ≤ ∑ k ∈ Ioc 0 ⌊(n : ℝ) / (1 / 5)⌋₊, cPrime k := by
    rw [theta_eq_sum_cPrime]
    exact sum_cPrime_le (hab.trans hbc)
  have hSR := sum_cPrime_le (a := ⌊(n : ℝ) / 20⌋₊) hbc
  have hSO := sum_cPrime_le (a := ⌊(n : ℝ) / (3 / 7)⌋₊) (le_refl ⌊(n : ℝ) / (1 / 5)⌋₊)
  have hθ0 : 0 ≤ Chebyshev.theta ((n : ℝ) / 20) := Chebyshev.theta_nonneg _
  have hLn := mul_le_mul_of_nonneg_right hL.le hn2.le
  nlinarith

end
end Zeta32.ArithSum

end
