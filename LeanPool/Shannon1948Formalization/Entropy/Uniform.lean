/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import LeanPool.Shannon1948Formalization.Entropy.Core

/-!
# Shannon.Entropy.Uniform

Phase 1 of the characterization: equiprobable distributions.

Main outputs:
- multiplicative/additive behavior on uniform choices (`Apos_mul`, `Apos_pow`);
- logarithmic characterization `Apos H n = K H * log n`;
- positivity of the scale factor `K`.
-/
namespace LeanPool.Shannon1948Formalization

noncomputable section
open Filter
open scoped Topology

/-! ## Phase 1: Equiprobable Characterization -/

lemma relabel_compose_uniform_eq_uniform_mul (n m : ℕ+) :
    relabelProb (sigmaConstFinEquivFinMul n m)
      (composeProb (uniformPNat n) (fun _ : Fin n => uniformPNat m))
    = uniformPNat (n * m) := by
  ext x
  simp [relabelProb, composeProb, uniformPNat, sigmaConstFinEquivFinMul]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt n.2
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt m.2
  field_simp [hn, hm]

lemma Apos_mul
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    (n m : ℕ+) :
    Apos H (n * m) = Apos H n + Apos H m := by
  let p : ProbDist (Fin n) := uniformPNat n
  let q : (a : Fin n) → ProbDist (Fin m) := fun _ => uniformPNat m
  have hsum : (∑ a : Fin n, p a * H (q a)) = H (uniformPNat m) := by
    change (∑ a : Fin n, p a * H (uniformPNat m)) = H (uniformPNat m)
    simp [← Finset.sum_mul, prob_sum_eq_one p]
  have hident : relabelProb (sigmaConstFinEquivFinMul n m) (composeProb p q)
      = uniformPNat (n * m) :=
    by simpa [p, q] using relabel_compose_uniform_eq_uniform_mul n m
  have hrelab' : H (uniformPNat (n * m)) = H (composeProb p q) := by
    rw [← hident]; exact hH.relabelInvariant (sigmaConstFinEquivFinMul n m) (composeProb p q)
  calc
    Apos H (n * m) = H (composeProb p q) := by simpa [Apos] using hrelab'
    _ = H p + (∑ a : Fin n, p a * H (q a)) := hH.grouping p q
    _ = H p + H (uniformPNat m) := by rw [hsum]
    _ = Apos H n + Apos H m := by simp [Apos, p]

lemma Apos_one_zero
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) :
    Apos H 1 = 0 := by
  have h11 : Apos H 1 = Apos H 1 + Apos H 1 := by simpa using Apos_mul H hH 1 1
  linarith

lemma Apos_pow
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    (n : ℕ+)
    (k : ℕ) :
    Apos H (n ^ k) = (k : ℝ) * Apos H n := by
  induction k with
  | zero => simpa using Apos_one_zero H hH
  | succ k ih =>
      have : Apos H (n ^ (k + 1)) = Apos H (n ^ k) + Apos H n := by
        simpa [pow_succ] using Apos_mul H hH (n ^ k) n
      simp only [Nat.cast_succ]
      linarith

lemma Apos_nonneg
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    (n : ℕ+) :
    0 ≤ Apos H n := by
  have hmono : Apos H 1 ≤ Apos H n := hH.uniformMonotone.monotone (Nat.succ_le_of_lt n.2)
  linarith [Apos_one_zero H hH]

lemma Apos_pos_two
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) :
    0 < Apos H 2 := by
  have h1 : Apos H 1 = 0 := Apos_one_zero H hH
  have h2 : Apos H 1 < Apos H 2 := hH.uniformMonotone (by decide)
  linarith

/-- Strict monotonicity gives positivity of `Apos` for any alphabet size `> 1`. -/
lemma Apos_pos_of_one_lt
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    {n : ℕ+}
    (hn : 1 < n) :
    0 < Apos H n := by
  have h1 : Apos H 1 = 0 := Apos_one_zero H hH
  have h2 : Apos H 1 < Apos H n := hH.uniformMonotone hn
  linarith

/-- If two reals are in the same closed interval, their distance is interval width. -/
lemma abs_sub_le_of_mem_interval
    {a b l u : ℝ}
    (haL : l ≤ a)
    (haU : a ≤ u)
    (hbL : l ≤ b)
    (hbU : b ≤ u) :
    |a - b| ≤ u - l :=
  abs_le.mpr ⟨by linarith [sub_le_sub hbU haL], sub_le_sub haU hbL⟩

/-- The canonical positive scale factor from the two-outcome uniform case. -/
def K
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ) : ℝ :=
  Apos H 2 / Real.log 2

lemma K_pos
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) :
    0 < K H :=
  div_pos (Apos_pos_two H hH) (Real.log_pos (by norm_num : (1 : ℝ) < 2))

lemma Apos_ratio_logb_close
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    {s t n : ℕ+}
    (hs : 1 < s) :
    |Apos H t / Apos H s - Real.logb (s : ℝ) (t : ℝ)| ≤ 1 / (n : ℝ) := by
  let m : ℕ := Nat.log (s : ℕ) ((t : ℕ) ^ (n : ℕ))
  have htn_ne_zero : ((t : ℕ) ^ (n : ℕ)) ≠ 0 := by
    exact pow_ne_zero _ (Nat.ne_of_gt t.2)
  have hs_nat : 1 < (s : ℕ) := hs
  have hs_real : 1 < (s : ℝ) := by exact_mod_cast hs
  have hpow_le_nat : (s : ℕ) ^ m ≤ (t : ℕ) ^ (n : ℕ) := by
    simpa [m] using Nat.pow_log_le_self (s : ℕ) htn_ne_zero
  have hpow_lt_nat : (t : ℕ) ^ (n : ℕ) < (s : ℕ) ^ (m + 1) := by
    simpa [m] using Nat.lt_pow_succ_log_self hs_nat ((t : ℕ) ^ (n : ℕ))
  have hpow_le : s ^ m ≤ t ^ (n : ℕ) := by
    exact_mod_cast hpow_le_nat
  have hpow_lt : t ^ (n : ℕ) < s ^ (m + 1) := by
    exact_mod_cast hpow_lt_nat
  have hA_le : Apos H (s ^ m) ≤ Apos H (t ^ (n : ℕ)) :=
    hH.uniformMonotone.monotone hpow_le
  have hA_lt : Apos H (t ^ (n : ℕ)) < Apos H (s ^ (m + 1)) :=
    hH.uniformMonotone hpow_lt
  have hAs_pos : 0 < Apos H s := Apos_pos_of_one_lt H hH hs
  have hAs_ne : Apos H s ≠ 0 := ne_of_gt hAs_pos
  have hn_pos : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast n.2
  have hn_ne : ((n : ℕ) : ℝ) ≠ 0 := ne_of_gt hn_pos
  let ratioA : ℝ := Apos H t / Apos H s
  let ratioL : ℝ := Real.logb (s : ℝ) (t : ℝ)
  let nR : ℝ := (n : ℕ)
  have hA_left : (m : ℝ) / nR ≤ ratioA := by
    have hmul : (m : ℝ) * Apos H s ≤ ((n : ℕ) : ℝ) * Apos H t := by
      have := Apos_pow H hH s m
      have := Apos_pow H hH t (n : ℕ)
      linarith [hA_le]
    exact (div_le_iff₀ hn_pos).2 (by
      simp only [ratioA]
      rw [div_mul_eq_mul_div, le_div_iff₀ hAs_pos]
      linarith)
  have hA_right : ratioA ≤ ((m + 1 : ℕ) : ℝ) / nR := by
    have hmul : ((n : ℕ) : ℝ) * Apos H t ≤ ((m + 1 : ℕ) : ℝ) * Apos H s := by
      have := Apos_pow H hH t (n : ℕ)
      have := Apos_pow H hH s (m + 1)
      linarith [hA_lt.le]
    exact (le_div_iff₀ hn_pos).2 (by
      simp only [ratioA]
      rw [div_mul_eq_mul_div, div_le_iff₀ hAs_pos]
      linarith)
  have hs_pow_pos : 0 < ((s : ℝ) ^ m) := by positivity
  have ht_pow_pos : 0 < ((t : ℝ) ^ (n : ℕ)) := by positivity
  have hs_pow_next_pos : 0 < ((s : ℝ) ^ (m + 1)) := by positivity
  have hlog_le :
      Real.logb (s : ℝ) ((s : ℝ) ^ m) ≤ Real.logb (s : ℝ) ((t : ℝ) ^ (n : ℕ)) :=
    (Real.logb_le_logb hs_real hs_pow_pos ht_pow_pos).2 (by exact_mod_cast hpow_le_nat)
  have hlog_lt :
      Real.logb (s : ℝ) ((t : ℝ) ^ (n : ℕ)) < Real.logb (s : ℝ) ((s : ℝ) ^ (m + 1)) :=
    (Real.logb_lt_logb_iff hs_real ht_pow_pos hs_pow_next_pos).2 (by exact_mod_cast hpow_lt_nat)
  have hL_left : (m : ℝ) / nR ≤ ratioL := by
    have hmul : (m : ℝ) ≤ ((n : ℕ) : ℝ) * ratioL := by
      have h1 : (m : ℝ) = Real.logb (s : ℝ) ((s : ℝ) ^ m) := by
        rw [Real.logb_pow, Real.logb_self_eq_one hs_real, mul_one]
      have h2 : ((n : ℕ) : ℝ) * ratioL = Real.logb (s : ℝ) ((t : ℝ) ^ (n : ℕ)) := by
        simp [ratioL, Real.logb_pow]
      linarith [hlog_le]
    exact (div_le_iff₀ hn_pos).2 (by simpa [nR, mul_comm] using hmul)
  have hL_right : ratioL ≤ ((m + 1 : ℕ) : ℝ) / nR := by
    have hmul : ((n : ℕ) : ℝ) * ratioL ≤ ((m + 1 : ℕ) : ℝ) := by
      have h1 : ((n : ℕ) : ℝ) * ratioL = Real.logb (s : ℝ) ((t : ℝ) ^ (n : ℕ)) := by
        simp [ratioL, Real.logb_pow]
      have h2 : (((m + 1 : ℕ) : ℝ)) = Real.logb (s : ℝ) ((s : ℝ) ^ (m + 1)) := by
        rw [Real.logb_pow, Real.logb_self_eq_one hs_real, mul_one]
      linarith [hlog_lt.le]
    exact (le_div_iff₀ hn_pos).2 (by simpa [nR, mul_comm] using hmul)
  have habs : |ratioA - ratioL| ≤ (((m + 1 : ℕ) : ℝ) / nR) - ((m : ℝ) / nR) :=
    abs_sub_le_of_mem_interval hA_left hA_right hL_left hL_right
  have hwidth : (((m + 1 : ℕ) : ℝ) / nR) - ((m : ℝ) / nR) = 1 / nR := by
    have : ((m + 1 : ℕ) : ℝ) - (m : ℝ) = 1 := by push_cast; ring
    field_simp [show nR ≠ 0 from hn_ne]; linarith
  simpa [ratioA, ratioL, nR] using habs.trans_eq hwidth

lemma Apos_ratio_eq_logb
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    {s t : ℕ+}
    (hs : 1 < s) :
    Apos H t / Apos H s = Real.logb (s : ℝ) (t : ℝ) := by
  by_contra hneq
  have hpos : 0 < |Apos H t / Apos H s - Real.logb (s : ℝ) (t : ℝ)| :=
    abs_pos.mpr (sub_ne_zero.mpr hneq)
  rcases exists_nat_one_div_lt hpos with ⟨N, hN⟩
  let n : ℕ+ := Nat.succPNat N
  have hbound := Apos_ratio_logb_close H hH (s := s) (t := t) (n := n) hs
  exact (not_lt_of_ge hbound) (by simpa [n, Nat.succPNat_coe] using hN)

lemma Apos_eq_K_mul_log
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    (n : ℕ+) :
    Apos H n = K H * Real.log (n : ℝ) := by
  have hratio : Apos H n / Apos H 2 = Real.logb (2 : ℝ) (n : ℝ) :=
    Apos_ratio_eq_logb H hH (s := 2) (t := n) (by decide)
  have hA2_ne : Apos H 2 ≠ 0 := ne_of_gt (Apos_pos_two H hH)
  have hlog2_ne : Real.log 2 ≠ 0 := Real.log_ne_zero.mpr (by norm_num)
  have hmain : Apos H n = Real.logb (2 : ℝ) (n : ℝ) * Apos H 2 :=
    (div_eq_iff hA2_ne).1 hratio
  rw [hmain, ← Real.log_div_log]
  unfold K
  field_simp [hlog2_ne]

lemma Apos_pow_two_eq_K_log_pow
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    (k : ℕ) :
    Apos H (2 ^ k) = K H * Real.log ((2 : ℝ) ^ k) := by
  rw [Real.log_pow, Apos_pow H hH 2 k, Apos_eq_K_mul_log H hH 2]
  push_cast
  ring

lemma A_monotone
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) :
    Monotone (A H) := by
  intro n m hnm
  simpa [A, Apos, uniformFin, uniformPNat] using
    hH.uniformMonotone.monotone (Nat.succPNat_mono hnm)

lemma Apos_monotone
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) :
    Monotone (Apos H) :=
  hH.uniformMonotone.monotone

/-- Entropy-form expression with natural logarithm. -/
def entropyNat
    {α : Type} [Fintype α]
    (p : ProbDist α) : ℝ :=
  -∑ a, p a * Real.log (p a)

/-- Entropy-form expression with logarithm base `b`. -/
def entropyBase
    {α : Type} [Fintype α]
    (b : ℝ)
    (p : ProbDist α) : ℝ :=
  -∑ a, p a * Real.logb b (p a)

lemma continuous_entropyNat
    {α : Type} [Fintype α] :
    Continuous (fun p : ProbDist α => entropyNat p) := by
  classical
  unfold entropyNat
  refine (continuous_finset_sum (s := Finset.univ)
    (f := fun a => fun p : ProbDist α => p a * Real.log (p a)) ?_).neg
  intro a _
  simpa using Real.Continuous.mul_log ((continuous_apply a).comp continuous_subtype_val)

lemma nonempty_of_probDist
    {α : Type} [Fintype α]
    (p : ProbDist α) :
    Nonempty α := by
  by_contra h
  haveI : IsEmpty α := not_nonempty_iff.mp h
  linarith [show (∑ a, p a) = 0 from by simp, prob_sum_eq_one p]

lemma Apos_eq_K_mul_logb
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    (b : ℝ)
    (hb : 1 < b)
    (n : ℕ+) :
    Apos H n = (K H * Real.log b) * Real.logb b (n : ℝ) := by
  have hb_pos : 0 < b := lt_trans (by norm_num) hb
  have hlogb_ne : Real.log b ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hb_pos (ne_of_gt hb)
  rw [Apos_eq_K_mul_log H hH n]
  unfold Real.logb
  field_simp [hlogb_ne]


end

end LeanPool.Shannon1948Formalization
