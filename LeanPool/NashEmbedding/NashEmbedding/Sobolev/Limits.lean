/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Differentiation

/-!
# Sobolev sequence spaces: algebra, finite sums, derivatives, limits

Elementary closure properties of `MemSobolev n s` / `sobolevNormSq n s` on coefficient
sequences `(Fin n → ℤ) → ℂ` that the Günther iteration (Theorem B) needs:

* closure under `+`, `-`, scalar multiples, finite sums, with the quasi-triangle
  inequalities `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` and `‖∑_{i∈S} aᵢ‖² ≤ |S| ∑_{i∈S} ‖aᵢ‖²`;
* the derivative bound `‖∂ⱼ a‖²_(s) ≤ ‖a‖²_(s+1)`;
* **Fatou**: a coefficientwise limit of a sequence bounded in `H^s` lies in `H^s` with the
  same bound;
* **completeness without completeness**: a Cauchy sequence in `H^s` has a coefficientwise
  limit `a ∈ H^s`, and converges to `a` in `H^s`.

The last two replace Rellich compactness in the regularity argument for Theorem B: the
iterates are bounded in every `H^k`, hence so is their coefficientwise limit.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Basic algebra -/

lemma sobolevNormSq_nonneg (s : ℝ) (a : (Fin n → ℤ) → ℂ) : 0 ≤ sobolevNormSq n s a :=
  tsum_nonneg fun m => mul_nonneg (weight_nonneg s m) (sq_nonneg _)

lemma memSobolev_zero (s : ℝ) : MemSobolev n s (fun _ => (0 : ℂ)) := by
  simp [MemSobolev, summable_zero]

lemma sobolevNormSq_zero (s : ℝ) : sobolevNormSq n s (fun _ => (0 : ℂ)) = 0 := by
  simp [sobolevNormSq]

/-- Each weighted term is bounded by the squared norm. -/
lemma weight_mul_norm_sq_le_sobolevNormSq {s : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n s a) (m : Fin n → ℤ) :
    weight n s m * ‖a m‖ ^ 2 ≤ sobolevNormSq n s a :=
  ha.le_tsum m fun _ _ => mul_nonneg (weight_nonneg s _) (sq_nonneg _)

/-- A sequence with vanishing `H^s` norm is zero. -/
lemma eq_zero_of_sobolevNormSq_eq_zero {s : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n s a) (h : sobolevNormSq n s a = 0) : ∀ m, a m = 0 := by
  intro m
  have h1 := weight_mul_norm_sq_le_sobolevNormSq ha m
  rw [h] at h1
  have h2 : ‖a m‖ ^ 2 ≤ 0 :=
    le_of_mul_le_mul_left (by simpa using h1) (weight_pos s m)
  have h3 : ‖a m‖ = 0 := by nlinarith [norm_nonneg (a m)]
  exact norm_eq_zero.mp h3

lemma MemSobolev.smul {s : ℝ} {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) (c : ℂ) :
    MemSobolev n s (fun m => c * a m) := by
  have h := ha.mul_left (‖c‖ ^ 2)
  refine h.congr fun m => ?_
  rw [norm_mul, mul_pow]
  ring

lemma sobolevNormSq_smul (s : ℝ) (c : ℂ) (a : (Fin n → ℤ) → ℂ) :
    sobolevNormSq n s (fun m => c * a m) = ‖c‖ ^ 2 * sobolevNormSq n s a := by
  unfold sobolevNormSq
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [norm_mul, mul_pow]
  ring

lemma MemSobolev.neg {s : ℝ} {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) :
    MemSobolev n s (fun m => -a m) := by
  simpa [MemSobolev] using ha

lemma sobolevNormSq_neg (s : ℝ) (a : (Fin n → ℤ) → ℂ) :
    sobolevNormSq n s (fun m => -a m) = sobolevNormSq n s a := by
  simp [sobolevNormSq]

lemma MemSobolev.add {s : ℝ} {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n s a) (hb : MemSobolev n s b) :
    MemSobolev n s (fun m => a m + b m) := by
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (weight_nonneg s m) (sq_nonneg _)) (fun m => ?_)
    ((ha.mul_left 2).add (hb.mul_left 2))
  have h1 : ‖a m + b m‖ ^ 2 ≤ 2 * ‖a m‖ ^ 2 + 2 * ‖b m‖ ^ 2 := by
    have h2 : ‖a m + b m‖ ^ 2 ≤ (‖a m‖ + ‖b m‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (a m) (b m)) 2
    nlinarith [sq_nonneg (‖a m‖ - ‖b m‖)]
  calc weight n s m * ‖a m + b m‖ ^ 2
      ≤ weight n s m * (2 * ‖a m‖ ^ 2 + 2 * ‖b m‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (weight_nonneg s m)
    _ = 2 * (weight n s m * ‖a m‖ ^ 2) + 2 * (weight n s m * ‖b m‖ ^ 2) := by ring

lemma MemSobolev.sub {s : ℝ} {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n s a) (hb : MemSobolev n s b) :
    MemSobolev n s (fun m => a m - b m) := by
  simpa [sub_eq_add_neg] using ha.add hb.neg

/-- Quasi-triangle inequality: `‖a + b‖²_(s) ≤ 2 ‖a‖²_(s) + 2 ‖b‖²_(s)`. -/
lemma sobolevNormSq_add_le {s : ℝ} {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n s a) (hb : MemSobolev n s b) :
    sobolevNormSq n s (fun m => a m + b m) ≤ 2 * sobolevNormSq n s a + 2 * sobolevNormSq n s b := by
  have hstep : ∀ m, weight n s m * ‖a m + b m‖ ^ 2
      ≤ 2 * (weight n s m * ‖a m‖ ^ 2) + 2 * (weight n s m * ‖b m‖ ^ 2) := by
    intro m
    have h1 : ‖a m + b m‖ ^ 2 ≤ 2 * ‖a m‖ ^ 2 + 2 * ‖b m‖ ^ 2 := by
      have h2 : ‖a m + b m‖ ^ 2 ≤ (‖a m‖ + ‖b m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (a m) (b m)) 2
      nlinarith [sq_nonneg (‖a m‖ - ‖b m‖)]
    calc weight n s m * ‖a m + b m‖ ^ 2
        ≤ weight n s m * (2 * ‖a m‖ ^ 2 + 2 * ‖b m‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (weight_nonneg s m)
      _ = 2 * (weight n s m * ‖a m‖ ^ 2) + 2 * (weight n s m * ‖b m‖ ^ 2) := by ring
  calc sobolevNormSq n s (fun m => a m + b m)
      ≤ ∑' m, (2 * (weight n s m * ‖a m‖ ^ 2) + 2 * (weight n s m * ‖b m‖ ^ 2)) :=
        Summable.tsum_le_tsum hstep (ha.add hb) ((ha.mul_left 2).add (hb.mul_left 2))
    _ = 2 * sobolevNormSq n s a + 2 * sobolevNormSq n s b := by
        rw [Summable.tsum_add (ha.mul_left 2) (hb.mul_left 2), tsum_mul_left, tsum_mul_left]
        rfl

lemma sobolevNormSq_sub_le {s : ℝ} {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n s a) (hb : MemSobolev n s b) :
    sobolevNormSq n s (fun m => a m - b m) ≤ 2 * sobolevNormSq n s a + 2 * sobolevNormSq n s b := by
  have h := sobolevNormSq_add_le ha hb.neg
  rw [sobolevNormSq_neg] at h
  simpa [sub_eq_add_neg] using h

/-! ## Finite sums -/

lemma MemSobolev.finset_sum {ι : Type*} {s : ℝ} (S : Finset ι) {a : ι → (Fin n → ℤ) → ℂ}
    (ha : ∀ i ∈ S, MemSobolev n s (a i)) :
    MemSobolev n s (fun m => ∑ i ∈ S, a i m) := by
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (weight_nonneg s m) (sq_nonneg _)) (fun m => ?_)
    (((summable_sum (f := fun i m => weight n s m * ‖a i m‖ ^ 2) ha)).mul_left (S.card : ℝ))
  have h1 : ‖∑ i ∈ S, a i m‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖a i m‖ ^ 2 := by
    calc ‖∑ i ∈ S, a i m‖ ^ 2 ≤ (∑ i ∈ S, ‖a i m‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S (fun i => a i m)) 2
      _ ≤ (S.card : ℝ) * ∑ i ∈ S, ‖a i m‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  calc weight n s m * ‖∑ i ∈ S, a i m‖ ^ 2
      ≤ weight n s m * ((S.card : ℝ) * ∑ i ∈ S, ‖a i m‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (weight_nonneg s m)
    _ = (S.card : ℝ) * ∑ i ∈ S, weight n s m * ‖a i m‖ ^ 2 := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- Quasi-triangle inequality for finite sums:
`‖∑_{i∈S} aᵢ‖²_(s) ≤ |S| ∑_{i∈S} ‖aᵢ‖²_(s)` (Cauchy–Schwarz termwise). -/
lemma sobolevNormSq_finset_sum_le {ι : Type*} {s : ℝ} (S : Finset ι) {a : ι → (Fin n → ℤ) → ℂ}
    (ha : ∀ i ∈ S, MemSobolev n s (a i)) :
    sobolevNormSq n s (fun m => ∑ i ∈ S, a i m) ≤ S.card * ∑ i ∈ S, sobolevNormSq n s (a i) := by
  have hsummable := (summable_sum (f := fun i m => weight n s m * ‖a i m‖ ^ 2) ha).mul_left
      (S.card : ℝ)
  have hstep : ∀ m, weight n s m * ‖∑ i ∈ S, a i m‖ ^ 2
      ≤ (S.card : ℝ) * ∑ i ∈ S, weight n s m * ‖a i m‖ ^ 2 := by
    intro m
    have h1 : ‖∑ i ∈ S, a i m‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖a i m‖ ^ 2 := by
      calc ‖∑ i ∈ S, a i m‖ ^ 2 ≤ (∑ i ∈ S, ‖a i m‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S (fun i => a i m)) 2
        _ ≤ (S.card : ℝ) * ∑ i ∈ S, ‖a i m‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    calc weight n s m * ‖∑ i ∈ S, a i m‖ ^ 2
        ≤ weight n s m * ((S.card : ℝ) * ∑ i ∈ S, ‖a i m‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (weight_nonneg s m)
      _ = (S.card : ℝ) * ∑ i ∈ S, weight n s m * ‖a i m‖ ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  calc sobolevNormSq n s (fun m => ∑ i ∈ S, a i m)
      ≤ ∑' m, (S.card : ℝ) * ∑ i ∈ S, weight n s m * ‖a i m‖ ^ 2 :=
        Summable.tsum_le_tsum hstep (MemSobolev.finset_sum S ha) hsummable
    _ = S.card * ∑ i ∈ S, sobolevNormSq n s (a i) := by
        rw [tsum_mul_left, Summable.tsum_finsetSum ha]
        rfl

/-! ## Derivatives -/

/-- `‖∂ⱼ a‖²_(s) ≤ ‖a‖²_(s+1)` termwise: `(1+|m|²)^s mⱼ² ≤ (1+|m|²)^{s+1}`. -/
lemma weight_norm_partialCoeff_sq_le (s : ℝ) (j : Fin n) (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) :
    weight n s m * ‖partialCoeff j a m‖ ^ 2 ≤ weight n (s + 1) m * ‖a m‖ ^ 2 := by
  have h1 : ((m j : ℝ)) ^ 2 ≤ 1 + ∑ i, ((m i : ℝ)) ^ 2 := by
    have h2 : ((m j : ℝ)) ^ 2 ≤ ∑ i, ((m i : ℝ)) ^ 2 :=
      Finset.single_le_sum (f := fun i => ((m i : ℝ)) ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ j)
    linarith
  have h3 : weight n (s + 1) m = weight n s m * (1 + ∑ i, ((m i : ℝ)) ^ 2) := by
    rw [← weight_mul s 1 m]
    simp [weight, Real.rpow_one]
  rw [norm_partialCoeff, mul_pow, sq_abs, h3]
  calc weight n s m * ((m j : ℝ) ^ 2 * ‖a m‖ ^ 2)
      ≤ weight n s m * ((1 + ∑ i, ((m i : ℝ)) ^ 2) * ‖a m‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
          (weight_nonneg s m)
    _ = weight n s m * (1 + ∑ i, ((m i : ℝ)) ^ 2) * ‖a m‖ ^ 2 := by ring

lemma memSobolev_partialCoeff {s : ℝ} {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n (s + 1) a)
    (j : Fin n) : MemSobolev n s (partialCoeff j a) := by
  exact Summable.of_nonneg_of_le (fun m => mul_nonneg (weight_nonneg s m) (sq_nonneg _))
    (fun m => weight_norm_partialCoeff_sq_le s j a m) ha

lemma sobolevNormSq_partialCoeff_le {s : ℝ} {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n (s + 1) a)
    (j : Fin n) : sobolevNormSq n s (partialCoeff j a) ≤ sobolevNormSq n (s + 1) a := by
  exact Summable.tsum_le_tsum (fun m => weight_norm_partialCoeff_sq_le s j a m)
    (memSobolev_partialCoeff ha j) ha

/-! ## Limits -/

/-- **Fatou.** If `v p → a` coefficientwise and `‖v p‖²_(s) ≤ M` for all `p`, then
`a ∈ H^s` with `‖a‖²_(s) ≤ M`. -/
theorem memSobolev_of_tendsto_coeff {s : ℝ} {v : ℕ → (Fin n → ℤ) → ℂ} {a : (Fin n → ℤ) → ℂ}
    {M : ℝ} (hv : ∀ p, MemSobolev n s (v p)) (hM : ∀ p, sobolevNormSq n s (v p) ≤ M)
    (hlim : ∀ m, Tendsto (fun p => v p m) atTop (𝓝 (a m))) :
    MemSobolev n s a ∧ sobolevNormSq n s a ≤ M := by
  have hnn : 0 ≤ fun m => weight n s m * ‖a m‖ ^ 2 := fun m =>
    mul_nonneg (weight_nonneg s m) (sq_nonneg _)
  have key : ∀ T : Finset (Fin n → ℤ), ∑ m ∈ T, weight n s m * ‖a m‖ ^ 2 ≤ M := by
    intro T
    have hT : Tendsto (fun p => ∑ m ∈ T, weight n s m * ‖v p m‖ ^ 2) atTop
        (𝓝 (∑ m ∈ T, weight n s m * ‖a m‖ ^ 2)) := by
      exact tendsto_finsetSum _ fun m _ => (((hlim m).norm).pow 2).const_mul _
    refine le_of_tendsto hT ?_
    filter_upwards with p
    calc ∑ m ∈ T, weight n s m * ‖v p m‖ ^ 2 ≤ sobolevNormSq n s (v p) :=
          Summable.sum_le_tsum T
            (fun i _ => mul_nonneg (weight_nonneg s i) (sq_nonneg _)) (hv p)
      _ ≤ M := hM p
  exact ⟨summable_of_sum_le hnn key, Real.tsum_le_of_sum_le hnn key⟩

/-- **Cauchy sequences converge.** A sequence that is Cauchy for `‖·‖²_(s)` has a
coefficientwise limit `a ∈ H^s`, and converges to `a` in `‖·‖²_(s)`. -/
theorem exists_limit_of_cauchy {s : ℝ} {v : ℕ → (Fin n → ℤ) → ℂ}
    (hv : ∀ p, MemSobolev n s (v p))
    (hc : ∀ ε > 0, ∃ P, ∀ p ≥ P, ∀ q ≥ P, sobolevNormSq n s (fun m => v p m - v q m) ≤ ε) :
    ∃ a : (Fin n → ℤ) → ℂ, MemSobolev n s a ∧
      (∀ m, Tendsto (fun p => v p m) atTop (𝓝 (a m))) ∧
      Tendsto (fun p => sobolevNormSq n s (fun m => v p m - a m)) atTop (𝓝 0) := by
  have hcauchy : ∀ m, CauchySeq (fun p => v p m) := by
    intro m
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨P, hP⟩ := hc (weight n s m * (ε / 2) ^ 2)
      (mul_pos (weight_pos s m) (by positivity))
    refine ⟨P, fun p hp q hq => ?_⟩
    have h1 := hP p hp q hq
    have h2 : weight n s m * ‖v p m - v q m‖ ^ 2 ≤ weight n s m * (ε / 2) ^ 2 :=
      le_trans (weight_mul_norm_sq_le_sobolevNormSq ((hv p).sub (hv q)) m) h1
    have h3 : ‖v p m - v q m‖ ^ 2 ≤ (ε / 2) ^ 2 := le_of_mul_le_mul_left h2 (weight_pos s m)
    have h4 : ‖v p m - v q m‖ ≤ ε / 2 := by
      nlinarith [norm_nonneg (v p m - v q m)]
    calc dist (v p m) (v q m) = ‖v p m - v q m‖ := dist_eq_norm _ _
      _ ≤ ε / 2 := h4
      _ < ε := by linarith
  choose a ha using fun m => cauchySeq_tendsto_of_complete (hcauchy m)
  have key : ∀ ε > 0, ∃ P, ∀ p ≥ P, MemSobolev n s (fun m => v p m - a m) ∧
      sobolevNormSq n s (fun m => v p m - a m) ≤ ε := by
    intro ε hε
    obtain ⟨P, hP⟩ := hc ε hε
    refine ⟨P, fun p hp => ?_⟩
    refine memSobolev_of_tendsto_coeff (v := fun q m => v p m - v (q + P) m) (M := ε)
      (fun q => (hv p).sub (hv (q + P))) (fun q => hP p hp (q + P) (by omega)) (fun m => ?_)
    exact tendsto_const_nhds.sub ((ha m).comp (tendsto_add_atTop_nat P))
  obtain ⟨P₀, hP₀⟩ := key 1 one_pos
  have hmemA : MemSobolev n s a := by
    have h1 := (hP₀ P₀ le_rfl).1
    simpa using (hv P₀).sub h1
  refine ⟨a, hmemA, ha, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P, hP⟩ := key (ε / 2) (by positivity)
  refine ⟨P, fun p hp => ?_⟩
  have h1 := (hP p hp).2
  have h2 := sobolevNormSq_nonneg s (fun m => v p m - a m)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h2]
  linarith

end NashEmbedding.Sobolev

end
