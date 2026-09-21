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
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.SeqVector

/-!
# The Günther iteration, abstractly

Let `T v = c + B v w` with `B` bilinear on vector coefficient sequences, satisfying at a base
level `r` (a natural number) and at all higher levels `k`:

* (E1) `‖B v w‖²_(r) ≤ A ‖v‖²_(r) ‖w‖²_(r)`;
* (E2) `‖B v w‖²_(k) ≤ A' (‖v‖²_(k) ‖w‖²_(r) + ‖v‖²_(r) ‖w‖²_(k))
          + Bₖ (‖v‖²_(k-1) ‖w‖²_(r) + ‖v‖²_(r) ‖w‖²_(k-1) + ‖v‖²_(r) ‖w‖²_(r))`  for `k > r`,
  with `A'` **independent of `k`** (the last lower-order term is redundant for `k > r`
  but makes the estimate uniform in `k ≥ r` for the concrete operator);
* polarization `B v v - B w w = B (v - w) v + B w (v - w)`.

If the squared radius `ρ` is small (`4Aρ ≤ 1/4`, `4A'ρ ≤ 1/2`) and `4‖c‖²_(r) ≤ ρ`, then the
iterates `v⁰ = 0`, `vᵖ⁺¹ = T vᵖ`
* stay in the ball `‖v‖²_(r) ≤ ρ`,
* are Cauchy in `H^r` (contraction factor `1/4` on squared norms),
* are bounded in every `H^k` (induction on `k`: `xₚ₊₁ ≤ ½ xₚ + D` gives `xₚ ≤ 2D`),

so their coefficientwise limit `v` (which exists by `exists_limit_of_cauchy_vec`) lies in every
`H^k` by Fatou and satisfies `v = T v`. Any predicate preserved by `T` and by coefficientwise
limits (e.g. being the coefficients of a real-valued map) holds for `v`.

Rellich compactness is not used. This is the analytic core of Theorem B; the concrete
Günther operator is shown to satisfy (E1), (E2) in `GuntherOperator.lean`.
-/

open scoped BigOperators
open Filter Topology NashEmbedding.Sobolev

noncomputable section

namespace NashEmbedding

variable {n N : ℕ}

/-- Hypotheses on a polarized operator `v ↦ c + B v v` at base level `r`. -/
structure IterHyp (n N : ℕ) (r : ℕ) (c : VecSeq n N)
    (B : VecSeq n N → VecSeq n N → VecSeq n N) (A A' : ℝ) (Bk : ℕ → ℝ) : Prop where
  A_nonneg : 0 ≤ A
  A'_nonneg : 0 ≤ A'
  Bk_nonneg : ∀ k, 0 ≤ Bk k
  c_mem : ∀ k : ℕ, VMem n N k c
  B_mem : ∀ k : ℕ, r ≤ k → ∀ v w, VMem n N k v → VMem n N k w → VMem n N k (B v w)
  E1 : ∀ v w, VMem n N r v → VMem n N r w →
    vecNormSq n N r (B v w) ≤ A * vecNormSq n N r v * vecNormSq n N r w
  E2 : ∀ k : ℕ, r < k → ∀ v w, VMem n N k v → VMem n N k w →
    vecNormSq n N k (B v w) ≤
      A' * (vecNormSq n N k v * vecNormSq n N r w + vecNormSq n N r v * vecNormSq n N k w)
      + Bk k * (vecNormSq n N ((k - 1 : ℕ) : ℝ) v * vecNormSq n N r w
                + vecNormSq n N r v * vecNormSq n N ((k - 1 : ℕ) : ℝ) w
                + vecNormSq n N r v * vecNormSq n N r w)
  polar : ∀ v w, VMem n N r v → VMem n N r w → B v v - B w w = B (v - w) v + B w (v - w)

/-- The iterates `v⁰ = 0`, `vᵖ⁺¹ = c + B vᵖ vᵖ`. -/
def iter (c : VecSeq n N) (B : VecSeq n N → VecSeq n N → VecSeq n N) : ℕ → VecSeq n N
  | 0 => 0
  | p + 1 => c + B (iter c B p) (iter c B p)

section

variable {r : ℕ} {c : VecSeq n N} {B : VecSeq n N → VecSeq n N → VecSeq n N} {A A' : ℝ}
  {Bk : ℕ → ℝ} (h : IterHyp n N r c B A A' Bk)
include h

lemma iter_mem (k : ℕ) (hk : r ≤ k) : ∀ p, VMem n N k (iter c B p)
  | 0 => vmem_zero _
  | p + 1 => (h.c_mem k).add (h.B_mem k hk _ _ (iter_mem k hk p) (iter_mem k hk p))

variable {ρ : ℝ} (hρ : 0 < ρ) (hA : 4 * A * ρ ≤ 1 / 4) (hA' : 4 * A' * ρ ≤ 1 / 2)
  (hc : 4 * vecNormSq n N r c ≤ ρ)
include hρ hA hc

/-- The iterates stay in the ball `‖v‖²_(r) ≤ ρ`. -/
lemma iter_ball : ∀ p, vecNormSq n N r (iter c B p) ≤ ρ
  | 0 => by rw [iter, vecNormSq_zero]; exact hρ.le
  | p + 1 => by
    have hm := iter_mem h r le_rfl p
    have hprev := iter_ball p
    have hBm := h.B_mem r le_rfl _ _ hm hm
    have h1 := vecNormSq_add_le (h.c_mem r) hBm
    have h2 := h.E1 _ _ hm hm
    have h0 := vecNormSq_nonneg (r : ℝ) (iter c B p)
    have h3 : A * vecNormSq n N r (iter c B p) * vecNormSq n N r (iter c B p) ≤ A * ρ * ρ := by
      have := mul_le_mul hprev hprev h0 hρ.le
      nlinarith [h.A_nonneg]
    rw [iter]
    nlinarith

omit hρ hc in
/-- One step contracts squared `H^r` distances by `1/4`. -/
lemma iter_contract_step (p q : ℕ)
    (hp : vecNormSq n N r (iter c B p) ≤ ρ) (hq : vecNormSq n N r (iter c B q) ≤ ρ) :
    vecNormSq n N r (iter c B (p + 1) - iter c B (q + 1)) ≤
      (1 / 4) * vecNormSq n N r (iter c B p - iter c B q) := by
  have hmp := iter_mem h r le_rfl p
  have hmq := iter_mem h r le_rfl q
  have hd := hmp.sub hmq
  have heq : iter c B (p + 1) - iter c B (q + 1)
      = B (iter c B p - iter c B q) (iter c B p) + B (iter c B q) (iter c B p - iter c B q) := by
    simp only [iter]
    rw [add_sub_add_left_eq_sub]
    exact h.polar _ _ hmp hmq
  rw [heq]
  have hB1 := h.B_mem r le_rfl _ _ hd hmp
  have hB2 := h.B_mem r le_rfl _ _ hmq hd
  have h1 := vecNormSq_add_le hB1 hB2
  have h2 := h.E1 _ _ hd hmp
  have h3 := h.E1 _ _ hmq hd
  have hd0 := vecNormSq_nonneg (r : ℝ) (iter c B p - iter c B q)
  have h4 : A * vecNormSq n N r (iter c B p - iter c B q) * vecNormSq n N r (iter c B p)
      ≤ A * ρ * vecNormSq n N r (iter c B p - iter c B q) := by
    have := mul_le_mul_of_nonneg_left hp (mul_nonneg h.A_nonneg hd0)
    linarith [this]
  have h5 : A * vecNormSq n N r (iter c B q) * vecNormSq n N r (iter c B p - iter c B q)
      ≤ A * ρ * vecNormSq n N r (iter c B p - iter c B q) := by
    have := mul_le_mul_of_nonneg_left hq h.A_nonneg
    exact mul_le_mul_of_nonneg_right this hd0
  nlinarith

/-- Iterated contraction: `d(vᵖ⁺ʲ, vᵠ⁺ʲ) ≤ 4⁻ʲ d(vᵖ, vᵠ)`. -/
lemma iter_contract (p q : ℕ) : ∀ j : ℕ,
    vecNormSq n N r (iter c B (p + j) - iter c B (q + j)) ≤
      (1 / 4) ^ j * vecNormSq n N r (iter c B p - iter c B q)
  | 0 => by simp
  | j + 1 => by
    have hstep := iter_contract_step h hA (p + j) (q + j)
      (iter_ball h hρ hA hc _) (iter_ball h hρ hA hc _)
    have ih := iter_contract p q j
    calc vecNormSq n N r (iter c B (p + (j + 1)) - iter c B (q + (j + 1)))
        = vecNormSq n N r (iter c B (p + j + 1) - iter c B (q + j + 1)) := by
          rw [add_assoc, add_assoc]
      _ ≤ (1 / 4) * vecNormSq n N r (iter c B (p + j) - iter c B (q + j)) := hstep
      _ ≤ (1 / 4) * ((1 / 4) ^ j * vecNormSq n N r (iter c B p - iter c B q)) := by
          exact mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1 / 4) ^ (j + 1) * vecNormSq n N r (iter c B p - iter c B q) := by ring

/-- Uniform Cauchy bound: for `P ≤ p, q`, `d(vᵖ, vᵠ) ≤ 4⁻ᴾ ρ`. -/
lemma iter_cauchy_bound (P p q : ℕ) (hp : P ≤ p) (hq : P ≤ q) :
    vecNormSq n N r (iter c B p - iter c B q) ≤ (1 / 4) ^ P * ρ := by
  -- reduce to the case `p ≤ q` by symmetry
  have key : ∀ p q : ℕ, P ≤ p → p ≤ q →
      vecNormSq n N r (iter c B p - iter c B q) ≤ (1 / 4) ^ P * ρ := by
    intro p q hp hpq
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hpq
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hp
    -- `d(v^{P+i}, v^{P+i+j}) ≤ 4^{-(P+i)} d(v^0, v^j)`, and `d(v^0, v^j) = ‖v^j‖² ≤ ρ`
    have h1 := iter_contract h hρ hA hc 0 j (P + i)
    rw [zero_add, add_comm j (P + i)] at h1
    have h2 : vecNormSq n N r (iter c B 0 - iter c B j) ≤ ρ := by
      rw [iter, zero_sub, vecNormSq_neg]; exact iter_ball h hρ hA hc j
    have h3 : ((1 : ℝ) / 4) ^ (P + i) ≤ (1 / 4) ^ P :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right P i)
    calc vecNormSq n N r (iter c B (P + i) - iter c B (P + i + j))
        ≤ (1 / 4) ^ (P + i) * vecNormSq n N r (iter c B 0 - iter c B j) := h1
      _ ≤ (1 / 4) ^ P * ρ := mul_le_mul h3 h2 (vecNormSq_nonneg _ _) (by positivity)
  rcases le_total p q with hpq | hqp
  · exact key p q hp hpq
  · have := key q p hq hqp
    rwa [← vecNormSq_neg, neg_sub] at this

/-- The iterates are Cauchy in `H^r`. -/
lemma iter_cauchy (ε : ℝ) (hε : 0 < ε) :
    ∃ P, ∀ p ≥ P, ∀ q ≥ P, vecNormSq n N r (iter c B p - iter c B q) ≤ ε := by
  obtain ⟨P, hP⟩ := exists_pow_lt_of_lt_one (div_pos hε hρ) (by norm_num : (1 : ℝ) / 4 < 1)
  refine ⟨P, fun p hp q hq => ?_⟩
  calc vecNormSq n N r (iter c B p - iter c B q) ≤ (1 / 4) ^ P * ρ :=
        iter_cauchy_bound h hρ hA hc P p q hp hq
    _ ≤ (ε / ρ) * ρ := mul_le_mul_of_nonneg_right hP.le hρ.le
    _ = ε := div_mul_cancel₀ ε hρ.ne'

include hA' in
/-- The iterates are bounded in every `H^k`, `k ≥ r` (induction on `k`). -/
lemma iter_bounded (k : ℕ) (hk : r ≤ k) : ∃ M : ℝ, ∀ p, vecNormSq n N k (iter c B p) ≤ M := by
  induction k, hk using Nat.le_induction with
  | base => exact ⟨ρ, iter_ball h hρ hA hc⟩
  | succ k hrk ih =>
    obtain ⟨M, hM⟩ := ih
    have hM0 : 0 ≤ M := le_trans (vecNormSq_nonneg _ _) (hM 0)
    have hlt : r < k + 1 := Nat.lt_succ_of_le hrk
    set D : ℝ := 2 * vecNormSq n N (k + 1 : ℕ) c + 4 * Bk (k + 1) * ρ * M
      + 2 * Bk (k + 1) * ρ * ρ with hD
    have hD0 : 0 ≤ D := by
      have := vecNormSq_nonneg ((k + 1 : ℕ) : ℝ) c
      have := h.Bk_nonneg (k + 1)
      positivity
    refine ⟨2 * D, ?_⟩
    intro p
    induction p with
    | zero => rw [iter, vecNormSq_zero]; linarith
    | succ p ih =>
      have hm := iter_mem h (k + 1) hlt.le p
      have hBm := h.B_mem (k + 1) hlt.le _ _ hm hm
      have h1 := vecNormSq_add_le (h.c_mem (k + 1)) hBm
      have h2 := h.E2 (k + 1) hlt _ _ hm hm
      rw [Nat.add_sub_cancel] at h2
      have hball := iter_ball h hρ hA hc p
      have hMk := hM p
      have hx0 := vecNormSq_nonneg ((k + 1 : ℕ) : ℝ) (iter c B p)
      have hk0 := vecNormSq_nonneg (k : ℝ) (iter c B p)
      have hr0 := vecNormSq_nonneg (r : ℝ) (iter c B p)
      -- the top-order term: `A' · 2 x ‖v‖²_r ≤ 2 A' ρ x ≤ x / 4`
      have htop : A' * (vecNormSq n N (k + 1 : ℕ) (iter c B p) * vecNormSq n N r (iter c B p)
          + vecNormSq n N r (iter c B p) * vecNormSq n N (k + 1 : ℕ) (iter c B p))
          ≤ 2 * A' * ρ * vecNormSq n N (k + 1 : ℕ) (iter c B p) := by
        have := mul_le_mul_of_nonneg_left hball (mul_nonneg h.A'_nonneg hx0)
        nlinarith
      -- the lower-order term: `Bₖ (2 ‖v‖²_{k} ‖v‖²_r + ‖v‖⁴_r) ≤ Bₖ (2 ρ M + ρ²)`
      have hlow : Bk (k + 1) * (vecNormSq n N k (iter c B p) * vecNormSq n N r (iter c B p)
          + vecNormSq n N r (iter c B p) * vecNormSq n N k (iter c B p)
          + vecNormSq n N r (iter c B p) * vecNormSq n N r (iter c B p))
          ≤ 2 * Bk (k + 1) * ρ * M + Bk (k + 1) * ρ * ρ := by
        have hBk := h.Bk_nonneg (k + 1)
        have h6 := mul_le_mul hMk hball hr0 hM0
        have h7 := mul_le_mul hball hball hr0 hρ.le
        nlinarith
      rw [iter]
      nlinarith

end

/-- **The abstract Günther fixed-point theorem.** Under `IterHyp` and the smallness conditions,
there is `v` in every `H^k` with `v = c + B v v`, `‖v‖²_(r) ≤ ρ`, and `v` satisfies any predicate
`P` that holds at `0`, is preserved by `v ↦ c + B v v`, and is closed under coefficientwise
limits. -/
theorem exists_fixed_point {r : ℕ} {c : VecSeq n N} {B : VecSeq n N → VecSeq n N → VecSeq n N}
    {A A' : ℝ} {Bk : ℕ → ℝ} (h : IterHyp n N r c B A A' Bk)
    {ρ : ℝ} (hρ : 0 < ρ) (hA : 4 * A * ρ ≤ 1 / 4) (hA' : 4 * A' * ρ ≤ 1 / 2)
    (hc : 4 * vecNormSq n N r c ≤ ρ)
    (P : VecSeq n N → Prop) (hP0 : P 0) (hPT : ∀ v, P v → P (c + B v v))
    (hPlim : ∀ (u : ℕ → VecSeq n N) (a : VecSeq n N), (∀ p, P (u p)) →
      (∀ α m, Tendsto (fun p => u p α m) atTop (𝓝 (a α m))) → P a) :
    ∃ v : VecSeq n N, (∀ k : ℕ, VMem n N k v) ∧ v = c + B v v ∧ vecNormSq n N r v ≤ ρ ∧ P v := by
  -- the limit of the iterates
  obtain ⟨v, hvmem, hvlim, hvconv⟩ := exists_limit_of_cauchy_vec (iter_mem h r le_rfl)
    (iter_cauchy h hρ hA hc)
  have hball : vecNormSq n N r v ≤ ρ :=
    (vmem_of_tendsto_coeff (iter_mem h r le_rfl) (iter_ball h hρ hA hc) hvlim).2
  refine ⟨v, ?_, ?_, hball, ?_⟩
  · -- regularity: Fatou at every level `k ≥ r`, monotonicity below `r`
    intro k
    rcases le_or_gt r k with hk | hk
    · obtain ⟨M, hM⟩ := iter_bounded h hρ hA hA' hc k hk
      exact (vmem_of_tendsto_coeff (iter_mem h k hk) hM hvlim).1
    · exact hvmem.mono (by exact_mod_cast hk.le)
  · -- fixed point: `T vᵖ → T v` in `H^r`, and `T vᵖ = vᵖ⁺¹ → v` coefficientwise
    have hTmem : VMem n N r (c + B v v) := (h.c_mem r).add (h.B_mem r le_rfl _ _ hvmem hvmem)
    have hTconv : Tendsto (fun p => vecNormSq n N r (iter c B (p + 1) - (c + B v v))) atTop (𝓝 0) := by
      have hbnd : ∀ p, vecNormSq n N r (iter c B (p + 1) - (c + B v v))
          ≤ 4 * A * ρ * vecNormSq n N r (iter c B p - v) := by
        intro p
        have hmp := iter_mem h r le_rfl p
        have hd := hmp.sub hvmem
        have heq : iter c B (p + 1) - (c + B v v)
            = B (iter c B p - v) (iter c B p) + B v (iter c B p - v) := by
          simp only [iter]
          rw [add_sub_add_left_eq_sub]
          exact h.polar _ _ hmp hvmem
        rw [heq]
        have h1 := vecNormSq_add_le (h.B_mem r le_rfl _ _ hd hmp) (h.B_mem r le_rfl _ _ hvmem hd)
        have h2 := h.E1 _ _ hd hmp
        have h3 := h.E1 _ _ hvmem hd
        have hd0 := vecNormSq_nonneg (r : ℝ) (iter c B p - v)
        have hp := iter_ball h hρ hA hc p
        have h4 : A * vecNormSq n N r (iter c B p - v) * vecNormSq n N r (iter c B p)
            ≤ A * ρ * vecNormSq n N r (iter c B p - v) := by
          have := mul_le_mul_of_nonneg_left hp (mul_nonneg h.A_nonneg hd0)
          linarith [this]
        have h5 : A * vecNormSq n N r v * vecNormSq n N r (iter c B p - v)
            ≤ A * ρ * vecNormSq n N r (iter c B p - v) := by
          have := mul_le_mul_of_nonneg_left hball h.A_nonneg
          exact mul_le_mul_of_nonneg_right this hd0
        nlinarith
      refine squeeze_zero (fun p => vecNormSq_nonneg _ _) hbnd ?_
      simpa using hvconv.const_mul (4 * A * ρ)
    funext α m
    have hcoef : Tendsto (fun p => iter c B (p + 1) α m) atTop (𝓝 ((c + B v v) α m)) :=
      tendsto_coeff_of_tendsto_vecNormSq (fun p => iter_mem h r le_rfl (p + 1)) hTmem hTconv α m
    have hcoef' : Tendsto (fun p => iter c B (p + 1) α m) atTop (𝓝 (v α m)) :=
      (hvlim α m).comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hcoef' hcoef
  · -- the invariant predicate
    have hPiter : ∀ p, P (iter c B p) := by
      intro p
      induction p with
      | zero => exact hP0
      | succ p ih => exact hPT _ ih
    exact hPlim _ v hPiter hvlim

end NashEmbedding

end
