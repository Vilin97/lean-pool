/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.LossVariance
public import LeanPool.AsymptoticTrianglePacking.Internal.RegularMost
public import LeanPool.AsymptoticTrianglePacking.Internal.IterationSeq
public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Greedy
public import LeanPool.AsymptoticTrianglePacking.Internal.Round
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Bound






/-!
# LeanPool.AsymptoticTrianglePacking.Internal — T3 convergence core : geometric decay of the
uncovered set

Standalone, Mathlib-only. The mathematical heart of the iterated nibble (T3): if each round covers a
definite fraction of the remaining vertices — so the uncovered count `a k` shrinks by a factor
`λ < 1` per round — then after `T = O(log 1/β)` rounds the uncovered count is `≤ β · a 0 = βq`.

* `geometric_decay` — `a (k+1) ≤ λ·a k` (with `a ≥ 0`, `λ ≥ 0`) ⇒ `a k ≤ λ^k · a 0`.
* `exists_round_count_below` — for `0 ≤ λ < 1` and target `β > 0`, some round count `T` reaches
  `a T ≤ β · a 0`.

This is the deterministic convergence mechanism into which the per-round covering bound
(`exists_large_round_matching` / `E[covered] ≥ …`) plugs to complete T3.

Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-- **T3-conv(1) — geometric decay.** If `a (k+1) ≤ λ · a k` for all `k` (with `a` nonnegative and
`λ ≥ 0`), then `a k ≤ λ^k · a 0`. -/
theorem geometric_decay {a : ℕ → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hstep : ∀ k, a (k + 1) ≤ lam * a k) : ∀ k, a k ≤ lam ^ k * a 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc a (k + 1) ≤ lam * a k := hstep k
        _ ≤ lam * (lam ^ k * a 0) := mul_le_mul_of_nonneg_left ih hlam
        _ = lam ^ (k + 1) * a 0 := by ring

/-- **T3-conv(2) — the uncovered count reaches `β · a 0`.** For a per-round shrink factor
`0 ≤ λ < 1` and any target fraction `β > 0`, some round count `T` brings the uncovered count down to
`a T ≤ β · a 0`. (Take `T` with `λ^T < β`.) -/
theorem exists_round_count_below {a : ℕ → ℝ} {lam β : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hβ : 0 < β) (ha : ∀ k, 0 ≤ a k) (hstep : ∀ k, a (k + 1) ≤ lam * a k) :
    ∃ T, a T ≤ β * a 0 := by
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hβ hlam1
  exact ⟨T, le_trans (geometric_decay hlam0 hstep T)
    (mul_le_mul_of_nonneg_right hT.le (ha 0))⟩

/-- **Per-round decrease bridge.** If each round's uncovered count `a` drops by the covered amount
`b` (`a(k+1) ≤ a k - b k`) and each round covers at least a `(1-λ)` fraction (`(1-λ)·a k ≤ b k`),
then the uncovered sequence shrinks by factor `λ`: `a(k+1) ≤ λ·a k`. -/
theorem uncovered_step {a b : ℕ → ℝ} {lam : ℝ}
    (hstep : ∀ k, a (k + 1) ≤ a k - b k) (hcov : ∀ k, (1 - lam) * a k ≤ b k) :
    ∀ k, a (k + 1) ≤ lam * a k := by
  intro k
  have h1 := hstep k
  have h2 := hcov k
  nlinarith only [h1, h2]

/-- **T3 convergence chain.** If each round covers at least a `(1-λ)` fraction of the remaining
uncovered vertices (`0 ≤ λ < 1`), then for any target `β > 0` some round count `T` brings the
uncovered set down to `≤ β · a 0` — the nibble reaches `(1-β)`-coverage. -/
theorem exists_uncovered_below {a b : ℕ → ℝ} {lam β : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hβ : 0 < β) (ha : ∀ k, 0 ≤ a k) (hstep : ∀ k, a (k + 1) ≤ a k - b k)
    (hcov : ∀ k, (1 - lam) * a k ≤ b k) :
    ∃ T, a T ≤ β * a 0 :=
  exists_round_count_below hlam0 hlam1 hβ ha (uncovered_step hstep hcov)

/-! ### Bounded-rounds versions (only require the per-round bound for `k < T`)

The unbounded `hcov : ∀ k, (1-λ)·a k ≤ b k` is TOO STRONG for the nibble: the per-round covering
fraction degrades (`d_k → 0`), so `(1-λ) ≤ frac_k` cannot hold for all `k`. These bounded variants
require the decrease/covering only for `k < T`, and take `T` with `λ^T ≤ β` as data — matching the
real nibble, where the covering holds while the residual is still near-regular (`k < T`). -/

/-- **Bounded geometric decay.** If `a (k+1) ≤ λ·a k` for `k < T`, then `a T ≤ λ^T · a 0`. -/
theorem geometric_decay_lt {a : ℕ → ℝ} {lam : ℝ} (hlam : 0 ≤ lam) :
    ∀ (T : ℕ), (∀ k, k < T → a (k + 1) ≤ lam * a k) → a T ≤ lam ^ T * a 0 := by
  intro T
  induction T with
  | zero => intro _; simp
  | succ T ih =>
      intro hstep
      have hstep' : ∀ k, k < T → a (k + 1) ≤ lam * a k :=
        fun k hk => hstep k (Nat.lt_succ_of_lt hk)
      calc a (T + 1) ≤ lam * a T := hstep T (Nat.lt_succ_self T)
        _ ≤ lam * (lam ^ T * a 0) := mul_le_mul_of_nonneg_left (ih hstep') hlam
        _ = lam ^ (T + 1) * a 0 := by ring

/-- **Bounded per-round decrease bridge.** As `uncovered_step`, but only for `k < T`. -/
theorem uncovered_step_lt {a b : ℕ → ℝ} {lam : ℝ} (T : ℕ)
    (hstep : ∀ k, k < T → a (k + 1) ≤ a k - b k)
    (hcov : ∀ k, k < T → (1 - lam) * a k ≤ b k) :
    ∀ k, k < T → a (k + 1) ≤ lam * a k := by
  intro k hk
  have h1 := hstep k hk
  have h2 := hcov k hk
  nlinarith only [h1, h2]

/-- **Bounded convergence.** For a fixed `T` with `λ^T ≤ β`, if each round `k < T` covers at least a
`(1-λ)` fraction, then `a T ≤ β · a 0`. -/
theorem uncovered_below_lt {a b : ℕ → ℝ} {lam β : ℝ} (hlam0 : 0 ≤ lam) (ha : ∀ k, 0 ≤ a k)
    (T : ℕ) (hT : lam ^ T ≤ β)
    (hstep : ∀ k, k < T → a (k + 1) ≤ a k - b k)
    (hcov : ∀ k, k < T → (1 - lam) * a k ≤ b k) :
    a T ≤ β * a 0 :=
  le_trans (geometric_decay_lt hlam0 T (uncovered_step_lt T hstep hcov))
    (mul_le_mul_of_nonneg_right hT (ha 0))

end LeanPool.AsymptoticTrianglePacking.Internal

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — discharge of the round-dependent iteration

Standalone, Mathlib-only. The sequence-indexed counterpart of
`LeanPool.AsymptoticTrianglePacking.Internal.Discharge`: with a *sequence*
of retention strategies (necessary by `LeanPool.AsymptoticTrianglePacking.Internal.total_gain_le`,
which caps the total coverage of any
single fixed strategy), each round `k` may cover a different fraction `1 - lam k` of the remaining
uncovered vertices, and the uncovered count after `T` rounds is controlled by the PRODUCT
`∏_{k<T} lam k` rather than by a power `lam ^ T`.

* `geometric_decay_prod_lt`, `uncovered_below_prod_lt` — convergence with round-dependent factors.
* `nibble_matching_card_of_oracle_seq_lt` — the covered-count bound from a bounded-rounds oracle.
* `exists_matching_of_oracle_seq_lt` — the `NibbleTheorem` per-instance conclusion.

Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open Finset

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-- **Convergence with round-dependent factors.**  If `a (k+1) ≤ lam k · a k` for every `k < T`,
then `a T ≤ (∏_{k<T} lam k) · a 0`. -/
theorem geometric_decay_prod_lt {a : ℕ → ℝ} {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) :
    ∀ (T : ℕ), (∀ k, k < T → a (k + 1) ≤ lam k * a k) →
      a T ≤ (∏ k ∈ Finset.range T, lam k) * a 0 := by
  intro T
  induction T with
  | zero => intro _; simp
  | succ T ih =>
      intro hstep
      have hstep' : ∀ k, k < T → a (k + 1) ≤ lam k * a k :=
        fun k hk => hstep k (Nat.lt_succ_of_lt hk)
      calc a (T + 1) ≤ lam T * a T := hstep T (Nat.lt_succ_self T)
        _ ≤ lam T * ((∏ k ∈ Finset.range T, lam k) * a 0) :=
            mul_le_mul_of_nonneg_left (ih hstep') (hlam T)
        _ = (∏ k ∈ Finset.range (T + 1), lam k) * a 0 := by
            rw [Finset.prod_range_succ]; ring

/-- **Bounded convergence with round-dependent factors.**  If round `k < T` decreases the uncovered
count by at least a `(1 - lam k)`-fraction, then `a T ≤ (∏_{k<T} lam k) · a 0 ≤ β · a 0`. -/
theorem uncovered_below_prod_lt {a b : ℕ → ℝ} {lam : ℕ → ℝ} {β : ℝ}
    (hlam0 : ∀ k, 0 ≤ lam k) (ha : ∀ k, 0 ≤ a k)
    (T : ℕ) (hT : (∏ k ∈ Finset.range T, lam k) ≤ β)
    (hstep : ∀ k, k < T → a (k + 1) ≤ a k - b k)
    (hcov : ∀ k, k < T → (1 - lam k) * a k ≤ b k) :
    a T ≤ β * a 0 := by
  have hdecay : ∀ k, k < T → a (k + 1) ≤ lam k * a k := by
    intro k hk
    have h1 := hstep k hk
    have h2 := hcov k hk
    linarith only [h1, h2]
  exact le_trans (geometric_decay_prod_lt hlam0 T hdecay)
    (mul_le_mul_of_nonneg_right hT (ha 0))

end LeanPool.AsymptoticTrianglePacking.Internal

namespace Hypergraph

open LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V]

/-- **Round-dependent discharge.**  With a sequence of retention strategies and a bounded-rounds
oracle — round `k < T` covers at least a `(1 - lam k)`-fraction of the vertices still uncovered —
the accumulated matching after `T` rounds covers at least `(1-β)·|V|`, hence has size at least
`(1-β)·(|V|/r)`, provided `∏_{k<T} lam k ≤ β`. -/
theorem nibble_matching_card_of_oracle_seq_lt [Fintype V]
    {R : ℕ → Finset (Finset V) → Finset (Finset V)} (hR : ∀ k H', R k H' ⊆ H')
    {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r) (hr1 : 1 ≤ r)
    {lam : ℕ → ℝ} {β : ℝ} (hlam0 : ∀ k, 0 ≤ lam k) (T : ℕ)
    (hTβ : (∏ k ∈ Finset.range T, lam k) ≤ β)
    (horacle : ∀ k, k < T →
      (1 - lam k) * ((Fintype.card V : ℝ) - ((support (nibbleMatchingSeq R H k)).card : ℝ))
        ≤ ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ)) :
    (1 - β) * ((Fintype.card V : ℝ) / r) ≤ ((nibbleMatchingSeq R H T).card : ℝ) := by
  have hann : ∀ k, 0 ≤ (Fintype.card V : ℝ) - ((support (nibbleMatchingSeq R H k)).card : ℝ) := by
    intro k
    have h : ((support (nibbleMatchingSeq R H k)).card : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast Finset.card_le_univ _
    linarith
  have hstep : ∀ k, k < T →
      (Fintype.card V : ℝ) - ((support (nibbleMatchingSeq R H (k + 1))).card : ℝ)
        ≤ ((Fintype.card V : ℝ) - ((support (nibbleMatchingSeq R H k)).card : ℝ))
          - ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ) := by
    intro k _
    have hrec : ((support (nibbleMatchingSeq R H (k + 1))).card : ℝ)
        = ((support (nibbleMatchingSeq R H k)).card : ℝ)
          + ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ) := by
      exact_mod_cast nibbleMatchingSeq_support_card_succ hR H k
    linarith
  have hconv := uncovered_below_prod_lt hlam0 hann T hTβ hstep horacle
  have h0 : (support (nibbleMatchingSeq R H 0)).card = 0 := by
    simp [show nibbleMatchingSeq R H 0 = (∅ : Finset (Finset V)) from rfl, support,
      Finset.biUnion_empty]
  rw [h0] at hconv
  simp only [Nat.cast_zero, sub_zero] at hconv
  have hM : IsMatching H (nibbleMatchingSeq R H T) := nibbleMatchingSeq_isMatching hR H T
  have hsc : ((support (nibbleMatchingSeq R H T)).card : ℝ)
      = (r : ℝ) * ((nibbleMatchingSeq R H T).card : ℝ) := by
    exact_mod_cast matching_support_card hr hM
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  rw [← mul_div_assoc, div_le_iff₀ hrpos]
  linarith only [hconv, hsc]

/-- **Round-dependent oracle ⇒ the `NibbleTheorem` per-instance conclusion.** -/
theorem exists_matching_of_oracle_seq_lt [Fintype V]
    {R : ℕ → Finset (Finset V) → Finset (Finset V)} (hR : ∀ k H', R k H' ⊆ H')
    {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r) (hr1 : 1 ≤ r)
    {lam : ℕ → ℝ} {β : ℝ} (hlam0 : ∀ k, 0 ≤ lam k) (T : ℕ)
    (hTβ : (∏ k ∈ Finset.range T, lam k) ≤ β)
    (horacle : ∀ k, k < T →
      (1 - lam k) * ((Fintype.card V : ℝ) - ((support (nibbleMatchingSeq R H k)).card : ℝ))
        ≤ ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ)) :
    ∃ M : Finset (Finset V), IsMatching H M
      ∧ (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ) :=
  ⟨nibbleMatchingSeq R H T, nibbleMatchingSeq_isMatching hR H T,
    nibble_matching_card_of_oracle_seq_lt hR hr hr1 hlam0 T hTβ horacle⟩

end Hypergraph

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — from a per-round covering oracle to the adaptive
strategy sequence

Standalone (imports only `LeanPool.AsymptoticTrianglePacking.Internal.IterationSeq` /
`LeanPool.AsymptoticTrianglePacking.Internal.DischargeSeq` and Mathlib).

The corrected outer interface of the nibble
(`LeanPool.AsymptoticTrianglePacking.Internal.AdaptiveOracleExistsCeil`) asks for a *strategy
sequence* `R : ℕ → Finset (Finset V) → Finset (Finset V)`, per-round rates `lam : ℕ → ℝ` with
`∏_{k<T} lam k ≤ β`, and the per-round covering demand

  `(1 - lam k) · (#uncovered after k rounds) ≤ #(vertices covered in round k)`.

This file performs the two *architectural* reductions of that demand, both placeholder-free:

* `exists_adaptive_rates_of_uncovered_le` — the rate sequence `lam` is never an obstruction: for ANY
  strategy sequence `R`, the rates `lam k := u (k+1) / u k` (with `u k` the uncovered count after
  `k` rounds) satisfy the per-round demand *with equality*, and their product telescopes to
  `u T / u 0`.  Hence the whole outer demand is EQUIVALENT to the single scalar statement
  `u T ≤ β · |V|` — "after `T` rounds at most a `β`-fraction of the vertices is still uncovered".

* `exists_uncovered_le_of_roundOracle` — that scalar statement follows from a purely *one-round*
  oracle `HasRoundOracle H c β`: an invariant `Inv` on (residual hypergraph, covered set) pairs
  which
  holds initially and, as long as more than a `β`-fraction of the vertices is uncovered, can be
  advanced by one round that covers at least a `c`-fraction of the still-uncovered vertices.  The
  strategy sequence is built explicitly (`oracleStrategy`, `oracleStateSeq`) so that no
  well-founded recursion or dependent choice over the history is needed.

Combining the two gives `exists_adaptive_strategy_of_roundOracle`, which is exactly the per-instance
conclusion of `AdaptiveOracleExistsCeil`.  The converse `hasRoundOracle_of_matching` shows the
one-round oracle is not a strengthening: it already follows from the existence of one large
matching.

Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V]

/-- A matching is its own round matching: every retained edge is isolated. -/
theorem roundMatching_eq_of_isMatching {H M : Finset (Finset V)} (hM : IsMatching H M) :
    roundMatching M = M := by
  ext e
  refine ⟨fun he => roundMatching_subset M he, fun he => ?_⟩
  rw [roundMatching, Finset.mem_filter]
  exact ⟨he, fun f hf hfe => hM.disjoint e he f hf (fun h => hfe h.symm)⟩

/-! ## The uncovered count -/

section Uncovered

variable [Fintype V]

/-- The number of vertices still uncovered after `k` rounds of the strategy sequence `R`. -/
noncomputable def uncoveredCount (R : ℕ → Finset (Finset V) → Finset (Finset V))
    (H : Finset (Finset V)) (k : ℕ) : ℝ :=
  (Fintype.card V : ℝ) - ((support (nibbleMatchingSeq R H k)).card : ℝ)

theorem uncoveredCount_nonneg (R : ℕ → Finset (Finset V) → Finset (Finset V))
    (H : Finset (Finset V)) (k : ℕ) : 0 ≤ uncoveredCount R H k := by
  have h : ((support (nibbleMatchingSeq R H k)).card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Finset.card_le_univ _
  simp only [uncoveredCount]; linarith

@[simp] theorem uncoveredCount_zero (R : ℕ → Finset (Finset V) → Finset (Finset V))
    (H : Finset (Finset V)) : uncoveredCount R H 0 = (Fintype.card V : ℝ) := by
  simp [uncoveredCount, show nibbleMatchingSeq R H 0 = (∅ : Finset (Finset V)) from rfl,
    support, Finset.biUnion_empty]

/-- One round decreases the uncovered count by exactly the number of vertices it covers. -/
theorem uncoveredCount_succ {R : ℕ → Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ k H', R k H' ⊆ H') (H : Finset (Finset V)) (k : ℕ) :
    uncoveredCount R H (k + 1)
      = uncoveredCount R H k
        - ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ) := by
  have h : ((support (nibbleMatchingSeq R H (k + 1))).card : ℝ)
      = ((support (nibbleMatchingSeq R H k)).card : ℝ)
        + ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ) := by
    exact_mod_cast nibbleMatchingSeq_support_card_succ hR H k
  simp only [uncoveredCount, h]; ring

theorem uncoveredCount_antitone {R : ℕ → Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ k H', R k H' ⊆ H') (H : Finset (Finset V)) (k : ℕ) :
    uncoveredCount R H (k + 1) ≤ uncoveredCount R H k := by
  rw [uncoveredCount_succ hR H k]
  have : (0 : ℝ) ≤ ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ) :=
    Nat.cast_nonneg _
  linarith

end Uncovered

/-! ## The rate sequence is never an obstruction

For ANY strategy sequence, the *canonical* rates `lam k = u (k+1) / u k` meet the per-round covering
demand with equality and telescope. So the entire outer-loop demand of `AdaptiveOracleExistsCeil`
reduces to the single scalar statement `u T ≤ β · |V|`. -/

section Rates

variable [Fintype V]

/-- The canonical per-round rate of a strategy sequence: the ratio of consecutive uncovered counts
(with the convention `0` once everything is covered). -/
noncomputable def canonicalRate (R : ℕ → Finset (Finset V) → Finset (Finset V))
    (H : Finset (Finset V)) (k : ℕ) : ℝ :=
  if uncoveredCount R H k = 0 then 0 else uncoveredCount R H (k + 1) / uncoveredCount R H k

theorem canonicalRate_nonneg (R : ℕ → Finset (Finset V) → Finset (Finset V))
    (H : Finset (Finset V)) (k : ℕ) :
    0 ≤ canonicalRate R H k := by
  simp only [canonicalRate]
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (uncoveredCount_nonneg R H (k + 1))
      (uncoveredCount_nonneg R H k)

/-- The canonical rates telescope exactly. -/
theorem prod_canonicalRate {R : ℕ → Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ k H', R k H' ⊆ H') (H : Finset (Finset V)) (n : ℕ) :
    (∏ k ∈ Finset.range n, canonicalRate R H k) * uncoveredCount R H 0
      = uncoveredCount R H n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ]
      have hstep : (∏ k ∈ Finset.range n, canonicalRate R H k) * canonicalRate R H n
            * uncoveredCount R H 0
          = uncoveredCount R H n * canonicalRate R H n := by
        rw [mul_right_comm, ih]
      rw [hstep]
      simp only [canonicalRate]
      split_ifs with h
      · have h1 : uncoveredCount R H (n + 1) ≤ 0 := by
          have := uncoveredCount_antitone hR H n; linarith
        have h2 : 0 ≤ uncoveredCount R H (n + 1) := uncoveredCount_nonneg R H (n + 1)
        rw [h]; linarith
      · field_simp

/-- The canonical rates satisfy the per-round covering demand — with equality when some vertex is
still uncovered. -/
theorem canonicalRate_cover {R : ℕ → Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ k H', R k H' ⊆ H') (H : Finset (Finset V)) (k : ℕ) :
    (1 - canonicalRate R H k) * uncoveredCount R H k
      ≤ ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ) := by
  have hsucc := uncoveredCount_succ hR H k
  simp only [canonicalRate]
  split_ifs with h
  · rw [h]; simp
  · have : (1 - uncoveredCount R H (k + 1) / uncoveredCount R H k) * uncoveredCount R H k
        = uncoveredCount R H k - uncoveredCount R H (k + 1) := by
      field_simp
    rw [this]; linarith only [hsucc]

/-- **The rate sequence is never an obstruction.** If after `T` rounds at most a `β`-fraction of the
vertices is uncovered, then the canonical rates witness the full per-round demand of
`AdaptiveOracleExistsCeil`. -/
theorem exists_adaptive_rates_of_uncovered_le
    {R : ℕ → Finset (Finset V) → Finset (Finset V)} (hR : ∀ k H', R k H' ⊆ H')
    (H : Finset (Finset V)) {β : ℝ} (hβ : 0 ≤ β) (T : ℕ)
    (hT : uncoveredCount R H T ≤ β * (Fintype.card V : ℝ)) :
    ∃ (lam : ℕ → ℝ) (T' : ℕ), (∀ k, 0 ≤ lam k) ∧
      (∏ k ∈ Finset.range T', lam k) ≤ β ∧
      (∀ k, k < T' →
        (1 - lam k) * ((Fintype.card V : ℝ) - ((support (nibbleMatchingSeq R H k)).card : ℝ))
          ≤ ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ)) := by
  refine ⟨canonicalRate R H, T + 1, canonicalRate_nonneg R H, ?_,
    fun k _ => canonicalRate_cover hR H k⟩
  have hprod := prod_canonicalRate hR H (T + 1)
  rw [uncoveredCount_zero] at hprod
  have hTle : uncoveredCount R H (T + 1) ≤ β * (Fintype.card V : ℝ) :=
    le_trans (uncoveredCount_antitone hR H T) hT
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hV | hV
  · -- no vertices: every rate is `0`, and the product over a nonempty range vanishes
    have h0 : uncoveredCount R H 0 = 0 := by rw [uncoveredCount_zero, hV]; norm_num
    have : canonicalRate R H 0 = 0 := by simp [canonicalRate, h0]
    have hmem : (0 : ℕ) ∈ Finset.range (T + 1) := Finset.mem_range.mpr (Nat.succ_pos T)
    rw [Finset.prod_eq_zero hmem this]
    exact hβ
  · have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hV
    have hmul : (∏ k ∈ Finset.range (T + 1), canonicalRate R H k) * (Fintype.card V : ℝ)
        ≤ β * (Fintype.card V : ℝ) := by rw [hprod]; exact hTle
    exact le_of_mul_le_mul_right hmul hVpos

end Rates

/-! ## The explicit strategy sequence built from a one-round oracle -/

section Oracle

/-- The state (accumulated matching, current residual) after `k` rounds of the *state-indexed*
oracle `G`, which chooses the retained set from the current residual and the current covered set. -/
def oracleStateSeq (G : Finset (Finset V) → Finset V → Finset (Finset V))
    (H : Finset (Finset V)) : ℕ → Finset (Finset V) × Finset (Finset V)
  | 0 => (∅, H)
  | (k + 1) =>
      ((oracleStateSeq G H k).1 ∪
          roundMatching (G (oracleStateSeq G H k).2 (support (oracleStateSeq G H k).1)),
        Hypergraph.residual (oracleStateSeq G H k).2
          (G (oracleStateSeq G H k).2 (support (oracleStateSeq G H k).1)))

/-- The strategy sequence induced by a state-indexed oracle: in round `k` it feeds the oracle the
covered set reached after `k` rounds.  This is a *bona fide* `ℕ → Finset (Finset V) →
Finset (Finset V)` — no dependence on the run-time history is needed, because the history is a
function of `G` and `H` alone. -/
def oracleStrategy (G : Finset (Finset V) → Finset V → Finset (Finset V))
    (H : Finset (Finset V)) : ℕ → Finset (Finset V) → Finset (Finset V) :=
  fun k H' => G H' (support (oracleStateSeq G H k).1)

theorem oracleStrategy_subset {G : Finset (Finset V) → Finset V → Finset (Finset V)}
    (hG : ∀ H' S, G H' S ⊆ H') (H : Finset (Finset V)) (k : ℕ) (H' : Finset (Finset V)) :
    oracleStrategy G H k H' ⊆ H' := hG _ _

/-- The nibble iteration of `oracleStrategy G H` is exactly the oracle state sequence. -/
theorem nibbleIterSeq_oracleStrategy (G : Finset (Finset V) → Finset V → Finset (Finset V))
    (H : Finset (Finset V)) :
    ∀ k, nibbleIterSeq (oracleStrategy G H) H k = oracleStateSeq G H k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((nibbleIterSeq (oracleStrategy G H) H k).1
              ∪ roundMatching (oracleStrategy G H k (nibbleIterSeq (oracleStrategy G H) H k).2),
            Hypergraph.residual (nibbleIterSeq (oracleStrategy G H) H k).2
              (oracleStrategy G H k (nibbleIterSeq (oracleStrategy G H) H k).2))
          = oracleStateSeq G H (k + 1)
      rw [ih]
      rfl

theorem nibbleMatchingSeq_oracleStrategy (G : Finset (Finset V) → Finset V → Finset (Finset V))
    (H : Finset (Finset V)) (k : ℕ) :
    nibbleMatchingSeq (oracleStrategy G H) H k = (oracleStateSeq G H k).1 := by
  rw [nibbleMatchingSeq, nibbleIterSeq_oracleStrategy]

theorem nibbleResidualSeq_oracleStrategy (G : Finset (Finset V) → Finset V → Finset (Finset V))
    (H : Finset (Finset V)) (k : ℕ) :
    nibbleResidualSeq (oracleStrategy G H) H k = (oracleStateSeq G H k).2 := by
  rw [nibbleResidualSeq, nibbleIterSeq_oracleStrategy]

end Oracle

/-! ## The one-round oracle -/

section RoundOracle

variable [Fintype V]

/-- **The one-round covering oracle.**  An invariant `Inv` on pairs (current residual hypergraph,
currently covered set) which

* holds at the start, and
* as long as more than a `β`-fraction of the vertices is still uncovered, can be advanced by ONE
  round: a retained set `R' ⊆ H'` whose round matching covers at least a `c`-fraction of the
  still-uncovered vertices and re-establishes the invariant.

This is the per-round (non-iterated) content of the nibble outer loop. -/
@[expose] def HasRoundOracle (H : Finset (Finset V)) (c β : ℝ) : Prop :=
  ∃ Inv : Finset (Finset V) → Finset V → Prop,
    Inv H ∅ ∧
    ∀ (H' : Finset (Finset V)) (S : Finset V), Inv H' S →
      β * (Fintype.card V : ℝ) < (Fintype.card V : ℝ) - (S.card : ℝ) →
      ∃ R' : Finset (Finset V), R' ⊆ H' ∧
        Inv (Hypergraph.residual H' R') (S ∪ support (roundMatching R')) ∧
        c * ((Fintype.card V : ℝ) - (S.card : ℝ))
          ≤ ((support (roundMatching R')).card : ℝ)

/-- **Iterating the one-round oracle.**  A per-round oracle covering a `c`-fraction of the uncovered
set drives the uncovered count below `β·|V|` in a bounded number of rounds. -/
theorem exists_uncovered_le_of_roundOracle (H : Finset (Finset V)) {c β : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β) (hO : HasRoundOracle H c β) :
    ∃ (R : ℕ → Finset (Finset V) → Finset (Finset V)) (T : ℕ), (∀ k H', R k H' ⊆ H') ∧
      uncoveredCount R H T ≤ β * (Fintype.card V : ℝ) := by
  classical
  obtain ⟨Inv, hInv0, hstep⟩ := hO
  choose! g hgsub hgInv hgcov using hstep
  set G : Finset (Finset V) → Finset V → Finset (Finset V) := fun H' S => g H' S ∩ H' with hGdef
  have hGsub : ∀ H' S, G H' S ⊆ H' := fun H' S => Finset.inter_subset_right
  have hGeq : ∀ (H' : Finset (Finset V)) (S : Finset V), Inv H' S →
      β * (Fintype.card V : ℝ) < (Fintype.card V : ℝ) - (S.card : ℝ) → G H' S = g H' S := by
    intro H' S hInv hlt
    exact Finset.inter_eq_left.mpr (hgsub H' S hInv hlt)
  set R := oracleStrategy G H with hRdef
  have hRsub : ∀ k H', R k H' ⊆ H' := fun k H' => oracleStrategy_subset hGsub H k H'
  -- the round-`k` retained set, in terms of the state
  have hround : ∀ k, R k (nibbleResidualSeq R H k)
      = G (nibbleResidualSeq R H k) (support (nibbleMatchingSeq R H k)) := by
    intro k
    simp only [hRdef, oracleStrategy, nibbleMatchingSeq_oracleStrategy]
  -- the main induction
  have key : ∀ k, uncoveredCount R H k ≤ β * (Fintype.card V : ℝ) ∨
      (Inv (nibbleResidualSeq R H k) (support (nibbleMatchingSeq R H k)) ∧
        uncoveredCount R H k ≤ (1 - c) ^ k * (Fintype.card V : ℝ)) := by
    intro k
    induction k with
    | zero =>
        right
        refine ⟨?_, by simp⟩
        have h1 : nibbleResidualSeq R H 0 = H := rfl
        have h2 : support (nibbleMatchingSeq R H 0) = (∅ : Finset V) := by
          simp [show nibbleMatchingSeq R H 0 = (∅ : Finset (Finset V)) from rfl, support,
            Finset.biUnion_empty]
        rw [h1, h2]; exact hInv0
    | succ k ih =>
        rcases ih with hdone | ⟨hInv, hbd⟩
        · exact Or.inl (le_trans (uncoveredCount_antitone hRsub H k) hdone)
        · by_cases hstop : uncoveredCount R H k ≤ β * (Fintype.card V : ℝ)
          · exact Or.inl (le_trans (uncoveredCount_antitone hRsub H k) hstop)
          · push Not at hstop
            have hlt : β * (Fintype.card V : ℝ)
                < (Fintype.card V : ℝ) - ((support (nibbleMatchingSeq R H k)).card : ℝ) := hstop
            have hgs := hgsub _ _ hInv hlt
            have hgi := hgInv _ _ hInv hlt
            have hgc := hgcov _ _ hInv hlt
            have heq : R k (nibbleResidualSeq R H k)
                = g (nibbleResidualSeq R H k) (support (nibbleMatchingSeq R H k)) := by
              rw [hround k, hGeq _ _ hInv hlt]
            right
            constructor
            · have hres : nibbleResidualSeq R H (k + 1)
                  = Hypergraph.residual (nibbleResidualSeq R H k) (R k (nibbleResidualSeq R H k)) :=
                rfl
              have hmat : support (nibbleMatchingSeq R H (k + 1))
                  = support (nibbleMatchingSeq R H k)
                    ∪ support (roundMatching (R k (nibbleResidualSeq R H k))) := by
                change support (nibbleMatchingSeq R H k
                    ∪ roundMatching (R k (nibbleResidualSeq R H k))) = _
                exact support_union _ _
              rw [hres, hmat, heq]
              exact hgi
            · have hcov : c * uncoveredCount R H k
                  ≤ ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ) := by
                rw [heq]; exact hgc
              have hsucc := uncoveredCount_succ hRsub H k
              have hstepbd : uncoveredCount R H (k + 1) ≤ (1 - c) * uncoveredCount R H k := by
                rw [hsucc]; linarith
              have hpow : (1 - c) * uncoveredCount R H k
                  ≤ (1 - c) * ((1 - c) ^ k * (Fintype.card V : ℝ)) :=
                mul_le_mul_of_nonneg_left hbd (by linarith)
              calc uncoveredCount R H (k + 1) ≤ (1 - c) * uncoveredCount R H k := hstepbd
                _ ≤ (1 - c) * ((1 - c) ^ k * (Fintype.card V : ℝ)) := hpow
                _ = (1 - c) ^ (k + 1) * (Fintype.card V : ℝ) := by ring
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hβ0 (show (1 : ℝ) - c < 1 by linarith)
  refine ⟨R, T, hRsub, ?_⟩
  rcases key T with h | ⟨_, h⟩
  · exact h
  · have hVnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    have : (1 - c) ^ T * (Fintype.card V : ℝ) ≤ β * (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_right hT.le hVnn
    linarith

/-- **The per-round oracle produces the full adaptive strategy sequence.**  This is exactly the
per-instance conclusion demanded by
`LeanPool.AsymptoticTrianglePacking.Internal.AdaptiveOracleExistsCeil`. -/
theorem exists_adaptive_strategy_of_roundOracle (H : Finset (Finset V)) {c β : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β) (hO : HasRoundOracle H c β) :
    ∃ (R : ℕ → Finset (Finset V) → Finset (Finset V)) (lam : ℕ → ℝ) (T : ℕ),
      (∀ k H', R k H' ⊆ H') ∧ (∀ k, 0 ≤ lam k) ∧
      (∏ k ∈ Finset.range T, lam k) ≤ β ∧
      (∀ k, k < T →
        (1 - lam k) * ((Fintype.card V : ℝ) - ((support (nibbleMatchingSeq R H k)).card : ℝ))
          ≤ ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ)) := by
  obtain ⟨R, T, hRsub, hT⟩ := exists_uncovered_le_of_roundOracle H hc0 hc1 hβ0 hO
  obtain ⟨lam, T', hlam0, hprod, hcov⟩ :=
    exists_adaptive_rates_of_uncovered_le hRsub H hβ0.le T hT
  exact ⟨R, lam, T', hRsub, hlam0, hprod, hcov⟩

/-- **Round oracle from a scheduled invariant.**  In practice the nibble invariant is not preserved
by an unbounded number of rounds: the degree scale, the regularity slack and the exceptional set all
degrade from round to round, and the schedule is only good for `T` rounds.  This lemma performs the
bookkeeping: an invariant *indexed by the round counter*, preserved for `T` rounds, each round
covering a `c`-fraction of the uncovered set, already yields a `HasRoundOracle` — because after `T`
rounds fewer than a `β`-fraction of the vertices is left, so the oracle is never asked to step
again.  The hypothesis `hdisj` (edges of the current residual avoid the covered set) is the standing
invariant of the nibble iteration (`nibbleResidualSeq_disjoint_support`). -/
theorem hasRoundOracle_of_scheduled_invariant (H : Finset (Finset V)) {c β : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (T : ℕ) (hT : (1 - c) ^ T ≤ β)
    (P : ℕ → Finset (Finset V) → Finset V → Prop)
    (hP0 : P 0 H ∅)
    (hdisj : ∀ (j : ℕ) (H' : Finset (Finset V)) (S : Finset V), P j H' S →
      ∀ e ∈ H', Disjoint e S)
    (hstep : ∀ j, j < T → ∀ (H' : Finset (Finset V)) (S : Finset V), P j H' S →
      β * (Fintype.card V : ℝ) < (Fintype.card V : ℝ) - (S.card : ℝ) →
      ∃ R' : Finset (Finset V), R' ⊆ H' ∧
        P (j + 1) (Hypergraph.residual H' R') (S ∪ support (roundMatching R')) ∧
        c * ((Fintype.card V : ℝ) - (S.card : ℝ))
          ≤ ((support (roundMatching R')).card : ℝ)) :
    HasRoundOracle H c β := by
  classical
  have hNnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  refine ⟨fun H' S => ∃ j, P j H' S ∧
    ((Fintype.card V : ℝ) - (S.card : ℝ)) ≤ (1 - c) ^ j * (Fintype.card V : ℝ), ⟨0, hP0, ?_⟩, ?_⟩
  · simp
  · rintro H' S ⟨j, hPj, hdec⟩ hlt
    have hjT : j < T := by
      by_contra hge
      push Not at hge
      have hpow : (1 - c) ^ j ≤ (1 - c) ^ T :=
        pow_le_pow_of_le_one (by linarith) (by linarith) hge
      have : (Fintype.card V : ℝ) - (S.card : ℝ) ≤ β * (Fintype.card V : ℝ) :=
        le_trans hdec (le_trans (mul_le_mul_of_nonneg_right hpow hNnn)
          (mul_le_mul_of_nonneg_right hT hNnn))
      linarith
    obtain ⟨R', hR'sub, hP', hcov⟩ := hstep j hjT H' S hPj hlt
    refine ⟨R', hR'sub, ⟨j + 1, hP', ?_⟩, hcov⟩
    have hXdisj : Disjoint S (support (roundMatching R')) := by
      rw [Finset.disjoint_right]
      intro x hx hxS
      rw [support, Finset.mem_biUnion] at hx
      obtain ⟨e, he, hxe⟩ := hx
      exact (Finset.disjoint_left.mp
        (hdisj j H' S hPj e (hR'sub (roundMatching_subset _ he))) hxe) hxS
    have hcard : ((S ∪ support (roundMatching R')).card : ℝ)
        = (S.card : ℝ) + ((support (roundMatching R')).card : ℝ) := by
      rw [Finset.card_union_of_disjoint hXdisj]; push_cast; ring
    rw [hcard]
    have h1 : (Fintype.card V : ℝ) - (S.card : ℝ)
        - ((support (roundMatching R')).card : ℝ)
        ≤ (1 - c) * ((Fintype.card V : ℝ) - (S.card : ℝ)) := by linarith
    calc (Fintype.card V : ℝ) - ((S.card : ℝ) + ((support (roundMatching R')).card : ℝ))
        = (Fintype.card V : ℝ) - (S.card : ℝ)
            - ((support (roundMatching R')).card : ℝ) := by ring
      _ ≤ (1 - c) * ((Fintype.card V : ℝ) - (S.card : ℝ)) := h1
      _ ≤ (1 - c) * ((1 - c) ^ j * (Fintype.card V : ℝ)) :=
          mul_le_mul_of_nonneg_left hdec (by linarith)
      _ = (1 - c) ^ (j + 1) * (Fintype.card V : ℝ) := by ring

/-! ### Bridges to the hypergraph bricks

The two elementary conversions a concrete round oracle has to perform: from a lower bound on the
round matching's *cardinality* to the covering demand (via `r`-uniformity), and from a set of
high-degree vertices to a lower bound on the number of edges (handshake). -/

omit [Fintype V] in
/-- **Covering demand from the round matching's cardinality.**  In an `r`-uniform hypergraph the
round matching covers exactly `r` times its cardinality, so a cardinality bound is a covering
bound. -/
theorem round_cover_of_matching_card {H' R' : Finset (Finset V)} {r : ℕ} {c U : ℝ}
    (huni : IsUniform H' r) (hR' : R' ⊆ H')
    (h : c * U ≤ (r : ℝ) * ((roundMatching R').card : ℝ)) :
    c * U ≤ ((support (roundMatching R')).card : ℝ) := by
  have hM : IsMatching H' (roundMatching R') := roundMatching_isMatching hR'
  have hsc : ((support (roundMatching R')).card : ℝ) = (r : ℝ) * ((roundMatching R').card : ℝ) := by
    exact_mod_cast matching_support_card huni hM
  rw [hsc]; exact h

omit [Fintype V] in
/-- **Handshake lower bound on the edge count.**  Any set `A` of vertices of degree at least `δ`
forces `δ · |A| ≤ r · |H|`. -/
theorem card_mul_le_of_degree_ge [Finite V] {H : Finset (Finset V)} {r : ℕ} (huni : IsUniform H r)
    (A : Finset V) {δ : ℝ} (hA : ∀ v ∈ A, δ ≤ (degree H v : ℝ)) :
    δ * (A.card : ℝ) ≤ (r : ℝ) * (H.card : ℝ) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  have hsum : (∑ v : V, (degree H v : ℝ)) = (r : ℝ) * (H.card : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (sum_degree H huni)
  have h1 : δ * (A.card : ℝ) ≤ ∑ v ∈ A, (degree H v : ℝ) := by
    rw [mul_comm]
    simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hA
  have h2 : (∑ v ∈ A, (degree H v : ℝ)) ≤ ∑ v : V, (degree H v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      (fun v _ _ => Nat.cast_nonneg _)
  rw [← hsum]
  linarith

omit [Fintype V] in
/-- **The covering demand of `HasRoundOracle`, from the standard one-round output.**  This is the
last bridge a concrete round oracle has to cross.  The nibble bricks deliver a round matching of
cardinality at least `γ·|H'|` (with `γ = p·(1-p)^{rΔ}` minus the bad-event penalty); the residual
near-regularity delivers a set `A` of vertices of degree at least `δ` in `H'`; and the exceptional
(dead) vertices are at most `m`. Then the round covers at least `γ·δ·(U - m)` vertices, where `U` is
the number of still-uncovered vertices.  Handshake plus `r`-uniformity, nothing else. -/
theorem round_cover_demand_of_gain [Finite V] {H' R' : Finset (Finset V)} {r : ℕ} {γ δ U m : ℝ}
    (huni : IsUniform H' r) (hR' : R' ⊆ H') (A : Finset V)
    (hA : ∀ v ∈ A, δ ≤ (degree H' v : ℝ)) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hgain : γ * (H'.card : ℝ) ≤ ((roundMatching R').card : ℝ))
    (hAU : U - m ≤ (A.card : ℝ)) :
    γ * δ * (U - m) ≤ ((support (roundMatching R')).card : ℝ) := by
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have hhand : δ * (A.card : ℝ) ≤ (r : ℝ) * (H'.card : ℝ) :=
    card_mul_le_of_degree_ge huni A hA
  have h1 : δ * (U - m) ≤ δ * (A.card : ℝ) := mul_le_mul_of_nonneg_left hAU hδ
  have h2 : γ * (δ * (U - m)) ≤ γ * ((r : ℝ) * (H'.card : ℝ)) :=
    mul_le_mul_of_nonneg_left (le_trans h1 hhand) hγ
  have h3 : (r : ℝ) * (γ * (H'.card : ℝ)) ≤ (r : ℝ) * ((roundMatching R').card : ℝ) :=
    mul_le_mul_of_nonneg_left hgain hrnn
  refine round_cover_of_matching_card huni hR' ?_
  calc γ * δ * (U - m) = γ * (δ * (U - m)) := by ring
    _ ≤ γ * ((r : ℝ) * (H'.card : ℝ)) := h2
    _ = (r : ℝ) * (γ * (H'.card : ℝ)) := by ring
    _ ≤ (r : ℝ) * ((roundMatching R').card : ℝ) := h3

/-- **The one-round oracle is not a strengthening.**  A single matching covering a `(1-β)`-fraction
of the vertices already realises a one-round oracle with `c = 1 - β`. -/
theorem hasRoundOracle_of_matching (H : Finset (Finset V)) {β : ℝ}
    {M : Finset (Finset V)} (hM : IsMatching H M)
    (hcard : (1 - β) * (Fintype.card V : ℝ) ≤ ((support M).card : ℝ)) :
    HasRoundOracle H (1 - β) β := by
  classical
  refine ⟨fun H' S => (S = ∅ ∧ H' = H) ∨
    ((Fintype.card V : ℝ) - (S.card : ℝ) ≤ β * (Fintype.card V : ℝ)), Or.inl ⟨rfl, rfl⟩, ?_⟩
  rintro H' S (⟨hS, hH'⟩ | hsmall) hlt
  · subst hS
    refine ⟨M, by rw [hH']; exact hM.subset, ?_, ?_⟩
    · right
      rw [roundMatching_eq_of_isMatching hM]
      have hcard' : ((∅ ∪ support M : Finset V).card : ℝ) = ((support M).card : ℝ) := by simp
      rw [hcard']
      linarith
    · rw [roundMatching_eq_of_isMatching hM]
      simpa using hcard
  · exact absurd hsmall (not_le.mpr hlt)

end RoundOracle

end LeanPool.AsymptoticTrianglePacking.Internal

end


/-! # Ceiling-carrying oracle interface

This module contains the interface and deterministic assembly shared by the
tight-band nibble proof.  It deliberately contains no historical majority-only
or round-oracle development: the global degree ceiling is part of every input.
-/

public section

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-- The adaptive ceiling oracle obtained by iterating a one-round oracle. -/
def AdaptiveOracleExistsCeil : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β →
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ),
        0 < d → d₀ ≤ d → IsUniform H r → NearlyRegularMost H d μ η →
          CodegreeBounded H (μ * d) →
            (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
              ∃ (R : ℕ → Finset (Finset V) → Finset (Finset V)) (lam : ℕ → ℝ)
                (T : ℕ),
                (∀ k H', R k H' ⊆ H') ∧ (∀ k, 0 ≤ lam k) ∧
                  (∏ k ∈ Finset.range T, lam k) ≤ β ∧
                    (∀ k, k < T →
                      (1 - lam k) *
                          ((Fintype.card V : ℝ) -
                            ((support (nibbleMatchingSeq R H k)).card : ℝ)) ≤
                        ((support (roundMatching
                          (R k (nibbleResidualSeq R H k)))).card : ℝ))

/-- The ceiling interface follows from its adaptive oracle. -/
theorem nibbleTheoremMostCeil_of_adaptiveOracleCeil (h : AdaptiveOracleExistsCeil) :
    NibbleTheoremMostCeil := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hOracle⟩ := h r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd₀ hUniform hRegular hCodegree hCeiling
  obtain ⟨R, lam, T, hSubset, hNonnegative, hProduct, hRound⟩ :=
    hOracle H d hd hd₀ hUniform hRegular hCodegree hCeiling
  have hrOne : 1 ≤ r := le_trans (by norm_num) hr
  exact exists_matching_of_oracle_seq_lt hSubset hUniform hrOne hNonnegative T hProduct hRound

/-- A one-round ceiling oracle which can be iterated into the adaptive oracle. -/
@[expose] def RoundOracleExistsCeil : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β →
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∃ c : ℝ,
      0 < c ∧ c ≤ 1 ∧
        ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ),
          0 < d → d₀ ≤ d → IsUniform H r → NearlyRegularMost H d μ η →
            CodegreeBounded H (μ * d) →
              (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
                HasRoundOracle H c β

/-- Iterating the one-round ceiling oracle yields the adaptive ceiling oracle. -/
theorem adaptiveOracleExistsCeil_of_roundOracleCeil (h : RoundOracleExistsCeil) :
    AdaptiveOracleExistsCeil := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, c, hcPositive, hcOne, hOracle⟩ := h r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd₀ hUniform hRegular hCodegree hCeiling
  exact exists_adaptive_strategy_of_roundOracle H hcPositive hcOne hβ
    (hOracle H d hd hd₀ hUniform hRegular hCodegree hCeiling)

/-- The ceiling-carrying theorem entails the strict near-regular theorem. -/
theorem NibbleTheoremMostCeil.nibbleTheorem (h : NibbleTheoremMostCeil) : NibbleTheorem := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hMain⟩ := h r hr β hβ
  refine ⟨μ, hμ, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd₀ hUniform hRegular hCodegree
  exact hMain H d hd hd₀ hUniform (hRegular.nearlyRegularMost hη.le) hCodegree
    (fun x => (hRegular x).2)

end LeanPool.AsymptoticTrianglePacking.Internal

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the tight-band assembly: from one sharp round to the
LeanPool.AsymptoticTrianglePacking.Internal theorem

This file performs the ASSEMBLY of the LeanPool.AsymptoticTrianglePacking.Internal out of the
iterable single round
`LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundHyp`
(`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound`):

* `LeanPool.AsymptoticTrianglePacking.Internal.TightParams` — the schedule: the round rate `γ`, the
  relative tolerance `ε`, the per-round
  exceptional fraction `θ`, the initial exceptional fraction `η`, the number of rounds `T`, the
  degree band `[d·lo k, d·hi k]` after `k` rounds and the exceptional budget `sig k`, together with
  every inequality the iteration consumes.
* `LeanPool.AsymptoticTrianglePacking.Internal.roundOracle_of_sharpRound_params` — one round of the
  schedule: the tight-band invariant is
  re-established (band, global ceiling, codegree, exceptional budget) and a `γ/(16r)` fraction of
  the
  uncovered vertices is covered; iterated by
  `LeanPool.AsymptoticTrianglePacking.Internal.hasRoundOracle_of_scheduled_invariant`.
* `LeanPool.AsymptoticTrianglePacking.Internal.exists_tightParams` — the schedule exists for every
  `r ≥ 2` and `β ∈ (0,1)`.
* `LeanPool.AsymptoticTrianglePacking.Internal.roundOracleExistsCeil_of_sharpRound`,
  `LeanPool.AsymptoticTrianglePacking.Internal.nibbleTheoremMostCeil_of_sharpRound`,
  `LeanPool.AsymptoticTrianglePacking.Internal.nibbleTheoremMostCeilSized_of_sharpRound`,
  `LeanPool.AsymptoticTrianglePacking.Internal.nibbleTheorem_of_sharpRound` — the
  packaged conclusions.

The three mechanisms of the assembly are:

* **the band step** — the floor falls by at most `((r−1)/r)γΔ + εγΔ` and the ceiling by at least
  `((r−1)/r)γ(δ−lost)δ(1−γ)/Δ − εγΔ`, so a band of relative width `n` widens to `n(1 + 8((r−1)/r)γ)`
  while both ends fall by the factor `1 − ((r−1)/r)γ`;
* **the exceptional bookkeeping** — the vertices that leave the band (`B`), the vertices with too
  many edges into the exceptional set (`heavy`), the vertices that break the new ceiling (`Hi`,
  contained in `E ∪ B ∪ heavy`) and the vertices damaged by pruning `Hi` (`Dam`) are all counted by
  the deterministic estimate `LeanPool.AsymptoticTrianglePacking.Internal.card_heavyLoss_le`; the
  exceptional set therefore grows by a
  bounded factor `(2 + r/(εγ))²` per round, which the choice of `θ` absorbs;
* **the covering count** — the round covers a `γ/(8r)` fraction of the live set, which is at least
  half of the uncovered set as long as the exceptional set stays below `β|V|/2`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-! ## The schedule -/

/-- **The tight-band schedule.** All parameters of the `T`-round
LeanPool.AsymptoticTrianglePacking.Internal at uniformity `r` and target
`β`, with the inequalities the iteration consumes.  `lo k`, `hi k` are the degree band after `k`
rounds RELATIVE to the regular degree `d`, and `sig k` is the exceptional budget as a fraction of
`|V|`. -/
structure TightParams (r : ℕ) (β : ℝ) where
  /-- round rate -/
  gam : ℝ
  /-- relative band tolerance -/
  eps : ℝ
  /-- per-round exceptional fraction -/
  exc : ℝ
  /-- initial exceptional fraction -/
  eta : ℝ
  /-- initial relative band width -/
  wid : ℝ
  /-- a positive lower bound for the relative band floor -/
  lomin : ℝ
  /-- the number of rounds -/
  T : ℕ
  /-- relative degree floor after `k` rounds -/
  lo : ℕ → ℝ
  /-- relative degree ceiling after `k` rounds -/
  hi : ℕ → ℝ
  /-- exceptional budget after `k` rounds -/
  sig : ℕ → ℝ
  gam_pos : 0 < gam
  gam_le : gam ≤ 1 / 2
  eps_pos : 0 < eps
  eps_le : eps ≤ 1
  /-- the tolerance is at least twice the round rate; this is the regime in which the sharp round
  `LeanPool.AsymptoticTrianglePacking.Internal.sharpRoundFor_of_two_gamma_le_eps` is proved -/
  two_gam_le_eps : 2 * gam ≤ eps
  exc_pos : 0 < exc
  exc_le : exc ≤ 1
  eta_pos : 0 < eta
  wid_pos : 0 < wid
  lomin_pos : 0 < lomin
  lomin_le : ∀ k, k ≤ T → lomin ≤ lo k
  hi_le_two_lo : ∀ k, k ≤ T → hi k ≤ 2 * lo k
  lo_le_hi : ∀ k, k ≤ T → lo k ≤ hi k
  init_lo : lo 0 ≤ 1 - wid
  init_hi : 1 + wid ≤ hi 0
  step_lo : ∀ k, k < T →
    lo (k + 1) ≤ lo k - ((r : ℝ) - 1) / r * gam * hi k - 2 * eps * gam * hi k
  step_hi : ∀ k, k < T →
    hi k - ((r : ℝ) - 1) / r * gam * (lo k - eps * gam * hi k) * lo k * (1 - gam) / hi k
      + eps * gam * hi k ≤ hi (k + 1)
  sig_init : eta ≤ sig 0
  sig_step : ∀ k, k < T → (2 + (r : ℝ) / (eps * gam)) ^ 2 * (sig k + exc) ≤ sig (k + 1)
  sig_le : ∀ k, k ≤ T → sig k ≤ β / 2
  decay : (1 - gam / (16 * r)) ^ T ≤ β

/-! ## Elementary hypergraph bricks used by the step -/

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Pruning kills the degree of the pruned vertices. -/
theorem degree_prune_eq_zero {K : Finset (Finset V)} {B : Finset V} {v : V} (hv : v ∈ B) :
    degree (prune K B) v = 0 := by
  classical
  rw [degree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hve
  rw [prune, Finset.mem_filter] at he
  exact (Finset.disjoint_left.mp he.2 hve) hv

omit [Fintype V] in
/-- Degrees are monotone in the hypergraph. -/
theorem degree_mono {K K' : Finset (Finset V)} (h : K' ⊆ K) (v : V) :
    degree K' v ≤ degree K v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

omit [Fintype V] in
/-- Codegrees are monotone in the hypergraph. -/
theorem codegree_mono {K K' : Finset (Finset V)} (h : K' ⊆ K) (x y : V) :
    codegree K' x y ≤ codegree K x y :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

omit [Fintype V] in
/-- Only the part of the deleted set that the edges actually meet matters. -/
theorem lostDegree_union_of_disjoint {K : Finset (Finset V)} {S E : Finset V}
    (hS : ∀ e ∈ K, Disjoint e S) (v : V) :
    lostDegree K (S ∪ E) v = lostDegree K E v := by
  classical
  unfold lostDegree
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro e he
  constructor
  · rintro ⟨hve, hne⟩
    refine ⟨hve, fun hd => hne ?_⟩
    rw [Finset.disjoint_union_right]
    exact ⟨hS e he, hd⟩
  · rintro ⟨hve, hne⟩
    refine ⟨hve, fun hd => hne ?_⟩
    exact (Finset.disjoint_union_right.mp hd).2

omit [Fintype V] in
/-- A vertex in an edge-avoided set has degree zero. -/
theorem degree_eq_zero_of_disjoint {K : Finset (Finset V)} {S : Finset V}
    (hS : ∀ e ∈ K, Disjoint e S) {v : V} (hv : v ∈ S) : degree K v = 0 := by
  classical
  rw [degree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hve
  exact (Finset.disjoint_left.mp (hS e he) hve) hv

omit [Fintype V] in
/-- The number of edges meeting `B`, bounded by the degree sum over `B`. -/
theorem card_edges_meeting_le_sum {K : Finset (Finset V)} (B : Finset V) :
    (K.filter (fun e => ¬ Disjoint e B)).card ≤ ∑ x ∈ B, degree K x := by
  exact Hypergraph.edges_meeting_le_of_not_disjoint K B

/-- The total loss equals the size of the edges meeting `B`. -/
theorem sum_lostDegree_eq {K : Finset (Finset V)} (B : Finset V) :
    ∑ v : V, lostDegree K B v = ∑ e ∈ K.filter (fun e => ¬ Disjoint e B), e.card := by
  classical
  have h1 : ∀ v : V, lostDegree K B v
      = ∑ e ∈ K, (if v ∈ e ∧ ¬ Disjoint e B then 1 else 0) := by
    intro v; unfold lostDegree; rw [Finset.card_filter]
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases hd : Disjoint e B
  · simp [hd]
  · simp [hd, Finset.sum_ite_mem]

/-- **Few vertices lose many edges (real form).**  At most `r·|B|·Δ/ζ` vertices lose more than `ζ`
edges when the edges meeting `B` are deleted. -/
theorem card_heavyLoss_le_real {K : Finset (Finset V)} {r : ℕ} (hr : IsUniform K r) {Δ : ℝ}
    (hΔ : ∀ x : V, (degree K x : ℝ) ≤ Δ) (B : Finset V) (ζ : ℝ) :
    (((Finset.univ : Finset V).filter (fun v => ζ < (lostDegree K B v : ℝ))).card : ℝ) * ζ
      ≤ (r : ℝ) * ((B.card : ℝ) * Δ) := by
  classical
  set T := (Finset.univ : Finset V).filter (fun v => ζ < (lostDegree K B v : ℝ)) with hT
  have hstep1 : (T.card : ℝ) * ζ ≤ ∑ v ∈ T, (lostDegree K B v : ℝ) := by
    calc (T.card : ℝ) * ζ = ∑ _v ∈ T, ζ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ T, (lostDegree K B v : ℝ) :=
        Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2.le)
  have hstep2 : ∑ v ∈ T, (lostDegree K B v : ℝ) ≤ ∑ v : V, (lostDegree K B v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => Nat.cast_nonneg _)
  have hstep3 : (∑ v : V, (lostDegree K B v : ℝ))
      = ((∑ e ∈ K.filter (fun e => ¬ Disjoint e B), e.card : ℕ) : ℝ) := by
    rw [← sum_lostDegree_eq]
    push_cast
    rfl
  have hstep4 : ((∑ e ∈ K.filter (fun e => ¬ Disjoint e B), e.card : ℕ) : ℝ)
      = (r : ℝ) * ((K.filter (fun e => ¬ Disjoint e B)).card : ℝ) := by
    have : ∑ e ∈ K.filter (fun e => ¬ Disjoint e B), e.card
        = (K.filter (fun e => ¬ Disjoint e B)).card * r := by
      rw [Finset.sum_congr rfl (fun e he => hr e (Finset.mem_of_mem_filter e he)),
        Finset.sum_const, smul_eq_mul]
    rw [this]; push_cast; ring
  have hstep5 : ((K.filter (fun e => ¬ Disjoint e B)).card : ℝ) ≤ (B.card : ℝ) * Δ := by
    have h1 : ((K.filter (fun e => ¬ Disjoint e B)).card : ℝ) ≤
        ((∑ x ∈ B, degree K x : ℕ) : ℝ) := by
      exact_mod_cast card_edges_meeting_le_sum B
    have h2 : ((∑ x ∈ B, degree K x : ℕ) : ℝ) ≤ (B.card : ℝ) * Δ := by
      push_cast
      calc ∑ x ∈ B, (degree K x : ℝ) ≤ ∑ _x ∈ B, Δ := Finset.sum_le_sum (fun x _ => hΔ x)
        _ = (B.card : ℝ) * Δ := by rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  calc (T.card : ℝ) * ζ ≤ ∑ v : V, (lostDegree K B v : ℝ) := le_trans hstep1 hstep2
    _ = (r : ℝ) * ((K.filter (fun e => ¬ Disjoint e B)).card : ℝ) := by rw [hstep3, hstep4]
    _ ≤ (r : ℝ) * ((B.card : ℝ) * Δ) := mul_le_mul_of_nonneg_left hstep5 hr0

/-- **Few vertices lose many edges (ratio form).**  If `r·Δ = psi·ζ` then at most `psi·|B|` vertices
lose more than `ζ` edges when the edges meeting `B` are deleted. -/
theorem card_heavyLoss_le_ratio {K : Finset (Finset V)} {r : ℕ} (hr : IsUniform K r) {Δ ζ psi : ℝ}
    (hΔ : ∀ x : V, (degree K x : ℝ) ≤ Δ) (hζ : 0 < ζ) (hratio : (r : ℝ) * Δ = psi * ζ)
    (B : Finset V) :
    ((((Finset.univ : Finset V).filter (fun v => ζ < (lostDegree K B v : ℝ))).card : ℝ))
      ≤ psi * (B.card : ℝ) := by
  refine le_of_mul_le_mul_right ?_ hζ
  refine le_trans (card_heavyLoss_le_real hr hΔ B ζ) (le_of_eq ?_)
  rw [show (r : ℝ) * ((B.card : ℝ) * Δ) = ((r : ℝ) * Δ) * (B.card : ℝ) by ring, hratio]
  ring

omit [Fintype V] in
/-- The cardinality of a five-fold union, in real form. -/
theorem card_union_five_le (A B C D E : Finset V) :
    (((A ∪ B ∪ C ∪ D ∪ E).card : ℝ))
      ≤ (A.card : ℝ) + (B.card : ℝ) + (C.card : ℝ) + (D.card : ℝ) + (E.card : ℝ) := by
  have hn : (A ∪ B ∪ C ∪ D ∪ E).card ≤ A.card + B.card + C.card + D.card + E.card := by
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
    exact Finset.card_union_le _ _
  exact_mod_cast hn

/-- The complement of `S ∪ E` is at least as large as `|V| − |S| − |E|`. -/
theorem card_compl_union_ge (S E : Finset V) :
    (Fintype.card V : ℝ) - (S.card : ℝ) - (E.card : ℝ) ≤ (((S ∪ E)ᶜ).card : ℝ) := by
  classical
  have hle : (S ∪ E).card ≤ Fintype.card V := Finset.card_le_univ _
  have hunion : ((S ∪ E).card : ℝ) ≤ (S.card : ℝ) + (E.card : ℝ) := by
    exact_mod_cast Finset.card_union_le S E
  have hcompl : (((S ∪ E)ᶜ).card : ℝ) = (Fintype.card V : ℝ) - ((S ∪ E).card : ℝ) := by
    rw [Finset.card_compl]
    push_cast [Nat.cast_sub hle]
    ring
  rw [hcompl]
  linarith

/-- **The ceiling of the next round.** The drop requested by
`LeanPool.AsymptoticTrianglePacking.Internal.TightParams.step_hi`, at the
absolute scale `d` and with an actual loss `l` below the tolerance `εγ·d·hi`, still lands below
`d·hi₁`. -/
theorem tight_ceiling_step_bound {a gam eps lo hi hi1 d l : ℝ}
    (hd : 0 < d) (hhi0 : 0 < hi) (ha0 : 0 ≤ a) (hgam0 : 0 ≤ gam) (hg1 : 0 ≤ 1 - gam)
    (hlo0 : 0 ≤ lo) (hl : l ≤ eps * gam * (d * hi))
    (hstep : hi - a * gam * (lo - eps * gam * hi) * lo * (1 - gam) / hi + eps * gam * hi ≤ hi1) :
    d * hi - a * gam * (d * lo - l) * (d * lo) * (1 - gam) / (d * hi) + eps * gam * (d * hi)
      ≤ d * hi1 := by
  have hDhi : (0 : ℝ) < d * hi := mul_pos hd hhi0
  have hfac : (0 : ℝ) ≤ a * gam * (d * lo) * (1 - gam) / (d * hi) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha0 hgam0) (mul_nonneg hd.le hlo0)) hg1)
      hDhi.le
  have hmono : a * gam * (d * lo - eps * gam * (d * hi)) * (d * lo) * (1 - gam) / (d * hi)
      ≤ a * gam * (d * lo - l) * (d * lo) * (1 - gam) / (d * hi) := by
    have e1 : a * gam * (d * lo - eps * gam * (d * hi)) * (d * lo) * (1 - gam) / (d * hi)
        = (a * gam * (d * lo) * (1 - gam) / (d * hi)) * (d * lo - eps * gam * (d * hi)) := by
      ring
    have e2 : a * gam * (d * lo - l) * (d * lo) * (1 - gam) / (d * hi)
        = (a * gam * (d * lo) * (1 - gam) / (d * hi)) * (d * lo - l) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (by linarith) hfac
  have heq : a * gam * (d * lo - eps * gam * (d * hi)) * (d * lo) * (1 - gam) / (d * hi)
      = d * (a * gam * (lo - eps * gam * hi) * lo * (1 - gam) / hi) := by
    field_simp
  have hsd : d * (hi - a * gam * (lo - eps * gam * hi) * lo * (1 - gam) / hi + eps * gam * hi)
      ≤ d * hi1 := mul_le_mul_of_nonneg_left hstep hd.le
  linarith only [hmono, heq, hsd]

/-- **Vertex count from the codegree bound.**  A vertex of degree `D` forces
`(r−1)·D ≤ (|V| − 1)·κ`. -/
theorem card_ge_of_codegree {K : Finset (Finset V)} {r : ℕ} (hr : IsUniform K r) (hr1 : 1 ≤ r)
    {κ : ℝ} (hκ : ∀ x y : V, x ≠ y → (codegree K x y : ℝ) ≤ κ) (v : V) :
    ((r : ℝ) - 1) * (degree K v : ℝ) ≤ ((Fintype.card V : ℝ) - 1) * κ := by
  classical
  have hsum : ∑ u ∈ (Finset.univ : Finset V).erase v, codegree K v u = (r - 1) * degree K v :=
    sum_codegree_erase_eq hr v
  have hsumR : ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree K v u : ℝ)
      = ((r : ℝ) - 1) * (degree K v : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hsum
    push_cast [Nat.cast_sub hr1] at h
    simpa using h
  have hle : ∀ u ∈ (Finset.univ : Finset V).erase v, (codegree K v u : ℝ) ≤ κ := by
    intro u hu
    exact hκ v u (fun h => (Finset.mem_erase.mp hu).1 h.symm)
  have hcardV : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hcard : (((Finset.univ : Finset V).erase v).card : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
    push_cast [Nat.cast_sub hcardV]
    ring
  calc ((r : ℝ) - 1) * (degree K v : ℝ)
      = ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree K v u : ℝ) := hsumR.symm
    _ ≤ ∑ _u ∈ (Finset.univ : Finset V).erase v, κ := Finset.sum_le_sum hle
    _ = (((Finset.univ : Finset V).erase v).card : ℝ) * κ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Fintype.card V : ℝ) - 1) * κ := by rw [hcard]

/-- The arithmetic of the exceptional budget: the new exceptional set is the old one (`e`) plus the
vertices that left the band (`b`), plus those heavily damaged by the old exceptional set (`h`), plus
those breaking the new ceiling (`hh ≤ e + b + h`), plus those damaged by pruning the latter
(`dm ≤ psi·hh`); the total is at most `(2 + psi)²(e + b)`. -/
theorem budget_arith {e b h hh dm tot psi sigj exc sig1 N : ℝ}
    (hpsi0 : 0 ≤ psi) (he : 0 ≤ e) (hb : 0 ≤ b)
    (htot : tot ≤ e + b + h + hh + dm)
    (h1 : h ≤ psi * e) (h2 : hh ≤ e + b + h) (h3 : dm ≤ psi * hh)
    (hEB : e + b ≤ (sigj + exc) * N) (hN : 0 ≤ N)
    (hstep : (2 + psi) ^ 2 * (sigj + exc) ≤ sig1) :
    tot ≤ sig1 * N := by
  have hs : (0 : ℝ) ≤ e + b := by linarith
  have hps : (0 : ℝ) ≤ psi * (e + b) := mul_nonneg hpsi0 hs
  have g1 : h ≤ psi * (e + b) := by nlinarith [mul_nonneg hpsi0 hb]
  have g2 : hh ≤ (1 + psi) * (e + b) := by nlinarith
  have g3 : dm ≤ psi * ((1 + psi) * (e + b)) := by nlinarith
  have g4 : tot ≤ (2 + psi) ^ 2 * (e + b) := by nlinarith
  have g5 : (2 + psi) ^ 2 * (e + b) ≤ (2 + psi) ^ 2 * ((sigj + exc) * N) :=
    mul_le_mul_of_nonneg_left hEB (sq_nonneg _)
  nlinarith only [g4, g5, hstep, hN]

/-! ## One round of the schedule -/

/-- **One round of the tight-band schedule.**  From the invariant at stage `j` — an `r`-uniform
sub-hypergraph `K` avoiding the covered set `S`, with global degree ceiling `d·hi j`, degree floor
`d·lo j` off the exceptional set `E`, codegrees `≤ κ` and `|E| ≤ sig j·|V|` — one sharp round
produces a retained set covering a `γ/(16r)` fraction of the uncovered vertices and re-establishes
the invariant at stage `j+1`. -/
theorem tight_round_step {r : ℕ} (hr : 2 ≤ r) {β : ℝ} (Pm : TightParams r β)
    {D₀ c₀ : ℝ} (hc₀ : 0 ≤ c₀) (hround : SharpRoundFor r Pm.gam Pm.eps Pm.exc (β / 2) D₀ c₀)
    {W : Type} [Fintype W] [DecidableEq W]
    {d κ : ℝ} (hd : 0 < d) (hκ0 : 0 ≤ κ)
    (hDlo : D₀ ≤ d * Pm.lomin) (hcodsmall : κ ≤ c₀ * (d * Pm.lomin))
    (hNbig : D₀ ≤ (Fintype.card W : ℝ))
    {j : ℕ} (hj : j < Pm.T)
    {K : Finset (Finset W)} {S E : Finset W}
    (huni : IsUniform K r)
    (hSdisj : ∀ e ∈ K, Disjoint e S)
    (hhi : ∀ v : W, (degree K v : ℝ) ≤ d * Pm.hi j)
    (hlo : ∀ v : W, v ∉ S → v ∉ E → d * Pm.lo j ≤ (degree K v : ℝ))
    (hcodeg : ∀ x y : W, x ≠ y → (codegree K x y : ℝ) ≤ κ)
    (hE : (E.card : ℝ) ≤ Pm.sig j * (Fintype.card W : ℝ))
    (huncov : β * (Fintype.card W : ℝ) < (Fintype.card W : ℝ) - (S.card : ℝ)) :
    ∃ R' : Finset (Finset W), R' ⊆ K ∧
      Pm.gam / (16 * r) * ((Fintype.card W : ℝ) - (S.card : ℝ)) ≤ ((covered R').card : ℝ) ∧
      ∃ (K' : Finset (Finset W)) (E' : Finset W),
        K' ⊆ Hypergraph.residual K R' ∧ IsUniform K' r ∧
        (∀ e ∈ K', Disjoint e (S ∪ covered R')) ∧
        (∀ v : W, (degree K' v : ℝ) ≤ d * Pm.hi (j + 1)) ∧
        (∀ v : W, v ∉ S ∪ covered R' → v ∉ E' → d * Pm.lo (j + 1) ≤ (degree K' v : ℝ)) ∧
        (∀ x y : W, x ≠ y → (codegree K' x y : ℝ) ≤ κ) ∧
        (E'.card : ℝ) ≤ Pm.sig (j + 1) * (Fintype.card W : ℝ) := by
  classical
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hjT : j ≤ Pm.T := le_of_lt hj
  have hj1T : j + 1 ≤ Pm.T := hj
  have hlo_pos : 0 < Pm.lo j := lt_of_lt_of_le Pm.lomin_pos (Pm.lomin_le j hjT)
  have hhi_pos : 0 < Pm.hi j := lt_of_lt_of_le hlo_pos (Pm.lo_le_hi j hjT)
  have hlo1_pos : 0 < Pm.lo (j + 1) := lt_of_lt_of_le Pm.lomin_pos (Pm.lomin_le (j + 1) hj1T)
  have hhi1_pos : 0 < Pm.hi (j + 1) := lt_of_lt_of_le hlo1_pos (Pm.lo_le_hi (j + 1) hj1T)
  have hgam := Pm.gam_pos
  have heps := Pm.eps_pos
  set N : ℝ := (Fintype.card W : ℝ) with hNdef
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  set A : Finset W := (S ∪ E)ᶜ with hAdef
  -- the live set is large
  have hAcard : N - (S.card : ℝ) - (E.card : ℝ) ≤ (A.card : ℝ) := card_compl_union_ge S E
  have hsigj : Pm.sig j ≤ β / 2 := Pm.sig_le j hjT
  have hEsmall : (E.card : ℝ) ≤ β / 2 * N := by
    refine le_trans hE ?_
    exact mul_le_mul_of_nonneg_right hsigj hN0
  have hAhalf : ((Fintype.card W : ℝ) - (S.card : ℝ)) / 2 ≤ (A.card : ℝ) := by linarith
  have hAbig : β / 2 * N ≤ (A.card : ℝ) := by linarith
  -- apply the sharp round
  have hlo' : ∀ v ∈ A, d * Pm.lo j ≤ (degree K v : ℝ) := by
    intro v hv
    rw [hAdef, Finset.mem_compl, Finset.mem_union] at hv
    push Not at hv
    exact hlo v hv.1 hv.2
  have hlomin_le_hi : Pm.lomin ≤ Pm.hi j := le_trans (Pm.lomin_le j hjT) (Pm.lo_le_hi j hjT)
  have hDΔ : D₀ ≤ d * Pm.hi j :=
    le_trans hDlo (mul_le_mul_of_nonneg_left hlomin_le_hi hd.le)
  have hcκ : κ ≤ c₀ * (d * Pm.hi j) :=
    le_trans hcodsmall (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hlomin_le_hi hd.le) hc₀)
  have h2δ : d * Pm.hi j ≤ 2 * (d * Pm.lo j) := by
    have hh2 := Pm.hi_le_two_lo j hjT
    linarith only [mul_le_mul_of_nonneg_left hh2 hd.le]
  obtain ⟨R', hR'K, B, hBcard, hband, hcov⟩ :=
    hround K A (d * Pm.lo j) (d * Pm.hi j) κ huni hhi hlo' hcodeg hκ0 hcκ hDΔ h2δ hNbig hAbig
  refine ⟨R', hR'K, ?_, ?_⟩
  · -- the covering bound
    have hfrac : 0 ≤ Pm.gam / (8 * (r : ℝ)) := by positivity
    have h1 : Pm.gam / (8 * (r : ℝ)) * (((Fintype.card W : ℝ) - (S.card : ℝ)) / 2)
        ≤ Pm.gam / (8 * (r : ℝ)) * (A.card : ℝ) := mul_le_mul_of_nonneg_left hAhalf hfrac
    have h2 : Pm.gam / (16 * (r : ℝ)) * ((Fintype.card W : ℝ) - (S.card : ℝ))
        = Pm.gam / (8 * (r : ℝ)) * (((Fintype.card W : ℝ) - (S.card : ℝ)) / 2) := by
      field_simp
      ring
    rw [h2]
    linarith [hcov]
  -- the new invariant
  set ζ : ℝ := Pm.eps * Pm.gam * (d * Pm.hi j) with hζdef
  have hζpos : 0 < ζ := by rw [hζdef]; positivity
  set Kres : Finset (Finset W) := Hypergraph.residual K R' with hKresdef
  have hKresK : Kres ⊆ K := Hypergraph.residual_subset K R'
  have hKreshi : ∀ v : W, (degree Kres v : ℝ) ≤ d * Pm.hi j := by
    intro v
    exact le_trans (by exact_mod_cast degree_mono hKresK v) (hhi v)
  set heavy : Finset W :=
    (Finset.univ : Finset W).filter (fun v => ζ < (lostDegree K E v : ℝ)) with hheavydef
  set Hi : Finset W :=
    (Finset.univ : Finset W).filter (fun v => d * Pm.hi (j + 1) < (degree Kres v : ℝ)) with hHidef
  set K' : Finset (Finset W) := prune Kres Hi with hK'def
  set Dam : Finset W :=
    (Finset.univ : Finset W).filter (fun v => ζ < (lostDegree Kres Hi v : ℝ)) with hDamdef
  have hDhi : (0 : ℝ) < d * Pm.hi j := by positivity
  have hr1' : (0 : ℝ) ≤ (r : ℝ) - 1 := by linarith
  have hg1 : (0 : ℝ) ≤ 1 - Pm.gam := by linarith only [Pm.gam_le]
  have hKres0 : ∀ v : W, v ∈ S ∪ covered R' → degree Kres v = 0 := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · have h0 : degree K v = 0 := degree_eq_zero_of_disjoint hSdisj h
      have := degree_mono hKresK v
      omega
    · exact degree_eq_zero_of_disjoint
        (fun e he => Hypergraph.residual_disjoint_covered he) h
  -- every vertex breaking the new ceiling is exceptional, badly-banded, or heavily damaged
  have hHisub : Hi ⊆ E ∪ B ∪ heavy := by
    intro v hvHi
    have hdeg : d * Pm.hi (j + 1) < (degree Kres v : ℝ) := (Finset.mem_filter.mp hvHi).2
    have hpos1 : (0 : ℝ) < d * Pm.hi (j + 1) := by positivity
    by_contra hc
    simp only [Finset.mem_union, not_or] at hc
    obtain ⟨⟨hvE, hvB⟩, hvheavy⟩ := hc
    have hvS : v ∉ S := by
      intro h
      rw [hKres0 v (Finset.mem_union_left _ h)] at hdeg
      simp only [Nat.cast_zero] at hdeg
      linarith
    have hvcov : v ∉ covered R' := by
      intro h
      rw [hKres0 v (Finset.mem_union_right _ h)] at hdeg
      simp only [Nat.cast_zero] at hdeg
      linarith
    have hvA : v ∈ A := by
      rw [hAdef, Finset.mem_compl, Finset.mem_union]
      push Not
      exact ⟨hvS, hvE⟩
    obtain ⟨_, hup⟩ := hband v hvA hvB hvcov
    have hlostA : (lostDegree K Aᶜ v : ℝ) = (lostDegree K E v : ℝ) := by
      rw [hAdef, compl_compl, lostDegree_union_of_disjoint hSdisj]
    rw [hlostA] at hup
    have hlostle : (lostDegree K E v : ℝ) ≤ Pm.eps * Pm.gam * (d * Pm.hi j) := by
      by_contra hcc
      push Not at hcc
      exact hvheavy (Finset.mem_filter.mpr ⟨Finset.mem_univ v, by rw [hζdef]; exact hcc⟩)
    have hbound := tight_ceiling_step_bound (a := ((r : ℝ) - 1) / r) hd hhi_pos
      (div_nonneg hr1' hrpos.le) hgam.le hg1 hlo_pos.le hlostle (Pm.step_hi j hj)
    linarith only [hdeg, hup, hbound]
  refine ⟨K', E ∪ B ∪ heavy ∪ Hi ∪ Dam, Finset.filter_subset _ _,
    fun e he => huni e (hKresK (Finset.mem_of_mem_filter e he)), ?_, ?_, ?_, ?_, ?_⟩
  · -- edges avoid the new covered set
    intro e he
    have heK : e ∈ Kres := Finset.mem_of_mem_filter e he
    rw [Finset.disjoint_union_right]
    exact ⟨hSdisj e (hKresK heK), Hypergraph.residual_disjoint_covered heK⟩
  · -- the new ceiling
    intro v
    by_cases hv : v ∈ Hi
    · rw [hK'def, degree_prune_eq_zero hv]
      push_cast
      positivity
    · have h1 : (degree K' v : ℝ) ≤ (degree Kres v : ℝ) := by
        exact_mod_cast degree_mono (Finset.filter_subset _ _) v
      have h2 : ¬ (d * Pm.hi (j + 1) < (degree Kres v : ℝ)) := by
        intro hlt
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hlt⟩)
      push Not at h2
      linarith
  · -- the new floor
    intro v hvS hvE'
    simp only [Finset.mem_union, not_or] at hvS hvE'
    obtain ⟨⟨⟨⟨hvE, hvB⟩, hvheavy⟩, _hvHi⟩, hvDam⟩ := hvE'
    have hvA : v ∈ A := by
      rw [hAdef, Finset.mem_compl, Finset.mem_union]
      push Not
      exact ⟨hvS.1, hvE⟩
    obtain ⟨hlow, _⟩ := hband v hvA hvB hvS.2
    have hdrop : (degree Kres v : ℝ) ≤ (degree K' v : ℝ) + (lostDegree Kres Hi v : ℝ) := by
      exact_mod_cast degree_prune_ge Hi v
    have hlost : (lostDegree Kres Hi v : ℝ) ≤ ζ := by
      by_contra hc
      push Not at hc
      exact hvDam (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
    have hstep := Pm.step_lo j hj
    have hkey : d * Pm.lo (j + 1)
        ≤ d * Pm.lo j - ((r : ℝ) - 1) / r * Pm.gam * (d * Pm.hi j)
          - Pm.eps * Pm.gam * (d * Pm.hi j) - ζ := by
      rw [hζdef]
      linarith only [mul_le_mul_of_nonneg_left hstep hd.le]
    linarith
  · -- codegrees only decrease
    intro x y hxy
    refine le_trans ?_ (hcodeg x y hxy)
    exact_mod_cast codegree_mono
      (Finset.Subset.trans (Finset.filter_subset _ _) hKresK) x y
  · -- the exceptional budget
    obtain ⟨psi, hpsidef⟩ : ∃ p : ℝ, p = (r : ℝ) / (Pm.eps * Pm.gam) := ⟨_, rfl⟩
    have hpsi0 : (0 : ℝ) ≤ psi := by rw [hpsidef]; positivity
    have hratio : (r : ℝ) * (d * Pm.hi j) = psi * ζ := by
      rw [hpsidef, hζdef]; field_simp
    have hheavy_le : (heavy.card : ℝ) ≤ psi * (E.card : ℝ) :=
      card_heavyLoss_le_ratio huni hhi hζpos hratio E
    have hDam_le : (Dam.card : ℝ) ≤ psi * (Hi.card : ℝ) :=
      card_heavyLoss_le_ratio (fun e he => huni e (hKresK he)) hKreshi hζpos hratio Hi
    have hHi_le : (Hi.card : ℝ) ≤ (E.card : ℝ) + (B.card : ℝ) + (heavy.card : ℝ) := by
      have h1 : Hi.card ≤ (E ∪ B ∪ heavy).card := Finset.card_le_card hHisub
      have h2 : (E ∪ B ∪ heavy).card ≤ E.card + B.card + heavy.card :=
        le_trans (Finset.card_union_le _ _)
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      have : Hi.card ≤ E.card + B.card + heavy.card := le_trans h1 h2
      exact_mod_cast this
    have hunion : ((E ∪ B ∪ heavy ∪ Hi ∪ Dam).card : ℝ)
        ≤ (E.card : ℝ) + (B.card : ℝ) + (heavy.card : ℝ) + (Hi.card : ℝ) + (Dam.card : ℝ) :=
      card_union_five_le E B heavy Hi Dam
    -- the total is at most `(2 + psi)^2` times the fresh exceptional mass
    have hEB : (E.card : ℝ) + (B.card : ℝ) ≤ (Pm.sig j + Pm.exc) * N := by
      have hb : (B.card : ℝ) ≤ Pm.exc * N := hBcard
      linarith only [hE, hb]
    have hEnn : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg _
    have hBnn : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
    have hstepsig : (2 + psi) ^ 2 * (Pm.sig j + Pm.exc) ≤ Pm.sig (j + 1) := by
      rw [hpsidef]; exact Pm.sig_step j hj
    exact budget_arith hpsi0 hEnn hBnn hunion hheavy_le hHi_le hDam_le hEB hN0 hstepsig

end LeanPool.AsymptoticTrianglePacking.Internal

end


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

public section

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
