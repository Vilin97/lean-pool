/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.Greedy
import LeanPool.AsymptoticTrianglePacking.Internal.Round
import LeanPool.AsymptoticTrianglePacking.Internal.IterationSeq
import LeanPool.AsymptoticTrianglePacking.Internal.Convergence
import Mathlib.Analysis.RCLike.Basic

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
