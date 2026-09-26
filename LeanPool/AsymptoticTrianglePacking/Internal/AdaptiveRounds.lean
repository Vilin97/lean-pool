/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.IterationSeq
public import LeanPool.AsymptoticTrianglePacking.Internal.DischargeSeq

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
def HasRoundOracle (H : Finset (Finset V)) (c β : ℝ) : Prop :=
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
