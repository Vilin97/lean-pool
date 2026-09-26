/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.AdaptiveRounds
public import LeanPool.AsymptoticTrianglePacking.Internal.RegularMost

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
