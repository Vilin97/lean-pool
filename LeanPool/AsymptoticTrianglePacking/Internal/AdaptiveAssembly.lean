/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — the ADAPTIVE outer assembly (STEP 3, corrected route)

The fixed-parameter route (`MostAssembly.nibbleTheoremMost_holds_of_params`) is refuted
(`ParamsCoreRefutation.not_nibbleParamsExistThreshold`): a fixed `lam` cannot cover a `(1-lam)`
fraction of the WHOLE vertex set every round. The corrected route uses a per-round strategy sequence
`R : ℕ → …` and per-round rates `lam : ℕ → ℝ`, with the oracle covering the still-UNCOVERED set each
round (`exists_matching_of_oracle_seq_lt`, DischargeSeq.lean). The per-round covering demand is
satisfiable at the *scalar* level (`AdaptiveSchedule.adaptive_crux_satisfiable`).

This file PEELS the outer layer: it reduces `NibbleTheoremMost` to the adaptive existence atom
`AdaptiveOracleExists`.

**STATUS (2026-08-05) — the atom `AdaptiveOracleExists` is FALSE, and so is the interface
`NibbleTheoremMost` it was peeled from.**  See `LeanPool.AsymptoticTrianglePacking.Internal.StarCounterexample`:  the complete bipartite
graph `K_{m,D}` (`2`-uniform) is exactly `D`-regular outside an exceptional set of `D` vertices, has
codegree `≤ 1`, and yet has matching number `≤ D`, while `NibbleTheoremMost` demands a matching of
size `≥ (1-β)(m+D)/2`.  The `η`-fraction exceptional set of `NearlyRegularMost` is allowed to carry
ALL the edges, so majority near-regularity *without a global degree ceiling* controls nothing.  The
failure is NOT an artefact of the per-round architecture: `adaptiveOracleExists_of_nibbleTheoremMost`
below shows the atom is in fact EQUIVALENT to `NibbleTheoremMost` (one round with the whole matching
realises the oracle).

The repair is the ceiling interface `NibbleTheoremMostCeil` (already present in `RegularMost.lean`
and already consumed by `NibbleGapReduction`), which additionally assumes `deg H x ≤ (1+μ)d` for
EVERY vertex — the star witness has right-degrees `m ≫ (1+μ)D`, so it is excluded.  This file
therefore also provides the corrected adaptive atom `AdaptiveOracleExistsCeil`, together with the two
placeholder-free reductions
`nibbleTheoremMostCeil_of_adaptiveOracleCeil` / `adaptiveOracleExistsCeil_of_nibbleTheoremMostCeil`
(so the corrected atom is *equivalent* to `NibbleTheoremMostCeil`) and the bridge
`NibbleTheoremMostCeil.nibbleTheorem` to the strict interface.  Discharging
`AdaptiveOracleExistsCeil` — equivalently `NibbleTheoremMostCeil` — is the remaining outer-loop
obligation of the nibble.

**UPDATE (2026-08-05) — the outer loop of the corrected atom is now DISCHARGED.**  The two
non-mathematical ingredients of `AdaptiveOracleExistsCeil`, namely the *rate sequence* `lam` and the
*iteration* producing `R`, are proved in `LeanPool.AsymptoticTrianglePacking.Internal.AdaptiveRounds` and consumed here by
`adaptiveOracleExistsCeil_of_roundOracleCeil`.  What remains is the strictly ONE-round atom
`RoundOracleExistsCeil`: a single nibble round covering a fixed fraction `c` of the still-uncovered
vertices while re-establishing a round invariant.  `roundOracleExistsCeil_of_nibbleTheoremMostCeil`
shows this atom is still EQUIVALENT to `NibbleTheoremMostCeil`, so nothing was lost in the peeling.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.AdaptiveRounds
import LeanPool.AsymptoticTrianglePacking.Internal.RoundOracleKernel
import LeanPool.AsymptoticTrianglePacking.Internal.DischargeSeq
import LeanPool.AsymptoticTrianglePacking.Internal.RegularMost
import LeanPool.AsymptoticTrianglePacking.Internal.StarCounterexample

open Hypergraph Finset

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-- **The adaptive oracle atom.** For uniformity `r` and target `β`, richness parameters `μ, η > 0`
and a degree threshold `d₀` such that every admissible near-regular input admits a per-round strategy
sequence `R` with per-round rates `lam` (`∏_{k<T} lam k ≤ β`) whose round-`k` matching covers a
`(1 - lam k)` fraction of the still-uncovered vertices. This was the intended (satisfiable-looking)
replacement for the refuted fixed-parameter `NibbleParamsExistThreshold`; it is itself FALSE
(`not_adaptiveOracleExists`) — see the module docstring. -/
def AdaptiveOracleExists : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β →
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
        IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
        ∃ (R : ℕ → Finset (Finset V) → Finset (Finset V)) (lam : ℕ → ℝ) (T : ℕ),
          (∀ k H', R k H' ⊆ H') ∧ (∀ k, 0 ≤ lam k) ∧
          (∏ k ∈ Finset.range T, lam k) ≤ β ∧
          (∀ k, k < T →
            (1 - lam k) * ((Fintype.card V : ℝ) - ((support (nibbleMatchingSeq R H k)).card : ℝ))
              ≤ ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ))

/-- **`NibbleTheoremMost` — assembled from the adaptive oracle (PEELED, placeholder-free modulo the atom).**
Combines `AdaptiveOracleExists` with the proved sequence-discharge `exists_matching_of_oracle_seq_lt`. -/
theorem nibbleTheoremMost_of_adaptiveOracle (h : AdaptiveOracleExists) : NibbleTheoremMost := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hO⟩ := h r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg
  obtain ⟨R, lam, T, hR, hlam0, hTβ, horacle⟩ := hO H d hd hd0 huni hreg hcodeg
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  exact exists_matching_of_oracle_seq_lt hR huni hr1 hlam0 T hTβ horacle

/-! ## One round realises any matching

The technical content of the converse reductions: a matching `M ⊆ H` is realised by the one-round
strategy `R k H' = H' ∩ M`, whose round-`0` matching is `M` itself. -/

section OneRound

variable {V : Type*} [DecidableEq V]

/-- The one-round strategy that retains exactly the edges of `M`. -/
def matchingStrategy (M : Finset (Finset V)) :
    ℕ → Finset (Finset V) → Finset (Finset V) :=
  fun _ H' => H'.filter (fun e => e ∈ M)

theorem matchingStrategy_subset (M : Finset (Finset V)) (k : ℕ) (H' : Finset (Finset V)) :
    matchingStrategy M k H' ⊆ H' := Finset.filter_subset _ _

theorem matchingStrategy_apply {H M : Finset (Finset V)} (hMH : M ⊆ H) (k : ℕ) :
    matchingStrategy M k H = M := by
  classical
  ext e
  simp only [matchingStrategy, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hMH h, h⟩⟩

/-- A matching is its own round matching: every retained edge is isolated. -/
theorem roundMatching_of_isMatching {H M : Finset (Finset V)} (hM : IsMatching H M) :
    roundMatching M = M := by
  ext e
  refine ⟨fun he => roundMatching_subset M he, fun he => ?_⟩
  rw [roundMatching, Finset.mem_filter]
  exact ⟨he, fun f hf hfe => hM.disjoint e he f hf (fun h => hfe h.symm)⟩

/-- **One round realises a matching.**  For a matching `M` of `H`, the strategy sequence
`matchingStrategy M` covers `|support M|` vertices in round `0`. -/
theorem oracle_of_matching_one_round {H M : Finset (Finset V)} (hM : IsMatching H M) :
    roundMatching (matchingStrategy M 0 (nibbleResidualSeq (matchingStrategy M) H 0)) = M := by
  have h0 : nibbleResidualSeq (matchingStrategy M) H 0 = H := rfl
  rw [h0, matchingStrategy_apply hM.subset, roundMatching_of_isMatching hM]

end OneRound

/-- **The adaptive oracle atom is EQUIVALENT to `NibbleTheoremMost` (converse direction).**  A
matching covering a `(1-β)` fraction is realised by the ONE-round strategy `matchingStrategy M` with
the constant rate `lam ≡ β`.  Hence the falsity of `AdaptiveOracleExists` is a failure of the
interface hypotheses, not of the per-round architecture. -/
theorem adaptiveOracleExists_of_nibbleTheoremMost (h : NibbleTheoremMost) :
    AdaptiveOracleExists := by
  classical
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := h r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg
  obtain ⟨M, hM, hcard⟩ := hmain H d hd hd0 huni hreg hcodeg
  refine ⟨matchingStrategy M, fun _ => β, 1, matchingStrategy_subset M, fun _ => hβ.le,
    by simp, ?_⟩
  intro k hk
  have hk0 : k = 0 := Nat.lt_one_iff.mp hk
  subst hk0
  have hsupp0 : (support (nibbleMatchingSeq (matchingStrategy M) H 0)).card = 0 := by
    simp [show nibbleMatchingSeq (matchingStrategy M) H 0 = (∅ : Finset (Finset V)) from rfl,
      support, Finset.biUnion_empty]
  rw [oracle_of_matching_one_round hM, hsupp0]
  have hrpos : (0 : ℝ) < r := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hsc : ((support M).card : ℝ) = (r : ℝ) * (M.card : ℝ) := by
    exact_mod_cast matching_support_card huni hM
  rw [hsc]
  have hid : (r : ℝ) * ((1 - β) * ((Fintype.card V : ℝ) / r)) = (1 - β) * (Fintype.card V : ℝ) := by
    field_simp
  have h2 : (1 - β) * (Fintype.card V : ℝ) ≤ (r : ℝ) * (M.card : ℝ) := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hcard hrpos.le
  simpa using h2

/-- **The adaptive oracle atom `AdaptiveOracleExists` is FALSE.**  It implies `NibbleTheoremMost`
(`nibbleTheoremMost_of_adaptiveOracle`), which the star witness `LeanPool.AsymptoticTrianglePacking.Internal.starHG` refutes
(`not_nibbleTheoremMost`). -/
theorem not_adaptiveOracleExists : ¬ AdaptiveOracleExists := fun h =>
  not_nibbleTheoremMost (nibbleTheoremMost_of_adaptiveOracle h)

/-
**REFUTED — kept for the record.**  The following three declarations were the intended endpoints of
this file.  They cannot be proved: `adaptiveOracleExists_holds` asserts `AdaptiveOracleExists`, which
is refuted by `not_adaptiveOracleExists` above (equivalently, `nibbleTheoremMost_holds` asserts the
interface `NibbleTheoremMost` refuted by `not_nibbleTheoremMost`).  The corrected, ceiling-carrying
versions are `adaptiveOracleExistsCeil_of_nibbleTheoremMostCeil`,
`nibbleTheoremMostCeil_of_adaptiveOracleCeil` and `NibbleTheoremMostCeil.nibbleTheorem` below.

/-- **The isolated adaptive research kernel (DELEGATE).** -/
theorem adaptiveOracleExists_holds : AdaptiveOracleExists := by
  placeholder

/-- **`NibbleTheoremMost` — assembled (placeholder-free modulo `adaptiveOracleExists_holds`).** -/
theorem nibbleTheoremMost_holds : NibbleTheoremMost :=
  nibbleTheoremMost_of_adaptiveOracle adaptiveOracleExists_holds

/-- **`NibbleTheorem`** via the majority form. -/
theorem nibbleTheorem_holds : NibbleTheorem :=
  nibbleTheoremMost_holds.nibbleTheorem
-/

/-! ## The corrected atom: majority near-regularity WITH a global degree ceiling -/

/-- **The corrected adaptive oracle atom.**  Identical to `AdaptiveOracleExists` except that the
input is additionally assumed to satisfy the global degree ceiling `deg H x ≤ (1+μ)d` for EVERY
vertex — the hypothesis whose absence the star counterexample exploits.  This is the atom peeled off
`NibbleTheoremMostCeil`. -/
def AdaptiveOracleExistsCeil : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β →
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
        IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
        (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
        ∃ (R : ℕ → Finset (Finset V) → Finset (Finset V)) (lam : ℕ → ℝ) (T : ℕ),
          (∀ k H', R k H' ⊆ H') ∧ (∀ k, 0 ≤ lam k) ∧
          (∏ k ∈ Finset.range T, lam k) ≤ β ∧
          (∀ k, k < T →
            (1 - lam k) * ((Fintype.card V : ℝ) - ((support (nibbleMatchingSeq R H k)).card : ℝ))
              ≤ ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ))

/-- **`NibbleTheoremMostCeil` from the corrected adaptive oracle.**  Same geometric discharge as
`nibbleTheoremMost_of_adaptiveOracle`, with the ceiling threaded through. -/
theorem nibbleTheoremMostCeil_of_adaptiveOracleCeil (h : AdaptiveOracleExistsCeil) :
    NibbleTheoremMostCeil := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hO⟩ := h r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil
  obtain ⟨R, lam, T, hR, hlam0, hTβ, horacle⟩ := hO H d hd hd0 huni hreg hcodeg hceil
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  exact exists_matching_of_oracle_seq_lt hR huni hr1 hlam0 T hTβ horacle

/-- **Converse: `NibbleTheoremMostCeil` gives the corrected adaptive oracle.**  Together with
`nibbleTheoremMostCeil_of_adaptiveOracleCeil` this makes the corrected atom EQUIVALENT to the
ceiling interface. -/
theorem adaptiveOracleExistsCeil_of_nibbleTheoremMostCeil (h : NibbleTheoremMostCeil) :
    AdaptiveOracleExistsCeil := by
  classical
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := h r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil
  obtain ⟨M, hM, hcard⟩ := hmain H d hd hd0 huni hreg hcodeg hceil
  refine ⟨matchingStrategy M, fun _ => β, 1, matchingStrategy_subset M, fun _ => hβ.le,
    by simp, ?_⟩
  intro k hk
  have hk0 : k = 0 := Nat.lt_one_iff.mp hk
  subst hk0
  have hsupp0 : (support (nibbleMatchingSeq (matchingStrategy M) H 0)).card = 0 := by
    simp [show nibbleMatchingSeq (matchingStrategy M) H 0 = (∅ : Finset (Finset V)) from rfl,
      support, Finset.biUnion_empty]
  rw [oracle_of_matching_one_round hM, hsupp0]
  have hrpos : (0 : ℝ) < r := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hsc : ((support M).card : ℝ) = (r : ℝ) * (M.card : ℝ) := by
    exact_mod_cast matching_support_card huni hM
  rw [hsc]
  have hid : (r : ℝ) * ((1 - β) * ((Fintype.card V : ℝ) / r)) = (1 - β) * (Fintype.card V : ℝ) := by
    field_simp
  have h2 : (1 - β) * (Fintype.card V : ℝ) ≤ (r : ℝ) * (M.card : ℝ) := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hcard hrpos.le
  simpa using h2

/-- **The ceiling interface implies the strict `NibbleTheorem`.**  Strict `(1±μ)`-near-regularity
gives majority near-regularity with an EMPTY exceptional set and the global ceiling for free, so
`NibbleTheoremMostCeil` still suffices for the whole Layer E chain. -/
theorem NibbleTheoremMostCeil.nibbleTheorem (h : NibbleTheoremMostCeil) : NibbleTheorem := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := h r hr β hβ
  refine ⟨μ, hμ, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcod
  exact hmain H d hd hd0 huni (hreg.nearlyRegularMost hη.le) hcod (fun x => (hreg x).2)

/-! ### Peeling the iteration off the corrected atom

The two ingredients of `AdaptiveOracleExistsCeil` — the *rate sequence* `lam` and the *iteration*
building `R` — are pure bookkeeping and are discharged in `LeanPool.AsymptoticTrianglePacking.Internal.AdaptiveRounds`:

* `exists_adaptive_rates_of_uncovered_le`: for ANY strategy sequence the canonical rates
  `lam k = u (k+1) / u k` meet the per-round covering demand with equality and telescope, so the
  outer demand is equivalent to the single scalar statement "after `T` rounds at most a
  `β`-fraction of the vertices is uncovered";
* `exists_uncovered_le_of_roundOracle`: that scalar statement follows from a genuinely ONE-round
  oracle (`HasRoundOracle`), iterated by the explicit strategy `oracleStrategy`.

What is left is therefore the single-round atom `RoundOracleExistsCeil` below: a nibble round that
covers a fixed fraction `c` of the still-uncovered vertices while re-establishing an invariant.  No
induction over rounds and no rate arithmetic remains in it. -/

/-- **The one-round oracle atom, with global degree ceiling.**  For uniformity `r` and target `β`,
richness parameters `μ, η > 0`, a degree threshold `d₀` and a per-round covering fraction `c > 0`
such that every admissible input (majority near-regular, low codegree, GLOBAL degree ceiling) carries
a one-round covering oracle `HasRoundOracle H c β`.  This is `AdaptiveOracleExistsCeil` with the
round iteration and the rate bookkeeping removed. -/
def RoundOracleExistsCeil : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β →
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
        IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
        (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
        HasRoundOracle H c β

/-- **The corrected adaptive oracle from the one-round oracle (PEELED, placeholder-free).**  All of the
iteration and rate arithmetic of `AdaptiveOracleExistsCeil` is discharged here; only the single-round
covering step remains. -/
theorem adaptiveOracleExistsCeil_of_roundOracleCeil (h : RoundOracleExistsCeil) :
    AdaptiveOracleExistsCeil := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, c, hc0, hc1, hO⟩ := h r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil
  exact exists_adaptive_strategy_of_roundOracle H hc0 hc1 hβ
    (hO H d hd hd0 huni hreg hcodeg hceil)

/-- **Converse: the one-round atom is no stronger than the interface.**  A single matching covering a
`(1-β)`-fraction already realises a one-round oracle, so `RoundOracleExistsCeil` is EQUIVALENT to
`NibbleTheoremMostCeil` (together with `adaptiveOracleExistsCeil_of_roundOracleCeil` and
`nibbleTheoremMostCeil_of_adaptiveOracleCeil`).  The peeling above therefore loses nothing. -/
theorem roundOracleExistsCeil_of_nibbleTheoremMostCeil (h : NibbleTheoremMostCeil) :
    RoundOracleExistsCeil := by
  intro r hr β hβ
  rcases le_or_gt 1 β with hβ1 | hβ1
  · -- `β ≥ 1` is vacuous: more than a `β`-fraction can never be uncovered
    refine ⟨1, one_pos, 1, one_pos, 1, one_pos, 1, one_pos, le_rfl, ?_⟩
    intro V _ _ H d _ _ _ _ _ _
    refine ⟨fun _ _ => True, trivial, ?_⟩
    intro H' S _ hlt
    exfalso
    have hS : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    nlinarith
  · obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := h r hr β hβ
    refine ⟨μ, hμ, η, hη, d₀, hd₀, 1 - β, by linarith, by linarith, ?_⟩
    intro V _ _ H d hd hd0 huni hreg hcodeg hceil
    obtain ⟨M, hM, hcard⟩ := hmain H d hd hd0 huni hreg hcodeg hceil
    have hrpos : (0 : ℝ) < r := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    have hsc : ((support M).card : ℝ) = (r : ℝ) * (M.card : ℝ) := by
      exact_mod_cast matching_support_card huni hM
    refine hasRoundOracle_of_matching H hM ?_
    rw [hsc]
    have hid : (r : ℝ) * ((1 - β) * ((Fintype.card V : ℝ) / r))
        = (1 - β) * (Fintype.card V : ℝ) := by field_simp
    calc (1 - β) * (Fintype.card V : ℝ)
        = (r : ℝ) * ((1 - β) * ((Fintype.card V : ℝ) / r)) := hid.symm
      _ ≤ (r : ℝ) * (M.card : ℝ) := mul_le_mul_of_nonneg_left hcard hrpos.le

/-- **The corrected single-round research kernel (DELEGATE).**  One nibble round at the current
residual, covering a fixed fraction `c` of the still-uncovered vertices while re-establishing the
round invariant, for inputs carrying the GLOBAL degree ceiling `deg ≤ (1+μ)d` (which excludes the
star counterexample).  Its scalar feasibility is `AdaptiveSchedule.adaptive_crux_satisfiable`; the
per-round retention is supplied by the Freedman concentration bricks
(`exists_good_retention_freedman`, `exists_good_round_freedman_uncond`).  By
`adaptiveOracleExistsCeil_of_roundOracleCeil` / `roundOracleExistsCeil_of_nibbleTheoremMostCeil` this
atom is equivalent to `NibbleTheoremMostCeil`, and it is now the SOLE remaining obligation: the round
iteration and the rate bookkeeping have been discharged in `LeanPool.AsymptoticTrianglePacking.Internal.AdaptiveRounds`.

**STEP 4 (this revision).**  The atom is now further peeled in `LeanPool.AsymptoticTrianglePacking.Internal.RoundOracleKernel`: the whole
parameter selection (`μ`, `η`, `d₀`, the covering fraction `c = 1/(512r)`, the round budget `T`, the
relative slack `ε` and the exceptional-growth budget `δ`), the round invariant `LeanPool.AsymptoticTrianglePacking.Internal.CeilRoundInv`
together with its initialisation and its persistence, and the geometric decay of the uncovered count
are all discharged there (`exists_roundOracle_params_of_nibbleRoundStep`, placeholder-free).  The only
remaining input is the purely probabilistic single round `LeanPool.AsymptoticTrianglePacking.Internal.NibbleRoundStep`. -/
theorem roundOracleExistsCeil_of_nibbleRoundStep (hstep : NibbleRoundStep) :
    RoundOracleExistsCeil :=
  fun r hr β hβ => exists_roundOracle_params_of_nibbleRoundStep hstep r hr β hβ

/-- **The corrected adaptive research kernel**, from the single-round atom. -/
theorem adaptiveOracleExistsCeil_of_nibbleRoundStep (hstep : NibbleRoundStep) :
    AdaptiveOracleExistsCeil :=
  adaptiveOracleExistsCeil_of_roundOracleCeil (roundOracleExistsCeil_of_nibbleRoundStep hstep)

/-- **`NibbleTheorem` via the ceiling route.**  `NibbleTheorem` consumes `NearlyRegular` (full
`(1±μ)` degree control), which supplies the ceiling for free, so the corrected ceiling interface
suffices. -/
theorem nibbleTheorem_of_nibbleRoundStep (hstep : NibbleRoundStep) : NibbleTheorem :=
  (nibbleTheoremMostCeil_of_adaptiveOracleCeil
    (adaptiveOracleExistsCeil_of_nibbleRoundStep hstep)).nibbleTheorem

/-
**HISTORICAL NOTE (kept for the record).**  The three declarations above used to be stated
unconditionally,

```
theorem roundOracleExistsCeil_holds : RoundOracleExistsCeil :=
  fun r hr β hβ => exists_roundOracle_params_of_nibbleRoundStep nibbleRoundStep_holds r hr β hβ
theorem adaptiveOracleExistsCeil_holds : AdaptiveOracleExistsCeil :=
  adaptiveOracleExistsCeil_of_roundOracleCeil roundOracleExistsCeil_holds
theorem nibbleTheorem_holds : NibbleTheorem :=
  (nibbleTheoremMostCeil_of_adaptiveOracleCeil adaptiveOracleExistsCeil_holds).nibbleTheorem
```

resting on `nibbleRoundStep_holds : NibbleRoundStep`.  That obligation is FALSE
(`LeanPool.AsymptoticTrianglePacking.Internal.not_nibbleRoundStep`, refuted on the complete bipartite witness `K_{m,8m}`), and the
declaration `nibbleRoundStep_holds` has since been removed from `LeanPool.AsymptoticTrianglePacking.Internal.RoundOracleKernel`, so the
unconditional forms no longer elaborate.  They are replaced above by the honest hypothetical forms.
The live route is the tight-band one: `LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundHyp` (`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound`) and the
assembly `LeanPool.AsymptoticTrianglePacking.Internal.nibbleTheoremMostCeil_of_sharpRound` (`LeanPool.AsymptoticTrianglePacking.Internal.TightAssembly`).
-/

end LeanPool.AsymptoticTrianglePacking.Internal
