/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

/-
# LeanPool.AsymptoticTrianglePacking.Internal — the CEILING one-round oracle: invariant, glue, and the residual research core

`LeanPool.AsymptoticTrianglePacking.Internal.AdaptiveAssembly` peels the whole outer loop of the LeanPool.AsymptoticTrianglePacking.Internal down to the single-round atom
`RoundOracleExistsCeil` (all iteration and rate arithmetic being discharged in
`LeanPool.AsymptoticTrianglePacking.Internal.AdaptiveRounds`).  This file peels that atom one layer further, isolating the *probabilistic*
content of one LeanPool.AsymptoticTrianglePacking.Internal round from all of the bookkeeping.

The architecture:

* `loScale`, `hiScale` — the two degree scales of the round schedule.  With retention
  `p_k = 1/(2 r Δ_k)` (so `r Δ_k p_k = 1/2`) a round halves all degrees, up to a relative slack `ε`;
  hence the lower scale `L_k = (d/2)(1/2-ε)^k` and the upper scale `U_k = 2d(1/2+ε)^k`.  Their ratio
  `U_k / L_k = 4·((1/2+ε)/(1/2-ε))^k` stays `≤ 8` for the (bounded) number of rounds that the outer
  loop performs, provided `ε` is small — this is `hiScale_le_eight_loScale`.

* `CeilRoundInv` — the round invariant actually threaded by the oracle.  It says: after `k` rounds
  (with the uncovered count already down to `(1-c)^k|V|`) the current residual contains a
  sub-hypergraph `K` which is `r`-uniform, has small codegree, avoids the covered set `S`, has ALL
  degrees `≤ U_k`, and has degree `≥ L_k` at every still-uncovered vertex outside a small
  exceptional set.  The invariant is *existential over a sub-hypergraph*: this is what allows a round
  to prune the (few) vertices whose residual degree is too large, which is how the global degree
  ceiling is re-established each round without a union bound over the `|V|` vertices.

* `NibbleRoundStep` — ONE LeanPool.AsymptoticTrianglePacking.Internal round at the current scale: covering a constant fraction of the
  good uncovered vertices, halving the degree scale up to the relative slack `ε`, and growing the
  exceptional set by at most `δ|V|`.

* `NibbleRoundProb` — the intended isolated research core: the PROBABILISTIC half of that round,
  controlling only *fractions* of vertices (all but a `δlow` fraction keep degree `≥ (1/2-ε/2)L`,
  and at most a `blow` fraction exceed the new ceiling).  **It is FALSE**: see
  `LeanPool.AsymptoticTrianglePacking.Internal.not_nibbleRoundProb` in `LeanPool.AsymptoticTrianglePacking.Internal.RoundProbRefutation` and the long comment before
  `nibbleRoundStep_of_nibbleRoundProb` below.  Its cover clause is true and unconditional
  (`LeanPool.AsymptoticTrianglePacking.Internal.exists_round_cover_fraction` in `LeanPool.AsymptoticTrianglePacking.Internal.RoundCoverFraction`); its two degree clauses are
  jointly unsatisfiable on the complete bipartite graph `K_{m,8m}`, because the ceiling is measured
  against the global upper scale `U` and the floor against the global lower scale `L` while a round
  does not halve a spread-out degree distribution uniformly.  `NibbleRoundStep` itself is now ALSO
  refuted — `LeanPool.AsymptoticTrianglePacking.Internal.not_nibbleRoundStep` in `LeanPool.AsymptoticTrianglePacking.Internal.RoundStepRefutation`, by a two-sided edge count
  on the same witness which no pruning can evade — so this file has no `sorry` left, and no unproved
  obligation either: what it contains is a reduction to a statement that is false.  See the long
  comment where `nibbleRoundStep_holds` used to be, and `LeanPool.AsymptoticTrianglePacking.Internal.NibbleRoundStepVar` for the shape a
  repaired round has to have.

* `nibbleRoundStep_of_nibbleRoundProb` — sorry-free (but, by the above, vacuous): the deterministic
  half of the round assuming the refuted probabilistic half.  The
  global ceiling is restored by pruning (`LeanPool.AsymptoticTrianglePacking.Internal.pruneHigh`) and the pruning damage is bounded by
  `LeanPool.AsymptoticTrianglePacking.Internal.card_pruneDamaged_le_of_bounds`.

* `exists_roundOracle_params_of_nibbleRoundStep` — the reduction (sorry-free): the whole parameter
  selection (`μ`, `η`, `d₀`, `c`, the round budget `T`, the slack `ε` and the exceptional growth
  `δ`), the initialisation of the invariant, its persistence and the geometric decay of the
  uncovered count are all discharged here.  It is what
  `LeanPool.AsymptoticTrianglePacking.Internal.roundOracleExistsCeil_of_nibbleRoundStep` consumes.

Everything in this file is sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
The consumers in `LeanPool.AsymptoticTrianglePacking.Internal.AdaptiveAssembly` now carry `NibbleRoundStep` as an explicit hypothesis,
since it cannot be discharged.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.AdaptiveRounds
import LeanPool.AsymptoticTrianglePacking.Internal.RegularMost
import LeanPool.AsymptoticTrianglePacking.Internal.Round
import LeanPool.AsymptoticTrianglePacking.Internal.Pruning
import LeanPool.AsymptoticTrianglePacking.Internal.MarkovVertices
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Monotonicity

open Hypergraph Finset

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-! ## Elementary monotonicity glue -/

section Glue

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Uniformity passes to sub-hypergraphs. -/
theorem isUniform_of_subset {K H : Finset (Finset V)} {r : ℕ} (hKH : K ⊆ H)
    (hH : IsUniform H r) : IsUniform K r := fun e he => hH e (hKH he)

/-- Codegree bounds pass to sub-hypergraphs. -/
theorem codegreeBounded_of_subset {K H : Finset (Finset V)} {C : ℝ} (hKH : K ⊆ H)
    (hH : CodegreeBounded H C) : CodegreeBounded K C := by
  intro x y hxy
  refine le_trans ?_ (hH x y hxy)
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hKH)

/-- The residual is monotone in its first argument. -/
theorem residual_mono {H₁ H₂ R : Finset (Finset V)} (h : H₁ ⊆ H₂) :
    Hypergraph.residual H₁ R ⊆ Hypergraph.residual H₂ R :=
  Finset.filter_subset_filter _ h

/-- Every vertex covered by the round matching of `R' ⊆ K` lies on an edge of `K`. -/
theorem support_roundMatching_subset_support {K R' : Finset (Finset V)} (hR' : R' ⊆ K) :
    support (roundMatching R') ⊆ support K := by
  intro v hv
  simp only [support, Finset.mem_biUnion, id] at hv ⊢
  obtain ⟨e, he, hve⟩ := hv
  exact ⟨e, hR' (roundMatching_subset R' he), hve⟩

/-- If every edge of `K` avoids `S`, then so does the support of the round matching of any
`R' ⊆ K`. -/
theorem disjoint_support_roundMatching {K R' : Finset (Finset V)} {S : Finset V}
    (hR' : R' ⊆ K) (hK : ∀ e ∈ K, Disjoint e S) :
    Disjoint (support (roundMatching R')) S := by
  rw [Finset.disjoint_left]
  intro v hv hvS
  simp only [support, Finset.mem_biUnion, id] at hv
  obtain ⟨e, he, hve⟩ := hv
  exact (Finset.disjoint_left.mp (hK e (hR' (roundMatching_subset R' he))) hve) hvS

/-- **Edge-count lower bound at the current scale.**  If every uncovered vertex outside the
exceptional set has degree `≥ L`, then `r·|K|` is at least `L` times the number of good uncovered
vertices.  (This is what converts the round's covering guarantee, which is proportional to `|K|`,
into a guarantee proportional to the uncovered count.) -/
theorem edge_count_lower_uncovered [Fintype V] {K : Finset (Finset V)} {r : ℕ}
    (hr : IsUniform K r) (S Exc : Finset V) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ v : V, v ∉ S → v ∉ Exc → L ≤ (degree K v : ℝ)) :
    (((Fintype.card V : ℝ) - (S.card : ℝ)) - (Exc.card : ℝ)) * L ≤ (r : ℝ) * (K.card : ℝ) := by
  classical
  obtain ⟨W, hWdef⟩ : ∃ W : Finset V, W = (Finset.univ : Finset V) \ (S ∪ Exc) := ⟨_, rfl⟩
  have hcard0 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (S ∪ Exc))
  rw [Finset.card_univ] at hcard0
  have hWcard : ((Fintype.card V : ℝ) - (S.card : ℝ)) - (Exc.card : ℝ) ≤ (W.card : ℝ) := by
    have h1 : (S ∪ Exc).card ≤ S.card + Exc.card := Finset.card_union_le S Exc
    have h2 : W.card = Fintype.card V - (S ∪ Exc).card := by
      rw [hWdef]; omega
    have h3 : (S ∪ Exc).card ≤ Fintype.card V := Finset.card_le_univ _
    have h4 : (W.card : ℝ) = (Fintype.card V : ℝ) - ((S ∪ Exc).card : ℝ) := by
      rw [h2]
      push_cast [Nat.cast_sub h3]
      ring
    have h5 : (((S ∪ Exc).card : ℕ) : ℝ) ≤ (S.card : ℝ) + (Exc.card : ℝ) := by
      exact_mod_cast h1
    rw [h4]
    linarith
  have hsum : (W.card : ℝ) * L ≤ ∑ v ∈ W, (degree K v : ℝ) := by
    have : ∑ _v ∈ W, L ≤ ∑ v ∈ W, (degree K v : ℝ) := by
      refine Finset.sum_le_sum (fun v hv => ?_)
      rw [hWdef, Finset.mem_sdiff, Finset.mem_union] at hv
      exact hL v (fun h => hv.2 (Or.inl h)) (fun h => hv.2 (Or.inr h))
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hall : ∑ v ∈ W, (degree K v : ℝ) ≤ ∑ v : V, (degree K v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => Nat.cast_nonneg _)
  have htotal : ∑ v : V, (degree K v : ℝ) = (r : ℝ) * (K.card : ℝ) := by
    have hs := Hypergraph.sum_degree K hr
    have hc : ((∑ v : V, degree K v : ℕ) : ℝ) = ((r * K.card : ℕ) : ℝ) := by rw [hs]
    push_cast at hc
    exact hc
  have hmul : (((Fintype.card V : ℝ) - (S.card : ℝ)) - (Exc.card : ℝ)) * L ≤ (W.card : ℝ) * L :=
    mul_le_mul_of_nonneg_right hWcard hL0
  linarith

end Glue

/-! ## The two degree scales of the round schedule -/

/-- The lower degree scale after `k` rounds: a round halves the degrees, up to relative slack `ε`. -/
noncomputable def loScale (d ε : ℝ) (k : ℕ) : ℝ := d / 2 * (1 / 2 - ε) ^ k

/-- The upper degree scale after `k` rounds (the round's global degree ceiling). -/
noncomputable def hiScale (d ε : ℝ) (k : ℕ) : ℝ := 2 * d * (1 / 2 + ε) ^ k

@[simp] theorem loScale_zero (d ε : ℝ) : loScale d ε 0 = d / 2 := by simp [loScale]

@[simp] theorem hiScale_zero (d ε : ℝ) : hiScale d ε 0 = 2 * d := by simp [hiScale]

theorem loScale_succ (d ε : ℝ) (k : ℕ) :
    loScale d ε (k + 1) = (1 / 2 - ε) * loScale d ε k := by
  simp [loScale, pow_succ]; ring

theorem hiScale_succ (d ε : ℝ) (k : ℕ) :
    hiScale d ε (k + 1) = (1 / 2 + ε) * hiScale d ε k := by
  simp [hiScale, pow_succ]; ring

theorem hiScale_nonneg {d ε : ℝ} (hd : 0 ≤ d) (hε : 0 ≤ ε) (k : ℕ) : 0 ≤ hiScale d ε k := by
  have : (0 : ℝ) ≤ 1 / 2 + ε := by linarith
  exact mul_nonneg (by linarith) (pow_nonneg this k)

theorem loScale_pos {d ε : ℝ} (hd : 0 < d) (hε : ε ≤ 1 / 8) (k : ℕ) : 0 < loScale d ε k := by
  have : (0 : ℝ) < 1 / 2 - ε := by linarith
  exact mul_pos (by linarith) (pow_pos this k)

/-- With `ε ≤ 1/8`, the lower scale is at least `(d/2)·(1/4)^k`. -/
theorem loScale_ge {d ε : ℝ} (hd : 0 ≤ d) (hε : ε ≤ 1 / 8) (k : ℕ) :
    d / 2 * (1 / 4) ^ k ≤ loScale d ε k := by
  have h : (1 / 4 : ℝ) ≤ 1 / 2 - ε := by linarith
  have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/4) h k
  exact mul_le_mul_of_nonneg_left this (by linarith)

/-- `(1+u)^T ≤ 2` whenever `u ≥ 0` and `T·u ≤ 1/2`. -/
theorem one_add_pow_le_two {u : ℝ} (hu : 0 ≤ u) {T : ℕ} (hT : (T : ℝ) * u ≤ 1 / 2) :
    (1 + u) ^ T ≤ 2 := by
  have h1 : (1 + u) ^ T ≤ (Real.exp u) ^ T :=
    pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp u) T
  have h2 : (Real.exp u) ^ T = Real.exp ((T : ℝ) * u) := by
    rw [← Real.exp_nat_mul]
  have h3 : Real.exp ((T : ℝ) * u) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hT
  have h4 : Real.exp (1 / 2) ≤ 2 := by
    have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos _
    nlinarith [Real.exp_one_lt_d9]
  calc (1 + u) ^ T ≤ (Real.exp u) ^ T := h1
    _ = Real.exp ((T : ℝ) * u) := h2
    _ ≤ Real.exp (1 / 2) := h3
    _ ≤ 2 := h4

/-- **Bounded ratio of the two scales.**  With `ε = 1/(16(T+1))` the upper scale stays within a
factor `8` of the lower scale for all `k ≤ T`. -/
theorem hiScale_le_eight_loScale {d : ℝ} (hd : 0 ≤ d) (T : ℕ) {k : ℕ} (hk : k ≤ T) :
    hiScale d (1 / (16 * ((T : ℝ) + 1))) k ≤ 8 * loScale d (1 / (16 * ((T : ℝ) + 1))) k := by
  set ε : ℝ := 1 / (16 * ((T : ℝ) + 1)) with hεdef
  have hTpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hε8 : ε ≤ 1 / 16 := by
    rw [hεdef]
    have h16 : (16 : ℝ) ≤ 16 * ((T : ℝ) + 1) := by
      have : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
      nlinarith
    exact one_div_le_one_div_of_le (by norm_num) h16
  -- reduce to `((1/2+ε)/(1/2-ε))^k ≤ 2`, i.e. `(1/2+ε)^k ≤ 2 (1/2-ε)^k`
  have hlow : (0 : ℝ) < 1 / 2 - ε := by linarith
  have hstep : (1 / 2 + ε) ≤ (1 + 8 * ε) * (1 / 2 - ε) := by nlinarith
  have hpow : (1 / 2 + ε) ^ k ≤ (1 + 8 * ε) ^ k * (1 / 2 - ε) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hstep k
  have hbudget : ((k : ℝ)) * (8 * ε) ≤ 1 / 2 := by
    have hkT : (k : ℝ) ≤ (T : ℝ) := by exact_mod_cast hk
    rw [hεdef]
    rw [show (k : ℝ) * (8 * (1 / (16 * ((T : ℝ) + 1)))) = (k : ℝ) / (2 * ((T : ℝ) + 1)) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h2 : (1 + 8 * ε) ^ k ≤ 2 := one_add_pow_le_two (by linarith) hbudget
  have hposk : (0 : ℝ) < (1 / 2 - ε) ^ k := pow_pos hlow k
  have hchain : (1 / 2 + ε) ^ k ≤ 2 * (1 / 2 - ε) ^ k := by
    calc (1 / 2 + ε) ^ k ≤ (1 + 8 * ε) ^ k * (1 / 2 - ε) ^ k := hpow
      _ ≤ 2 * (1 / 2 - ε) ^ k := by
          exact mul_le_mul_of_nonneg_right h2 (le_of_lt hposk)
  simp only [hiScale, loScale]
  nlinarith only [hchain, hd]

/-! ## The round invariant -/

/-- **The one-round invariant threaded by the ceiling oracle.**  `CeilRoundInv r d μ ε δ c T H' S`
says: for some round index `k ≤ T`, the uncovered count is already down to `(1-c)^k |V|`, and the
current residual `H'` contains a sub-hypergraph `K` which is `r`-uniform, has codegree `≤ μd`, whose
edges avoid the covered set `S`, whose degrees are all `≤ hiScale d ε k`, and whose degree at every
uncovered vertex outside an exceptional set of size `≤ (k+1)δ|V|` is `≥ loScale d ε k`. -/
def CeilRoundInv (r : ℕ) (d μ ε δ c : ℝ) (T : ℕ) {V : Type} [Fintype V] [DecidableEq V]
    (H' : Finset (Finset V)) (S : Finset V) : Prop :=
  ∃ k : ℕ, k ≤ T ∧
    ((Fintype.card V : ℝ) - (S.card : ℝ) ≤ (1 - c) ^ k * (Fintype.card V : ℝ)) ∧
    ∃ K : Finset (Finset V), K ⊆ H' ∧ IsUniform K r ∧ CodegreeBounded K (μ * d) ∧
      (∀ e ∈ K, Disjoint e S) ∧
      (∀ v : V, (degree K v : ℝ) ≤ hiScale d ε k) ∧
      ∃ Exc : Finset V, (Exc.card : ℝ) ≤ ((k : ℝ) + 1) * δ * (Fintype.card V : ℝ) ∧
        ∀ v : V, v ∉ S → v ∉ Exc → loScale d ε k ≤ (degree K v : ℝ)

/-! ## The isolated research core: one LeanPool.AsymptoticTrianglePacking.Internal round -/

/-- **The single LeanPool.AsymptoticTrianglePacking.Internal round (research core).**  For every uniformity `r ≥ 2`, every exceptional
growth budget `δ > 0` and every relative slack `ε ∈ (0, 1/8]` there are a codegree ratio `ecod > 0`
and a degree threshold `L₀` such that: any `r`-uniform `K` avoiding the covered set `S`, with
codegree `≤ ecod·L`, all degrees `≤ U ≤ 8L` and degree `≥ L ≥ L₀` at every uncovered vertex outside
`Exc`, admits a retained set `R' ⊆ K` whose round matching

* covers at least a `1/(256r)` fraction of the good uncovered vertices, and
* leaves a pruned sub-hypergraph `K'` of the residual whose degrees are all `≤ (1/2+ε)U` and which
  still has degree `≥ (1/2-ε)L` at every uncovered vertex outside an exceptional set larger by at
  most `δ|V|`.

This is the standard LeanPool.AsymptoticTrianglePacking.Internal round: retention probability `p = 1/(2rΔ)` with `Δ = ⌈U⌉` (so
`rΔp = 1/2`, halving all degrees in expectation), a first-moment/Markov selection of one outcome
which simultaneously covers many vertices and has few vertices with an atypical residual degree, and
a deterministic pruning of the few vertices whose residual degree exceeds `(1/2+ε)U` (which is what
re-establishes the global ceiling; the pruning damages the degree of at most `O(rδ|V|/ε)` further
vertices, absorbed into the exceptional set). -/
def NibbleRoundStep : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (δ ε : ℝ), 0 < δ → 0 < ε → ε ≤ 1 / 8 →
    ∃ ecod : ℝ, 0 < ecod ∧ ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (K : Finset (Finset V)) (S Exc : Finset V)
        (L U : ℝ), L₀ ≤ L → U ≤ 8 * L → 0 ≤ U →
        IsUniform K r → CodegreeBounded K (ecod * L) →
        (∀ e ∈ K, Disjoint e S) → (∀ v : V, (degree K v : ℝ) ≤ U) →
        (∀ v : V, v ∉ S → v ∉ Exc → L ≤ (degree K v : ℝ)) →
        ∃ R' : Finset (Finset V), R' ⊆ K ∧
          (1 / (256 * (r : ℝ))) * (((Fintype.card V : ℝ) - (S.card : ℝ)) - (Exc.card : ℝ))
            ≤ ((support (roundMatching R')).card : ℝ) ∧
          ∃ K' : Finset (Finset V), K' ⊆ Hypergraph.residual K R' ∧
            (∀ v : V, (degree K' v : ℝ) ≤ (1 / 2 + ε) * U) ∧
            ∃ Exc' : Finset V, (Exc'.card : ℝ) ≤ (Exc.card : ℝ) + δ * (Fintype.card V : ℝ) ∧
              ∀ v : V, v ∉ (S ∪ support (roundMatching R')) → v ∉ Exc' →
                (1 / 2 - ε) * L ≤ (degree K' v : ℝ)

/-- **The PROBABILISTIC half of one LeanPool.AsymptoticTrianglePacking.Internal round.**  Same setting as `NibbleRoundStep`, but the two
deterministic ingredients are stripped off: the round only has to produce a retained set `R'` whose
round matching covers a `1/(256r)` fraction of the good uncovered vertices, such that

* all but a `δlow` fraction of the good uncovered vertices keep residual degree `≥ (1/2-ε/2)L`
  (the degrees are halved, up to the relative slack `ε/2`), and
* at most a `blow` fraction of the vertices have residual degree above the new ceiling `(1/2+ε)U`.

No global degree ceiling on the residual is demanded: it is restored deterministically by pruning
(`LeanPool.AsymptoticTrianglePacking.Internal.pruneHigh`), which is exactly what `nibbleRoundStep_of_nibbleRoundProb` does.  Since only
*fractions* of vertices have to be controlled, this statement needs no union bound over the vertex
set — per-vertex tail estimates plus Markov's inequality suffice, which is what makes it provable
with a degree threshold `L₀` independent of `|V|`. -/
def NibbleRoundProb : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (δlow blow ε : ℝ), 0 < δlow → 0 < blow → 0 < ε → ε ≤ 1 / 8 →
    ∃ ecod : ℝ, 0 < ecod ∧ ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (K : Finset (Finset V)) (S Exc : Finset V)
        (L U : ℝ), L₀ ≤ L → U ≤ 8 * L → 0 ≤ U →
        IsUniform K r → CodegreeBounded K (ecod * L) →
        (∀ e ∈ K, Disjoint e S) → (∀ v : V, (degree K v : ℝ) ≤ U) →
        (∀ v : V, v ∉ S → v ∉ Exc → L ≤ (degree K v : ℝ)) →
        ∃ R' : Finset (Finset V), R' ⊆ K ∧
          (1 / (256 * (r : ℝ))) * (((Fintype.card V : ℝ) - (S.card : ℝ)) - (Exc.card : ℝ))
            ≤ ((support (roundMatching R')).card : ℝ) ∧
          (∃ Elow : Finset V, (Elow.card : ℝ) ≤ δlow * (Fintype.card V : ℝ) ∧
            ∀ v : V, v ∉ (S ∪ support (roundMatching R')) → v ∉ Exc → v ∉ Elow →
              (1 / 2 - ε / 2) * L ≤ (degree (Hypergraph.residual K R') v : ℝ)) ∧
          ((highDeg (Hypergraph.residual K R') ((1 / 2 + ε) * U)).card : ℝ)
            ≤ blow * (Fintype.card V : ℝ)

/-
**`NibbleRoundProb` IS FALSE.**  The statement below was the intended remaining obligation:

```
/-- **The probabilistic round — the sole remaining obligation of the LeanPool.AsymptoticTrianglePacking.Internal.** -/
theorem nibbleRoundProb_holds : NibbleRoundProb := ...
```

It is refuted in `LeanPool.AsymptoticTrianglePacking.Internal.RoundProbRefutation` by `LeanPool.AsymptoticTrianglePacking.Internal.not_nibbleRoundProb`: the complete
bipartite graph `K_{m,8m}` (`r = 2`, hubs of degree `8m = U`, leaves of degree `m = L`, codegree
`≤ 1`, `|V| = 9m`) satisfies every hypothesis of `NibbleRoundProb`, yet for EVERY retained set
`R' ⊆ K` the two degree clauses conflict: a round matching uses up a distinct hub per edge, hence
covers at most `m` leaves, so an uncovered hub keeps residual degree `≥ 7m > 5m = (1/2+ε)U` and is
high; pushing the high set below `blow·|V|` forces all but `9·blow·m` hubs to be covered, and then
the `≥ 7m` uncovered leaves all have residual degree `≤ 9·blow·m < (1/2-ε/2)L`, far more low
vertices than the allowed `δlow·|V|`.

The reason is structural, not a slack issue: the ceiling clause is measured against the GLOBAL upper
scale `U` and the floor clause against the GLOBAL lower scale `L`, while a LeanPool.AsymptoticTrianglePacking.Internal round only halves
degrees *relative to the local degree distribution*.  As soon as the degrees genuinely spread over
the band `[L, 8L]` that `CeilRoundInv` permits, no retained set halves them uniformly, and the
unpruned residual cannot meet a global ceiling of `(1/2+ε)U`.

What survives:

* the COVER clause of `NibbleRoundProb` is true and is proved unconditionally in
  `LeanPool.AsymptoticTrianglePacking.Internal.RoundCoverFraction` (`LeanPool.AsymptoticTrianglePacking.Internal.exists_round_cover_fraction`);
* the consumer `NibbleRoundStep` is NOT refuted, because it may prune the residual before the
  ceiling is imposed (`K' ⊆ residual K R'`), and on `K_{m,8m}` a *balanced* pruning of the hubs down
  to `5m` costs each leaf only about `(3/8)m` of its `m` edges, leaving it above `(1/2-ε)L`.  The
  remaining obligation of the LeanPool.AsymptoticTrianglePacking.Internal is therefore `nibbleRoundStep_holds` itself: a probabilistic
  round together with a pruning that spreads its damage evenly (the greedy pruning of
  `nibbleRoundStep_of_nibbleRoundProb` is not enough, since it is driven by the number of high
  vertices, which the example makes large).

`nibbleRoundStep_of_nibbleRoundProb` below is kept: it is a correct implication, but it is now known
to be vacuous.
-/

/-- **The full LeanPool.AsymptoticTrianglePacking.Internal round from its probabilistic half (sorry-free).**  The global degree ceiling
of the residual is restored by pruning at level `(1/2+ε)U` (`LeanPool.AsymptoticTrianglePacking.Internal.pruneHigh`); by
`LeanPool.AsymptoticTrianglePacking.Internal.card_pruneDamaged_le_of_bounds` the pruning lowers the degree by more than `(ε/2)L` at no
more than `r · blow|V| · U / ((ε/2)L) ≤ δ|V|/2` vertices, which — together with the `δlow|V| = δ|V|/2`
vertices of atypically small residual degree — is absorbed into the exceptional set. -/
theorem nibbleRoundStep_of_nibbleRoundProb (hprob : NibbleRoundProb) : NibbleRoundStep := by
  classical
  intro r hr δ ε hδ0 hε0 hε8
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  set δlow : ℝ := δ / 2 with hδlowdef
  set blow : ℝ := δ * ε / (64 * (r : ℝ)) with hblowdef
  have hδlow0 : 0 < δlow := by rw [hδlowdef]; linarith
  have hblow0 : 0 < blow := by rw [hblowdef]; positivity
  obtain ⟨ecod, hecod0, L₀, hL₀0, hround⟩ := hprob r hr δlow blow ε hδlow0 hblow0 hε0 hε8
  refine ⟨ecod, hecod0, L₀, hL₀0, ?_⟩
  intro V _ _ K S Exc L U hL hU8 hU0 huni hcod hdisj hhi hlo
  obtain ⟨R', hR'K, hcov, ⟨Elow, hElow, hlowdeg⟩, hhigh⟩ :=
    hround K S Exc L U hL hU8 hU0 huni hcod hdisj hhi hlo
  have hLpos : 0 < L := lt_of_lt_of_le hL₀0 hL
  have hNnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  set G : Finset (Finset V) := Hypergraph.residual K R' with hGdef
  set M : ℝ := (1 / 2 + ε) * U with hMdef
  set t : ℝ := ε / 2 * L with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have hM0 : 0 ≤ M := by rw [hMdef]; nlinarith
  have hGK : G ⊆ K := Hypergraph.residual_subset K R'
  have hGuni : IsUniform G r := isUniform_of_subset hGK huni
  have hGdeg : ∀ u : V, (degree G u : ℝ) ≤ U := by
    intro u
    refine le_trans ?_ (hhi u)
    exact_mod_cast Hypergraph.degree_mono hGK u
  -- the pruning damage is at most `δ|V|/2`
  have hdam : ((pruneDamaged G M t).card : ℝ) ≤ δ / 2 * (Fintype.card V : ℝ) := by
    have hb := card_pruneDamaged_le_of_bounds (t := t) hGuni hGdeg hU0 hhigh
    have hkey : (r : ℝ) * (blow * (Fintype.card V : ℝ)) * U
        ≤ (δ / 2 * (Fintype.card V : ℝ)) * t := by
      have hrb : (r : ℝ) * blow = δ * ε / 64 := by
        rw [hblowdef]; field_simp
      have hlhs : (r : ℝ) * (blow * (Fintype.card V : ℝ)) * U
          = (δ * ε / 64) * ((Fintype.card V : ℝ) * U) := by
        rw [← hrb]; ring
      have hrhs : (δ / 2 * (Fintype.card V : ℝ)) * t
          = (δ * ε / 4) * ((Fintype.card V : ℝ) * L) := by
        rw [htdef]; ring
      rw [hlhs, hrhs]
      have hNU : (Fintype.card V : ℝ) * U ≤ (Fintype.card V : ℝ) * (8 * L) :=
        mul_le_mul_of_nonneg_left hU8 hNnn
      have hcoef : (0 : ℝ) < δ * ε / 64 := by positivity
      nlinarith [mul_nonneg hNnn hLpos.le]
    have h1 : ((pruneDamaged G M t).card : ℝ) * t ≤ (δ / 2 * (Fintype.card V : ℝ)) * t :=
      le_trans hb hkey
    exact le_of_mul_le_mul_right h1 htpos
  refine ⟨R', hR'K, hcov, pruneHigh G M, pruneHigh_subset G M, ?_,
    Exc ∪ Elow ∪ pruneDamaged G M t, ?_, ?_⟩
  · -- the restored ceiling
    intro v
    exact degree_pruneHigh_le G hM0 v
  · -- the exceptional set grew by at most `δ|V|`
    have hcard1 : ((Exc ∪ Elow ∪ pruneDamaged G M t).card : ℝ)
        ≤ ((Exc ∪ Elow).card : ℝ) + ((pruneDamaged G M t).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (Exc ∪ Elow) (pruneDamaged G M t)
    have hcard2 : ((Exc ∪ Elow).card : ℝ) ≤ (Exc.card : ℝ) + (Elow.card : ℝ) := by
      exact_mod_cast Finset.card_union_le Exc Elow
    have hElow' : (Elow.card : ℝ) ≤ δ / 2 * (Fintype.card V : ℝ) := by
      rw [hδlowdef] at hElow; exact hElow
    linarith
  · -- the restored lower bound
    intro v hvSsupp hvExc'
    have hvExc : v ∉ Exc := fun h => hvExc' (by simp [h])
    have hvElow : v ∉ Elow := fun h => hvExc' (by simp [h])
    have hvD : v ∉ pruneDamaged G M t := fun h => hvExc' (by simp [h])
    have hG : (1 / 2 - ε / 2) * L ≤ (degree G v : ℝ) := hlowdeg v hvSsupp hvExc hvElow
    have hdrop : (degree G v : ℝ) ≤ (degree (pruneHigh G M) v : ℝ) + t := by
      by_contra hcon
      push_neg at hcon
      exact hvD (by
        simp only [pruneDamaged, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hcon)
    have ht' : t = ε / 2 * L := htdef
    nlinarith [hG, hdrop]

/-
**`NibbleRoundStep` IS FALSE — the declaration below is kept for the record.**  It used to be the
sole remaining obligation of the LeanPool.AsymptoticTrianglePacking.Internal:

```
/-- **The single LeanPool.AsymptoticTrianglePacking.Internal round — the remaining obligation of the LeanPool.AsymptoticTrianglePacking.Internal.** -/
theorem nibbleRoundStep_holds : NibbleRoundStep := ...
```

It is refuted in `LeanPool.AsymptoticTrianglePacking.Internal.RoundStepRefutation` by `LeanPool.AsymptoticTrianglePacking.Internal.not_nibbleRoundStep`, on the SAME complete
bipartite witness `K_{m,8m}` that refutes `NibbleRoundProb` — but by a two-sided edge count which,
unlike the argument against `NibbleRoundProb`, survives an arbitrary pruning `K' ⊆ residual K R'`.

With `m` hubs of degree `8m = U` and `8m` leaves of degree `m = L`, every edge has one hub and one
leaf, so a round matching of size `k` covers exactly `k` hubs and `k` leaves.  Counting the edges of
`K'` from the hub side (a covered hub has residual degree `0`, every other hub obeys the ceiling)
and from the leaf side (every uncovered leaf outside `Exc'` obeys the floor) gives

  `(8m - k - δ·9m)·(1/2-ε)·m ≤ |K'| ≤ (m - k)·(1/2+ε)·8m`,

hence `7·|support M| ≤ (64ε + 18δ)·m` (`LeanPool.AsymptoticTrianglePacking.Internal.BipRef.bip_cover_le_of_step`).  Matching one edge
destroys `4m` units of hub *capacity* but only `m/2` units of leaf *demand*: on a band with
`U/L = 8` the round can therefore cover only an `O(ε + δ)` fraction of the vertices, whereas
`NibbleRoundStep` demands the fixed fraction `1/(256r)` for EVERY `δ, ε > 0`.

What survives, and how to repair it:

* the cover clause alone is true and unconditional (`LeanPool.AsymptoticTrianglePacking.Internal.exists_round_cover_fraction`), and so is
  the deterministic pruning machinery (`LeanPool.AsymptoticTrianglePacking.Internal.pruneHigh`, `LeanPool.AsymptoticTrianglePacking.Internal.card_pruneDamaged_le_of_bounds`);
* the obstruction is *not* probabilistic and not a slack issue: it is the `8 : 1` degree imbalance
  that `CeilRoundInv` permits.  A repaired round must either let its covering fraction degrade with
  `ε` and `δ` (`LeanPool.AsymptoticTrianglePacking.Internal.NibbleRoundStepVar` below — but then the round budget `T ≈ log(1/β)/c` no
  longer fits inside the band budget `k ≲ 1/(8ε)` of `hiScale_le_eight_loScale`, so the outer
  schedule of `exists_roundOracle_params_of_nibbleRoundStep` must be redesigned as well), or keep
  the degree band ratio `U/L` near `1` — i.e. genuinely re-establish near-regularity each round,
  which is what the classical LeanPool.AsymptoticTrianglePacking.Internal does and what makes the obstruction vanish (the loss term
  carries a factor `1 - L/U`).
-/

/-- **A repaired shape for the single LeanPool.AsymptoticTrianglePacking.Internal round.**  Identical to `NibbleRoundStep` except that
the covering fraction `cfrac` is produced by the round *after* seeing `δ` and `ε`, instead of being
the fixed constant `1/(256r)`.  This is the weakest change that is not refuted by the witness of
`LeanPool.AsymptoticTrianglePacking.Internal.not_nibbleRoundStep`, which forces `cfrac ≲ ε + δ/4` on a degree band of ratio `8`.

It is stated here for the record only: it is NOT proved, and — as explained in the comment above —
the outer schedule of `exists_roundOracle_params_of_nibbleRoundStep` (which fixes the covering
fraction before choosing `δ` and `ε`) cannot consume it as it stands. -/
def NibbleRoundStepVar : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (δ ε : ℝ), 0 < δ → 0 < ε → ε ≤ 1 / 8 →
    ∃ cfrac : ℝ, 0 < cfrac ∧ ∃ ecod : ℝ, 0 < ecod ∧ ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (K : Finset (Finset V)) (S Exc : Finset V)
        (L U : ℝ), L₀ ≤ L → U ≤ 8 * L → 0 ≤ U →
        IsUniform K r → CodegreeBounded K (ecod * L) →
        (∀ e ∈ K, Disjoint e S) → (∀ v : V, (degree K v : ℝ) ≤ U) →
        (∀ v : V, v ∉ S → v ∉ Exc → L ≤ (degree K v : ℝ)) →
        ∃ R' : Finset (Finset V), R' ⊆ K ∧
          cfrac * (((Fintype.card V : ℝ) - (S.card : ℝ)) - (Exc.card : ℝ))
            ≤ ((support (roundMatching R')).card : ℝ) ∧
          ∃ K' : Finset (Finset V), K' ⊆ Hypergraph.residual K R' ∧
            (∀ v : V, (degree K' v : ℝ) ≤ (1 / 2 + ε) * U) ∧
            ∃ Exc' : Finset V, (Exc'.card : ℝ) ≤ (Exc.card : ℝ) + δ * (Fintype.card V : ℝ) ∧
              ∀ v : V, v ∉ (S ∪ support (roundMatching R')) → v ∉ Exc' →
                (1 / 2 - ε) * L ≤ (degree K' v : ℝ)

/-! ## Auxiliary estimates of the schedule -/

/-- **The floor scale stays above the round threshold.**  With `d ≥ 2L₀·4^T` the floor scale
`loScale d ε k` is at least `L₀` for every `k ≤ T`. -/
theorem loScale_ge_threshold {d ε L₀ : ℝ} {T k : ℕ} (hd : 0 < d) (hε8 : ε ≤ 1 / 8)
    (hdL₀ : 2 * L₀ * 4 ^ T ≤ d) (hk : k ≤ T) : L₀ ≤ loScale d ε k := by
  refine le_trans ?_ (loScale_ge hd.le hε8 k)
  have h4 : (1 / 4 : ℝ) ^ T ≤ (1 / 4 : ℝ) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have hcancel : (4 : ℝ) ^ T * (1 / 4 : ℝ) ^ T = 1 := by
    rw [← mul_pow]; norm_num
  have h1 : L₀ ≤ d / 2 * (1 / 4 : ℝ) ^ T := by
    have hmul : (2 * L₀ * 4 ^ T) * (1 / 4 : ℝ) ^ T ≤ d * (1 / 4 : ℝ) ^ T :=
      mul_le_mul_of_nonneg_right hdL₀ (by positivity)
    have he : (2 * L₀ * (4 : ℝ) ^ T) * (1 / 4 : ℝ) ^ T = 2 * L₀ := by
      rw [mul_assoc, hcancel, mul_one]
    linarith only [hmul, he]
  exact le_trans h1 (mul_le_mul_of_nonneg_left h4 (by positivity))

/-- **The interface codegree ratio fits the round's.**  With `μ ≤ ecod·(1/2)·(1/4)^T` the absolute
codegree bound `μ·d` is below `ecod·loScale d ε k` for every `k ≤ T`. -/
theorem mu_mul_le_ecod_loScale {d ε μ ecod : ℝ} {T k : ℕ} (hd : 0 < d) (hε8 : ε ≤ 1 / 8)
    (hecod0 : 0 < ecod) (hμcod : μ ≤ ecod * (1 / 2) * (1 / 4) ^ T) (hk : k ≤ T) :
    μ * d ≤ ecod * loScale d ε k := by
  have hge := loScale_ge hd.le hε8 k
  have h4 : (1 / 4 : ℝ) ^ T ≤ (1 / 4 : ℝ) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have h1 : μ * d ≤ ecod * (d / 2 * (1 / 4 : ℝ) ^ k) := by
    have hA : μ * d ≤ ecod * (1 / 2) * (1 / 4 : ℝ) ^ T * d :=
      mul_le_mul_of_nonneg_right hμcod hd.le
    have hB : (ecod * d / 2) * (1 / 4 : ℝ) ^ T ≤ (ecod * d / 2) * (1 / 4 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    calc μ * d ≤ ecod * (1 / 2) * (1 / 4 : ℝ) ^ T * d := hA
      _ = (ecod * d / 2) * (1 / 4 : ℝ) ^ T := by ring
      _ ≤ (ecod * d / 2) * (1 / 4 : ℝ) ^ k := hB
      _ = ecod * (d / 2 * (1 / 4 : ℝ) ^ k) := by ring
  exact le_trans h1 (mul_le_mul_of_nonneg_left hge hecod0.le)

/-- **The covering demand of a round.**  As long as the exceptional set is at most half of the
uncovered set, the round's own guarantee (a `1/(256r)` fraction of the uncovered non-exceptional
vertices) delivers the schedule's demand (a `1/(512r)` fraction of the uncovered vertices). -/
theorem round_cover_demand {N Sc Ec β c rr : ℝ} (hrr : 0 < rr) (hc : c = 1 / (512 * rr))
    (hExc : Ec ≤ β / 2 * N) (hlt : β * N < N - Sc) :
    c * (N - Sc) ≤ (1 / (256 * rr)) * ((N - Sc) - Ec) := by
  have h1 : (N - Sc) / 2 ≤ (N - Sc) - Ec := by linarith
  have h2 : (1 / (256 * rr)) * ((N - Sc) / 2) ≤ (1 / (256 * rr)) * ((N - Sc) - Ec) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : c * (N - Sc) = (1 / (256 * rr)) * ((N - Sc) / 2) := by
    rw [hc]; field_simp; ring
  linarith only [h2, h3]

/-! ## The reduction -/

/-- **The ceiling one-round oracle from the single LeanPool.AsymptoticTrianglePacking.Internal round (sorry-free reduction).**
All of the parameter selection, the initialisation of `CeilRoundInv`, its persistence across a round
and the geometric decay of the uncovered count are discharged here; the only input is the
probabilistic round `NibbleRoundStep`.  (This is the body of `LeanPool.AsymptoticTrianglePacking.Internal.RoundOracleExistsCeil` at fixed
`r` and `β`; the packaged form is `LeanPool.AsymptoticTrianglePacking.Internal.roundOracleExistsCeil_holds`.) -/
theorem exists_roundOracle_params_of_nibbleRoundStep (hstep : NibbleRoundStep)
    (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
        IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
        (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
        HasRoundOracle H c β := by
  classical
  rcases le_or_gt 1 β with hβ1 | hβ1
  · -- `β ≥ 1`: the oracle demand is vacuous
    refine ⟨1, one_pos, 1, one_pos, 1, one_pos, 1, one_pos, le_rfl, ?_⟩
    intro V _ _ H d _ _ _ _ _ _
    refine ⟨fun _ _ => True, trivial, ?_⟩
    intro H' S _ hlt
    exfalso
    have hS : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- the substantive case `0 < β < 1`
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  -- the per-round covering fraction
  set c : ℝ := 1 / (512 * (r : ℝ)) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hc1 : c ≤ 1 := by
    rw [hcdef, div_le_one (by positivity)]; linarith
  have hcsmall : c ≤ 1 / 1024 := by
    rw [hcdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hlt1 : (1 : ℝ) - c < 1 := by linarith
  have hnn1 : (0 : ℝ) ≤ 1 - c := by linarith
  -- the round budget
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hβ hlt1
  -- the exceptional growth budget and the relative slack
  set δ : ℝ := β / (2 * ((T : ℝ) + 1)) with hδdef
  have hTpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  set ε : ℝ := 1 / (16 * ((T : ℝ) + 1)) with hεdef
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hε8 : ε ≤ 1 / 8 := by
    have h16 : ε ≤ 1 / 16 := by
      rw [hεdef]
      have h16' : (16 : ℝ) ≤ 16 * ((T : ℝ) + 1) := by
        have : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
        nlinarith
      exact one_div_le_one_div_of_le (by norm_num) h16'
    linarith
  -- the round step supplies the codegree ratio and the degree threshold
  obtain ⟨ecod, hecod0, L₀, hL₀0, hround⟩ := hstep r hr δ ε hδ0 hε0 hε8
  -- the interface parameters
  set μ : ℝ := min (1 / 2) (ecod * (1 / 2) * (1 / 4) ^ T) with hμdef
  have hμ0 : 0 < μ := by
    rw [hμdef]
    exact lt_min (by norm_num) (by positivity)
  have hμhalf : μ ≤ 1 / 2 := by rw [hμdef]; exact min_le_left _ _
  have hμcod : μ ≤ ecod * (1 / 2) * (1 / 4) ^ T := by rw [hμdef]; exact min_le_right _ _
  set d₀ : ℝ := max 1 (2 * L₀ * 4 ^ T) with hd₀def
  have hd₀0 : 0 < d₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨μ, hμ0, δ, hδ0, d₀, hd₀0, c, hc0, hc1, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil
  -- basic consequences of `d ≥ d₀`
  have hdL₀ : 2 * L₀ * 4 ^ T ≤ d := le_trans (le_max_right _ _) hd0
  have hNnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  -- the scales are in the right range for every `k ≤ T`
  have hloL₀ : ∀ k : ℕ, k ≤ T → L₀ ≤ loScale d ε k := fun k hk =>
    loScale_ge_threshold hd hε8 hdL₀ hk
  have hcodK : ∀ k : ℕ, k ≤ T → μ * d ≤ ecod * loScale d ε k := fun k hk =>
    mu_mul_le_ecod_loScale hd hε8 hecod0 hμcod hk
  -- the invariant
  refine ⟨fun H' S => CeilRoundInv r d μ ε δ c T H' S, ?_, ?_⟩
  · -- initialisation
    obtain ⟨Exc, hExc, hExcdeg⟩ := hreg
    refine ⟨0, Nat.zero_le _, by simp, H, Finset.Subset.refl _, huni, hcodeg, ?_, ?_,
      Exc, ?_, ?_⟩
    · intro e _; exact Finset.disjoint_empty_right e
    · intro v
      rw [hiScale_zero]
      refine le_trans (hceil v) ?_
      have hmd : μ * d ≤ 1 / 2 * d := mul_le_mul_of_nonneg_right hμhalf hd.le
      nlinarith
    · simpa using hExc
    · intro v _ hv
      rw [loScale_zero]
      refine le_trans ?_ (hExcdeg v hv).1
      have hmd : μ * d ≤ 1 / 2 * d := mul_le_mul_of_nonneg_right hμhalf hd.le
      nlinarith
  · -- the round
    intro H' S hInv hlt
    obtain ⟨k, hkT, huncov, K, hKH', hKuni, hKcod, hKS, hKhi, Exc, hExc, hKlo⟩ := hInv
    -- the uncovered count is positive, so `|V| > 0`
    have hSN : (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast Finset.card_le_univ S
    have hNpos : 0 < (Fintype.card V : ℝ) := by
      rcases lt_or_eq_of_le hNnn with h | h
      · exact h
      · exfalso
        have hz : β * (Fintype.card V : ℝ) = 0 := by rw [← h]; ring
        rw [hz, ← h] at hlt
        linarith
    -- the round index has not exhausted the budget
    have hkltT : k < T := by
      by_contra hkge
      push_neg at hkge
      have h1 : (1 - c) ^ k ≤ (1 - c) ^ T :=
        pow_le_pow_of_le_one hnn1 (by linarith) hkge
      have h2 : (1 - c) ^ k * (Fintype.card V : ℝ) ≤ β * (Fintype.card V : ℝ) :=
        mul_le_mul_of_nonneg_right (le_trans h1 hT.le) hNnn
      linarith
    -- the exceptional set is at most half of the uncovered set
    have hExcsmall : (Exc.card : ℝ) ≤ β / 2 * (Fintype.card V : ℝ) := by
      have hk1 : ((k : ℝ) + 1) ≤ (T : ℝ) + 1 := by
        have : (k : ℝ) ≤ (T : ℝ) := by exact_mod_cast hkT
        linarith
      have hδT : ((T : ℝ) + 1) * δ = β / 2 := by
        rw [hδdef]; field_simp
      have hkd : ((k : ℝ) + 1) * δ ≤ β / 2 := by
        rw [← hδT]
        exact mul_le_mul_of_nonneg_right hk1 hδ0.le
      calc (Exc.card : ℝ) ≤ ((k : ℝ) + 1) * δ * (Fintype.card V : ℝ) := hExc
        _ ≤ β / 2 * (Fintype.card V : ℝ) := mul_le_mul_of_nonneg_right hkd hNnn
    -- apply the round step at the current scale
    have hlo := hloL₀ k hkT
    have hratio : hiScale d ε k ≤ 8 * loScale d ε k := hiScale_le_eight_loScale hd.le T hkT
    have hKcod' : CodegreeBounded K (ecod * loScale d ε k) :=
      fun x y hxy => le_trans (hKcod x y hxy) (hcodK k hkT)
    obtain ⟨R', hR'K, hcov, K', hK'res, hK'hi, Exc', hExc', hK'lo⟩ :=
      hround K S Exc (loScale d ε k) (hiScale d ε k) hlo hratio
        (hiScale_nonneg hd.le hε0.le k) hKuni hKcod' hKS hKhi hKlo
    refine ⟨R', hR'K.trans hKH', ?_, ?_⟩
    · -- the invariant is re-established at level `k+1`
      refine ⟨k + 1, hkltT, ?_, K', hK'res.trans (residual_mono hKH'),
        isUniform_of_subset (hK'res.trans ((Hypergraph.residual_subset K R'))) hKuni,
        codegreeBounded_of_subset (hK'res.trans ((Hypergraph.residual_subset K R'))) hKcod,
        ?_, ?_, Exc', ?_, ?_⟩
      · -- geometric decay of the uncovered count
        have hdisjS : Disjoint (support (roundMatching R')) S :=
          disjoint_support_roundMatching hR'K hKS
        have hcard : ((S ∪ support (roundMatching R')).card : ℝ)
            = (S.card : ℝ) + ((support (roundMatching R')).card : ℝ) := by
          rw [Finset.card_union_of_disjoint hdisjS.symm]
          push_cast; ring
        have hcov' : c * ((Fintype.card V : ℝ) - (S.card : ℝ))
            ≤ ((support (roundMatching R')).card : ℝ) :=
          le_trans (round_cover_demand hrpos hcdef hExcsmall hlt) hcov
        rw [hcard]
        have hstepdec : (Fintype.card V : ℝ) - ((S.card : ℝ)
            + ((support (roundMatching R')).card : ℝ))
            ≤ (1 - c) * ((Fintype.card V : ℝ) - (S.card : ℝ)) := by linarith
        calc (Fintype.card V : ℝ) - ((S.card : ℝ) + ((support (roundMatching R')).card : ℝ))
            ≤ (1 - c) * ((Fintype.card V : ℝ) - (S.card : ℝ)) := hstepdec
          _ ≤ (1 - c) * ((1 - c) ^ k * (Fintype.card V : ℝ)) :=
              mul_le_mul_of_nonneg_left huncov hnn1
          _ = (1 - c) ^ (k + 1) * (Fintype.card V : ℝ) := by rw [pow_succ]; ring
      · -- edges of `K'` avoid the new covered set
        intro e he
        have he1 : e ∈ Hypergraph.residual K R' := hK'res he
        have he2 : e ∈ K := Hypergraph.residual_subset K R' he1
        have hd1 : Disjoint e S := hKS e he2
        have hd2 : Disjoint e (support (roundMatching R')) :=
          Hypergraph.residual_disjoint_covered he1
        exact Finset.disjoint_union_right.mpr ⟨hd1, hd2⟩
      · -- the new ceiling
        intro v
        rw [hiScale_succ]
        exact hK'hi v
      · -- the exceptional set grew by at most `δ|V|`
        refine le_trans hExc' ?_
        have hk : (((k + 1 : ℕ) : ℝ) + 1) * δ * (Fintype.card V : ℝ)
            = ((k : ℝ) + 1) * δ * (Fintype.card V : ℝ) + δ * (Fintype.card V : ℝ) := by
          push_cast; ring
        rw [hk]
        linarith
      · -- the new lower bound
        intro v hvS hvE
        rw [loScale_succ]
        exact hK'lo v hvS hvE
    · -- the covering demand
      exact le_trans (round_cover_demand hrpos hcdef hExcsmall hlt) hcov

end LeanPool.AsymptoticTrianglePacking.Internal
