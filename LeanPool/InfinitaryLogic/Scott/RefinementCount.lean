/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.OrdinalUtil
import LeanPool.InfinitaryLogic.Scott.Sentence
/-!
# Proof of CountableRefinementHypothesis

This file proves `CountableRefinementHypothesis` and provides unconditional wrappers for
all Sentence.lean-level theorems. Together with the downstream wrappers in Rank.lean,
Height.lean, CountableCorollary.lean, and CountingModels.lean, this recovers the full
unconditional API.

## Strategy

The proof uses the "constant chain" argument:
1. Self-stabilization (`exists_complete_self_stabilization`) gives α₀ < ω₁ where the
   internal BFEquiv relation on M is frozen.
2. Under self-stabilization, forth/back witnesses chosen at level α₀ automatically work
   at all higher levels (`chain_step` + `witness_at_all_levels`).
3. By transfinite induction (`BFEquiv_of_all_finite_levels`), BFEquiv (α₀+k) for all k
   upgrades to BFEquiv ε for all ε.
4. Hence no refinement ordinals exist above γ = sup_k(α₀+k) < ω₁, and R(n,a) ⊆ [0,γ)
   is countable.

## Main Result

- `countableRefinementHypothesis` : `CountableRefinementHypothesis L`
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal BoundedFormulaω

/-! ### Self-stabilization to full stabilization

The key insight: `SelfStabilizesCompletely M α₀` (internal BFEquiv stabilization) implies
that the back-and-forth game cannot create new refinements above α₀ + ω, because any
forth/back witness at level α₀ already works at all higher levels (the "constant chain"
argument). This avoids the need to count external BFEquiv types directly. -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Internal BFEquiv upgrade: if BFEquiv α₀ holds internally (M vs M) at self-stabilization,
it upgrades to all higher ordinals. -/
private theorem BFEquiv_self_upgrade
    {M : Type w} [L.Structure M]
    {α₀ : Ordinal.{0}} (hstab : SelfStabilizesCompletely (L := L) M α₀)
    {n : ℕ} {a a' : Fin n → M}
    (h : BFEquiv (L := L) α₀ n a a') (β : Ordinal.{0}) (hβ : α₀ ≤ β) :
    BFEquiv (L := L) β n a a' := by
  induction β using Ordinal.limitRecOn generalizing n a a' with
  | zero => rwa [le_antisymm hβ bot_le] at h
  | add_one γ ih =>
    rw [← Order.succ_eq_add_one] at hβ ⊢
    rcases hβ.lt_or_eq with hlt | heq
    · rw [Order.lt_succ_iff] at hlt
      have h_succ := (hstab n a a').mp h
      rw [BFEquiv.succ]; refine ⟨@ih n a a' h hlt, fun m => ?_, fun m' => ?_⟩
      · let ⟨m', hm'⟩ := BFEquiv.forth h_succ m; exact ⟨m', @ih _ _ _ hm' hlt⟩
      · let ⟨m, hm⟩ := BFEquiv.back h_succ m'; exact ⟨m, @ih _ _ _ hm hlt⟩
    · exact heq ▸ h
  | limit β _ ih =>
    rw [BFEquiv.limit β ‹_›]; intro γ hγ
    exact (le_or_gt α₀ γ).elim (@ih γ hγ n a a' h) (fun hαγ => BFEquiv.monotone hαγ.le h)

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Chain-constant step: under self-stabilization at α₀, if BFEquiv ε holds at (n+1)-tuples
and BFEquiv (succ(succ ε)) holds at n-tuples, then BFEquiv (succ ε) holds at (n+1)-tuples.

The proof uses back at level succ ε to find an M-witness mw, then self-stabilization to
show the original and new M-witnesses are equivalent at all levels ≥ α₀. -/
private theorem chain_step
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N] [Countable N]
    {α₀ : Ordinal.{0}} (hstab : SelfStabilizesCompletely (L := L) M α₀)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} {m : M} {m' : N}
    {ε : Ordinal.{0}} (hε : α₀ ≤ ε)
    (hBF_ext : BFEquiv (L := L) ε (n + 1) (Fin.snoc a m) (Fin.snoc b m'))
    (hBF_base : BFEquiv (L := L) (Order.succ (Order.succ ε)) n a b) :
    BFEquiv (L := L) (Order.succ ε) (n + 1) (Fin.snoc a m) (Fin.snoc b m') := by
  obtain ⟨mw, hmw⟩ := BFEquiv.back hBF_base m'
  exact BFEquiv.trans
    (BFEquiv_self_upgrade hstab
      (BFEquiv.monotone hε (BFEquiv.trans hBF_ext (BFEquiv.symm (BFEquiv.of_succ hmw))))
      (Order.succ ε) (le_of_lt (Order.lt_succ_of_le hε)))
    hmw

private theorem add_nat_succ (α : Ordinal.{0}) (k : ℕ) :
    α + ↑(k + 1) = Order.succ (α + ↑k) := by
  simp only [Order.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_assoc]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- From a forth/back witness at level α₀, upgrade to BFEquiv (α₀+k) for all k.
Uses `chain_step` inductively: each level α₀+k upgrades to α₀+(k+1) because
self-stabilization forces the witness chain to be constant. -/
private theorem witness_at_all_levels
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N] [Countable N]
    {α₀ : Ordinal.{0}} (hstab : SelfStabilizesCompletely (L := L) M α₀)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} {m : M} {m' : N}
    (hbase : ∀ k : ℕ, BFEquiv (L := L) (α₀ + ↑k) n a b)
    (h0 : BFEquiv (L := L) α₀ (n + 1) (Fin.snoc a m) (Fin.snoc b m'))
    (k : ℕ) : BFEquiv (L := L) (α₀ + ↑k) (n + 1) (Fin.snoc a m) (Fin.snoc b m') := by
  induction k with
  | zero => simpa using h0
  | succ j ih =>
    rw [add_nat_succ]
    apply chain_step hstab le_self_add ih
    rw [Order.succ_eq_add_one, Order.succ_eq_add_one, add_assoc, add_assoc]
    convert hbase (j + 2) using 1; norm_cast

-- Main upgrade: from self-stabilization at α₀ and BFEquiv (α₀+k) for all k ∈ ℕ,
-- deduce BFEquiv ε for all ordinals ε. Uses transfinite induction on ε with
-- `witness_at_all_levels` to provide forth/back witnesses at successor steps.
omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
private theorem BFEquiv_of_all_finite_levels
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N] [Countable N]
    {α₀ : Ordinal.{0}} (hstab : SelfStabilizesCompletely (L := L) M α₀)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : ∀ k : ℕ, BFEquiv (L := L) (α₀ + ↑k) n a b)
    (ε : Ordinal.{0}) :
    BFEquiv (L := L) ε n a b := by
  induction ε using Ordinal.limitRecOn generalizing n a b with
  | zero => exact BFEquiv.monotone bot_le (by simpa using h 0)
  | add_one ε ih =>
    have hsucc_α₀ : BFEquiv (L := L) (Order.succ α₀) n a b := by
      have := h 1; rwa [Nat.cast_one, ← Order.succ_eq_add_one] at this
    rw [← Order.succ_eq_add_one, BFEquiv.succ]; refine ⟨@ih n a b h, fun m => ?_, fun m' => ?_⟩
    · let ⟨m'₀, hm'₀⟩ := BFEquiv.forth hsucc_α₀ m
      exact ⟨m'₀, @ih _ _ _ (witness_at_all_levels hstab h hm'₀)⟩
    · let ⟨m₀, hm₀⟩ := BFEquiv.back hsucc_α₀ m'
      exact ⟨m₀, @ih _ _ _ (witness_at_all_levels hstab h hm₀)⟩
  | limit ε hε ih => rw [BFEquiv.limit ε hε]; exact fun δ hδ => @ih δ hδ n a b h

/-! ### The Counting Lemma -/

/-- The countable refinement hypothesis holds for all countable relational languages.

For a countable structure M in a countable relational language, and any n-tuple a from M,
the set of refinement ordinals R(n, a) = {ε < ω₁ | ∃ (N, b), BFEquiv ε ∧ ¬BFEquiv (succ ε)}
is countable.

**Proof**: Self-stabilization (`exists_complete_self_stabilization`) gives α₀ < ω₁ where
internal BFEquiv on M is frozen. For any ε above γ = sup_k(α₀+k) with BFEquiv ε n a b,
the monotonicity of BFEquiv gives BFEquiv (α₀+k) for all k. The "constant chain" argument
(`witness_at_all_levels`) shows that forth/back witnesses at level α₀ work at all higher
levels (via self-stabilization + transitivity), so `BFEquiv_of_all_finite_levels` upgrades
BFEquiv to the successor. Hence no refinement ordinals exist above γ < ω₁. -/
theorem countableRefinementHypothesis : CountableRefinementHypothesis.{u, v, w} L := by
  intro M inst_struct inst_count n a
  obtain ⟨α₀, hα₀_lt, hstab⟩ := exists_complete_self_stabilization (L := L) M
  have hα_k_lt : ∀ k : ℕ, α₀ + ↑k < (Cardinal.aleph 1).ord := by
    intro k; rw [Cardinal.ord_aleph]
    induction k with
    | zero => simpa
    | succ j ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) ih
  have hBdd : BddAbove (Set.range fun k : ℕ => α₀ + (↑k : Ordinal.{0})) :=
    ⟨(Cardinal.aleph 1).ord, fun _ ⟨k, hk⟩ => hk ▸ le_of_lt (hα_k_lt k)⟩
  set γ := ⨆ k : ℕ, (α₀ + (↑k : Ordinal.{0}))
  have hγ_lt : γ < Ordinal.omega 1 := by
    exact Ordinal.iSup_lt_omega_one fun k => by rw [← Cardinal.ord_aleph]; exact hα_k_lt k
  apply Set.Countable.mono (s₂ := Set.Iio γ) _ (InfinitaryLogic.setCountable_Iio_of_lt_omega1 γ hγ_lt)
  intro ε ⟨_, N, instN, instCN, b, hBF, hNot⟩
  simp only [Set.mem_Iio]
  by_contra hge; push Not at hge
  exact hNot (BFEquiv_of_all_finite_levels hstab
    (fun k => BFEquiv.monotone (le_trans (le_ciSup hBdd k) hge) hBF)
    (Order.succ ε))

/-! ### Unconditional Wrappers (Sentence.lean level)

Each theorem below is a one-liner applying `countableRefinementHypothesis` to the
corresponding `_of` variant in Sentence.lean. -/

/-- The set of refinement ordinals for any tuple is countable. -/
theorem countable_refinement_steps
    {M : Type w} [L.Structure M] [Countable M]
    (n : ℕ) (a : Fin n → M) :
    Set.Countable {α : Ordinal.{0} | α < Ordinal.omega 1 ∧
      ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
        BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b} :=
  countableRefinementHypothesis M n a

/-- Per-tuple stabilization below ω₁. -/
theorem per_tuple_stabilization_below_omega1
    {M : Type w} [L.Structure M] [Countable M]
    (n : ℕ) (a : Fin n → M) :
    ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
      ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
        ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
          (BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (Order.succ α) n a b) :=
  per_tuple_stabilization_below_omega1_of countableRefinementHypothesis n a

/-- Complete stabilization below ω₁. -/
theorem exists_complete_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesCompletely (L := L) M α :=
  exists_complete_stabilization_of countableRefinementHypothesis M

/-- Existence of a stabilization ordinal (BFEquiv0 characterizes isomorphism). -/
theorem exists_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesAt (L := L) M α :=
  exists_stabilization_of countableRefinementHypothesis M

/-- The stabilization ordinal is below ω₁. -/
theorem stabilizationOrdinal_lt_omega1' (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M < Ordinal.omega 1 :=
  stabilizationOrdinal_lt_omega1_of countableRefinementHypothesis M

/-- The characterization property holds at stabilizationOrdinal. -/
theorem stabilizationOrdinal_stabilizes (M : Type w) [L.Structure M] [Countable M] :
    StabilizesAt (L := L) M (stabilizationOrdinal (L := L) M) :=
  stabilizationOrdinal_stabilizes_of countableRefinementHypothesis M

/-- BFEquiv0 at stabilizationOrdinal characterizes isomorphism. -/
theorem stabilizationOrdinal_spec (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    BFEquiv0 (L := L) M N (stabilizationOrdinal (L := L) M) ↔ Nonempty (M ≃[L] N) :=
  stabilizationOrdinal_stabilizes M N

/-- The Scott sentence of M characterizes M up to isomorphism among countable structures. -/
theorem scottSentence_characterizes (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    (scottSentence (L := L) M).realize_as_sentence N ↔ Nonempty (M ≃[L] N) :=
  scottSentence_characterizes_of countableRefinementHypothesis M N

/-- If N realizes the Scott sentence of M, then M ≃[L] N. -/
theorem scottSentence_realizes_implies_equiv (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N]
    (h : (scottSentence (L := L) M).realize_as_sentence N) : Nonempty (M ≃[L] N) :=
  (scottSentence_characterizes M N).mp h

/-- M itself satisfies its own Scott sentence. -/
theorem scottSentence_self (M : Type w) [L.Structure M] [Countable M] :
    (scottSentence (L := L) M).realize_as_sentence M :=
  (scottSentence_characterizes M M).mpr ⟨Equiv.refl L M⟩

/-- Isomorphic structures satisfy each other's Scott sentences. -/
theorem scottSentence_of_equiv (M N : Type w) [L.Structure M] [L.Structure N]
    [Countable M] [Countable N] (e : M ≃[L] N) :
    (scottSentence (L := L) M).realize_as_sentence N :=
  (scottSentence_characterizes M N).mpr ⟨e⟩

end Language

end FirstOrder
