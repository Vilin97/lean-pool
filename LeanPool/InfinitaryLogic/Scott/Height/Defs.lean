/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Karp.PotentialIso
import LeanPool.InfinitaryLogic.Karp.CarrierTheorem
import LeanPool.InfinitaryLogic.Scott.Formula
import LeanPool.InfinitaryLogic.Scott.Rank
import LeanPool.InfinitaryLogic.Scott.RefinementCount
/-!
# Scott Height: Definition and Core Properties

The Scott height of a structure M is the least ordinal at which the Scott
formula analysis stabilizes for all tuples simultaneously.

## Main Definitions

- `scottHeight`: The least ordinal where the Scott formulas stabilize for all tuples.

## Main Results

- `scottHeight_lt_omega1`: Scott height is a countable ordinal.
- `scottHeight_stabilizesCompletely`: At Scott height, all tuple sizes have stabilized.
- `scottHeight_eq_of_equiv`: Scott height is invariant under L-isomorphism.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal

/-- The Scott height of a structure M: the least ordinal at which the Scott formula
analysis stabilizes for all tuples simultaneously.

This is defined as the least ordinal α such that for all n and all tuples a : Fin n → M,
if a structure N satisfies scottFormula a α, then it also satisfies scottFormula a (α + 1),
and vice versa.

Equivalently, this is the least α where BFEquiv α n a b implies BFEquiv (α + 1) n a b
for all tuples.

Scott height is related to but may differ from Scott rank. We always have
scottHeight ≤ scottRank. -/
noncomputable def scottHeight (M : Type w) [L.Structure M]
    [_countableM : Countable M] : Ordinal.{0} :=
  sInf {α : Ordinal.{0} | ∀ {n : ℕ} (a : Fin n → M)
    (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
    BFEquiv (L := L) α n a b → BFEquiv (L := L) (Order.succ α) n a b}

/-- Conditional variant of `scottHeight_lt_omega1`. -/
theorem scottHeight_lt_omega1_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    scottHeight (L := L) M < Ordinal.omega 1 := by
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization_of hcount M
  have h_mem : α ∈ {α : Ordinal.{0} | ∀ {n : ℕ} (a : Fin n → M)
      (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
      BFEquiv (L := L) α n a b → BFEquiv (L := L) (Order.succ α) n a b} := by
    intro n a N _ _ b hBF
    exact (hstab n N a b).mp hBF
  exact lt_of_le_of_lt (csInf_le ⟨0, fun _ _ => bot_le⟩ h_mem) hα_lt

/-- Conditional variant of `scottHeight_stabilizesCompletely`. -/
theorem scottHeight_stabilizesCompletely_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    StabilizesCompletely (L := L) M (scottHeight (L := L) M) := by
  obtain ⟨α, _, hstab⟩ := exists_complete_stabilization_of hcount M
  intro n N _ _ a b
  constructor
  · intro hBF
    suffices h : ∀ {k : ℕ} (a' : Fin k → M) (N' : Type w) [L.Structure N']
        [Countable N'] (b' : Fin k → N'),
        BFEquiv (L := L) (scottHeight (L := L) M) k a' b' →
        BFEquiv (L := L) (Order.succ (scottHeight (L := L) M)) k a' b' from h a N b hBF
    change scottHeight (L := L) M ∈ {α : Ordinal.{0} | ∀ {n : ℕ} (a : Fin n → M)
        (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
        BFEquiv (L := L) α n a b → BFEquiv (L := L) (Order.succ α) n a b}
    apply csInf_mem
    exact ⟨α, fun {k} a' N' _ _ b' hBF' => (hstab k N' a' b').mp hBF'⟩
  · exact BFEquiv.of_succ

/-- At any ordinal ≥ scottHeight, the structure stabilizes completely.
Conditional on `CountableRefinementHypothesis`. -/
theorem scottHeight_le_implies_stabilizesCompletely_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M]
    {α : Ordinal.{0}} (hα : scottHeight (L := L) M ≤ α) :
    StabilizesCompletely (L := L) M α := by
  have hstab := scottHeight_stabilizesCompletely_of hcount M
  intro n N _ _ a b
  constructor
  · intro hBF
    -- BFEquiv α → BFEquiv (scottHeight M) by monotonicity
    have hBF_sh := BFEquiv.monotone hα hBF
    -- Upgrade from scottHeight to succ α (succ α ≥ scottHeight M)
    exact BFEquiv_upgrade_at_stabilization hstab hBF_sh (Order.succ α)
      (le_trans hα (Order.le_succ α))
  · exact BFEquiv.of_succ

/-- Scott height is less than ω₁ for countable structures. -/
theorem scottHeight_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    scottHeight (L := L) M < Ordinal.omega 1 :=
  scottHeight_lt_omega1_of countableRefinementHypothesis M

/-- At Scott height, all tuple sizes have stabilized (BFEquiv α ↔ BFEquiv (succ α)). -/
theorem scottHeight_stabilizesCompletely (M : Type w) [L.Structure M] [Countable M] :
    StabilizesCompletely (L := L) M (scottHeight (L := L) M) :=
  scottHeight_stabilizesCompletely_of countableRefinementHypothesis M

/-- Scott height is invariant under L-isomorphism. -/
theorem scottHeight_eq_of_equiv
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    (e : M ≃[L] N) :
    scottHeight (L := L) M = scottHeight (L := L) N := by
  unfold scottHeight
  apply le_antisymm
  · -- scottHeight M ≤ scottHeight N: show S_N ⊆ S_M
    apply csInf_le_csInf
    · -- S_M is BddBelow
      exact ⟨0, fun _ _ => bot_le⟩
    · -- S_N is nonempty: exists_complete_stabilization N gives a member
      obtain ⟨α, _, hstab⟩ := exists_complete_stabilization (L := L) N
      exact ⟨α, fun {n} a P _ _ b hBF => (hstab n P a b).mp hBF⟩
    · -- S_N ⊆ S_M
      intro α hα_N
      simp only [Set.mem_ofPred_eq] at hα_N ⊢
      intro n a P _ _ b hBF
      -- Translate a to N via e: BFEquiv α (e ∘ a) b
      have h1 : BFEquiv (L := L) α n (e ∘ a) b :=
        (equiv_implies_BFEquiv e α n a).symm.trans hBF
      -- Use α ∈ S_N to upgrade: BFEquiv (succ α) (e ∘ a) b
      have h2 : BFEquiv (L := L) (Order.succ α) n (e ∘ a) b :=
        hα_N (e ∘ a) P b h1
      -- Translate back: BFEquiv (succ α) a b
      exact (equiv_implies_BFEquiv e (Order.succ α) n a).trans h2
  · -- scottHeight N ≤ scottHeight M: show S_M ⊆ S_N
    apply csInf_le_csInf
    · exact ⟨0, fun _ _ => bot_le⟩
    · obtain ⟨α, _, hstab⟩ := exists_complete_stabilization (L := L) M
      exact ⟨α, fun {n} a P _ _ b hBF => (hstab n P a b).mp hBF⟩
    · intro α hα_M
      simp only [Set.mem_ofPred_eq] at hα_M ⊢
      intro n a P _ _ b hBF
      have h1 : BFEquiv (L := L) α n (e.symm ∘ a) b :=
        (equiv_implies_BFEquiv e.symm α n a).symm.trans hBF
      have h2 : BFEquiv (L := L) (Order.succ α) n (e.symm ∘ a) b :=
        hα_M (e.symm ∘ a) P b h1
      exact (equiv_implies_BFEquiv e.symm (Order.succ α) n a).trans h2

end Language

end FirstOrder
