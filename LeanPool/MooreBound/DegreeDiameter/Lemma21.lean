/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.CommonBasis
public import LeanPool.MooreBound.DegreeDiameter.OddEvenRoute

/-!
# Alternating routes between complete flags

This file proves Lemma 2.1 in the same three visible stages as the paper:

1. invoke the separately proved common-basis theorem from `CommonBasis.lean`;
2. apply the separately proved `n`-round odd--even transposition route;
3. take prefix spans and verify that only ranks of the active parity change.

Indices are zero based in Lean: rank `i` is `space i`, while paper step
`s + 1` has Lean index `s`.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

public section

namespace MooreBound

open Module

namespace DegreeDiameter

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A purely combinatorial alternating layer. At layer `s + 1`, all prefix
sets of parity opposite to `s + 1` are unchanged. -/
def OrderingStep {n : ℕ} (s : Fin n)
    (σ τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin (n + 1), i.val % 2 ≠ (s.val + 1) % 2 → PrefixSet σ i = PrefixSet τ i

/-- Odd--even transposition routing, stated independently of linear algebra. -/
theorem oddEvenRoute {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∃ route : Fin (n + 1) → Equiv.Perm (Fin n),
      route 0 = 1 ∧
      route (Fin.last n) = π ∧
      ∀ s : Fin n, OrderingStep s (route s.castSucc) (route s.succ) := by
  obtain ⟨route, hzero, hlast, hstep⟩ := OddEvenSorting.oddEvenRoute2 π
  refine ⟨route, ?_, hlast, ?_⟩
  · change route 0 = Equiv.refl _
    exact hzero
  · simpa only [OrderingStep, PrefixSet, OddEvenSorting.OrderingStep2,
      OddEvenSorting.PrefixSet2] using hstep

theorem ofBasis_reindex_eq_at_of_prefixSet_eq {n : ℕ} (b : Basis (Fin n) K V)
    {σ τ : Equiv.Perm (Fin n)} {i : Fin (n + 1)} (h : PrefixSet σ i = PrefixSet τ i) :
    CompleteFlag.ofBasis (b.reindex σ.symm) i =
      CompleteFlag.ofBasis (b.reindex τ.symm) i := by
  rw [ofBasis_reindex_apply, ofBasis_reindex_apply, h]

/-- Step `s + 1` may change only ranks with the same parity as `s + 1`.
Equivalently, every rank of the other parity is frozen. -/
@[expose]
def AlternatingStep {n : ℕ} (s : Fin n)
    (F G : CompleteFlag K V n) : Prop :=
  ∀ i : Fin (n + 1), i.val % 2 ≠ (s.val + 1) % 2 → F i = G i

/-- Exact statement of Lemma 2.1: `route 0 = F`, `route n = F'`, and
the transition from `route s` to `route (s+1)` changes only ranks of the
parity prescribed by the one-based step number `s+1`. -/
theorem alternating_route {n : ℕ} (F F' : CompleteFlag K V n) :
    ∃ route : Fin (n + 1) → CompleteFlag K V n,
      route 0 = F ∧
      route (Fin.last n) = F' ∧
      ∀ s : Fin n, AlternatingStep K V s (route s.castSucc) (route s.succ) := by
  obtain ⟨b, π, hFspan, hF'span⟩ :=
    common_basis_orderings K V F F'
  have hF : F = CompleteFlag.ofBasis b := by
    apply CompleteFlag.ext
    intro i
    change F i = b.flag i
    simpa only [Module.Basis.flag] using hFspan i
  have hF' : F' = CompleteFlag.ofBasis (b.reindex π.symm) := by
    apply CompleteFlag.ext
    intro i
    rw [hF'span i]
    exact (ofBasis_reindex_apply K V b π i).symm
  obtain ⟨route, hroute0, hrouteLast, hrouteStep⟩ := oddEvenRoute π
  refine ⟨fun j ↦ CompleteFlag.ofBasis (b.reindex (route j).symm), ?_, ?_, ?_⟩
  · change CompleteFlag.ofBasis (b.reindex (route 0).symm) = F
    rw [hroute0]
    have hb : b.reindex (1 : Equiv.Perm (Fin n)).symm = b := by
      ext i
      simp
    rw [hb]
    exact hF.symm
  · change CompleteFlag.ofBasis (b.reindex (route (Fin.last n)).symm) = F'
    rw [hrouteLast]
    exact hF'.symm
  · intro s i hi
    exact ofBasis_reindex_eq_at_of_prefixSet_eq K V b (hrouteStep s i hi)

end DegreeDiameter

end MooreBound
