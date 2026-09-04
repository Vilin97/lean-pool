/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Combinatorics.InfiniteRamsey
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Lattice

/-!
# Countable-family diagonal infinite Ramsey on `ℕ`

This file derives the countable-family ("eventually homogeneous for every coloring") form of
infinite Ramsey from the single-coloring lemma `infinite_ramsey_nat_arity`, by diagonalizing a
descending chain of order-embeddings — one homogenization step per coloring.

This is the pure combinatorial residual consumed by `MorleyHanfExtractionTail` (the cheap route
of the tail-weakened Morley–Hanf extraction; see `InfinitaryLogic/Conditional/MorleyHanfTransfer.lean`).
-/

universe u

/-- The descending chain of homogenizing embeddings: `familyEmb c (k+1)` homogenizes coloring
`c k` (post-composed with the previous step), so `Set.range (familyEmb c (k+1)) ⊆
Set.range (familyEmb c k)`. -/
private noncomputable def familyEmb (c : ℕ → Σ n, (Fin n ↪o ℕ) → Bool) : ℕ → (ℕ ↪o ℕ)
  | 0 => RelEmbedding.refl (· ≤ ·)
  | k + 1 =>
      (infinite_ramsey_nat_arity (c k).1
        (fun w => (c k).2 (w.trans (familyEmb c k)))).choose.trans (familyEmb c k)

/-- Definitional unfolding of `familyEmb` at a successor. -/
private theorem familyEmb_succ (c : ℕ → Σ n, (Fin n ↪o ℕ) → Bool) (k : ℕ) :
    familyEmb c (k + 1) =
      (infinite_ramsey_nat_arity (c k).1
        (fun w => (c k).2 (w.trans (familyEmb c k)))).choose.trans (familyEmb c k) := rfl

/-- Per-step homogeneity: at level `k`, coloring `c k` is constant on tuples drawn through
`familyEmb c (k+1)`. -/
private theorem familyEmb_homog (c : ℕ → Σ n, (Fin n ↪o ℕ) → Bool) (k : ℕ)
    (u v : Fin (c k).1 ↪o ℕ) :
    (c k).2 (u.trans (familyEmb c (k + 1))) = (c k).2 (v.trans (familyEmb c (k + 1))) := by
  set fk := (infinite_ramsey_nat_arity (c k).1
    (fun w => (c k).2 (w.trans (familyEmb c k)))).choose with hfk
  have hspec := (infinite_ramsey_nat_arity (c k).1
    (fun w => (c k).2 (w.trans (familyEmb c k)))).choose_spec
  rw [← hfk] at hspec
  have key : ∀ (w : Fin (c k).1 ↪o ℕ),
      w.trans (familyEmb c (k + 1)) = (w.trans fk).trans (familyEmb c k) := by
    intro w; rw [familyEmb_succ]; ext x; rfl
  rw [key u, key v]
  exact hspec _ _

/-- One step of the descending chain: the range shrinks. -/
private theorem familyEmb_range_succ_subset (c : ℕ → Σ n, (Fin n ↪o ℕ) → Bool) (k : ℕ) :
    Set.range (familyEmb c (k + 1)) ⊆ Set.range (familyEmb c k) := by
  rintro x ⟨j, rfl⟩; rw [familyEmb_succ]; exact ⟨_, rfl⟩

/-- The ranges form an antitone chain. -/
private theorem familyEmb_range_antitone (c : ℕ → Σ n, (Fin n ↪o ℕ) → Bool) :
    Antitone (fun k => Set.range (familyEmb c k)) :=
  antitone_nat_of_succ_le (familyEmb_range_succ_subset c)

/-- The diagonal of the chain: `diag c m` lands in `Set.range (familyEmb c m)` and is strictly
increasing in `m`. -/
private noncomputable def diag (c : ℕ → Σ n, (Fin n ↪o ℕ) → Bool) : ℕ → ℕ
  | 0 => familyEmb c 0 0
  | k + 1 => familyEmb c (k + 1) (diag c k + 1)

/-- The diagonal is strictly increasing. -/
private theorem diag_strictMono (c : ℕ → Σ n, (Fin n ↪o ℕ) → Bool) : StrictMono (diag c) := by
  apply strictMono_nat_of_lt_succ
  intro k
  show diag c k < familyEmb c (k + 1) (diag c k + 1)
  have h1 : diag c k + 1 ≤ familyEmb c (k + 1) (diag c k + 1) :=
    (familyEmb c (k + 1)).strictMono.le_apply
  omega

/-- Each diagonal value lives in the range of the corresponding chain embedding. -/
private theorem diag_mem_range (c : ℕ → Σ n, (Fin n ↪o ℕ) → Bool) (m : ℕ) :
    diag c m ∈ Set.range (familyEmb c m) := by
  cases m with
  | zero => exact ⟨0, rfl⟩
  | succ k => exact ⟨diag c k + 1, rfl⟩

/-- A tuple whose entries all lie in `Set.range p` factors as `w'.trans p` for some `w'`. -/
private theorem factor_through_range {m : ℕ} (p : ℕ ↪o ℕ) (w : Fin m ↪o ℕ)
    (hmem : ∀ k, w k ∈ Set.range p) : ∃ w' : Fin m ↪o ℕ, w = w'.trans p := by
  choose g hg using hmem
  have hg_sm : StrictMono g := by
    intro a b hab
    have : p (g a) < p (g b) := by rw [hg a, hg b]; exact w.strictMono hab
    exact p.lt_iff_lt.mp this
  refine ⟨OrderEmbedding.ofStrictMono g hg_sm, ?_⟩
  ext k
  rw [RelEmbedding.trans_apply]
  show w k = p ((OrderEmbedding.ofStrictMono g hg_sm) k)
  rw [OrderEmbedding.coe_ofStrictMono]
  exact (hg k).symm

/-- **Countable-family diagonal infinite Ramsey on `ℕ`.**

Given countably many finite-arity `Bool` colorings `c : ℕ → Σ n, (Fin n ↪o ℕ) → Bool`, there is
a single order embedding `g : ℕ ↪o ℕ` and, for each coloring `c i`, a cutoff `N` beyond which
`c i` is constant on all `n`-tuples `u.trans g` whose underlying indices are all `≥ N`.

Diagonalization of `infinite_ramsey_nat_arity`: build a descending chain of embeddings
`p 0 ⊇ p 1 ⊇ …` (in the sense `Set.range (p (k+1)) ⊆ Set.range (p k)`), where `p (k+1)`
homogenizes coloring `c k`; then read off a strictly increasing diagonal `g` with
`g j ∈ Set.range (p j)`. Every order-embedding `ℕ ↪o ℕ` has unbounded range, so the diagonal is
well-defined and strictly increasing, and a deep tuple `u` (indices `≥ i+1`) has `u.trans g`
landing in `Set.range (p (i+1))`, where `c i` is constant. -/
theorem infinite_ramsey_nat_family (c : ℕ → Σ n, (Fin n ↪o ℕ) → Bool) :
    ∃ g : ℕ ↪o ℕ, ∀ i : ℕ, ∃ N : ℕ,
      ∀ u v : Fin (c i).1 ↪o ℕ,
        (∀ k, N ≤ u k) → (∀ k, N ≤ v k) →
        (c i).2 (u.trans g) = (c i).2 (v.trans g) := by
  refine ⟨OrderEmbedding.ofStrictMono (diag c) (diag_strictMono c), ?_⟩
  set g := OrderEmbedding.ofStrictMono (diag c) (diag_strictMono c) with hg
  intro i
  refine ⟨i + 1, ?_⟩
  intro u v hu hv
  -- A deep tuple (entries `≥ i+1`) lands in `Set.range (familyEmb c (i+1))`.
  have hgval : ∀ (w : Fin (c i).1 ↪o ℕ), (∀ k, i + 1 ≤ w k) →
      ∀ k, (w.trans g) k ∈ Set.range (familyEmb c (i + 1)) := by
    intro w hw k
    rw [RelEmbedding.trans_apply]
    show g (w k) ∈ Set.range (familyEmb c (i + 1))
    rw [hg, OrderEmbedding.coe_ofStrictMono]
    exact familyEmb_range_antitone c (hw k) (diag_mem_range c (w k))
  obtain ⟨u', hu'⟩ := factor_through_range (familyEmb c (i + 1)) (u.trans g) (hgval u hu)
  obtain ⟨v', hv'⟩ := factor_through_range (familyEmb c (i + 1)) (v.trans g) (hgval v hv)
  rw [hu', hv']
  exact familyEmb_homog c i u' v'
