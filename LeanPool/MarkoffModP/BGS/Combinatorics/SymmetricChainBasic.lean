/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Antichain
public import Mathlib.Tactic

/-!
# Finite symmetric-chain decompositions

The structure below packages an explicit partition into monotone chains.
Each chain is indexed by a finite key type, starts at a declared rank, and
has a declared length symmetric about `total / 2`.

The main abstract consequence is the Sperner injection: an antichain meets
each chain at most once, so mapping every point to the central point of its
chain injects the antichain into the central rank.
-/

@[expose] public section

namespace BGS.Combinatorics

/-- An explicit symmetric-chain decomposition of a ranked partial order. -/
structure SymmetricChainDecomposition
    (P : Type*) [PartialOrder P] (rank : P → ℕ) (total : ℕ) where
  Key : Type
  [keyFintype : Fintype Key]
  start : Key → ℕ
  length : Key → ℕ
  equiv : P ≃ Σ key : Key, Fin (length key + 1)
  rank_decode :
    ∀ point : Σ key : Key, Fin (length key + 1),
      rank (equiv.symm point) = start point.1 + point.2
  decode_mono :
    ∀ (key : Key) (i j : Fin (length key + 1)),
      i ≤ j →
        equiv.symm ⟨key, i⟩ ≤ equiv.symm ⟨key, j⟩
  symmetric : ∀ key : Key, 2 * start key + length key = total

namespace SymmetricChainDecomposition

variable {P : Type*} [PartialOrder P] {rank : P → ℕ} {total : ℕ}

/-- The first component of the chain code of a point. -/
def key (decomposition : SymmetricChainDecomposition P rank total)
    (x : P) : decomposition.Key :=
  (decomposition.equiv x).1

/-- The position component of the chain code of a point. -/
def position (decomposition : SymmetricChainDecomposition P rank total)
    (x : P) : Fin (decomposition.length (decomposition.key x) + 1) :=
  (decomposition.equiv x).2

theorem start_le_half
    (decomposition : SymmetricChainDecomposition P rank total)
    (key : decomposition.Key) :
    decomposition.start key ≤ total / 2 := by
  have hsymmetric := decomposition.symmetric key
  omega

theorem half_sub_start_le_length
    (decomposition : SymmetricChainDecomposition P rank total)
    (key : decomposition.Key) :
    total / 2 - decomposition.start key ≤ decomposition.length key := by
  have hsymmetric := decomposition.symmetric key
  omega

/-- The unique point of a symmetric chain in the central rank. -/
def center
    (decomposition : SymmetricChainDecomposition P rank total)
    (key : decomposition.Key) : P :=
  decomposition.equiv.symm
    ⟨key,
      ⟨total / 2 - decomposition.start key,
        Nat.lt_succ_iff.mpr
          (decomposition.half_sub_start_le_length key)⟩⟩

theorem rank_center
    (decomposition : SymmetricChainDecomposition P rank total)
    (key : decomposition.Key) :
    rank (decomposition.center key) = total / 2 := by
  rw [center, decomposition.rank_decode]
  exact Nat.add_sub_of_le (decomposition.start_le_half key)

private theorem key_injective_on_antichain
    [Fintype P]
    (decomposition : SymmetricChainDecomposition P rank total)
    (antichain : Finset P)
    (hantichain : IsAntichain (· ≤ ·) (antichain : Set P)) :
    Function.Injective
      (fun x : ↥antichain ↦ decomposition.key x.1) := by
  intro x y hkey
  apply Subtype.ext
  rcases hxcode : decomposition.equiv x.1 with ⟨kx, ix⟩
  rcases hycode : decomposition.equiv y.1 with ⟨ky, iy⟩
  have hkey' : kx = ky := by
    simpa [key, hxcode, hycode] using hkey
  subst ky
  rcases le_total ix iy with hxy | hyx
  · have hle : x.1 ≤ y.1 := by
      have hdecode :=
        decomposition.decode_mono kx ix iy hxy
      have hxback : decomposition.equiv.symm ⟨kx, ix⟩ = x.1 := by
        apply decomposition.equiv.injective
        simp [hxcode]
      have hyback : decomposition.equiv.symm ⟨kx, iy⟩ = y.1 := by
        apply decomposition.equiv.injective
        simp [hycode]
      simpa [hxback, hyback] using hdecode
    by_contra hne
    exact
      (hantichain (by simp using x.2)
        (by simp using y.2) hne) hle
  · have hle : y.1 ≤ x.1 := by
      have hdecode :=
        decomposition.decode_mono kx iy ix hyx
      have hxback : decomposition.equiv.symm ⟨kx, ix⟩ = x.1 := by
        apply decomposition.equiv.injective
        simp [hxcode]
      have hyback : decomposition.equiv.symm ⟨kx, iy⟩ = y.1 := by
        apply decomposition.equiv.injective
        simp [hycode]
      simpa [hxback, hyback] using hdecode
    by_contra hne
    exact
      (hantichain (by simp using y.2)
        (by simp using x.2) (Ne.symm hne)) hle

/-- Every antichain injects into the central rank of a finite ranked poset
equipped with an explicit symmetric-chain decomposition. -/
theorem antichain_card_le_central_rank
    [Fintype P]
    (decomposition : SymmetricChainDecomposition P rank total)
    (antichain : Finset P)
    (hantichain : IsAntichain (· ≤ ·) (antichain : Set P)) :
    antichain.card ≤
      Fintype.card {x : P // rank x = total / 2} := by
  classical
  let centerMap : ↥antichain → {x : P // rank x = total / 2} :=
    fun x ↦
      ⟨decomposition.center (decomposition.key x.1),
        decomposition.rank_center (decomposition.key x.1)⟩
  have hkeyInjective :=
    decomposition.key_injective_on_antichain antichain hantichain
  have hcenterInjective : Function.Injective centerMap := by
    intro x y hcenter
    apply hkeyInjective
    have hcode := congrArg decomposition.equiv (congrArg Subtype.val hcenter)
    simpa [centerMap, center] using congrArg Sigma.fst hcode
  simpa using Fintype.card_le_of_injective centerMap hcenterInjective

end SymmetricChainDecomposition

end BGS.Combinatorics
