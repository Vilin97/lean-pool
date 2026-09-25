/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Simplified.FirstPoints
public import Mathlib.Basic.Denumerable

/-!
# Checkpoint interface and its construction from an enumeration
-/

@[expose] public section

namespace GenLimit.FiniteWitness.Simplified

variable {α : Type*}

/-- The semantic properties of the first k elements in one fixed enumeration. -/
structure Checkpoints (α : Type*) where
  /-- The finite initial segments assigned to each target language. -/
  points : Set α → ℕ → Finset α
  subset : ∀ L k, (↑(points L k) : Set α) ⊆ L
  card : ∀ {L}, L.Infinite → ∀ k, (points L k).card = k
  exhaust : ∀ L x, x ∈ L → ∃ k, x ∈ points L (k + 1)
  agree : ∀ {L}, L.Infinite → ∀ {S : Finset α} {j k},
    (↑S : Set α) ⊆ L → points L k ⊆ S → j ≤ k →
    points (↑S : Set α) j = points L j

/-- Transport the first natural-number points along a fixed equivalence. -/
noncomputable def orderedCheckpoints (e : α ≃ ℕ) : Checkpoints α where
  points L k := (firstPoints (e '' L) k).map e.symm.toEmbedding
  subset L k := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨z, hz, he⟩ := firstPoints_subset (e '' L) k hy
    simpa [← he] using hz
  card hL k := by
    rw [Finset.card_map]
    exact firstPoints_card (hL.image e.injective.injOn) k
  exhaust L x hx := by
    obtain ⟨k, hk⟩ := firstPoints_exhausts (e '' L) (Set.mem_image_of_mem e hx)
    exact ⟨k, Finset.mem_map.mpr ⟨e x, hk, e.symm_apply_apply x⟩⟩
  agree := by
    intro L hL S j k hSL hseen hjk
    let R := S.map e.toEmbedding
    have hR : (↑R : Set ℕ) = e '' (↑S : Set α) := by
      ext y
      simp [R]
    have hRL : (↑R : Set ℕ) ⊆ e '' L := by
      rw [hR]
      exact Set.image_mono hSL
    have hseenR : firstPoints (e '' L) k ⊆ R := by
      intro y hy
      have hx := hseen (Finset.mem_map.mpr ⟨y, hy, rfl⟩)
      exact Finset.mem_map.mpr ⟨e.symm y, hx, e.apply_symm_apply y⟩
    have he := firstPoints_agree (hL.image e.injective.injOn) hRL hseenR hjk
    rw [hR] at he
    exact congrArg (fun P : Finset ℕ => P.map e.symm.toEmbedding) he

/-- Checkpoints in the usual ordering of the natural numbers. -/
noncomputable def naturalCheckpoints : Checkpoints ℕ := orderedCheckpoints (Equiv.refl ℕ)

@[simp] theorem naturalCheckpoints_points (L : Set ℕ) (k : ℕ) :
    naturalCheckpoints.points L k = firstPoints L k := by
  simp [naturalCheckpoints, orderedCheckpoints]

end GenLimit.FiniteWitness.Simplified
