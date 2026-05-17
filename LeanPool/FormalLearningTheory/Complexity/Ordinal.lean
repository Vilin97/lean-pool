/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.VCDimension
import LeanPool.FormalLearningTheory.Complexity.Littlestone
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Ordinal Extensions

Extends ℕ∞-valued complexity measures to ordinal-valued ones for universal
learning theory. WithTop ℕ has a single infinity (⊤); Ordinal has ω, ω², ε₀, ...
The embedding ℕ∞ ↪ Ordinal sends n ↦ n and ⊤ ↦ ω, but ordinal VC dimension
can take values beyond ω.
-/

universe u v

/-! ## BddAbove infrastructure for nat-to-ordinal iSup

Ordinal has `ConditionallyCompleteLinearOrderBot`, not `CompleteLattice`,
so every `ciSup`/`le_ciSup_of_le` call needs an explicit `BddAbove` witness.

Key invariant: `(n : ℕ) : Ordinal` is always `< ω`, so ω bounds every
nat-cast-to-ordinal range uniformly. -/

/-- Inner BddAbove: for a fixed S, the range over shattering witnesses is trivially bounded. -/
theorem ordinalVCDim_inner_bddAbove (X : Type u) (C : ConceptClass X Bool)
    (S : Finset X) :
    BddAbove (Set.range (fun (_ : Shatters X C S) => ((S.card : ℕ) : Ordinal))) :=
  ⟨S.card, fun _ ⟨_, h⟩ => h ▸ le_refl _⟩

/-- Outer BddAbove: the range of the full OrdinalVCDim iSup is bounded by ω.
    Holds for all concept classes regardless of whether VCDim is finite or infinite. -/
theorem ordinalVCDim_outer_bddAbove (X : Type u) (C : ConceptClass X Bool) :
    BddAbove (Set.range (fun S : Finset X =>
      ⨆ (_ : Shatters X C S), ((S.card : ℕ) : Ordinal))) := by
  refine ⟨Ordinal.omega0, fun x ⟨S, hS⟩ => ?_⟩
  subst hS
  apply ciSup_le'
  intro _
  exact le_of_lt (Ordinal.natCast_lt_omega0 S.card)

/-- VCL tree: combines VC dimension and Littlestone dimension into a
    single ordinal-valued measure. Used in universal learning trichotomy. -/
structure VCLTree (X : Type u) where
  /-- The ordinal value of the combined VC-Littlestone measure -/
  value : Ordinal.{0}
  /-- The concept class this measures -/
  conceptClass : ConceptClass X Bool

/-- Ordinal VC dimension: extends VCdim to ordinal values. -/
noncomputable def OrdinalVCDim (X : Type u) (C : ConceptClass X Bool) : Ordinal :=
  ⨆ (S : Finset X) (_ : Shatters X C S), ((S.card : ℕ) : Ordinal)

/-- Ordinal Littlestone dimension. -/
noncomputable def OrdinalLittlestoneDim (X : Type u) (C : ConceptClass X Bool) : Ordinal :=
  ⨆ (T : MistakeTree X) (_ : T.isShattered X C), ((T.depth : ℕ) : Ordinal)

/-- Embedding: finite VCDim embeds into OrdinalVCDim. -/
-- Helper: extract S.card ≤ n from VCDim = n
private theorem vcdim_card_le {X : Type u} {C : ConceptClass X Bool} {n : ℕ}
    (h : VCDim X C = n) {S : Finset X} (hS : Shatters X C S) : S.card ≤ n := by
  have : (S.card : WithTop ℕ) ≤ ↑n := by
    show (S.card : WithTop ℕ) ≤ (n : WithTop ℕ)
    calc (S.card : WithTop ℕ)
        ≤ ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ) :=
          le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) =>
            (S.card : WithTop ℕ)) S hS
      _ = ↑n := h
  exact WithTop.coe_le_coe.mp this

/-- Embedding: finite VCDim embeds into OrdinalVCDim. -/
theorem VCDim_embed_ordinal (X : Type u) (C : ConceptClass X Bool)
    (n : ℕ) (h : VCDim X C = n) : OrdinalVCDim X C = (n : Ordinal) := by
  unfold OrdinalVCDim
  apply le_antisymm
  · -- Upper bound: ⨆ ... ≤ n (all shattered S have card ≤ n)
    apply ciSup_le'
    intro S
    apply ciSup_le'
    intro hS
    exact Nat.cast_le.mpr (vcdim_card_le h hS)
  · -- Lower bound: n ≤ ⨆ ... (extract witness, apply le_ciSup_of_le with BddAbove)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact bot_le
    · -- n > 0: extract witness S₀ with S₀.card = n and Shatters X C S₀
      -- from VCDim X C = n via iSup_eq_top / finite extraction
      have hlt : VCDim X C < ⊤ := h ▸ WithTop.coe_lt_top n
      -- VCDim unfolds to ⨆ S, ⨆ _ : Shatters, (S.card : WithTop ℕ)
      -- Use the fact that in a CompleteLattice, if ⨆ f = n with n : ℕ,
      -- then some index achieves it
      have hVCDim_eq : ⨆ (S : Finset X) (_ : Shatters X C S),
          (S.card : WithTop ℕ) = ↑n := h
      -- Every shattered set has card ≤ n
      have hle : ∀ S, Shatters X C S → S.card ≤ n := fun S hS => vcdim_card_le h hS
      -- Since VCDim = n ≥ 1, there exists a shattered set with card = n
      -- (otherwise VCDim ≤ n-1, contradiction)
      have ⟨S₀, hS₀_shat, hS₀_card⟩ : ∃ S₀, Shatters X C S₀ ∧ S₀.card = n := by
        by_contra h_none
        push Not at h_none
        have : ∀ S, Shatters X C S → S.card ≤ n - 1 := by
          intro S hS
          have hle := hle S hS
          have hne := h_none S hS
          omega
        have hbound : VCDim X C ≤ ↑(n - 1) := by
          apply iSup₂_le
          intro S hS
          exact WithTop.coe_le_coe.mpr (this S hS)
        rw [h] at hbound
        have : n ≤ n - 1 := WithTop.coe_le_coe.mp hbound
        omega
      calc (↑n : Ordinal) = ↑S₀.card := by exact_mod_cast hS₀_card.symm
        _ ≤ ⨆ (_ : Shatters X C S₀), ((S₀.card : ℕ) : Ordinal) :=
            le_ciSup (ordinalVCDim_inner_bddAbove X C S₀) hS₀_shat
        _ ≤ ⨆ S, ⨆ (_ : Shatters X C S), ((S.card : ℕ) : Ordinal) :=
            le_ciSup_of_le (ordinalVCDim_outer_bddAbove X C) S₀ le_rfl

