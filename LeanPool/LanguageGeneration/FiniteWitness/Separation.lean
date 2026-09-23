/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Characterization
public import Mathlib.Tactic.Push

/-!
# An infinitary positive-separation characterization

A single positive assignment must separate every subfamily with finite full
intersection. The subfamilies here are arbitrary sets of languages.
This file extends, and does not alter, the previously checked characterization.
-/

@[expose] public section

namespace GenLimit.FiniteWitness

variable {α : Type*}

/-- Every finite-core subfamily contains a witness point missing from a member. -/
def Separates (H : Generic.LanguageClass α)
    (T : Generic.Language α → Finset α) : Prop :=
  ∀ F : Set (Set α), F ⊆ H → F.Nonempty → (⋂₀ F).Finite →
    ∃ L ∈ F, ∃ K ∈ F, ∃ x ∈ T L, x ∉ K

/-- The full finite-witness criterion equals simultaneous positive separation. -/
theorem finiteWitnesses_iff_separating (H : Generic.LanguageClass α) :
    HasFiniteWitnesses H ↔
      ∃ T : Generic.Language α → Finset α,
        (∀ L, L ∈ H → (↑(T L) : Set α) ⊆ L) ∧ Separates H T := by
  classical
  constructor
  · rintro ⟨T, hpos, hcore⟩
    refine ⟨T, hpos, ?_⟩
    intro F hFH hF hC
    by_contra hsep
    push Not at hsep
    let S := hC.toFinset
    have hactive : ∀ L ∈ F, L ∈ active H T S := by
      intro L hL
      refine ⟨hFH hL, ?_, ?_⟩
      · intro x hx
        exact hC.mem_toFinset.mpr (fun K hK => hsep L hL K hK x hx)
      · intro x hx
        exact (hC.mem_toFinset.mp hx) L hL
    obtain ⟨L, hL⟩ := hF
    have hinf := hcore S ⟨L, hactive L hL⟩
    apply hinf
    apply hC.subset
    intro x hx K hK
    exact hx K (hactive K hK)
  · rintro ⟨T, hpos, hsep⟩
    refine ⟨T, hpos, ?_⟩
    intro S hactive
    change ¬ (activeCore H T S).Finite
    intro hfinite
    have heq : ⋂₀ active H T S = activeCore H T S := by
      ext x
      simp [activeCore]
    have hfin : (⋂₀ active H T S).Finite := by
      rw [heq]
      exact hfinite
    obtain ⟨L, hL, K, hK, x, hx, hnotK⟩ :=
      hsep (active H T S) (fun _ h => h.1) hactive hfin
    exact hnotK (hK.2.2 (hL.2.1 hx))

/-- Ordinary generation is equivalent to finitely supported positive separation. -/
theorem ordinary_iff_separating [Countable α] [Infinite α]
    (H : Generic.LanguageClass α) (hUUS : Generic.UUS H) :
    Generic.GeneratableInLimit H ↔
      ∃ T : Generic.Language α → Finset α,
        (∀ L, L ∈ H → (↑(T L) : Set α) ⊆ L) ∧ Separates H T :=
  (ordinary_iff_finiteWitnesses H hUUS).trans (finiteWitnesses_iff_separating H)

end GenLimit.FiniteWitness
