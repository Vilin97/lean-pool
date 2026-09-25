/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.UpperRamificationGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HasseArf.LowerRamificationGroupEventuallyBot
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HasseArf.RealLowerRamificationGroupNat
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HasseArf.UpperRamificationGroupAntitone
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HasseArf.UpperRamificationGroupCanonical
public import LeanPool.ClassFieldTheory.ClassFieldTheory.HasseArf
/-!
# Eventual triviality of upper ramification groups

The public real lower group agrees with the original natural-index lower
group at each integer. Eventual triviality then passes to upper numbering
through the Herbrand-index identity and antitonicity.
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

/-- The canonical upper ramification groups of a finite Abelian local
extension are trivial above some real upper index. -/
theorem upperRamificationGroup_eventually_bot
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → upperRamificationGroup K L t = ⊥ := by
  let A := (ValuativeRel.valuation L).valuationSubring
  let : IsNoetherianRing A := by
    change IsNoetherianRing ((ValuativeRel.valuation L).valuationSubring)
    rw [← HasseArf.chosenLocalExtension_valuationSubring_eq_canonical K L]
    exact ((LocalFieldTheory.chosenLocalExtensionCompleteDVF K
      L).toDVF).valuationSubring_isNoetherianRing
  obtain ⟨N, hN⟩ := lowerRamificationGroup_eventually_bot K A
  refine ⟨herbrandFunction K A (N : ℝ), ?_⟩
  intro t ht
  have hAt :
      upperRamificationGroup K L (herbrandFunction K A (N : ℝ)) = ⊥ := by
    rw [upperRamificationGroup_herbrandFunction K L (N : ℝ),
      realLowerRamificationGroup_nat K A N]
    exact hN N le_rfl
  apply le_antisymm _ bot_le
  exact (upperRamificationGroup_antitone K L ht).trans (le_of_eq hAt)

end ClassFieldTheory
