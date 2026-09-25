/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictedPowerSeries
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Nonarchimedean Scottish Book — Problem 29

**Proposer:** Alexander Zavyalov
**Date:** 6 June 2019

## Problem Statement

Let A → B be a flat continuous morphism of complete strongly noetherian Tate-Huber rings.
Does flatness of A⟨T⟩ → B⟨T⟩ follow?

## Notes

None.

## Status

RESOLVED: No (Gabber counterexample).

## Definitions needed

- **Strongly noetherian**: A Tate ring A such that A⟨T_1, ..., T_n⟩ is noetherian for
  all n.
- **Tate algebra A⟨T⟩**: The ring of restricted power series in one variable over A,
  i.e., `restrictedMvPowerSeriesSubring 1 A`.
-/

@[expose] public section

namespace ScottishBook

universe u

/-! ### Functorial map on restricted power series -/

/-- If `f : A →+* B` is continuous and `g` is a restricted power series over `A`,
then `MvPowerSeries.map f g` is a restricted power series over `B`. The key fact:
a continuous ring homomorphism maps `0` to `0`, so `f ∘ (coefficients tending to 0)`
still tends to `0`. -/
private theorem MvPowerSeries.IsRestricted_map {k : ℕ} {A B : Type u}
    [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
    {f : A →+* B} (hf : Continuous f) {g : MvPowerSeries (Fin k) A}
    (hg : MvPowerSeries.IsRestricted g) :
    MvPowerSeries.IsRestricted (MvPowerSeries.map f g) := by
  unfold MvPowerSeries.IsRestricted at *
  simp only [MvPowerSeries.coeff_map]
  exact (f.map_zero ▸ hf.tendsto 0).comp hg

/-- The canonical ring homomorphism `A⟨T⟩ → B⟨T⟩` induced by a continuous ring
homomorphism `f : A →+* B`. This is the functorial action of the restricted power
series construction on morphisms: it applies `f` coefficientwise.

Uses `restrictedMvPowerSeriesSubring 1 A` as the canonical one-variable restricted
power series ring. Continuity of `f` is required to ensure that the image of a
restricted power series (coefficients tending to `0`) is again restricted. -/
noncomputable def restrictedPowerSeriesMap {A B : Type u} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]
    (f : A →+* B) (hf : Continuous f) :
    restrictedMvPowerSeriesSubring 1 A →+* restrictedMvPowerSeriesSubring 1 B :=
  (MvPowerSeries.map f).restrict
    (restrictedMvPowerSeriesSubring 1 A) (restrictedMvPowerSeriesSubring 1 B)
    (fun _ hg => MvPowerSeries.IsRestricted_map hf hg)

/-! ### Problem 29: Counterexample -/

/-- **Scottish Book Problem 29** (Zavyalov, 6 June 2019; resolved: No, by Gabber):

*Let `A → B` be a flat continuous morphism of complete strongly noetherian Tate-Huber
rings. Does `A⟨T⟩ → B⟨T⟩` remain flat?*

Gabber constructed a counterexample showing that flatness of restricted power series
does **not** follow from flatness of the base morphism, even under the strong
hypotheses of completeness, strong noetherianity, and the Tate condition.

The existential asserts: there exist complete strongly noetherian Tate rings `A`, `B`
with a flat continuous ring homomorphism `f : A →+* B` such that the induced map
`restrictedPowerSeriesMap f : A⟨T⟩ →+* B⟨T⟩` is **not** flat.

The `sorry` represents Gabber's counterexample construction. -/
theorem problem29_counterexample :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : @NonarchimedeanRing A _ _) (_ : @NonarchimedeanRing B _ _)
      (_ : @IsStronglyNoetherian A _ _ _) (_ : @IsStronglyNoetherian B _ _ _)
      (f : A →+* B),
      Continuous f ∧
      f.Flat ∧
      ∀ (hf : Continuous f),
        ¬ (@restrictedPowerSeriesMap A B _ _ _ _ _ _ f hf).Flat := by
  sorry

end ScottishBook
