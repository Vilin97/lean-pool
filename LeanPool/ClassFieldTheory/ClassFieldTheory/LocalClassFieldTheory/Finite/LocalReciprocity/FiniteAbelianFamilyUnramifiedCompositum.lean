/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.FiniteUnramifiedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.CompositumRestriction
/-!
# An unramified factor large enough for finite Artin rigidity

For a finite abelian local extension `E`, adjoining the unramified extension
of degree divisible by `|Gal(E/K)|` produces a Galois group annihilated by
that degree. Restriction to the unramified factor sends the normalized Artin
value of a valuation-one unit to a generator. These are the two field-level
inputs to cyclic-quotient rigidity.
-/

noncomputable section

namespace LocalClassFieldTheory

open RamificationTheory LocalFieldTheory
open scoped ValuativeRel

/-- The Galois group of the compositum is annihilated by the unramified
degree when that degree is divisible by the size of the first Galois group. -/
theorem finiteAbelianUnramifiedCompositum_pow_eq_one
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (d : ℕ) (hd : 0 < d)
    (hcard : Nat.card (E ≃ₐ[K] E) ∣ d) :
    ∀ σ : Gal(↑(E ⊔ localFiniteUnramifiedField K d hd) / K),
      σ ^ d = 1 := by
  let U := localFiniteUnramifiedField K d hd
  let F := E ⊔ U
  let rE := intermediateFieldRestrictNormalHom E F le_sup_left
  let rU := intermediateFieldRestrictNormalHom U F le_sup_right
  have hUcard : Nat.card (U ≃ₐ[K] U) = d := by
    rw [IsGalois.card_aut_eq_finrank]
    exact localFiniteUnramifiedField_finrank K d hd
  have hinj : Function.Injective (rE.prod rU) :=
    intermediateFieldRestrictNormalHom_prod_injective_of_sup_eq
      K E U F le_sup_left le_sup_right rfl
  intro σ
  apply hinj
  change (rE.prod rU) (σ ^ d) = (rE.prod rU) 1
  apply Prod.ext
  · change rE (σ ^ d) = rE 1
    rw [map_pow, map_one]
    exact (orderOf_dvd_iff_pow_eq_one).mp
      ((orderOf_dvd_natCard (rE σ)).trans hcard)
  · change rU (σ ^ d) = rU 1
    rw [map_pow, map_one]
    exact (orderOf_dvd_iff_pow_eq_one).mp
      (hUcard ▸ orderOf_dvd_natCard (rU σ))

/-- Restriction of the canonical local Artin value of a valuation-one unit
generates the Galois group of the standard unramified extension. -/
theorem finiteAbelianArtin_unramifiedRestriction_zpowers_eq_top
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d)
    (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsAbelianGalois K F]
    (hUF : localFiniteUnramifiedField K d hd ≤ F)
    (u : Kˣ)
    (hu : LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul u) = 1) :
    Subgroup.zpowers
      (intermediateFieldRestrictNormalHom
        (localFiniteUnramifiedField K d hd) F hUF
        (abelianLocalArtinMap K F u)) = ⊤ := by
  let U := localFiniteUnramifiedField K d hd
  let rU := intermediateFieldRestrictNormalHom U F hUF
  have hrestrict : rU (abelianLocalArtinMap K F u) =
      arithmeticFrobeniusOfUnramifiedValuation K U := by
    have h := DFunLike.congr_fun
      (abelianLocalArtinMap_restrict K U F hUF) u
    change rU (abelianLocalArtinMap K F u) =
      abelianLocalArtinMap K U u at h
    exact h.trans (ClassFieldTheory.finiteAbelianLocalArtinMap_uniformizer K U u hu)
  have hUcard : Nat.card (U ≃ₐ[K] U) = d := by
    rw [IsGalois.card_aut_eq_finrank]
    exact localFiniteUnramifiedField_finrank K d hd
  apply (Subgroup.card_eq_iff_eq_top
    (Subgroup.zpowers (rU (abelianLocalArtinMap K F u)))).mp
  calc
    Nat.card (Subgroup.zpowers (rU (abelianLocalArtinMap K F u))) =
        orderOf (rU (abelianLocalArtinMap K F u)) := Nat.card_zpowers _
    _ = d := by
      rw [hrestrict]
      exact localFiniteUnramifiedField_arithmeticFrobenius_order K d hd
    _ = Nat.card (U ≃ₐ[K] U) := hUcard.symm

end LocalClassFieldTheory
