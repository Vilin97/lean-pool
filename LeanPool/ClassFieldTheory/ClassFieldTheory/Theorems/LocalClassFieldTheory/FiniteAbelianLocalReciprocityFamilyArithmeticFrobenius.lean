/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedResidueUniqueness
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Extension
/-!
# Arithmetic Frobenius in the coherent local reciprocity family

For an unramified member of one coherent finite local Artin family, the
inverse of every uniformizer maps to the unique Galois automorphism whose
reduction is the arithmetic `q`-power Frobenius.  The uniqueness clause is
essential: residue-field behavior is a normalization of the same family,
not a separate independently chosen reciprocity map.
-/

open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory

/-- A coherent finite local reciprocity family whose inverse-uniformizer
value is characterized uniquely by arithmetic Frobenius on residues. -/
theorem finiteAbelianLocalReciprocity_family_arithmeticFrobenius
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ artin : (E : FiniteAbelianLocalExtension K) →
        Kˣ →ₜ* (E.1 ≃ₐ[K] E.1),
      (∀ E : FiniteAbelianLocalExtension K,
        Function.Surjective (artin E) ∧
          (artin E).toMonoidHom.ker = E.normSubgroup) ∧
      (∀ (E F : FiniteAbelianLocalExtension K)
        (hEF : E.1 ≤ F.1) (x : Kˣ) (y : E.1),
        IntermediateField.inclusion hEF ((artin E x) y) =
          (artin F x) (IntermediateField.inclusion hEF y)) ∧
      ∀ (E : FiniteAbelianLocalExtension K)
        [ValuativeRel E.1] [UniformSpace E.1] [IsUniformAddGroup E.1]
        [IsNonarchimedeanLocalField E.1]
        [Valuation.HasExtension (ValuativeRel.valuation K)
          (ValuativeRel.valuation E.1)],
        (𝓂[E.1] : Ideal 𝒪[E.1]).ramificationIdx 𝒪[K] = 1 →
        ∀ (π : 𝒪[K])
          (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
          (σ : E.1 ≃ₐ[K] E.1),
          (∀ x : 𝒪[E.1],
            ∃ z : 𝒪[E.1],
              (z : E.1) = σ (x : E.1) ∧
                IsLocalRing.residue 𝒪[E.1] z =
                  (IsLocalRing.residue 𝒪[E.1] x) ^ Nat.card 𝓀[K]) ↔
            σ = artin E ((Units.mk0 (π : K) hπ.ne_zero)⁻¹) := by
  refine ⟨fun E => LocalClassFieldTheory.abelianLocalArtinMap K E.1,
    ?_, ?_, ?_⟩
  · intro E
    constructor
    · exact LocalClassFieldTheory.abelianLocalArtinMap_surjective K E.1
    · change
        (LocalClassFieldTheory.abelianLocalArtinMap K E.1).toMonoidHom.ker =
          LocalFieldTheory.localNormSubgroup K E.1
      exact LocalClassFieldTheory.abelianLocalArtinMap_ker K E.1
  · intro E F hEF x y
    have hrestrict := DFunLike.congr_fun
      (LocalClassFieldTheory.abelianLocalArtinMap_restrict K E.1 F.1 hEF) x
    change
      RamificationTheory.intermediateFieldRestrictNormalHom E.1 F.1 hEF
          (LocalClassFieldTheory.abelianLocalArtinMap K F.1 x) =
        LocalClassFieldTheory.abelianLocalArtinMap K E.1 x at hrestrict
    apply Subtype.ext
    change
      E.1.val ((LocalClassFieldTheory.abelianLocalArtinMap K E.1 x) y) =
        F.1.val ((LocalClassFieldTheory.abelianLocalArtinMap K F.1 x)
          (IntermediateField.inclusion hEF y))
    calc
      E.1.val ((LocalClassFieldTheory.abelianLocalArtinMap K E.1 x) y) =
          E.1.val
            ((RamificationTheory.intermediateFieldRestrictNormalHom
                E.1 F.1 hEF
                (LocalClassFieldTheory.abelianLocalArtinMap K F.1 x)) y) := by
            rw [hrestrict]
      _ = F.1.val ((LocalClassFieldTheory.abelianLocalArtinMap K F.1 x)
            (IntermediateField.inclusion hEF y)) :=
          RamificationTheory.intermediateFieldRestrictNormalHom_apply_val
            E.1 F.1 hEF
            (LocalClassFieldTheory.abelianLocalArtinMap K F.1 x) y
  · intro E _ _ _ _ _ hUnram π hπ σ
    exact
      letI : LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
          K E.1 := ⟨hUnram⟩
      finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow_iff
        K E.1 π hπ σ

end ClassFieldTheory
