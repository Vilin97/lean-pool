/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalReciprocityUnramifiedHomExt
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedResidueUniqueness
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Valuation.Extension
/-!
# Uniqueness of normalized families on unramified members

Two finite local reciprocity families with the norm kernels and arithmetic
Frobenius residue normalization agree on every unramified valued member. This
does not assert uniqueness on ramified members of the families.
-/

@[expose] public section

open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory

/-- The norm-kernel and arithmetic Frobenius conditions determine the value of
two local reciprocity families at an unramified member. -/
theorem finiteAbelianLocalReciprocity_unramified_family_ext
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f g : (E : FiniteAbelianLocalExtension K) →
      Kˣ →ₜ* (E.1 ≃ₐ[K] E.1))
    (hfker : ∀ E : FiniteAbelianLocalExtension K,
      (f E).toMonoidHom.ker = E.normSubgroup)
    (hgker : ∀ E : FiniteAbelianLocalExtension K,
      (g E).toMonoidHom.ker = E.normSubgroup)
    (hfrob : ∀ (E : FiniteAbelianLocalExtension K)
      [ValuativeRel E.1] [UniformSpace E.1] [IsUniformAddGroup E.1]
      [IsNonarchimedeanLocalField E.1]
      [Valuation.HasExtension (ValuativeRel.valuation K)
        (ValuativeRel.valuation E.1)],
      (𝓂[E.1] : Ideal 𝒪[E.1]).ramificationIdx 𝒪[K] = 1 →
      ∀ (π : 𝒪[K])
        (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
        (x : 𝒪[E.1]),
        ∃ z : 𝒪[E.1],
          (z : E.1) =
            (f E ((Units.mk0 (π : K) hπ.ne_zero)⁻¹)) (x : E.1) ∧
          IsLocalRing.residue 𝒪[E.1] z =
            (IsLocalRing.residue 𝒪[E.1] x) ^ Nat.card 𝓀[K])
    (hgrob : ∀ (E : FiniteAbelianLocalExtension K)
      [ValuativeRel E.1] [UniformSpace E.1] [IsUniformAddGroup E.1]
      [IsNonarchimedeanLocalField E.1]
      [Valuation.HasExtension (ValuativeRel.valuation K)
        (ValuativeRel.valuation E.1)],
      (𝓂[E.1] : Ideal 𝒪[E.1]).ramificationIdx 𝒪[K] = 1 →
      ∀ (π : 𝒪[K])
        (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
        (x : 𝒪[E.1]),
        ∃ z : 𝒪[E.1],
          (z : E.1) =
            (g E ((Units.mk0 (π : K) hπ.ne_zero)⁻¹)) (x : E.1) ∧
          IsLocalRing.residue 𝒪[E.1] z =
            (IsLocalRing.residue 𝒪[E.1] x) ^ Nat.card 𝓀[K])
    (E : FiniteAbelianLocalExtension K)
    [ValuativeRel E.1] [UniformSpace E.1] [IsUniformAddGroup E.1]
    [IsNonarchimedeanLocalField E.1]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation E.1)]
    (hUnram : (𝓂[E.1] : Ideal 𝒪[E.1]).ramificationIdx 𝒪[K] = 1)
    (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) :
    f E = g E := by
  let : LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      K E.1 := ⟨hUnram⟩
  have hfϖ :
      f E ((Units.mk0 (π : K) hπ.ne_zero)⁻¹) =
        LocalClassFieldTheory.abelianLocalArtinMap K E.1
          ((Units.mk0 (π : K) hπ.ne_zero)⁻¹) :=
    (finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow_iff
      K E.1 π hπ _).mp (hfrob E hUnram π hπ)
  have hgϖ :
      g E ((Units.mk0 (π : K) hπ.ne_zero)⁻¹) =
        LocalClassFieldTheory.abelianLocalArtinMap K E.1
          ((Units.mk0 (π : K) hπ.ne_zero)⁻¹) :=
    (finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow_iff
      K E.1 π hπ _).mp (hgrob E hUnram π hπ)
  have hfker' := hfker E
  have hgker' := hgker E
  change (f E).toMonoidHom.ker = fieldNormSubgroup K E.1 at hfker'
  change (g E).toMonoidHom.ker = fieldNormSubgroup K E.1 at hgker'
  exact finiteAbelianLocalReciprocity_unramified_hom_ext
    K E.1 hUnram π hπ (f E) (g E) hfker' hgker' (hfϖ.trans hgϖ.symm)

end ClassFieldTheory
