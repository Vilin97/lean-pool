/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
/-!
# Uniqueness of arithmetic Frobenius from its residue action

For an unramified finite abelian extension, the arithmetic `q`-power action
on residues determines the Galois automorphism uniquely.  The canonical local
Artin map takes an inverse uniformizer to this automorphism.
-/

@[expose] public section

open scoped ValuativeRel

noncomputable
section

namespace ClassFieldTheory

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]

private noncomputable instance : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
  LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure K L

private noncomputable instance : Module.Finite 𝒪[K] 𝒪[L] :=
  LocalFieldTheory.localCompleteDVF_integerRing_moduleFinite K L

/-- The residue `q`-power action characterizes the canonical local Artin
image of an inverse uniformizer in an unramified finite abelian extension. -/
theorem finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow_iff
    (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (σ : L ≃ₐ[K] L) :
    (∀ x : 𝒪[L],
      ∃ z : 𝒪[L],
        (z : L) = σ (x : L) ∧
          IsLocalRing.residue 𝒪[L] z =
            (IsLocalRing.residue 𝒪[L] x) ^ Nat.card 𝓀[K]) ↔
      σ = LocalClassFieldTheory.abelianLocalArtinMap K L
        ((Units.mk0 (π : K) hπ.ne_zero)⁻¹) := by
  let u : Kˣ := (Units.mk0 (π : K) hπ.ne_zero)⁻¹
  have hvalUnit :
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul (Units.mk0 (π : K) hπ.ne_zero)) = -1 :=
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_uniformizerFieldUnit
      K π hπ
  have hval :
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul u) = 1 := by
    calc
      _ = -LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul (Units.mk0 (π : K) hπ.ne_zero)) := by
            change
              LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
                  (-(Additive.ofMul (Units.mk0 (π : K) hπ.ne_zero))) = _
            exact
              LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_neg
                K (Additive.ofMul (Units.mk0 (π : K) hπ.ne_zero))
      _ = 1 := by rw [hvalUnit]; norm_num
  have hArtin (x : 𝒪[L]) :=
    finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow K L u hval x
  constructor
  · intro hσ
    apply
      LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
      K L
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨zσ, hzσ, hresσ⟩ := hσ x
    obtain ⟨za, hza, hresa⟩ := hArtin x
    have hzσ' :
        LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure
          K L σ x = zσ := by
      apply Subtype.ext
      exact (LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure_apply
        K L σ x).trans hzσ.symm
    have hza' :
        LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure
          K L (LocalClassFieldTheory.abelianLocalArtinMap K L u) x = za := by
      apply Subtype.ext
      exact (LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure_apply
        K L (LocalClassFieldTheory.abelianLocalArtinMap K L u) x).trans hza.symm
    change IsLocalRing.residue 𝒪[L]
        (LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure
          K L σ x) =
      IsLocalRing.residue 𝒪[L]
        (LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure
          K L (LocalClassFieldTheory.abelianLocalArtinMap K L u) x)
    rw [hzσ', hza']
    exact hresσ.trans hresa.symm
  · intro hσ
    subst σ
    exact hArtin

end ClassFieldTheory
