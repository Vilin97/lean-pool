/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.FiniteUnramifiedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbelianFamilyRigidity
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbelianFamilySubgroupKernel
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbelianFamilyUnramifiedCompositum
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedResidueUniqueness
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalReciprocityUnramifiedFamilyExt
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Valuation.Extension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
/-!
# Uniqueness of the normalized coherent local Artin family

Norm kernels and tower compatibility alone leave an orientation ambiguity at
finite levels. Arithmetic Frobenius on unramified extensions removes it for
the entire coherent family, including ramified extensions.
-/

open _root_.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension renaming
  maximalIdeal_ramificationIdx_eq_one →
    maximalIdeal_ramificationIdx_eq_one


open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory

/-- A coherent family of finite local Artin maps is uniquely determined by
its norm kernels and its arithmetic-Frobenius normalization. The chosen
uniformizer is only used to express that normalization; the conclusion does
not depend on it. -/
theorem finiteAbelianLocalReciprocity_family_ext
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f g : (E : FiniteAbelianLocalExtension K) →
      Kˣ →ₜ* (E.1 ≃ₐ[K] E.1))
    (hfker : ∀ E : FiniteAbelianLocalExtension K,
      (f E).toMonoidHom.ker = E.normSubgroup)
    (hgker : ∀ E : FiniteAbelianLocalExtension K,
      (g E).toMonoidHom.ker = E.normSubgroup)
    (hfcoh : ∀ (E F : FiniteAbelianLocalExtension K)
      (hEF : E.1 ≤ F.1) (x : Kˣ) (y : E.1),
      IntermediateField.inclusion hEF ((f E x) y) =
        (f F x) (IntermediateField.inclusion hEF y))
    (hgcoh : ∀ (E F : FiniteAbelianLocalExtension K)
      (hEF : E.1 ≤ F.1) (x : Kˣ) (y : E.1),
      IntermediateField.inclusion hEF ((g E x) y) =
        (g F x) (IntermediateField.inclusion hEF y))
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
    : f = g := by
  obtain ⟨π, hπ⟩ := (LocalFieldTheory.localCompleteDVF K).exists_uniformizer
  have hrestrict
      (a : (E : FiniteAbelianLocalExtension K) →
        Kˣ →ₜ* (E.1 ≃ₐ[K] E.1))
      (hcoh : ∀ (E F : FiniteAbelianLocalExtension K)
        (hEF : E.1 ≤ F.1) (x : Kˣ) (y : E.1),
        IntermediateField.inclusion hEF ((a E x) y) =
          (a F x) (IntermediateField.inclusion hEF y))
      (E F : FiniteAbelianLocalExtension K)
      (hEF : E.1 ≤ F.1) (x : Kˣ) :
      RamificationTheory.intermediateFieldRestrictNormalHom E.1 F.1 hEF
          (a F x) = a E x := by
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    change
      E.1.val ((RamificationTheory.intermediateFieldRestrictNormalHom
        E.1 F.1 hEF (a F x)) y) = E.1.val ((a E x) y)
    calc
      E.1.val ((RamificationTheory.intermediateFieldRestrictNormalHom
          E.1 F.1 hEF (a F x)) y) =
          F.1.val ((a F x) (IntermediateField.inclusion hEF y)) :=
            RamificationTheory.intermediateFieldRestrictNormalHom_apply_val
              E.1 F.1 hEF (a F x) y
      _ = F.1.val (IntermediateField.inclusion hEF ((a E x) y)) := by
        rw [hcoh E F hEF x y]
      _ = E.1.val ((a E x) y) := rfl
  funext E
  let d : ℕ := Nat.card (E.1 ≃ₐ[K] E.1)
  have hd : 0 < d := Nat.card_pos
  let U := LocalClassFieldTheory.localFiniteUnramifiedField K d hd
  let Upack : FiniteAbelianLocalExtension K :=
    ⟨U, inferInstance, inferInstance⟩
  let Ffield := E.1 ⊔ U
  let Fpack : FiniteAbelianLocalExtension K :=
    ⟨Ffield, inferInstance, inferInstance⟩
  let rU := RamificationTheory.intermediateFieldRestrictNormalHom
    U Ffield le_sup_right
  let rE := RamificationTheory.intermediateFieldRestrictNormalHom
    E.1 Ffield le_sup_left
  let u : Kˣ := (Units.mk0 (π : K) hπ.ne_zero)⁻¹
  have huval : LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul u) = 1 := by
    have hπval :=
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_uniformizerFieldUnit
        K π hπ
    change LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (-(Additive.ofMul (Units.mk0 (π : K) hπ.ne_zero))) = 1
    rw [LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_neg]
    change -(LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul (LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerFieldUnit
        K π hπ))) = 1
    rw [hπval]
    norm_num
  have hUnram :
      (𝓂[U] : Ideal 𝒪[U]).ramificationIdx 𝒪[K] = 1 :=
    maximalIdeal_ramificationIdx_eq_one
  have hUeq : f Upack = g Upack :=
    finiteAbelianLocalReciprocity_unramified_family_ext K f g
      hfker hgker hfrob hgrob Upack hUnram π hπ
  have hfUcanonical : f Upack u =
      LocalClassFieldTheory.abelianLocalArtinMap K U u :=
    (finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow_iff
      K U π hπ _).mp (hfrob Upack hUnram π hπ)
  have hcanon :=
    LocalClassFieldTheory.finiteAbelianArtin_unramifiedRestriction_zpowers_eq_top
      K d hd Ffield le_sup_right u huval
  have hfc : rU (f Fpack u) =
      rU (LocalClassFieldTheory.abelianLocalArtinMap K Ffield u) := by
    calc
      rU (f Fpack u) = f Upack u :=
        hrestrict f hfcoh Upack Fpack le_sup_right u
      _ = LocalClassFieldTheory.abelianLocalArtinMap K U u := hfUcanonical
      _ = rU (LocalClassFieldTheory.abelianLocalArtinMap K Ffield u) := by
        symm
        exact DFunLike.congr_fun
          (LocalClassFieldTheory.abelianLocalArtinMap_restrict
            K U Ffield le_sup_right) u
  have hgen : Subgroup.zpowers (rU (f Fpack u)) = ⊤ := by
    rw [hfc]
    exact hcanon
  have hUcard : Nat.card (U ≃ₐ[K] U) = d := by
    rw [IsGalois.card_aut_eq_finrank]
    exact LocalClassFieldTheory.localFiniteUnramifiedField_finrank K d hd
  have horder : orderOf (rU (f Fpack u)) = d :=
    (orderOf_eq_card_of_zpowers_eq_top hgen).trans hUcard
  have hFmon : (f Fpack).toMonoidHom = (g Fpack).toMonoidHom := by
    apply LocalClassFieldTheory.monoidHom_ext_of_cyclic_quotient_and_subgroups
      (f Fpack).toMonoidHom (g Fpack).toMonoidHom rU u
    · exact hgen
    · intro σ
      change σ ^ orderOf (rU (f Fpack u)) = 1
      rw [horder]
      exact LocalClassFieldTheory.finiteAbelianUnramifiedCompositum_pow_eq_one
        K E.1 d hd (dvd_refl d) σ
    · intro S x hx
      exact LocalClassFieldTheory.finiteAbelianArtinFamilies_subgroup_preimage_le
        K f g hfker hgker hfcoh hgcoh Fpack S x hx
    · intro x
      calc
        rU (g Fpack x) = g Upack x :=
          hrestrict g hgcoh Upack Fpack le_sup_right x
        _ = f Upack x := DFunLike.congr_fun hUeq.symm x
        _ = rU (f Fpack x) :=
          (hrestrict f hfcoh Upack Fpack le_sup_right x).symm
  have hF : f Fpack = g Fpack := by
    apply ContinuousMonoidHom.ext
    intro x
    exact DFunLike.congr_fun hFmon x
  apply ContinuousMonoidHom.ext
  intro x
  calc
    f E x = rE (f Fpack x) :=
      (hrestrict f hfcoh E Fpack le_sup_left x).symm
    _ = rE (g Fpack x) := congrArg rE (DFunLike.congr_fun hF x)
    _ = g E x := hrestrict g hgcoh E Fpack le_sup_left x

end ClassFieldTheory
