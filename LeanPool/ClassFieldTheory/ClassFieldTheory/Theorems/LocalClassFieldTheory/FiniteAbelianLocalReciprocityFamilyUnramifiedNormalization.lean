/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
/-!
# Frobenius normalization of one coherent finite local reciprocity family

The same family has norm kernels and restriction compatibility, and at each
unramified valued realization sends an inverse uniformizer to arithmetic
Frobenius on the residue field. The local-field structures on an intermediate
field are explicit because the chosen separable closure does not currently
carry a canonical valued-field structure in the public definitions.
-/

@[expose] public section

open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory

/-- One coherent family of finite local Artin maps is normalized by arithmetic
Frobenius at every unramified valued realization of a member. The valuation
of the member must extend the valuation of `K`. -/
theorem finiteAbelianLocalReciprocity_family_unramifiedNormalization
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
          (x : 𝒪[E.1]),
          ∃ z : 𝒪[E.1],
            (z : E.1) =
                (artin E ((Units.mk0 (π : K) hπ.ne_zero)⁻¹)) (x : E.1) ∧
              IsLocalRing.residue 𝒪[E.1] z =
                (IsLocalRing.residue 𝒪[E.1] x) ^ Nat.card 𝓀[K] := by
  refine ⟨fun E => LocalClassFieldTheory.abelianLocalArtinMap K E.1, ?_, ?_, ?_⟩
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
  · intro E _ _ _ _ _ hUnram π hπ x
    have : LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        K E.1 := ⟨hUnram⟩
    let u : Kˣ := Units.mk0 (π : K) hπ.ne_zero
    have hvalUnit :
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            (Additive.ofMul u) = -1 :=
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_uniformizerFieldUnit
        K π hπ
    have hval :
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            (Additive.ofMul (u⁻¹)) = 1 := by
      calc
        _ = -LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            (Additive.ofMul u) := by
              change
                LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
                    (-(Additive.ofMul u)) = _
              exact
                LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_neg
                  K (Additive.ofMul u)
        _ = 1 := by rw [hvalUnit]; norm_num
    simpa only [u] using
      (finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow
        K E.1 (u⁻¹) hval x)

end ClassFieldTheory
