/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
/-!
# Arithmetic normalization of finite local reciprocity

For an unramified finite abelian extension, one and the same Artin map is
surjective, has the field-norm kernel, and sends every inverse uniformizer
to the arithmetic Frobenius on residues. The statement uses only Mathlib
and public Definitions vocabulary; the implementation is used in the proof.
-/

@[expose] public section

open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory

/-- An unramified finite abelian extension admits a norm-kernel Artin map
whose value on the inverse of each uniformizer acts by the arithmetic
`q`-power Frobenius on the residue field. -/
theorem finiteAbelianLocalReciprocity_unramifiedNormalization
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    (hUnram : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1) :
    ∃ artin : Kˣ →ₜ* (L ≃ₐ[K] L),
      Function.Surjective artin ∧
        artin.toMonoidHom.ker = fieldNormSubgroup K L ∧
        ∀ (π : 𝒪[K])
          (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
          (x : 𝒪[L]),
          ∃ z : 𝒪[L],
            (z : L) =
                (artin ((Units.mk0 (π : K) hπ.ne_zero)⁻¹)) (x : L) ∧
              IsLocalRing.residue 𝒪[L] z =
                (IsLocalRing.residue 𝒪[L] x) ^ Nat.card 𝓀[K] := by
  have : LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      K L := ⟨hUnram⟩
  refine ⟨LocalClassFieldTheory.abelianLocalArtinMap K L, ?_, ?_, ?_⟩
  · exact LocalClassFieldTheory.abelianLocalArtinMap_surjective K L
  · change
      (LocalClassFieldTheory.abelianLocalArtinMap K L).toMonoidHom.ker =
        LocalFieldTheory.localNormSubgroup K L
    exact LocalClassFieldTheory.abelianLocalArtinMap_ker K L
  · intro π hπ x
    let u : Kˣ := Units.mk0 (π : K) hπ.ne_zero
    have hvalUnit :
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            (Additive.ofMul u) = -1 := by
      exact
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
    exact finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow
      K L (u⁻¹) hval x

end ClassFieldTheory
