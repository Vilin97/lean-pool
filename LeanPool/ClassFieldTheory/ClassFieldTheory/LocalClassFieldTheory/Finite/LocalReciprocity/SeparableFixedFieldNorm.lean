/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.PrimitiveElement
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm

/-! # Separable Fixed Field Norm -/
namespace LocalClassFieldTheory
open RamificationTheory KummerTheory

open LocalFieldTheory

open ClassFormation CyclicCohomology

/-!
# Finite local reciprocity: norms from arbitrary finite separable fixed fields

The henselian condition in the abstract class-formation framework quantifies over every finite
  abstract
field, not only over normal ones.  For an intermediate finite separable field
`E` in a separably closed Galois ambient field, the left cosets of
`Gal(Ω / E)` are canonically the `K`-embeddings `E → Ω`.  This file uses that
identification to compare the abstract class-formation coset norm with the ordinary field
norm, without a normality assumption on `E / K`.
-/

noncomputable section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

section CosetsAndEmbeddings

variable (E : IntermediateField K Ω)

/-- Restriction to `E` sends a left coset of `Gal(Ω/E)` to the corresponding
`K`-embedding of `E` into `Ω`. -/
def baseFixingCosetToAlgHom :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) →
      (E →ₐ[K] Ω) := fun q =>
  Quotient.liftOn' q
    (fun σ => σ.1.toAlgHom.comp E.val)
    (by
      intro σ τ hστ
      have hmem : σ⁻¹ * τ ∈
          extensionSubgroup
            (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
            (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) :=
        QuotientGroup.leftRel_apply.mp hστ
      let η : (closedFixingSubgroup K Ω E).toSubgroup :=
        ⟨(σ⁻¹ * τ).1, hmem⟩
      have hτ : τ = σ * Subgroup.inclusion
          (fixingSubgroupLeBase K Ω E) η := by
        apply Subtype.ext
        change τ.1 = σ.1 * η.1
        simp [η]
      apply AlgHom.ext
      intro x
      have hηfix :=
        (IntermediateField.mem_fixingSubgroup_iff E η.1).mp η.2
      have hηx : η.1 (x : Ω) = (x : Ω) := hηfix x x.2
      have hτ' := congrArg Subtype.val hτ
      change τ.1 = σ.1 * η.1 at hτ'
      change σ.1 (x : Ω) = τ.1 (x : Ω)
      calc
        σ.1 (x : Ω) = σ.1 (η.1 (x : Ω)) :=
          congrArg σ.1 hηx.symm
        _ = (σ.1 * η.1) (x : Ω) := rfl
        _ = τ.1 (x : Ω) := by rw [hτ'])

omit [IsSepClosed Ω] in
/-- States the theorem `baseFixingCosetToAlgHom_mk`. -/
@[simp]
theorem baseFixingCosetToAlgHom_mk
    (σ : (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup) :
    baseFixingCosetToAlgHom K Ω E (QuotientGroup.mk σ) =
      σ.1.toAlgHom.comp E.val :=
  rfl

private theorem baseFixingCosetToAlgHom_surjective
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    Function.Surjective (baseFixingCosetToAlgHom K Ω E) := by
  intro f
  let : Algebra.IsSeparable E Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K E Ω
  obtain ⟨φ, hφ⟩ :=
    (IsSepClosed.surjective_domRestrict_of_isSeparable
      (K := K) (L := E) (M := Ω) (E := Ω)) f
  let σ : Ω ≃ₐ[K] Ω :=
    AlgEquiv.ofBijective φ
      (Normal.toIsAlgebraic.algHom_bijective₂
        φ (AlgHom.id K Ω)).1
  have hσ : σ ∈ (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup := by
    change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top σ
  let σbase : (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup := ⟨σ, hσ⟩
  refine ⟨QuotientGroup.mk σbase, ?_⟩
  apply AlgHom.ext
  intro x
  have hx := congrArg (fun ψ : E →ₐ[K] Ω => ψ x) hφ
  change φ (x : Ω) = f x
  change φ (x : Ω) = f x at hx
  exact hx

omit [IsSepClosed Ω] in
private theorem baseFixingCosetToAlgHom_injective :
    Function.Injective (baseFixingCosetToAlgHom K Ω E) := by
  intro q r hqr
  rw [← Quotient.out_eq q, ← Quotient.out_eq r] at hqr ⊢
  apply Quotient.sound'
  apply QuotientGroup.leftRel_apply.mpr
  apply (mem_extensionSubgroup_iff
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
    ((Quotient.out q)⁻¹ * Quotient.out r)).2
  change (Quotient.out q).1⁻¹ * (Quotient.out r).1 ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let y : E := ⟨x, hx⟩
  have hy := congrArg (fun ψ : E →ₐ[K] Ω => ψ y) hqr
  change (Quotient.out q).1 (y : Ω) =
    (Quotient.out r).1 (y : Ω) at hy
  change (Quotient.out q).1⁻¹ ((Quotient.out r).1 x) = x
  rw [← hy]
  simp [y]

/-- Left cosets of the absolute subgroup fixing `E` are the actual
`K`-embeddings of `E` into the separably closed ambient field. -/
def baseFixingCosetEquivAlgHom
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) ≃
      (E →ₐ[K] Ω) :=
  Equiv.ofBijective (baseFixingCosetToAlgHom K Ω E)
    ⟨baseFixingCosetToAlgHom_injective K Ω E,
      baseFixingCosetToAlgHom_surjective K Ω E⟩

/-- Provides the instance `baseFixingExtensionQuotient_finite_of_isSeparable`. -/
noncomputable instance baseFixingExtensionQuotient_finite_of_isSeparable
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    Finite
      ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
        extensionSubgroup
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) :=
  (baseFixingCosetEquivAlgHom K Ω E).finite_iff.mpr inferInstance

end CosetsAndEmbeddings

section NormAsProduct

/-- A power basis enumerates the algebra embeddings of a finite separable field extension. -/
noncomputable local instance finiteSeparableAlgHomFintype
    {k F T : Type} [Field k] [Field F] [Field T]
    [Algebra k F] [Algebra k T]
    [FiniteDimensional k F] [Algebra.IsSeparable k F] :
    Fintype (F →ₐ[k] T) :=
  PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable k F)

variable (E : IntermediateField K Ω)
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

omit [IsSepClosed Ω] [FiniteDimensional K E] [Algebra.IsSeparable K E] in

/-- The abstract coset action on an `E`-unit is evaluation under the
corresponding actual `K`-embedding of `E`. -/
theorem relativeCosetAction_intermediateFieldUnit_val_of_isSeparable
    (x : Eˣ)
    (q : (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) :
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q) : Ωˣ) : Ω) =
      baseFixingCosetToAlgHom K Ω E q (x : E) := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rfl

/-- For every finite separable intermediate field, including a nonnormal
one, the abstract class-formation left-coset norm is the ordinary field norm. -/
theorem relativeNorm_intermediateFieldUnit_val_of_isSeparable (x : Eˣ) :
    ((Additive.toMul
      ((relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K (x : E)) := by
  let Q := (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup ⧸
    extensionSubgroup
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
  let := Fintype.ofFinite Q
  change
    ((Additive.toMul
      (relativeNormValue (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))) : Ωˣ) : Ω) = _
  rw [relativeNormValue]
  change
    (↑(Additive.toMul (∑ q : Q,
      relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q) : Ωˣ) : Ω) = _

  change (Units.coeHom Ω) (∏ q : Q,
    Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q)) = _
  rw [map_prod]
  change
    (∏ q : Q,
      ((Additive.toMul
        (relativeCosetAction (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
          (intermediateFieldUnitsEquivGaloisFixed K Ω E
            (Additive.ofMul x)) q) : Ωˣ) : Ω)) = _
  calc
    _ = ∏ σ : E →ₐ[K] Ω, σ (x : E) := by
      exact Fintype.prod_equiv
        (baseFixingCosetEquivAlgHom K Ω E)
        (fun q : Q =>
          ((Additive.toMul
            (relativeCosetAction (galoisAmbientUnitsRep K Ω)
              (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
              (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
              (intermediateFieldUnitsEquivGaloisFixed K Ω E
                (Additive.ofMul x)) q) : Ωˣ) : Ω))
        (fun σ : E →ₐ[K] Ω => σ (x : E))
        (relativeCosetAction_intermediateFieldUnit_val_of_isSeparable
          K Ω E x)
    _ = algebraMap K Ω (Algebra.norm K (x : E)) :=
      (algebraMap_norm_eq_prod_embeddings_of_isSepClosed
        K Ω E (x : E)).symm

/-- Equivariant form of the nonnormal finite-separable norm comparison. -/
theorem relativeNorm_intermediateFieldUnit_of_isSeparable (x : Eˣ) :
    relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) =
      baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K E x)) := by
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  exact relativeNorm_intermediateFieldUnit_val_of_isSeparable K Ω E x

end NormAsProduct

end
end LocalClassFieldTheory
