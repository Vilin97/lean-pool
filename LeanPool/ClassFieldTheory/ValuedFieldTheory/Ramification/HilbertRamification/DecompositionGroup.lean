/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.AbsoluteValueConjugacy
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring
/-!
# Decomposition-group restriction law

This file gives the three tower-intersection formulas in their common ambient
Galois group.  The decomposition-group statement is formulated for arbitrary
absolute values, including the archimedean case.  The inertia and ramification
statements use valuation subrings and therefore cover the nonarchimedean case
in which those groups are defined.
-/

noncomputable section

universe u v w

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations
open RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type u) {L : Type w} [Field K] [Field L] [Algebra K L]

/-- The decomposition group of an absolute-value class.  Membership says that pullback by the
automorphism preserves the strict unit ball, equivalently the valuation
class, rather than requiring equality of chosen absolute-value representatives.
-/
def absoluteValueDecompositionGroup (w : AbsoluteValue L ℝ) :
    Subgroup (L ≃ₐ[K] L) where
  carrier := { σ | ∀ x : L, w (σ x) < 1 ↔ w x < 1 }
  one_mem' := by
    intro x
    rfl
  mul_mem' := by
    intro σ τ hσ hτ x
    exact (hσ (τ x)).trans (hτ x)
  inv_mem' := by
    intro σ hσ x
    have h := hσ (σ⁻¹ x)
    simpa using h.symm

@[simp] theorem mem_absoluteValueDecompositionGroup_iff
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    σ ∈ absoluteValueDecompositionGroup K w ↔
      ∀ x : L, w (σ x) < 1 ↔ w x < 1 :=
  Iff.rfl

/-- Membership really is preservation of the absolute-value class: the
pullback absolute value is equivalent to the chosen representative. -/
theorem mem_absoluteValueDecompositionGroup_iff_equivalent
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    σ ∈ absoluteValueDecompositionGroup K w ↔
      LubinTate.Valuations.EquivalentAbsoluteValues
        (w.comp (f := σ.toRingEquiv.toRingHom) σ.injective) w := by
  rw [LubinTate.Valuations.equivalentAbsoluteValues_iff_isEquiv,
    AbsoluteValue.isEquiv_iff_lt_one_iff]
  rfl

/-- The decomposition and inertia definition: on the normalized extension type,
the decomposition group is exactly the stabilizer of the chosen extension
under `w ↦ w ∘ σ`. -/
theorem mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
    {K₀ : Type u} {L₀ : Type w} [Field K₀] [Field L₀] [Algebra K₀ L₀]
    (vK : AbsoluteValue K₀ ℝ) (hvK : vK.IsNontrivial)
    (vL : AbsoluteValueExtension vK L₀) (σ : L₀ ≃ₐ[K₀] L₀) :
    σ ∈ absoluteValueDecompositionGroup K₀ vL.1 ↔
      absoluteValueExtensionConjugate vK vL σ = vL := by
  rw [mem_absoluteValueDecompositionGroup_iff_equivalent]
  change
    LubinTate.Valuations.EquivalentAbsoluteValues
        (absoluteValueExtensionConjugate vK vL σ).1 vL.1 ↔ _
  constructor
  · exact equivalent_exactExtensions_eq vK hvK
      (absoluteValueExtensionConjugate vK vL σ) vL
  · intro h
    rw [h]
    exact LubinTate.Valuations.equivalentAbsoluteValues_refl vL.1

section IntermediateField

variable {M : Type v} [Field M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L]

/-- The scalar-restriction map in the decomposition-group restriction law is the canonical inclusion
`G(L/M) → G(L/K)`. -/
theorem decompositionGroupRestriction_restrictAutomorphismScalars_injective :
    Function.Injective
      (RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
        (K := K) (M := M) (L := L)) := by
  intro σ τ h
  ext x
  exact DFunLike.congr_fun h x

/-- The decomposition-group restriction law, decomposition-group membership form: scalar restriction
does not change the action on the chosen valuation of `L`. -/
theorem decompositionGroupRestriction_mem_absoluteValueDecompositionGroup_restrictScalars_iff
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[M] L) :
    RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars (K := K)
      (M := M) σ ∈
        absoluteValueDecompositionGroup K w ↔
      σ ∈ absoluteValueDecompositionGroup M w :=
  Iff.rfl

/-- The decomposition-group restriction law, including the archimedean case:
inside `G(L/K)`, the decomposition group over `M` is
`G_w(L/K) ∩ G(L/M)`. -/
theorem decompositionGroupRestriction_absoluteValueDecompositionGroup_range_eq_inf
    (w : AbsoluteValue L ℝ) :
    Subgroup.map
        (RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars (K
          := K) (M := M))
        (absoluteValueDecompositionGroup M w) =
      absoluteValueDecompositionGroup K w ⊓
        (RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
          (K := K) (M := M)).range := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact
      ⟨(decompositionGroupRestriction_mem_absoluteValueDecompositionGroup_restrictScalars_iff
          (K := K) (M := M) w τ).mpr hτ,
        ⟨τ, rfl⟩⟩
  · rintro ⟨hσ, τ, rfl⟩
    exact
      ⟨τ,
        (decompositionGroupRestriction_mem_absoluteValueDecompositionGroup_restrictScalars_iff
          (K := K) (M := M) w τ).mp hσ,
        rfl⟩

end IntermediateField

namespace ValuationSubring

section NonarchimedeanIntermediateField

variable {M : Type v} [Field M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L]

/-- The decomposition-group restriction law, ambient-automorphism form:
inside `G(L/K)`, one has `I_w(L/M) = I_w(L/K) ∩ G(L/M)`. -/
theorem decompositionGroupRestriction_inertiaGroupInAut_range_eq_inf
    (A : _root_.ValuationSubring L) :
    Subgroup.map (restrictAutomorphismScalars (K := K) (M := M))
        (inertiaGroupInAut M A) =
      inertiaGroupInAut K A ⊓
        (restrictAutomorphismScalars (K := K) (M := M)).range := by
  ext σ
  constructor
  · rintro ⟨τ, ⟨δ, hδ, rfl⟩, rfl⟩
    refine ⟨?_, ⟨(δ : L ≃ₐ[M] L), rfl⟩⟩
    exact
      ⟨decompositionGroupRestrictScalars (K := K) (M := M) A δ,
        (mem_inertiaGroup_restrictScalars_iff
          (K := K) (M := M) A δ).mpr hδ,
        rfl⟩
  · rintro ⟨hσ, τ, rfl⟩
    rcases hσ with ⟨δ, hδ, hδτ⟩
    let δM : decompositionGroup M A :=
      ⟨τ,
        (mem_decompositionGroup_restrictScalars_iff
          (K := K) (M := M) A τ).mp (hδτ ▸ δ.property)⟩
    have hrestrict :
        decompositionGroupRestrictScalars (K := K) (M := M) A δM = δ := by
      apply Subtype.ext
      exact hδτ.symm
    have hδM : δM ∈ inertiaGroup M A :=
      (mem_inertiaGroup_restrictScalars_iff
        (K := K) (M := M) A δM).mp (hrestrict ▸ hδ)
    refine ⟨τ, ?_, rfl⟩
    exact ⟨δM, hδM, rfl⟩

/-- The decomposition-group restriction law, ambient-automorphism form:
inside `G(L/K)`, one has `R_w(L/M) = R_w(L/K) ∩ G(L/M)`. -/
theorem decompositionGroupRestriction_ramificationGroupInAut_range_eq_inf
    (A : _root_.ValuationSubring L) :
    Subgroup.map (restrictAutomorphismScalars (K := K) (M := M))
        (ramificationGroupInAut M A) =
      ramificationGroupInAut K A ⊓
        (restrictAutomorphismScalars (K := K) (M := M)).range := by
  ext σ
  constructor
  · rintro ⟨τ, ⟨ι, hι, rfl⟩, rfl⟩
    refine ⟨?_, ⟨inertiaGroupToAut (K := M) A ι, rfl⟩⟩
    exact
      ⟨inertiaGroupRestrictScalars (K := K) (M := M) A ι,
        (mem_ramificationGroup_restrictScalars_iff
          (K := K) (M := M) A ι).mpr hι,
        rfl⟩
  · rintro ⟨hσ, τ, rfl⟩
    rcases hσ with ⟨ι, hι, hιτ⟩
    let δM : decompositionGroup M A :=
      ⟨τ,
        (mem_decompositionGroup_restrictScalars_iff
          (K := K) (M := M) A τ).mp
            (hιτ ▸ (ι : decompositionGroup K A).property)⟩
    have hrestrictD :
        decompositionGroupRestrictScalars (K := K) (M := M) A δM =
          (ι : decompositionGroup K A) := by
      apply Subtype.ext
      exact hιτ.symm
    have hδM : δM ∈ inertiaGroup M A :=
      (mem_inertiaGroup_restrictScalars_iff
        (K := K) (M := M) A δM).mp (hrestrictD ▸ ι.property)
    let ιM : inertiaGroup M A := ⟨δM, hδM⟩
    have hrestrictI :
        inertiaGroupRestrictScalars (K := K) (M := M) A ιM = ι := by
      apply Subtype.ext
      exact hrestrictD
    have hιM : ιM ∈ ramificationGroup M A :=
      (mem_ramificationGroup_restrictScalars_iff
        (K := K) (M := M) A ιM).mp (hrestrictI ▸ hι)
    refine ⟨τ, ?_, rfl⟩
    exact ⟨ιM, hιM, rfl⟩

end NonarchimedeanIntermediateField

end ValuationSubring

end HilbertRamification
