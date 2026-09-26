/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
/-!
# Compatibility names for the absolute abelianization

The field-generic construction is owned by
`AlgebraicNumberTheory.Galois.AbsoluteAbelianization`.  This module preserves
the established local names as definitional wrappers for downstream users.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

variable (K : Type) [Field K]

/-- Compatibility name for the absolute commutator closure. -/
abbrev localAbsoluteCommutatorClosure :
    ClosedSubgroup (intrinsicAbsoluteGalois K) :=
  absoluteCommutatorClosure K

/-- Compatibility instance for normality of the absolute commutator closure. -/
instance localAbsoluteCommutatorClosure_normal :
    (localAbsoluteCommutatorClosure K).Normal :=
  absoluteCommutatorClosure_normal K

/-- Compatibility name for the maximal abelian subextension. -/
abbrev localMaximalAbelianExtension :
    IntermediateField K (SeparableClosure K) :=
  maximalAbelianExtension K

/-- Compatibility instance for the Galois structure on the maximal abelian
subextension. -/
instance localMaximalAbelianExtension_isGalois :
    IsGalois K (localMaximalAbelianExtension K) :=
  maximalAbelianExtension_isGalois K

/-- Compatibility name for the underlying multiplicative equivalence. -/
noncomputable abbrev localAbsoluteAbelianizationMulEquiv :
    TopologicalAbelianization (intrinsicAbsoluteGalois K) ≃*
      Gal(localMaximalAbelianExtension K/K) :=
  absoluteAbelianizationMulEquivMaximalAbelianGalois K

/-- The compatibility equivalence sends a quotient class to restriction. -/
@[simp]
theorem localAbsoluteAbelianizationMulEquiv_mk
    (sigma : intrinsicAbsoluteGalois K) :
    localAbsoluteAbelianizationMulEquiv K (QuotientGroup.mk sigma) =
      AlgEquiv.restrictNormalHom (localMaximalAbelianExtension K) sigma :=
  absoluteAbelianizationMulEquivMaximalAbelianGalois_mk K sigma

/-- Compatibility form of continuity of the multiplicative equivalence. -/
theorem localAbsoluteAbelianizationMulEquiv_continuous :
    Continuous (localAbsoluteAbelianizationMulEquiv K) :=
  absoluteAbelianizationMulEquivMaximalAbelianGalois_continuous K

/-- Compatibility name for the canonical topological equivalence. -/
noncomputable abbrev localAbsoluteAbelianizationEquiv :
    TopologicalAbelianization (intrinsicAbsoluteGalois K) ≃ₜ*
      Gal(localMaximalAbelianExtension K/K) :=
  absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K

/-- Compatibility instance for total disconnectedness. -/
instance localAbsoluteTopologicalAbelianization_totallyDisconnectedSpace :
    TotallyDisconnectedSpace
      (TopologicalAbelianization (intrinsicAbsoluteGalois K)) :=
  absoluteTopologicalAbelianization_totallyDisconnectedSpace K

/-- Compatibility instance for the abelian Galois structure. -/
instance localMaximalAbelianExtension_isAbelianGalois :
    IsAbelianGalois K (localMaximalAbelianExtension K) :=
  maximalAbelianExtension_isAbelianGalois K

end LocalClassFieldTheory
