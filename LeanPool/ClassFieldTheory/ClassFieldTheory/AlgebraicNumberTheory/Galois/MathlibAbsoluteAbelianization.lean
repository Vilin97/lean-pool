/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.TopologicalAbelianizationCongr
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
/-!
# Comparison with Mathlib's absolute Galois abelianization

Restriction from the algebraic closure to the separable closure identifies
Mathlib's absolute Galois group with the separable-closure model. The induced
map on topological abelianizations is a homeomorphism of groups, not merely
an abstract group isomorphism.
-/

@[expose] public section

noncomputable section

universe u

/-- Mathlib's absolute Galois abelianization and the separable-closure
topological abelianization are canonically isomorphic as topological groups. -/
noncomputable def absoluteGaloisGroupAbelianizationEquivSeparable
    (K : Type u) [Field K] :
    Field.absoluteGaloisGroupAbelianization K ≃ₜ*
      TopologicalAbelianization Gal(SeparableClosure K/K) :=
  LocalClassFieldTheory.topologicalAbelianizationCongr
    (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv K)

/-- The comparison sends an absolute Galois automorphism to its restriction
to the separable closure, also after passing to the abelianization. -/
@[simp]
theorem absoluteGaloisGroupAbelianizationEquivSeparable_mk
    (K : Type u) [Field K] (σ : Field.absoluteGaloisGroup K) :
    absoluteGaloisGroupAbelianizationEquivSeparable K
        (QuotientGroup.mk σ) =
      QuotientGroup.mk (AlgEquiv.separableClosure σ) :=
  LocalClassFieldTheory.topologicalAbelianizationCongr_mk
    (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv K) σ
