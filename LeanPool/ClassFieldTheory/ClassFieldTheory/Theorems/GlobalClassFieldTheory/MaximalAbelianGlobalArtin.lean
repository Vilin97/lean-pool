/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.IsMaximalAbelianGlobalArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.GlobalClassFieldTheory.TopologicalGlobalReciprocity
/-!
# The maximal abelian global Artin map

This map from Mathlib's idèle class group to Mathlib's abelianized absolute
Galois group is continuous, surjective, and has the identity component as
its kernel. It is induced by a topological reciprocity isomorphism. The
statement does not yet fix Frobenius normalization at finite levels, so it
does not assert uniqueness of the map.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace ClassFieldTheory

universe u

/-- A continuous surjective global Artin map with the expected kernel exists. -/
theorem maximalAbelianGlobalArtin
    (K : Type u) [Field K] [NumberField K] :
    ∃ artin : NumberField.IdeleClassGroup (𝓞 K) K →ₜ*
        Field.absoluteGaloisGroupAbelianization K,
      IsMaximalAbelianGlobalArtin K artin := by
  obtain ⟨e⟩ := topologicalGlobalReciprocity K
  let H : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K) :=
    Subgroup.connectedComponentOfOne _
  let q : NumberField.IdeleClassGroup (𝓞 K) K →ₜ*
      IdeleClassConnectedQuotient K :=
    { toMonoidHom := QuotientGroup.mk' H
      continuous_toFun := QuotientGroup.continuous_mk }
  let artin : NumberField.IdeleClassGroup (𝓞 K) K →ₜ*
      Field.absoluteGaloisGroupAbelianization K :=
    (ContinuousMonoidHom.toContinuousMonoidHom e).comp q
  refine ⟨artin, ?_, ?_⟩
  · intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H y
    exact ⟨x, rfl⟩
  · change artin.toMonoidHom.ker = H
    change (e.toMonoidHom.comp (QuotientGroup.mk' H)).ker = H
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' H) e.toMonoidHom
      e.injective]
    exact QuotientGroup.ker_mk' H

end ClassFieldTheory
