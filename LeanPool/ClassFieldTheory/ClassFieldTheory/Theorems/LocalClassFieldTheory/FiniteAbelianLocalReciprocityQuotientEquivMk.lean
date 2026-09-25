/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.MathlibInterface
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalReciprocityQuotientEquivOfArtin
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
/-!
# The local norm quotient is induced by the Artin map

The existence statements for the finite Artin map and the norm-quotient
isomorphism alone do not say that their witnesses agree. Here a single
canonical Artin map is chosen, and its quotient isomorphism is characterized
uniquely by its values on classes of nonzero field elements.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

/-- The continuous norm-quotient equivalence is uniquely determined by the
canonical finite local Artin map, with the expected value on every class. -/
theorem finiteAbelianLocalReciprocity_quotientEquiv_mk
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ artin : Kˣ →ₜ* (L ≃ₐ[K] L),
      Function.Surjective artin ∧
      artin.ker = fieldNormSubgroup K L ∧
      ∃! e : FieldNormQuotient K L ≃ₜ* (L ≃ₐ[K] L),
        ∀ x : Kˣ, e (QuotientGroup.mk' (fieldNormSubgroup K L) x) = artin x := by
  let artin := LocalClassFieldTheory.abelianLocalArtinMap K L
  have hker : artin.ker = fieldNormSubgroup K L := by
    change (LocalClassFieldTheory.abelianLocalArtinMap K L).toMonoidHom.ker =
      LocalFieldTheory.localNormSubgroup K L
    exact LocalClassFieldTheory.abelianLocalArtinMap_ker K L
  exact ⟨artin, LocalClassFieldTheory.abelianLocalArtinMap_surjective K L,
    hker,
    finiteAbelianLocalReciprocity_quotientEquiv_of_artin K L artin
      (LocalClassFieldTheory.abelianLocalArtinMap_surjective K L) hker⟩

end ClassFieldTheory
