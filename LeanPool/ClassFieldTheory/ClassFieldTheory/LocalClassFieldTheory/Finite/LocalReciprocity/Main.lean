/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityCanonical
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalClassFieldAxiom
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalHenselianValuation

/-! # Main -/
namespace LocalClassFieldTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: the local reciprocity law

The residue Frobenius datum, the normalized henselian valuation, and the
class-field axiom constructed over the fixed separable closure are inserted
into the abstract reciprocity theorem.  The resulting isomorphism is independent of the
embedding used to realize the finite Galois extension in that closure.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Finite local reciprocity (Local Reciprocity Law).**  For every finite Galois
extension of nonarchimedean local fields, reciprocity gives the canonical
isomorphism
`G(L/K)ᵃᵇ ≃ Kˣ / N_{L/K}(Lˣ)`.

The coefficient module used in the construction is
`(SeparableClosure K)ˣ`, in the fixed-separable-closure model. -/
noncomputable def abelianizationEquivNormQuotient :
    Abelianization (Gal(L / K)) ≃* NormQuotient K L :=
  concreteReciprocityEquiv K L
    (localResidueDatum K)
    (localHenselianValuation K)
    (separableClosureUnits_isClassFormation K)

/-- The isomorphism in the finite local reciprocity construction is independent of the embedding
used to
realize `L/K` inside the fixed separable closure. -/
private theorem abelianizationEquivNormQuotient_eq_of_embedding
    (i : L →ₐ[K] SeparableClosure K) :
    abelianizationEquivNormQuotient K L =
      concreteReciprocityEquivOfEmbedding K L i
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K) := by
  simpa [abelianizationEquivNormQuotient, concreteReciprocityEquiv] using
    (concreteReciprocityEquivOfEmbedding_eq K L
      (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L) i
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K))

/-- The local norm-residue symbol is the inverse of reciprocity, preceded by
the quotient map from `Kˣ`. -/
noncomputable def localArtinMonoidHom :
    Kˣ →* Abelianization (Gal(L / K)) :=
  (abelianizationEquivNormQuotient K L).symm.toMonoidHom.comp
    (normClass K L)

/-- The canonical local norm-residue symbol can be computed using any
explicit realization of the finite Galois extension in the fixed separable
closure.  This is the symbol-level form of the embedding independence in
the finite local reciprocity construction. -/
theorem localArtinMonoidHom_eq_of_embedding
    (i : L →ₐ[K] SeparableClosure K) :
    localArtinMonoidHom K L =
      concreteNormResidueSymbolOfEmbedding K L i
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K) := by
  apply MonoidHom.ext
  intro x
  change (abelianizationEquivNormQuotient K L).symm
      (normClass K L x) =
    (concreteReciprocityEquivOfEmbedding K L i
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)).symm
        (normClass K L x)
  rw [abelianizationEquivNormQuotient_eq_of_embedding K L i]

/-- The local norm-residue symbol of the finite local reciprocity construction is surjective. -/
theorem localArtinMonoidHom_surjective :
    Function.Surjective (localArtinMonoidHom K L) :=
  (abelianizationEquivNormQuotient K L).symm.surjective.comp
    (QuotientGroup.mk'_surjective (localNormSubgroup K L))

/-- The kernel of the local norm-residue symbol is exactly the norm
subgroup `N_{L/K}(Lˣ)`. -/
theorem localArtinMonoidHom_ker :
    (localArtinMonoidHom K L).ker = localNormSubgroup K L := by
  ext x
  rw [MonoidHom.mem_ker]
  change
    (abelianizationEquivNormQuotient K L).symm
        (normClass K L x) = 1 ↔
      x ∈ localNormSubgroup K L
  constructor
  · intro hx
    have hx' := congrArg (abelianizationEquivNormQuotient K L) hx
    rw [(abelianizationEquivNormQuotient K L).apply_symm_apply, map_one] at hx'
    exact (normClass_eq_one_iff_mem K L x).mp hx'
  · intro hx
    have hq : normClass K L x = 1 :=
      (normClass_eq_one_iff_mem K L x).2 hx
    rw [hq, map_one]

end
end LocalClassFieldTheory
