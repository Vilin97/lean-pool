/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.AlgebraTower
/-!
# Separable field norms as products of embeddings

For a finite separable extension, the field norm becomes the product over all
base-field embeddings after mapping into a separably closed ambient field.
The ambient field need not be a normal extension of the base field.
-/

noncomputable section

open scoped BigOperators

namespace LocalClassFieldTheory

/-- The finite type of embeddings used to express a field norm as a product over embeddings. -/
noncomputable local instance finiteSeparableAlgHomFintypeForNormProduct
    {k E T : Type} [Field k] [Field E] [Field T]
    [Algebra k E] [Algebra k T]
    [FiniteDimensional k E] [Algebra.IsSeparable k E] :
    Fintype (E →ₐ[k] T) :=
  PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable k E)

/-- The embeddings of a finite separable tower above a power-basis generator
split into embeddings of the lower field and their extensions. -/
theorem prod_embeddings_algebraMap_powerBasisGen_eq
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    {L E : Type} [Field L] [Field E]
    [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
    [Algebra.IsSeparable k E] [FiniteDimensional k E]
    (pb : PowerBasis k L) :
    ∏ σ : E →ₐ[k] Ω, σ (algebraMap L E pb.gen) =
      ((@Finset.univ (L →ₐ[k] Ω) (PowerBasis.AlgHom.fintype pb)).prod
        (fun σ => σ pb.gen)) ^ Module.finrank L E := by
  have : FiniteDimensional L E := FiniteDimensional.right k L E
  have : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable k L E
  let : Fintype (L →ₐ[k] Ω) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.prod_equiv algHomEquivSigma
    (fun σ : E →ₐ[k] Ω => σ (algebraMap L E pb.gen))
    (fun σ => σ.1 pb.gen)]
  · rw [← Finset.univ_sigma_univ, Finset.prod_sigma, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun σ _ => ?_
    let : Algebra L Ω := σ.toRingHom.toAlgebra
    simp_rw [Finset.prod_const]
    congr
    rw [Finset.card_univ, Fintype.card_eq_nat_card]
    exact AlgHom.natCard_of_splits L E Ω (fun x =>
      IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable L x))
  · intro σ
    change σ (algebraMap L E pb.gen) =
      (σ.comp (IsScalarTower.toAlgHom k L E)) pb.gen
    exact (AlgHom.comp_apply σ (IsScalarTower.toAlgHom k L E) pb.gen).symm

/-- Mapping the norm of an element of a finite separable extension into a
separably closed field gives the product of all base-field embeddings. -/
theorem algebraMap_norm_eq_prod_embeddings_of_isSepClosed
    (k Ω E : Type) [Field k] [Field Ω] [Field E]
    [Algebra k Ω] [IsSepClosed Ω] [Algebra k E]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    (x : E) :
    algebraMap k Ω (Algebra.norm k x) = ∏ σ : E →ₐ[k] Ω, σ x := by
  have hx := Algebra.IsSeparable.isIntegral k x
  let : Algebra.IsSeparable k
      (IntermediateField.adjoin k ({x} : Set E)) :=
    Algebra.isSeparable_tower_bot_of_isSeparable k
      (IntermediateField.adjoin k ({x} : Set E)) E
  rw [Algebra.norm_eq_norm_adjoin k x, map_pow,
    ← IntermediateField.adjoin.powerBasis_gen hx,
    Algebra.norm_eq_prod_embeddings_gen Ω
      (IntermediateField.adjoin.powerBasis hx)
      (IsSepClosed.splits_codomain _
        (Algebra.IsSeparable.isSeparable k
          (IntermediateField.adjoin.powerBasis hx).gen))]
  · simpa only [IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.AdjoinSimple.algebraMap_gen] using
      (prod_embeddings_algebraMap_powerBasisGen_eq
        (L := IntermediateField.adjoin k ({x} : Set E)) (E := E)
        k Ω (IntermediateField.adjoin.powerBasis hx)).symm
  · exact Algebra.IsSeparable.isSeparable k _

end LocalClassFieldTheory
