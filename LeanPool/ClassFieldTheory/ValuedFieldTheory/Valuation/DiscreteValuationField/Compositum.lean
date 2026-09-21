/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.TensorProduct.Finite
/-!
# Field-theoretic composita for finite valued extensions

The actual common-top part of Abhyankar's lemma needs valuation data on the
compositum `L ⊔ K'` inside a common ambient field.  This file records the
purely field-theoretic source facts before any valuation extension is added:
finite-dimensionality over either branch, degree bounds and equalities, the
intersection degree square, and separability of the common top.
-/

noncomputable section

universe u v

namespace DiscreteValuationField
namespace FieldCompositum

open scoped TensorProduct

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]

/-- A finitely generated intermediate field of the ambient field `Ω` which is
contained in `L` remains finitely generated after pulling it back to the field
type `L`. -/
theorem fg_comap_val_of_fg_of_le
    (L₀ L : IntermediateField K Ω) (hL₀_le : L₀ ≤ L) (hfg : L₀.FG) :
    (L₀.comap L.val).FG := by
  classical
  obtain ⟨T, hT⟩ := hfg
  let S : Set L := L.val ⁻¹' (T : Set Ω)
  have hS_finite : S.Finite := by
    exact Set.Finite.preimage
      (f := L.val) (s := (T : Set Ω))
      (fun x _hx y _hy hxy => Subtype.ext hxy)
      T.finite_toSet
  have hImage : L.val '' S = (T : Set Ω) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hxL₀ : x ∈ L₀ := by
        rw [← hT]
        exact IntermediateField.subset_adjoin K (T : Set Ω) hx
      exact ⟨⟨x, hL₀_le hxL₀⟩, hx, rfl⟩
  have hComap :
      (L₀.comap L.val).map L.val = L₀ :=
    IntermediateField.map_comap_eq_self
      (f := L.val) (S := L₀)
      (by simpa [IntermediateField.fieldRange_val] using hL₀_le)
  refine IntermediateField.fg_def.2 ⟨S, hS_finite, ?_⟩
  apply IntermediateField.map_injective L.val
  calc
    (IntermediateField.adjoin K S).map L.val
        = IntermediateField.adjoin K (L.val '' S) := by
          rw [IntermediateField.adjoin_map]
    _ = IntermediateField.adjoin K (T : Set Ω) := by
          rw [hImage]
    _ = L₀ := hT
    _ = (L₀.comap L.val).map L.val := hComap.symm

/-- The image of an intermediate field of `L` under the ambient inclusion
`L -> Ω` is contained in the original ambient intermediate field `L`. -/
theorem map_val_le_self
    (L : IntermediateField K Ω) (U : IntermediateField K L) :
    U.map L.val ≤ L := by
  intro x hx
  rcases hx with ⟨y, _hy, rfl⟩
  exact y.2

/-- If the right finite-support field lies in `K'`, then the finite common
top built from a left subfield of `L` maps into the ambient common top
`L ⊔ K'`. -/
theorem sup_map_val_sup_le_sup_of_right_le
    (L K' : IntermediateField K Ω) (U : IntermediateField K L)
    {K₀ : IntermediateField K Ω} (hK₀ : K₀ ≤ K') :
    (U.map L.val ⊔ K₀ : IntermediateField K Ω) ≤
      (L ⊔ K' : IntermediateField K Ω) := by
  refine sup_le ?_ ?_
  · exact
      (map_val_le_self (K := K) (Ω := Ω) L U).trans
        (show L ≤ (L ⊔ K' : IntermediateField K Ω) from le_sup_left)
  · exact
      hK₀.trans
        (show K' ≤ (L ⊔ K' : IntermediateField K Ω) from le_sup_right)

/-- Finite-dimensionality transfers from a left subextension `U ≤ L` to its
image in the ambient field `Ω`. -/
theorem finiteDimensional_map_val_of_finiteDimensional
    (L : IntermediateField K Ω) (U : IntermediateField K L)
    [FiniteDimensional K U] :
    FiniteDimensional K (U.map L.val) :=
  (IntermediateField.equivMap U L.val).toLinearEquiv.finiteDimensional

instance supRightAlgebra (L K' : IntermediateField K Ω) :
    Algebra K' (L ⊔ K' : IntermediateField K Ω) :=
  (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right)).toAlgebra

instance supLeftAlgebra (L K' : IntermediateField K Ω) :
    Algebra L (L ⊔ K' : IntermediateField K Ω) :=
  (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left)).toAlgebra

instance supRightIsScalarTower (L K' : IntermediateField K Ω) :
    IsScalarTower K K' (L ⊔ K' : IntermediateField K Ω) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  ext
  rfl

instance supLeftIsScalarTower (L K' : IntermediateField K Ω) :
    IsScalarTower K L (L ⊔ K' : IntermediateField K Ω) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  ext
  rfl

/-- Every tensor is a finite sum of pure tensors.  This local source form is
used to move from abstract field-level tensor representatives to denominator
clearing data in the compositum arguments. -/
theorem tensorProduct_exists_list_sum_tmul
    {R : Type u} {A B : Type v} [CommSemiring R]
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    (z : A ⊗[R] B) :
    ∃ l : List (A × B), z = (l.map (fun p => p.1 ⊗ₜ[R] p.2)).sum := by
  refine TensorProduct.inductionOn z ?tmul ?add
  · intro a b
    exact ⟨[(a, b)], by simp⟩
  · intro x y hx hy
    rcases hx with ⟨lx, hx⟩
    rcases hy with ⟨ly, hy⟩
    refine ⟨lx ++ ly, ?_⟩
    rw [List.map_append, List.sum_append, ← hx, ← hy]

/-- The field-level product map `L ⊗_K K' -> Ω` has image exactly the
compositum subalgebra `L ⊔ K'`.  This is the pure algebraic generation source
behind the later valuation-ring common-top comparison. -/
theorem sup_productMap_range
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    (Algebra.TensorProduct.productMap L.val K'.val).range =
      (L ⊔ K').toSubalgebra := by
  rw [Algebra.TensorProduct.productMap_range, L.range_val, K'.range_val,
    IntermediateField.sup_toSubalgebra_of_left]

/-- Every element of the compositum is represented by a tensor under the
field-level product map `L ⊗_K K' -> Ω`. -/
theorem exists_tensor_productMap_eq_of_mem_sup
    (L K' : IntermediateField K Ω) [FiniteDimensional K L]
    {x : Ω} (hx : x ∈ (L ⊔ K' : IntermediateField K Ω)) :
    ∃ z : L ⊗[K] K', Algebra.TensorProduct.productMap L.val K'.val z = x := by
  have hmem :
      x ∈ (Algebra.TensorProduct.productMap L.val K'.val).range := by
    rw [sup_productMap_range (K := K) (Ω := Ω) L K']
    exact hx
  rcases hmem with ⟨z, hz⟩
  exact ⟨z, hz⟩

/-- The product map into the actual compositum subtype agrees with the
ambient product map after coercing the target back to `Ω`. -/
theorem sup_productMap_val_comp
    (L K' : IntermediateField K Ω) :
    (L ⊔ K').val.comp
        (Algebra.TensorProduct.productMap
          (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left))
          (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right))) =
        Algebra.TensorProduct.productMap L.val K'.val := by
    apply Algebra.TensorProduct.ext
    · ext a
      rfl
    · ext b
      rfl

/-- Every element of the compositum subtype is represented by a tensor under
the intrinsic product map `L ⊗_K K' -> L ⊔ K'`. -/
theorem exists_sup_tensor_productMap_eq
    (L K' : IntermediateField K Ω) [FiniteDimensional K L]
    (x : (L ⊔ K' : IntermediateField K Ω)) :
    ∃ z : L ⊗[K] K',
      Algebra.TensorProduct.productMap
          (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left))
          (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right)) z =
        x := by
  rcases exists_tensor_productMap_eq_of_mem_sup
      (K := K) (Ω := Ω) L K' x.2 with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  rw [← hz]
  exact congrArg (fun f => f z)
    (sup_productMap_val_comp (K := K) (Ω := Ω) L K')

/-- The intrinsic field-level product map `L ⊗_K K' -> L ⊔ K'` is
surjective.  This is the exact field-generation source used before any
valuation-ring generation statement is attempted. -/
theorem sup_productMap_surjective
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    Function.Surjective
      (Algebra.TensorProduct.productMap
        (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left))
        (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right))) := by
  intro x
  exact exists_sup_tensor_productMap_eq (K := K) (Ω := Ω) L K' x

/-- Finite-sum form of the intrinsic field-level product-map generation
`L ⊗_K K' -> L ⊔ K'`. -/
theorem exists_list_sum_sup_tensor_productMap_eq
    (L K' : IntermediateField K Ω) [FiniteDimensional K L]
    (x : (L ⊔ K' : IntermediateField K Ω)) :
    ∃ l : List (L × K'),
      Algebra.TensorProduct.productMap
          (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left))
          (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right))
          ((l.map (fun p => p.1 ⊗ₜ[K] p.2)).sum) =
        x := by
  rcases exists_sup_tensor_productMap_eq (K := K) (Ω := Ω) L K' x with
    ⟨z, hz⟩
  rcases tensorProduct_exists_list_sum_tmul
      (R := K) (A := L) (B := K') z with ⟨l, hl⟩
  refine ⟨l, ?_⟩
  rw [← hl]
  exact hz

/-- The compositum is generated over the left factor by the right factor. -/
theorem sup_left_adjoin_right_range_eq_top
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    Algebra.adjoin L
        (Set.range
          (IntermediateField.inclusion
            (show K' ≤ L ⊔ K' from le_sup_right))) =
      (⊤ : Subalgebra L (L ⊔ K' : IntermediateField K Ω)) := by
  let iL :
      L →ₐ[K] (L ⊔ K' : IntermediateField K Ω) :=
    IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left)
  let iK' :
      K' →ₐ[K] (L ⊔ K' : IntermediateField K Ω) :=
    IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right)
  let S : Subalgebra L (L ⊔ K' : IntermediateField K Ω) :=
    Algebra.adjoin L (Set.range iK')
  change S = ⊤
  apply Algebra.eq_top_iff.2
  intro x
  rcases exists_sup_tensor_productMap_eq (K := K) (Ω := Ω) L K' x with
    ⟨z, hz⟩
  rw [← hz]
  refine TensorProduct.inductionOn z ?tmul ?add
  · intro a b
    have ha : iL a ∈ S := by
      change algebraMap L (L ⊔ K' : IntermediateField K Ω) a ∈ S
      exact S.algebraMap_mem a
    have hb : iK' b ∈ S :=
      Algebra.subset_adjoin (R := L) (s := Set.range iK') ⟨b, rfl⟩
    simpa [S, iL, iK', Algebra.TensorProduct.productMap_apply_tmul] using
      S.mul_mem ha hb
  · intro x y hx hy
    simpa [map_add] using S.add_mem hx hy

/-- The field-level product map `K' ⊗_K L -> Ω` has image exactly the
compositum subalgebra `L ⊔ K'`.  This is the order matching the later
valuation-ring tensor product `O_K' ⊗_{O_K} O_L`. -/
theorem sup_flip_productMap_range
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    (Algebra.TensorProduct.productMap K'.val L.val).range =
      (L ⊔ K').toSubalgebra := by
  rw [Algebra.TensorProduct.productMap_range, K'.range_val, L.range_val,
    ← IntermediateField.sup_toSubalgebra_of_right (E1 := K') (E2 := L),
    sup_comm]

/-- Every element of the compositum is represented by a tensor under the
field-level product map `K' ⊗_K L -> Ω`, in the order matching the valuation
ring tensor product. -/
theorem exists_flip_tensor_productMap_eq_of_mem_sup
    (L K' : IntermediateField K Ω) [FiniteDimensional K L]
    {x : Ω} (hx : x ∈ (L ⊔ K' : IntermediateField K Ω)) :
    ∃ z : K' ⊗[K] L, Algebra.TensorProduct.productMap K'.val L.val z = x := by
  have hmem :
      x ∈ (Algebra.TensorProduct.productMap K'.val L.val).range := by
    rw [sup_flip_productMap_range (K := K) (Ω := Ω) L K']
    exact hx
  rcases hmem with ⟨z, hz⟩
  exact ⟨z, hz⟩

/-- The product map `K' ⊗_K L -> L ⊔ K'` agrees with the ambient product map
after coercing the target back to `Ω`. -/
theorem sup_flip_productMap_val_comp
    (L K' : IntermediateField K Ω) :
    (L ⊔ K').val.comp
        (Algebra.TensorProduct.productMap
          (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right))
          (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left))) =
        Algebra.TensorProduct.productMap K'.val L.val := by
    apply Algebra.TensorProduct.ext
    · ext a
      rfl
    · ext b
      rfl

/-- Every element of the compositum subtype is represented by a tensor under
the intrinsic product map `K' ⊗_K L -> L ⊔ K'`. -/
theorem exists_sup_flip_tensor_productMap_eq
    (L K' : IntermediateField K Ω) [FiniteDimensional K L]
    (x : (L ⊔ K' : IntermediateField K Ω)) :
    ∃ z : K' ⊗[K] L,
      Algebra.TensorProduct.productMap
          (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right))
          (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left)) z =
        x := by
  rcases exists_flip_tensor_productMap_eq_of_mem_sup
      (K := K) (Ω := Ω) L K' x.2 with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  rw [← hz]
  exact congrArg (fun f => f z)
    (sup_flip_productMap_val_comp (K := K) (Ω := Ω) L K')

/-- The intrinsic field-level product map `K' ⊗_K L -> L ⊔ K'` is
surjective.  This is the source form aligned with the valuation-ring tensor
map used in the unramified base-change construction. -/
theorem sup_flip_productMap_surjective
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    Function.Surjective
      (Algebra.TensorProduct.productMap
        (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right))
        (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left))) := by
  intro x
  exact exists_sup_flip_tensor_productMap_eq (K := K) (Ω := Ω) L K' x

/-- The intrinsic product map `K' ⊗_K L -> L ⊔ K'`, regarded as a
`K'`-algebra hom.  This is the field-level base-change map used in the
the unramified base-change theorem; no separability of `K'/K` is involved. -/
noncomputable def supFlipProductMapRightAlgHom
    (L K' : IntermediateField K Ω) :
    K' ⊗[K] L →ₐ[K'] (L ⊔ K' : IntermediateField K Ω) :=
  AlgHom.mk'
    (Algebra.TensorProduct.productMap
      (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right))
      (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left))).toRingHom
    (by
      intro c x
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra])

/-- The `K'`-algebra product map `K' ⊗_K L -> L ⊔ K'` is surjective. -/
theorem supFlipProductMapRightAlgHom_surjective
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    Function.Surjective
      (supFlipProductMapRightAlgHom (K := K) (Ω := Ω) L K') := by
  simpa [supFlipProductMapRightAlgHom] using
    sup_flip_productMap_surjective (K := K) (Ω := Ω) L K'

/-- The actual compositum `L ⊔ K'` is finite over the right factor whenever
the left factor is finite over the base.

This is the finite-dimensional source needed for unramified base change:
base change by an arbitrary algebraic extension is reduced elementwise to a
finite right subextension, but the finiteness of the right branch itself comes
from the finite left factor. -/
theorem finiteDimensional_sup_over_right_of_left
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    FiniteDimensional K' (L ⊔ K' : IntermediateField K Ω) := by
  exact
    FiniteDimensional.of_surjective
      (supFlipProductMapRightAlgHom (K := K) (Ω := Ω) L K').toLinearMap
      (supFlipProductMapRightAlgHom_surjective (K := K) (Ω := Ω) L K')

/-- The algebraic first-isomorphism theorem with the source ring structure
fixed by its commutative-ring parent. -/
local instance tensorProductIdealHasQuotient
    (L K' : IntermediateField K Ω) :
    HasQuotient (K' ⊗[K] L) (Ideal (K' ⊗[K] L)) :=
  @Ideal.instHasQuotient (K' ⊗[K] L)
    (inferInstance : CommRing (K' ⊗[K] L)).toRing

private noncomputable def quotientKerAlgEquivOfSurjectiveCommRing
    {R A B : Type*}
    [ringR : CommSemiring R] [ringA : CommRing A]
    [algebraRA : Algebra R A]
    [ringB : Semiring B] [algebraRB : Algebra R B]
    {f : A →ₐ[R] B} (hf : Function.Surjective f) :
    (@HasQuotient.Quotient A (Ideal A)
      (@Ideal.instHasQuotient A ringA.toRing)
      (RingHom.ker f.toRingHom)) ≃ₐ[R] B :=
  Ideal.quotientKerAlgEquivOfSurjective hf

/-- The field factor selected by the product map `K' ⊗_K L -> L ⊔ K'` is
the actual compositum field: quotienting by the kernel of the surjective
`K'`-algebra map gives `L ⊔ K'`. -/
noncomputable def supFlipProductMapRightAlgHomQuotientKerAlgEquiv
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    ((K' ⊗[K] L) ⧸
        (RingHom.ker
          (supFlipProductMapRightAlgHom (K := K) (Ω := Ω) L K').toRingHom))
      ≃ₐ[K'] (L ⊔ K' : IntermediateField K Ω) :=
  let f : K' ⊗[K] L →ₐ[K'] (L ⊔ K' : IntermediateField K Ω) :=
    supFlipProductMapRightAlgHom (K := K) (Ω := Ω) L K'
  have hf : Function.Surjective f :=
    supFlipProductMapRightAlgHom_surjective (K := K) (Ω := Ω) L K'
  quotientKerAlgEquivOfSurjectiveCommRing
    (R := K') (A := K' ⊗[K] L)
    (B := (L ⊔ K' : IntermediateField K Ω))
    (ringR := (inferInstance : CommSemiring K'))
    (ringA := (inferInstance : CommRing (K' ⊗[K] L)))
    (algebraRA := (inferInstance : Algebra K' (K' ⊗[K] L)))
    (ringB := (inferInstance : Semiring (L ⊔ K' : IntermediateField K Ω)))
    (algebraRB := (inferInstance : Algebra K' (L ⊔ K' : IntermediateField K Ω)))
    (f := f) hf

/-- Finite-sum form of the intrinsic field-level product-map generation
`K' ⊗_K L -> L ⊔ K'`, in the order matching the valuation-ring tensor
product. -/
theorem exists_list_sum_sup_flip_tensor_productMap_eq
    (L K' : IntermediateField K Ω) [FiniteDimensional K L]
    (x : (L ⊔ K' : IntermediateField K Ω)) :
    ∃ l : List (K' × L),
      Algebra.TensorProduct.productMap
          (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right))
          (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left))
          ((l.map (fun p => p.1 ⊗ₜ[K] p.2)).sum) =
        x := by
  rcases exists_sup_flip_tensor_productMap_eq (K := K) (Ω := Ω) L K' x with
    ⟨z, hz⟩
  rcases tensorProduct_exists_list_sum_tmul
      (R := K) (A := K') (B := L) z with ⟨l, hl⟩
  refine ⟨l, ?_⟩
  rw [← hl]
  exact hz

/-- The compositum is generated over the right factor by the left factor. -/
theorem sup_right_adjoin_left_range_eq_top
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    Algebra.adjoin K'
        (Set.range
          (IntermediateField.inclusion
            (show L ≤ L ⊔ K' from le_sup_left))) =
      (⊤ : Subalgebra K' (L ⊔ K' : IntermediateField K Ω)) := by
  let iK' :
      K' →ₐ[K] (L ⊔ K' : IntermediateField K Ω) :=
    IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right)
  let iL :
      L →ₐ[K] (L ⊔ K' : IntermediateField K Ω) :=
    IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left)
  let S : Subalgebra K' (L ⊔ K' : IntermediateField K Ω) :=
    Algebra.adjoin K' (Set.range iL)
  change S = ⊤
  apply Algebra.eq_top_iff.2
  intro x
  rcases exists_sup_flip_tensor_productMap_eq (K := K) (Ω := Ω) L K' x with
    ⟨z, hz⟩
  rw [← hz]
  refine TensorProduct.inductionOn z ?tmul ?add
  · intro a b
    have ha : iK' a ∈ S := by
      change algebraMap K' (L ⊔ K' : IntermediateField K Ω) a ∈ S
      exact S.algebraMap_mem a
    have hb : iL b ∈ S :=
      Algebra.subset_adjoin (R := K') (s := Set.range iL) ⟨b, rfl⟩
    simpa [S, iK', iL, Algebra.TensorProduct.productMap_apply_tmul] using
      S.mul_mem ha hb
  · intro x y hx hy
    simpa [map_add] using S.add_mem hx hy

/-- If the left factor is generated over `K` by one element, then the
compositum is generated over the right factor by the image of that same
element.  This is the field-level primitive-generator source behind the
residue-generation step in unramified base change. -/
theorem sup_right_adjoin_left_singleton_eq_top_of_adjoin_eq_top
    (L K' : IntermediateField K Ω) [FiniteDimensional K L]
    (x : L)
    (hx : Algebra.adjoin K ({x} : Set L) =
      (⊤ : Subalgebra K L)) :
    Algebra.adjoin K'
        ({(IntermediateField.inclusion
            (show L ≤ L ⊔ K' from le_sup_left)) x} :
          Set (L ⊔ K' : IntermediateField K Ω)) =
      (⊤ : Subalgebra K' (L ⊔ K' : IntermediateField K Ω)) := by
  let iL :
      L →ₐ[K] (L ⊔ K' : IntermediateField K Ω) :=
    IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left)
  let S : Subalgebra K' (L ⊔ K' : IntermediateField K Ω) :=
    Algebra.adjoin K' ({iL x} : Set (L ⊔ K' : IntermediateField K Ω))
  have hrange_le :
      Algebra.adjoin K' (Set.range iL) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    intro y hy
    rcases hy with ⟨z, rfl⟩
    have hz : z ∈ Algebra.adjoin K ({x} : Set L) := by
      simp [hx]
    change iL z ∈ S
    refine
      Algebra.adjoin_induction
        (p := fun z _ => iL z ∈ S)
        ?mem ?algebraMap ?add ?mul hz
    · intro z hz
      have hz_eq : z = x := by
        simpa using hz
      rw [hz_eq]
      exact Algebra.self_mem_adjoin_singleton K' (iL x)
    · intro a
      have hscalar :
          iL (algebraMap K L a) =
            algebraMap K' (L ⊔ K' : IntermediateField K Ω)
              (algebraMap K K' a) := by
        ext
        rfl
      rw [hscalar]
      exact S.algebraMap_mem (algebraMap K K' a)
    · intro z₁ z₂ _hz₁ _hz₂ hz₁_mem hz₂_mem
      simpa [map_add] using S.add_mem hz₁_mem hz₂_mem
    · intro z₁ z₂ _hz₁ _hz₂ hz₁_mem hz₂_mem
      simpa [map_mul] using S.mul_mem hz₁_mem hz₂_mem
  have htop_le : (⊤ : Subalgebra K' (L ⊔ K' : IntermediateField K Ω)) ≤ S := by
    rw [← sup_right_adjoin_left_range_eq_top (K := K) (Ω := Ω) L K']
    exact hrange_le
  exact le_antisymm le_top htop_le

/-- Tower formula for the degree of the compositum over the right factor. -/
theorem right_finrank_mul_compositum_finrank
    (L K' : IntermediateField K Ω) :
    Module.finrank K K' *
        Module.finrank K'
          (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) =
      Module.finrank K (L ⊔ K' : IntermediateField K Ω) := by
  have h := IntermediateField.finrank_bot_mul_relfinrank
    (show K' ≤ L ⊔ K' from le_sup_right)
  simpa [IntermediateField.relfinrank_eq_finrank_of_le
    (show K' ≤ L ⊔ K' from le_sup_right)] using h

/-- Tower formula for the degree of the compositum over the left factor. -/
theorem left_finrank_mul_compositum_finrank
    (L K' : IntermediateField K Ω) :
    Module.finrank K L *
        Module.finrank L
          (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) =
      Module.finrank K (L ⊔ K' : IntermediateField K Ω) := by
  have h := IntermediateField.finrank_bot_mul_relfinrank
    (show L ≤ L ⊔ K' from le_sup_left)
  simpa [IntermediateField.relfinrank_eq_finrank_of_le
    (show L ≤ L ⊔ K' from le_sup_left)] using h

/-- The compositum is finite over the right factor when the left factor is
finite over the base. -/
theorem finiteDimensional_compositum_over_right_of_left
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] :
    FiniteDimensional K'
      (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) := by
  change FiniteDimensional K' (L ⊔ K' : IntermediateField K Ω)
  exact finiteDimensional_sup_over_right_of_left L K'

/-- The compositum is finite over the right factor when both factors are
finite over the base. -/
theorem finiteDimensional_compositum_over_right
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K'] :
    FiniteDimensional K'
      (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) := by
  exact finiteDimensional_compositum_over_right_of_left L K'

/-- The compositum is finite over the left factor when both factors are finite
over the base. -/
theorem finiteDimensional_compositum_over_left
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K'] :
    FiniteDimensional L
      (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) := by
  apply FiniteDimensional.of_finrank_pos
  have hformula := left_finrank_mul_compositum_finrank (K := K) (Ω := Ω) L K'
  have hsup_pos : 0 < Module.finrank K (L ⊔ K' : IntermediateField K Ω) := by
    exact Module.finrank_pos
  rw [← hformula] at hsup_pos
  exact Nat.pos_of_mul_pos_left hsup_pos

/-- The common top field `L ⊔ K'` is finite over the right factor. -/
theorem finiteDimensional_sup_over_right
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K'] :
    FiniteDimensional K' (L ⊔ K' : IntermediateField K Ω) := by
  exact finiteDimensional_sup_over_right_of_left L K'

/-- The common top field `L ⊔ K'` is finite over the left factor. -/
theorem finiteDimensional_sup_over_left
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K'] :
    FiniteDimensional L (L ⊔ K' : IntermediateField K Ω) := by
  exact FiniteDimensional.right K L (L ⊔ K' : IntermediateField K Ω)

/-- The degree of the base-changed field extension `L K' / K'` is bounded by
the degree of `L / K`. -/
theorem compositum_finrank_over_right_le_left
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K'] :
    Module.finrank K'
        (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) ≤
      Module.finrank K L := by
  have hformula := right_finrank_mul_compositum_finrank (K := K) (Ω := Ω) L K'
  have hsup_le := IntermediateField.finrank_sup_le L K'
  have hmul :
      Module.finrank K K' *
          Module.finrank K'
            (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) ≤
        Module.finrank K K' * Module.finrank K L := by
    calc
      Module.finrank K K' *
          Module.finrank K'
            (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) =
          Module.finrank K (L ⊔ K' : IntermediateField K Ω) := hformula
      _ ≤ Module.finrank K L * Module.finrank K K' := hsup_le
      _ = Module.finrank K K' * Module.finrank K L := by rw [mul_comm]
  exact Nat.le_of_mul_le_mul_left hmul
    (Module.finrank_pos (R := K) (M := K'))

/-- Symmetric bound for the degree of the compositum over the left factor. -/
theorem compositum_finrank_over_left_le_right
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K'] :
    Module.finrank L
        (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) ≤
      Module.finrank K K' := by
  have hformula := left_finrank_mul_compositum_finrank (K := K) (Ω := Ω) L K'
  have hsup_le := IntermediateField.finrank_sup_le L K'
  have hmul :
      Module.finrank K L *
          Module.finrank L
            (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) ≤
        Module.finrank K L * Module.finrank K K' := by
    calc
      Module.finrank K L *
          Module.finrank L
            (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) =
          Module.finrank K (L ⊔ K' : IntermediateField K Ω) := hformula
      _ ≤ Module.finrank K L * Module.finrank K K' := hsup_le
  exact Nat.le_of_mul_le_mul_left hmul
    (Module.finrank_pos (R := K) (M := L))

/-- Common-top form of the degree bound for `L ⊔ K' / K'`. -/
theorem sup_finrank_over_right_le_left
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K'] :
    Module.finrank K' (L ⊔ K' : IntermediateField K Ω) ≤
      Module.finrank K L := by
  have hformula :
      Module.finrank K K' *
          Module.finrank K' (L ⊔ K' : IntermediateField K Ω) =
        Module.finrank K (L ⊔ K' : IntermediateField K Ω) :=
    Module.finrank_mul_finrank K K' (L ⊔ K' : IntermediateField K Ω)
  have hsup_le := IntermediateField.finrank_sup_le L K'
  have hmul :
      Module.finrank K K' *
          Module.finrank K' (L ⊔ K' : IntermediateField K Ω) ≤
        Module.finrank K K' * Module.finrank K L := by
    calc
      Module.finrank K K' *
          Module.finrank K' (L ⊔ K' : IntermediateField K Ω) =
          Module.finrank K (L ⊔ K' : IntermediateField K Ω) := hformula
      _ ≤ Module.finrank K L * Module.finrank K K' := hsup_le
      _ = Module.finrank K K' * Module.finrank K L := by rw [mul_comm]
  exact Nat.le_of_mul_le_mul_left hmul
    (Module.finrank_pos (R := K) (M := K'))

/-- Common-top form of the degree bound for `L ⊔ K' / L`. -/
theorem sup_finrank_over_left_le_right
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K'] :
    Module.finrank L (L ⊔ K' : IntermediateField K Ω) ≤
      Module.finrank K K' := by
  have hformula :
      Module.finrank K L *
          Module.finrank L (L ⊔ K' : IntermediateField K Ω) =
        Module.finrank K (L ⊔ K' : IntermediateField K Ω) :=
    Module.finrank_mul_finrank K L (L ⊔ K' : IntermediateField K Ω)
  have hsup_le := IntermediateField.finrank_sup_le L K'
  have hmul :
      Module.finrank K L *
          Module.finrank L (L ⊔ K' : IntermediateField K Ω) ≤
        Module.finrank K L * Module.finrank K K' := by
    calc
      Module.finrank K L *
          Module.finrank L (L ⊔ K' : IntermediateField K Ω) =
          Module.finrank K (L ⊔ K' : IntermediateField K Ω) := hformula
      _ ≤ Module.finrank K L * Module.finrank K K' := hsup_le
  exact Nat.le_of_mul_le_mul_left hmul
    (Module.finrank_pos (R := K) (M := L))

/-- Relative-degree square for a compositum, measured from the intersection
`L ⊓ K'`. -/
theorem relfinrank_intersection_square
    (L K' : IntermediateField K Ω) :
    (L ⊓ K').relfinrank K' * K'.relfinrank (L ⊔ K') =
      (L ⊓ K').relfinrank L * L.relfinrank (L ⊔ K') := by
  have hright :
      (L ⊓ K').relfinrank K' * K'.relfinrank (L ⊔ K') =
        (L ⊓ K').relfinrank (L ⊔ K') :=
    IntermediateField.relfinrank_mul_relfinrank
      (show L ⊓ K' ≤ K' from inf_le_right)
      (show K' ≤ L ⊔ K' from le_sup_right)
  have hleft :
      (L ⊓ K').relfinrank L * L.relfinrank (L ⊔ K') =
        (L ⊓ K').relfinrank (L ⊔ K') :=
    IntermediateField.relfinrank_mul_relfinrank
      (show L ⊓ K' ≤ L from inf_le_left)
      (show L ≤ L ⊔ K' from le_sup_left)
  rw [hright, hleft]

/-- The same relative-degree square written with base-changed intermediate
fields over the right and left compositum branches. -/
theorem relfinrank_intersection_extendScalars_square
    (L K' : IntermediateField K Ω) :
    (L ⊓ K').relfinrank K' *
        Module.finrank K'
          (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) =
      (L ⊓ K').relfinrank L *
        Module.finrank L
          (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) := by
  rw [← IntermediateField.relfinrank_eq_finrank_of_le
      (show K' ≤ L ⊔ K' from le_sup_right),
    ← IntermediateField.relfinrank_eq_finrank_of_le
      (show L ≤ L ⊔ K' from le_sup_left)]
  exact relfinrank_intersection_square L K'

/-- The right compositum degree divides the left intersection-product. -/
theorem compositum_finrank_over_right_dvd_intersection_product
    (L K' : IntermediateField K Ω) :
    Module.finrank K'
        (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) ∣
      (L ⊓ K').relfinrank L *
        Module.finrank L
          (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) := by
  exact dvd_of_mul_left_eq _
    (relfinrank_intersection_extendScalars_square L K')

/-- The left compositum degree divides the symmetric intersection-product. -/
theorem compositum_finrank_over_left_dvd_intersection_product
    (L K' : IntermediateField K Ω) :
    Module.finrank L
        (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) ∣
      (L ⊓ K').relfinrank K' *
        Module.finrank K'
          (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) := by
  exact dvd_of_mul_left_eq _
    (relfinrank_intersection_extendScalars_square L K').symm

/-- Common-top form of the right branch degree divisibility. -/
theorem sup_finrank_over_right_dvd_intersection_product
    (L K' : IntermediateField K Ω) :
    Module.finrank K' (L ⊔ K' : IntermediateField K Ω) ∣
      (L ⊓ K').relfinrank L *
        Module.finrank L (L ⊔ K' : IntermediateField K Ω) := by
  change Module.finrank K'
      (IntermediateField.extendScalars
        (show K' ≤ L ⊔ K' from le_sup_right)) ∣
    (L ⊓ K').relfinrank L *
      Module.finrank L
        (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left))
  exact compositum_finrank_over_right_dvd_intersection_product L K'

/-- Common-top form of the left branch degree divisibility. -/
theorem sup_finrank_over_left_dvd_intersection_product
    (L K' : IntermediateField K Ω) :
    Module.finrank L (L ⊔ K' : IntermediateField K Ω) ∣
      (L ⊓ K').relfinrank K' *
        Module.finrank K' (L ⊔ K' : IntermediateField K Ω) := by
  change Module.finrank L
      (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) ∣
    (L ⊓ K').relfinrank K' *
      Module.finrank K'
        (IntermediateField.extendScalars
          (show K' ≤ L ⊔ K' from le_sup_right))
  exact compositum_finrank_over_left_dvd_intersection_product L K'

/-- If two finite-degree intermediate fields have coprime degrees over the
base, then they are linearly disjoint over the base. -/
theorem linearDisjoint_of_finrank_coprime
    (L K' : IntermediateField K Ω)
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K')) :
    L.LinearDisjoint K' :=
  IntermediateField.LinearDisjoint.of_finrank_coprime hcop

/-- Under linear disjointness, the degree of `L K' / K'` equals the degree of
`L / K`. -/
theorem compositum_finrank_over_right_eq_left_of_linearDisjoint
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K K']
    (hlin : L.LinearDisjoint K') :
    Module.finrank K'
        (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) =
      Module.finrank K L := by
  have hformula := right_finrank_mul_compositum_finrank (K := K) (Ω := Ω) L K'
  have hsup := hlin.finrank_sup
  have hmul :
      Module.finrank K K' *
          Module.finrank K'
            (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) =
        Module.finrank K K' * Module.finrank K L := by
    calc
      Module.finrank K K' *
          Module.finrank K'
            (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) =
          Module.finrank K (L ⊔ K' : IntermediateField K Ω) := hformula
      _ = Module.finrank K L * Module.finrank K K' := hsup
      _ = Module.finrank K K' * Module.finrank K L := by rw [mul_comm]
  exact Nat.mul_left_cancel (Module.finrank_pos (R := K) (M := K')) hmul

/-- Under linear disjointness, the degree of `L K' / L` equals the degree of
`K' / K`. -/
theorem compositum_finrank_over_left_eq_right_of_linearDisjoint
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L]
    (hlin : L.LinearDisjoint K') :
    Module.finrank L
        (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) =
      Module.finrank K K' := by
  have hformula := left_finrank_mul_compositum_finrank (K := K) (Ω := Ω) L K'
  have hsup := hlin.finrank_sup
  have hmul :
      Module.finrank K L *
          Module.finrank L
            (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) =
        Module.finrank K L * Module.finrank K K' := by
    calc
      Module.finrank K L *
          Module.finrank L
            (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) =
          Module.finrank K (L ⊔ K' : IntermediateField K Ω) := hformula
      _ = Module.finrank K L * Module.finrank K K' := hsup
  exact Nat.mul_left_cancel (Module.finrank_pos (R := K) (M := L)) hmul

/-- Common-top form of the degree equality for `L ⊔ K' / K'` under linear
disjointness. -/
theorem sup_finrank_over_right_eq_left_of_linearDisjoint
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K']
    (hlin : L.LinearDisjoint K') :
    Module.finrank K' (L ⊔ K' : IntermediateField K Ω) =
      Module.finrank K L := by
  have hformula :
      Module.finrank K K' *
          Module.finrank K' (L ⊔ K' : IntermediateField K Ω) =
        Module.finrank K (L ⊔ K' : IntermediateField K Ω) :=
    Module.finrank_mul_finrank K K' (L ⊔ K' : IntermediateField K Ω)
  have hsup := hlin.finrank_sup
  have hmul :
      Module.finrank K K' *
          Module.finrank K' (L ⊔ K' : IntermediateField K Ω) =
        Module.finrank K K' * Module.finrank K L := by
    calc
      Module.finrank K K' *
          Module.finrank K' (L ⊔ K' : IntermediateField K Ω) =
          Module.finrank K (L ⊔ K' : IntermediateField K Ω) := hformula
      _ = Module.finrank K L * Module.finrank K K' := hsup
      _ = Module.finrank K K' * Module.finrank K L := by rw [mul_comm]
  exact Nat.mul_left_cancel (Module.finrank_pos (R := K) (M := K')) hmul

/-- Common-top form of the degree equality for `L ⊔ K' / L` under linear
disjointness. -/
theorem sup_finrank_over_left_eq_right_of_linearDisjoint
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K']
    (hlin : L.LinearDisjoint K') :
    Module.finrank L (L ⊔ K' : IntermediateField K Ω) =
      Module.finrank K K' := by
  have hformula :
      Module.finrank K L *
          Module.finrank L (L ⊔ K' : IntermediateField K Ω) =
        Module.finrank K (L ⊔ K' : IntermediateField K Ω) :=
    Module.finrank_mul_finrank K L (L ⊔ K' : IntermediateField K Ω)
  have hsup := hlin.finrank_sup
  have hmul :
      Module.finrank K L *
          Module.finrank L (L ⊔ K' : IntermediateField K Ω) =
        Module.finrank K L * Module.finrank K K' := by
    calc
      Module.finrank K L *
          Module.finrank L (L ⊔ K' : IntermediateField K Ω) =
          Module.finrank K (L ⊔ K' : IntermediateField K Ω) := hformula
      _ = Module.finrank K L * Module.finrank K K' := hsup
  exact Nat.mul_left_cancel (Module.finrank_pos (R := K) (M := L)) hmul

/-- Coprime-degree form of the degree equality for `L K' / K'`. -/
theorem compositum_finrank_over_right_eq_left_of_finrank_coprime
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K K']
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K')) :
    Module.finrank K'
        (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) =
      Module.finrank K L :=
  compositum_finrank_over_right_eq_left_of_linearDisjoint L K'
    (linearDisjoint_of_finrank_coprime L K' hcop)

/-- Coprime-degree form of the degree equality for `L K' / L`. -/
theorem compositum_finrank_over_left_eq_right_of_finrank_coprime
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L]
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K')) :
    Module.finrank L
        (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) =
      Module.finrank K K' :=
  compositum_finrank_over_left_eq_right_of_linearDisjoint L K'
    (linearDisjoint_of_finrank_coprime L K' hcop)

/-- Common-top coprime-degree form of the degree equality for `L ⊔ K' / K'`. -/
theorem sup_finrank_over_right_eq_left_of_finrank_coprime
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K']
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K')) :
    Module.finrank K' (L ⊔ K' : IntermediateField K Ω) =
      Module.finrank K L :=
  sup_finrank_over_right_eq_left_of_linearDisjoint L K'
    (linearDisjoint_of_finrank_coprime L K' hcop)

/-- Common-top coprime-degree form of the degree equality for `L ⊔ K' / L`. -/
theorem sup_finrank_over_left_eq_right_of_finrank_coprime
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K']
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K')) :
    Module.finrank L (L ⊔ K' : IntermediateField K Ω) =
      Module.finrank K K' :=
  sup_finrank_over_left_eq_right_of_linearDisjoint L K'
    (linearDisjoint_of_finrank_coprime L K' hcop)

/-- Field-level source for unramified base change: after arbitrary finite
base change `K'/K`, the common top `L ⊔ K'` is separable over `K'` as soon as
`L/K` is separable.

This uses formal unramifiedness of separable field extensions, stability under
base change, and the surjective product map `K' ⊗_K L -> L ⊔ K'`. -/
theorem isSeparable_sup_over_right_of_left
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K']
    [Algebra.IsSeparable K L] :
    Algebra.IsSeparable K' (L ⊔ K' : IntermediateField K Ω) := by
  have : Algebra.FormallyUnramified K L :=
    Algebra.FormallyUnramified.of_isSeparable K L
  have hsurj : Function.Surjective
      (supFlipProductMapRightAlgHom (K := K) (Ω := Ω) L K') :=
    supFlipProductMapRightAlgHom_surjective (K := K) (Ω := Ω) L K'
  have : Algebra.FormallyUnramified K'
      (L ⊔ K' : IntermediateField K Ω) :=
    Algebra.FormallyUnramified.of_surjective
      (R := K') (A := K' ⊗[K] L)
      (B := (L ⊔ K' : IntermediateField K Ω))
      (supFlipProductMapRightAlgHom (K := K) (Ω := Ω) L K')
      hsurj
  have : Algebra.EssFiniteType K'
      (L ⊔ K' : IntermediateField K Ω) := by
    have : FiniteDimensional K' (L ⊔ K' : IntermediateField K Ω) :=
      finiteDimensional_sup_over_right_of_left (K := K) (Ω := Ω) L K'
    infer_instance
  exact Algebra.FormallyUnramified.isSeparable K'
    (L ⊔ K' : IntermediateField K Ω)

/-- The compositum is separable over the right factor after arbitrary finite
base change, provided the left factor is separable over the base. -/
theorem isSeparable_compositum_over_right
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K']
    [Algebra.IsSeparable K L] :
    Algebra.IsSeparable K'
      (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) := by
  change Algebra.IsSeparable K' (L ⊔ K' : IntermediateField K Ω)
  exact isSeparable_sup_over_right_of_left L K'

/-- Symmetric separability statement for the compositum over the left factor. -/
theorem isSeparable_compositum_over_left
    (L K' : IntermediateField K Ω)
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] :
    Algebra.IsSeparable L
      (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) := by
  have : Algebra.IsSeparable K
      (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) := by
    change Algebra.IsSeparable K
      ((IntermediateField.extendScalars
        (show L ≤ L ⊔ K' from le_sup_left)).restrictScalars K)
    rw [IntermediateField.extendScalars_restrictScalars]
    infer_instance
  exact Algebra.isSeparable_tower_top_of_isSeparable K L
    (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left))

/-- The common top field is separable over the right factor after arbitrary
finite base change, provided the left factor is separable over the base. -/
theorem isSeparable_sup_over_right
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K']
    [Algebra.IsSeparable K L] :
    Algebra.IsSeparable K' (L ⊔ K' : IntermediateField K Ω) := by
  exact isSeparable_sup_over_right_of_left L K'

/-- The common top field is separable over the left factor when both factors
are separable over the base. -/
theorem isSeparable_sup_over_left
    (L K' : IntermediateField K Ω)
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] :
    Algebra.IsSeparable L (L ⊔ K' : IntermediateField K Ω) := by
  exact Algebra.isSeparable_tower_top_of_isSeparable K L
    (L ⊔ K' : IntermediateField K Ω)

end FieldCompositum
end DiscreteValuationField

end
