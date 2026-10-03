/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FinitePlaceTensorNormSubgroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Finite-place norm kernels of a global Artin map

This is a Mathlib-typed local--global compatibility statement. Restricting
one global Artin map along Mathlib's one-place idèle-class homomorphism has
the local tensor-norm group as its kernel. It specifies the kernel at each
finite place, not yet the value normalization against a separately chosen
local Artin map or the real-place comparison.

The proof transports the established restricted-product reciprocity map
through the algebraic comparison with Mathlib's idèle class group.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

open GlobalClassFieldTheory.Reciprocity renaming
  chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm →
    chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm in
/-- A finite abelian extension has one global Artin homomorphism whose
restriction to each finite completion has precisely the tensor-norm kernel. -/
theorem exists_finiteAbelianGlobalArtin_finitePlaceNormKernel
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    ∃ artin : NumberField.IdeleClassGroup (𝓞 K) K →*
        (L ≃ₐ[K] L),
      Function.Surjective artin ∧
      ∀ (v : HeightOneSpectrum (𝓞 K))
        (x : (v.adicCompletion K)ˣ),
        artin (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x) = 1 ↔
          x ∈ finitePlaceTensorNormSubgroup K L v := by
  let e := IdeleGroup.ideleClassGroupEquivMathlib K
  let artin : NumberField.IdeleClassGroup (𝓞 K) K →* (L ≃ₐ[K] L) :=
    (GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom K L).comp
      e.symm.toMonoidHom
  refine ⟨artin, ?_, ?_⟩
  · exact (GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_surjective
      K L).comp e.symm.surjective
  · intro v x
    have hclass :
        e.symm (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x) =
          IdeleGroup.finitePlaceIdeleClass v x := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact (IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass
        K v x).symm
    change GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom K L
        (e.symm (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x)) =
          1 ↔ _
    rw [hclass]
    have hcompat :
        GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom K L
            (IdeleGroup.finitePlaceIdeleClass v x) =
          GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v x := by
      simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun
        (GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_comp_finitePlaceIdeleClass
          (K := K) (L := L) v) x
    rw [hcompat]
    rw [chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm,
      ← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup (K := K) (L := L) v]
    change x ∈ (localTensorNorm (K := K) (L := L) v).range ↔
      x ∈ finitePlaceTensorNormSubgroup K L v
    rfl

end ClassFieldTheory
