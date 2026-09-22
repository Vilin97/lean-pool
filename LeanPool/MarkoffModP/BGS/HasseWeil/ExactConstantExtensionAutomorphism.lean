/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtension
import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantFieldAutomorphism
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Galois groups of exact constant extensions

For a tower `C ⊆ L ⊆ N` and a finite Galois extension `S / C`, the tensor
compositum `S ⊗[C] N` carries two commuting actions: constants act on the left
factor and `Gal(N/L)` acts on the right factor.  The actions are jointly
faithful without any exact-constant hypothesis.

If `C` is the exact constant field of `N`, the tensor product is a field.  A
degree count then proves that the combined action exhausts its full Galois
group over `L`:

`Gal((S ⊗[C] N) / L) ≃ Gal(S/C) × Gal(N/L)`.

This is the direct-product statement used in Stichtenoth, Proposition 5.2.8.
-/

open scoped TensorProduct

namespace BGS.HasseWeil

noncomputable section

/-- The tensor compositum of a field `N` and a constant extension `S / C`. -/
abbrev ExactConstantExtension (C N S : Type*) [CommRing C] [CommRing N]
    [CommRing S] [Algebra C N] [Algebra C S] :=
  S ⊗[C] N

section Algebra

variable (C L N S : Type*) [Field C] [Field L] [Field N] [Field S]
  [Algebra L N] [Algebra C N] [Algebra C S]

/-- The field structure on the tensor compositum supplied by exact constants
and finite Galois constant extension. -/
@[reducible] noncomputable def exactConstantExtensionField
    [FiniteDimensional C S] [IsGalois C S]
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    Field (ExactConstantExtension C N S) :=
  (exactConstantExtensionTensor_isField C N S hExact).toField

/-- The `L`-algebra structure on the tensor compositum induced by the right
factor `N`. -/
@[reducible] noncomputable def exactConstantExtensionBaseAlgebra :
    Algebra L (ExactConstantExtension C N S) :=
  RingHom.toAlgebra
    ((Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := N)).toRingHom.comp (algebraMap L N))

/-- The `L ⊆ N ⊆ S ⊗[C] N` scalar tower. -/
theorem exactConstantExtensionBaseTower :
    letI := exactConstantExtensionBaseAlgebra C L N S
    letI := exactConstantExtensionAlgebra C N S
    IsScalarTower L N (ExactConstantExtension C N S) := by
  let := exactConstantExtensionBaseAlgebra C L N S
  let := exactConstantExtensionAlgebra C N S
  exact IsScalarTower.of_algebraMap_eq' rfl

end Algebra

section Actions

variable (C L N S : Type*) [Field C] [Field L] [Field N] [Field S]
  [Algebra C L] [Algebra L N] [Algebra C N] [IsScalarTower C L N]
  [Algebra C S]

/-- A constant-field automorphism acting on the left tensor factor and fixing
`N`, viewed as an automorphism over `L`. -/
noncomputable def exactConstantExtensionConstantAlgEquivOverBase
    (σ : S ≃ₐ[C] S) :
    letI := exactConstantExtensionBaseAlgebra C L N S
    ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S := by
  letI := exactConstantExtensionBaseAlgebra C L N S
  exact
    { tensorConstantAlgEquiv C S N σ with
      commutes' := fun l => by
        change tensorConstantAlgEquiv C S N σ
            (Algebra.TensorProduct.includeRight (algebraMap L N l)) =
          Algebra.TensorProduct.includeRight (algebraMap L N l)
        simp }

/-- A function-field automorphism acting on the right tensor factor and
fixing `S`, viewed as an automorphism over `L`. -/
noncomputable def exactConstantExtensionFunctionAlgEquivOverBase
    (g : N ≃ₐ[L] N) :
    letI := exactConstantExtensionBaseAlgebra C L N S
    ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S := by
  letI := exactConstantExtensionBaseAlgebra C L N S
  let gC : N ≃ₐ[C] N := g.restrictScalars C
  let eC : ExactConstantExtension C N S ≃ₐ[C]
      ExactConstantExtension C N S :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[C] S) gC
  exact
    { eC with
      commutes' := fun l => by
        change eC (Algebra.TensorProduct.includeRight (algebraMap L N l)) =
          Algebra.TensorProduct.includeRight (algebraMap L N l)
        simp [eC, gC, Algebra.TensorProduct.includeRight_apply] }

/-- The constant-field action as a homomorphism into automorphisms over
`L`. -/
noncomputable def exactConstantExtensionConstantAutHom :
    letI := exactConstantExtensionBaseAlgebra C L N S
    (S ≃ₐ[C] S) →*
      (ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S) := by
  letI := exactConstantExtensionBaseAlgebra C L N S
  exact
    { toFun := exactConstantExtensionConstantAlgEquivOverBase C L N S
      map_one' := by
        apply AlgEquiv.ext
        intro z
        induction z using TensorProduct.inductionOn with
        | tmul s n => simp [exactConstantExtensionConstantAlgEquivOverBase]
        | add x y hx hy => simp [hx, hy]
      map_mul' := by
        intro σ τ
        apply AlgEquiv.ext
        intro z
        induction z using TensorProduct.inductionOn with
        | tmul s n => simp [exactConstantExtensionConstantAlgEquivOverBase]
        | add x y hx hy => simp [hx, hy] }

/-- The function-field action as a homomorphism into automorphisms over
`L`. -/
noncomputable def exactConstantExtensionFunctionAutHom :
    letI := exactConstantExtensionBaseAlgebra C L N S
    (N ≃ₐ[L] N) →*
      (ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S) := by
  letI := exactConstantExtensionBaseAlgebra C L N S
  exact
    { toFun := exactConstantExtensionFunctionAlgEquivOverBase C L N S
      map_one' := by
        apply AlgEquiv.ext
        intro z
        induction z using TensorProduct.inductionOn with
        | tmul s n => simp [exactConstantExtensionFunctionAlgEquivOverBase]
        | add x y hx hy => simp [hx, hy]
      map_mul' := by
        intro g h
        apply AlgEquiv.ext
        intro z
        induction z using TensorProduct.inductionOn with
        | tmul s n => simp [exactConstantExtensionFunctionAlgEquivOverBase]
        | add x y hx hy => simp [hx, hy] }

/-- Constant-field and function-field automorphisms commute on the tensor
compositum. -/
theorem exactConstantExtension_constant_function_commute
    (σ : S ≃ₐ[C] S) (g : N ≃ₐ[L] N) :
    letI := exactConstantExtensionBaseAlgebra C L N S
    Commute
      (exactConstantExtensionConstantAutHom C L N S σ)
      (exactConstantExtensionFunctionAutHom C L N S g) := by
  let := exactConstantExtensionBaseAlgebra C L N S
  rw [Commute]
  apply AlgEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s n => simp [exactConstantExtensionConstantAutHom,
      exactConstantExtensionFunctionAutHom,
      exactConstantExtensionConstantAlgEquivOverBase,
      exactConstantExtensionFunctionAlgEquivOverBase]
  | add x y hx hy =>
      simp only [map_add]
      exact congrArg₂ (· + ·) hx hy

/-- The product of the commuting constant and function-field actions. -/
noncomputable def exactConstantExtensionCombinedAutHom :
    letI := exactConstantExtensionBaseAlgebra C L N S
    (S ≃ₐ[C] S) × (N ≃ₐ[L] N) →*
      (ExactConstantExtension C N S ≃ₐ[L]
        ExactConstantExtension C N S) := by
  letI := exactConstantExtensionBaseAlgebra C L N S
  exact (exactConstantExtensionConstantAutHom C L N S).noncommCoprod
    (exactConstantExtensionFunctionAutHom C L N S)
    (exactConstantExtension_constant_function_commute C L N S)

/-- The two tensor-factor actions are jointly faithful. -/
theorem exactConstantExtensionCombinedAutHom_injective :
    letI := exactConstantExtensionBaseAlgebra C L N S
    Function.Injective (exactConstantExtensionCombinedAutHom C L N S) := by
  let := exactConstantExtensionBaseAlgebra C L N S
  intro p q hpq
  apply Prod.ext
  · ext s
    have h := DFunLike.congr_fun hpq (s ⊗ₜ[C] (1 : N))
    have hinc :
        Algebra.TensorProduct.includeLeft
            (R := C) (S := C) (A := S) (B := N) (p.1 s) =
          Algebra.TensorProduct.includeLeft
            (R := C) (S := C) (A := S) (B := N) (q.1 s) := by
      simpa [Algebra.TensorProduct.includeLeft_apply,
        exactConstantExtensionCombinedAutHom,
        exactConstantExtensionConstantAutHom,
        exactConstantExtensionFunctionAutHom,
        exactConstantExtensionConstantAlgEquivOverBase,
        exactConstantExtensionFunctionAlgEquivOverBase] using h
    exact Algebra.TensorProduct.includeLeft_injective
      (R := C) (S := C) (A := S) (B := N) (algebraMap C N).injective hinc
  · ext n
    have h := DFunLike.congr_fun hpq ((1 : S) ⊗ₜ[C] n)
    have hinc :
        Algebra.TensorProduct.includeRight
            (R := C) (A := S) (B := N) (p.2 n) =
          Algebra.TensorProduct.includeRight
            (R := C) (A := S) (B := N) (q.2 n) := by
      simpa [Algebra.TensorProduct.includeRight_apply,
        exactConstantExtensionCombinedAutHom,
        exactConstantExtensionConstantAutHom,
        exactConstantExtensionFunctionAutHom,
        exactConstantExtensionConstantAlgEquivOverBase,
        exactConstantExtensionFunctionAlgEquivOverBase] using h
    exact Algebra.TensorProduct.includeRight_injective
      (R := C) (A := S) (B := N) (algebraMap C S).injective hinc

end Actions

section Galois

variable (C L N S : Type*) [Field C] [Field L] [Field N] [Field S]
  [Algebra C L] [Algebra L N] [Algebra C N] [IsScalarTower C L N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [FiniteDimensional L N] [IsGalois L N]

omit [Algebra C L] [IsScalarTower C L N]
  [FiniteDimensional C S] [IsGalois C S]
  [FiniteDimensional L N] [IsGalois L N] in
/-- The tensor compositum has degree `[N : L] [S : C]` over `L`. -/
theorem exactConstantExtension_finrank_over_base :
    letI := exactConstantExtensionBaseAlgebra C L N S
    Module.finrank L (ExactConstantExtension C N S) =
      Module.finrank L N * Module.finrank C S := by
  let := exactConstantExtensionBaseAlgebra C L N S
  let := exactConstantExtensionAlgebra C N S
  let := exactConstantExtensionBaseTower C L N S
  change Module.finrank L (S ⊗[C] N) =
    Module.finrank L N * Module.finrank C S
  rw [← Module.finrank_mul_finrank L N (ExactConstantExtension C N S),
    exactConstantExtension_finrank C N S]

/-- With exact constants, the tensor compositum is Galois over `L`. -/
theorem exactConstantExtension_isGalois
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    IsGalois L (ExactConstantExtension C N S) := by
  let := exactConstantExtensionField C N S hExact
  let := exactConstantExtensionBaseAlgebra C L N S
  let := exactConstantExtensionAlgebra C N S
  let := exactConstantExtensionBaseTower C L N S
  let e := exactConstantExtensionLinearEquiv C N S
  let : Module.Finite N (N ⊗[C] S) := Module.Finite.base_change C N S
  let : Module.Finite N (ExactConstantExtension C N S) := Module.Finite.equiv e
  let : Module.Finite L (ExactConstantExtension C N S) :=
    Module.Finite.trans N (ExactConstantExtension C N S)
  apply IsGalois.of_card_aut_eq_finrank
  apply Nat.le_antisymm
  · calc
      Nat.card (ExactConstantExtension C N S ≃ₐ[L]
          ExactConstantExtension C N S) =
          Nat.card (ExactConstantExtension C N S →ₐ[L]
            ExactConstantExtension C N S) :=
        Nat.card_congr
          (algEquivEquivAlgHom L (ExactConstantExtension C N S))
      _ ≤ Module.finrank L (ExactConstantExtension C N S) :=
        card_algHom_le_finrank L (ExactConstantExtension C N S)
          (ExactConstantExtension C N S)
  · calc
      Module.finrank L (ExactConstantExtension C N S) =
          Module.finrank L N * Module.finrank C S :=
        exactConstantExtension_finrank_over_base C L N S
      _ = Nat.card (N ≃ₐ[L] N) * Nat.card (S ≃ₐ[C] S) := by
        rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
      _ = Nat.card ((S ≃ₐ[C] S) × (N ≃ₐ[L] N)) := by
        rw [Nat.card_prod, mul_comm]
      _ ≤ Nat.card (ExactConstantExtension C N S ≃ₐ[L]
          ExactConstantExtension C N S) :=
        Nat.card_le_card_of_injective
          (exactConstantExtensionCombinedAutHom C L N S)
          (exactConstantExtensionCombinedAutHom_injective C L N S)

/-- The full Galois group of an exact finite constant extension is the direct
product of the constant and function-field Galois groups. -/
noncomputable def exactConstantExtensionAutMulEquiv
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    (S ≃ₐ[C] S) × (N ≃ₐ[L] N) ≃*
      (ExactConstantExtension C N S ≃ₐ[L]
        ExactConstantExtension C N S) := by
  letI := exactConstantExtensionField C N S hExact
  letI := exactConstantExtensionBaseAlgebra C L N S
  letI := exactConstantExtensionAlgebra C N S
  letI := exactConstantExtensionBaseTower C L N S
  let e := exactConstantExtensionLinearEquiv C N S
  letI : Module.Finite N (N ⊗[C] S) := Module.Finite.base_change C N S
  letI : Module.Finite N (ExactConstantExtension C N S) := Module.Finite.equiv e
  letI : Module.Finite L (ExactConstantExtension C N S) :=
    Module.Finite.trans N (ExactConstantExtension C N S)
  letI : IsGalois L (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C L N S hExact
  let h := exactConstantExtensionCombinedAutHom C L N S
  let hinj := exactConstantExtensionCombinedAutHom_injective C L N S
  apply MulEquiv.ofBijective h
  apply hinj.bijective_of_nat_card_le
  rw [Nat.card_prod, IsGalois.card_aut_eq_finrank,
    exactConstantExtension_finrank_over_base C L N S,
    IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank, mul_comm]

end Galois

end

end BGS.HasseWeil
