/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionAutomorphism

/-!
# The Frobenius quotient of an exact constant extension

The direct-product description of the constant extension gives a canonical
quotient from its full Galois group to the Galois group of the enlarged
constants.  Its kernel is exactly the original function-field Galois group.
When the constants are finite, the Frobenius fiber is explicitly equivalent
to that kernel; these are the twists used in the lower-bound argument.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

variable (C L N S : Type*) [Field C] [Field L] [Field N] [Field S]
  [Algebra C L] [Algebra L N] [Algebra C N] [IsScalarTower C L N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [FiniteDimensional L N] [IsGalois L N]

/-- Restriction to the enlarged constants, defined through the proved
direct-product description of the full Galois group. -/
noncomputable def exactConstantExtensionConstantQuotient
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    (ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S) →*
      (S ≃ₐ[C] S) := by
  letI := exactConstantExtensionField C N S hExact
  letI := exactConstantExtensionBaseAlgebra C L N S
  exact (MonoidHom.fst (S ≃ₐ[C] S) (N ≃ₐ[L] N)).comp
    (exactConstantExtensionAutMulEquiv C L N S hExact).symm.toMonoidHom

/-- On an automorphism assembled from its two tensor factors, the constant
quotient returns the first factor. -/
theorem exactConstantExtensionConstantQuotient_combined
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))
    (σ : S ≃ₐ[C] S) (g : N ≃ₐ[L] N) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    exactConstantExtensionConstantQuotient C L N S hExact
        (exactConstantExtensionCombinedAutHom C L N S (σ, g)) = σ := by
  let := exactConstantExtensionField C N S hExact
  let := exactConstantExtensionBaseAlgebra C L N S
  let e := exactConstantExtensionAutMulEquiv C L N S hExact
  change (e.symm (e (σ, g))).1 = σ
  rw [e.symm_apply_apply]

/-- The constant quotient records exactly how a full automorphism acts on
the embedded enlarged constant field. -/
theorem exactConstantExtensionConstantQuotient_action_on_constants
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))
    (g : letI := exactConstantExtensionField C N S hExact
      letI := exactConstantExtensionBaseAlgebra C L N S
      ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S)
    (s : S) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    g (Algebra.TensorProduct.includeLeft
      (R := C) (S := C) (A := S) (B := N) s) =
      Algebra.TensorProduct.includeLeft
        (R := C) (S := C) (A := S) (B := N)
        (exactConstantExtensionConstantQuotient C L N S hExact g s) := by
  let := exactConstantExtensionField C N S hExact
  let := exactConstantExtensionBaseAlgebra C L N S
  let e := exactConstantExtensionAutMulEquiv C L N S hExact
  let p := e.symm g
  have hgp : e p = g := e.apply_symm_apply g
  rw [← hgp]
  have hq := exactConstantExtensionConstantQuotient_combined
    C L N S hExact p.1 p.2
  change exactConstantExtensionCombinedAutHom C L N S p
      (Algebra.TensorProduct.includeLeft
        (R := C) (S := C) (A := S) (B := N) s) =
    Algebra.TensorProduct.includeLeft
      (R := C) (S := C) (A := S) (B := N)
      (exactConstantExtensionConstantQuotient C L N S hExact (e p) s)
  rw [show e p = exactConstantExtensionCombinedAutHom C L N S p by rfl]
  rw [hq]
  simp [exactConstantExtensionCombinedAutHom,
    exactConstantExtensionConstantAutHom,
    exactConstantExtensionFunctionAutHom,
    exactConstantExtensionConstantAlgEquivOverBase,
    exactConstantExtensionFunctionAlgEquivOverBase,
    Algebra.TensorProduct.includeLeft_apply]

/-- The constant quotient is onto. -/
theorem exactConstantExtensionConstantQuotient_surjective
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    Function.Surjective
      (exactConstantExtensionConstantQuotient C L N S hExact) := by
  let := exactConstantExtensionField C N S hExact
  let := exactConstantExtensionBaseAlgebra C L N S
  intro σ
  refine ⟨exactConstantExtensionCombinedAutHom C L N S
    (σ, (1 : N ≃ₐ[L] N)), ?_⟩
  exact exactConstantExtensionConstantQuotient_combined
    C L N S hExact σ 1

/-- The kernel of the constant quotient is precisely the image of the
function-field action. -/
theorem exactConstantExtensionConstantQuotient_ker :
    ∀ (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)),
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    (exactConstantExtensionConstantQuotient C L N S hExact).ker =
      (exactConstantExtensionFunctionAutHom C L N S).range := by
  intro hExact
  let := exactConstantExtensionField C N S hExact
  let := exactConstantExtensionBaseAlgebra C L N S
  ext x
  constructor
  · intro hx
    let e := exactConstantExtensionAutMulEquiv C L N S hExact
    let p := e.symm x
    have hpFirst : p.1 = 1 := by
      have hx' := (MonoidHom.mem_ker.mp hx)
      change p.1 = 1 at hx'
      exact hx'
    refine ⟨p.2, ?_⟩
    have hp : (1, p.2) = p := by
      apply Prod.ext
      · exact hpFirst.symm
      · rfl
    change exactConstantExtensionFunctionAutHom C L N S p.2 = x
    calc
      exactConstantExtensionFunctionAutHom C L N S p.2 =
          exactConstantExtensionCombinedAutHom C L N S (1, p.2) := by
        simp [exactConstantExtensionCombinedAutHom]
      _ = e (1, p.2) := rfl
      _ = e p := congrArg e hp
      _ = x := e.apply_symm_apply x
  · rintro ⟨g, rfl⟩
    apply MonoidHom.mem_ker.mpr
    have h := exactConstantExtensionConstantQuotient_combined
      C L N S hExact (1 : S ≃ₐ[C] S) g
    simpa [exactConstantExtensionCombinedAutHom] using h

omit [FiniteDimensional C S] [IsGalois C S]
  [FiniteDimensional L N] [IsGalois L N] in
/-- The constant-factor action is faithful. -/
theorem exactConstantExtensionConstantAutHom_injective :
    letI := exactConstantExtensionBaseAlgebra C L N S
    Function.Injective (exactConstantExtensionConstantAutHom C L N S) := by
  let := exactConstantExtensionBaseAlgebra C L N S
  intro σ τ h
  have hpair := exactConstantExtensionCombinedAutHom_injective C L N S
    (show exactConstantExtensionCombinedAutHom C L N S
        (σ, (1 : N ≃ₐ[L] N)) =
      exactConstantExtensionCombinedAutHom C L N S
        (τ, (1 : N ≃ₐ[L] N)) by
      simpa [exactConstantExtensionCombinedAutHom] using h)
  exact congrArg Prod.fst hpair

section Finite

variable [Fintype C] [Finite S]

/-- Frobenius on `S / C`, lifted to the tensor compositum while fixing `N`. -/
noncomputable def exactConstantExtensionFrobenius :
    letI := exactConstantExtensionBaseAlgebra C L N S
    ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S := by
  letI := exactConstantExtensionBaseAlgebra C L N S
  exact exactConstantExtensionConstantAutHom C L N S
    (FiniteField.frobeniusAlgEquivOfAlgebraic C S)

omit [FiniteDimensional C S] [FiniteDimensional L N] [IsGalois L N] in
/-- The lifted Frobenius has order `[S : C]`. -/
theorem orderOf_exactConstantExtensionFrobenius :
    letI := exactConstantExtensionBaseAlgebra C L N S
    orderOf (exactConstantExtensionFrobenius C L N S) =
      Module.finrank C S := by
  let := exactConstantExtensionBaseAlgebra C L N S
  change orderOf ((exactConstantExtensionConstantAutHom C L N S)
    (FiniteField.frobeniusAlgEquivOfAlgebraic C S)) = _
  rw [orderOf_injective (exactConstantExtensionConstantAutHom C L N S)
    (exactConstantExtensionConstantAutHom_injective C L N S)]
  exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic C S

omit [Finite S] in
/-- The constant quotient sends the lifted Frobenius to finite-field
Frobenius. -/
theorem exactConstantExtensionConstantQuotient_frobenius
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    exactConstantExtensionConstantQuotient C L N S hExact
        (exactConstantExtensionFrobenius C L N S) =
      FiniteField.frobeniusAlgEquivOfAlgebraic C S := by
  let := exactConstantExtensionField C N S hExact
  let := exactConstantExtensionBaseAlgebra C L N S
  have h := exactConstantExtensionConstantQuotient_combined
    C L N S hExact (FiniteField.frobeniusAlgEquivOfAlgebraic C S)
      (1 : N ≃ₐ[L] N)
  simpa [exactConstantExtensionFrobenius,
    exactConstantExtensionCombinedAutHom] using h

omit [Finite S] in
/-- The Frobenius fiber of the constant quotient is parametrized exactly by
the original function-field Galois group. -/
noncomputable def exactConstantExtensionFrobeniusFiberEquiv
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    (N ≃ₐ[L] N) ≃
      (exactConstantExtensionConstantQuotient C L N S hExact ⁻¹'
        ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} : Set (S ≃ₐ[C] S))) := by
  letI := exactConstantExtensionField C N S hExact
  letI := exactConstantExtensionBaseAlgebra C L N S
  let e := exactConstantExtensionAutMulEquiv C L N S hExact
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic C S
  exact
    { toFun := fun g =>
        ⟨e (φ, g), exactConstantExtensionConstantQuotient_combined
          C L N S hExact φ g⟩
      invFun := fun x => (e.symm x.1).2
      left_inv := fun g => by simp
      right_inv := fun x => by
        apply Subtype.ext
        have hfirst : (e.symm x.1).1 = φ := x.2
        have hp : (φ, (e.symm x.1).2) = e.symm x.1 := by
          apply Prod.ext
          · exact hfirst.symm
          · rfl
        calc
          e (φ, (e.symm x.1).2) = e (e.symm x.1) := congrArg e hp
          _ = x.1 := e.apply_symm_apply x.1 }

omit [Finite S] in
/-- Consequently the Frobenius fiber has the same cardinality as
`Gal(N/L)`. -/
theorem natCard_exactConstantExtensionFrobeniusFiber
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    Nat.card
        (exactConstantExtensionConstantQuotient C L N S hExact ⁻¹'
          ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
            Set (S ≃ₐ[C] S))) =
      Nat.card (N ≃ₐ[L] N) := by
  let := exactConstantExtensionField C N S hExact
  let := exactConstantExtensionBaseAlgebra C L N S
  exact Nat.card_congr
    (exactConstantExtensionFrobeniusFiberEquiv C L N S hExact).symm

end Finite

end

end BGS.HasseWeil
