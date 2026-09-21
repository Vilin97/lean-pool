/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Exact constants and finite constant extensions

Let `N / C` be a field extension whose exact constant field is `C`, meaning
that no element of `N \ C` is algebraic over `C`.  If `S / C` is finite
Galois, then `S` and `N` are linearly disjoint over `C`.  Consequently the
tensor product `S ⊗[C] N` is a field, and its degree over `N` is `[S : C]`.

Mathlib's finite-Galois intersection criterion assumes both intermediate
fields are finite over the base.  The first theorem below proves the variant
needed here: only the Galois field on the left must be finite.  This is the
algebraic foundation for the constant-extension twists in Stichtenoth,
Proposition 5.2.8.
-/

open scoped TensorProduct

namespace BGS.HasseWeil

noncomputable section

universe u v

section LinearDisjoint

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

private theorem linearDisjoint_of_inf_eq_bot_of_sup_eq_top
    (A B : IntermediateField F E)
    [IsGalois F A] [FiniteDimensional F A]
    (hsup : A ⊔ B = ⊤) (hinf : A ⊓ B = ⊥) : A.LinearDisjoint B := by
  let ι := Module.Free.ChooseBasisIndex F A
  let a : Module.Basis ι F A := Module.Free.chooseBasis F A
  letI : Fintype ι := Fintype.ofFinite ι
  have hAspan : A.toSubalgebra.toSubmodule =
      Submodule.span F (Set.range (A.val ∘ a)) := by
    calc
      A.toSubalgebra.toSubmodule =
          Submodule.map A.val.toLinearMap (⊤ : Submodule F A) := by
            ext x
            simp
      _ = Submodule.map A.val.toLinearMap
          (Submodule.span F (Set.range a)) := by rw [Module.Basis.span_eq a]
      _ = Submodule.span F (Set.range (A.val ∘ a)) := by
        rw [Submodule.map_span]
        congr 1
        ext x
        simp [Function.comp_apply]
  have hAdjoinField : IntermediateField.adjoin B (A : Set E) = ⊤ := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.restrictScalars_adjoin_eq_sup]
    simpa [sup_comm] using hsup
  have hAdjoin : Algebra.adjoin B (A : Set E) = ⊤ := by
    rw [← IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic_right B A,
      hAdjoinField]
    rfl
  have hspan : Submodule.span B (Set.range (A.val ∘ a)) = ⊤ := by
    have hAdjoin' : Algebra.adjoin B (A.toSubalgebra : Set E) = ⊤ := by
      simpa only [IntermediateField.coe_toSubalgebra] using hAdjoin
    rw [← A.toSubalgebra.adjoin_eq_span_of_eq_span B hAspan, hAdjoin']
    rfl
  letI : FiniteDimensional B E := by
    have hfinite : Module.Finite B
        (Submodule.span B (Set.range (A.val ∘ a))) :=
      Module.Finite.span_of_finite B (Set.toFinite _)
    rw [hspan] at hfinite
    exact Module.Finite.equiv (Submodule.topEquiv (R := B) (M := E))
  letI : IsGalois B E := IsGalois.sup_right A B hsup
  have hfinrank : Module.finrank B E = Module.finrank F A := by
    rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
    exact Nat.card_congr <| Equiv.ofBijective
      (IntermediateField.restrictRestrictAlgEquivMapHom F A B E)
      ⟨IntermediateField.restrictRestrictAlgEquivMapHom_injective A B hsup,
        IntermediateField.restrictRestrictAlgEquivMapHom_surjective A B hinf⟩
  apply IntermediateField.LinearDisjoint.of_basis_left a
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · exact hspan.ge
  · rw [hfinrank]
    exact (Module.finrank_eq_card_basis a).symm

/-- A finite Galois intermediate field is linearly disjoint from any other
intermediate field having trivial intersection with it.  Unlike Mathlib's
finite intersection criterion, the field on the right need not be finite over
the base. -/
theorem linearDisjoint_of_inf_eq_bot_of_finite_galois_left
    (A B : IntermediateField F E)
    [IsGalois F A] [FiniteDimensional F A]
    (hinf : A ⊓ B = ⊥) : A.LinearDisjoint B := by
  let D : IntermediateField F E := A ⊔ B
  let A' : IntermediateField F D := A.restrict le_sup_left
  let B' : IntermediateField F D := B.restrict le_sup_right
  have hA : IntermediateField.map D.val A' = A :=
    IntermediateField.lift_restrict le_sup_left
  have hB : IntermediateField.map D.val B' = B :=
    IntermediateField.lift_restrict le_sup_right
  suffices A'.LinearDisjoint B' from
    hA ▸ hB ▸ IntermediateField.LinearDisjoint.map this D.val
  have hsup : A' ⊔ B' = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top,
      IntermediateField.lift_sup, IntermediateField.lift_restrict le_sup_left,
      IntermediateField.lift_restrict le_sup_right]
  have hinf' : A' ⊓ B' = ⊥ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_bot,
      IntermediateField.lift_inf, IntermediateField.lift_restrict le_sup_left,
      IntermediateField.lift_restrict le_sup_right, hinf]
  let eA : A ≃ₐ[F] A' := IntermediateField.restrict_algEquiv ..
  letI : FiniteDimensional F A' := Module.Finite.equiv eA.toLinearEquiv
  haveI : IsGalois F A' := IsGalois.of_algEquiv eA
  exact linearDisjoint_of_inf_eq_bot_of_sup_eq_top A' B' hsup hinf'

end LinearDisjoint

section Constants

variable (C N S : Type*) [Field C] [Field N] [Field S]
  [Algebra C N] [Algebra C S]
  [FiniteDimensional C S] [IsGalois C S]

/-- Inside a common algebraic closure, a finite Galois constant extension and
a field with exact constant field `C` are linearly disjoint over `C`. -/
theorem exactConstantExtensionImages_linearDisjoint
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    let Ω := AlgebraicClosure N
    let fS : S →ₐ[C] Ω := IsAlgClosed.lift
    fS.fieldRange.LinearDisjoint
      (IsScalarTower.toAlgHom C N Ω).fieldRange := by
  let Ω := AlgebraicClosure N
  let fS : S →ₐ[C] Ω := IsAlgClosed.lift
  letI : Algebra S Ω := fS.toAlgebra
  letI : IsScalarTower C S Ω := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact (fS.commutes c).symm)
  let A := fS.fieldRange
  let B := (IsScalarTower.toAlgHom C N Ω).fieldRange
  have hInf : A ⊓ B = (⊥ : IntermediateField C Ω) := by
    refine eq_bot_iff.mpr ?_
    intro x hx
    obtain ⟨s, hs⟩ := hx.1
    obtain ⟨n, hn⟩ := hx.2
    have hxAlg : IsAlgebraic C x := by
      rw [← hs]
      exact (Algebra.IsIntegral.isIntegral s).map fS |>.isAlgebraic
    have hnAlg : IsAlgebraic C n := by
      apply (isAlgebraic_algHom_iff
        (IsScalarTower.toAlgHom C N Ω)
        (IsScalarTower.toAlgHom C N Ω).injective).mp
      have hn' : (IsScalarTower.toAlgHom C N Ω) n = x := hn
      rw [hn']
      exact hxAlg
    have hnBot : n ∈ (⊥ : IntermediateField C N) := by
      rw [← hExact]
      exact mem_algebraicClosure_iff.mpr hnAlg
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hnBot
    apply IntermediateField.mem_bot.mpr
    refine ⟨c, ?_⟩
    rw [← hn, ← hc]
    rfl
  let eA : S ≃ₐ[C] A := AlgEquiv.ofInjectiveField fS
  letI : FiniteDimensional C A := Module.Finite.equiv eA.toLinearEquiv
  haveI : IsGalois C A := IsGalois.of_algEquiv eA
  exact linearDisjoint_of_inf_eq_bot_of_finite_galois_left A B hInf

/-- If `C` is the exact constant field of `N`, adjoining any finite Galois
extension `S / C` by tensor product produces a field. -/
theorem exactConstantExtensionTensor_isField
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    IsField (S ⊗[C] N) := by
  exact IntermediateField.LinearDisjoint.isField_of_isAlgebraic'
    (exactConstantExtensionImages_linearDisjoint C N S hExact)
    (Or.inl (Algebra.IsAlgebraic.of_finite C S))

/-- The algebra structure on `S ⊗[C] N` induced by the copy of `N` in the
right tensor factor. -/
@[reducible] noncomputable def exactConstantExtensionAlgebra :
    Algebra N (S ⊗[C] N) :=
  (Algebra.TensorProduct.includeRight (R := C) (A := S) (B := N)).toAlgebra

/-- Commuting the tensor factors identifies the constant extension with the
usual scalar extension of `S` from `C` to `N`. -/
noncomputable def exactConstantExtensionLinearEquiv :
    letI := exactConstantExtensionAlgebra C N S
    N ⊗[C] S ≃ₗ[N] S ⊗[C] N := by
  letI := exactConstantExtensionAlgebra C N S
  let e := (Algebra.TensorProduct.comm C N S).toRingEquiv
  exact
    { toEquiv := e.toEquiv
      map_add' := map_add e
      map_smul' := by
        intro x z
        refine TensorProduct.induction_on z (by simp) (fun y s => ?_)
          (fun z w hz hw => ?_)
        · change e ((x * y) ⊗ₜ[C] s) =
            e (x ⊗ₜ[C] (1 : S)) * e (y ⊗ₜ[C] s)
          rw [← map_mul]
          simp
        · rw [smul_add]
          calc
            e (x • z + x • w) = e (x • z) + e (x • w) := map_add e _ _
            _ = x • e z + x • e w := congrArg₂ (· + ·) hz hw
            _ = x • e (z + w) := by rw [map_add, smul_add] }

omit [FiniteDimensional C S] [IsGalois C S] in
/-- A finite constant extension has the expected degree over the original
field. -/
theorem exactConstantExtension_finrank :
    letI := exactConstantExtensionAlgebra C N S
    Module.finrank N (S ⊗[C] N) = Module.finrank C S := by
  letI := exactConstantExtensionAlgebra C N S
  calc
    Module.finrank N (S ⊗[C] N) = Module.finrank N (N ⊗[C] S) :=
      (exactConstantExtensionLinearEquiv C N S).finrank_eq.symm
    _ = Module.finrank C S := Module.finrank_baseChange

end Constants

end

end BGS.HasseWeil
