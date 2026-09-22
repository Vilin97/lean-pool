/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FunctionFieldConstantExtension
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Galois.Basic

/-!
# Automorphisms of plane-curve constant extensions

For an algebraic extension `E / K`, this file transports every element of
`Gal(E/K)` to the scalar extension of a plane-curve function field.  The
transported automorphisms act on `E` in the prescribed way and fix the
original function field pointwise.

When `K` and `E` are finite, the scalar-extended function field has degree
`[E : K]`, is Galois over the original function field, and its full Galois
group is identified with `Gal(E/K)`.  The finite-field Frobenius therefore
acts with exact order `[E : K]` on the base-changed function field.

This file does not identify fixed points or rational places; those are the
next local-geometric layer.
-/

open scoped TensorProduct

namespace BGS.HasseWeil

noncomputable section

section Tensor

variable (K E L : Type*) [Field K] [Field E] [CommRing L]
  [Algebra K E] [Algebra K L]

noncomputable def tensorConstantAlgEquiv (σ : E ≃ₐ[K] E) :
    E ⊗[K] L ≃ₐ[K] E ⊗[K] L :=
  Algebra.TensorProduct.congr σ (AlgEquiv.refl : L ≃ₐ[K] L)

@[simp]
theorem tensorConstantAlgEquiv_tmul (σ : E ≃ₐ[K] E) (e : E) (x : L) :
    tensorConstantAlgEquiv K E L σ (e ⊗ₜ[K] x) = σ e ⊗ₜ[K] x := by
  rfl

@[simp]
theorem tensorConstantAlgEquiv_includeRight (σ : E ≃ₐ[K] E) (x : L) :
    tensorConstantAlgEquiv K E L σ
        (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := L) x) =
      Algebra.TensorProduct.includeRight (R := K) (A := E) (B := L) x := by
  simp [Algebra.TensorProduct.includeRight_apply]

noncomputable def tensorConstantAutHom :
    (E ≃ₐ[K] E) →* (E ⊗[K] L ≃ₐ[K] E ⊗[K] L) where
  toFun := tensorConstantAlgEquiv K E L
  map_one' := by
    apply AlgEquiv.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul e x => simp
    | add x y hx hy => simp [hx, hy]
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul e x => simp
    | add x y hx hy => simp [hx, hy]

theorem tensorConstantAutHom_injective [Nontrivial L] :
    Function.Injective (tensorConstantAutHom K E L) := by
  intro σ τ h
  ext e
  have h' := DFunLike.congr_fun h (e ⊗ₜ[K] (1 : L))
  change tensorConstantAlgEquiv K E L σ (e ⊗ₜ[K] (1 : L)) =
    tensorConstantAlgEquiv K E L τ (e ⊗ₜ[K] (1 : L)) at h'
  have hinc :
      Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := E) (B := L) (σ e) =
        Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := E) (B := L) (τ e) := by
    simpa [Algebra.TensorProduct.includeLeft_apply] using h'
  exact (Algebra.TensorProduct.includeLeft_injective
    (R := K) (S := K) (A := E) (B := L) (algebraMap K L).injective) hinc

end Tensor

section Plane

open BGS.CorvajaZannier

variable (K E : Type*) [Field K] [Field E] [Algebra K E]
  (f : MvPolynomial (Fin 2) K)
  (hf : Irreducible f)
  (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
  [Algebra.IsAlgebraic K E]

noncomputable def planeCurveConstantAlgEquiv (σ : E ≃ₐ[K] E) :
    PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f) ≃ₐ[K]
      PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f) := by
  let φ := (planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE).restrictScalars K
  exact φ.symm.trans ((tensorConstantAlgEquiv K E (PlaneCurveFunctionField f) σ).trans φ)

noncomputable def planeCurveFunctionFieldBaseChangeAlgHom :
    PlaneCurveFunctionField f →ₐ[K]
      PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f) :=
  ((planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE).restrictScalars K).toAlgHom.comp
    (Algebra.TensorProduct.includeRight
      (R := K) (A := E) (B := PlaneCurveFunctionField f))

@[simp]
theorem planeCurveConstantAlgEquiv_baseChange
    (σ : E ≃ₐ[K] E) (x : PlaneCurveFunctionField f) :
    planeCurveConstantAlgEquiv K E f hf hfE σ
        (planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE x) =
      planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE x := by
  simp [planeCurveConstantAlgEquiv, planeCurveFunctionFieldBaseChangeAlgHom]

@[simp]
theorem planeCurveConstantAlgEquiv_algebraMap
    (σ : E ≃ₐ[K] E) (e : E) :
    planeCurveConstantAlgEquiv K E f hf hfE σ
        (algebraMap E
          (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) e) =
      algebraMap E
        (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) (σ e) := by
  let φ := planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE
  change φ ((tensorConstantAlgEquiv K E (PlaneCurveFunctionField f) σ)
      (φ.symm (algebraMap E
        (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) e))) = _
  have hpre :
      φ.symm (algebraMap E
        (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) e) =
        e ⊗ₜ[K] (1 : PlaneCurveFunctionField f) := by
    simpa only [φ, AlgEquiv.symm_apply_apply] using congrArg φ.symm
      (planeCurveFunctionFieldBaseChangeAlgEquiv_tmul_one
        K E f hf hfE e).symm
  rw [hpre]
  rw [tensorConstantAlgEquiv_tmul]
  exact planeCurveFunctionFieldBaseChangeAlgEquiv_tmul_one K E f hf hfE (σ e)

noncomputable def planeCurveConstantAutHom :
    (E ≃ₐ[K] E) →*
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f) ≃ₐ[K]
        PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) where
  toFun := planeCurveConstantAlgEquiv K E f hf hfE
  map_one' := by
    apply AlgEquiv.ext
    intro x
    change (planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE)
      ((tensorConstantAlgEquiv K E (PlaneCurveFunctionField f) 1)
        ((planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE).symm x)) = x
    rw [show tensorConstantAlgEquiv K E (PlaneCurveFunctionField f) 1 = 1 from
      (tensorConstantAutHom K E (PlaneCurveFunctionField f)).map_one]
    simp
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    change (planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE)
      ((tensorConstantAlgEquiv K E (PlaneCurveFunctionField f) (σ * τ))
        ((planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE).symm x)) = _
    rw [show tensorConstantAlgEquiv K E (PlaneCurveFunctionField f) (σ * τ) =
        tensorConstantAlgEquiv K E (PlaneCurveFunctionField f) σ *
          tensorConstantAlgEquiv K E (PlaneCurveFunctionField f) τ from
      (tensorConstantAutHom K E (PlaneCurveFunctionField f)).map_mul σ τ]
    simp [planeCurveConstantAlgEquiv]

theorem planeCurveConstantAutHom_injective :
    Function.Injective (planeCurveConstantAutHom K E f hf hfE) := by
  let : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveCoordinateRing_isDomain hfE
  intro σ τ h
  ext e
  have h' := DFunLike.congr_fun h
    (algebraMap E
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) e)
  change planeCurveConstantAlgEquiv K E f hf hfE σ _ =
    planeCurveConstantAlgEquiv K E f hf hfE τ _ at h'
  rw [planeCurveConstantAlgEquiv_algebraMap,
    planeCurveConstantAlgEquiv_algebraMap] at h'
  exact (algebraMap E
    (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f))).injective h'

/-- The algebra structure on the base-changed function field induced by the
canonical embedding of the original function field. -/
@[reducible] noncomputable def planeCurveFunctionFieldBaseChangeAlgebra :
    Algebra (PlaneCurveFunctionField f)
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) :=
  (planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE).toAlgebra

/-- The base-changed function field has the expected dimension over the
original function field. -/
noncomputable def planeCurveFunctionFieldBaseChangeLinearEquiv :
    letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
    (PlaneCurveFunctionField f) ⊗[K] E ≃ₗ[PlaneCurveFunctionField f]
      PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveCoordinateRing_isDomain hfE
  letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
  let φ := planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE
  let ψ := (Algebra.TensorProduct.comm K (PlaneCurveFunctionField f) E).toRingEquiv.trans
    φ.toRingEquiv
  exact
    { toEquiv := ψ.toEquiv
      map_add' := map_add ψ
      map_smul' := by
        intro x z
        induction z using TensorProduct.inductionOn with
        | tmul y e =>
            change φ (e ⊗ₜ[K] (x * y)) =
              φ (1 ⊗ₜ[K] x) * φ (e ⊗ₜ[K] y)
            rw [← map_mul]
            simp
        | add z w hz hw =>
            rw [smul_add]
            calc
              ψ (x • z + x • w) = ψ (x • z) + ψ (x • w) := map_add ψ _ _
              _ = x • ψ z + x • ψ w := congrArg₂ (· + ·) hz hw
              _ = x • ψ (z + w) := by rw [map_add, smul_add] }

theorem planeCurveFunctionFieldBaseChange_finrank :
    letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
    Module.finrank (PlaneCurveFunctionField f)
        (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) =
      Module.finrank K E := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveCoordinateRing_isDomain hfE
  let := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
  calc
    Module.finrank (PlaneCurveFunctionField f)
        (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) =
        Module.finrank (PlaneCurveFunctionField f)
          ((PlaneCurveFunctionField f) ⊗[K] E) :=
      (planeCurveFunctionFieldBaseChangeLinearEquiv K E f hf hfE).finrank_eq.symm
    _ = Module.finrank K E := Module.finrank_baseChange

/-- A constant-field automorphism, viewed as an automorphism over the
embedded original function field. -/
noncomputable def planeCurveConstantAlgEquivOverBase (σ : E ≃ₐ[K] E) :
    letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
    PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f) ≃ₐ[
        PlaneCurveFunctionField f]
      PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f) := by
  letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
  exact
    { planeCurveConstantAlgEquiv K E f hf hfE σ with
      commutes' := fun x => by
        change planeCurveConstantAlgEquiv K E f hf hfE σ
            (planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE x) =
          planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE x
        exact planeCurveConstantAlgEquiv_baseChange K E f hf hfE σ x }

noncomputable def planeCurveConstantAutOverBaseHom :
    letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
    (E ≃ₐ[K] E) →*
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f) ≃ₐ[
          PlaneCurveFunctionField f]
        PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) := by
  letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
  exact
    { toFun := planeCurveConstantAlgEquivOverBase K E f hf hfE
      map_one' := by
        apply AlgEquiv.ext
        intro x
        exact DFunLike.congr_fun
          (planeCurveConstantAutHom K E f hf hfE).map_one x
      map_mul' := by
        intro σ τ
        apply AlgEquiv.ext
        intro x
        exact DFunLike.congr_fun
          ((planeCurveConstantAutHom K E f hf hfE).map_mul σ τ) x }

theorem planeCurveConstantAutOverBaseHom_injective :
    letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
    Function.Injective (planeCurveConstantAutOverBaseHom K E f hf hfE) := by
  let := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
  intro σ τ h
  apply planeCurveConstantAutHom_injective K E f hf hfE
  apply AlgEquiv.ext
  intro x
  exact DFunLike.congr_fun h x

theorem planeCurveFunctionFieldBaseChange_isGalois
    [Fintype K] [Finite E] :
    letI : IsDomain (PlaneCurveCoordinateRing f) :=
      planeCurveCoordinateRing_isDomain hf
    letI : IsDomain (PlaneCurveCoordinateRing
        (MvPolynomial.map (algebraMap K E) f)) :=
      planeCurveCoordinateRing_isDomain hfE
    letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
    IsGalois (PlaneCurveFunctionField f)
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveCoordinateRing_isDomain hfE
  let := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
  let e := planeCurveFunctionFieldBaseChangeLinearEquiv K E f hf hfE
  let : Module.Finite (PlaneCurveFunctionField f)
      ((PlaneCurveFunctionField f) ⊗[K] E) :=
    Module.Finite.base_change K (PlaneCurveFunctionField f) E
  let : Module.Finite (PlaneCurveFunctionField f)
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) :=
    Module.Finite.equiv e
  apply IsGalois.of_card_aut_eq_finrank
  apply Nat.le_antisymm
  · calc
      Nat.card (PlaneCurveFunctionField
          (MvPolynomial.map (algebraMap K E) f) ≃ₐ[PlaneCurveFunctionField f]
            PlaneCurveFunctionField
              (MvPolynomial.map (algebraMap K E) f)) =
          Nat.card (PlaneCurveFunctionField
            (MvPolynomial.map (algebraMap K E) f) →ₐ[PlaneCurveFunctionField f]
              PlaneCurveFunctionField
                (MvPolynomial.map (algebraMap K E) f)) :=
        Nat.card_congr (algEquivEquivAlgHom
          (PlaneCurveFunctionField f)
          (PlaneCurveFunctionField
            (MvPolynomial.map (algebraMap K E) f)))
      _ ≤ Module.finrank (PlaneCurveFunctionField f)
          (PlaneCurveFunctionField
            (MvPolynomial.map (algebraMap K E) f)) :=
        card_algHom_le_finrank _ _ _
  · rw [planeCurveFunctionFieldBaseChange_finrank K E f hf hfE,
      ← IsGalois.card_aut_eq_finrank K E]
    exact Nat.card_le_card_of_injective
      (planeCurveConstantAutOverBaseHom K E f hf hfE)
      (planeCurveConstantAutOverBaseHom_injective K E f hf hfE)

/-- The Galois group of the constant extension is exactly the Galois group of
the enlarged constants. -/
noncomputable def planeCurveConstantAutOverBaseMulEquiv
    [Fintype K] [Finite E] :
    letI : IsDomain (PlaneCurveCoordinateRing f) :=
      planeCurveCoordinateRing_isDomain hf
    letI : IsDomain (PlaneCurveCoordinateRing
        (MvPolynomial.map (algebraMap K E) f)) :=
      planeCurveCoordinateRing_isDomain hfE
    letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
    (E ≃ₐ[K] E) ≃*
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f) ≃ₐ[
          PlaneCurveFunctionField f]
        PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveCoordinateRing_isDomain hfE
  letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
  let e := planeCurveFunctionFieldBaseChangeLinearEquiv K E f hf hfE
  letI : Module.Finite (PlaneCurveFunctionField f)
      ((PlaneCurveFunctionField f) ⊗[K] E) :=
    Module.Finite.base_change K (PlaneCurveFunctionField f) E
  letI : Module.Finite (PlaneCurveFunctionField f)
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) :=
    Module.Finite.equiv e
  letI : IsGalois (PlaneCurveFunctionField f)
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveFunctionFieldBaseChange_isGalois K E f hf hfE
  let h := planeCurveConstantAutOverBaseHom K E f hf hfE
  let hinj := planeCurveConstantAutOverBaseHom_injective K E f hf hfE
  apply MulEquiv.ofBijective h
  apply hinj.bijective_of_nat_card_le
  rw [IsGalois.card_aut_eq_finrank,
    planeCurveFunctionFieldBaseChange_finrank K E f hf hfE,
    IsGalois.card_aut_eq_finrank K E]

section Frobenius

variable [Fintype K]

/-- Frobenius on the enlarged constant field, transported to the
base-changed plane-curve function field. -/
noncomputable def planeCurveConstantFrobeniusAlgEquiv :
    PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f) ≃ₐ[K]
      PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f) :=
  planeCurveConstantAlgEquiv K E f hf hfE
    (FiniteField.frobeniusAlgEquivOfAlgebraic K E)

@[simp]
theorem planeCurveConstantFrobeniusAlgEquiv_algebraMap (e : E) :
    planeCurveConstantFrobeniusAlgEquiv K E f hf hfE
        (algebraMap E
          (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) e) =
      algebraMap E
        (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f))
        (e ^ Fintype.card K) := by
  rw [planeCurveConstantFrobeniusAlgEquiv,
    planeCurveConstantAlgEquiv_algebraMap]
  rfl

@[simp]
theorem planeCurveConstantFrobeniusAlgEquiv_baseChange
    (x : PlaneCurveFunctionField f) :
    planeCurveConstantFrobeniusAlgEquiv K E f hf hfE
        (planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE x) =
      planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE x := by
  exact planeCurveConstantAlgEquiv_baseChange K E f hf hfE _ x

variable [Finite E]

theorem orderOf_planeCurveConstantFrobeniusAlgEquiv :
    orderOf (planeCurveConstantFrobeniusAlgEquiv K E f hf hfE) =
      Module.finrank K E := by
  change orderOf ((planeCurveConstantAutHom K E f hf hfE)
    (FiniteField.frobeniusAlgEquivOfAlgebraic K E)) = _
  rw [orderOf_injective (planeCurveConstantAutHom K E f hf hfE)
    (planeCurveConstantAutHom_injective K E f hf hfE)]
  exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic K E

theorem natCard_zpowers_planeCurveConstantFrobeniusAlgEquiv :
    Nat.card (Subgroup.zpowers
      (planeCurveConstantFrobeniusAlgEquiv K E f hf hfE)) =
      Module.finrank K E := by
  rw [Nat.card_zpowers, orderOf_planeCurveConstantFrobeniusAlgEquiv]

end Frobenius

end Plane

end

end BGS.HasseWeil
