/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedProduct
/-!
# Galois action on the restricted local product

The Galois action on `𝔸_K ⊗[K] L` commutes with evaluation at every
place.  Consequently the exact restricted-product equivalence for
relative ideles is equivariant, and the transported action is the
coordinatewise tensor-conjugation action.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v w

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The natural action on relative ideles, upgraded to an action by
group automorphisms for the restricted-product comparison. -/
@[reducible]
noncomputable def relativeIdeleRestrictedMulDistribMulAction :
    MulDistribMulAction
      (L ≃ₐ[K] L) (RelativeIdeleGroup K L) where
  __ := RelativeIdeleGroup.relativeIdeleMulAction K L
  smul_one σ :=
    map_one
      (RelativeIdeleGroup.conjugationIdele K L σ)
  smul_mul σ a b :=
    map_mul
      (RelativeIdeleGroup.conjugationIdele K L σ) a b

section ScalarTensor

variable
    {A : Type w} [CommRing A] [Algebra K A]

/-- Conjugation on the second factor of an arbitrary scalar extension
`A ⊗[K] L`. -/
noncomputable def scalarTensorConjugation
    (σ : L ≃ₐ[K] L) :
    A ⊗[K] L ≃ₐ[A] A ⊗[K] L := by
  let f : A ⊗[K] L →ₐ[A] A ⊗[K] L :=
    Algebra.TensorProduct.map
      (AlgHom.id A A) σ.toAlgHom
  let g : A ⊗[K] L →ₐ[A] A ⊗[K] L :=
    Algebra.TensorProduct.map
      (AlgHom.id A A) σ.symm.toAlgHom
  exact AlgEquiv.ofAlgHom f g
    (by ext x; simp [f, g])
    (by ext x; simp [f, g])

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
@[simp]
theorem scalarTensorConjugation_tmul
    (σ : L ≃ₐ[K] L) (a : A) (x : L) :
    scalarTensorConjugation
        (K := K) (L := L) (A := A) σ
        (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] σ x :=
  rfl

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
theorem scalarTensorConjugation_one
    (z : A ⊗[K] L) :
    scalarTensorConjugation
        (K := K) (L := L) (A := A)
        (1 : L ≃ₐ[K] L) z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp
  | add x y hx hy => simp [hx, hy]

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
theorem scalarTensorConjugation_mul
    (σ τ : L ≃ₐ[K] L)
    (z : A ⊗[K] L) :
    scalarTensorConjugation
        (K := K) (L := L) (A := A) (σ * τ) z =
      scalarTensorConjugation
        (K := K) (L := L) (A := A) σ
        (scalarTensorConjugation
          (K := K) (L := L) (A := A) τ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp
  | add x y hx hy => simp [hx, hy]

/-- The action by tensor conjugation on local tensor units. -/
@[reducible]
noncomputable def scalarTensorUnitsAction :
    MulDistribMulAction
      (L ≃ₐ[K] L) (A ⊗[K] L)ˣ where
  smul σ z :=
    Units.mapEquiv
      (scalarTensorConjugation
        (K := K) (L := L) (A := A) σ).toMulEquiv z
  one_smul z := by
    apply Units.ext
    exact scalarTensorConjugation_one
      (K := K) (L := L) (A := A)
      (z : A ⊗[K] L)
  mul_smul σ τ z := by
    apply Units.ext
    exact scalarTensorConjugation_mul
      (K := K) (L := L) (A := A)
      σ τ (z : A ⊗[K] L)
  smul_one σ := by
    apply Units.ext
    exact
      (scalarTensorConjugation
        (K := K) (L := L) (A := A) σ).map_one
  smul_mul σ x y := by
    apply Units.ext
    exact
      (scalarTensorConjugation
        (K := K) (L := L) (A := A) σ).map_mul
        (x : A ⊗[K] L) (y : A ⊗[K] L)

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
@[simp]
theorem scalarTensorUnitsAction_coe
    (σ : L ≃ₐ[K] L)
    (z : (A ⊗[K] L)ˣ) :
    letI := scalarTensorUnitsAction
      (K := K) (L := L) (A := A)
    ((σ • z : (A ⊗[K] L)ˣ) :
        A ⊗[K] L) =
      scalarTensorConjugation
        (K := K) (L := L) (A := A) σ
        (z : A ⊗[K] L) :=
  rfl

end ScalarTensor

omit [NumberField L] [FiniteDimensional K L] in
/-- Infinite-place evaluation commutes with Galois conjugation. -/
theorem relativeAdeleInfiniteComponent_conjugation
    (w : InfinitePlace K)
    (σ : L ≃ₐ[K] L)
    (z : RelativeAdeleRing K L) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w
        (RelativeIdeleGroup.conjugation K L σ z) =
      scalarTensorConjugation
        (K := K) (L := L)
        (A := w.Completion) σ
        (relativeAdeleInfiniteComponent
          (K := K) (L := L) w z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp [hx, hy]

omit [NumberField L] [FiniteDimensional K L] in
/-- Finite-place evaluation commutes with Galois conjugation. -/
theorem relativeAdeleFiniteComponent_conjugation
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (z : RelativeAdeleRing K L) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w
        (RelativeIdeleGroup.conjugation K L σ z) =
      scalarTensorConjugation
        (K := K) (L := L)
        (A := w.adicCompletion K) σ
        (relativeAdeleFiniteComponent
          (K := K) (L := L) w z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp [hx, hy]

omit [NumberField L] [FiniteDimensional K L] in
/-- The infinite local unit component map is equivariant. -/
theorem RelativeIdeleGroup.infiniteComponent_smul
    (w : InfinitePlace K)
    (σ : L ≃ₐ[K] L)
    (z : RelativeIdeleGroup K L) :
    letI := scalarTensorUnitsAction
      (K := K) (L := L) (A := w.Completion)
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w (σ • z) =
      σ • RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w z := by
  let _ := scalarTensorUnitsAction
    (K := K) (L := L) (A := w.Completion)
  apply Units.ext
  exact relativeAdeleInfiniteComponent_conjugation
    (K := K) (L := L) w σ
      (z : RelativeAdeleRing K L)

omit [NumberField L] [FiniteDimensional K L] in
/-- The finite local unit component map is equivariant. -/
theorem RelativeIdeleGroup.finiteComponent_smul
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (z : RelativeIdeleGroup K L) :
    letI := scalarTensorUnitsAction
      (K := K) (L := L)
      (A := w.adicCompletion K)
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w (σ • z) =
      σ • RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z := by
  let _ := scalarTensorUnitsAction
    (K := K) (L := L)
    (A := w.adicCompletion K)
  apply Units.ext
  exact relativeAdeleFiniteComponent_conjugation
    (K := K) (L := L) w σ
      (z : RelativeAdeleRing K L)

/-- The Galois action on the restricted local product transported
through the exact relative-idele equivalence. -/
@[reducible]
noncomputable def relativeLocalIdeleDataMulDistribMulAction :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (RelativeLocalIdeleData
        (K := K) (L := L)) := by
  letI : MulDistribMulAction
      (L ≃ₐ[K] L) (RelativeIdeleGroup K L) :=
    relativeIdeleRestrictedMulDistribMulAction
      (K := K) (L := L)
  let e :=
    relativeIdeleMulEquivLocalData
      (K := K) (L := L)
  exact
    { smul := fun σ a => e (σ • e.symm a)
      one_smul := by
        intro a
        change e (1 • e.symm a) = a
        rw [one_smul, e.apply_symm_apply]
      mul_smul := by
        intro σ τ a
        change
          e ((σ * τ) • e.symm a) =
            e (σ • e.symm (e (τ • e.symm a)))
        rw [e.symm_apply_apply, mul_smul]
      smul_one := by
        intro σ
        change e (σ • e.symm 1) = 1
        rw [e.symm.map_one, smul_one, e.map_one]
      smul_mul := by
        intro σ a b
        change
          e (σ • e.symm (a * b)) =
            e (σ • e.symm a) *
              e (σ • e.symm b)
        rw [e.symm.map_mul,
          MulDistribMulAction.smul_mul, e.map_mul] }

omit [NumberField L] in
/-- Equivariance of the exact restricted-product equivalence. -/
theorem relativeIdeleMulEquivLocalData_smul
    (σ : L ≃ₐ[K] L)
    (z : RelativeIdeleGroup K L) :
    letI :=
      relativeIdeleRestrictedMulDistribMulAction
        (K := K) (L := L)
    letI :=
      relativeLocalIdeleDataMulDistribMulAction
        (K := K) (L := L)
    relativeIdeleMulEquivLocalData
        (K := K) (L := L) (σ • z) =
      σ • relativeIdeleMulEquivLocalData
        (K := K) (L := L) z := by
  let _ :=
    relativeIdeleRestrictedMulDistribMulAction
      (K := K) (L := L)
  let _ :=
    relativeLocalIdeleDataMulDistribMulAction
      (K := K) (L := L)
  change
    relativeIdeleMulEquivLocalData
        (K := K) (L := L) (σ • z) =
      relativeIdeleMulEquivLocalData
        (K := K) (L := L)
        (σ •
          (relativeIdeleMulEquivLocalData
            (K := K) (L := L)).symm
            (relativeIdeleMulEquivLocalData
              (K := K) (L := L) z))
  rw [(relativeIdeleMulEquivLocalData
    (K := K) (L := L)).symm_apply_apply]

omit [NumberField L] in
/-- The transported action is coordinatewise tensor conjugation at
infinite places. -/
theorem RelativeLocalIdeleData.infinite_smul
    (σ : L ≃ₐ[K] L)
    (a : RelativeLocalIdeleData (K := K) (L := L))
    (w : InfinitePlace K) :
    letI :=
      relativeIdeleRestrictedMulDistribMulAction
        (K := K) (L := L)
    letI :=
      relativeLocalIdeleDataMulDistribMulAction
        (K := K) (L := L)
    letI := scalarTensorUnitsAction
      (K := K) (L := L) (A := w.Completion)
    (σ • a).infinite w =
      σ • a.infinite w := by
  let _ :=
    relativeIdeleRestrictedMulDistribMulAction
      (K := K) (L := L)
  let _ :=
    relativeLocalIdeleDataMulDistribMulAction
      (K := K) (L := L)
  let _ := scalarTensorUnitsAction
    (K := K) (L := L) (A := w.Completion)
  change
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w
        (σ • relativeIdeleOfLocalData
          (K := K) (L := L) a) =
      σ • a.infinite w
  rw [RelativeIdeleGroup.infiniteComponent_smul,
    relativeIdeleOfLocalData_infiniteComponent]

omit [NumberField L] in
/-- The transported action is coordinatewise tensor conjugation at
finite places. -/
theorem RelativeLocalIdeleData.finite_smul
    (σ : L ≃ₐ[K] L)
    (a : RelativeLocalIdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    letI :=
      relativeIdeleRestrictedMulDistribMulAction
        (K := K) (L := L)
    letI :=
      relativeLocalIdeleDataMulDistribMulAction
        (K := K) (L := L)
    letI := scalarTensorUnitsAction
      (K := K) (L := L)
      (A := w.adicCompletion K)
    (σ • a).finite w =
      σ • a.finite w := by
  let _ :=
    relativeIdeleRestrictedMulDistribMulAction
      (K := K) (L := L)
  let _ :=
    relativeLocalIdeleDataMulDistribMulAction
      (K := K) (L := L)
  let _ := scalarTensorUnitsAction
    (K := K) (L := L)
    (A := w.adicCompletion K)
  change
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w
        (σ • relativeIdeleOfLocalData
          (K := K) (L := L) a) =
      σ • a.finite w
  rw [RelativeIdeleGroup.finiteComponent_smul,
    relativeIdeleOfLocalData_finiteComponent]
