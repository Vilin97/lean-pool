/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Geometrically integral algebras

A commutative algebra over a field is geometrically integral when its scalar extension to every
field in the ambient universe is a domain. This algebraic formulation is the one used by the
filtered-substitution argument: an irreducible polynomial over the base field remains prime after
extending its coefficients to a geometrically integral algebra.

The proof embeds the scalar extension by the irreducible polynomial's quotient domain into the
scalar extension by its fraction field. Polynomial and quotient tensor equivalences then identify
that tensor product with the required polynomial quotient.

The definition quantifies over the fields of the universe `max u v` of `B ⊗[k] L`. A `Prop`
cannot quantify over universes, and the universe-free characterization, that `B ⊗[k] k̄` is a
domain for an algebraic closure `k̄`, is a theorem of descent that is not in Mathlib; the
scheme-theoretic `AlgebraicGeometry.GeometricallyIntegral` is likewise fixed to one universe. For
the paper's quotient `P̂/I`, the statement in every universe is proved separately, by putting a
lowering derivation on `E ⊗_K P̂` rather than from this definition.
-/

open scoped TensorProduct

universe u v w

namespace Algebra

public noncomputable section

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/-- A commutative algebra is geometrically integral when every scalar extension to a field in the
ambient universe is a domain. -/
def IsGeometricallyIntegral (k : Type u) (B : Type v)
    [Field k] [CommRing B] [Algebra k B] : Prop :=
  ∀ (K : Type (max u v)) [Field K] [Algebra k K], IsDomain (B ⊗[k] K)

/-- A geometrically integral algebra is a domain. -/
theorem IsGeometricallyIntegral.isDomain
    {k : Type u} [Field k] {B : Type v} [CommRing B] [Algebra k B]
    (hB : IsGeometricallyIntegral k B) : IsDomain B := by
  haveI : IsDomain (B ⊗[k] ULift.{max u v} k) :=
    hB (ULift.{max u v} k)
  let e : (B ⊗[k] ULift.{max u v} k) ≃ₐ[k] (B ⊗[k] k) :=
    Algebra.TensorProduct.congr AlgEquiv.refl ULift.algEquiv
  haveI : IsDomain (B ⊗[k] k) := e.symm.toMulEquiv.isDomain _
  exact (Algebra.TensorProduct.rid k k B).symm.toMulEquiv.isDomain _

section BaseChange

/-- Geometric integrality transports along an algebra equivalence. -/
theorem IsGeometricallyIntegral.of_algEquiv {k : Type u} [Field k] {A B : Type v}
    [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (hA : IsGeometricallyIntegral k A) (e : A ≃ₐ[k] B) :
    IsGeometricallyIntegral k B := fun M _ _ ↦ by
  haveI : IsDomain (A ⊗[k] M) := hA M
  exact (Algebra.TensorProduct.congr e
    (AlgEquiv.refl (R := k) (A₁ := M))).symm.toMulEquiv.isDomain _

end BaseChange

variable {k : Type u} {σ : Type (max u v)} {B : Type v}
  [Field k] [CommRing B] [Algebra k B]

/-- The defining field-extension criterion for geometric integrality. -/
theorem isGeometricallyIntegral_iff :
    IsGeometricallyIntegral k B ↔
      ∀ (K : Type (max u v)) [Field K] [Algebra k K], IsDomain (B ⊗[k] K) :=
  Iff.rfl

/-- An algebra over a field whose tensor products with the fields of some universe are domains
remains a domain after tensoring with any domain of that universe: the tensor product embeds, by
flatness, into the tensor product with the fraction field. -/
theorem isDomain_tensor_of_isDomain_of_forall_field {k : Type u} [Field k] {B : Type v}
    [CommRing B] [Algebra k B]
    (hB : ∀ (L : Type w) [Field L] [Algebra k L], IsDomain (B ⊗[k] L))
    (D : Type w) [CommRing D] [IsDomain D] [Algebra k D] : IsDomain (B ⊗[k] D) := by
  let L := FractionRing D
  letI : Algebra k L := Algebra.ofModule
    (fun r x y ↦ smul_mul_assoc r x y)
    (fun r x y ↦ mul_smul_comm r x y)
  letI : IsScalarTower k D L := inferInstance
  letI : IsDomain (B ⊗[k] L) := hB L
  let ι : D →ₐ[k] L := (IsScalarTower.toAlgHom k D L).restrictScalars k
  let Φ : B ⊗[k] D →ₐ[k] B ⊗[k] L :=
    Algebra.TensorProduct.map (AlgHom.id k B) ι
  have hι : Function.Injective ι := IsFractionRing.injective D L
  have hΦ : Function.Injective Φ := by
    have h := TensorProduct.map_injective_of_flat_flat
      (LinearMap.id (R := k) (M := B))
      ((IsScalarTower.toAlgHom k D L).restrictScalars k).toLinearMap
      Function.injective_id hι
    change Function.Injective Φ.toLinearMap
    dsimp only [Φ]
    rw [Algebra.TensorProduct.toLinearMap_map,
      TensorProduct.AlgebraTensorModule.map_eq]
    exact h
  exact hΦ.isDomain Φ.toRingHom

/-- A geometrically integral algebra remains a domain after tensoring with any domain of the
ambient universe over the base field. -/
theorem IsGeometricallyIntegral.isDomain_tensor_of_isDomain
    (hB : IsGeometricallyIntegral k B) (D : Type (max u v)) [CommRing D] [IsDomain D]
    [Algebra k D] : IsDomain (B ⊗[k] D) :=
  isDomain_tensor_of_isDomain_of_forall_field (fun L _ _ ↦ hB L) D

/-- An irreducible polynomial over the base field generates a prime ideal after extending
coefficients to a geometrically integral algebra. -/
theorem IsGeometricallyIntegral.isDomain_mvPolynomial_quotient_span_map
    (hB : IsGeometricallyIntegral k B) {F : MvPolynomial σ k}
    (hF : Irreducible F) :
    IsDomain
      (MvPolynomial σ B ⧸
        Ideal.span {MvPolynomial.map (algebraMap k B) F}) := by
  let I : Ideal (MvPolynomial σ k) := Ideal.span {F}
  have hFPrime : Prime F :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hF
  have hIPrime : I.IsPrime := by
    exact (Ideal.span_singleton_prime hFPrime.ne_zero).mpr hFPrime
  letI : I.IsPrime := hIPrime
  let D := MvPolynomial σ k ⧸ I
  letI : IsDomain (B ⊗[k] D) := hB.isDomain_tensor_of_isDomain D
  let ePoly : B ⊗[k] MvPolynomial σ k ≃ₐ[B] MvPolynomial σ B :=
    MvPolynomial.algebraTensorAlgEquiv k B
  let rightInclusion : MvPolynomial σ k →ₐ[k] B ⊗[k] MvPolynomial σ k :=
    Algebra.TensorProduct.includeRight
  let J : Ideal (B ⊗[k] MvPolynomial σ k) := I.map rightInclusion
  let eQuot :=
    Algebra.TensorProduct.tensorQuotientEquiv
      (R := k) B (MvPolynomial σ k) B I
  have hIdeal :
      Ideal.map ePoly.toRingEquiv J =
        Ideal.span {MvPolynomial.map (algebraMap k B) F} := by
    dsimp only [J, I]
    change Ideal.map ePoly.toRingEquiv.toRingHom
        (Ideal.map rightInclusion.toRingHom (Ideal.span {F})) = _
    rw [Ideal.map_map rightInclusion.toRingHom ePoly.toRingEquiv.toRingHom]
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change ePoly (rightInclusion F) = MvPolynomial.map (algebraMap k B) F
    simp [rightInclusion, ePoly]
  letI : IsDomain
      ((B ⊗[k] MvPolynomial σ k) ⧸ J) :=
    eQuot.symm.toMulEquiv.isDomain
  let eMap :
      (B ⊗[k] MvPolynomial σ k) ⧸ J ≃+*
        MvPolynomial σ B ⧸ Ideal.span {MvPolynomial.map (algebraMap k B) F} :=
    Ideal.quotientEquiv _ _ ePoly.toRingEquiv hIdeal.symm
  exact eMap.symm.toMulEquiv.isDomain

private def quotientSpanEquivOfEq {A C : Type*} [CommRing A] [CommRing C]
    (e : A ≃+* C) {x : A} {y : C} (hxy : e x = y) :
    A ⧸ Ideal.span {x} ≃+* C ⧸ Ideal.span {y} :=
  Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {y}) e <| by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {y} = Ideal.span {e x}
    rw [hxy]

/-- The irreducible base-change quotient is a domain for a finite variable type, independently
of the universes of the base field and coefficient algebra. -/
theorem IsGeometricallyIntegral.isDomain_fin_mvPolynomial_quotient_span_map
    (hB : IsGeometricallyIntegral k B) {n : ℕ} {F : MvPolynomial (Fin n) k}
    (hF : Irreducible F) :
    IsDomain
      (MvPolynomial (Fin n) B ⧸
        Ideal.span {MvPolynomial.map (algebraMap k B) F}) := by
  let τ := ULift.{max u v, 0} (Fin n)
  let liftEquiv : Fin n ≃ τ := Equiv.ulift.symm
  let F' : MvPolynomial τ k := MvPolynomial.renameEquiv k liftEquiv F
  have hF' : Irreducible F' := by
    exact hF.map (MvPolynomial.renameEquiv k liftEquiv).toMulEquiv
  letI : IsDomain
      (MvPolynomial τ B ⧸
        Ideal.span {MvPolynomial.map (algebraMap k B) F'}) :=
    hB.isDomain_mvPolynomial_quotient_span_map hF'
  let e : MvPolynomial (Fin n) B ≃+* MvPolynomial τ B :=
    (MvPolynomial.renameEquiv B liftEquiv).toRingEquiv
  have hmap :
      e (MvPolynomial.map (algebraMap k B) F) =
        MvPolynomial.map (algebraMap k B) F' := by
    change MvPolynomial.rename liftEquiv
        (MvPolynomial.map (algebraMap k B) F) =
      MvPolynomial.map (algebraMap k B)
        (MvPolynomial.rename liftEquiv F)
    exact MvPolynomial.map_rename (algebraMap k B) liftEquiv F |>.symm
  let eQuot := quotientSpanEquivOfEq e hmap
  exact eQuot.isDomain _

end

end Algebra
