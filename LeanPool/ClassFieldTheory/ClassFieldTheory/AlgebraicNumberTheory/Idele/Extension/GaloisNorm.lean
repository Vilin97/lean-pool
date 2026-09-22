/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormProperties
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
/-!
# The Galois product formula for the relative idele norm

This file proves that, in the tensor-product presentation
`𝔸_L = 𝔸_K ⊗_K L`, extension of the determinant norm back to `𝔸_L`
is the product of all Galois conjugates.
-/

open scoped BigOperators TensorProduct
open NumberField

noncomputable section


namespace RelativeIdeleGroup

universe u v w

variable
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- The determinant norm as a homogeneous polynomial in the coordinates
of a basis.  Keeping this polynomial over the ground field is what makes
the Galois product formula stable under arbitrary scalar extension. -/
def normPolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) : MvPolynomial ι K :=
  (-1 : MvPolynomial ι K) ^ Module.finrank K L *
    ((Algebra.lmul K L).toLinearMap.polyCharpoly b).coeff 0

@[simp]
theorem eval_normPolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (x : L) :
    MvPolynomial.eval (b.repr x) (normPolynomial b) =
      Algebra.norm K x := by
  rw [normPolynomial, map_mul, map_pow, map_neg, map_one,
    LinearMap.polyCharpoly_coeff_eval]
  exact ((Algebra.norm_apply K x).trans
    (LinearMap.det_eq_sign_charpoly_coeff
      ((Algebra.lmul K L) x))).symm

/-- The linear polynomial whose value at the coordinates of `x` is the
`σ`-conjugate of `x`. -/
def conjugatePolynomial
    {ι : Type w} [Fintype ι]
    (b : Module.Basis ι K L) (σ : L ≃ₐ[K] L) :
    MvPolynomial ι L :=
  ∑ i, MvPolynomial.X i * MvPolynomial.C (σ (b i))

omit [FiniteDimensional K L] in
@[simp]
theorem eval_conjugatePolynomial
    {ι : Type w} [Fintype ι]
    (b : Module.Basis ι K L) (σ : L ≃ₐ[K] L) (x : L) :
    MvPolynomial.eval
        (fun i ↦ algebraMap K L (b.repr x i))
        (conjugatePolynomial b σ) =
      σ x := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  rw [conjugatePolynomial, map_sum]
  simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
  calc
    ∑ i, algebraMap K L (b.repr x i) * σ (b i) =
        ∑ i, σ ((b.repr x i) • b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Algebra.smul_def]
    _ = σ (∑ i, (b.repr x i) • b i) := by
      rw [map_sum]
    _ = σ x := by rw [b.sum_repr]

/-- The product of the universal conjugates, written as a polynomial over
the splitting field. -/
def galoisProductPolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) :
    MvPolynomial ι L :=
  ∏ σ : L ≃ₐ[K] L, conjugatePolynomial b σ

@[simp]
theorem eval_galoisProductPolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (x : L) :
    MvPolynomial.eval
        (fun i ↦ algebraMap K L (b.repr x i))
        (galoisProductPolynomial b) =
      ∏ σ : L ≃ₐ[K] L, σ x := by
  simp [galoisProductPolynomial]

/-- The universal determinant norm polynomial becomes the product of the
universal Galois conjugates after extending its coefficients to `L`. -/
theorem map_normPolynomial_eq_galoisProductPolynomial
    [IsGalois K L] [Infinite K]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) :
    MvPolynomial.map (algebraMap K L) (normPolynomial b) =
      galoisProductPolynomial b := by
  apply MvPolynomial.funext_set
    (fun _ : ι ↦ Set.range (algebraMap K L))
  · intro i
    exact Set.infinite_range_of_injective
      (algebraMap K L).injective
  · intro c hc
    choose d hd using fun i ↦ hc i (Set.mem_univ i)
    let x : L :=
      b.repr.symm (Finsupp.equivFunOnFinite.symm d)
    have hcoords :
        c = fun i ↦ algebraMap K L (b.repr x i) := by
      funext i
      calc
        c i = algebraMap K L (d i) := (hd i).symm
        _ = algebraMap K L (b.repr x i) := by simp [x]
    rw [hcoords, eval_galoisProductPolynomial]
    rw [MvPolynomial.eval_map]
    change MvPolynomial.eval₂ (algebraMap K L)
        ((algebraMap K L) ∘ fun i ↦ b.repr x i)
        (normPolynomial b) =
      _
    rw [← MvPolynomial.eval₂_comp]
    rw [eval_normPolynomial]
    exact Algebra.norm_eq_prod_automorphisms K x

omit [FiniteDimensional K L] in
/-- Base change carries the regular representation of `L/K` to the regular
representation of `A ⊗[K] L` over `A`. -/
theorem baseChangedLmul_eq
    (A : Type w) [CommRing A] [Algebra K A] :
    LinearMap.tensorProduct K A L L ∘ₗ
        (Algebra.lmul K L).toLinearMap.baseChange A =
      (Algebra.lmul A (A ⊗[K] L)).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
      rw [map_add, map_add, hz₁, hz₂]
  | tmul a x =>
      apply LinearMap.ext
      intro y
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ hy₁ hy₂ =>
          rw [map_add, map_add, hy₁, hy₂]
      | tmul b t =>
          simp [LinearMap.tensorProduct,
            Algebra.TensorProduct.tmul_mul_tmul,
            Algebra.smul_def, mul_comm]

/-- Evaluation of the universal norm polynomial after arbitrary scalar
extension is the determinant norm on the scalar-extended algebra. -/
theorem eval₂_normPolynomial_baseChange
    (A : Type*) [CommRing A] [Algebra K A] [Nontrivial A]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (z : A ⊗[K] L) :
    MvPolynomial.eval₂ (algebraMap K A)
        ((Algebra.TensorProduct.basis A b).repr z)
        (normPolynomial b) =
      Algebra.norm A z := by
  have hcoeff := congrArg
      (fun p : Polynomial (MvPolynomial ι A) ↦ p.coeff 0)
      (LinearMap.polyCharpoly_baseChange
        (Algebra.lmul K L).toLinearMap b A)
  rw [Polynomial.coeff_map] at hcoeff
  rw [normPolynomial, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_neg,
    MvPolynomial.eval₂_one]
  have heval :=
    MvPolynomial.eval₂_eq_eval_map
      (algebraMap K A)
      ((Algebra.TensorProduct.basis A b).repr z)
      (((Algebra.lmul K L).toLinearMap.polyCharpoly b).coeff 0)
  rw [heval, ← hcoeff]
  rw [LinearMap.polyCharpoly_coeff_eval]
  rw [baseChangedLmul_eq (K := K) (L := L) A]
  rw [Algebra.norm_apply,
    LinearMap.det_eq_sign_charpoly_coeff,
    Module.finrank_baseChange]
  rfl

/-- Galois conjugation after scalar extension to an arbitrary commutative
`K`-algebra. -/
def scalarConjugation
    (A : Type*) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) :
    A ⊗[K] L →ₐ[A] A ⊗[K] L :=
  Algebra.TensorProduct.map (AlgHom.id A A) σ.toAlgHom

omit [FiniteDimensional K L] in
@[simp]
theorem scalarConjugation_tmul
    (A : Type*) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (a : A) (x : L) :
    scalarConjugation (K := K) (L := L) A σ (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] σ x :=
  rfl

omit [FiniteDimensional K L] in
/-- Evaluating a universal conjugate polynomial at the coordinates of a
base-changed element gives its actual scalar-extended conjugate. -/
theorem eval₂_conjugatePolynomial_baseChange
    (A : Type*) [CommRing A] [Algebra K A]
    {ι : Type w} [Fintype ι]
    (b : Module.Basis ι K L) (σ : L ≃ₐ[K] L)
    (z : A ⊗[K] L) :
    MvPolynomial.eval₂
        ((Algebra.TensorProduct.includeRight
          (R := K) (A := A) (B := L)).toRingHom)
        (fun i ↦ (Algebra.TensorProduct.includeLeft
          (R := K) (S := K) (A := A) (B := L))
          ((Algebra.TensorProduct.basis A b).repr z i))
        (conjugatePolynomial b σ) =
      scalarConjugation (K := K) (L := L) A σ z := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  simp only [conjugatePolynomial, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_C]
  calc
    ∑ i, (Algebra.TensorProduct.includeLeft
          (R := K) (S := K) (A := A) (B := L))
          ((Algebra.TensorProduct.basis A b).repr z i) *
        (Algebra.TensorProduct.includeRight
          (R := K) (A := A) (B := L)) (σ (b i)) =
        ∑ i, scalarConjugation (K := K) (L := L) A σ
          (((Algebra.TensorProduct.basis A b).repr z i) •
            Algebra.TensorProduct.basis A b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [scalarConjugation, Algebra.TensorProduct.basis_apply,
        Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.smul_def]
    _ = scalarConjugation (K := K) (L := L) A σ
          (∑ i, ((Algebra.TensorProduct.basis A b).repr z i) •
            Algebra.TensorProduct.basis A b i) := by
      rw [map_sum]
    _ = scalarConjugation (K := K) (L := L) A σ z := by
      rw [(Algebra.TensorProduct.basis A b).sum_repr]

/-- The full scalar-extension formula: extending
the determinant norm back to a Galois algebra is the product of all
Galois conjugates.  The coefficient algebra `A` is arbitrary. -/
theorem includeLeft_norm_eq_prod_scalarConjugations
    [IsGalois K L] [Infinite K]
    (A : Type*) [CommRing A] [Algebra K A] [Nontrivial A]
    (z : A ⊗[K] L) :
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A) (B := L))
        (Algebra.norm A z) =
      ∏ σ : L ≃ₐ[K] L,
        scalarConjugation (K := K) (L := L) A σ z := by
  classical
  let b := Module.Free.chooseBasis K L
  let c : Module.Free.ChooseBasisIndex K L → A :=
    fun i ↦ (Algebra.TensorProduct.basis A b).repr z i
  let iL : A →+* A ⊗[K] L :=
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A) (B := L)).toRingHom
  let iR : L →+* A ⊗[K] L :=
    (Algebra.TensorProduct.includeRight
      (R := K) (A := A) (B := L)).toRingHom
  have hmaps :
      iL.comp (algebraMap K A) =
        iR.comp (algebraMap K L) := by
    ext x
    simp [iL, iR]
  have hleft :
      MvPolynomial.eval₂ iR (fun i ↦ iL (c i))
          (MvPolynomial.map (algebraMap K L)
            (normPolynomial b)) =
        iL (Algebra.norm A z) := by
    rw [MvPolynomial.eval₂_map]
    rw [← hmaps]
    rw [← MvPolynomial.hom_eval₂]
    rw [eval₂_normPolynomial_baseChange]
  have hright :
      MvPolynomial.eval₂ iR (fun i ↦ iL (c i))
          (galoisProductPolynomial b) =
        ∏ σ : L ≃ₐ[K] L,
          scalarConjugation (K := K) (L := L) A σ z := by
    rw [galoisProductPolynomial,
      MvPolynomial.eval₂_prod]
    apply Finset.prod_congr rfl
    intro σ hσ
    exact eval₂_conjugatePolynomial_baseChange
      (K := K) (L := L) A b σ z
  change iL (Algebra.norm A z) =
    ∏ σ : L ≃ₐ[K] L,
      scalarConjugation (K := K) (L := L) A σ z
  rw [← hright, ← hleft,
    map_normPolynomial_eq_galoisProductPolynomial b]

omit [FiniteDimensional K L] in
@[simp]
theorem scalarConjugation_baseAdele_apply
    [NumberField K]
    (σ : L ≃ₐ[K] L) (z : RelativeAdeleRing K L) :
    scalarConjugation
        (NumberField.AdeleRing (𝓞 K) K) σ z =
      conjugation K L σ z :=
  rfl

/-- In full adèle form, the base extension of the
determinant norm of an arbitrary relative adèle is the product of all of
its Galois conjugates. -/
theorem adeleInclusion_norm_eq_prod_conjugates
    [NumberField K] [IsGalois K L]
    (z : RelativeAdeleRing K L) :
    adeleInclusion K L
        (Algebra.norm
          (NumberField.AdeleRing (𝓞 K) K) z) =
      ∏ σ : L ≃ₐ[K] L, conjugation K L σ z := by
  change
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := NumberField.AdeleRing (𝓞 K) K) (B := L))
        (Algebra.norm
          (NumberField.AdeleRing (𝓞 K) K) z) =
      _
  simpa only [scalarConjugation_baseAdele_apply] using
    (includeLeft_norm_eq_prod_scalarConjugations
      (K := K) (L := L)
      (NumberField.AdeleRing (𝓞 K) K) z)

/-- In full idèle form,
`i_{L/K}(N_{L/K}(a)) = ∏_{σ ∈ Gal(L/K)} σ(a)` for every relative
idèle `a`. -/
theorem inclusion_norm_eq_prod_conjugates
    [NumberField K] [IsGalois K L]
    (a : RelativeIdeleGroup K L) :
    inclusion K L (norm K L a) =
      ∏ σ : L ≃ₐ[K] L, σ • a := by
  apply Units.ext
  simp only [inclusion, norm, MonoidHom.comp_apply,
    Units.coe_map, Units.coe_prod,
    smul_def, conjugationIdele_coe]
  exact adeleInclusion_norm_eq_prod_conjugates
    (K := K) (L := L) (a : RelativeAdeleRing K L)

end RelativeIdeleGroup
