/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.ExtensionFactorClassification
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.SeparablePolynomialFactors
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.BaseChangeAdjoinRoot
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.PolynomialCRT
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.CanonicalTensorMap
public import Mathlib.Algebra.Group.Pi.Units
/-!
# Tensor-product decomposition over a completion

For a finite separable extension `L / K`, the canonical map
`L ⊗_K K_v → ∏_{w|v} L_w` is an isomorphism.  The proof follows the
construction: choose a primitive element, factor its mapped minimal polynomial,
apply the Chinese remainder theorem, and identify every simple factor with
the corresponding completion using the extension-factor correspondence.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped BigOperators TensorProduct
open ValuationTheory.Completion

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

/-- The primitive power basis used in the separable proof of the completion
tensor-product decomposition. -/
noncomputable def completionTensorDecompositionPowerBasis
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] : PowerBasis K L :=
  Field.powerBasisOfFiniteOfSeparable K L

/-- the extension-factor correspondence makes the extensions `w | v` into a finite type. -/
@[reducible]
noncomputable def completionTensorDecompositionExtensionFintype
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    Fintype (AbsoluteValueExtension vK L) := by
  let pb := completionTensorDecompositionPowerBasis K L
  let hf : Irreducible (minpoly K pb.gen) :=
    minpoly.irreducible pb.isIntegral_gen
  let e := completionExtensionFactorExtensionEquivFactors vK hvK hf
    (minpoly.aeval K pb.gen) pb.adjoin_gen_eq_top
  exact Fintype.ofEquiv _ e.symm

/-- In the separable case the mapped minimal polynomial is the product of
the factors indexed by all extensions `w | v`. -/
theorem completionTensorDecomposition_mapped_minpoly_eq_prod_extensionFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
    (minpoly K (completionTensorDecompositionPowerBasis K L).gen).map
        (algebraMap K vK.Completion) =
      ∏ w : AbsoluteValueExtension vK L,
        completionExtensionFactorExtensionFactor vK
          (completionTensorDecompositionPowerBasis K L).gen w := by
  classical
  let := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecompositionPowerBasis K L
  let p := (minpoly K pb.gen).map (algebraMap K vK.Completion)
  let hf : Irreducible (minpoly K pb.gen) :=
    minpoly.irreducible pb.isIntegral_gen
  let e := completionExtensionFactorExtensionEquivFactors vK hvK hf
    (minpoly.aeval K pb.gen) pb.adjoin_gen_eq_top
  have hpmonic : p.Monic :=
    (minpoly.monic pb.isIntegral_gen).map (algebraMap K vK.Completion)
  have hpsep : p.Separable :=
    Polynomial.Separable.map
      (Algebra.IsSeparable.isSeparable K (pb.gen : L))
  calc
    p = ∏ g : CompletionExtensionFactorCompletionFactors vK (minpoly K pb.gen),
        (g.1 : vK.Completion[X]) :=
      separable_monic_eq_prod_distinctNormalizedFactors p hpmonic hpsep
    _ = ∏ w : AbsoluteValueExtension vK L,
        completionExtensionFactorExtensionFactor vK pb.gen w := by
      symm
      exact Fintype.prod_equiv e _ _ (fun _ ↦ rfl)

/-- The factors indexed by distinct extensions are pairwise coprime. -/
theorem completionTensorDecomposition_extensionFactors_pairwise_coprime
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
    ∀ w w' : AbsoluteValueExtension vK L, w ≠ w' →
      IsCoprime
        (completionExtensionFactorExtensionFactor vK
          (completionTensorDecompositionPowerBasis K L).gen w)
        (completionExtensionFactorExtensionFactor vK
          (completionTensorDecompositionPowerBasis K L).gen w') := by
  classical
  let := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecompositionPowerBasis K L
  let hf : Irreducible (minpoly K pb.gen) :=
    minpoly.irreducible pb.isIntegral_gen
  let e := completionExtensionFactorExtensionEquivFactors vK hvK hf
    (minpoly.aeval K pb.gen) pb.adjoin_gen_eq_top
  intro w w' hww'
  have he : e w ≠ e w' := fun h ↦ hww' (e.injective h)
  exact distinctNormalizedFactors_pairwise_coprime
    ((minpoly K pb.gen).map (algebraMap K vK.Completion))
    (e w) (e w') he

/-- The factorization/CRT equivalence in the left tensor order
`K_v ⊗_K L`. -/
noncomputable def completionTensorDecompositionFactorEquiv
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    vK.Completion ⊗[K] L ≃ₐ[vK.Completion]
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion := by
  classical
  letI := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecompositionPowerBasis K L
  let hα := pb.isIntegral_gen
  let hgen := pb.adjoin_gen_eq_top
  letI hK : ∀ w : AbsoluteValueExtension vK L,
      Algebra K w.1.Completion :=
    fun w ↦ AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : ∀ w : AbsoluteValueExtension vK L, SMul K w.1.Completion :=
    fun w ↦ (hK w).toSMul
  letI : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let ebase := baseChangeEquivAdjoinRoot (A := vK.Completion) pb
  let hprod := completionTensorDecomposition_mapped_minpoly_eq_prod_extensionFactors
    (K := K) (L := L) vK hvK
  let econgr := AdjoinRoot.algEquivOfEq vK.Completion _ _ hprod
  let ecrt := adjoinRootProdEquivPi
    (fun w : AbsoluteValueExtension vK L ↦
      completionExtensionFactorExtensionFactor vK pb.gen w)
    (completionTensorDecomposition_extensionFactors_pairwise_coprime
      (K := K) (L := L) vK hvK)
  let elocal := AlgEquiv.piCongrRight fun w ↦
    completionExtensionFactorAdjoinRootEquivCompletion
      vK hvK pb.gen hα hgen w
  exact ebase.trans (econgr.trans (ecrt.trans elocal))

/-- The CRT equivalence sends the primitive generator to its canonical
image in every completion. -/
@[simp]
theorem completionTensorDecomposition_factorEquiv_one_tmul_gen
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    completionTensorDecompositionFactorEquiv (K := K) (L := L) vK hvK
        (1 ⊗ₜ[K] (completionTensorDecompositionPowerBasis K L).gen) w =
      AbsoluteValue.toCompletionAlgHom (K := K) w.1
        (completionTensorDecompositionPowerBasis K L).gen := by
  classical
  let := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecompositionPowerBasis K L
  let hK : ∀ w : AbsoluteValueExtension vK L,
      Algebra K w.1.Completion :=
    fun w ↦ AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : ∀ w : AbsoluteValueExtension vK L, SMul K w.1.Completion :=
    fun w ↦ (hK w).toSMul
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let factors := fun w : AbsoluteValueExtension vK L ↦
    completionExtensionFactorExtensionFactor vK pb.gen w
  let hcop := completionTensorDecomposition_extensionFactors_pairwise_coprime
    (K := K) (L := L) vK hvK
  let ebase := baseChangeEquivAdjoinRoot (A := vK.Completion) pb
  let hprod := completionTensorDecomposition_mapped_minpoly_eq_prod_extensionFactors
    (K := K) (L := L) vK hvK
  let econgr := AdjoinRoot.algEquivOfEq vK.Completion _ _ hprod
  let ecrt := adjoinRootProdEquivPi factors hcop
  let elocal := AlgEquiv.piCongrRight fun w ↦
    completionExtensionFactorAdjoinRootEquivCompletion
      vK hvK pb.gen pb.isIntegral_gen pb.adjoin_gen_eq_top w
  change elocal (ecrt (econgr (ebase (1 ⊗ₜ[K] pb.gen)))) w = _
  rw [baseChangeEquivAdjoinRoot_one_tmul_gen,
    AdjoinRoot.algEquivOfEq_root]
  change
    (completionExtensionFactorAdjoinRootEquivCompletion
      vK hvK pb.gen pb.isIntegral_gen pb.adjoin_gen_eq_top w)
        (adjoinRootProdEquivPi factors hcop
          (AdjoinRoot.mk (∏ w, factors w) X) w) = _
  rw [adjoinRootProdEquivPi_mk]
  exact completionExtensionFactor_adjoinRootEquivCompletion_root
    vK hvK pb.gen pb.isIntegral_gen pb.adjoin_gen_eq_top w

/-- The factorization equivalence is not merely an abstract isomorphism:
its algebra homomorphism is the canonical product map. -/
theorem completionTensorDecomposition_factorEquiv_toAlgHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    (completionTensorDecompositionFactorEquiv (K := K) (L := L) vK hvK).toAlgHom =
      completionTensorMapLeftCanonicalHom vK := by
  classical
  let := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecompositionPowerBasis K L
  let hK : ∀ w : AbsoluteValueExtension vK L,
      Algebra K w.1.Completion :=
    fun w ↦ AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : ∀ w : AbsoluteValueExtension vK L, SMul K w.1.Completion :=
    fun w ↦ (hK w).toSMul
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  apply (powerBasisBaseChange (A := vK.Completion) pb).algHom_ext
  funext w
  change
    completionTensorDecompositionFactorEquiv (K := K) (L := L) vK hvK
        (1 ⊗ₜ[K] (completionTensorDecompositionPowerBasis K L).gen) w =
      completionTensorMapLeftCanonicalHom (K := K) (L := L) vK
        (1 ⊗ₜ[K] (completionTensorDecompositionPowerBasis K L).gen) w
  rw [completionTensorDecomposition_factorEquiv_one_tmul_gen
      (K := K) (L := L) vK hvK w,
    completionTensorMap_leftCanonicalHom_tmul_apply]
  simp

/-- The canonical product map in the left tensor order is bijective. -/
theorem completionTensorDecomposition_leftCanonicalHom_bijective
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    Function.Bijective
      (completionTensorMapLeftCanonicalHom (K := K) (L := L) vK) := by
  classical
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  rw [← completionTensorDecomposition_factorEquiv_toAlgHom
    (K := K) (L := L) vK hvK]
  exact (completionTensorDecompositionFactorEquiv
    (K := K) (L := L) vK hvK).bijective

/-- the completion tensor-product decomposition in the left tensor order, retained for the scalar
extension calculations in the local degree, norm, and trace formulas.  Its underlying map is
  canonical. -/
noncomputable def completionTensorDecompositionLeft
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    vK.Completion ⊗[K] L ≃ₐ[vK.Completion]
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion := by
  letI : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  exact AlgEquiv.ofBijective
    (completionTensorMapLeftCanonicalHom (K := K) (L := L) vK)
    (completionTensorDecomposition_leftCanonicalHom_bijective
      (K := K) (L := L) vK hvK)

@[simp]
theorem completionTensorDecomposition_left_tmul_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (b : vK.Completion) (a : L)
    (w : AbsoluteValueExtension vK L) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    completionTensorDecompositionLeft (K := K) (L := L) vK hvK (b ⊗ₜ[K] a) w =
      algebraMap vK.Completion w.1.Completion b *
        AbsoluteValue.toCompletionAlgHom (K := K) w.1 a := by
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  change completionTensorMapLeftCanonicalHom (K := K) (L := L) vK
    (b ⊗ₜ[K] a) w = _
  exact completionTensorMap_leftCanonicalHom_tmul_apply vK b a w

/-- The canonical map in the chosen tensor-factor order is bijective. -/
theorem completionTensorDecomposition_canonicalHom_bijective
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI := Algebra.TensorProduct.rightAlgebra
      (R := K) (A := L) (B := vK.Completion)
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    Function.Bijective
      (completionTensorMapCanonicalHom (K := K) (L := L) vK) := by
  let := Algebra.TensorProduct.rightAlgebra
    (R := K) (A := L) (B := vK.Completion)
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let c := Algebra.TensorProduct.comm K L vK.Completion
  let h := completionTensorMapLeftCanonicalHom (K := K) (L := L) vK
  change Function.Bijective (fun x ↦ h (c x))
  exact (completionTensorDecomposition_leftCanonicalHom_bijective
    (K := K) (L := L) vK hvK).comp c.bijective

/-- **The completion tensor-product decomposition.**  The canonical map
`L ⊗_K K_v → ∏_{w|v} L_w` is an isomorphism for a finite separable
extension. -/
noncomputable def completionTensorDecomposition
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI := Algebra.TensorProduct.rightAlgebra
      (R := K) (A := L) (B := vK.Completion)
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    L ⊗[K] vK.Completion ≃ₐ[vK.Completion]
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion := by
  letI := Algebra.TensorProduct.rightAlgebra
    (R := K) (A := L) (B := vK.Completion)
  letI : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  exact AlgEquiv.ofBijective
    (completionTensorMapCanonicalHom (K := K) (L := L) vK)
    (completionTensorDecomposition_canonicalHom_bijective
      (K := K) (L := L) vK hvK)

/-- The endpoint is exactly the canonical homomorphism, not merely an
abstract algebra equivalence. -/
theorem completionTensorDecomposition_toAlgHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI := Algebra.TensorProduct.rightAlgebra
      (R := K) (A := L) (B := vK.Completion)
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    (completionTensorDecomposition (K := K) (L := L) vK hvK).toAlgHom =
      completionTensorMapCanonicalHom vK := by
  let := Algebra.TensorProduct.rightAlgebra
    (R := K) (A := L) (B := vK.Completion)
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  rfl

@[simp]
theorem completionTensorDecomposition_tmul_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (a : L) (b : vK.Completion)
    (w : AbsoluteValueExtension vK L) :
    letI := Algebra.TensorProduct.rightAlgebra
      (R := K) (A := L) (B := vK.Completion)
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    completionTensorDecomposition (K := K) (L := L) vK hvK (a ⊗ₜ[K] b) w =
      AbsoluteValue.toCompletionAlgHom (K := K) w.1 a *
        algebraMap vK.Completion w.1.Completion b := by
  let := Algebra.TensorProduct.rightAlgebra
    (R := K) (A := L) (B := vK.Completion)
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  change completionTensorMapCanonicalHom (K := K) (L := L) vK
    (a ⊗ₜ[K] b) w = _
  exact completionTensorMap_canonicalHom_tmul_apply vK a b w

/-- the completion tensor-product decomposition on unit groups, in the tensor-factor order used by
local scalar extension. -/
noncomputable def localTensorUnitsEquivCompletionProduct
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    (vK.Completion ⊗[K] L)ˣ ≃*
      (∀ w' : AbsoluteValueExtension vK L,
        w'.1.Completionˣ) := by
  letI : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  exact
    (Units.mapEquiv
      (completionTensorDecompositionLeft
        (K := K) (L := L) vK hvK).toMulEquiv).trans
      MulEquiv.piUnits

/-- Evaluation of the unit-group form of the completion tensor-product decomposition agrees with the
underlying tensor-product decomposition. -/
@[simp]
theorem localTensorUnitsEquivCompletionProduct_apply_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (z : (vK.Completion ⊗[K] L)ˣ)
    (w' : AbsoluteValueExtension vK L) :
    letI : ∀ u : AbsoluteValueExtension vK L,
        Algebra vK.Completion u.1.Completion :=
      fun u ↦ AbsoluteValue.completionAlgebra vK u.1 u.2
    (((localTensorUnitsEquivCompletionProduct vK hvK z) w' :
        w'.1.Completionˣ) : w'.1.Completion) =
      completionTensorDecompositionLeft (K := K) (L := L) vK hvK
        (z : vK.Completion ⊗[K] L) w' :=
  rfl

end Valuations
end AlgebraicNumberTheory

end
