/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponentTensor
public import Mathlib.RingTheory.TensorProduct.Basic
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeInitialForm

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Extension of scalars from $\widehat{\mathrm P}$

This module proves LM24, Proposition 6.1.2. The homogeneous-component equivalences of Proposition
5.3.1
assemble to the graded algebra equivalence

`P̂ ⊗[K] K(ℝ^{≤ 0}) ≃ₐ[K] RV̂`.

The map sends a pure tensor to the product of the principal graded embedding and the grade-zero
finite-support embedding. Its component at `α` is exactly the equivalence on the
`α`-component. Thus both scalar factors and all homogeneous projections remain visible in the
public API. The displayed orientation agrees with Proposition 5.3.1; one sentence in the printed
proof reverses the corresponding component arrow.

The construction is stated over a coefficient field of characteristic zero, which supplies the
two multiplicativity theorems behind the principal and degree gradings.
-/

open scoped DirectSum HahnSeries NatOrdinal TensorProduct

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K]

variable (K) in
private def principalSubringTensorLinearEquiv :
    PrincipalSubring K ⊗[K] FiniteSupportRing (K := K) ≃ₗ[K]
      DegreeGraded K :=
  TensorProduct.directSumLeft K K (PrincipalComponent K)
      (FiniteSupportRing (K := K)) ≪≫ₗ
    DirectSum.congrLinearEquiv
      (fun α ↦ principalComponentTensorEquiv K α)

variable (K) in
/-- The canonical projection of the tensor product onto its tensor factor in principal grade
`α`. -/
def principalSubringTensorComponent (α : NatOrdinal) :
    PrincipalSubring K ⊗[K] FiniteSupportRing (K := K) →ₗ[K]
      PrincipalComponent K α ⊗[K] FiniteSupportRing (K := K) :=
  (DirectSum.component K NatOrdinal
    (fun β ↦ PrincipalComponent K β ⊗[K] FiniteSupportRing (K := K))
    α).comp
      (TensorProduct.directSumLeft K K (PrincipalComponent K)
        (FiniteSupportRing (K := K))).toLinearMap

/-- The tensor component of a pure tensor is the tensor of the corresponding principal
component. -/
@[simp]
theorem principalSubringTensorComponent_tmul (α : NatOrdinal) (x : PrincipalSubring K)
    (p : FiniteSupportRing (K := K)) :
    principalSubringTensorComponent K α (x ⊗ₜ p) = x α ⊗ₜ p := by
  exact TensorProduct.directSumLeft_tmul K K x p α

private theorem principalSubringTensorLinearEquiv_tmul_apply
    (x : PrincipalSubring K) (p : FiniteSupportRing (K := K))
    (α : NatOrdinal) :
    principalSubringTensorLinearEquiv K (x ⊗ₜ p) α =
      principalComponentTensorEquiv K α (x α ⊗ₜ p) := by
  simp [principalSubringTensorLinearEquiv, DirectSum.coe_congrLinearEquiv]

variable (K) in
/-- The finite-support ring embeds in the degree-graded ring through the
degree-zero residue equivalence. -/
def finiteSupportGradedEmbedding :
    FiniteSupportRing (K := K) →ₐ[K] DegreeGraded K where
  toRingHom := (DirectSum.ofZeroRingHom
    (HahnSeries.Nonpositive.degreeValuation K).Component).comp
      (HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K).toRingHom
  commutes' k := by
    change DirectSum.of _ 0
        (HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K
          (HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k)) =
      algebraMap K (DegreeGraded K) k
    rw [degreeFiniteSupportResidueEquiv_scalar,
      degreeGraded_algebraMap_apply]

/-- The finite-support embedding places the degree residue class in grade zero. -/
@[simp]
theorem finiteSupportGradedEmbedding_apply (p : FiniteSupportRing (K := K)) :
    finiteSupportGradedEmbedding K p =
      DirectSum.of _ 0
        (HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K p) :=
  (rfl)

/-- Multiplication by the grade-zero finite-support embedding is the residue-ring scalar action
on each homogeneous component. -/
theorem finiteSupportGradedEmbedding_mul_of (p : FiniteSupportRing (K := K)) (α : NatOrdinal)
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    finiteSupportGradedEmbedding K p *
        DirectSum.of
          (HahnSeries.Nonpositive.degreeValuation K).Component α x =
      DirectSum.of
        (HahnSeries.Nonpositive.degreeValuation K).Component α
        (HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K p • x) := by
  rw [finiteSupportGradedEmbedding_apply, ← DirectSum.of_zero_smul]

variable (K) in
/-- The grade-zero finite-support embedding is injective. -/
theorem finiteSupportGradedEmbedding_injective :
    Function.Injective (finiteSupportGradedEmbedding K) := by
  intro p q hpq
  apply (HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K).injective
  exact (DirectSum.of_injective 0) hpq

variable (K) in
/-- Multiplication of the two canonical graded embeddings induces the global tensor map. -/
def principalSubringTensorMap [CharZero K] :
    PrincipalSubring K ⊗[K] FiniteSupportRing (K := K) →ₐ[K]
      DegreeGraded K :=
  Algebra.TensorProduct.productMap
    (principalSubringEmbedding K)
    (finiteSupportGradedEmbedding K)

/-- On a pure tensor, the global tensor map is multiplication of the two embedded factors. -/
theorem principalSubringTensorMap_tmul [CharZero K] (x : PrincipalSubring K) (p :
  FiniteSupportRing (K := K)) :
    principalSubringTensorMap K (x ⊗ₜ p) =
      principalSubringEmbedding K x *
        finiteSupportGradedEmbedding K p :=
  (rfl)

private theorem degreeGraded_of_zero_mul
    (a : (HahnSeries.Nonpositive.degreeValuation K).Component 0)
    (x : DegreeGraded K) :
    DirectSum.of _ 0 a * x = a • x := by
  induction x using DirectSum.induction_on with
  | zero => rw [mul_zero, smul_zero]
  | of α x =>
      rw [← DirectSum.of_zero_smul]
      exact (DirectSum.lof
        ((HahnSeries.Nonpositive.degreeValuation K).Component 0)
        NatOrdinal
        (HahnSeries.Nonpositive.degreeValuation K).Component
        α).map_smul a x
  | add x y hx hy => rw [mul_add, smul_add, hx, hy]

private theorem principalSubringTensorMap_eq_linearEquiv [CharZero K]
    (z : PrincipalSubring K ⊗[K] FiniteSupportRing (K := K)) :
    principalSubringTensorMap K z =
      principalSubringTensorLinearEquiv K z := by
  induction z using TensorProduct.inductionOn with
  | tmul x p =>
      rw [principalSubringTensorMap_tmul,
        finiteSupportGradedEmbedding_apply, mul_comm,
        degreeGraded_of_zero_mul]
      ext α
      rw [DirectSum.smul_apply,
        principalSubringTensorLinearEquiv_tmul_apply,
        principalSubringEmbedding_apply,
        principalComponentTensorEquiv_tmul]
  | add x y hx hy =>
      calc
        principalSubringTensorMap K (x + y) =
            principalSubringTensorMap K x +
              principalSubringTensorMap K y :=
          (principalSubringTensorMap K).map_add x y
        _ = principalSubringTensorLinearEquiv K x +
              principalSubringTensorLinearEquiv K y :=
          congrArg₂ (· + ·) hx hy
        _ = principalSubringTensorLinearEquiv K (x + y) :=
          ((principalSubringTensorLinearEquiv K).map_add x y).symm

variable (K) in
/-- The multiplication-induced global tensor map is bijective. -/
theorem principalSubringTensorMap_bijective [CharZero K] :
    Function.Bijective (principalSubringTensorMap K) := by
  have hfunctions :
      (principalSubringTensorMap K :
          PrincipalSubring K ⊗[K] FiniteSupportRing (K := K) →
            DegreeGraded K) =
        principalSubringTensorLinearEquiv K := by
    funext z
    exact principalSubringTensorMap_eq_linearEquiv z
  rw [hfunctions]
  exact (principalSubringTensorLinearEquiv K).bijective

variable (K) in
/-- LM24, Proposition 6.1.2: the algebra equivalence induced by multiplication. -/
@[blueprint "fact:principal-subring-tensor-decomposition"
  (phase := "Polynomial presentations")
  (title := "Scalar extension from $\\widehat{\\mathrm P}$ to $\\widehat{\\mathrm{RV}}$ (LM24, \
    Proposition 6.1.2)")
  (statement := /--
    Let $K$ be a field of characteristic zero. Multiplication of initial forms
    induces an isomorphism of $K$-algebras
    \[
      \widehat{\mathrm P}\otimes_K K(\mathbb R^{\le 0})
        \xrightarrow{\sim}\widehat{\mathrm{RV}}.
    \]
  -/)
  (proof := /--
  \ref{fact:principal-series-representatives} gives in each degree the
  component equivalence of LM24, Proposition 5.3.1.
  \ref{fact:degree-multiplicativity} makes multiplication of initial forms respect those
  components, so their direct sum is an algebra homomorphism.  Every element has finite degree
  support; applying the inverse component maps degree by degree proves bijectivity.
  -/)]
def principalSubringTensorEquiv [CharZero K] :
    PrincipalSubring K ⊗[K] FiniteSupportRing (K := K) ≃ₐ[K]
      DegreeGraded K :=
  AlgEquiv.ofBijective (principalSubringTensorMap K)
    (principalSubringTensorMap_bijective K)

/-- The graded tensor equivalence has the multiplication-induced tensor map as its forward map. -/
@[simp]
theorem principalSubringTensorEquiv_apply [CharZero K]
    (z : PrincipalSubring K ⊗[K] FiniteSupportRing (K := K)) :
    principalSubringTensorEquiv K z =
      principalSubringTensorMap K z :=
  (rfl)

/-- The graded tensor equivalence multiplies the images of a pure tensor's two factors. -/
theorem principalSubringTensorEquiv_tmul [CharZero K]
    (x : PrincipalSubring K) (p : FiniteSupportRing (K := K)) :
    principalSubringTensorEquiv K (x ⊗ₜ p) =
      principalSubringEmbedding K x *
        finiteSupportGradedEmbedding K p := by
  rw [principalSubringTensorEquiv_apply, principalSubringTensorMap_tmul]

/-- On a pure tensor, each homogeneous projection of the global equivalence is the corresponding
homogeneous-component equivalence. -/
theorem principalSubringTensorEquiv_tmul_apply [CharZero K]
    (x : PrincipalSubring K) (p : FiniteSupportRing (K := K))
    (α : NatOrdinal) :
    principalSubringTensorEquiv K (x ⊗ₜ p) α =
      principalComponentTensorEquiv K α (x α ⊗ₜ p) := by
  rw [principalSubringTensorEquiv_apply,
    principalSubringTensorMap_eq_linearEquiv,
    principalSubringTensorLinearEquiv_tmul_apply]

/-- On an arbitrary tensor, every homogeneous projection of the global equivalence is the
corresponding homogeneous-component equivalence applied to the canonical tensor component. -/
theorem principalSubringTensorEquiv_component [CharZero K]
    (z : PrincipalSubring K ⊗[K] FiniteSupportRing (K := K))
    (α : NatOrdinal) :
    principalSubringTensorEquiv K z α =
      principalComponentTensorEquiv K α
        (principalSubringTensorComponent K α z) := by
  rw [principalSubringTensorEquiv_apply,
    principalSubringTensorMap_eq_linearEquiv]
  rw [principalSubringTensorLinearEquiv, LinearEquiv.trans_apply,
    principalSubringTensorComponent, LinearMap.comp_apply,
    DirectSum.coe_congrLinearEquiv, DirectSum.lmap_apply,
    ← DirectSum.apply_eq_component]
  rfl

/-- The canonical tensor component of the inverse global equivalence is the inverse
homogeneous-component
equivalence of that homogeneous component. -/
@[simp]
theorem principalSubringTensorComponent_symm_apply [CharZero K]
    (y : DegreeGraded K) (α : NatOrdinal) :
    principalSubringTensorComponent K α
        ((principalSubringTensorEquiv K).symm y) =
      (principalComponentTensorEquiv K α).symm (y α) := by
  apply (principalComponentTensorEquiv K α).injective
  rw [← principalSubringTensorEquiv_component]
  simp

/-- Restricting the global equivalence to the finite-support factor gives its grade-zero
embedding. -/
theorem principalSubringTensorEquiv_one_tmul [CharZero K] (p : FiniteSupportRing (K := K)) :
    principalSubringTensorEquiv K (1 ⊗ₜ p) =
      finiteSupportGradedEmbedding K p := by
  rw [principalSubringTensorEquiv_tmul, map_one, one_mul]

/-- Restricting the global equivalence to the principal graded factor gives its canonical
embedding. -/
theorem principalSubringTensorEquiv_tmul_one [CharZero K] (x : PrincipalSubring K) :
    principalSubringTensorEquiv K (x ⊗ₜ 1) =
      principalSubringEmbedding K x := by
  rw [principalSubringTensorEquiv_tmul, map_one, mul_one]

/-- The inverse global tensor equivalence sends the finite-support embedding to the corresponding
pure tensor. -/
theorem principalSubringTensorEquiv_symm_finiteSupportGradedEmbedding [CharZero K]
    (p : FiniteSupportRing (K := K)) :
    (principalSubringTensorEquiv K).symm
        (finiteSupportGradedEmbedding K p) = 1 ⊗ₜ p := by
  apply (principalSubringTensorEquiv K).injective
  rw [AlgEquiv.apply_symm_apply, principalSubringTensorEquiv_one_tmul]

/-- The inverse global tensor equivalence sends the principal graded embedding to the
corresponding pure tensor. -/
@[simp]
theorem principalSubringTensorEquiv_symm_principalGradedEmbedding [CharZero K] (x :
  PrincipalSubring K) :
    (principalSubringTensorEquiv K).symm
        (principalSubringEmbedding K x) = x ⊗ₜ 1 := by
  apply (principalSubringTensorEquiv K).injective
  rw [AlgEquiv.apply_symm_apply, principalSubringTensorEquiv_tmul_one]

/-- A nonzero finite-support series has degree zero. -/
theorem degreeValuation_finiteSupport_eq_zero (p : FiniteSupportRing (K := K)) (hp : p ≠ 0) :
    HahnSeries.Nonpositive.degreeValuation K (p : Series K) = 0 := by
  rw [HahnSeries.Nonpositive.degreeValuation_apply, HahnSeries.degree_eq_zero]
  refine ⟨fun h ↦ hp (Subtype.ext (Subtype.ext h)), ?_⟩
  exact (HahnSeries.Nonpositive.mem_finiteSupportSubring_iff (p : Series K)).mp p.property

/-- A finite-support series as a representative in the weak degree filtration at zero. -/
def finiteSupportFiltrationRepresentative (p : FiniteSupportRing (K := K)) :
    (HahnSeries.Nonpositive.degreeValuation K).filtrationLE 0 :=
  ⟨(p : Series K), ((HahnSeries.Nonpositive.degreeValuation K).mem_filtrationLE_iff 0 _).mpr (by
    by_cases hp : p = 0
    · subst hp
      simp
    · rw [degreeValuation_finiteSupport_eq_zero p hp, WithBot.coe_zero])⟩

@[simp]
theorem coe_finiteSupportFiltrationRepresentative (p : FiniteSupportRing (K := K)) :
    (finiteSupportFiltrationRepresentative p : Series K) = (p : Series K) :=
  (rfl)

/-- The finite-support embedding sends a series to its grade-zero homogeneous class. -/
theorem finiteSupportGradedEmbedding_eq_homogeneousMk (p : FiniteSupportRing (K := K)) :
    finiteSupportGradedEmbedding K p =
      (HahnSeries.Nonpositive.degreeValuation K).homogeneousMk 0
        (finiteSupportFiltrationRepresentative p) := by
  rw [finiteSupportGradedEmbedding_apply,
    HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv_apply,
    (HahnSeries.Nonpositive.degreeValuation K).residueMap_apply,
    MaxAddDegree.homogeneousMk_apply]
  apply congrArg (DirectSum.of (HahnSeries.Nonpositive.degreeValuation K).Component 0)
  apply congrArg ((HahnSeries.Nonpositive.degreeValuation K).componentMk 0)
  apply Subtype.ext
  rw [(HahnSeries.Nonpositive.degreeValuation K).coe_nonpositiveEquivFiltrationLEZero,
    RingEquiv.coe_subringCongr_apply, coe_finiteSupportFiltrationRepresentative]

/-- The finite-support embedding sends a series to its initial form. -/
theorem finiteSupportGradedEmbedding_eq_initialForm (p : FiniteSupportRing (K := K)) :
    finiteSupportGradedEmbedding K p =
      (HahnSeries.Nonpositive.degreeValuation K).initialForm (p : Series K) := by
  rw [finiteSupportGradedEmbedding_eq_homogeneousMk]
  by_cases hp : p = 0
  · have hzero : (HahnSeries.Nonpositive.degreeValuation K).homogeneousMk 0
        (finiteSupportFiltrationRepresentative p) = 0 := by
      rw [MaxAddDegree.homogeneousMk_eq_zero_iff, coe_finiteSupportFiltrationRepresentative, hp,
        ZeroMemClass.coe_zero, MaxAddDegree.map_zero]
      exact WithBot.bot_lt_coe 0
    rw [hzero, hp, ZeroMemClass.coe_zero, MaxAddDegree.initialForm_zero]
  · have hne : (HahnSeries.Nonpositive.degreeValuation K).componentMk 0
        (finiteSupportFiltrationRepresentative p) ≠ 0 := by
      rw [ne_eq, MaxAddDegree.componentMk_eq_zero_iff, coe_finiteSupportFiltrationRepresentative,
        degreeValuation_finiteSupport_eq_zero p hp]
      exact lt_irrefl _
    exact (MaxAddDegree.initialForm_eq_homogeneousMk_of_componentMk_ne_zero _ 0 _ hne).symm

end

end Berarducci
