/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringTensor
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportMonoidAlgebra

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MonoidAlgebra.SingleZeroFactors
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedDivisibility
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# The degree-graded ring as a monoid algebra

LM24, Proposition 6.1.2 identifies the degree-graded ring with the tensor product of
`P̂` and the finite-support Hahn-series ring. Combining that identification
with the canonical monoid-algebra presentation of finite-support Hahn series presents the full
graded ring as a finite-support monoid algebra over `P̂`.

Under this presentation, the principal graded subring consists precisely of the terms supported
at exponent zero. Therefore, if a product of two nonzero graded elements lies in the principal
graded subring, then both factors lie there. This is the algebraic step used in LM24,
Corollary 6.2.2.
-/

open scoped DirectSum HahnSeries NatOrdinal TensorProduct

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

variable (K) in
/-- The canonical monoid-algebra presentation of the degree-graded ring. -/
def degreeGradedEquivPrincipalMonoidAlgebra :
    DegreeGraded K ≃ₐ[K]
      AddMonoidAlgebra (PrincipalSubring K)
        (HahnSeries.Nonpositive.exponentMonoid ℝ) :=
  (principalSubringTensorEquiv K).symm |>.trans
    (Algebra.TensorProduct.congr AlgEquiv.refl
      HahnSeries.Nonpositive.finiteSupportAddMonoidAlgebraEquiv) |>.trans
    ((AddMonoidAlgebra.scalarTensorEquiv K (PrincipalSubring K)
      (M := HahnSeries.Nonpositive.exponentMonoid ℝ)).restrictScalars K)

/-- A principal graded element corresponds to a term supported at exponent zero. -/
@[simp]
theorem degreeGradedEquivPrincipalMonoidAlgebra_principal
    (x : PrincipalSubring K) :
    degreeGradedEquivPrincipalMonoidAlgebra K
        (principalSubringEmbedding K x) =
      AddMonoidAlgebra.single 0 x := by
  have htensor :
      (principalSubringTensorEquiv K).symm
          (principalSubringEmbedding K x) =
        x ⊗ₜ (1 : FiniteSupportRing (K := K)) := by
    apply (principalSubringTensorEquiv K).injective
    rw [(principalSubringTensorEquiv K).apply_symm_apply]
    rw [principalSubringTensorEquiv_tmul]
    rw [map_one, mul_one]
  rw [degreeGradedEquivPrincipalMonoidAlgebra,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, htensor]
  simp only [Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
    Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one,
    AlgEquiv.coe_restrictScalars', AddMonoidAlgebra.scalarTensorEquiv_tmul]
  rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.smul_single', mul_one]

variable (K) in
/-- A finite-support Hahn monomial corresponds to the same exponent with coefficient one. -/
theorem degreeGradedEquivPrincipalMonoidAlgebra_finiteSupportMonomial
    (g : HahnSeries.Nonpositive.exponentMonoid ℝ) :
    degreeGradedEquivPrincipalMonoidAlgebra K
        (finiteSupportGradedEmbedding K
          (HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g)) =
      AddMonoidAlgebra.single g 1 := by
  have htensor :
      (principalSubringTensorEquiv K).symm
          (finiteSupportGradedEmbedding K
            (HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g)) =
        (1 : PrincipalSubring K) ⊗ₜ
          HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g := by
    apply (principalSubringTensorEquiv K).injective
    rw [(principalSubringTensorEquiv K).apply_symm_apply]
    rw [principalSubringTensorEquiv_tmul]
    rw [map_one, one_mul]
  rw [degreeGradedEquivPrincipalMonoidAlgebra,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, htensor]
  simp only [Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_algHom,
    HahnSeries.Nonpositive.finiteSupportAddMonoidAlgebraEquiv_monomial,
    AlgEquiv.coe_restrictScalars', AddMonoidAlgebra.scalarTensorEquiv_tmul,
    AddMonoidAlgebra.mapAlgHom_single, map_one, one_smul]

/-- A principal coefficient multiplied by a finite-support Hahn monomial corresponds to a
single formal monomial. -/
theorem degreeGradedEquivPrincipalMonoidAlgebra_principal_monomial
    (x : PrincipalSubring K)
    (g : HahnSeries.Nonpositive.exponentMonoid ℝ) :
    degreeGradedEquivPrincipalMonoidAlgebra K
        (principalSubringEmbedding K x *
          finiteSupportGradedEmbedding K
            (HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g)) =
      AddMonoidAlgebra.single g x := by
  rw [map_mul,
    degreeGradedEquivPrincipalMonoidAlgebra_principal,
    degreeGradedEquivPrincipalMonoidAlgebra_finiteSupportMonomial]
  rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

/-- The inverse presentation sends one formal monomial to the corresponding product of the
principal coefficient and finite-support Hahn monomial. -/
@[simp]
theorem degreeGradedEquivPrincipalMonoidAlgebra_symm_single
    (g : HahnSeries.Nonpositive.exponentMonoid ℝ)
    (x : PrincipalSubring K) :
    (degreeGradedEquivPrincipalMonoidAlgebra K).symm
        (AddMonoidAlgebra.single g x) =
      principalSubringEmbedding K x *
        finiteSupportGradedEmbedding K
          (HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g) := by
  apply (degreeGradedEquivPrincipalMonoidAlgebra K).injective
  rw [(degreeGradedEquivPrincipalMonoidAlgebra K).apply_symm_apply]
  exact (degreeGradedEquivPrincipalMonoidAlgebra_principal_monomial x g).symm

/-- Nonzero factors of an element of the principal graded subalgebra lie in that subalgebra. -/
theorem factors_mem_principalGradedSubalgebra_of_mul_mem {B C : DegreeGraded K}
    (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : B * C ∈ principalSubringSubalgebra K) :
    B ∈ principalSubringSubalgebra K ∧
      C ∈ principalSubringSubalgebra K := by
  let eP := principalSubringEquivSubalgebra K
  let BC : principalSubringSubalgebra K := ⟨B * C, hBC⟩
  let x := eP.symm BC
  have hx : principalSubringEmbedding K x = B * C := by
    calc
      principalSubringEmbedding K x = (eP x : DegreeGraded K) :=
        (principalSubringEquivSubalgebra_apply x).symm
      _ = B * C := congrArg Subtype.val (eP.apply_symm_apply BC)
  let e := degreeGradedEquivPrincipalMonoidAlgebra K
  have hProduct : e B * e C = AddMonoidAlgebra.single 0 x := by
    calc
      e B * e C = e (B * C) := (e.map_mul B C).symm
      _ = e (principalSubringEmbedding K x) := congrArg e hx.symm
      _ = AddMonoidAlgebra.single 0 x := by
        change degreeGradedEquivPrincipalMonoidAlgebra K
          (principalSubringEmbedding K x) = _
        exact degreeGradedEquivPrincipalMonoidAlgebra_principal x
  have heB : e B ≠ 0 := fun h ↦ hB (e.injective (h.trans (map_zero e).symm))
  have heC : e C ≠ 0 := fun h ↦ hC (e.injective (h.trans (map_zero e).symm))
  obtain ⟨b, c, hb, hc⟩ :=
    AddMonoidAlgebra.exists_eq_single_zero_of_mul_eq_single_zero
      (R := PrincipalSubring K)
      (M := HahnSeries.Nonpositive.exponentMonoid ℝ)
      (HahnSeries.Nonpositive.exponentMonoid_top_eq_zero ℝ)
      heB heC hProduct
  constructor
  · have hB_eq : principalSubringEmbedding K b = B := by
      apply e.injective
      calc
        e (principalSubringEmbedding K b) =
            AddMonoidAlgebra.single 0 b := by
          change degreeGradedEquivPrincipalMonoidAlgebra K
            (principalSubringEmbedding K b) = _
          exact degreeGradedEquivPrincipalMonoidAlgebra_principal b
        _ = e B := hb.symm
    rw [← hB_eq, mem_principalGradedSubalgebra_iff, isPrincipalGraded_iff]
    intro α
    rw [principalSubringEmbedding_apply]
    exact principalComponentToHahnDegreeLayer_isPrincipal α (b α)
  · have hC_eq : principalSubringEmbedding K c = C := by
      apply e.injective
      calc
        e (principalSubringEmbedding K c) =
            AddMonoidAlgebra.single 0 c := by
          change degreeGradedEquivPrincipalMonoidAlgebra K
            (principalSubringEmbedding K c) = _
          exact degreeGradedEquivPrincipalMonoidAlgebra_principal c
        _ = e C := hc.symm
    rw [← hC_eq, mem_principalGradedSubalgebra_iff, isPrincipalGraded_iff]
    intro α
    rw [principalSubringEmbedding_apply]
    exact principalComponentToHahnDegreeLayer_isPrincipal α (c α)

end

end Berarducci
