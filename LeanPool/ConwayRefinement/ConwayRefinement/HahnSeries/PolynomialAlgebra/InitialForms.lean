/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.PrincipalGraded
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringTensor
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.Degree
public import LeanPool.ConwayRefinement.ConwayRefinement.LinearAlgebra.TensorProduct.SubalgebraBasis
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Data.Finsupp.Weight
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeWeightedPolynomial
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.BaseChange

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The series ring over the finite-support series and `RV̂ ≅ P̂ ⊗_K K_fin`

Let `K((ℝ^{≤0}))` be the series ring, with the finite-support series `K_fin = K(ℝ^{≤0})`. The
degree is a separated multiplicative degree on `K((ℝ^{≤0}))`, and
`RV̂ = gr_deg K((ℝ^{≤0})) ≅ P̂ ⊗_K K_fin`. This file records the structure map
`K_fin → K((ℝ^{≤0}))`, its degree, and the compatibility of the identification
`RV̂ ≅ P̂ ⊗_K K_fin` with initial forms: `1 ⊗ c` is the initial form of the finite-support series
`c`, and `B ⊗ 1` is the initial form of any series of degree `α` whose class is `B ∈ P_α`. The
lifts of a minimal system of homogeneous generators and the degree formula for polynomials in them
are in `Berarducci.PolynomialRing`.
-/

open HahnSeries HahnSeries.Nonpositive Berarducci

open scoped TensorProduct MaxAddDegree

universe v

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K]

omit [CharZero K] in
/-- The structure map `K_fin → K((ℝ^{≤0}))` is the subring inclusion. -/
theorem algebraMap_finiteSupportRing_apply (c : Berarducci.FiniteSupportRing (K := K)) :
    algebraMap (Berarducci.FiniteSupportRing (K := K)) (Nonpositive ℝ K) c =
      (c : Nonpositive ℝ K) := (rfl)

omit [CharZero K] in
/-- A nonzero finite-support series has degree zero, stated for the structure map
`K_fin → K((ℝ^{≤0}))`. -/
theorem degreeValuation_algebraMap_eq_zero (c : Berarducci.FiniteSupportRing (K := K))
    (hc : c ≠ 0) :
    degreeValuation K (algebraMap (Berarducci.FiniteSupportRing (K := K)) (Nonpositive ℝ K) c) =
      0 :=
  degreeValuation_finiteSupport_eq_zero c hc

/-- The right tensor factor gives `P̂ ⊗_K K_fin` its canonical `K_fin`-algebra structure. -/
instance principalSubringTensorFiniteSupportAlgebra :
    Algebra (Berarducci.FiniteSupportRing (K := K))
      (PrincipalSubring K ⊗[K] Berarducci.FiniteSupportRing (K := K)) :=
  Algebra.TensorProduct.rightAlgebra

/-- The identification `P̂ ⊗_K K_fin ≅ RV̂` sends a finite-support scalar to its initial form. -/
theorem principalSubringTensorEquiv_one_tmul_eq_initialForm
    (c : Berarducci.FiniteSupportRing (K := K)) :
    principalSubringTensorEquiv K (1 ⊗ₜ[K] c) =
      (degreeValuation K).initialForm
        (algebraMap (Berarducci.FiniteSupportRing (K := K)) (Nonpositive ℝ K) c) := by
  rw [principalSubringTensorEquiv_one_tmul, finiteSupportGradedEmbedding_eq_initialForm]
  rfl

/-- The identification `P̂ ⊗_K K_fin ≅ RV̂` on a homogeneous pure tensor: `rv(b) ⊗ 1`, for `b` a
principal series of exact degree `α`, maps to the initial form of `b`. -/
theorem principalSubringTensorEquiv_of_tmul_one_eq_initialForm
    {α : NatOrdinal} (b : Nonpositive ℝ K)
    (hb : Berarducci.ordinalValue b < ω^ (α + 1))
    (hprin : IsPrincipal b)
    (hdeg : ((b : Nonpositive ℝ K) : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal)) :
    principalSubringTensorEquiv K
        ((DirectSum.of (Berarducci.PrincipalComponent K) α
          (Berarducci.principalComponentMk α b hb)) ⊗ₜ 1) =
      (degreeValuation K).initialForm b := by
  classical
  have hbLe : ((b : Nonpositive ℝ K) : K⟦ℝ⟧).degree ≤ (α : WithBot NatOrdinal) := hdeg.le
  -- The homogeneous class corresponds to the degree-graded class of the same representative.
  have hclassPrin : Berarducci.IsPrincipalDegreeClass α
      (Berarducci.degreeLayerMk α b hbLe) := by
    rw [Berarducci.isPrincipalDegreeClass_iff]
    exact Or.inr ⟨b, hprin, hdeg, rfl⟩
  have hA : Berarducci.principalComponentToHahnDegreeLayer K α
      (Berarducci.principalComponentMk α b hb) =
      Berarducci.degreeLayerMk α b hbLe := by
    have hproj : Berarducci.degreeLayerToPrincipalComponent K α
        (Berarducci.degreeLayerMk α b hbLe) =
        Berarducci.principalComponentMk α b hb :=
      Berarducci.degreeLayerToPrincipalComponent_mk α b hbLe
    rw [← hproj]
    exact
      Berarducci.principalComponentToHahnDegreeLayer_degreeLayerToPrincipalComponent_of_isPrincipal
        α _ hclassPrin
  change principalSubringTensorEquiv K (_ ⊗ₜ[K] 1) = _
  rw [principalSubringTensorEquiv_tmul_one, Berarducci.principalSubringEmbedding_of, hA]
  -- The degree-graded class of the representative is its initial form.
  rw [Berarducci.degreeLayerMk_eq_componentMk, ← MaxAddDegree.homogeneousMk_apply,
    ← MaxAddDegree.initialForm_eq_homogeneousMk_of_componentMk_ne_zero]
  intro h0
  rw [MaxAddDegree.componentMk_eq_zero_iff] at h0
  have hvalue : degreeValuation K b = ((b : Nonpositive ℝ K) : K⟦ℝ⟧).degree :=
    degreeValuation_apply b
  rw [hvalue, hdeg] at h0
  exact lt_irrefl _ h0

end Berarducci
