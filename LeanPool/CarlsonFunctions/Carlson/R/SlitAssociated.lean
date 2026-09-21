/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.AssociatedDependence
public import LeanPool.CarlsonFunctions.Carlson.R.SlitRecurrence

/-!
# Polynomial relations on the full slit domain

The polynomial coefficients of an associated relation are entire in the nodes.
Consequently the same coefficients that work on right-half-plane nodes work on
the whole product slit plane. This extends Carlson's relation 8.4-1 and Theorem
8.4-3 without changing their coefficients or introducing parameter exceptions.

The existential coefficients of Theorem 8.4-3 are still chosen for fixed exponent
and Dirichlet parameters; no polynomial or analytic dependence of those witnesses
on the parameters is claimed.
-/

open Complex Set
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Carlson's Theorem 8.4-3 for all complex parameters and slit-plane nodes.
Nontriviality is polynomial nontriviality, not a pointwise assertion. The empty
index type is included through the existing entire-parameter theorem. -/
theorem exists_polynomial_relation_associatedRSlit
    (t : ℂ) (b : ι → ℂ)
    (s : Fin (Fintype.card ι + 1) → CarlsonRAssociatedShift ι) :
    ∃ A : Fin (Fintype.card ι + 1) → MvPolynomial ι ℂ,
      (∃ j, A j ≠ 0) ∧
      ∀ (z : ι → ℂ), z ∈ carlsonRSlitDomain →
        ∑ j, (A j).eval z *
          regCarlsonRSlit ((s j).exponentValue t) ((s j).parameterValue b) z = 0 := by
  obtain ⟨A, hA, hrel⟩ := exists_polynomial_relation_associatedRContinued t b s
  exact ⟨A, hA, fun _ hz => polynomial_relation_regCarlsonRSlit_of_right
    Finset.univ A _ _ hrel hz⟩

end DirichletTransform
