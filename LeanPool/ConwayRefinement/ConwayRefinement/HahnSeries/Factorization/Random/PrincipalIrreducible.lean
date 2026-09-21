/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.HomogeneousPrime
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.LeastTerm
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubring
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedValuation

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGradedDomain
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.OrdinalValueDegree

/-!
# Irreducibility at a power of `ω`

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility of generalised power series* (2024),
§ 1, deduce from Berarducci's `P_α · P_β ⊆ P_{α ⊕ β}` that every principal series of order type
`ω ^ (ω ^ α)` is irreducible, because there are no nonzero `β, γ` with `β ⊕ γ = ω ^ α`. This
module is that deduction, carried out on the graded ring rather than on series.

Their statement is the stronger one: it concludes irreducibility in `K((ℝ^{≤ 0}))` itself, where
this concludes it for the class in `P̂`. LM24, Theorem E is stronger again, covering order type
`ω ^ (ω ^ α) +̂ β` for every `β < ω ^ (ω ^ α)` and every `α`, not only the additively principal
grades. Nothing here is new; the point of formalizing it is that the grade-splitting argument is
general, and lives in `ConwayRefinement.Algebra.DirectSum.HomogeneousPrime` next to the
primality lift it is the easy counterpart of.
-/

open scoped DirectSum NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci

variable {K : Type v} [Field K]

theorem not_isUnit_of_grade_ne_zero {alpha : NatOrdinal} (halpha : alpha ≠ 0)
    (X : PrincipalComponent K alpha) :
    ¬ IsUnit (DirectSum.of (PrincipalComponent K) alpha X) := by
  intro hunit
  obtain ⟨y, hy⟩ := hunit.exists_right_inv
  have hzero : (DirectSum.of (PrincipalComponent K) alpha X * y) 0 = 0 := by
    apply DirectSum.of_mul_apply_eq_zero_of_not_exists
    rintro ⟨j, hj⟩
    exact halpha (NatOrdinal.add_eq_zero_iff.mp hj).1
  rw [hy] at hzero
  apply (one_ne_zero : (1 : PrincipalSubring K) ≠ 0)
  rw [DirectSum.one_def] at hzero ⊢
  simp only [DirectSum.of_apply, dif_pos] at hzero
  rw [show (GradedMonoid.GOne.one : PrincipalComponent K 0) = 0 by simpa using hzero, map_zero]

/-- A nonzero class of grade zero is a unit: grade zero is the scalar field. -/
theorem isUnit_of_grade_zero (u : PrincipalComponent K 0) (hu : u ≠ 0) :
    IsUnit (DirectSum.of (PrincipalComponent K) 0 u) := by
  obtain ⟨c, rfl⟩ := principalComponentScalarHom_surjective K u
  have hc : c ≠ 0 := by
    intro hzero
    exact hu (by rw [hzero, map_zero])
  have heq : DirectSum.of (PrincipalComponent K) 0 (principalComponentScalarHom K c) =
      algebraMap K (PrincipalSubring K) c := rfl
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map (algebraMap K (PrincipalSubring K))

variable [CharZero K] in
/-- FLLM24, § 1: a nonzero homogeneous class at a power of `ω` is irreducible, here in `P̂`: the
products of nonzero homogeneous classes are nonzero because the ordinal value is multiplicative
(Berarducci, Theorem 9.7). -/
theorem irreducible_of_isAdditivelyPrincipal
    {alpha : NatOrdinal} (halpha : Ordinal.IsAdditivelyPrincipal alpha.val)
    (X : PrincipalComponent K alpha) (hX : X ≠ 0) :
    Irreducible (DirectSum.of (PrincipalComponent K) alpha X) := by
  have halphaNe : alpha ≠ 0 := by
    obtain ⟨e, he⟩ := Ordinal.isAdditivelyPrincipal_iff.mp halpha
    intro hzero
    rw [hzero] at he
    exact Ordinal.opow_ne_zero e Ordinal.omega0_ne_zero (by simpa using he.symm)
  refine DirectSum.irreducible_of_homogeneous_of_grade_not_split
    (PrincipalComponent K) X
    (fun u v hu hv ↦ MaxAddDegree.componentMul_ne_zero
      (ordinalValueDegreeValuation K) u v hu hv)
    (fun _ ↦ zero_le) isUnit_of_grade_zero
    (fun j k hjk ↦ ?_) ?_ (not_isUnit_of_grade_ne_zero halphaNe X)
  · rcases eq_or_ne j 0 with h | h
    · exact Or.inl h
    · rcases eq_or_ne k 0 with h' | h'
      · exact Or.inr h'
      · exact absurd hjk (NatOrdinal.add_ne_of_isAdditivelyPrincipal halpha h h')
  · intro hzero
    exact hX (DirectSum.of_injective alpha (by rw [hzero, map_zero]))

end FLLM24

end
