/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeInitialForm

/-!
# Degree-zero scalar maps

A scalar map whose nonzero values all have degree zero induces a ring homomorphism from the
scalar ring to the associated graded ring, sending each scalar to its initial form. Its image is
represented in grade zero. This is how the scalars of a subalgebra act on a fibre associated
graded ring.
-/

open scoped MaxAddDegree

universe u v w

public noncomputable section

namespace MaxAddDegree

variable {R : Type u} {M : Type v} {k : Type w} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]

private def degreeZeroScalarFiltration [CommRing k]
    (ν : MaxAddDegree R M) (ι : k →+* R)
    (hdegree : ∀ c : k, c ≠ 0 → ν (ι c) = 0) (c : k) :
    ν.filtrationLE 0 :=
  ⟨ι c, (ν.mem_filtrationLE_iff 0 _).mpr <| by
    by_cases hc : c = 0
    · subst c
      simp
    · rw [hdegree c hc, WithBot.coe_zero]⟩

/-- The ring homomorphism from degree-zero scalars to their grade-zero initial classes. -/
def degreeZeroScalarHom [CommRing k]
    (ν : MaxAddDegree R M) (ι : k →+* R)
    (hdegree : ∀ c : k, c ≠ 0 → ν (ι c) = 0) :
    k →+* ν.AssociatedGraded where
  toFun c := ν.homogeneousMk 0 (degreeZeroScalarFiltration ν ι hdegree c)
  map_zero' := by
    change ν.homogeneousMk 0 (degreeZeroScalarFiltration ν ι hdegree 0) = 0
    have hzero : degreeZeroScalarFiltration ν ι hdegree 0 = 0 := by
      apply Subtype.ext
      exact ι.map_zero
    rw [hzero]
    exact (ν.homogeneousMk 0).map_zero
  map_one' := by
    rw [ν.homogeneousMk_apply]
    change DirectSum.of ν.Component 0
        (ν.componentMk 0 (degreeZeroScalarFiltration ν ι hdegree 1)) =
      DirectSum.of ν.Component 0 ν.componentOne
    apply congrArg (DirectSum.of ν.Component 0)
    rw [ν.componentOne_eq_componentMk]
    apply congrArg (ν.componentMk 0)
    apply Subtype.ext
    exact ι.map_one
  map_add' c d := by
    change ν.homogeneousMk 0 (degreeZeroScalarFiltration ν ι hdegree (c + d)) =
      ν.homogeneousMk 0 (degreeZeroScalarFiltration ν ι hdegree c) +
        ν.homogeneousMk 0 (degreeZeroScalarFiltration ν ι hdegree d)
    rw [← (ν.homogeneousMk 0).map_add]
    apply congrArg (ν.homogeneousMk 0)
    apply Subtype.ext
    exact ι.map_add c d
  map_mul' c d := by
    rw [ν.homogeneousMk_mul, ν.homogeneousMk_apply, ν.homogeneousMk_apply]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply Sigma.ext (zero_add 0).symm
    apply ν.componentMk_heq_of_grade_eq_of_coe_eq (zero_add 0).symm
    rw [ν.coe_mulFiltrationLE]
    exact ι.map_mul c d

/-- Evaluation of the degree-zero scalar homomorphism on any grade-zero filtration
representative of the scalar's image. -/
theorem degreeZeroScalarHom_apply [CommRing k]
    (ν : MaxAddDegree R M) (ι : k →+* R)
    (hdegree : ∀ c : k, c ≠ 0 → ν (ι c) = 0) (c : k)
    (x : ν.filtrationLE 0) (hx : (x : R) = ι c) :
    degreeZeroScalarHom ν ι hdegree c = ν.homogeneousMk 0 x := by
  change ν.homogeneousMk 0 (degreeZeroScalarFiltration ν ι hdegree c) = _
  refine congrArg (ν.homogeneousMk 0) (Subtype.ext ?_)
  exact hx.symm

/-- The degree-zero scalar homomorphism sends each scalar to its initial form. -/
theorem degreeZeroScalarHom_apply_eq_initialForm [CommRing k]
    (ν : MaxAddDegree R M) (ι : k →+* R)
    (hdegree : ∀ c : k, c ≠ 0 → ν (ι c) = 0) (c : k) :
    degreeZeroScalarHom ν ι hdegree c = ν.initialForm (ι c) := by
  by_cases hc : c = 0
  · subst c
    rw [(degreeZeroScalarHom ν ι hdegree).map_zero, ι.map_zero, ν.initialForm_zero]
  · rw [degreeZeroScalarHom_apply ν ι hdegree c ⟨ι c, (ν.mem_filtrationLE_iff 0 _).mpr
      (hdegree c hc).le⟩ rfl]
    exact ν.homogeneousMk_eq_initialForm_of_degree_eq _ (hdegree c hc)

end MaxAddDegree
