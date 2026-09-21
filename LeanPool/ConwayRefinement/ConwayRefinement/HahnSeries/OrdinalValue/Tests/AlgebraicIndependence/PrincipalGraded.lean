/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.PrincipalGraded

/-!
# API checks for the finite-degree part `P̂_{<ω}` and the quotient `P̂/I`

The approach-zero series supplies a nonzero class in `P_1`. Its homogeneous realization belongs
to `(P̂_{<ω})₊`, whereas a nonzero scalar in `P_0` belongs to `P̂_{<ω}` but not to `(P̂_{<ω})₊`.
These two examples separate the ideal of positive degree from both the zero ideal and all of
`P̂_{<ω}`.

The same degree-one class remains nonzero modulo the decomposables because
`(P̂_{<ω})₊² ∩ P_1 = 0`. Its nonzero square belongs to `(P̂_{<ω})₊² ∩ P_2` and vanishes in
`P_2 / ((P̂_{<ω})₊² ∩ P_2)`. These examples distinguish the decomposables from both zero and the
whole component. They also show that the minimal system `𝓑` has a member of degree one, so the
polynomial evaluation statements are nonvacuous. Surjectivity is then exercised on an element
having both nonzero scalar and positive homogeneous parts.

Finally, a nonzero homogeneous class in degree `ω` is excluded from `P̂_{<ω}`, distinguishing
`P̂_{<ω}` from `P̂`.
-/

public noncomputable section

namespace Tests

open scoped DirectSum HahnSeries NatOrdinal

private theorem approachZero_ordinalValue_bound_for_finiteDegree :
    Berarducci.ordinalValue approachZeroNonpositive <
      ω^ (((1 : ℕ) : NatOrdinal) + 1) := by
  rw [Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
    approachZero_degree_eq_one]
  rw [Nat.cast_one]
  exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one (1 : NatOrdinal))

/-- The nonzero degree-one principal class represented by the approach-zero series. -/
def finiteDegreeApproachZeroComponent :
    Berarducci.PrincipalComponent ℚ ((1 : ℕ) : NatOrdinal) :=
  Berarducci.principalComponentMk ((1 : ℕ) : NatOrdinal) approachZeroNonpositive
    approachZero_ordinalValue_bound_for_finiteDegree

theorem finiteDegreeApproachZeroComponent_ne_zero :
    finiteDegreeApproachZeroComponent ≠ 0 := by
  intro hzero
  rw [finiteDegreeApproachZeroComponent] at hzero
  have hlt := (Berarducci.principalComponentMk_eq_zero_iff
    ((1 : ℕ) : NatOrdinal) approachZeroNonpositive
      approachZero_ordinalValue_bound_for_finiteDegree).mp hzero
  rw [Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
    approachZero_degree_eq_one] at hlt
  rw [Nat.cast_one] at hlt
  exact (lt_irrefl _) hlt

/-- The approach-zero class regarded as a homogeneous element of `P̂_{<ω}`. -/
def finiteDegreeApproachZeroElement :
    Berarducci.principalFiniteDegreePart ℚ :=
  Berarducci.finiteDegreeOf ℚ 1
    finiteDegreeApproachZeroComponent

/-- The degree-one fixture belongs to `(P̂_{<ω})₊` and remains nonzero in `P̂_{<ω}`. -/
theorem finiteDegreeApproachZeroElement_positive_nonzero :
    finiteDegreeApproachZeroElement ∈
        Berarducci.positiveFinitePrincipalIdeal ℚ ∧
      finiteDegreeApproachZeroElement ≠ 0 := by
  constructor
  · rw [Berarducci.mem_positiveFinitePrincipalIdeal_iff_component_zero,
      finiteDegreeApproachZeroElement,
      Berarducci.coe_finiteDegreeOf,
      DirectSum.of_apply]
    simp
  · intro hzero
    apply finiteDegreeApproachZeroComponent_ne_zero
    apply Berarducci.finiteDegreeOf_injective ℚ 1
    rw [map_zero]
    exact hzero

private theorem principalComponentScalarOne_ne_zero :
    Berarducci.principalComponentScalarHom ℚ (1 : ℚ) ≠ 0 := by
  rw [Berarducci.principalComponentScalarHom_apply]
  intro hzero
  have hlt := (Berarducci.principalComponentMk_eq_zero_iff 0
    ((HahnSeries.Nonpositive.C : ℚ →+* Berarducci.Series ℚ) 1)
      (Berarducci.ordinalValue_C_lt_wpow_one 1)).mp hzero
  rw [Berarducci.ordinalValue_C_of_ne one_ne_zero,
    NatOrdinal.wpow_zero] at hlt
  exact (lt_irrefl _) hlt

/-- The nonzero scalar one, represented homogeneously in degree zero of `P̂_{<ω}`. -/
def finiteDegreeScalarOne :
    Berarducci.principalFiniteDegreePart ℚ :=
  1

/-- The scalar fixture belongs to `P̂_{<ω}` but not to its ideal `(P̂_{<ω})₊` of positive degree. -/
theorem finiteDegreeScalarOne_not_mem_positive :
    finiteDegreeScalarOne ∉
      Berarducci.positiveFinitePrincipalIdeal ℚ := by
  rw [Berarducci.mem_positiveFinitePrincipalIdeal_iff_component_zero,
    finiteDegreeScalarOne]
  change (1 : Berarducci.PrincipalSubring ℚ) 0 ≠ 0
  rw [← map_one (algebraMap ℚ (Berarducci.PrincipalSubring ℚ)),
    Berarducci.principalSubring_algebraMap_apply, DirectSum.of_apply]
  simp

/-- The nonzero degree-one class in the quotient `P_1 / ((P̂_{<ω})₊² ∩ P_1)`. -/
def finiteDegreeApproachZeroIndecomposable :
    Berarducci.PrincipalIndecomposableQuotient ℚ 1 :=
  Berarducci.principalIndecomposableMk ℚ 1
    finiteDegreeApproachZeroComponent

/-- The approach-zero class survives modulo the decomposables, as `(P̂_{<ω})₊² ∩ P_1 = 0`. -/
theorem finiteDegreeApproachZeroIndecomposable_ne_zero :
    finiteDegreeApproachZeroIndecomposable ≠ 0 := by
  rw [finiteDegreeApproachZeroIndecomposable, ne_eq,
    Berarducci.principalIndecomposableMk_eq_zero_iff,
    Berarducci.decomposablePrincipalComponent_one, Submodule.mem_bot]
  exact finiteDegreeApproachZeroComponent_ne_zero

/-- The square of the approach-zero principal class, in degree two. -/
def finiteDegreeApproachZeroSquare :
    Berarducci.PrincipalComponent ℚ ((2 : ℕ) : NatOrdinal) :=
  Berarducci.principalComponentMulNat ℚ 1 1
    finiteDegreeApproachZeroComponent
    finiteDegreeApproachZeroComponent

/-- The square is a nonzero decomposable vector: it lies in `(P̂_{<ω})₊² ∩ P_2`. -/
theorem finiteDegreeApproachZeroSquare_mem_decomposable_ne_zero :
    finiteDegreeApproachZeroSquare ∈
        Berarducci.decomposablePrincipalComponent ℚ 2 ∧
      finiteDegreeApproachZeroSquare ≠ 0 := by
  constructor
  · exact Berarducci.principalComponentMulNat_mem_decomposable
      (i := 1) (j := 1) (Nat.zero_lt_succ 0) (Nat.zero_lt_succ 0)
      finiteDegreeApproachZeroComponent
      finiteDegreeApproachZeroComponent
  · exact Berarducci.principalComponentMulNat_ne_zero
      finiteDegreeApproachZeroComponent_ne_zero
      finiteDegreeApproachZeroComponent_ne_zero

/-- The same nonzero decomposable square vanishes in `P_2 / ((P̂_{<ω})₊² ∩ P_2)`. -/
theorem finiteDegreeApproachZeroSquare_indecomposable_eq_zero :
    Berarducci.principalIndecomposableMk ℚ 2
      finiteDegreeApproachZeroSquare = 0 := by
  rw [Berarducci.principalIndecomposableMk_eq_zero_iff]
  exact finiteDegreeApproachZeroSquare_mem_decomposable_ne_zero.1

/-- The quotient map `π : P̂ → P̂/I` kills the degree-one fixture. -/
theorem finiteDegreeApproachZeroElement_quotient_eq_zero :
    Berarducci.principalFibreMap ℚ
        (finiteDegreeApproachZeroElement :
          Berarducci.PrincipalSubring ℚ) = 0 := by
  rw [Berarducci.principalFibreMap_eq_zero_iff]
  exact Berarducci.coe_mem_principalFibreIdeal
    finiteDegreeApproachZeroElement_positive_nonzero.1

/-- A nonzero homogeneous class in degree `ω` does not belong to `P̂_{<ω}`. -/
theorem infiniteDegreeHomogeneous_not_mem_finite
    (x : Berarducci.PrincipalComponent ℚ (NatOrdinal.of Ordinal.omega0))
    (hx : x ≠ 0) :
    DirectSum.of (Berarducci.PrincipalComponent ℚ)
        (NatOrdinal.of Ordinal.omega0) x ∉
      Berarducci.principalFiniteDegreePart ℚ := by
  intro hmem
  have hfinite :=
    (Berarducci.mem_principalFiniteDegreePart_iff _).mp hmem
  have hcomponent :
      (DirectSum.of (Berarducci.PrincipalComponent ℚ)
        (NatOrdinal.of Ordinal.omega0) x) (NatOrdinal.of Ordinal.omega0) ≠ 0 := by
    rw [DirectSum.of_apply]
    simpa using hx
  exact (lt_irrefl _) (hfinite (NatOrdinal.of Ordinal.omega0) hcomponent)

/-- The minimal system `𝓑` has an element of degree one. -/
theorem exists_minimalSystem_degree_one :
    ∃ x : Berarducci.MinimalSystem ℚ,
      Berarducci.minimalSystemDegree x = 1 := by
  let q := finiteDegreeApproachZeroIndecomposable
  have hq : q ≠ 0 := finiteDegreeApproachZeroIndecomposable_ne_zero
  letI : Nontrivial (Berarducci.PrincipalIndecomposableQuotient ℚ 1) :=
    ⟨⟨q, 0, hq⟩⟩
  obtain ⟨i⟩ := (Berarducci.principalIndecomposableBasis ℚ 1).index_nonempty
  exact ⟨⟨⟨1, by decide⟩, i⟩, rfl⟩

/-- The evaluation `K[X_B : B ∈ 𝓑] → P̂_{<ω}` has a variable `X_B` with `deg B = 1` whose value is
nonzero and of positive degree. -/
theorem exists_finiteDegreePolynomialVariable_degree_one :
    ∃ x : Berarducci.MinimalSystem ℚ,
      Berarducci.minimalSystemDegree x = 1 ∧
        Berarducci.finiteDegreePolynomialEval ℚ (MvPolynomial.X x) ≠ 0 ∧
        Berarducci.finiteDegreePolynomialEval ℚ (MvPolynomial.X x) ∈
          Berarducci.positiveFinitePrincipalIdeal ℚ := by
  obtain ⟨x, hx⟩ := exists_minimalSystem_degree_one
  refine ⟨x, hx, ?_, ?_⟩
  · rw [Berarducci.finiteDegreePolynomialEval_X]
    exact Berarducci.minimalSystemElement_ne_zero x
  · rw [Berarducci.finiteDegreePolynomialEval_X]
    exact Berarducci.minimalSystemElement_mem_positive x

/-- Polynomial evaluation reaches a target with nonzero degree-zero and degree-one parts. -/
theorem exists_finiteDegreePolynomial_scalar_add_approachZero :
    ∃ p : MvPolynomial (Berarducci.MinimalSystem ℚ) ℚ,
      Berarducci.finiteDegreePolynomialEval ℚ p =
        finiteDegreeScalarOne + finiteDegreeApproachZeroElement :=
  Berarducci.finiteDegreePolynomialEval_surjective ℚ _

end Tests
