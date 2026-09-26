/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Primality.Primality

/-!
# API checks for the polynomial presentation of the series ring

The polynomial presentation `K((ℝ^{≤0})) = K_fin[b_i]` of the whole series ring over its subring
`K_fin = K(ℝ^{≤0})` of series with finite support [LM24, Not. 2.1.5], on the lifts `b_i` of a
minimal system of homogeneous generators of `P̂`, differs from the presentation
`S = K_fin[b_B : B ∈ 𝓑]` of the ring of series of finite degree in its scope: there every value
`F(b_𝓑)` has degree below `ω`, here every series, of whatever degree, is a value `F(b)`. The
checks record this separation, the two directions of the isomorphism on the variables, and that
the lifts are not scalars: `b_i` has the positive degree `wt i`, hence infinite support. The
factorisation consequences are recorded on an arbitrary series: every series is primal, and an
irreducible series is prime with no hypothesis on its degree or support.
-/

public noncomputable section

namespace Tests

open HahnSeries HahnSeries.Nonpositive Berarducci OrdinalGraded

open scoped MaxAddDegree

universe v w

variable {K : Type v} [Field K] [CharZero K]
variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}
variable (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
  (σ : GeneratorLifts wt x)
include hx

/-- Every series of degree at least `ω` is a value `F(b)`: the presentation covers what the
presentation of `S` leaves out. -/
theorem exists_evalAtLifts_eq_of_omega_le_degree {t : Series K}
    (_ : (NatOrdinal.of Ordinal.omega0 : WithBot NatOrdinal) ≤ (t : K⟦ℝ⟧).degree) :
    ∃ F : MvPolynomial ι (FiniteSupportRing (K := K)), evalAtLifts σ F = t :=
  evalAtLifts_surjective hx σ t

/-- The isomorphism `K_fin[X_i] ≅ K((ℝ^{≤0}))` sends `X_i` to `b_i`. -/
theorem polynomialRingEquiv_X (i : ι) : polynomialRingEquiv hx σ (MvPolynomial.X i) = σ.lift i := by
  rw [polynomialRingEquiv_apply, evalAtLifts_X]

/-- The inverse isomorphism `K((ℝ^{≤0})) ≅ K_fin[X_i]` sends `b_i` to `X_i`. -/
theorem seriesPolynomialRingEquiv_lift (i : ι) :
    seriesPolynomialRingEquiv hx σ (σ.lift i) = MvPolynomial.X i := by
  rw [← evalAtLifts_X σ i, seriesPolynomialRingEquiv_evalAtLifts]

omit hx in
/-- `deg b_i = wt i`, and `wt i` is positive. -/
theorem degree_lift_pos (hwt : ∀ i, wt i ≠ 0) (i : ι) :
    degreeValuation K (σ.lift i) = (wt i : WithBot NatOrdinal) ∧
      0 < degreeValuation K (σ.lift i) := by
  refine ⟨σ.degreeValuation_lift i, ?_⟩
  rw [σ.degreeValuation_lift i, ← WithBot.coe_zero, WithBot.coe_lt_coe]
  exact pos_iff_ne_zero.mpr (hwt i)

/-- A lift `b_i` has infinite support: the presentation is not the scalar ring `K_fin`. -/
theorem lift_support_infinite (i : ι) : ¬ ((σ.lift i : Series K) : K⟦ℝ⟧).support.Finite := by
  intro hfin
  have hle : degreeValuation K (σ.lift i) ≤ 0 := by
    rw [degreeValuation_apply]
    exact HahnSeries.degree_le_zero_iff.mpr hfin
  exact absurd (lt_of_lt_of_le (degree_lift_pos σ hx.ne_zero i).2 hle) (lt_irrefl _)

omit hx

/-- Every series is primal, with no hypothesis on its degree or support. -/
theorem isPrimal' (a : Series K) : IsPrimal a :=
  Berarducci.isPrimal a

/-- An irreducible series of degree at least `ω` is prime: the hypothesis `deg a < ω` of the
finite-degree theorem is gone. -/
theorem prime_of_irreducible_of_omega_le_degree {a : Series K} (ha : Irreducible a)
    (_ : (NatOrdinal.of Ordinal.omega0 : WithBot NatOrdinal) ≤ (a : K⟦ℝ⟧).degree) : Prime a :=
  prime_of_irreducible ha

end Tests
