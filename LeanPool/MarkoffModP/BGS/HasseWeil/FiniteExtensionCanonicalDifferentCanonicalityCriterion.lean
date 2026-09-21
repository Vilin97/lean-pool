/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionCanonicalDifferentGenusBound

/-!
# Canonicality criterion for the finite-extension different divisor

The Corvaja--Zannier development constructs the divisor of the separating
differential `dX` place by place: its finite coefficients are trace-different
multiplicities, and its coefficients above infinity are the different
multiplicity minus twice the ramification index.  The Riemann--Roch library,
on the other hand, defines canonical divisors as maximal vanishing divisors
of nonzero adelic Weil functionals.

This module gives the exact theorem-level reduction between those two
presentations.  It does not assume or package canonicality.  The target is
equivalent to:

* the Riemann--Hurwitz identity for the total trace different; and
* the dimension statement

  `genus K L ≤ finrank K (finiteExtensionRiemannSpace K L Ddiff)`.

Once the degree identity is known, Riemann--Roch proves that this finrank is
already between `g - 1` and `g`.  Thus the exact remaining
trace-residue/Kähler-to-Weil theorem is the displayed lower bound: construct
the Weil functional attached to `dX`, identify its local annihilator with the
trace-different/Kähler module, and thereby close the last one-dimensional
gap.
-/

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open scoped Polynomial

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance canonicalCriterionConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance canonicalCriterionConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) canonicalCriterionPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance canonicalCriterionPolynomialTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance canonicalCriterionConstantPolynomialTower :
    IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- A degree-zero chart divisor has a Riemann--Roch space of dimension at
most one. -/
theorem chart_ell_le_one_of_degree_eq_zero
    [FunctionField.IsFullConstantField K L]
    (D : FunctionField.Chart.DivisorA K L)
    (hdegree : FunctionField.Chart.deg K L D = 0) :
    FunctionField.Chart.ell K L D ≤ 1 := by
  by_cases hell : FunctionField.Chart.ell K L D = 0
  · omega
  · have hpositive : 0 < FunctionField.Chart.ell K L D :=
      Nat.pos_of_ne_zero hell
    obtain ⟨x, heffective⟩ :=
      FunctionField.Chart.exists_effective_add_principal_of_ell_pos
        K L D hpositive
    let P := FunctionField.Chart.principalDivisorA K L (Additive.ofMul x)
    have hdegreeZero : FunctionField.Chart.deg K L (D + P) = 0 := by
      rw [FunctionField.Chart.deg_add,
        FunctionField.Chart.deg_principalDivisorA_eq_zero, hdegree]
      omega
    have hzero : D + P = 0 :=
      FunctionField.Chart.eq_zero_of_effective_deg_zero K L
        heffective hdegreeZero
    have hellAdd := FunctionField.Chart.ell_add_principal K L D x
    change FunctionField.Chart.ell K L (D + P) =
      FunctionField.Chart.ell K L D at hellAdd
    rw [hzero, FunctionField.Chart.ell_zero] at hellAdd
    omega

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- At canonical degree, Riemann--Roch leaves at most a one-dimensional
defect from canonicality. -/
theorem chart_ell_le_genus_of_degree_eq_two_genus_sub_two
    [FunctionField.IsFullConstantField K L]
    (D : FunctionField.Chart.DivisorA K L)
    (hdegree : FunctionField.Chart.deg K L D =
      2 * (FunctionField.Chart.genus K L : ℤ) - 2) :
    FunctionField.Chart.ell K L D ≤ FunctionField.Chart.genus K L := by
  obtain ⟨W, hW⟩ := FunctionField.Chart.exists_isCanonical K L
  have hdegreeDiff : FunctionField.Chart.deg K L (W - D) = 0 := by
    rw [FunctionField.Chart.deg_sub,
      FunctionField.Chart.deg_canonical K L hW, hdegree]
    omega
  have hellDiff : FunctionField.Chart.ell K L (W - D) ≤ 1 :=
    chart_ell_le_one_of_degree_eq_zero K L (W - D) hdegreeDiff
  have hRR := FunctionField.Chart.riemann_roch K L hW D
  rw [hdegree] at hRR
  omega

/-- Canonicality of the explicit different divisor is equivalent to its
canonical degree and canonical Riemann--Roch dimension.  Both conditions are
stated entirely in the exhaustive BGS divisor model. -/
theorem finiteExtensionCanonicalDifferent_isCanonical_iff_degree_finrank
    [FunctionField.IsFullConstantField K L] :
    FunctionField.Chart.IsCanonical K L
        (finiteExtensionDivisorEquivChart K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) ↔
      finiteExtensionDivisorDegree K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) =
          2 * (FunctionField.Chart.genus K L : ℤ) - 2 ∧
        Module.finrank K
            (finiteExtensionRiemannSpace K L
              (finiteExtensionCanonicalDifferentDivisor K L
                (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) =
          FunctionField.Chart.genus K L := by
  let D := finiteExtensionCanonicalDifferentDivisor K L
    (finiteExtensionFiniteDifferentIdeal_ne_bot K L)
  rw [FunctionField.chart_isCanonical_iff_degree_ell]
  rw [← finiteExtensionDivisorDegree_eq_chart K L D]
  change finiteExtensionDivisorDegree K L D = _ ∧
    Module.finrank K (FunctionField.Chart.RRspace K L
      (finiteExtensionDivisorEquivChart K L D)) = _ ↔ _
  rw [← finiteExtensionRiemannSpace_eq_chart K L D]

/-- Once Riemann--Hurwitz supplies the degree identity, canonicality is
equivalent to closing the single remaining Riemann--Roch dimension gap. -/
theorem finiteExtensionCanonicalDifferent_isCanonical_iff_genus_le_finrank_of_degree_eq
    [FunctionField.IsFullConstantField K L]
    (hdegree : finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) =
      2 * (FunctionField.Chart.genus K L : ℤ) - 2) :
    FunctionField.Chart.IsCanonical K L
        (finiteExtensionDivisorEquivChart K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) ↔
      FunctionField.Chart.genus K L ≤
        Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionCanonicalDifferentDivisor K L
              (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) := by
  let D := finiteExtensionCanonicalDifferentDivisor K L
    (finiteExtensionFiniteDifferentIdeal_ne_bot K L)
  have hdegreeChart : FunctionField.Chart.deg K L
      (finiteExtensionDivisorEquivChart K L D) =
        2 * (FunctionField.Chart.genus K L : ℤ) - 2 := by
    rw [← finiteExtensionDivisorDegree_eq_chart K L D]
    exact hdegree
  have hupperChart : FunctionField.Chart.ell K L
      (finiteExtensionDivisorEquivChart K L D) ≤
        FunctionField.Chart.genus K L :=
    chart_ell_le_genus_of_degree_eq_two_genus_sub_two K L
      (finiteExtensionDivisorEquivChart K L D) hdegreeChart
  have hupper : Module.finrank K (finiteExtensionRiemannSpace K L D) ≤
      FunctionField.Chart.genus K L := by
    rw [finiteExtensionRiemannSpace_eq_chart]
    exact hupperChart
  rw [finiteExtensionCanonicalDifferent_isCanonical_iff_degree_finrank K L]
  constructor
  · rintro ⟨_hdegree, hfinrank⟩
    simpa only [D] using hfinrank.ge
  · intro hlower
    refine ⟨hdegree, ?_⟩
    apply Nat.le_antisymm
    · simpa only [D] using hupper
    · exact hlower

/-- The degree identity leaves at most one unit of uncertainty in the
Riemann--Roch dimension of the explicit different divisor. -/
theorem finiteExtensionCanonicalDifferent_finrank_bounds_of_degree_eq
    [FunctionField.IsFullConstantField K L]
    (hdegree : finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) =
      2 * (FunctionField.Chart.genus K L : ℤ) - 2) :
    (FunctionField.Chart.genus K L : ℤ) - 1 ≤
        (Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionCanonicalDifferentDivisor K L
              (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) : ℤ) ∧
      Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionCanonicalDifferentDivisor K L
              (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) ≤
        FunctionField.Chart.genus K L := by
  let D := finiteExtensionCanonicalDifferentDivisor K L
    (finiteExtensionFiniteDifferentIdeal_ne_bot K L)
  have hdegreeChart : FunctionField.Chart.deg K L
      (finiteExtensionDivisorEquivChart K L D) =
        2 * (FunctionField.Chart.genus K L : ℤ) - 2 := by
    rw [← finiteExtensionDivisorDegree_eq_chart K L D]
    exact hdegree
  have hlowerChart := FunctionField.Chart.riemann_ineq K L
    (finiteExtensionDivisorEquivChart K L D)
  rw [hdegreeChart] at hlowerChart
  have hlowerInt : (FunctionField.Chart.genus K L : ℤ) - 1 ≤
      (FunctionField.Chart.ell K L
        (finiteExtensionDivisorEquivChart K L D) : ℤ) := by
    omega
  have hupperChart :=
    chart_ell_le_genus_of_degree_eq_two_genus_sub_two K L
      (finiteExtensionDivisorEquivChart K L D) hdegreeChart
  change (FunctionField.Chart.genus K L : ℤ) - 1 ≤
      (Module.finrank K (finiteExtensionRiemannSpace K L D) : ℤ) ∧
    Module.finrank K (finiteExtensionRiemannSpace K L D) ≤
      FunctionField.Chart.genus K L
  have hfinrank : Module.finrank K (finiteExtensionRiemannSpace K L D) =
      FunctionField.Chart.ell K L
        (finiteExtensionDivisorEquivChart K L D) := by
    rw [finiteExtensionRiemannSpace_eq_chart]
    rfl
  constructor
  · rw [hfinrank]
    exact hlowerInt
  · rw [hfinrank]
    exact hupperChart

omit [Fintype K] in
/-- The degree half of canonicality is exactly the Riemann--Hurwitz identity
for the finite and infinite trace different. -/
theorem finiteExtensionCanonicalDifferent_degree_eq_two_genus_sub_two_iff
    [FunctionField.IsFullConstantField K L] :
    finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) =
        2 * (FunctionField.Chart.genus K L : ℤ) - 2 ↔
      (finiteExtensionFiniteDifferentDegree K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L) : ℤ) +
          (infinityDifferentDegree K L : ℤ) =
        2 * (Module.finrank (RatFunc K) L : ℤ) +
          2 * (FunctionField.Chart.genus K L : ℤ) - 2 := by
  rw [finiteExtensionCanonicalDifferentDivisor_degree]
  constructor <;> intro h <;> omega

end

end BGS.HasseWeil
