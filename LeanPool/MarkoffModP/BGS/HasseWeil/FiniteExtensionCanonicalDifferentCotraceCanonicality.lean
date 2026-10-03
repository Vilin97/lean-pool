/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionCanonicalDifferentCotrace
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionCanonicalDifferentCanonicalityCriterion

/-!
# Canonicality from cotrace and the different degree

The cotrace construction proves that the explicit different divisor is a
vanishing divisor of a nonzero Weil differential.  This file records the
exact consequence of that inclusion: once the Riemann--Hurwitz degree identity
is known, equality of degrees forces equality with the maximal vanishing
divisor.  Thus canonicality no longer needs a separate Riemann--Roch dimension
hypothesis.

The degree identity remains an explicit premise; it is not derived or hidden
here.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open scoped Polynomial

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- The algebra structure from `K` to `L` used in the finite extension canonical different
    cotrace canonicality construction. -/
local instance cotraceCanonicalityConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance cotraceCanonicalityConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The algebra structure from `K[X]` to `L` used in the finite extension canonical
    different cotrace canonicality construction. -/
local instance (priority := 10) cotraceCanonicalityPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance cotraceCanonicalityPolynomialTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance cotraceCanonicalityConstantPolynomialTower :
    IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

omit [Fintype K] in
/-- The cotrace inclusion and the Riemann--Hurwitz degree identity identify
the explicit different divisor with a canonical divisor. -/
theorem finiteExtensionCanonicalDifferent_isCanonical_of_degree_eq
    [MarkoffRiemannRoch.FunctionField.IsFullConstantField K L]
    (hdegree : finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) =
      2 * (MarkoffRiemannRoch.FunctionField.Chart.genus K L : ℤ) - 2) :
    MarkoffRiemannRoch.FunctionField.Chart.IsCanonical K L
      (finiteExtensionDivisorEquivChart K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) := by
  let D := finiteExtensionDivisorEquivChart K L
    (finiteExtensionCanonicalDifferentDivisor K L
      (finiteExtensionFiniteDifferentIdeal_ne_bot K L))
  obtain ⟨ω, hω, hDle⟩ :=
    finiteExtensionCanonicalDifferent_le_divOmega K L
  have hcanonicalOmega : MarkoffRiemannRoch.FunctionField.Chart.IsCanonical K L
      (MarkoffRiemannRoch.FunctionField.Chart.WeilDifferential.divOmega ω hω) :=
    ⟨ω, hω, rfl⟩
  have hdegOmega : MarkoffRiemannRoch.FunctionField.Chart.deg K L
      (MarkoffRiemannRoch.FunctionField.Chart.WeilDifferential.divOmega ω hω) =
        2 * (MarkoffRiemannRoch.FunctionField.Chart.genus K L : ℤ) - 2 :=
    MarkoffRiemannRoch.FunctionField.Chart.deg_canonical K L hcanonicalOmega
  have hdegD : MarkoffRiemannRoch.FunctionField.Chart.deg K L D =
      2 * (MarkoffRiemannRoch.FunctionField.Chart.genus K L : ℤ) - 2 := by
    rw [← finiteExtensionDivisorDegree_eq_chart]
    exact hdegree
  have heq : D = MarkoffRiemannRoch.FunctionField.Chart.WeilDifferential.divOmega ω hω :=
    MarkoffRiemannRoch.FunctionField.Chart.eq_of_le_of_deg_le K L hDle (by
      rw [hdegOmega, hdegD])
  exact ⟨ω, hω, heq.symm⟩

omit [Fintype K] in
/-- Consequently, a degree upper bound gives a genus upper bound once the
Riemann--Hurwitz degree identity is supplied. -/
theorem finiteExtension_genus_le_budget_of_cotrace_and_degree_eq
    [MarkoffRiemannRoch.FunctionField.IsFullConstantField K L]
    (budget : ℕ)
    (hdegreeEq : finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) =
      2 * (MarkoffRiemannRoch.FunctionField.Chart.genus K L : ℤ) - 2)
    (hdegreeLe : finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) ≤
      2 * (budget : ℤ) - 2) :
    MarkoffRiemannRoch.FunctionField.genus K L ≤ budget := by
  exact finiteExtension_genus_le_budget_of_canonicalDifferent_isCanonical
    K L budget
      (finiteExtensionCanonicalDifferent_isCanonical_of_degree_eq
        K L hdegreeEq)
      hdegreeLe

end

end BGS.HasseWeil
