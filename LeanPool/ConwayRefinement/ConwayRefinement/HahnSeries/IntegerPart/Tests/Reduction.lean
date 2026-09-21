/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Tests.ClassTruncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Reduction

/-!
# API checks for LM24 reduction

The zero-`τ` check uses the nonzero boundary monomial from the class-truncation certificate:
`T` retains it while `τ` removes it, so `ρ` must take the zero branch. The nonzero-`τ` check is
polymorphic and verifies that `ρ` selects the quotient construction whenever the open truncation
is nonzero. These checks distinguish both clauses of LM24, Definition 8.2.4.
-/

public noncomputable section

namespace Tests

open HahnSeries FiniteArchimedeanClass

def rationalBoundaryFieldSeries : Nonpositive ℚ ℚ :=
  Nonpositive.single (-1) 5 (by norm_num)

theorem rho_rationalBoundarySeries_eq_T
    (u : HahnEmbedding.ArchimedeanStrata ℚ ℚ) :
    Nonpositive.rho u rationalClass rationalBoundaryFieldSeries =
      Nonpositive.T (K := ℚ) rationalClass rationalBoundaryFieldSeries := by
  apply Nonpositive.rho_of_tau_eq_zero
  apply Subtype.ext
  ext g
  by_cases hg : g = -1
  · subst g
    rw [Nonpositive.coeff_tau_of_not_mem _ _ negOne_not_mem_ball]
    simp
  · have hcoeff : (rationalBoundaryFieldSeries : ℚ⟦ℚ⟧).coeff g = 0 := by
      rw [rationalBoundaryFieldSeries, Nonpositive.coe_single]
      simp [hg]
    by_cases hball : g ∈ ball ℚ rationalClass
    · rw [Nonpositive.coeff_tau_of_mem _ _ hball, hcoeff]
      rfl
    · rw [Nonpositive.coeff_tau_of_not_mem _ _ hball]
      rfl

theorem rho_eq_reductionQuotient_of_tau_ne_zero
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (htau : Nonpositive.tau (K := K) c x ≠ 0) :
    Nonpositive.rho u c x = Nonpositive.reductionQuotient u c x
      (fun hzero ↦ htau ((Nonpositive.tauBall_eq_zero_iff c x).mp hzero)) :=
  Nonpositive.rho_of_tau_ne_zero u c x htau

/-- The fixed-class characterization in LM24, Proposition 8.2.5. -/
theorem rho_fixed_at_containing_class_iff
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (hx : x ≠ 0) (hT : Nonpositive.T (K := K) c x = x) :
    Nonpositive.rho u c x = x ↔
      Nonpositive.tau (K := K) c x = 0 ∨ Nonpositive.tau (K := K) c x = 1 :=
  Nonpositive.rho_eq_self_iff_tau_eq_zero_or_one u c x hx hT

/-- LM24, Proposition 8.2.5 `(3) ↔ (4)` at the leading class. -/
theorem rho_fixed_at_leading_class_iff
    {K G R : Type*}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (u : HahnEmbedding.ArchimedeanStrata K G) (x : Nonpositive G R) (hx : x ≠ 0)
    (horder : (x : R⟦G⟧).order ≠ 0) :
    Nonpositive.rho u (Nonpositive.leadingClass x horder) x = x ↔
      Nonpositive.tau (K := K) (Nonpositive.leadingClass x horder) x = 0 ∨
        Nonpositive.tau (K := K) (Nonpositive.leadingClass x horder) x = 1 :=
  Nonpositive.rho_leadingClass_eq_self_iff_tau_eq_zero_or_one u x hx horder

end Tests
