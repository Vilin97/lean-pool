/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.ClassTruncation

/-!
# API checks for Archimedean-class truncations

In the Archimedean exponent group `ℚ`, the class of `-1` is the unique nonzero class. At that
class, `T` keeps the boundary monomial while `tau` removes it. This distinguishes LM24's weak and
strict class cuts; an ordinary exponent truncation at the representative `-1` would not provide
the same class-invariant interface.
-/

public noncomputable section

namespace Tests

open HahnSeries FiniteArchimedeanClass

def rationalClass : FiniteArchimedeanClass ℚ :=
  FiniteArchimedeanClass.mk (-1 : ℚ) (by norm_num)

def rationalBoundarySeries : Nonpositive ℚ ℤ :=
  Nonpositive.single (-1) 5 (by norm_num)

theorem negOne_mem_closedBall : (-1 : ℚ) ∈ closedBall ℚ rationalClass := by
  rw [FiniteArchimedeanClass.mem_closedBall_iff]
  intro h
  simp [rationalClass]

theorem negOne_not_mem_ball : (-1 : ℚ) ∉ ball ℚ rationalClass := by
  rw [FiniteArchimedeanClass.mem_ball_iff]
  simp only [not_forall]
  exact ⟨by norm_num, by simp [rationalClass]⟩

theorem classTruncation_boundary_coefficients :
    ((Nonpositive.T (K := ℚ) rationalClass rationalBoundarySeries :
      Nonpositive ℚ ℤ) : ℤ⟦ℚ⟧).coeff (-1) = 5 ∧
    ((Nonpositive.tau (K := ℚ) rationalClass rationalBoundarySeries :
      Nonpositive ℚ ℤ) : ℤ⟦ℚ⟧).coeff (-1) = 0 := by
  constructor
  · rw [Nonpositive.coeff_T_of_mem _ _ negOne_mem_closedBall]
    simp [rationalBoundarySeries]
  · rw [Nonpositive.coeff_tau_of_not_mem _ _ negOne_not_mem_ball]

/-- The leading-class API retains a nonconstant boundary monomial. -/
theorem T_rationalBoundarySeries_leadingClass :
    Nonpositive.T (K := ℚ)
        (Nonpositive.leadingClass rationalBoundarySeries (by
          rw [rationalBoundarySeries, Nonpositive.coe_single,
            HahnSeries.order_single (by norm_num)]
          norm_num))
        rationalBoundarySeries = rationalBoundarySeries :=
  Nonpositive.T_leadingClass rationalBoundarySeries (by
    rw [rationalBoundarySeries, Nonpositive.coe_single,
      HahnSeries.order_single (by norm_num)]
    norm_num)

end Tests
