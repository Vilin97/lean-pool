/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportResidue

/-!
# API checks for the degree-zero residue ring

A two-term nonpositive series belongs to the finite-support subring and has a nonzero coefficient
at exponent `-1`, so this subring cannot be replaced by the constants. The approach-to-zero
series has support order type `ω` and is excluded, so the finite-support subring cannot be replaced
by the whole nonpositive Hahn ring. For any valuation realizing degree, the residue equivalence
sends the two-term series to a nonzero class.
-/

public noncomputable section

open scoped DirectSum HahnSeries

namespace Tests

/-- A nonconstant two-term nonpositive Hahn series. -/
def finiteSupportTwoTerm : HahnSeries.Nonpositive ℝ ℚ :=
  HahnSeries.Nonpositive.C 1 +
    HahnSeries.Nonpositive.single (-1) 1 (by norm_num)

/-- The two-term fixture has a nonzero coefficient at exponent `-1`. -/
theorem finiteSupportTwoTerm_coeff_neg_one :
    (finiteSupportTwoTerm : ℚ⟦ℝ⟧).coeff (-1) = 1 := by
  simp [finiteSupportTwoTerm]

/-- The two-term fixture has constant coefficient one. -/
theorem finiteSupportTwoTerm_coeff_zero :
    (finiteSupportTwoTerm : ℚ⟦ℝ⟧).coeff 0 = 1 := by
  simp [finiteSupportTwoTerm]

/-- The two-term fixture belongs to the finite-support subring. -/
theorem finiteSupportTwoTerm_mem :
    finiteSupportTwoTerm ∈
      (HahnSeries.Nonpositive.finiteSupportSubring :
        Subring (HahnSeries.Nonpositive ℝ ℚ)) := by
  rw [HahnSeries.Nonpositive.mem_finiteSupportSubring_iff]
  apply Set.Finite.subset
    ((Set.finite_singleton 0).union (Set.finite_singleton (-1)))
  intro x hx
  rcases HahnSeries.support_add_subset _ _ hx with hx | hx
  · left
    rw [HahnSeries.Nonpositive.coe_C] at hx
    exact HahnSeries.support_single_subset hx
  · right
    rw [HahnSeries.Nonpositive.coe_single] at hx
    exact HahnSeries.support_single_subset hx

/-- The finite-support subring contains more than the constant series. -/
theorem finiteSupportTwoTerm_not_constant :
    ∀ q : ℚ, finiteSupportTwoTerm ≠ HahnSeries.Nonpositive.C q := by
  intro q h
  have hcoeff := congrArg
    (fun b : HahnSeries.Nonpositive ℝ ℚ ↦ (b : ℚ⟦ℝ⟧).coeff (-1)) h
  have hconstant :
      ((HahnSeries.Nonpositive.C q : HahnSeries.Nonpositive ℝ ℚ) :
          ℚ⟦ℝ⟧).coeff (-1) = 0 := by
    rw [HahnSeries.Nonpositive.coe_C, HahnSeries.C_apply]
    simp
  rw [finiteSupportTwoTerm_coeff_neg_one, hconstant] at hcoeff
  exact one_ne_zero hcoeff

/-- An infinite nonpositive support is not in the finite-support subring. -/
theorem approachZero_not_mem_finiteSupportSubring :
    approachZeroNonpositive ∉
      (HahnSeries.Nonpositive.finiteSupportSubring :
        Subring (HahnSeries.Nonpositive ℝ ℚ)) := by
  rw [HahnSeries.Nonpositive.mem_finiteSupportSubring_iff]
  intro hfinite
  have hlt := HahnSeries.support_finite_iff_supportOrderType_lt_omega.mp hfinite
  rw [coe_approachZeroNonpositive, approachZero_supportOrderType] at hlt
  exact (lt_irrefl Ordinal.omega0) hlt

section Residue

variable (w : MaxAddDegree (HahnSeries.Nonpositive ℝ ℚ) NatOrdinal)
  (hvalue : ∀ b, w b = (b : ℚ⟦ℝ⟧).degree)

/-- The two-term fixture as an element of the finite-support subring. -/
def finiteSupportTwoTermInSubring :
    (HahnSeries.Nonpositive.finiteSupportSubring :
      Subring (HahnSeries.Nonpositive ℝ ℚ)) :=
  ⟨finiteSupportTwoTerm, finiteSupportTwoTerm_mem⟩

/-- The residue equivalence does not kill the nonconstant two-term fixture. -/
theorem finiteSupportTwoTerm_residue_ne_zero :
    HahnSeries.Nonpositive.finiteSupportResidueEquiv w hvalue
        finiteSupportTwoTermInSubring ≠ 0 := by
  intro himage
  have hzero : finiteSupportTwoTermInSubring = 0 := by
    apply (HahnSeries.Nonpositive.finiteSupportResidueEquiv w hvalue).injective
    rw [himage, map_zero]
  have hcoeff := congrArg
    (fun b : HahnSeries.Nonpositive ℝ ℚ ↦ (b : ℚ⟦ℝ⟧).coeff (-1))
    (congrArg Subtype.val hzero)
  simp [finiteSupportTwoTermInSubring, finiteSupportTwoTerm_coeff_neg_one] at hcoeff

/-- The transported `rv` class agrees with the residue isomorphism on the two-term fixture. -/
theorem finiteSupportTwoTerm_rv_residue_compatibility [w.IsMultiplicative] :
    (w.rvEquivHomogeneous (w.rv finiteSupportTwoTerm) : w.AssociatedGraded) =
      w.residueRingHom
        (HahnSeries.Nonpositive.finiteSupportResidueEquiv w hvalue
          finiteSupportTwoTermInSubring) :=
  HahnSeries.Nonpositive.coe_rvEquivHomogeneous_rv_eq_residueRingHom_finiteSupportResidueEquiv
    w hvalue finiteSupportTwoTermInSubring

/-- The RV/residue compatibility includes the bottom-valued zero class. -/
theorem finiteSupportZero_rv_residue_compatibility [w.IsMultiplicative] :
    (w.rvEquivHomogeneous (w.rv (0 : HahnSeries.Nonpositive ℝ ℚ)) :
        w.AssociatedGraded) =
      w.residueRingHom
        (HahnSeries.Nonpositive.finiteSupportResidueEquiv w hvalue
          (0 : HahnSeries.Nonpositive.finiteSupportSubring)) :=
  HahnSeries.Nonpositive.coe_rvEquivHomogeneous_rv_eq_residueRingHom_finiteSupportResidueEquiv
    w hvalue 0

end Residue

end Tests
