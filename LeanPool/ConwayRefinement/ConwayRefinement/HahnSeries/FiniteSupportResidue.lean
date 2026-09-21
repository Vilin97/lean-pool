/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.Residue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DegreeValuation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupport

/-!
# The degree-zero residue ring

For a max-additive degree on nonpositive real Hahn series whose value is degree, the nonpositive
subring is the finite-support subring and the negative ideal is zero. The residue map is
therefore a ring isomorphism from finite-support nonpositive Hahn series. This is the proof of
LM24, Proposition 5.1.1, stated for any degree whose value is Hahn-series degree.
-/

universe v

public noncomputable section

open scoped DirectSum

namespace HahnSeries.Nonpositive

variable {K : Type v} [CommRing K]

variable (w : MaxAddDegree (Nonpositive ℝ K) NatOrdinal)

/-- A degree function equal to the Hahn-series degree has the finite-support subring as its
nonpositive subring. -/
theorem nonpositiveSubring_eq_finiteSupportSubring_of_value_eq_degree
    (hvalue : ∀ b, w b = (b : K⟦ℝ⟧).degree) :
    w.nonpositiveSubring = finiteSupportSubring := by
  ext b
  rw [MaxAddDegree.mem_nonpositiveSubring_iff,
    mem_finiteSupportSubring_iff, hvalue, HahnSeries.degree_le_zero_iff]

/-- A degree function equal to the Hahn-series degree has zero strictly-negative ideal. -/
theorem negativeIdeal_eq_bot_of_value_eq_degree
    (hvalue : ∀ b, w b = (b : K⟦ℝ⟧).degree) :
    w.negativeIdeal = ⊥ := by
  ext b
  rw [MaxAddDegree.mem_negativeIdeal_iff, Ideal.mem_bot, hvalue,
    HahnSeries.degree_lt_zero_iff]
  simp

/-- The residue map of a degree function equal to the Hahn-series degree is injective. -/
theorem residueMap_injective_of_value_eq_degree
    (hvalue : ∀ b, w b = (b : K⟦ℝ⟧).degree) :
    Function.Injective w.residueMap := by
  apply (RingHom.injective_iff_ker_eq_bot w.residueMap).mpr
  rw [w.residueMap_ker, negativeIdeal_eq_bot_of_value_eq_degree w hvalue]

/-- LM24, Proposition 5.1.1 in the grade-zero-component presentation of the residue ring. -/
def finiteSupportResidueEquiv
    (hvalue : ∀ b, w b = (b : K⟦ℝ⟧).degree) :
    (finiteSupportSubring : Subring (Nonpositive ℝ K)) ≃+* w.ResidueRing :=
  (RingEquiv.subringCongr
      (nonpositiveSubring_eq_finiteSupportSubring_of_value_eq_degree w hvalue).symm).trans
    (RingEquiv.ofBijective w.residueMap
      ⟨residueMap_injective_of_value_eq_degree w hvalue, w.residueMap_surjective⟩)

/-- The residue-ring equivalence is the restriction of the residue map. -/
@[simp]
theorem finiteSupportResidueEquiv_apply
    (hvalue : ∀ b, w b = (b : K⟦ℝ⟧).degree)
    (b : (finiteSupportSubring : Subring (Nonpositive ℝ K))) :
    finiteSupportResidueEquiv w hvalue b =
      w.residueMap
        (RingEquiv.subringCongr
          (nonpositiveSubring_eq_finiteSupportSubring_of_value_eq_degree w hvalue).symm b) := by
  simp [finiteSupportResidueEquiv]

/-- Under the RV/homogeneous equivalence, the residue isomorphism is the restriction of `rv`. -/
theorem coe_rvEquivHomogeneous_rv_eq_residueRingHom_finiteSupportResidueEquiv
    [w.IsMultiplicative]
    (hvalue : ∀ b, w b = (b : K⟦ℝ⟧).degree)
    (b : (finiteSupportSubring : Subring (Nonpositive ℝ K))) :
    (w.rvEquivHomogeneous (w.rv (b : Nonpositive ℝ K)) :
        w.AssociatedGraded) =
      w.residueRingHom (finiteSupportResidueEquiv w hvalue b) := by
  rw [finiteSupportResidueEquiv_apply]
  let x : w.nonpositiveSubring :=
    RingEquiv.subringCongr
      (nonpositiveSubring_eq_finiteSupportSubring_of_value_eq_degree w hvalue).symm b
  have hxcoe : (x : Nonpositive ℝ K) = b := by
    exact RingEquiv.coe_subringCongr_apply _ b
  have hxvalue : w (x : Nonpositive ℝ K) = 0 ∨
      w (x : Nonpositive ℝ K) = ⊥ := by
    by_cases hb : (b : Nonpositive ℝ K) = 0
    · right
      rw [hvalue, hxcoe, hb]
      simp
    · left
      rw [hvalue, hxcoe]
      apply HahnSeries.degree_eq_zero.mpr
      refine ⟨?_,
        (mem_finiteSupportSubring_iff (b : Nonpositive ℝ K)).mp b.2⟩
      simpa using hb
  have hdiagram :=
    w.coe_rvEquivHomogeneous_rv_eq_residueRingHom_residueMap x hxvalue
  rw [hxcoe] at hdiagram
  exact hdiagram

variable (K) in
/-- LM24, Proposition 5.1.1 for the degree valuation: the finite-support subring is its
degree-zero residue ring. -/
def degreeFiniteSupportResidueEquiv [Nontrivial K] :
    (finiteSupportSubring : Subring (Nonpositive ℝ K)) ≃+* (degreeValuation K).ResidueRing :=
  finiteSupportResidueEquiv (degreeValuation K) degreeValuation_apply

/-- The degree-residue equivalence is the residue map restricted to finite-support series. -/
@[simp]
theorem degreeFiniteSupportResidueEquiv_apply [Nontrivial K]
    (b : (finiteSupportSubring : Subring (Nonpositive ℝ K))) :
    degreeFiniteSupportResidueEquiv K b =
      (degreeValuation K).residueMap
        (RingEquiv.subringCongr
          (nonpositiveSubring_eq_finiteSupportSubring_of_value_eq_degree
            (degreeValuation K) degreeValuation_apply).symm b) :=
  finiteSupportResidueEquiv_apply (degreeValuation K) degreeValuation_apply b

end HahnSeries.Nonpositive
