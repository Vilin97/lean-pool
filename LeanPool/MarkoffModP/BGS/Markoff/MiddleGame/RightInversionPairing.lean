/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTraceEquation

/-!
# The right-coordinate inversion pairing

The right-hand trace in the weighted middle-game equation is invariant under
inversion.  Away from the two-torsion points, every solution therefore occurs
with a distinct partner having the same left coordinate.  This gives a genuine
factor of two for the nonparabolic left support, while leaving the existing
parabolic escape branch responsible for the two fixed points.
-/

@[expose] public section

namespace BGS.Markoff

variable {E : Type*} [Field E] [Fintype E]

omit [Fintype E] in
/-- The ordinary split trace is invariant under inversion. -/
theorem splitTorusTrace_right_inv (h : Eˣ) :
    splitTorusTrace h⁻¹ = splitTorusTrace h := by
  simp only [splitTorusTrace, Units.val_inv_eq_inv_val, inv_inv]
  exact add_comm _ _

/-- Inverting the right coordinate preserves every weighted trace-equation
solution and leaves its left coordinate unchanged. -/
theorem weightedTraceEquationSolutions_right_inv_mem
    {alpha beta : E} {H₁ H₂ : Subgroup Eˣ} {z : H₁ × H₂}
    (hz : z ∈ weightedTraceEquationSolutions alpha beta H₁ H₂) :
    (z.1, z.2⁻¹) ∈ weightedTraceEquationSolutions alpha beta H₁ H₂ := by
  rw [mem_weightedTraceEquationSolutions_iff] at hz ⊢
  change weightedSplitTorusTrace alpha beta (z.1 : Eˣ) =
    splitTorusTrace ((z.2 : Eˣ)⁻¹)
  rw [splitTorusTrace_right_inv]
  exact hz

omit [Fintype E] in
/-- A subgroup element whose square is not one is distinct from its inverse. -/
theorem subgroupElement_ne_inv_of_sq_ne_one
    {H : Subgroup Eˣ} (h : H) (hsq : ((h : Eˣ) ^ 2) ≠ 1) :
    h ≠ h⁻¹ := by
  intro hinv
  apply hsq
  have hinv' : (h : Eˣ) = ((h⁻¹ : H) : Eˣ) :=
    congrArg (fun u : H ↦ (u : Eˣ)) hinv
  calc
    (h : Eˣ) ^ 2 = (h : Eˣ) * (h : Eˣ) := pow_two _
    _ = (h : Eˣ) * ((h⁻¹ : H) : Eˣ) := congrArg ((h : Eˣ) * ·) hinv'
    _ = 1 := by simp

/-- The nonparabolic part of a weighted trace-equation solution set. -/
noncomputable def weightedTraceEquationNonparabolicSolutions
    (alpha beta : E) (H₁ H₂ : Subgroup Eˣ) : Finset (H₁ × H₂) := by
  classical
  exact (weightedTraceEquationSolutions alpha beta H₁ H₂).filter fun z ↦
    ((z.2 : Eˣ) ^ 2) ≠ 1

@[simp]
theorem mem_weightedTraceEquationNonparabolicSolutions_iff
    {alpha beta : E} {H₁ H₂ : Subgroup Eˣ} {z : H₁ × H₂} :
    z ∈ weightedTraceEquationNonparabolicSolutions alpha beta H₁ H₂ ↔
      z ∈ weightedTraceEquationSolutions alpha beta H₁ H₂ ∧
        ((z.2 : Eˣ) ^ 2) ≠ 1 := by
  classical
  simp [weightedTraceEquationNonparabolicSolutions]

/-- Left elements occurring in a nonparabolic weighted solution. -/
noncomputable def weightedTraceEquationNonparabolicLeftSupport
    (alpha beta : E) (H₁ H₂ : Subgroup Eˣ) : Finset H₁ := by
  classical
  exact
    (weightedTraceEquationNonparabolicSolutions alpha beta H₁ H₂).image Prod.fst

@[simp]
theorem mem_weightedTraceEquationNonparabolicLeftSupport_iff
    {alpha beta : E} {H₁ H₂ : Subgroup Eˣ} {h₁ : H₁} :
    h₁ ∈ weightedTraceEquationNonparabolicLeftSupport alpha beta H₁ H₂ ↔
      ∃ h₂ : H₂,
        weightedSplitTorusTrace alpha beta h₁ = splitTorusTrace h₂ ∧
          ((h₂ : Eˣ) ^ 2) ≠ 1 := by
  classical
  simp only [weightedTraceEquationNonparabolicLeftSupport, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_weightedTraceEquationNonparabolicSolutions_iff] at hz
    exact ⟨z.2, mem_weightedTraceEquationSolutions_iff.mp hz.1, hz.2⟩
  · rintro ⟨h₂, heq, hsq⟩
    exact ⟨(h₁, h₂), mem_weightedTraceEquationNonparabolicSolutions_iff.mpr
      ⟨mem_weightedTraceEquationSolutions_iff.mpr heq, hsq⟩, rfl⟩

/-- Every fiber of the nonparabolic right-inversion quotient has at least two
points.  Consequently twice the left-support cardinality is bounded by the
full Corvaja--Zannier solution count. -/
theorem two_mul_weightedTraceEquationNonparabolicLeftSupport_card_le_solutions
    (alpha beta : E) (H₁ H₂ : Subgroup Eˣ) :
    2 * (weightedTraceEquationNonparabolicLeftSupport
      alpha beta H₁ H₂).card ≤
        (weightedTraceEquationSolutions alpha beta H₁ H₂).card := by
  classical
  let solutions :=
    weightedTraceEquationSolutions alpha beta H₁ H₂
  let nonparabolic :=
    weightedTraceEquationNonparabolicSolutions alpha beta H₁ H₂
  have hfiber :
      ∀ h₁ ∈ nonparabolic.image Prod.fst,
        2 ≤ (nonparabolic.filter fun z ↦ Prod.fst z = h₁).card := by
    intro h₁ hh₁
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh₁
    have hzData :
        z ∈ solutions ∧ ((z.2 : Eˣ) ^ 2) ≠ 1 := by
      simpa [nonparabolic, solutions] using
        (mem_weightedTraceEquationNonparabolicSolutions_iff.mp hz)
    have hzInvSolutions :
        (z.1, z.2⁻¹) ∈ solutions := by
      simpa [solutions] using
        weightedTraceEquationSolutions_right_inv_mem hzData.1
    have hzInvSq : ((((z.2⁻¹ : H₂) : Eˣ) ^ 2) ≠ 1) := by
      intro h
      apply hzData.2
      have h' := congrArg Inv.inv h
      simpa using h'
    have hzInv :
        (z.1, z.2⁻¹) ∈ nonparabolic := by
      rw [show nonparabolic =
          weightedTraceEquationNonparabolicSolutions alpha beta H₁ H₂ by rfl,
        mem_weightedTraceEquationNonparabolicSolutions_iff]
      exact ⟨by simpa [solutions] using hzInvSolutions, hzInvSq⟩
    have hne : z ≠ (z.1, z.2⁻¹) := by
      intro h
      exact subgroupElement_ne_inv_of_sq_ne_one z.2 hzData.2
        (congrArg Prod.snd h)
    have hsubset :
        ({z, (z.1, z.2⁻¹)} : Finset (H₁ × H₂)) ⊆
          nonparabolic.filter fun w ↦ Prod.fst w = z.1 := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_filter]
      rcases hw with rfl | rfl
      · exact ⟨hz, rfl⟩
      · exact ⟨hzInv, rfl⟩
    have hcard := Finset.card_le_card hsubset
    simpa [hne] using hcard
  have hpaired :
      2 * (nonparabolic.image Prod.fst).card ≤ nonparabolic.card :=
    Finset.mul_card_image_le_card nonparabolic 2 hfiber
  calc
    2 * (weightedTraceEquationNonparabolicLeftSupport
        alpha beta H₁ H₂).card =
        2 * (nonparabolic.image Prod.fst).card := by
          rfl
    _ ≤ nonparabolic.card := hpaired
    _ ≤ solutions.card := by
      exact Finset.card_le_card fun z hz ↦ by
        exact
          (mem_weightedTraceEquationNonparabolicSolutions_iff.mp
            (by simpa [nonparabolic] using hz)).1

end BGS.Markoff
