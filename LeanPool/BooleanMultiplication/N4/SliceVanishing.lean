/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.FeedbackSlice

/-!
# Vanishing slices of a zero-place tangent

The feedback factor `δ + ρx + σy + xy` is zero on an odd number of the four
anchor corners.  Right idempotence makes the target child vanish on every
zero corner.  Two such vanishing slices would have equal first differences
in the complementary `u` and `v` directions, forcing the corners to be
equal.  Hence there is exactly one zero corner and exactly three active
slices.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Embed six complementary values between the two anchor variables. -/
@[expose] def sliceAssignment (x y : F₂) (z : Fin 6 → F₂) : Fin 8 → F₂ :=
  ![x, z 0, z 1, z 2, y, z 3, z 4, z 5]

/-- The zero assignment on the six complementary slice inputs. -/
def sliceComplementZero : Fin 6 → F₂ := ![0, 0, 0, 0, 0, 0]
/-- The complementary assignment selecting the first polynomial linear coefficient. -/
def sliceComplementU : Fin 6 → F₂ := ![1, 0, 0, 0, 0, 0]
/-- The complementary assignment selecting the second polynomial linear coefficient. -/
def sliceComplementV : Fin 6 → F₂ := ![0, 0, 0, 1, 0, 0]

/-- The ANF vanishes on every assignment with the specified anchor values. -/
def SliceVanishes (F : ANF 8) (x y : F₂) : Prop :=
  ∀ z : Fin 6 → F₂, eval F (sliceAssignment x y z) = 0

theorem mul_target_zero_anf :
    Mul 4 0 = monomial ({0, 4} : Finset (Fin 8)) := by
  simp (disch := decide)
    [UnrestrictedBooleanMul.Mul, mulCoefficient, Fin.sum_univ_succ,
      aVar, bVar, X, monomial_mul]

theorem mul_target_one_anf :
    Mul 4 1 =
      monomial ({0, 5} : Finset (Fin 8)) +
        monomial ({1, 4} : Finset (Fin 8)) := by
  simp (disch := decide)
    [UnrestrictedBooleanMul.Mul, mulCoefficient, Fin.sum_univ_succ,
      aVar, bVar, X, monomial_mul]

/-- First difference of a tangent slice in the complementary `u` direction. -/
theorem zero_tangent_sliceU_difference
    {F : ANF 8} {targetConst eps : F₂}
    {targetLinear : LinearForm}
    (hFRep : F =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (x y : F₂) :
    eval F (sliceAssignment x y sliceComplementU) +
        eval F (sliceAssignment x y sliceComplementZero) =
      targetLinear 1 + y := by
  rw [hFRep, targetANF_zero_tangent, mul_target_zero_anf,
    mul_target_one_anf]
  simp [affineANF, linearANF, eval_add', eval_smul', eval_monomial, eval_X, sliceAssignment,
    sliceComplementU, sliceComplementZero, Fin.sum_univ_succ]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- First difference of a tangent slice in the complementary `v` direction. -/
theorem zero_tangent_sliceV_difference
    {F : ANF 8} {targetConst eps : F₂}
    {targetLinear : LinearForm}
    (hFRep : F =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (x y : F₂) :
    eval F (sliceAssignment x y sliceComplementV) +
        eval F (sliceAssignment x y sliceComplementZero) =
      targetLinear 5 + x := by
  rw [hFRep, targetANF_zero_tangent, mul_target_zero_anf,
    mul_target_one_anf]
  simp [affineANF, linearANF, eval_add', eval_smul', eval_monomial, eval_X, sliceAssignment,
    sliceComplementV, sliceComplementZero, Fin.sum_univ_succ]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- A tangent target cannot vanish on two distinct anchor slices. -/
theorem zero_tangent_vanishing_slices_injective
    {F : ANF 8} {targetConst eps : F₂}
    {targetLinear : LinearForm}
    (hFRep : F =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    {x y x' y' : F₂}
    (hxy : SliceVanishes F x y)
    (hxy' : SliceVanishes F x' y') :
    x = x' ∧ y = y' := by
  have hu := zero_tangent_sliceU_difference hFRep x y
  have hu' := zero_tangent_sliceU_difference hFRep x' y'
  rw [hxy sliceComplementU, hxy sliceComplementZero] at hu
  rw [hxy' sliceComplementU, hxy' sliceComplementZero] at hu'
  have hv := zero_tangent_sliceV_difference hFRep x y
  have hv' := zero_tangent_sliceV_difference hFRep x' y'
  rw [hxy sliceComplementV, hxy sliceComplementZero] at hv
  rw [hxy' sliceComplementV, hxy' sliceComplementZero] at hv'
  constructor
  · exact add_left_cancel (hv.symm.trans hv')
  · exact add_left_cancel (hu.symm.trans hu')

/-- The scalar zero-place feedback factor at one anchor corner. -/
def feedbackCorner (delta rho sigma x y : F₂) : F₂ :=
  delta + rho * x + sigma * y + x * y

theorem eval_zero_place_feedback
    {factor : ANF 8} {delta rho sigma : F₂}
    (hfactor : factor =
      affineANF delta (rho • sliceX + sigma • sliceY) +
        rationalANF (rationalSingleton 0))
    (x y : F₂) (z : Fin 6 → F₂) :
    eval factor (sliceAssignment x y z) =
      feedbackCorner delta rho sigma x y := by
  rw [hfactor, rationalANF_singleton_zero, mul_target_zero_anf]
  simp [feedbackCorner, affineANF, linearANF, sliceX, sliceY, aLinear, bLinear, aCoord,
    bCoord, Pi.basisFun, eval_add', eval_smul', eval_monomial, eval_X, sliceAssignment,
    Fin.sum_univ_succ]
  ring

/-- A zero feedback corner makes the target child vanish on that slice. -/
theorem slice_vanishes_of_feedbackCorner_zero
    {F factor : ANF 8} {delta rho sigma : F₂}
    (hfactor : factor =
      affineANF delta (rho • sliceX + sigma • sliceY) +
        rationalANF (rationalSingleton 0))
    (hright : F * factor = F)
    {x y : F₂} (hzero : feedbackCorner delta rho sigma x y = 0) :
    SliceVanishes F x y := by
  intro z
  have h := congrArg
    (fun p : ANF 8 => eval p (sliceAssignment x y z)) hright
  rw [eval_mul', eval_zero_place_feedback hfactor, hzero, mul_zero] at h
  exact h.symm

/-- A Boolean polynomial with `xy` coefficient one has a zero corner. -/
theorem feedbackCorner_has_zero (delta rho sigma : F₂) :
    ∃ x y : F₂, feedbackCorner delta rho sigma x y = 0 := by
  revert delta rho sigma
  decide

/-- The feedback factor vanishes at exactly one of the four Boolean anchor corners. -/
@[expose]
def ExactlyThreeActiveCorners (delta rho sigma : F₂) : Prop :=
  ∃ x₀ y₀ : F₂,
    feedbackCorner delta rho sigma x₀ y₀ = 0 ∧
    ∀ x y : F₂, x ≠ x₀ ∨ y ≠ y₀ →
      feedbackCorner delta rho sigma x y = 1

/-- Right idempotence and tangent separation leave exactly three active
anchor slices. -/
theorem exactlyThreeActiveCorners_of_right_idempotence
    {F factor : ANF 8}
    {targetConst eps delta rho sigma : F₂}
    {targetLinear : LinearForm}
    (hFRep : F =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactor : factor =
      affineANF delta (rho • sliceX + sigma • sliceY) +
        rationalANF (rationalSingleton 0))
    (hright : F * factor = F) :
    ExactlyThreeActiveCorners delta rho sigma := by
  rcases feedbackCorner_has_zero delta rho sigma with ⟨x₀, y₀, hzero⟩
  refine ⟨x₀, y₀, hzero, ?_⟩
  intro x y hne
  rcases f2_eq_zero_or_one (feedbackCorner delta rho sigma x y) with
      hcornerZero | hcornerOne
  · have hs₀ := slice_vanishes_of_feedbackCorner_zero hfactor hright hzero
    have hs := slice_vanishes_of_feedbackCorner_zero hfactor hright hcornerZero
    have heq := zero_tangent_vanishing_slices_injective hFRep hs hs₀
    exact (hne.elim (fun hx => hx heq.1) (fun hy => hy heq.2)).elim
  · exact hcornerOne

end

end N4
end UnrestrictedBooleanMul
