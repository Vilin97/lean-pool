/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.PlaceState

/-!
# Fixed homogeneous bridges for the feedback state

Only six quartic rows are consumed by the zero-wedge and second-jet minors.
This file connects those rows to actual Boolean ANF products.  The proof is
bilinear and checks the fixed `7 × 7 × 6` basis matrix; it never enumerates
circuits or Boolean functions.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The six quartic coordinates used by the feedback minors. -/
@[expose]
def feedbackQuarticCoord : Fin 6 → Fin 8 × Fin 8 × Fin 8 × Fin 8 :=
  ![(0, 1, 4, 5), (0, 1, 4, 6), (0, 3, 4, 7),
    (0, 3, 5, 7), (0, 3, 6, 7), (0, 1, 6, 7)]

/-- Extract the six quartic ANF coefficients used in feedback arguments. -/
@[expose]
def feedbackQuarticProbeANF : ANF 8 →ₗ[F₂] (Fin 6 → F₂) where
  toFun p u := anfFourProjection p (feedbackQuarticCoord u).1
    (feedbackQuarticCoord u).2.1
    (feedbackQuarticCoord u).2.2.1
    (feedbackQuarticCoord u).2.2.2
  map_add' p q := by
    funext u
    simp
  map_smul' a p := by
    funext u
    simp

@[simp] theorem feedbackQuarticProbeANF_apply (p : ANF 8) (u : Fin 6) :
    feedbackQuarticProbeANF p u =
      anfFourProjection p (feedbackQuarticCoord u).1
        (feedbackQuarticCoord u).2.1
        (feedbackQuarticCoord u).2.2.1
        (feedbackQuarticCoord u).2.2.2 := rfl

/-- Extract the six feedback coordinates of a wedge of two two-forms. -/
@[expose]
def feedbackQuarticWedgeProbe (q c : TwoForm) : Fin 6 → F₂ := fun u =>
  wedgeTwo q c (feedbackQuarticCoord u).1
    (feedbackQuarticCoord u).2.1
    (feedbackQuarticCoord u).2.2.1
    (feedbackQuarticCoord u).2.2.2

theorem anfFourProjection_eq_zero_of_degreeLE_three
    {p : ANF 8} (hp : DegreeLE 3 p) : anfFourProjection p = 0 := by
  funext i j k l
  by_cases hcard : ({i, j, k, l} : Finset (Fin 8)).card = 4
  · change (if ({i, j, k, l} : Finset (Fin 8)).card = 4 then
      p.coeff ⟨{i, j, k, l}⟩ else 0) = 0
    rw [ite_eq_left hcard]
    exact hp _ (by simp [hcard])
  · simp [anfFourProjection, hcard]

theorem feedbackQuarticProbeANF_eq_zero_of_degreeLE_three
    {p : ANF 8} (hp : DegreeLE 3 p) : feedbackQuarticProbeANF p = 0 := by
  have hfour := anfFourProjection_eq_zero_of_degreeLE_three hp
  funext u
  exact congrFun (congrFun (congrFun (congrFun hfour
    (feedbackQuarticCoord u).1)
    (feedbackQuarticCoord u).2.1)
    (feedbackQuarticCoord u).2.2.1)
    (feedbackQuarticCoord u).2.2.2

private theorem targetANF_targetBasis_feedback_quartic (s : Fin 7) :
    targetANF (targetBasis s) = Mul 4 s := by
  simp [targetANF, targetBasis_apply]

private theorem feedbackQuarticProbe_Mul_mul_zero :
    ∀ t : Fin 7, feedbackQuarticProbeANF (Mul 4 0 * Mul 4 t) =
      feedbackQuarticWedgeProbe
        (targetTwo (targetBasis 0)) (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_feedback_quartic,
    ← targetANF_targetBasis_feedback_quartic]
  simp only [feedbackQuarticProbeANF_apply, anfFourProjection, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem feedbackQuarticProbe_Mul_mul_one :
    ∀ t : Fin 7, feedbackQuarticProbeANF (Mul 4 1 * Mul 4 t) =
      feedbackQuarticWedgeProbe
        (targetTwo (targetBasis 1)) (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_feedback_quartic,
    ← targetANF_targetBasis_feedback_quartic]
  simp only [feedbackQuarticProbeANF_apply, anfFourProjection, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem feedbackQuarticProbe_Mul_mul_two :
    ∀ t : Fin 7, feedbackQuarticProbeANF (Mul 4 2 * Mul 4 t) =
      feedbackQuarticWedgeProbe
        (targetTwo (targetBasis 2)) (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_feedback_quartic,
    ← targetANF_targetBasis_feedback_quartic]
  simp only [feedbackQuarticProbeANF_apply, anfFourProjection, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem feedbackQuarticProbe_Mul_mul_three :
    ∀ t : Fin 7, feedbackQuarticProbeANF (Mul 4 3 * Mul 4 t) =
      feedbackQuarticWedgeProbe
        (targetTwo (targetBasis 3)) (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_feedback_quartic,
    ← targetANF_targetBasis_feedback_quartic]
  simp only [feedbackQuarticProbeANF_apply, anfFourProjection, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem feedbackQuarticProbe_Mul_mul_four :
    ∀ t : Fin 7, feedbackQuarticProbeANF (Mul 4 4 * Mul 4 t) =
      feedbackQuarticWedgeProbe
        (targetTwo (targetBasis 4)) (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_feedback_quartic,
    ← targetANF_targetBasis_feedback_quartic]
  simp only [feedbackQuarticProbeANF_apply, anfFourProjection, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem feedbackQuarticProbe_Mul_mul_five :
    ∀ t : Fin 7, feedbackQuarticProbeANF (Mul 4 5 * Mul 4 t) =
      feedbackQuarticWedgeProbe
        (targetTwo (targetBasis 5)) (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_feedback_quartic,
    ← targetANF_targetBasis_feedback_quartic]
  simp only [feedbackQuarticProbeANF_apply, anfFourProjection, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem feedbackQuarticProbe_Mul_mul_six :
    ∀ t : Fin 7, feedbackQuarticProbeANF (Mul 4 6 * Mul 4 t) =
      feedbackQuarticWedgeProbe
        (targetTwo (targetBasis 6)) (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_feedback_quartic,
    ← targetANF_targetBasis_feedback_quartic]
  simp only [feedbackQuarticProbeANF_apply, anfFourProjection, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem feedbackQuarticProbe_Mul_mul (s t : Fin 7) :
    feedbackQuarticProbeANF (Mul 4 s * Mul 4 t) =
      feedbackQuarticWedgeProbe
        (targetTwo (targetBasis s)) (targetTwo (targetBasis t)) := by
  fin_cases s
  · exact feedbackQuarticProbe_Mul_mul_zero t
  · exact feedbackQuarticProbe_Mul_mul_one t
  · exact feedbackQuarticProbe_Mul_mul_two t
  · exact feedbackQuarticProbe_Mul_mul_three t
  · exact feedbackQuarticProbe_Mul_mul_four t
  · exact feedbackQuarticProbe_Mul_mul_five t
  · exact feedbackQuarticProbe_Mul_mul_six t

/-- The six feedback wedge probes as a bilinear map. -/
def feedbackQuarticWedgeProbeBilinear :
    TwoForm →ₗ[F₂] TwoForm →ₗ[F₂] (Fin 6 → F₂) where
  toFun q :=
    { toFun := feedbackQuarticWedgeProbe q
      map_add' := by
        intro c d
        funext u
        simp [feedbackQuarticWedgeProbe, wedgeTwo]
        ring
      map_smul' := by
        intro a c
        funext u
        simp [feedbackQuarticWedgeProbe, wedgeTwo]
        ring }
  map_add' q r := by
    apply LinearMap.ext
    intro c
    funext u
    simp [feedbackQuarticWedgeProbe, wedgeTwo]
    ring
  map_smul' a q := by
    apply LinearMap.ext
    intro c
    funext u
    simp [feedbackQuarticWedgeProbe, wedgeTwo]
    ring

private theorem targetTwo_eq_sum_feedback_basis (c : TargetCoeff) :
    targetTwo c = ∑ s : Fin 7, c s • targetTwo (targetBasis s) := by
  change targetTwoLinear c =
    ∑ s : Fin 7, c s • targetTwoLinear (targetBasis s)
  have h := congrArg targetTwoLinear (targetBasis_reconstruction c)
  simpa only [map_sum, map_smul] using h.symm

private theorem feedbackQuarticProbe_Mul_mul_targetANF
    (s : Fin 7) (d : TargetCoeff) :
    feedbackQuarticProbeANF (Mul 4 s * targetANF d) =
      feedbackQuarticWedgeProbe
        (targetTwo (targetBasis s)) (targetTwo d) := by
  rw [targetANF]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, feedbackQuarticProbe_Mul_mul]
  change (∑ t : Fin 7, d t •
      feedbackQuarticWedgeProbe (targetTwo (targetBasis s))
        (targetTwo (targetBasis t))) =
    feedbackQuarticWedgeProbeBilinear
      (targetTwo (targetBasis s)) (targetTwo d)
  rw [targetTwo_eq_sum_feedback_basis d]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro t _
  rfl

theorem feedbackQuarticProbe_target_mul_target (c d : TargetCoeff) :
    feedbackQuarticProbeANF (targetANF c * targetANF d) =
      feedbackQuarticWedgeProbe (targetTwo c) (targetTwo d) := by
  change feedbackQuarticProbeANF
    ((∑ s : Fin 7, c s • Mul 4 s) * targetANF d) = _
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul]
  calc
    (∑ s : Fin 7, c s •
        feedbackQuarticProbeANF (Mul 4 s * targetANF d)) =
        ∑ s : Fin 7, c s •
          feedbackQuarticWedgeProbe (targetTwo (targetBasis s))
            (targetTwo d) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [feedbackQuarticProbe_Mul_mul_targetANF]
    _ = feedbackQuarticWedgeProbeBilinear (targetTwo c) (targetTwo d) := by
      rw [targetTwo_eq_sum_feedback_basis c]
      simp only [map_sum, map_smul]
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
      apply Finset.sum_congr rfl
      intro s _
      rfl

theorem feedbackProduct_quarticProbe
    (a b : F₂) (ell m : LinearForm) (q c : FeedbackCoord) :
    feedbackQuarticProbeANF
        ((affineANF a ell + targetANF (feedbackCoeffRep q)) *
          (affineANF b m + targetANF (feedbackCoeffRep c))) =
      feedbackQuarticWedgeProbe
        (targetTwo (feedbackCoeffRep q))
        (targetTwo (feedbackCoeffRep c)) := by
  simp only [add_mul, mul_add, map_add]
  have haa : feedbackQuarticProbeANF
      (affineANF a ell * affineANF b m) = 0 :=
    feedbackQuarticProbeANF_eq_zero_of_degreeLE_three
      ((degreeLE_one_affineANF a ell).mul
        (degreeLE_one_affineANF b m) |>.mono (by omega))
  have hat : feedbackQuarticProbeANF
      (affineANF a ell * targetANF (feedbackCoeffRep c)) = 0 :=
    feedbackQuarticProbeANF_eq_zero_of_degreeLE_three
      ((degreeLE_one_affineANF a ell).mul
        (degreeLE_two_targetANF _) |>.mono (by omega))
  have hta : feedbackQuarticProbeANF
      (targetANF (feedbackCoeffRep q) * affineANF b m) = 0 :=
    feedbackQuarticProbeANF_eq_zero_of_degreeLE_three
      ((degreeLE_two_targetANF _).mul
        (degreeLE_one_affineANF b m) |>.mono (by omega))
  rw [haa, hat, hta, zero_add, zero_add, zero_add,
    feedbackQuarticProbe_target_mul_target]

/-- Quartic vanishing for a product of two feedback-low wires has exactly
the zero-wedge alternatives of `Feedback.lean`. -/
theorem feedbackProduct_zeroWedgeStructure
    (a b : F₂) (ell m : LinearForm) (q c : FeedbackCoord)
    (hzero : feedbackQuarticProbeANF
      ((affineANF a ell + targetANF (feedbackCoeffRep q)) *
        (affineANF b m + targetANF (feedbackCoeffRep c))) = 0) :
    q = 0 ∨ c = 0 ∨ q = c ∨
      (InFirstJetPlane q ∧ InFirstJetPlane c) := by
  rw [feedbackProduct_quarticProbe] at hzero
  have row (u : Fin 6) :
      feedbackQuarticWedgeProbe
        (targetTwo (feedbackCoeffRep q))
        (targetTwo (feedbackCoeffRep c)) u = 0 := by
    exact congrFun hzero u
  apply feedback_zero_wedge_structure_of_rows
  · simpa [feedbackQuarticWedgeProbe, feedbackQuarticCoord] using row 0
  · simpa [feedbackQuarticWedgeProbe, feedbackQuarticCoord] using row 1
  · simpa [feedbackQuarticWedgeProbe, feedbackQuarticCoord] using row 2
  · simpa [feedbackQuarticWedgeProbe, feedbackQuarticCoord] using row 3
  · simpa [feedbackQuarticWedgeProbe, feedbackQuarticCoord] using row 4

end

end N4
end UnrestrictedBooleanMul
