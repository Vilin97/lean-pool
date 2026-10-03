/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.HMinusOneNorm

/-! # HDot⁻¹ duality for a smooth periodic test function

If `hMinusOneNorm h` is finite then `|∫ h w| ≤ ‖h‖_{HDot⁻¹} · ‖∇w‖_{L²}` for every smooth periodic
`w`; in the degenerate case `∇w = 0` this forces `∫ h w = 0` (constants are admissible tests, so
`‖h‖_{HDot⁻¹}` would otherwise be infinite). -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization

namespace AVenhance.Infra.Section5.Integration.Energy

open AVenhance

theorem measurableSet_unitCube : MeasurableSet unitCube :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem spaceGrad_const_mul {w : Vec 2 → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (c : ℝ) (x : Vec 2) :
    spaceGrad (fun y => c * w y) x = fun i => c * spaceGrad w x i := by
  funext i
  change fderiv ℝ (fun y => c * w y) x (basisVec i) = _
  rw [fderiv_const_mul (hw.differentiable (by simp) x)]
  simp [spaceGrad]

theorem gradNormSq_nonneg (D : Vec 2 → Vec 2) : 0 ≤ gradNormSq D :=
  integral_nonneg fun _ => vecNormSq_nonneg _

theorem gradNormSq_const_mul {w : Vec 2 → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (c : ℝ) :
    gradNormSq (spaceGrad fun y => c * w y) = c ^ 2 * gradNormSq (spaceGrad w) := by
  unfold gradNormSq
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_unitCube fun x _ => ?_
  simp only [spaceGrad_const_mul hw c x, vecNormSq, vecDot]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A scalar multiple of an admissible-up-to-scaling smooth periodic function is a test, giving
the basic inequality `λ |∫ h w| ≤ ‖h‖_{HDot⁻¹}` whenever `λ ‖∇w‖ ≤ 1`. -/
theorem scaled_pairing_le {h w : Vec 2 → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hper : IsZ2Periodic w)
    (hfin : hMinusOneNorm h ≠ ⊤) {c : ℝ} (hc : 0 ≤ c)
    (hcG : c ^ 2 * gradNormSq (spaceGrad w) ≤ 1) :
    c * |∫ x in unitCube, h x * w x| ≤ (hMinusOneNorm h).toReal := by
  have hadm : ContDiff ℝ (⊤ : ℕ∞) (fun y => c * w y) ∧ IsZ2Periodic (fun y => c * w y) ∧
      gradNormSq (spaceGrad fun y => c * w y) ≤ 1 := by
    refine ⟨contDiff_const.mul hw, fun k x => by simp [hper k x], ?_⟩
    rw [gradNormSq_const_mul hw c]
    exact hcG
  have hle : ENNReal.ofReal |∫ x in unitCube, h x * (c * w x)| ≤ hMinusOneNorm h :=
    le_iSup (fun φ : {φ : Vec 2 → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ IsZ2Periodic φ ∧
      gradNormSq (spaceGrad φ) ≤ 1} => ENNReal.ofReal |∫ x in unitCube, h x * φ.1 x|)
      ⟨fun y => c * w y, hadm⟩
  have h2 := (ENNReal.ofReal_le_iff_le_toReal hfin).1 hle
  have h3 : ∫ x in unitCube, h x * (c * w x) = c * ∫ x in unitCube, h x * w x := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_unitCube fun x _ => by ring
  rw [h3, abs_mul, abs_of_nonneg hc] at h2
  exact h2

/-- The duality bound `|∫ h w| ≤ ‖h‖_{HDot⁻¹} ‖∇w‖_{L²}` for finite `‖h‖_{HDot⁻¹}`. -/
theorem abs_integral_mul_le_hMinusOneNorm {h w : Vec 2 → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hper : IsZ2Periodic w) (hfin : hMinusOneNorm h ≠ ⊤) :
    |∫ x in unitCube, h x * w x| ≤
      (hMinusOneNorm h).toReal * Real.sqrt (gradNormSq (spaceGrad w)) := by
  set I := |∫ x in unitCube, h x * w x| with hI
  set N := (hMinusOneNorm h).toReal with hN
  set Gs := gradNormSq (spaceGrad w) with hGs
  have hGs0 : 0 ≤ Gs := gradNormSq_nonneg _
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hI0 : 0 ≤ I := abs_nonneg _
  have hsq : Real.sqrt Gs ^ 2 = Gs := Real.sq_sqrt hGs0
  rcases (Real.sqrt_nonneg Gs).eq_or_lt with hG | hG
  · -- degenerate case: every multiple of `w` is a test
    rw [← hG, mul_zero]
    by_contra hpos
    have hIpos : 0 < I := lt_of_not_ge (by simpa using hpos)
    have hGs' : Gs = 0 := by
      have : Real.sqrt Gs ^ 2 = 0 := by rw [← hG]; ring
      linarith
    have hc : 0 ≤ (N + 1) / I := by positivity
    have hmain := scaled_pairing_le hw hper hfin hc (by rw [← hGs]; rw [hGs']; simp)
    have : (N + 1) / I * I = N + 1 := by field_simp
    rw [← hI] at hmain
    linarith
  · -- generic case: test with `w / ‖∇w‖`
    have hc : 0 ≤ (Real.sqrt Gs)⁻¹ := by positivity
    have hmain := scaled_pairing_le hw hper hfin hc (by
      rw [inv_pow, hsq]
      have : Gs ≠ 0 := by
        intro h0
        have : Real.sqrt Gs = 0 := by rw [h0]; simp
        linarith
      rw [inv_mul_cancel₀ this])
    rw [← hI] at hmain
    rw [inv_mul_eq_div, div_le_iff₀ hG] at hmain
    linarith

end AVenhance.Infra.Section5.Integration.Energy

end
