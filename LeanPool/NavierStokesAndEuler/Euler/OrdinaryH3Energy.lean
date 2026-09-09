/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Commutator
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordConstraints

@[expose] public section

/-! The genuine spatial H³ difference-energy estimate for ordinary Euler.
The pressure term vanishes exactly. The constant uses only the reference
H⁴ norm and the H³ norm of the difference. -/

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal Finset
open scoped ContDiff

theorem wordField_neg (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    wordField (fieldNeg A) w=fieldNeg (wordField A w) := wordField_map _ A w

theorem wordBound_add {s : ℕ} {M N : ℝ} {A B : SmoothL2Field Space}
    (hA : WordBound s M A) (hB : WordBound s N B) : WordBound s (M+N) (addField A B) := by
  intro n hn w
  rw [wordField_add,toLp_addField]
  exact (norm_add_le _ _).trans (add_le_add (hA n hn w) (hB n hn w))

def differenceRhs (U W P : SmoothL2Field Space) : SmoothL2Field Space :=
  fieldNeg (addField (addField (advectionField (addField U W) W) (advectionField W U)) P)

theorem differenceRhs_field (U W P : SmoothL2Field Space) (x : Space) :
    (differenceRhs U W P).field x =
      -fderiv ℝ W.field x (U.field x+W.field x)-fderiv ℝ U.field x (W.field x)-P.field x := by
  simp only [differenceRhs,fieldNeg_field,addField_field,advectionField_field]
  abel

theorem differenceRhs_pairing (U W P : SmoothL2Field Space)
    (hdiv : ∀ x, divergence (addField U W).field x=0)
    (hW : W.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace)
    {n : ℕ} (w : Fin n → Fin 3) :
    ⟪(wordField W w).toLp,(wordField (differenceRhs U W P) w).toLp⟫_ℝ =
      -⟪(transportCommutator (addField U W) W w).toLp,(wordField W w).toLp⟫_ℝ-
        ⟪(wordField (advectionField W U) w).toLp,(wordField W w).toLp⟫_ℝ := by
  have ht : ⟪(wordField W w).toLp,(wordField (advectionField (addField U W) W) w).toLp⟫_ℝ =
      ⟪(transportCommutator (addField U W) W w).toLp,(wordField W w).toLp⟫_ℝ := by
    rw [real_inner_comm,transportCommutator,toLp_fieldSub,inner_sub_left,
      advection_inner_zero (addField U W) (wordField W w) hdiv,sub_zero]
  have hp : ⟪(wordField W w).toLp,(wordField P w).toLp⟫_ℝ=0 := by
    rw [real_inner_comm]
    exact word_pressure_pairing_zero P W hP hW w
  simp only [differenceRhs,wordField_neg,wordField_add,toLp_fieldNeg,toLp_addField,
    inner_neg_right,inner_add_right]
  rw [ht,hp,real_inner_comm (wordField W w).toLp (wordField (advectionField W U) w).toLp]
  ring

theorem differenceRhs_word_bound (U W P : SmoothL2Field Space) (M X : ℝ)
    (hU : WordBound 4 M U) (hWb : WordBound 3 X W)
    (hdiv : ∀ x, divergence (addField U W).field x=0)
    (hW : W.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace)
    {n : ℕ} (hn : n ≤ 3) (w : Fin n → Fin 3) :
    ⟪(wordField W w).toLp,(wordField (differenceRhs U W P) w).toLp⟫_ℝ ≤
      45*h3ProductConstant*(M+X)*X^2 := by
  have hM := wordBound_nonneg hU
  have hX := wordBound_nonneg hWb
  have hC := h3ProductConstant_nonneg
  have hMX : 0 ≤ M+X := add_nonneg hM hX
  have hv := wordBound_add (wordBound_mono hU (by norm_num : 3 ≤ 4)) hWb
  have hk := transportCommutator_bound (addField U W) W (M+X) X hv hWb hn w
  have hs := source_advection_outer W U X M hWb hU hn w
  have hpow : (2 : ℝ)^n ≤ 8 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    norm_num at h ⊢
    exact h
  have hkcoef : 3*((2 : ℝ)^n-1) ≤ 21 := by linarith
  have hscoef : 3*(2 : ℝ)^n ≤ 24 := by linarith
  have hkb : ‖(transportCommutator (addField U W) W w).toLp‖ ≤
      21*h3ProductConstant*(M+X)*X := hk.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hkcoef hC) hMX) hX)
  have hsb : ‖(wordField (advectionField W U) w).toLp‖ ≤
      24*h3ProductConstant*(M+X)*X := by
    apply hs.trans
    calc
      _ ≤ 24*h3ProductConstant*X*M := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscoef hC) hX) hM
      _ = 24*h3ProductConstant*M*X := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hX) (by positivity)) hX
  have hsum : ‖(transportCommutator (addField U W) W w).toLp‖+
      ‖(wordField (advectionField W U) w).toLp‖ ≤
        45*h3ProductConstant*(M+X)*X :=
    (add_le_add hkb hsb).trans_eq (by ring)
  rw [differenceRhs_pairing U W P hdiv hW hP w]
  calc
    _ ≤ |⟪(transportCommutator (addField U W) W w).toLp,(wordField W w).toLp⟫_ℝ|+
        |⟪(wordField (advectionField W U) w).toLp,(wordField W w).toLp⟫_ℝ| := by
      linarith [neg_le_abs ⟪(transportCommutator (addField U W) W w).toLp,(wordField W w).toLp⟫_ℝ,
        neg_le_abs ⟪(wordField (advectionField W U) w).toLp,(wordField W w).toLp⟫_ℝ]
    _ ≤ ‖(transportCommutator (addField U W) W w).toLp‖*‖(wordField W w).toLp‖+
        ‖(wordField (advectionField W U) w).toLp‖*‖(wordField W w).toLp‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ = (‖(transportCommutator (addField U W) W w).toLp‖+
        ‖(wordField (advectionField W U) w).toLp‖)*‖(wordField W w).toLp‖ := by ring
    _ ≤ (45*h3ProductConstant*(M+X)*X)*X :=
      mul_le_mul hsum (hWb n hn w) (norm_nonneg _) (by positivity)
    _ = _ := by ring

def energyProduction (W Q : SmoothL2Field Space) : ℝ :=
  2*(∑ n ∈ range 4, ∑ w : Fin n → Fin 3, ⟪(wordField W w).toLp,(wordField Q w).toLp⟫_ℝ)

theorem difference_energy_bound (U W P : SmoothL2Field Space) (M : ℝ)
    (hU : WordBound 4 M U)
    (hdiv : ∀ x, divergence (addField U W).field x=0)
    (hW : W.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace) :
    energyProduction W (differenceRhs U W P) ≤
      3600*h3ProductConstant*(M+Real.sqrt (wordEnergy 3 W))*wordEnergy 3 W := by
  let X := Real.sqrt (wordEnergy 3 W)
  have hx : X^2=wordEnergy 3 W := Real.sq_sqrt (wordEnergy_nonneg 3 W)
  have hh : (∑ n ∈ range 4, ∑ w : Fin n → Fin 3,
      ⟪(wordField W w).toLp,(wordField (differenceRhs U W P) w).toLp⟫_ℝ) ≤
        40*(45*h3ProductConstant*(M+X)*X^2) := by
    calc
      _ ≤ ∑ n ∈ range 4, ∑ _w : Fin n → Fin 3, 45*h3ProductConstant*(M+X)*X^2 := by
        apply sum_le_sum
        intro n hn
        exact sum_le_sum (fun w _ => differenceRhs_word_bound U W P M X hU
          (wordBound_sqrt_energy 3 W) hdiv hW hP (by have := mem_range.mp hn; omega) w)
      _ = _ := by norm_num [sum_range_succ]; ring
  apply (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  change 2*(40*(45*h3ProductConstant*(M+X)*X^2)) =
    3600*h3ProductConstant*(M+X)*wordEnergy 3 W
  rw [← hx]
  ring

end EulerOrdinarySobolev
