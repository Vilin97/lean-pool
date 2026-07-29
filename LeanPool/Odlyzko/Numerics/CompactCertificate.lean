/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Numerics.Integrability
public import LeanPool.Odlyzko.Numerics.PolynomialCertificate
public import LeanPool.Odlyzko.Numerics.Tail

/-! TODO: Add doc-string. -/

@[expose] public section

open MeasureTheory Set

namespace NumberField.Odlyzko

private theorem integrableOn_archimedean_Ioc (a b : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (archimedeanIntegrand odlyzkoScale) (Set.Ioc a b) :=
  (integrableOn_archimedeanIntegrand_Ioi odlyzkoScale).mono_set <| by
    grind

private theorem integrableOn_scaled_deficit_exp_Ioc (c a b : ℝ) :
    IntegrableOn
      (fun x : ℝ ↦ c * (odlyzkoDeficitPolynomial x * Real.exp (-x))) (Set.Ioc a b) := by
  have hc : Continuous
      (fun x : ℝ ↦ c * (odlyzkoDeficitPolynomial x * Real.exp (-x))) := by
    simp only [odlyzkoDeficitPolynomial, tartarAmplitudeLowerSix]
    fun_prop
  exact (hc.continuousOn.integrableOn_Icc.mono_set fun _ hx ↦
    ⟨hx.1.le, hx.2⟩)

theorem integral_archimedean_odlyzkoScale_Ioc_zero_one_le :
    (∫ x in Set.Ioc (0 : ℝ) 1, archimedeanIntegrand odlyzkoScale x) ≤
      43765751791833997513324237919 / 669768750000000000000000000000 := by
  have hmono :
      (∫ x in Set.Ioc (0 : ℝ) 1, archimedeanIntegrand odlyzkoScale x) ≤
        ∫ x in Set.Ioc (0 : ℝ) 1, odlyzkoDeficitQuotient x := by
    have hdeficit :
        IntegrableOn odlyzkoDeficitQuotient (Set.Ioc (0 : ℝ) 1) := by
      have hc : Continuous odlyzkoDeficitQuotient := by
        unfold odlyzkoDeficitQuotient
        fun_prop
      exact (hc.continuousOn.integrableOn_Icc.mono_set fun _ hx ↦
        ⟨hx.1.le, hx.2⟩)
    apply integral_mono_ae (integrableOn_archimedean_Ioc 0 1 (by norm_num))
      hdeficit
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hx4 : x ≤ 4 := hx.2.trans (by norm_num)
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx0
    have hnum := one_sub_tartarTestFunction_le_odlyzkoDeficitPolynomial hx0.le hx4
    have hpoly := odlyzkoDeficitPolynomial_nonneg hx0.le hx4
    have hsinh : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx0.le
    rw [← odlyzkoDeficitPolynomial_div]
    calc
      archimedeanIntegrand odlyzkoScale x
          ≤ odlyzkoDeficitPolynomial x / Real.sinh x := by
            rw [archimedeanIntegrand]
            exact div_le_div_of_nonneg_right hnum hs.le
      _ ≤ odlyzkoDeficitPolynomial x / x := by
            exact div_le_div_of_nonneg_left hpoly hx0 hsinh
  calc
    (∫ x in Set.Ioc (0 : ℝ) 1, archimedeanIntegrand odlyzkoScale x)
        ≤ ∫ x in Set.Ioc (0 : ℝ) 1, odlyzkoDeficitQuotient x := hmono
    _ = ∫ x in (0 : ℝ)..1, odlyzkoDeficitPolynomial x / x := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply integral_congr_ae
      filter_upwards [] with x
      exact (odlyzkoDeficitPolynomial_div x).symm
    _ = _ := integral_odlyzkoDeficitPolynomial_div_id_zero_one

theorem integral_archimedean_odlyzkoScale_Ioc_one_two_lt :
    (∫ x in Set.Ioc (1 : ℝ) 2, archimedeanIntegrand odlyzkoScale x) <
      (7 / 3 : ℝ) * (29 / 500) := by
  have hmono :
      (∫ x in Set.Ioc (1 : ℝ) 2, archimedeanIntegrand odlyzkoScale x) ≤
        ∫ x in Set.Ioc (1 : ℝ) 2,
          (7 / 3 : ℝ) * (odlyzkoDeficitPolynomial x * Real.exp (-x)) := by
    apply integral_mono_ae (integrableOn_archimedean_Ioc 1 2 (by norm_num))
      (integrableOn_scaled_deficit_exp_Ioc (7 / 3) 1 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 ≤ x := le_trans (by norm_num) hx.1.le
    have hx4 : x ≤ 4 := hx.2.trans (by norm_num)
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr (lt_trans (by norm_num) hx.1)
    have hnum := one_sub_tartarTestFunction_le_odlyzkoDeficitPolynomial hx0 hx4
    have hpoly := odlyzkoDeficitPolynomial_nonneg hx0 hx4
    calc
      archimedeanIntegrand odlyzkoScale x
          ≤ odlyzkoDeficitPolynomial x / Real.sinh x := by
            rw [archimedeanIntegrand]
            exact div_le_div_of_nonneg_right hnum hs.le
      _ = odlyzkoDeficitPolynomial x * (1 / Real.sinh x) := by ring
      _ ≤ odlyzkoDeficitPolynomial x * ((7 / 3 : ℝ) * Real.exp (-x)) := by
            gcongr
            exact one_div_sinh_le_seven_thirds_exp hx.1.le
      _ = (7 / 3 : ℝ) * (odlyzkoDeficitPolynomial x * Real.exp (-x)) := by ring
  calc
    (∫ x in Set.Ioc (1 : ℝ) 2, archimedeanIntegrand odlyzkoScale x)
        ≤ ∫ x in Set.Ioc (1 : ℝ) 2,
          (7 / 3 : ℝ) * (odlyzkoDeficitPolynomial x * Real.exp (-x)) := hmono
    _ = (7 / 3 : ℝ) *
        ∫ x in (1 : ℝ)..2, odlyzkoDeficitPolynomial x * Real.exp (-x) := by
          rw [intervalIntegral.integral_of_le (by norm_num), integral_const_mul]
    _ < (7 / 3 : ℝ) * (29 / 500) := by
          gcongr
          exact integral_odlyzkoDeficitPolynomial_mul_exp_one_two_lt

theorem integral_archimedean_odlyzkoScale_Ioc_two_four_lt :
    (∫ x in Set.Ioc (2 : ℝ) 4, archimedeanIntegrand odlyzkoScale x) <
      (64 / 31 : ℝ) * (3 / 40) := by
  have hmono :
      (∫ x in Set.Ioc (2 : ℝ) 4, archimedeanIntegrand odlyzkoScale x) ≤
        ∫ x in Set.Ioc (2 : ℝ) 4,
          (64 / 31 : ℝ) * (odlyzkoDeficitPolynomial x * Real.exp (-x)) := by
    apply integral_mono_ae (integrableOn_archimedean_Ioc 2 4 (by norm_num))
      (integrableOn_scaled_deficit_exp_Ioc (64 / 31) 2 4)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 ≤ x := le_trans (by norm_num) hx.1.le
    have hx4 : x ≤ 4 := hx.2
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr (lt_trans (by norm_num) hx.1)
    have hnum := one_sub_tartarTestFunction_le_odlyzkoDeficitPolynomial hx0 hx4
    have hpoly := odlyzkoDeficitPolynomial_nonneg hx0 hx4
    calc
      archimedeanIntegrand odlyzkoScale x
          ≤ odlyzkoDeficitPolynomial x / Real.sinh x := by
            rw [archimedeanIntegrand]
            exact div_le_div_of_nonneg_right hnum hs.le
      _ = odlyzkoDeficitPolynomial x * (1 / Real.sinh x) := by ring
      _ ≤ odlyzkoDeficitPolynomial x * ((64 / 31 : ℝ) * Real.exp (-x)) := by
            gcongr
            exact one_div_sinh_le_sixty_four_thirty_one_exp hx.1.le
      _ = (64 / 31 : ℝ) * (odlyzkoDeficitPolynomial x * Real.exp (-x)) := by ring
  calc
    (∫ x in Set.Ioc (2 : ℝ) 4, archimedeanIntegrand odlyzkoScale x)
        ≤ ∫ x in Set.Ioc (2 : ℝ) 4,
          (64 / 31 : ℝ) * (odlyzkoDeficitPolynomial x * Real.exp (-x)) := hmono
    _ = (64 / 31 : ℝ) *
        ∫ x in (2 : ℝ)..4, odlyzkoDeficitPolynomial x * Real.exp (-x) := by
          rw [intervalIntegral.integral_of_le (by norm_num), integral_const_mul]
    _ < (64 / 31 : ℝ) * (3 / 40) := by
          gcongr
          exact integral_odlyzkoDeficitPolynomial_mul_exp_two_four_lt

theorem integral_archimedean_odlyzkoScale_Ioc_zero_four_le :
    (∫ x in Set.Ioc (0 : ℝ) 4, archimedeanIntegrand odlyzkoScale x) ≤ 9 / 25 := by
  have h01 := integral_archimedean_odlyzkoScale_Ioc_zero_one_le
  have h12 := integral_archimedean_odlyzkoScale_Ioc_one_two_lt
  have h24 := integral_archimedean_odlyzkoScale_Ioc_two_four_lt
  have hsplit :
      Set.Ioc (0 : ℝ) 4 =
        Set.Ioc (0 : ℝ) 1 ∪ (Set.Ioc (1 : ℝ) 2 ∪ Set.Ioc (2 : ℝ) 4) := by grind
  have hd12 : Disjoint (Set.Ioc (1 : ℝ) 2) (Set.Ioc (2 : ℝ) 4) := by simp
  have hd01 : Disjoint (Set.Ioc (0 : ℝ) 1)
      (Set.Ioc (1 : ℝ) 2 ∪ Set.Ioc (2 : ℝ) 4) := by simp
  rw [hsplit, setIntegral_union hd01 (measurableSet_Ioc.union measurableSet_Ioc)
    (integrableOn_archimedean_Ioc 0 1 (by norm_num))
    ((integrableOn_archimedean_Ioc 1 2 (by norm_num)).union
      (integrableOn_archimedean_Ioc 2 4 (by norm_num))),
    setIntegral_union hd12 measurableSet_Ioc
      (integrableOn_archimedean_Ioc 1 2 (by norm_num))
      (integrableOn_archimedean_Ioc 2 4 (by norm_num))]
  grind

end NumberField.Odlyzko
