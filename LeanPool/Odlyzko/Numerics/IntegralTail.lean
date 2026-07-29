/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Numerics.Degree
public import LeanPool.Odlyzko.Numerics.Integrability
public import LeanPool.Odlyzko.Numerics.Tail
public import LeanPool.Odlyzko.TestFunction.Bounds
public import LeanPool.Odlyzko.TestFunction.TaylorBound
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! TODO: Add doc-string. -/

@[expose] public section

section

open MeasureTheory Set

namespace NumberField.Odlyzko

/-- An odlyzko deficit polynomial used in the Odlyzko-bound argument. -/
noncomputable def odlyzkoDeficitPolynomial (x : ℝ) : ℝ :=
  1 - tartarAmplitudeLowerSix (odlyzkoScale * x) ^ 2

/-- A deficit c2 used in the Odlyzko-bound argument. -/
noncomputable def deficitC2 : ℝ := 2 * odlyzkoScale ^ 2 / 10
/-- A deficit c4 used in the Odlyzko-bound argument. -/
noncomputable def deficitC4 : ℝ :=
  -(odlyzkoScale ^ 4 / 100 + 2 * odlyzkoScale ^ 4 / 280)
/-- A deficit c6 used in the Odlyzko-bound argument. -/
noncomputable def deficitC6 : ℝ :=
  2 * odlyzkoScale ^ 6 / 15120 +
    2 * (odlyzkoScale ^ 2 / 10) * (odlyzkoScale ^ 4 / 280)
/-- A deficit c8 used in the Odlyzko-bound argument. -/
noncomputable def deficitC8 : ℝ :=
  -((odlyzkoScale ^ 4 / 280) ^ 2 +
    2 * (odlyzkoScale ^ 2 / 10) * (odlyzkoScale ^ 6 / 15120))
/-- A deficit c10 used in the Odlyzko-bound argument. -/
noncomputable def deficitC10 : ℝ :=
  2 * (odlyzkoScale ^ 4 / 280) * (odlyzkoScale ^ 6 / 15120)
/-- A deficit c12 used in the Odlyzko-bound argument. -/
noncomputable def deficitC12 : ℝ :=
  -(odlyzkoScale ^ 6 / 15120) ^ 2

/-- An odlyzko exp polynomial obj used in the Odlyzko-bound argument. -/
noncomputable def odlyzkoExpPolynomialObj : Polynomial ℝ :=
  Polynomial.C deficitC2 *
      (Polynomial.X ^ 2 + 2 * Polynomial.X + 2) +
    Polynomial.C deficitC4 *
      (Polynomial.X ^ 4 + 4 * Polynomial.X ^ 3 + 12 * Polynomial.X ^ 2 +
        24 * Polynomial.X + 24) +
    Polynomial.C deficitC6 *
      (Polynomial.X ^ 6 + 6 * Polynomial.X ^ 5 + 30 * Polynomial.X ^ 4 +
        120 * Polynomial.X ^ 3 + 360 * Polynomial.X ^ 2 + 720 * Polynomial.X + 720) +
    Polynomial.C deficitC8 *
      (Polynomial.X ^ 8 + 8 * Polynomial.X ^ 7 + 56 * Polynomial.X ^ 6 +
        336 * Polynomial.X ^ 5 + 1680 * Polynomial.X ^ 4 + 6720 * Polynomial.X ^ 3 +
        20160 * Polynomial.X ^ 2 + 40320 * Polynomial.X + 40320) +
    Polynomial.C deficitC10 *
      (Polynomial.X ^ 10 + 10 * Polynomial.X ^ 9 + 90 * Polynomial.X ^ 8 +
        720 * Polynomial.X ^ 7 + 5040 * Polynomial.X ^ 6 + 30240 * Polynomial.X ^ 5 +
        151200 * Polynomial.X ^ 4 + 604800 * Polynomial.X ^ 3 +
        1814400 * Polynomial.X ^ 2 + 3628800 * Polynomial.X + 3628800) +
    Polynomial.C deficitC12 *
      (Polynomial.X ^ 12 + 12 * Polynomial.X ^ 11 + 132 * Polynomial.X ^ 10 +
        1320 * Polynomial.X ^ 9 + 11880 * Polynomial.X ^ 8 + 95040 * Polynomial.X ^ 7 +
        665280 * Polynomial.X ^ 6 + 3991680 * Polynomial.X ^ 5 +
        19958400 * Polynomial.X ^ 4 + 79833600 * Polynomial.X ^ 3 +
        239500800 * Polynomial.X ^ 2 + 479001600 * Polynomial.X + 479001600)

/-- An odlyzko exp polynomial used in the Odlyzko-bound argument. -/
noncomputable abbrev odlyzkoExpPolynomial (x : ℝ) : ℝ :=
  odlyzkoExpPolynomialObj.eval x

/-- An odlyzko exp antiderivative used in the Odlyzko-bound argument. -/
noncomputable abbrev odlyzkoExpAntiderivative : ℝ → ℝ :=
  -((Real.exp ∘ Neg.neg) * odlyzkoExpPolynomial)

theorem deficit_polynomial_expansion (x : ℝ) :
    odlyzkoDeficitPolynomial x =
      deficitC2 * x ^ 2 + deficitC4 * x ^ 4 + deficitC6 * x ^ 6 +
      deficitC8 * x ^ 8 + deficitC10 * x ^ 10 + deficitC12 * x ^ 12 := by
  simp only [odlyzkoDeficitPolynomial, tartarAmplitudeLowerSix, deficitC2, deficitC4,
    deficitC6, deficitC8, deficitC10, deficitC12]
  ring

theorem tartarAmplitudeLowerSix_odlyzkoScale_nonneg {x : ℝ}
    (hx0 : 0 ≤ x) (hx4 : x ≤ 4) :
    0 ≤ tartarAmplitudeLowerSix (odlyzkoScale * x) := by
  let z := odlyzkoScale * x
  have hs0 : 0 < odlyzkoScale := odlyzkoScale_pos
  have hz0 : 0 ≤ z := mul_nonneg hs0.le hx0
  have hzmax : z ≤ 82 / 25 := by
    dsimp only [z, odlyzkoScale]
    nlinarith
  have hzsq : z ^ 2 ≤ 11 := by nlinarith [sq_nonneg (z - 82 / 25)]
  have hcorr : 0 ≤ z ^ 4 * (54 - z ^ 2) / 15120 := by
    have hzfour0 : 0 ≤ z ^ 4 := by positivity
    exact div_nonneg (mul_nonneg hzfour0 (by linarith)) (by norm_num)
  have hid :
      tartarAmplitudeLowerSix z =
        1 - z ^ 2 / 10 + z ^ 4 * (54 - z ^ 2) / 15120 := by
    simp only [tartarAmplitudeLowerSix]
    ring
  rw [hid]
  by_cases hz10 : z ^ 2 ≤ 10
  · nlinarith
  · have hz10' : 10 ≤ z ^ 2 := le_of_not_ge hz10
    have hzfour : 100 ≤ z ^ 4 := by nlinarith [sq_nonneg (z ^ 2 - 10)]
    nlinarith

theorem one_sub_tartarTestFunction_le_odlyzkoDeficitPolynomial {x : ℝ}
    (hx0 : 0 ≤ x) (hx4 : x ≤ 4) :
    1 - Tartar.testFunction (odlyzkoScale * x) ≤ odlyzkoDeficitPolynomial x := by
  have harg : |odlyzkoScale * x| ≤ 4 := by
    rw [abs_of_nonneg (mul_nonneg odlyzkoScale_pos.le hx0)]
    calc
      odlyzkoScale * x ≤ odlyzkoScale * 4 :=
        mul_le_mul_of_nonneg_left hx4 odlyzkoScale_pos.le
      _ ≤ 4 := by norm_num [odlyzkoScale]
  have hlower := tartarAmplitudeLowerSix_le harg
  have hq0 := tartarAmplitudeLowerSix_odlyzkoScale_nonneg hx0 hx4
  have hsquares :
      tartarAmplitudeLowerSix (odlyzkoScale * x) ^ 2 ≤
        Tartar.amplitude (odlyzkoScale * x) ^ 2 := by nlinarith
  simpa only [odlyzkoDeficitPolynomial, Tartar.testFunction] using
    (sub_le_sub_left hsquares 1)

theorem odlyzkoDeficitPolynomial_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx4 : x ≤ 4) :
    0 ≤ odlyzkoDeficitPolynomial x := by
  have hq0 := tartarAmplitudeLowerSix_odlyzkoScale_nonneg hx0 hx4
  have harg : |odlyzkoScale * x| ≤ 4 := by
    rw [abs_of_nonneg (mul_nonneg odlyzkoScale_pos.le hx0)]
    calc
      odlyzkoScale * x ≤ odlyzkoScale * 4 :=
        mul_le_mul_of_nonneg_left hx4 odlyzkoScale_pos.le
      _ ≤ 4 := by norm_num [odlyzkoScale]
  have hqle := (tartarAmplitudeLowerSix_le harg).trans
    (le_trans (le_abs_self _) (abs_tartarAmplitude_le_one _))
  simp only [odlyzkoDeficitPolynomial]
  nlinarith

theorem hasDerivAt_odlyzkoExpAntiderivative (x : ℝ) :
    HasDerivAt odlyzkoExpAntiderivative
      (odlyzkoDeficitPolynomial x * Real.exp (-x)) x := by
  have he := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hp := odlyzkoExpPolynomialObj.hasDerivAt (x := x)
  apply ((he.mul hp).neg).congr_deriv
  rw [deficit_polynomial_expansion]
  simp only [Function.comp_apply, odlyzkoExpPolynomialObj,
    Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X_pow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_ofNat,
    zero_mul]
  norm_num
  ring

theorem integral_odlyzkoDeficitPolynomial_mul_exp (a b : ℝ) :
    ∫ x in a..b, odlyzkoDeficitPolynomial x * Real.exp (-x) =
      odlyzkoExpAntiderivative b - odlyzkoExpAntiderivative a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hasDerivAt_odlyzkoExpAntiderivative x)]
  have hc : Continuous
      (fun x : ℝ ↦ odlyzkoDeficitPolynomial x * Real.exp (-x)) := by
    simp only [odlyzkoDeficitPolynomial, tartarAmplitudeLowerSix]
    fun_prop
  exact hc.intervalIntegrable _ _

private theorem exp_neg_nat (n : ℕ) :
    Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
  rw [← Real.exp_nat_mul]
  norm_num

theorem integral_odlyzkoDeficitPolynomial_mul_exp_one_two_lt :
    ∫ x in (1 : ℝ)..2, odlyzkoDeficitPolynomial x * Real.exp (-x) < 29 / 500 := by
  rw [integral_odlyzkoDeficitPolynomial_mul_exp]
  simp only [odlyzkoExpAntiderivative, Pi.neg_apply, Pi.mul_apply, Function.comp_apply,
    odlyzkoExpPolynomial, odlyzkoExpPolynomialObj, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
    Polynomial.eval_ofNat, deficitC2, deficitC4, deficitC6, deficitC8, deficitC10,
    deficitC12, odlyzkoScale]
  have hu := Real.exp_neg_one_lt_d9
  rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, exp_neg_nat]
  nlinarith [sq_nonneg (Real.exp (-1) - 36787944116 / 10 ^ 11)]

theorem integral_odlyzkoDeficitPolynomial_mul_exp_two_four_lt :
    ∫ x in (2 : ℝ)..4, odlyzkoDeficitPolynomial x * Real.exp (-x) < 3 / 40 := by
  rw [integral_odlyzkoDeficitPolynomial_mul_exp]
  simp only [odlyzkoExpAntiderivative, Pi.neg_apply, Pi.mul_apply, Function.comp_apply,
    odlyzkoExpPolynomial, odlyzkoExpPolynomialObj, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
    Polynomial.eval_ofNat, deficitC2, deficitC4, deficitC6, deficitC8, deficitC10,
    deficitC12, odlyzkoScale]
  have hu := Real.exp_neg_one_lt_d9
  have hu0 := Real.exp_pos (-1)
  rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, show (-4 : ℝ) = -(4 : ℕ) by norm_num,
    exp_neg_nat, exp_neg_nat]
  norm_num at hu ⊢
  have hsq :
      Real.exp (-1) ^ 2 < (919698603 / 2500000000 : ℝ) ^ 2 := by
    nlinarith [mul_self_lt_mul_self hu0.le hu]
  nlinarith

/-- An odlyzko deficit quotient used in the Odlyzko-bound argument. -/
noncomputable def odlyzkoDeficitQuotient (x : ℝ) : ℝ :=
  deficitC2 * x + deficitC4 * x ^ 3 + deficitC6 * x ^ 5 +
    deficitC8 * x ^ 7 + deficitC10 * x ^ 9 + deficitC12 * x ^ 11

theorem odlyzkoDeficitPolynomial_div (x : ℝ) :
    odlyzkoDeficitPolynomial x / x = odlyzkoDeficitQuotient x := by
  rw [deficit_polynomial_expansion]
  simp only [odlyzkoDeficitQuotient]
  grind

theorem integral_odlyzkoDeficitPolynomial_div_id_zero_one :
    ∫ x in (0 : ℝ)..1, odlyzkoDeficitPolynomial x / x =
      43765751791833997513324237919 / 669768750000000000000000000000 := by
  simp_rw [odlyzkoDeficitPolynomial_div]
  simp only [odlyzkoDeficitQuotient]
  let F : ℝ → ℝ := fun x ↦
    deficitC2 * x ^ 2 / 2 + deficitC4 * x ^ 4 / 4 + deficitC6 * x ^ 6 / 6 +
      deficitC8 * x ^ 8 / 8 + deficitC10 * x ^ 10 / 10 + deficitC12 * x ^ 12 / 12
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F)]
  · simp only [F, deficitC2, deficitC4, deficitC6, deficitC8, deficitC10, deficitC12,
      odlyzkoScale]
    norm_num
  · intro x _
    dsimp only [F]
    have hderiv := (((((((hasDerivAt_const x deficitC2).mul
      (hasDerivAt_pow 2 x)).div_const 2).add
      (((hasDerivAt_const x deficitC4).mul (hasDerivAt_pow 4 x)).div_const 4)).add
      (((hasDerivAt_const x deficitC6).mul (hasDerivAt_pow 6 x)).div_const 6)).add
      (((hasDerivAt_const x deficitC8).mul (hasDerivAt_pow 8 x)).div_const 8)).add
      (((hasDerivAt_const x deficitC10).mul (hasDerivAt_pow 10 x)).div_const 10)).add
      (((hasDerivAt_const x deficitC12).mul (hasDerivAt_pow 12 x)).div_const 12)
    exact hderiv.congr_deriv (by grind)
  · exact (by fun_prop : Continuous (fun x : ℝ ↦
      deficitC2 * x + deficitC4 * x ^ 3 + deficitC6 * x ^ 5 +
        deficitC8 * x ^ 7 + deficitC10 * x ^ 9 + deficitC12 * x ^ 11))
      |>.intervalIntegrable _ _

end NumberField.Odlyzko

end

section

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

private theorem integral_archimedean_Ioc_le_mul (c lo hi : ℝ)
    (hlo : 0 < lo) (hle : lo ≤ hi) (hhi : hi ≤ 4)
    (hbound : ∀ x : ℝ, lo ≤ x → 1 / Real.sinh x ≤ c * Real.exp (-x)) :
    (∫ x in Set.Ioc lo hi, archimedeanIntegrand odlyzkoScale x) ≤
      c * ∫ x in lo..hi, odlyzkoDeficitPolynomial x * Real.exp (-x) := by
  have hmono :
      (∫ x in Set.Ioc lo hi, archimedeanIntegrand odlyzkoScale x) ≤
        ∫ x in Set.Ioc lo hi,
          c * (odlyzkoDeficitPolynomial x * Real.exp (-x)) := by
    apply integral_mono_ae (integrableOn_archimedean_Ioc lo hi hlo.le)
      (integrableOn_scaled_deficit_exp_Ioc c lo hi)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 ≤ x := (hlo.trans hx.1).le
    have hx4 : x ≤ 4 := hx.2.trans hhi
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr (hlo.trans hx.1)
    have hnum := one_sub_tartarTestFunction_le_odlyzkoDeficitPolynomial hx0 hx4
    have hpoly := odlyzkoDeficitPolynomial_nonneg hx0 hx4
    calc
      archimedeanIntegrand odlyzkoScale x
          ≤ odlyzkoDeficitPolynomial x / Real.sinh x := by
            rw [archimedeanIntegrand]
            exact div_le_div_of_nonneg_right hnum hs.le
      _ = odlyzkoDeficitPolynomial x * (1 / Real.sinh x) := by ring
      _ ≤ odlyzkoDeficitPolynomial x * (c * Real.exp (-x)) := by
            gcongr
            exact hbound x hx.1.le
      _ = c * (odlyzkoDeficitPolynomial x * Real.exp (-x)) := by ring
  calc
    (∫ x in Set.Ioc lo hi, archimedeanIntegrand odlyzkoScale x)
        ≤ ∫ x in Set.Ioc lo hi,
          c * (odlyzkoDeficitPolynomial x * Real.exp (-x)) := hmono
    _ = c * ∫ x in lo..hi, odlyzkoDeficitPolynomial x * Real.exp (-x) := by
          rw [intervalIntegral.integral_of_le hle, integral_const_mul]

theorem integral_archimedean_odlyzkoScale_Ioc_zero_four_le :
    (∫ x in Set.Ioc (0 : ℝ) 4, archimedeanIntegrand odlyzkoScale x) ≤ 9 / 25 := by
  have h01 := integral_archimedean_odlyzkoScale_Ioc_zero_one_le
  have h12 :
      (∫ x in Set.Ioc (1 : ℝ) 2, archimedeanIntegrand odlyzkoScale x) <
        (7 / 3 : ℝ) * (29 / 500) :=
    lt_of_le_of_lt
      (integral_archimedean_Ioc_le_mul (7 / 3) 1 2 one_pos (by norm_num) (by norm_num)
        fun x hx ↦ one_div_sinh_le_seven_thirds_exp hx)
      (mul_lt_mul_of_pos_left
        integral_odlyzkoDeficitPolynomial_mul_exp_one_two_lt (by norm_num))
  have h24 :
      (∫ x in Set.Ioc (2 : ℝ) 4, archimedeanIntegrand odlyzkoScale x) <
        (64 / 31 : ℝ) * (3 / 40) :=
    lt_of_le_of_lt
      (integral_archimedean_Ioc_le_mul (64 / 31) 2 4 two_pos (by norm_num) le_rfl
        fun x hx ↦ one_div_sinh_le_sixty_four_thirty_one_exp hx)
      (mul_lt_mul_of_pos_left
        integral_odlyzkoDeficitPolynomial_mul_exp_two_four_lt (by norm_num))
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

end

namespace NumberField.Odlyzko

theorem abs_archimedeanIntegrand_odlyzkoScale_le_exp {x : ℝ} (hx : 4 ≤ x) :
    |archimedeanIntegrand odlyzkoScale x| ≤
      37 * ((8 / 3 : ℝ) * Real.exp (-x)) := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx0
  have harg : 1 ≤ |odlyzkoScale * x| := by
    rw [abs_of_pos (mul_pos odlyzkoScale_pos hx0)]
    rw [odlyzkoScale]
    grind
  have htest0 := tartarTestFunction_nonneg (odlyzkoScale * x)
  have htest36 := tartarTestFunction_le_thirty_six harg
  have : |1 - Tartar.testFunction (odlyzkoScale * x)| ≤ 37 := by grind
  rw [archimedeanIntegrand, abs_div, abs_of_pos hs]
  calc
    |1 - Tartar.testFunction (odlyzkoScale * x)| / Real.sinh x
        ≤ 37 * (1 / Real.sinh x) := by
          rw [div_eq_mul_inv]
          simp_all
    _ ≤ 37 * ((8 / 3 : ℝ) * Real.exp (-x)) := by
      gcongr
      exact one_div_sinh_le_exp_tail (by linarith)

theorem integrableOn_archimedeanIntegrand_odlyzkoScale_Ioi_four :
    MeasureTheory.IntegrableOn (archimedeanIntegrand odlyzkoScale) (Set.Ioi 4) := by
  have hmajor :
      MeasureTheory.IntegrableOn
        (fun x : ℝ ↦ 37 * ((8 / 3 : ℝ) * Real.exp (-x))) (Set.Ioi 4) :=
    ((integrableOn_exp_neg_Ioi 4).const_mul (8 / 3 : ℝ)).const_mul 37
  apply MeasureTheory.Integrable.mono' hmajor
  · exact (((measurable_const.sub
      (tartarTestFunction_measurable.comp (measurable_const.mul measurable_id))).div
        Real.continuous_sinh.measurable).aestronglyMeasurable)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    exact abs_archimedeanIntegrand_odlyzkoScale_le_exp hx.le

theorem NumericalCertificate.odlyzkoScale_tail_lt :
    (∫ x in Set.Ioi (4 : ℝ), archimedeanIntegrand odlyzkoScale x) < 1 / 25 :=
  NumericalCertificate.integral_archimedeanIntegrand_Ioi_four_lt
    integrableOn_archimedeanIntegrand_odlyzkoScale_Ioi_four

theorem NumericalCertificate.archimedeanIntegral_le_of_compact_bound
    (hcompactInt :
      MeasureTheory.IntegrableOn (archimedeanIntegrand odlyzkoScale) (Set.Ioc 0 4))
    (hcompact :
      (∫ x in Set.Ioc (0 : ℝ) 4, archimedeanIntegrand odlyzkoScale x) ≤ 9 / 25) :
    archimedeanIntegral odlyzkoScale ≤ 2 / 5 := by
  have hunion : Set.Ioc (0 : ℝ) 4 ∪ Set.Ioi 4 = Set.Ioi 0 := by simp
  have hdisjoint : Disjoint (Set.Ioc (0 : ℝ) 4) (Set.Ioi 4) := by simp
  rw [archimedeanIntegral, ← hunion,
    MeasureTheory.setIntegral_union hdisjoint measurableSet_Ioi hcompactInt
      integrableOn_archimedeanIntegrand_odlyzkoScale_Ioi_four]
  linarith [NumericalCertificate.odlyzkoScale_tail_lt]

theorem NumericalCertificate.archimedeanIntegral_le :
    archimedeanIntegral odlyzkoScale ≤ 2 / 5 :=
  NumericalCertificate.archimedeanIntegral_le_of_compact_bound
    ((integrableOn_archimedeanIntegrand_Ioi odlyzkoScale).mono_set <| by
      grind)
    integral_archimedean_odlyzkoScale_Ioc_zero_four_le

end NumberField.Odlyzko
