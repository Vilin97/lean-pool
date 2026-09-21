/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Rosenthal.Truncation

/-! # Scalar Bennett -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open Set
open scoped Topology

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

theorem bennettOptimalLambda_nonneg {v y t : ℝ}
    (hy : 0 < y) (hv : 0 < v) (ht : 0 ≤ t) :
    0 ≤ bennettOptimalLambda v y t := by
  unfold bennettOptimalLambda
  have hratio_nonneg : 0 ≤ t * y / v := by
    exact div_nonneg (mul_nonneg ht hy.le) hv.le
  have hlog_nonneg : 0 ≤ Real.log (1 + t * y / v) := by
    apply Real.log_nonneg
    linarith
  exact div_nonneg hlog_nonneg hy.le

theorem bennettOptimalExponent_eq {v y t : ℝ}
    (hy : 0 < y) (hv : 0 < v) (ht : 0 ≤ t) :
    -bennettOptimalLambda v y t * t
      + (v / y ^ (2 : ℕ))
          * (Real.exp (bennettOptimalLambda v y t * y) - 1 - bennettOptimalLambda v y t * y)
      = -(v / y ^ (2 : ℕ)) * bennettH (t * y / v) := by
  unfold bennettOptimalLambda bennettH
  have hy_ne : y ≠ 0 := hy.ne'
  have hv_ne : v ≠ 0 := hv.ne'
  have harg_pos : 0 < 1 + t * y / v := by
    have : 0 ≤ t * y / v := by
      exact div_nonneg (mul_nonneg ht hy.le) hv.le
    linarith
  have hmuly :
      (Real.log (1 + t * y / v) / y) * y = Real.log (1 + t * y / v) := by
    field_simp [hy_ne]
  rw [hmuly, Real.exp_log harg_pos]
  field_simp [hy_ne, hv_ne]
  ring

theorem integrable_of_abs_le_const
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} {C : ℝ}
    (hXm : AEMeasurable X μ)
    (hXbdd : ∀ᵐ ω ∂μ, |X ω| ≤ C) :
    Integrable X μ := by
  refine Integrable.mono' (integrable_const C) hXm.aestronglyMeasurable ?_
  filter_upwards [hXbdd] with ω hω
  simpa using hω

theorem integrable_pow_two_of_abs_le_const
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} {C : ℝ}
    (hXm : AEMeasurable X μ)
    (hXbdd : ∀ᵐ ω ∂μ, |X ω| ≤ C) :
    Integrable (fun ω => X ω ^ (2 : ℕ)) μ := by
  refine Integrable.mono' (integrable_const (C ^ (2 : ℕ)))
    (by
      fun_prop : AEStronglyMeasurable (fun ω => X ω ^ (2 : ℕ)) μ) ?_
  filter_upwards [hXbdd] with ω hω
  have hsq : X ω ^ (2 : ℕ) ≤ C ^ (2 : ℕ) := by
    exact sq_le_sq' (abs_le.mp hω).1 (abs_le.mp hω).2
  simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ X ω ^ (2 : ℕ))] using hsq

theorem integrable_exp_mul_of_abs_le_const
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} {l y : ℝ}
    (hl : 0 ≤ l)
    (hXm : AEMeasurable X μ)
    (hXbdd : ∀ᵐ ω ∂μ, |X ω| ≤ y) :
    Integrable (fun ω => Real.exp (l * X ω)) μ := by
  refine Integrable.mono' (integrable_const (Real.exp (l * y)))
    (Real.continuous_exp.comp_aestronglyMeasurable
      (hXm.aestronglyMeasurable.const_mul l)) ?_
  filter_upwards [hXbdd] with ω hω
  have hx_le : X ω ≤ y := le_trans (le_abs_self (X ω)) hω
  have hle : l * X ω ≤ l * y := by
    exact mul_le_mul_of_nonneg_left hx_le hl
  have hexp_le : Real.exp (l * X ω) ≤ Real.exp (l * y) := Real.exp_monotone hle
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using hexp_le

/-- The tail term in the second-order exponential remainder series. -/
noncomputable def bennettTailTerm (a : ℝ) (n : ℕ) : ℝ :=
  a ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)

theorem summable_bennettTailTerm (a : ℝ) : Summable (bennettTailTerm a) := by
  simpa [bennettTailTerm] using!
    ((_root_.summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial a))

/-- Scalar Bennett envelope on `[-y, y]`, proved by comparing the exponential
tail series termwise against the quadratic remainder at the endpoint `y`. -/
theorem exp_mul_le_bennettEnvelope_of_abs_le
    {x y l : ℝ}
    (hy : 0 < y) (hl : 0 ≤ l) (hxy : |x| ≤ y) :
    Real.exp (l * x) ≤
      1 + l * x + (x ^ (2 : ℕ) / y ^ (2 : ℕ)) * (Real.exp (l * y) - 1 - l * y) := by
  let tailX : ℕ → ℝ := bennettTailTerm (l * x)
  let tailY : ℕ → ℝ := bennettTailTerm (l * y)
  have htailx_summable : Summable tailX := by
    simpa [tailX] using summable_bennettTailTerm (l * x)
  have htaily_summable : Summable tailY := by
    simpa [tailY] using summable_bennettTailTerm (l * y)
  have htaily_scaled_summable :
      Summable (fun n : ℕ => (x ^ (2 : ℕ) / y ^ (2 : ℕ)) * tailY n) := by
    exact Summable.mul_left (x ^ (2 : ℕ) / y ^ (2 : ℕ)) htaily_summable
  have hx_series :
      Real.exp (l * x) =
        (∑ i ∈ Finset.range 2, (l * x) ^ i / (Nat.factorial i : ℝ)) +
          ∑' n : ℕ, tailX n := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    symm
    exact (Real.summable_pow_div_factorial (l * x)).sum_add_tsum_nat_add 2
  have hy_series :
      Real.exp (l * y) =
        (∑ i ∈ Finset.range 2, (l * y) ^ i / (Nat.factorial i : ℝ)) +
          ∑' n : ℕ, tailY n := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    symm
    exact (Real.summable_pow_div_factorial (l * y)).sum_add_tsum_nat_add 2
  have hheadx :
      (∑ i ∈ Finset.range 2, (l * x) ^ i / (Nat.factorial i : ℝ)) = 1 + l * x := by
    norm_num [Finset.sum_range_succ]
  have hheady :
      (∑ i ∈ Finset.range 2, (l * y) ^ i / (Nat.factorial i : ℝ)) = 1 + l * y := by
    norm_num [Finset.sum_range_succ]
  have hterm :
      ∀ n : ℕ, tailX n ≤ (x ^ (2 : ℕ) / y ^ (2 : ℕ)) * tailY n := by
    intro n
    have habs_mul_le : |l * x| ≤ l * y := by
      rw [abs_mul, abs_of_nonneg hl]
      exact mul_le_mul_of_nonneg_left hxy hl
    have habs_pow_le : |l * x| ^ n ≤ (l * y) ^ n := by
      exact pow_le_pow_left₀ (abs_nonneg (l * x)) habs_mul_le n
    have hnum :
        (l * x) ^ (n + 2) ≤
          (x ^ (2 : ℕ) / y ^ (2 : ℕ)) * (l * y) ^ (n + 2) := by
      have hnum_abs :
          |l * x| ^ (n + 2) ≤
            (x ^ (2 : ℕ) / y ^ (2 : ℕ)) * (l * y) ^ (n + 2) := by
        calc
          |l * x| ^ (n + 2) = |l * x| ^ n * |l * x| ^ (2 : ℕ) := by
            rw [pow_add]
          _ ≤ (l * y) ^ n * |l * x| ^ (2 : ℕ) := by
            gcongr
          _ = (l * y) ^ n * ((l * x) ^ (2 : ℕ)) := by
            rw [sq_abs]
          _ = (l * y) ^ n * (l ^ (2 : ℕ) * x ^ (2 : ℕ)) := by
            ring
          _ = (x ^ (2 : ℕ) / y ^ (2 : ℕ)) * (l * y) ^ (n + 2) := by
            field_simp [hy.ne']
            ring
      have hpow_abs : (l * x) ^ (n + 2) ≤ |l * x| ^ (n + 2) := by
        rw [← abs_pow]
        exact le_abs_self _
      exact le_trans hpow_abs hnum_abs
    have hfac_pos : 0 < (Nat.factorial (n + 2) : ℝ) := by positivity
    calc
      tailX n
        = (l * x) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) := by
            simp [tailX, bennettTailTerm]
      _
        ≤ ((x ^ (2 : ℕ) / y ^ (2 : ℕ)) * (l * y) ^ (n + 2)) / (Nat.factorial (n + 2) : ℝ) := by
          exact div_le_div_of_nonneg_right hnum hfac_pos.le
      _ = (x ^ (2 : ℕ) / y ^ (2 : ℕ)) * tailY n := by
          simp [tailY, bennettTailTerm, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  calc
    Real.exp (l * x)
      = 1 + l * x + ∑' n : ℕ, tailX n := by
          rw [hx_series, hheadx]
    _ ≤ 1 + l * x +
          ∑' n : ℕ, (x ^ (2 : ℕ) / y ^ (2 : ℕ)) * tailY n := by
          have htsum_le :
              ∑' n : ℕ, tailX n ≤ ∑' n : ℕ, (x ^ (2 : ℕ) / y ^ (2 : ℕ)) * tailY n :=
            htailx_summable.tsum_le_tsum hterm htaily_scaled_summable
          linarith
    _ = 1 + l * x +
          (x ^ (2 : ℕ) / y ^ (2 : ℕ)) *
            ∑' n : ℕ, tailY n := by
          rw [← Summable.tsum_mul_left _ htaily_summable]
    _ = 1 + l * x + (x ^ (2 : ℕ) / y ^ (2 : ℕ)) * (Real.exp (l * y) - 1 - l * y) := by
          rw [hy_series, hheady]
          ring

/-- One-variable Bennett mgf estimate in the pre-exponential `1 + A` form. -/
theorem mgf_le_one_add_bennett_of_abs_le_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {y l : ℝ}
    (hy : 0 < y) (hl : 0 ≤ l)
    (hXm : AEMeasurable X μ)
    (hXbdd : ∀ᵐ ω ∂μ, |X ω| ≤ y)
    (hXmean : μ[X] = 0) :
    mgf X μ l ≤
      1 + (ProbabilityTheory.moment X 2 μ / y ^ (2 : ℕ)) *
        (Real.exp (l * y) - 1 - l * y) := by
  let C : ℝ := Real.exp (l * y) - 1 - l * y
  let quad : Ω → ℝ := fun ω => X ω ^ (2 : ℕ) / y ^ (2 : ℕ)
  let rhs : Ω → ℝ := fun ω => 1 + l * X ω + quad ω * C
  have hX_int : Integrable X μ :=
    integrable_of_abs_le_const (μ := μ) hXm hXbdd
  have hX2_int : Integrable (fun ω => X ω ^ (2 : ℕ)) μ :=
    integrable_pow_two_of_abs_le_const (μ := μ) hXm hXbdd
  have hquad_int : Integrable quad μ := by
    simpa [quad, div_eq_mul_inv] using hX2_int.mul_const ((y ^ (2 : ℕ))⁻¹)
  have hExp_int : Integrable (fun ω => Real.exp (l * X ω)) μ :=
    integrable_exp_mul_of_abs_le_const (μ := μ) hl hXm hXbdd
  have hrhs_int : Integrable rhs μ := by
    have hsplit_rhs :
        rhs = (fun _ : Ω => (1 : ℝ)) + ((fun ω => l * X ω) + fun ω => quad ω * C) := by
      funext ω
      simp [rhs, add_assoc]
    rw [hsplit_rhs]
    exact (integrable_const (1 : ℝ)).add ((hX_int.const_mul l).add (hquad_int.mul_const C))
  have hpointwise :
      ∀ᵐ ω ∂μ, Real.exp (l * X ω) ≤ rhs ω := by
    filter_upwards [hXbdd] with ω hω
    simpa [rhs, quad] using exp_mul_le_bennettEnvelope_of_abs_le hy hl hω
  calc
    mgf X μ l = ∫ ω, Real.exp (l * X ω) ∂μ := rfl
    _ ≤ ∫ ω, rhs ω ∂μ := integral_mono_ae hExp_int hrhs_int hpointwise
    _ = 1 + l * μ[X] + (ProbabilityTheory.moment X 2 μ / y ^ (2 : ℕ)) * C := by
        have hlin_int : Integrable (fun ω => l * X ω) μ := hX_int.const_mul l
        have hquadC_int : Integrable (fun ω => C * quad ω) μ := hquad_int.const_mul C
        have hcalc :
            ∫ ω, 1 + l * X ω + C * quad ω ∂μ =
              1 + l * μ[X] + (ProbabilityTheory.moment X 2 μ / y ^ (2 : ℕ)) * C := by
          calc
            ∫ ω, 1 + l * X ω + C * quad ω ∂μ
              = ∫ ω, ((fun ω => (1 : ℝ) + l * X ω) + fun ω => C * quad ω) ω ∂μ := by
                  simp [add_assoc]
            _ = ∫ ω, (1 : ℝ) + l * X ω ∂μ + ∫ ω, C * quad ω ∂μ := by
                  simpa [Pi.add_apply] using
                    (integral_add ((integrable_const (1 : ℝ)).add hlin_int) hquadC_int)
            _ = (∫ ω, (fun _ : Ω => (1 : ℝ)) ω ∂μ + ∫ ω, l * X ω ∂μ) + ∫ ω, C * quad ω ∂μ := by
                  congr 1
                  simpa [Pi.add_apply] using
                    (integral_add (integrable_const (1 : ℝ)) hlin_int)
            _ = 1 + l * μ[X] + C * ∫ ω, quad ω ∂μ := by
                  have hquad_scaled : ∫ ω, C * quad ω ∂μ = C * ∫ ω, quad ω ∂μ := by
                    simpa using integral_const_mul C quad
                  rw [integral_const, integral_const_mul, hquad_scaled]
                  simp [smul_eq_mul]
            _ = 1 + l * μ[X] + C * (ProbabilityTheory.moment X 2 μ / y ^ (2 : ℕ)) := by
                  congr 1
                  simp [quad, ProbabilityTheory.moment, integral_div]
            _ = 1 + l * μ[X] + (ProbabilityTheory.moment X 2 μ / y ^ (2 : ℕ)) * C := by
                  ring
        simpa [rhs, mul_comm, mul_left_comm, mul_assoc] using hcalc
    _ = 1 + (ProbabilityTheory.moment X 2 μ / y ^ (2 : ℕ)) * C := by
        rw [hXmean]
        ring

/-- One-variable Bennett mgf estimate for a centered variable bounded by `y`. -/
theorem mgf_le_exp_bennett_of_abs_le_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {y l : ℝ}
    (hy : 0 < y) (hl : 0 ≤ l)
    (hXm : AEMeasurable X μ)
    (hXbdd : ∀ᵐ ω ∂μ, |X ω| ≤ y)
    (hXmean : μ[X] = 0) :
    mgf X μ l ≤
      Real.exp
        ((ProbabilityTheory.moment X 2 μ / y ^ (2 : ℕ)) *
          (Real.exp (l * y) - 1 - l * y)) := by
  have hmoment_nonneg : 0 ≤ ProbabilityTheory.moment X 2 μ := by
    simp [ProbabilityTheory.moment]
    positivity
  have hgap_nonneg : 0 ≤ Real.exp (l * y) - 1 - l * y := by
    have h := Real.add_one_le_exp (l * y)
    linarith
  have hA_nonneg :
      0 ≤
        (ProbabilityTheory.moment X 2 μ / y ^ (2 : ℕ)) *
          (Real.exp (l * y) - 1 - l * y) := by
    refine mul_nonneg ?_ hgap_nonneg
    exact div_nonneg hmoment_nonneg (pow_nonneg hy.le _)
  calc
    mgf X μ l
      ≤ 1 + (ProbabilityTheory.moment X 2 μ / y ^ (2 : ℕ)) *
          (Real.exp (l * y) - 1 - l * y) := by
          exact mgf_le_one_add_bennett_of_abs_le_of_integral_eq_zero
            (μ := μ) hy hl hXm hXbdd hXmean
    _ ≤ Real.exp
          ((ProbabilityTheory.moment X 2 μ / y ^ (2 : ℕ)) *
            (Real.exp (l * y) - 1 - l * y)) := by
          simpa [add_comm] using Real.add_one_le_exp
            ((ProbabilityTheory.moment X 2 μ / y ^ (2 : ℕ)) *
              (Real.exp (l * y) - 1 - l * y))

/-- A Bennett-type moment-generating-function bound implies the corresponding
upper-tail estimate after Chernoff optimization. -/
theorem measureReal_upperTailEvent_le_of_mgf_le_bennett
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} {v y a : ℝ}
    (hy : 0 < y) (hv : 0 < v) (ha : 0 ≤ a)
    (h_int : ∀ l, 0 ≤ l → Integrable (fun ω => Real.exp (l * X ω)) μ)
    (hmgf : ∀ l, 0 ≤ l →
      mgf X μ l ≤
        Real.exp ((v / y ^ (2 : ℕ)) * (Real.exp (l * y) - 1 - l * y))) :
    μ.real (upperTailEvent X a) ≤
      Real.exp (-(v / y ^ (2 : ℕ)) * bennettH (a * y / v)) := by
  let l : ℝ := bennettOptimalLambda v y a
  have hl_nonneg : 0 ≤ l := bennettOptimalLambda_nonneg hy hv ha
  have hsubset : upperTailEvent X a ⊆ {ω | a ≤ X ω} := by
    intro ω hω
    simpa [upperTailEvent] using (le_of_lt hω)
  refine (measureReal_mono (s₂ := {ω | a ≤ X ω}) hsubset).trans ?_
  calc
    μ.real {ω | a ≤ X ω}
      ≤ Real.exp (-l * a) * mgf X μ l := by
        exact measure_ge_le_exp_mul_mgf
          (μ := μ) (X := X) (ε := a) (t := l) hl_nonneg (h_int l hl_nonneg)
    _ ≤ Real.exp (-l * a) *
          Real.exp ((v / y ^ (2 : ℕ)) * (Real.exp (l * y) - 1 - l * y)) := by
        gcongr
        exact hmgf l hl_nonneg
    _ = Real.exp (-(v / y ^ (2 : ℕ)) * bennettH (a * y / v)) := by
        rw [← Real.exp_add]
        congr 1
        simpa [l] using bennettOptimalExponent_eq hy hv ha

/-- Finite independent sums inherit Bennett-form mgf bounds with the variances
adding linearly. -/
theorem mgf_finset_sum_le_of_iIndepFun_of_mgf_le_bennett
    {X : ι → Ω → ℝ} {v : ι → ℝ} {s : Finset ι} {y l : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hmgf : ∀ i ∈ s,
      mgf (X i) μ l ≤
        Real.exp ((v i / y ^ (2 : ℕ)) * (Real.exp (l * y) - 1 - l * y))) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ l ≤
      Real.exp (((∑ i ∈ s, v i) / y ^ (2 : ℕ)) * (Real.exp (l * y) - 1 - l * y)) := by
  calc
    mgf (fun ω => ∑ i ∈ s, X i ω) μ l = ∏ i ∈ s, mgf (X i) μ l := by
      have hsumfun : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
        funext ω
        simp [Finset.sum_apply]
      rw [hsumfun]
      exact h_indep.mgf_sum (t := l) h_meas s
    _ ≤ ∏ i ∈ s,
          Real.exp ((v i / y ^ (2 : ℕ)) * (Real.exp (l * y) - 1 - l * y)) := by
      refine Finset.prod_le_prod ?_ hmgf
      intro i hi
      exact mgf_nonneg
    _ = Real.exp (∑ i ∈ s,
          (v i / y ^ (2 : ℕ)) * (Real.exp (l * y) - 1 - l * y)) := by
      rw [← Real.exp_sum]
    _ = Real.exp (((∑ i ∈ s, v i) / y ^ (2 : ℕ)) * (Real.exp (l * y) - 1 - l * y)) := by
      let C : ℝ := Real.exp (l * y) - 1 - l * y
      congr 1
      calc
        ∑ i ∈ s, v i / y ^ (2 : ℕ) * (Real.exp (l * y) - 1 - l * y)
            = ∑ i ∈ s, v i * ((y ^ (2 : ℕ))⁻¹ * C) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [C, div_eq_mul_inv]
                ring
        _ = (∑ i ∈ s, v i) * ((y ^ (2 : ℕ))⁻¹ * C) := by
              rw [Finset.sum_mul]
        _ = ((∑ i ∈ s, v i) / y ^ (2 : ℕ)) * (Real.exp (l * y) - 1 - l * y) := by
              simp [C, div_eq_mul_inv]
              ring

/-- Bennett tail bounds for finite independent sums, assuming Bennett-form mgf
bounds for each summand. -/
theorem measureReal_upperTailEvent_finset_sum_le_of_iIndepFun_of_mgf_le_bennett
    [IsFiniteMeasure μ]
    {X : ι → Ω → ℝ} {v : ι → ℝ} {s : Finset ι} {y a : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hy : 0 < y)
    (hv : 0 < ∑ i ∈ s, v i)
    (ha : 0 ≤ a)
    (h_int : ∀ i ∈ s, ∀ l, 0 ≤ l → Integrable (fun ω => Real.exp (l * X i ω)) μ)
    (hmgf : ∀ i ∈ s, ∀ l, 0 ≤ l →
      mgf (X i) μ l ≤
        Real.exp ((v i / y ^ (2 : ℕ)) * (Real.exp (l * y) - 1 - l * y))) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      Real.exp (-
        (((∑ i ∈ s, v i) / y ^ (2 : ℕ)) * bennettH (a * y / (∑ i ∈ s, v i)))) := by
  simpa [neg_mul] using
    (measureReal_upperTailEvent_le_of_mgf_le_bennett
      (μ := μ)
      (X := fun ω => ∑ i ∈ s, X i ω)
      (v := ∑ i ∈ s, v i)
      (y := y)
      (a := a)
      hy hv ha
      (by
        intro l hl
        simpa [Finset.sum_apply] using
          (ProbabilityTheory.iIndepFun.integrable_exp_mul_sum
            (μ := μ) (X := X) (t := l) h_indep h_meas (s := s)
            (fun i hi => h_int i hi l hl)))
      (by
        intro l hl
        exact mgf_finset_sum_le_of_iIndepFun_of_mgf_le_bennett
          (μ := μ) (X := X) (v := v) (s := s) (y := y) (l := l)
          h_indep h_meas (fun i hi => hmgf i hi l hl)))

/-- Bounded centered independent summands satisfy the project Bennett mgf bound
with variance proxy given by the sum of second moments. -/
theorem mgf_finset_sum_le_bennett_of_iIndepFun_of_abs_le_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {y l : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hy : 0 < y) (hl : 0 ≤ l)
    (hXbdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ y)
    (hXmean : ∀ i ∈ s, μ[X i] = 0) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ l ≤
      Real.exp
        (((∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) / y ^ (2 : ℕ)) *
          (Real.exp (l * y) - 1 - l * y)) := by
  exact mgf_finset_sum_le_of_iIndepFun_of_mgf_le_bennett
    (μ := μ)
    (X := X)
    (v := fun i => ProbabilityTheory.moment (X i) 2 μ)
    (s := s)
    (y := y)
    (l := l)
    h_indep
    h_meas
    (fun i hi =>
      mgf_le_exp_bennett_of_abs_le_of_integral_eq_zero
        (μ := μ)
        (X := X i)
        (y := y)
        (l := l)
        hy
        hl
        (h_meas i).aemeasurable
        (hXbdd i hi)
        (hXmean i hi))

/-- Bennett upper-tail estimate for finite sums of bounded centered independent
real random variables. -/
theorem measureReal_upperTailEvent_finset_sum_le_bennett_of_iIndepFun_of_abs_le_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {y a : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hy : 0 < y)
    (hv : 0 < ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)
    (ha : 0 ≤ a)
    (hXbdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ y)
    (hXmean : ∀ i ∈ s, μ[X i] = 0) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      Real.exp
        (-
          (((∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) / y ^ (2 : ℕ)) *
            bennettH (a * y / (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)))) := by
  exact measureReal_upperTailEvent_finset_sum_le_of_iIndepFun_of_mgf_le_bennett
    (μ := μ)
    (X := X)
    (v := fun i => ProbabilityTheory.moment (X i) 2 μ)
    (s := s)
    (y := y)
    (a := a)
    h_indep
    h_meas
    hy
    hv
    ha
    (by
      intro i hi l hl
      exact integrable_exp_mul_of_abs_le_const
        (μ := μ)
        (X := X i)
        (l := l)
        (y := y)
        hl
        (h_meas i).aemeasurable
        (hXbdd i hi))
    (by
      intro i hi l hl
      exact mgf_le_exp_bennett_of_abs_le_of_integral_eq_zero
        (μ := μ)
        (X := X i)
        (y := y)
        (l := l)
        hy
        hl
        (h_meas i).aemeasurable
        (hXbdd i hi)
        (hXmean i hi))

/-- Bennett absolute-tail estimate for finite sums of bounded centered independent
real random variables. -/
theorem measureReal_absTailEvent_finset_sum_le_bennett_of_iIndepFun_of_abs_le_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {y a : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hy : 0 < y)
    (hv : 0 < ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)
    (ha : 0 ≤ a)
    (hXbdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ y)
    (hXmean : ∀ i ∈ s, μ[X i] = 0) :
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      2 * Real.exp
        (-
          (((∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) / y ^ (2 : ℕ)) *
            bennettH (a * y / (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)))) := by
  let S : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω
  let Xneg : ι → Ω → ℝ := fun i ω => -X i ω
  let B : ℝ :=
    Real.exp
      (-
        (((∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) / y ^ (2 : ℕ)) *
          bennettH (a * y / (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))))
  have hsubset :
      absTailEvent S a ⊆ upperTailEvent S a ∪ upperTailEvent (fun ω => -S ω) a := by
    intro ω hω
    rw [mem_union, mem_upperTailEvent, mem_upperTailEvent]
    exact lt_abs.mp (by simpa [absTailEvent, upperTailEvent] using hω)
  have h_indep_neg : iIndepFun Xneg μ := by
    simpa [Xneg, Function.comp] using!
      h_indep.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
  have h_meas_neg : ∀ i, Measurable (Xneg i) := by
    intro i
    simpa [Xneg] using h_meas i
  have hv_neg : 0 < ∑ i ∈ s, ProbabilityTheory.moment (Xneg i) 2 μ := by
    simpa [Xneg, ProbabilityTheory.moment] using hv
  have hXbdd_neg : ∀ i ∈ s, ∀ᵐ ω ∂μ, |Xneg i ω| ≤ y := by
    intro i hi
    simpa [Xneg] using hXbdd i hi
  have hXmean_neg : ∀ i ∈ s, μ[Xneg i] = 0 := by
    intro i hi
    simpa [Xneg, integral_neg] using congrArg Neg.neg (hXmean i hi)
  have hupper : μ.real (upperTailEvent S a) ≤ B := by
    simpa [S, B] using
      (measureReal_upperTailEvent_finset_sum_le_bennett_of_iIndepFun_of_abs_le_of_integral_eq_zero
      (μ := μ)
      (X := X)
      (s := s)
      (y := y)
      (a := a)
      h_indep
      h_meas
      hy
      hv
      ha
      hXbdd
      hXmean)
  have hupper_neg : μ.real (upperTailEvent (fun ω => -S ω) a) ≤ B := by
    simpa [S, Xneg, B, ProbabilityTheory.moment, Finset.sum_neg_distrib] using
      (measureReal_upperTailEvent_finset_sum_le_bennett_of_iIndepFun_of_abs_le_of_integral_eq_zero
        (μ := μ)
        (X := Xneg)
        (s := s)
        (y := y)
        (a := a)
        h_indep_neg
        h_meas_neg
        hy
        hv_neg
        ha
        hXbdd_neg
        hXmean_neg)
  have hsum :
      μ.real (upperTailEvent S a) + μ.real (upperTailEvent (fun ω => -S ω) a) ≤ B + B :=
    add_le_add hupper hupper_neg
  calc
    μ.real (absTailEvent S a) ≤
        μ.real (upperTailEvent S a ∪ upperTailEvent (fun ω => -S ω) a) := by
          exact measureReal_mono hsubset
    _ ≤ μ.real (upperTailEvent S a) + μ.real (upperTailEvent (fun ω => -S ω) a) := by
          exact measureReal_union_le _ _
    _ ≤ B + B := hsum
    _ = 2 * B := by ring
    _ =
        2 * Real.exp
          (-
            (((∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) / y ^ (2 : ℕ)) *
              bennettH (a * y / (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)))) := by
          rfl

end
end IndependentSums
end Homogenization
