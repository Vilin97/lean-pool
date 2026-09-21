/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Rosenthal.ScalarBennett

/-! # Centered Truncation -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open Set
open scoped Topology

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Bennett mgf bound for the finite sum of centered bounded truncations. -/
theorem mgf_centeredFinsetSum_absTruncation_le_bennett
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι} {y l : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (hy : 0 < y) (hl : 0 ≤ l)
    (hr_nonneg : ∀ i ∈ s, 0 ≤ r i)
    (hr_bdd : ∀ i ∈ s, 2 * r i ≤ y) :
    mgf (centeredFinsetSum (fun i => absTruncation (X i) (r i)) μ s) μ l ≤
      Real.exp
        (((∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ) /
            y ^ (2 : ℕ)) *
          (Real.exp (l * y) - 1 - l * y)) := by
  let Y : ι → Ω → ℝ := centeredAbsTruncationFamily X r μ
  have h_indepY : iIndepFun Y μ :=
    centeredAbsTruncationFamily_iIndepFun (μ := μ) (X := X) (r := r) h_indep
  have h_measY : ∀ i, Measurable (Y i) :=
    centeredAbsTruncationFamily_measurable (μ := μ) (X := X) (r := r) h_meas
  have h_bddY : ∀ i ∈ s, ∀ᵐ ω ∂μ, |Y i ω| ≤ y := by
    intro i hi
    exact Filter.Eventually.of_forall fun ω =>
      (abs_centeredAbsTruncationFamily_le_two_mul
        (μ := μ) (X := X) (r := r) (i := i) (h_meas i) (h_int i hi) (hr_nonneg i hi) ω).trans
        (hr_bdd i hi)
  have h_meanY : ∀ i ∈ s, μ[Y i] = 0 := by
    intro i hi
    exact centeredAbsTruncationFamily_integral_eq_zero
      (μ := μ) (X := X) (r := r) (i := i) (h_meas i) (h_int i hi)
  have hsum_eq :
      (fun ω => ∑ i ∈ s, Y i ω) =
        centeredFinsetSum (fun i => absTruncation (X i) (r i)) μ s := by
    simpa [Y] using
      (sum_centeredAbsTruncationFamily_eq_centeredFinsetSum_absTruncation
        (μ := μ) (X := X) (r := r) (s := s))
  rw [← hsum_eq]
  exact
    (mgf_finset_sum_le_bennett_of_iIndepFun_of_abs_le_of_integral_eq_zero
      (μ := μ) (X := Y) (s := s) (y := y) (l := l)
      h_indepY h_measY hy hl h_bddY h_meanY)

/-- Bennett upper-tail bound for the finite sum of centered bounded truncations. -/
theorem measureReal_upperTailEvent_centeredFinsetSum_absTruncation_le_bennett
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι} {y a : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (hy : 0 < y)
    (hv : 0 < ∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ)
    (ha : 0 ≤ a)
    (hr_nonneg : ∀ i ∈ s, 0 ≤ r i)
    (hr_bdd : ∀ i ∈ s, 2 * r i ≤ y) :
    μ.real (upperTailEvent (centeredFinsetSum (fun i => absTruncation (X i) (r i)) μ s) a) ≤
      Real.exp
        (-
          (((∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ) /
              y ^ (2 : ℕ)) *
            bennettH
              (a * y /
                (∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ)))) := by
  let Y : ι → Ω → ℝ := centeredAbsTruncationFamily X r μ
  have h_indepY : iIndepFun Y μ :=
    centeredAbsTruncationFamily_iIndepFun (μ := μ) (X := X) (r := r) h_indep
  have h_measY : ∀ i, Measurable (Y i) :=
    centeredAbsTruncationFamily_measurable (μ := μ) (X := X) (r := r) h_meas
  have h_bddY : ∀ i ∈ s, ∀ᵐ ω ∂μ, |Y i ω| ≤ y := by
    intro i hi
    exact Filter.Eventually.of_forall fun ω =>
      (abs_centeredAbsTruncationFamily_le_two_mul
        (μ := μ) (X := X) (r := r) (i := i) (h_meas i) (h_int i hi) (hr_nonneg i hi) ω).trans
        (hr_bdd i hi)
  have h_meanY : ∀ i ∈ s, μ[Y i] = 0 := by
    intro i hi
    exact centeredAbsTruncationFamily_integral_eq_zero
      (μ := μ) (X := X) (r := r) (i := i) (h_meas i) (h_int i hi)
  have hsum_eq :
      (fun ω => ∑ i ∈ s, Y i ω) =
        centeredFinsetSum (fun i => absTruncation (X i) (r i)) μ s := by
    simpa [Y] using
      (sum_centeredAbsTruncationFamily_eq_centeredFinsetSum_absTruncation
        (μ := μ) (X := X) (r := r) (s := s))
  rw [← hsum_eq]
  exact
    (measureReal_upperTailEvent_finset_sum_le_bennett_of_iIndepFun_of_abs_le_of_integral_eq_zero
      (μ := μ) (X := Y) (s := s) (y := y) (a := a)
      h_indepY h_measY hy hv ha h_bddY h_meanY)

/-- Bennett absolute-tail bound for the finite sum of centered bounded truncations. -/
theorem measureReal_absTailEvent_centeredFinsetSum_absTruncation_le_bennett
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι} {y a : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (hy : 0 < y)
    (hv : 0 < ∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ)
    (ha : 0 ≤ a)
    (hr_nonneg : ∀ i ∈ s, 0 ≤ r i)
    (hr_bdd : ∀ i ∈ s, 2 * r i ≤ y) :
    μ.real (absTailEvent (centeredFinsetSum (fun i => absTruncation (X i) (r i)) μ s) a) ≤
      2 * Real.exp
        (-
          (((∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ) /
              y ^ (2 : ℕ)) *
            bennettH
              (a * y /
                (∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ)))) := by
  let Y : ι → Ω → ℝ := centeredAbsTruncationFamily X r μ
  have h_indepY : iIndepFun Y μ :=
    centeredAbsTruncationFamily_iIndepFun (μ := μ) (X := X) (r := r) h_indep
  have h_measY : ∀ i, Measurable (Y i) :=
    centeredAbsTruncationFamily_measurable (μ := μ) (X := X) (r := r) h_meas
  have h_bddY : ∀ i ∈ s, ∀ᵐ ω ∂μ, |Y i ω| ≤ y := by
    intro i hi
    exact Filter.Eventually.of_forall fun ω =>
      (abs_centeredAbsTruncationFamily_le_two_mul
        (μ := μ) (X := X) (r := r) (i := i) (h_meas i) (h_int i hi) (hr_nonneg i hi) ω).trans
        (hr_bdd i hi)
  have h_meanY : ∀ i ∈ s, μ[Y i] = 0 := by
    intro i hi
    exact centeredAbsTruncationFamily_integral_eq_zero
      (μ := μ) (X := X) (r := r) (i := i) (h_meas i) (h_int i hi)
  have hsum_eq :
      (fun ω => ∑ i ∈ s, Y i ω) =
        centeredFinsetSum (fun i => absTruncation (X i) (r i)) μ s := by
    simpa [Y] using
      (sum_centeredAbsTruncationFamily_eq_centeredFinsetSum_absTruncation
        (μ := μ) (X := X) (r := r) (s := s))
  rw [← hsum_eq]
  exact
    (measureReal_absTailEvent_finset_sum_le_bennett_of_iIndepFun_of_abs_le_of_integral_eq_zero
      (μ := μ) (X := Y) (s := s) (y := y) (a := a)
      h_indepY h_measY hy hv ha h_bddY h_meanY)

/-- Splitting the centered sum into bounded truncation plus tail yields an
absolute-tail bound with a Bennett term for the truncation piece and a residual
tail term for the large-value part. -/
theorem measureReal_absTailEvent_centeredFinsetSum_le_bennett_add_tail
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι} {y a b : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (hy : 0 < y)
    (hv : 0 < ∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ)
    (ha : 0 ≤ a)
    (hr_nonneg : ∀ i ∈ s, 0 ≤ r i)
    (hr_bdd : ∀ i ∈ s, 2 * r i ≤ y) :
    μ.real (absTailEvent (centeredFinsetSum X μ s) (a + b)) ≤
      2 * Real.exp
        (-
          (((∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ) /
              y ^ (2 : ℕ)) *
            bennettH
              (a * y /
                (∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ)))) +
        μ.real
          (absTailEvent (centeredFinsetSum (fun i => absTailIndicator (X i) (r i)) μ s) b) := by
  have hTrunc_int : ∀ i ∈ s, Integrable (absTruncation (X i) (r i)) μ := by
    intro i hi
    exact integrable_absTruncation_of_integrable (h_meas i) (h_int i hi)
  have hTail_int : ∀ i ∈ s, Integrable (absTailIndicator (X i) (r i)) μ := by
    intro i hi
    exact integrable_absTailIndicator_of_integrable (h_meas i) (h_int i hi)
  refine (measureReal_absTailEvent_centeredFinsetSum_le_truncation_add_tail
    (μ := μ) (X := X) (r := r) (s := s) hTrunc_int hTail_int).trans ?_
  gcongr
  exact measureReal_absTailEvent_centeredFinsetSum_absTruncation_le_bennett
    (μ := μ) (X := X) (r := r) (s := s) (y := y) (a := a)
    h_indep h_meas h_int hy hv ha hr_nonneg hr_bdd

/-- The residual centered tail piece is controlled by the first moments of the
large-value tails via Markov's inequality and the bound
`∫ |Y - E[Y]| ≤ 2 ∫ |Y|`. -/
theorem measureReal_absTailEvent_centeredFinsetSum_absTailIndicator_le_two_mul_div
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι} {b : ℝ}
    (hb : 0 < b)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ) :
    μ.real (absTailEvent (centeredFinsetSum (fun i => absTailIndicator (X i) (r i)) μ s) b) ≤
      (2 * ∑ i ∈ s, ∫ ω, |absTailIndicator (X i) (r i) ω| ∂μ) / b := by
  let Z : ι → Ω → ℝ :=
    fun i ω => absTailIndicator (X i) (r i) ω - μ[absTailIndicator (X i) (r i)]
  let Y : ι → Ω → ℝ := fun i ω => |Z i ω|
  let F : Ω → ℝ := Finset.sum s Y
  have hY_nonneg : ∀ i ∈ s, ∀ ω, 0 ≤ Y i ω := by
    intro i hi ω
    exact abs_nonneg _
  have hY_int : ∀ i ∈ s, Integrable (Y i) μ := by
    intro i hi
    have hTail_int : Integrable (absTailIndicator (X i) (r i)) μ :=
      integrable_absTailIndicator_of_integrable (h_meas i) (h_int i hi)
    exact (hTail_int.sub (integrable_const _)).norm
  have hsubset :
      absTailEvent (centeredFinsetSum (fun i => absTailIndicator (X i) (r i)) μ s) b ⊆
        upperTailEvent F b := by
    intro ω hω
    change b < |∑ i ∈ s, Z i ω| at hω
    change b < F ω
    exact lt_of_lt_of_le hω
      (by simpa [F, Y, Z] using (Finset.abs_sum_le_sum_abs (f := fun i => Z i ω) (s := s)))
  have hF_nonneg : 0 ≤ᵐ[μ] F := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    simpa [F] using Finset.sum_nonneg fun i hi => hY_nonneg i hi ω
  have hF_int : Integrable F μ := by
    simpa [F] using integrable_finsetSum' s hY_int
  have hmarkov :
      μ.real (upperTailEvent F b) ≤
        (∑ i ∈ s, ∫ ω, Y i ω ∂μ) / b := by
    have hmono :
        μ.real (upperTailEvent F b) ≤
          μ.real {ω | b ≤ F ω} := by
      refine measureReal_mono ?_
      intro ω hω
      show b ≤ F ω
      exact le_of_lt (by simpa [F, upperTailEvent] using hω)
    have hmul :
        b * μ.real (upperTailEvent F b) ≤
          ∑ i ∈ s, ∫ ω, Y i ω ∂μ := by
      calc
        b * μ.real (upperTailEvent F b)
            ≤ b * μ.real {ω | b ≤ F ω} := by
              exact mul_le_mul_of_nonneg_left hmono hb.le
        _ ≤ ∫ ω, ∑ i ∈ s, Y i ω ∂μ := by
              simpa [F] using
                (mul_meas_ge_le_integral_of_nonneg (μ := μ) hF_nonneg hF_int b)
        _ = ∑ i ∈ s, ∫ ω, Y i ω ∂μ := by
              rw [integral_finsetSum s hY_int]
    exact (le_div_iff₀' hb).2 hmul
  have hsum_le :
      ∑ i ∈ s, ∫ ω, Y i ω ∂μ ≤
        ∑ i ∈ s, 2 * ∫ ω, |absTailIndicator (X i) (r i) ω| ∂μ := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hTail_int : Integrable (absTailIndicator (X i) (r i)) μ :=
      integrable_absTailIndicator_of_integrable (h_meas i) (h_int i hi)
    simpa [Y, Z] using
      (integral_abs_sub_integral_le_two_mul
        (μ := μ) (Y := absTailIndicator (X i) (r i)) hTail_int)
  calc
    μ.real (absTailEvent (centeredFinsetSum (fun i => absTailIndicator (X i) (r i)) μ s) b)
        ≤ μ.real (upperTailEvent F b) := by
            exact measureReal_mono hsubset
    _ ≤ (∑ i ∈ s, ∫ ω, Y i ω ∂μ) / b := hmarkov
    _ ≤ (∑ i ∈ s, 2 * ∫ ω, |absTailIndicator (X i) (r i) ω| ∂μ) / b := by
          exact div_le_div_of_nonneg_right hsum_le hb.le
    _ = (2 * ∑ i ∈ s, ∫ ω, |absTailIndicator (X i) (r i) ω| ∂μ) / b := by
          congr 1
          rw [Finset.mul_sum]

/-- Combined note-facing tail estimate: the centered sum is bounded by the
Bennett truncation term plus an explicit first-moment tail contribution. -/
theorem measureReal_absTailEvent_centeredFinsetSum_le_bennett_add_tailIntegrals
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι} {y a b : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (hy : 0 < y)
    (hv : 0 < ∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ)
    (ha : 0 ≤ a)
    (hb : 0 < b)
    (hr_nonneg : ∀ i ∈ s, 0 ≤ r i)
    (hr_bdd : ∀ i ∈ s, 2 * r i ≤ y) :
    μ.real (absTailEvent (centeredFinsetSum X μ s) (a + b)) ≤
      2 * Real.exp
        (-
          (((∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ) /
              y ^ (2 : ℕ)) *
            bennettH
              (a * y /
                (∑ i ∈ s, ProbabilityTheory.moment (centeredAbsTruncationFamily X r μ i) 2 μ)))) +
        (2 * ∑ i ∈ s, ∫ ω, |absTailIndicator (X i) (r i) ω| ∂μ) / b := by
  refine (measureReal_absTailEvent_centeredFinsetSum_le_bennett_add_tail
    (μ := μ) (X := X) (r := r) (s := s) (y := y) (a := a) (b := b)
    h_indep h_meas h_int hy hv ha hr_nonneg hr_bdd).trans ?_
  gcongr
  exact measureReal_absTailEvent_centeredFinsetSum_absTailIndicator_le_two_mul_div
    (μ := μ) (X := X) (r := r) (s := s) (b := b) hb h_meas h_int

section

omit [MeasurableSpace Ω]

@[simp] theorem absTailIndicator_neg
    {X : Ω → ℝ} {r : ℝ} :
    absTailIndicator (fun ω => -X ω) r = -absTailIndicator X r := by
  funext ω
  by_cases hω : r < |X ω|
  · simp [absTailIndicator, hω, abs_neg]
  · simp [absTailIndicator, hω, abs_neg]

@[simp] theorem absTruncation_neg
    {X : Ω → ℝ} {r : ℝ} :
    absTruncation (fun ω => -X ω) r = -absTruncation X r := by
  funext ω
  by_cases hω : r < |X ω|
  · simp [absTruncation, absTailIndicator, hω, abs_neg]
  · simp [absTruncation, absTailIndicator, hω, abs_neg]

end


end
end IndependentSums
end Homogenization
