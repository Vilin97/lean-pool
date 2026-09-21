/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Moments.Basic
import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.WeakOrlicz

/-! # Truncation -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The one-sided bounded truncation `min (X, L)` used in the Chapter 4
heavy-tail concentration argument. -/
def upperTruncation (X : Ω → ℝ) (L : ℝ) : Ω → ℝ :=
  fun ω => min (X ω) L

omit [MeasurableSpace Ω] in
@[simp] theorem upperTruncation_apply (X : Ω → ℝ) (L : ℝ) (ω : Ω) :
    upperTruncation X L ω = min (X ω) L :=
  rfl

omit [MeasurableSpace Ω] in
@[simp] theorem upperTruncation_of_le {X : Ω → ℝ} {L : ℝ} {ω : Ω}
    (h : X ω ≤ L) :
    upperTruncation X L ω = X ω := by
  simp [upperTruncation, min_eq_left h]

omit [MeasurableSpace Ω] in
@[simp] theorem upperTruncation_of_lt {X : Ω → ℝ} {L : ℝ} {ω : Ω}
    (h : L < X ω) :
    upperTruncation X L ω = L := by
  simp [upperTruncation, min_eq_right (le_of_lt h)]

omit [MeasurableSpace Ω] in
theorem upperTruncation_le_self (X : Ω → ℝ) (L : ℝ) (ω : Ω) :
    upperTruncation X L ω ≤ X ω := by
  simp [upperTruncation]

omit [MeasurableSpace Ω] in
theorem upperTruncation_le (X : Ω → ℝ) (L : ℝ) (ω : Ω) :
    upperTruncation X L ω ≤ L := by
  simp [upperTruncation]

theorem upperTruncation_measurable {X : Ω → ℝ} {L : ℝ}
    (hX : Measurable X) :
    Measurable (upperTruncation X L) := by
  exact hX.min measurable_const

theorem iIndepFun_upperTruncation {X : ι → Ω → ℝ} {L : ℝ}
    (h_indep : iIndepFun X μ) :
    iIndepFun (fun i ω => upperTruncation (X i) L ω) μ := by
  let g : ι → ℝ → ℝ := fun _ x => min x L
  have hg : ∀ i, Measurable (g i) := by
    intro i
    simpa [g] using (measurable_id.min measurable_const)
  exact h_indep.comp g hg

omit [MeasurableSpace Ω] in
/-- If a finite sum exceeds `a`, then either the corresponding upper-truncated
sum still exceeds `a`, or one of the summands exceeded the truncation level. -/
theorem upperTailEvent_finset_sum_subset_upperTailEvent_finset_sum_upperTruncation_union
    (s : Finset ι) {X : ι → Ω → ℝ} {L a : ℝ} :
    upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a ⊆
      upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a ∪
        ⋃ i ∈ s, upperTailEvent (X i) L := by
  intro ω hω
  by_cases htail : ∃ i ∈ s, L < X i ω
  · rcases htail with ⟨i, hi, hXi⟩
    right
    refine Set.mem_iUnion.2 ?_
    exact ⟨i, Set.mem_iUnion.2 ⟨hi, hXi⟩⟩
  · left
    have hEq :
        (∑ i ∈ s, upperTruncation (X i) L ω) = ∑ i ∈ s, X i ω := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hle : X i ω ≤ L := le_of_not_gt (fun hXi => htail ⟨i, hi, hXi⟩)
      simp [upperTruncation, min_eq_left hle]
    change a < ∑ i ∈ s, upperTruncation (X i) L ω
    rw [hEq]
    exact hω

/-- Measure-theoretic form of the basic truncation split used in the Chapter 4
heavy-tail concentration proof. -/
theorem measureReal_upperTailEvent_finset_sum_le_upperTruncation_add
    [IsFiniteMeasure μ]
    (s : Finset ι) {X : ι → Ω → ℝ} {L a : ℝ} :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) +
        ∑ i ∈ s, μ.real (upperTailEvent (X i) L) := by
  refine le_trans
    (measureReal_mono
      (upperTailEvent_finset_sum_subset_upperTailEvent_finset_sum_upperTruncation_union
        (s := s) (X := X) (L := L) (a := a))) ?_
  calc
    μ.real
        (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a ∪
          ⋃ i ∈ s, upperTailEvent (X i) L)
      ≤
        μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) +
          μ.real (⋃ i ∈ s, upperTailEvent (X i) L) := by
            exact measureReal_union_le _ _
    _ ≤
        μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) +
          ∑ i ∈ s, μ.real (upperTailEvent (X i) L) := by
            gcongr
            exact measureReal_biUnion_finset_le s (fun i => upperTailEvent (X i) L)

/-- If each summand satisfies the note-facing upper-tail bound with unit scale,
the large-value part of the truncation split is bounded by
`card(s) / Ψ(L)`. -/
theorem measureReal_upperTailEvent_finset_sum_le_upperTruncation_add_card_mul_of_isBigOWith
    [IsFiniteMeasure μ]
    {Ψ : ℝ → ℝ} {X : ι → Ω → ℝ} {s : Finset ι} {L a : ℝ}
    (hX : ∀ i ∈ s, IsBigOWith μ Ψ (X i) 1)
    (hL : 1 ≤ L) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) +
        (s.card : ℝ) * (Ψ L)⁻¹ := by
  calc
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a)
      ≤
        μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) +
          ∑ i ∈ s, μ.real (upperTailEvent (X i) L) :=
        measureReal_upperTailEvent_finset_sum_le_upperTruncation_add
          (μ := μ) (s := s) (X := X) (L := L) (a := a)
    _ ≤
        μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) +
          ∑ i ∈ s, (Ψ L)⁻¹ := by
            have hsum :
                ∑ i ∈ s, μ.real (upperTailEvent (X i) L) ≤ ∑ i ∈ s, (Ψ L)⁻¹ := by
              exact Finset.sum_le_sum fun i hi => by
                simpa using hX i hi hL
            simpa using add_le_add_left hsum
              (μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a))
    _ =
        μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) +
          (s.card : ℝ) * (Ψ L)⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]

/-- A measurable random variable bounded above by `B` has finite exponential
moment `E[e^{λY}]` for every `λ ≥ 0` on a finite measure space. -/
theorem integrable_exp_mul_of_le_const [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {l B : ℝ}
    (hYm : Measurable Y) (hl : 0 ≤ l) (hYB : ∀ ω, Y ω ≤ B) :
    Integrable (fun ω => Real.exp (l * Y ω)) μ := by
  refine Integrable.mono' (integrable_const (Real.exp (l * B)))
    ((hYm.const_mul l).exp.aemeasurable.aestronglyMeasurable) ?_
  filter_upwards with ω
  have hmul : l * Y ω ≤ l * B := mul_le_mul_of_nonneg_left (hYB ω) hl
  have hexp : Real.exp (l * Y ω) ≤ Real.exp (l * B) := Real.exp_le_exp.2 hmul
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using hexp

/-- The exponential moment of an upper-truncated variable is always defined for
nonnegative `λ`. -/
theorem integrable_exp_mul_upperTruncation [IsFiniteMeasure μ]
    {X : Ω → ℝ} {l L : ℝ}
    (hXm : Measurable X) (hl : 0 ≤ l) :
    Integrable (fun ω => Real.exp (l * upperTruncation X L ω)) μ := by
  refine integrable_exp_mul_of_le_const
    (μ := μ)
    (Y := upperTruncation X L)
    (l := l)
    (B := L)
    (upperTruncation_measurable hXm)
    hl
    ?_
  intro ω
  exact upperTruncation_le X L ω

private theorem exp_sub_one_sub_id_le_half_sq_mul_exp_max (z : ℝ) :
    Real.exp z - (1 + z) ≤ (z ^ (2 : ℕ) / 2) * Real.exp (max z 0) := by
  by_cases hz : 0 ≤ z
  · rcases eq_or_lt_of_le hz with rfl | hzpos
    · norm_num
    have hu : UniqueDiffOn ℝ (Set.Icc 0 z) := uniqueDiffOn_Icc hzpos
    obtain ⟨ξ, hξ, hξeq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.exp) (x₀ := 0) (x := z) (n := 1) hzpos.ne
        (Real.contDiff_exp.contDiffOn)
    rw [Set.uIoo_of_le hz] at hξ
    rw [Set.uIcc_of_le hz] at hξeq
    have hderiv0 : derivWithin Real.exp (Set.Icc 0 z) 0 = 1 := by
      simpa using ((Real.hasDerivAt_exp 0).hasDerivWithinAt).derivWithin
        (hu.uniqueDiffWithinAt (by exact ⟨le_rfl, hzpos.le⟩))
    have htaylor : taylorWithinEval Real.exp 1 (Set.Icc 0 z) 0 z = 1 + z := by
      simp [taylor_within_apply, hderiv0]
    have hiter : iteratedDeriv 2 Real.exp ξ = Real.exp ξ := by
      rw [iteratedDeriv_eq_iterate]
      exact congrFun (Real.iter_deriv_exp 2) ξ
    have hformula : Real.exp z - (1 + z) = Real.exp ξ * z ^ (2 : ℕ) / 2 := by
      rw [← htaylor, hξeq, hiter]
      norm_num [Nat.factorial]
    have hξexp : Real.exp ξ ≤ Real.exp z := Real.exp_le_exp.2 hξ.2.le
    have hzsq_nonneg : 0 ≤ z ^ (2 : ℕ) / 2 := by positivity
    calc
      Real.exp z - (1 + z) = Real.exp ξ * z ^ (2 : ℕ) / 2 := hformula
      _ = (z ^ (2 : ℕ) / 2) * Real.exp ξ := by ring
      _ ≤ (z ^ (2 : ℕ) / 2) * Real.exp z := mul_le_mul_of_nonneg_left hξexp hzsq_nonneg
      _ = (z ^ (2 : ℕ) / 2) * Real.exp (max z 0) := by simp [max_eq_left hz]
  · have hzneg : z < 0 := lt_of_not_ge hz
    let u : ℝ := -z
    have hupos : 0 < u := by simpa [u] using neg_pos.mpr hzneg
    have hu : UniqueDiffOn ℝ (Set.Icc 0 u) := uniqueDiffOn_Icc hupos
    obtain ⟨ξ, hξ, hξeq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := fun s : ℝ => Real.exp (-s)) (x₀ := 0) (x := u) (n := 1) hupos.ne
        ((Real.contDiff_exp.comp (by fun_prop)).contDiffOn :
          ContDiffOn ℝ (1 + 1) (fun s : ℝ => Real.exp (-s)) (Set.uIcc 0 u))
    rw [Set.uIoo_of_le hupos.le] at hξ
    rw [Set.uIcc_of_le hupos.le] at hξeq
    have hderiv0 : derivWithin (fun s : ℝ => Real.exp (-s)) (Set.Icc 0 u) 0 = -1 := by
      have hderivAt : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-1) 0 := by
        simpa using ((hasDerivAt_id 0).neg.exp)
      exact hderivAt.hasDerivWithinAt.derivWithin
        (hu.uniqueDiffWithinAt (by exact ⟨le_rfl, hupos.le⟩))
    have htaylor :
        taylorWithinEval (fun s : ℝ => Real.exp (-s)) 1 (Set.Icc 0 u) 0 u = 1 - u := by
      simp [taylor_within_apply, hderiv0]
      ring
    have hiter : iteratedDeriv 2 (fun s : ℝ => Real.exp (-s)) ξ = Real.exp (-ξ) := by
      simpa [pow_two] using congrFun (iteratedDeriv_exp_const_mul (n := 2) (-1)) ξ
    have hξle : Real.exp (-ξ) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (by linarith [hξ.1])
    have hformula0 : Real.exp (-u) - (1 - u) = Real.exp (-ξ) * u ^ (2 : ℕ) / 2 := by
      rw [← htaylor, hξeq, hiter]
      norm_num [Nat.factorial]
    have hformula : Real.exp (-u) - (1 + -u) = Real.exp (-ξ) * u ^ (2 : ℕ) / 2 := by
      simpa [sub_eq_add_neg] using hformula0
    have husq_nonneg : 0 ≤ u ^ (2 : ℕ) / 2 := by positivity
    have haux : Real.exp z - (1 + z) ≤ u ^ (2 : ℕ) / 2 := by
      calc
        Real.exp z - (1 + z) = Real.exp (-u) - (1 + -u) := by simp [u]
        _ = Real.exp (-ξ) * u ^ (2 : ℕ) / 2 := hformula
        _ = (u ^ (2 : ℕ) / 2) * Real.exp (-ξ) := by ring
        _ ≤ (u ^ (2 : ℕ) / 2) * 1 := mul_le_mul_of_nonneg_left hξle husq_nonneg
        _ = u ^ (2 : ℕ) / 2 := by ring
    have hmax : max z 0 = 0 := max_eq_right (le_of_lt hzneg)
    have hzsq : z ^ (2 : ℕ) = u ^ (2 : ℕ) := by
      simp [u, pow_two]
    rw [hmax, Real.exp_zero, hzsq]
    simpa using haux

/-- A scaled Taylor-remainder bound for `exp (λx)` with a global exponential
weight on the positive part of `x`. -/
theorem exp_mul_le_one_add_mul_add_half_mul_sq_mul_exp_max_zero_of_nonneg
    {l x : ℝ} (hl : 0 ≤ l) :
    Real.exp (l * x) ≤
      1 + l * x + (l ^ (2 : ℕ) / 2) * x ^ (2 : ℕ) * Real.exp (l * max x 0) := by
  have hbase := exp_sub_one_sub_id_le_half_sq_mul_exp_max (z := l * x)
  have hmax : max (l * x) 0 = l * max x 0 := by
    symm
    simpa [mul_comm] using (mul_max_of_nonneg x 0 hl)
  have hstep :
      Real.exp (l * x) ≤
        1 + l * x + ((l * x) ^ (2 : ℕ) / 2) * Real.exp (l * max x 0) := by
    have hbase' :
        Real.exp (l * x) - (1 + l * x) ≤
          ((l * x) ^ (2 : ℕ) / 2) * Real.exp (l * max x 0) := by
      simpa [hmax] using hbase
    linarith
  calc
    Real.exp (l * x)
      ≤ 1 + l * x + ((l * x) ^ (2 : ℕ) / 2) * Real.exp (l * max x 0) := hstep
    _ = 1 + l * x + (l ^ (2 : ℕ) / 2) * x ^ (2 : ℕ) * Real.exp (l * max x 0) := by
          ring

/-- The upper truncation `min (X, L)` is integrable whenever `X` is integrable
on a finite measure space. -/
theorem integrable_upperTruncation_of_integrable [IsFiniteMeasure μ]
    {X : Ω → ℝ} {L : ℝ}
    (hXm : Measurable X) (hXint : Integrable X μ) :
    Integrable (upperTruncation X L) μ := by
  refine Integrable.mono'
    ((hXint.norm).add (integrable_const |L|))
    ((upperTruncation_measurable (X := X) (L := L) hXm).aemeasurable.aestronglyMeasurable)
    ?_
  filter_upwards with ω
  by_cases hω : X ω ≤ L
  · rw [upperTruncation_of_le hω]
    exact le_add_of_nonneg_right (abs_nonneg L)
  · have hω' : L < X ω := lt_of_not_ge hω
    rw [upperTruncation_of_lt hω']
    exact le_add_of_nonneg_left (abs_nonneg (X ω))

/-- If `X` is centered, then its upper truncation `min (X, L)` has
nonpositive expectation. -/
theorem integral_upperTruncation_le_zero_of_integral_eq_zero
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} {L : ℝ}
    (hXm : Measurable X) (hXint : Integrable X μ)
    (hXmean : ∫ ω, X ω ∂μ = 0) :
    ∫ ω, upperTruncation X L ω ∂μ ≤ 0 := by
  have hYint :=
    integrable_upperTruncation_of_integrable (μ := μ) (X := X) (L := L) hXm hXint
  exact (integral_mono_ae hYint hXint
    (Filter.Eventually.of_forall fun ω => upperTruncation_le_self X L ω)).trans_eq hXmean


end

end IndependentSums

end Homogenization
