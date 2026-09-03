/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import LeanPool.ZetaZeros.MontgomeryTaylor.AffineKernel
public import LeanPool.ZetaZeros.MontgomeryTaylor.Integrability

/-!
# Reducing the functional to a single integral against `G`

`Q_0 0` is the integral of `f_0` squared and the moment term is the double integral of
`|u - v| f_0 u f_0 v`; added, they are the integral of `f_0` against `G`.
-/

@[expose] public section

open MeasureTheory

namespace ZetaZeros

/-- The self-convolution restricted to the support interval. -/
lemma extremalSelfConv_eq_interval (α : ℝ) :
    extremalSelfConv α = ∫ t in (-(1:ℝ)/2)..(1/2), extremalTest t * extremalTest (α - t) := by
  rw [extremalSelfConv]
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1:ℝ)/2) ≤ 1/2),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [Set.mem_Icc, not_and_or] at hx
  have hxout : 1 / 2 < |x| := by
    rw [lt_abs]
    rcases hx with h | h
    · right; push Not at h; linarith
    · left; push Not at h; linarith
  rw [extremalTest_eq_zero hxout, zero_mul]

/-- Part (I): `Q₀(0) = ∫_{-1/2}^{1/2} f₀(u)² du`. -/
lemma step1_selfconv0 :
    extremalSelfConv 0 = ∫ u in (-(1:ℝ)/2)..(1/2), extremalTest u * extremalTest u := by
  rw [extremalSelfConv]
  -- extremalTest (0 - t) = extremalTest (-t) = extremalTest t
  have hev : (fun t => extremalTest t * extremalTest (0 - t))
      = (fun t => extremalTest t * extremalTest t) := by
    funext t
    rw [zero_sub, extremalTest_even]
  rw [hev]
  -- convert full-line integral to the interval via support
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1:ℝ)/2) ≤ 1/2),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [Set.mem_Icc, not_and_or] at hx
  have hxout : 1 / 2 < |x| := by
    rw [lt_abs]
    rcases hx with h | h
    · right; push Not at h; linarith
    · left; push Not at h; linarith
  rw [extremalTest_eq_zero hxout, mul_zero]

/-- Inner reduction: substituting `β = α - t` and using the support of `extremalTest`,
    `∫ α in 0..1, α · f₀(α - t) = ∫ β in -1/2..1/2, max(β+t, 0) · f₀(β)` for `|t| ≤ 1/2`. -/
lemma inner_reduce {t : ℝ} (ht : |t| ≤ 1 / 2) :
    (∫ α in (0:ℝ)..1, α * extremalTest (α - t))
      = ∫ β in (-(1:ℝ)/2)..(1/2), max (β + t) 0 * extremalTest β := by
  have htle : -(1:ℝ)/2 ≤ t ∧ t ≤ 1/2 := by
    rw [abs_le] at ht; constructor <;> linarith [ht.1, ht.2]
  -- substitute β = α - t
  have hsub : (∫ α in (0:ℝ)..1, α * extremalTest (α - t))
      = ∫ β in (0 - t)..(1 - t), (β + t) * extremalTest β := by
    have h := intervalIntegral.integral_comp_sub_right
      (fun β => (β + t) * extremalTest β) t (a := (0:ℝ)) (b := 1)
    simp only [sub_add_cancel] at h
    rw [← h]
  rw [hsub, show (0:ℝ) - t = -t from by ring]
  -- LHS: ∫ β in -t..(1-t), (β+t)·g β. Split at 1/2 and drop [1/2, 1-t] where g = 0.
  have hmt_le_half : -t ≤ (1:ℝ)/2 := by linarith [htle.1]
  have hhalf_le : (1:ℝ)/2 ≤ 1 - t := by linarith [htle.2]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := -t) (b := (1:ℝ)/2) (c := 1 - t)
    (linTest_intervalIntegrable t _ _) (linTest_intervalIntegrable t _ _)]
  -- the [1/2, 1-t] piece vanishes: g β = 0 there
  have hdrop : (∫ β in ((1:ℝ)/2)..(1 - t), (β + t) * extremalTest β) = 0 := by
    rw [intervalIntegral.integral_of_le hhalf_le,
      MeasureTheory.integral_eq_zero_of_ae]
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioc ((1:ℝ)/2) (1-t), ?_, ?_⟩
    · exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioc
    · intro β hβ
      rw [Set.mem_Ioc] at hβ
      have hb0 : (1:ℝ)/2 < |β| := by rw [lt_abs]; left; linarith [hβ.1]
      change (β + t) * extremalTest β = 0
      rw [extremalTest_eq_zero hb0, mul_zero]
  rw [hdrop, add_zero]
  -- RHS: ∫ β in -1/2..1/2, max(β+t,0)·g β. Split at -t; drop [-1/2, -t] where max = 0.
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := -(1:ℝ)/2) (b := -t) (c := (1:ℝ)/2)
    (maxTest_intervalIntegrable t _ _) (maxTest_intervalIntegrable t _ _)]
  have hdrop2 : (∫ β in (-(1:ℝ)/2)..(-t), max (β + t) 0 * extremalTest β) = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith [htle.1] : -(1:ℝ)/2 ≤ -t),
      MeasureTheory.integral_eq_zero_of_ae]
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioc (-(1:ℝ)/2) (-t), ?_, ?_⟩
    · exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioc
    · intro β hβ
      rw [Set.mem_Ioc] at hβ
      have hbt : β + t ≤ 0 := by linarith [hβ.2]
      change max (β + t) 0 * extremalTest β = 0
      rw [max_eq_right hbt, zero_mul]
  rw [hdrop2, zero_add]
  -- the two middle pieces on [-t, 1/2] agree: max(β+t,0) = β+t since β+t ≥ 0.
  apply intervalIntegral.integral_congr
  intro β hβ
  rw [Set.uIcc_of_le hmt_le_half, Set.mem_Icc] at hβ
  simp only
  rw [max_eq_left (by linarith [hβ.1] : (0:ℝ) ≤ β + t)]

/-- Part (II): `2 ∫₀¹ α Q₀(α) dα = ∫∫ |u-v| f₀(u) f₀(v)`. -/
lemma step1_double :
    2 * ∫ α in (0:ℝ)..1, α * extremalSelfConv α
      = ∫ u in (-(1:ℝ)/2)..(1/2),
          extremalTest u * ∫ v in (-(1:ℝ)/2)..(1/2), |u - v| * extremalTest v := by
  set g := extremalTest with hg
  -- The common middle expression: `∫∫ max(t+β,0) g(t) g(β)`.
  set a : ℝ := -(1:ℝ)/2 with ha
  set b : ℝ := (1:ℝ)/2 with hb
  have hab : a ≤ b := by rw [ha, hb]; norm_num
  -- Continuity/integrability facts on the fixed interval.
  have hgIntOn : ∀ (s : Set ℝ), volume s < ⊤ → IntegrableOn g s volume :=
    fun s hs => extremalTest_integrableOn hs
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_lt : Real.sqrt 2 < 2 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) < 4)
    rwa [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h
  have hinv_pos : (0:ℝ) < 1 / Real.sqrt 2 := by positivity
  have hinv_lt_pi : 1 / Real.sqrt 2 < Real.pi := by
    have hlt1 : 1 / Real.sqrt 2 < 1 := by
      rw [div_lt_one h2]
      have : Real.sqrt 1 < Real.sqrt 2 := by apply Real.sqrt_lt_sqrt <;> norm_num
      simpa using this
    linarith [Real.pi_gt_three]
  have hsin_pos : 0 < Real.sin (1 / Real.sqrt 2) :=
    Real.sin_pos_of_pos_of_lt_pi hinv_pos hinv_lt_pi
  have hden_pos : 0 < Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) := mul_pos h2 hsin_pos
  -- Step 1: restrict inner conv and pull α inside.
  have hL1 : (∫ α in (0:ℝ)..1, α * extremalSelfConv α)
      = ∫ α in (0:ℝ)..1, ∫ t in a..b, α * (g t * g (α - t)) := by
    apply intervalIntegral.integral_congr
    intro α _
    simp only
    rw [extremalSelfConv_eq_interval, ← ha, ← hb, hg]
    rw [intervalIntegral.integral_const_mul]
  -- integrability of the joint integrand on the rectangle
  have hMeas : Measurable (Function.uncurry (fun α t => α * (g t * g (α - t)))) := by
    unfold Function.uncurry
    apply Measurable.mul measurable_fst
    apply Measurable.mul
    · exact extremalTest_measurable.comp measurable_snd
    · exact extremalTest_measurable.comp (measurable_fst.sub measurable_snd)
  set C : ℝ := (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))⁻¹ with hC
  have hCnn : 0 ≤ C := by rw [hC]; exact le_of_lt (inv_pos.mpr hden_pos)
  have hIntegrRect : IntegrableOn (Function.uncurry (fun α t => α * (g t * g (α - t))))
      (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc a b) volume := by
    apply MeasureTheory.IntegrableOn.of_bound _ hMeas.aestronglyMeasurable (1 * (C * C))
    · filter_upwards [MeasureTheory.ae_restrict_mem
        ((measurableSet_uIoc).prod (measurableSet_uIoc))] with p hp
      rw [Set.mem_prod, Set.uIoc, Set.uIoc, Set.mem_Ioc, Set.mem_Ioc] at hp
      simp only [min_eq_left (by norm_num : (0:ℝ) ≤ 1),
        max_eq_right (by norm_num : (0:ℝ) ≤ 1)] at hp
      simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      apply mul_le_mul _ _ (by positivity) (by norm_num)
      · rw [abs_of_pos hp.1.1]
        exact hp.1.2.trans (by norm_num)
      · exact mul_le_mul (extremalTest_abs_le _) (extremalTest_abs_le _) (abs_nonneg _) hCnn
    · rw [Measure.volume_eq_prod]
      refine lt_of_le_of_lt (Measure.prod_prod_le _ _) ?_
      apply ENNReal.mul_lt_top
      · rw [Set.uIoc]; exact measure_Ioc_lt_top
      · rw [Set.uIoc]; exact measure_Ioc_lt_top
  -- Step 2 (Fubini): swap the two interval integrals.
  have hL2 : (∫ α in (0:ℝ)..1, ∫ t in a..b, α * (g t * g (α - t)))
      = ∫ t in a..b, ∫ α in (0:ℝ)..1, α * (g t * g (α - t)) := by
    -- convert interval integrals to set integrals over Ioc, then apply the product swap.
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have hcongr1 : ∀ α, (∫ t in a..b, α * (g t * g (α - t)))
        = ∫ t in Set.Ioc a b, α * (g t * g (α - t)) :=
      fun α => intervalIntegral.integral_of_le hab
    have hcongr2 : ∀ t, (∫ α in (0:ℝ)..1, α * (g t * g (α - t)))
        = ∫ α in Set.Ioc (0:ℝ) 1, α * (g t * g (α - t)) :=
      fun t => intervalIntegral.integral_of_le (by norm_num)
    simp_rw [hcongr1, hcongr2]
    rw [intervalIntegral.integral_of_le hab]
    -- rephrase as integral against restricted measures
    have hInt : Integrable (Function.uncurry (fun α t => α * (g t * g (α - t))))
        ((volume.restrict (Set.Ioc (0:ℝ) 1)).prod (volume.restrict (Set.Ioc a b))) := by
      rw [Measure.prod_restrict]
      have : Set.uIoc (0:ℝ) 1 = Set.Ioc (0:ℝ) 1 := Set.uIoc_of_le (by norm_num)
      have hb2 : Set.uIoc a b = Set.Ioc a b := Set.uIoc_of_le hab
      rw [this, hb2] at hIntegrRect
      exact hIntegrRect
    have := MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
      (ν := volume.restrict (Set.Ioc a b)) hInt
    simpa only [Function.uncurry] using this
  -- Step 3: `∫ α, α Q₀ α = ∫ t, g t · ∫ v, max(t - v, 0) · g v`.
  have hM : (∫ α in (0:ℝ)..1, α * extremalSelfConv α)
      = ∫ t in a..b, g t * ∫ v in a..b, max (t - v) 0 * g v := by
    rw [hL1, hL2]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab, ha, hb, Set.mem_Icc] at ht
    have htabs : |t| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    -- pull g t out of the inner integral
    have hpull : (∫ α in (0:ℝ)..1, α * (g t * g (α - t)))
        = g t * ∫ α in (0:ℝ)..1, α * g (α - t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro α _; ring
    simp only
    rw [hpull, hg, inner_reduce htabs]
    -- reflect v → -v : ∫ β, max(β+t,0) g β = ∫ v, max(t-v,0) g v
    congr 1
    -- apply integral_comp_neg to `f v = max (t - v) 0 * extremalTest v`
    have hrefl := intervalIntegral.integral_comp_neg
      (fun v => max (t - v) 0 * extremalTest v) (a := -(1:ℝ)/2) (b := (1:ℝ)/2)
    rw [show (-(-(1:ℝ)/2)) = (1:ℝ)/2 from by norm_num,
      show (-((1:ℝ)/2)) = -(1:ℝ)/2 from by norm_num] at hrefl
    rw [ha, hb, ← hrefl]
    apply intervalIntegral.integral_congr
    intro β _
    simp only
    rw [extremalTest_even, sub_neg_eq_add, add_comm]
  -- Step 4 (symmetry): swapping `t ↔ v` in the double integral of `K t v = g t g v max(t-v,0)`.
  have hsymm : (∫ t in a..b, g t * ∫ v in a..b, max (t - v) 0 * g v)
      = ∫ t in a..b, g t * ∫ v in a..b, max (v - t) 0 * g v := by
    -- pull `g t` inside on both sides to get the double integral of `φ t v = g t g v max(t-v,0)`
    have hpullL : (∫ t in a..b, g t * ∫ v in a..b, max (t - v) 0 * g v)
        = ∫ t in a..b, ∫ v in a..b, g t * g v * max (t - v) 0 := by
      apply intervalIntegral.integral_congr; intro t _
      simp only
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr; intro v _; simp only; ring
    have hpullR : (∫ t in a..b, g t * ∫ v in a..b, max (v - t) 0 * g v)
        = ∫ t in a..b, ∫ v in a..b, g v * g t * max (v - t) 0 := by
      apply intervalIntegral.integral_congr; intro t _
      simp only
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr; intro v _; simp only; ring
    rw [hpullL, hpullR]
    -- Fubini swap `∫ t ∫ v φ t v = ∫ v ∫ t φ t v`, then rename dummy variables.
    set φ : ℝ → ℝ → ℝ := fun t v => g t * g v * max (t - v) 0 with hφ
    -- measurability of the uncurried kernel
    have hMeasφ : Measurable (Function.uncurry φ) := by
      unfold Function.uncurry
      simp only [hφ]
      apply Measurable.mul
      · exact (extremalTest_measurable.comp measurable_fst).mul
          (extremalTest_measurable.comp measurable_snd)
      · exact (measurable_fst.sub measurable_snd).max measurable_const
    -- integrability on the square
    have hIntφ : IntegrableOn (Function.uncurry φ)
        (Set.uIoc a b ×ˢ Set.uIoc a b) volume := by
      apply MeasureTheory.IntegrableOn.of_bound _ hMeasφ.aestronglyMeasurable (C * C * 1)
      · filter_upwards [MeasureTheory.ae_restrict_mem
          ((measurableSet_uIoc).prod (measurableSet_uIoc))] with p hp
        rw [Set.mem_prod] at hp
        rw [show Set.uIoc a b = Set.Ioc a b from Set.uIoc_of_le hab] at hp
        rw [Set.mem_Ioc, Set.mem_Ioc, ha, hb] at hp
        simp only [hφ, Function.uncurry, Real.norm_eq_abs, abs_mul]
        apply mul_le_mul
        · exact mul_le_mul (extremalTest_abs_le _) (extremalTest_abs_le _)
            (abs_nonneg _) hCnn
        · rw [abs_of_nonneg (le_max_right _ _)]
          rw [max_le_iff]
          exact ⟨by linarith [hp.1.2, hp.2.1], by norm_num⟩
        · positivity
        · positivity
      · rw [Measure.volume_eq_prod]
        refine lt_of_le_of_lt (Measure.prod_prod_le _ _) ?_
        apply ENNReal.mul_lt_top
        · rw [Set.uIoc]; exact measure_Ioc_lt_top
        · rw [Set.uIoc]; exact measure_Ioc_lt_top
    -- fold both integrands into `φ`
    have hLHS : (∫ t in a..b, ∫ v in a..b, g t * g v * max (t - v) 0)
        = ∫ t in a..b, ∫ v in a..b, φ t v := by
      apply intervalIntegral.integral_congr; intro t _
      apply intervalIntegral.integral_congr; intro v _
      simp only [hφ]
    have hRHS : (∫ t in a..b, ∫ v in a..b, g v * g t * max (v - t) 0)
        = ∫ t in a..b, ∫ v in a..b, φ v t := by
      apply intervalIntegral.integral_congr; intro t _
      apply intervalIntegral.integral_congr; intro v _
      simp only [hφ]
    rw [hLHS, hRHS]
    -- convert both nested interval integrals over a..b to set integrals over Ioc a b
    have hc1 : ∀ t, (∫ v in a..b, φ t v) = ∫ v in Set.Ioc a b, φ t v :=
      fun t => intervalIntegral.integral_of_le hab
    have hc2 : ∀ t, (∫ v in a..b, φ v t) = ∫ v in Set.Ioc a b, φ v t :=
      fun t => intervalIntegral.integral_of_le hab
    have hL : (∫ t in a..b, ∫ v in a..b, φ t v)
        = ∫ t in Set.Ioc a b, ∫ v in Set.Ioc a b, φ t v := by
      rw [intervalIntegral.integral_of_le hab]; simp_rw [hc1]
    have hR : (∫ t in a..b, ∫ v in a..b, φ v t)
        = ∫ t in Set.Ioc a b, ∫ v in Set.Ioc a b, φ v t := by
      rw [intervalIntegral.integral_of_le hab]; simp_rw [hc2]
    rw [hL, hR]
    -- now goal: ∫ t in Ioc, ∫ v in Ioc, φ t v = ∫ t in Ioc, ∫ v in Ioc, φ v t
    rw [show Set.uIoc a b = Set.Ioc a b from Set.uIoc_of_le hab] at hIntφ
    have hInt : Integrable (Function.uncurry φ)
        ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc a b))) := by
      rw [Measure.prod_restrict]
      exact hIntφ
    have hswap := MeasureTheory.integral_integral_swap
      (μ := volume.restrict (Set.Ioc a b)) (ν := volume.restrict (Set.Ioc a b)) hInt
    rw [show (∫ t in Set.Ioc a b, ∫ v in Set.Ioc a b, φ t v)
        = ∫ t, ∫ v, φ t v ∂(volume.restrict (Set.Ioc a b))
            ∂(volume.restrict (Set.Ioc a b)) from rfl]
    rw [hswap]
  -- Step 5: `2·(∫ α Q₀) = ∫∫ (max(t-v,0)+max(v-t,0)) g t g v = ∫∫ |t-v| g t g v = RHS`.
  rw [hM, two_mul]
  nth_rewrite 2 [hsymm]
  rw [← intervalIntegral.integral_add ?hi1 ?hi2]
  · apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [← mul_add, ← intervalIntegral.integral_add
      (maxSubTest_intervalIntegrable t a b) ?_]
    · congr 1
      apply intervalIntegral.integral_congr
      intro v _
      simp only
      rw [← add_mul, ← max_zero_add_max_neg_zero_eq_abs_self (t - v),
        show -(t - v) = v - t from by ring]
    · exact (extremalTest_intervalIntegrable_gen a b).continuousOn_mul
        (by fun_prop : ContinuousOn (fun v => max (v - t) 0) (Set.uIcc a b))
  case hi1 =>
    rw [ha, hb, hg]
    exact outer_intervalIntegrable (fun t v => max (t - v) 0) (by fun_prop)
  case hi2 =>
    rw [ha, hb, hg]
    exact outer_intervalIntegrable (fun t v => max (v - t) 0) (by fun_prop)

lemma montgomeryTaylor_step1 :
    extremalSelfConv 0 + 2 * ∫ α in (0:ℝ)..1, α * extremalSelfConv α
      = ∫ u in (-(1:ℝ)/2)..(1/2), extremalTest u * extremalG u := by
  rw [step1_selfconv0, step1_double]
  -- Integrability of the two pieces of `f₀·G`.
  have hint1 : IntervalIntegrable (fun u => extremalTest u * extremalTest u)
      MeasureTheory.volume (-(1:ℝ)/2) (1/2) :=
    (extremalTest_continuousOn.mul extremalTest_continuousOn).intervalIntegrable
  have hint2 : IntervalIntegrable
      (fun u => extremalTest u * ∫ v in (-(1:ℝ)/2)..(1/2), |u - v| * extremalTest v)
      MeasureTheory.volume (-(1:ℝ)/2) (1/2) := by
    -- rewrite the inner kernel to its continuous form on the interval, giving a jointly
    -- continuous parametric integral, then multiply by the continuous `extremalTest`.
    have hcont : Continuous (fun u => ∫ v in (-(1:ℝ)/2)..(1/2),
        |u - v| * (Real.cos (Real.sqrt 2 * v) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)))) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun u v =>
          |u - v| * (Real.cos (Real.sqrt 2 * v) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))))
      fun_prop
    apply ContinuousOn.intervalIntegrable
    apply extremalTest_continuousOn.mul
    apply ContinuousOn.congr (hcont.continuousOn)
    intro u _
    apply intervalIntegral.integral_congr
    intro v hv
    simp only
    rw [extremalTest_eqOn_uIcc hv]
  -- Now split the integral of the sum on the RHS.
  rw [show (fun u => extremalTest u * extremalG u)
      = (fun u => extremalTest u * extremalTest u
          + extremalTest u * ∫ v in (-(1:ℝ)/2)..(1/2), |u - v| * extremalTest v) from by
        funext u; rw [extremalG, mul_add]]
  rw [intervalIntegral.integral_add hint1 hint2]

end ZetaZeros
