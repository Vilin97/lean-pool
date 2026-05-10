/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Defs
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Gaussian Helper Lemmas

Gaussian normalization, gradient of exponential-quadratic functions,
integrability, and related analysis lemmas used in Section 3.
-/

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.multiGoal false
set_option linter.style.show false
set_option linter.unnecessarySeqFocus false

namespace VML

-- ============================================================================
-- Part 1: vGrad_exp_quadratic
-- ============================================================================

/-- The velocity gradient of exp(a + b·v + c·|v|²) equals exp(a + b·v + c·|v|²)·(b + 2c·v).
    Proved by Aristotle (Harmonic). -/
lemma vGrad_exp_quadratic (a : ℝ) (b : Fin 3 → ℝ) (c : ℝ) :
    ∀ v : Fin 3 → ℝ,
    vGrad (fun w => Real.exp (a + dotProduct b w + c * normSq w)) v =
    Real.exp (a + dotProduct b v + c * normSq v) • (b + (2 * c) • v) := by
  unfold vGrad normSq
  intro v
  ext i
  erw [ fderiv_exp ]
  norm_num [ dotProduct, Fin.sum_univ_three ]
  ring_nf
  · field_simp
    erw [ HasFDerivAt.fderiv (by
      exact HasFDerivAt.add
        (HasFDerivAt.add
          (HasFDerivAt.add
            (HasFDerivAt.add
              (HasFDerivAt.add
                (HasFDerivAt.add
                  (hasFDerivAt_const _ _)
                  (HasFDerivAt.mul
                    (hasFDerivAt_const _ _)
                    (hasFDerivAt_apply _ _)))
                (HasFDerivAt.mul
                  (hasFDerivAt_apply _ _ |> HasFDerivAt.pow <| 2)
                  (hasFDerivAt_const _ _)))
              (HasFDerivAt.mul
                (hasFDerivAt_const _ _)
                (hasFDerivAt_apply _ _)))
            (HasFDerivAt.mul
              (hasFDerivAt_const _ _)
              (hasFDerivAt_apply _ _ |> HasFDerivAt.pow <| 2)))
          (HasFDerivAt.mul
            (hasFDerivAt_const _ _)
            (hasFDerivAt_apply _ _)))
        (HasFDerivAt.mul
          (hasFDerivAt_const _ _)
          (hasFDerivAt_apply _ _ |> HasFDerivAt.pow <| 2))) ]
    ring_nf
    fin_cases i <;> simp [ Pi.single_apply ] <;> ring!
  · norm_num [ dotProduct ]
    fun_prop (disch := norm_num)

/-- Gaussian normalization: if f(v) = exp(a₀ + c₀|v|²) with c₀ < 0 and ∫f = ρ_ion,
    then f = equilibriumMaxwellian ρ_ion T with T = -1/(2c₀).
    Proved by Aristotle (project 1236b757). -/
lemma gaussian_normalization_maxwellian
    (ρ_ion a₀ c₀ : ℝ) (hρ : 0 < ρ_ion) (hc₀ : c₀ < 0)
    (f : (Fin 3 → ℝ) → ℝ)
    (hf : ∀ v, f v = Real.exp (a₀ + c₀ * normSq v))
    (hf_int : ∫ v : Fin 3 → ℝ, f v = ρ_ion) :
    ∀ v, f v = equilibriumMaxwellian ρ_ion (-1 / (2 * c₀)) v := by
  -- Proved by Aristotle (project 1236b757), adapted to standard Mathlib generalize_proofs.
  have h_m_int : ∫ v : Fin 3 → ℝ,
      Real.exp (c₀ * (normSq v)) = (Real.pi / (-c₀)) ^ ((3 : ℝ) / 2) := by
    have h_gauss : ∫ v : Fin 3 → ℝ,
        Real.exp (c₀ * normSq v) =
        (∏ i : Fin 3, ∫ v : ℝ, Real.exp (c₀ * v^2)) := by
      have h_fubini : ∫ v : Fin 3 → ℝ,
          Real.exp (c₀ * normSq v) =
          ∫ v : Fin 3 → ℝ,
          (∏ i : Fin 3, Real.exp (c₀ * (v i) ^ 2)) := by
        norm_num [ ← Real.exp_sum, normSq ]
        norm_num [ dotProduct, Fin.sum_univ_three ]
        congr
        ext
        ring_nf
      generalize_proofs at *; (
      erw [ h_fubini, ← MeasureTheory.integral_fintype_prod_eq_prod ]
      exact rfl)
    generalize_proofs at *; (
    have := integral_gaussian ( -c₀)
    simp_all [ div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm ]
    have hnn : (0 : ℝ) ≤ -(π * c₀⁻¹) := by
      have : c₀⁻¹ < 0 := inv_neg''.mpr hc₀
      nlinarith [Real.pi_pos]
    rw [ Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hnn ]
    norm_num )
  simp_all [ Real.exp_add, MeasureTheory.integral_const_mul ]
  intro v
  rw [ ← hf_int ]
  unfold equilibriumMaxwellian
  have hc₀_ne : c₀ ≠ 0 := ne_of_lt hc₀
  have h_eq : 2 * Real.pi * (-1 / (2 * c₀)) = Real.pi / (-c₀) := by field_simp
  rw [h_eq]
  have h_rpow_ne : (Real.pi / (-c₀)) ^ ((3 : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by
      exact div_pos Real.pi_pos (neg_pos.mpr hc₀)) _)
  rw [mul_div_assoc, div_self h_rpow_ne, mul_one]
  congr 1; field_simp


/-- Gaussian first moment: ∫ vᵢ exp(a+b·v+c|v|²) = (-bᵢ/(2c)) · ∫ exp(a+b·v+c|v|²).
    Proved by Aristotle (project 4c5e7998). -/
lemma gaussian_first_moment (a : ℝ) (b : Fin 3 → ℝ) (c : ℝ) (hc : c < 0)
    (hf_int : Integrable (fun v : Fin 3 → ℝ => Real.exp (a + dotProduct b v + c * normSq v))) :
    ∀ i : Fin 3, ∫ v, v i * Real.exp (a + dotProduct b v + c * normSq v) =
      (-b i / (2 * c)) * ∫ v, Real.exp (a + dotProduct b v + c * normSq v) := by
  -- Proved by Aristotle (project 4c5e7998), adapted with erw for Fubini steps.
  intro i
  have h_gauss : ∫ v : Fin 3 → ℝ,
      v i * Real.exp (a + b ⬝ᵥ v + c * normSq v) =
      (-b i / (2 * c)) *
      (∫ v : Fin 3 → ℝ,
        Real.exp (a + b ⬝ᵥ v + c * normSq v)) := by
    have h_gauss_integral : ∀ a b c : ℝ, c < 0 →
        ∫ v : ℝ, v * Real.exp (a + b * v + c * v^2) =
        (-b / (2 * c)) *
        (∫ v : ℝ, Real.exp (a + b * v + c * v^2)) := by
      intro a b c hc_neg
      have h_gauss_integral : ∫ v : ℝ, (v + b / (2 * c)) * Real.exp (a + b * v + c * v^2) = 0 := by
        suffices h_subst :
            ∫ v : ℝ, (v + b / (2 * c)) *
              Real.exp (a + b * v + c * v^2) =
            ∫ u : ℝ, u *
              Real.exp (a - b^2 / (4 * c) + c * u^2) by
          have h_odd : ∀ f : ℝ → ℝ, (∀ x, f (-x) = -f x) → ∫ x : ℝ, f x = 0 := by
            intro f hf_odd
            have h_symm : ∫ x : ℝ, f x = ∫ x : ℝ, f (-x) := by
              rw [ MeasureTheory.integral_neg_eq_self ]
            have h_zero : ∫ x : ℝ, f x = -∫ x : ℝ, f x := by
              conv_lhs => rw [h_symm]
              simp_rw [hf_odd]
              rw [MeasureTheory.integral_neg]
            linarith [h_zero]
          exact h_subst.trans (h_odd _ fun x => by ring_nf)
        rw [ ← MeasureTheory.integral_add_right_eq_self _ ( -b / (2 * c) ) ]
        congr
        ext
        ring_nf
        norm_num [ hc_neg.ne ]
        ring_nf
        grind
      simp_all [ add_mul, div_eq_mul_inv, MeasureTheory.integral_const_mul ]
      rw [ MeasureTheory.integral_add ] at h_gauss_integral <;> norm_num at *
      · rw [ MeasureTheory.integral_const_mul ] at h_gauss_integral; linarith
      · have h_integrable : MeasureTheory.Integrable
            (fun v : ℝ => v * Real.exp (c * v^2 + b * v))
            MeasureTheory.MeasureSpace.volume := by
          have h_gauss : ∀ v : ℝ,
              |v * Real.exp (c * v^2 + b * v)| ≤
              |v| * Real.exp (c * v^2 / 2) *
              Real.exp (b^2 / (2 * |c|)) := by
            intro v
            simp [abs_mul]
            rw [ mul_assoc, ← Real.exp_add ]
            ring_nf
            norm_num [ abs_of_neg hc_neg ]
            ring_nf
            norm_num [ hc_neg ]; (
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr <| by
                nlinarith [ sq_nonneg (v * c + b),
                  mul_inv_cancel₀ (ne_of_lt hc_neg) ])
              (abs_nonneg v))
          have h_integrable : MeasureTheory.Integrable
              (fun v : ℝ => |v| * Real.exp (c * v^2 / 2))
              MeasureTheory.MeasureSpace.volume := by
            have h_integrable : MeasureTheory.Integrable
                (fun v : ℝ => v * Real.exp (c * v^2 / 2))
                MeasureTheory.MeasureSpace.volume := by
              have := @integrable_rpow_mul_exp_neg_mul_sq
              convert @this ( -c / 2) (by linarith) 1 (by norm_num) using 3
              · simp [Real.rpow_one]
              · congr 1; ring
            convert h_integrable.norm using 2; norm_num [ abs_mul, abs_of_nonneg, Real.exp_nonneg ]
          exact MeasureTheory.Integrable.mono'
            (h_integrable.mul_const _)
            (Continuous.aestronglyMeasurable (by continuity))
            (Filter.Eventually.of_forall h_gauss)
        convert h_integrable.mul_const (Real.exp a) using 2; ring_nf
        rw [ mul_assoc, ← Real.exp_add ]
      · have h_gauss_integral :
            ∫ v : ℝ, Real.exp (a + b * v + c * v^2) =
            Real.sqrt (Real.pi / (-c)) *
            Real.exp (a - b^2 / (4 * c)) := by
          have h_gauss_integral :
              ∫ v : ℝ, Real.exp (c * (v - (-b / (2 * c)))^2) =
              Real.sqrt (Real.pi / (-c)) := by
            convert integral_gaussian ( -c) using 1 <;> norm_num [ hc_neg.le ]
            rw [ eq_comm, ← MeasureTheory.integral_sub_right_eq_self ]
          rw [ ← h_gauss_integral, ← MeasureTheory.integral_mul_const ]
          congr
          ext v
          ring_nf
          rw [ ← Real.exp_add ]
          norm_num [ sq, mul_assoc, hc_neg.ne ]
          ring
        exact MeasureTheory.Integrable.const_mul (by
          exact (by
            contrapose! h_gauss_integral
            rw [ MeasureTheory.integral_undef h_gauss_integral ]
            exact ne_of_lt (mul_pos
              (Real.sqrt_pos.mpr
                (div_pos Real.pi_pos (neg_pos.mpr hc_neg)))
              (Real.exp_pos _)))) _
    have h_gauss_integral_component :
        ∀ i : Fin 3,
        ∫ v : Fin 3 → ℝ, v i * Real.exp (a + b ⬝ᵥ v + c * normSq v) =
        (∫ v : ℝ, v * Real.exp (a + b i * v + c * v^2)) *
        (∏ j ∈ Finset.univ.erase i,
          ∫ v : ℝ, Real.exp (b j * v + c * v^2)) := by
      intro i
      have h_fubini :
          ∫ v : Fin 3 → ℝ,
            v i * Real.exp (a + b ⬝ᵥ v + c * normSq v) =
          ∫ v : Fin 3 → ℝ,
            (∏ j, (if j = i
              then v j * Real.exp (a + b j * v j + c * v j^2)
              else Real.exp (b j * v j + c * v j^2))) := by
        simp [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ]
        simp [ mul_assoc, ← Real.exp_sum,
          Finset.sum_add_distrib,
          Finset.mul_sum _ _ _, Finset.sum_mul, normSq ]
        simp [ ← Real.exp_add, Fin.sum_univ_three, dotProduct ]
        congr
        ext
        ring_nf!
      have h_fubini2 :
          ∫ v : Fin 3 → ℝ, (∏ j, (if j = i
            then v j * Real.exp (a + b j * v j + c * v j^2)
            else Real.exp (b j * v j + c * v j^2))) =
          (∏ j, ∫ v : ℝ, (if j = i
            then v * Real.exp (a + b j * v + c * v^2)
            else Real.exp (b j * v + c * v^2))) := by
        erw [← MeasureTheory.integral_fintype_prod_eq_prod]; rfl
      simp_all [ Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ i) ]
      exact Or.inl (by rw [ Finset.sdiff_singleton_eq_erase ]
                       exact Finset.prod_congr rfl fun x hx => by simp_all)
    have h_gauss_integral_component2 :
        ∫ v : Fin 3 → ℝ,
          Real.exp (a + b ⬝ᵥ v + c * normSq v) =
        (∏ j : Fin 3,
          ∫ v : ℝ, Real.exp (b j * v + c * v^2)) *
        Real.exp a := by
      have h_gauss_integral_component3 :
          ∫ v : Fin 3 → ℝ,
            Real.exp (a + b ⬝ᵥ v + c * normSq v) =
          (∫ v : Fin 3 → ℝ, Real.exp (a) *
            (∏ j : Fin 3,
              Real.exp (b j * v j + c * v j^2))) := by
        simp [ normSq, dotProduct, Fin.sum_univ_three, ← Real.exp_sum, ← Real.exp_add ]
        congr
        ext
        ring_nf
      rw [ h_gauss_integral_component3, mul_comm ]
      rw [ MeasureTheory.integral_const_mul ]
      congr 1
      erw [← MeasureTheory.integral_fintype_prod_eq_prod]; rfl
    simp_all [ Finset.prod_erase_mul _ _ (Finset.mem_univ i) ]
    rw [ ← Finset.mul_prod_erase _ _ (Finset.mem_univ i) ]; ring_nf
    simp [ Real.exp_add, mul_add, add_comm,
      add_left_comm, mul_assoc, mul_comm, mul_left_comm,
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_mul_const ]
  exact h_gauss

/-- Gaussian integrability: exp(a₀+b·v+c₀|v|²) with f integrable implies c₀ < 0. -/
lemma analysis_gaussian_integrability
    (f : (Fin 3 → ℝ) → ℝ) (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_int : Integrable f)
    (hf_exp : ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)) :
    c₀ < 0 := by
  -- Proved by Aristotle (Harmonic)
  contrapose! hf_int
  by_contra h_contra
  have h_integrable : MeasureTheory.Integrable
      (fun v : Fin 3 → ℝ => Real.exp (a₀ + b ⬝ᵥ v))
      MeasureTheory.MeasureSpace.volume := by
    refine h_contra.mono' ?_ ?_
    · fun_prop
    · simp_all [ Real.exp_pos ]
      exact Filter.Eventually.of_forall fun x => mul_nonneg hf_int (by
        show 0 ≤ VML.normSq x
        unfold VML.normSq
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have h_integrable : MeasureTheory.Integrable
      (fun v : Fin 3 → ℝ => Real.exp (b ⬝ᵥ v))
      MeasureTheory.MeasureSpace.volume := by
    convert h_integrable.const_mul (Real.exp ( -a₀) ) using 2
    rw [ ← Real.exp_add ]
    ring_nf
  have h_integrable : MeasureTheory.Integrable
      (fun v : ℝ => Real.exp (b 0 * v))
      MeasureTheory.MeasureSpace.volume := by
    have h_integrable :
        MeasureTheory.Integrable
          (fun v : Fin 3 → ℝ => Real.exp (b ⬝ᵥ v))
          MeasureTheory.MeasureSpace.volume →
        MeasureTheory.Integrable
          (fun v : ℝ => Real.exp (b 0 * v))
          MeasureTheory.MeasureSpace.volume := by
      intro h_integrable
      have h_integrable :
          MeasureTheory.Integrable
            (fun v : ℝ × (Fin 2 → ℝ) =>
              Real.exp (b 0 * v.1 + ∑ i : Fin 2, b (Fin.succ i) * v.2 i))
            (MeasureTheory.MeasureSpace.volume.prod
              MeasureTheory.MeasureSpace.volume) := by
        convert h_integrable using 1
        have h_iso :
            (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)) =
            MeasureTheory.Measure.map
              (fun v : ℝ × (Fin 2 → ℝ) => Fin.cons v.1 v.2)
              (MeasureTheory.volume.prod MeasureTheory.volume) := by
          simp [ MeasureTheory.MeasureSpace.volume ]
          erw [ MeasureTheory.Measure.pi_eq ]
          intro s hs
          erw [ MeasureTheory.Measure.map_apply ]
          · simp [ Set.preimage, Fin.forall_fin_succ ]
            erw [ show
              { x : ℝ × (Fin 2 → ℝ) |
                x.1 ∈ s 0 ∧ x.2 0 ∈ s 1 ∧ x.2 1 ∈ s 2 } =
              (s 0 ×ˢ { x : Fin 2 → ℝ | x 0 ∈ s 1 ∧ x 1 ∈ s 2 })
              by ext; simp [Set.mem_prod],
              MeasureTheory.Measure.prod_prod ]
            simp [ Fin.prod_univ_three ]
            erw [ show
              { x : Fin 2 → ℝ | x 0 ∈ s 1 ∧ x 1 ∈ s 2 } =
              (Set.pi Set.univ fun i : Fin 2 =>
                if i = 0 then s 1 else s 2)
              by ext; simp [ Fin.forall_fin_two ] ]
            erw [ MeasureTheory.Measure.pi_pi ]
            simp [ mul_assoc ]
          · exact measurable_pi_iff.mpr fun i => by
              fin_cases i <;> [exact measurable_fst;
                exact measurable_pi_iff.mp measurable_snd 0;
                exact measurable_pi_iff.mp measurable_snd 1]
          · exact MeasurableSet.univ_pi hs
        rw [ h_iso, MeasureTheory.integrable_map_measure ]
        · rfl
        · exact Continuous.aestronglyMeasurable
            (by exact Real.continuous_exp.comp <|
              continuous_const.dotProduct continuous_id')
        · refine Continuous.aemeasurable ?_
          exact continuous_pi_iff.mpr fun i => by
            fin_cases i <;> [exact continuous_fst;
              exact continuous_apply 0 |> Continuous.comp <| continuous_snd;
              exact continuous_apply 1 |> Continuous.comp <| continuous_snd]
      rw [ MeasureTheory.integrable_prod_iff ] at h_integrable
      · simp_all [ Real.exp_add,
          MeasureTheory.integral_const_mul,
          MeasureTheory.integral_mul_const ]
        by_cases h :
            ∫ (a : Fin 2 → ℝ),
              Real.exp (b 1 * a 0) *
              Real.exp (b 2 * a 1) = 0 <;>
          simp_all [
            MeasureTheory.integrable_const_mul_iff ]
        · rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg (fun _ => by positivity) ] at h
          · exact absurd (h.exists) (by norm_num [ Real.exp_ne_zero ])
          · exact h_integrable
        · convert h_integrable.2.div_const
            (∫ (a : Fin 2 → ℝ),
              Real.exp (b 1 * a 0) *
              Real.exp (b 2 * a 1) ) using 1
          ext v; simp [mul_div_cancel_of_imp (fun h' => absurd h' h)]
      · exact h_integrable.1
    exact h_integrable ‹_›
  by_cases hb0 : b 0 = 0
  · simp_all [ MeasureTheory.integrable_const_iff ]
    exact absurd (h_integrable.measure_univ_lt_top) (by norm_num)
  · have := h_integrable.comp_smul (inv_ne_zero hb0)
    simp_all [ mul_assoc, mul_comm, mul_left_comm ]
    convert absurd (this.lintegral_lt_top) _; norm_num [ Real.exp_pos ]
    have h_exp_inf :
        ∫⁻ (x : ℝ), ENNReal.ofReal (Real.exp x) ≥
        ∫⁻ (x : ℝ) in Set.Ioi 0,
          ENNReal.ofReal (Real.exp x) := by
      exact MeasureTheory.setLIntegral_le_lintegral _ _
    exact le_top.antisymm (h_exp_inf.trans' <| by
      exact le_trans (by norm_num) <|
        MeasureTheory.setLIntegral_mono' measurableSet_Ioi
          fun x hx =>
          ENNReal.ofReal_le_ofReal <|
          Real.one_le_exp hx.out.le)

/-- Smoothness of velocity gradient: if g is smooth, so is vGrad g. -/
lemma analysis_vGrad_smooth
    (g : (Fin 3 → ℝ) → ℝ) (hg : ContDiff ℝ 3 g) :
    ContDiff ℝ 2 (fun v => vGrad g v) := by
  -- Proved by Aristotle (Harmonic)
  refine contDiff_pi.2 fun i => ?_
  apply_rules [ ContDiff.fderiv_apply, contDiff_id, contDiff_const ]
  fun_prop (disch := solve_by_elim)
  norm_num

/-- Gap 12: (v · a) |v|² = 0 for all v ∈ ℝ³ implies a = 0.
    Choose v = t eᵢ, divide by t³, let t → ∞.
    Reference: Step in the proof of Lemma 14 (lem:T_constant). -/
lemma cubic_coeff_zero (a : Fin 3 → ℝ) (h : ∀ v, dotProduct v a * normSq v = 0) :
    a = 0 := by
  -- Proved by Aristotle (Harmonic)
  ext j
  by_contra h_a_nonzero
  specialize h (Pi.single j 1)
  simp_all [Fin.sum_univ_three, dotProduct]
  fin_cases j <;> simp_all [VML.normSq]

/-- Gap 15: Maximum principle for the Poisson–Boltzmann equation on T³.
    If T∞ Δ(log n) = n - ρ_ion with T∞ > 0 and n > 0, then n ≡ ρ_ion.
    At the maximum of n: Δ(log n) ≤ 0 → n ≤ ρ_ion.
    At the minimum: Δ(log n) ≥ 0 → n ≥ ρ_ion.
    Reference: Proof of Lemma 21 (lem:density_constant). -/
lemma poisson_boltzmann_max_principle
    (X : Type*) [Nonempty X]
    (n : X → ℝ) (ρ_ion T_infty : ℝ)
    (laplacian : (X → ℝ) → X → ℝ)
    (_hn_pos : ∀ x, 0 < n x) (hT : 0 < T_infty) (_hρ : 0 < ρ_ion)
    -- PB equation: T∞ Δ(log n) = n - ρ_ion
    (hPB : ∀ x, T_infty * laplacian (Real.log ∘ n) x = n x - ρ_ion)
    -- Maximum principle: n attains its max and min (compactness)
    (x_max : X) (hmax : ∀ x, n x ≤ n x_max)
    (x_min : X) (hmin : ∀ x, n x_min ≤ n x)
    -- At a maximum of n, Δ(log n) ≤ 0 (second derivative test)
    (hmax_lapl : laplacian (Real.log ∘ n) x_max ≤ 0)
    -- At a minimum of n, Δ(log n) ≥ 0
    (hmin_lapl : 0 ≤ laplacian (Real.log ∘ n) x_min) :
    ∀ x, n x = ρ_ion := by
  -- Proved by Aristotle (Harmonic)
  have h_eq : n x_max = ρ_ion ∧ n x_min = ρ_ion := by
    constructor <;> nlinarith [hPB x_max, hPB x_min, hmax x_min, hmin x_max]
  exact fun x => le_antisymm (by linarith [hmax x]) (by linarith [hmin x])

/-- If `f` equals a Gaussian `exp(a₀ + b·v + c₀|v|²)`, then the first moment
    `∫ vᵢ f(v)` equals `(∫ f(v)) * (-1/(2c₀)) * bᵢ`. -/
lemma current_density_of_gaussian
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_int : Integrable f)
    (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hform : ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v))
    (i : Fin 3) :
    ∫ v, v i * f v = (∫ v, f v) * ((-1 / (2 * c₀)) * b i) := by
  have h_rw : ∫ v, v i * f v = ∫ v, v i *
      Real.exp (a₀ + dotProduct b v + c₀ * normSq v) := by
    congr 1; ext v; rw [hform]
  rw [h_rw]
  have hc₀_neg : c₀ < 0 := analysis_gaussian_integrability f a₀ b c₀ hf_pos hf_int hform
  have h_int : Integrable (fun v : Fin 3 → ℝ =>
      Real.exp (a₀ + dotProduct b v + c₀ * normSq v)) := by
    convert hf_int using 1; ext v; rw [hform]
  have h_fm := gaussian_first_moment a₀ b c₀ hc₀_neg h_int i
  rw [h_fm]
  have h_rho : ∫ v : Fin 3 → ℝ,
      Real.exp (a₀ + dotProduct b v + c₀ * normSq v) = ∫ v, f v := by
    congr 1; ext v; rw [hform]
  rw [h_rho]; ring

end VML
