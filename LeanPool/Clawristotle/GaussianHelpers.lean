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
  · norm_num [ dotProduct, Fin.sum_univ_three ]
    ring_nf
    field_simp
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
    fin_cases i <;> simp <;> ring!
  · norm_num [ dotProduct ]
    fun_prop (disch := norm_num)

/-- Gaussian normalization: if f(v) = exp(a₀ + c₀|v|²) with c₀ < 0 and ∫f = ρIon,
    then f = equilibriumMaxwellian ρIon T with T = -1/(2c₀).
    Proved by Aristotle (project 1236b757). -/
lemma gaussian_normalization_maxwellian
    (ρIon a₀ c₀ : ℝ) (_hρ : 0 < ρIon) (hc₀ : c₀ < 0)
    (f : (Fin 3 → ℝ) → ℝ)
    (hf : ∀ v, f v = Real.exp (a₀ + c₀ * normSq v))
    (hf_int : ∫ v : Fin 3 → ℝ, f v = ρIon) :
    ∀ v, f v = equilibriumMaxwellian ρIon (-1 / (2 * c₀)) v := by
  -- Proved by Aristotle (project 1236b757), adapted to standard Mathlib generalize_proofs.
  have h_m_int : ∫ v : Fin 3 → ℝ,
      Real.exp (c₀ * (normSq v)) = (Real.pi / (-c₀)) ^ ((3 : ℝ) / 2) := by
    have h_gauss : ∫ v : Fin 3 → ℝ,
        Real.exp (c₀ * normSq v) =
        (∏ i : Fin 3, ∫ v : ℝ, Real.exp (c₀ * v^2)) := by
      have h_fubini : ∫ v : Fin 3 → ℝ, Real.exp (c₀ * normSq v) =
          ∫ v : Fin 3 → ℝ, (∏ i : Fin 3, Real.exp (c₀ * (v i) ^ 2)) := by
        norm_num [← Real.exp_sum, normSq, dotProduct, Fin.sum_univ_three]
        congr 1; ext; ring_nf
      generalize_proofs at *
      erw [h_fubini, ← MeasureTheory.integral_fintype_prod_eq_prod]
      rfl
    generalize_proofs at *
    have := integral_gaussian (-c₀)
    simp_all only [prod_const, card_univ, Fintype.card_fin, neg_neg, div_eq_mul_inv, inv_neg,
      mul_neg, mul_comm]
    have hnn : (0 : ℝ) ≤ -(π * c₀⁻¹) := by
      nlinarith [Real.pi_pos, inv_neg''.mpr hc₀]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hnn]
    norm_num
  simp_all only [exp_add, integral_const_mul]
  intro v
  rw [← hf_int]
  unfold equilibriumMaxwellian
  have hc₀_ne : c₀ ≠ 0 := ne_of_lt hc₀
  rw [show 2 * Real.pi * (-1 / (2 * c₀)) = Real.pi / (-c₀) from by field_simp]
  have h_rpow_ne : (Real.pi / (-c₀)) ^ ((3 : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (div_pos Real.pi_pos (neg_pos.mpr hc₀)) _)
  rw [mul_div_assoc, div_self h_rpow_ne, mul_one]
  congr 1; field_simp


/-- Gaussian first moment: ∫ vᵢ exp(a+b·v+c|v|²) = (-bᵢ/(2c)) · ∫ exp(a+b·v+c|v|²).
    Proved by Aristotle (project 4c5e7998). -/
lemma gaussian_first_moment (a : ℝ) (b : Fin 3 → ℝ) (c : ℝ) (hc : c < 0)
    (_hf_int : Integrable (fun v : Fin 3 → ℝ => Real.exp (a + dotProduct b v + c * normSq v))) :
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
        (∫ v : ℝ, Real.exp (a + b * v + c * v^2)) := fun a b c hc_neg => by
      have h_gauss_integral : ∫ v : ℝ, (v + b / (2 * c)) * Real.exp (a + b * v + c * v^2) = 0 := by
        suffices h_subst :
            ∫ v : ℝ, (v + b / (2 * c)) *
              Real.exp (a + b * v + c * v^2) =
            ∫ u : ℝ, u *
              Real.exp (a - b^2 / (4 * c) + c * u^2) by
          have h_odd : ∀ f : ℝ → ℝ, (∀ x, f (-x) = -f x) → ∫ x : ℝ, f x = 0 := fun f hf_odd => by
            have h_symm : ∫ x : ℝ, f x = ∫ x : ℝ, f (-x) := by
              rw [ MeasureTheory.integral_neg_eq_self ]
            have h_zero : ∫ x : ℝ, f x = -∫ x : ℝ, f x := by
              conv_lhs => rw [h_symm]
              simp_rw [hf_odd]
              rw [MeasureTheory.integral_neg]
            linarith [h_zero]
          exact h_subst.trans (h_odd _ fun x => by ring_nf)
        rw [← MeasureTheory.integral_add_right_eq_self _ (-b / (2 * c))]
        congr 1; ext; ring_nf; norm_num [hc_neg.ne]; ring_nf; grind
      simp_all only [div_eq_mul_inv, _root_.mul_inv_rev, add_mul, neg_mul]
      rw [ MeasureTheory.integral_add ] at h_gauss_integral <;> norm_num at *
      · rw [ MeasureTheory.integral_const_mul ] at h_gauss_integral; linarith
      · have h_integrable : MeasureTheory.Integrable
            (fun v : ℝ => v * Real.exp (c * v^2 + b * v))
            MeasureTheory.MeasureSpace.volume := by
          have h_gauss : ∀ v : ℝ,
              |v * Real.exp (c * v^2 + b * v)| ≤
              |v| * Real.exp (c * v^2 / 2) *
              Real.exp (b^2 / (2 * |c|)) := fun v => by
            simp only [abs_mul, abs_exp]
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
            convert integral_gaussian ( -c) using 1
            norm_num [ hc_neg.le ]
            rw [ eq_comm, ← MeasureTheory.integral_sub_right_eq_self ]
          rw [← h_gauss_integral, ← MeasureTheory.integral_mul_const]
          congr 1; ext v; ring_nf; rw [← Real.exp_add]; norm_num [sq, mul_assoc, hc_neg.ne]; ring
        exact MeasureTheory.Integrable.const_mul (by
          contrapose! h_gauss_integral
          rw [MeasureTheory.integral_undef h_gauss_integral]
          exact ne_of_lt (mul_pos
            (Real.sqrt_pos.mpr (div_pos Real.pi_pos (neg_pos.mpr hc_neg)))
            (Real.exp_pos _))) _
    have h_gauss_integral_component :
        ∀ i : Fin 3,
        ∫ v : Fin 3 → ℝ, v i * Real.exp (a + b ⬝ᵥ v + c * normSq v) =
        (∫ v : ℝ, v * Real.exp (a + b i * v + c * v^2)) *
        (∏ j ∈ Finset.univ.erase i,
          ∫ v : ℝ, Real.exp (b j * v + c * v^2)) := fun i => by
      have h_fubini :
          ∫ v : Fin 3 → ℝ,
            v i * Real.exp (a + b ⬝ᵥ v + c * normSq v) =
          ∫ v : Fin 3 → ℝ,
            (∏ j, (if j = i
              then v j * Real.exp (a + b j * v j + c * v j^2)
              else Real.exp (b j * v j + c * v j^2))) := by
        simp only [prod_ite, filter_eq', mem_univ, ↓reduceIte, prod_singleton, filter_ne']
        simp only [normSq, ← exp_sum, sum_add_distrib, mem_univ, sum_erase_eq_sub, mul_assoc]
        simp only [dotProduct, Fin.sum_univ_three, Fin.isValue, ← exp_add]
        congr 1; ext; ring_nf!
      have h_fubini2 :
          ∫ v : Fin 3 → ℝ, (∏ j, (if j = i
            then v j * Real.exp (a + b j * v j + c * v j^2)
            else Real.exp (b j * v j + c * v j^2))) =
          (∏ j, ∫ v : ℝ, (if j = i
            then v * Real.exp (a + b j * v + c * v^2)
            else Real.exp (b j * v + c * v^2))) := by
        erw [← MeasureTheory.integral_fintype_prod_eq_prod]; rfl
      simp_all only [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i), ↓reduceIte,
        mul_eq_mul_left_iff, mul_eq_zero, div_eq_zero_iff, neg_eq_zero, OfNat.ofNat_ne_zero,
        false_or]
      exact Or.inl (by
        rw [Finset.sdiff_singleton_eq_erase]
        exact Finset.prod_congr rfl fun x hx => by simp_all)
    have h_gauss_integral_component2 :
        ∫ v : Fin 3 → ℝ,
          Real.exp (a + b ⬝ᵥ v + c * normSq v) =
        (∏ j : Fin 3,
          ∫ v : ℝ, Real.exp (b j * v + c * v^2)) *
        Real.exp a := by
      rw [show ∫ v : Fin 3 → ℝ, Real.exp (a + b ⬝ᵥ v + c * normSq v) =
          ∫ v : Fin 3 → ℝ,
            Real.exp a * ∏ j : Fin 3, Real.exp (b j * v j + c * v j^2) from by
          simp only [dotProduct, Fin.sum_univ_three, Fin.isValue, normSq, ← exp_sum, ← exp_add]
          congr 1; ext; ring_nf,
        mul_comm, MeasureTheory.integral_const_mul]
      congr 1
      erw [← MeasureTheory.integral_fintype_prod_eq_prod]; rfl
    simp_all only
    rw [ ← Finset.mul_prod_erase _ _ (Finset.mem_univ i) ]; ring_nf
    simp [ Real.exp_add, add_comm,
      mul_assoc, mul_comm, mul_left_comm,
      MeasureTheory.integral_const_mul ]
  exact h_gauss

/-- Gaussian integrability: exp(a₀+b·v+c₀|v|²) with f integrable implies c₀ < 0. -/
lemma analysis_gaussian_integrability
    (f : (Fin 3 → ℝ) → ℝ) (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (_hf_pos : ∀ v, 0 < f v)
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
    · simp_all only [exp_pos, implies_true, norm_eq_abs, abs_exp, exp_le_exp,
        le_add_iff_nonneg_right]
      exact Filter.Eventually.of_forall fun x => mul_nonneg hf_int (by
        change 0 ≤ VML.normSq x
        unfold VML.normSq
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have h_integrable : MeasureTheory.Integrable
      (fun v : Fin 3 → ℝ => Real.exp (b ⬝ᵥ v))
      MeasureTheory.MeasureSpace.volume := by
    convert h_integrable.const_mul (Real.exp (-a₀)) using 2
    simp [← Real.exp_add]
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
          simp only [volume, Nat.reduceAdd]
          erw [ MeasureTheory.Measure.pi_eq ]
          intro s hs
          erw [ MeasureTheory.Measure.map_apply ]
          · simp only [Set.preimage, Set.mem_pi, Set.mem_univ, forall_const, Fin.forall_fin_succ,
              Fin.isValue, Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
              IsEmpty.forall_iff, and_true]
            erw [ show
              { x : ℝ × (Fin 2 → ℝ) |
                x.1 ∈ s 0 ∧ x.2 0 ∈ s 1 ∧ x.2 1 ∈ s 2 } =
              (s 0 ×ˢ { x : Fin 2 → ℝ | x 0 ∈ s 1 ∧ x 1 ∈ s 2 })
              by ext; simp [Set.mem_prod],
              MeasureTheory.Measure.prod_prod ]
            simp only [Fin.isValue, Fin.prod_univ_three]
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
      · simp_all only [exp_add, Fin.isValue, Fin.sum_univ_two, Fin.succ_zero_eq_one,
          Fin.succ_one_eq_two, norm_mul, norm_eq_abs, abs_exp, integral_const_mul]
        by_cases h :
            ∫ (a : Fin 2 → ℝ),
              Real.exp (b 1 * a 0) *
              Real.exp (b 2 * a 1) = 0 <;>
          simp_all only [isUnit_iff_ne_zero, ne_eq, exp_ne_zero, not_false_eq_true,
            integrable_const_mul_iff, Fin.isValue, Filter.eventually_const, mul_zero]
        · rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg (fun _ => by positivity) ] at h
          · exact absurd (h.exists) (by norm_num [ Real.exp_ne_zero ])
          · exact h_integrable.1
        · convert h_integrable.2.div_const
            (∫ (a : Fin 2 → ℝ),
              Real.exp (b 1 * a 0) *
              Real.exp (b 2 * a 1) ) using 1
          ext v; simp [mul_div_cancel_of_imp (fun h' => absurd h' h)]
      · exact h_integrable.1
    exact h_integrable ‹_›
  by_cases hb0 : b 0 = 0
  · simp_all only [Fin.isValue, zero_mul, exp_zero, integrable_const_iff, one_ne_zero, false_or]
    exact absurd (h_integrable.measure_univ_lt_top) (by norm_num)
  · have := h_integrable.comp_smul (inv_ne_zero hb0)
    simp_all only [Fin.isValue, mul_comm, smul_eq_mul, mul_left_comm, ne_eq, not_false_eq_true,
      mul_inv_cancel₀, mul_one]
    convert absurd (this.lintegral_lt_top) _; norm_num [ Real.exp_pos ]
    exact le_top.antisymm ((MeasureTheory.setLIntegral_le_lintegral _ _).trans' <| by
      exact le_trans (by norm_num) <|
        MeasureTheory.setLIntegral_mono' measurableSet_Ioi
          fun x hx =>
          ENNReal.ofReal_le_ofReal <|
          Real.one_le_exp hx.out.le)

/-- Smoothness of velocity gradient: if g is smooth, so is vGrad g. -/
lemma analysis_vGrad_smooth
    (g : (Fin 3 → ℝ) → ℝ) (hg : ContDiff ℝ 3 g) :
    ContDiff ℝ 2 (fun v => vGrad g v) :=
  contDiff_pi.2 fun i => by
    apply_rules [ContDiff.fderiv_apply, contDiff_id, contDiff_const]
    · fun_prop (disch := solve_by_elim)
    · norm_num

/-- Gap 12: (v · a) |v|² = 0 for all v ∈ ℝ³ implies a = 0.
    Choose v = t eᵢ, divide by t³, let t → ∞.
    Reference: Step in the proof of Lemma 14 (lem:T_constant). -/
lemma cubic_coeff_zero (a : Fin 3 → ℝ) (h : ∀ v, dotProduct v a * normSq v = 0) :
    a = 0 := by
  -- Proved by Aristotle (Harmonic)
  ext j
  by_contra h_a_nonzero
  specialize h (Pi.single j 1)
  simp_all only [Pi.zero_apply, dotProduct, Fin.sum_univ_three, Fin.isValue, mul_eq_zero]
  fin_cases j <;> simp_all [VML.normSq]

/-- Gap 15: Maximum principle for the Poisson–Boltzmann equation on T³.
    If T∞ Δ(log n) = n - ρIon with T∞ > 0 and n > 0, then n ≡ ρIon.
    At the maximum of n: Δ(log n) ≤ 0 → n ≤ ρIon.
    At the minimum: Δ(log n) ≥ 0 → n ≥ ρIon.
    Reference: Proof of Lemma 21 (lem:density_constant). -/
lemma poisson_boltzmann_max_principle
    (X : Type*) [Nonempty X]
    (n : X → ℝ) (ρIon T_infty : ℝ)
    (laplacian : (X → ℝ) → X → ℝ)
    (_hn_pos : ∀ x, 0 < n x) (hT : 0 < T_infty) (_hρ : 0 < ρIon)
    -- PB equation: T∞ Δ(log n) = n - ρIon
    (hPB : ∀ x, T_infty * laplacian (Real.log ∘ n) x = n x - ρIon)
    -- Maximum principle: n attains its max and min (compactness)
    (xMax : X) (hmax : ∀ x, n x ≤ n xMax)
    (xMin : X) (hmin : ∀ x, n xMin ≤ n x)
    -- At a maximum of n, Δ(log n) ≤ 0 (second derivative test)
    (hmax_lapl : laplacian (Real.log ∘ n) xMax ≤ 0)
    -- At a minimum of n, Δ(log n) ≥ 0
    (hmin_lapl : 0 ≤ laplacian (Real.log ∘ n) xMin) :
    ∀ x, n x = ρIon := by
  -- Proved by Aristotle (Harmonic)
  have h_eq : n xMax = ρIon ∧ n xMin = ρIon := by
    constructor <;> nlinarith [hPB xMax, hPB xMin, hmax xMin, hmin xMax]
  exact fun x => le_antisymm (by linarith [hmax x]) (by linarith [hmin x])

/-- If `f` equals a Gaussian `exp(a₀ + b·v + c₀|v|²)`, then the first moment
    `∫ vᵢ f(v)` equals `(∫ f(v)) * (-1/(2c₀)) * bᵢ`. -/
lemma current_density_of_gaussian
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_int : Integrable f)
    (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hform : ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v))
    (i : Fin 3) :
    ∫ v, v i * f v = (∫ v, f v) * ((-1 / (2 * c₀)) * b i) := by
  have hc₀_neg : c₀ < 0 := analysis_gaussian_integrability f a₀ b c₀ hf_pos hf_int hform
  rw [show ∫ v, v i * f v = ∫ v, v i * Real.exp (a₀ + dotProduct b v + c₀ * normSq v) from
    congr_arg _ (funext fun v => by rw [hform]),
    gaussian_first_moment a₀ b c₀ hc₀_neg
      (hf_int.congr (by filter_upwards [] with v; rw [hform])) i,
    show ∫ v : Fin 3 → ℝ, Real.exp (a₀ + dotProduct b v + c₀ * normSq v) = ∫ v, f v from
      congr_arg _ (funext fun v => by rw [hform])]
  ring

end VML
