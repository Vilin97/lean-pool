/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.CoulombFlux

/-!
# PSD Helpers: Continuity and Pointwise Bounds for Coulomb

Proves the Landau quadratic form bound, continuity of the PSD integrand
(the Coulomb singularity cancels in the quadratic form), and pointwise bounds.
These are building blocks for the integrability and Fubini results in CoulombPSD.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

lemma landau_bound (z u : Fin 3 → ℝ) :
    abs (dotProduct u (mulVec (landauMatrix coulombKernel z) u)) ≤
    (if eucNorm z = 0 then 0 else (eucNorm z)⁻¹) * (eucNorm u)^2 := by
      unfold landauMatrix eucNorm coulombKernel innerLandauMatrix normSq
      split_ifs <;> norm_cast <;> norm_num [ Matrix.vecMulVec ] at *
      · simp_all only [dotProduct, Fin.sum_univ_three, Fin.isValue, Std.le_refl]
        rw [ Real.sqrt_eq_zero' ] at *
        norm_num [ show z 0 = 0 by nlinarith, show z 1 = 0 by nlinarith,
                   show z 2 = 0 by nlinarith, Matrix.mulVec ]
      · exact False.elim <| ‹¬Real.sqrt (z ⬝ᵥ z) = 0› <| le_antisymm ‹_› <| Real.sqrt_nonneg _
      · rw [ Real.sqrt_eq_zero' ] at *; linarith
      · suffices h_simp :
            abs ((Real.sqrt (dotProduct z z))⁻¹ ^ 3 *
              (dotProduct z z * dotProduct u u - (dotProduct z u) ^ 2)) ≤
            (Real.sqrt (dotProduct z z))⁻¹ * (Real.sqrt (dotProduct u u)) ^ 2 by
          convert h_simp using 2
          norm_num [ Matrix.mulVec, dotProduct ]
          ring_nf
          norm_num [ Fin.sum_univ_three, Matrix.one_apply ]; ring
        suffices h_cancel :
            abs (z ⬝ᵥ z * u ⬝ᵥ u - (z ⬝ᵥ u) ^ 2) ≤
            (Real.sqrt (z ⬝ᵥ z)) ^ 2 * (Real.sqrt (u ⬝ᵥ u)) ^ 2 by
          rw [ abs_mul, abs_of_nonneg (by positivity) ]
          field_simp
          exact h_cancel
        rw [ Real.sq_sqrt (by positivity),
             Real.sq_sqrt (by exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _) ]
        norm_num [ Fin.sum_univ_three, dotProduct ] at *
        exact abs_le.mpr
          ⟨ by nlinarith [ sq_nonneg (z 0 * u 1 - z 1 * u 0),
                           sq_nonneg (z 0 * u 2 - z 2 * u 0),
                           sq_nonneg (z 1 * u 2 - z 2 * u 1) ],
            by nlinarith [ sq_nonneg (z 0 * u 1 - z 1 * u 0),
                           sq_nonneg (z 0 * u 2 - z 2 * u 0),
                           sq_nonneg (z 1 * u 2 - z 2 * u 1) ] ⟩


lemma tendsto_landau_quadratic_diag
    (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hG : ContDiff ℝ 1 G)
    (x : Fin 3 → ℝ) :
    Filter.Tendsto (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (G p.1 - G p.2)
        (mulVec (landauMatrix coulombKernel (p.1 - p.2)) (G p.1 - G p.2)))
      (nhds (x, x)) (nhds 0) := by
        obtain ⟨U, hU⟩ : ∃ U : Set (Fin 3 → ℝ), IsOpen U ∧ x ∈ U ∧
            ∃ L : ℝ, ∀ u v : Fin 3 → ℝ,
              u ∈ U → v ∈ U → eucNorm (G u - G v) ≤ L * eucNorm (u - v) := by
          obtain ⟨U, hU⟩ : ∃ U : Set (Fin 3 → ℝ), IsOpen U ∧ x ∈ U ∧
              ∃ L : ℝ, ∀ u ∈ U, ∀ v ∈ U, ‖G u - G v‖ ≤ L * ‖u - v‖ := by
            have hG_diff := hG.differentiable one_ne_zero
            obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ u ∈ Metric.closedBall x 1, ‖fderiv ℝ G u‖ ≤ K := by
              exact IsCompact.exists_bound_of_continuousOn
                (ProperSpace.isCompact_closedBall x 1)
                (hG.continuous_fderiv one_ne_zero |> Continuous.continuousOn)
            refine ⟨ Metric.ball x 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, K,
              fun u hu v hv => ?_ ⟩
            exact (convex_ball x 1).norm_image_sub_le_of_norm_fderiv_le
              (fun y hy => hG_diff.differentiableAt)
              (fun y hy => hK y (Metric.ball_subset_closedBall hy))
              (Metric.mem_ball.mp hv) (Metric.mem_ball.mp hu)
          obtain ⟨ L, hL ⟩ := hU.2.2
          -- eucNorm z ≤ √3 * ‖z‖ and ‖z‖ ≤ eucNorm z for Fin 3 → ℝ
          have h_norm_le_euc : ∀ z : Fin 3 → ℝ, ‖z‖ ≤ eucNorm z := by
            intro z; unfold eucNorm normSq
            have h_each : ∀ i : Fin 3, |z i| ≤ Real.sqrt (z ⬝ᵥ z) := by
              intro i
              refine Real.le_sqrt_of_sq_le ?_
              simp only [dotProduct, Fin.sum_univ_three]
              fin_cases i <;> simp [sq_abs] <;>
                nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2)]
            calc ‖z‖ = ‖z‖ := rfl
              _ ≤ Real.sqrt (z ⬝ᵥ z) := by
                  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
                  exact fun i => by rw [Real.norm_eq_abs]; exact h_each i
          have h_euc_le_norm : ∀ z : Fin 3 → ℝ, eucNorm z ≤ Real.sqrt 3 * ‖z‖ := by
            intro z; unfold eucNorm normSq
            rw [show Real.sqrt 3 * ‖z‖ = Real.sqrt (3 * ‖z‖ ^ 2) from by
              rw [Real.sqrt_mul (by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_sq (norm_nonneg z)]]
            apply Real.sqrt_le_sqrt
            simp only [dotProduct, Fin.sum_univ_three]
            have h0 := norm_le_pi_norm z (0 : Fin 3)
            have h1 := norm_le_pi_norm z (1 : Fin 3)
            have h2 := norm_le_pi_norm z (2 : Fin 3)
            rw [Real.norm_eq_abs] at h0 h1 h2
            nlinarith [sq_abs (z 0), sq_abs (z 1), sq_abs (z 2),
              sq_nonneg ‖z‖,
              sq_le_sq' (by linarith [abs_nonneg (z 0), norm_nonneg z]) h0,
              sq_le_sq' (by linarith [abs_nonneg (z 1), norm_nonneg z]) h1,
              sq_le_sq' (by linarith [abs_nonneg (z 2), norm_nonneg z]) h2]
          refine ⟨ U, hU.1, hU.2.1, Real.sqrt 3 * L, fun u v hu hv => ?_ ⟩
          by_cases huv : u = v
          · simp [huv, eucNorm, normSq, dotProduct]
          · have hLuv := hL u hu v hv
            have hL_nn : 0 ≤ L := by
              have hn := norm_nonneg (G u - G v)
              have hpos : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
              nlinarith
            calc eucNorm (G u - G v)
                ≤ Real.sqrt 3 * ‖G u - G v‖ := h_euc_le_norm _
              _ ≤ Real.sqrt 3 * (L * ‖u - v‖) := by gcongr
              _ ≤ Real.sqrt 3 * (L * eucNorm (u - v)) := by
                  gcongr; exact h_norm_le_euc _
              _ = Real.sqrt 3 * L * eucNorm (u - v) := by ring
        obtain ⟨L, hL⟩ := hU.right.right
        have h_bound : ∀ᶠ p : (Fin 3 → ℝ) × (Fin 3 → ℝ) in nhds (x, x),
            abs ((G p.1 - G p.2) ⬝ᵥ landauMatrix coulombKernel (p.1 - p.2) *ᵥ (G p.1 - G p.2)) ≤
            (if eucNorm (p.1 - p.2) = 0 then 0 else (eucNorm (p.1 - p.2))⁻¹) *
            (L * eucNorm (p.1 - p.2))^2 := by
          have h_bound : ∀ᶠ p : (Fin 3 → ℝ) × (Fin 3 → ℝ) in nhds (x, x),
              eucNorm (G p.1 - G p.2) ≤ L * eucNorm (p.1 - p.2) := by
            exact Filter.eventually_of_mem
              (IsOpen.mem_nhds (hU.1.prod hU.1) ⟨hU.2.1, hU.2.1⟩)
              fun p hp => hL _ _ hp.1 hp.2
          filter_upwards [ h_bound ] with p hp
          exact le_trans (landau_bound _ _) (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Real.sqrt_nonneg _) hp 2)
            (by split_ifs with h
                · exact le_refl 0
                · exact inv_nonneg.2 (Real.sqrt_nonneg _)))
        have h_simplified_bound : ∀ᶠ p : (Fin 3 → ℝ) × (Fin 3 → ℝ) in nhds (x, x),
            abs ((G p.1 - G p.2) ⬝ᵥ landauMatrix coulombKernel (p.1 - p.2) *ᵥ
              (G p.1 - G p.2)) ≤ L^2 * eucNorm (p.1 - p.2) := by
          filter_upwards [ h_bound ] with p hp using le_trans hp
            (by split_ifs <;>
              simp [ *, sq, mul_assoc, mul_comm, mul_left_comm ])
        have h_cont : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
            L ^ 2 * eucNorm (p.1 - p.2)) :=
          Continuous.mul continuous_const <| Real.continuous_sqrt.comp <|
            (Continuous.dotProduct (continuous_fst.sub continuous_snd)
              (continuous_fst.sub continuous_snd))
        have h_tends : Filter.Tendsto (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
            L ^ 2 * eucNorm (p.1 - p.2)) (nhds (x, x)) (nhds 0) :=
          h_cont.tendsto' _ _ (by simp [eucNorm, normSq, dotProduct])
        exact squeeze_zero_norm' (h_simplified_bound.mono fun p hp => by
          rw [Real.norm_eq_abs]; exact hp) h_tends


lemma continuous_landau_quadratic
    (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hG : ContDiff ℝ 1 G) :
    Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (G p.1 - G p.2)
        (mulVec (landauMatrix coulombKernel (p.1 - p.2)) (G p.1 - G p.2))) := by
        set F : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) → ℝ := fun p =>
          (G p.1 - G p.2) ⬝ᵥ landauMatrix coulombKernel (p.1 - p.2) *ᵥ (G p.1 - G p.2)
        have h_cont_away : ∀ p : (Fin 3 → ℝ) × (Fin 3 → ℝ), p.1 ≠ p.2 → ContinuousAt F p := by
          intro p hp_ne
          have h_cont_A : ContinuousAt (fun z => landauMatrix coulombKernel z) (p.1 - p.2) := by
            change ContinuousAt
              (fun z => coulombKernel (eucNorm z) • innerLandauMatrix z) (p.1 - p.2)
            apply ContinuousAt.smul
            · have h_cont_eucNorm : ContinuousAt (fun z => eucNorm z) (p.1 - p.2) := by
                exact Continuous.continuousAt
                  (by exact Real.continuous_sqrt.comp <|
                    by exact Continuous.dotProduct continuous_id continuous_id)
              have h_pos : 0 < eucNorm (p.1 - p.2) := by
                unfold eucNorm
                unfold normSq; simp only [dotProduct_sub, sub_dotProduct, sqrt_pos, sub_pos]
                simp_all only [ne_eq, dotProduct, Fin.sum_univ_three, Fin.isValue]
                exact not_le.mp fun h => hp_ne <| by
                  ext i; fin_cases i <;> nlinarith! [ sq_nonneg (p.1 0 - p.2 0),
                    sq_nonneg (p.1 1 - p.2 1), sq_nonneg (p.1 2 - p.2 2) ]
              have h_cont_coulomb :
                  ContinuousAt (fun z => coulombKernel z) (eucNorm (p.1 - p.2)) := by
                have h_rpow : ContinuousAt (fun z => z ^ ((-3 : ℝ) : ℝ)) (eucNorm (p.1 - p.2)) :=
                  ContinuousAt.rpow continuousAt_id continuousAt_const <|
                    Or.inl <| ne_of_gt h_pos
                exact h_rpow.congr (Filter.eventuallyEq_iff_exists_mem.mpr
                  ⟨Set.Ioi 0, lt_mem_nhds h_pos, fun z hz => by
                    simp only [Set.mem_Ioi] at hz
                    simp only [coulombKernel, if_neg (not_le.mpr hz)]⟩)
              exact h_cont_coulomb.comp h_cont_eucNorm
            · exact (Continuous.smul
                (show Continuous fun z : Fin 3 → ℝ => normSq z from
                  Continuous.dotProduct (continuous_id') (continuous_id') )
                (continuous_const)
                |>.sub <|
                  Continuous.matrix_vecMulVec (continuous_id') (continuous_id')).continuousAt
          have h_cont_G : ContinuousAt (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => G p.1 - G p.2) p := by
            exact ContinuousAt.sub
              (hG.continuous.continuousAt.comp continuousAt_fst)
              (hG.continuous.continuousAt.comp continuousAt_snd)
          have h_cont_F : ContinuousAt (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
              (G p.1 - G p.2) ⬝ᵥ
              (landauMatrix coulombKernel (p.1 - p.2)) *ᵥ (G p.1 - G p.2)) p := by
            fun_prop (disch := norm_num)
          exact h_cont_F
        apply continuous_iff_continuousAt.mpr
        intro p
        by_cases hp : p.1 = p.2
        · have h_tendsto : Filter.Tendsto F (nhds (p.1, p.1)) (nhds 0) := by
            convert tendsto_landau_quadratic_diag G hG p.1 using 1
          change ContinuousAt F p
          have hpeq : p = (p.1, p.1) := Prod.ext rfl hp.symm
          rw [ContinuousAt, hpeq, show F (p.1, p.1) = 0 from by simp [F]]
          exact h_tendsto
        · exact h_cont_away p hp

/-- PSD integrand is jointly continuous for Coulomb kernel.
    Despite Ψ(r) = r⁻³ being singular, the score difference cancels the singularity.
    Proved by Aristotle (job 14300a69).
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma psd_continuous_coulomb
    (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ 3 f) :
    Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand coulombKernel f p.1 p.2) := by
  simp only [PSDIntegrand]
  refine Continuous.mul
    (Continuous.mul
      (hf_smooth.continuous.comp continuous_fst)
      (hf_smooth.continuous.comp continuous_snd) ) ?_
  set G := fun v => fderiv ℝ (Real.log ∘ f) v
  have h_log_smooth : ContDiff ℝ 3 (Real.log ∘ f) := by
    exact ContDiff.log hf_smooth fun v => ne_of_gt <| hf_pos v
  have h_G_smooth : ContDiff ℝ 1 G := by
    apply_rules [ ContDiff.fderiv, h_log_smooth ]
    exacts [ h_log_smooth.comp (contDiff_snd), contDiff_id, by norm_num ]
  convert continuous_landau_quadratic (fun v => (fun i => G v (Pi.single i 1) )) ?_ using 1
  exact contDiff_pi.mpr fun i => h_G_smooth.clm_apply (contDiff_const)


/-- Pointwise bound on PSD integrand for Coulomb kernel:
    |PSD(v,w)| ≤ 18Cg²f(v) * ((1+‖v‖)^{2Kg}·‖v-w‖⁻¹f(w) + ‖v-w‖⁻¹·(1+‖w‖)^{2Kg}f(w)) -/
lemma psd_pointwise_bound_coulomb
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v)
    {Cg : ℝ} {Kg : ℕ}
    (h_score : ∀ u i, |vGrad (Real.log ∘ f) u i| ≤ Cg * (1 + ‖u‖) ^ Kg)
    (v w : Fin 3 → ℝ) :
    |PSDIntegrand coulombKernel f v w| ≤
    18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * (‖v - w‖⁻¹ * f w) +
                          ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w)) := by
  unfold PSDIntegrand
  set Δ := vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w
  rw [abs_mul, abs_mul, abs_of_pos (hf_pos v), abs_of_pos (hf_pos w)]
  by_cases hvw : v - w = 0
  · have hveqw : v = w := sub_eq_zero.mp hvw; subst hveqw
    simp only [Δ, sub_self, Pi.zero_apply, dotProduct, mulVec, Finset.sum_const_zero,
      mul_zero, abs_zero]; simp [norm_zero, _root_.inv_zero]
  · have h_entry : ∀ i j, |landauMatrix coulombKernel (v - w) i j| ≤ ‖v - w‖⁻¹ :=
      fun i j => coulomb_landauMatrix_entry_le_pi _ i j hvw
    have h_mulvec : ∀ i, |(mulVec (landauMatrix coulombKernel (v - w)) Δ) i| ≤
        ‖v - w‖⁻¹ * ∑ j : Fin 3, |Δ j| := by
      intro i; simp only [mulVec, dotProduct]
      calc |∑ j, landauMatrix coulombKernel (v - w) i j * Δ j|
          ≤ ∑ j, |landauMatrix coulombKernel (v - w) i j| * |Δ j| := by
            exact le_trans (Finset.abs_sum_le_sum_abs _ _)
              (Finset.sum_le_sum fun j _ => (abs_mul _ _).le)
        _ ≤ ∑ j, ‖v - w‖⁻¹ * |Δ j| :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (h_entry i j) (abs_nonneg _)
        _ = ‖v - w‖⁻¹ * ∑ j, |Δ j| := (Finset.mul_sum _ _ _).symm
    have h_quad : |dotProduct Δ (mulVec (landauMatrix coulombKernel (v - w)) Δ)| ≤
        ‖v - w‖⁻¹ * (∑ i : Fin 3, |Δ i|) ^ 2 := by
      simp only [dotProduct]
      calc |∑ i, Δ i * (mulVec (landauMatrix coulombKernel (v - w)) Δ) i|
          ≤ ∑ i, |Δ i| * |(mulVec (landauMatrix coulombKernel (v - w)) Δ) i| := by
            exact le_trans (Finset.abs_sum_le_sum_abs _ _)
              (Finset.sum_le_sum fun i _ => (abs_mul _ _).le)
        _ ≤ ∑ i, |Δ i| * (‖v - w‖⁻¹ * ∑ j, |Δ j|) :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (h_mulvec i) (abs_nonneg _)
        _ = ‖v - w‖⁻¹ * (∑ i : Fin 3, |Δ i|) ^ 2 := by
            rw [sq, ← Finset.sum_mul]; ring
    have h_delta_sum : ∑ i : Fin 3, |Δ i| ≤
        3 * Cg * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg) := by
      simp only [Δ, Pi.sub_apply]
      calc ∑ i : Fin 3, |vGrad (Real.log ∘ f) v i - vGrad (Real.log ∘ f) w i|
          ≤ ∑ i : Fin 3, (Cg * (1 + ‖v‖) ^ Kg + Cg * (1 + ‖w‖) ^ Kg) :=
            Finset.sum_le_sum fun i _ => by
              have := norm_sub_le (vGrad (Real.log ∘ f) v i) (vGrad (Real.log ∘ f) w i)
              rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at this
              linarith [h_score v i, h_score w i]
        _ = 3 * Cg * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg) := by
            simp; ring
    have h_sq_bound : (∑ i : Fin 3, |Δ i|) ^ 2 ≤
        18 * Cg ^ 2 * ((1 + ‖v‖) ^ (2 * Kg) + (1 + ‖w‖) ^ (2 * Kg)) := by
      have h_sum_nn : 0 ≤ ∑ i : Fin 3, |Δ i| :=
        Finset.sum_nonneg fun i _ => abs_nonneg _
      have h1 : (∑ i : Fin 3, |Δ i|) ^ 2 ≤
          9 * Cg ^ 2 * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg) ^ 2 := by
        have h_neg : -(3 * Cg * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg)) ≤ ∑ i : Fin 3, |Δ i| := by
          linarith
        calc _ ≤ (3 * Cg * ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg)) ^ 2 :=
              sq_le_sq' h_neg h_delta_sum
          _ = _ := by ring
      have h2 : ((1 + ‖v‖) ^ Kg + (1 + ‖w‖) ^ Kg) ^ 2 ≤
          2 * ((1 + ‖v‖) ^ (2 * Kg) + (1 + ‖w‖) ^ (2 * Kg)) := by
        rw [show 2 * Kg = Kg + Kg from by omega, pow_add, pow_add]
        nlinarith [sq_nonneg ((1 + ‖v‖) ^ Kg - (1 + ‖w‖) ^ Kg)]
      nlinarith
    calc f v * f w * |dotProduct Δ (mulVec (landauMatrix coulombKernel (v - w)) Δ)|
        ≤ f v * f w * (‖v - w‖⁻¹ *
            (18 * Cg ^ 2 * ((1 + ‖v‖) ^ (2 * Kg) + (1 + ‖w‖) ^ (2 * Kg)))) := by
          gcongr
          · exact mul_nonneg (le_of_lt (hf_pos v)) (le_of_lt (hf_pos w))
          · exact le_trans h_quad (mul_le_mul_of_nonneg_left h_sq_bound
              (inv_nonneg.mpr (norm_nonneg _)))
      _ = 18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * (‖v - w‖⁻¹ * f w) +
               ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w)) := by ring

/-- Pointwise bound on the Fubini double integrand for Coulomb.
    |score(v) · (A(v-w) · flux(v,w))| ≤ 3Cg(1+‖v‖)^Kg * ‖v-w‖⁻¹ * Σ_j (...). -/
lemma fubini_double_pointwise_bound
    {f : (Fin 3 → ℝ) → ℝ} (hf_pos : ∀ v, 0 < f v)
    {Cg : ℝ} {Kg : ℕ}
    (h_score : ∀ u i, |vGrad (Real.log ∘ f) u i| ≤ Cg * (1 + ‖u‖) ^ Kg)
    (v w : Fin 3 → ℝ) :
    |dotProduct (vGrad (Real.log ∘ f) v)
      (mulVec (landauMatrix coulombKernel (v - w))
        (f w • vGrad f v - f v • vGrad f w))| ≤
      3 * Cg * (1 + ‖v‖) ^ Kg * (‖v - w‖⁻¹ *
        (∑ j : Fin 3, (f w * |vGrad f v j| + f v * |vGrad f w j|))) := by
  simp only [dotProduct, mulVec]
  calc |∑ i : Fin 3, vGrad (Real.log ∘ f) v i *
          ∑ j : Fin 3, landauMatrix coulombKernel (v - w) i j *
            (f w • vGrad f v - f v • vGrad f w) j|
      ≤ ∑ i : Fin 3, |vGrad (Real.log ∘ f) v i| *
          |∑ j : Fin 3, landauMatrix coulombKernel (v - w) i j *
            (f w • vGrad f v - f v • vGrad f w) j| := by
        exact le_trans (Finset.abs_sum_le_sum_abs _ _)
          (Finset.sum_le_sum fun i _ => (abs_mul _ _).le)
    _ ≤ ∑ i : Fin 3, Cg * (1 + ‖v‖) ^ Kg *
          (‖v - w‖⁻¹ * ∑ j : Fin 3, |(f w • vGrad f v - f v • vGrad f w) j|) := by
        apply Finset.sum_le_sum; intro i _
        have h_nn : 0 ≤ Cg * (1 + ‖v‖) ^ Kg :=
          le_trans (abs_nonneg _) (h_score v i)
        apply mul_le_mul (h_score v i) _ (abs_nonneg _) h_nn
        by_cases hvw : v - w = 0
        · have : v = w := sub_eq_zero.mp hvw; subst this
          simp [dotProduct, landauMatrix, innerLandauMatrix, normSq, vecMulVec,
            eucNorm, coulombKernel]
        · calc |∑ j, landauMatrix coulombKernel (v - w) i j *
                (f w • vGrad f v - f v • vGrad f w) j|
              ≤ ∑ j, |landauMatrix coulombKernel (v - w) i j *
                (f w • vGrad f v - f v • vGrad f w) j| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ j, ‖v - w‖⁻¹ * |(f w • vGrad f v - f v • vGrad f w) j| := by
                apply Finset.sum_le_sum; intro j _
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_right
                  (coulomb_landauMatrix_entry_le_pi _ _ _ hvw) (abs_nonneg _)
            _ = ‖v - w‖⁻¹ * ∑ j, |(f w • vGrad f v - f v • vGrad f w) j| :=
                (Finset.mul_sum _ _ _).symm
    _ = 3 * (Cg * (1 + ‖v‖) ^ Kg) *
          (‖v - w‖⁻¹ * ∑ j, |(f w • vGrad f v - f v • vGrad f w) j|) := by
        simp; ring
    _ ≤ 3 * Cg * (1 + ‖v‖) ^ Kg * (‖v - w‖⁻¹ *
          ∑ j, (f w * |vGrad f v j| + f v * |vGrad f w j|)) := by
        rw [show 3 * Cg * (1 + ‖v‖) ^ Kg = 3 * (Cg * (1 + ‖v‖) ^ Kg) from by ring]
        gcongr
        · have hCg : 0 ≤ Cg := nonneg_of_mul_nonneg_left
            (le_trans (abs_nonneg _) (h_score v 0))
            (pow_pos (by linarith [norm_nonneg v]) _)
          exact mul_nonneg (by linarith)
            (mul_nonneg hCg (pow_nonneg (by linarith [norm_nonneg v]) _))
        · next j _ =>
          simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          have := norm_sub_le (f w * vGrad f v j) (f v * vGrad f w j)
          rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_mul, abs_mul, abs_of_pos (hf_pos w), abs_of_pos (hf_pos v)] at this
          exact this

/-- The Fubini double integrand (score · Landau matrix · flux) is
    AEStronglyMeasurable on the product space (Fin 3 → ℝ) × (Fin 3 → ℝ). -/
lemma fubini_double_aestronglyMeasurable
    {f : (Fin 3 → ℝ) → ℝ} (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ 3 f) :
    AEStronglyMeasurable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (vGrad (Real.log ∘ f) p.1)
        (mulVec (landauMatrix coulombKernel (p.1 - p.2))
          (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2)))
      (volume.prod volume) := by
  simp only [dotProduct, mulVec]
  apply Measurable.aestronglyMeasurable
  apply Finset.measurable_sum; intro i _
  apply Measurable.mul
  · -- score component: v ↦ fderiv ℝ (log ∘ f) v (Pi.single i 1) composed with fst
    exact ((ContDiff.continuous_fderiv
      (hf_smooth.log (fun v => ne_of_gt (hf_pos v))) (by norm_num)).clm_apply
      continuous_const).comp continuous_fst |>.measurable
  · apply Finset.measurable_sum
    intro j _
    apply Measurable.mul
    · -- landauMatrix entry: measurable via coulombKernel ∘ eucNorm and innerLandauMatrix
      simp only [landauMatrix, smul_apply, smul_eq_mul]
      apply Measurable.mul
      · apply ((Measurable.ite measurableSet_Iic measurable_const
          (measurable_id.pow measurable_const)) : Measurable coulombKernel).comp
        simp only [eucNorm, normSq, dotProduct]
        exact (continuous_sqrt.comp (continuous_finsetSum _ fun k _ =>
          ((continuous_apply k).comp (continuous_fst.sub continuous_snd)).mul
          ((continuous_apply k).comp (continuous_fst.sub continuous_snd)))).measurable
      · simp only [innerLandauMatrix_apply]
        apply Continuous.measurable
        apply Continuous.sub
        · by_cases h : i = j
          · simp only [h, ↓reduceIte, normSq, dotProduct]
            exact continuous_finsetSum _ fun k _ =>
              ((continuous_apply k).comp (continuous_fst.sub continuous_snd)).mul
              ((continuous_apply k).comp (continuous_fst.sub continuous_snd))
          · simp only [h, ↓reduceIte]
            exact continuous_const
        · exact ((continuous_apply i).comp (continuous_fst.sub continuous_snd)).mul
                ((continuous_apply j).comp (continuous_fst.sub continuous_snd))
    · -- flux component: continuous hence measurable
      exact (Continuous.sub
        ((hf_smooth.continuous.comp continuous_snd).mul
          ((hf_smooth.continuous_fderiv (by norm_num)).comp continuous_fst
            |>.clm_apply continuous_const))
        ((hf_smooth.continuous.comp continuous_fst).mul
          ((hf_smooth.continuous_fderiv (by norm_num)).comp continuous_snd
            |>.clm_apply continuous_const))
        ).measurable

end VML
end
