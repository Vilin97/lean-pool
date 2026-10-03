/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaAnalyticBound

/-! Analytic estimates under the stream-regularity and diffusivity-recursion estimates, with an
    explicit initial derivative trace. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Topology

namespace AVenhance.Infra.Section4

theorem ThetaAnalyticTrace.theta_initial_trace_l2_sq_le
    {B R : ℝ} {θ₀ : Vec 2 → ℝ}
    (hB : 0 ≤ B)
    (hTrace : ∀ w : List (Fin 2),
      Real.sqrt (∫ x in AVenhance.unitCube,
        (classicalWordDerivative w θ₀ x) ^ 2) ≤
      B * ((w.length.factorial : ℝ) / R ^ w.length)) :
    AVenhance.l2NormSq θ₀ ≤ B ^ 2 := by
  have hzero := hTrace []
  have hnorm : Real.sqrt (AVenhance.l2NormSq θ₀) ≤ B := by
    simpa [AVenhance.l2NormSq, classicalWordDerivative,
      Classical.classicalWordDerivative] using hzero
  have hSnonneg : 0 ≤ AVenhance.l2NormSq θ₀ := by
    unfold AVenhance.l2NormSq
    exact integral_nonneg fun _ => sq_nonneg _
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) hB).mpr hnorm
  rw [Real.sq_sqrt hSnonneg] at hsq
  exact hsq

/-- The homogeneous differentiated energy identity bounds the order-zero
space-time gradient using only the initial L² trace. This is the base datum
used by the coordinate profile; no time-uniform scalar norm enters. -/
theorem theta_homogeneous_gradient_energy_le_of_initial_l2_sq
    {κ B : ℝ} {φ : ℝ → Vec 2 → ℝ}
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ)
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel φ) κ (fun _ _ => 0) θ₀ θ)
    (hInitial : AVenhance.l2NormSq θ₀ ≤ B ^ 2) :
    κ * AVenhance.spaceTimeGradNormSq
      (fun t => AVenhance.spaceGrad (θ t)) ≤ B ^ 2 := by
  let w : List (Fin 2) := []
  have htime :
      (∫ t in (0 : ℝ)..1,
        ∫ x in AVenhance.unitCube,
          vecNormSq (AVenhance.spaceGrad
            (classicalWordDerivative w (θ t)) x)) =
        thetaWordSpaceTimeGradientEnergy θ w := by
    simpa [thetaIntervalWordGradientEnergy] using
      (theta_interval_gradient_energy_eq_full hsol.1 w)
  have henergy := (theta_classical_differentiated_energy_integrated
    hφ hsol (by norm_num : 0 ≤ (1 : ℝ)) w).1
  rw [htime] at henergy
  have hidentity :
      thetaWordSpatialEnergy θ w 1 +
          2 * κ * thetaWordSpaceTimeGradientEnergy θ w =
        AVenhance.l2NormSq θ₀ := by
    simpa [w, thetaWordSpatialEnergy, AVenhance.l2NormSq,
      classicalWordDerivative,
      Classical.classicalWordDerivative, classicalTransport,
      Classical.classicalTransport] using henergy
  have hSnonneg : 0 ≤ thetaWordSpatialEnergy θ w 1 := by
    exact integral_nonneg fun _ => sq_nonneg _
  have hGbound : κ * thetaWordSpaceTimeGradientEnergy θ w ≤ B ^ 2 := by
    nlinarith only [hidentity, hSnonneg, hInitial]
  have hG : thetaWordSpaceTimeGradientEnergy θ w =
      AVenhance.spaceTimeGradNormSq (fun t => AVenhance.spaceGrad (θ t)) := by
    simp [w, thetaWordSpaceTimeGradientEnergy,
      AVenhance.spaceTimeGradNormSq, classicalWordDerivative,
      Classical.classicalWordDerivative]
  rw [← hG]
  exact hGbound

theorem ThetaAnalyticTrace.theta_gradient_only_order_zero_bound_of_initial_l2_sq
    {κ B : ℝ} {φ : ℝ → Vec 2 → ℝ}
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ)
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel φ) κ (fun _ _ => 0) θ₀ θ)
    (hκ : 0 < κ) (hB : 0 ≤ B)
    (hInitial : AVenhance.l2NormSq θ₀ ≤ B ^ 2) :
    thetaAnalyticInductionLevel θ κ 0 ≤ B := by
  have hG := theta_homogeneous_gradient_energy_le_of_initial_l2_sq
    hφ hsol hInitial
  have hroot : Real.sqrt κ * Real.sqrt
      (thetaWordSpaceTimeGradientEnergy θ []) ≤ B := by
    rw [← Real.sqrt_mul hκ.le]
    exact (Real.sqrt_le_iff).2 ⟨hB, by
      simpa [AVenhance.spaceTimeGradNormSq,
        thetaWordSpaceTimeGradientEnergy, classicalWordDerivative,
        Classical.classicalWordDerivative] using hG⟩
  simpa [thetaAnalyticInductionLevel] using hroot

theorem ThetaAnalyticTrace.theta_gradient_only_order_zero_bound_of_gradient_energy
    {κ B : ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hκ : 0 < κ) (hB : 0 ≤ B)
    (hzero : κ * thetaWordSpaceTimeGradientEnergy θ [] ≤ B ^ 2) :
    thetaAnalyticInductionLevel θ κ 0 ≤ B := by
  have hroot : Real.sqrt κ * Real.sqrt
      (thetaWordSpaceTimeGradientEnergy θ []) ≤ B := by
    rw [← Real.sqrt_mul hκ.le]
    exact (Real.sqrt_le_iff).2 ⟨hB, hzero⟩
  simpa [thetaAnalyticInductionLevel] using hroot

/-- Positive-order analytic energy bounds from the initial trace and a
gradient-only order-zero datum. The trace is required only at positive order;
the zeroth level is supplied separately by `hzero`. -/
theorem theta_analytic_positive_energy_bound_of_initial_trace_A3_A5
    {β : ℝ} {M m : ℕ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : AVenhance.IsStreamSeq I Φ)
    (hm : 2 ≤ m) (hmM : m ≤ M) {κ : ℝ}
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    {c C B R : ℝ} (hc : 0 < c) (_hC : c < C)
    (hB : 0 < B) (hR : 0 < R)
    (hzero : AVenhance.Ingredients.kappaSeq I κ M (m - 1) *
      AVenhance.spaceTimeGradNormSq (fun t => AVenhance.spaceGrad (θ t)) ≤ B ^ 2)
    (hTrace : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in AVenhance.unitCube,
        (classicalWordDerivative w θ₀ x) ^ 2) ≤
      B * ((w.length.factorial : ℝ) / R ^ w.length))
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (hA5 : ∀ j : ℕ, 1 ≤ j → j < M →
      c * (AVenhance.a β I.Λ j * AVenhance.epsilon β I.Λ j ^
        (2 + AVenhance.gamma β)) ≤ I.kappaAt κ j (M - j) ∧
      I.kappaAt κ j (M - j) ≤
        C * (AVenhance.a β I.Λ j * AVenhance.epsilon β I.Λ j ^
          (2 + AVenhance.gamma β)))
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel (fun t => Φ (m - 1) t))
      (AVenhance.Ingredients.kappaSeq I κ M (m - 1))
      (fun _ _ => 0) θ₀ θ) :
    ∀ n : ℕ, 1 ≤ n →
      thetaEnergyLevel θ (AVenhance.Ingredients.kappaSeq I κ M (m - 1)) n ≤
        2 * B * (n.factorial : ℝ) *
          thetaAnalyticRadius c (AVenhance.epsilon β I.Λ (m - 1))
            (AVenhance.gamma β) R ^ n := by
  let φ : ℝ → Vec 2 → ℝ := fun t => Φ (m - 1) t
  let κm : ℝ := AVenhance.Ingredients.kappaSeq I κ M (m - 1)
  let e : ℝ := AVenhance.epsilon β I.Λ (m - 1)
  let γ : ℝ := AVenhance.gamma β
  let L : ℝ := thetaAnalyticRadius c e γ R
  have hmpos : 1 ≤ m - 1 := by omega
  have hindex : m - 1 < M := by omega
  have hA5lower := hA5 (m - 1) hmpos hindex
  have hκlower : c * (AVenhance.a β I.Λ (m - 1) *
      AVenhance.epsilon β I.Λ (m - 1) ^ (2 + AVenhance.gamma β)) ≤ κm := by
    simpa [κm, AVenhance.Ingredients.kappaSeq] using hA5lower.1
  have hscales := theta_analytic_radius_scales_of_A5
    (I := I) (R₀ := R) (m := m) hc hκlower
  have hκpos : 0 < κm := by simpa [κm] using hscales.1
  have hLpos : 0 < L := by simpa [L, e, γ] using hscales.2.1
  have hLinitial : 2 / R ≤ L := by simpa [L, e, γ] using hscales.2.2.1
  have hQ1scale := hscales.2.2.2.1
  have hHighscale := hscales.2.2.2.2
  have hφ : AVenhance.IsAdmissibleStream φ :=
    theta_prev_stream_admissible I Φ hΦ hm
  have hzero' : κm * thetaWordSpaceTimeGradientEnergy θ [] ≤ B ^ 2 := by
    simpa [κm, AVenhance.spaceTimeGradNormSq,
      thetaWordSpaceTimeGradientEnergy, classicalWordDerivative,
      Classical.classicalWordDerivative] using hzero
  have hbase : thetaAnalyticInductionLevel θ κm 0 ≤ B := by
    simpa [κm] using
      ThetaAnalyticTrace.theta_gradient_only_order_zero_bound_of_gradient_energy
        hκpos hB.le hzero'
  have hMnonneg : ∀ q : ℕ,
      0 ≤ thetaPotentialDerivativeCoefficient (m := m) I q := by
    intro q
    have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
      AVenhance.Infra.Cutoff.epsilon_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le
    unfold thetaPotentialDerivativeCoefficient
    rw [AVenhance.a]
    positivity
  let E : ℕ → ℝ := fun n => thetaAnalyticInductionLevel θ κm n
  let Q : ℕ → ℝ := fun q => thetaPotentialDerivativeCoefficient (m := m) I q
  have hrec : ∀ n : ℕ, 1 ≤ n →
      E n ≤ 2 * B * ((n.factorial : ℝ) / R ^ n) +
        4 * Real.sqrt ((n : ℝ) * Q 2 / κm) * E (n - 1) +
        4 * (∑ q ∈ Finset.range (n + 1),
          if 2 ≤ q then
            ((n.choose q : ℕ) : ℝ) * (Q q / κm) * E (n - q)
          else 0) := by
    intro n hn
    have h := theta_analytic_level_recursion_of_A3
      I Φ hΦ hm hA3 hsol hκpos hTrace hn
    simpa [E, Q, κm] using h
  have hEbound := theta_analytic_bound_of_energy_recursion
    (E := E) (M := Q) (B := B) (R := R) (L := L) (κ := κm)
    hB hR hLpos hκpos hbase hMnonneg hLinitial
    (by simpa [E, Q, L, e, γ, κm] using hQ1scale)
    (by simpa [E, Q, L, e, γ, κm] using hHighscale)
    hrec
  intro n hn
  have hpos := hEbound n
  have hn0 : n ≠ 0 := by omega
  have hlevel : thetaEnergyLevel θ κm n ≤
      2 * B * (n.factorial : ℝ) * L ^ n := by
    simpa [E, thetaAnalyticInductionLevel, hn0, div_eq_mul_inv] using hpos
  simpa [L, e, γ, κm] using hlevel

end AVenhance.Infra.Section4

end
