/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaAnalyticScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaHonestRecursion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaZeroBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaClassicalUniqueness
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeq

/-! Full analytic theta estimate under the conditional stream-regularity and diffusivity-recursion
conclusion data. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Topology

namespace AVenhance.Infra.Section4

theorem ThetaAnalyticBound.theta_gradient_only_order_zero_bound
    {κ N : ℝ} {φ : ℝ → Vec 2 → ℝ}
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ)
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel φ) κ (fun _ _ => 0) θ₀ θ)
    (hκ : 0 < κ) (hN : N = Real.sqrt (AVenhance.l2NormSq θ₀)) :
    thetaAnalyticInductionLevel θ κ 0 ≤ N := by
  let w : List (Fin 2) := []
  let S₀ : ℝ := AVenhance.l2NormSq θ₀
  have hS₀nonneg : 0 ≤ S₀ := by
    dsimp [S₀, AVenhance.l2NormSq]
    exact integral_nonneg fun _ => sq_nonneg _
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
          2 * κ * thetaWordSpaceTimeGradientEnergy θ w = S₀ := by
    simpa [w, S₀, thetaWordSpatialEnergy, AVenhance.l2NormSq,
      classicalWordDerivative,
      Classical.classicalWordDerivative, classicalTransport,
      Classical.classicalTransport] using henergy
  have hSnonneg : 0 ≤ thetaWordSpatialEnergy θ w 1 := by
    exact integral_nonneg fun _ => sq_nonneg _
  have hNnonneg : 0 ≤ N := by
    rw [hN]
    exact Real.sqrt_nonneg _
  have hNsq : N ^ 2 = S₀ := by
    rw [hN]
    exact Real.sq_sqrt hS₀nonneg
  have hGbound : κ * thetaWordSpaceTimeGradientEnergy θ w ≤ N ^ 2 := by
    rw [hNsq]
    nlinarith [hidentity, hSnonneg]
  have hroot :
      Real.sqrt κ * Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) ≤ N := by
    rw [← Real.sqrt_mul hκ.le]
    exact (Real.sqrt_le_iff).2 ⟨hNnonneg, hGbound⟩
  simpa [thetaAnalyticInductionLevel, w] using hroot

/-- The §4 analytic estimate for every ordered derivative energy level.
The zero-order induction datum is only the dissipative gradient term; the
full zero-order estimate is supplied separately by the energy identity. -/
theorem theta_analytic_energy_bound_of_A3_A5
    {β : ℝ} {M m : ℕ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : AVenhance.IsStreamSeq I Φ)
    (hm : 2 ≤ m) (hmM : m ≤ M) {κ : ℝ}
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    {c C R : ℝ} (hR : 0 < R)
    (hθ₀ : AVenhance.IsThetaAnalytic R θ₀)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (hA5 : 0 < c ∧ c < C ∧
      ∀ j : ℕ, 1 ≤ j → j < M →
        c * (AVenhance.a β I.Λ j * AVenhance.epsilon β I.Λ j ^
          (2 + AVenhance.gamma β)) ≤ I.kappaAt κ j (M - j) ∧
        I.kappaAt κ j (M - j) ≤
          C * (AVenhance.a β I.Λ j * AVenhance.epsilon β I.Λ j ^
            (2 + AVenhance.gamma β)))
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel (fun t => Φ (m - 1) t))
      (AVenhance.Ingredients.kappaSeq I κ M (m - 1))
      (fun _ _ => 0) θ₀ θ) :
    ∀ n : ℕ,
      thetaEnergyLevel θ (AVenhance.Ingredients.kappaSeq I κ M (m - 1)) n ≤
        2 * Real.sqrt (AVenhance.l2NormSq θ₀) * (n.factorial : ℝ) *
          thetaAnalyticRadius c
            (AVenhance.epsilon β I.Λ (m - 1))
            (AVenhance.gamma β) R ^ n := by
  let φ : ℝ → Vec 2 → ℝ := fun t => Φ (m - 1) t
  let κm : ℝ := AVenhance.Ingredients.kappaSeq I κ M (m - 1)
  let N : ℝ := Real.sqrt (AVenhance.l2NormSq θ₀)
  let e : ℝ := AVenhance.epsilon β I.Λ (m - 1)
  let γ : ℝ := AVenhance.gamma β
  let L : ℝ := thetaAnalyticRadius c e γ R
  have hmpos : 1 ≤ m - 1 := by omega
  have hindex : m - 1 < M := by omega
  have hA5lower := hA5.2.2 (m - 1) hmpos hindex
  have hκlower : c * (AVenhance.a β I.Λ (m - 1) *
      AVenhance.epsilon β I.Λ (m - 1) ^ (2 + AVenhance.gamma β)) ≤ κm := by
    simpa [κm, AVenhance.Ingredients.kappaSeq] using hA5lower.1
  have hscales := theta_analytic_radius_scales_of_A5
    (I := I) (R₀ := R) (m := m) hA5.1 hκlower
  have hκpos : 0 < κm := by simpa [κm] using hscales.1
  have hLpos : 0 < L := by simpa [L, e, γ] using hscales.2.1
  have hLinitial : 2 / R ≤ L := by simpa [L, e, γ] using hscales.2.2.1
  have hQ1scale := hscales.2.2.2.1
  have hHighscale := hscales.2.2.2.2
  have hφ : AVenhance.IsAdmissibleStream φ :=
    theta_prev_stream_admissible I Φ hΦ hm
  have hTrace : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in AVenhance.unitCube,
        (classicalWordDerivative w θ₀ x) ^ 2) ≤
        N * ((w.length.factorial : ℝ) / R ^ w.length) := by
    intro w hn
    simpa [N] using theta_initial_word_l2_le_of_analytic hθ₀ hsol w
  by_cases hNzero : N = 0
  · have hSzero : AVenhance.l2NormSq θ₀ = 0 := by
      have hsq : (Real.sqrt (AVenhance.l2NormSq θ₀)) ^ 2 = 0 := by
        simp [N, hNzero]
      have hSnonneg : 0 ≤ AVenhance.l2NormSq θ₀ := by
        unfold AVenhance.l2NormSq
        exact integral_nonneg fun _ => sq_nonneg _
      rw [Real.sq_sqrt hSnonneg] at hsq
      exact hsq
    have hθ₀smooth : ContDiff ℝ (⊤ : ℕ∞) θ₀ := by
      have hsmooth := classicalSmooth_slice_nonneg hsol.1 (t := 0) le_rfl
      have hinit : θ 0 = θ₀ := funext hsol.2.2.1
      rw [← hinit]
      exact hsmooth
    have hperiodic : AVenhance.IsZ2Periodic θ₀ := by
      have hper := hsol.2.1 0 le_rfl
      have hinit : θ 0 = θ₀ := funext hsol.2.2.1
      rw [← hinit]
      exact hper
    have hθ₀zero :
        θ₀ = (fun _ : Vec 2 => 0) :=
      theta_continuous_periodic_eq_zero_of_l2NormSq_eq_zero
        hθ₀smooth hperiodic hSzero
    have hsolzero : AVenhance.IsClassicalSol
        (AVenhance.streamVel φ) κm (fun _ _ => 0)
        (fun _ : Vec 2 => 0) θ := by
      simpa [φ, κm, hθ₀zero] using hsol
    intro n
    have hlevelzero := theta_zero_energy_level_eq_zero n hφ hκpos hsolzero
    simpa [N, hNzero, L, κm] using (le_of_eq hlevelzero)
  · have hNpos : 0 < N := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hNzero)
    have hbase : thetaAnalyticInductionLevel θ κm 0 ≤ N := by
      simpa [φ, κm, N] using
        ThetaAnalyticBound.theta_gradient_only_order_zero_bound hφ hsol hκpos rfl
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
        E n ≤ 2 * N * ((n.factorial : ℝ) / R ^ n) +
          4 * Real.sqrt ((n : ℝ) * Q 2 / κm) * E (n - 1) +
          4 * (∑ q ∈ Finset.range (n + 1),
            if 2 ≤ q then
              ((n.choose q : ℕ) : ℝ) * (Q q / κm) * E (n - q)
            else 0) := by
      intro n hn
      have h := theta_analytic_level_recursion_of_A3
        I Φ hΦ hm hA3 hsol hκpos hTrace hn
      simpa [E, Q, N, κm] using h
    have hEbound := theta_analytic_bound_of_energy_recursion
      (E := E) (M := Q) (B := N) (R := R) (L := L) (κ := κm)
      hNpos hR hLpos hκpos hbase hMnonneg hLinitial
      (by simpa [E, Q, L, e, γ, κm] using hQ1scale)
      (by simpa [E, Q, L, e, γ, κm] using hHighscale)
      hrec
    intro n
    by_cases hn0 : n = 0
    · subst n
      have hzero := theta_order_zero_energy_bound hφ hsol hκpos
        (N := N) rfl
      simpa [N, L, κm] using hzero
    · have hpos := hEbound n
      have hlevel : thetaEnergyLevel θ κm n ≤ 2 * N *
          (n.factorial : ℝ) * L ^ n := by
        simpa [E, thetaAnalyticInductionLevel, hn0] using hpos
      simpa [N, L, κm] using hlevel

end AVenhance.Infra.Section4

end
