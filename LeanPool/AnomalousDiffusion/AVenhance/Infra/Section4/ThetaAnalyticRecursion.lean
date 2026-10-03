/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaAnalyticProof
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaHonestRecursion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaScale
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0IsLeast
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeq

/-! The normalized analytic derivative recursion for the classical theta
solution, conditional on the stream-regularity and diffusivity-recursion conclusion data. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Topology

namespace AVenhance.Infra.Section4

theorem ThetaAnalyticRecursion.theta_analytic_energyLevel_nonneg
    {θ : ℝ → Vec 2 → ℝ} {κ : ℝ} (n : ℕ) :
    0 ≤ thetaEnergyLevel θ κ n := by
  let i : Fin n → Fin 2 := fun _ => 0
  have hterm : 0 ≤ Real.sqrt (thetaWordSpatialEnergySup θ
      (thetaCoordinateWord i)) + Real.sqrt κ * Real.sqrt
        (thetaWordSpaceTimeGradientEnergy θ (thetaCoordinateWord i)) := by
    exact add_nonneg (Real.sqrt_nonneg _) <|
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact hterm.trans (thetaEnergyLevel_le_of_coordinate θ κ n i)

theorem ThetaAnalyticRecursion.theta_analytic_inductionLevel_nonneg
    {θ : ℝ → Vec 2 → ℝ} {κ : ℝ} (n : ℕ) :
    0 ≤ thetaAnalyticInductionLevel θ κ n := by
  by_cases hn : n = 0
  · simp only [thetaAnalyticInductionLevel, hn]
    exact mul_nonneg (Real.sqrt_nonneg κ) (Real.sqrt_nonneg _)
  · simp only [thetaAnalyticInductionLevel, hn, ↓reduceIte]
    exact ThetaAnalyticRecursion.theta_analytic_energyLevel_nonneg n

/-- The full space-time gradient energy is the interval energy at `T = 1`. -/
theorem theta_interval_gradient_energy_eq_full
    {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) :
    thetaIntervalWordGradientEnergy θ 1 w =
      thetaWordSpaceTimeGradientEnergy θ w := by
  let f : ℝ × Vec 2 → ℝ := fun p =>
    vecNormSq (thetaWordGradientExtension θ w p)
  have hf : Continuous f := by
    change Continuous (fun p => ∑ j : Fin 2,
      thetaWordGradientExtension θ w p j * thetaWordGradientExtension θ w p j)
    have hgrad := thetaWordGradientExtension_continuous (u := θ) (w := w) hθ
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp hgrad).mul
      ((continuous_apply j).comp hgrad)
  have hcube := theta_timeCube_integral_eq_interval_integral hf
  have htime :
      (∫ t in (0 : ℝ)..1, ∫ x in AVenhance.unitCube, f (t, x)) =
        thetaIntervalWordGradientEnergy θ 1 w := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    apply integral_congr_ae
    filter_upwards with x
    dsimp [f, thetaIntervalWordGradientEnergy]
    rw [thetaWordGradientExtension_eq_slice
      (u := θ) (w := w) t ht'.1 x]
  calc
    thetaIntervalWordGradientEnergy θ 1 w =
        ∫ t in (0 : ℝ)..1, ∫ x in AVenhance.unitCube, f (t, x) := htime.symm
    _ = ∫ p in AVenhance.timeCube, f p := hcube.symm
    _ = thetaWordSpaceTimeGradientEnergy θ w := by
      dsimp [f]
      exact (thetaWordGradientExtension_energy_eq (u := θ) (w := w)).symm

theorem ThetaAnalyticRecursion.theta_analytic_young
    {κ G H : ℝ} (hκ : 0 < κ) (hG : 0 ≤ G) :
    4 * Real.sqrt G * H ≤ κ * G + 4 * H ^ 2 / κ := by
  let Y := Real.sqrt κ * Real.sqrt G
  let Z := 2 * H / Real.sqrt κ
  have hYsq : Y ^ 2 = κ * G := by
    dsimp [Y]
    rw [mul_pow, Real.sq_sqrt hκ.le, Real.sq_sqrt hG]
  have hZsq : Z ^ 2 = 4 * H ^ 2 / κ := by
    dsimp [Z]
    rw [div_pow, Real.sq_sqrt hκ.le]
    ring
  have hYZ : 2 * Y * Z = 4 * Real.sqrt G * H := by
    dsimp [Y, Z]
    have hsqrtκ : Real.sqrt κ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hκ)
    field_simp [hsqrtκ]
    ring
  have hsq := sq_nonneg (Y - Z)
  linarith only [hsq, hYsq, hZsq, hYZ]

/-- One ordered derivative energy estimate, with the top derivative kept at
the same partial time level as the differentiated energy identity. -/
theorem ThetaAnalyticRecursion.theta_word_energy_step_of_A3
    {β κ R₀ B : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : AVenhance.IsStreamSeq I Φ)
    (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel (fun t => Φ (m - 1) t)) κ
      (fun _ _ => 0) θ₀ θ)
    (hκ : 0 < κ)
    (hTrace : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in AVenhance.unitCube,
        (classicalWordDerivative w θ₀ x) ^ 2) ≤
        B * ((w.length.factorial : ℝ) / R₀ ^ w.length))
    (w : List (Fin 2)) (hn : 1 ≤ w.length) :
    Real.sqrt (thetaWordSpatialEnergySup θ w) +
      Real.sqrt κ * Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) ≤
      2 * B * ((w.length.factorial : ℝ) / R₀ ^ w.length) +
      4 * Real.sqrt ((w.length : ℝ) *
        thetaPotentialDerivativeCoefficient (m := m) I 2 / κ) *
        thetaAnalyticInductionLevel θ κ (w.length - 1) +
      4 * (thetaAnalyticHighConvolution (m := m) I κ θ w.length) /
        Real.sqrt κ := by
  let φ : ℝ → Vec 2 → ℝ := fun t => Φ (m - 1) t
  let S₀ : ℝ := ∫ x in AVenhance.unitCube,
    (classicalWordDerivative w θ₀ x) ^ 2
  let M₂ := thetaPotentialDerivativeCoefficient (m := m) I 2
  let H := thetaAnalyticHighConvolution (m := m) I κ θ w.length
  let Q₁ := 4 * (w.length : ℝ) * M₂ *
    thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ
  let Q := S₀ + Q₁ + 4 * H ^ 2 / κ
  have hφ : AVenhance.IsAdmissibleStream φ :=
    theta_prev_stream_admissible I Φ hΦ hm
  have hS₀nonneg : 0 ≤ S₀ := by
    dsimp [S₀]
    exact integral_nonneg fun _ => sq_nonneg _
  have hM₂pos : 0 < M₂ := by
    have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
      AVenhance.Infra.Cutoff.epsilon_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have ha : 0 < AVenhance.a β I.Λ (m - 1) := by
      rw [AVenhance.a]
      exact Real.rpow_pos_of_pos he _
    dsimp [M₂, thetaPotentialDerivativeCoefficient]
    positivity
  have hEnonneg (k : ℕ) : 0 ≤ thetaAnalyticInductionLevel θ κ k :=
    ThetaAnalyticRecursion.theta_analytic_inductionLevel_nonneg k
  have hHnonneg : 0 ≤ H := by
    dsimp [H, thetaAnalyticHighConvolution]
    apply Finset.sum_nonneg
    intro q hq
    by_cases hq2 : 2 ≤ q
    · have hcoef : 0 ≤ (w.length.choose q : ℝ) := by positivity
      have hM : 0 ≤ thetaPotentialDerivativeCoefficient (m := m) I q := by
        have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
          AVenhance.Infra.Cutoff.epsilon_pos
            I.one_lt_beta I.beta_lt I.two_pow_seven_le
        unfold thetaPotentialDerivativeCoefficient
        rw [AVenhance.a]
        positivity
      have hE := hEnonneg (w.length - q)
      positivity
    · simp [hq2]
  have henergyT (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
      thetaWordSpatialEnergy θ w T + κ *
        thetaIntervalWordGradientEnergy θ T w ≤ Q := by
    let P : ℝ := ∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
      vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
        (thetaStreamCommutatorFlux w ((fun s => Φ (m - 1) s) t) (θ t) x)
    have hid := (theta_classical_differentiated_energy_integrated hφ hsol
      hT.1 w).2
    have hflux := theta_flux_pairing_split_abs_le_of_A3
      I Φ hΦ hm hA3 hsol hκ hT w
    have hPbound : |P| ≤
        2 * w.length * M₂ *
            thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ +
          2 * Real.sqrt (thetaIntervalWordGradientEnergy θ T w) * H := by
      simpa [P, H, M₂, φ] using hflux
    have hPcost : -2 * P ≤ Q₁ +
        4 * Real.sqrt (thetaIntervalWordGradientEnergy θ T w) * H := by
      calc
        -2 * P ≤ 2 * |P| := by linarith only [neg_le_abs P]
        _ ≤ 2 * (2 * w.length * M₂ *
            thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ +
          2 * Real.sqrt (thetaIntervalWordGradientEnergy θ T w) * H) :=
            mul_le_mul_of_nonneg_left hPbound (by norm_num)
        _ = _ := by dsimp [Q₁]; ring
    have hGnonneg : 0 ≤ thetaIntervalWordGradientEnergy θ T w := by
      dsimp [thetaIntervalWordGradientEnergy]
      apply intervalIntegral.integral_nonneg hT.1
      intro t ht
      exact integral_nonneg fun _ => vecNormSq_nonneg _
    have hYoung := ThetaAnalyticRecursion.theta_analytic_young (H := H) hκ hGnonneg
    have hidentity : thetaWordSpatialEnergy θ w T +
        2 * κ * thetaIntervalWordGradientEnergy θ T w = S₀ - 2 * P := by
      simpa [thetaWordSpatialEnergy, thetaIntervalWordGradientEnergy,
        S₀, P, classicalWordDerivative,
        Classical.classicalWordDerivative] using hid
    dsimp [Q]
    linarith [hidentity, hPcost, hYoung]
  have hSsup : thetaWordSpatialEnergySup θ w ≤ Q := by
    apply thetaWordSpatialEnergySup_le
    intro T hT
    have h := henergyT T hT
    have hGnonneg : 0 ≤ thetaIntervalWordGradientEnergy θ T w := by
      dsimp [thetaIntervalWordGradientEnergy]
      apply intervalIntegral.integral_nonneg hT.1
      intro t ht
      exact integral_nonneg fun _ => vecNormSq_nonneg _
    linarith only [h, mul_nonneg hκ.le hGnonneg]
  have hGfull : κ * thetaWordSpaceTimeGradientEnergy θ w ≤ Q := by
    have h := henergyT 1 (by norm_num)
    rw [theta_interval_gradient_energy_eq_full hsol.1 w] at h
    have hS : 0 ≤ thetaWordSpatialEnergy θ w 1 := by
      exact integral_nonneg fun _ => sq_nonneg _
    linarith
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hSroot : Real.sqrt (thetaWordSpatialEnergySup θ w) ≤ Real.sqrt Q :=
    Real.sqrt_le_sqrt hSsup
  have hGroot : Real.sqrt κ *
      Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) ≤ Real.sqrt Q := by
    calc
      Real.sqrt κ * Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) =
          Real.sqrt (κ * thetaWordSpaceTimeGradientEnergy θ w) := by
            rw [← Real.sqrt_mul hκ.le]
      _ ≤ Real.sqrt Q := Real.sqrt_le_sqrt hGfull
  have hS₀root : Real.sqrt S₀ ≤
      B * ((w.length.factorial : ℝ) / R₀ ^ w.length) := by
    simpa [S₀] using hTrace w hn
  have hQ₁nonneg : 0 ≤ Q₁ := by
    dsimp [Q₁]
    positivity
  have hQ₁root : Real.sqrt Q₁ =
      2 * Real.sqrt ((w.length : ℝ) * M₂ / κ) *
        thetaAnalyticInductionLevel θ κ (w.length - 1) := by
    let X := (w.length : ℝ) * M₂ / κ
    let E := thetaAnalyticInductionLevel θ κ (w.length - 1)
    have hX : 0 ≤ X := by dsimp [X]; positivity
    have hXsqrt : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX
    have hRhsSq : (2 * Real.sqrt X * E) ^ 2 = 4 * X * E ^ 2 := by
      rw [mul_pow, mul_pow, hXsqrt]
      ring
    have hQeq : Q₁ = (2 * Real.sqrt X * E) ^ 2 := by
      calc
        Q₁ = 4 * X * E ^ 2 := by dsimp [Q₁, X, E]; ring
        _ = (2 * Real.sqrt X * E) ^ 2 := hRhsSq.symm
    calc
      Real.sqrt Q₁ = Real.sqrt ((2 * Real.sqrt X * E) ^ 2) :=
        congrArg Real.sqrt hQeq
      _ = |2 * Real.sqrt X * E| := Real.sqrt_sq_eq_abs _
      _ = 2 * Real.sqrt X * E := abs_of_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg X)) (hEnonneg _))
  have hHsq : (2 * H / Real.sqrt κ) ^ 2 = 4 * H ^ 2 / κ := by
    calc
      (2 * H / Real.sqrt κ) ^ 2 = (2 * H) ^ 2 / (Real.sqrt κ) ^ 2 := by
        rw [div_pow]
      _ = 4 * H ^ 2 / κ := by rw [Real.sq_sqrt hκ.le]; ring
  have hHroot : Real.sqrt (4 * H ^ 2 / κ) ≤ 2 * H / Real.sqrt κ := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, hHsq.symm.le⟩
  have hsumSq : S₀ + Q₁ + 4 * H ^ 2 / κ ≤
      (Real.sqrt S₀ + Real.sqrt Q₁ + 2 * H / Real.sqrt κ) ^ 2 := by
    have hs₀ : (Real.sqrt S₀) ^ 2 = S₀ := Real.sq_sqrt hS₀nonneg
    have hs₁ : (Real.sqrt Q₁) ^ 2 = Q₁ := Real.sq_sqrt hQ₁nonneg
    have hcross₀₁ : 0 ≤ 2 * Real.sqrt S₀ * Real.sqrt Q₁ := by positivity
    have hcross₀₂ : 0 ≤ 2 * Real.sqrt S₀ * (2 * H / Real.sqrt κ) := by
      positivity
    have hcross₁₂ : 0 ≤ 2 * Real.sqrt Q₁ * (2 * H / Real.sqrt κ) := by
      positivity
    linarith only [hs₀, hs₁, hHsq, hcross₀₁, hcross₀₂, hcross₁₂]
  have hrootQ : Real.sqrt Q ≤
      Real.sqrt S₀ + Real.sqrt Q₁ + 2 * H / Real.sqrt κ := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by simpa [Q] using hsumSq⟩
  have hlevel :
      Real.sqrt (thetaWordSpatialEnergySup θ w) +
          Real.sqrt κ * Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) ≤
        2 * Real.sqrt Q := by
    linarith [hSroot, hGroot]
  have hlevel' :
      Real.sqrt (thetaWordSpatialEnergySup θ w) +
          Real.sqrt κ * Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) ≤
        2 * (B * ((w.length.factorial : ℝ) / R₀ ^ w.length) +
          2 * Real.sqrt ((w.length : ℝ) * M₂ / κ) *
            thetaAnalyticInductionLevel θ κ (w.length - 1) + 2 * H / Real.sqrt κ) := by
    calc
      _ ≤ 2 * (Real.sqrt S₀ + Real.sqrt Q₁ + 2 * H / Real.sqrt κ) := by
        exact hlevel.trans
          (mul_le_mul_of_nonneg_left hrootQ (by norm_num))
      _ ≤ 2 * (B * ((w.length.factorial : ℝ) / R₀ ^ w.length) +
          2 * Real.sqrt ((w.length : ℝ) * M₂ / κ) *
            thetaAnalyticInductionLevel θ κ (w.length - 1) + 2 * H / Real.sqrt κ) := by
        rw [hQ₁root]
        gcongr
  calc
    _ ≤ 2 * (B * ((w.length.factorial : ℝ) / R₀ ^ w.length) +
          2 * Real.sqrt ((w.length : ℝ) * M₂ / κ) *
            thetaAnalyticInductionLevel θ κ (w.length - 1) + 2 * H / Real.sqrt κ) := hlevel'
    _ = 2 * B * ((w.length.factorial : ℝ) / R₀ ^ w.length) +
          4 * Real.sqrt ((w.length : ℝ) * M₂ / κ) *
            thetaAnalyticInductionLevel θ κ (w.length - 1) + 4 * H / Real.sqrt κ := by ring

/-- Lift the ordered-word energy identity to the maximum derivative level.
The zero-level value is not used here: every order in this recursion is
positive, and all lower levels use the gradient-only convention. -/
theorem theta_analytic_level_recursion_of_A3
    {β κ R₀ B : ℝ} {m n : ℕ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : AVenhance.IsStreamSeq I Φ)
    (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel (fun t => Φ (m - 1) t)) κ
      (fun _ _ => 0) θ₀ θ)
    (hκ : 0 < κ)
    (hTrace : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in AVenhance.unitCube,
        (classicalWordDerivative w θ₀ x) ^ 2) ≤
        B * ((w.length.factorial : ℝ) / R₀ ^ w.length))
    (hn : 1 ≤ n) :
    thetaAnalyticInductionLevel θ κ n ≤
      2 * B * ((n.factorial : ℝ) / R₀ ^ n) +
        4 * Real.sqrt ((n : ℝ) *
          thetaPotentialDerivativeCoefficient (m := m) I 2 / κ) *
          thetaAnalyticInductionLevel θ κ (n - 1) +
        4 * (∑ q ∈ Finset.range (n + 1),
          if 2 ≤ q then
            ((n.choose q : ℕ) : ℝ) *
              (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
              thetaAnalyticInductionLevel θ κ (n - q)
          else 0) := by
  have hlevel : thetaEnergyLevel θ κ n ≤
      2 * B * ((n.factorial : ℝ) / R₀ ^ n) +
        4 * Real.sqrt ((n : ℝ) *
          thetaPotentialDerivativeCoefficient (m := m) I 2 / κ) *
          thetaAnalyticInductionLevel θ κ (n - 1) +
        4 * (∑ q ∈ Finset.range (n + 1),
          if 2 ≤ q then
            ((n.choose q : ℕ) : ℝ) *
              (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
              thetaAnalyticInductionLevel θ κ (n - q)
          else 0) := by
    unfold thetaEnergyLevel
    apply Finset.sup'_le
    intro i hi
    let w := thetaCoordinateWord i
    have hlen : w.length = n := by simp [w]
    have hnw : 1 ≤ w.length := by omega
    have hword := ThetaAnalyticRecursion.theta_word_energy_step_of_A3 I Φ hΦ hm hA3 hsol hκ
      hTrace w hnw
    have hconv :
        4 * thetaAnalyticHighConvolution (m := m) I κ θ n / Real.sqrt κ =
          4 * (∑ q ∈ Finset.range (n + 1),
            if 2 ≤ q then
              ((n.choose q : ℕ) : ℝ) *
                (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
                thetaAnalyticInductionLevel θ κ (n - q)
            else 0) := by
      let s := Real.sqrt κ
      have hs : s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hκ)
      dsimp [thetaAnalyticHighConvolution, s]
      rw [Finset.mul_sum, Finset.sum_div]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hq2 : 2 ≤ q
      · simp [hq2]
        field_simp [hs]
        rw [Real.sq_sqrt hκ.le]
      · simp [hq2]
    have hword' :
        Real.sqrt (thetaWordSpatialEnergySup θ w) +
            Real.sqrt κ * Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) ≤
          2 * B * ((n.factorial : ℝ) / R₀ ^ n) +
            4 * Real.sqrt ((n : ℝ) *
              thetaPotentialDerivativeCoefficient (m := m) I 2 / κ) *
              thetaAnalyticInductionLevel θ κ (n - 1) +
            4 * (∑ q ∈ Finset.range (n + 1),
              if 2 ≤ q then
                ((n.choose q : ℕ) : ℝ) *
                  (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
                  thetaAnalyticInductionLevel θ κ (n - q)
              else 0) := by
      simpa [w, hlen, hconv, mul_div_assoc] using hword
    exact hword'
  have hn0 : n ≠ 0 := by omega
  simpa [thetaAnalyticInductionLevel, hn0] using hlevel

end AVenhance.Infra.Section4

end
