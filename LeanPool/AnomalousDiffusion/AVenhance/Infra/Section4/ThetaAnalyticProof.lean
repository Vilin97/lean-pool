/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaAnalyticEstimate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaZeroBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0IsLeast
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeq

/-! The q=1 integration-by-parts contribution and the higher-order energy
convolution, assembled into the normalized analytic estimate. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Topology

namespace AVenhance.Infra.Section4

theorem ThetaAnalyticProof.theta_proof_energyLevel_nonneg
    {θ : ℝ → Vec 2 → ℝ} {κ : ℝ} (n : ℕ) :
    0 ≤ thetaEnergyLevel θ κ n := by
  let i : Fin n → Fin 2 := fun _ => 0
  have hterm : 0 ≤ Real.sqrt (thetaWordSpatialEnergySup θ
      (thetaCoordinateWord i)) + Real.sqrt κ * Real.sqrt
        (thetaWordSpaceTimeGradientEnergy θ (thetaCoordinateWord i)) := by
    exact add_nonneg (Real.sqrt_nonneg _) <|
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact hterm.trans (thetaEnergyLevel_le_of_coordinate θ κ n i)

/-- Recursion level with a gradient-only order-zero base. Positive orders
use the full spatial-supremum plus integrated-gradient energy level. -/
noncomputable def thetaAnalyticInductionLevel
    (θ : ℝ → Vec 2 → ℝ) (κ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then
    Real.sqrt κ * Real.sqrt (thetaWordSpaceTimeGradientEnergy θ [])
  else thetaEnergyLevel θ κ n

theorem ThetaAnalyticProof.theta_proof_sqrt_gradient_le_level
    {θ : ℝ → Vec 2 → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (w : List (Fin 2)) :
    Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) ≤
      thetaAnalyticInductionLevel θ κ w.length / Real.sqrt κ := by
  by_cases hw : w.length = 0
  · have hword : w = [] := List.length_eq_zero_iff.mp hw
    subst w
    simp only [thetaAnalyticInductionLevel]
    change Real.sqrt (thetaWordSpaceTimeGradientEnergy θ []) ≤
      (Real.sqrt κ * Real.sqrt (thetaWordSpaceTimeGradientEnergy θ [])) /
        Real.sqrt κ
    rw [le_div_iff₀ (Real.sqrt_pos.2 hκ)]
    nlinarith [Real.sqrt_nonneg (thetaWordSpaceTimeGradientEnergy θ [])]
  · have hwpos : 1 ≤ w.length := by omega
    have hword : thetaCoordinateWord (fun j : Fin w.length => w.get j) = w :=
      List.ofFn_get w
    have hlevel := thetaEnergyLevel_le_of_coordinate θ κ w.length
      (fun j : Fin w.length => w.get j)
    rw [hword] at hlevel
    have hgrad : Real.sqrt κ *
        Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) ≤
          thetaEnergyLevel θ κ w.length := by
      have hsp := Real.sqrt_nonneg (thetaWordSpatialEnergySup θ w)
      linarith
    apply (le_div_iff₀ (Real.sqrt_pos.2 hκ)).2
    simpa [thetaAnalyticInductionLevel, hw, mul_comm] using hgrad

theorem ThetaAnalyticProof.theta_proof_abs_list_sum_le (L : List ℝ) :
    |L.sum| ≤ (L.map fun x => |x|).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.sum_cons, List.map_cons]
    calc
      |x + L.sum| ≤ |x| + |L.sum| := abs_add_le _ _
      _ ≤ |x| + (L.map fun x => |x|).sum := by nlinarith [ih]

/-- Higher-order convolution of potential derivative bounds and analytic induction levels. -/
noncomputable def thetaAnalyticHighConvolution
    {β : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
    (κ : ℝ) (θ : ℝ → Vec 2 → ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (n + 1),
    if 2 ≤ q then
      ((n.choose q : ℕ) : ℝ) *
        (thetaPotentialDerivativeCoefficient (m := m) I q *
          thetaAnalyticInductionLevel θ κ (n - q) / Real.sqrt κ)
    else 0

private theorem theta_flux_pairing_split_abs_le_of_A3_term1 :
  ∀ {β κ : ℝ} {m : ℕ} (I : Ingredients β) (Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ), IsStreamSeq I Φ → (2 :
    ℕ) ≤ m → (∀ (j : ℕ), (1 : ℕ) ≤ j → ∀ (t : ℝ) (n : ℕ), (2 : ℕ) ≤ n → barNorm n ((2 : ℝ) ^ (8
    : ℕ) * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤ ENNReal.ofReal ((2 : ℝ) ^ (5 : ℕ) * AVenhance.a β I.Λ
    j * epsilon β I.Λ j ^ (2 : ℕ) * (((↑n : ℝ) + (2 : ℝ)) ^ (2 : ℕ) / ((↑n : ℝ) + (1 : ℝ)) ^ (3
    : ℕ)))) → ∀ {θ₀ : Vec (2 : ℕ) → ℝ} {θ : ℝ → Vec (2 : ℕ) → ℝ}, IsClassicalSol (streamVel fun
    (t : ℝ) => Φ (m - (1 : ℕ)) t) κ (fun (_ : ℝ) (_ : Vec (2 : ℕ)) => (0 : ℝ)) θ₀ θ → (0 : ℝ)
    < κ → ∀ {T : ℝ}, T ∈ Set.Icc (0 : ℝ) (1 : ℝ) → ∀ (w : List (Fin (2 : ℕ))),
  let φ : ℝ → Vec (2 : ℕ) → ℝ := fun (t : ℝ) => Φ (m - (1 : ℕ)) t;
  let L : List (List (Fin (2 : ℕ)) × List (Fin (2 : ℕ))) := classicalWordCommutatorSplits w;
  ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry θ) (Set.Ici (0 : ℝ) ×ˢ Set.univ) → ∀
    split ∈ L, |∫ (p : ℝ × Vec (2 : ℕ)) in Set.Ioo (0 : ℝ) T ×ˢ unitCube, vecDot
    (thetaWordGradientExtension θ w p) (thetaStreamSplitExtension φ θ split p)| ≤ if
    split.1.length = (1 : ℕ) then (2 : ℝ) * thetaPotentialDerivativeCoefficient (m := m) I (2 :
    ℕ) * thetaAnalyticInductionLevel θ κ (w.length - (1 : ℕ)) ^ (2 : ℕ) / κ else (2 : ℝ) *
    thetaPotentialDerivativeCoefficient (m := m) I split.1.length *
    √(thetaIntervalWordGradientEnergy θ T w) * thetaAnalyticInductionLevel θ κ split.2.length /
    √κ
    := by
  intro β κ m I Φ hΦ hm hA3 θ₀ θ hsol hκ T hT w φ L hθ split hsplit
  have hleft : 1 ≤ split.1.length := by
    have hne := classicalWordCommutatorSplits_left_ne_nil w hsplit
    cases hword : split.1 with
    | nil => exact (hne hword).elim
    | cons j rest => simp
  by_cases hq : split.1.length = 1
  · have hfirst := theta_first_order_stream_split_pairing_time_abs_le_of_A3
      I Φ hΦ hm hA3 hsol hT split hsplit hq
    have hpartial := theta_interval_word_gradient_energy_le hθ hT split.2
    have hlevel := ThetaAnalyticProof.theta_proof_sqrt_gradient_le_level (θ := θ) hκ split.2
    have hlevelsq :
        thetaWordSpaceTimeGradientEnergy θ split.2 ≤
          thetaAnalyticInductionLevel θ κ split.2.length ^ 2 / κ := by
      have hGnonneg : 0 ≤ thetaWordSpaceTimeGradientEnergy θ split.2 := by
        unfold thetaWordSpaceTimeGradientEnergy
        exact integral_nonneg fun _ => Homogenization.vecNormSq_nonneg _
      have hsqrt := Real.sq_sqrt hGnonneg
      calc
        thetaWordSpaceTimeGradientEnergy θ split.2 =
            Real.sqrt (thetaWordSpaceTimeGradientEnergy θ split.2) ^ 2 := hsqrt.symm
        _ ≤ (thetaAnalyticInductionLevel θ κ split.2.length / Real.sqrt κ) ^ 2 := by
          simpa only [pow_two] using
            (mul_self_le_mul_self (Real.sqrt_nonneg _) hlevel)
        _ = thetaAnalyticInductionLevel θ κ split.2.length ^ 2 / κ := by
          rw [div_pow, Real.sq_sqrt hκ.le]
    have hcoeff :
        2 * (2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
          AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
          ((2 : ℕ).factorial : ℝ) *
          (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ 2) =
        2 * thetaPotentialDerivativeCoefficient (m := m) I 2 := by
      simp [thetaPotentialDerivativeCoefficient]
    have hlenR : (w.length - 1) = split.2.length := by
      have hlength := classicalWordCommutatorSplits_length w hsplit
      omega
    have hMnonneg : 0 ≤ 2 * thetaPotentialDerivativeCoefficient (m := m) I 2 :=
      mul_nonneg (by norm_num) (by
        have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
          AVenhance.Infra.Cutoff.epsilon_pos
            I.one_lt_beta I.beta_lt I.two_pow_seven_le
        have ha : 0 < AVenhance.a β I.Λ (m - 1) := by
          rw [AVenhance.a]
          exact Real.rpow_pos_of_pos he _
        unfold thetaPotentialDerivativeCoefficient
        positivity)
    have hconvert :
        2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
            (∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
              Homogenization.vecNormSq
                (AVenhance.spaceGrad (classicalWordDerivative split.2 (θ t)) x)) ≤
          2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
            thetaAnalyticInductionLevel θ κ split.2.length ^ 2 / κ := by
      calc
        _ ≤ 2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
            thetaWordSpaceTimeGradientEnergy θ split.2 :=
          mul_le_mul_of_nonneg_left hpartial hMnonneg
        _ ≤ 2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
            (thetaAnalyticInductionLevel θ κ split.2.length ^ 2 / κ) :=
          mul_le_mul_of_nonneg_left hlevelsq hMnonneg
        _ = _ := by ring
    have hfirst' :
        |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
          vecDot (thetaWordGradientExtension θ w p)
            (thetaStreamSplitExtension φ θ split p)| ≤
          2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
            (∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
              Homogenization.vecNormSq
                (AVenhance.spaceGrad (classicalWordDerivative split.2 (θ t)) x)) := by
      change |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
          vecDot (thetaWordGradientExtension θ w p)
            (fun j => thetaWordExtension φ split.1 p *
              thetaStreamWordExtension θ split.2 p j)| ≤ _
      calc
        _ ≤ 2 * (2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
              AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
              ((2 : ℕ).factorial : ℝ) *
              (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ 2) *
              (∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
                Homogenization.vecNormSq
                  (AVenhance.spaceGrad (classicalWordDerivative split.2 (θ t)) x)) := by
            simpa [φ] using hfirst
        _ = _ := by rw [hcoeff]
    rw [hlenR]
    simpa [hq] using hfirst'.trans hconvert
  · have hq2 : 2 ≤ split.1.length := by omega
    have hhigher := theta_higher_order_stream_split_pairing_abs_le_of_A3
      I Φ hΦ hm hA3 hsol hT (w := w) split hq2
    have hright := ThetaAnalyticProof.theta_proof_sqrt_gradient_le_level (θ := θ) hκ split.2
    have hpartial := theta_interval_word_gradient_energy_le hθ hT split.2
    have hrightPartial :
        Real.sqrt (thetaIntervalWordGradientEnergy θ T split.2) ≤
          thetaAnalyticInductionLevel θ κ split.2.length / Real.sqrt κ := by
      exact (Real.sqrt_le_sqrt hpartial).trans hright
    have hM : 0 ≤ thetaPotentialDerivativeCoefficient (m := m) I split.1.length := by
      have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
        AVenhance.Infra.Cutoff.epsilon_pos
          I.one_lt_beta I.beta_lt I.two_pow_seven_le
      have ha : 0 < AVenhance.a β I.Λ (m - 1) := by
        rw [AVenhance.a]
        exact Real.rpow_pos_of_pos he _
      unfold thetaPotentialDerivativeCoefficient
      positivity
    have hfactor : 0 ≤ (2 : ℝ) *
        thetaPotentialDerivativeCoefficient (m := m) I split.1.length *
        Real.sqrt (thetaIntervalWordGradientEnergy θ T w) := by
      exact mul_nonneg (mul_nonneg (by norm_num) hM)
        (Real.sqrt_nonneg (thetaIntervalWordGradientEnergy θ T w))
    have hmul := mul_le_mul_of_nonneg_left hrightPartial hfactor
    have htarget :
        |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
          vecDot (thetaWordGradientExtension θ w p)
            (thetaStreamSplitExtension φ θ split p)| ≤
          2 * thetaPotentialDerivativeCoefficient (m := m) I split.1.length *
            Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
              thetaAnalyticInductionLevel θ κ split.2.length / Real.sqrt κ := by
      calc
        _ ≤ 2 * thetaPotentialDerivativeCoefficient (m := m) I split.1.length *
            Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
              Real.sqrt (thetaIntervalWordGradientEnergy θ T split.2) := by
          simpa [thetaStreamSplitExtension] using hhigher
        _ ≤ 2 * thetaPotentialDerivativeCoefficient (m := m) I split.1.length *
            Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
              (thetaAnalyticInductionLevel θ κ split.2.length / Real.sqrt κ) := by
          simpa [mul_assoc] using hmul
        _ = _ := by ring
    simpa [hq] using htarget

/-- The flux pairing is split into the q=1 square-energy term and the
q≥2 Cauchy term. -/
theorem theta_flux_pairing_split_abs_le_of_A3
    {β κ : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
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
    (hκ : 0 < κ) {T : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1)
    (w : List (Fin 2)) :
    |∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
      vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
        (thetaStreamCommutatorFlux w ((fun t => Φ (m - 1) t) t) (θ t) x)| ≤
      (2 * w.length * thetaPotentialDerivativeCoefficient (m := m) I 2 *
      thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ +
        2 * Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
          thetaAnalyticHighConvolution (m := m) I κ θ w.length) := by
  let φ : ℝ → Vec 2 → ℝ := fun t => Φ (m - 1) t
  let L := classicalWordCommutatorSplits w
  let P : List ℝ := L.map fun split =>
    ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      vecDot (thetaWordGradientExtension θ w p)
        (thetaStreamSplitExtension φ θ split p)
  have hφadm : AVenhance.IsAdmissibleStream φ :=
    theta_prev_stream_admissible I Φ hΦ hm
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    exact hφadm.1.contDiffOn.mono (by intro p hp; exact Set.mem_univ p)
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hsol.1
  have hflux := theta_classical_flux_interval_integral_eq_split_sum hT hφ hθ w
  have hflux' :
      (∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
        vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
          (thetaStreamCommutatorFlux w (φ t) (θ t) x)) = P.sum := by
    simpa [P, L] using hflux
  have hterm (split : List (Fin 2) × List (Fin 2))
      (hsplit : split ∈ L) :
      |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
        vecDot (thetaWordGradientExtension θ w p)
          (thetaStreamSplitExtension φ θ split p)| ≤
        if split.1.length = 1 then
          2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
            thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ
        else
          2 * thetaPotentialDerivativeCoefficient (m := m) I split.1.length *
            Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
              thetaAnalyticInductionLevel θ κ split.2.length / Real.sqrt κ := by
    exact @theta_flux_pairing_split_abs_le_of_A3_term1 β κ m I Φ hΦ hm hA3 θ₀ θ hsol hκ T hT w hθ
        split hsplit
  have habs : |P.sum| ≤ (P.map fun x => |x|).sum :=
    ThetaAnalyticProof.theta_proof_abs_list_sum_le P
  have htermSum :
      (P.map fun x => |x|).sum ≤
        (L.map fun split =>
          if split.1.length = 1 then
            2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
              thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ
          else
            2 * thetaPotentialDerivativeCoefficient (m := m) I split.1.length *
              Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
                thetaAnalyticInductionLevel θ κ split.2.length / Real.sqrt κ).sum := by
    calc
      _ = (L.map fun split =>
          |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
            vecDot (thetaWordGradientExtension θ w p)
              (thetaStreamSplitExtension φ θ split p)|).sum := by
            simp [P, L, List.map_map, Function.comp_def]
      _ ≤ _ := by
        apply List.sum_le_sum
        intro split hsplit
        exact hterm split hsplit
  have hsame :
      (L.map fun split =>
          if split.1.length = 1 then
            2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
              thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ
          else
            2 * thetaPotentialDerivativeCoefficient (m := m) I split.1.length *
              Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
              thetaAnalyticInductionLevel θ κ split.2.length / Real.sqrt κ).sum =
      ((classicalWordCommutatorSplits w).map fun split =>
        if split.1.length = 1 then
          2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
            thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ
        else
          2 * thetaPotentialDerivativeCoefficient (m := m) I split.1.length *
            Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
              thetaAnalyticInductionLevel θ κ (w.length - split.1.length) / Real.sqrt κ).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro split hsplit
    have hlength := classicalWordCommutatorSplits_length w hsplit
    by_cases hq : split.1.length = 1
    · simp [hq]
    · have hright : split.2.length = w.length - split.1.length := by omega
      simp [hq, hright]
  have hweight := theta_commutator_split_weighted_sum w (fun q =>
    if q = 1 then
      2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
        thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ
    else
      2 * thetaPotentialDerivativeCoefficient (m := m) I q *
        Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
          thetaAnalyticInductionLevel θ κ (w.length - q) / Real.sqrt κ)
  have hweight' :
      ((classicalWordCommutatorSplits w).map fun split =>
        if split.1.length = 1 then
          2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
            thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ
        else
          2 * thetaPotentialDerivativeCoefficient (m := m) I split.1.length *
            Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
              thetaAnalyticInductionLevel θ κ (w.length - split.1.length) / Real.sqrt κ).sum =
      ∑ q ∈ Finset.range (w.length + 1),
        (((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) *
          (if q = 1 then
            2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
              thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ
          else
            2 * thetaPotentialDerivativeCoefficient (m := m) I q *
              Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
                thetaAnalyticInductionLevel θ κ (w.length - q) / Real.sqrt κ)) := by
    simpa using hweight
  have hqdecomp :
      (∑ q ∈ Finset.range (w.length + 1),
        (((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) *
          (if q = 1 then
            2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
              thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ
          else
            2 * thetaPotentialDerivativeCoefficient (m := m) I q *
              Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
                thetaAnalyticInductionLevel θ κ (w.length - q) / Real.sqrt κ))) =
        (2 * w.length * thetaPotentialDerivativeCoefficient (m := m) I 2 *
            thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ +
          2 * Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
            thetaAnalyticHighConvolution (m := m) I κ θ w.length) := by
    let K : ℝ := 2 * thetaPotentialDerivativeCoefficient (m := m) I 2 *
      thetaAnalyticInductionLevel θ κ (w.length - 1) ^ 2 / κ
    let H : ℕ → ℝ := fun q =>
      2 * thetaPotentialDerivativeCoefficient (m := m) I q *
        Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
          thetaAnalyticInductionLevel θ κ (w.length - q) / Real.sqrt κ
    have hsplit :
        (∑ q ∈ Finset.range (w.length + 1),
          (((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) *
            (if q = 1 then K else H q))) =
          (∑ q ∈ Finset.range (w.length + 1),
            if q = 1 then
              ((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) * K
            else 0) +
          (∑ q ∈ Finset.range (w.length + 1),
            if 2 ≤ q then
              ((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) * H q
            else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hzero : q = 0
      · simp [hzero, K, H]
      · by_cases hone : q = 1
        · simp [hone, K, H]
        · have htwo : 2 ≤ q := by omega
          simp [hzero, hone, htwo, K, H]
    have hfirst :
        (∑ q ∈ Finset.range (w.length + 1),
          if q = 1 then
            ((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) * K
          else 0) = w.length * K := by
      by_cases hn : w.length = 0
      · simp [hn, K]
      · have hnpos : 1 ≤ w.length := by omega
        simp [Nat.choose_one_right, hn, K]
    have hhigh :
        (∑ q ∈ Finset.range (w.length + 1),
          if 2 ≤ q then
            ((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) * H q
          else 0) =
          2 * Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
            thetaAnalyticHighConvolution (m := m) I κ θ w.length := by
      simp only [H, thetaAnalyticHighConvolution, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hq2 : 2 ≤ q
      · have hq0 : q ≠ 0 := by omega
        simp [hq2, hq0]
        ring
      · simp [hq2]
    rw [hsplit, hfirst, hhigh]
    simp [K]
    ring
  change |∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
      vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
        (thetaStreamCommutatorFlux w (φ t) (θ t) x)| ≤ _
  rw [hflux']
  calc
    |P.sum| ≤ (P.map fun x => |x|).sum := habs
    _ ≤ _ := htermSum
    _ = _ := (hsame.trans hweight').trans hqdecomp

end AVenhance.Infra.Section4

end
