/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTScalarZeroUpgrade
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusivityComparison
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTThetaUpgrade

/-! # TUpgrade Consumers Scalar Zero

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem iterate_T_upgrade_conditional_A3_A5_flow_material_scalar_zero {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (κ : ℝ) (M : ℕ) {m : ℕ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m (I.kappaAt κ m (M - m)) (I.kappaAt κ (m - 1)
        (M - (m - 1))) θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaAt κ (m - 1) (M - (m - 1))) (fun _ _ =>
        0) θ₀ θprev)
    (hm : 2 ≤ m) (hmM : m ≤ M) (hκtop : 0 < κ)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t))
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {c Ck K Cflow Cmean Rflow Cθ Rθ C₀ N : ℝ}
    (hN : 0 < N)
    (hc : 0 < c) (hcC : c < Ck)
    (hA5 : ∀ j : ℕ, 1 ≤ j → j < M →
      c * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) ≤ I.kappaAt κ j (M - j) ∧
      I.kappaAt κ j (M - j) ≤ Ck * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β))) (hK : 0 ≤ K)
          (hCf : 0 ≤ Cflow) (hCm : 0 ≤ Cmean)
    (hRf : 256 ≤ Rflow) (hRθ : 0 < Rθ)
    (hC₀ : iterateSourceConstant
      (iterateBudgetUniversalConstant K Ck c ((2 : ℝ) ^ (-25 : ℤ)) Cflow Cmean) Rflow Cθ ≤ C₀)
    (hradius : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ)
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * C₀ ^ 3)⁻¹)
    (hKm : ∀ t j k, |I.Kmat (I.kappaAt κ m (M - m)) m t j k| ≤ K * (I.kappaAt κ (m - 1) (M - (m -
        1))))
    (hcondition : epsilon β I.Λ m ^ 2 ≤ (I.kappaAt κ m (M - m)) * tau β I.Λ m / 2)
    (hMeanScale : iterateMeanErrorBound I (I.kappaAt κ m (M - m)) m ≤
      (I.kappaAt κ (m - 1) (M - (m - 1))) * Cmean * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hzero : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ j k,
      |(I.flowGrad hΦ m l t x - 1) j k| ≤ Cflow * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hpositive : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ p : List (Fin 2), 1 ≤ p.length → ∀ j k,
      |iterateSpatialWord p (fun y => (I.flowGrad hΦ m l t y - 1) j k) x| ≤
        Cflow * (p.length.factorial : ℝ) * (Rflow / epsilon β I.Λ (m - 1)) ^ p.length)
    (hbase : iterateCoordinateEnergyProfile θprev (I.kappaAt κ (m - 1) (M - (m - 1))) N
      (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0)
    (hscalar : ∀ s, 0 ≤ s → s ≤ 1 → Real.sqrt (l2NormSq (θprev s)) ≤ N) :
    ∀ s, 0 ≤ s → s ≤ 1 →
    Real.sqrt (l2NormSq (T (Nstar β) s)) + Real.sqrt (I.kappaAt κ (m - 1) (M - (m - 1))) *
      Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (T (Nstar β) t))) ≤
      2 * N * (1 + (C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β)) * (Nstar β : ℝ) * ((2 * Nstar
          β).factorial : ℝ)) := by
  have hκm := Infra.Section3.kappaAt_pos I hκtop m (M - m)
  have hpoint := hA5 (m - 1) (by omega) (by omega)
  have hmean : ∀ j k, |(timeAvgMat (I.Kmat (I.kappaAt κ m (M - m)) m) -
      I.kappaAt κ (m - 1) (M - (m - 1)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
      I.kappaAt κ (m - 1) (M - (m - 1)) * Cmean *
        epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    intro j k
    have hn := iterate_mean_coefficient_bound I κ (by omega : 1 ≤ m) hmM hκm hcondition
    have he : |(timeAvgMat (I.Kmat (I.kappaAt κ m (M - m)) m) -
        I.kappaAt κ (m - 1) (M - (m - 1)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
        iterateMeanErrorBound I (I.kappaAt κ m (M - m)) m := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ k).trans ((norm_le_pi_norm _ j).trans hn)
    exact he.trans hMeanScale
  exact iterate_T_source_upgrade_of_diffusivity_and_flow_scalar_zero
    (hκscale := iterate_kappaAt_abs_le_previous I hκtop (by omega) hmM) I hΦ hT hθ hm hκm
    hflow hflowp hA3 hN hc (hc.trans hcC).le hK hCf hCm hRf hRθ
    hpoint.1 hpoint.2 hC₀ hradius hsmall hKm hmean hzero hpositive hbase hscalar

theorem iterate_T_upgrade_of_theta_flow_material_scalar_zero (β Ccut : ℝ) :
    ∃ c Ck : ℝ, 0 < c ∧ c < Ck ∧
    ∀ (I : Ingredients β) (_hz : I.Czeta ≤ Ccut) (_hxi : I.Cxi ≤ Ccut)
      (_hh : I.Chat ≤ Ccut)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (κ : ℝ) (M : ℕ) {m : ℕ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (_hT : I.IsTIterates hΦ m (I.kappaAt κ m (M - m)) (I.kappaAt κ (m - 1)
        (M - (m - 1))) θ₀ θprev T)
    (_hθ : IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaAt κ (m - 1) (M - (m - 1))) (fun _ _ =>
        0) θ₀ θprev)
    (_hm : 2 ≤ m) (_hmM : m ≤ M) (_hPerm : κ ∈ permittedInterval β I.Λ M)
    (_hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (_hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t))
    (Cflow Rflow Cθ Rθ C₀ N : ℝ)
    (_hN : 0 < N)
    (_hCf : 0 ≤ Cflow)
    (_hRf : 256 ≤ Rflow) (_hRθ : 0 < Rθ)
    (_hC₀ : iterateReducedSourceConstant β Ccut c Ck Cflow Rflow Cθ ≤ C₀)
    (_hradius : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ)
    (_hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * C₀ ^ 3)⁻¹)
    (_hzero : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ j k,
      |(I.flowGrad hΦ m l t x - 1) j k| ≤ Cflow * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (_hpositive : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ p : List (Fin 2), 1 ≤ p.length → ∀ j k,
      |iterateSpatialWord p (fun y => (I.flowGrad hΦ m l t y - 1) j k) x| ≤
        Cflow * (p.length.factorial : ℝ) * (Rflow / epsilon β I.Λ (m - 1)) ^ p.length)
    (_hbase : iterateCoordinateEnergyProfile θprev (I.kappaAt κ (m - 1) (M - (m - 1))) N
      (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0)
    (_hscalar : ∀ s, 0 ≤ s → s ≤ 1 → Real.sqrt (l2NormSq (θprev s)) ≤ N),
    ∀ s, 0 ≤ s → s ≤ 1 →
    Real.sqrt (l2NormSq (T (Nstar β) s)) + Real.sqrt (I.kappaAt κ (m - 1) (M - (m - 1))) *
      Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (T (Nstar β) t))) ≤
      2 * N * (1 + (C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β)) * (Nstar β : ℝ) * ((2 * Nstar
          β).factorial : ℝ)) := by
  obtain ⟨c, Ck, hc, hcC, hrec⟩ := AVenhance.l_recurse β Ccut
  refine ⟨c, Ck, hc, hcC, ?_⟩
  intro I hz hxi hh Φ hΦ κ M m θ₀ θprev T hT hθ hm hmM hPerm
    hflow hflowp Cflow Rflow Cθ Rθ C₀ N hN hCf hRf hRθ hC₀ hradius hsmall
    hzero hpositive hbase hscalar
  have hM : 1 ≤ M := by omega
  have hκ : 0 < κ := (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
    (Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le) _)).trans_le hPerm.1
  have hpermissible : κ ∈ permissibleSet β I.Λ :=
    Set.mem_iUnion.mpr ⟨M, Set.mem_iUnion.mpr ⟨hM, hPerm⟩⟩
  have hA5 := hrec I hz hxi hh κ hpermissible M hM hPerm
  obtain ⟨_, _, hreg⟩ := AVenhance.stream_regularity β
  have hA3 := fun j hj t n hn => (hreg I Φ hΦ j hj t).2.1 n hn
  have hsource : iterateSourceConstant
      (iterateBudgetUniversalConstant (iterateKmatConstant β Ccut) Ck c
        ((2 : ℝ) ^ (-25 : ℤ)) Cflow
        (iterateMeanScaleConstant β Ccut (iterateRatioConstant β Ck))) Rflow Cθ ≤ C₀ :=
    (le_max_right _ _).trans hC₀
  have hC1 : 1 ≤ C₀ := (iterate_source_constant_bounds _ _ _).1.trans hsource
  have hthreshold : iterateDischargeThreshold β Ccut Ck ≤ C₀ :=
    (le_max_left _ _).trans hC₀
  have hinputs := iterate_chain_upgrade_inputs I hz hh hm hmM hκ hPerm
    (hc.trans hcC).le hC1 hthreshold hsmall (fun j hj hjM => (hA5.2 j hj hjM).2)
  have hcut : 0 ≤ Ccut := (by linarith only [I.one_le_Czeta] : 0 ≤ I.Czeta).trans hz
  have hK : 0 ≤ iterateKmatConstant β Ccut := by
    unfold iterateKmatConstant
    positivity
  have hCm : 0 ≤ iterateMeanScaleConstant β Ccut (iterateRatioConstant β Ck) := by
    unfold iterateMeanScaleConstant iterateRatioConstant
    positivity
  exact iterate_T_upgrade_conditional_A3_A5_flow_material_scalar_zero I hΦ κ M hT hθ hm hmM hκ
    hflow hflowp hA3 hN hc hcC hA5.1 hK hCf hCm hRf hRθ hsource hradius hsmall
    hinputs.1 hinputs.2.1 hinputs.2.2 hzero hpositive hbase hscalar

theorem iterate_T_upgrade_of_theta_scalar_zero (β Ccut : ℝ) :
    ∃ c Ck : ℝ, 0 < c ∧ c < Ck ∧
    ∀ (I : Ingredients β) (_hz : I.Czeta ≤ Ccut) (_hxi : I.Cxi ≤ Ccut)
      (_hh : I.Chat ≤ Ccut)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (κ : ℝ) (M : ℕ) {m : ℕ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (_hT : I.IsTIterates hΦ m (I.kappaAt κ m (M - m)) (I.kappaAt κ (m - 1)
        (M - (m - 1))) θ₀ θprev T)
    (_hθ : IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaAt κ (m - 1) (M - (m - 1))) (fun _ _ =>
        0) θ₀ θprev)
    (_hm : 2 ≤ m) (_hmM : m ≤ M) (_hPerm : κ ∈ permittedInterval β I.Λ M)
    (Cθ Rθ C₀ N : ℝ)
    (_hN : 0 < N)
    (_hRθ : 0 < Rθ)
    (_hC₀ : iterateReducedSourceConstant β Ccut c Ck 40 (2 ^ 10) Cθ ≤ C₀)
    (_hradius : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ)
    (_hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * C₀ ^ 3)⁻¹)
    (_hbase : iterateCoordinateEnergyProfile θprev (I.kappaAt κ (m - 1) (M - (m - 1))) N
      (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0)
    (_hscalar : ∀ s, 0 ≤ s → s ≤ 1 → Real.sqrt (l2NormSq (θprev s)) ≤ N),
    ∀ s, 0 ≤ s → s ≤ 1 →
    Real.sqrt (l2NormSq (T (Nstar β) s)) + Real.sqrt (I.kappaAt κ (m - 1) (M - (m - 1))) *
      Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (T (Nstar β) t))) ≤
      2 * N * (1 + (C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β)) * (Nstar β : ℝ) * ((2 * Nstar
          β).factorial : ℝ)) := by
  obtain ⟨c, Ck, hc, hcC, hupgrade⟩ := iterate_T_upgrade_of_theta_flow_material_scalar_zero β Ccut
  refine ⟨c, Ck, hc, hcC, ?_⟩
  intro I hz hxi hh Φ hΦ κ M m θ₀ θprev T hT hθ hm hmM hPerm
    Cθ Rθ C₀ N hN hRθ hC₀ hradius hsmall hbase hscalar
  exact hupgrade I hz hxi hh hΦ κ M hT hθ hm hmM hPerm
    (fun l => iterate_flowGrad_joint_smooth I hΦ m l)
    (fun t _ l => iterate_flowGrad_periodic I hΦ m l t)
    40 (2 ^ 10) Cθ Rθ C₀ N hN (by norm_num) (by norm_num) hRθ hC₀ hradius hsmall
    (fun t x l hn i j => iterate_flowGrad_zero_bound I hΦ (l := l) (t := t) hm hn x i j)
    (fun t x l hn w _ i j => iterate_flowGrad_word_bound I hΦ (l := l) (t := t) hm hn w x i j)
        hbase hscalar

end AVenhance.Infra.Section4
