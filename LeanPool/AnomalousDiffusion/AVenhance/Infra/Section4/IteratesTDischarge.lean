/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDischargeBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTA5Upgrade
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse

/-! # Iterates TDischarge

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- A concrete enlargement of the l.V constant discharges the coefficient
smallness premises; all constants are chosen before ingredients and data. -/
def iterateReducedSourceConstant (β Ccut c Ck Cflow Rflow Cθ : ℝ) : ℝ :=
  max (iterateDischargeThreshold β Ccut Ck)
    (iterateSourceConstant
      (iterateBudgetUniversalConstant (iterateKmatConstant β Ccut) Ck c
        ((2 : ℝ) ^ (-25 : ℤ)) Cflow
        (iterateMeanScaleConstant β Ccut (iterateRatioConstant β Ck))) Rflow Cθ)

/-- Actual T upgrade with stream-regularity/diffusivity-recursion and the two-error mean and Kmat
inputs discharged. The positive amplitude is abstract; the theta base uses
only its zeroth gradient energy and positive scalar derivative energies. -/
theorem iterate_T_upgrade_of_theta_flow_material (β Ccut : ℝ) :
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
      (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0),
    (Real.sqrt (I.kappaAt κ (m - 1) (M - (m - 1))) * Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (T (Nstar β) t))) ≤
      N * (1 + (C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β)) * (Nstar β : ℝ) * ((2 * Nstar
          β).factorial : ℝ))) ∧
    (∀ v w : List (Fin 2), v.length = w.length → 1 ≤ v.length →
      ∀ s, 0 ≤ s → s ≤ 1 →
      Real.sqrt (l2NormSq (iterateSpatialWord v (T (Nstar β) s))) +
        Real.sqrt (I.kappaAt κ (m - 1) (M - (m - 1))) *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (T (Nstar β)
            t)))) ≤
      N * (4 : ℝ) ^ Nstar β * ((2 * Nstar β).factorial : ℝ) * (v.length.factorial : ℝ) *
        ((4 * C₀ ^ 3) * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) ^ v.length) := by
  obtain ⟨c, Ck, hc, hcC, hrec⟩ := AVenhance.l_recurse β Ccut
  refine ⟨c, Ck, hc, hcC, ?_⟩
  intro I hz hxi hh Φ hΦ κ M m θ₀ θprev T hT hθ hm hmM hPerm
    hflow hflowp Cflow Rflow Cθ Rθ C₀ N hN hCf hRf hRθ hC₀ hradius hsmall
    hzero hpositive hbase
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
  exact iterate_T_upgrade_conditional_A3_A5_flow_material I hΦ κ M hT hθ hm hmM hκ
    hflow hflowp hA3 hN hc hcC hA5.1 hK hCf hCm hRf hRθ hsource hradius hsmall
    hinputs.1 hinputs.2.1 hinputs.2.2 hzero hpositive hbase

end AVenhance.Infra.Section4
