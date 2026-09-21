/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.Dynamics
import LeanPool.FullyDynamicMatching.FD1D.Expectations

/-!
# Unified energy estimates for the v5 policy

This module proves the stationary and finite-horizon forms of the manuscript's
master energy inequality.
-/

namespace FD1D.V5.Dynamics

noncomputable section

open scoped BigOperators

variable {L m : ℕ}

/-- Sum of transport energy and the weighted finest-level rate energy. -/
def combinedEnergy (a : ℝ)
    (x : InventoryState (DyadicNode L) m) : ℝ :=
  a ^ 2 / 2 * stateRateEnergy a x L + stateTransportEnergy a x

theorem stateRateEnergy_nonneg
    (a : ℝ) (x : InventoryState (DyadicNode L) m) (d : ℕ) :
    0 ≤ stateRateEnergy a x d := by
  unfold stateRateEnergy hazardEnergy weightedLevel
  exact Finset.sum_nonneg fun v _ =>
    mul_nonneg (nodeMass_nonneg d v) (sq_nonneg _)

theorem stateTransportEnergy_nonneg
    (a : ℝ) (x : InventoryState (DyadicNode L) m) :
    0 ≤ stateTransportEnergy a x := by
  unfold stateTransportEnergy TreePolicy.transportEnergy
    internalWeightedSum weightedLevel
  apply Finset.sum_nonneg
  intro d hd
  apply Finset.sum_nonneg
  intro v hv
  exact mul_nonneg (nodeMass_nonneg d v) (sq_nonneg _)

theorem combinedEnergy_nonneg
    (a : ℝ) (x : InventoryState (DyadicNode L) m) :
    0 ≤ combinedEnergy a x := by
  unfold combinedEnergy
  exact add_nonneg
    (mul_nonneg (div_nonneg (sq_nonneg a) (by norm_num))
      (stateRateEnergy_nonneg a x L))
    (stateTransportEnergy_nonneg a x)

/-- The one-state inequality preceding the master energy telescope. -/
theorem state_combinedEnergy_le_drift
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (haL : 2000 * (L : ℝ) ≤ a)
    (x : InventoryState (DyadicNode L) m) :
    combinedEnergy a x -
        501 * a ^ 2 / (m : ℝ) ^ 2 ≤
      1000 * a * (stateDrift a x - stateRemainder a x) := by
  let H := stateRateEnergy a x L
  let G := stateTransportEnergy a x
  have hH : 0 ≤ H := stateRateEnergy_nonneg a x L
  have hD := stateDrift_lower_bound a ha hm x
  have hR :
      stateRemainder a x ≤ (L : ℝ) * H :=
    (stateRemainder_bounds a ha hm x).2.1.trans
      (stateRemainder_bounds a ha hm x).2.2
  have hdepth : (L : ℝ) ≤ a / 2000 := by linarith
  have hRH : stateRemainder a x ≤ a / 2000 * H := by
    exact hR.trans (mul_le_mul_of_nonneg_right hdepth hH)
  have hbase :
      a / 2000 * H + G / (1000 * a) -
          501 * a / (1000 * (m : ℝ) ^ 2) ≤
        stateDrift a x - stateRemainder a x := by
    dsimp [H, G] at *
    linarith
  have hmul := mul_le_mul_of_nonneg_left hbase
    (show 0 ≤ 1000 * a by positivity)
  calc
    combinedEnergy a x - 501 * a ^ 2 / (m : ℝ) ^ 2 =
        1000 * a *
          (a / 2000 * H + G / (1000 * a) -
            501 * a / (1000 * (m : ℝ) ^ 2)) := by
              unfold combinedEnergy
              dsimp [H, G]
              field_simp [ha.ne']
              ring
    _ ≤ 1000 * a *
          (stateDrift a x - stateRemainder a x) := hmul

theorem expect_combinedEnergy_le
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (haL : 2000 * (L : ℝ) ≤ a)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m)) :
    μ.expect (combinedEnergy a) ≤
      501 * a ^ 2 / (m : ℝ) ^ 2 +
        1000 * a *
          (μ.expect (stateDrift a) - μ.expect (stateRemainder a)) := by
  have hmono := μ.expect_mono
    (state_combinedEnergy_le_drift a ha hm haL)
  have hrewrite :
      μ.expect (fun x =>
          combinedEnergy a x - 501 * a ^ 2 / (m : ℝ) ^ 2) =
        μ.expect (combinedEnergy a) -
          501 * a ^ 2 / (m : ℝ) ^ 2 := by
    rw [μ.expect_sub, μ.expect_const]
  have hrewrite' :
      μ.expect (fun x =>
          1000 * a * (stateDrift a x - stateRemainder a x)) =
        1000 * a *
          (μ.expect (stateDrift a) - μ.expect (stateRemainder a)) := by
    rw [μ.expect_const_mul, μ.expect_sub]
  rw [hrewrite, hrewrite'] at hmono
  linarith

theorem stationary_expected_drift_eq_remainder
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hμ : (kernel a ha hm).IsStationary μ) :
    μ.expect (stateDrift a) = μ.expect (stateRemainder a) := by
  have hstationary :
      ∀ y, ∑ x, μ.mass x * kernel a ha hm x y = μ.mass y := by
    intro y
    have hy := congrArg
      (fun ν : FiniteLaw (InventoryState (DyadicNode L) m) => ν.mass y) hμ
    simpa only [FiniteKernel.mass_step] using hy
  exact stationary_expect_drift_eq_remainder μ (kernel a ha hm)
    (statePotential a) (stateDrift a) (stateRemainder a)
    (kernel a ha hm).sum_trans hstationary
    (kernel_drift_eq_stateDrift_sub_stateRemainder a ha hm)

/-- The two stationary energy bounds in Proposition 4.4. -/
theorem stationary_energy_estimates
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (haL : 2000 * (L : ℝ) ≤ a)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hμ : (kernel a ha hm).IsStationary μ) :
    μ.expect (fun x => stateRateEnergy a x L) ≤
        1002 / (m : ℝ) ^ 2 ∧
      μ.expect (stateTransportEnergy a) ≤
        501 * a ^ 2 / (m : ℝ) ^ 2 := by
  let H := μ.expect (fun x => stateRateEnergy a x L)
  let G := μ.expect (stateTransportEnergy a)
  have hH : 0 ≤ H :=
    μ.expect_nonneg (fun x => stateRateEnergy_nonneg a x L)
  have hG : 0 ≤ G :=
    μ.expect_nonneg (stateTransportEnergy_nonneg a)
  have hcombined :
      μ.expect (combinedEnergy a) ≤
        501 * a ^ 2 / (m : ℝ) ^ 2 := by
    have h := expect_combinedEnergy_le a ha hm haL μ
    rw [stationary_expected_drift_eq_remainder a ha hm μ hμ] at h
    simpa using h
  have hexpand :
      μ.expect (combinedEnergy a) = a ^ 2 / 2 * H + G := by
    unfold combinedEnergy
    rw [μ.expect_add, μ.expect_const_mul]
  rw [hexpand] at hcombined
  have haSq : 0 < a ^ 2 := sq_pos_of_pos ha
  constructor
  · change H ≤ 1002 / (m : ℝ) ^ 2
    have hcoef : 0 < a ^ 2 / 2 := by positivity
    have hAH :
        a ^ 2 / 2 * H ≤ 501 * a ^ 2 / (m : ℝ) ^ 2 := by
      linarith
    calc
      H ≤ (501 * a ^ 2 / (m : ℝ) ^ 2) / (a ^ 2 / 2) := by
        apply (le_div_iff₀ hcoef).2
        simpa [mul_comm] using hAH
      _ = 1002 / (m : ℝ) ^ 2 := by
        field_simp [ha.ne']
        norm_num
  · change G ≤ 501 * a ^ 2 / (m : ℝ) ^ 2
    nlinarith

theorem existsUnique_stationaryLaw
    (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    ∃! μ : FiniteLaw (InventoryState (DyadicNode L) m),
      (kernel a ha hm).IsStationary μ := by
  let : Nonempty (InventoryState (DyadicNode L) m) :=
    ⟨⟨fun i => if i = 0 then m else 0, by simp⟩⟩
  obtain ⟨μ, hμ⟩ :=
    (kernel (L := L) a ha hm).exists_stationary
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  exact FiniteKernel.stationary_unique
    (kernel_irreducible (L := L) a ha hm) hν hμ

/-- The manuscript's finite-horizon master energy estimate. -/
theorem master_energy_estimate
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (haL : 2000 * (L : ℝ) ≤ a)
    (μ₀ : FiniteLaw (InventoryState (DyadicNode L) m))
    (T : ℕ) (hT : 0 < T) :
    (∑ t ∈ Finset.range T,
        ((kernel a ha hm).iterate t μ₀).expect (combinedEnergy a)) /
        (T : ℝ) ≤
      501 * a ^ 2 / (m : ℝ) ^ 2 +
        1000 * a / (T : ℝ) *
          (((kernel a ha hm).iterate T μ₀).expect (statePotential a) -
            μ₀.expect (statePotential a)) := by
  let K : FiniteKernel (InventoryState (DyadicNode L) m) :=
    kernel (L := L) a ha hm
  let μt : ℕ → FiniteLaw (InventoryState (DyadicNode L) m) :=
    fun t => K.iterate t μ₀
  let Phi : ℕ → ℝ := fun t => (μt t).expect (statePotential a)
  have hdrift (t : ℕ) :
      Phi (t + 1) - Phi t =
        (μt t).expect (stateDrift a) -
          (μt t).expect (stateRemainder a) := by
    calc
      Phi (t + 1) - Phi t =
          (μt t).expect (fun x =>
            ∑ y, K x y *
              (statePotential a y - statePotential a x)) := by
        simpa [Phi, μt] using
          K.expect_iterate_succ μ₀ t (statePotential a)
      _ = (μt t).expect
          (fun x => stateDrift a x - stateRemainder a x) := by
        apply congrArg (μt t).expect
        funext x
        exact kernel_drift_eq_stateDrift_sub_stateRemainder a ha hm x
      _ = _ := (μt t).expect_sub _ _
  have hstep (t : ℕ) :
      (μt t).expect (combinedEnergy a) ≤
        501 * a ^ 2 / (m : ℝ) ^ 2 +
          1000 * a * (Phi (t + 1) - Phi t) := by
    rw [hdrift]
    exact expect_combinedEnergy_le a ha hm haL (μt t)
  have hsum :
      ∑ t ∈ Finset.range T, (μt t).expect (combinedEnergy a) ≤
        ∑ t ∈ Finset.range T,
          (501 * a ^ 2 / (m : ℝ) ^ 2 +
            1000 * a * (Phi (t + 1) - Phi t)) := by
    apply Finset.sum_le_sum
    intro t ht
    exact hstep t
  have htel :
      (∑ t ∈ Finset.range T,
          (501 * a ^ 2 / (m : ℝ) ^ 2 +
            1000 * a * (Phi (t + 1) - Phi t))) =
        (T : ℝ) * (501 * a ^ 2 / (m : ℝ) ^ 2) +
          1000 * a * (Phi T - Phi 0) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_range_sub]
  rw [htel] at hsum
  have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
  apply (div_le_iff₀ hTR).2
  change
    ∑ t ∈ Finset.range T,
        ((kernel a ha hm).iterate t μ₀).expect (combinedEnergy a) ≤ _
  change
    ∑ t ∈ Finset.range T, (μt t).expect (combinedEnergy a) ≤ _
  calc
    ∑ t ∈ Finset.range T, (μt t).expect (combinedEnergy a) ≤
        (T : ℝ) * (501 * a ^ 2 / (m : ℝ) ^ 2) +
          1000 * a * (Phi T - Phi 0) := hsum
    _ = (501 * a ^ 2 / (m : ℝ) ^ 2 +
          1000 * a / (T : ℝ) *
            (((kernel a ha hm).iterate T μ₀).expect (statePotential a) -
              μ₀.expect (statePotential a))) * (T : ℝ) := by
      dsimp [Phi, μt, K]
      field_simp [hTR.ne']

/-- The finite-horizon bound on average transport energy. -/
theorem finite_transport_energy_estimate
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (haL : 2000 * (L : ℝ) ≤ a)
    (hbudget : Real.log (1 + 2 * (m : ℝ) / a) ≤ a / 2000)
    (μ₀ : FiniteLaw (InventoryState (DyadicNode L) m))
    (T : ℕ) (hT : 0 < T) :
    (∑ t ∈ Finset.range T,
        ((kernel a ha hm).iterate t μ₀).expect
          (stateTransportEnergy a)) / (T : ℝ) ≤
      501 * a ^ 2 / (m : ℝ) ^ 2 + a ^ 2 / (2 * (T : ℝ)) := by
  have hmaster :=
    master_energy_estimate a ha hm haL μ₀ T hT
  have hdrop :
      (∑ t ∈ Finset.range T,
          ((kernel a ha hm).iterate t μ₀).expect
            (stateTransportEnergy a)) / (T : ℝ) ≤
        (∑ t ∈ Finset.range T,
          ((kernel a ha hm).iterate t μ₀).expect
            (combinedEnergy a)) / (T : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro t ht
    apply FiniteLaw.expect_mono
    intro x
    unfold combinedEnergy
    have hH := stateRateEnergy_nonneg a x L
    nlinarith [sq_nonneg a]
  have hPhiT :
      ((kernel a ha hm).iterate T μ₀).expect (statePotential a) ≤
        Real.log (1 + 2 * (m : ℝ) / a) := by
    calc
      ((kernel a ha hm).iterate T μ₀).expect (statePotential a) ≤
          ((kernel a ha hm).iterate T μ₀).expect
            (fun _ => Real.log (1 + 2 * (m : ℝ) / a)) :=
        ((kernel a ha hm).iterate T μ₀).expect_mono
          (statePotential_le_log_one_add_two_mul_div a ha)
      _ = _ := FiniteLaw.expect_const _ _
  have hPhi0 : 0 ≤ μ₀.expect (statePotential a) :=
    μ₀.expect_nonneg (statePotential_nonneg a ha)
  have hdiff :
      ((kernel a ha hm).iterate T μ₀).expect (statePotential a) -
          μ₀.expect (statePotential a) ≤ a / 2000 := by
    linarith
  have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
  calc
    (∑ t ∈ Finset.range T,
        ((kernel a ha hm).iterate t μ₀).expect
          (stateTransportEnergy a)) / (T : ℝ)
        ≤ (∑ t ∈ Finset.range T,
          ((kernel a ha hm).iterate t μ₀).expect
            (combinedEnergy a)) / (T : ℝ) := hdrop
    _ ≤ 501 * a ^ 2 / (m : ℝ) ^ 2 +
        1000 * a / (T : ℝ) *
          (((kernel a ha hm).iterate T μ₀).expect (statePotential a) -
            μ₀.expect (statePotential a)) := hmaster
    _ ≤ 501 * a ^ 2 / (m : ℝ) ^ 2 +
          1000 * a / (T : ℝ) * (a / 2000) := by
      gcongr
    _ = 501 * a ^ 2 / (m : ℝ) ^ 2 +
          a ^ 2 / (2 * (T : ℝ)) := by
      field_simp [hTR.ne']
      ring

end

end FD1D.V5.Dynamics
