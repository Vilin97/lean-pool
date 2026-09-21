/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Dynamics
import LeanPool.FullyDynamicMatching.FD1D.Expectations

/-! # Bounds -/

namespace FD1D

noncomputable section

open scoped BigOperators

namespace HierarchicalDynamics

variable {L m : ℕ}

theorem stateHazardEnergy_nonneg (a : ℝ)
    (x : InventoryState (DyadicNode L) m) (d : ℕ) :
    0 ≤ stateHazardEnergy a x d := by
  unfold stateHazardEnergy hazardEnergy weightedLevel
  exact Finset.sum_nonneg fun v _ =>
    mul_nonneg (nodeMass_nonneg d v) (sq_nonneg _)

theorem stateHazardEnergy_root (a : ℝ)
    (x : InventoryState (DyadicNode L) m) :
    stateHazardEnergy a x 0 = 1 / (m : ℝ) ^ 2 := by
  rw [stateHazardEnergy, hazardEnergy_root]
  change (HierarchicalPolicy.hazard (aggregatedInventory x) a 0 dyadicRoot) ^ 2 =
    1 / (m : ℝ) ^ 2
  rw [HierarchicalPolicy.hazard_root]
  ring

theorem stateHazardEnergy_root_le
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m) :
    1 / (m : ℝ) ^ 2 ≤ stateHazardEnergy a x L := by
  rw [← stateHazardEnergy_root a x]
  exact stateHazardEnergy_mono_to_depth a ha x (Nat.zero_le L) le_rfl

/-- A canonical witness that the fixed-total count state space is nonempty. -/
def concentratedInventory (L m : ℕ) :
    InventoryState (DyadicNode L) m :=
  ⟨fun i => if i = 0 then m else 0, by simp⟩

instance inventoryStateNonempty (L m : ℕ) :
    Nonempty (InventoryState (DyadicNode L) m) :=
  ⟨concentratedInventory L m⟩

private theorem expect_scaled_hazard_sub
    {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (a c : ℝ) (H : α → ℝ) :
    μ.expect (fun x => a * (H x / 100 - c)) =
      a / 100 * μ.expect H - a * c := by
  calc
    μ.expect (fun x => a * (H x / 100 - c)) =
        μ.expect (fun x => a / 100 * H x - a * c) := by
          apply congrArg μ.expect
          funext x
          ring
    _ = μ.expect (fun x => a / 100 * H x) -
          μ.expect (fun _ => a * c) := μ.expect_sub _ _
    _ = a / 100 * μ.expect H - a * c := by
          rw [μ.expect_const_mul, μ.expect_const]

private theorem expect_depth_mul
    {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (depth : ℝ) (H : α → ℝ) :
    μ.expect (fun x => depth * H x) = depth * μ.expect H :=
  μ.expect_const_mul depth H

/--
Equation (11) for an actual stationary law of the concrete hierarchical
count kernel.
-/
theorem stationary_expected_hazard_bound
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (haL : 200 * (L : ℝ) ≤ a)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hμ : (kernel a ha hm).IsStationary μ) :
    μ.expect (fun x => stateHazardEnergy a x L) ≤
      206 / (3 * (m : ℝ) ^ 2) := by
  let H : ℝ := μ.expect (fun x => stateHazardEnergy a x L)
  have hH : 0 ≤ H :=
    μ.expect_nonneg (fun x => stateHazardEnergy_nonneg a x L)
  have hstationary :
      ∀ y, ∑ x, μ.mass x * kernel a ha hm x y = μ.mass y := by
    intro y
    have hy := congrArg
      (fun ν : FiniteLaw (InventoryState (DyadicNode L) m) => ν.mass y) hμ
    simpa only [FiniteKernel.mass_step] using hy
  have hDR :
      μ.expect (stateDrift a) = μ.expect (stateRemainder a) :=
    stationary_expect_drift_eq_remainder μ (kernel a ha hm)
      (statePotential a) (stateDrift a) (stateRemainder a)
      (kernel a ha hm).sum_trans hstationary
      (kernel_drift_eq_stateDrift_sub_stateRemainder a ha hm)
  have hD :
      a / 100 * H - 103 * a / (300 * (m : ℝ) ^ 2) ≤
        μ.expect (stateDrift a) := by
    calc
      a / 100 * H - 103 * a / (300 * (m : ℝ) ^ 2) =
          μ.expect (fun x =>
            a * (stateHazardEnergy a x L / 100 -
              103 / (300 * (m : ℝ) ^ 2))) := by
            rw [expect_scaled_hazard_sub]
            dsimp [H]
            ring
      _ ≤ μ.expect (stateDrift a) :=
        μ.expect_mono (stateDrift_lower_bound a ha hm)
  have hR :
      μ.expect (stateRemainder a) ≤ (L : ℝ) * H := by
    calc
      μ.expect (stateRemainder a) ≤
          μ.expect (fun x => (L : ℝ) * stateHazardEnergy a x L) := by
            apply μ.expect_mono
            intro x
            exact (stateRemainder_bounds a ha hm x).2.1.trans
              (stateRemainder_bounds a ha hm x).2.2
      _ = (L : ℝ) * H := by
            rw [expect_depth_mul]
  have hmain :
      (a / 100 - (L : ℝ)) * H ≤
        103 * a / (300 * (m : ℝ) ^ 2) := by
    rw [hDR] at hD
    linarith
  exact stationary_hazard_bound ha (by exact_mod_cast hm)
    (Nat.cast_nonneg L) hH haL hmain

/-- The concrete count chain has a unique stationary law. -/
theorem existsUnique_stationaryLaw
    (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    ∃! μ : FiniteLaw (InventoryState (DyadicNode L) m),
      (kernel a ha hm).IsStationary μ := by
  obtain ⟨μ, hμ⟩ :=
    (kernel (L := L) a ha hm).exists_stationary
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  exact FiniteKernel.stationary_unique
    (kernel_irreducible (L := L) a ha hm) hν hμ

/--
Equation (12) for the actual kernel iterates, from an arbitrary initial count
law.  No invariance assumption is needed for this potential estimate.
-/
theorem finite_average_expected_hazard_bound
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (haL : 200 * (L : ℝ) ≤ a)
    (hlogA : 200 * Real.log (1 + (m : ℝ) / a) ≤ a)
    (μ₀ : FiniteLaw (InventoryState (DyadicNode L) m))
    (T : ℕ) (hT : 0 < T) :
    (∑ t ∈ Finset.range T,
        ((kernel a ha hm).iterate t μ₀).expect
          (fun x => stateHazardEnergy a x L)) / (T : ℝ) ≤
      206 / (3 * (m : ℝ) ^ 2) + 1 / (T : ℝ) := by
  let K : FiniteKernel (InventoryState (DyadicNode L) m) :=
    kernel (L := L) a ha hm
  let μt : ℕ → FiniteLaw (InventoryState (DyadicNode L) m) :=
    fun t => K.iterate t μ₀
  let Phi : ℕ → ℝ := fun t => (μt t).expect (statePotential a)
  let D : ℕ → ℝ := fun t => (μt t).expect (stateDrift a)
  let R : ℕ → ℝ := fun t => (μt t).expect (stateRemainder a)
  let H : ℕ → ℝ := fun t =>
    (μt t).expect (fun x => stateHazardEnergy a x L)
  have hdrift : ∀ t < T, Phi (t + 1) - Phi t = D t - R t := by
    intro t _
    calc
      Phi (t + 1) - Phi t =
          (μt t).expect (fun x =>
            ∑ y, K x y * (statePotential a y - statePotential a x)) := by
              simpa [Phi, μt] using
                K.expect_iterate_succ μ₀ t (statePotential a)
      _ = (μt t).expect
          (fun x => stateDrift a x - stateRemainder a x) := by
            apply congrArg (μt t).expect
            funext x
            exact kernel_drift_eq_stateDrift_sub_stateRemainder a ha hm x
      _ = D t - R t := by
            rw [(μt t).expect_sub]
  have hD : ∀ t < T,
      a * (H t / 100 - 103 / (300 * (m : ℝ) ^ 2)) ≤ D t := by
    intro t _
    calc
      a * (H t / 100 - 103 / (300 * (m : ℝ) ^ 2)) =
          (μt t).expect (fun x =>
            a * (stateHazardEnergy a x L / 100 -
              103 / (300 * (m : ℝ) ^ 2))) := by
                rw [expect_scaled_hazard_sub]
                dsimp [H]
                ring
      _ ≤ D t := by
            dsimp [D]
            exact (μt t).expect_mono (stateDrift_lower_bound a ha hm)
  have hR : ∀ t < T, R t ≤ (L : ℝ) * H t := by
    intro t _
    calc
      R t ≤ (μt t).expect
          (fun x => (L : ℝ) * stateHazardEnergy a x L) := by
            dsimp [R]
            apply (μt t).expect_mono
            intro x
            exact (stateRemainder_bounds a ha hm x).2.1.trans
              (stateRemainder_bounds a ha hm x).2.2
      _ = (L : ℝ) * H t := by
            rw [expect_depth_mul]
  have hPhi0 : 0 ≤ Phi 0 := by
    dsimp [Phi]
    exact (μt 0).expect_nonneg (statePotential_nonneg a ha)
  have hPhiT : Phi T ≤ Real.log (1 + (m : ℝ) / a) := by
    calc
      Phi T ≤ (μt T).expect
          (fun _ => Real.log (1 + (m : ℝ) / a)) := by
            dsimp [Phi]
            exact (μt T).expect_mono (statePotential_le_log_one_add a ha)
      _ = Real.log (1 + (m : ℝ) / a) := (μt T).expect_const _
  have hmain :
      (a / 100 - (L : ℝ)) *
          ((∑ t ∈ Finset.range T, H t) / (T : ℝ)) ≤
        a * (103 / (300 * (m : ℝ) ^ 2)) +
          Real.log (1 + (m : ℝ) / a) / (T : ℝ) :=
    finite_time_hazard_drift_inequality Phi D R H hT hdrift hD hR
      hPhi0 hPhiT
  have hmain' :
      (a / 100 - (L : ℝ)) *
          ((∑ t ∈ Finset.range T, H t) / (T : ℝ)) ≤
        103 * a / (300 * (m : ℝ) ^ 2) +
          Real.log (1 + (m : ℝ) / a) / (T : ℝ) := by
    convert hmain using 1 <;> ring
  have hHave : 0 ≤ (∑ t ∈ Finset.range T, H t) / (T : ℝ) := by
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro t _
      exact (μt t).expect_nonneg
        (fun x => stateHazardEnergy_nonneg a x L)
    · positivity
  have hlog : 0 ≤ Real.log (1 + (m : ℝ) / a) := by
    apply Real.log_nonneg
    have : 0 ≤ (m : ℝ) / a := div_nonneg (Nat.cast_nonneg m) ha.le
    linarith
  have hbound := transient_hazard_bound
    (a := a) (L := (L : ℝ)) (m := (m : ℝ)) (T := (T : ℝ))
    (H := (∑ t ∈ Finset.range T, H t) / (T : ℝ))
    (logTerm := Real.log (1 + (m : ℝ) / a))
    ha (by exact_mod_cast hm) (by exact_mod_cast hT)
    (Nat.cast_nonneg L) hHave hlog haL hlogA hmain'
  simpa [H, μt, K] using hbound

end HierarchicalDynamics

end

end FD1D
