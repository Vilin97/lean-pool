/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.SquaredCost
import LeanPool.FullyDynamicMatching.FD1D.V5.Parameters
import LeanPool.FullyDynamicMatching.FD1D.FiniteConvergence

/-!
# RMS matching-cost bounds for the v5 count chain

This module combines the v5 energy estimates with squared quantile transport,
discharges the parameter arithmetic, and records stationary, transient, and
ordinary-convergence bounds for the count-state cost envelope.
-/

namespace FD1D.V5

noncomputable section

open Filter
open MeasureTheory
open scoped BigOperators Topology

variable {L m : ℕ}

namespace Transport

/--
RMS transport for a uniform mixture of finite count laws.  Each law may be
different, but each must retain the child-subtree swap symmetries.
-/
theorem sqrt_average_stateSquaredCostEnvelope_le
    (a : ℝ) (mu : ℕ → FiniteLaw (InventoryState (DyadicNode L) m))
    (T : ℕ) (hT : 0 < T)
    (hinv : ∀ t (d : Fin L) (v : DyadicNode d.val),
      FiniteKernel.LawInvariant (mu t)
        (FD1D.TreeSymmetry.inventorySwap d.isLt v)) :
    Real.sqrt
        ((∑ t ∈ Finset.range T,
            (mu t).expect (stateSquaredCostEnvelope a)) / (T : ℝ)) ≤
      dyadicCellWidth L +
        Real.sqrt
          ((1 / 12) *
            ((∑ t ∈ Finset.range T,
              (mu t).expect (Dynamics.stateTransportEnergy a)) /
                (T : ℝ))) := by
  let nu : FiniteLaw
      (Fin T × InventoryState (DyadicNode L) m) :=
    FiniteLaw.timeAverage hT (fun t : Fin T => mu t)
  let H : InventoryState (DyadicNode L) m → ℝ := fun x =>
    haarL2 (haarNodeLeft (L := L)) (haarNodeWidth (L := L))
      (stateHaarCoefficient a x)
  let w : ℝ := dyadicCellWidth L
  have hw : 0 ≤ w := (dyadicCellWidth_pos L).le
  have hH (z : Fin T × InventoryState (DyadicNode L) m) :
      0 ≤ H z.2 := by
    unfold H haarL2
    exact integral_nonneg fun _ => sq_nonneg _
  have halgebra :
      Real.sqrt
          (nu.expect (fun z => stateSquaredCostEnvelope a z.2)) ≤
        w + Real.sqrt (nu.expect (fun z => H z.2)) := by
    change Real.sqrt
        (nu.expect (fun z => (w + Real.sqrt (H z.2)) ^ 2)) ≤
      w + Real.sqrt (nu.expect (fun z => H z.2))
    exact sqrt_expect_add_sqrt_sq_le nu w hw (fun z => H z.2) hH
  have henvelope :
      nu.expect (fun z => stateSquaredCostEnvelope a z.2) =
        (∑ t ∈ Finset.range T,
          (mu t).expect (stateSquaredCostEnvelope a)) / (T : ℝ) := by
    simpa [nu] using
      FiniteLaw.expect_timeAverage_state hT mu
        (stateSquaredCostEnvelope a)
  have hhaarAverage :
      nu.expect (fun z => H z.2) =
        (∑ t ∈ Finset.range T, (mu t).expect H) / (T : ℝ) := by
    simpa [nu] using FiniteLaw.expect_timeAverage_state hT mu H
  have hsum :
      (∑ t ∈ Finset.range T, (mu t).expect H) =
        (1 / 12) *
          ∑ t ∈ Finset.range T,
            (mu t).expect (Dynamics.stateTransportEnergy a) := by
    calc
      (∑ t ∈ Finset.range T, (mu t).expect H) =
          ∑ t ∈ Finset.range T,
            (1 / 12) *
              (mu t).expect (Dynamics.stateTransportEnergy a) := by
        apply Finset.sum_congr rfl
        intro t ht
        have h :=
          expected_haarL2_eq_transportEnergy a (mu t) (hinv t)
        change (mu t).expect H =
          (1 / 12) * (mu t).expect
            (Dynamics.stateTransportEnergy a) at h
        exact h
      _ = _ := by rw [Finset.mul_sum]
  rw [henvelope, hhaarAverage, hsum] at halgebra
  dsimp only [w] at halgebra
  convert halgebra using 1 <;> ring

end Transport

/-! ## Parameterized count chain -/

def parameterizedKernel (m : ℕ) (hm : 1 ≤ m) :
    FiniteKernel
      (InventoryState (DyadicNode (treeDepth m)) m) :=
  Dynamics.kernel
    (L := treeDepth m) (parameterA m : ℝ)
    (parameterA_cast_pos hm) (by omega)

def parameterizedTransportEnergy (m : ℕ)
    (x : InventoryState (DyadicNode (treeDepth m)) m) : ℝ :=
  Dynamics.stateTransportEnergy (parameterA m : ℝ) x

def parameterizedSquaredCostEnvelope (m : ℕ)
    (x : InventoryState (DyadicNode (treeDepth m)) m) : ℝ :=
  Transport.stateSquaredCostEnvelope (parameterA m : ℝ) x

def refreshedIterate (m : ℕ) (hm : 1 ≤ m) (t : ℕ) :
    FiniteLaw
      (InventoryState (DyadicNode (treeDepth m)) m) :=
  (parameterizedKernel m hm).iterate t
    (refreshedLaw (treeDepth m) m)

theorem parameterizedKernel_irreducible
    {m : ℕ} (hm : 1 ≤ m) :
    (parameterizedKernel m hm).Irreducible := by
  simpa [parameterizedKernel] using
    Dynamics.kernel_irreducible
      (L := treeDepth m) (m := m)
      (parameterA m : ℝ) (parameterA_cast_pos hm) (by omega)

theorem parameterizedKernel_hasPositiveLoops
    {m : ℕ} (hm : 1 ≤ m) :
    (parameterizedKernel m hm).HasPositiveLoops := by
  simpa [parameterizedKernel] using
    Dynamics.kernel_hasPositiveLoops
      (L := treeDepth m) (m := m)
      (parameterA m : ℝ) (parameterA_cast_pos hm) (by omega)

private theorem stationary_sqrt_energy_le
    {a m G : ℝ} (ha : 0 < a) (hm : 0 < m)
    (hG : G ≤ 501 * a ^ 2 / m ^ 2) :
    Real.sqrt ((1 / 12) * G) ≤ (13 / 2) * a / m := by
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · calc
      (1 / 12) * G ≤
          (1 / 12) * (501 * a ^ 2 / m ^ 2) := by
        gcongr
      _ ≤ ((13 / 2) * a / m) ^ 2 := by
        field_simp [hm.ne']
        nlinarith [sq_nonneg a]

/-- The stationary count-state RMS envelope is strictly below `8.5 a/m`. -/
theorem stationary_sqrt_expected_squaredCostEnvelope_le
    {m : ℕ} (hm : 1 ≤ m)
    (pi : FiniteLaw
      (InventoryState (DyadicNode (treeDepth m)) m))
    (hpi : (parameterizedKernel m hm).IsStationary pi) :
    Real.sqrt (pi.expect (parameterizedSquaredCostEnvelope m)) ≤
      (17 / 2) * (parameterA m : ℝ) / (m : ℝ) := by
  have hmpos : 0 < m := by omega
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have ha := parameterA_cast_pos hm
  have hpi' :
      (Dynamics.kernel
        (L := treeDepth m) (m := m)
        (parameterA m : ℝ) ha hmpos).IsStationary pi := by
    simpa [parameterizedKernel] using hpi
  have hinv :
      ∀ (d : Fin (treeDepth m)) (v : DyadicNode d.val),
        FiniteKernel.LawInvariant pi
          (FD1D.TreeSymmetry.inventorySwap d.isLt v) := by
    intro d v
    exact TreeSymmetry.stationary_lawInvariant
      d.isLt v (parameterA m : ℝ) ha hmpos hpi'
  have hrms :=
    Transport.sqrt_expected_stateSquaredCostEnvelope_le
      (parameterA m : ℝ) pi hinv
  have hG :
      pi.expect (Dynamics.stateTransportEnergy (parameterA m : ℝ)) ≤
        501 * (parameterA m : ℝ) ^ 2 / (m : ℝ) ^ 2 :=
    (Dynamics.stationary_energy_estimates
      (L := treeDepth m) (m := m)
      (parameterA m : ℝ) ha hmpos
      (parameterA_cast_ge_treeDepth hm) pi hpi').2
  have hsqrt :=
    stationary_sqrt_energy_le ha hmreal hG
  have hcell :
      dyadicCellWidth (treeDepth m) ≤
        2 * (parameterA m : ℝ) / (m : ℝ) := by
    simpa [dyadicCellWidth, leafCount] using
      one_div_leafCount_le_two_mul_parameterA_div hm
  change
    Real.sqrt
        (pi.expect
          (Transport.stateSquaredCostEnvelope (parameterA m : ℝ))) ≤ _
  calc
    Real.sqrt
        (pi.expect
          (Transport.stateSquaredCostEnvelope (parameterA m : ℝ))) ≤
        dyadicCellWidth (treeDepth m) +
          Real.sqrt ((1 / 12) *
            pi.expect
              (Dynamics.stateTransportEnergy (parameterA m : ℝ))) :=
      hrms
    _ ≤ 2 * (parameterA m : ℝ) / (m : ℝ) +
        (13 / 2) * (parameterA m : ℝ) / (m : ℝ) :=
      add_le_add hcell hsqrt
    _ = (17 / 2) * (parameterA m : ℝ) / (m : ℝ) := by ring

/-- The refreshed transient average RMS envelope is at most `8.5 a/m`. -/
theorem refreshed_average_rms_squaredCostEnvelope_le
    {m T : ℕ} (hm : 1 ≤ m) (hT : m ^ 2 ≤ T) :
    Real.sqrt
        ((∑ t ∈ Finset.range T,
            (refreshedIterate m hm t).expect
              (parameterizedSquaredCostEnvelope m)) / (T : ℝ)) ≤
      (17 / 2) * (parameterA m : ℝ) / (m : ℝ) := by
  have hmpos : 0 < m := by omega
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hTpos : 0 < T := by
    have : 0 < m ^ 2 := pow_pos hmpos 2
    omega
  have hTreal : (m : ℝ) ^ 2 ≤ (T : ℝ) := by
    exact_mod_cast hT
  have ha := parameterA_cast_pos hm
  have hrms :=
    Transport.sqrt_average_stateSquaredCostEnvelope_le
      (L := treeDepth m) (m := m)
      (parameterA m : ℝ) (refreshedIterate m hm) T hTpos
      (by
        intro t d v
        simpa [refreshedIterate, parameterizedKernel] using
          Transport.iterate_refreshedLaw_lawInvariant
            (L := treeDepth m) (m := m)
            (parameterA m : ℝ) ha hmpos t d v)
  have hG :
      (∑ t ∈ Finset.range T,
          (refreshedIterate m hm t).expect
            (parameterizedTransportEnergy m)) / (T : ℝ) ≤
        501 * (parameterA m : ℝ) ^ 2 / (m : ℝ) ^ 2 +
          (parameterA m : ℝ) ^ 2 / (2 * (T : ℝ)) := by
    change
      (∑ t ∈ Finset.range T,
          ((Dynamics.kernel
            (L := treeDepth m) (m := m)
            (parameterA m : ℝ) ha hmpos).iterate t
              (refreshedLaw (treeDepth m) m)).expect
                (Dynamics.stateTransportEnergy
                  (parameterA m : ℝ))) / (T : ℝ) ≤ _
    exact
      Dynamics.finite_transport_energy_estimate
        (L := treeDepth m) (m := m)
        (parameterA m : ℝ) ha hmpos
        (parameterA_cast_ge_treeDepth hm)
        (log_one_add_two_mul_div_le_parameterA_div_two_thousand hm)
        (refreshedLaw (treeDepth m) m) T hTpos
  have hsqrt :
      Real.sqrt
          ((1 / 12) *
            ((∑ t ∈ Finset.range T,
              (refreshedIterate m hm t).expect
                (parameterizedTransportEnergy m)) / (T : ℝ))) ≤
        (13 / 2) * (parameterA m : ℝ) / (m : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · calc
        (1 / 12) *
            ((∑ t ∈ Finset.range T,
              (refreshedIterate m hm t).expect
                (parameterizedTransportEnergy m)) / (T : ℝ)) ≤
            (1 / 12) *
              (501 * (parameterA m : ℝ) ^ 2 / (m : ℝ) ^ 2 +
                (parameterA m : ℝ) ^ 2 / (2 * (T : ℝ))) := by
          gcongr
        _ ≤ (1 / 12) *
              (501 * (parameterA m : ℝ) ^ 2 / (m : ℝ) ^ 2 +
                (parameterA m : ℝ) ^ 2 /
                  (2 * (m : ℝ) ^ 2)) := by
          gcongr
        _ ≤ ((13 / 2) * (parameterA m : ℝ) / (m : ℝ)) ^ 2 := by
          field_simp [hmreal.ne']
          nlinarith [sq_nonneg (parameterA m : ℝ)]
  have hcell :
      dyadicCellWidth (treeDepth m) ≤
        2 * (parameterA m : ℝ) / (m : ℝ) := by
    simpa [dyadicCellWidth, leafCount] using
      one_div_leafCount_le_two_mul_parameterA_div hm
  change
    Real.sqrt
        ((∑ t ∈ Finset.range T,
          (refreshedIterate m hm t).expect
            (Transport.stateSquaredCostEnvelope
              (parameterA m : ℝ))) / (T : ℝ)) ≤ _
  calc
    Real.sqrt
        ((∑ t ∈ Finset.range T,
          (refreshedIterate m hm t).expect
            (Transport.stateSquaredCostEnvelope
              (parameterA m : ℝ))) / (T : ℝ)) ≤
        dyadicCellWidth (treeDepth m) +
          Real.sqrt
            ((1 / 12) *
              ((∑ t ∈ Finset.range T,
                (refreshedIterate m hm t).expect
                  (Dynamics.stateTransportEnergy
                    (parameterA m : ℝ))) / (T : ℝ))) :=
      hrms
    _ ≤ 2 * (parameterA m : ℝ) / (m : ℝ) +
        (13 / 2) * (parameterA m : ℝ) / (m : ℝ) := by
      apply add_le_add hcell
      change
        Real.sqrt
            ((1 / 12) *
              ((∑ t ∈ Finset.range T,
                (refreshedIterate m hm t).expect
                  (Dynamics.stateTransportEnergy
                    (parameterA m : ℝ))) / (T : ℝ))) ≤
          (13 / 2) * (parameterA m : ℝ) / (m : ℝ) at hsqrt
      exact hsqrt
    _ = (17 / 2) * (parameterA m : ℝ) / (m : ℝ) := by ring

/-! ## Ordinary convergence from arbitrary count laws -/

def rmsSquaredCostExpectation
    (m : ℕ) (hm : 1 ≤ m)
    (mu0 : FiniteLaw
      (InventoryState (DyadicNode (treeDepth m)) m))
    (t : ℕ) : ℝ :=
  Real.sqrt
    (((parameterizedKernel m hm).iterate t mu0).expect
      (parameterizedSquaredCostEnvelope m))

theorem exists_stationary_rmsSquaredCost_tendsto
    {m : ℕ} (hm : 1 ≤ m)
    (mu0 : FiniteLaw
      (InventoryState (DyadicNode (treeDepth m)) m)) :
    ∃ pi : FiniteLaw
        (InventoryState (DyadicNode (treeDepth m)) m),
      (parameterizedKernel m hm).IsStationary pi ∧
      Tendsto (rmsSquaredCostExpectation m hm mu0) atTop
        (nhds (Real.sqrt
          (pi.expect (parameterizedSquaredCostEnvelope m)))) ∧
      Real.sqrt (pi.expect (parameterizedSquaredCostEnvelope m)) ≤
        (17 / 2) * (parameterA m : ℝ) / (m : ℝ) := by
  obtain ⟨pi, hpi⟩ := (parameterizedKernel m hm).exists_stationary
  have hconv :=
    FiniteKernel.tendsto_expect_iterate
      (parameterizedKernel m hm)
      (parameterizedKernel_irreducible hm)
      (parameterizedKernel_hasPositiveLoops hm)
      pi hpi mu0 (parameterizedSquaredCostEnvelope m)
  refine ⟨pi, hpi, ?_, stationary_sqrt_expected_squaredCostEnvelope_le hm pi hpi⟩
  exact Real.continuous_sqrt.continuousAt.tendsto.comp hconv

theorem limsup_rmsSquaredCostExpectation_le
    {m : ℕ} (hm : 1 ≤ m)
    (mu0 : FiniteLaw
      (InventoryState (DyadicNode (treeDepth m)) m)) :
    Filter.limsup (rmsSquaredCostExpectation m hm mu0) atTop ≤
      (17 / 2) * (parameterA m : ℝ) / (m : ℝ) := by
  obtain ⟨pi, _hpi, hconv, hbound⟩ :=
    exists_stationary_rmsSquaredCost_tendsto hm mu0
  rw [hconv.limsup_eq]
  exact hbound

end

end FD1D.V5
