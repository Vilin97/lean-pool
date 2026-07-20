/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.NesterovSeqGen
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.Step1

/-!
# Auxiliary Variable Recursion for Arbitrary States

The one-step recursion for the auxiliary variable u, proved for arbitrary
NesterovState (not just nesterovSeq-reachable states). This is the
state-based analogue of `auxVar_recursion` from AuxVar.lean.

Key identity: u' = ((1-a)·P⊥v + √μ'·e - √η·P⊥g) + √μ'·ξ
where u' = auxVarOfState at step(s), and all quantities are computed from s.
-/

noncomputable section

namespace PLAcceleratedNesterovLean
open scoped Topology NNReal
open Manifold

variable {d : ℕ}

-- Helper: the velocity of a stepped state
private theorem nesterovStep_v (f : E d → ℝ) (η ρ : ℝ) (s : NesterovState d) :
    (nesterovStep f η ρ s).v = ρ • (s.v - Real.sqrt η • gradient f (s.lookahead η)) := by
  simp [nesterovStep]

-- Helper: the position of a stepped state
private theorem nesterovStep_x (f : E d → ℝ) (η ρ : ℝ) (s : NesterovState d) :
    (nesterovStep f η ρ s).x = s.lookahead η - η • gradient f (s.lookahead η) := by
  simp [nesterovStep]

/-- Step displacement formula: h = ρ·√η·v - (1+ρ)·η·g -/
theorem stepDispOfState_eq (f : E d → ℝ) (η ρ : ℝ) (s : NesterovState d)
    (hη_pos : 0 < η) :
    stepDispOfState f η ρ s =
    ρ • Real.sqrt η • s.v - (1 + ρ) • η • gradient f (s.lookahead η) := by
  have hsq : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt (le_of_lt hη_pos)
  simp only [stepDispOfState, NesterovState.lookahead, nesterovStep_x, nesterovStep_v]
  have : Real.sqrt η • (ρ • (s.v - Real.sqrt η • gradient f (s.lookahead η))) =
      ρ • (Real.sqrt η • s.v - η • gradient f (s.lookahead η)) := by
    rw [smul_comm, smul_sub, ← mul_smul, hsq]
  simp only [NesterovState.lookahead] at this ⊢
  rw [this]; module

/-- One-step auxVar recursion for arbitrary states. -/
theorem auxVarOfState_step (P : E d →L[ℝ] E d) (μ' η ρ : ℝ) (π : E d → E d)
    (f : E d → ℝ) (s : NesterovState d)
    (hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    (ha_pos : 0 < Real.sqrt (μ' * η))
    (hη_pos : 0 < η)
    (hμ_pos : 0 < μ') :
    let gn := gradient f (s.lookahead η)
    let en := normalDispOfState π η s
    let ξn := curvatureErrorOfState (↑P) π f η ρ s
    let a := Real.sqrt (μ' * η)
    auxVarOfState P μ' π η (nesterovStep f η ρ s) =
    ((1 - a) • (s.v - P s.v) + Real.sqrt μ' • en -
     Real.sqrt η • (gn - P gn)) + Real.sqrt μ' • ξn := by
  simp only
  -- Key scalar identities
  have hsq : Real.sqrt η * Real.sqrt η = η :=
    Real.mul_self_sqrt (le_of_lt hη_pos)
  have h1a : (0 : ℝ) < 1 + Real.sqrt (μ' * η) := by linarith
  have h_rho_id : (1 + Real.sqrt (μ' * η)) * ρ = 1 - Real.sqrt (μ' * η) :=
    rho_identity (Real.sqrt (μ' * η)) ρ h1a.ne' hρ
  have h_sqrt_prod : Real.sqrt μ' * Real.sqrt η = Real.sqrt (μ' * η) := by
    rw [← Real.sqrt_mul (le_of_lt hμ_pos)]
  -- Abbreviations
  set a := Real.sqrt (μ' * η) with ha_def
  set gn := gradient f (s.lookahead η)
  set en := normalDispOfState π η s
  -- Fact A: velocity of nesterovStep unfolds to ρ·(v - √η·g)
  have hA : auxVarOfState P μ' π η (nesterovStep f η ρ s) =
      ρ • ((s.v - P s.v) - Real.sqrt η • (gn - P gn)) +
      Real.sqrt μ' • normalDispOfState π η (nesterovStep f η ρ s) := by
    unfold auxVarOfState
    rw [nesterovStep_v]
    rw [show (ρ • (s.v - Real.sqrt η • gn) - P (ρ • (s.v - Real.sqrt η • gn))) =
        ρ • ((s.v - P s.v) - Real.sqrt η • (gn - P gn)) from by
      rw [map_smul, map_sub, map_smul]; module]
  -- Fact B: normalDispOfState at s' = en + (h - Ph) + ξ
  have hB : normalDispOfState π η (nesterovStep f η ρ s) =
      en + (stepDispOfState f η ρ s - P (stepDispOfState f η ρ s)) +
      curvatureErrorOfState (↑P) π f η ρ s := by
    -- Unfold en and curvatureErrorOfState for consistent atoms
    change normalDispOfState π η (nesterovStep f η ρ s) =
      normalDispOfState π η s +
      (stepDispOfState f η ρ s - P (stepDispOfState f η ρ s)) +
      curvatureErrorOfState (↑P) π f η ρ s
    simp only [curvatureErrorOfState, stepDispOfState]
    abel
  -- Fact C: h - Ph = ρ·√η·P⊥v - (1+ρ)·η·P⊥g
  have hC : stepDispOfState f η ρ s - P (stepDispOfState f η ρ s) =
      ρ • Real.sqrt η • (s.v - P s.v) -
      (1 + ρ) • η • (gn - P gn) := by
    rw [stepDispOfState_eq f η ρ s hη_pos,
      map_sub, map_smul, map_smul, map_smul, map_smul]; module
  -- Combine
  rw [hA, hB, hC]
  set pv := s.v - P s.v
  set pg := gn - P gn
  set ξ := curvatureErrorOfState (↑P) π f η ρ s
  -- Distribute ρ • (pv - √η • pg) = ρ • pv - (ρ * √η) • pg
  rw [show ρ • (pv - Real.sqrt η • pg) = ρ • pv - (ρ * Real.sqrt η) • pg from by
    rw [smul_sub, smul_smul]]
  -- Distribute √μ' • (en + (ρ • √η • pv - (1+ρ) • η • pg) + ξ)
  rw [smul_add, smul_add]
  -- Distribute √μ' • (ρ • √η • pv - (1+ρ) • η • pg)
  rw [show Real.sqrt μ' • (ρ • Real.sqrt η • pv - (1 + ρ) • η • pg) =
      (Real.sqrt μ' * ρ * Real.sqrt η) • pv - (Real.sqrt μ' * (1 + ρ) * η) • pg from by
    rw [smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]]
  -- Coefficient check: ρ + √μ'·ρ·√η = 1-a
  have hpv_coeff : ρ + Real.sqrt μ' * ρ * Real.sqrt η = 1 - a := by
    have : Real.sqrt μ' * ρ * Real.sqrt η = ρ * a := by
      have := h_sqrt_prod; nlinarith
    linarith [h_rho_id]
  -- Coefficient check: ρ·√η + √μ'·(1+ρ)·η = √η
  have hpg_coeff : ρ * Real.sqrt η + Real.sqrt μ' * (1 + ρ) * η = Real.sqrt η := by
    have hcoeff : ρ + (1 + ρ) * a = 1 := by nlinarith [h_rho_id]
    have h_prod : Real.sqrt μ' * (1 + ρ) * η = (1 + ρ) * a * Real.sqrt η := by
      conv_lhs => rw [show η = Real.sqrt η * Real.sqrt η from hsq.symm]
      rw [show Real.sqrt μ' * (1 + ρ) * (Real.sqrt η * Real.sqrt η) =
          (1 + ρ) * (Real.sqrt μ' * Real.sqrt η) * Real.sqrt η from by ring,
        h_sqrt_prod]
    rw [h_prod, show ρ * Real.sqrt η + (1 + ρ) * a * Real.sqrt η =
        (ρ + (1 + ρ) * a) * Real.sqrt η from by ring, hcoeff, one_mul]
  -- Collect pv and pg coefficients
  rw [show ρ • pv - (ρ * Real.sqrt η) • pg +
      (Real.sqrt μ' • en + ((Real.sqrt μ' * ρ * Real.sqrt η) • pv -
      (Real.sqrt μ' * (1 + ρ) * η) • pg) + Real.sqrt μ' • ξ) =
      (ρ • pv + (Real.sqrt μ' * ρ * Real.sqrt η) • pv) + Real.sqrt μ' • en -
      ((ρ * Real.sqrt η) • pg + (Real.sqrt μ' * (1 + ρ) * η) • pg) +
      Real.sqrt μ' • ξ from by abel,
    ← add_smul, ← add_smul, hpv_coeff, hpg_coeff]

end PLAcceleratedNesterovLean
