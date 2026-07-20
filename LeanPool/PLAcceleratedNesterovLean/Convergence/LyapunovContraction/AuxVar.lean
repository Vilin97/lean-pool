/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.Step1

/-!
# Auxiliary Variable Recursion for Lyapunov Contraction

Establishes the one-step recursion for the auxiliary variable in the Nesterov
accelerated gradient method, decomposing the update into perpendicular
velocity, normal displacement, and curvature error components.
-/

noncomputable section

namespace PLAcceleratedNesterovLean
open scoped Topology NNReal
open Manifold

variable {d : ℕ}

theorem auxVar_recursion (P : E d →L[ℝ] E d) (μ' η ρ : ℝ) (π : E d → E d)
    (f : E d → ℝ) (x₁ : E d) (n : ℕ)
    (hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    (ha_pos : 0 < Real.sqrt (μ' * η))
    (hη_pos : 0 < η)
    (hμ_pos : 0 < μ') :
    let sn := nesterovSeq f η ρ x₁ n
    let gn := gradient f (sn.lookahead η)
    let en := normalDisp π f η ρ x₁ n
    let ξn := curvatureError (↑P) π f η ρ x₁ n
    let a := Real.sqrt (μ' * η)
    auxVar P μ' π f η ρ x₁ (n + 1) =
    ((1 - a) • (sn.v - P sn.v) + Real.sqrt μ' • en -
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
  -- Abbreviation
  set a := Real.sqrt (μ' * η) with ha_def
  set sn := nesterovSeq f η ρ x₁ n with hsn
  set gn := gradient f (sn.lookahead η) with hgn
  set en := normalDisp π f η ρ x₁ n with hen
  -- Rewrite the target using an intermediate "wn + √μ'•ξn" form
  -- where wn involves the perpendicular components.
  -- Strategy: express everything in terms of sn.v, P sn.v, gn, P gn, en, ξn
  -- by unfolding auxVar/curvatureError/normalDisp/nesterovH/nesterovStep

  -- LHS unfolds to:
  --   (ρ•(sn.v - √η•gn) - P(ρ•(sn.v - √η•gn)))
  --   + √μ' • (x'_{n+1} - π(x'_{n+1}))
  -- = ρ•(sn.v - P sn.v - √η•(gn - P gn))  + √μ'•en1

  -- And en1 (= normalDisp(n+1)) = en + (hn - P hn) + ξn  by curvatureError def
  -- where hn = ρ•√η•sn.v - (1+ρ)•η•gn

  -- So LHS = ρ•(P⊥v - √η•P⊥g)
  --        + √μ'•en + √μ'•(ρ•√η•P⊥v - (1+ρ)•η•P⊥g) + √μ'•ξn
  -- = (ρ + √μ'•ρ•√η)•P⊥v + √μ'•en - (ρ•√η + √μ'•(1+ρ)•η)•P⊥g + √μ'•ξn
  -- = (1-a)•P⊥v + √μ'•en - √η•P⊥g + √μ'•ξn   [using coefficient identities]
  -- = RHS  ✓

  -- For the proof, I'll compute an explicit chain:

  -- Fact A: auxVar at (n+1) unfolds
  have hA : auxVar P μ' π f η ρ x₁ (n + 1) =
      ρ • ((sn.v - P sn.v) - Real.sqrt η • (gn - P gn)) +
      Real.sqrt μ' • normalDisp π f η ρ x₁ (n + 1) := by
    change (ρ • (sn.v - Real.sqrt η • gn) - P (ρ • (sn.v - Real.sqrt η • gn))) +
      Real.sqrt μ' • normalDisp π f η ρ x₁ (n + 1) = _
    rw [map_smul, map_sub, map_smul]; module
  -- Fact B: normalDisp(n+1) = en + (hn - P hn) + ξn
  have hB : normalDisp π f η ρ x₁ (n + 1) =
      en + (nesterovH f η ρ x₁ n - P (nesterovH f η ρ x₁ n)) +
      curvatureError (↑P) π f η ρ x₁ n := by
    simp only [curvatureError, hen]; module
  -- Fact C: hn - P hn = ρ•√η•P⊥v - (1+ρ)•η•P⊥g
  have hC : nesterovH f η ρ x₁ n - P (nesterovH f η ρ x₁ n) =
      ρ • Real.sqrt η • (sn.v - P sn.v) -
      (1 + ρ) • η • (gn - P gn) := by
    -- First expand hn
    have h_hn : nesterovH f η ρ x₁ n =
        ρ • Real.sqrt η • sn.v - (1 + ρ) • η • gn := by
      -- Expand hn directly without simp (to keep sn/gn abbreviations)
      change sn.x + Real.sqrt η • sn.v - η • gn +
          Real.sqrt η • (ρ • (sn.v - Real.sqrt η • gn)) - sn.lookahead η =
          ρ • Real.sqrt η • sn.v - (1 + ρ) • η • gn
      simp only [NesterovState.lookahead]
      have : Real.sqrt η • (ρ • (sn.v - Real.sqrt η • gn)) =
          ρ • (Real.sqrt η • sn.v - η • gn) := by
        rw [smul_comm, smul_sub, ← mul_smul, hsq]
      rw [this]; module
    rw [h_hn, map_sub, map_smul, map_smul, map_smul, map_smul]; module
  -- Now combine
  rw [hA, hB]
  -- Goal: ρ•(P⊥v - √η•P⊥g) + √μ'•(en + (hn-Phn) + ξn) =
  --       (1-a)•P⊥v + √μ'•en - √η•P⊥g + √μ'•ξn
  rw [hC]
  -- Goal: ρ•(P⊥v - √η•P⊥g) + √μ'•(en + (ρ•√η•P⊥v - (1+ρ)•η•P⊥g) + ξn) =
  --       (1-a)•P⊥v + √μ'•en - √η•P⊥g + √μ'•ξn

  -- Now collect terms. The key coefficient identities:
  -- P⊥v coefficient: ρ + √μ'·ρ·√η = ρ·(1 + a) = 1-a
  -- P⊥g coefficient: ρ·√η + √μ'·(1+ρ)·η = √η·(ρ + (1+ρ)·a) = √η

  -- We'll convert the LHS to match the RHS by showing coefficient equality
  -- Method: convert all nested smuls to explicit scalar coefficients,
  -- then verify coefficient identities

  -- Convert nested smuls
  -- √μ' • (ρ • √η • P⊥v) = (√μ' * ρ * √η) • P⊥v = (ρ * a) • P⊥v
  -- √μ' • ((1+ρ) • η • P⊥g) = (√μ' * (1+ρ) * η) • P⊥g

  -- We need a suffices that reduces to coefficient checking
  suffices h : ρ • ((sn.v - P sn.v) - Real.sqrt η • (gn - P gn)) +
      Real.sqrt μ' •
        (en + (ρ • Real.sqrt η • (sn.v - P sn.v) -
               (1 + ρ) • η • (gn - P gn)) +
         curvatureError (↑P) π f η ρ x₁ n) =
      (1 - a) • (sn.v - P sn.v) + Real.sqrt μ' • en -
      Real.sqrt η • (gn - P gn) + Real.sqrt μ' • curvatureError (↑P) π f η ρ x₁ n by
    exact h
  -- Now set the perpendicular components as atoms
  set pv := sn.v - P sn.v
  set pg := gn - P gn
  set ξ := curvatureError (↑P) π f η ρ x₁ n
  -- Distribute smul over addition and subtraction
  -- LHS = ρ•pv - ρ•√η•pg + √μ'•en + √μ'•ρ•√η•pv - √μ'•(1+ρ)•η•pg + √μ'•ξ
  -- = (ρ + √μ'·ρ·√η)•pv + √μ'•en - (ρ·√η + √μ'·(1+ρ)·η)•pg + √μ'•ξ

  -- Coefficient check: ρ + √μ'·ρ·√η = ρ(1 + a) = 1-a
  have hpv_coeff : ρ + Real.sqrt μ' * ρ * Real.sqrt η = 1 - a := by
    have : Real.sqrt μ' * ρ * Real.sqrt η = ρ * a := by
      have := h_sqrt_prod  -- √μ' * √η = a
      nlinarith
    linarith [h_rho_id]
  -- Coefficient check: ρ·√η + √μ'·(1+ρ)·η = √η
  have hpg_coeff : ρ * Real.sqrt η + Real.sqrt μ' * (1 + ρ) * η = Real.sqrt η := by
    have hη_eq : η = Real.sqrt η * Real.sqrt η := hsq.symm
    have hcoeff : ρ + (1 + ρ) * a = 1 := by nlinarith [h_rho_id]
    have h_prod : Real.sqrt μ' * (1 + ρ) * η = (1 + ρ) * a * Real.sqrt η := by
      have h1 : Real.sqrt μ' * Real.sqrt η = a := h_sqrt_prod
      have h2 : η = Real.sqrt η * Real.sqrt η := hsq.symm
      conv_lhs => rw [h2]
      rw [show Real.sqrt μ' * (1 + ρ) * (Real.sqrt η * Real.sqrt η) =
          (1 + ρ) * (Real.sqrt μ' * Real.sqrt η) * Real.sqrt η from by ring,
        h1]
    rw [h_prod]
    have : ρ * Real.sqrt η + (1 + ρ) * a * Real.sqrt η =
        (ρ + (1 + ρ) * a) * Real.sqrt η := by ring
    rw [this, hcoeff, one_mul]
  -- Now use these to convert the equation
  -- Split into: ρ•(pv - √η•pg) + √μ'•(en + hC_term + ξ)
  -- where hC_term = ρ•√η•pv - (1+ρ)•η•pg
  set hC_term := ρ • Real.sqrt η • pv - (1 + ρ) • η • pg with hC_term_def
  -- Distribute √μ'•(en + hC_term + ξ)
  have hdist : Real.sqrt μ' • (en + hC_term + ξ) =
      Real.sqrt μ' • en + Real.sqrt μ' • hC_term + Real.sqrt μ' • ξ := by
    rw [smul_add, smul_add]
  -- Distribute √μ'•hC_term
  have hdist2 : Real.sqrt μ' • hC_term =
      (Real.sqrt μ' * ρ * Real.sqrt η) • pv - (Real.sqrt μ' * (1 + ρ) * η) • pg := by
    rw [hC_term_def, smul_sub]
    simp only [smul_smul]
    congr 1 <;> congr 1 <;> ring
  -- Distribute ρ•(pv - √η•pg)
  have hdist3 : ρ • (pv - Real.sqrt η • pg) =
      ρ • pv - (ρ * Real.sqrt η) • pg := by
    rw [smul_sub, smul_smul]
  rw [hdist3, hdist, hdist2]
  -- Goal: ρ•pv - (ρ*√η)•pg + (√μ'•en + ((√μ'*ρ*√η)•pv - (√μ'*(1+ρ)*η)•pg) + √μ'•ξ) =
  --       (1-a)•pv + √μ'•en - √η•pg + √μ'•ξ
  -- Collect pv: ρ•pv + (√μ'*ρ*√η)•pv = (ρ + √μ'*ρ*√η)•pv
  -- Collect pg: (ρ*√η)•pg + (√μ'*(1+ρ)*η)•pg = (ρ*√η + √μ'*(1+ρ)*η)•pg
  rw [show ρ • pv - (ρ * Real.sqrt η) • pg +
      (Real.sqrt μ' • en + ((Real.sqrt μ' * ρ * Real.sqrt η) • pv -
      (Real.sqrt μ' * (1 + ρ) * η) • pg) + Real.sqrt μ' • ξ) =
      (ρ • pv + (Real.sqrt μ' * ρ * Real.sqrt η) • pv) + Real.sqrt μ' • en -
      ((ρ * Real.sqrt η) • pg + (Real.sqrt μ' * (1 + ρ) * η) • pg) +
      Real.sqrt μ' • ξ from by abel,
    ← add_smul, ← add_smul, hpv_coeff, hpg_coeff]

end PLAcceleratedNesterovLean
