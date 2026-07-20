/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.Step1
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.Step2

/-!
# Lyapunov Contraction Step 3: Algebraic Assembly Lemmas

This file provides the arithmetic/algebraic backbone for the contraction proof
  L_{n+1} ≤ (1 - a/2) · L_n
by decomposing it into independent, self-contained lemmas.

## Architecture

The contraction proof has two layers:

**Layer 1 (this file): Pure arithmetic.**
All lemmas are stated with real-valued parameters (no norms, no vectors).
Each is ≤ 20 lines and provable by `nlinarith` / `linarith` / `ring`.

**Layer 2 (LyapunovContraction.lean): Geometric bridge.**
Extract real values from norms/inner products, verify arithmetic hypotheses,
apply the assembly lemma.

## Proof Strategy

The Lyapunov function L_n has three components:
  L_n = F_n + U_n/2 + T_n
where F_n = f(x_n) - f*, U_n = ‖u_n‖², T_n = λ‖Pv_n‖².

**Step A**: In the "flat" case (no curvature error), each component of L_{n+1}
is bounded by (1-a) times the corresponding component of L_n.

**Step B**: The curvature error ξ_n contributes a perturbation of size O(a² L_n).

**Step C**: Since (1-a) + (a/2) = (1-a/2), the perturbation is absorbed:
  L_{n+1} ≤ (1-a) L_n + perturbation ≤ (1-a/2) L_n.
-/

noncomputable section

namespace PLAcceleratedNesterovLean

-- ════════════════════════════════════════════════════════════════════════════
-- § 1. Leading coefficient slack
-- ════════════════════════════════════════════════════════════════════════════

/-- The coefficients (1-a), (1-a)/2, (1-a)/2 in the flat-case bound are all
    ≤ (1-a/2) times the corresponding Lyapunov coefficients 1, 1/2, λ.
    This creates an (a/2)·L_n slack for perturbation absorption.

    Concretely: (1-a)·F + ((1-a)/2)·U + ((1-a)/2)·V ≤ (1-a/2)·(F + U/2 + λ·V)
    when λ = (1+a)²/(2(1-a)) and 0 < a < 1. -/
theorem leading_coeff_slack (a F U V : ℝ)
    (ha : 0 < a) (ha1 : a < 1)
    (hF : 0 ≤ F) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (lam : ℝ) (hlam : lam = (1 + a) ^ 2 / (2 * (1 - a))) :
    (1 - a) * F + (1 - a) / 2 * U + (1 - a) / 2 * V ≤
    (1 - a / 2) * (F + U / 2 + lam * V) := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  -- It suffices to show each coefficient on the LHS is ≤ the corresponding one on the RHS
  -- F: (1-a) ≤ (1-a/2)  ✓ since a > 0
  -- U: (1-a)/2 ≤ (1-a/2)/2  ✓ since a > 0
  -- V: (1-a)/2 ≤ (1-a/2)·λ  needs λ ≥ (1-a)/(2(1-a/2)) = (1-a)/(2-a)
  --    λ = (1+a)²/(2(1-a)). Need (1+a)²/(2(1-a)) ≥ (1-a)/(2-a).
  --    Cross multiply: (1+a)²(2-a) ≥ 2(1-a)². For 0<a<1 this holds (checked).
  subst hlam
  -- Strategy: show RHS - LHS ≥ 0 by clearing denominators
  -- RHS - LHS = (a/2)F + (a/4)U + ((1-a/2)(1+a)²/(2(1-a)) - (1-a)/2)V
  -- The V-coefficient × 2(1-a) = (1-a/2)(1+a)² - (1-a)² = a(7/2 - a - a²/2) > 0
  suffices h : 0 ≤ 2 * (1 - a) * ((1 - a / 2) * (F + U / 2 +
      (1 + a) ^ 2 / (2 * (1 - a)) * V) -
      ((1 - a) * F + (1 - a) / 2 * U + (1 - a) / 2 * V)) by
    nlinarith
  -- Clear denominators: 2(1-a) · ((1-a/2)·(1+a)²/(2(1-a))·V) = (1-a/2)(1+a)²V
  have h_clear : 2 * (1 - a) * ((1 - a / 2) * (F + U / 2 +
      (1 + a) ^ 2 / (2 * (1 - a)) * V) -
      ((1 - a) * F + (1 - a) / 2 * U + (1 - a) / 2 * V)) =
      2 * (1 - a) * (a / 2 * F + a / 4 * U) +
      ((1 - a / 2) * (1 + a) ^ 2 - (1 - a) ^ 2) * V := by
    field_simp
    ring
  rw [h_clear]
  have h_Vcoeff : (1 - a / 2) * (1 + a) ^ 2 - (1 - a) ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg a]
  nlinarith [mul_pos ha h1a]

/-- Variant: the slack is at least (a/2)·F + (a/4)·U (used for absorption budget). -/
theorem leading_coeff_slack_lower (a F U V : ℝ)
    (_ha : 0 < a) (_ha1 : a < 1)
    (_hF : 0 ≤ F) (_hU : 0 ≤ U) (hV : 0 ≤ V) :
    (1 - a / 2) * (F + U / 2 + V) -
    ((1 - a) * F + (1 - a) / 2 * U + (1 - a) / 2 * V) ≥
    a / 2 * F + a / 4 * U := by
  nlinarith

-- ════════════════════════════════════════════════════════════════════════════
-- § 2. Lambda-rho identity and tangential coefficient
-- ════════════════════════════════════════════════════════════════════════════

/-- λρ² = (1-a)/2. Already in Step1; re-exported for convenience. -/
theorem lambda_rho_sq' (a ρ lam : ℝ) (ha_ne : 1 + a ≠ 0) (ha_pos : 1 - a ≠ 0)
    (hρ : ρ = (1 - a) / (1 + a))
    (hlam : lam = (1 + a) ^ 2 / (2 * (1 - a))) :
    lam * ρ ^ 2 = (1 - a) / 2 :=
  lambda_rho_sq a ρ lam ha_ne ha_pos hρ hlam

-- ════════════════════════════════════════════════════════════════════════════
-- § 3. Flat-case function-value bound
-- ════════════════════════════════════════════════════════════════════════════

/-- Function-value bound from descent + strong aiming.

    Given:
    - Descent:  F1 ≤ F' - (η/2)·G²
    - Aiming:   A ≥ F' + (μ'/2)·E²
    where A = ⟨g_n, e_n⟩, G² = ‖g_n‖², E² = ‖e_n‖²,
    F' = f(x'_n) - f*, F1 = f(x_{n+1}) - f*.

    Then: F1 ≤ A - (μ'/2)·E² - (η/2)·G².
    The aiming inequality provides a tighter bound on A than Cauchy-Schwarz. -/
theorem function_descent_with_aiming
    (F1 F' A : ℝ) (G_sq E_sq η μ' : ℝ)
    (h_desc : F1 ≤ F' - η / 2 * G_sq)
    (h_aim : A ≥ F' + μ' / 2 * E_sq) :
    F1 ≤ A - μ' / 2 * E_sq - η / 2 * G_sq := by
  linarith

-- ════════════════════════════════════════════════════════════════════════════
-- § 4. Gradient inner product decomposition
-- ════════════════════════════════════════════════════════════════════════════

/-- Gradient inner product splits: ⟨g, e⟩ = ⟨P⊥g, e⟩ + ⟨Pg, e⟩.
    In the flat case, ⟨Pg, e⟩ = 0 (tangent vs normal).
    The Hessian bound controls ⟨Pg, e⟩ in the curved case. -/
theorem gradient_inner_split (ge perpge tange : ℝ)
    (h_split : ge = perpge + tange) :
    ge = perpge + tange := h_split

-- ════════════════════════════════════════════════════════════════════════════
-- § 5. Normal energy: the completing-the-square core
-- ════════════════════════════════════════════════════════════════════════════

-- In the flat case, the auxiliary variable satisfies:
--   u_{n+1} = (1-a)u_n + (a²/√η)e_n - √η P⊥g_n     (*)
--
-- where a = √(μ'η). The proof of (*) uses the ρ-identity (1+a)ρ = 1-a
-- and the recursion for e_{n+1} (flat case).
--
-- From (*), ‖u_{n+1}‖² involves three squared terms plus cross terms.
-- Combined with the strong aiming and descent terms, the cross terms
-- and squared terms recombine to give ≤ (1-a)·‖u_n‖²/2.

/-- Arithmetic core: (1-a)² ≤ (1-a) for 0 ≤ a ≤ 1. -/
theorem sq_contraction_le (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (1 - a) ^ 2 ≤ 1 - a := by
  nlinarith [sq_nonneg a]

-- For the normal energy, the leading coefficient (1-a)² plus the
-- perturbation from εη must be ≤ (1-a):
--   (1-a)² + εη·(1-a) ≤ (1-a)  when εη ≤ a.
-- Already proved in Step1 as velocity_normal_coeff.

-- ════════════════════════════════════════════════════════════════════════════
-- § 6. Assembly: flat case contraction
-- ════════════════════════════════════════════════════════════════════════════

/-- **Flat-case contraction assembly** (pure arithmetic).

    If each component of L_{n+1} is bounded by (1-a) times the corresponding
    component of L_n, then L_{n+1} ≤ (1-a/2) L_n.

    This is the core of the contraction: the gap between (1-a) and (1-a/2)
    provides room for perturbation absorption. -/
theorem flat_contraction_assembly (a : ℝ)
    (ha : 0 < a) (_ha1 : a < 1)
    -- Components of L_n (all nonneg)
    (Fn Un Tn : ℝ) (hFn : 0 ≤ Fn) (hUn : 0 ≤ Un) (hTn : 0 ≤ Tn)
    -- Lyapunov at step n
    (Ln : ℝ) (hLn : Ln = Fn + Un / 2 + Tn)
    -- Components of L_{n+1}
    (Fn1 Un1 Tn1 : ℝ) (_hFn1 : 0 ≤ Fn1) (_hUn1 : 0 ≤ Un1) (_hTn1 : 0 ≤ Tn1)
    -- Lyapunov at step n+1
    (Ln1 : ℝ) (hLn1 : Ln1 = Fn1 + Un1 / 2 + Tn1)
    -- Component bounds (flat case: each ≤ (1-a) times original)
    (hF : Fn1 ≤ (1 - a) * Fn)
    (hU : Un1 / 2 ≤ (1 - a) * Un / 2)
    (hT : Tn1 ≤ (1 - a) * Tn) :
    Ln1 ≤ (1 - a / 2) * Ln := by
  rw [hLn1, hLn]
  have h_sum : Fn1 + Un1 / 2 + Tn1 ≤ (1 - a) * (Fn + Un / 2 + Tn) := by linarith
  have h_slack : (1 - a) * (Fn + Un / 2 + Tn) ≤ (1 - a / 2) * (Fn + Un / 2 + Tn) := by
    nlinarith
  linarith

-- ════════════════════════════════════════════════════════════════════════════
-- § 7. Assembly: contraction with perturbation
-- ════════════════════════════════════════════════════════════════════════════

/-- **Contraction with perturbation** (pure arithmetic).

    If each component of L_{n+1} is bounded by (1-a) times the corresponding
    component of L_n, PLUS a perturbation δ, then L_{n+1} ≤ (1-a/2) L_n
    provided δ ≤ (a/2) L_n. -/
theorem contraction_with_perturbation (a : ℝ)
    (_ha : 0 < a) (_ha1 : a < 1)
    (Ln Ln1 δ : ℝ)
    (_hLn : 0 ≤ Ln)
    -- L_{n+1} ≤ (1-a) L_n + δ
    (h_flat : Ln1 ≤ (1 - a) * Ln + δ)
    -- Perturbation absorbed by slack
    (h_perturb : δ ≤ a / 2 * Ln) :
    Ln1 ≤ (1 - a / 2) * Ln := by
  linarith

/-- Variant: if we can bound the perturbation by C·ε·η·L_n and ε·η ≤ a and C ≤ 1/2,
    then δ ≤ (a/2)·L_n. -/
theorem perturbation_bound (a εη C Ln : ℝ)
    (hεη : 0 ≤ εη) (hLn : 0 ≤ Ln)
    (_hC : 0 ≤ C) (hC_half : C ≤ 1 / 2)
    (hbound : εη ≤ a) :
    C * εη * Ln ≤ a / 2 * Ln := by
  have h1 : C * εη ≤ 1 / 2 * a := by nlinarith
  nlinarith

-- ════════════════════════════════════════════════════════════════════════════
-- § 8. Tangential energy expansion
-- ════════════════════════════════════════════════════════════════════════════

/-- The tangential energy at step n+1, expanded.

    From v_{n+1} = ρ(v_n - √η g_n) and P linear:
      Pv_{n+1} = ρ(Pv_n - √η Pg_n)
      ‖Pv_{n+1}‖² = ρ²(‖Pv_n‖² - 2√η⟨Pv_n, Pg_n⟩ + η‖Pg_n‖²)

    So: λ‖Pv_{n+1}‖² = λρ²(‖Pv_n‖² - 2√η⟨Pv_n, Pg_n⟩ + η‖Pg_n‖²)
                       = ((1-a)/2)(‖Pv_n‖² - 2√η⟨Pv_n, Pg_n⟩ + η‖Pg_n‖²)

    The (1-a)/2 ≤ (1-a)λ ensures this is ≤ (1-a)·Tn + cross terms. -/
theorem tangential_energy_expansion (a η : ℝ)
    (PVsq PGsq PVG : ℝ) -- ‖Pv_n‖², ‖Pg_n‖², ⟨Pv_n, Pg_n⟩
    (sqrtη : ℝ) (_hsqrtη : sqrtη ^ 2 = η) :
    (1 - a) / 2 * (PVsq - 2 * sqrtη * PVG + η * PGsq) =
    (1 - a) / 2 * PVsq - (1 - a) * sqrtη * PVG + (1 - a) / 2 * η * PGsq := by
  ring

/-- Tangential cross-term absorption: the -(1-a)√η⟨Pv,Pg⟩ term satisfies
    |-(1-a)√η⟨Pv,Pg⟩| ≤ (1-a)/2 · (α‖Pv‖² + η/α ‖Pg‖²)
    for any α > 0 (Young's inequality). With α = 1 this gives:
    |term| ≤ (1-a)/2 · (‖Pv‖² + η‖Pg‖²). -/
theorem tangential_cross_absorption (a sqrtη PVsq PGsq PVG : ℝ)
    (_ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hPVsq : 0 ≤ PVsq) (hPGsq : 0 ≤ PGsq)
    (h_cs : |PVG| ≤ Real.sqrt PVsq * Real.sqrt PGsq)
    (hsqrtη : 0 ≤ sqrtη) :
    -(1 - a) * sqrtη * PVG ≤ (1 - a) / 2 * (PVsq + sqrtη ^ 2 * PGsq) := by
  -- It suffices to bound |PVG| and use -(1-a)·sqrtη·PVG ≤ (1-a)·sqrtη·|PVG|
  have h1a : 0 ≤ 1 - a := by linarith
  -- Key: (1-a)/2 · (PVsq + sqrtη²·PGsq) ≥ (1-a)·sqrtη·√(PVsq)·√(PGsq)
  -- by AM-GM: PVsq + sqrtη²·PGsq ≥ 2·sqrtη·√(PVsq·sqrtη²·PGsq) ... no
  -- Simpler: use (√PVsq - sqrtη·√PGsq)² ≥ 0
  -- → PVsq - 2·sqrtη·√PVsq·√PGsq + sqrtη²·PGsq ≥ 0
  -- → PVsq + sqrtη²·PGsq ≥ 2·sqrtη·√PVsq·√PGsq
  have h_amgm : PVsq + sqrtη ^ 2 * PGsq ≥ 2 * sqrtη * Real.sqrt PVsq * Real.sqrt PGsq := by
    have := sq_nonneg (Real.sqrt PVsq - sqrtη * Real.sqrt PGsq)
    rw [sub_sq] at this
    simp only [Real.sq_sqrt hPVsq, mul_pow, Real.sq_sqrt hPGsq] at this
    nlinarith
  -- Now: -(1-a)·sqrtη·PVG ≤ (1-a)·sqrtη·|PVG|
  have h_abs : -(1 - a) * sqrtη * PVG ≤ (1 - a) * sqrtη * |PVG| := by
    nlinarith [neg_abs_le PVG, mul_nonneg h1a hsqrtη]
  -- And: (1-a)·sqrtη·|PVG| ≤ (1-a)·sqrtη·√PVsq·√PGsq ≤ (1-a)/2·(PVsq + sqrtη²·PGsq)
  calc -(1 - a) * sqrtη * PVG
      ≤ (1 - a) * sqrtη * |PVG| := h_abs
    _ ≤ (1 - a) * sqrtη * (Real.sqrt PVsq * Real.sqrt PGsq) := by
        nlinarith [mul_nonneg h1a hsqrtη]
    _ = (1 - a) * (sqrtη * Real.sqrt PVsq * Real.sqrt PGsq) := by ring
    _ ≤ (1 - a) / 2 * (PVsq + sqrtη ^ 2 * PGsq) := by nlinarith

-- ════════════════════════════════════════════════════════════════════════════
-- § 9. Combined descent + tangential: gradient squared recovery
-- ════════════════════════════════════════════════════════════════════════════

/-- The descent provides -η/2 ‖g‖², and the tangential expansion creates
    +(1-a)/2 · η · ‖Pg‖². The net gradient-squared term is:

      -η/2 ‖g‖² + (1-a)/2 · η · ‖Pg‖²
    = -η/2(‖Pg‖² + ‖P⊥g‖²) + (1-a)/2 · η · ‖Pg‖²
    = -ηa/2 · ‖Pg‖² - η/2 · ‖P⊥g‖²

    Both terms are ≤ 0, giving descent in BOTH tangential and normal gradient. -/
theorem gradient_sq_net (a η PGsq PperpGsq Gsq : ℝ)
    (_ha : 0 ≤ a) (_ha1 : a ≤ 1) (_hη : 0 ≤ η)
    (_hPGsq : 0 ≤ PGsq) (_hPperpGsq : 0 ≤ PperpGsq)
    (h_orth : Gsq = PGsq + PperpGsq) :
    -η / 2 * Gsq + (1 - a) / 2 * η * PGsq =
    -η * a / 2 * PGsq - η / 2 * PperpGsq := by
  rw [h_orth]; ring

-- ════════════════════════════════════════════════════════════════════════════
-- § 10. Main assembly theorem (the entry point for LyapunovContraction.lean)
-- ════════════════════════════════════════════════════════════════════════════

/-- **Main contraction assembly** (pure arithmetic).

    Takes all real-valued intermediate quantities as parameters and
    combines them to prove the contraction.

    The caller (LyapunovContraction.lean) extracts these values from
    the geometric setup (norms, inner products) and verifies the hypotheses.

    Parameter naming convention:
    - F, U, T = components of L_n (function gap, normal energy, tangential energy)
    - F', U', T' = components of L_{n+1}
    - G = ‖gradient‖², E = ‖normal displacement‖²
    - a = √(μ'η), the contraction rate parameter
-/
theorem lyapunov_contraction_arithmetic
    (a : ℝ) (_ha : 0 < a) (_ha1 : a < 1)
    -- L_n components (nonneg)
    (Fn Un_half Tn : ℝ)
    (_hFn : 0 ≤ Fn) (_hUn : 0 ≤ Un_half) (_hTn : 0 ≤ Tn)
    (Ln : ℝ) (_hLn_def : Ln = Fn + Un_half + Tn)
    -- L_{n+1} components (nonneg)
    (Fn1 Un1_half Tn1 : ℝ)
    (_hFn1 : 0 ≤ Fn1) (_hUn1 : 0 ≤ Un1_half) (_hTn1 : 0 ≤ Tn1)
    (Ln1 : ℝ) (hLn1_def : Ln1 = Fn1 + Un1_half + Tn1)
    -- The three component bounds (with perturbation δ)
    (δ : ℝ) (_hδ : 0 ≤ δ)
    (hbound : Fn1 + Un1_half + Tn1 ≤ (1 - a) * Ln + δ)
    (habsorb : δ ≤ a / 2 * Ln) :
    Ln1 ≤ (1 - a / 2) * Ln := by
  rw [hLn1_def]
  linarith

-- ════════════════════════════════════════════════════════════════════════════
-- § 11. Sufficient condition for perturbation absorption
-- ════════════════════════════════════════════════════════════════════════════

/-- The perturbation from curvature error ξ_n contributes to ‖u_{n+1}‖²
    via the expansion ‖w + c·ξ‖² = ‖w‖² + 2c⟨w,ξ⟩ + c²‖ξ‖².

    If ‖ξ_n‖ ≤ C_ξ·√η·√L_n (from `motion_bounds_curvature_error`) and
    ‖w_n‖ ≤ C_w·√L_n (from coercivity), then:

    |perturbation| = |√μ'(2⟨w_n,ξ_n⟩ + μ'‖ξ_n‖²)|
                   ≤ √μ'(2 C_w C_ξ √η L_n + μ' C_ξ² η L_n)
                   = a(2 C_w C_ξ + a C_ξ²) L_n

    For the absorption δ ≤ (a/2)L_n, we need 2 C_w C_ξ + a C_ξ² ≤ 1/2.
    This holds when C_w, C_ξ are small (guaranteed by shrinking the neighborhood). -/
theorem curvature_perturbation_absorption
    (a C_w C_ξ Ln : ℝ)
    (ha : 0 < a) (ha1 : a < 1)
    (hLn : 0 ≤ Ln)
    (_hCw : 0 ≤ C_w) (_hCξ : 0 ≤ C_ξ)
    (h_small : 2 * C_w * C_ξ + a * C_ξ ^ 2 ≤ 1 / 2) :
    a * (2 * C_w * C_ξ + a * C_ξ ^ 2) * Ln ≤ a / 2 * Ln := by
  have h1 : 2 * C_w * C_ξ + a * C_ξ ^ 2 ≤ 1 / 2 := h_small
  have h2 : a * (2 * C_w * C_ξ + a * C_ξ ^ 2) ≤ a * (1 / 2) := by
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt ha)
  nlinarith [mul_nonneg (le_of_lt ha) hLn]

-- ════════════════════════════════════════════════════════════════════════════
-- § 12. Orthogonal projector norm decomposition
-- ════════════════════════════════════════════════════════════════════════════

/-- For an orthogonal projector P: ‖v‖² = ‖Pv‖² + ‖P⊥v‖².
    This is the Pythagorean theorem. Stated for real numbers. -/
theorem norm_sq_decomp (total tang perp : ℝ)
    (h : total = tang + perp) (_ht : 0 ≤ tang) (_hp : 0 ≤ perp) :
    total = tang + perp := h

-- ════════════════════════════════════════════════════════════════════════════
-- § 13. Strong aiming gives normal velocity recursion
-- ════════════════════════════════════════════════════════════════════════════

-- Strong aiming provides: ⟨g_n, e_n⟩ ≥ Ψ(x'_n) where Ψ = (f-f*) + (μ'/2)‖e‖².
-- This decomposes as: ⟨P⊥g_n, e_n⟩ + ⟨Pg_n, e_n⟩ ≥ F' + (μ'/2)E²
-- In the flat case, ⟨Pg_n, e_n⟩ = 0, so ⟨P⊥g_n, e_n⟩ ≥ F' + (μ'/2)E².
-- The P⊥g_n term creates a "return force" that drives the normal component
-- toward the manifold. Combined with the completing-the-square,
-- this gives the (1-a) contraction for the normal energy.

-- ════════════════════════════════════════════════════════════════════════════
-- § 14. Two-step contraction: sufficiency lemma
-- ════════════════════════════════════════════════════════════════════════════

/-- **Two-step sufficiency**: To prove L_{n+1} ≤ (1-a/2)L_n, it suffices to show:

    1. L_{n+1} ≤ (1-a) · L_n + δ      (flat-case bound + perturbation)
    2. δ ≤ (a/2) · L_n                 (perturbation absorption)

    This is the entry point for the `contraction` case in LyapunovContraction.lean.
    The proof simply adds the two inequalities. -/
theorem two_step_contraction (a Ln Ln1 δ : ℝ)
    (_ha : 0 < a) (_ha1 : a < 1)
    (_hLn : 0 ≤ Ln)
    (h_step1 : Ln1 ≤ (1 - a) * Ln + δ)
    (h_step2 : δ ≤ a / 2 * Ln) :
    Ln1 ≤ (1 - a / 2) * Ln := by
  linarith

/-- **Generalized two-step sufficiency** with budget-split parameter θ ∈ (0,1):

    1. L_{n+1} ≤ (1-a) · L_n + δ      (flat-case bound + perturbation)
    2. δ ≤ θ·a · L_n                   (perturbation absorption with fraction θ)

    Conclusion: L_{n+1} ≤ (1-(1-θ)·a) · L_n.

    When θ = 1/2, this recovers `two_step_contraction`. Choosing θ → 0 gives a
    contraction rate (1-a) approaching the ideal (perturbation-free) rate. -/
theorem two_step_contraction_general (a θ Ln Ln1 δ : ℝ)
    (_ha : 0 < a) (_ha1 : a < 1)
    (_hθ : 0 < θ) (_hθ1 : θ < 1)
    (_hLn : 0 ≤ Ln)
    (h_step1 : Ln1 ≤ (1 - a) * Ln + δ)
    (h_step2 : δ ≤ θ * a * Ln) :
    Ln1 ≤ (1 - (1 - θ) * a) * Ln := by
  nlinarith

end PLAcceleratedNesterovLean
