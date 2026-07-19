/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Flat-Case Lyapunov Contraction: Arithmetic Core

Pure arithmetic lemma for the flat-case bound:
  Fn1 + wn_sq/2 + Tn1 ≤ (1-a) * (Fn + Un/2 + Tn)

All quantities are real numbers. The geometric content (norms, inner products,
projections) has been extracted by the caller.

## Proof strategy
Use the function-value identity
  (1-a)·Fn = Fnprime − (1-a)·(Fnprime − Fn) − a·Fnprime
and bound each piece:
  • Fn1 via descent:  Fn1 ≤ Fnprime − η/2·(PGsq + PperpGsq)
  • (1-a)·(Fnprime − Fn) via segment estimate
  • a·Fnprime − a·ip_PperpG_en via aiming

After cancellations the remaining coefficients are all ≤ 0:
  • PGsq:      −a·η/2 ≤ 0
  • PperpGsq:  0
  • ip_PG_PV, ip_PperpG_PperpV, ip_PperpG_en, Esq:  cancel to 0
  • PVsq:      ((1-a)·εη − 3a − a²)/2 ≤ 0  (since εη ≤ a)
  • PperpVsq:  (1-a)·(εη − a)/2 ≤ 0          (since εη ≤ a)
-/


namespace PLAcceleratedNesterovLean

/-- The main arithmetic assembly for the flat-case Lyapunov contraction.

Parameters represent extracted real values from the geometric proof:
  • a = √(μ·η), the contraction rate
  • Fn, Fn1 = function gaps at steps n, n+1
  • Fnprime = function gap at lookahead point x'_n
  • PVsq, PperpVsq = ‖P v‖², ‖P⊥ v‖²
  • PGsq, PperpGsq = ‖P g‖², ‖P⊥ g‖²
  • Esq = ‖e_n‖²
  • Various inner products
-/
theorem flat_case_arithmetic
    -- Rate parameter
    (a : ℝ) (ha_pos : 0 < a) (ha_lt1 : a < 1)
    -- Physical parameters
    (η μ sqrtμ sqrtη : ℝ)
    (hη_pos : 0 < η) (_hμ_pos : 0 < μ)
    (_hsqrtμ_nn : 0 ≤ sqrtμ) (_hsqrtη_nn : 0 ≤ sqrtη)
    (_hsqrtμ_sq : sqrtμ ^ 2 = μ) (_hsqrtη_sq : sqrtη ^ 2 = η)
    (_h_prod : sqrtμ * sqrtη = a)
    -- Curvature parameter
    (εη : ℝ) (hεη_nn : 0 ≤ εη) (hεη_le : εη ≤ a)
    -- Function gap values
    (Fn Fn1 Fnprime : ℝ)
    (_hFn_nn : 0 ≤ Fn) (_hFn1_nn : 0 ≤ Fn1) (_hFnp_nn : 0 ≤ Fnprime)
    -- Squared norms (all ≥ 0)
    (PVsq PperpVsq PGsq PperpGsq Esq : ℝ)
    (hPVsq_nn : 0 ≤ PVsq) (hPperpVsq_nn : 0 ≤ PperpVsq)
    (hPGsq_nn : 0 ≤ PGsq) (_hPperpGsq_nn : 0 ≤ PperpGsq)
    (_hEsq_nn : 0 ≤ Esq)
    -- Inner products (signed, no nonnegativity)
    (ip_PperpG_en ip_PG_PV ip_PperpG_PperpV ip_PperpV_en : ℝ)
    -- Projector-freezing error: |⟨g, Pe⟩| (zero when P kills normals exactly)
    (proj_error : ℝ) (_hproj_nn : 0 ≤ proj_error)
    -- KEY BOUNDS:
    -- 1. Descent (from L-smoothness): f(x_{n+1}) ≤ f(x'_n) − η/2·‖g‖²
    (h_descent : Fn1 ≤ Fnprime - η / 2 * (PGsq + PperpGsq))
    -- 2. Segment estimate (√η·⟨g,v⟩ ≥ f(x'n)−f(xn) − εη/2·‖v‖²)
    (h_segment : sqrtη * (ip_PG_PV + ip_PperpG_PperpV) ≥
        Fnprime - Fn - εη / 2 * (PVsq + PperpVsq))
    -- 3. Aiming inequality (⟨P⊥g, en⟩ ≥ f(x'n)−f* + μ/2·‖en‖² − proj_error)
    (h_aiming : ip_PperpG_en ≥ Fnprime + μ / 2 * Esq - proj_error)
    -- NORM IDENTITIES:
    -- wn_sq = ‖(1-a)·P⊥v + √μ·en − √η·P⊥g‖²
    (wn_sq : ℝ)
    (hwn_sq : wn_sq = (1 - a) ^ 2 * PperpVsq + μ * Esq + η * PperpGsq
        + 2 * (1 - a) * sqrtμ * ip_PperpV_en
        - 2 * (1 - a) * sqrtη * ip_PperpG_PperpV
        - 2 * a * ip_PperpG_en)
    -- Un = ‖P⊥v + √μ·en‖²
    (Un : ℝ)
    (hUn : Un = PperpVsq + 2 * sqrtμ * ip_PperpV_en + μ * Esq)
    -- Tn1 = (1-a)/2·‖Pv − √η·Pg‖²
    (Tn1 : ℝ)
    (hTn1 : Tn1 = (1 - a) / 2 * PVsq - (1 - a) * sqrtη * ip_PG_PV +
        (1 - a) * η / 2 * PGsq)
    -- Tn = (1+a)²/(2(1-a))·‖Pv‖²
    (Tn : ℝ)
    (hTn : Tn = (1 + a) ^ 2 / (2 * (1 - a)) * PVsq)
    :
    Fn1 + wn_sq / 2 + Tn1 ≤ (1 - a) * (Fn + Un / 2 + Tn) + a * proj_error := by
  -- Positivity of 1-a
  have h1a : (0 : ℝ) < 1 - a := by linarith
  -- Clear the division in Tn: 2·(1-a)·Tn = (1+a)²·PVsq
  have hTn' : 2 * (1 - a) * Tn = (1 + a) ^ 2 * PVsq := by
    rw [hTn]; field_simp
  -- Substitute norm identities to eliminate wn_sq, Un, Tn1
  subst hwn_sq; subst hUn; subst hTn1
  -- Scale segment estimate by (1-a) > 0
  have h_seg_sc : (1 - a) * (sqrtη * (ip_PG_PV + ip_PperpG_PperpV)) ≥
      (1 - a) * (Fnprime - Fn - εη / 2 * (PVsq + PperpVsq)) :=
    mul_le_mul_of_nonneg_left h_segment (le_of_lt h1a)
  -- Scale aiming by a > 0: a·ip_PperpG_en ≥ a·(Fnprime + μ/2·Esq − proj_error)
  have h_aim_sc : a * ip_PperpG_en ≥ a * Fnprime + a * (μ / 2) * Esq - a * proj_error := by
    have := mul_le_mul_of_nonneg_left h_aiming (le_of_lt ha_pos)
    nlinarith
  -- Coefficient of PperpVsq: (1-a)·(a − εη)·PperpVsq ≥ 0
  have hc_ppv : (1 - a) * (a - εη) * PperpVsq ≥ 0 := by
    apply mul_nonneg _ hPperpVsq_nn
    apply mul_nonneg <;> linarith
  -- Coefficient of PVsq: (3a + a² − (1-a)·εη)·PVsq ≥ 0
  have hc_pv : (3 * a + a ^ 2 - (1 - a) * εη) * PVsq ≥ 0 := by
    apply mul_nonneg _ hPVsq_nn; nlinarith [sq_nonneg a]
  -- Coefficient of PGsq: a·η·PGsq ≥ 0
  have hc_pg : a * η * PGsq ≥ 0 := by
    simp_all
  -- Main closure: combine all bounds and coefficient signs
  nlinarith [hTn', h_descent, h_seg_sc, h_aim_sc, hc_ppv, hc_pv, hc_pg]

end PLAcceleratedNesterovLean
