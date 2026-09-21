/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.TriadicScale
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Scalar -/

namespace Homogenization

/-!
# Coarse Caccioppoli cross term: scalar bounds
-/

noncomputable section

open scoped BigOperators

theorem coarseCaccioppoli_gapInv_rpow_eq {ρ₁ ρ₂ q : ℝ} :
    Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) q =
      Real.rpow (ρ₂ - ρ₁) (-q) := by
  rw [coarseCaccioppoliGapInv_eq_inv]
  symm
  simpa using (Real.rpow_neg_eq_inv_rpow (ρ₂ - ρ₁) q)

theorem coarseCaccioppoliBoundaryCrossCoeffOfHeight_sq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ) (h : ℝ → ℝ → ℝ)
    {ρ₁ ρ₂ : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ uL2Sq) :
    (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂) ^ (2 : ℕ) =
      (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
        LambdaSq Q s (.finite 1) a * uL2Sq) *
        (C * Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂)) := by
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs
  have h3sq :
      (Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) ^ (2 : ℕ) =
        Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) := by
    calc
      (Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) ^ (2 : ℕ) =
          Real.rpow (Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) (2 : ℝ) := by
            symm
            exact Real.rpow_natCast _ 2
      _ = Real.rpow (3 : ℝ) ((s * h ρ₁ ρ₂) * 2) := by
            simpa using
              (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (s * h ρ₁ ρ₂) (2 : ℝ)).symm
      _ = Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) := by ring_nf
  have hLambda_sq :
      (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) ^ (2 : ℕ) =
        LambdaSq Q s (.finite 1) a := by
    exact sq_rpow_half_eq_self_of_nonneg hLambda_nonneg
  unfold coarseCaccioppoliBoundaryCrossCoeffOfHeight
  calc
    (C * coarseCaccioppoliGapInv ρ₁ ρ₂ *
        Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
        Real.sqrt uL2Sq) ^ (2 : ℕ)
        =
          C ^ (2 : ℕ) * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            (Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) ^ (2 : ℕ) *
            (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) ^ (2 : ℕ) *
            (Real.sqrt uL2Sq) ^ (2 : ℕ) := by
            ring
    _ = C ^ (2 : ℕ) * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
          Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) *
          LambdaSq Q s (.finite 1) a *
          uL2Sq := by
            rw [h3sq, hLambda_sq, Real.sq_sqrt hu]
    _ = (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
          LambdaSq Q s (.finite 1) a * uL2Sq) *
          (C * Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂)) := by
            ring

theorem coarseCaccioppoli_boundary_explicitHeight_leftBranch_scalar
    {ρ₁ ρ₂ s C : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s < 1)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂) (hlt : ρ₁ < ρ₂) :
    C * Real.rpow (3 : ℝ) (2 * s * ((k : ℝ) + 4)) ≤
      (6561 : ℝ) * 6561 * C *
        Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) := by
  have h2s_nonneg : 0 ≤ 2 * s := by positivity
  have hpow_base_le : (3 : ℝ) ^ k ≤ 81 * coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    coarseCaccioppoli_pow_scale_le_mul_gapInv_of_triadicGapScaleChoice hchoice hlt
  have hk_rpow :
      Real.rpow (3 : ℝ) (2 * s * (k : ℝ)) =
        Real.rpow ((3 : ℝ) ^ k) (2 * s) := by
    calc
      Real.rpow (3 : ℝ) (2 * s * (k : ℝ))
          = Real.rpow (3 : ℝ) ((k : ℝ) * (2 * s)) := by congr 1; ring
      _ = Real.rpow ((3 : ℝ) ^ k) (2 * s) := by
            simpa [Real.rpow_natCast] using
              (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (k : ℝ) (2 * s))
  have hk_le :
      Real.rpow (3 : ℝ) (2 * s * (k : ℝ)) ≤
        Real.rpow (81 * coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) := by
    rw [hk_rpow]
    exact Real.rpow_le_rpow (by positivity) hpow_base_le h2s_nonneg
  have h81_le :
      Real.rpow (81 : ℝ) (2 * s) ≤ (6561 : ℝ) := by
    have h2s_le : 2 * s ≤ (2 : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hs1.le (by norm_num : 0 ≤ (2 : ℝ))
    have htmp :
        Real.rpow (81 : ℝ) (2 * s) ≤ Real.rpow (81 : ℝ) (2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (81 : ℝ)) h2s_le
    norm_num [Real.rpow_natCast] at htmp ⊢
    exact htmp
  have h3_le :
      Real.rpow (3 : ℝ) (8 * s) ≤ (6561 : ℝ) := by
    have h8s_le : 8 * s ≤ (8 : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hs1.le (by norm_num : 0 ≤ (8 : ℝ))
    have htmp :
        Real.rpow (3 : ℝ) (8 * s) ≤ Real.rpow (3 : ℝ) (8 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ)) h8s_le
    norm_num [Real.rpow_natCast] at htmp ⊢
    exact htmp
  have hmul :
      Real.rpow (81 * coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) =
        Real.rpow (81 : ℝ) (2 * s) *
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) := by
    exact Real.mul_rpow (by positivity) (coarseCaccioppoliGapInv_nonneg hlt)
  have hsplit :
      Real.rpow (3 : ℝ) (2 * s * ((k : ℝ) + 4)) =
        Real.rpow (3 : ℝ) (2 * s * (k : ℝ)) * Real.rpow (3 : ℝ) (8 * s) := by
    rw [show 2 * s * ((k : ℝ) + 4) = 2 * s * (k : ℝ) + 8 * s by ring]
    exact Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _
  calc
    C * Real.rpow (3 : ℝ) (2 * s * ((k : ℝ) + 4))
        = C * (Real.rpow (3 : ℝ) (2 * s * (k : ℝ)) * Real.rpow (3 : ℝ) (8 * s)) := by
            rw [hsplit]
    _ ≤ C * (Real.rpow (81 * coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) *
          Real.rpow (3 : ℝ) (8 * s)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hk_le
                (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
              hC
    _ = C * ((Real.rpow (81 : ℝ) (2 * s) *
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s)) *
          Real.rpow (3 : ℝ) (8 * s)) := by
            rw [hmul]
    _ ≤ C * ((6561 * Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s)) * 6561) := by
            refine mul_le_mul_of_nonneg_left ?_ hC
            refine mul_le_mul ?_ h3_le ?_ ?_
            · exact mul_le_mul_of_nonneg_right h81_le
                (Real.rpow_nonneg (coarseCaccioppoliGapInv_nonneg hlt) _)
            · exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
            · exact mul_nonneg (by positivity)
                (Real.rpow_nonneg (coarseCaccioppoliGapInv_nonneg hlt) _)
    _ = (6561 : ℝ) * 6561 * C *
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) := by
            ring

theorem coarseCaccioppoli_boundary_explicitHeight_rightBranch_scalar
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {ρ₁ ρ₂ s t C : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂) (hlt : ρ₁ < ρ₂)
    (hbranch :
      (k : ℝ) + 4 <
        (((Nat.ceil
          (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k) /
            (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)))) : ℕ) : ℝ)) :
    C * Real.rpow (3 : ℝ)
        (2 * s *
          (((Nat.ceil
            (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k) /
              (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)))) : ℕ) : ℝ)) ≤
      ((9 : ℝ) * Real.rpow (4 : ℝ) (coarseCaccioppoliPower s t) *
        Real.rpow (81 : ℝ) (coarseCaccioppoliPower s t)) * C *
        Real.rpow
          (C / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
          (coarseCaccioppoliPower s t) *
        Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliPower s t) := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let p : ℝ := coarseCaccioppoliPower s t
  let A : ℝ := coarseCaccioppoliBoundaryHeightLogArg Q a s t C k
  let M : ℝ := C / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
  let x : ℝ := Real.log A / (σ * Real.log (3 : ℝ))
  let n : ℝ := (((Nat.ceil x) : ℕ) : ℝ)
  have hσ_pos : 0 < σ := coarseCaccioppoli_sigma_pos hst
  have h2s_pos : 0 < 2 * s := by positivity
  have hp_nonneg : 0 ≤ p := coarseCaccioppoli_power_nonneg hs hst
  have hs1 : s < 1 := by linarith
  have hden_nonneg : 0 ≤ s * (1 - s) := mul_one_sub_nonneg hs.le hs1.le
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (div_nonneg hC hden_nonneg)
      (Real.rpow_nonneg htheta_nonneg _)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, coarseCaccioppoliBoundaryHeightLogArg]
    refine mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) ?_
    refine mul_nonneg ?_ (Real.rpow_nonneg htheta_nonneg _)
    exact mul_nonneg (div_nonneg hC hden_nonneg) (by positivity)
  have hkchoice :
      (3 : ℝ) ^ k ≤ 81 * coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    coarseCaccioppoli_pow_scale_le_mul_gapInv_of_triadicGapScaleChoice hchoice hlt
  have hgap_nonneg : 0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    coarseCaccioppoliGapInv_nonneg hlt
  have hceil_one_real : (1 : ℝ) ≤ n := by
    dsimp [n]
    linarith
  have hceil_one_nat : 1 ≤ Nat.ceil x := by
    dsimp [n] at hceil_one_real
    exact_mod_cast hceil_one_real
  have hx_pos : 0 < x := (Nat.one_le_ceil_iff).1 hceil_one_nat
  have hden_pos : 0 < σ * Real.log (3 : ℝ) := by
    exact mul_pos hσ_pos (Real.log_pos (by norm_num))
  have hlogA_pos : 0 < Real.log A := by
    have hx' : 0 < Real.log A / (σ * Real.log (3 : ℝ)) := by simpa [x] using hx_pos
    have hden_not_neg : ¬ σ * Real.log (3 : ℝ) < 0 := by linarith
    exact (div_pos_iff.mp hx').elim (fun h => h.1) (fun h => (hden_not_neg h.2).elim)
  have hA_pos : 0 < A := by
    have hA_gt_one : 1 < A := (Real.log_pos_iff hA_nonneg).1 hlogA_pos
    linarith
  have hceil_lt : n < x + 1 := by
    dsimp [n]
    simpa [x] using (Nat.ceil_lt_add_one hx_pos.le)
  have hmain_exp :
      2 * s * n ≤ 2 * s * (x + 1) := by
    exact mul_le_mul_of_nonneg_left hceil_lt.le h2s_pos.le
  have hpow_le :
      Real.rpow (3 : ℝ) (2 * s * n) ≤
        Real.rpow (3 : ℝ) (2 * s * (x + 1)) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ)) hmain_exp
  have hx_factor :
      2 * s * x = p * Real.logb (3 : ℝ) A := by
    have hσ_ne : σ ≠ 0 := hσ_pos.ne'
    have hlog3_ne : Real.log (3 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    calc
      2 * s * x = 2 * s * (Real.log A / (σ * Real.log (3 : ℝ))) := by rfl
      _ = (2 * s / σ) * (Real.log A / Real.log (3 : ℝ)) := by
            field_simp [hσ_ne, hlog3_ne]
      _ = p * Real.logb (3 : ℝ) A := by
            rw [Real.log_div_log]
            change (2 * s / σ) * Real.logb (3 : ℝ) A =
              (2 * s / σ) * Real.logb (3 : ℝ) A
            rfl
  have hpow_logb :
      Real.rpow (3 : ℝ) (p * Real.logb (3 : ℝ) A) = Real.rpow A p := by
    calc
      Real.rpow (3 : ℝ) (p * Real.logb (3 : ℝ) A)
          = (Real.rpow (3 : ℝ) (Real.logb (3 : ℝ) A)) ^ p := by
              simpa [mul_comm] using
                (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (Real.logb (3 : ℝ) A) p)
      _ = Real.rpow A p := by
            simpa using
              congrArg (fun y : ℝ => Real.rpow y p)
                (Real.rpow_logb (by norm_num : 0 < (3 : ℝ))
                  (by norm_num : (3 : ℝ) ≠ 1) hA_pos)
  have hthree_le :
      Real.rpow (3 : ℝ) (2 * s) ≤ (9 : ℝ) := by
    have h2s_le : 2 * s ≤ (2 : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hs1.le (by norm_num : 0 ≤ (2 : ℝ))
    have htmp :
        Real.rpow (3 : ℝ) (2 * s) ≤ Real.rpow (3 : ℝ) (2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ)) h2s_le
    norm_num [Real.rpow_natCast] at htmp ⊢
    exact htmp
  have hA_pow_le :
      Real.rpow A p ≤
        Real.rpow (4 : ℝ) p *
          Real.rpow (81 : ℝ) p *
          Real.rpow M p *
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p := by
    have hkpow_le :
        Real.rpow ((3 : ℝ) ^ k) p ≤
          Real.rpow (81 * coarseCaccioppoliGapInv ρ₁ ρ₂) p := by
      exact Real.rpow_le_rpow (by positivity) hkchoice hp_nonneg
    have hmul :
        Real.rpow (81 * coarseCaccioppoliGapInv ρ₁ ρ₂) p =
          Real.rpow (81 : ℝ) p *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p := by
      exact Real.mul_rpow (by positivity) hgap_nonneg
    calc
      Real.rpow A p = Real.rpow (4 * M * ((3 : ℝ) ^ k)) p := by
        congr 1
        dsimp [A, M, coarseCaccioppoliBoundaryHeightLogArg]
        ring
      _ = Real.rpow (4 * M) p * Real.rpow ((3 : ℝ) ^ k) p := by
            have htmp : 0 ≤ 4 * M := by positivity
            simpa [mul_assoc] using
              (Real.mul_rpow htmp (by positivity : 0 ≤ ((3 : ℝ) ^ k)) (z := p))
      _ = (Real.rpow (4 : ℝ) p * Real.rpow M p) * Real.rpow ((3 : ℝ) ^ k) p := by
            have htmp :
                Real.rpow (4 * M) p = Real.rpow (4 : ℝ) p * Real.rpow M p := by
              exact Real.mul_rpow (by positivity) hM_nonneg
            rw [htmp]
      _ ≤ (Real.rpow (4 : ℝ) p * Real.rpow M p) *
            Real.rpow (81 * coarseCaccioppoliGapInv ρ₁ ρ₂) p := by
              exact mul_le_mul_of_nonneg_left hkpow_le
                (mul_nonneg (Real.rpow_nonneg (by positivity) _)
                  (Real.rpow_nonneg hM_nonneg _))
      _ = (Real.rpow (4 : ℝ) p * Real.rpow M p) *
            (Real.rpow (81 : ℝ) p *
              Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p) := by
              rw [hmul]
      _ = Real.rpow (4 : ℝ) p *
            Real.rpow (81 : ℝ) p *
            Real.rpow M p *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p := by
              ring
  calc
    C * Real.rpow (3 : ℝ)
        (2 * s *
          (((Nat.ceil
            (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k) /
              (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)))) : ℕ) : ℝ))
        = C * Real.rpow (3 : ℝ) (2 * s * n) := by
            rfl
    _ ≤ C * Real.rpow (3 : ℝ) (2 * s * (x + 1)) := by
          exact mul_le_mul_of_nonneg_left hpow_le hC
    _ = C * (Real.rpow (3 : ℝ) (2 * s * x) * Real.rpow (3 : ℝ) (2 * s)) := by
          congr 1
          rw [show 2 * s * (x + 1) = 2 * s * x + 2 * s by ring]
          exact Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _
    _ = C * (Real.rpow A p * Real.rpow (3 : ℝ) (2 * s)) := by
          rw [hx_factor, hpow_logb]
    _ ≤ C * (Real.rpow A p * 9) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hthree_le (Real.rpow_nonneg hA_nonneg _))
            hC
    _ = 9 * C * Real.rpow A p := by ring
    _ ≤ 9 * (C * (Real.rpow (4 : ℝ) p *
          Real.rpow (81 : ℝ) p *
          Real.rpow M p *
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hA_pow_le hC)
                (by norm_num : 0 ≤ (9 : ℝ)))
    _ = ((9 : ℝ) * Real.rpow (4 : ℝ) p *
          Real.rpow (81 : ℝ) p) * C *
          Real.rpow M p *
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p := by
            ring

theorem coarseCaccioppoli_boundary_explicitHeight_rightBranch_scalar_with_front
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    {ρ₁ ρ₂ s t Calpha Ccross : ℝ} {k : ℕ}
    (hCalpha : 0 < Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂) (hlt : ρ₁ < ρ₂)
    (hbranch :
      (k : ℝ) + 4 <
        (((Nat.ceil
          (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t Calpha k) /
            (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)))) : ℕ) : ℝ)) :
    Ccross * Real.rpow (3 : ℝ)
        (2 * s *
          (((Nat.ceil
            (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t Calpha k) /
              (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)))) : ℕ) : ℝ)) ≤
      ((9 : ℝ) * Real.rpow (4 : ℝ) (coarseCaccioppoliPower s t) *
        Real.rpow (81 : ℝ) (coarseCaccioppoliPower s t)) * Ccross *
        Real.rpow
          (Calpha / (s * (1 - s)) *
            Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
          (coarseCaccioppoliPower s t) *
        Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliPower s t) := by
  let X : ℝ :=
    Real.rpow (3 : ℝ)
      (2 * s *
        (((Nat.ceil
          (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t Calpha k) /
            (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)))) : ℕ) : ℝ))
  let Y : ℝ :=
    ((9 : ℝ) * Real.rpow (4 : ℝ) (coarseCaccioppoliPower s t) *
      Real.rpow (81 : ℝ) (coarseCaccioppoliPower s t)) *
      Real.rpow
        (Calpha / (s * (1 - s)) *
          Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
        (coarseCaccioppoliPower s t) *
      Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliPower s t)
  have hmain :
      Calpha * X ≤ Calpha * Y := by
    have hraw :
        Calpha * X ≤
          ((9 : ℝ) * Real.rpow (4 : ℝ) (coarseCaccioppoliPower s t) *
            Real.rpow (81 : ℝ) (coarseCaccioppoliPower s t)) * Calpha *
            Real.rpow
              (Calpha / (s * (1 - s)) *
                Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
              (coarseCaccioppoliPower s t) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliPower s t) := by
      exact
      coarseCaccioppoli_boundary_explicitHeight_rightBranch_scalar
        Q a hCalpha.le hs ht hst hchoice hlt hbranch
    have hY :
        ((9 : ℝ) * Real.rpow (4 : ℝ) (coarseCaccioppoliPower s t) *
            Real.rpow (81 : ℝ) (coarseCaccioppoliPower s t)) * Calpha *
            Real.rpow
              (Calpha / (s * (1 - s)) *
                Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
              (coarseCaccioppoliPower s t) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliPower s t) =
          Calpha * Y := by
      ring
    exact hraw.trans_eq hY
  have hXY : X ≤ Y :=
    (mul_le_mul_iff_of_pos_left hCalpha).1 hmain
  have hfront : Ccross * X ≤ Ccross * Y :=
    mul_le_mul_of_nonneg_left hXY hCcross
  have hfront_rhs :
      Ccross * Y =
        ((9 : ℝ) * Real.rpow (4 : ℝ) (coarseCaccioppoliPower s t) *
          Real.rpow (81 : ℝ) (coarseCaccioppoliPower s t)) * Ccross *
          Real.rpow
            (Calpha / (s * (1 - s)) *
              Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
            (coarseCaccioppoliPower s t) *
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliPower s t) := by
    ring
  exact hfront.trans_eq hfront_rhs

/-- A stronger triadic-scale cross-term estimate, stated using the note's
auxiliary scale `k`, implies the actual cross-term square bound appearing in
the boundary coefficient bookkeeping. -/
theorem coarseCaccioppoli_boundary_noteCrossTermBound_of_triadicGapScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∃ k : ℕ, CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ ∧
          C * Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) ≤
            Real.rpow
                (C / (s * (1 - s)) *
                  Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
                (coarseCaccioppoliPower s t) *
              Real.rpow (((3 : ℝ) ^ k) / 81) (coarseCaccioppoliPower s t)) :
    CoarseCaccioppoliBoundaryNoteCrossTermBound Q a s t C uL2Sq h := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hscale hρ₁ hlt hρ₂ with ⟨k, hkchoice, hkbound⟩
  let M : ℝ :=
    C / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
  let p : ℝ := coarseCaccioppoliPower s t
  have hs1 : s < 1 := by
    linarith
  have hden_nonneg : 0 ≤ s * (1 - s) := mul_one_sub_nonneg hs.le hs1.le
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (div_nonneg hC hden_nonneg)
      (Real.rpow_nonneg htheta_nonneg _)
  have hp_nonneg : 0 ≤ p := coarseCaccioppoli_power_nonneg hs hst
  have hgap_nonneg : 0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    coarseCaccioppoliGapInv_nonneg hlt
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  have hbase_le : ((3 : ℝ) ^ k) / 81 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    exact (div_le_iff₀ (show (0 : ℝ) < 81 by norm_num)).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (coarseCaccioppoli_pow_scale_le_mul_gapInv_of_triadicGapScaleChoice hkchoice hlt)
  have hbase_nonneg : 0 ≤ ((3 : ℝ) ^ k) / 81 := by positivity
  have hgap_pow :
      Real.rpow (((3 : ℝ) ^ k) / 81) p ≤
        Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p := by
    exact Real.rpow_le_rpow hbase_nonneg hbase_le hp_nonneg
  have hfactor :
      C * Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) ≤
        Real.rpow M p * Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p := by
    refine le_trans hkbound ?_
    exact mul_le_mul_of_nonneg_left hgap_pow (Real.rpow_nonneg hM_nonneg _)
  have hprefix_nonneg :
      0 ≤ C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
        LambdaSq Q s (.finite 1) a * uL2Sq := by
    refine mul_nonneg (mul_nonneg ?_ hLambda_nonneg) hu
    exact mul_nonneg hC (sq_nonneg _)
  have h3sq :
      (Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) ^ (2 : ℕ) =
        Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) := by
    calc
      (Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) ^ (2 : ℕ) =
          Real.rpow (Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) (2 : ℝ) := by
            symm
            exact Real.rpow_natCast _ 2
      _ = Real.rpow (3 : ℝ) ((s * h ρ₁ ρ₂) * 2) := by
            simpa using (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (s * h ρ₁ ρ₂) (2 : ℝ)).symm
      _ = Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) := by ring_nf
  have hLambda_sq :
      (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) ^ (2 : ℕ) =
        LambdaSq Q s (.finite 1) a := by
    simpa using sq_rpow_half_eq_self_of_nonneg hLambda_nonneg
  have hcross_sq :
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂) ^ (2 : ℕ) =
        (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
          LambdaSq Q s (.finite 1) a * uL2Sq) *
          (C * Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂)) := by
    unfold coarseCaccioppoliBoundaryCrossCoeffOfHeight
    calc
      (C * coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.sqrt uL2Sq) ^ (2 : ℕ)
          =
            C ^ (2 : ℕ) * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
              (Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) ^ (2 : ℕ) *
              (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) ^ (2 : ℕ) *
              (Real.sqrt uL2Sq) ^ (2 : ℕ) := by
              ring
      _ = C ^ (2 : ℕ) * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) *
            LambdaSq Q s (.finite 1) a *
            uL2Sq := by
              rw [h3sq, hLambda_sq, Real.sq_sqrt hu]
      _ = (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            (C * Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂)) := by
              ring
  have hbound' :
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂) ^ (2 : ℕ) ≤
        (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
          LambdaSq Q s (.finite 1) a * uL2Sq) *
          (Real.rpow M p * Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p) := by
    rw [hcross_sq]
    exact mul_le_mul_of_nonneg_left hfactor hprefix_nonneg
  have hgapSqEq :
      (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) = Real.rpow (ρ₂ - ρ₁) (-2 : ℝ) := by
    rw [coarseCaccioppoliGapInv_eq_inv]
    calc
      ((ρ₂ - ρ₁)⁻¹) ^ (2 : ℕ) = Real.rpow ((ρ₂ - ρ₁)⁻¹) (2 : ℝ) := by
        symm
        exact Real.rpow_natCast _ 2
      _ = Real.rpow (ρ₂ - ρ₁) (-(2 : ℝ)) := by
            simp
      _ = Real.rpow (ρ₂ - ρ₁) (-2 : ℝ) := by ring
  have hgapPowEq :
      Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p = Real.rpow (ρ₂ - ρ₁) (-p) := by
    rw [coarseCaccioppoliGapInv_eq_inv]
    symm
    simpa using (Real.rpow_neg_eq_inv_rpow (ρ₂ - ρ₁) p)
  calc
    (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂) ^ (2 : ℕ)
        ≤ (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            (Real.rpow M p * Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p) := hbound'
    _ = C * Real.rpow M p * LambdaSq Q s (.finite 1) a * uL2Sq *
          (Real.rpow (ρ₂ - ρ₁) (-2 : ℝ) * Real.rpow (ρ₂ - ρ₁) (-p)) := by
            rw [hgapSqEq, hgapPowEq]
            ring
    _ = C * Real.rpow M p * LambdaSq Q s (.finite 1) a * uL2Sq *
          Real.rpow (ρ₂ - ρ₁) (-(2 : ℝ) + (-p)) := by
            congr 1
            symm
            exact Real.rpow_add (sub_pos.mpr hlt) (-2 : ℝ) (-p)
    _ = C * Real.rpow M p * LambdaSq Q s (.finite 1) a * uL2Sq *
          Real.rpow (ρ₂ - ρ₁) (-(coarseCaccioppoliBeta s t)) := by
            rw [coarseCaccioppoli_beta_eq_two_add_power hst]
            dsimp [p]
            congr 2
            ring
    _ = (C * Real.rpow M p * LambdaSq Q s (.finite 1) a * uL2Sq) *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
            ring
    _ = coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
            change
              (C * Real.rpow M p * LambdaSq Q s (.finite 1) a * uL2Sq) *
                  Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) =
                (C * Real.rpow M p * LambdaSq Q s (.finite 1) a * uL2Sq) *
                  Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t)
            rfl

end

end Homogenization
