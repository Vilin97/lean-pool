/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-! Exact shift gains and the final coarse factorial splitting for finite packets. -/

namespace EulerGevrey

theorem majorant_succ_identity (R : ℝ) (d n : ℕ) :
    majorant R (d+1) n=R*((n+d+1 : ℕ) : ℝ)^2*majorant R d n := by
  simp only [majorant, show n+(d+1)=n+d+1 by omega, Nat.factorial_succ,
    Nat.cast_mul, pow_succ]
  ring

theorem majorant_mono_shift (R : ℝ) (hR : 1 ≤ R) (d D n : ℕ) (h : d ≤ D) :
    majorant R d n ≤ majorant R D n := by
  have hf : ((n+d).factorial : ℝ) ≤ ((n+D).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.add_le_add_left h n)
  have hs : ((n+d).factorial : ℝ)^2 ≤ ((n+D).factorial : ℝ)^2 :=
    pow_le_pow_left₀ (by positivity) hf 2
  exact mul_le_mul (pow_le_pow_right₀ hR (Nat.add_le_add_left h n)) hs
    (sq_nonneg _) (pow_nonneg (by linarith) _)

/-- A single spare shift pays a linear number of grade terms at one fixed radius. -/
theorem linear_grade_cost_absorbed (C R : ℝ) (hC : 0 ≤ C) (hR : C ≤ R)
    (p d n : ℕ) (hd : 0 < d) (hpd : p ≤ d) :
    (C*(p : ℝ))*majorant R (d-1) n ≤ majorant R d n := by
  have hR0 : 0 ≤ R := hC.trans hR
  have hnd : (1 : ℝ) ≤ ((n+d : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+d by omega)
  have hpnd : (p : ℝ) ≤ ((n+d : ℕ) : ℝ) := by exact_mod_cast (show p ≤ n+d by omega)
  have hpsq : (p : ℝ) ≤ ((n+d : ℕ) : ℝ)^2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ ((n+d : ℕ) : ℝ) by positivity) (sub_nonneg.mpr hnd)]
  have hcost : C*(p : ℝ) ≤ R*((n+d : ℕ) : ℝ)^2 :=
    (mul_le_mul_of_nonneg_left hpsq hC).trans (mul_le_mul_of_nonneg_right hR (sq_nonneg _))
  calc
    _ ≤ (R*((n+d : ℕ) : ℝ)^2)*majorant R (d-1) n :=
      mul_le_mul_of_nonneg_right hcost (majorant_nonneg R hR0 _ _)
    _ = majorant R d n := by
      have h := majorant_succ_identity R (d-1) n
      rw [show d-1+1=d by omega, show n+(d-1)+1=n+d by omega] at h
      exact h.symm

theorem factorial_sum_split (n d : ℕ) :
    (n+d).factorial ≤ 2^(n+d)*n.factorial*d.factorial := by
  calc
    (n+d).factorial=(n+d).choose n*n.factorial*d.factorial := by
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.choose_mul_factorial_mul_factorial (show n ≤ n+d by omega)).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.choose_le_two_pow (n+d) n))

/-- Used once at the final coarse split, or for a fixed coefficient shift. -/
theorem majorant_coarse_split (R : ℝ) (hR : 0 ≤ R) (d n : ℕ) :
    majorant R d n ≤ ((4*R)^d*(d.factorial : ℝ)^2)*majorant (4*R) 0 n := by
  have hf : ((n+d).factorial : ℝ) ≤ (2 : ℝ)^(n+d)*(n.factorial : ℝ)*(d.factorial : ℝ) := by
    exact_mod_cast factorial_sum_split n d
  have hs := pow_le_pow_left₀ (show (0 : ℝ) ≤ ((n+d).factorial : ℝ) by positivity) hf 2
  have hpow : ((2 : ℝ)^(n+d))^2=(4 : ℝ)^(n+d) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  calc
    majorant R d n ≤ R^(n+d)*((2 : ℝ)^(n+d)*(n.factorial : ℝ)*(d.factorial : ℝ))^2 :=
      mul_le_mul_of_nonneg_left hs (pow_nonneg hR _)
    _ = (4*R)^(n+d)*(n.factorial : ℝ)^2*(d.factorial : ℝ)^2 := by
      simp only [mul_pow, hpow]
      ring
    _ = _ := by
      simp only [majorant, Nat.add_zero, pow_add]
      ring

end EulerGevrey
