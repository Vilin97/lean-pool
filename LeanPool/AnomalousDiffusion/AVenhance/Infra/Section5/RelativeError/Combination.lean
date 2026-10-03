/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Basic.Real.Basic

/-!# RelativeError: abstract low/high frequency recombination

This module isolates the scalar part of the RelativeError trace/tail argument.  The
Fourier trace estimate, analytic tail estimate, and mean-zero energy estimate
are inputs to `e44_combine_low_mode_and_analytic_tail`; the exponential
absorption needed to use them is stated explicitly.
-/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

/-- Combine a dissipation-controlled low-frequency estimate with an analytic
high-frequency tail estimate.  The hypothesis `habs` is the precise numeric
absorption of the Poincare loss by the exponential tail.  It is kept separate
from any parameter-sequence instantiation, as in RelativeError (6)--(7). -/
theorem e44_combine_low_mode_and_analytic_tail
    {n : ℕ} {r R A ν S N Cₚ Cₜ c : ℝ}
    (hr : 0 < r) (hR : r ≤ R) (hA : 1 ≤ A)
    (hν : 0 < ν) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hCp : 0 ≤ Cₚ) (hCt : 1 ≤ Cₜ)
    (habs : (Real.sqrt ν)⁻¹ * Real.exp (-c * R * (A / r)) ≤ 1)
    (hPoincare : N ≤ Cₚ * (Real.sqrt ν)⁻¹ * S)
    (low high total : ℝ)
    (hlow : low ≤ 2 * Real.exp 1 * (A / r) ^ n * S)
    (hhigh : high ≤ Cₜ * (n.factorial : ℝ) * (Cₜ / R) ^ n *
      Real.exp (-c * R * (A / r)) * N)
    (htotal : total ≤ low + high) :
    total ≤ (2 * Real.exp 1 + Cₜ * Cₚ) * (n.factorial : ℝ) *
      (max A Cₜ / r) ^ n * S := by
  have hrR : 0 < R := lt_of_lt_of_le hr hR
  have hsqrt : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have he : 0 ≤ Real.exp (-c * R * (A / r)) := Real.exp_nonneg _
  have hsmall :
      Real.exp (-c * R * (A / r)) * N ≤ Cₚ * S := by
    calc
      Real.exp (-c * R * (A / r)) * N ≤
          Real.exp (-c * R * (A / r)) * (Cₚ * (Real.sqrt ν)⁻¹ * S) :=
        mul_le_mul_of_nonneg_left hPoincare he
      _ = (Cₚ * S) * ((Real.sqrt ν)⁻¹ * Real.exp (-c * R * (A / r))) := by ring
      _ ≤ Cₚ * S := by
        have hCS : 0 ≤ Cₚ * S := mul_nonneg hCp hS
        nlinarith [mul_le_mul_of_nonneg_left habs hCS]
  have hscaleA : A ≤ max A Cₜ := le_max_left _ _
  have hscaleT : Cₜ ≤ max A Cₜ := le_max_right _ _
  have hscalePos : 0 < max A Cₜ := by
    exact lt_of_lt_of_le (by linarith [hA]) hscaleA
  have hscaleBase : A / r ≤ max A Cₜ / r := by
    exact (div_le_div_iff₀ hr hr).2 (by nlinarith)
  have hfreqBase : Cₜ / R ≤ max A Cₜ / r := by
    apply (div_le_div_iff₀ hrR hr).2
    have h₁ : Cₜ * r ≤ max A Cₜ * r :=
      mul_le_mul_of_nonneg_right hscaleT hr.le
    have h₂ : max A Cₜ * r ≤ max A Cₜ * R :=
      mul_le_mul_of_nonneg_left hR (le_of_lt hscalePos)
    exact le_trans h₁ h₂
  have hpowA : (A / r) ^ n ≤ (max A Cₜ / r) ^ n := by
    exact pow_le_pow_left₀ (by positivity) hscaleBase n
  have hpowT : (Cₜ / R) ^ n ≤ (max A Cₜ / r) ^ n := by
    exact pow_le_pow_left₀ (by positivity) hfreqBase n
  have hfact : 1 ≤ (n.factorial : ℝ) := by
    have hpos : 0 < n.factorial := Nat.factorial_pos n
    exact_mod_cast (show (1 : ℕ) ≤ n.factorial by omega)
  have hlow' : low ≤ 2 * Real.exp 1 *
      ((n.factorial : ℝ) * (max A Cₜ / r) ^ n * S) := by
    calc
      low ≤ 2 * Real.exp 1 * (A / r) ^ n * S := hlow
      _ ≤ 2 * Real.exp 1 * (max A Cₜ / r) ^ n * S := by
        gcongr
      _ ≤ 2 * Real.exp 1 *
          ((n.factorial : ℝ) * (max A Cₜ / r) ^ n * S) := by
        have hexp : 0 ≤ 2 * Real.exp 1 := by positivity
        have hpow : 0 ≤ (max A Cₜ / r) ^ n := by positivity
        have hscaled :
            (max A Cₜ / r) ^ n * S ≤
              (n.factorial : ℝ) * ((max A Cₜ / r) ^ n * S) := by
          calc
            (max A Cₜ / r) ^ n * S =
                1 * ((max A Cₜ / r) ^ n * S) := by ring
            _ ≤ (n.factorial : ℝ) * ((max A Cₜ / r) ^ n * S) :=
              mul_le_mul_of_nonneg_right hfact (mul_nonneg hpow hS)
        calc
          2 * Real.exp 1 * (max A Cₜ / r) ^ n * S =
              (2 * Real.exp 1) * ((max A Cₜ / r) ^ n * S) := by ring
          _ ≤ (2 * Real.exp 1) *
              ((n.factorial : ℝ) * ((max A Cₜ / r) ^ n * S)) := by
            exact mul_le_mul_of_nonneg_left hscaled hexp
          _ = 2 * Real.exp 1 *
              ((n.factorial : ℝ) * (max A Cₜ / r) ^ n * S) := by ring
  have hhigh' : high ≤ Cₜ * Cₚ *
      ((n.factorial : ℝ) * (max A Cₜ / r) ^ n * S) := by
    calc
      high ≤ Cₜ * (n.factorial : ℝ) * (Cₜ / R) ^ n *
          (Real.exp (-c * R * (A / r)) * N) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hhigh
      _ ≤ Cₜ * (n.factorial : ℝ) * (max A Cₜ / r) ^ n * (Cₚ * S) := by
        have hcoeff₁ :
            Cₜ * (n.factorial : ℝ) * (Cₜ / R) ^ n ≤
              Cₜ * (n.factorial : ℝ) * (max A Cₜ / r) ^ n := by
          have hnonneg : 0 ≤ Cₜ * (n.factorial : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left hpowT hnonneg
        have hcoeff : 0 ≤ Cₜ * (n.factorial : ℝ) * (max A Cₜ / r) ^ n := by
          positivity
        calc
          Cₜ * (n.factorial : ℝ) * (Cₜ / R) ^ n *
              (Real.exp (-c * R * (A / r)) * N) ≤
              (Cₜ * (n.factorial : ℝ) * (max A Cₜ / r) ^ n) *
                (Real.exp (-c * R * (A / r)) * N) :=
            mul_le_mul_of_nonneg_right hcoeff₁ (mul_nonneg he hN)
          _ ≤ (Cₜ * (n.factorial : ℝ) * (max A Cₜ / r) ^ n) *
                (Cₚ * S) := mul_le_mul_of_nonneg_left hsmall hcoeff
      _ = Cₜ * Cₚ *
          ((n.factorial : ℝ) * (max A Cₜ / r) ^ n * S) := by ring
  have hsum : low + high ≤
      (2 * Real.exp 1 + Cₜ * Cₚ) *
        ((n.factorial : ℝ) * (max A Cₜ / r) ^ n * S) := by
    have := add_le_add hlow' hhigh'
    nlinarith [this]
  calc
    total ≤ low + high := htotal
    _ ≤ (2 * Real.exp 1 + Cₜ * Cₚ) *
        ((n.factorial : ℝ) * (max A Cₜ / r) ^ n * S) := hsum
    _ = (2 * Real.exp 1 + Cₜ * Cₚ) * (n.factorial : ℝ) *
        (max A Cₜ / r) ^ n * S := by ring

end AVenhance.Infra.Section5.RelativeError

end
