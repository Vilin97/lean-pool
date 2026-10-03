/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFluxPointwise

/-! # Abstract real inequalities for the pointwise bounds of the `twistie4`, `twistie5` fluxes

Pure real algebra (no transcendental functions): the final squaring steps of
`sd_flux_bound` and `sd_slow_pointwise`. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

theorem scf_flux_sq {v : Vec 2} {e P gT C : ℝ} (hC : 2 * C ^ 2 ≤ 64 ^ 2) (h : ∀ i, |v i| ≤ C * (e
    * P * gT)) :
    vecNormSq v ≤ (64 * (e * P)) ^ 2 * gT ^ 2 := by
  have h2 := sa_vecNormSq_le h
  have hq : 0 ≤ (e * P * gT) ^ 2 := sq_nonneg _
  calc vecNormSq v ≤ 2 * (C * (e * P * gT)) ^ 2 := h2
    _ = (2 * C ^ 2) * (e * P * gT) ^ 2 := by ring
    _ ≤ 64 ^ 2 * (e * P * gT) ^ 2 := mul_le_mul_of_nonneg_right hC hq
    _ = _ := by ring

theorem scf_slow_abs {ξ K S B : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hK : 0 ≤ K)
    (hS : |S| ≤ B) : |ξ * K * S| ≤ K * B := by
  rw [abs_mul, abs_mul, abs_of_nonneg hξ0, abs_of_nonneg hK]
  calc ξ * K * |S| ≤ 1 * K * B :=
        mul_le_mul (mul_le_mul hξ1 le_rfl hK zero_le_one) hS (abs_nonneg _) (by positivity)
    _ = K * B := by ring

theorem scf_slow_abs' {ξ S B : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hS : |S| ≤ B) : |ξ * S| ≤ B := by
  have := scf_slow_abs hξ0 hξ1 zero_le_one hS
  simpa using this

/-- The squaring step of the slow factors: with `K = κ` or `1`, `q = ε_{m-1}⁻¹`. -/
theorem scf_slow_sq {f K e q gT h0 h1 : ℝ} (hK : 0 ≤ K) (he : 0 ≤ e) (hq : 0 ≤ q)
    (hg : 0 ≤ gT) (h0n : 0 ≤ h0) (h1n : 0 ≤ h1)
    (hf : |f| ≤ K * e * (4 * h0 + 4 * h1 + 16 * (2 ^ 16 * q) * gT)) :
    f ^ 2 ≤ ((28 * 2 ^ 16) * K * e * q) ^ 2 * gT ^ 2 + (7 * K * e) ^ 2 * (h0 ^ 2 + h1 ^ 2) := by
  set u := K * e with hu
  have hu0 : 0 ≤ u := mul_nonneg hK he
  set s := 4 * h0 + 4 * h1 + 16 * (2 ^ 16 * q) * gT with hs
  have hs0 : 0 ≤ s := by positivity
  have hf2 : f ^ 2 ≤ (u * s) ^ 2 := by
    have := sq_le_sq' (abs_le.1 hf).1 (abs_le.1 hf).2
    simpa [hu] using this
  have h3 := sa_sq3 (4 * h0) (4 * h1) (16 * (2 ^ 16 * q) * gT)
  have hs2 : s ^ 2 ≤ 48 * h0 ^ 2 + 48 * h1 ^ 2 + 768 * (2 ^ 16 * q) ^ 2 * gT ^ 2 := by
    rw [hs]; nlinarith [h3]
  have hq2 : 0 ≤ (u * (2 ^ 16 * q) * gT) ^ 2 := sq_nonneg _
  have hh0 : 0 ≤ (u * h0) ^ 2 := sq_nonneg _
  have hh1 : 0 ≤ (u * h1) ^ 2 := sq_nonneg _
  calc f ^ 2 ≤ (u * s) ^ 2 := hf2
    _ = u ^ 2 * s ^ 2 := by ring
    _ ≤ u ^ 2 * (48 * h0 ^ 2 + 48 * h1 ^ 2 + 768 * (2 ^ 16 * q) ^ 2 * gT ^ 2) :=
        mul_le_mul_of_nonneg_left hs2 (sq_nonneg u)
    _ ≤ _ := by
        have e1 : (28 * 2 ^ 16 * K * e * q) ^ 2 * gT ^ 2 = 784 * (u * (2 ^ 16 * q) * gT) ^ 2 := by
          rw [hu]; ring
        have e2 : (7 * K * e) ^ 2 * (h0 ^ 2 + h1 ^ 2) = 49 * (u * h0) ^ 2 + 49 * (u * h1) ^ 2 := by
          rw [hu]; ring
        have e3 : u ^ 2 * (48 * h0 ^ 2 + 48 * h1 ^ 2 + 768 * (2 ^ 16 * q) ^ 2 * gT ^ 2) =
            48 * (u * h0) ^ 2 + 48 * (u * h1) ^ 2 + 768 * (u * (2 ^ 16 * q) * gT) ^ 2 := by ring
        rw [e1, e2, e3]
        linarith

end AVenhance.Infra.Section5.Contracts
end
