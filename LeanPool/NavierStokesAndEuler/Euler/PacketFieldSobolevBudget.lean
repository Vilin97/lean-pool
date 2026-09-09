/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldSobolev
public import LeanPool.NavierStokesAndEuler.Euler.PacketTailBound

@[expose] public section

/-! Actual packet word bounds give the finite weighted Sobolev budgets
used by the nonlinear correction, with no change to the spatial radius. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set Finset EulerSmoothLimit EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerPacketProfileRecursion EulerParameterWordGevrey EulerGevrey EulerPacketWeights
  EulerH6Pressure EulerSobolevGevreyOperators EulerPacketTailBound

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}
  {G : Field P T raw} {q d : ℕ} {R A : ℝ}

theorem WordBound.toFieldTower_weightedNorm_le (hG : G.WordBound q R A d)
    (s N : ℕ) (hN : N+q ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (t : Icc (0 : ℝ) T) :
    weightedNorm P q N ρ (G.toFieldTower.realization s t) ≤
      A*(∑ n ∈ range (N+1), weight ρ n*majorant R d n) := by
  calc
    _ ≤ ∑ n ∈ range (N+1), weight ρ n*(A*majorant R d n) := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left
        ((G.toFieldTower_blockNorm_le s q n (by have := mem_range.mp hn; omega) t).trans (hG n))
        (weight_pos hρ n).le
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      ring

theorem WordBound.toFieldTower_weightedDerivativeNorm_le (hG : G.WordBound q R A d)
    (s N : ℕ) (hN : N+q ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (t : Icc (0 : ℝ) T) :
    (∑ i : Fin 4, weightedNorm P q N ρ
      (derivativeOperator P s i (G.toFieldTower.realization (s+1) t))) ≤
      A*(∑ n ∈ range (N+1), weight ρ n*majorant R (d+1) n) := by
  have hb (n : ℕ) (hn : n ∈ range (N+1)) :
      (∑ i : Fin 4, blockNorm P
        (toJet P (derivativeOperator P s i (G.toFieldTower.realization (s+1) t))) q n) ≤
        A*majorant R (d+1) n := by
    have h := (G.toFieldTower_derivative_block_sum_le s q n
      (by have := mem_range.mp hn; omega) t).trans (hG (n+1))
    simpa only [majorant, show n+1+d=n+(d+1) by omega] using h
  calc
    _ = ∑ n ∈ range (N+1), weight ρ n*(∑ i : Fin 4, blockNorm P
        (toJet P (derivativeOperator P s i (G.toFieldTower.realization (s+1) t))) q n) := by
      unfold weightedNorm
      rw [sum_comm]
      simp only [mul_sum]
    _ ≤ ∑ n ∈ range (N+1), weight ρ n*(A*majorant R (d+1) n) :=
      sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hb n hn) (weight_pos hρ n).le)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      ring

theorem weight_majorant_zero (ρ R : ℝ) (n : ℕ) :
    weight ρ n*majorant R 0 n = (ρ*R)^n := by
  unfold weight majorant
  simp only [Nat.add_zero, mul_pow]
  field_simp [factorial_cast_ne_zero n]

theorem weight_majorant_one (ρ R : ℝ) (n : ℕ) :
    weight ρ n*majorant R 1 n = R*((ρ*R)^n*((n+1 : ℕ) : ℝ)^2) := by
  rw [show (1 : ℕ)=0+1 from rfl, majorant_succ_identity]
  simp only [Nat.add_zero]
  calc
    _ = R*((weight ρ n*majorant R 0 n)*((n+1 : ℕ) : ℝ)^2) := by ring
    _ = _ := by rw [weight_majorant_zero]

private theorem half_square_sum_identity (N : ℕ) :
    (∑ n ∈ range N, (1/2 : ℝ)^n*((n+1 : ℕ) : ℝ)^2) +
      (2*(N : ℝ)^2+8*(N : ℝ)+12)*(1/2 : ℝ)^N = 12 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ, pow_succ (1/2 : ℝ) N]
    convert ih using 1
    push_cast
    ring

theorem square_geometric_le_twelve (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) (N : ℕ) :
    (∑ n ∈ range N, r^n*((n+1 : ℕ) : ℝ)^2) ≤ 12 := by
  have hs : (∑ n ∈ range N, (1/2 : ℝ)^n*((n+1 : ℕ) : ℝ)^2) ≤ 12 := by
    have h := half_square_sum_identity N
    have hp : 0 ≤ (2*(N : ℝ)^2+8*(N : ℝ)+12)*(1/2 : ℝ)^N := by positivity
    linarith only [h, hp]
  exact (sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hr hrhalf n) (sq_nonneg _))).trans hs

/-- The unshifted all-order packet estimate yields a cutoff-independent
background or residual budget, with the original word radius R. -/
theorem WordBound.toFieldTower_weightedNorm_le_two (hG : G.WordBound q R A 0)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (s N : ℕ) (hN : N+q ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ*R ≤ 1/2) (t : Icc (0 : ℝ) T) :
    weightedNorm P q N ρ (G.toFieldTower.realization s t) ≤ 2*A := by
  have h := hG.toFieldTower_weightedNorm_le s N hN ρ hρ t
  simp_rw [weight_majorant_zero] at h
  exact h.trans ((mul_le_mul_of_nonneg_left
    (sum_geometric_le_two (ρ*R) (mul_nonneg hρ.le hR) hsmall (N+1)) hA).trans_eq (by ring))

/-- All four actual derivative budgets together cost 12*A*R, independent
of the cutoff and with no extra alphabet factor. -/
theorem WordBound.toFieldTower_weightedDerivativeNorm_le_twelve (hG : G.WordBound q R A 0)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (s N : ℕ) (hN : N+q ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ*R ≤ 1/2) (t : Icc (0 : ℝ) T) :
    (∑ i : Fin 4, weightedNorm P q N ρ
      (derivativeOperator P s i (G.toFieldTower.realization (s+1) t))) ≤ 12*A*R := by
  have h := hG.toFieldTower_weightedDerivativeNorm_le s N hN ρ hρ t
  simp_rw [show (0+1 : ℕ)=1 from rfl, weight_majorant_one] at h
  rw [← mul_sum] at h
  exact h.trans ((mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (square_geometric_le_twelve (ρ*R) (mul_nonneg hρ.le hR) hsmall (N+1)) hR) hA).trans_eq (by
        ring))

end EulerPacketCylinderField.Field
