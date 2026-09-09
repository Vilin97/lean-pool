/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketWeights
public import LeanPool.NavierStokesAndEuler.Euler.H6Pressure
import LeanPool.NavierStokesAndEuler.Euler.H6PressureInverse
import Mathlib.Algebra.Order.Star.Real

/-! Explicit polynomial dependence of the fixed-order inverse on coefficient bounds. -/

@[expose] public section


noncomputable section

namespace EulerH6Pressure

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerJetProductBounds  EulerPressureSpatialRegularity
open scoped Topology

variable (period : ℝ) [Fact (0 < period)] {directions : Fin 4 → LiftTangent}

omit [Fact (0 < period)] in
theorem coefficient_restrict_level {s q n : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (hq : q ≤ s) (hn : n ≤ q) :
    boundLevel period (CoefficientJet.restrict K q hq) n = boundLevel period K n := by
  induction q generalizing s A n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst n
    simp [CoefficientJet.restrict, boundLevel]
  | succ q ih =>
    cases s with
    | zero => omega
    | succ s =>
      cases K with
      | succ dA lower hd =>
        cases n with
        | zero => simp only [CoefficientJet.restrict, boundLevel]
        | succ n =>
          simp only [CoefficientJet.restrict, boundLevel]
          exact Finset.sum_congr rfl (fun i _ => ih (lower i) (by omega) (by omega))

variable {period}

omit [Fact (0 < period)] in
/-- Uniform coefficient level bounds pass to every immediate derivative subtree. -/
theorem coefficient_child_levels {s : ℕ} {A : SmoothCoefficient period}
    (dA : Fin 4 → SmoothCoefficient period)
    (lower : ∀ i, EulerSpatialSobolevInverse.CoefficientJet period directions s (dA i))
    (hd : ∀ i x, (dA i).coefficient x = EulerTransportDerivatives.fieldDerivative period
        (directions i) A.coefficient x)
    (L : ℝ)
    (h : ∀ r ≤ s + 1, boundLevel period (.succ dA lower hd) r ≤ L) (i : Fin 4) :
    ∀ r ≤ s, boundLevel period (lower i) r ≤ L := by
  intro r hr
  have hs := h (r + 1) (by omega)
  rw [boundLevel] at hs
  exact (Finset.single_le_sum (fun j _ => boundLevel_nonneg (lower j)) (Finset.mem_univ i)).trans hs

omit [Fact (0 < period)] in
/-- The fixed-order multiplier constant has an explicit polynomial bound. -/
theorem productConstant_polynomial {q : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions q A)
    (L : ℝ) (hL : 0 ≤ L) (hcoeff : ∀ r ≤ q, boundLevel period K r ≤ L) :
    K.productConstant ≤ (9 : ℝ) ^ q * L := by
  induction q generalizing A with
  | zero =>
    cases K
    simpa [EulerSpatialSobolevInverse.CoefficientJet.productConstant, boundLevel] using hcoeff 0 (by
        omega)
  | succ q ih =>
    cases K with
    | succ dA lower hd =>
      let K := EulerSpatialSobolevInverse.CoefficientJet.succ dA lower hd
      have ht : ∀ r ≤ q, boundLevel period K.truncate r ≤ L := by
        intro r hr
        rw [boundLevel_truncate K hr]
        exact hcoeff r (by omega)
      have hbase := ih K.truncate ht
      have hchild : ∀ i, (lower i).productConstant ≤ (9 : ℝ) ^ q * L :=
        fun i => ih (lower i) (coefficient_child_levels dA lower hd L hcoeff i)
      have hzero : (A.bound : ℝ) ≤ L := by simpa only [boundLevel] using hcoeff 0 (by omega)
      have hpower : L ≤ (9 : ℝ) ^ q * L := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)) hL
      calc
        _ = (A.bound : ℝ) + ∑ i : Fin 4,
            (K.truncate.productConstant + (lower i).productConstant) := by
          rw [EulerSpatialSobolevInverse.CoefficientJet.productConstant]
        _ ≤ L + ∑ _i : Fin 4, ((9 : ℝ) ^ q * L + (9 : ℝ) ^ q * L) :=
          add_le_add hzero (Finset.sum_le_sum (fun i _ => add_le_add hbase (hchild i)))
        _ = L + 8 * ((9 : ℝ) ^ q * L) := by simp; ring
        _ ≤ (9 : ℝ) ^ (q + 1) * L := by rw [pow_succ]; nlinarith only [hpower]

/-- A simple bound used to keep the inverse majorant polynomial at each fixed order. -/
theorem succ_le_three_pow (q : ℕ) : q + 1 ≤ 3 ^ q := by
  induction q with
  | zero => norm_num
  | succ q ih => rw [pow_succ]; omega

/-- The inverse majorant dominates nine times the fixed-order multiplier majorant. -/
theorem inverse_majorant_dominates (q : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    9 * ((9 : ℝ) ^ q * L) ≤ (9 * L) ^ (3 ^ q) := by
  have hp : 1 ≤ L ^ q := one_le_pow₀ hL
  have hstep : L ≤ L ^ (q + 1) := by
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ L)
  calc
    _ = (9 : ℝ) ^ (q + 1) * L := by rw [pow_succ]; ring
    _ ≤ (9 : ℝ) ^ (q + 1) * L ^ (q + 1) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (9 * L) ^ (q + 1) := (mul_pow ..).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (succ_le_three_pow q)

/-- One stage of the explicit polynomial inverse bound. -/
theorem inverse_majorant_step {L B M : ℝ} (hL : 1 ≤ L) (hB : L ≤ B) (hM : 9 * B ≤ M) :
    L + 4 * (M * (1 + B * M)) ≤ M ^ 3 := by
  have hM9 : 9 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hLleM : L ≤ M := by linarith
  have hM2 : 81 ≤ M ^ 2 := by nlinarith only [hM9]
  have hcube := mul_le_mul_of_nonneg_right hM2 hM0
  have hprod := mul_le_mul_of_nonneg_right hM (sq_nonneg M)
  have hcubepos : 0 ≤ M ^ 3 := by positivity
  nlinarith only [hLleM, hcube, hprod, hcubepos]

omit [Fact (0 < period)] in
/-- Every fixed-order coercive inverse constant is bounded by an explicit polynomial in L.
At the source's Sobolev index6 the exponent is729, independent of the external cutoff. -/
theorem pressureConstant_polynomial {q : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions q A)
    (c L : ℝ) (hc : 0 < c) (hL : 1 ≤ L) (hcL : c⁻¹ ≤ L)
    (hcoeff : ∀ r ≤ q, boundLevel period K r ≤ L) :
    K.pressureConstant c ≤ (9 * L) ^ (3 ^ q) := by
  induction q generalizing A with
  | zero =>
    cases K
    simp only [EulerSpatialSobolevInverse.CoefficientJet.pressureConstant, pow_zero, pow_one]
    linarith
  | succ q ih =>
    cases K with
    | succ dA lower hd =>
      let K := EulerSpatialSobolevInverse.CoefficientJet.succ dA lower hd
      let B : ℝ := (9 : ℝ) ^ q * L
      let M : ℝ := (9 * L) ^ (3 ^ q)
      have ht : ∀ r ≤ q, boundLevel period K.truncate r ≤ L := by
        intro r hr
        rw [boundLevel_truncate K hr]
        exact hcoeff r (by omega)
      have hbase : K.truncate.pressureConstant c ≤ M := ih K.truncate ht
      have hchild : ∀ i, (lower i).productConstant ≤ B :=
        fun i => productConstant_polynomial (lower i) L (by linarith)
          (coefficient_child_levels dA lower hd L hcoeff i)
      have hB : L ≤ B := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)) (by linarith : 0 ≤ L)
      have hM : 9 * B ≤ M := inverse_majorant_dominates q hL
      have hM0 : 0 ≤ M := by dsimp [M]; positivity
      have hbase0 : 0 ≤ K.truncate.pressureConstant c := K.truncate.pressureConstant_nonneg c hc
      have hB0 : 0 ≤ B := by linarith
      have hterm : ∀ i, K.truncate.pressureConstant c *
          (1 + (lower i).productConstant * K.truncate.pressureConstant c) ≤ M * (1 + B * M) := by
        intro i
        exact mul_le_mul hbase
          (add_le_add le_rfl (mul_le_mul (hchild i) hbase hbase0 hB0))
          (add_nonneg zero_le_one (mul_nonneg (lower i).productConstant_nonneg hbase0)) hM0
      calc
        _ = c⁻¹ + ∑ i : Fin 4, K.truncate.pressureConstant c *
            (1 + (lower i).productConstant * K.truncate.pressureConstant c) := by
          rw [EulerSpatialSobolevInverse.CoefficientJet.pressureConstant]
        _ ≤ L + ∑ _i : Fin 4, M * (1 + B * M) :=
          add_le_add hcL (Finset.sum_le_sum (fun i _ => hterm i))
        _ = L + 4 * (M * (1 + B * M)) := by simp
        _ ≤ M ^ 3 := inverse_majorant_step hL hB hM
        _ = (9 * L) ^ (3 ^ (q + 1)) := by dsimp [M]; rw [← pow_mul, pow_succ]

/-- The shifted Hq pressure estimate with an explicit polynomial coefficient constant.
All assumptions concern the actual coefficient, its derivative bounds, and coercivity. -/
theorem pressure_shifted_Hq_polynomial_bound {s q : ℕ} {A : SmoothCoefficient period} {f : LiftL2
    period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + q ≤ s) (L ρ Rc : ℝ)
    (hL : 1 ≤ L) (hcL : c⁻¹ ≤ L) (hρ : 0 < ρ) (hRc : 0 ≤ Rc)
    (hbasecoeff : ∀ r ≤ q, boundLevel period K r ≤ L)
    (hsmall : 4 * (9 * L) ^ (3 ^ q) * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N →
      coefficientBlock period K q l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2) :
    (∑ n ∈ Finset.range (N + 1), ((n + 1 : ℕ) : ℝ) * EulerPacketWeights.weight ρ (n + 1) *
      blockNorm period (J.solvePressure K κ m c hc hpos) q n) ≤
      2 * (9 * L) ^ (3 ^ q) * ∑ n ∈ Finset.range (N + 1),
        ((n + 1 : ℕ) : ℝ) * EulerPacketWeights.weight ρ (n + 1) * blockNorm period J q n := by
  have hq : q ≤ s := by omega
  have hbase : (CoefficientJet.restrict K q hq).pressureConstant c ≤ (9 * L) ^ (3 ^ q) := by
    apply pressureConstant_polynomial _ c L hc hL hcL
    intro r hr
    rw [coefficient_restrict_level period K hq hr]
    exact hbasecoeff r hr
  exact pressure_shifted_Hq_bound K J κ m c hc hpos N hN hq ρ Rc ((9 * L) ^ (3 ^ q))
    hρ hRc (one_le_pow₀ (by linarith)) hbase hsmall hcoeff

end EulerH6Pressure
