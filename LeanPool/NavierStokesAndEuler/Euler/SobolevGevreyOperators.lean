/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevCoefficientPressure
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketWeights
public import LeanPool.NavierStokesAndEuler.Euler.H6NonlinearProduct
public import LeanPool.NavierStokesAndEuler.Euler.H6Pressure
public import LeanPool.NavierStokesAndEuler.Euler.SobolevProduct
import LeanPool.NavierStokesAndEuler.Euler.SobolevGevreyProduct
import LeanPool.NavierStokesAndEuler.Euler.UnshiftedPressure
import LeanPool.NavierStokesAndEuler.Euler.UnshiftedProducts

/-! Actual coefficient and pressure operators on finite weighted Sobolev sums. -/

@[expose] public section


noncomputable section

namespace EulerSobolevGevreyOperators

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevL2Product EulerH6Nonlinear EulerH6Pressure
      EulerJetProductBounds
  EulerPacketWeights EulerSobolevGevreyProduct EulerSobolevCoefficientPressure
      EulerPressureJetIdentities
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The truncated Gevrey sum of genuine fixed-order Sobolev blocks. -/
def weightedNorm {s : ℕ} (q N : ℕ) (ρ : ℝ) (u : SobolevSpace period s) : ℝ :=
  ∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period (toJet period u) q n

/-- Weighted coefficient derivative bounds in the same fixed base norm. -/
def weightedCoefficient {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A) (q N : ℕ) (ρ : ℝ)
        : ℝ :=
  ∑ n ∈ Finset.range (N+1), weight ρ n * coefficientBlock period K q n

theorem weightedNorm_nonneg {s : ℕ} (q N : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (u : SobolevSpace period s) :
    0 ≤ weightedNorm period q N ρ u :=
  Finset.sum_nonneg fun n _ => mul_nonneg (weight_pos hρ n).le (blockNorm_nonneg _)

omit [Fact (0 < period)] in
theorem weightedCoefficient_nonneg {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A) (q N : ℕ) (ρ : ℝ)
        (hρ : 0 < ρ) :
    0 ≤ weightedCoefficient period K q N ρ :=
  Finset.sum_nonneg fun n _ => mul_nonneg (weight_pos hρ n).le (coefficientBlock_nonneg _)

/-- A genuine fixed-order block is independent of the chosen derivative-jet construction. -/
theorem blockNorm_unique {s t q n : ℕ} {f g : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period standardDirection s f)
    (K : EulerSpatialSobolevInverse.SpatialJet period standardDirection t g)
    (hfg : f = g) (hs : n + q ≤ s) (ht : n + q ≤ t) :
    blockNorm period J q n = blockNorm period K q n := by
  unfold blockNorm
  apply Finset.sum_congr rfl
  intro r hr
  rw [levelNorm_eq_words, levelNorm_eq_words]
  apply Finset.sum_congr rfl
  intro w _
  rw [EulerPressureJetIdentities.SpatialJet.word_unique J K hfg
    (by have := Finset.mem_range.mp hr; omega) (by have := Finset.mem_range.mp hr; omega) w]

/-- The actual complete Sobolev weighted norm satisfies the triangle inequality at every valid
cutoff. -/
theorem weightedNorm_add_le {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (u v : SobolevSpace period s) :
    weightedNorm period q N ρ (u+v) ≤ weightedNorm period q N ρ u + weightedNorm period q N ρ v :=
        by
  unfold weightedNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  rw [blockNorm_unique period (toJet period (u+v)) ((toJet period u).add (toJet period v)) rfl
    (by
        have := Finset.mem_range.mp hn; omega) (by
            have := Finset.mem_range.mp hn; omega), ← mul_add]
  exact mul_le_mul_of_nonneg_left (blockNorm_add_le _ _) (weight_pos hρ n).le

/-- The zero Sobolev field has zero weighted energy. -/
theorem weightedNorm_zero {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) :
    weightedNorm period q N ρ (0 : SobolevSpace period s) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hz : blockNorm period (toJet period (0 : SobolevSpace period s)) q n = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [levelNorm_eq_words]
    apply Finset.sum_eq_zero
    intro w _
    rw [toJet_word period (0 : SobolevSpace period s) (by
        have := Finset.mem_range.mp hn; have := Finset.mem_range.mp hr; omega)]
    change ‖(0 : LiftL2 period)‖ = 0
    exact norm_zero
  rw [hz, mul_zero]

/-- The actual finite weighted Sobolev norm is subadditive on finite sums. -/
theorem weightedNorm_sum_le {s : ℕ} {ι : Type*} (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (S : Finset ι) (u : ι → SobolevSpace period s) :
    weightedNorm period q N ρ (∑ i ∈ S, u i) ≤ ∑ i ∈ S, weightedNorm period q N ρ (u i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, weightedNorm_zero period q N hN ρ, le_refl]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (weightedNorm_add_le period q N hN ρ hρ (u i) (∑ j ∈ S, u j)).trans (add_le_add le_rfl ih)

/-- Actual coefficient multiplication has a cutoff-independent weighted Sobolev bound. -/
theorem weightedNorm_coefficient {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (u : SobolevSpace period s) :
    weightedNorm period q N ρ (coefficientSobolevOperator period K u) ≤
      weightedCoefficient period K q N ρ * weightedNorm period q N ρ u := by
  have heq : weightedNorm period q N ρ (coefficientSobolevOperator period K u) =
      ∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period
        (EulerSpatialSobolevInverse.SpatialJet.multiply K (toJet period u)) q n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [blockNorm_unique period (toJet period (coefficientSobolevOperator period K u))
      (EulerSpatialSobolevInverse.SpatialJet.multiply K (toJet period u))
      (coefficientSobolevOperator_value period K u)
      (by have := Finset.mem_range.mp hn; omega) (by have := Finset.mem_range.mp hn; omega)]
  rw [heq]
  exact multiply_block_weighted_bound period K (toJet period u) N hN ρ hρ

/-- The actual coercive pressure operator obeys the unshifted finite Gevrey estimate on complete
Sobolev inputs. -/
theorem weightedNorm_pressure {s q : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + q ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K q (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K q l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (u : SobolevSpace period s) :
    weightedNorm period q N ρ (pressureSobolevOperator period K κ m c hc hpos u) ≤
      2*M*weightedNorm period q N ρ u := by
  have heq : weightedNorm period q N ρ (pressureSobolevOperator period K κ m c hc hpos u) =
      ∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period
        ((toJet period u).solvePressure K κ m c hc hpos) q n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [blockNorm_unique period (toJet period (pressureSobolevOperator period K κ m c hc hpos u))
      ((toJet period u).solvePressure K κ m c hc hpos)
      (pressureSobolevOperator_value period K κ m c hc hpos u)
      (by have := Finset.mem_range.mp hn; omega) (by have := Finset.mem_range.mp hn; omega)]
  rw [heq]
  exact pressure_unshifted_Hq_bound period K (toJet period u) κ m c hc hpos N hN (by omega)
    ρ Rc M hρ hRc hM hbase hsmall hcoeff

/-- Actual scalar-component multiplication in finite Gevrey sums. -/
theorem weightedNorm_product {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (u v : SobolevSpace period s) :
    weightedNorm period 6 N ρ (productHq period hs L hL u v) ≤
      productConstant period 3 * weightedNorm period 6 N ρ u * weightedNorm period 6 N ρ v :=
  product_weighted_bound period hs N hN ρ hρ L hL u v

end EulerSobolevGevreyOperators
