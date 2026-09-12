/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.H6PressureCommutator
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketWeights
import LeanPool.NavierStokesAndEuler.Euler.Foundations.WeightedPressure

/-! The actual coercive pressure inverse in fixed Sobolev blocks, followed by external Gevrey
weighting. -/

@[expose] public section


noncomputable section

namespace EulerH6Pressure

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerJetProductBounds EulerPressureJetIdentities EulerPressureSpatialRegularity
open scoped Topology

variable (period : ℝ) [Fact (0 < period)] {directions : Fin 4 → LiftTangent}

/-- The already-constructed coercive inverse is bounded in the genuine fixed-order Sobolev norm. -/
theorem pressure_sobolevSize_bound {q : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions q A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions q f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) :
    sobolevSize period (directions := directions) q (A.pressure κ m c hc hpos f) ≤
      K.pressureConstant c * sobolevSize period (directions := directions) q f := by
  rw [sobolevSize_eq period (J.solvePressure K κ m c hc hpos), sobolevSize_eq period J]
  exact J.solvePressure_norm_le K κ m c hc hpos

variable {period}

/-- Apply the fixed-order Sobolev inverse separately to every actual external derivative word. -/
theorem pressure_block_inverse {s q n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hq : q ≤ s) (h : n + q ≤ s) :
    blockNorm period (J.solvePressure K κ m c hc hpos) q n ≤
      (CoefficientJet.restrict K q hq).pressureConstant c *
        (blockNorm period J q n + commutatorBlock K (J.solvePressure K κ m c hc hpos) q n) := by
  let P := J.solvePressure K κ m c hc hpos
  let K₀ := CoefficientJet.restrict K q hq
  have hw : ∀ w : Fin n → Fin 4,
      sobolevSize period (directions := directions) q (P.word w) ≤
        K₀.pressureConstant c * (sobolevSize period (directions := directions) q (J.word w) +
          sobolevSize period (directions := directions) q
            ((EulerSpatialSobolevInverse.SpatialJet.multiply K P).word w - A.operator (P.word w)))
                := by
    intro w
    let R := J.word w -
      ((EulerSpatialSobolevInverse.SpatialJet.multiply K P).word w - A.operator (P.word w))
    let RJ := (SpatialJet.derivativeJet J w h).sub (commutatorJet K P w h)
    have hi : P.word w = A.pressure κ m c hc hpos R :=
      EulerPressureJetIdentities.SpatialJet.pressure_word_inverse K J κ m c hc hpos (by omega) w
    calc
      _ = sobolevSize period (directions := directions) q (A.pressure κ m c hc hpos R) :=
        congrArg (sobolevSize period (directions := directions) q) hi
      _ ≤ K₀.pressureConstant c * sobolevSize period (directions := directions) q R :=
        pressure_sobolevSize_bound period K₀ RJ κ m c hc hpos
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sobolevSize_sub_le (SpatialJet.derivativeJet J w h) (commutatorJet K P w h))
        (K₀.pressureConstant_nonneg c hc)
  calc
    _ = ∑ w : Fin n → Fin 4, sobolevSize period (directions := directions) q (P.word w) :=
      blockNorm_eq_word_sizes P h
    _ ≤ ∑ w : Fin n → Fin 4, K₀.pressureConstant c *
        (sobolevSize period (directions := directions) q (J.word w) +
          sobolevSize period (directions := directions) q
            ((EulerSpatialSobolevInverse.SpatialJet.multiply K P).word w - A.operator (P.word w)))
                :=
      Finset.sum_le_sum (fun w _ => hw w)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← blockNorm_eq_word_sizes J h]
      rfl

/-- The pressure recurrence has the required external-order binomial coefficients and Hq blocks. -/
theorem pressure_block_recurrence {s q n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hq : q ≤ s) (h : n + q ≤ s) (M : ℝ)
    (hM : (CoefficientJet.restrict K q hq).pressureConstant c ≤ M) :
    blockNorm period (J.solvePressure K κ m c hc hpos) q n ≤
      M * (blockNorm period J q n + ∑ l ∈ Finset.range n,
        (n.choose (l + 1) : ℝ) * coefficientBlock period K q (l + 1) *
          blockNorm period (J.solvePressure K κ m c hc hpos) q (n - (l + 1))) := by
  let P := J.solvePressure K κ m c hc hpos
  let K₀ := CoefficientJet.restrict K q hq
  have hsum : 0 ≤ ∑ l ∈ Finset.range n,
      (n.choose (l + 1) : ℝ) * coefficientBlock period K q (l + 1) *
        blockNorm period P q (n - (l + 1)) := by
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (coefficientBlock_nonneg K)) (blockNorm_nonneg
        P)
  calc
    _ ≤ K₀.pressureConstant c * (blockNorm period J q n + commutatorBlock K P q n) :=
      pressure_block_inverse K J κ m c hc hpos hq h
    _ ≤ K₀.pressureConstant c * (blockNorm period J q n +
        commutatorConvolution (coefficientBlock period K q) (blockNorm period P q) n) :=
      mul_le_mul_of_nonneg_left (add_le_add_right (commutatorBlock_bound K P h) _)
        (K₀.pressureConstant_nonneg c hc)
    _ = K₀.pressureConstant c * (blockNorm period J q n + ∑ l ∈ Finset.range n,
        (n.choose (l + 1) : ℝ) * coefficientBlock period K q (l + 1) *
          blockNorm period P q (n - (l + 1))) := by rw [commutatorConvolution_eq_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right hM (add_nonneg (blockNorm_nonneg J) hsum)

/-- Source equation18's shifted inverse estimate in genuine fixed Hq blocks.
The constant depends on q and base coefficient bounds, and is independent of the external cutoff N.
-/
theorem pressure_shifted_Hq_bound {s q : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + q ≤ s) (hq : q ≤ s)
    (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (CoefficientJet.restrict K q hq).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N →
      coefficientBlock period K q l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2) :
    (∑ n ∈ Finset.range (N + 1), ((n + 1 : ℕ) : ℝ) * EulerPacketWeights.weight ρ (n + 1) *
      blockNorm period (J.solvePressure K κ m c hc hpos) q n) ≤
      2 * M * ∑ n ∈ Finset.range (N + 1), ((n + 1 : ℕ) : ℝ) * EulerPacketWeights.weight ρ (n + 1) *
        blockNorm period J q n := by
  apply EulerWeightedPressure.shifted_weighted_inverse ρ Rc M hρ hRc hM hsmall N
    (coefficientBlock period K q) (blockNorm period J q)
    (blockNorm period (J.solvePressure K κ m c hc hpos) q)
    (fun _ => blockNorm_nonneg J) (fun _ => blockNorm_nonneg _) hcoeff
  intro n hn
  exact pressure_block_recurrence K J κ m c hc hpos hq (by omega) M hbase

end EulerH6Pressure
