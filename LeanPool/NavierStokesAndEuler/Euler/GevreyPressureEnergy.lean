/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyPressureShifted
public import LeanPool.NavierStokesAndEuler.Euler.GevreyLowNorms
public import LeanPool.NavierStokesAndEuler.Euler.BasePressureCommutator
public import LeanPool.NavierStokesAndEuler.Euler.PressureCommutatorWeights

@[expose] public section

/-! The actual pressure commutators occurring in the Gevrey energy estimate. -/

noncomputable section

namespace EulerGevreyPressureEnergy

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerJetProductBounds EulerPacketWeights
  EulerSobolevGevreyOperators EulerBasePressureCommutator EulerGevreyPressureTransport
    EulerH6Nonlinear
  EulerSobolevTransportCommutator EulerSobolevCoefficientPressure EulerGevreyLowNorms

variable (period : ℝ) [Fact (0 < period)]

/-- The actual weighted H⁶ external pressure commutator norm. -/
def externalPressureNorm {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (N : ℕ) (ρ : ℝ) (p : SobolevSpace period s) : ℝ :=
  ∑ n ∈ Finset.range (N+1), weight ρ n * commutatorBlock K (toJet period p) 6 n

/-- The actual weighted L² base pressure commutator norm. -/
def basePressureNorm {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ) (p : SobolevSpace period s) : ℝ :=
  ∑ n : Fin (N+1), weight ρ n.val * basePressureBlock period K (toJet period p) n.val (by have :=
    n.isLt; omega)

/-- Ordinary coefficient-product control for the actual external pressure commutator. -/
theorem externalPressureNorm_unshifted {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (p : SobolevSpace period s) :
    externalPressureNorm period K N ρ p ≤ weightedCoefficient period K 6 N ρ * weightedNorm period
      6 N ρ p := by
  have hpoint (n : ℕ) (hn : n ≤ N) : commutatorBlock K (toJet period p) 6 n ≤
      leibnizConvolution (coefficientBlock period K 6) (blockNorm period (toJet period p) 6) n := by
    apply (commutatorBlock_bound K (toJet period p) (by omega : n+6 ≤ s)).trans
    exact sub_le_self _ (mul_nonneg (coefficientBlock_nonneg K) (blockNorm_nonneg _))
  have h := Finset.sum_le_sum (s := Finset.range (N+1)) (fun n hn =>
    mul_le_mul_of_nonneg_left (hpoint n (by have := Finset.mem_range.mp hn; omega)) (weight_pos hρ
      n).le)
  exact h.trans (EulerWeightedConvolution.unshifted_product_sum ρ hρ N _ _
    (fun _ => coefficientBlock_nonneg K) (fun _ => blockNorm_nonneg _))

/-- External pressure commutators use only shifted pressure orders strictly below the chosen cutoff. -/
theorem externalPressureNorm_shifted {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (N : ℕ) (hN : (N+1)+6 ≤ s) (ρ Rc : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc)
    (hsmall : ρ*Rc ≤ 1/2)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N+1 → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2)
    (p : SobolevSpace period s) :
    externalPressureNorm period K (N+1) ρ p ≤ 2*Rc*shiftedPressureNorm period N ρ p :=
  commutatorBlock_weighted_shifted period K (toJet period p) (N+1) hN ρ Rc hρ hRc hsmall hcoeff

/-- Actual base pressure commutators are controlled by the unshifted one-order-lower pressure norm. -/
theorem basePressureNorm_lower {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (p : SobolevSpace period s) :
    basePressureNorm period K N hN ρ p ≤ 448*baseCoefficientSum period K*weightedNorm period 5 N ρ
      p :=
  basePressure_weighted_bound period K (toJet period p) N hN ρ hρ

/-- The same actual base commutators can be controlled by an available H⁶ pressure bound. -/
theorem basePressureNorm_unshifted {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (p : SobolevSpace period s) :
    basePressureNorm period K N hN ρ p ≤ 448*baseCoefficientSum period K*weightedNorm period 6 N ρ
      p :=
  (basePressureNorm_lower period K N hN ρ hρ p).trans (mul_le_mul_of_nonneg_left
    (weightedNorm_mono period (by norm_num : 5 ≤ 6) N ρ hρ p)
    (mul_nonneg (by norm_num) (baseCoefficientSum_nonneg period K)))

/-- The actual nonlinear transport pressure has the required external commutator bound with no extra velocity order. -/
theorem nonlinear_externalPressure_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ)
    (N : ℕ) (hN : (N+1)+6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4*M*(ρ*Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N+1 → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) :
    externalPressureNorm period K (N+1) ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (32*Rc*M*productConstant period 3)*weightedNorm period 6 (N+1) ρ u*weightedLoss period 6
        (N+1) ρ v := by
  have hhalf : ρ*Rc ≤ 1/2 := by nlinarith [mul_nonneg hρ.le hRc]
  have hcN : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2 :=
    fun l hl hn => hcoeff l hl (by omega)
  have hp := transportPressure_shifted period hs K κ m c hc hpos N (by omega) ρ Rc M hρ hRc hM
    hbase hsmall hcN L hL u v
  exact (externalPressureNorm_shifted period K N hN ρ Rc hρ hRc hhalf hcoeff _).trans
    ((mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hRc)).trans_eq (by ring))

end EulerGevreyPressureEnergy
