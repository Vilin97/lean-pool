/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyPressureEnergy
public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricComparison
import LeanPool.NavierStokesAndEuler.Euler.GevreyBaseTransport

/-! Literal differentiated forcing arrays and their actual finite Gevrey norms. -/

@[expose] public section


noncomputable section

namespace EulerGevreyForcingComponents

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerPacketWeights EulerSobolevGevreyOperators
  EulerBaseWordMetric EulerFiniteMetricEnergy EulerWeightedCylinderEnergy
      EulerGevreyMetricComparison
  EulerSobolevWordLevel EulerSobolevTransportCommutator EulerGevreyPressureEnergy
      EulerBasePressureCommutator
  EulerGevreyBaseTransport

variable (period : ℝ) [Fact (0 < period)]

/-- A finite family of actual base-word derivatives is controlled by its genuine derivative-sum
norm. -/
theorem forcing_le_jetSum {ι : Type*} [Fintype ι] (order : ι → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (f : ι → LiftL2 period) (J : ∀ i, EulerSpatialSobolevInverse.SpatialJet period
        standardDirection 6 (f i)) :
    weightedForcingSum ρ order (fun i => baseWordValues period (J i)) ≤
      ∑ i, weight ρ (order i)*(J i).sobolevNorm := by
  apply Finset.sum_le_sum
  intro i _
  have h := familyNorm_le_sum_norm (baseWordValues period (J i))
  rw [sum_baseWordValues_norm] at h
  exact mul_le_mul_of_nonneg_left h (weight_pos hρ (order i)).le

/-- The actual differentiated order-zero source is controlled by its finite weighted Sobolev norm.
-/
theorem sourceForcing_weighted_bound {s : ℕ} (N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (f : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (energyValues period 6 N hN f) ≤
        weightedNorm period 6 N ρ f := by
  have h := forcing_le_jetSum period (fun I : ExternalWord N => I.1.val) ρ hρ
    (fun I => (toJet period f).word I.2)
    (fun I => EulerH6Pressure.SpatialJet.derivativeJet (q := 6) (toJet period f) I.2 (by
        have := I.1.isLt; omega))
  have he : (∑ I : ExternalWord N, weight ρ I.1.val *
      (EulerH6Pressure.SpatialJet.derivativeJet (q := 6) (toJet period f) I.2 (by
          have := I.1.isLt; omega)).sobolevNorm) =
      ∑ I : ExternalWord N, weight ρ I.1.val * sumNorm period
        (wordAtLevel period 6 I.1.val I.2 (by have := I.1.isLt; omega) f) := by
    apply Finset.sum_congr rfl
    intro I _
    rw [sumNorm_wordAtLevel]
  exact h.trans_eq (he.trans (weighted_word_sums period 6 N hN ρ f))

/-- The literal base derivatives of the external transport commutator. -/
def externalTransportForcing {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) : ExternalWord N → BaseWord 6 → LiftL2 period := fun I =>
  baseWordValues period (toJet period (externalCommutator period hs I.1.val I.2 (by
      have := I.1.isLt; omega) L hL u v))

/-- The actual external transport forcing is bounded by the already proved commutator norm. -/
theorem externalTransportForcing_bound {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (externalTransportForcing period hs N
        hN L hL u v) ≤
      weightedCommutatorNorm period hs N hN ρ L hL u v := by
  have h := forcing_le_jetSum period (fun I : ExternalWord N => I.1.val) ρ hρ _
    (fun I => toJet period (externalCommutator period hs I.1.val I.2 (by
        have := I.1.isLt; omega) L hL u v))
  simp only [← sumNorm_eq_jet] at h
  exact h.trans_eq (by simp only [Fintype.sum_sigma, weightedCommutatorNorm, Finset.mul_sum])

/-- The literal base derivatives of the actual external coefficient-pressure commutator. -/
def externalPressureForcing {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (N : ℕ) (hN : N + 6 ≤ s) (p : SobolevSpace period s) : ExternalWord N → BaseWord 6 → LiftL2
        period := fun I =>
  baseWordValues period (commutatorJet K (toJet period p) I.2 (by
      have := I.1.isLt; omega : I.1.val+6 ≤ s))

/-- The actual differentiated external pressure forcing is controlled by its proved H⁶ commutator
sum. -/
theorem externalPressureForcing_bound {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (p : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (externalPressureForcing period K N hN
        p) ≤
      externalPressureNorm period K N ρ p := by
  have h := forcing_le_jetSum period (fun I : ExternalWord N => I.1.val) ρ hρ _
    (fun I => commutatorJet K (toJet period p) I.2 (by have := I.1.isLt; omega : I.1.val+6 ≤ s))
  apply h.trans_eq
  rw [Fintype.sum_sigma, externalPressureNorm, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  rw [commutatorBlock, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [sobolevSize_eq period (commutatorJet K (toJet period p) w (by
      have := n.isLt; omega : n.val+6 ≤ s))]

/-- At order zero the genuine Sobolev size is exactly the L² norm. -/
theorem sobolevSize_order_zero (f : LiftL2 period) :
    sobolevSize period (directions := standardDirection) 0 f = ‖f‖ := by
  exact sobolevSize_eq period (EulerSpatialSobolevInverse.SpatialJet.zero f)

/-- The literal base derivative commutator of G with each external pressure derivative. -/
def basePressureForcing {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (p : SobolevSpace period s) : ExternalWord N → BaseWord 6 → LiftL2
        period := fun I a =>
  (EulerSpatialSobolevInverse.SpatialJet.multiply K
    (EulerH6Pressure.SpatialJet.derivativeJet (q := 6) (toJet period p) I.2 (by
        have := I.1.isLt; omega))).word a.2 -
    A.operator ((EulerH6Pressure.SpatialJet.derivativeJet (q := 6) (toJet period p) I.2 (by
        have := I.1.isLt; omega)).word a.2)

/-- At each external word, summing the actual base commutator norms gives the base-pressure block
expression. -/
theorem basePressureForcing_family_bound {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (p : SobolevSpace period s) (I : ExternalWord N) :
    familyNorm (basePressureForcing period K N hN p I) ≤
      ∑ r ∈ Finset.range 7, commutatorBlock K
        (EulerH6Pressure.SpatialJet.derivativeJet (q := 6) (toJet period p) I.2 (by
            have := I.1.isLt; omega)) 0 r := by
  apply (familyNorm_le_sum_norm _).trans_eq
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  simp only [commutatorBlock, sobolevSize_order_zero, basePressureForcing]

/-- The actual base pressure forcing is controlled by the previously proved lower-order pressure
commutator norm. -/
theorem basePressureForcing_bound {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (p : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (basePressureForcing period K N hN p) ≤
      basePressureNorm period K N hN ρ p := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (ExternalWord N))) (fun I _ =>
    mul_le_mul_of_nonneg_left (basePressureForcing_family_bound period K N hN p I) (weight_pos hρ
        I.1.val).le)
  exact h.trans_eq (by
      simp only [Fintype.sum_sigma, basePressureNorm, basePressureBlock, Finset.mul_sum])

end EulerGevreyForcingComponents
