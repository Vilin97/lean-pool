/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WeightedCylinderEnergy
public import LeanPool.NavierStokesAndEuler.Euler.GevreyPressureEnergy

/-! Related estimates used together by the same construction modules. -/

section

/-! Exact triangle inequalities for the actual finite Hilbert forcing families. -/

@[expose] public section

noncomputable section

namespace EulerWeightedForcingAlgebra

open EulerFiniteMetricEnergy EulerWeightedCylinderEnergy EulerPacketWeights

variable {α β H : Type*} [Fintype α] [Fintype β]
  [NormedAddCommGroup H]

/-- Triangle inequality for the root-of-sum-of-squares norm of actual finite Hilbert families. -/
theorem familyNorm_add_le (v w : β → H) : familyNorm (v+w) ≤ familyNorm v + familyNorm w := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (familyNorm_nonneg v) (familyNorm_nonneg w), ?_⟩
  have hsq : familySquaredNorm (v+w) ≤ ∑ i : β, (‖v i‖+‖w i‖)^2 := by
    apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (v i) (w i)) 2
  have heq : (∑ i : β, (‖v i‖+‖w i‖)^2) =
      familySquaredNorm v + 2*(∑ i : β, ‖v i‖*‖w i‖) + familySquaredNorm w := by
    simp only [familySquaredNorm, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [heq] at hsq
  have hcs := family_cauchy_schwarz v w
  have hv := familyNorm_sq v
  have hw := familyNorm_sq w
  nlinarith

/-- Signs do not change the genuine Hilbert family norm. -/
theorem familyNorm_neg (v : β → H) : familyNorm (-v) = familyNorm v := by
  simp only [familyNorm, familySquaredNorm, Pi.neg_apply, norm_neg]

/-- Weighted forcing is subadditive without any cardinality factor. -/
theorem weightedForcingSum_add_le (ρ : ℝ) (hρ : 0 < ρ) (order : α → ℕ) (f g : α → β → H) :
    weightedForcingSum ρ order (f+g) ≤ weightedForcingSum ρ order f + weightedForcingSum ρ order g
        := by
  unfold weightedForcingSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_left (familyNorm_add_le (f i) (g i)) (weight_pos hρ (order
      i)).le).trans_eq (mul_add ..)

/-- Weighted forcing is invariant under the overall sign. -/
theorem weightedForcingSum_neg (ρ : ℝ) (order : α → ℕ) (f : α → β → H) :
    weightedForcingSum ρ order (-f) = weightedForcingSum ρ order f := by
  simp only [weightedForcingSum, Pi.neg_apply, familyNorm_neg]

/-- The forcing norm of a sum is controlled by the sum of the norms of its actual terms. -/
theorem weightedForcingSum_sum_le {ι : Type*} (ρ : ℝ) (hρ : 0 < ρ) (order : α → ℕ)
    (S : Finset ι) (f : ι → α → β → H) :
    weightedForcingSum ρ order (∑ i ∈ S, f i) ≤ ∑ i ∈ S, weightedForcingSum ρ order (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [weightedForcingSum, familyNorm, familySquaredNorm]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (weightedForcingSum_add_le ρ hρ order (f i) (∑ j ∈ S, f j)).trans (add_le_add le_rfl ih)

end EulerWeightedForcingAlgebra

end
end

end

section

/-! Complete finite-cutoff pressure commutator bounds for both actual source components. -/

@[expose] public section

noncomputable section

namespace EulerGevreyPressureEnergy

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerJetProductBounds EulerPacketWeights
  EulerSobolevGevreyOperators EulerBasePressureCommutator EulerGevreyPressureTransport
      EulerH6Nonlinear
  EulerSobolevTransportCommutator EulerSobolevCoefficientPressure

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
/-- Monotonicity of the actual coefficient derivative blocks in their fixed Sobolev index. -/
theorem coefficientBlock_mono {s p q : ℕ} (hpq : p ≤ q) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A) (n : ℕ) :
    coefficientBlock period K p n ≤ coefficientBlock period K q n := by
  apply mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hpq)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : p+1 ≤ q+1))
      (fun r _ _ => (boundLevel_nonneg K : 0 ≤ boundLevel period K (n+r))))
    (Finset.sum_nonneg (fun r _ => (boundLevel_nonneg K : 0 ≤ boundLevel period K (n+r))))
    (pow_nonneg (by norm_num) q)

/-- The actual nonlinear external pressure commutator bound includes the zero-cutoff case. -/
theorem nonlinear_externalPressure_bound_all {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) :
    externalPressureNorm period K N ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (32*Rc*M*productConstant period 3)*weightedNorm period 6 N ρ u*weightedLoss period 6 N ρ v :=
          by
  cases N with
  | zero => simp [externalPressureNorm, weightedLoss, commutatorBlock_zero]
  | succ N =>
      exact nonlinear_externalPressure_bound period hs K κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase
          hsmall hcoeff L hL u v

/-- Actual base transport-pressure commutators are bounded by the product of the two velocity
energies at the same cutoff. -/
theorem nonlinear_basePressure_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 5 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) :
    basePressureNorm period K0 N hN ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (448*baseCoefficientSum period K0)*(8*M*(5460*lowerProductConstant period 3)) *
        weightedNorm period 6 N ρ u*weightedNorm period 6 N ρ v := by
  have hc5 : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 5 l ≤ Rc^l*(l.factorial : ℝ)^2 :=
    fun l hl hn => (coefficientBlock_mono period (by norm_num : 5 ≤ 6) K l).trans (hcoeff l hl hn)
  have hp := transportPressure_lower period hs K κ m c hc hpos N (by
      omega) ρ Rc M hρ hRc hM hbase hsmall hc5 L hL u v
  exact (basePressureNorm_lower period K0 N hN ρ hρ _).trans
    ((mul_le_mul_of_nonneg_left hp (mul_nonneg (by
        norm_num) (baseCoefficientSum_nonneg period K0))).trans_eq (by ring))

/-- Both actual commutators of the order-zero pressure are controlled by the unshifted source norm.
-/
theorem source_pressure_commutators {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (f : SobolevSpace period s) :
    externalPressureNorm period K N ρ (pressureSobolevOperator period K κ m c hc hpos f) +
      basePressureNorm period K0 N hN ρ (pressureSobolevOperator period K κ m c hc hpos f) ≤
      (2*M*(weightedCoefficient period K 6 N ρ + 448*baseCoefficientSum period K0))*weightedNorm
          period 6 N ρ f := by
  have he := externalPressureNorm_unshifted period K N hN ρ hρ (pressureSobolevOperator period K κ
      m c hc hpos f)
  have hb := basePressureNorm_unshifted period K0 N hN ρ hρ (pressureSobolevOperator period K κ m c
      hc hpos f)
  have hp := weightedNorm_pressure period K κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase hsmall hcoeff
      f
  have hsum := add_le_add he hb
  rw [← add_mul] at hsum
  exact hsum.trans ((mul_le_mul_of_nonneg_left hp (add_nonneg
    (weightedCoefficient_nonneg period K 6 N ρ hρ)
    (mul_nonneg (by norm_num) (baseCoefficientSum_nonneg period K0)))).trans_eq (by ring))

end EulerGevreyPressureEnergy

end
end

end
