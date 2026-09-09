/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WeightedCylinderEnergy

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
