/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.InvariantSet


/-!
# Poisson invariance of bounded Yosida exponentials

This file proves the uniformization argument: a normalized resolvent preserving
a closed convex set containing zero has Yosida exponentials preserving that set.
-/

@[expose] public section

noncomputable section PortComputability

open Filter Set Topology
open NormedSpace

section

namespace MarkovProcess.Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exponential of a scalar multiple of the identity is scalar
multiplication by the real exponential. -/
theorem exp_smul_id_apply (a : ℝ) (x : E) :
    exp (a • ContinuousLinearMap.id ℝ E) x = Real.exp a • x := by
  have hmap := NormedSpace.map_exp
    (algebraMap ℝ (E →L[ℝ] E))
    (continuous_algebraMap ℝ (E →L[ℝ] E)) a
  rw [← Real.exp_eq_exp_ℝ] at hmap
  have halg : algebraMap ℝ (E →L[ℝ] E) a =
      a • ContinuousLinearMap.id ℝ E := by
    ext y
    simp only [ContinuousLinearMap.algebraMap_apply,
      smul_apply, ContinuousLinearMap.id_apply]
  rw [halg] at hmap
  rw [← hmap]
  exact ContinuousLinearMap.algebraMap_apply _ _

/-- The operator exponential applied to a vector is its power-series sum. -/
theorem exp_apply_eq_tsum [CompleteSpace E] (A : E →L[ℝ] E) (x : E) :
    exp A x = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • (A ^ n) x := by
  have hop : Summable fun n : ℕ ↦ ((n.factorial : ℝ)⁻¹) • A ^ n := by
    simpa [NormedSpace.expSeries,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply] using
      (NormedSpace.expSeries_summable (𝕂 := ℝ) (𝔸 := E →L[ℝ] E) A)
  rw [NormedSpace.exp_eq_tsum ℝ]
  change (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • A ^ n) x = _
  exact (ContinuousLinearMap.apply ℝ E x).map_tsum hop

private theorem smul_pow_apply (c : ℝ) (Q : E →L[ℝ] E) (n : ℕ) (x : E) :
    ((c • Q) ^ n) x = c ^ n • (Q ^ n) x := by
  induction n generalizing x with
  | zero => simp only [pow_zero, one_apply_eq_self, one_smul]
  | succ n ih =>
      rw [pow_succ, pow_succ, mul_apply_eq_comp, ih,
        smul_apply, map_smul, smul_smul]
      rw [mul_comm (c ^ n) c]
      rw [pow_succ, mul_apply_eq_comp]

/-- Poisson-series representation of a bounded uniformization exponential. -/
theorem exp_smul_sub_id_apply_eq_tsum [CompleteSpace E]
    (Q : E →L[ℝ] E) (c : ℝ) (x : E) :
    exp (c • (Q - ContinuousLinearMap.id ℝ E)) x =
      ∑' n : ℕ, (Real.exp (-c) * (c ^ n / n.factorial)) • (Q ^ n) x := by
  have hcomm : Commute
      ((-c) • ContinuousLinearMap.id ℝ E) (c • Q) := by
    ext y
    simp only [mul_apply_eq_comp, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_smul]
    rw [mul_comm (-c) c]
  have hsplit : c • (Q - ContinuousLinearMap.id ℝ E) =
      (-c) • ContinuousLinearMap.id ℝ E + c • Q := by
    ext y
    simp only [smul_apply, add_apply,
      sub_eq_add_neg, smul_add, smul_neg, neg_smul]
    exact add_comm _ _
  rw [hsplit, NormedSpace.exp_add_of_commute hcomm,
    mul_apply_eq_comp, exp_smul_id_apply]
  rw [exp_apply_eq_tsum]
  have hsum : Summable fun n : ℕ ↦
      ((n.factorial : ℝ)⁻¹) • ((c • Q) ^ n) x := by
    have hop : Summable fun n : ℕ ↦
        ((n.factorial : ℝ)⁻¹) • (c • Q) ^ n :=
      by
        simpa [NormedSpace.expSeries,
          ContinuousMultilinearMap.mkPiAlgebraFin_apply] using
          (NormedSpace.expSeries_summable (𝕂 := ℝ)
            (𝔸 := E →L[ℝ] E) (c • Q))
    simpa only [Function.comp_apply, smul_apply] using!
      hop.map (ContinuousLinearMap.apply ℝ E x)
        (ContinuousLinearMap.continuous _)
  change ((Real.exp (-c)) • ContinuousLinearMap.id ℝ E)
      (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • ((c • Q) ^ n) x) = _
  rw [((Real.exp (-c)) • ContinuousLinearMap.id ℝ E).map_tsum hsum]
  · apply tsum_congr
    intro n
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    rw [smul_pow_apply]
    simp only [div_eq_mul_inv, smul_smul]
    congr 1
    ring

/-- The Poisson coefficients with parameter `c`. -/
def poissonWeight (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-c) * (c ^ n / n.factorial)

theorem poissonWeight_nonneg {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ poissonWeight c n := by
  exact mul_nonneg (Real.exp_pos _).le
    (div_nonneg (pow_nonneg hc n) (Nat.cast_nonneg n.factorial))

theorem summable_poissonWeight (c : ℝ) : Summable (poissonWeight c) := by
  unfold poissonWeight
  exact (Real.summable_pow_div_factorial c).mul_left (Real.exp (-c))

theorem tsum_poissonWeight (c : ℝ) : ∑' n, poissonWeight c n = 1 := by
  have hseries : ∑' n : ℕ, c ^ n / n.factorial = Real.exp c := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    apply tsum_congr
    intro n
    simp only [div_eq_mul_inv, smul_eq_mul]
    ring
  unfold poissonWeight
  rw [tsum_mul_left, hseries, ← Real.exp_add]
  simp only [neg_add_cancel, Real.exp_zero]

theorem summable_poissonWeight_smul_pow_apply
    [CompleteSpace E] (Q : E →L[ℝ] E) (c : ℝ) (x : E) :
    Summable fun n : ℕ ↦ poissonWeight c n • (Q ^ n) x := by
  have hop : Summable fun n : ℕ ↦
      ((n.factorial : ℝ)⁻¹) • (c • Q) ^ n := by
    simpa [NormedSpace.expSeries,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply] using
      (NormedSpace.expSeries_summable (𝕂 := ℝ)
        (𝔸 := E →L[ℝ] E) (c • Q))
  have happ : Summable fun n : ℕ ↦
      ((n.factorial : ℝ)⁻¹) • ((c • Q) ^ n) x := by
    simpa only [Function.comp_apply, smul_apply] using!
      hop.map (ContinuousLinearMap.apply ℝ E x)
        (ContinuousLinearMap.continuous _)
  have hscaled := happ.map
    ((Real.exp (-c)) • ContinuousLinearMap.id ℝ E)
    (ContinuousLinearMap.continuous _)
  apply hscaled.congr
  intro n
  simp only [Function.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_smul, poissonWeight, div_eq_mul_inv,
    smul_pow_apply]
  congr 1
  ring

namespace ContractiveResolvent

variable [CompleteSpace E]

/-- A normalized-resolvent invariant closed convex set containing zero is
invariant under every bounded Yosida exponential. -/
theorem preservesSet_yosidaOperator_of_scaledOperator
    (R : ContractiveResolvent E) (C : Set E) (hclosed : IsClosed C)
    (hconvex : Convex ℝ C) (hzero : 0 ∈ C) (α : PositiveShift)
    (hQ : PreservesSet (R.scaledOperator α) C C) (t : NNReal) :
    PreservesSet (R.yosidaOperator α t) C C := by
  intro x hx
  let c : ℝ := (t : ℝ) * (α : ℝ)
  have hc : 0 ≤ c := mul_nonneg t.property α.property.le
  have hpowers : ∀ n, ((R.scaledOperator α) ^ n) x ∈ C :=
    fun n ↦ R.preservesSet_scaledOperator_pow C α hQ n hx
  have hmem := Convex.tsum_mem_of_tsum_le_one
    hclosed hconvex hzero (poissonWeight c)
    (fun n ↦ ((R.scaledOperator α) ^ n) x)
    (poissonWeight_nonneg hc) (summable_poissonWeight c)
    (by rw [tsum_poissonWeight]) hpowers
    (summable_poissonWeight_smul_pow_apply (R.scaledOperator α) c x)
  rw [yosidaOperator, yosidaGenerator, smul_smul]
  change exp (c • (R.scaledOperator α - ContinuousLinearMap.id ℝ E)) x ∈ C
  rw [exp_smul_sub_id_apply_eq_tsum]
  exact hmem

/-- Direct invariant-set transfer from all normalized resolvents to the
canonically generated contraction semigroup. -/
theorem preservesSet_generatedSemigroup_of_scaledOperator
    (R : ContractiveResolvent E) (C : Set E) (hclosed : IsClosed C)
    (hconvex : Convex ℝ C) (hzero : 0 ∈ C)
    (hQ : ∀ α, PreservesSet (R.scaledOperator α) C C) (t : NNReal) :
    PreservesSet (R.generatedSemigroup t) C C := by
  exact R.preservesSet_generatedSemigroup C hclosed
    (fun α s ↦ R.preservesSet_yosidaOperator_of_scaledOperator
      C hclosed hconvex hzero α (hQ α) s) t

end ContractiveResolvent

end MarkovProcess.Semigroup

end

end PortComputability
