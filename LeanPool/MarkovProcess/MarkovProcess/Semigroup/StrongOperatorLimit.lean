/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.Normed.Operator.Completeness

/-!
# Strong operator limits of contractions

This module constructs the pointwise limit of a sequence of continuous linear
contractions on a complete real normed space and records the small convergence
API needed to pass algebraic identities to the limit.
-/

open Filter Topology

namespace MarkovProcess.Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Completeness

variable [CompleteSpace E]

/-- The continuous linear map obtained as the pointwise limit of a pointwise
Cauchy sequence of contractions. -/
noncomputable def strongOperatorLimit (T : ℕ → E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hcauchy : ∀ x, CauchySeq (fun n ↦ T n x)) :
    E →L[ℝ] E :=
  ContinuousLinearMap.ofTendstoOfBoundedRange
    (fun x ↦ limUnder atTop (fun n ↦ T n x)) T
    (tendsto_pi_nhds.2 fun x ↦ (hcauchy x).tendsto_limUnder)
    (isBounded_iff_forall_norm_le.2
      ⟨1, Set.forall_mem_range.2 fun n ↦ hT n⟩)

/-- The defining pointwise convergence of `strongOperatorLimit`. -/
theorem tendsto_strongOperatorLimit_apply (T : ℕ → E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hcauchy : ∀ x, CauchySeq (fun n ↦ T n x)) (x : E) :
    Tendsto (fun n ↦ T n x) atTop (nhds (strongOperatorLimit T hT hcauchy x)) := by
  change Tendsto (fun n ↦ T n x) atTop
    (nhds (limUnder atTop (fun n ↦ T n x)))
  exact (hcauchy x).tendsto_limUnder

/-- The strong operator limit of contractions is again a contraction pointwise. -/
theorem norm_strongOperatorLimit_apply_le (T : ℕ → E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hcauchy : ∀ x, CauchySeq (fun n ↦ T n x)) (x : E) :
    ‖strongOperatorLimit T hT hcauchy x‖ ≤ ‖x‖ := by
  refine le_of_tendsto (tendsto_strongOperatorLimit_apply T hT hcauchy x).norm ?_
  exact Eventually.of_forall fun n ↦
    calc
      ‖T n x‖ ≤ ‖T n‖ * ‖x‖ := (T n).le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (hT n) (norm_nonneg x)
      _ = ‖x‖ := one_mul _

/-- The strong operator limit of contractions has operator norm at most one. -/
theorem norm_strongOperatorLimit_le_one (T : ℕ → E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hcauchy : ∀ x, CauchySeq (fun n ↦ T n x)) :
    ‖strongOperatorLimit T hT hcauchy‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun x ↦ by
      simpa only [one_mul] using norm_strongOperatorLimit_apply_le T hT hcauchy x)

end Completeness

/-- A pointwise operator limit may be evaluated along a convergent family of vectors, provided
the approximating operators are contractions.  Only the convergence of the operators at the
limiting vector is needed. -/
theorem tendsto_apply_of_opNorm_le_one {ι : Type*} {l : Filter ι}
    (T : ι → E →L[ℝ] E) (Tlim : E →L[ℝ] E) (v : ι → E) (w : E)
    (hT : ∀ i, ‖T i‖ ≤ 1)
    (hTlim : Tendsto (fun i ↦ T i w) l (nhds (Tlim w)))
    (hv : Tendsto v l (nhds w)) :
    Tendsto (fun i ↦ T i (v i)) l (nhds (Tlim w)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [Metric.tendsto_nhds.mp hv (ε / 2) hε2,
    Metric.tendsto_nhds.mp hTlim (ε / 2) hε2] with i hvi hTi
  have hcontract : dist (T i (v i)) (T i w) ≤ dist (v i) w := by
    calc
      dist (T i (v i)) (T i w) ≤ ‖T i‖ * dist (v i) w := (T i).dist_le_opNorm _ _
      _ ≤ 1 * dist (v i) w := mul_le_mul_of_nonneg_right (hT i) dist_nonneg
      _ = dist (v i) w := one_mul _
  calc
    dist (T i (v i)) (Tlim w) ≤ dist (T i (v i)) (T i w) + dist (T i w) (Tlim w) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hcontract.trans_lt hvi) hTi
    _ = ε := add_halves ε

/-- Two pointwise operator limits may be composed when the outer approximating
operators are contractions. -/
theorem tendsto_apply_comp_of_opNorm_le_one
    (T U : ℕ → E →L[ℝ] E) (Tlim Ulim : E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1)
    (hTlim : ∀ x, Tendsto (fun n ↦ T n x) atTop (nhds (Tlim x)))
    (hUlim : ∀ x, Tendsto (fun n ↦ U n x) atTop (nhds (Ulim x))) (x : E) :
    Tendsto (fun n ↦ T n (U n x)) atTop (nhds (Tlim (Ulim x))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hU_eventually : ∀ᶠ n in atTop, dist (U n x) (Ulim x) < ε / 2 :=
    Metric.tendsto_nhds.mp (hUlim x) (ε / 2) hε2
  have hT_eventually : ∀ᶠ n in atTop, dist (T n (Ulim x)) (Tlim (Ulim x)) < ε / 2 :=
    Metric.tendsto_nhds.mp (hTlim (Ulim x)) (ε / 2) hε2
  filter_upwards [hU_eventually, hT_eventually] with n hUn hTn
  have hcontract : dist (T n (U n x)) (T n (Ulim x)) ≤ dist (U n x) (Ulim x) := by
    calc
      dist (T n (U n x)) (T n (Ulim x)) ≤ ‖T n‖ * dist (U n x) (Ulim x) :=
        (T n).dist_le_opNorm (U n x) (Ulim x)
      _ ≤ 1 * dist (U n x) (Ulim x) :=
        mul_le_mul_of_nonneg_right (hT n) dist_nonneg
      _ = dist (U n x) (Ulim x) := one_mul _
  calc
    dist (T n (U n x)) (Tlim (Ulim x)) ≤
        dist (T n (U n x)) (T n (Ulim x)) +
          dist (T n (Ulim x)) (Tlim (Ulim x)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
      lt_of_le_of_lt (add_le_add hcontract le_rfl) (add_lt_add hUn hTn)
    _ = ε := add_halves ε

end MarkovProcess.Semigroup
