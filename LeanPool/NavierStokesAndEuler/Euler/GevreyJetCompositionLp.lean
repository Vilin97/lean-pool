/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyCompositionLp
import LeanPool.NavierStokesAndEuler.Euler.GevreyComposition
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! The L² composition estimate over an arbitrary measure space.  This
version allows the base to be a periodic cylinder while the derivatives
are tensors on its Euclidean cover.  The output is the literal finite
Taylor composition of the given jets. -/

@[expose] public section


noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace EulerGevreyJetCompositionLp

open EulerGevreyComposition EulerGevreyCompositionLp

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem taylorComp_partition_bound
    (P : FormalMultilinearSeries ℝ E E) (Q : FormalMultilinearSeries ℝ E F)
    (n : ℕ) (B R : ℝ)
    (hP : ∀ j, 0 < j → j ≤ n → ‖P j‖ ≤ B * R ^ j * (j.factorial : ℝ) ^ 2) :
    ‖Q.taylorComp P n‖ ≤ ∑ c : OrderedFinpartition n, innerPartitionBound B R c*‖Q c.length‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  calc
    _ ≤ ‖Q c.length‖*∏ i, ‖P (c.partSize i)‖ := c.norm_compAlongOrderedFinpartition_le _ _
    _ ≤ ‖Q c.length‖*innerPartitionBound B R c := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
        (fun i _ => hP _ (c.partSize_pos i) (c.partSize_le i))
    _ = _ := mul_comm _ _

/-- Outer tensors are transported in L² by the actual measure-preserving
map; only the positive inner tensors use uniform bounds. -/
theorem composition_memLp_and_bound
    (μ : Measure X) (φ : X → X) (hφ : MeasurePreserving φ μ μ)
    (P : X → FormalMultilinearSeries ℝ E E) (Q : X → FormalMultilinearSeries ℝ E F)
    (n : ℕ)
    (hcomp : AEStronglyMeasurable (fun x => (Q (φ x)).taylorComp (P x) n) μ)
    (A B R S : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hQLp : ∀ j ≤ n, MemLp (fun x => Q x j) 2 μ)
    (hQ : ∀ j ≤ n, (eLpNorm (fun x => Q x j) 2 μ).toReal ≤ A * S ^ j * (j.factorial : ℝ) ^ 2)
    (hP : ∀ j, 0 < j → j ≤ n → ∀ x, ‖P x j‖ ≤ B * R ^ j * (j.factorial : ℝ) ^ 2) :
    MemLp (fun x => (Q (φ x)).taylorComp (P x) n) 2 μ ∧
      (eLpNorm (fun x => (Q (φ x)).taylorComp (P x) n) 2 μ).toReal ≤
        A*(R*(B*S+2))^n*(n.factorial : ℝ)^2 := by
  let H : OrderedFinpartition n → X → ℝ := fun c x =>
    innerPartitionBound B R c*‖Q (φ x) c.length‖
  have hHpos (c : OrderedFinpartition n) (x : X) : 0 ≤ H c x :=
    mul_nonneg (innerPartitionBound_nonneg B R hB hR c) (norm_nonneg _)
  have hHLp (c : OrderedFinpartition n) : MemLp (H c) 2 μ :=
    (((hQLp c.length c.length_le).norm).comp_measurePreserving hφ).const_mul _
  have hsumLp : MemLp (fun x => ∑ c : OrderedFinpartition n, H c x) 2 μ :=
    memLp_finsetSum _ (fun c _ => hHLp c)
  have hdom (x : X) : ‖(Q (φ x)).taylorComp (P x) n‖ ≤ ∑ c : OrderedFinpartition n, H c x :=
    taylorComp_partition_bound (P x) (Q (φ x)) n B R (fun j hj hjn => hP j hj hjn x)
  have hcompLp : MemLp (fun x => (Q (φ x)).taylorComp (P x) n) 2 μ := by
    apply hsumLp.of_le hcomp
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun c _ => hHpos c x))]
    exact hdom x
  refine ⟨hcompLp,?_⟩
  have he : (fun x => ∑ c : OrderedFinpartition n, H c x) = ∑ c : OrderedFinpartition n, H c := by
    funext x
    simp only [Finset.sum_apply]
  have hsumNorm := eLpNorm_sum_le
    (fun c (_ : c ∈ (Finset.univ : Finset (OrderedFinpartition n))) => (hHLp
        c).aestronglyMeasurable)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hLpNorm : eLpNorm (fun x => (Q (φ x)).taylorComp (P x) n) 2 μ ≤
      ∑ c : OrderedFinpartition n, eLpNorm (H c) 2 μ := by
    apply (eLpNorm_mono_ae_real (Filter.Eventually.of_forall hdom)).trans
    rw [he]
    exact hsumNorm
  have hreal := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun c _ => (hHLp c).eLpNorm_ne_top)) hLpNorm
  rw [ENNReal.toReal_sum (fun c _ => (hHLp c).eLpNorm_ne_top)] at hreal
  have hHnorm (c : OrderedFinpartition n) :
      (eLpNorm (H c) 2 μ).toReal = innerPartitionBound B R c *
        (eLpNorm (fun x => Q x c.length) 2 μ).toReal := by
    have hfun : H c = innerPartitionBound B R c • ((fun y => ‖Q y c.length‖) ∘ φ) := rfl
    rw [hfun, eLpNorm_const_smul,
      eLpNorm_comp_measurePreserving (hQLp c.length c.length_le).aestronglyMeasurable.norm hφ,
      eLpNorm_norm, ENNReal.toReal_mul, toReal_enorm,
      Real.norm_of_nonneg (innerPartitionBound_nonneg B R hB hR c)]
  simp_rw [hHnorm] at hreal
  calc
    _ ≤ ∑ c : OrderedFinpartition n, innerPartitionBound B R c *
        (eLpNorm (fun x => Q x c.length) 2 μ).toReal := hreal
    _ ≤ ∑ c : OrderedFinpartition n, innerPartitionBound B R c *
        (A*S^c.length*(c.length.factorial : ℝ)^2) := by
      exact Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
        (hQ c.length c.length_le) (innerPartitionBound_nonneg B R hB hR c)
    _ = A*R^n*partitionSum n (B*S) := by
      rw [partitionSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [mul_comm]
      exact partition_bound_factorization c A B R S
    _ ≤ A*R^n*((B*S+2)^n*(n.factorial : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (partitionSum_le n (B*S) (mul_nonneg hB hS))
        (mul_nonneg hA (pow_nonneg hR n))
    _ = _ := by rw [mul_pow]; ring

end EulerGevreyJetCompositionLp
