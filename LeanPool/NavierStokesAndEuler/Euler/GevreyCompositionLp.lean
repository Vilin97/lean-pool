/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyComposition
public import LeanPool.NavierStokesAndEuler.Euler.VolumeSobolevComposition

@[expose] public section

/-! Gevrey-two composition with the outer derivatives in actual L².
Only the inner positive derivatives are bounded in sup norm.  The outer
L² norm is transported by a measure-preserving map, so it is not replaced
by a pointwise bound or by a volume of the ambient domain. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace EulerGevreyCompositionLp

open EulerGevreyComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def innerPartitionBound {n : ℕ} (B R : ℝ) (c : OrderedFinpartition n) : ℝ :=
  ∏ i, B*R^(c.partSize i)*((c.partSize i).factorial : ℝ)^2

lemma innerPartitionBound_nonneg {n : ℕ} (B R : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (c : OrderedFinpartition n) : 0 ≤ innerPartitionBound B R c := by
  unfold innerPartitionBound
  exact Finset.prod_nonneg fun i _ => mul_nonneg (mul_nonneg hB (pow_nonneg hR _)) (sq_nonneg _)

theorem composition_partition_bound (f : E → E) (g : E → F)
    (n : ℕ) (x : E) (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g (f x))
    (B R : ℝ) (_hB : 0 ≤ B) (_hR : 0 ≤ R)
    (hfjet : ∀ j, 0 < j → j ≤ n →
      ‖iteratedFDeriv ℝ j f x‖ ≤ B*R^j*(j.factorial : ℝ)^2) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤
      ∑ c : OrderedFinpartition n,
        innerPartitionBound B R c*‖iteratedFDeriv ℝ c.length g (f x)‖ := by
  rw [iteratedFDeriv_comp hg hf le_rfl]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  calc
    _ ≤ ‖iteratedFDeriv ℝ c.length g (f x)‖ *
        ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) f x‖ :=
      c.norm_compAlongOrderedFinpartition_le _ _
    _ ≤ ‖iteratedFDeriv ℝ c.length g (f x)‖*innerPartitionBound B R c := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
        (fun i _ => hfjet _ (c.partSize_pos i) (c.partSize_le i))
    _ = _ := mul_comm _ _

variable [MeasurableSpace E]

/-- A genuine L² composition estimate with factorial-square growth.
The measurability premise is automatic for smooth finite-dimensional
fields, and no L² premise is required for the composed derivative. -/
theorem composition_memLp_and_bound
    (μ : Measure E) (f : E → E) (g : E → F)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hmp : MeasurePreserving f μ μ) (n : ℕ)
    (hfg : AEStronglyMeasurable (iteratedFDeriv ℝ n (g ∘ f)) μ)
    (A B R S : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hgLp : ∀ j ≤ n, MemLp (iteratedFDeriv ℝ j g) 2 μ)
    (hgjet : ∀ j ≤ n,
      (eLpNorm (iteratedFDeriv ℝ j g) 2 μ).toReal ≤ A*S^j*(j.factorial : ℝ)^2)
    (hfjet : ∀ j, 0 < j → j ≤ n → ∀ x,
      ‖iteratedFDeriv ℝ j f x‖ ≤ B*R^j*(j.factorial : ℝ)^2) :
    MemLp (iteratedFDeriv ℝ n (g ∘ f)) 2 μ ∧
      (eLpNorm (iteratedFDeriv ℝ n (g ∘ f)) 2 μ).toReal ≤
        A*(R*(B*S+2))^n*(n.factorial : ℝ)^2 := by
  let H : OrderedFinpartition n → E → ℝ := fun c x =>
    innerPartitionBound B R c*‖iteratedFDeriv ℝ c.length g (f x)‖
  have hHpos (c : OrderedFinpartition n) (x : E) : 0 ≤ H c x :=
    mul_nonneg (innerPartitionBound_nonneg B R hB hR c) (norm_nonneg _)
  have hHLp (c : OrderedFinpartition n) : MemLp (H c) 2 μ :=
    (((hgLp c.length c.length_le).norm).comp_measurePreserving hmp).const_mul _
  have hsumLp : MemLp (fun x => ∑ c : OrderedFinpartition n, H c x) 2 μ :=
    memLp_finsetSum _ (fun c _ => hHLp c)
  have hdom (x : E) : ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ ∑ c : OrderedFinpartition n, H c x :=
    composition_partition_bound f g n x
      (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))
      B R hB hR (fun j hj hjn => hfjet j hj hjn x)
  have hcompLp : MemLp (iteratedFDeriv ℝ n (g ∘ f)) 2 μ := by
    apply hsumLp.of_le hfg
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
  have hLpNorm : eLpNorm (iteratedFDeriv ℝ n (g ∘ f)) 2 μ ≤
      ∑ c : OrderedFinpartition n, eLpNorm (H c) 2 μ := by
    apply (eLpNorm_mono_ae_real (Filter.Eventually.of_forall hdom)).trans
    rw [he]
    exact hsumNorm
  have hreal := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun c _ => (hHLp c).eLpNorm_ne_top)) hLpNorm
  rw [ENNReal.toReal_sum (fun c _ => (hHLp c).eLpNorm_ne_top)] at hreal
  have hHnorm (c : OrderedFinpartition n) :
      (eLpNorm (H c) 2 μ).toReal = innerPartitionBound B R c*
        (eLpNorm (iteratedFDeriv ℝ c.length g) 2 μ).toReal := by
    have hfun : H c = innerPartitionBound B R c •
        ((fun y => ‖iteratedFDeriv ℝ c.length g y‖) ∘ f) := rfl
    rw [hfun, eLpNorm_const_smul,
      eLpNorm_comp_measurePreserving (hgLp c.length c.length_le).aestronglyMeasurable.norm hmp,
      eLpNorm_norm, ENNReal.toReal_mul, toReal_enorm,
      Real.norm_of_nonneg (innerPartitionBound_nonneg B R hB hR c)]
  simp_rw [hHnorm] at hreal
  calc
    _ ≤ ∑ c : OrderedFinpartition n, innerPartitionBound B R c*
        (eLpNorm (iteratedFDeriv ℝ c.length g) 2 μ).toReal := hreal
    _ ≤ ∑ c : OrderedFinpartition n, innerPartitionBound B R c*
        (A*S^c.length*(c.length.factorial : ℝ)^2) := by
      exact Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
        (hgjet c.length c.length_le) (innerPartitionBound_nonneg B R hB hR c)
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

end EulerGevreyCompositionLp
