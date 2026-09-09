/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.NormNum.GCD

/-! A genuine L² Gevrey product estimate, with the coefficient tensors
bounded uniformly and the field tensors measured in L². It applies on
any base, including cylinder tensors evaluated through a cover section. -/

@[expose] public section


noncomputable section

namespace EulerGevreyProductLp

open MeasureTheory Filter EulerGevrey
open scoped ContDiff ENNReal

variable {X E V W : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedSpace ℝ V] in
theorem finite_domination {ι : Type*} (μ : Measure X) (I : Finset ι)
    (f : X → V) (hf : AEStronglyMeasurable f μ) (H : ι → X → ℝ)
    (hH : ∀ i ∈ I, MemLp (H i) 2 μ)
    (hdom : ∀ x, ‖f x‖ ≤ ∑ i ∈ I, H i x) :
    MemLp f 2 μ ∧ (eLpNorm f 2 μ).toReal ≤ ∑ i ∈ I, (eLpNorm (H i) 2 μ).toReal := by
  have hsum : MemLp (fun x => ∑ i ∈ I, H i x) 2 μ := memLp_finsetSum I hH
  have hLp := hsum.mono' hf (Eventually.of_forall hdom)
  refine ⟨hLp,?_⟩
  have he : (fun x => ∑ i ∈ I, H i x) = ∑ i ∈ I, H i := by
    funext x
    simp only [Finset.sum_apply]
  have hn : eLpNorm f 2 μ ≤ ∑ i ∈ I, eLpNorm (H i) 2 μ := by
    apply (eLpNorm_mono_ae_real (Eventually.of_forall hdom)).trans
    rw [he]
    exact eLpNorm_sum_le (fun i hi => (hH i hi).aestronglyMeasurable) (by norm_num)
  have hr := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i hi => (hH i hi).eLpNorm_ne_top)) hn
  rwa [ENNReal.toReal_sum (fun i hi => (hH i hi).eLpNorm_ne_top)] at hr

theorem clm_apply_memLp_and_bound
    (μ : Measure X) (σ : X → E) (f : E → V →L[ℝ] W) (g : E → V)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ)
    (hm : AEStronglyMeasurable (fun x => iteratedFDeriv ℝ n (fun y => f y (g y)) (σ x)) μ)
    (R B C : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B) (hC : 0 ≤ C) (d e : ℕ)
    (hb : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j f (σ x)‖ ≤ B * majorant R d j)
    (hLp : ∀ j ≤ n, MemLp (fun x => iteratedFDeriv ℝ j g (σ x)) 2 μ)
    (hNorm : ∀ j ≤ n,
      (eLpNorm (fun x => iteratedFDeriv ℝ j g (σ x)) 2 μ).toReal ≤ C * majorant R e j) :
    MemLp (fun x => iteratedFDeriv ℝ n (fun y => f y (g y)) (σ x)) 2 μ ∧
      (eLpNorm (fun x => iteratedFDeriv ℝ n (fun y => f y (g y)) (σ x)) 2 μ).toReal ≤
        (3*B*C)*majorant R (d+e) n := by
  let a : ℕ → ℝ := fun j => (n.choose j : ℝ)*(B*majorant R d j)
  let H : ℕ → X → ℝ := fun j x => a j*‖iteratedFDeriv ℝ (n-j) g (σ x)‖
  have ha (j : ℕ) : 0 ≤ a j :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB (majorant_nonneg R hR d j))
  have hH (j : ℕ) (_hj : j ∈ Finset.range (n+1)) : MemLp (H j) 2 μ :=
    ((hLp (n-j) (Nat.sub_le n j)).norm).const_mul _
  have hdom (x : X) :
      ‖iteratedFDeriv ℝ n (fun y => f y (g y)) (σ x)‖ ≤ ∑ j ∈ Finset.range (n+1), H j x := by
    apply (norm_iteratedFDeriv_clm_apply hf hg (σ x) (by simp)).trans
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hb j (by
          simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) x)
        (Nat.cast_nonneg _)) (norm_nonneg _)
  obtain ⟨hprod,hn⟩ := finite_domination μ (Finset.range (n+1)) _ hm H hH hdom
  refine ⟨hprod,hn.trans ?_⟩
  have hHnorm (j : ℕ) : (eLpNorm (H j) 2 μ).toReal =
      a j*(eLpNorm (fun x => iteratedFDeriv ℝ (n-j) g (σ x)) 2 μ).toReal := by
    have he : H j = a j • (fun x => ‖iteratedFDeriv ℝ (n-j) g (σ x)‖) := rfl
    rw [he,eLpNorm_const_smul,eLpNorm_norm,ENNReal.toReal_mul,toReal_enorm,Real.norm_of_nonneg (ha
        j)]
  simp_rw [hHnorm]
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), a j*(C*majorant R e (n-j)) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hNorm (n-j) (Nat.sub_le n j)) (ha j))
    _ = B*C*(∑ j ∈ Finset.range (n+1),
        (n.choose j : ℝ)*majorant R d j*majorant R e (n-j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [a]
      ring
    _ ≤ B*C*(3*majorant R (d+e) n) :=
      mul_le_mul_of_nonneg_left (majorant_convolution R hR n d e) (mul_nonneg hB hC)
    _ = _ := by ring

end EulerGevreyProductLp
