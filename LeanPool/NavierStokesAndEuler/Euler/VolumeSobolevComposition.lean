/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedGradientSpace
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Actual Sobolev integrability under a smooth volume-preserving change
of variables, with an explicit finite-order composition constant. -/

@[expose] public section


noncomputable section

namespace EulerVolumeSobolevComposition

open Set MeasureTheory EulerLiftedGradientSpace
open scoped ContDiff NNReal ENNReal

variable (f g : Vector3 → Vector3) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
  (n : ℕ) (D : ℝ) (hD : 0 ≤ D)
  (hjet : ∀ i, 1 ≤ i → i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i)

include hf hg hjet in
theorem compositionTensor_pointwise (x : Vector3) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤
      ((n.factorial : ℝ)*D^n) * ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖ := by
  have h := norm_iteratedFDeriv_comp_le hg hf (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω)) x
    (C := ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖) (D := D)
    (fun i hi => Finset.single_le_sum
      (f := fun j : Fin (n+1) => ‖iteratedFDeriv ℝ j.val g (f x)‖)
      (fun _ _ => norm_nonneg _)
      (Finset.mem_univ (⟨i,by omega⟩ : Fin (n+1))))
    (fun i h1 hi => hjet i h1 hi x)
  exact h.trans_eq (by ring)

variable (hmp : MeasurePreserving f volume volume)
  (hLp : ∀ i, i ≤ n → MemLp (iteratedFDeriv ℝ i g) 2 volume)

include hmp hLp in
theorem composedJetNorm_memLp (i : Fin (n + 1)) :
    MemLp (fun x => ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume :=
  ((hLp i (by omega)).norm).comp_measurePreserving hmp

include hf hg hD hjet hmp hLp in
theorem compositionTensor_memLp :
    MemLp (iteratedFDeriv ℝ n (g ∘ f)) 2 volume := by
  have hs : MemLp (fun x => ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume :=
    memLp_finsetSum _ (fun i _ => composedJetNorm_memLp f g n hmp hLp i)
  have hc : Continuous (iteratedFDeriv ℝ n (g ∘ f)) :=
    (hg.comp hf).continuous_iteratedFDeriv (by simp)
  apply (hs.const_mul ((n.factorial : ℝ)*D^n)).of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))]
  exact compositionTensor_pointwise f g hf hg n D hjet x

/-- Composition tensor Lᵖ, given by `(compositionTensor_memLp f g hf hg n D hD hjet hmp
hLp).toLp (iteratedFDeriv ℝ n (g ∘ f))`. -/
def compositionTensorLp :
    Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3) :=
  (compositionTensor_memLp f g hf hg n D hD hjet hmp hLp).toLp (iteratedFDeriv ℝ n (g ∘ f))

theorem compositionTensorLp_norm_le :
    ‖compositionTensorLp f g hf hg n D hD hjet hmp hLp‖ ≤
      ((n.factorial : ℝ)*D^n) * ∑ i : Fin (n+1),
        (eLpNorm (iteratedFDeriv ℝ i.val g) 2 volume).toReal := by
  let β : ℝ≥0 := ⟨(n.factorial : ℝ)*D^n,by positivity⟩
  have hA : eLpNorm (iteratedFDeriv ℝ n (g ∘ f)) 2 volume ≤
      (β : ℝ≥0∞)*eLpNorm (fun x => ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    filter_upwards [] with x
    apply NNReal.coe_le_coe.mp
    change ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ ((n.factorial : ℝ)*D^n) *
      ‖∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖‖
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact compositionTensor_pointwise f g hf hg n D hjet x
  have he : (fun x => ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖) =
      ∑ i : Fin (n+1), (fun x => ‖iteratedFDeriv ℝ i.val g (f x)‖) := by
    funext x
    simp only [Finset.sum_apply]
  rw [he] at hA
  have hB := eLpNorm_sum_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n+1)))) =>
    (composedJetNorm_memLp f g n hmp hLp i).aestronglyMeasurable)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hc (i : Fin (n+1)) : eLpNorm (fun x => ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume =
      eLpNorm (iteratedFDeriv ℝ i.val g) 2 volume := by
    change eLpNorm ((fun y => ‖iteratedFDeriv ℝ i.val g y‖) ∘ f) 2 volume = _
    rw [eLpNorm_comp_measurePreserving (hLp i (by
        omega)).aestronglyMeasurable.norm hmp,eLpNorm_norm]
  simp_rw [hc] at hB
  have hAB : eLpNorm (iteratedFDeriv ℝ n (g ∘ f)) 2 volume ≤
      (β : ℝ≥0∞)*∑ i : Fin (n+1), eLpNorm (iteratedFDeriv ℝ i.val g) 2 volume := by
    exact hA.trans (mul_le_mul le_rfl hB (by positivity) (by positivity))
  have hfin : (β : ℝ≥0∞)*∑ i : Fin (n+1),
      eLpNorm (iteratedFDeriv ℝ i.val g) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.sum_ne_top.2 (fun i _ => (hLp i (by omega)).eLpNorm_ne_top))
  have hR := ENNReal.toReal_mono hfin hAB
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal,
    ENNReal.toReal_sum (fun (i : Fin (n+1)) _ => (hLp i.val (by omega)).eLpNorm_ne_top)] at hR
  have hβ : (β : ℝ) = (n.factorial : ℝ)*D^n := rfl
  rw [hβ] at hR
  simpa only [compositionTensorLp,Lp.norm_toLp] using hR

end EulerVolumeSobolevComposition
