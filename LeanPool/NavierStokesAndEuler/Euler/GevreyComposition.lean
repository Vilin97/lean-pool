/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyCompositionPartitions
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section

/-!
# Composition preserves the Gevrey-two factorial bound

The inner function is only bounded in positive derivative orders, allowing
unbounded coordinate changes such as a flow on all of Euclidean space.
The Faà di Bruno partition estimate gives the fixed output radius
`R * (B*S + 2)`, independently of the derivative order.
-/

noncomputable section

open scoped BigOperators ContDiff

namespace EulerGevreyComposition

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma partition_bound_factorization {n : ℕ} (c : OrderedFinpartition n)
    (A B R S : ℝ) :
    (A * S^c.length * (c.length.factorial : ℝ)^2) *
        (∏ i, B * R^(c.partSize i) * ((c.partSize i).factorial : ℝ)^2) =
      A * R^n * partitionWeight (B*S) c := by
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow_eq_pow_sum, sum_partSize, Finset.prod_pow]
  unfold partitionWeight factorialProduct
  rw [mul_pow]
  ring

/-- A factorial-square bound for a formal Taylor composition, using exactly the
derivatives that occur in its order-`n` Faà di Bruno formula. -/
theorem norm_taylorComp_le
    (q : FormalMultilinearSeries ℝ F G) (p : FormalMultilinearSeries ℝ E F)
    (n : ℕ) (A B R S : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hq : ∀ j ≤ n, ‖q j‖ ≤ A * S^j * (j.factorial : ℝ)^2)
    (hp : ∀ j, 0 < j → j ≤ n → ‖p j‖ ≤ B * R^j * (j.factorial : ℝ)^2) :
    ‖q.taylorComp p n‖ ≤ A * (R*(B*S+2))^n * (n.factorial : ℝ)^2 := by
  have hterm (c : OrderedFinpartition n) :
      ‖q.compAlongOrderedFinpartition p c‖ ≤ A * R^n * partitionWeight (B*S) c := by
    calc
      _ ≤ ‖q c.length‖ * ∏ i, ‖p (c.partSize i)‖ :=
        c.norm_compAlongOrderedFinpartition_le _ _
      _ ≤ (A * S^c.length * (c.length.factorial : ℝ)^2) *
          (∏ i, B * R^(c.partSize i) * ((c.partSize i).factorial : ℝ)^2) := by
        apply mul_le_mul (hq _ c.length_le)
        · apply Finset.prod_le_prod
          · intro i _
            exact norm_nonneg _
          · intro i _
            exact hp _ (c.partSize_pos i) (c.partSize_le i)
        · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
        · positivity
      _ = _ := partition_bound_factorization c A B R S
  calc
    _ ≤ ∑ c : OrderedFinpartition n, ‖q.compAlongOrderedFinpartition p c‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition n, A * R^n * partitionWeight (B*S) c :=
      Finset.sum_le_sum (fun c _ => hterm c)
    _ = A * R^n * partitionSum n (B*S) := by
      rw [partitionSum, Finset.mul_sum]
    _ ≤ A * R^n * ((B*S+2)^n * (n.factorial : ℝ)^2) := by
      exact mul_le_mul_of_nonneg_left (partitionSum_le n (B*S) (mul_nonneg hB hS))
        (mul_nonneg hA (pow_nonneg hR n))
    _ = _ := by rw [mul_pow]; ring

/-- The actual derivative of a composition obeys a Gevrey-two bound with a
single fixed radius.  Only finite jets at the two relevant points are needed. -/
theorem norm_iteratedFDeriv_comp_gevrey_at
    (f : E → F) (g : F → G) (n : ℕ) (x : E)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g (f x))
    (A B R S : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hgjet : ∀ j ≤ n,
      ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A * S ^ j * (j.factorial : ℝ) ^ 2)
    (hfjet : ∀ j, 0 < j → j ≤ n →
      ‖iteratedFDeriv ℝ j f x‖ ≤ B * R ^ j * (j.factorial : ℝ) ^ 2) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤
      A * (R*(B*S+2))^n * (n.factorial : ℝ)^2 := by
  rw [iteratedFDeriv_comp hg hf le_rfl]
  exact norm_taylorComp_le (ftaylorSeries ℝ g (f x)) (ftaylorSeries ℝ f x)
    n A B R S hA hB hR hS hgjet hfjet

/-- Uniform all-order composition bound.  In particular the output radius
does not grow with `n` and the outer amplitude remains linear. -/
theorem norm_iteratedFDeriv_comp_gevrey
    (f : E → F) (g : F → G) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (A B R S : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hgjet : ∀ j y, ‖iteratedFDeriv ℝ j g y‖ ≤ A * S^j * (j.factorial : ℝ)^2)
    (hfjet : ∀ j, 0 < j → ∀ x,
      ‖iteratedFDeriv ℝ j f x‖ ≤ B * R^j * (j.factorial : ℝ)^2)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤
      A * (R*(B*S+2))^n * (n.factorial : ℝ)^2 := by
  apply norm_iteratedFDeriv_comp_gevrey_at f g n x
    (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))
    A B R S hA hB hR hS
  · exact fun j _ => hgjet j (f x)
  · exact fun j hj _ => hfjet j hj x

end EulerGevreyComposition
