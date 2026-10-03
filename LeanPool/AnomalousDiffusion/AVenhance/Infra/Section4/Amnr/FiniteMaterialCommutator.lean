/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureDiffusionRates

/-! Quantitative material/spatial commutation for arbitrary outer words. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Every outer word can be applied to the actual material/spatial
commutator; complementary subwords control each product factor. -/
theorem amnr_word_material_spatial_abs_le_of_finite_bounds
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (w : List (Option (Fin 2)))
    (hf : ContDiff ℝ (amnrBudget w + 2) f) (i : Fin 2) (z : AmnrSpace) {S H F B G : ℝ}
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hF : |amnrWord b (w ++ [some i, none]) f z| ≤ F)
    (hBb : ∀ p v, v.Sublist w →
      |amnrWord b v (amnrVelocityGradient b p i) z| ≤ B * amnrWeight S H v)
    (hGb : ∀ p v, v.Sublist w →
      |amnrWord b v (amnrOp b (some p) f) z| ≤ G * amnrWeight S H v) :
    |amnrWord b w (amnrOp b none (amnrOp b (some i) f)) z| ≤
      F + (2 : ℝ) ^ (w.length + 1) * B * G * amnrWeight S H w := by
  let A := amnrWord b [some i, none] f
  let P := fun p : Fin 2 => amnrVelocityGradient b p i * amnrOp b (some p) f
  have hA : ContDiff ℝ (amnrBudget w) A := contDiffOn_univ.mp
    (amnrWord_contDiffOn isOpen_univ (hb.of_le (by simp)).contDiffOn hf.contDiffOn
      [some i, none] (n := amnrBudget w) (by simp))
  have hBs (p : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (amnrVelocityGradient b p i) :=
    contDiffOn_univ.mp (amnrVelocityGradient_contDiffOn_infty isOpen_univ hb.contDiffOn p i)
  have hGs (p : Fin 2) : ContDiff ℝ (amnrBudget w) (amnrOp b (some p) f) :=
    contDiffOn_univ.mp (amnrWord_contDiffOn isOpen_univ (hb.of_le (by simp)).contDiffOn
      hf.contDiffOn [some p] (n := amnrBudget w) (by simp))
  have hP (p : Fin 2) : ContDiff ℝ (amnrBudget w) (P p) := ((hBs p).of_le (by simp)).mul (hGs p)
  have hsum : ContDiff ℝ (amnrBudget w) (∑ p : Fin 2, P p) := by
    simpa only [Finset.sum_fn] using ContDiff.sum (s := Finset.univ) (fun p _ => hP p)
  have heq : amnrOp b none (amnrOp b (some i) f) = A - ∑ p : Fin 2, P p := by
    funext y
    exact amnr_material_spatial_commutator (hb.differentiable (by simp) y)
      (hf.contDiffAt.of_le (by exact_mod_cast (show 2 ≤ amnrBudget w + 2 by omega))) i
  rw [heq, amnrWord_sub isOpen_univ (hb.of_le (by simp)).contDiffOn
    hA.contDiffOn hsum.contDiffOn w (amnrBudget_length_le w) (mem_univ z)]
  have hfinite := amnrWord_sum isOpen_univ
    (hb.of_le (by simp)).contDiffOn Finset.univ P
    (fun p _ => (hP p).of_le (by exact_mod_cast amnrBudget_length_le w) |>.contDiffOn)
    w (N := w.length) le_rfl (mem_univ z)
  have hprod (p : Fin 2) : |amnrWord b w (P p) z| ≤
      (2 : ℝ) ^ w.length * B * G * amnrWeight S H w := by
    have hh := amnrWord_mul_abs_le_at (N := amnrBudget w) isOpen_univ
      (hb.of_le (by simp)).contDiffOn ((hBs p).of_le (by simp)).contDiffOn
      (hGs p).contDiffOn hS hH hB hG w le_rfl (mem_univ z) (hBb p) (hGb p)
    exact hh
  have hAb : |amnrWord b w A z| ≤ F := by rw [← amnrWord_append]; exact hF
  have hPb : |amnrWord b w (∑ p : Fin 2, P p) z| ≤
      (2 : ℝ) ^ (w.length + 1) * B * G * amnrWeight S H w := by
    rw [hfinite]
    simp only [Finset.sum_apply]
    have hh := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin 2))) => hprod p))
    refine hh.trans_eq ?_
    rw [Fin.sum_univ_two, pow_succ]
    ring
  exact (abs_sub _ _).trans (add_le_add hAb hPb)

end AVenhance.Infra.Section4
