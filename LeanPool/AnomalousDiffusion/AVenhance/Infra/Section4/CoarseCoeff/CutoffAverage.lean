/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Representation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.CutoffConsequences

/-! # Cutoff Average

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Convexity of the large-cutoff average, including its actual finite support. -/
theorem coarseCoeff_hatXi_average_abs_le {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (f : ℤ → ℝ) {B : ℝ}
    (hb : ∀ l : ℤ, I.hatXiML m l t ≠ 0 → |f l| ≤ B) :
    |∑' l : ℤ, I.hatXiML m l t * f l| ≤ B := by
  classical
  let S := (I.hatXiML_support_finite hm t).toFinset
  have hz (l : ℤ) (hl : l ∉ S) : I.hatXiML m l t = 0 := by
    by_contra hne
    exact hl ((Set.Finite.mem_toFinset _).2 hne)
  have hsum : (∑' l : ℤ, I.hatXiML m l t * f l) =
      ∑ l ∈ S, I.hatXiML m l t * f l :=
    tsum_eq_sum (fun l hl => by rw [hz l hl, zero_mul])
  have hweights : ∑ l ∈ S, I.hatXiML m l t = 1 := by
    have hh : (∑' l : ℤ, I.hatXiML m l t) = ∑ l ∈ S, I.hatXiML m l t :=
      tsum_eq_sum (fun l hl => hz l hl)
    rw [← hh]
    exact Ingredients.hatXiML_partition I hm t
  rw [hsum]
  calc
    |∑ l ∈ S, I.hatXiML m l t * f l| ≤
        ∑ l ∈ S, |I.hatXiML m l t * f l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ S, I.hatXiML m l t * B := by
      apply Finset.sum_le_sum
      intro l hl
      have hw := (Ingredients.hatXiML_mem_Icc I hm l t).1
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hb l ((Set.Finite.mem_toFinset _).1 hl)) hw
    _ = B := by rw [← Finset.sum_mul, hweights, one_mul]

end AVenhance.Infra.Section4
