/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.WordBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Representation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.CutoffAverage
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.CutoffMemory
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.MatrixBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergy

/-! # Iterates Coefficient Words

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- The LeftJacobian jet uses all flow suborders in the quadratic Leibniz budget. -/
theorem iterate_sMat_word_entry_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κm t : ℝ)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t))
    (w : List (Fin 2)) (x : Vec 2) {K : ℝ} {F : ℕ → ℝ}
    (hK : ∀ i j, |I.Kmat κm m t i j| ≤ K)
    (hF : ∀ l, I.hatXiML m l t ≠ 0 → ∀ v : List (Fin 2), ∀ y i j,
      |iterateSpatialWord v (fun z => (I.flowGrad hΦ m l t z - 1) i j) y| ≤ F v.length)
    (i j : Fin 2) :
    |iterateSpatialWord w (fun y => I.sMat hΦ m κm t y i j) x| ≤
      coarseCoeffWordBudget K κm F w := by
  classical
  have hactive : ∃ l : ℤ, I.hatXiML m l t ≠ 0 := by
    by_contra h
    push Not at h
    have hp := Infra.Ingredients.hatXiML_partition I hm t
    simp only [h, tsum_zero] at hp
    norm_num at hp
  obtain ⟨l, hl⟩ := hactive
  have hF0 (n : ℕ) : 0 ≤ F n := by
    have hb := hF l hl (List.replicate n (0 : Fin 2)) 0 0 0
    simp only [List.length_replicate] at hb
    exact (abs_nonneg _).trans hb
  exact (sMat_coarseCoeffForm I hΦ m κm).word_entry_bound hm t hF0 hK hflow hF w x i j

end AVenhance.Infra.Section4
