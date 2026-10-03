/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatXiML

/-! Pointwise consequences of the large-scale cutoff requirements. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Ingredients

theorem CutoffConsequences.indIcc_nonneg (a b t : ℝ) : 0 ≤ AVenhance.indIcc a b t := by
  by_cases ht : t ∈ Set.Icc a b <;> simp [AVenhance.indIcc, ht]

theorem CutoffConsequences.indIcc_le_one (a b t : ℝ) : AVenhance.indIcc a b t ≤ 1 := by
  by_cases ht : t ∈ Set.Icc a b <;> simp [AVenhance.indIcc, ht]

/-- `e.hatxi.partition` (1345-1347): the translated `ξ̂` functions sum to one. -/
theorem hatXiML_partition {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    ∑' l : ℤ, I.hatXiML m l t = 1 := by
  simpa [AVenhance.Ingredients.hatXiML] using I.hatXi_partition m hm t

/-- `e.hatxi.partition` and `e.zeta.prime.ml.fitting` (1327-1347):
each translated `ξ̂` cutoff lies between zero and one. -/
theorem hatXiML_mem_Icc {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ) :
    I.hatXiML m l t ∈ Set.Icc 0 1 := by
  constructor
  · exact (CutoffConsequences.indIcc_nonneg _ _ _).trans (I.hatXi_ge m hm l t)
  · exact (I.hatXi_le m hm l t).trans (CutoffConsequences.indIcc_le_one _ _ _)

/-- `e.zeta.prime.ml.fitting` (1327-1334): each translated `ζ̂` cutoff is nonnegative. -/
theorem hatZetaML_nonneg {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ) :
    0 ≤ I.hatZetaML m l t :=
  (CutoffConsequences.indIcc_nonneg _ _ _).trans (I.hatZeta_ge m hm l t)

end AVenhance.Infra.Ingredients
