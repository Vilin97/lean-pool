/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools

/-! Reusable test duality for divergence terms with either sign. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

/-- The sign of a divergence does not affect its homogeneous norm. -/
theorem hMinusOneNorm_neg_vecDiv_le {F : Vec 2 → Vec 2}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hper : IsZ2Periodic F) :
    hMinusOneNorm (fun x => -vecDiv F x) ≤
      ENNReal.ofReal (Real.sqrt (gradNormSq F)) := by
  have hneg : hMinusOneNorm (fun x => -cellDivergence F x) =
      hMinusOneNorm (cellDivergence F) := by
    rw [show (fun x => -cellDivergence F x) =
        fun x => (-1 : ℝ) * cellDivergence F x by funext x; ring,
      hMinusOneNorm_const_mul]
    norm_num
  have hform : (fun x => -vecDiv F x) = fun x => -cellDivergence F x := by
    funext x
    simp [cellDivergence, vecDiv, spaceGrad]
  rw [hform, hneg]
  exact hMinusOneNorm_divergence_le F hF hper

/-- Time-integrated version of signed divergence duality. -/
theorem timeHMinusOneNorm_neg_vecDiv_le {F : ℝ → Vec 2 → Vec 2}
    (hF : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ContDiff ℝ (⊤ : ℕ∞) (F t))
    (hper : ∀ t ∈ Set.Ioo (0 : ℝ) 1, IsZ2Periodic (F t)) :
    timeHMinusOneNorm (fun t x => -vecDiv (F t) x) ≤
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (gradNormSq (F t))) ^ 2) ^ (1 / 2 : ℝ) := by
  apply timeHMinusOneNorm_le_of_bound
  intro t ht
  exact hMinusOneNorm_neg_vecDiv_le (hF t ht) (hper t ht)

end AVenhance.Infra.Section5
end
