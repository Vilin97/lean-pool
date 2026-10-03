/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.DivergenceTools

/-! HDot⁻¹ duality estimate for the divergence-form term `twistie3`. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Vector flux under the divergence in `twistie3`. -/
def twistie3Flux (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t • (diffusionMatrix I hΦ m κm t x).mulVec
      (spaceGrad (T t) x - G I hΦ m T (lIdx β I.Λ m k) t x)

/-- Time-integrated HDot⁻¹ estimate for `twistie3`. -/
theorem timeHMinusOneNorm_twistie3_le
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (hF : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ContDiff ℝ (⊤ : ℕ∞) (twistie3Flux I hΦ m κm T t))
    (hper : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      IsZ2Periodic (twistie3Flux I hΦ m κm T t)) :
    timeHMinusOneNorm (fun t => twistie3 I hΦ m κm T t) ≤
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (gradNormSq (twistie3Flux I hΦ m κm T t))) ^ 2) ^
          (1 / 2 : ℝ) := by
  have hEq : (fun t => twistie3 I hΦ m κm T t) =
      fun t x => -vecDiv (twistie3Flux I hΦ m κm T t) x := by
    funext t x
    rfl
  rw [hEq]
  exact timeHMinusOneNorm_neg_vecDiv_le hF hper

end AVenhance.Infra.Section5
end
