/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! Common source-scale target and scalar L²-to-HDot⁻¹ transfer.

The scale inputs in the term files are estimates on spatial L² quantities.
They do not assume the desired negative-norm estimate. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

/-- The requested Section 5 source scale, with the physical coefficient bounds
left as explicit hypotheses in each term-specific estimate. -/
def section5SourceScale (β : ℝ) (Λ m : ℕ) (κm C : ℝ)
    (θ₀ : Vec 2 → ℝ) : ℝ :=
  C * (epsilon β Λ (m - 1)) ^ delta β * Real.sqrt κm *
    Real.sqrt (l2NormSq θ₀)

/-- Transfer a source-scale estimate on the spatial L² norms of a mean-zero
scalar term to the exact time-integrated HDot⁻¹ norm. -/
theorem timeHMinusOneNorm_le_L2_of_sourceScale
    {f : ℝ → Vec 2 → ℝ} {S : ℝ}
    (hL2 : ∀ t ∈ Set.Ioo (0 : ℝ) 1, MemL2On unitCube (f t))
    (hmean : ∀ t ∈ Set.Ioo (0 : ℝ) 1, MeanZeroOn unitCube (f t))
    (hscale :
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.sqrt (l2NormSq (f t))) ^ 2) ^
          (1 / 2 : ℝ) ≤ ENNReal.ofReal S) :
    timeHMinusOneNorm f ≤ ENNReal.ofReal S := by
  exact (timeHMinusOneNorm_le_L2 hL2 hmean).trans hscale

end AVenhance.Infra.Section5
end
