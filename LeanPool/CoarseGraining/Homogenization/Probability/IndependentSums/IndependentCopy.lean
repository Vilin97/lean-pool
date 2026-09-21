/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Probability.IdentDistrib

/-! # Independent Copy -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω ι 𝓧 𝓨 : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
variable {μ : Measure Ω}

/-- On the product probability space `Ω × Ω`, the two coordinate copies of a
random variable have the same law. This is the basic independent-copy package
used later in the symmetrization step of Rosenthal's inequality. -/
theorem identDistrib_comp_fst_comp_snd_prod
    [IsProbabilityMeasure μ] {X : Ω → 𝓧} (hX : AEMeasurable X μ) :
    IdentDistrib
      (fun ω : Ω × Ω => X ω.1)
      (fun ω : Ω × Ω => X ω.2)
      (μ.prod μ)
      (μ.prod μ) := by
  refine
    { aemeasurable_fst := hX.comp_quasiMeasurePreserving
        measurePreserving_fst.quasiMeasurePreserving
      aemeasurable_snd := hX.comp_quasiMeasurePreserving
        measurePreserving_snd.quasiMeasurePreserving
      map_eq := ?_ }
  have hXfst : AEMeasurable X ((μ.prod μ).map Prod.fst) := by
    rw [measurePreserving_fst.map_eq]
    exact hX
  have hXsnd : AEMeasurable X ((μ.prod μ).map Prod.snd) := by
    rw [measurePreserving_snd.map_eq]
    exact hX
  calc
    Measure.map (fun ω : Ω × Ω => X ω.1) (μ.prod μ)
        = Measure.map X ((μ.prod μ).map Prod.fst) := by
            symm
            exact AEMeasurable.map_map_of_aemeasurable hXfst measurable_fst.aemeasurable
    _ = Measure.map X μ := by rw [measurePreserving_fst.map_eq]
    _ = Measure.map X ((μ.prod μ).map Prod.snd) := by rw [measurePreserving_snd.map_eq]
    _ = Measure.map (fun ω : Ω × Ω => X ω.2) (μ.prod μ) := by
          exact AEMeasurable.map_map_of_aemeasurable hXsnd measurable_snd.aemeasurable

/-- On the product probability space `Ω × Ω`, functions of the first
coordinate are independent from functions of the second coordinate. -/
theorem indepFun_comp_fst_comp_snd_prod
    [IsProbabilityMeasure μ] {X : Ω → 𝓧} {Y : Ω → 𝓨}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    (fun ω : Ω × Ω => X ω.1) ⟂ᵢ[μ.prod μ] (fun ω => Y ω.2) := by
  exact indepFun_prod₀ (μ := μ) (ν := μ) hX hY

variable {X : ι → Ω → ℝ}

/-- The finite-sum copy obtained from the first coordinate and the corresponding
copy obtained from the second coordinate are identically distributed on
`Ω × Ω`. -/
theorem identDistrib_finset_sum_comp_fst_comp_snd_prod
    [IsProbabilityMeasure μ] {s : Finset ι}
    (hX : ∀ i, Measurable (X i)) :
    IdentDistrib
      (fun ω : Ω × Ω => ∑ i ∈ s, X i ω.1)
      (fun ω : Ω × Ω => ∑ i ∈ s, X i ω.2)
      (μ.prod μ)
      (μ.prod μ) := by
  have hsum : Measurable (fun ω => ∑ i ∈ s, X i ω) := by
    exact Finset.measurable_sum s fun i _ => hX i
  simpa [Finset.sum_apply] using
    (identDistrib_comp_fst_comp_snd_prod
      (μ := μ)
      (X := fun ω => ∑ i ∈ s, X i ω)
      hsum.aemeasurable)

/-- Finite sums formed from the first and second coordinate copies are
independent on `Ω × Ω`. -/
theorem indepFun_finset_sum_comp_fst_comp_snd_prod
    [IsProbabilityMeasure μ] {s t : Finset ι}
    (hX : ∀ i, Measurable (X i)) :
    (fun ω : Ω × Ω => ∑ i ∈ s, X i ω.1) ⟂ᵢ[μ.prod μ]
      (fun ω => ∑ i ∈ t, X i ω.2) := by
  have hs : Measurable (fun ω => ∑ i ∈ s, X i ω) := by
    exact Finset.measurable_sum s fun i _ => hX i
  have ht : Measurable (fun ω => ∑ i ∈ t, X i ω) := by
    exact Finset.measurable_sum t fun i _ => hX i
  exact indepFun_comp_fst_comp_snd_prod
    (μ := μ)
    (X := fun ω => ∑ i ∈ s, X i ω)
    (Y := fun ω => ∑ i ∈ t, X i ω)
    hs.aemeasurable
    ht.aemeasurable

end
end IndependentSums
end Homogenization
