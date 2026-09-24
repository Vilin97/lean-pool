/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Kernel
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Causality

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Heat CKN.Core.HeatPotential
open CKN.Foundation.Parabolic.Morrey
open scoped ENNReal


noncomputable section

/-!
# Causality of the heat potential

Step 3 of the proof of `thm:A` splits every localized source at `t = 0`,
writing `F = F⁻ + F⁺` and `G_k = G_k⁻ + G_k⁺` with `F⁻ = 1_{t ≤ 0} F`, and
observes that the positive-time kernel `W₊` annihilates the future part, so
that on `{t ≤ 0}` the localized velocity is the potential of the past part
alone. `heatPotential_time_truncation` is that statement in the equivalent
form used here: truncating the sources after a time does not change the
potential at or before that time. No integrability hypothesis is needed,
because the integrands agree pointwise, including at the boundary time.
Consequently the cut-offs of Step 3 may reach `{t > 0}`, as they must, since
the closure of the half cylinder contains its top face.
-/

namespace CKN.Core.Endgame

/-- A time truncation preserves the data required by the heat-source
estimate and cannot increase its Morrey seminorm. -/
theorem time_truncation_source_data
    {F : ParabolicPoint → ℝ} {P θ T : ℝ} (hP : 0 ≤ P)
    (hF : AEMeasurable F volume) (hN : morreyNorm P θ F < ∞)
    (hs : HasCompactSupport F) :
    AEMeasurable ({v : ParabolicPoint | v.2 ≤ T}.indicator F) volume ∧
      morreyNorm P θ ({v : ParabolicPoint | v.2 ≤ T}.indicator F) < ∞ ∧
      HasCompactSupport ({v : ParabolicPoint | v.2 ≤ T}.indicator F) := by
  refine ⟨hF.indicator ?_, (morreyNorm_indicator_le hP _ F).trans_lt hN, ?_⟩
  · exact (isClosed_le continuous_snd_parabolicPoint continuous_const).measurableSet
  · apply hs.mono
    intro z hz
    by_contra hzero
    have hz0 : F z = 0 := by simpa only [Function.mem_support, not_not] using hzero
    exact hz (by by_cases ht : z.2 ≤ T <;> simp [ht, hz0])

/-- Truncating the sources after a time does not change their heat potential
at or before that time. No integrability assumption is needed: the integrands
are pointwise equal, including at the time boundary. -/
theorem heatPotential_time_truncation
    (F : ParabolicPoint → ℝ) (G : Fin 3 → ParabolicPoint → ℝ)
    {T : ℝ} {w : ParabolicPoint} (hw : w.2 ≤ T) :
    heatPotential ({v : ParabolicPoint | v.2 ≤ T}.indicator F)
      (fun i => {v : ParabolicPoint | v.2 ≤ T}.indicator (G i)) w =
        heatPotential F G w := by
  have hF : ∀ v, heatPotentialKernel w v *
      {v : ParabolicPoint | v.2 ≤ T}.indicator F v =
        heatPotentialKernel w v * F v := by
    intro v
    by_cases hv : v.2 ≤ T
    · simp [hv]
    · have ht : w.2 - v.2 ≤ 0 := by linarith only [hw, not_le.mp hv]
      have hk : heatPotentialKernel w v = 0 := by
        exact heatKernelPlus_eq_zero_of_nonpos ht
      simp [hk]
  have hG : ∀ i v, heatPotentialSpatialKernel i w v *
      {v : ParabolicPoint | v.2 ≤ T}.indicator (G i) v =
        heatPotentialSpatialKernel i w v * G i v := by
    intro i v
    by_cases hv : v.2 ≤ T
    · simp [hv]
    · have ht : ¬0 < w.2 - v.2 := by linarith only [hw, not_le.mp hv]
      simp [heatPotentialSpatialKernel, heatKernelSpaceDerivative, ht]
  unfold heatPotential
  congr 1
  · exact integral_congr_ae (Filter.Eventually.of_forall hF)
  · apply Finset.sum_congr rfl
    intro i _hi
    exact integral_congr_ae (Filter.Eventually.of_forall (hG i))

end CKN.Core.Endgame
