/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceForceTime

/-!
# The harmonic force bound on interior time boxes

The force term in `eq:pressure-gradient-morrey` is controlled almost
everywhere by its measurable fixed-radius envelope on any local time box.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The force components lie in spatial `L^{6/5}` almost everywhere on an
arbitrary suitable-solution local box. -/
theorem origin_force_components_memLp_ae_on_local_box
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hbox : localBox Ω I B J) :
    ∀ᵐ s ∂volume.restrict J, ∀ j : Fin 3,
      MemLp (fun y => f (y, s) j) (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) := by
  apply ae_all_iff.mpr
  intro j
  have hm := origin_time_slice_norm_aemeasurable (by norm_num : (0 : ℝ) < 6 / 5)
    (hsol.2.2.2.2.1 B J hbox j).aestronglyMeasurable.aemeasurable
  have ht := lintegral_force_slice_eLpNorm_lt_top_of_sws hsol hbox j
  filter_upwards [ae_lt_top' hm ht.ne] with s hs
  exact memLp_iff.mpr hs

/-- The actual harmonic force constant is bounded a.e. by the force envelope
on any interior origin ball-times-window box. -/
theorem origin_harmonic_force_le_envelope_on_local_box
    {Ω : Set Vec3} {I J : Set ℝ} {q R : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hR : 0 < R)
    (hbox : localBox Ω I (vec3Ball 0 R) J) :
    ∀ᵐ s ∂volume.restrict J,
      ENNReal.ofReal (harmonicRemainderForceBound ((0 : Vec3), 0) hR f s) ≤
        originForceGrowthEnvelope R f s := by
  filter_upwards [origin_force_components_memLp_ae_on_local_box hsol hbox] with s hs
  exact origin_harmonic_force_le_envelope hR s hs

end CKN.Core.Step4
