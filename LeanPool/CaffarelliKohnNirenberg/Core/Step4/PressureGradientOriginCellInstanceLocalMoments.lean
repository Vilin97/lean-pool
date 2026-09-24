/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceWholeFinite

/-!
# Local velocity moments throughout the solution domain

The cylinder integrability of the velocity cube extends to every compact
space-time subset of the solution domain. This supplies the time integrals
on arbitrary compact windows in `prop:bootstrap`, without restricting time
to the origin unit cylinder.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The velocity cube of a suitable solution is locally integrable at every
point of its open space-time domain. -/
theorem origin_velocity_cube_locallyIntegrableOn_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) :
    LocallyIntegrableOn (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ)) (spaceTimeSet Ω I) volume := by
  intro z hz
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_spaceTimeSet Ω I hsol.1 hsol.2.1).mem_nhds hz)
  let R := ε / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have h2R : 0 < 2 * R := by positivity
  have hsub : closure (parabolicCylinder z.1 (z.2 + R ^ 2) (2 * R)) ⊆ spaceTimeSet Ω I := by
    intro w hw
    rw [closure_parabolicCylinder h2R] at hw
    apply hεsub
    rw [Metric.mem_ball, dist_eq_parabolicDist]
    change max (vec3EuclideanNorm (w.1 - z.1)) (Real.sqrt |w.2 - z.2|) < ε
    apply max_lt
    · have hspace := hw.1
      change vec3EuclideanNorm (w.1 - z.1) ≤ 2 * R at hspace
      dsimp [R] at hspace
      linarith only [hspace, hε]
    · apply (Real.sqrt_lt' hε).mpr
      have htime : |w.2 - z.2| ≤ 3 * R ^ 2 := by
        rw [abs_le]
        constructor <;> nlinarith only [hw.2.1, hw.2.2]
      have hlt : 3 * R ^ 2 < ε ^ 2 := by
        dsimp [R]
        nlinarith only [sq_pos_of_pos hε]
      exact htime.trans_lt hlt
  refine ⟨parabolicCylinder z.1 (z.2 + R ^ 2) (2 * R),
    mem_nhdsWithin_of_mem_nhds ?_, tsai_integrable_velocity_cube_on_cylinder (z := (z.1, z.2 + R ^ 2)) hsol h2R hsub⟩
  apply mem_interior_iff_mem_nhds.mp
  rw [interior_parabolicCylinder]
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
    exact h2R
  · nlinarith only [sq_pos_of_pos hR]
  · linarith only [sq_pos_of_pos hR]

/-- The velocity cube is integrable on any local box, including compact
time windows anywhere in the solution interval. -/
theorem origin_velocity_cube_integrable_on_local_box
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hbox : localBox Ω I B J) :
    IntegrableOn (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ)) (spaceTimeSet B J) volume := by
  have hcompact : IsCompact (parabolicHomeomorph ⁻¹' (closure B ×ˢ closure J)) :=
    parabolicHomeomorph.isCompact_preimage.mpr (hbox.2.1.prod hbox.2.2.2.2.1)
  have hsub : parabolicHomeomorph ⁻¹' (closure B ×ˢ closure J) ⊆ spaceTimeSet Ω I := by
    intro w hw
    exact ⟨hbox.2.2.1 hw.1, hbox.2.2.2.2.2 hw.2⟩
  have hh := (origin_velocity_cube_locallyIntegrableOn_of_sws hsol).integrableOn_compact_subset hsub hcompact
  exact hh.mono_set (fun w hw => ⟨subset_closure hw.1, subset_closure hw.2⟩)

end CKN.Core.Step4
