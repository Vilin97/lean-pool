/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientTimeRestriction
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeWeight
public import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathGluing
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathNaturality
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTimeWeight

/-!
# Profile normalization across the history/forward junction

The profile is exactly one on the history interval and the specified positive
continuous profile on the elapsed forward interval. Normalization commutes
with the actual join, without estimating either extremum of the profile.
-/

@[expose] public section


noncomputable section

namespace EulerElapsedTimePathGluing

open Set ContinuousLinearMap EulerContinuousTimeWeight EulerTimeIntervalRestriction

attribute [local instance] EulerPacketTimePathGluing.compactInterval

variable (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
  (g : C(Icc (0 : ℝ) (S - τ), ℝ))
  (hg0 : g ⟨0, le_rfl, sub_nonneg.mpr hτS⟩ = 1)

/-- The literal piecewise profile; no differentiability of it is required. -/
def profile : C(Icc (0 : ℝ) S,ℝ) :=
  join S τ hτ0 hτS (ContinuousMap.const _ 1) g hg0.symm

theorem profile_left (t : Icc (0 : ℝ) τ) :
    profile S τ hτ0 hτS g hg0 ⟨t,t.property.1,t.property.2.trans hτS⟩ = 1 :=
  join_left S τ hτ0 hτS (ContinuousMap.const _ 1) g hg0.symm t

theorem profile_right (t : Icc τ S) :
    profile S τ hτ0 hτS g hg0 ⟨t,hτ0.trans t.property.1,t.property.2⟩ =
      g ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2 τ⟩ :=
  join_right S τ hτ0 hτS (ContinuousMap.const _ 1) g hg0.symm t

theorem profile_pos (hg : ∀ t, 0 < g t) (t : Icc (0 : ℝ) S) :
    0 < profile S τ hτ0 hτS g hg0 t := by
  by_cases ht : (t : ℝ) ≤ τ
  · rw [profile_left S τ hτ0 hτS g hg0 ⟨t,t.property.1,ht⟩]
    norm_num
  · rw [profile_right S τ hτ0 hτS g hg0 ⟨t,(not_le.mp ht).le,t.property.2⟩]
    exact hg _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (hg : ∀ t, 0 < g t)
  (u : C(Icc (0 : ℝ) τ, E)) (v : C(Icc (0 : ℝ) (S - τ), E))
  (hm : u ⟨τ, hτ0, le_rfl⟩ = v ⟨0, le_rfl, sub_nonneg.mpr hτS⟩)

include hg0 hm in
theorem normalize_match : u ⟨τ,hτ0,le_rfl⟩ =
    normalize g hg v ⟨0,le_rfl,sub_nonneg.mpr hτS⟩ := by
  simp only [EulerContinuousTimeWeight.normalize_apply,hg0,inv_one,one_smul]
  exact hm

/-- The normalized join is exactly the join of the normalized forward path. -/
theorem normalize_join :
    normalize (profile S τ hτ0 hτS g hg0) (profile_pos S τ hτ0 hτS g hg0 hg)
      (join S τ hτ0 hτS u v hm) =
        join S τ hτ0 hτS u (normalize g hg v)
          (normalize_match S τ hτ0 hτS g hg0 hg u v hm) := by
  apply ContinuousMap.ext
  intro t
  by_cases ht : (t : ℝ) ≤ τ
  · have hp := profile_left S τ hτ0 hτS g hg0 ⟨t,t.property.1,ht⟩
    have hu := join_left S τ hτ0 hτS u v hm ⟨t,t.property.1,ht⟩
    have hv := join_left S τ hτ0 hτS u (normalize g hg v)
      (normalize_match S τ hτ0 hτS g hg0 hg u v hm) ⟨t,t.property.1,ht⟩
    rw [EulerContinuousTimeWeight.normalize_apply,hp,hu,hv,inv_one,one_smul]
  · have hr : τ ≤ (t : ℝ) := (not_le.mp ht).le
    have hp := profile_right S τ hτ0 hτS g hg0 ⟨t,hr,t.property.2⟩
    have hu := join_right S τ hτ0 hτS u v hm ⟨t,hr,t.property.2⟩
    have hv := join_right S τ hτ0 hτS u (normalize g hg v)
      (normalize_match S τ hτ0 hτS g hg0 hg u v hm) ⟨t,hr,t.property.2⟩
    rw [EulerContinuousTimeWeight.normalize_apply, hp, hu, hv,
        EulerContinuousTimeWeight.normalize_apply]

/-- Restriction of a normalized full path to the history is unchanged. -/
theorem normalize_initial (p : C(Icc (0 : ℝ) S, E)) :
    (normalize (profile S τ hτ0 hτS g hg0) (profile_pos S τ hτ0 hτS g hg0 hg) p).comp
      (initialInclusion S τ hτS) = p.comp (initialInclusion S τ hτS) := by
  apply ContinuousMap.ext
  intro t
  change (profile S τ hτ0 hτS g hg0 ⟨t,t.property.1,t.property.2.trans hτS⟩)⁻¹ • p _ = p _
  rw [profile_left,inv_one,one_smul]

/-- Restriction of the normalized full path to the future uses exactly g. -/
theorem normalize_tail (p : C(Icc (0 : ℝ) S, E)) :
    (normalize (profile S τ hτ0 hτS g hg0) (profile_pos S τ hτ0 hτS g hg0 hg) p).comp
      (tailInclusion S τ hτ0) = normalize g hg (p.comp (tailInclusion S τ hτ0)) := by
  apply ContinuousMap.ext
  intro t
  have hright := profile_right S τ hτ0 hτS g hg0
    ⟨τ+(t : ℝ),by linarith [t.property.1],by linarith [t.property.2]⟩
  have hsub : τ+(t : ℝ)-τ = t := by ring
  simp only [hsub] at hright
  change (profile S τ hτ0 hτS g hg0 ⟨τ+t,by
      linarith [t.property.1],by linarith [t.property.2]⟩)⁻¹ • p _ =
    (g t)⁻¹ • p _
  rw [hright]

end EulerElapsedTimePathGluing

namespace EulerLpCylinderTranslation

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerElapsedTimePathGluing EulerContinuousTimeWeight EulerParameterWordGevrey
  EulerLpCylinderRectangular
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem normalize_orbit_contDiff {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (g : C(K, ℝ)) (hg : ∀ t, 0 < g t) (p : C(K, CylinderL2 P V))
    (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p)) :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (normalize g hg p)) := by
  have he : (fun a => pathTranslate P a (normalize g hg p)) =
      fun a => normalize g hg (pathTranslate P a p) :=
    funext (fun a => translate_normalize P g hg a p)
  rw [he]
  exact (normalize g hg).contDiff.comp hp

/-- Profile normalization at the join preserves the exact external radius. -/
theorem normalized_join_block (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (g : C(Icc (0 : ℝ) (S - τ), ℝ)) (hg : ∀ t, 0 < g t)
    (hg0 : g ⟨0, le_rfl, sub_nonneg.mpr hτS⟩ = 1)
    (u : C(Icc (0 : ℝ) τ, CylinderL2 P V)) (v : C(Icc (0 : ℝ) (S - τ), CylinderL2 P V))
    (hm : u ⟨τ, hτ0, le_rfl⟩ = v ⟨0, le_rfl, sub_nonneg.mpr hτS⟩)
    (hu : ContDiff ℝ ∞ (fun a => pathTranslate P a u))
    (hv : ContDiff ℝ ∞ (fun a => pathTranslate P a v))
    {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q n : ℕ) (a : LiftTangent) :
    block directions q (fun b => pathTranslate P b
      (normalize (profile S τ hτ0 hτS g hg0) (profile_pos S τ hτ0 hτS g hg0 hg)
        (join S τ hτ0 hτS u v hm))) n a ≤
      block directions q (fun b => pathTranslate P b u) n a +
        block directions q (fun b => pathTranslate P b (normalize g hg v)) n a := by
  rw [normalize_join]
  exact join_orbit_block P S τ hτ0 hτS u (normalize g hg v)
    (normalize_match S τ hτ0 hτS g hg0 hg u v hm) hu
    (normalize_orbit_contDiff P g hg v hv) directions q n a

end EulerLpCylinderTranslation
