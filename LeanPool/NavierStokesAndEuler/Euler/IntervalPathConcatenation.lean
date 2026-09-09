/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral

@[expose] public section

/-! Concatenation of two paths on closed time intervals. Matching
endpoint values and derivatives give a genuine derivative at the seam. -/

noncomputable section

namespace EulerIntervalConcatenation

open Set Filter
open scoped Topology

def join {E : Type*} (T S : ℝ) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (f : Icc (0 : ℝ) T → E) (g : Icc (0 : ℝ) S → E) (t : ℝ) : E :=
  if t ≤ T then f (projIcc 0 T hT t) else g (projIcc 0 S hS (t-T))

variable {E : Type*} {T S : ℝ} {hT : 0 ≤ T} {hS : 0 ≤ S}
  (f : Icc (0 : ℝ) T → E) (g : Icc (0 : ℝ) S → E)

theorem join_left {t : ℝ} (ht : t ≤ T) :
    join T S hT hS f g t=f (projIcc 0 T hT t) := by simp only [join,ht,ite_true]

theorem join_right (hfg : f ⟨T,hT,le_rfl⟩=g ⟨0,le_rfl,hS⟩) {t : ℝ} (ht : T ≤ t) :
    join T S hT hS f g t=g (projIcc 0 S hS (t-T)) := by
  by_cases h : t ≤ T
  · have he : t=T := le_antisymm h ht
    subst t
    simpa only [join,le_refl,ite_true,sub_self,
      projIcc_of_mem hT (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩),
      projIcc_of_mem hS (show (0 : ℝ) ∈ Icc 0 S from ⟨le_rfl,hS⟩)] using hfg
  · simp only [join,h,ite_false]

theorem map_join {F : Type*} (A : E → F) (t : ℝ) :
    A (join T S hT hS f g t)=
      join T S hT hS (fun s => A (f s)) (fun s => A (g s)) t := by
  unfold join
  split <;> rfl

theorem join_continuous [TopologicalSpace E] (hf : Continuous f) (hg : Continuous g)
    (hfg : f ⟨T,hT,le_rfl⟩=g ⟨0,le_rfl,hS⟩) :
    Continuous (join T S hT hS f g) := by
  apply Continuous.if_le (hf.comp continuous_projIcc)
    (hg.comp (continuous_projIcc.comp (continuous_id.sub continuous_const)))
    continuous_id continuous_const
  intro t ht
  change t=T at ht
  subst t
  simpa only [Function.comp_apply,Pi.sub_apply,id_eq,sub_self,
    projIcc_of_mem hT (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩),
    projIcc_of_mem hS (show (0 : ℝ) ∈ Icc 0 S from ⟨le_rfl,hS⟩)] using hfg

section Derivative

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  (df : Icc (0 : ℝ) T → E) (dg : Icc (0 : ℝ) S → E)
  (hTpos : 0 < T) (hSpos : 0 < S)
  (hfg : f ⟨T,hT,le_rfl⟩=g ⟨0,le_rfl,hS⟩)
  (hdf : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (fun r => f (projIcc 0 T hT r)) (df t) (Icc (0 : ℝ) T) t)
  (hdg : ∀ t : Icc (0 : ℝ) S,
    HasDerivWithinAt (fun r => g (projIcc 0 S hS r)) (dg t) (Icc (0 : ℝ) S) t)
  (hderiv : df ⟨T,hT,le_rfl⟩=dg ⟨0,le_rfl,hS⟩)

include hTpos hSpos hfg hdf hdg hderiv

theorem join_hasDerivAt_seam :
    HasDerivAt (join T S hT hS f g) (df ⟨T,hT,le_rfl⟩) T := by
  have hleft : HasDerivWithinAt (join T S hT hS f g)
      (df ⟨T,hT,le_rfl⟩) (Icc (0 : ℝ) T) T := by
    apply (hdf ⟨T,hT,le_rfl⟩).congr
    · intro r hr
      exact join_left f g hr.2
    · exact join_left f g le_rfl
  have hmap : MapsTo (fun r : ℝ => r-T) (Icc T (T+S)) (Icc (0 : ℝ) S) := by
    intro r hr
    exact ⟨sub_nonneg.mpr hr.1,by linarith only [hr.2]⟩
  have hshift : HasDerivWithinAt (fun r => g (projIcc 0 S hS (r-T)))
      (dg ⟨0,le_rfl,hS⟩) (Icc T (T+S)) T := by
    have hd := (hdg ⟨0,le_rfl,hS⟩).scomp_of_eq T
      ((hasDerivAt_id T).sub_const T).hasDerivWithinAt hmap (by simp)
    simpa only [Function.comp_def,id_eq,one_smul] using hd
  have hright : HasDerivWithinAt (join T S hT hS f g)
      (df ⟨T,hT,le_rfl⟩) (Icc T (T+S)) T := by
    rw [hderiv]
    apply hshift.congr
    · intro r hr
      exact join_right f g hfg hr.1
    · exact join_right f g hfg le_rfl
  have hu := hleft.union hright
  rw [Icc_union_Icc_eq_Icc hT (le_add_of_nonneg_right hS)] at hu
  exact hu.hasDerivAt (Icc_mem_nhds hTpos (lt_add_of_pos_right T hSpos))

theorem join_hasDerivAt (t : ℝ) (ht : t ∈ Ioo 0 (T+S)) :
    HasDerivAt (join T S hT hS f g) (join T S hT hS df dg t) t := by
  rcases lt_trichotomy t T with hlt | heq | hgt
  · have hm : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le,hlt.le⟩
    rw [join_left df dg hlt.le,projIcc_of_mem hT hm]
    apply ((hdf ⟨t,hm⟩).hasDerivAt (Icc_mem_nhds ht.1 hlt)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlt] with r hr
    exact join_left f g hr.le
  · subst t
    rw [join_left df dg le_rfl,projIcc_of_mem hT (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩)]
    exact join_hasDerivAt_seam f g df dg hTpos hSpos hfg hdf hdg hderiv
  · have hm : t-T ∈ Icc (0 : ℝ) S := ⟨sub_nonneg.mpr hgt.le,by linarith only [ht.2]⟩
    have hi : t-T ∈ Ioo (0 : ℝ) S := ⟨sub_pos.mpr hgt,by linarith only [ht.2]⟩
    have hd := ((hdg ⟨t-T,hm⟩).hasDerivAt (Icc_mem_nhds hi.1 hi.2)).scomp t
      ((hasDerivAt_id t).sub_const T)
    have hds : HasDerivAt (fun r => g (projIcc 0 S hS (r-T))) (dg ⟨t-T,hm⟩) t := by
      simpa only [Function.comp_def,id_eq,one_smul] using hd
    have he : join T S hT hS df dg t=dg ⟨t-T,hm⟩ := by
      simp only [join,not_le.mpr hgt,ite_false,projIcc_of_mem hS hm]
    rw [he]
    apply hds.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with r hr
    change T < r at hr
    simp only [join,not_le.mpr hr,ite_false]

end Derivative
end EulerIntervalConcatenation
