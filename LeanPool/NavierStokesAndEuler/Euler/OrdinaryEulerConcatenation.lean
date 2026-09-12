/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryHelmholtzField
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryStrongTime
import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Two actual ordinary Euler solutions with matching endpoint data
concatenate to an actual solution. The projected equation identifies
their time derivatives at the seam; the scalar pressure is canonical. -/

section

/-! Concatenation of two paths on closed time intervals. Matching
endpoint values and derivatives give a genuine derivative at the seam. -/

@[expose] public section

noncomputable section

namespace EulerIntervalConcatenation

open Set Filter
open scoped Topology

/-- Join, with branches according to `t ≤ T`. -/
def join {E : Type*} (T S : ℝ) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (f : Icc (0 : ℝ) T → E) (g : Icc (0 : ℝ) S → E) (t : ℝ) : E :=
  if t ≤ T then f (projIcc 0 T hT t) else g (projIcc 0 S hS (t-T))

variable {E : Type*} {T S : ℝ} {hT : 0 ≤ T} {hS : 0 ≤ S}
  (f : Icc (0 : ℝ) T → E) (g : Icc (0 : ℝ) S → E)

theorem join_left {t : ℝ} (ht : t ≤ T) :
    join T S hT hS f g t=f (projIcc 0 T hT t) := by simp only [join,ht,ite_true]

theorem join_right (hfg : f ⟨T, hT, le_rfl⟩ = g ⟨0, le_rfl, hS⟩) {t : ℝ} (ht : T ≤ t) :
    join T S hT hS f g t=g (projIcc 0 S hS (t-T)) := by
  by_cases h : t ≤ T
  · have he : t=T := le_antisymm h ht
    subst t
    simpa only [join,le_refl,ite_true,sub_self,
      projIcc_of_mem hT (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩),
      projIcc_of_mem hS (show (0 : ℝ) ∈ Icc 0 S from ⟨le_rfl,hS⟩)] using hfg
  · simp only [join,h,ite_false]

theorem map_join {F : Type*} (A : E → F) (t : ℝ) :
    A (join T S hT hS f g t) =
      join T S hT hS (fun s => A (f s)) (fun s => A (g s)) t := by
  unfold join
  split <;> rfl

theorem join_continuous [TopologicalSpace E] (hf : Continuous f) (hg : Continuous g)
    (hfg : f ⟨T, hT, le_rfl⟩ = g ⟨0, le_rfl, hS⟩) :
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
  (hfg : f ⟨T, hT, le_rfl⟩ = g ⟨0, le_rfl, hS⟩)
  (hdf : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (fun r => f (projIcc 0 T hT r)) (df t) (Icc (0 : ℝ) T) t)
  (hdg : ∀ t : Icc (0 : ℝ) S,
    HasDerivWithinAt (fun r => g (projIcc 0 S hS r)) (dg t) (Icc (0 : ℝ) S) t)
  (hderiv : df ⟨T, hT, le_rfl⟩ = dg ⟨0, le_rfl, hS⟩)

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

theorem join_hasDerivAt (t : ℝ) (ht : t ∈ Ioo 0 (T + S)) :
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev.Evolution

open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSolenoidal EulerIntervalConcatenation
open scoped Topology

variable {T S : ℝ} {hT : 0 ≤ T} {hS : 0 ≤ S}
  (U : Evolution T hT) (V : Evolution S hS)

/-- Joined velocity, given by `join T S hT hS U.velocity V.velocity t`. -/
def joinedVelocity (t : Icc (0 : ℝ) (T + S)) : SmoothL2Field Space :=
  join T S hT hS U.velocity V.velocity t

theorem joinedVelocity_continuous
    (hmatch : U.velocity ⟨T, hT, le_rfl⟩ = V.velocity ⟨0, le_rfl, hS⟩) (n : ℕ) :
    Continuous (fun t => (U.joinedVelocity V t).jetLp n) := by
  have hc := join_continuous (hT := hT) (hS := hS)
    (fun t => (U.velocity t).jetLp n) (fun t => (V.velocity t).jetLp n)
    (U.velocity_continuous n) (V.velocity_continuous n)
    (congrArg (fun A : SmoothL2Field Space => A.jetLp n) hmatch)
  have he : (fun t : Icc (0 : ℝ) (T+S) => (U.joinedVelocity V t).jetLp n) =
      fun t : Icc (0 : ℝ) (T+S) =>
        join T S hT hS (fun s => (U.velocity s).jetLp n) (fun s => (V.velocity s).jetLp n) t := by
    funext t
    exact map_join U.velocity V.velocity (fun A : SmoothL2Field Space => A.jetLp n) t
  rw [he]
  exact hc.comp continuous_subtype_val

theorem velocity_toLp_hasDerivWithinAt_projected (hpos : 0 < T) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r => (U.velocity (projIcc 0 T hT r)).toLp)
      (projectedRhs (U.velocity t)).toLp (Icc (0 : ℝ) T) t := by
  rw [← U.derivative_toLp_projected hpos t]
  have h := U.velocityPath_hasDerivWithinAt t
  rw [U.velocityPath_extend] at h
  exact h

theorem joinedVelocity_derivative (hTpos : 0 < T) (hSpos : 0 < S)
    (hmatch : U.velocity ⟨T, hT, le_rfl⟩ = V.velocity ⟨0, le_rfl, hS⟩)
    (t : ℝ) (ht : t ∈ Ioo 0 (T + S)) :
    HasDerivAt (fun r => (U.joinedVelocity V (projIcc 0 (T+S) (add_nonneg hT hS) r)).toLp)
      (projectedRhs (U.joinedVelocity V ⟨t,ht.1.le,ht.2.le⟩)).toLp t := by
  have hd := join_hasDerivAt (fun s => (U.velocity s).toLp) (fun s => (V.velocity s).toLp)
    (fun s => (projectedRhs (U.velocity s)).toLp) (fun s => (projectedRhs (V.velocity s)).toLp)
    hTpos hSpos (congrArg (fun A : SmoothL2Field Space => A.toLp) hmatch)
    (U.velocity_toLp_hasDerivWithinAt_projected hTpos)
    (V.velocity_toLp_hasDerivWithinAt_projected hSpos)
    (congrArg (fun A : SmoothL2Field Space => (projectedRhs A).toLp) hmatch) t ht
  have hb : join T S hT hS (fun s => (projectedRhs (U.velocity s)).toLp)
      (fun s => (projectedRhs (V.velocity s)).toLp) t =
      (projectedRhs (U.joinedVelocity V ⟨t,ht.1.le,ht.2.le⟩)).toLp :=
    (map_join U.velocity V.velocity (fun A : SmoothL2Field Space => (projectedRhs A).toLp) t).symm
  rw [hb] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
  rw [projIcc_of_mem (add_nonneg hT hS) hr]
  exact map_join U.velocity V.velocity (fun A : SmoothL2Field Space => A.toLp) r

theorem joinedVelocity_solenoidal (t : Icc (0 : ℝ) (T + S)) :
    (U.joinedVelocity V t).toLp ∈ solenoidalSpace := by
  unfold joinedVelocity EulerIntervalConcatenation.join
  split
  · exact U.solenoidal _
  · exact V.solenoidal _

/-- Concatenate, bundling `velocity`, `pressureForce`, `velocity_continuous`,
`pressure_continuous` and the required compatibility proofs. -/
def concatenate (hTpos : 0 < T) (hSpos : 0 < S)
    (hmatch : U.velocity ⟨T, hT, le_rfl⟩ = V.velocity ⟨0, le_rfl, hS⟩) :
    Evolution (T+S) (add_nonneg hT hS) where
  velocity := U.joinedVelocity V
  pressureForce t := pressureField (U.joinedVelocity V t)
  velocity_continuous := U.joinedVelocity_continuous V hmatch
  pressure_continuous := pressureField_continuous (U.joinedVelocity V)
    (U.joinedVelocity_continuous V hmatch)
  solenoidal := U.joinedVelocity_solenoidal V
  gradient t := pressureField_mem_gradient (U.joinedVelocity V t)
  time_law t ht x := by
    have hd := pointwise_derivative_of_l2 (T+S) (add_nonneg hT hS)
      (U.joinedVelocity V) (fun s => projectedRhs (U.joinedVelocity V s))
      (U.joinedVelocity_continuous V hmatch)
      (projectedRhs_continuous (U.joinedVelocity V) (U.joinedVelocity_continuous V hmatch))
      (U.joinedVelocity_derivative V hTpos hSpos hmatch) ⟨t,ht.1.le,ht.2.le⟩ x
    simpa only [projectedRhs_field] using hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem concatenate_initial (hTpos : 0 < T) (hSpos : 0 < S)
    (hmatch : U.velocity ⟨T, hT, le_rfl⟩ = V.velocity ⟨0, le_rfl, hS⟩) :
    (U.concatenate V hTpos hSpos hmatch).velocity ⟨0,le_rfl,add_nonneg hT hS⟩=
      U.velocity ⟨0,le_rfl,hT⟩ := by
  change join T S hT hS U.velocity V.velocity 0=U.velocity ⟨0,le_rfl,hT⟩
  rw [join_left U.velocity V.velocity hT,projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from
      ⟨le_rfl,hT⟩)]

theorem concatenate_left (hTpos : 0 < T) (hSpos : 0 < S)
    (hmatch : U.velocity ⟨T, hT, le_rfl⟩ = V.velocity ⟨0, le_rfl, hS⟩)
    (t : Icc (0 : ℝ) T) :
    (U.concatenate V hTpos hSpos hmatch).velocity
        ⟨t,t.property.1,t.property.2.trans (le_add_of_nonneg_right hS)⟩=U.velocity t := by
  change join T S hT hS U.velocity V.velocity t=U.velocity t
  rw [join_left U.velocity V.velocity t.property.2,projIcc_of_mem hT t.property]

theorem concatenate_right (hTpos : 0 < T) (hSpos : 0 < S)
    (hmatch : U.velocity ⟨T, hT, le_rfl⟩ = V.velocity ⟨0, le_rfl, hS⟩)
    (t : Icc (0 : ℝ) S) :
    (U.concatenate V hTpos hSpos hmatch).velocity
        ⟨T+t,add_nonneg hT t.property.1,add_le_add_right t.property.2 T⟩=V.velocity t := by
  change join T S hT hS U.velocity V.velocity (T+t)=V.velocity t
  rw [join_right U.velocity V.velocity hmatch (le_add_of_nonneg_right t.property.1),
    add_sub_cancel_left,projIcc_of_mem hS t.property]

end EulerOrdinarySobolev.Evolution
