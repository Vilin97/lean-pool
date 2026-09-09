/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.IntervalPathConcatenation
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerLifespan

@[expose] public section

/-! Two actual ordinary Euler solutions with matching endpoint data
concatenate to an actual solution. The projected equation identifies
their time derivatives at the seam; the scalar pressure is canonical. -/

noncomputable section

namespace EulerOrdinarySobolev.Evolution

open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSolenoidal EulerIntervalConcatenation
open scoped Topology

variable {T S : ℝ} {hT : 0 ≤ T} {hS : 0 ≤ S}
  (U : Evolution T hT) (V : Evolution S hS)

def joinedVelocity (t : Icc (0 : ℝ) (T+S)) : SmoothL2Field Space :=
  join T S hT hS U.velocity V.velocity t

theorem joinedVelocity_continuous
    (hmatch : U.velocity ⟨T,hT,le_rfl⟩=V.velocity ⟨0,le_rfl,hS⟩) (n : ℕ) :
    Continuous (fun t => (U.joinedVelocity V t).jetLp n) := by
  have hc := join_continuous (hT := hT) (hS := hS)
    (fun t => (U.velocity t).jetLp n) (fun t => (V.velocity t).jetLp n)
    (U.velocity_continuous n) (V.velocity_continuous n)
    (congrArg (fun A : SmoothL2Field Space => A.jetLp n) hmatch)
  have he : (fun t : Icc (0 : ℝ) (T+S) => (U.joinedVelocity V t).jetLp n)=
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
    (hmatch : U.velocity ⟨T,hT,le_rfl⟩=V.velocity ⟨0,le_rfl,hS⟩)
    (t : ℝ) (ht : t ∈ Ioo 0 (T+S)) :
    HasDerivAt (fun r => (U.joinedVelocity V (projIcc 0 (T+S) (add_nonneg hT hS) r)).toLp)
      (projectedRhs (U.joinedVelocity V ⟨t,ht.1.le,ht.2.le⟩)).toLp t := by
  have hd := join_hasDerivAt (fun s => (U.velocity s).toLp) (fun s => (V.velocity s).toLp)
    (fun s => (projectedRhs (U.velocity s)).toLp) (fun s => (projectedRhs (V.velocity s)).toLp)
    hTpos hSpos (congrArg (fun A : SmoothL2Field Space => A.toLp) hmatch)
    (U.velocity_toLp_hasDerivWithinAt_projected hTpos)
    (V.velocity_toLp_hasDerivWithinAt_projected hSpos)
    (congrArg (fun A : SmoothL2Field Space => (projectedRhs A).toLp) hmatch) t ht
  have hb : join T S hT hS (fun s => (projectedRhs (U.velocity s)).toLp)
      (fun s => (projectedRhs (V.velocity s)).toLp) t=
      (projectedRhs (U.joinedVelocity V ⟨t,ht.1.le,ht.2.le⟩)).toLp :=
    (map_join U.velocity V.velocity (fun A : SmoothL2Field Space => (projectedRhs A).toLp) t).symm
  rw [hb] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
  rw [projIcc_of_mem (add_nonneg hT hS) hr]
  exact map_join U.velocity V.velocity (fun A : SmoothL2Field Space => A.toLp) r

theorem joinedVelocity_solenoidal (t : Icc (0 : ℝ) (T+S)) :
    (U.joinedVelocity V t).toLp ∈ solenoidalSpace := by
  unfold joinedVelocity EulerIntervalConcatenation.join
  split
  · exact U.solenoidal _
  · exact V.solenoidal _

def concatenate (hTpos : 0 < T) (hSpos : 0 < S)
    (hmatch : U.velocity ⟨T,hT,le_rfl⟩=V.velocity ⟨0,le_rfl,hS⟩) :
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
    (hmatch : U.velocity ⟨T,hT,le_rfl⟩=V.velocity ⟨0,le_rfl,hS⟩) :
    (U.concatenate V hTpos hSpos hmatch).velocity ⟨0,le_rfl,add_nonneg hT hS⟩=
      U.velocity ⟨0,le_rfl,hT⟩ := by
  change join T S hT hS U.velocity V.velocity 0=U.velocity ⟨0,le_rfl,hT⟩
  rw [join_left U.velocity V.velocity hT,projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from
    ⟨le_rfl,hT⟩)]

theorem concatenate_left (hTpos : 0 < T) (hSpos : 0 < S)
    (hmatch : U.velocity ⟨T,hT,le_rfl⟩=V.velocity ⟨0,le_rfl,hS⟩)
    (t : Icc (0 : ℝ) T) :
    (U.concatenate V hTpos hSpos hmatch).velocity
        ⟨t,t.property.1,t.property.2.trans (le_add_of_nonneg_right hS)⟩=U.velocity t := by
  change join T S hT hS U.velocity V.velocity t=U.velocity t
  rw [join_left U.velocity V.velocity t.property.2,projIcc_of_mem hT t.property]

theorem concatenate_right (hTpos : 0 < T) (hSpos : 0 < S)
    (hmatch : U.velocity ⟨T,hT,le_rfl⟩=V.velocity ⟨0,le_rfl,hS⟩)
    (t : Icc (0 : ℝ) S) :
    (U.concatenate V hTpos hSpos hmatch).velocity
        ⟨T+t,add_nonneg hT t.property.1,add_le_add_right t.property.2 T⟩=V.velocity t := by
  change join T S hT hS U.velocity V.velocity (T+t)=V.velocity t
  rw [join_right U.velocity V.velocity hmatch (le_add_of_nonneg_right t.property.1),
    add_sub_cancel_left,projIcc_of_mem hS t.property]

end EulerOrdinarySobolev.Evolution
