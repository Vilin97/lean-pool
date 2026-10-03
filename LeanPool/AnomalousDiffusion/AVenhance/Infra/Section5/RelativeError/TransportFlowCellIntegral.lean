/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.Flow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSmoothFromFixedStart
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.MeasurePreservation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowIdentities
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic

/-! # RelativeError: inverse-flow change of variables on the periodic cell -/

@[expose] public section

noncomputable section

open Homogenization
open MeasureTheory
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Ergodic
open AVenhance.Infra.Torus

/-- The fixed-time flow and its inverse form a smooth periodic
measure-preserving diffeomorphism of the torus. -/
noncomputable def flowPeriodicVolumePreservingDiffeomorphism
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0) (t : ℝ) :
    PeriodicVolumePreservingDiffeomorphism 2 := by
  let L : ℝ := Classical.choose (Infra.Flow.exists_global_spatial_lipschitz hb)
  have hLspec := Classical.choose_spec
    (Infra.Flow.exists_global_spatial_lipschitz hb)
  have hL := hLspec.2
  let hLip : ∀ r x y, ‖b r x - b r y‖ ≤ L * ‖x - y‖ := hL
  have hbper (r : ℝ) : AVenhance.IsZ2Periodic (b r) := by
    intro k x
    simpa using hb.periodic 0 k r x
  have hdiv' (r : ℝ) (x : Vec 2) : Infra.Flow.spatialDivergence b r x = 0 := by
    rw [Infra.Construction.spatialDivergence_eq_vecDiv hb]
    exact hdiv r x
  have hjoint := Infra.Flow.flow_joint_contDiff_infty hb hX
  have hmap : ContDiff ℝ ∞ (fun x : Vec 2 => (t, x, (0 : ℝ))) := by
    fun_prop
  have hforward : ContDiff ℝ ∞ (fun x : Vec 2 => X t x 0) := by
    change ContDiff ℝ ∞ ((fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) ∘
      fun x : Vec 2 => (t, x, (0 : ℝ)))
    exact hjoint.comp hmap
  have hinverseJoint := Infra.Flow.flow_inverse_joint_contDiff_infty hb hX
  have hinverse : ContDiff ℝ ∞ (fun x : Vec 2 => X 0 x t) := by
    change ContDiff ℝ ∞ ((fun p : ℝ × Vec 2 × ℝ => X p.2.2 p.2.1 p.1) ∘
      fun x : Vec 2 => (t, x, (0 : ℝ)))
    exact hinverseJoint.comp hmap
  obtain ⟨_, _, hleft, hright⟩ :=
    Infra.Flow.flow_fixed_time_maps_are_C1_inverses hb hX 0 t
  have hmp : MeasurePreserving (fun x : Vec 2 => X t x 0) volume volume :=
    Infra.Flow.flow_measurePreserving_of_divergence_free hb hX hdiv' 0 t
  refine ⟨fun x => X t x 0, fun x => X 0 x t, hforward, hinverse, ?_, ?_, ?_, hmp⟩
  · intro x
    exact hleft x
  · intro x
    exact hright x
  · intro x k
    change X t (x + AVenhance.latticeShift k) 0 =
      X t x 0 + AVenhance.latticeShift k
    exact Infra.Flow.flow_lattice_equivariant b ⟨L, hL⟩ hbper hX x 0 t k

/-- Inverse transport preserves integrals over one periodic cell. The proof
uses the induced measure-preserving torus diffeomorphism, represented by its
Euclidean lift. -/
theorem integral_unitCell_comp_inverseFlow
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {f : Vec 2 → ℝ} (hf : IsZ2Periodic f) (t : ℝ) :
    (∫ x in unitCell 2, f (X 0 x t)) = ∫ x in unitCell 2, f x := by
  let F := flowPeriodicVolumePreservingDiffeomorphism hb hX hdiv t
  have hInv : F.invFun = fun x => X 0 x t := rfl
  have hf' : IsZPeriodic f := (isZPeriodic_iff_isZ2Periodic f).2 hf
  have hcomp : IsZPeriodic (fun x => f (F.invFun x)) := hf'.comp_invFlow F
  have haverage := cellAverage_comp_flow_eq
    (fun x => f (F.invFun x)) hcomp F
  have hcell : unitCell 2 = unitCellSet 2 := by
    ext x
    simp [unitCell, unitCellAt, unitCellSet]
  have hcancel : (fun x : Vec 2 => f (F.invFun (F.toFun x))) = f := by
    funext x
    exact congrArg f (F.left_inv x)
  calc
    (∫ x in unitCell 2, f (X 0 x t)) =
        cellAverage (fun x => f (F.invFun x)) := by
      rw [cellAverage_eq_unitCellIntegral, ← hcell]
      rw [hInv]
    _ = cellAverage (fun x => f (F.invFun (F.toFun x))) := by
      rw [haverage]
    _ = cellAverage f := by rw [hcancel]
    _ = ∫ x in unitCell 2, f x := by
      rw [cellAverage_eq_unitCellIntegral, ← hcell]

end AVenhance.Infra.Section5.RelativeError

end
