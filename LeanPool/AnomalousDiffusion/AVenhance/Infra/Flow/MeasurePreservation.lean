/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Liouville
public import Mathlib.MeasureTheory.Function.Jacobian

/-! Lebesgue measure is preserved by divergence-free smooth flows. -/

@[expose] public section

open Homogenization
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace AVenhance.Infra.Flow

/-- A divergence-free smooth periodic vector field generates a
measure-preserving spatial flow map at every pair of times. -/
theorem flow_measurePreserving_of_divergence_free
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hdiv : ∀ t x, spatialDivergence b t x = 0)
    (s t : ℝ) : MeasurePreserving (fun x => X t x s) volume volume := by
  let f : Vec 2 → Vec 2 := fun x => X t x s
  let f' : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun x => fderiv ℝ f x
  have hderiv : ∀ x ∈ (Set.univ : Set (Vec 2)),
      HasFDerivWithinAt f (f' x) Set.univ x := by
    intro x hx
    obtain ⟨V, J, hV, hJ, hF⟩ := exists_flow_hasFDerivAt_spatial hb hX x s t
    have hF' : HasFDerivAt f (f' x) x := by
      change HasFDerivAt (fun y => X t y s) (fderiv ℝ f x) x
      rw [hF.fderiv]
      exact hF
    exact hF'.hasFDerivWithinAt
  obtain ⟨_, _, hleft, hright⟩ := flow_fixed_time_maps_are_C1_inverses hb hX s t
  have hinj : Set.InjOn f Set.univ := by
    intro x _ y _ hxy
    calc
      x = X s (X t x s) t := (hleft x).symm
      _ = X s (X t y s) t := congrArg (fun z => X s z t) hxy
      _ = y := hleft y
  have himage : f '' Set.univ = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    exact ⟨X s y t, Set.mem_univ _, hright y⟩
  have hdet : ∀ x, (f' x).det = 1 := by
    intro x
    exact flow_spatial_jacobian_det_eq_one_of_divergence_free hb hX hdiv x s t
  have hdensity : (fun x => ENNReal.ofReal |(f' x).det|) = fun _ => (1 : ℝ≥0∞) := by
    funext x
    rw [hdet x]
    norm_num
  have hchange : Measure.map f
    ((volume.restrict Set.univ).withDensity fun x => ENNReal.ofReal |(f' x).det|) =
        volume.restrict (f '' Set.univ) :=
    MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar volume
      (by simp) hderiv hinj
  rw [hdensity, himage] at hchange
  refine ⟨(flow_spatial_contDiff_one hb hX s t).continuous.measurable, ?_⟩
  · simpa [f] using hchange

end AVenhance.Infra.Flow
