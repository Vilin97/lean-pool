/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialC3
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FlowOn

/-! The first spatial jet of a smooth flow is itself a characterized flow on
the product of position and two direction columns. -/

@[expose] public section

open Homogenization
open Filter
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- The augmented vector field for position and a pair of spatial directions. -/
def firstJetField (b : ℝ → Vec 2 → Vec 2) :
    ℝ → (Vec 2 × (Fin 2 → Vec 2)) → (Vec 2 × (Fin 2 → Vec 2)) :=
  fun t z =>
    (b t z.1, fun i => jointSpatialFDeriv b t z.1 (z.2 i))

/-- The first-jet vector field is smooth on its full product state space. -/
theorem firstJetField_contDiff
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ContDiff ℝ ∞ (Function.uncurry (firstJetField b)) := by
  let D : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 :=
    fun p => jointSpatialFDeriv b p.1 p.2
  have hDbase : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => fderiv ℝ
      (Function.uncurry b) p) := hb.smooth.fderiv_right (by norm_num)
  have hD : ContDiff ℝ ∞ D := by
    have hcomp : ContDiff ℝ ∞
        (fun p : ℝ × Vec 2 => (fderiv ℝ (Function.uncurry b) p).comp
          (ContinuousLinearMap.inr ℝ ℝ (Vec 2))) :=
      hDbase.clm_comp contDiff_const
    simpa [D, jointSpatialFDeriv] using hcomp
  have hstate : ContDiff ℝ ∞
      (fun q : ℝ × (Vec 2 × (Fin 2 → Vec 2)) => (q.1, q.2.1)) := by
    fun_prop
  have hDstate : ContDiff ℝ ∞
      (fun q : ℝ × (Vec 2 × (Fin 2 → Vec 2)) => D (q.1, q.2.1)) := hD.comp hstate
  have hbase : ContDiff ℝ ∞
      (fun q : ℝ × (Vec 2 × (Fin 2 → Vec 2)) => b q.1 q.2.1) := by
    have hmap : ContDiff ℝ ∞
        (fun q : ℝ × (Vec 2 × (Fin 2 → Vec 2)) => (q.1, q.2.1)) := hstate
    exact hb.smooth.comp hmap
  have hcol (i : Fin 2) : ContDiff ℝ ∞
      (fun q : ℝ × (Vec 2 × (Fin 2 → Vec 2)) => D (q.1, q.2.1) (q.2.2 i)) := by
    have hdir : ContDiff ℝ ∞
        (fun q : ℝ × (Vec 2 × (Fin 2 → Vec 2)) => q.2.2 i) := by fun_prop
    exact hDstate.clm_apply hdir
  have hcols : ContDiff ℝ ∞
      (fun q : ℝ × (Vec 2 × (Fin 2 → Vec 2)) =>
        fun i => D (q.1, q.2.1) (q.2.2 i)) := contDiff_pi.2 hcol
  have hpair := hbase.prodMk hcols
  convert hpair using 1
  funext q
  rfl

/-- The augmented flow: its direction columns are the spatial derivative of
the original flow applied to the supplied initial columns. -/
def firstJetFlow (X : ℝ → Vec 2 → ℝ → Vec 2) :
    ℝ → (Vec 2 × (Fin 2 → Vec 2)) → ℝ → (Vec 2 × (Fin 2 → Vec 2)) :=
  fun t z s =>
    (X t z.1 s,
      fun i => fderiv ℝ (fun y => X t y s) z.1 (z.2 i))

/-- The position and first spatial jet satisfy their augmented ODE exactly. -/
theorem firstJetFlow_isFlow
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    IsFlowOn (firstJetField b) (firstJetFlow X) := by
  constructor
  · intro z s
    ext i <;> simp [firstJetFlow, hX.1]
  · intro z s t
    let V : ℝ → Vec 2 → ℝ → Vec 2 :=
      Classical.choose (existsUnique_flow_variationalEquation hb hX z.1 s)
    have hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X z.1 s) V :=
      (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX z.1 s)).1
    have hVuniq : ∀ W, AVenhance.IsFlow
        (linearizedFieldAlongFlow b X z.1 s) W → W = V :=
      (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX z.1 s)).2
    have hcolumn (r : ℝ) (v : Vec 2) :
        fderiv ℝ (fun y => X r y s) z.1 v = V r v s := by
      obtain ⟨W, J, hW, hJ, hD⟩ :=
        exists_flow_hasFDerivAt_spatial hb hX z.1 s r
      have hW_eq : W = V := hVuniq W hW
      calc
        fderiv ℝ (fun y => X r y s) z.1 v = J v := by rw [hD.fderiv]
        _ = W r v s := hJ v
        _ = V r v s := by rw [hW_eq]
    have hcols (i : Fin 2) :
        HasDerivAt
          (fun r => (firstJetFlow X r z s).2 i)
          (jointSpatialFDeriv b t (X t z.1 s)
            ((firstJetFlow X t z s).2 i)) t := by
      have h := hV.2 (z.2 i) s t
      have hEq : (fun r => (firstJetFlow X r z s).2 i) =
          fun r => V r (z.2 i) s := by
        funext r
        exact hcolumn r (z.2 i)
      rw [hEq]
      simpa [firstJetFlow, firstJetField, linearizedFieldAlongFlow,
        hcolumn t (z.2 i)] using h
    have hcols' : HasDerivAt
        (fun r => (firstJetFlow X r z s).2)
        (fun i => jointSpatialFDeriv b t (X t z.1 s)
          ((firstJetFlow X t z s).2 i)) t :=
      hasDerivAt_pi.mpr hcols
    have hbase := hX.2 z.1 s t
    simpa [firstJetFlow, firstJetField] using hbase.prodMk hcols'

/-- The augmented first-jet maps obey the same composition law as the
underlying flow. -/
theorem firstJetFlow_group_law
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (z : Vec 2 × (Fin 2 → Vec 2)) (s r t : ℝ) :
    firstJetFlow X t (firstJetFlow X r z s) r = firstJetFlow X t z s := by
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  have hcomp : (fderiv ℝ (fun y => X t y r) (X r z.1 s)).comp
      (fderiv ℝ (fun y => X r y s) z.1) =
      fderiv ℝ (fun y => X t y s) z.1 := by
    have hF : DifferentiableAt ℝ (fun y => X t y r) (X r z.1 s) :=
      (flow_spatial_contDiff_one hb hX r t).differentiable (by norm_num) _
    have hG : DifferentiableAt ℝ (fun y => X r y s) z.1 :=
      (flow_spatial_contDiff_one hb hX s r).differentiable (by norm_num) _
    have hchain :
        fderiv ℝ (fun y => X t (X r y s) r) z.1 =
          (fderiv ℝ (fun y => X t y r) (X r z.1 s)).comp
            (fderiv ℝ (fun y => X r y s) z.1) :=
      (HasFDerivAt.comp (f := fun y => X r y s) (x := z.1)
        hF.hasFDerivAt hG.hasFDerivAt).fderiv
    have hmap : (fun y => X t (X r y s) r) = fun y => X t y s := by
      funext y
      exact flow_group_law b ⟨L, hL⟩ hX y s r t
    simpa only [hmap] using hchain.symm
  apply Prod.ext
  · exact flow_group_law b ⟨L, hL⟩ hX z.1 s r t
  · funext i
    change (fderiv ℝ (fun y => X t y r) (X r z.1 s))
        ((fderiv ℝ (fun y => X r y s) z.1) (z.2 i)) =
      (fderiv ℝ (fun y => X t y s) z.1) (z.2 i)
    exact congrArg (fun A : Vec 2 →L[ℝ] Vec 2 => A (z.2 i)) hcomp

/-- For each pair of times, the augmented first-jet map is continuously
differentiable in its initial position and direction columns. -/
theorem firstJetFlow_spatial_contDiff_one
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (t s : ℝ) :
    ContDiff ℝ 1 (fun z : Vec 2 × (Fin 2 → Vec 2) => firstJetFlow X t z s) := by
  let f : Vec 2 → Vec 2 := fun x => X t x s
  let J : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun x => fderiv ℝ f x
  have hf : ContDiff ℝ 2 f := flow_spatial_contDiff_two hb hX s t
  have hJ : ContDiff ℝ 1 J := hf.fderiv_right (by norm_num)
  have hbase : ContDiff ℝ 1 (fun z : Vec 2 × (Fin 2 → Vec 2) => f z.1) :=
    hf.of_le (by norm_num) |>.comp contDiff_fst
  have hJfst : ContDiff ℝ 1
      (fun z : Vec 2 × (Fin 2 → Vec 2) => J z.1) := hJ.comp contDiff_fst
  have hcol (i : Fin 2) : ContDiff ℝ 1
      (fun z : Vec 2 × (Fin 2 → Vec 2) => J z.1 (z.2 i)) := by
    have hcoord : ContDiff ℝ 1
        (fun z : Vec 2 × (Fin 2 → Vec 2) => z.2 i) := by fun_prop
    exact hJfst.clm_apply hcoord
  have hcols : ContDiff ℝ 1
      (fun z : Vec 2 × (Fin 2 → Vec 2) => fun i => J z.1 (z.2 i)) :=
    contDiff_pi.2 hcol
  have hpair := hbase.prodMk hcols
  convert hpair using 1
  funext z
  rfl

end

end AVenhance.Infra.Flow
