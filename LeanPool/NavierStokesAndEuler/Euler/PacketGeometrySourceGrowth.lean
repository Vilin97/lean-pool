/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryAssembly
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePropagator

@[expose] public section

/-! The physical geometry theorem supplies the actual weighted-growth
input used by the source packet budgets.  The only bridge hypotheses are
literal interval, strain, and normal identities. -/

noncomputable section

namespace EulerPacketGeometrySourceGrowth

open Set InnerProductSpace EulerSmoothLimit EulerPacketMovingFrame
  EulerPacketMovingFrame.PhysicalGeometryData EulerPacketSourcePropagator
  EulerTransversePacketProvider

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U) {Ω : Set Space} (G : PhysicalGeometryData {x : Space // x ∈ Ω})
  {F F₁ Z Z₁ : ℝ → ℝ} (H : PhysicalGeometryConclusion G F F₁ Z Z₁)

def growthProfile : C(Icc (0 : ℝ) D.T,ℝ) where
  toFun t := Z ((G.a/G.ε)*t)
  continuous_toFun := (continuous_iff_continuousAt.mpr
    (fun t => (H.Z_derivative t).continuousAt)).comp
      (continuous_const.mul continuous_subtype_val)

theorem growthProfile_eq_physical (t : Icc (0 : ℝ) D.T) :
    growthProfile D G H t = physicalProfile Z G.t₀ G.a G.ε (G.t₀+t) := by
  simp only [growthProfile,ContinuousMap.coe_mk,physicalProfile,scaledTime,add_sub_cancel_left]

theorem growthProfile_initial :
    growthProfile D G H ⟨0,le_rfl,D.T_pos.le⟩=1 := by
  simpa only [growthProfile,ContinuousMap.coe_mk,mul_zero] using H.initial_values.2.2.1

theorem growthProfile_pos (hhorizon : G.time G.H=G.t₀+D.T)
    (t : Icc (0 : ℝ) D.T) : 0 < growthProfile D G H t := by
  rw [growthProfile_eq_physical]
  apply H.physical_profile_positive
  rw [hhorizon]
  exact ⟨by linarith [t.property.1],by linarith [t.property.2]⟩

def growthConstant : ℝ := 560*G.Θ^10/G.ε

theorem growthConstant_pos : 0 < growthConstant G := by
  unfold growthConstant
  positivity [G.Theta_pos,G.epsilon_pos]

theorem physicalGrowth_of_geometry
    (hinterval : G.S=Icc G.t₀ (G.t₀+D.T))
    (hhorizon : G.time G.H=G.t₀+D.T)
    (hstrain : ∀ (x : {x : Space // x ∈ Ω}) (t : Icc (0 : ℝ) D.T),
      G.M x (G.t₀+t)=D.M.field t x.1)
    (hnormal : ∀ (x : {x : Space // x ∈ Ω}) (t : Icc (0 : ℝ) D.T),
      G.r x (G.t₀+t)=D.normal.field t x.1) :
    PhysicalGrowth D Ω (growthProfile D G H) (growthConstant G) := by
  intro x hx w hw hw0 t s hst
  let ξ : {x : Space // x ∈ Ω} := ⟨x,hx⟩
  let u : ℝ → Space := fun r => w (r-G.t₀)
  have hmap : MapsTo (fun r => r-G.t₀) G.S (Icc (0 : ℝ) D.T) := by
    intro r hr
    rw [hinterval] at hr
    exact ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hu : ∀ r ∈ G.S, HasDerivWithinAt u
      (-(G.M ξ r) (u r)+(2*⟪G.r ξ r,(G.M ξ r) (u r)⟫_ℝ/‖G.r ξ r‖^2) • G.r ξ r) G.S r := by
    intro r hr
    let sr : Icc (0 : ℝ) D.T := ⟨r-G.t₀,hmap hr⟩
    have he : G.t₀+(sr : ℝ)=r := by dsimp only [sr]; ring
    have hM : G.M ξ r=D.M.field sr x := by rw [← he]; exact hstrain ξ sr
    have hm : G.r ξ r=D.normal.field sr x := by rw [← he]; exact hnormal ξ sr
    rw [hM,hm]
    have hd := (hw sr).scomp r ((hasDerivAt_id r).sub_const G.t₀).hasDerivWithinAt hmap
    simpa only [one_smul,Function.comp_def,id_eq,physicalRhs,u,sr] using hd
  have htan : ⟪G.r ξ G.t₀,u G.t₀⟫_ℝ=0 := by
    have hm := hnormal ξ ⟨0,le_rfl,D.T_pos.le⟩
    simp only [add_zero] at hm
    rw [hm]
    simpa only [u,sub_self] using hw0
  have hmem (r : Icc (0 : ℝ) D.T) : G.t₀+r ∈ Icc G.t₀ (G.time G.H) := by
    rw [hhorizon]
    exact ⟨by linarith [r.property.1],by linarith [r.property.2]⟩
  have hb := H.tangent_propagator ξ u hu htan (G.t₀+s) (G.t₀+t) (hmem s) (hmem t)
    (add_le_add le_rfl (show (s : ℝ) ≤ t from hst))
  rw [← growthProfile_eq_physical D G H t,← growthProfile_eq_physical D G H s] at hb
  calc
    ‖w t‖ ≤ growthConstant G*(growthProfile D G H t/growthProfile D G H s)*‖w s‖ := by
      simpa only [growthConstant,u,add_sub_cancel_left] using hb
    _ = growthConstant G*growthProfile D G H t/growthProfile D G H s*‖w s‖ := by ring

/-- The profile and its physical growth property are derived together
from the actual geometry stage. They are ready for the source-budget constructors. -/
theorem exists_growth_of_geometry
    (hinterval : G.S=Icc G.t₀ (G.t₀+D.T))
    (hhorizon : G.time G.H=G.t₀+D.T)
    (hstrain : ∀ (x : {x : Space // x ∈ Ω}) (t : Icc (0 : ℝ) D.T),
      G.M x (G.t₀+t)=D.M.field t x.1)
    (hnormal : ∀ (x : {x : Space // x ∈ Ω}) (t : Icc (0 : ℝ) D.T),
      G.r x (G.t₀+t)=D.normal.field t x.1) :
    ∃ (g : C(Icc (0 : ℝ) D.T,ℝ)) (C : ℝ),
      (∀ t, 0 < g t) ∧ g ⟨0,le_rfl,D.T_pos.le⟩=1 ∧ 0 < C ∧ PhysicalGrowth D Ω g C := by
  obtain ⟨F,F₁,Z,Z₁,H⟩ := G.exists_geometry
  exact ⟨growthProfile D G H,growthConstant G,growthProfile_pos D G H hhorizon,
    growthProfile_initial D G H,growthConstant_pos G,
    physicalGrowth_of_geometry D G H hinterval hhorizon hstrain hnormal⟩

end EulerPacketGeometrySourceGrowth
