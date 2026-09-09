/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryLowBounds

@[expose] public section

/-! The source growth profile is selected together with its amplitude
bound. Keeping both properties in the choice specification is necessary
for a uniform source-frequency estimate. -/

noncomputable section

namespace EulerPacketGeometrySourceGrowth

open Set EulerSmoothLimit EulerPacketMovingFrame EulerTransversePacketProvider

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U) {Ω : Set Space} (G : PhysicalGeometryData {x : Space // x ∈ Ω})
  {F F₁ Z Z₁ : ℝ → ℝ} (H : PhysicalGeometryConclusion G F F₁ Z Z₁)

theorem growthProfile_amplitude_bound (hhorizon : G.time G.H=G.t₀+D.T)
    (t : Icc (0 : ℝ) D.T) :
    G.amplitude*growthProfile D G H t ≤ 8*Real.exp 6*G.δ*G.hchild/G.s₀ := by
  have ha : 0 < G.a := by linarith only [G.a_lower]
  have htime : D.T=(G.ε/G.a)*G.H := by
    change G.t₀+(G.ε/G.a)*G.H=G.t₀+D.T at hhorizon
    linarith only [hhorizon]
  have htop : (G.a/G.ε)*D.T=G.H := by
    rw [htime]
    field_simp [ha.ne',G.epsilon_pos.ne']
  have hcoef : 0 ≤ G.a/G.ε := (div_pos ha G.epsilon_pos).le
  apply H.amplitude_profile
  constructor
  · exact mul_nonneg hcoef t.property.1
  · exact (mul_le_mul_of_nonneg_left t.property.2 hcoef).trans_eq htop

end EulerPacketGeometrySourceGrowth

namespace EulerPacketGeometryLowBounds

open EulerPacketMovingFrame

theorem amplitude_pos {ι : Type*} (G : PhysicalGeometryData ι)
    (hδ : 0 < G.δ) (hh : 0 < G.hchild) : 0 < G.amplitude := by
  obtain ⟨F,F₁,Z,Z₁,H⟩ := G.exists_geometry
  have hp : 0 < G.amplitude*G.targetSize := by
    rw [H.amplitude_normalization]
    exact mul_pos hδ hh
  exact pos_of_mul_pos_left hp H.target_positive.le

end EulerPacketGeometryLowBounds

namespace EulerPacketSourceGeometry.Guards

open Set EulerSmoothLimit EulerPacketMovingFrame EulerTransversePacketProvider
  EulerPacketGeometrySourceGrowth EulerPacketSourcePropagator

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T} {P : ParentFrame D τ}
  {H : HistoryData (D.initial τ hτ hτT.le)} (A : Guards hτ hτT P H)
  (hball : (1/2 : ℝ) ≤ A.radius)

theorem primaryAmplitude_pos (hδ : 0 < A.δ) (hh : 0 < A.hchild) :
    0 < A.primaryAmplitude hball :=
  EulerPacketGeometryLowBounds.amplitude_pos (A.lowGeometry hball) hδ hh

theorem primaryAmplitude_exponential : A.primaryAmplitude hball ≤
    (4*P.horizon*A.δ*A.hchild/P.rayScale hτ hτT)*Real.exp (-(1/(4*P.sigma))) := by
  obtain ⟨F,F₁,Z,Z₁,J⟩ := (A.lowGeometry hball).exists_geometry
  exact J.amplitude_exponential

theorem halfBall_controlledGrowth :
    ∃ g : C(Icc (0 : ℝ) (D.T-τ),ℝ),
      (∀ t, 0 < g t) ∧ g ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩=1 ∧
        PhysicalGrowth (D.tail τ hτ.le hτT) {x | ‖x‖ ≤ (1/2 : ℝ)} g
          (560*P.horizon^10/P.epsilon) ∧
        ∀ t, A.primaryAmplitude hball*g t ≤
          8*Real.exp 6*A.δ*A.hchild/P.rayScale hτ hτT := by
  obtain ⟨F,F₁,Z,Z₁,J,hpos,hzero,hgrowth⟩ :=
    A.exists_geometry_and_growth {x | ‖x‖ ≤ (1/2 : ℝ)} (by norm_num)
      (fun _ hx => hx.trans hball)
  refine ⟨_,hpos,hzero,hgrowth,?_⟩
  intro t
  exact growthProfile_amplitude_bound (D.tail τ hτ.le hτT) _ J
    (A.source_horizon {x | ‖x‖ ≤ (1/2 : ℝ)} (by norm_num) (fun _ hx => hx.trans hball)) t

end EulerPacketSourceGeometry.Guards

namespace EulerPacketSourceGeometry.ForwardGuards

open Set EulerSmoothLimit EulerPacketMovingFrame EulerTransversePacketProvider
  EulerPacketGeometrySourceGrowth EulerPacketSourcePropagator

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {P : ParentFrame D 0} (A : ForwardGuards P)
  (hball : (1/2 : ℝ) ≤ A.radius)

theorem primaryAmplitude_pos (hδ : 0 < A.δ) (hh : 0 < A.hchild) :
    0 < A.primaryAmplitude hball :=
  EulerPacketGeometryLowBounds.amplitude_pos (A.lowGeometry hball) hδ hh

theorem primaryAmplitude_exponential : A.primaryAmplitude hball ≤
    (4*P.horizon*A.δ*A.hchild)*Real.exp (-(1/(4*P.sigma))) := by
  obtain ⟨F,F₁,Z,Z₁,J⟩ := (A.lowGeometry hball).exists_geometry
  have h := J.amplitude_exponential
  change A.primaryAmplitude hball ≤
    (4*P.horizon*A.δ*A.hchild/(1 : ℝ))*Real.exp (-(1/(4*P.sigma))) at h
  simpa only [div_one] using h

theorem halfBall_controlledGrowth :
    ∃ g : C(Icc (0 : ℝ) D.T,ℝ),
      (∀ t, 0 < g t) ∧ g ⟨0,le_rfl,D.T_pos.le⟩=1 ∧
        PhysicalGrowth D {x | ‖x‖ ≤ (1/2 : ℝ)} g
          (560*P.horizon^10/P.epsilon) ∧
        ∀ t, A.primaryAmplitude hball*g t ≤ 8*Real.exp 6*A.δ*A.hchild := by
  obtain ⟨F,F₁,Z,Z₁,J,hpos,hzero,hgrowth⟩ :=
    A.exists_geometry_and_growth {x | ‖x‖ ≤ (1/2 : ℝ)} (by norm_num)
      (fun _ hx => hx.trans hball)
  refine ⟨_,hpos,hzero,hgrowth,?_⟩
  intro t
  have h := growthProfile_amplitude_bound D _ J
    (A.source_horizon {x | ‖x‖ ≤ (1/2 : ℝ)} (by norm_num) (fun _ hx => hx.trans hball)) t
  change A.primaryAmplitude hball * _ ≤ 8*Real.exp 6*A.δ*A.hchild/(1 : ℝ) at h
  simpa only [div_one] using h

end EulerPacketSourceGeometry.ForwardGuards
