/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryAssembly
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometrySourceGrowth

@[expose] public section

/-! The actual constructed geometric stage supplies the physical H3
profile on the forward part of the source interval.  The same scalar
solution also retains the amplification and amplitude conclusions. -/

noncomputable section

namespace EulerPacketSourceGeometry.Guards

open Set InnerProductSpace EulerSmoothLimit EulerTransversePacketProvider
  EulerPacketMovingFrame EulerPacketGeometrySourceGrowth EulerPacketSourcePropagator
  EulerTimeIntervalRestriction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T} {P : ParentFrame D τ}
  {H : HistoryData (D.initial τ hτ hτT.le)} (A : Guards hτ hτT P H)
  (Ω : Set Space) (h0 : 0 ∈ Ω) (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ A.radius)

theorem source_interval :
    (A.geometryData Ω h0 hΩ).S =
      Icc (A.geometryData Ω h0 hΩ).t₀
        ((A.geometryData Ω h0 hΩ).t₀+(D.tail τ hτ.le hτT).T) := by
  change Icc τ D.T=Icc τ (τ+(D.T-τ))
  congr 1
  ring

theorem source_horizon :
    (A.geometryData Ω h0 hΩ).time (A.geometryData Ω h0 hΩ).H =
      (A.geometryData Ω h0 hΩ).t₀+(D.tail τ hτ.le hτT).T := by
  change physicalTime τ P.a P.epsilon (P.a*(D.T-τ)/P.epsilon)=τ+(D.T-τ)
  rw [activation_horizon_exact τ D.T P.a P.epsilon (a_pos hτ hτT P H A).ne'
    (epsilon_pos hτ hτT P H A).ne']
  ring

theorem source_strain (x : {x : Space // x ∈ Ω}) (t : Icc (0 : ℝ) (D.tail τ hτ.le hτT).T) :
    (A.geometryData Ω h0 hΩ).M x ((A.geometryData Ω h0 hΩ).t₀+t) =
      (D.tail τ hτ.le hτT).M.field t x.1 := by
  change D.M.field (D.clamp (τ+(t:ℝ))) x.1 =
    D.M.field (tailInclusion D.T τ hτ.le t) x.1
  have hc : D.clamp (τ+(t:ℝ))=tailInclusion D.T τ hτ.le t :=
    Data.clamp_coe D (tailInclusion D.T τ hτ.le t)
  rw [hc]

theorem source_normal (x : {x : Space // x ∈ Ω}) (t : Icc (0 : ℝ) (D.tail τ hτ.le hτT).T) :
    (A.geometryData Ω h0 hΩ).r x ((A.geometryData Ω h0 hΩ).t₀+t) =
      (D.tail τ hτ.le hτT).normal.field t x.1 := by
  change D.normal.field (D.clamp (τ+(t:ℝ))) x.1 =
    D.normal.field (tailInclusion D.T τ hτ.le t) x.1
  have hc : D.clamp (τ+(t:ℝ))=tailInclusion D.T τ hτ.le t :=
    Data.clamp_coe D (tailInclusion D.T τ hτ.le t)
  rw [hc]

theorem exists_geometry_and_growth :
    ∃ F F₁ Z Z₁ : ℝ → ℝ,
      ∃ J : PhysicalGeometryConclusion (A.geometryData Ω h0 hΩ) F F₁ Z Z₁,
        (∀ t, 0 < growthProfile (D.tail τ hτ.le hτT) (A.geometryData Ω h0 hΩ) J t) ∧
        growthProfile (D.tail τ hτ.le hτT) (A.geometryData Ω h0 hΩ) J
          ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ = 1 ∧
        PhysicalGrowth (D.tail τ hτ.le hτT) Ω
          (growthProfile (D.tail τ hτ.le hτT) (A.geometryData Ω h0 hΩ) J)
          (growthConstant (A.geometryData Ω h0 hΩ)) := by
  obtain ⟨F,F₁,Z,Z₁,J⟩ := (A.geometryData Ω h0 hΩ).exists_geometry
  refine ⟨F,F₁,Z,Z₁,J,?_,?_,?_⟩
  · exact growthProfile_pos (D.tail τ hτ.le hτT) _ J (A.source_horizon Ω h0 hΩ)
  · exact growthProfile_initial (D.tail τ hτ.le hτT) _ J
  · exact physicalGrowth_of_geometry (D.tail τ hτ.le hτT) _ J
      (A.source_interval Ω h0 hΩ) (A.source_horizon Ω h0 hΩ)
      (A.source_strain Ω h0 hΩ) (A.source_normal Ω h0 hΩ)

include A h0 hΩ in
theorem exists_physicalGrowth :
    ∃ g : C(Icc (0 : ℝ) (D.T-τ),ℝ),
      (∀ t, 0 < g t) ∧ g ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩=1 ∧
        PhysicalGrowth (D.tail τ hτ.le hτT) Ω g
          (560*P.horizon^10/P.epsilon) := by
  obtain ⟨F,F₁,Z,Z₁,J,hpos,hzero,hg⟩ := A.exists_geometry_and_growth Ω h0 hΩ
  exact ⟨growthProfile (D.tail τ hτ.le hτT) (A.geometryData Ω h0 hΩ) J,hpos,hzero,hg⟩

theorem halfBall_physicalGrowth (hball : (1/2 : ℝ) ≤ A.radius) :
    ∃ g : C(Icc (0 : ℝ) (D.T-τ),ℝ),
      (∀ t, 0 < g t) ∧ g ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩=1 ∧
        PhysicalGrowth (D.tail τ hτ.le hτT) {x | ‖x‖ ≤ (1/2 : ℝ)} g
          (560*P.horizon^10/P.epsilon) := by
  exact A.exists_physicalGrowth {x | ‖x‖ ≤ (1/2 : ℝ)} (by norm_num)
    (fun _ hx => hx.trans hball)

omit [CompleteSpace U] in
include A in
theorem growth_constant_pos : 0 < 560*P.horizon^10/P.epsilon := by
  have hpos : 0 < P.horizon := zero_lt_one.trans_le A.horizon_lower
  exact div_pos (mul_pos (by norm_num) (pow_pos hpos 10)) (epsilon_pos hτ hτT P H A)

end EulerPacketSourceGeometry.Guards
