/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceProfiles

@[expose] public section

/-! Literal slice and scalar-pressure regularity of the actually generated source profiles. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

theorem Field.sliceDifferentiable {P T : ℝ} [Fact (0 < P)] {raw raw_t : VectorField}
    (G : Field P T raw) (H : Field P T raw_t) (hT : 0 ≤ T) (hd : TimeDerivative hT G H)
    (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    SliceDifferentiable (Icc (0 : ℝ) T) raw (t,(x,θ)) :=
  ⟨(G.raw_hasDerivWithinAt hT H hd t x θ).differentiableWithinAt,
    (G.raw_smooth t).differentiable (by simp) (x,θ)⟩

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)

include hT in
theorem source_high_slice (p : ℕ) (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    SliceDifferentiable (Icc (0 : ℝ) M.T) (sourceProfiles P M D I Iprimary p).high (t,(x,θ)) := by
  let W := sourceProfileWitness P M D hT I Iprimary p
  exact W.high.sliceDifferentiable W.highDerivative M.T_pos.le W.high_time t x θ

include hT in
theorem source_mean_slice (p : ℕ) (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    SliceDifferentiable (Icc (0 : ℝ) M.T) (sourceProfiles P M D I Iprimary p).mean (t,(x,θ)) := by
  let W := sourceProfileWitness P M D hT I Iprimary p
  exact W.mean.sliceDifferentiable W.meanDerivative M.T_pos.le W.mean_time t x θ

include hT in
theorem source_corrector_slice (p : ℕ) (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    SliceDifferentiable (Icc (0 : ℝ) M.T) (sourceProfiles P M D I Iprimary p).corrector (t,(x,θ))
      := by
  let W := sourceProfileWitness P M D hT I Iprimary p
  exact W.corrector.sliceDifferentiable W.correctorDerivative M.T_pos.le W.corrector_time t x θ

include hT in
theorem source_highPressure_smooth (p : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Space × ℝ => (sourceProfiles P M D I Iprimary p).highPressure (t,y)) := by
  by_cases hp0 : p = 0
  · subst p
    simp only [sourceProfiles,profiles_zero]
    change ContDiff ℝ ∞ (fun _ : Space × ℝ => (0 : ℝ))
    exact contDiff_const
  by_cases hp1 : p = 1
  · subst p
    simpa only [sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile] using
      (homogeneousForcing (P := P) D).scalar_spatial_smooth Iprimary t
  have hp : 2 ≤ p := by omega
  let h : Nonempty (EulerTransversePacketProvider.Forcing P D
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨source_highForcing P M D hT I Iprimary p hp⟩
  unfold sourceProfiles
  rw [profiles_step _ _ p hp]
  change ContDiff ℝ ∞ (fun y : Space × ℝ =>
    (EulerTransversePacketProvider.highSolve P D I
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))).2 (t,y))
  rw [EulerTransversePacketProvider.highSolve_of_admissible D I _ h]
  exact (Classical.choice h).scalar_spatial_smooth I t

include hT in
theorem source_meanPressure_smooth (p : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Space × ℝ => (sourceProfiles P M D I Iprimary p).meanPressure (t,y)) := by
  by_cases hp0 : p = 0
  · subst p
    simp only [sourceProfiles,profiles_zero]
    change ContDiff ℝ ∞ (fun _ : Space × ℝ => (0 : ℝ))
    exact contDiff_const
  by_cases hp1 : p = 1
  · subst p
    simp only [sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile]
    change ContDiff ℝ ∞ (fun _ : Space × ℝ => (0 : ℝ))
    exact contDiff_const
  have hp : 2 ≤ p := by omega
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨source_meanForcing P M D hT I Iprimary p hp⟩
  unfold sourceProfiles
  rw [profiles_step _ _ p hp]
  change ContDiff ℝ ∞ (fun y : Space × ℝ =>
    (EulerMeanPacketProvider.meanSolve M
      (meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))).2 (t,y))
  rw [EulerMeanPacketProvider.meanSolve_of_admissible M _ h]
  exact (Classical.choice h).scalar_spatial_smooth t

include hT in
theorem source_meanPressure_angle (p : ℕ) (t : ℝ) (x : Space) (θ : ℝ) :
    (pressureJet (sourceProfiles P M D I Iprimary p).meanPressure (t,(x,θ))).2 angleDirection = 0
      := by
  by_cases hp0 : p = 0
  · subst p
    simp only [sourceProfiles,profiles_zero]
    change (pressureJet (0 : ScalarField) (t,(x,θ))).2 angleDirection = 0
    rw [pressureJet_zero]
    rfl
  by_cases hp1 : p = 1
  · subst p
    simp only [sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile]
    rw [pressureJet_zero]
    rfl
  have hp : 2 ≤ p := by omega
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨source_meanForcing P M D hT I Iprimary p hp⟩
  unfold sourceProfiles
  rw [profiles_step _ _ p hp]
  change (pressureJet (EulerMeanPacketProvider.meanSolve M
      (meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))).2
        (t,(x,θ))).2 angleDirection = 0
  rw [EulerMeanPacketProvider.meanSolve_of_admissible M _ h]
  exact (Classical.choice h).scalar_angle_jet t x θ

include hT in
theorem source_high_tangent (p : ℕ) (t : ℝ) (x : Space) (θ : ℝ) :
    inner ℝ (D.normalField (t,(x,θ))) ((sourceProfiles P M D I Iprimary p).high (t,(x,θ))) = 0 := by
  by_cases hp0 : p = 0
  · subst p
    simp only [sourceProfiles,profiles_zero]
    exact inner_zero_right _
  by_cases hp1 : p = 1
  · subst p
    simpa only [sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile] using
      (homogeneousForcing (P := P) D).vector_tangent Iprimary t x θ
  have hp : 2 ≤ p := by omega
  let h : Nonempty (EulerTransversePacketProvider.Forcing P D
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨source_highForcing P M D hT I Iprimary p hp⟩
  unfold sourceProfiles
  rw [profiles_step _ _ p hp]
  change inner ℝ (D.normalField (t,(x,θ)))
    ((EulerTransversePacketProvider.highSolve P D I
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))).1 (t,(x,θ))) = 0
  rw [EulerTransversePacketProvider.highSolve_of_admissible D I _ h]
  exact (Classical.choice h).vector_tangent I t x θ

end EulerPacketCylinderField
