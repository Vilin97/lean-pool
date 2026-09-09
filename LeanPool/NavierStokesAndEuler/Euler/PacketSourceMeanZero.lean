/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceProfiles

/-! Exact angular mean and raw corrector identities for the constructed source profiles. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)

include hT in
theorem source_high_mean_zero (p : ℕ) (t : ℝ) (x : Space) :
    (∫ θ in (0 : ℝ)..P, (sourceProfiles P M D I Iprimary p).high (t,(x,θ))) = 0 := by
  by_cases hp0 : p = 0
  · subst p
    simp only [sourceProfiles,profiles_zero]
    change (∫ _ in (0 : ℝ)..P, (0 : Space)) = 0
    exact intervalIntegral.integral_zero
  by_cases hp1 : p = 1
  · subst p
    simpa only [sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile] using
      (homogeneousForcing (P := P) D).vector_mean_zero Iprimary t x
  have hp : 2 ≤ p := by omega
  let h : Nonempty (EulerTransversePacketProvider.Forcing P D
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨sourceHighForcing P M D hT I Iprimary p hp⟩
  have he : sourceProfiles P M D I Iprimary p =
      EulerPacketProfileRecursion.step (sourceOperators P M D I) p (sourceProfiles P M D I
          Iprimary) :=
    profiles_step _ _ p hp
  rw [he]
  change (∫ θ in (0 : ℝ)..P, (EulerTransversePacketProvider.highSolve P D I
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))).1 (t,(x,θ))) = 0
  rw [EulerTransversePacketProvider.highSolve_of_admissible D I _ h]
  exact (Classical.choice h).vector_mean_zero I t x

theorem source_corrector_eq (p : ℕ) (hp : 1 ≤ p) :
    (sourceProfiles P M D I Iprimary p).corrector =
      D.curlCorrector P (sourceProfiles P M D I Iprimary p).high := by
  by_cases hp1 : p = 1
  · subst p
    simp only [sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile]
    rfl
  have hp2 : 2 ≤ p := by omega
  exact profiles_corrector _ _ p hp2

end EulerPacketCylinderField
