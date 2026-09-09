/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveCancellation

@[expose] public section

/-! The initial profile and the zero/first grades of the actual recursive packet. -/

noncomputable section

namespace EulerPacketProfileRecursion

open EulerSmoothLimit EulerPacketPointJets EulerFiniteGrades EulerPacketResidual InnerProductSpace
  Finset

def primaryProfile (O : Operators) (A : VectorField) (π : ScalarField) : Profile :=
  ⟨A,0,O.curlCorrector A,π,0⟩

theorem assembledJets_zero (O : Operators) (N : ℕ) (a : ℕ → Profile) (ha : a 0=0) (z : Domain) :
    assembledJets O N a z 0=0 := by
  unfold assembledJets
  apply assemble_zero
  rw [ha]
  simp [EulerPacketPointJets.slicedJet_zero']

theorem pressureJets_zero (N : ℕ) (a : ℕ → Profile) (ha : a 0=0) (z : Domain) :
    pressureJets N a z 0=0 := by
  unfold pressureJets
  apply assemble_zero
  rw [ha]
  simp [pressureJet_zero]

theorem recursiveGrade_zero (O : Operators) (primary : Profile) (N : ℕ) (z : Domain)
    (hqθ : ∀ i ≤ N, fastPressure (O.normal z) (pressureJet (profiles O primary i).meanPressure
      z)=0) :
    recursiveGrade O N (profiles O primary) z 0=0 := by
  have hv := assembledJets_zero O N (profiles O primary) (profiles_zero O primary) z
  have hq := pressureJets_zero N (profiles O primary) (profiles_zero O primary) z
  have hp : fastPressure (O.normal z) (pressureJets N (profiles O primary) z 1)=0 := by
    unfold pressureJets
    rw [assembled_fast_pressure N 0 (Nat.zero_le N) _ _ _ hqθ]
    simp [pressureJet_zero]
  exact coefficient_zero_grade N _ _ _ _ _ _ _ hv (by rw [hq, map_zero]) hp

theorem nonlinearGrade_one (M : ℕ) (hM : 2 ≤ M) (FInv : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → VectorJet) (hu0 : u 0=0) (htan : ⟪m,(u 1).1⟫_ℝ=0) :
    nonlinearGrade M 1 FInv m u=0 := by
  unfold nonlinearGrade
  rw [convolution_eq_range M 1 (by omega), convolution_eq_range M 2 hM]
  have hfast := fastAdvection_tangent_left m (u 1) (u 1) htan
  simp [sum_range_succ, hu0, hfast, map_zero, LinearMap.zero_apply]

theorem recursiveGrade_one (O : Operators) (A : VectorField) (π : ScalarField)
    (N : ℕ) (hN : 1 ≤ N) (z : Domain)
    (hqθ : ∀ i ≤ N, fastPressure (O.normal z)
      (pressureJet (profiles O (primaryProfile O A π) i).meanPressure z)=0)
    (htan : ⟪O.normal z,A z⟫_ℝ=0)
    (hlinear : linearPart (O.strain z) (slicedJet O.interval A z)+
      fastPressure (O.normal z) (pressureJet π z)=0) :
    recursiveGrade O N (profiles O (primaryProfile O A π)) z 1=0 := by
  let a := profiles O (primaryProfile O A π)
  have ha : a 0=0 := profiles_zero O _
  have hmean : (a 1).mean=0 := by simp [a, primaryProfile]
  have hu1 : assembledJets O N a z 1=slicedJet O.interval A z := by
    rw [assembledJets_eq_velocityJet O N a ha z 1 hN, velocityJet_primary O a ha hmean z]
    simp [a, primaryProfile]
  have hnl : nonlinearGrade (N+1) 1 (O.inverseFrame z) (O.normal z) (assembledJets O N a z)=0 :=
    nonlinearGrade_one (N+1) (by omega) _ _ _ (assembledJets_zero O N a ha z)
      (by rw [hu1]; exact htan)
  have he : recursiveGrade O N a z 1=
      (linearPart (O.strain z) (slicedJet O.interval (a 1).high z)+
        fastPressure (O.normal z) (pressureJet (a 1).highPressure z))+
      (linearPart (O.strain z) (slicedJet O.interval (a 1).mean z)+
        slowPressure (O.inverseFrame z) (pressureJet (a 1).meanPressure z))+
      (linearPart (O.strain z) (slicedJet O.interval (a 0).corrector z)+
        slowPressure (O.inverseFrame z) (pressureJet (a 0).highPressure z))+
      nonlinearGrade (N+1) 1 (O.inverseFrame z) (O.normal z) (assembledJets O N a z) := by
    unfold recursiveGrade assembledJets pressureJets
    have h := coefficient_assembled N 1 le_rfl hN (linearPart (O.strain z))
      (slowPressure (O.inverseFrame z)) (fastPressure (O.normal z))
      (slowAdvection (O.inverseFrame z)) (fastAdvection (O.normal z))
      (fun i => slicedJet O.interval (a i).high z) (fun i => slicedJet O.interval (a i).mean z)
      (fun i => slicedJet O.interval (a i).corrector z) (fun i => pressureJet (a i).meanPressure z)
      (fun i => pressureJet (a i).highPressure z) hqθ
    simpa only [Nat.sub_self, nonlinearGrade, add_assoc] using h
  change recursiveGrade O N a z 1=0
  rw [he, hnl]
  simpa only [a, profiles_one, profiles_zero, primaryProfile, zero_corrector, zero_highPressure,
    EulerPacketPointJets.slicedJet_zero', pressureJet_zero, map_zero, add_zero, zero_add] using
      hlinear

end EulerPacketProfileRecursion
