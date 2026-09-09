/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedJets

/-! The pressure entry contains only actual space/angle derivatives used by the PDE. -/

@[expose] public section


noncomputable section

namespace EulerPacketPointJets

open EulerFiniteGrades Finset

/-- The unused time slot is zero: no time derivative of the scalar potential is required. -/
def pressureJet (p : Domain → ℝ) (z : Domain) : ScalarJet :=
  (p z, joinDerivative 0 (fderiv ℝ (fun y => p (z.1,y)) z.2))

theorem pressureJet_space (p : Domain → ℝ) (z : Domain) (v : EulerSmoothLimit.Space) :
    (pressureJet p z).2 (spatialInjection v)=fderiv ℝ (fun y => p (z.1,y)) z.2 (v,0) := by
  simp [pressureJet, joinDerivative, spatialInjection]

theorem pressureJet_angle (p : Domain → ℝ) (z : Domain) :
    (pressureJet p z).2 angleDirection=fderiv ℝ (fun y => p (z.1,y)) z.2 (0,1) := by
  simp [pressureJet, joinDerivative, angleDirection]

theorem pressureJet_fieldSum (M : ℕ) (κ : ℝ) (p : ℕ → Domain → ℝ) (z : Domain)
    (hp : ∀ n ≤ M, DifferentiableAt ℝ (fun y => p n (z.1, y)) z.2) :
    pressureJet (fieldSum M κ p) z=evaluate M κ (fun n => pressureJet (p n) z) := by
  have hspace := HasFDerivAt.fun_sum (u := range (M+1))
    (fun n hn => ((hp n (by have h := mem_range.mp hn; omega)).hasFDerivAt).const_smul (κ^n))
  have hdx : fderiv ℝ (fun y => fieldSum M κ p (z.1,y)) z.2 =
      ∑ n ∈ range (M+1), κ^n • fderiv ℝ (fun y => p n (z.1,y)) z.2 := hspace.fderiv
  apply Prod.ext
  · change (∑ n ∈ range (M+1), κ^n • p n z) =
      (AddMonoidHom.fst ℝ (Domain →L[ℝ] ℝ)) (∑ n ∈ range (M+1), κ^n • pressureJet (p n) z)
    rw [map_sum]
    rfl
  · change joinDerivative 0 _ =
      (AddMonoidHom.snd ℝ (Domain →L[ℝ] ℝ)) (∑ n ∈ range (M+1), κ^n • pressureJet (p n) z)
    rw [hdx, map_sum]
    change joinDerivative 0 (∑ n ∈ range (M+1), κ^n • fderiv ℝ (fun y => p n (z.1,y)) z.2) =
      ∑ n ∈ range (M+1), κ^n • joinDerivative 0 (fderiv ℝ (fun y => p n (z.1,y)) z.2)
    apply ContinuousLinearMap.ext
    intro h
    simp only [joinDerivative_apply, smul_zero, zero_add, _root_.sum_apply, smul_apply]

end EulerPacketPointJets
