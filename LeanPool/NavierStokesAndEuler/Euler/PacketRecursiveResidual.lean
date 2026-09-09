/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveBase

/-! The literal residual of the generated finite packet contains only the uncancelled tail. -/

@[expose] public section


noncomputable section

namespace EulerPacketProfileRecursion

open EulerSmoothLimit EulerPacketPointJets EulerFiniteGrades InnerProductSpace Finset

/-- The generated profiles satisfy the actual closed-interval residual identity
when their two concrete linear solves satisfy their defining equations. -/
theorem recursive_residual_tail (O : Operators) (A : VectorField) (π : ScalarField)
    (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) (hκ : κ ≠ 0) (z : Domain)
    (hs : UniqueDiffWithinAt ℝ O.interval z.1)
    (hA : ∀ i, SliceDifferentiable O.interval (profiles O (primaryProfile O A π) i).high z)
    (hB : ∀ i, SliceDifferentiable O.interval (profiles O (primaryProfile O A π) i).mean z)
    (hC : ∀ i, SliceDifferentiable O.interval (profiles O (primaryProfile O A π) i).corrector z)
    (hq : ∀ i, DifferentiableAt ℝ
      (fun y => (profiles O (primaryProfile O A π) i).meanPressure (z.1, y)) z.2)
    (hπ : ∀ i, DifferentiableAt ℝ
      (fun y => (profiles O (primaryProfile O A π) i).highPressure (z.1, y)) z.2)
    (hqθ : ∀ i ≤ N, fastPressure (O.normal z)
      (pressureJet (profiles O (primaryProfile O A π) i).meanPressure z) = 0)
    (htan : ⟪O.normal z, A z⟫_ℝ = 0)
    (hprimary : linearPart (O.strain z) (slicedJet O.interval A z) +
      fastPressure (O.normal z) (pressureJet π z) = 0)
    (hhigh : ∀ p, 2 ≤ p → p ≤ N →
      ⟪O.normal z, (profiles O (primaryProfile O A π) p).high z⟫_ℝ = 0)
    (hmeanEquation : ∀ p, 2 ≤ p → p ≤ N →
      linearPart (O.strain z) (slicedJet O.interval (profiles O (primaryProfile O A π) p).mean z) +
      slowPressure (O.inverseFrame z) (pressureJet (profiles O (primaryProfile O A π)
          p).meanPressure z) =
        meanForce O p (profiles O (primaryProfile O A π)) z)
    (hhighEquation : ∀ p, 2 ≤ p → p ≤ N →
      linearPart (O.strain z) (slicedJet O.interval (profiles O (primaryProfile O A π) p).high z) +
      fastPressure (O.normal z) (pressureJet (profiles O (primaryProfile O A π) p).highPressure z) =
        highForce O p (profiles O (primaryProfile O A π)) z) :
    slicedMomentumResidual O.interval κ (O.inverseFrame z) (O.strain z) (O.normal z)
      (fieldSum (N+1) κ (assembledVelocity N (profiles O (primaryProfile O A π))))
      (fieldSum (N+1) κ (assembledPressure N (profiles O (primaryProfile O A π)))) z =
      ∑ n ∈ Ico (N+1) (2*N+3), κ^n • recursiveGrade O N (profiles O (primaryProfile O A π)) z n :=
          by
  let a := profiles O (primaryProfile O A π)
  have hv : ∀ i, SliceDifferentiable O.interval (assembledVelocity N a i) z :=
    fun i => sliceDifferentiable_assemble O.interval N i _ _ z
      (fun j _ => (hA j).add (hB j)) (fun j _ => hC j)
  have hp : ∀ i, DifferentiableAt ℝ (fun y => assembledPressure N a i (z.1,y)) z.2 :=
    fun i => spatialDifferentiable_assemble N i _ _ z (fun j _ => hq j) (fun j _ => hπ j)
  have hu0 : slicedJet O.interval (assembledVelocity N a 0) z=0 := by
    rw [slicedJet_assembledVelocity O N a z hA hB hC]
    exact assembledJets_zero O N a (profiles_zero O _) z
  have hp0 : fastPressure (O.normal z) (pressureJet (assembledPressure N a 0) z)=0 := by
    rw [pressureJet_assembledPressure N a z hq hπ, pressureJets_zero N a (profiles_zero O _) z,
      map_zero]
  have hc : ∀ n ≤ N,
      slicedMomentumGrade O.interval (N+1) (O.inverseFrame z) (O.strain z) (O.normal z)
        (assembledVelocity N a) (assembledPressure N a) z n=0 := by
    intro n hn
    rw [recursiveGrade_eq_actual O N a z hA hB hC hq hπ]
    by_cases hn0 : n=0
    · subst n
      exact recursiveGrade_zero O _ N z hqθ
    by_cases hn1 : n=1
    · subst n
      exact recursiveGrade_one O A π N hN z hqθ htan hprimary
    · have hn2 : 2 ≤ n := by omega
      exact recursiveGrade_eq_zero O _ rfl N n hn2 hn z htan (hhigh n hn2 hn) hqθ
        (hmeanEquation n hn2 hn) (hhighEquation n hn2 hn)
  have h := slicedMomentum_fieldSum_tail O.interval N κ hκ (O.inverseFrame z) (O.strain z)
    (O.normal z) (assembledVelocity N a) (assembledPressure N a) z hs
    (fun i _ => (hv i).1) (fun i _ => (hv i).2) (fun i _ => hp i) hu0 hp0 hc
  rw [h]
  apply sum_congr rfl
  intro n _
  rw [recursiveGrade_eq_actual O N a z hA hB hC hq hπ]

end EulerPacketProfileRecursion
