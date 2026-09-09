/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveForcing
public import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedAssembly
public import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedResidual
import LeanPool.NavierStokesAndEuler.Euler.PacketRecursionAlgebra

/-! Actual coefficient equations of the recursively constructed packet fields. -/

@[expose] public section


noncomputable section

namespace EulerPacketProfileRecursion

open EulerSmoothLimit EulerPacketPointJets EulerFiniteGrades EulerPacketResidual InnerProductSpace

/-- Assembled velocity, given by `assemble N (fun i => (a i).high+(a i).mean) (fun i => (a
i).corrector)`. -/
def assembledVelocity (N : ℕ) (a : ℕ → Profile) : ℕ → VectorField :=
  assemble N (fun i => (a i).high+(a i).mean) (fun i => (a i).corrector)

/-- Assembled pressure, given by `assemble N (fun i => (a i).meanPressure) (fun i => (a
i).highPressure)`. -/
def assembledPressure (N : ℕ) (a : ℕ → Profile) : ℕ → ScalarField :=
  assemble N (fun i => (a i).meanPressure) (fun i => (a i).highPressure)

/-- Pressure jets, given by `assemble N (fun i => pressureJet (a i).meanPressure z) (fun i =>
pressureJet (a i).highPressure z)`. -/
def pressureJets (N : ℕ) (a : ℕ → Profile) (z : Domain) : ℕ → ScalarJet :=
  assemble N (fun i => pressureJet (a i).meanPressure z) (fun i => pressureJet (a i).highPressure z)

/-- Recursive grade, constructed using `coefficient`. -/
def recursiveGrade (O : Operators) (N : ℕ) (a : ℕ → Profile) (z : Domain) (p : ℕ) : Space :=
  coefficient (N+1) (linearPart (O.strain z)) (slowPressure (O.inverseFrame z))
    (fastPressure (O.normal z)) (slowAdvection (O.inverseFrame z)) (fastAdvection (O.normal z))
    (assembledJets O N a z) (pressureJets N a z) p

theorem slicedJet_assembledVelocity (O : Operators) (N : ℕ) (a : ℕ → Profile) (z : Domain)
    (hA : ∀ i, SliceDifferentiable O.interval (a i).high z)
    (hB : ∀ i, SliceDifferentiable O.interval (a i).mean z)
    (hC : ∀ i, SliceDifferentiable O.interval (a i).corrector z) (i : ℕ) :
    slicedJet O.interval (assembledVelocity N a i) z=assembledJets O N a z i := by
  unfold assembledVelocity
  rw [slicedJet_assemble O.interval N i _ _ z (fun j _ => (hA j).add (hB j)) (fun j _ => hC j)]
  have h : (fun j => slicedJet O.interval ((a j).high+(a j).mean) z) =
      (fun j => slicedJet O.interval (a j).high z+slicedJet O.interval (a j).mean z) :=
    funext fun j => slicedJet_add (hA j) (hB j)
  rw [h]
  rfl

theorem pressureJet_assembledPressure (N : ℕ) (a : ℕ → Profile) (z : Domain)
    (hq : ∀ i, DifferentiableAt ℝ (fun y => (a i).meanPressure (z.1, y)) z.2)
    (hπ : ∀ i, DifferentiableAt ℝ (fun y => (a i).highPressure (z.1, y)) z.2) (i : ℕ) :
    pressureJet (assembledPressure N a i) z=pressureJets N a z i :=
  pressureJet_assemble N i _ _ z (fun j _ => hq j) (fun j _ => hπ j)

/-- The coefficient is that of the literal finite sum, with actual interval derivatives. -/
theorem recursiveGrade_eq_actual (O : Operators) (N : ℕ) (a : ℕ → Profile) (z : Domain)
    (hA : ∀ i, SliceDifferentiable O.interval (a i).high z)
    (hB : ∀ i, SliceDifferentiable O.interval (a i).mean z)
    (hC : ∀ i, SliceDifferentiable O.interval (a i).corrector z)
    (hq : ∀ i, DifferentiableAt ℝ (fun y => (a i).meanPressure (z.1, y)) z.2)
    (hπ : ∀ i, DifferentiableAt ℝ (fun y => (a i).highPressure (z.1, y)) z.2) (p : ℕ) :
    slicedMomentumGrade O.interval (N+1) (O.inverseFrame z) (O.strain z) (O.normal z)
      (assembledVelocity N a) (assembledPressure N a) z p=recursiveGrade O N a z p := by
  have hv := funext (slicedJet_assembledVelocity O N a z hA hB hC)
  have hp := funext (pressureJet_assembledPressure N a z hq hπ)
  unfold slicedMomentumGrade
  rw [hv, hp]
  rfl

/-- Solving the two linear equations used by the recursion cancels the whole grade. -/
theorem recursiveGrade_eq_zero (O : Operators) (primary : Profile) (hm : primary.mean = 0)
    (N p : ℕ) (hp : 2 ≤ p) (hpN : p ≤ N) (z : Domain)
    (hprimary : ⟪O.normal z, primary.high z⟫_ℝ = 0)
    (hhigh : ⟪O.normal z, (profiles O primary p).high z⟫_ℝ = 0)
    (hqθ : ∀ i ≤ N, fastPressure (O.normal z) (pressureJet (profiles O primary i).meanPressure z) =
        0)
    (hmeanEquation : linearPart (O.strain z) (slicedJet O.interval (profiles O primary p).mean z) +
      slowPressure (O.inverseFrame z) (pressureJet (profiles O primary p).meanPressure z) =
        meanForce O p (profiles O primary) z)
    (hhighEquation : linearPart (O.strain z) (slicedJet O.interval (profiles O primary p).high z) +
      fastPressure (O.normal z) (pressureJet (profiles O primary p).highPressure z) =
        highForce O p (profiles O primary) z) :
    recursiveGrade O N (profiles O primary) z p=0 := by
  have he :
      (linearPart (O.strain z) (slicedJet O.interval (profiles O primary p).high z) +
        fastPressure (O.normal z) (pressureJet (profiles O primary p).highPressure z)) +
      (linearPart (O.strain z) (slicedJet O.interval (profiles O primary p).mean z) +
        slowPressure (O.inverseFrame z) (pressureJet (profiles O primary p).meanPressure z)) =
      fullForce O N p (profiles O primary) z := by
    rw [hhighEquation, hmeanEquation, add_comm]
    exact recursive_forces_sum O primary hm N p hp hpN z hprimary hhigh
  unfold recursiveGrade assembledJets pressureJets
  rw [coefficient_assembled N p (by omega) hpN _ _ _ _ _ _ _ _ _ _ hqθ, he]
  unfold fullForce nonlinearGrade assembledJets
  abel

end EulerPacketProfileRecursion
