/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedAssembly
public import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedResidual
import LeanPool.NavierStokesAndEuler.Euler.PacketRecursionAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRecursion
public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeAssembly
import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeDiagonal

/-! Actual coefficient equations of the recursively constructed packet fields. -/

section

/-! The constructed recursive forcing equals the full nonlinear coefficient forcing. -/

@[expose] public section

noncomputable section

namespace EulerPacketProfileRecursion

open EulerSmoothLimit EulerPacketPointJets EulerFiniteGrades InnerProductSpace

@[simp] theorem zero_high : (0 : Profile).high=0 := rfl
@[simp] theorem zero_mean : (0 : Profile).mean=0 := rfl
@[simp] theorem zero_corrector : (0 : Profile).corrector=0 := rfl
@[simp] theorem zero_highPressure : (0 : Profile).highPressure=0 := rfl
@[simp] theorem zero_meanPressure : (0 : Profile).meanPressure=0 := rfl

theorem slicedJet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set ℝ) (z : Domain) : slicedJet s (0 : Domain → E) z=0 := by
  simp [slicedJet, joinDerivative]

/-- Assembled jets, constructed using `assemble`. -/
def assembledJets (O : Operators) (N : ℕ) (a : ℕ → Profile) (z : Domain) : ℕ → VectorJet :=
  assemble N (fun i => slicedJet O.interval (a i).high z+slicedJet O.interval (a i).mean z)
    (fun i => slicedJet O.interval (a i).corrector z)

theorem assembledJets_eq_velocityJet (O : Operators) (N : ℕ) (a : ℕ → Profile)
    (ha : a 0 = 0) (z : Domain) (i : ℕ) (hi : i ≤ N) :
    assembledJets O N a z i=velocityJet O.interval a z i := by
  by_cases hz : i=0
  · subst i
    unfold assembledJets
    rw [assemble_zero N _ _ (by rw [ha]; simp [slicedJet_zero])]
    simp [velocityJet]
  · unfold assembledJets
    rw [assemble_interior N i (by omega) hi]
    simp only [velocityJet, hz, ite_false]

theorem velocityJet_primary (O : Operators) (a : ℕ → Profile) (ha : a 0 = 0)
    (hmean : (a 1).mean = 0) (z : Domain) :
    velocityJet O.interval a z 1=slicedJet O.interval (a 1).high z := by
  simp only [velocityJet, one_ne_zero, ite_false, hmean, Nat.sub_self, ha]
  simp [slicedJet_zero]

theorem nonlinearGrade_cutoff (M K p : ℕ) (hM : p + 1 ≤ M) (hK : p + 1 ≤ K)
    (FInv : Space →L[ℝ] Space) (m : Space) (u : ℕ → VectorJet) :
    nonlinearGrade M p FInv m u=nonlinearGrade K p FInv m u := by
  unfold nonlinearGrade
  rw [convolution_eq_range M p (by omega), convolution_eq_range K p (by omega),
    convolution_eq_range M (p+1) hM, convolution_eq_range K (p+1) hK]

/-- Substituting the newly solved mean is the only change from the known forcing. -/
theorem assembled_nonlinear_eq_known (O : Operators) (N p : ℕ) (hp : 2 ≤ p) (hpN : p ≤ N)
    (a : ℕ → Profile) (ha : a 0 = 0) (hmean : (a 1).mean = 0) (z : Domain)
    (hprimary : ⟪O.normal z, (a 1).high z⟫_ℝ = 0) (hhigh : ⟪O.normal z, (a p).high z⟫_ℝ = 0) :
    nonlinearGrade (N+1) p (O.inverseFrame z) (O.normal z) (assembledJets O N a z) =
      nonlinearGrade (p+1) p (O.inverseFrame z) (O.normal z) (knownJets O p a z) +
      fastAdvection (O.normal z) (slicedJet O.interval (a p).mean z)
        (slicedJet O.interval (a 1).high z) := by
  have h₀ : knownJets O p a z 0=0 := by
    simp [knownJets, history, velocityJet, show 0<p by omega]
  have h₁ : knownJets O p a z 1=slicedJet O.interval (a 1).high z := by
    simp only [knownJets, history, show 1<p by omega, ite_true]
    exact velocityJet_primary O a ha hmean z
  have hsame : ∀ i<p, assembledJets O N a z i=knownJets O p a z i := by
    intro i hi
    rw [assembledJets_eq_velocityJet O N a ha z i (by omega)]
    simp only [knownJets, history, hi, ite_true]
  have hnew : assembledJets O N a z p=knownJets O p a z p +
      (slicedJet O.interval (a p).high z+slicedJet O.interval (a p).mean z) := by
    unfold assembledJets
    rw [assemble_interior N p (by omega) hpN]
    simp only [knownJets, history, lt_irrefl, ite_false, ite_true]
    abel
  have h := nonlinearGrade_update (N+1) p hp (by omega) (O.inverseFrame z) (O.normal z)
    (knownJets O p a z) (assembledJets O N a z) (slicedJet O.interval (a p).high z)
    (slicedJet O.interval (a p).mean z) h₀ hsame hnew
    (by rw [h₁]; exact hprimary) hhigh
  rw [h, h₁, nonlinearGrade_cutoff (N+1) (p+1) p (by omega) le_rfl]

/-- Full force as an element of `VectorField`. -/
def fullForce (O : Operators) (N p : ℕ) (a : ℕ → Profile) : VectorField :=
  fun z => -(linearPart (O.strain z) (slicedJet O.interval (a (p-1)).corrector z) +
    slowPressure (O.inverseFrame z) (pressureJet (a (p-1)).highPressure z) +
    nonlinearGrade (N+1) p (O.inverseFrame z) (O.normal z) (assembledJets O N a z))

theorem knownForce_sub_interaction (O : Operators) (N p : ℕ) (hp : 2 ≤ p) (hpN : p ≤ N)
    (a : ℕ → Profile) (ha : a 0 = 0) (hmean : (a 1).mean = 0) (z : Domain)
    (hprimary : ⟪O.normal z, (a 1).high z⟫_ℝ = 0) (hhigh : ⟪O.normal z, (a p).high z⟫_ℝ = 0) :
    knownForce O p a z-fastAdvection (O.normal z) (slicedJet O.interval (a p).mean z)
      (slicedJet O.interval (a 1).high z)=fullForce O N p a z := by
  unfold knownForce fullForce
  rw [assembled_nonlinear_eq_known O N p hp hpN a ha hmean z hprimary hhigh]
  abel

/-- The two right-hand sides actually generated by recursion sum to source (14). -/
theorem recursive_forces_sum (O : Operators) (primary : Profile) (hmean : primary.mean = 0)
    (N p : ℕ) (hp : 2 ≤ p) (hpN : p ≤ N) (z : Domain)
    (hprimary : ⟪O.normal z, primary.high z⟫_ℝ = 0)
    (hhigh : ⟪O.normal z, (profiles O primary p).high z⟫_ℝ = 0) :
    meanForce O p (profiles O primary) z+highForce O p (profiles O primary) z =
      fullForce O N p (profiles O primary) z := by
  have hm : (profiles O primary 1).mean=0 := by rw [profiles_one, hmean]
  have ht : ⟪O.normal z,(profiles O primary 1).high z⟫_ℝ=0 := by
    rw [profiles_one]
    exact hprimary
  have h := knownForce_sub_interaction O N p hp hpN (profiles O primary)
    (profiles_zero O primary) hm z ht hhigh
  unfold highForce
  rw [← profiles_mean O primary p hp]
  exact (by abel : meanForce O p (profiles O primary) z +
    (knownForce O p (profiles O primary) z-meanForce O p (profiles O primary) z -
      fastAdvection (O.normal z) (slicedJet O.interval (profiles O primary p).mean z)
        (slicedJet O.interval (profiles O primary 1).high z)) =
      knownForce O p (profiles O primary) z -
      fastAdvection (O.normal z) (slicedJet O.interval (profiles O primary p).mean z)
        (slicedJet O.interval (profiles O primary 1).high z)).trans h

end EulerPacketProfileRecursion

end
end

end

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
