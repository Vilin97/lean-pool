/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceRegularity

/-!
The actual sliced momentum coefficient equals the tail decomposition using
only finite velocity regularity. No regularity of the lower scalar pressures
is needed, because their coefficients are already outside the tail support.
-/

@[expose] public section


noncomputable section

namespace EulerPacketProfileRecursion

open Set EulerSmoothLimit EulerPacketPointJets EulerFiniteGrades EulerPacketResidual

theorem slicedJet_assembledVelocity_finite (O : Operators) (N : ℕ) (a : ℕ → Profile) (z : Domain)
    (hA : ∀ i ≤ N, SliceDifferentiable O.interval (a i).high z)
    (hB : ∀ i ≤ N, SliceDifferentiable O.interval (a i).mean z)
    (hC : ∀ i ≤ N, SliceDifferentiable O.interval (a i).corrector z) (i : ℕ) :
    slicedJet O.interval (assembledVelocity N a i) z = assembledJets O N a z i := by
  unfold assembledVelocity
  rw [slicedJet_assemble O.interval N i _ _ z
    (fun j hj => (hA j hj).add (hB j hj)) hC]
  change truncate N (fun j => slicedJet O.interval ((a j).high+(a j).mean) z) i + _ =
    truncate N (fun j => slicedJet O.interval (a j).high z+slicedJet O.interval (a j).mean z) i + _
  by_cases hi : i ≤ N
  · rw [truncate_of_le _ _ _ hi,truncate_of_le _ _ _ hi,slicedJet_add (hA i hi) (hB i hi)]
  · rw [truncate_of_gt _ _ _ (by omega),truncate_of_gt _ _ _ (by omega)]

theorem slicedMomentumGrade_tail_eq_recursive (O : Operators) (N n : ℕ) (hn : N + 1 ≤ n)
    (a : ℕ → Profile) (z : Domain)
    (hA : ∀ i ≤ N, SliceDifferentiable O.interval (a i).high z)
    (hB : ∀ i ≤ N, SliceDifferentiable O.interval (a i).mean z)
    (hC : ∀ i ≤ N, SliceDifferentiable O.interval (a i).corrector z) :
    slicedMomentumGrade O.interval (N+1) (O.inverseFrame z) (O.strain z) (O.normal z)
      (assembledVelocity N a) (assembledPressure N a) z n = recursiveGrade O N a z n := by
  have hv : (fun i => slicedJet O.interval (assembledVelocity N a i) z) = assembledJets O N a z :=
    funext (slicedJet_assembledVelocity_finite O N a z hA hB hC)
  have hg : truncate (N+1)
      (fun i => slowPressure (O.inverseFrame z) (pressureJet (assembledPressure N a i) z)) n =
      truncate (N+1) (fun i => slowPressure (O.inverseFrame z) (pressureJets N a z i)) n := by
    by_cases he : n=N+1
    · subst n
      rw [truncate_of_le _ _ _ le_rfl,truncate_of_le _ _ _ le_rfl]
      unfold assembledPressure pressureJets
      rw [assemble_last,assemble_last]
    · rw [truncate_of_gt _ _ _ (by omega),truncate_of_gt _ _ _ (by omega)]
  unfold slicedMomentumGrade
  rw [hv]
  unfold recursiveGrade coefficient
  rw [hg,shiftDown_above (N+1) n _ hn,shiftDown_above (N+1) n _ hn]

theorem slicedMomentumGrade_tail (O : Operators) (N n : ℕ) (hn : N + 1 ≤ n)
    (a : ℕ → Profile) (ha : a 0 = 0) (z : Domain)
    (hA : ∀ i ≤ N, SliceDifferentiable O.interval (a i).high z)
    (hB : ∀ i ≤ N, SliceDifferentiable O.interval (a i).mean z)
    (hC : ∀ i ≤ N, SliceDifferentiable O.interval (a i).corrector z) :
    slicedMomentumGrade O.interval (N+1) (O.inverseFrame z) (O.strain z) (O.normal z)
      (assembledVelocity N a) (assembledPressure N a) z n =
      (if n=N+1 then
        linearPart (O.strain z) (slicedJet O.interval (a N).corrector z) +
        slowPressure (O.inverseFrame z) (pressureJet (a N).highPressure z) else 0) +
      nonlinearGrade (N+1) n (O.inverseFrame z) (O.normal z) (knownJets O (N+1) a z) :=
  (slicedMomentumGrade_tail_eq_recursive O N n hn a z hA hB hC).trans
    (recursiveGrade_tail O N n hn a ha z)

end EulerPacketProfileRecursion

namespace EulerPacketCylinderField.ProfileRegularity

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {N : ℕ} {a : ℕ → Profile} {S : Set Space}

/-- Literal tail grade field used in packet residual tail actual. -/
def literalTailGradeField (hT : 0 < T)
    (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le S (a i))
    (C : CoefficientData P T O) (ha : a 0 = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    Field P T (fun z => slicedMomentumGrade O.interval (N+1) (O.inverseFrame z) (O.strain z)
        (O.normal z)
      (assembledVelocity N a) (assembledPressure N a) z n) := by
  refine (tailGradeField hT G C ha n hn).congr ?_
  intro t x θ
  apply slicedMomentumGrade_tail_eq_recursive O N n hn a (t,(x,θ))
  · intro i hi
    rw [C.interval_eq]
    exact (G i hi).high.sliceDifferentiable (G i hi).highDerivative hT.le (G i hi).high_time t x θ
  · intro i hi
    rw [C.interval_eq]
    exact (G i hi).mean.sliceDifferentiable (G i hi).meanDerivative hT.le (G i hi).mean_time t x θ
  · intro i hi
    rw [C.interval_eq]
    exact (G i hi).corrector.sliceDifferentiable (G i hi).correctorDerivative hT.le (G i
        hi).corrector_time t x θ

theorem literalTailGradeField_path (hT : 0 < T)
    (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le S (a i))
    (C : CoefficientData P T O) (ha : a 0 = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    (literalTailGradeField hT G C ha n hn).path = (tailGradeField hT G C ha n hn).path := rfl

end EulerPacketCylinderField.ProfileRegularity
