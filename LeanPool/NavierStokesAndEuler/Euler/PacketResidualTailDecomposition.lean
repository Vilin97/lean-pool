/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveCancellation

@[expose] public section

/-!
Exact residual-tail grades. Fast pressure is absent beyond degree N, and
only degree N+1 retains the linear terminal corrector and slow pressure.
-/

noncomputable section

namespace EulerFiniteGrades

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem shiftDown_convolution_eq (M n : ℕ) (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (u v : ℕ → V) :
    shiftDown (2*M) (convolution M B u v) n = convolution M B u v (n+1) := by
  unfold shiftDown
  by_cases h : n+1 ≤ 2*M
  · exact truncate_of_le _ _ _ h
  · rw [truncate_of_gt _ _ _ (by omega),convolution_above M (n+1) (by omega)]

end EulerFiniteGrades

namespace EulerPacketResidual

open EulerFiniteGrades

variable {V Q W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup Q] [Module ℝ Q] [AddCommGroup W] [Module ℝ W]

theorem coefficient_assembled_tail (N n : ℕ) (hn : N+1 ≤ n)
    (L : V →ₗ[ℝ] W) (G H : Q →ₗ[ℝ] W) (B C : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (u c : ℕ → V) (q π : ℕ → Q) :
    coefficient (N+1) L G H B C (assemble N u c) (assemble N q π) n =
      (if n=N+1 then L (c N)+G (π N) else 0) +
      convolution (N+1) B (assemble N u c) (assemble N u c) n +
      convolution (N+1) C (assemble N u c) (assemble N u c) (n+1) := by
  have hL : truncate (N+1) (fun i => L (assemble N u c i)) n =
      if n=N+1 then L (c N) else 0 := by
    by_cases h : n=N+1
    · subst n
      rw [truncate_of_le _ _ _ le_rfl,assemble_last,ite_eq_left rfl]
    · rw [truncate_of_gt _ _ _ (by omega),ite_eq_right h]
  have hG : truncate (N+1) (fun i => G (assemble N q π i)) n =
      if n=N+1 then G (π N) else 0 := by
    by_cases h : n=N+1
    · subst n
      rw [truncate_of_le _ _ _ le_rfl,assemble_last,ite_eq_left rfl]
    · rw [truncate_of_gt _ _ _ (by omega),ite_eq_right h]
  unfold coefficient
  rw [hL,hG,shiftDown_above (N+1) n _ hn,shiftDown_convolution_eq]
  by_cases h : n=N+1
  · simp only [h,ite_true,add_zero]
  · simp only [h,ite_false,zero_add]

end EulerPacketResidual

namespace EulerPacketProfileRecursion

open EulerSmoothLimit EulerPacketPointJets EulerFiniteGrades EulerPacketResidual

/-- The existing known-jet constructor is exactly the complete finite velocity family. -/
theorem assembledJets_eq_known (O : Operators) (N : ℕ) (a : ℕ → Profile)
    (ha : a 0=0) (z : Domain) :
    assembledJets O N a z = knownJets O (N+1) a z := by
  funext i
  by_cases hi : i ≤ N
  · rw [assembledJets_eq_velocityJet O N a ha z i hi]
    simp only [knownJets,history,show i < N+1 by omega,ite_true]
  by_cases he : i=N+1
  · subst i
    simp only [assembledJets,assemble_last,knownJets,history,lt_irrefl,ite_false,
      ite_true,Nat.add_sub_cancel]
  · have hz : assembledJets O N a z i = 0 := assemble_above N i (by omega) _ _
    rw [hz]
    simp only [knownJets,history,show ¬ i < N+1 by omega,ite_false,he]

theorem recursiveGrade_tail (O : Operators) (N n : ℕ) (hn : N+1 ≤ n)
    (a : ℕ → Profile) (ha : a 0=0) (z : Domain) :
    recursiveGrade O N a z n =
      (if n=N+1 then
        linearPart (O.strain z) (slicedJet O.interval (a N).corrector z)+
        slowPressure (O.inverseFrame z) (pressureJet (a N).highPressure z) else 0) +
      nonlinearGrade (N+1) n (O.inverseFrame z) (O.normal z) (knownJets O (N+1) a z) := by
  have h := coefficient_assembled_tail N n hn
    (linearPart (O.strain z)) (slowPressure (O.inverseFrame z)) (fastPressure (O.normal z))
    (slowAdvection (O.inverseFrame z)) (fastAdvection (O.normal z))
    (fun i => slicedJet O.interval (a i).high z+slicedJet O.interval (a i).mean z)
    (fun i => slicedJet O.interval (a i).corrector z)
    (fun i => pressureJet (a i).meanPressure z) (fun i => pressureJet (a i).highPressure z)
  change recursiveGrade O N a z n = _ at h
  rw [h]
  change (if n=N+1 then
      linearPart (O.strain z) (slicedJet O.interval (a N).corrector z)+
      slowPressure (O.inverseFrame z) (pressureJet (a N).highPressure z) else 0) +
    convolution (N+1) (slowAdvection (O.inverseFrame z)) (assembledJets O N a z) (assembledJets O N
      a z) n +
    convolution (N+1) (fastAdvection (O.normal z)) (assembledJets O N a z) (assembledJets O N a z)
      (n+1) = _
  rw [assembledJets_eq_known O N a ha z]
  simp only [nonlinearGrade,add_assoc]

end EulerPacketProfileRecursion
