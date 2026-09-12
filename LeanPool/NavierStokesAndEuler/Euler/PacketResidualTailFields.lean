/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderConvolution
public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveCancellation

/-! Actual continuous cylinder L² fields for every tail grade and for the finite tail sum. -/

section

/-!
Exact residual-tail grades. Fast pressure is absent beyond degree N, and
only degree N+1 retains the linear terminal corrector and slow pressure.
-/

@[expose] public section

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

theorem coefficient_assembled_tail (N n : ℕ) (hn : N + 1 ≤ n)
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
    (ha : a 0 = 0) (z : Domain) :
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

theorem recursiveGrade_tail (O : Operators) (N n : ℕ) (hn : N + 1 ≤ n)
    (a : ℕ → Profile) (ha : a 0 = 0) (z : Domain) :
    recursiveGrade O N a z n =
      (if n=N+1 then
        linearPart (O.strain z) (slicedJet O.interval (a N).corrector z) +
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
      linearPart (O.strain z) (slicedJet O.interval (a N).corrector z) +
      slowPressure (O.inverseFrame z) (pressureJet (a N).highPressure z) else 0) +
    convolution (N+1) (slowAdvection (O.inverseFrame z)) (assembledJets O N a z) (assembledJets O N
        a z) n +
    convolution (N+1) (fastAdvection (O.normal z)) (assembledJets O N a z) (assembledJets O N a z)
        (n+1) = _
  rw [assembledJets_eq_known O N a ha z]
  simp only [nonlinearGrade,add_assoc]

end EulerPacketProfileRecursion

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {N : ℕ} {a : ℕ → Profile}

/-- Tail nonlinear field as an element of `Field P T (fun z => nonlinearGrade (N+1) n
(O.inverseFrame z) (O.normal z) (knownJets O (N+1) a z))`. -/
def PrefixFields.tailNonlinearField (F : PrefixFields P T (N + 1) a)
    (C : CoefficientData P T O) (n : ℕ) :
    Field P T (fun z => nonlinearGrade (N+1) n (O.inverseFrame z) (O.normal z)
      (knownJets O (N+1) a z)) := by
  let J := F.knownJet O (by omega)
  let S := Field.convolution (N+1) n
    (fun i j z => slowAdvection (O.inverseFrame z) (knownJets O (N+1) a z i) (knownJets O (N+1) a z
        j))
    (fun i j => SpatialJetField.slowAdvection C.inverse (J i) (J j))
  let H := Field.convolution (N+1) (n+1)
    (fun i j z => fastAdvection (O.normal z) (knownJets O (N+1) a z i) (knownJets O (N+1) a z j))
    (fun i j => SpatialJetField.fastAdvection C.normal (J i) (J j))
  exact (S.add H).congr (fun _ _ _ => rfl)

/-- Tail linear field used in packet residual tail fields. -/
def PrefixFields.tailLinearField (F : PrefixFields P T (N + 1) a)
    (C : CoefficientData P T O) (hT : 0 < T) {correctorT : VectorField}
    (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector N (Nat.lt_succ_self N)) Ct)
    (pressure : Field P T (pressureGradient (a N).highPressure)) (n : ℕ) :
    Field P T (fun z => if n=N+1 then
      linearPart (O.strain z) (slicedJet O.interval (a N).corrector z) +
      slowPressure (O.inverseFrame z) (pressureJet (a N).highPressure z) else 0) := by
  by_cases hn : n=N+1
  · let L := Field.linearPart C.strain (F.corrector N (by omega)) Ct hT hCt O.interval C.interval_eq
    let Q := Field.slowPressure C.inverse (a N).highPressure pressure
    exact (L.add Q).congr (fun _ _ _ => by simp [hn])
  · exact (Field.zero P T).congr (fun _ _ _ => by simp [hn])

/-- Tail grade field as an element of `Field P T (fun z => recursiveGrade O N a z n)`. -/
def PrefixFields.tailGradeField (F : PrefixFields P T (N + 1) a)
    (C : CoefficientData P T O) (hT : 0 < T) {correctorT : VectorField}
    (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector N (Nat.lt_succ_self N)) Ct)
    (pressure : Field P T (pressureGradient (a N).highPressure))
    (ha : a 0 = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    Field P T (fun z => recursiveGrade O N a z n) :=
  ((F.tailLinearField C hT Ct hCt pressure n).add (F.tailNonlinearField C n)).congr
    (fun _ _ _ => recursiveGrade_tail O N n hn a ha _)

theorem PrefixFields.tailGradeField_path (F : PrefixFields P T (N + 1) a)
    (C : CoefficientData P T O) (hT : 0 < T) {correctorT : VectorField}
    (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector N (Nat.lt_succ_self N)) Ct)
    (pressure : Field P T (pressureGradient (a N).highPressure))
    (ha : a 0 = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    (F.tailGradeField C hT Ct hCt pressure ha n hn).path =
      (F.tailLinearField C hT Ct hCt pressure n).path + (F.tailNonlinearField C n).path := rfl

/-- Tail grades, given by `Ico (N+1) (2*N+3)`. -/
def tailGrades (N : ℕ) : Finset ℕ := Ico (N+1) (2*N+3)

theorem tailGrades_card (N : ℕ) : (tailGrades N).card = N+2 := by
  simp only [tailGrades, Nat.card_Ico]
  omega

/-- Tail sum field as an element of `Field P T (fun z => ∑ n ∈ tailGrades N, κ^n •
recursiveGrade O N a z n)`. -/
def PrefixFields.tailSumField (F : PrefixFields P T (N + 1) a)
    (C : CoefficientData P T O) (hT : 0 < T) {correctorT : VectorField}
    (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector N (Nat.lt_succ_self N)) Ct)
    (pressure : Field P T (pressureGradient (a N).highPressure)) (ha : a 0 = 0) (κ : ℝ) :
    Field P T (fun z => ∑ n ∈ tailGrades N, κ^n • recursiveGrade O N a z n) := by
  let term := fun q : {n // n ∈ tailGrades N} =>
    (F.tailGradeField C hT Ct hCt pressure ha q.1 (Finset.mem_Ico.mp q.2).1).smul (κ^q.1)
  let G := Field.finsetSum (tailGrades N).attach _ term
  refine G.congr ?_
  intro t x θ
  change (∑ n ∈ tailGrades N, κ^n • recursiveGrade O N a (t,(x,θ)) n) =
    (∑ q ∈ (tailGrades N).attach,
      (κ^q.1 • (fun z => recursiveGrade O N a z q.1) : VectorField)) (t,(x,θ))
  rw [Finset.sum_apply]
  simpa only [Pi.smul_apply] using (Finset.sum_attach (tailGrades N)
    (fun n => κ^n • recursiveGrade O N a (t,(x,θ)) n)).symm

namespace ProfileRegularity

variable {S : Set Space}

/-- Prefix through, given by `prefixFields (fun i hi => G i (by omega))`. -/
def prefixThrough (hT : 0 < T)
    (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le S (a i)) : PrefixFields P T (N+1) a :=
  prefixFields (fun i hi => G i (by omega))

/-- Tail grade field as an element of `Field P T (fun z => recursiveGrade O N a z n)`. -/
def tailGradeField (hT : 0 < T)
    (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le S (a i))
    (C : CoefficientData P T O) (ha : a 0 = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    Field P T (fun z => recursiveGrade O N a z n) :=
  (prefixThrough hT G).tailGradeField C hT (G N le_rfl).correctorDerivative
    (G N le_rfl).corrector_time (G N le_rfl).pressure ha n hn

/-- Tail sum field, given by `(prefixThrough hT G).tailSumField C hT (G N
le_rfl).correctorDerivative (G N le_rfl).corrector_time (G N le_rfl).pressure ha κ`. -/
def tailSumField (hT : 0 < T)
    (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le S (a i))
    (C : CoefficientData P T O) (ha : a 0 = 0) (κ : ℝ) :
    Field P T (fun z => ∑ n ∈ tailGrades N, κ^n • recursiveGrade O N a z n) :=
  (prefixThrough hT G).tailSumField C hT (G N le_rfl).correctorDerivative
    (G N le_rfl).corrector_time (G N le_rfl).pressure ha κ

end ProfileRegularity
end EulerPacketCylinderField
