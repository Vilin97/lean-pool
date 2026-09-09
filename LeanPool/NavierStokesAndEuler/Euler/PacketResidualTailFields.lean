/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderConvolution
public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailDecomposition

/-! Actual continuous cylinder L² fields for every tail grade and for the finite tail sum. -/

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
