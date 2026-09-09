/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderKnownJets
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderConvolution
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAverage

/-!
# Literal recursive forcing is an actual smooth cylinder L² path

Only the already constructed prefix fields, the true time derivative of the
previous corrector, its scalar-pressure gradient, and the actual coefficient
paths enter. No equation or cancellation for the new profile is assumed.
-/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion EulerFiniteGrades

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {p : ℕ} {a : ℕ → Profile}

/-- Both finite nonlinear convolutions are formed from the actual earlier fields. -/
def PrefixFields.nonlinear (F : PrefixFields P T p a) (C : CoefficientData P T O) (hp : 1 ≤ p) :
    Field P T (fun z => nonlinearGrade (p+1) p (O.inverseFrame z) (O.normal z) (knownJets O p a z))
        := by
  let J := F.knownJet O hp
  let S := Field.convolution (p+1) p
    (fun i j z => slowAdvection (O.inverseFrame z) (knownJets O p a z i) (knownJets O p a z j))
    (fun i j => SpatialJetField.slowAdvection C.inverse (J i) (J j))
  let A := Field.convolution (p+1) (p+1)
    (fun i j z => fastAdvection (O.normal z) (knownJets O p a z i) (knownJets O p a z j))
    (fun i j => SpatialJetField.fastAdvection C.normal (J i) (J j))
  exact (S.add A).congr (fun _ _ _ => rfl)

/-- The manuscript's exact knownForce expression has a genuine path and all spatial derivatives. -/
def PrefixFields.knownForce (F : PrefixFields P T p a) (C : CoefficientData P T O)
    (hp : 1 ≤ p) (hT : 0 < T) {correctorT : VectorField}
    (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P T (pressureGradient (a (p - 1)).highPressure)) :
    Field P T (EulerPacketProfileRecursion.knownForce O p a) := by
  let L := Field.linearPart C.strain (F.corrector (p-1) (by
      omega)) Ct hT hCt O.interval C.interval_eq
  let Q := Field.slowPressure C.inverse (a (p-1)).highPressure pressure
  exact (((L.add Q).add (F.nonlinear C hp)).neg).congr (fun _ _ _ => rfl)

/-- The actual mean-force raw field is also represented in cylinder L². -/
def PrefixFields.meanForce (F : PrefixFields P T p a) (C : CoefficientData P T O)
    (hp : 1 ≤ p) (hT : 0 < T) {correctorT : VectorField}
    (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P T (pressureGradient (a (p - 1)).highPressure)) :
    Field P T (EulerPacketProfileRecursion.meanForce O p a) :=
  ((F.knownForce C hp hT Ct hCt pressure).angleMean).congr (fun _ _ _ => by
    rw [EulerPacketProfileRecursion.meanForce,C.period_eq])

/-- Once the actual new mean has been supplied, the exact high-force expression is admissible as a
path. -/
def PrefixFields.highForce (F : PrefixFields P T p a) (C : CoefficientData P T O)
    (hp : 2 ≤ p) (hT : 0 < T) {correctorT : VectorField}
    (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P T (pressureGradient (a (p - 1)).highPressure))
    (newMean : Field P T (meanResult O p a).1) :
    Field P T (EulerPacketProfileRecursion.highForce O p a) := by
  let K := F.knownForce C (by omega) hT Ct hCt pressure
  let M := F.meanForce C (by omega) hT Ct hCt pressure
  let A := SpatialJetField.fastAdvection C.normal
    (SpatialJetField.ofField O.interval newMean)
    (SpatialJetField.ofField O.interval (F.high 1 (by omega)))
  exact ((K.sub M).sub A).congr (fun _ _ _ => rfl)

end EulerPacketCylinderField
