/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveCancellation

@[expose] public section

/-! The literal finite packet and its genuine time derivative are actual cylinder fields. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion EulerFiniteGrades

def rawTimeDerivative (T : ℝ) (raw : VectorField) : VectorField := fun z =>
  derivWithin (fun t => raw (t,z.2)) (Icc (0 : ℝ) T) z.1

variable {P T : ℝ} [Fact (0 < P)]

def Field.timeDerivativeField {raw raw_t : VectorField} (G : Field P T raw) (hT : 0 < T)
    (H : Field P T raw_t) (ht : TimeDerivative hT.le G H) :
    Field P T (rawTimeDerivative T raw) :=
  H.congr (fun t x θ => (G.raw_hasDerivWithinAt hT.le H ht t x θ).derivWithin
    ((uniqueDiffOn_Icc hT) _ t.property))

theorem Field.timeDerivativeField_time {raw raw_t : VectorField} (G : Field P T raw) (hT : 0 < T)
    (H : Field P T raw_t) (ht : TimeDerivative hT.le G H) :
    TimeDerivative hT.le G (G.timeDerivativeField hT H ht) := ht

namespace ProfileRegularity

variable {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))

def velocityGradeField (i : ℕ) : Field P T (assembledVelocity N a i) :=
  Field.assembleFamily N (fun j => (a j).high+(a j).mean) (fun j => (a j).corrector)
    (fun j hj => (G j hj).high.add (G j hj).mean) (fun j hj => (G j hj).corrector) i

def velocityTimeCoefficients : ℕ → VectorField :=
  assemble N (fun i => rawTimeDerivative T ((a i).high+(a i).mean))
    (fun i => rawTimeDerivative T (a i).corrector)

def velocityGradeDerivativeField (i : ℕ) : Field P T (velocityTimeCoefficients (T := T) (N := N) (a
  := a) i) :=
  Field.assembleFamily N (fun j => rawTimeDerivative T ((a j).high+(a j).mean))
    (fun j => rawTimeDerivative T (a j).corrector)
    (fun j hj => ((G j hj).high.add (G j hj).mean).timeDerivativeField hT
      ((G j hj).highDerivative.add (G j hj).meanDerivative)
      ((G j hj).high_time.add (G j hj).mean_time))
    (fun j hj => (G j hj).corrector.timeDerivativeField hT (G j hj).correctorDerivative
      (G j hj).corrector_time) i

theorem velocityGrade_time (i : ℕ) :
    TimeDerivative hT.le (velocityGradeField hT G i) (velocityGradeDerivativeField hT G i) :=
  TimeDerivative.assembleFamily N _ _ _ _ _ _ _ _
    (fun j hj => ((G j hj).high_time.add (G j hj).mean_time))
    (fun j hj => (G j hj).corrector_time) i

def velocityField (κ : ℝ) : Field P T (fieldSum (N+1) κ (assembledVelocity N a)) :=
  Field.evaluateFamily (N+1) κ _ (velocityGradeField hT G)

def velocityDerivativeField (κ : ℝ) :
    Field P T (fieldSum (N+1) κ (velocityTimeCoefficients (T := T) (N := N) (a := a))) :=
  Field.evaluateFamily (N+1) κ _ (velocityGradeDerivativeField hT G)

theorem velocityField_time (κ : ℝ) :
    TimeDerivative hT.le (velocityField hT G κ) (velocityDerivativeField hT G κ) :=
  TimeDerivative.evaluateFamily (N+1) κ _ _ _ _ (velocityGrade_time hT G)

end ProfileRegularity
end EulerPacketCylinderField
