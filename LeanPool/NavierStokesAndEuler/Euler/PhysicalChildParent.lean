/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketFrames
public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleFieldBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketVolumeDivergence
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowVolume
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldChain
import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldTimeJets
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphFlowBounds
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowCoefficientPaths
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldComposition
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldBilinear
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldAlgebra
import Mathlib.Analysis.Calculus.Deriv.Add

/-! The actual composed child coefficients form the next parent data.
The next spatial scale can be chosen independently of the current scale. -/

section

/-! Actual continuous bounded coefficient paths for the graph-flow
displacement, velocity, and acceleration. No extra supremum estimate on
the time derivative of the lifted velocity is required. -/

section

/-! Actual deformation, first time derivative, and second time derivative
as smooth bounded coefficient paths. Every spatial jet is continuous in
the sup norm; no third time derivative is used for the acceleration. -/

@[expose] public section

noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace EulerSmoothBanachFlow

open Set EulerVolterraConvolution EulerSmoothFlowGevrey

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowDeformation1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instSmoothFlowDeformation2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowDeformation3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowDeformation4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instSmoothFlowDeformation5 : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instSmoothFlowDeformation6 : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] (E →L[ℝ] E))` instance to shorten
typeclass synthesis. -/
local instance instSmoothFlowDeformation7 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] (E →L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] (E →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowDeformation8 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] (E →L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] E)))` instance to shorten
typeclass synthesis. -/
local instance instSmoothFlowDeformation9 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ]
    E))) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] E)))` instance to shorten
typeclass synthesis. -/
local instance instSmoothFlowDeformation10 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] E)))
    := inferInstance

variable (B R : ℝ) (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
  (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
  (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)

/-- Acceleration coefficient as an element of `SmoothTimeField (Icc (0 : ℝ) T) E E`. -/
def accelerationCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E E :=
  (A₁.add (SmoothTimeField.bilinear (ContinuousLinearMap.id ℝ (E →L[ℝ] E)) A.derivative
      A)).compDisplacement
    (displacementCoefficient T hT A B R hB hR hsmall hb)

@[simp] theorem accelerationCoefficient_apply (t : Icc (0 : ℝ) T) (x : E) :
    (accelerationCoefficient T hT A B R hB hR hsmall hb A₁).field t x =
      accelerationFamily T hT A A₁ x t := by
  change A₁.field t (x+(displacementCoefficient T hT A B R hB hR hsmall hb).field t x) +
    A.derivative.field t (x+(displacementCoefficient T hT A B R hB hR hsmall hb).field t x)
      (A.field t (x+(displacementCoefficient T hT A B R hB hR hsmall hb).field t x)) = _
  rw [displacementCoefficient_apply]
  have he : x+((flowData T hT A).forward t x-x) = (flowData T hT A).forward t x := by abel
  rw [he]
  change A₁.field t ((flowData T hT A).forward t x) +
    A.derivativeField t ((flowData T hT A).forward t x)
      (A.field t ((flowData T hT A).forward t x)) = _
  rw [A.derivativeField_eq]
  exact (accelerationFamily_apply T hT A A₁ x t).symm

/-- Deformation coefficient, given by `(SmoothTimeField.boundConstant (ContinuousLinearMap.id ℝ
E)).add (displacementCoefficient T hT A B R hB hR hsmall hb).derivative`. -/
def deformationCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E (E →L[ℝ] E) :=
  (SmoothTimeField.boundConstant (ContinuousLinearMap.id ℝ E)).add
    (displacementCoefficient T hT A B R hB hR hsmall hb).derivative

@[simp] theorem deformationCoefficient_apply (t : Icc (0 : ℝ) T) (x : E) :
    (deformationCoefficient T hT A B R hB hR hsmall hb).field t x =
      fderiv ℝ (fun y => (flowData T hT A).forward t y) x := by
  change ContinuousLinearMap.id ℝ E +
    (displacementCoefficient T hT A B R hB hR hsmall hb).derivativeField t x = _
  rw [SmoothTimeField.derivativeField_eq]
  have he : ((displacementCoefficient T hT A B R hB hR hsmall hb).field t : E → E) =
      fun y => (flowData T hT A).forward t y-y :=
    funext (fun y => displacementCoefficient_apply T hT A B R hB hR hsmall hb t y)
  rw [he]
  have hd : fderiv ℝ (fun y => (flowData T hT A).forward t y-y) x =
      fderiv ℝ (fun y => (flowData T hT A).forward t y) x - ContinuousLinearMap.id ℝ E := by
    simpa only [Pi.sub_def, id_eq, fderiv_id] using
      (fderiv_sub (𝕜 := ℝ) (f := fun y => (flowData T hT A).forward t y) (g := id)
        ((forward_contDiff T hT A t).differentiable (by simp) x) differentiableAt_id)
  rw [hd]
  abel

variable (htime : SmoothTimeField.TimeDerivative T hT A A₁)
  (B₁ R₁ : ℝ) (hB₁ : 0 ≤ B₁) (hR₁ : 0 ≤ R₁)
  (hb₁ : ∀ n, ‖A₁.jet n‖ ≤ B₁ * R₁ ^ n * (n.factorial : ℝ) ^ 2)

/-- Deformation time coefficient, given by `(velocityCoefficient T hT A B R hB hR hsmall hb A₁
htime B₁ R₁ hB₁ hR₁ hb₁).derivative`. -/
def deformationTimeCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E (E →L[ℝ] E) :=
  (velocityCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁).derivative

/-- Deformation second coefficient, given by `(accelerationCoefficient T hT A B R hB hR hsmall
hb A₁).derivative`. -/
def deformationSecondCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E (E →L[ℝ] E) :=
  (accelerationCoefficient T hT A B R hB hR hsmall hb A₁).derivative

theorem displacementCoefficient_time : SmoothTimeField.TimeDerivative T hT
    (displacementCoefficient T hT A B R hB hR hsmall hb)
    (velocityCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁) := by
  intro t x
  exact displacementFamily_time_derivative T hT A x t

theorem velocityCoefficient_time : SmoothTimeField.TimeDerivative T hT
    (velocityCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁)
    (accelerationCoefficient T hT A B R hB hR hsmall hb A₁) := by
  intro t x
  rw [accelerationCoefficient_apply]
  exact velocityFamily_time_derivative T hT A A₁ htime x t

theorem deformationCoefficient_time : SmoothTimeField.TimeDerivative T hT
    (deformationCoefficient T hT A B R hB hR hsmall hb)
    (deformationTimeCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁) := by
  have hd := SmoothTimeField.TimeDerivative.derivative T hT _ _
    (displacementCoefficient_time T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁)
  intro t x
  exact (hd t x).const_add (ContinuousLinearMap.id ℝ E)

theorem deformationTimeCoefficient_time : SmoothTimeField.TimeDerivative T hT
    (deformationTimeCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁)
    (deformationSecondCoefficient T hT A B R hB hR hsmall hb A₁) :=
  SmoothTimeField.TimeDerivative.derivative T hT _ _
    (velocityCoefficient_time T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁)

end EulerSmoothBanachFlow

end
end

end

@[expose] public section

noncomputable section

namespace EulerPhysicalGraphFlowBounds.Data

open Set EulerLiftedGradientSpace EulerSmoothBanachFlow EulerSmoothFlowGevrey
  EulerGraphInvariantFlow EulerVolterraConvolution

variable {P T : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P T)

/-- Cover displacement coefficient, given by `displacementCoefficient T G.time_nonneg G.A G.B
G.R G.B_nonneg G.R_pos G.small G.sup_bound`. -/
def coverDisplacementCoefficient : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent :=
  displacementCoefficient T G.time_nonneg G.A G.B G.R G.B_nonneg G.R_pos G.small G.sup_bound

/-- Cover velocity coefficient, given by `G.A.compDisplacement G.coverDisplacementCoefficient`. -/
def coverVelocityCoefficient : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent :=
  G.A.compDisplacement G.coverDisplacementCoefficient

/-- Cover acceleration coefficient, given by `accelerationCoefficient T G.time_nonneg G.A G.B
G.R G.B_nonneg G.R_pos G.small G.sup_bound G.A₁`. -/
def coverAccelerationCoefficient : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent :=
  accelerationCoefficient T G.time_nonneg G.A G.B G.R G.B_nonneg G.R_pos G.small G.sup_bound G.A₁

@[simp] theorem coverDisplacementCoefficient_apply (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    G.coverDisplacementCoefficient.field t x = (flowData T G.time_nonneg G.A).forward t x-x := rfl

@[simp] theorem coverVelocityCoefficient_apply (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    G.coverVelocityCoefficient.field t x = velocityFamily T G.time_nonneg G.A x t := by
  change G.A.field t (x+G.coverDisplacementCoefficient.field t x) = _
  rw [G.coverDisplacementCoefficient_apply]
  have he : x+((flowData T G.time_nonneg G.A).forward t x-x) =
      (flowData T G.time_nonneg G.A).forward t x := by abel
  rw [he]
  rfl

@[simp] theorem coverAccelerationCoefficient_apply (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    G.coverAccelerationCoefficient.field t x = accelerationFamily T G.time_nonneg G.A G.A₁ x t :=
  accelerationCoefficient_apply T G.time_nonneg G.A G.B G.R G.B_nonneg G.R_pos G.small G.sup_bound
      G.A₁ t x

theorem coverDisplacementCoefficient_time : SmoothTimeField.TimeDerivative T G.time_nonneg
    G.coverDisplacementCoefficient G.coverVelocityCoefficient := by
  intro t x
  have he : (fun s => G.coverDisplacementCoefficient.realField T G.time_nonneg s x) =
      extendPath T G.time_nonneg (displacementFamily T G.time_nonneg G.A x) := rfl
  rw [he,G.coverVelocityCoefficient_apply]
  exact displacementFamily_time_derivative T G.time_nonneg G.A x t

theorem coverVelocityCoefficient_time : SmoothTimeField.TimeDerivative T G.time_nonneg
    G.coverVelocityCoefficient G.coverAccelerationCoefficient := by
  intro t x
  have he : (fun s => G.coverVelocityCoefficient.realField T G.time_nonneg s x) =
      extendPath T G.time_nonneg (velocityFamily T G.time_nonneg G.A x) := by
    funext s
    exact G.coverVelocityCoefficient_apply (projIcc 0 T G.time_nonneg s) x
  rw [he,G.coverAccelerationCoefficient_apply]
  exact velocityFamily_time_derivative T G.time_nonneg G.A G.A₁ G.time_derivative x t

/-- Physical displacement coefficient, given by `physicalCoefficient k m T
G.coverDisplacementCoefficient ell`. -/
def physicalDisplacementCoefficient (k : ℝ) (m : Vector3) (ell : ℝ) :
    SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3 :=
  physicalCoefficient k m T G.coverDisplacementCoefficient ell

/-- Physical velocity coefficient, given by `physicalCoefficient k m T
G.coverVelocityCoefficient ell`. -/
def physicalVelocityCoefficient (k : ℝ) (m : Vector3) (ell : ℝ) :
    SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3 :=
  physicalCoefficient k m T G.coverVelocityCoefficient ell

/-- Physical acceleration coefficient, given by `physicalCoefficient k m T
G.coverAccelerationCoefficient ell`. -/
def physicalAccelerationCoefficient (k : ℝ) (m : Vector3) (ell : ℝ) :
    SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3 :=
  physicalCoefficient k m T G.coverAccelerationCoefficient ell

theorem physicalDisplacementCoefficient_time (k : ℝ) (m : Vector3) (ell : ℝ) :
    SmoothTimeField.TimeDerivative T G.time_nonneg
      (G.physicalDisplacementCoefficient k m ell) (G.physicalVelocityCoefficient k m ell) :=
  physicalCoefficient_timeDerivative k m T G.time_nonneg
    G.coverDisplacementCoefficient G.coverVelocityCoefficient ell
        G.coverDisplacementCoefficient_time

theorem physicalVelocityCoefficient_time (k : ℝ) (m : Vector3) (ell : ℝ) :
    SmoothTimeField.TimeDerivative T G.time_nonneg
      (G.physicalVelocityCoefficient k m ell) (G.physicalAccelerationCoefficient k m ell) :=
  physicalCoefficient_timeDerivative k m T G.time_nonneg
    G.coverVelocityCoefficient G.coverAccelerationCoefficient ell G.coverVelocityCoefficient_time

theorem physicalDisplacementCoefficient_eq (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.physicalDisplacementCoefficient k m ell).field t x = (G.displacementField k m ell hell
        t).field x := by
  rw [physicalDisplacementCoefficient, physicalCoefficient_apply,
      G.coverDisplacementCoefficient_apply]
  change ell • ((flowData T G.time_nonneg G.A).forward t _ - _).1 =
    ell • (displacement T G.time_nonneg G.A t _).1
  rw [displacement_eq]
  simp only [graphLinear_apply,EulerGraphPullback.graphMap_apply]

theorem physicalVelocityCoefficient_eq (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.physicalVelocityCoefficient k m ell).field t x = (G.velocityField k m ell hell t).field x :=
        by
  rw [physicalVelocityCoefficient,physicalCoefficient_apply,G.coverVelocityCoefficient_apply]
  rfl

theorem physicalAccelerationCoefficient_eq (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.physicalAccelerationCoefficient k m ell).field t x = (G.accelerationFieldL2 k m ell hell
        t).field x := by
  rw [physicalAccelerationCoefficient, physicalCoefficient_apply,
      G.coverAccelerationCoefficient_apply]
  rw [accelerationFamily_apply]
  rfl

end EulerPhysicalGraphFlowBounds.Data

end
end

end

section

/-! The literal child map X(t,Y(t,a)), its actual velocity, and its
actual acceleration, as continuous smooth coefficient paths. -/

@[expose] public section

noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace EulerChildParticleTime

open Set SmoothTimeField

variable {K E : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First term, given by `applyField (P.derivative.compDisplacement D) V`. -/
def firstTerm (P D V : SmoothTimeField K E E) : SmoothTimeField K E E :=
  applyField (P.derivative.compDisplacement D) V

/-- Second term, given by `applyField (applyField (P.derivative.derivative.compDisplacement D)
V) V`. -/
def secondTerm (P D V : SmoothTimeField K E E) : SmoothTimeField K E E :=
  applyField (applyField (P.derivative.derivative.compDisplacement D) V) V

/-- Displacement, given by `(P.compDisplacement D).add D`. -/
def displacement (P D : SmoothTimeField K E E) : SmoothTimeField K E E :=
  (P.compDisplacement D).add D

/-- Velocity, given by `((P₁.compDisplacement D).add D₁).add (firstTerm P D D₁)`. -/
def velocity (P P₁ D D₁ : SmoothTimeField K E E) : SmoothTimeField K E E :=
  ((P₁.compDisplacement D).add D₁).add (firstTerm P D D₁)

/-- Acceleration as an element of `SmoothTimeField K E E`. -/
def acceleration (P P₁ P₂ D D₁ D₂ : SmoothTimeField K E E) : SmoothTimeField K E E :=
  (((((P₂.compDisplacement D).add (firstTerm P₁ D D₁)).add
    (firstTerm P₁ D D₁)).add (secondTerm P D D₁)).add D₂).add (firstTerm P D D₂)

@[simp] theorem firstTerm_apply (P D V : SmoothTimeField K E E) (t : K) (x : E) :
    (firstTerm P D V).field t x = fderiv ℝ (P.field t : E → E) (x+D.field t x) (V.field t x) := by
  change P.derivativeField t (x+D.field t x) (V.field t x) = _
  rw [P.derivativeField_eq]

@[simp] theorem secondTerm_apply (P D V : SmoothTimeField K E E) (t : K) (x : E) :
    (secondTerm P D V).field t x =
      fderiv ℝ (fderiv ℝ (P.field t : E → E)) (x+D.field t x) (V.field t x) (V.field t x) := by
  change P.derivative.derivativeField t (x+D.field t x) (V.field t x) (V.field t x) = _
  rw [P.derivative.derivativeField_eq]
  have he : (P.derivative.field t : E → E →L[ℝ] E) = fderiv ℝ (P.field t : E → E) :=
    funext (P.derivativeField_eq t)
  rw [he]

@[simp] theorem displacement_apply (P D : SmoothTimeField K E E) (t : K) (x : E) :
    (displacement P D).field t x = P.field t (x+D.field t x)+D.field t x := rfl

@[simp] theorem velocity_apply (P P₁ D D₁ : SmoothTimeField K E E) (t : K) (x : E) :
    (velocity P P₁ D D₁).field t x = P₁.field t (x+D.field t x)+D₁.field t x +
      fderiv ℝ (P.field t : E → E) (x+D.field t x) (D₁.field t x) := by
  simp only [velocity,SmoothTimeField.add_apply,compDisplacement_apply,firstTerm_apply]

@[simp] theorem acceleration_apply (P P₁ P₂ D D₁ D₂ : SmoothTimeField K E E) (t : K) (x : E) :
    (acceleration P P₁ P₂ D D₁ D₂).field t x = P₂.field t (x+D.field t x) +
      fderiv ℝ (P₁.field t : E → E) (x+D.field t x) (D₁.field t x) +
      fderiv ℝ (P₁.field t : E → E) (x+D.field t x) (D₁.field t x) +
      fderiv ℝ (fderiv ℝ (P.field t : E → E)) (x+D.field t x) (D₁.field t x) (D₁.field t x) +
      D₂.field t x+fderiv ℝ (P.field t : E → E) (x+D.field t x) (D₂.field t x) := by
  simp only [acceleration, SmoothTimeField.add_apply, compDisplacement_apply, firstTerm_apply,
      secondTerm_apply]

theorem map_composition (P D : SmoothTimeField K E E) (t : K) (x : E) :
    x+(displacement P D).field t x =
      (x+D.field t x)+P.field t (x+D.field t x) := by
  rw [displacement_apply]
  abel

section Time

variable {T : ℝ} {hT : 0 ≤ T} [CompleteSpace E]
  {P P₁ P₂ D D₁ D₂ : SmoothTimeField (Icc (0 : ℝ) T) E E}

theorem displacement_time (hP : TimeDerivative T hT P P₁) (hD : TimeDerivative T hT D D₁) :
    TimeDerivative T hT (displacement P D) (velocity P P₁ D D₁) := by
  have h := (hP.compDisplacement hD).add hD
  apply h.congr_fields (fun _ _ => rfl)
  intro t x
  simp only [velocity,firstTerm,SmoothTimeField.add_apply,applyField_apply,compDisplacement_apply]
  abel

variable [FiniteDimensional ℝ E]

theorem velocity_time (hP : TimeDerivative T hT P P₁) (hP₁ : TimeDerivative T hT P₁ P₂)
    (hD : TimeDerivative T hT D D₁) (hD₁ : TimeDerivative T hT D₁ D₂) :
    TimeDerivative T hT (velocity P P₁ D D₁) (acceleration P P₁ P₂ D D₁ D₂) := by
  have hd := SmoothTimeField.TimeDerivative.derivative T hT P P₁ hP
  have hp := (hd.compDisplacement hD).applyField hD₁
  have h := ((hP₁.compDisplacement hD).add hD₁).add hp
  apply h.congr_fields (fun _ _ => rfl)
  intro t x
  simp only [acceleration, firstTerm, secondTerm, SmoothTimeField.add_apply, applyField_apply,
      compDisplacement_apply,
    _root_.add_apply]
  abel

end Time
end EulerChildParticleTime

end
end

end

section

/-! Initial identity and determinant one for the actual child coefficient
map. These invariants pass directly to the next parent coefficient data. -/

section

/-! Exact Jacobian composition for the child displacement. -/

@[expose] public section

noncomputable section

namespace EulerChildParticleTime

variable {K E : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem displacement_jacobian (P D : SmoothTimeField K E E) (t : K) (x : E) :
    ContinuousLinearMap.id ℝ E + fderiv ℝ ((displacement P D).field t : E → E) x =
      (ContinuousLinearMap.id ℝ E + fderiv ℝ (P.field t : E → E) (x+D.field t x)).comp
        (ContinuousLinearMap.id ℝ E + fderiv ℝ (D.field t : E → E) x) := by
  have hi := (hasFDerivAt_id x).add ((D.smooth t).differentiable (by simp) x).hasFDerivAt
  have ho := (hasFDerivAt_id (x+D.field t x)).add
    ((P.smooth t).differentiable (by simp) (x+D.field t x)).hasFDerivAt
  have hc := ho.comp x hi
  have hh := (hasFDerivAt_id x).add
    (((displacement P D).smooth t).differentiable (by simp) x).hasFDerivAt
  apply hh.unique
  apply hc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y => map_composition P D t y)

theorem displacement_det_one
    (P D : SmoothTimeField K E E) (t : K)
    (hP : ∀ y, (ContinuousLinearMap.id ℝ E + fderiv ℝ (P.field t : E → E) y).det = 1)
    (hD : ∀ y, (ContinuousLinearMap.id ℝ E + fderiv ℝ (D.field t : E → E) y).det = 1)
    (x : E) :
    (ContinuousLinearMap.id ℝ E + fderiv ℝ ((displacement P D).field t : E → E) x).det=1 := by
  rw [displacement_jacobian]
  change LinearMap.det
    ((ContinuousLinearMap.id ℝ E + fderiv ℝ (P.field t : E → E) (x+D.field t x)).toLinearMap.comp
      (ContinuousLinearMap.id ℝ E + fderiv ℝ (D.field t : E → E) x).toLinearMap)=1
  rw [LinearMap.det_comp]
  change (ContinuousLinearMap.id ℝ E + fderiv ℝ (P.field t : E → E) (x+D.field t x)).det *
    (ContinuousLinearMap.id ℝ E + fderiv ℝ (D.field t : E → E) x).det=1
  rw [hP,hD,mul_one]

end EulerChildParticleTime

end
end

end

@[expose] public section

noncomputable section

namespace EulerPhysicalGraphFlowBounds.Data

open Set EulerLiftedGradientSpace EulerSmoothBanachFlow EulerGraphInvariantFlow

variable {P T : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P T)
  (k : ℝ) (m : Vector3) (ell : ℝ)

theorem physicalDisplacementCoefficient_zero (x : Vector3) :
    (G.physicalDisplacementCoefficient k m ell).field ⟨0,le_rfl,G.time_nonneg⟩ x=0 := by
  rw [physicalDisplacementCoefficient, physicalCoefficient_apply,
      G.coverDisplacementCoefficient_apply]
  simp only [(flowData T G.time_nonneg G.A).forward_zero,sub_self,Prod.fst_zero,smul_zero]

theorem physicalDisplacementCoefficient_det_one
    (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0) (hell : 0 < ell)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    (ContinuousLinearMap.id ℝ Vector3 +
      fderiv ℝ ((G.physicalDisplacementCoefficient k m ell).field t : Vector3 → Vector3) x).det=1
          := by
  let C := G.physicalDisplacementCoefficient k m ell
  have he : (fun y => y+C.field t y) =
      (flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t := by
    funext y
    change y+(G.physicalDisplacementCoefficient k m ell).field t y=_
    rw [G.physicalDisplacementCoefficient_eq k m ell hell,
      G.displacementField_eq k m hgraph ell hell,displacement_eq]
    abel
  have hj : fderiv ℝ (fun y => y+C.field t y) x =
      ContinuousLinearMap.id ℝ Vector3 + fderiv ℝ (C.field t : Vector3 → Vector3) x :=
    ((hasFDerivAt_id x).add ((C.smooth t).differentiable (by simp) x).hasFDerivAt).fderiv
  rw [he] at hj
  change (ContinuousLinearMap.id ℝ Vector3 + fderiv ℝ (C.field t : Vector3 → Vector3) x).det=1
  rw [← hj]
  exact forward_det_one T G.time_nonneg (physicalCoefficient k m T G.A ell)
    (physicalCoefficient_trace_zero k m T G.A hgraph G.divergence ell hell.ne') t x

theorem childDisplacementCoefficient_zero
    (PD : SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3)
    (hPD : ∀ x, PD.field ⟨0, le_rfl, G.time_nonneg⟩ x = 0) (x : Vector3) :
    (EulerChildParticleTime.displacement PD (G.physicalDisplacementCoefficient k m ell)).field
      ⟨0,le_rfl,G.time_nonneg⟩ x=0 := by
  rw [EulerChildParticleTime.displacement_apply,G.physicalDisplacementCoefficient_zero,
    add_zero,hPD]

theorem childDisplacementCoefficient_det_one
    (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0) (hell : 0 < ell)
    (PD : SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3)
    (hPD : ∀ t x, (ContinuousLinearMap.id ℝ Vector3 +
      fderiv ℝ (PD.field t : Vector3 → Vector3) x).det = 1)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    (ContinuousLinearMap.id ℝ Vector3 +
      fderiv ℝ
        ((EulerChildParticleTime.displacement PD (G.physicalDisplacementCoefficient k m ell)).field
            t :
          Vector3 → Vector3) x).det=1 :=
  EulerChildParticleTime.displacement_det_one PD (G.physicalDisplacementCoefficient k m ell) t
    (hPD t) (G.physicalDisplacementCoefficient_det_one k m ell hgraph hell t) x

end EulerPhysicalGraphFlowBounds.Data

end
end

end

section

/-! The L² child fields used in the estimates are exactly the actual
first and second time derivatives of the composed particle map. -/

@[expose] public section

noncomputable section

namespace EulerChildParticleTime

open Set EulerSmoothLimit

variable {T : ℝ}

/-- Compatibility of two actual realizations of the six input fields.
These are literal value identities, not derivative or output assumptions. -/
structure Representation (G : Icc (0 : ℝ) T → EulerChildParticleFieldBounds.Data)
    (P P₁ P₂ D D₁ D₂ : SmoothTimeField (Icc (0 : ℝ) T) Space Space) : Prop where
  parentDisplacement : ∀ t x, (G t).parentDisplacement.field x=P.field t x
  parentVelocity : ∀ t x, (G t).parentVelocity.field x=P₁.field t x
  parentAcceleration : ∀ t x, (G t).parentAcceleration.field x=P₂.field t x
  displacement : ∀ t x, (G t).displacement.field x=D.field t x
  velocity : ∀ t x, (G t).velocity.field x=D₁.field t x
  acceleration : ∀ t x, (G t).acceleration.field x=D₂.field t x

namespace Representation

variable {G : Icc (0 : ℝ) T → EulerChildParticleFieldBounds.Data}
  {P P₁ P₂ D D₁ D₂ : SmoothTimeField (Icc (0 : ℝ) T) Space Space}
  (H : Representation G P P₁ P₂ D D₁ D₂)

include H

theorem childDisplacement (t : Icc (0 : ℝ) T) (x : Space) :
    (G t).childDisplacement.field x=(EulerChildParticleTime.displacement P D).field t x := by
  rw [EulerChildParticleFieldBounds.Data.childDisplacement_apply,displacement_apply]
  simp only [EulerChildParticleFieldBounds.Data.inner,H.parentDisplacement,H.displacement]

theorem childVelocity (t : Icc (0 : ℝ) T) (x : Space) :
    (G t).childVelocity.field x=(EulerChildParticleTime.velocity P P₁ D D₁).field t x := by
  rw [EulerChildParticleFieldBounds.Data.childVelocity_apply,velocity_apply]
  have he : (G t).parentDisplacement.field = (P.field t : Space → Space) :=
    funext (H.parentDisplacement t)
  simp only [EulerChildParticleFieldBounds.Data.inner,he,H.parentVelocity,H.displacement,H.velocity]

theorem childAcceleration (t : Icc (0 : ℝ) T) (x : Space) :
    (G t).childAcceleration.field x=(EulerChildParticleTime.acceleration P P₁ P₂ D D₁ D₂).field t x
        := by
  rw [EulerChildParticleFieldBounds.Data.childAcceleration_apply,acceleration_apply]
  have he : (G t).parentDisplacement.field = (P.field t : Space → Space) :=
    funext (H.parentDisplacement t)
  have he₁ : (G t).parentVelocity.field = (P₁.field t : Space → Space) :=
    funext (H.parentVelocity t)
  simp only [EulerChildParticleFieldBounds.Data.inner,he,he₁,
    H.parentAcceleration,H.displacement,H.velocity,H.acceleration]

variable {hT : 0 ≤ T}

theorem displacement_hasDerivWithinAt
    (hP : SmoothTimeField.TimeDerivative T hT P P₁)
    (hD : SmoothTimeField.TimeDerivative T hT D D₁)
    (t : Icc (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt (fun s => (G (projIcc 0 T hT s)).childDisplacement.field x)
      ((G t).childVelocity.field x) (Icc (0 : ℝ) T) t := by
  have he : (fun s => (G (projIcc 0 T hT s)).childDisplacement.field x) =
      (fun s => (EulerChildParticleTime.displacement P D).realField T hT s x) := by
    funext s
    exact H.childDisplacement (projIcc 0 T hT s) x
  rw [he,H.childVelocity]
  exact displacement_time hP hD t x

theorem velocity_hasDerivWithinAt
    (hP : SmoothTimeField.TimeDerivative T hT P P₁)
    (hP₁ : SmoothTimeField.TimeDerivative T hT P₁ P₂)
    (hD : SmoothTimeField.TimeDerivative T hT D D₁)
    (hD₁ : SmoothTimeField.TimeDerivative T hT D₁ D₂)
    (t : Icc (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt (fun s => (G (projIcc 0 T hT s)).childVelocity.field x)
      ((G t).childAcceleration.field x) (Icc (0 : ℝ) T) t := by
  have he : (fun s => (G (projIcc 0 T hT s)).childVelocity.field x) =
      (fun s => (EulerChildParticleTime.velocity P P₁ D D₁).realField T hT s x) := by
    funext s
    exact H.childVelocity (projIcc 0 T hT s) x
  rw [he,H.childAcceleration]
  exact velocity_time hP hP₁ hD hD₁ t x

theorem composition_hasDerivWithinAt
    (hP : SmoothTimeField.TimeDerivative T hT P P₁)
    (hD : SmoothTimeField.TimeDerivative T hT D D₁)
    (t : Icc (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt (fun s =>
      let F := G (projIcc 0 T hT s)
      (x+F.displacement.field x)+F.parentDisplacement.field (x+F.displacement.field x))
      ((G t).childVelocity.field x) (Icc (0 : ℝ) T) t := by
  have h := (H.displacement_hasDerivWithinAt hP hD t x).const_add x
  have he : (fun s => x+(G (projIcc 0 T hT s)).childDisplacement.field x) =
      (fun s =>
        let F := G (projIcc 0 T hT s)
        (x+F.displacement.field x)+F.parentDisplacement.field (x+F.displacement.field x)) := by
    funext s
    rw [EulerChildParticleFieldBounds.Data.childDisplacement_apply]
    simp only [EulerChildParticleFieldBounds.Data.inner]
    abel
  rw [← he]
  exact h

end Representation
end EulerChildParticleTime

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerSmoothBanachFlow
  EulerGraphInvariantFlow EulerPacketVolumeDivergence MeasureTheory

variable (A : EulerParentPacketFrames.Parent)

theorem displacement_det_one (t : Icc (0 : ℝ) A.T) (x : Space) :
    (ContinuousLinearMap.id ℝ Space + fderiv ℝ (A.displacement.field t : Space → Space) x).det=1 :=
        by
  have h := A.determinant t (A.ell⁻¹ • x)
  have hx : A.ell • (A.ell⁻¹ • x)=x := by
    rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  simpa only [hx,operatorMatrix_det] using h

variable {P : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P A.T)
  (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

/-- Child, bundling `T`, `T_pos`, `ell`, `ell_pos` and the required compatibility proofs. -/
def child : EulerParentPacketFrames.Parent where
  T := A.T
  T_pos := A.T_pos
  ell := nextEll
  ell_pos := hnext
  ell_le_one := hnext1
  displacement := EulerChildParticleTime.displacement A.displacement
    (G.physicalDisplacementCoefficient k m A.ell)
  velocity := EulerChildParticleTime.velocity A.displacement A.velocity
    (G.physicalDisplacementCoefficient k m A.ell) (G.physicalVelocityCoefficient k m A.ell)
  acceleration := EulerChildParticleTime.acceleration A.displacement A.velocity A.acceleration
    (G.physicalDisplacementCoefficient k m A.ell) (G.physicalVelocityCoefficient k m A.ell)
    (G.physicalAccelerationCoefficient k m A.ell)
  displacement_time := EulerChildParticleTime.displacement_time A.displacement_time
    (G.physicalDisplacementCoefficient_time k m A.ell)
  velocity_time := EulerChildParticleTime.velocity_time A.displacement_time A.velocity_time
    (G.physicalDisplacementCoefficient_time k m A.ell)
    (G.physicalVelocityCoefficient_time k m A.ell)
  initial := G.childDisplacementCoefficient_zero k m A.ell A.displacement A.initial
  determinant t x := by
    rw [operatorMatrix_det]
    exact G.childDisplacementCoefficient_det_one k m A.ell hgraph A.ell_pos
      A.displacement A.displacement_det_one t (nextEll • x)

theorem child_particleMap (t : Icc (0 : ℝ) A.T) (x : Space) :
    x+(A.child G k m hgraph nextEll hnext hnext1).displacement.field t x =
      let y := (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t x
      y+A.displacement.field t y := by
  change x+(EulerChildParticleTime.displacement A.displacement
    (G.physicalDisplacementCoefficient k m A.ell)).field t x=_
  rw [EulerChildParticleTime.map_composition]
  have hi : x+(G.physicalDisplacementCoefficient k m A.ell).field t x =
      (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t x := by
    rw [G.physicalDisplacementCoefficient_eq k m A.ell A.ell_pos,
      G.displacementField_eq k m hgraph A.ell A.ell_pos,EulerSmoothBanachFlow.displacement_eq]
    abel
  rw [hi]

theorem child_fields_match
    (E : Icc (0 : ℝ) A.T → EulerChildParticleFieldBounds.Data)
    (hD : ∀ t x, (E t).parentDisplacement.field x = A.displacement.field t x)
    (hV : ∀ t x, (E t).parentVelocity.field x = A.velocity.field t x)
    (hW : ∀ t x, (E t).parentAcceleration.field x = A.acceleration.field t x)
    (hd : ∀ t, (E t).displacement = G.displacementField k m A.ell A.ell_pos t)
    (hv : ∀ t, (E t).velocity = G.velocityField k m A.ell A.ell_pos t)
    (hw : ∀ t, (E t).acceleration = G.accelerationFieldL2 k m A.ell A.ell_pos t)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    (E t).childDisplacement.field x=(A.child G k m hgraph nextEll hnext hnext1).displacement.field
        t x ∧
    (E t).childVelocity.field x=(A.child G k m hgraph nextEll hnext hnext1).velocity.field t x ∧
    (E t).childAcceleration.field x=(A.child G k m hgraph nextEll hnext hnext1).acceleration.field
        t x := by
  let H : EulerChildParticleTime.Representation E A.displacement A.velocity A.acceleration
      (G.physicalDisplacementCoefficient k m A.ell)
      (G.physicalVelocityCoefficient k m A.ell)
      (G.physicalAccelerationCoefficient k m A.ell) :=
    { parentDisplacement := hD
      parentVelocity := hV
      parentAcceleration := hW
      displacement := by
        intro u y
        rw [hd]
        exact (G.physicalDisplacementCoefficient_eq k m A.ell A.ell_pos u y).symm
      velocity := by
        intro u y
        rw [hv]
        exact (G.physicalVelocityCoefficient_eq k m A.ell A.ell_pos u y).symm
      acceleration := by
        intro u y
        rw [hw]
        exact (G.physicalAccelerationCoefficient_eq k m A.ell A.ell_pos u y).symm }
  exact ⟨H.childDisplacement t x,H.childVelocity t x,H.childAcceleration t x⟩

/-- Child inverse, given by `(flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A
A.ell)).backward t (Y t x)`. -/
def childInverse (Y : Icc (0 : ℝ) A.T → Space → Space)
    (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).backward t (Y t x)

theorem childInverse_left (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hYX : ∀ t x, Y t (x + A.displacement.field t x) = x)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.childInverse G k m Y t
      (x+(A.child G k m hgraph nextEll hnext hnext1).displacement.field t x)=x := by
  rw [A.child_particleMap G k m hgraph nextEll hnext hnext1]
  change (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).backward t
    (Y t (_+A.displacement.field t _))=x
  rw [hYX]
  exact (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).backward_forward t x

theorem childInverse_right (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hXY : ∀ t x, Y t x + A.displacement.field t (Y t x) = x)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.childInverse G k m Y t x +
      (A.child G k m hgraph nextEll hnext hnext1).displacement.field t
        (A.childInverse G k m Y t x)=x := by
  rw [A.child_particleMap G k m hgraph nextEll hnext hnext1]
  change
    (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t
        ((flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).backward t (Y t x)) +
      A.displacement.field t
        ((flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t
          ((flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).backward t (Y t
              x)))=x
  rw [(flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward_backward]
  exact hXY t x

theorem childInverse_joint_continuous (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hY : Continuous (Function.uncurry Y)) :
    Continuous (Function.uncurry (A.childInverse G k m Y)) :=
  (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A
      A.ell)).backward_joint_continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk hY)

theorem child_particleMap_measurePreserving
    (hparent : ∀ t, MeasurePreserving (fun x => x + A.displacement.field t x) volume volume)
    (t : Icc (0 : ℝ) A.T) :
    MeasurePreserving
      (fun x => x+(A.child G k m hgraph nextEll hnext hnext1).displacement.field t x) volume volume
          := by
  have he : (fun x => x+(A.child G k m hgraph nextEll hnext hnext1).displacement.field t x) =
      (fun y => y+A.displacement.field t y) ∘
        (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t :=
    funext (A.child_particleMap G k m hgraph nextEll hnext hnext1 t)
  rw [he]
  exact (hparent t).comp
    (physical_forward_measurePreserving k m A.T G.time_nonneg G.A hgraph G.divergence
      A.ell A.ell_pos.ne' t)

end EulerParentPacketFrames.Parent
