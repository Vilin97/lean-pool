/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldChain

@[expose] public section

/-! The literal child map X(t,Y(t,a)), its actual velocity, and its
actual acceleration, as continuous smooth coefficient paths. -/

noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace EulerChildParticleTime

open Set SmoothTimeField

variable {K E : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def firstTerm (P D V : SmoothTimeField K E E) : SmoothTimeField K E E :=
  applyField (P.derivative.compDisplacement D) V

def secondTerm (P D V : SmoothTimeField K E E) : SmoothTimeField K E E :=
  applyField (applyField (P.derivative.derivative.compDisplacement D) V) V

def displacement (P D : SmoothTimeField K E E) : SmoothTimeField K E E :=
  (P.compDisplacement D).add D

def velocity (P P₁ D D₁ : SmoothTimeField K E E) : SmoothTimeField K E E :=
  ((P₁.compDisplacement D).add D₁).add (firstTerm P D D₁)

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
    (velocity P P₁ D D₁).field t x = P₁.field t (x+D.field t x)+D₁.field t x+
      fderiv ℝ (P.field t : E → E) (x+D.field t x) (D₁.field t x) := by
  simp only [velocity,SmoothTimeField.add_apply,compDisplacement_apply,firstTerm_apply]

@[simp] theorem acceleration_apply (P P₁ P₂ D D₁ D₂ : SmoothTimeField K E E) (t : K) (x : E) :
    (acceleration P P₁ P₂ D D₁ D₂).field t x = P₂.field t (x+D.field t x)+
      fderiv ℝ (P₁.field t : E → E) (x+D.field t x) (D₁.field t x)+
      fderiv ℝ (P₁.field t : E → E) (x+D.field t x) (D₁.field t x)+
      fderiv ℝ (fderiv ℝ (P.field t : E → E)) (x+D.field t x) (D₁.field t x) (D₁.field t x)+
      D₂.field t x+fderiv ℝ (P.field t : E → E) (x+D.field t x) (D₂.field t x) := by
  simp only [acceleration,SmoothTimeField.add_apply,compDisplacement_apply,firstTerm_apply,secondTerm_apply]

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
  simp only [acceleration,firstTerm,secondTerm,SmoothTimeField.add_apply,applyField_apply,compDisplacement_apply,
    _root_.add_apply]
  abel

end Time
end EulerChildParticleTime
