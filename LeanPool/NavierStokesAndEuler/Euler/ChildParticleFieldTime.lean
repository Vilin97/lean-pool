/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleTime
public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleFieldBounds

@[expose] public section

/-! The L² child fields used in the estimates are exactly the actual
first and second time derivatives of the composed particle map. -/

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
