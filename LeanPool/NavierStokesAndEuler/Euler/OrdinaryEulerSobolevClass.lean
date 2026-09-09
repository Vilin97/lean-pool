/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerConcatenation

@[expose] public section

/-! Characterization of the ordinary smooth Euler class by its actual
velocity alone. Pressure regularity follows from the projected equation.
Every solution has one continuous strong time derivative in every
spatial Sobolev order. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSolenoidal EulerVolterraConvolution EulerSmoothFieldSobolevTime

variable {T : ℝ} {hT : 0 ≤ T}

def IsSmoothProjectedEuler (A : Icc (0 : ℝ) T → SmoothL2Field Space) : Prop :=
  (∀ n, Continuous (fun t => (A t).jetLp n)) ∧
  (∀ t, (A t).toLp ∈ solenoidalSpace) ∧
  (∀ t (ht : t ∈ Ioo 0 T),
    HasDerivAt (fun r => (A (projIcc 0 T hT r)).toLp)
      (projectedRhs (A ⟨t,ht.1.le,ht.2.le⟩)).toLp t)

def evolutionOfProjectedEquation (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : IsSmoothProjectedEuler (hT := hT) A) : Evolution T hT where
  velocity := A
  pressureForce t := pressureField (A t)
  velocity_continuous := hA.1
  pressure_continuous := pressureField_continuous A hA.1
  solenoidal := hA.2.1
  gradient t := pressureField_mem_gradient (A t)
  time_law t ht x := by
    have h := pointwise_derivative_of_l2 T hT A (fun s => projectedRhs (A s)) hA.1
      (projectedRhs_continuous A hA.1) hA.2.2 ⟨t,ht.1.le,ht.2.le⟩ x
    simpa only [projectedRhs_field] using h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem Evolution.isSmoothProjectedEuler (U : Evolution T hT) (hpos : 0 < T) :
    IsSmoothProjectedEuler (hT := hT) U.velocity := by
  refine ⟨U.velocity_continuous,U.solenoidal,?_⟩
  intro t ht
  exact (U.velocity_toLp_hasDerivWithinAt_projected hpos ⟨t,ht.1.le,ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

theorem exists_evolution_iff_projected (hpos : 0 < T)
    (A : Icc (0 : ℝ) T → SmoothL2Field Space) :
    (∃ U : Evolution T hT, U.velocity=A) ↔ IsSmoothProjectedEuler (hT := hT) A := by
  constructor
  · rintro ⟨U,rfl⟩
    exact U.isSmoothProjectedEuler hpos
  · intro hA
    exact ⟨evolutionOfProjectedEquation A hA,rfl⟩

theorem Evolution.sobolevTimeDerivative (U : Evolution T hT) (q : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (sobolevPath U.velocity U.velocity_continuous q))
      (sobolevPath U.derivative U.derivative_continuous q t) (Icc (0 : ℝ) T) t := by
  apply sobolev_derivative_of_l2 T hT U.velocity U.derivative U.velocity_continuous
    U.derivative_continuous _ q t
  intro r hr
  have h := U.velocityPath_hasDerivWithinAt ⟨r,hr.1.le,hr.2.le⟩
  rw [U.velocityPath_extend] at h
  exact h.hasDerivAt (Icc_mem_nhds hr.1 hr.2)

theorem Evolution.sobolevSolutionClass (U : Evolution T hT) (q : ℕ) :
    Continuous (sobolevPath U.velocity U.velocity_continuous q) ∧
      Continuous (sobolevPath U.derivative U.derivative_continuous q) ∧
      ∀ t : Icc (0 : ℝ) T,
        HasDerivWithinAt (extendPath T hT (sobolevPath U.velocity U.velocity_continuous q))
          (sobolevPath U.derivative U.derivative_continuous q t) (Icc (0 : ℝ) T) t :=
  ⟨(sobolevPath U.velocity U.velocity_continuous q).continuous,
    (sobolevPath U.derivative U.derivative_continuous q).continuous,
    U.sobolevTimeDerivative q⟩

end EulerOrdinarySobolev
