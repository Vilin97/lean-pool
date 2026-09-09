/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.Support

@[expose] public section

/-!
# The whole-space assertion of Part II, Theorem 1.1

This module states the R³ theorem, including its comparison claim, independently
of the existing periodic target. The coordinates, Euclidean norm, and differential
operators are those of `NavierStokes.ProblemStatement`; no periodicity assumption
is made here. Time is the first coordinate of spacetime.

The force is a globally smooth function whose topological support is compact and
contained in strictly positive time. This represents the zero extension of an
element of `C_c^∞(R³ × (0, ∞); R³)` and, in particular, requires support separated
from initial time as well as from spatial and future-time infinity.

Smoothness of velocity and pressure at time zero is relative to the physical
half-domain. The equation uses ordinary derivatives at positive times; zero
initial velocity is imposed separately. This avoids differentiating an arbitrary
extension to negative time at the boundary. `∞` in the `ContDiff` scope means
every finite differentiability order.

`breakdownStatement` is the full proposition to prove. Introducing it does not
assert that it has a proof or supply a witness.
-/


noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace NavierStokesR3.ProblemStatement

/-- R³ with its ordinary Euclidean norm. -/
abbrev Space := NavierStokes.ProblemStatement.Space

/-- Spacetime, with time first. -/
abbrev SpaceTime := NavierStokes.ProblemStatement.SpaceTime

abbrev VelocityField := NavierStokes.ProblemStatement.VelocityField
abbrev PressureField := NavierStokes.ProblemStatement.PressureField

/-- The physical domain before the asserted singular time. -/
abbrev preSingularDomain := NavierStokes.ProblemStatement.preSingularDomain

/-- The physical domain for a global competing solution. -/
abbrev futureDomain := NavierStokes.ProblemStatement.futureDomain

/-- The open set in which the prescribed force must have compact support. -/
def positiveTimeDomain : Set SpaceTime := Ioi 0 ×ˢ univ

/-- The exact incompressible Navier--Stokes residual at viscosity `ν`.
The viscosity multiplies only the spatial Laplacian. -/
def navierStokesResidual (ν : ℝ) (u : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space) : Space :=
  NavierStokes.ProblemStatement.temporalDerivative u t x +
    NavierStokes.ProblemStatement.advection u t x -
    ν • NavierStokes.ProblemStatement.spatialLaplacian u t x +
    NavierStokes.ProblemStatement.pressureGradient p t x

/-- Compact spacetime support contained in `t > 0`, using the closure of the
nonzero set. Together with global smoothness this is the required force class. -/
def CompactPositiveTimeSupport (f : VelocityField) : Prop :=
  HasCompactSupport f ∧ tsupport f ⊆ positiveTimeDomain

/-- Square integrability with respect to ordinary Lebesgue volume on R³.
This condition is explicit because the real Bochner integral is totalized. -/
def SquareIntegrableAtTime (u : VelocityField) (t : ℝ) : Prop :=
  Integrable (fun x : Space => ‖u (t, x)‖ ^ 2) (volume : Measure Space)

/-- Kinetic energy at a time. It is used below only together with the explicit
integrability condition `SquareIntegrableAtTime`. -/
def kineticEnergy (u : VelocityField) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : Space, ‖u (t, x)‖ ^ 2 ∂(volume : Measure Space)

/-- One finite bound for the kinetic energy at every time in `times`, with
square integrability required at every such time. -/
def UniformFiniteEnergy (times : Set ℝ) (u : VelocityField) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ times,
    SquareIntegrableAtTime u t ∧ kineticEnergy u t ≤ E

/-- Pointwise unbounded speed in every left neighborhood of time one. For the
continuous, compactly supported spatial slices in `CandidateProperties`, this
expresses the L∞ blow-up assertion of Theorem 1.1. -/
abbrev SpeedUnboundedAtOne := NavierStokes.ProblemStatement.SpeedUnboundedAtOne

/-- The properties of the constructed fields in Theorem 1.1. The same single
compact set `K` contains both spatial supports for every `0 ≤ t < 1`. -/
structure CandidateProperties (ν : ℝ) (u : VelocityField) (p : PressureField)
    (f : VelocityField) (K : Set Space) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ u preSingularDomain
  pressure_smooth : ContDiffOn ℝ ∞ p preSingularDomain
  support_compact : IsCompact K
  velocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => u (t, x)) ⊆ K
  pressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => p (t, x)) ⊆ K
  force_smooth : ContDiff ℝ ∞ f
  force_support : CompactPositiveTimeSupport f
  zero_initial_velocity : ∀ x : Space, u (0, x) = 0
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
    NavierStokes.ProblemStatement.spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
    navierStokesResidual ν u p t x = f (t, x)
  energy_bounded : UniformFiniteEnergy (Ico 0 1) u
  speed_unbounded : SpeedUnboundedAtOne u

/-- Data realizing the primary existence assertion at one viscosity. -/
structure Candidate (ν : ℝ) where
  velocity : VelocityField
  pressure : PressureField
  force : VelocityField
  support : Set Space
  properties : CandidateProperties ν velocity pressure force support

/-- A global smooth solution with uniformly bounded kinetic energy for the
given viscosity and the given force, starting from the same zero datum.

There are no support, periodicity, pressure-growth, derivative-growth, or energy
inequality assumptions on a competitor. The square-integrability requirement
and its uniform energy bound use all of R³ and all nonnegative times. -/
structure GlobalFiniteEnergySolution (ν : ℝ) (f : VelocityField) where
  velocity : VelocityField
  pressure : PressureField
  velocity_smooth : ContDiffOn ℝ ∞ velocity futureDomain
  pressure_smooth : ContDiffOn ℝ ∞ pressure futureDomain
  zero_initial_velocity : ∀ x : Space, velocity (0, x) = 0
  divergence_free : ∀ t ∈ Ici (0 : ℝ), ∀ x : Space,
    NavierStokes.ProblemStatement.spatialDivergence velocity t x = 0
  navier_stokes : ∀ t ∈ Ioi (0 : ℝ), ∀ x : Space,
    navierStokesResidual ν velocity pressure t x = f (t, x)
  energy_bounded : UniformFiniteEnergy (Ici 0) velocity

/-- The primary existence assertion at one fixed viscosity. -/
def candidateStatement (ν : ℝ) : Prop :=
  ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
    CandidateProperties ν u p f K

/-- The primary existence assertion for every positive viscosity. -/
def coreBreakdownStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → candidateStatement ν

/-- The full assertion of Theorem 1.1: at every positive viscosity there is a
candidate whose same prescribed force and zero datum have no global smooth
solution with uniformly bounded kinetic energy. This is a target proposition,
not an asserted theorem. -/
def breakdownStatement : Prop :=
  ∀ ν : ℝ, 0 < ν →
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧ ¬ Nonempty (GlobalFiniteEnergySolution ν f)

/-- Bundling the witnesses in `Candidate` does not change any hypothesis of
the explicit primary existence assertion. -/
theorem candidateStatement_iff_nonempty (ν : ℝ) :
    candidateStatement ν ↔ Nonempty (Candidate ν) := by
  constructor
  · rintro ⟨u, p, f, K, h⟩
    exact ⟨⟨u, p, f, K, h⟩⟩
  · rintro ⟨c⟩
    exact ⟨c.velocity, c.pressure, c.force, c.support, c.properties⟩

/-- The unit-viscosity residual is exactly the existing differential expression. -/
@[simp] theorem residual_at_viscosity_one (u : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space) :
    navierStokesResidual 1 u p t x =
      NavierStokes.ProblemStatement.navierStokesResidual u p t x := by
  simp [navierStokesResidual, NavierStokes.ProblemStatement.navierStokesResidual]

/-- The support convention really excludes forcing at every nonpositive time. -/
theorem CompactPositiveTimeSupport.eq_zero_of_nonpos {f : VelocityField}
    (hf : CompactPositiveTimeSupport f) {t : ℝ} (ht : t ≤ 0) (x : Space) :
    f (t, x) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact (not_lt_of_ge ht) (hf.2 h).1

/-- Restricting the set of times preserves the same energy bound. -/
theorem UniformFiniteEnergy.mono {times shorter : Set ℝ} {u : VelocityField}
    (hu : UniformFiniteEnergy times u) (hsub : shorter ⊆ times) :
    UniformFiniteEnergy shorter u := by
  obtain ⟨E, hE, hu⟩ := hu
  exact ⟨E, hE, fun t ht => hu t (hsub ht)⟩

/-- Zero velocity and pressure solve the equation for zero force at any
viscosity. This checks that the competing-solution class is inhabited. -/
theorem zero_force_has_global_solution (ν : ℝ) :
    Nonempty (GlobalFiniteEnergySolution ν (fun _ => 0)) := by
  refine ⟨{
    velocity := fun _ => 0
    pressure := fun _ => 0
    velocity_smooth := contDiff_const.contDiffOn
    pressure_smooth := contDiff_const.contDiffOn
    zero_initial_velocity := fun _ => rfl
    divergence_free := ?_
    navier_stokes := ?_
    energy_bounded := ?_
  }⟩
  · intro t ht x
    simp [NavierStokes.ProblemStatement.spatialDivergence,
      NavierStokes.ProblemStatement.spatialDerivative]
  · intro t ht x
    simp [navierStokesResidual, NavierStokes.ProblemStatement.temporalDerivative,
      NavierStokes.ProblemStatement.advection,
      NavierStokes.ProblemStatement.spatialLaplacian,
      NavierStokes.ProblemStatement.spatialDerivative,
      NavierStokes.ProblemStatement.pressureGradient]
  · refine ⟨0, le_refl 0, ?_⟩
    intro t ht
    constructor
    · simp [SquareIntegrableAtTime]
    · simp [kineticEnergy]

/-- The full target contains the primary candidate-existence target. -/
theorem breakdown_implies_core (h : breakdownStatement) : coreBreakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, _⟩ := h ν hν
  exact ⟨u, p, f, K, hc⟩

end NavierStokesR3.ProblemStatement
