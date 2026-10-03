/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Solutions

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Basic Dirichlet and Perron predicates

This file contains the small shared vocabulary for Perron's method. It is
deliberately independent of the concrete comparison proof and of the
Aleksandrov/Jensen analysis files: Perron's method takes comparison as an
abstract hypothesis.
-/

@[expose] public noncomputable section

namespace ViscositySolns

variable {n : Nat}

/-- Boundary inequality for a Dirichlet subsolution. -/
def BoundarySubsolutionOn (boundary : Set (Point n)) (g u : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ boundary -> u x <= g x

/-- Boundary inequality for a Dirichlet supersolution. -/
def BoundarySupersolutionOn (boundary : Set (Point n)) (g u : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ boundary -> g x <= u x

/-- Boundary equality for a Dirichlet solution. -/
def BoundarySolutionOn (boundary : Set (Point n)) (g u : Point n -> Real) : Prop :=
  Set.EqOn u g boundary

/--
A viscosity subsolution with the Dirichlet boundary inequality and upper
semicontinuity up to the boundary on `C ∪ boundary`.

The set `C` is the PDE domain used by the existing viscosity predicates, while
`boundary` is kept separate so Section 4's strict boundary condition can be
assembled without forcing a specific closure encoding.
-/
def DirichletSubsolutionOn (C boundary : Set (Point n)) (F : Operator n)
    (g u : Point n -> Real) : Prop :=
  ViscositySubsolution C F u ∧ BoundarySubsolutionOn boundary g u ∧
    UpperSemicontinuousOn u (C ∪ boundary)

/-- A viscosity supersolution with the Dirichlet boundary inequality and lower
semicontinuity up to the boundary on `C ∪ boundary`. -/
def DirichletSupersolutionOn (C boundary : Set (Point n)) (F : Operator n)
    (g u : Point n -> Real) : Prop :=
  ViscositySupersolution C F u ∧ BoundarySupersolutionOn boundary g u ∧
    LowerSemicontinuousOn u (C ∪ boundary)

/-- A viscosity solution with equality on the Dirichlet boundary. -/
def DirichletSolutionOn (C boundary : Set (Point n)) (F : Operator n)
    (g u : Point n -> Real) : Prop :=
  ViscositySolution C F u ∧ BoundarySolutionOn boundary g u

theorem DirichletSubsolutionOn.viscosity
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hu : DirichletSubsolutionOn C boundary F g u) :
    ViscositySubsolution C F u :=
  hu.1

theorem DirichletSubsolutionOn.boundary
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hu : DirichletSubsolutionOn C boundary F g u) :
    BoundarySubsolutionOn boundary g u :=
  hu.2.1

theorem DirichletSubsolutionOn.upperSemicontinuousOn
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hu : DirichletSubsolutionOn C boundary F g u) :
    UpperSemicontinuousOn u (C ∪ boundary) := hu.2.2

theorem DirichletSubsolutionOn.boundary_le
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hu : DirichletSubsolutionOn C boundary F g u) {x : Point n} (hx : x ∈ boundary) :
    u x <= g x :=
  hu.boundary x hx

theorem ViscositySubsolution.congr_eqOn
    {C : Set (Point n)} {F : Operator n} {u v : Point n -> Real}
    (hu : ViscositySubsolution C F u) (h : Set.EqOn u v C) :
    ViscositySubsolution C F v := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact UpperSemicontinuousWithinAt.congr_of_eventuallyEq
      (hu.1 x hx) hx h.eventuallyEq_nhdsWithin
  · intro x hx J hJ
    have hJu : J ∈ Superjet C u x := by
      simpa [superjet_congr_eqOn h hx] using hJ
    simpa [h hx] using hu.2 x hx J hJu

theorem ViscositySupersolution.congr_eqOn
    {C : Set (Point n)} {F : Operator n} {u v : Point n -> Real}
    (hu : ViscositySupersolution C F u) (h : Set.EqOn u v C) :
    ViscositySupersolution C F v := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact LowerSemicontinuousWithinAt.congr_of_eventuallyEq
      (hu.1 x hx) hx h.eventuallyEq_nhdsWithin
  · intro x hx J hJ
    have hJu : J ∈ Subjet C u x := by
      simpa [subjet_congr_eqOn h hx] using hJ
    simpa [h hx] using hu.2 x hx J hJu

theorem DirichletSubsolutionOn.congr_eqOn
    {C boundary : Set (Point n)} {F : Operator n} {g u v : Point n -> Real}
    (hu : DirichletSubsolutionOn C boundary F g u)
    (hC : Set.EqOn u v C) (hboundary : Set.EqOn u v boundary) :
    DirichletSubsolutionOn C boundary F g v := by
  refine ⟨hu.viscosity.congr_eqOn hC, ?_, ?_⟩
  · intro x hx
    simpa [hboundary hx] using hu.boundary_le hx
  · intro x hx
    have hUnion : Set.EqOn u v (C ∪ boundary) := by
      intro z hz
      rcases hz with hz | hz
      · exact hC hz
      · exact hboundary hz
    exact UpperSemicontinuousWithinAt.congr_of_eventuallyEq
      (hu.upperSemicontinuousOn x hx) hx
      hUnion.eventuallyEq_nhdsWithin

theorem DirichletSupersolutionOn.viscosity
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hu : DirichletSupersolutionOn C boundary F g u) :
    ViscositySupersolution C F u :=
  hu.1

theorem DirichletSupersolutionOn.boundary
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hu : DirichletSupersolutionOn C boundary F g u) :
    BoundarySupersolutionOn boundary g u :=
  hu.2.1

theorem DirichletSupersolutionOn.lowerSemicontinuousOn
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hu : DirichletSupersolutionOn C boundary F g u) :
    LowerSemicontinuousOn u (C ∪ boundary) := hu.2.2

theorem DirichletSupersolutionOn.boundary_le
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hu : DirichletSupersolutionOn C boundary F g u) {x : Point n} (hx : x ∈ boundary) :
    g x <= u x :=
  hu.boundary x hx

theorem DirichletSupersolutionOn.congr_eqOn
    {C boundary : Set (Point n)} {F : Operator n} {g u v : Point n -> Real}
    (hu : DirichletSupersolutionOn C boundary F g u)
    (hC : Set.EqOn u v C) (hboundary : Set.EqOn u v boundary) :
    DirichletSupersolutionOn C boundary F g v := by
  refine ⟨hu.viscosity.congr_eqOn hC, ?_, ?_⟩
  · intro x hx
    simpa [hboundary hx] using hu.boundary_le hx
  · intro x hx
    have hUnion : Set.EqOn u v (C ∪ boundary) := by
      intro z hz
      rcases hz with hz | hz
      · exact hC hz
      · exact hboundary hz
    exact LowerSemicontinuousWithinAt.congr_of_eventuallyEq
      (hu.lowerSemicontinuousOn x hx) hx
      hUnion.eventuallyEq_nhdsWithin

theorem DirichletSolutionOn.viscosity
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hu : DirichletSolutionOn C boundary F g u) :
    ViscositySolution C F u :=
  hu.1

theorem DirichletSolutionOn.boundary
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hu : DirichletSolutionOn C boundary F g u) :
    BoundarySolutionOn boundary g u :=
  hu.2

theorem DirichletSolutionOn.boundary_eq
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hu : DirichletSolutionOn C boundary F g u) {x : Point n} (hx : x ∈ boundary) :
    u x = g x :=
  hu.boundary hx

/--
Abstract Dirichlet comparison principle used by Perron's method.

Concrete comparison theorems should later prove adapters into this predicate;
the Perron proof itself should only consume this hypothesis.
-/
def DirichletComparisonPrinciple (C boundary : Set (Point n)) (F : Operator n)
    (g : Point n -> Real) : Prop :=
  ∀ {u v : Point n -> Real},
    DirichletSubsolutionOn C boundary F g u ->
      DirichletSupersolutionOn C boundary F g v ->
        ∀ x : Point n, x ∈ C ∪ boundary -> u x <= v x

/--
A lower and upper barrier pair for the Dirichlet problem, including the order
relation needed to make the Perron class nonempty and bounded.
-/
structure DirichletBarrierPair (C boundary : Set (Point n)) (F : Operator n)
    (g : Point n -> Real) where
  /-- Lower Dirichlet barrier bounding the Perron family. -/
  lower : Point n -> Real
  /-- Upper Dirichlet barrier bounding the Perron family. -/
  upper : Point n -> Real
  lower_dirichlet : DirichletSubsolutionOn C boundary F g lower
  upper_dirichlet : DirichletSupersolutionOn C boundary F g upper
  lower_le_upper : ∀ x : Point n, x ∈ C ∪ boundary -> lower x <= upper x

/--
Membership in the Perron family between a lower and an upper barrier.

The pointwise envelope is formed from all such `w`.
-/
def PerronClass (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (lower upper w : Point n -> Real) : Prop :=
  DirichletSubsolutionOn C boundary F g w ∧
    (∀ x : Point n, x ∈ C ∪ boundary -> lower x <= w x) ∧
      (∀ x : Point n, x ∈ C ∪ boundary -> w x <= upper x)

/-- The pointwise Perron envelope of all admissible subsolutions. -/
def perronEnvelope (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (lower upper : Point n -> Real) : Point n -> Real :=
  fun x => sSup {r : Real | ∃ w : Point n -> Real,
    PerronClass C boundary F g lower upper w ∧ r = w x}

theorem PerronClass.dirichletSubsolution
    {C boundary : Set (Point n)} {F : Operator n} {g lower upper w : Point n -> Real}
    (hw : PerronClass C boundary F g lower upper w) :
    DirichletSubsolutionOn C boundary F g w :=
  hw.1

theorem PerronClass.lower_le
    {C boundary : Set (Point n)} {F : Operator n} {g lower upper w : Point n -> Real}
    (hw : PerronClass C boundary F g lower upper w) {x : Point n}
    (hx : x ∈ C ∪ boundary) :
    lower x <= w x :=
  hw.2.1 x hx

theorem PerronClass.le_upper
    {C boundary : Set (Point n)} {F : Operator n} {g lower upper w : Point n -> Real}
    (hw : PerronClass C boundary F g lower upper w) {x : Point n}
    (hx : x ∈ C ∪ boundary) :
    w x <= upper x :=
  hw.2.2 x hx

theorem DirichletBarrierPair.lower_mem_perronClass
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) :
    PerronClass C boundary F g B.lower B.upper B.lower := by
  refine ⟨B.lower_dirichlet, ?_, B.lower_le_upper⟩
  intro x _hx
  rfl

end ViscositySolns
