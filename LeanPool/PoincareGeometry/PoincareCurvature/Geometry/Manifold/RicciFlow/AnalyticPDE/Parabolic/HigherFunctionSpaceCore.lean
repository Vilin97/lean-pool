/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FunctionSpace
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Core higher parabolic Holder definitions

This lightweight module contains the foundational second-jet and
`C^{2+α,1+α/2}` predicates.  Keeping these definitions separate from the
large algebraic/compact-readout development lets analytic endpoint modules use
the generic interface without importing unrelated optional infrastructure.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE

/-- Time slice of a time-space set at a fixed spatial point. -/
def timeSliceDomain {X : Type*} (s : Set (ℝ × X)) (x : X) : Set ℝ :=
  {t | (t, x) ∈ s}

/-- Spatial slice of a time-space set at a fixed time. -/
def spaceSliceDomain {X : Type*} (s : Set (ℝ × X)) (t : ℝ) : Set X :=
  {x | (t, x) ∈ s}

@[simp]
theorem mem_timeSliceDomain {X : Type*} {s : Set (ℝ × X)} {x : X} {t : ℝ} :
    t ∈ timeSliceDomain s x ↔ (t, x) ∈ s :=
  Iff.rfl

@[simp]
theorem mem_spaceSliceDomain {X : Type*} {s : Set (ℝ × X)} {t : ℝ} {x : X} :
    x ∈ spaceSliceDomain s t ↔ (t, x) ∈ s :=
  Iff.rfl

variable {X E : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A coordinate parabolic second jet for a time-space function on a domain.
The fields are genuine derivative witnesses on the natural time and spatial
slices of the domain. -/
structure ParabolicSecondJet (u : ℝ × X → E) (s : Set (ℝ × X)) where
  timeDeriv : ℝ × X → E
  spaceDeriv : ℝ × X → X →L[ℝ] E
  spaceSecondDeriv : ℝ × X → X →L[ℝ] (X →L[ℝ] E)
  hasTimeDeriv : ∀ ⦃z : ℝ × X⦄, z ∈ s →
    HasDerivWithinAt (fun t : ℝ => u (t, z.2)) (timeDeriv z)
      (timeSliceDomain s z.2) z.1
  hasSpaceDeriv : ∀ ⦃z : ℝ × X⦄, z ∈ s →
    HasFDerivWithinAt (fun x : X => u (z.1, x)) (spaceDeriv z)
      (spaceSliceDomain s z.1) z.2
  hasSpaceSecondDeriv : ∀ ⦃z : ℝ × X⦄, z ∈ s →
    HasFDerivWithinAt (fun x : X => spaceDeriv (z.1, x)) (spaceSecondDeriv z)
      (spaceSliceDomain s z.1) z.2

namespace ParabolicSecondJet

/-- Restrict a parabolic second jet to a smaller time-space domain. -/
def restrict {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (J : ParabolicSecondJet u s) (hst : t ⊆ s) :
    ParabolicSecondJet u t where
  timeDeriv := J.timeDeriv
  spaceDeriv := J.spaceDeriv
  spaceSecondDeriv := J.spaceSecondDeriv
  hasTimeDeriv := by
    intro z hz
    refine (J.hasTimeDeriv (hst hz)).mono ?_
    intro τ hτ
    exact hst hτ
  hasSpaceDeriv := by
    intro z hz
    refine (J.hasSpaceDeriv (hst hz)).mono ?_
    intro x hx
    exact hst hx
  hasSpaceSecondDeriv := by
    intro z hz
    refine (J.hasSpaceSecondDeriv (hst hz)).mono ?_
    intro x hx
    exact hst hx

end ParabolicSecondJet

/-- Coordinate parabolic `C^{2+α,1+α/2}` single-radius control.  The
radius dominates the sum of the value, spatial derivative, spatial Hessian,
and time-derivative `C^{0,α}` radii of one genuine second jet. -/
def ParabolicC2AlphaNormLe (N α : ℝ) (u : ℝ × X → E) (s : Set (ℝ × X)) : Prop :=
  ∃ J : ParabolicSecondJet u s,
    ∃ Nu ≥ 0, ∃ Nx ≥ 0, ∃ Nxx ≥ 0, ∃ Nt ≥ 0,
      Nu + Nx + Nxx + Nt ≤ N ∧
        ParabolicC0AlphaNormLe Nu α u s ∧
        ParabolicC0AlphaNormLe Nx α J.spaceDeriv s ∧
        ParabolicC0AlphaNormLe Nxx α J.spaceSecondDeriv s ∧
        ParabolicC0AlphaNormLe Nt α J.timeDeriv s

namespace ParabolicC2AlphaNormLe

/-- Every admissible `C^{2+α,1+α/2}` control radius is nonnegative. -/
theorem nonneg {N α : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (h : ParabolicC2AlphaNormLe N α u s) : 0 ≤ N := by
  rcases h with ⟨_J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, _⟩
  have : 0 ≤ Nu + Nx + Nxx + Nt := by positivity
  exact this.trans hsum

/-- Enlarge the numerical radius of a `C^{2+α,1+α/2}` bound. -/
theorem mono_const {N₁ N₂ α : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (h : ParabolicC2AlphaNormLe N₁ α u s) (hNN : N₁ ≤ N₂) :
    ParabolicC2AlphaNormLe N₂ α u s := by
  rcases h with ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum,
    hu, hx, hxx, ht⟩
  exact ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt,
    hsum.trans hNN, hu, hx, hxx, ht⟩

/-- Package four `C^{0,α}` component bounds around one genuine second jet. -/
theorem of_secondJet {N α : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    {J : ParabolicSecondJet u s} {Nu Nx Nxx Nt : ℝ}
    (hNu : 0 ≤ Nu) (hNx : 0 ≤ Nx) (hNxx : 0 ≤ Nxx) (hNt : 0 ≤ Nt)
    (hu : ParabolicC0AlphaNormLe Nu α u s)
    (hx : ParabolicC0AlphaNormLe Nx α J.spaceDeriv s)
    (hxx : ParabolicC0AlphaNormLe Nxx α J.spaceSecondDeriv s)
    (ht : ParabolicC0AlphaNormLe Nt α J.timeDeriv s) :
    ParabolicC2AlphaNormLe (Nu + Nx + Nxx + Nt) α u s := by
  exact ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, le_rfl, hu, hx, hxx, ht⟩

end ParabolicC2AlphaNormLe

end AnalyticPDE
end RicciFlow
