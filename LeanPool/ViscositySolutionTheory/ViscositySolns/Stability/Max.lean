/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Solutions

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Stability under finite maxima and minima

This file proves the first finite lattice stability results for viscosity
solutions: maxima of subsolutions and minima of supersolutions.
-/

@[expose] public noncomputable section

namespace ViscositySolns

variable {n : Nat}

/--
The pointwise maximum of two viscosity subsolutions of the same equation is a
viscosity subsolution. No properness hypothesis is needed for this finite
same-operator statement, because every contact point has an active branch with
the same value.
-/
theorem ViscositySubsolution.max {C : Set (Point n)} {F : Operator n}
    {u v : Point n -> Real}
    (hu : ViscositySubsolution C F u) (hv : ViscositySubsolution C F v) :
    ViscositySubsolution C F (fun y => Max.max (u y) (v y)) := by
  refine ⟨?_, ?_⟩
  · exact hu.1.sup hv.1
  · intro x hx J hJ
    by_cases huv : u x <= v x
    · have hactive : Max.max (u x) (v x) = v x := max_eq_right huv
      have hJv : J ∈ Superjet C v x := superjet_max_of_right hJ hactive
      simpa [hactive] using hv.2 x hx J hJv
    · have hvu : v x <= u x := le_of_lt (lt_of_not_ge huv)
      have hactive : Max.max (u x) (v x) = u x := max_eq_left hvu
      have hJu : J ∈ Superjet C u x := superjet_max_of_left hJ hactive
      simpa [hactive] using hu.2 x hx J hJu

/--
The pointwise minimum of two viscosity supersolutions of the same equation is a
viscosity supersolution.
-/
theorem ViscositySupersolution.min {C : Set (Point n)} {F : Operator n}
    {u v : Point n -> Real}
    (hu : ViscositySupersolution C F u) (hv : ViscositySupersolution C F v) :
    ViscositySupersolution C F (fun y => Min.min (u y) (v y)) := by
  refine ⟨?_, ?_⟩
  · exact hu.1.inf hv.1
  · intro x hx J hJ
    by_cases huv : u x <= v x
    · have hactive : Min.min (u x) (v x) = u x := min_eq_left huv
      have hJu : J ∈ Subjet C u x := subjet_min_of_left hJ hactive
      simpa [hactive] using hu.2 x hx J hJu
    · have hvu : v x <= u x := le_of_lt (lt_of_not_ge huv)
      have hactive : Min.min (u x) (v x) = v x := min_eq_right hvu
      have hJv : J ∈ Subjet C v x := subjet_min_of_right hJ hactive
      simpa [hactive] using hv.2 x hx J hJv

end ViscositySolns
