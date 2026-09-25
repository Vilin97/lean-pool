/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.StrandBundle
public import LeanPool.RegtsSevenster.RS.Novel.Skein.HomSpaces

/-!
# The categorical trace on Hom spaces

The trace of a `(t + t)`-fragment is its full strand closure: the
closure pairing against the strand bundle, which threads each
output label back to the matching input.  The trace functional is
therefore the connection pairing evaluated at the bundle; it kills
the pairing kernel by construction and so descends to the Hom
spaces of the skein category.
-/

@[expose] public section

namespace RS

/-- The trace of a `(t + t)`-fragment under a parameter: the value
of its strand closure. -/
noncomputable def fragTrace (f : ClosedFragment → ℂ) {t : ℕ}
    (F : Fragment (Fin (t + t))) : ℂ :=
  f (pairClose F (strandBundle t))

/-- The trace as a linear functional on the free module: the
connection pairing evaluated at the strand bundle. -/
noncomputable def traceFunctional (f : ClosedFragment → ℂ) (t : ℕ) :
    (Fragment (Fin (t + t)) →₀ ℂ) →ₗ[ℂ] ℂ :=
  (LinearMap.proj (strandBundle t)).comp (connectionMap f (t + t))

/-- The trace functional on a single fragment is its trace. -/
theorem traceFunctional_single (f : ClosedFragment → ℂ) {t : ℕ}
    (F : Fragment (Fin (t + t))) :
    traceFunctional f t (Finsupp.single F 1) = fragTrace f F := by
  simp [traceFunctional, fragTrace, connectionMap, connectionPairing]

/-- The pairing kernel is contained in the trace kernel. -/
theorem ker_le_ker_traceFunctional (f : ClosedFragment → ℂ) (t : ℕ) :
    LinearMap.ker (connectionMap f (t + t)) ≤
      LinearMap.ker (traceFunctional f t) := fun x hx => by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [traceFunctional, LinearMap.comp_apply, hx]
  rfl

/-- The trace descends to the Hom space. -/
noncomputable def HomSpace.traceMap (f : ClosedFragment → ℂ) (t : ℕ) :
    HomSpace f (t + t) →ₗ[ℂ] ℂ :=
  Submodule.liftQ _ (traceFunctional f t)
    (ker_le_ker_traceFunctional f t)

/-- The descended trace on a fragment class is the fragment
trace. -/
theorem HomSpace.traceMap_ofFragment (f : ClosedFragment → ℂ)
    {t : ℕ} (F : Fragment (Fin (t + t))) :
    HomSpace.traceMap f t (HomSpace.ofFragment f F) = fragTrace f F := by
  exact traceFunctional_single f F

end RS
