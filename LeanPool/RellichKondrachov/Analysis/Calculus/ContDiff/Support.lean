/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support

/-!
# `RellichKondrachov.Analysis.Calculus.ContDiff.Support`

Small glue lemmas relating `ContDiffOn` to `ContDiff` using topological support.

The key pattern is: if `f` is `C^n` on an open set `s` and the topological support `tsupport f`
is contained in `s`, then `f` is globally `C^n` (it is `0` in a neighborhood of every point
outside `s`).
-/

namespace RellichKondrachov
namespace Analysis
namespace Calculus
namespace ContDiff

open Set Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `f` is `C^n` on an open set `s` and `tsupport f ⊆ s`, then `f` is globally `C^n`. -/
lemma contDiff_of_contDiffOn_of_tsupport_subset {n : WithTop ℕ∞} {f : E → F} {s : Set E}
    (hs : IsOpen s) (hf : ContDiffOn 𝕜 n f s) (hSupp : tsupport f ⊆ s) :
    ContDiff 𝕜 n f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · exact (hf.contDiffAt (hs.mem_nhds hx))
  · have hx' : x ∉ tsupport f := by
      exact fun hxSupp => hx (hSupp hxSupp)
    have hEq : f =ᶠ[𝓝 x] 0 :=
      (notMem_tsupport_iff_eventuallyEq (f := f) (x := x)).1 hx'
    -- On a neighborhood outside the support, `f` is identically `0`.
    exact (contDiffAt_const : ContDiffAt 𝕜 n (fun _ : E => (0 : F)) x).congr_of_eventuallyEq hEq

end ContDiff
end Calculus
end Analysis
end RellichKondrachov
