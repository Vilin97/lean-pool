/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordLocal

/-! Local equality preserves genuine fixed-Sobolev external derivative blocks. -/

@[expose] public section


noncomputable section

namespace EulerParameterWordGevrey

open scoped Topology

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- A fixed finite Sobolev sum depends only on the actual function germ. -/
theorem baseSize_eq_of_eventuallyEq (directions : ι → P) (q : ℕ) {f g : P → E} {x : P}
    (h : f =ᶠ[𝓝 x] g) : baseSize directions q f x = baseSize directions q g x := by
  unfold baseSize
  exact Finset.sum_congr rfl (fun k _ => wordSum_eq_of_eventuallyEq directions h k)

/-- All inner and external word derivatives agree under equality on a neighborhood. -/
theorem block_eq_of_eventuallyEq (directions : ι → P) (q : ℕ) {f g : P → E} {x : P}
    (h : f =ᶠ[𝓝 x] g) (n : ℕ) : block directions q f n x = block directions q g n x := by
  unfold block
  apply Finset.sum_congr rfl
  intro w _
  apply baseSize_eq_of_eventuallyEq directions q
  filter_upwards [h.iteratedFDeriv ℝ n] with y hy
  exact congrArg (fun D : P [×n]→L[ℝ] E => D (fun j => directions (w j))) hy

end EulerParameterWordGevrey
