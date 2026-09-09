/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterWordGevrey
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-! Actual ordered derivative sums depend only on the local function germ. -/

@[expose] public section


noncomputable section

namespace EulerParameterWordGevrey

open scoped Topology

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

omit [Fintype ι] in
/-- Equality on a genuine neighborhood identifies every actual ordered word derivative. -/
theorem wordDerivative_eq_of_eventuallyEq (directions : ι → P) {f g : P → E} {x : P}
    (h : f =ᶠ[𝓝 x] g) {n : ℕ} (w : Fin n → ι) :
    wordDerivative directions f w x = wordDerivative directions g w x := by
  unfold wordDerivative
  rw [(h.iteratedFDeriv ℝ n).eq_of_nhds]

/-- The identical external-word sum transfers across local equality, with no radius factor. -/
theorem wordSum_eq_of_eventuallyEq (directions : ι → P) {f g : P → E} {x : P}
    (h : f =ᶠ[𝓝 x] g) (n : ℕ) : wordSum directions f n x = wordSum directions g n x := by
  unfold wordSum
  apply Finset.sum_congr rfl
  intro w _
  rw [wordDerivative_eq_of_eventuallyEq directions h w]

end EulerParameterWordGevrey
