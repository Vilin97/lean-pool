/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.MainEstimate
public import LeanPool.Zeta5Irrational.Zeta5
import LeanPool.Zeta5Irrational.Criterion
public import Mathlib.NumberTheory.Real.Irrational

/-! # Irrationality of ζ(5)

`Zeta5Irrational.irrational_five` is the target statement. It follows from
`Zeta5Irrational.main_estimate`
(Theorem 2.1 of the paper, with a smaller decay rate) and the criterion
`Zeta5Irrational.irrational_of_eventually_exists_int_poly`. It depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

public section

open Polynomial Filter Topology

namespace Zeta5Irrational

/-- Theorem 1.1 of the paper, from Theorem 2.1. -/
theorem irrational_zeta5 : Irrational zeta5 := by
  obtain ⟨c, hc, h⟩ := main_estimate
  exact
    irrational_of_eventually_exists_int_poly zeta5 (fun n => 37 * n)
      (fun n => Real.exp (-c * (n : ℝ) ^ 2)) (tendsto_pow_mul_exp_neg_sq_of_pos hc)
      (h.mono fun _ ⟨Q, _, hdeg, hpos, hlt⟩ => ⟨Q, hdeg.le, hpos, hlt.le⟩)

theorem irrational_five : ∃ x, Irrational x ∧ riemannZeta 5 = x :=
  ⟨zeta5, irrational_zeta5, riemannZeta_five⟩

end Zeta5Irrational
