/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol

/-! Spatial derivatives of the classical solutions in Section 4 inherit the
periodicity needed by the torus energy argument. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section4

/-- Every iterated spatial derivative of a periodic function is periodic.
This is the derivative-level periodicity used when integrating the differentiated
equation by parts on the unit cell. -/
theorem iteratedFDeriv_z2Periodic {f : Vec 2 → ℝ}
    (hper : AVenhance.IsZ2Periodic f) (n : ℕ) (k : Fin 2 → ℤ) (x : Vec 2) :
    iteratedFDeriv ℝ n f (x + AVenhance.latticeShift k) =
      iteratedFDeriv ℝ n f x := by
  have hfun : (fun y : Vec 2 => f (y + AVenhance.latticeShift k)) = f := by
    funext y
    exact hper k y
  have hderiv := congrArg (fun g : Vec 2 → ℝ => iteratedFDeriv ℝ n g x) hfun
  simpa only [iteratedFDeriv_comp_add_right] using hderiv

end AVenhance.Infra.Section4
