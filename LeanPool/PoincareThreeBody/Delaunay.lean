/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Resonance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Delaunay frequencies and resonant actions

At zero mass the planar rotating Kepler Hamiltonian in Delaunay actions is
`-1 / (2 * I₁²) - I₂`, with frequency `(I₁⁻³, -1)`. Positive rational frequency ratios give an
explicit family of resonant actions.
-/

namespace LeanPool.PoincareThreeBody

/-- The rotating Kepler Hamiltonian in planar Delaunay actions. -/
noncomputable def delaunayHamiltonian (action : ActionSpace) : ℝ :=
  -1 / (2 * (action 0) ^ 2) - action 1

/-- The frequency of the rotating Kepler Hamiltonian. -/
noncomputable def delaunayFrequency (firstAction : ℝ) : ActionSpace :=
  ![1 / firstAction ^ 3, -1]

/-- A positive Delaunay action whose Kepler frequency ratio is the positive rational `q / p`. -/
noncomputable def resonantFirstAction (p q : ℕ) : ℝ :=
  ((p : ℝ) / (q : ℝ)) ^ ((3 : ℝ)⁻¹)

/-- The integer resonance vector, regarded as a real vector. -/
def resonanceVector (p q : ℕ) : ActionSpace :=
  ![(p : ℝ), (q : ℝ)]

lemma resonantFirstAction_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    0 < resonantFirstAction p q := by
  exact Real.rpow_pos_of_pos (div_pos (by positivity) (by positivity)) _

lemma resonantFirstAction_cube {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    resonantFirstAction p q ^ 3 = (p : ℝ) / (q : ℝ) := by
  apply Real.rpow_inv_natCast_pow
  · exact (div_pos (by positivity) (by positivity)).le
  · norm_num

lemma resonanceVector_ne_zero {p q : ℕ} (hp : 0 < p) : resonanceVector p q ≠ 0 := by
  intro hzero
  have hcoordinate : (p : ℝ) = 0 := by
    simpa only [resonanceVector, Matrix.cons_val_zero, Pi.zero_apply] using congrFun hzero 0
  exact (Nat.cast_ne_zero.mpr hp.ne') hcoordinate

/-- Every pair of positive natural numbers determines an exact Kepler resonance. -/
theorem resonantFirstAction_is_resonant {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    dot (resonanceVector p q) (delaunayFrequency (resonantFirstAction p q)) = 0 := by
  have hpReal : (p : ℝ) ≠ 0 := by positivity
  have hqReal : (q : ℝ) ≠ 0 := by positivity
  rw [dot_eq]
  simp only [resonanceVector, delaunayFrequency, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_neg, mul_one]
  rw [resonantFirstAction_cube hp hq]
  field_simp
  ring

/-- The abstract linear-algebra obstruction at every positive rational Kepler resonance. -/
theorem rationalKeplerResonance_obstruction {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {differential : ActionSpace} (hdifferential :
      dot (resonanceVector p q) differential = 0) :
    ¬LinearIndependent ℝ
      ![delaunayFrequency (resonantFirstAction p q), differential] :=
  not_linearIndependent_of_common_resonance (resonanceVector_ne_zero hp)
    (resonantFirstAction_is_resonant hp hq) hdifferential

end LeanPool.PoincareThreeBody
