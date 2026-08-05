/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Resonance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Archimedean

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

/-- Positive rational Kepler resonances occur in every positive open interval. -/
theorem exists_resonantFirstAction_between {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
      a < resonantFirstAction p q ∧ resonantFirstAction p q < b := by
  have hcubes : a ^ 3 < b ^ 3 := (show Odd 3 by decide).pow_lt_pow.mpr hab
  obtain ⟨r, har, hrb⟩ := exists_rat_btwn hcubes
  have hrposReal : (0 : ℝ) < (r : ℝ) := lt_trans (by positivity) har
  have hrpos : (0 : ℚ) < r := by exact_mod_cast hrposReal
  let p := r.num.natAbs
  let q := r.den
  have hnumPos : 0 < r.num := Rat.num_pos.mpr hrpos
  have hp : 0 < p := Int.natAbs_pos.mpr hnumPos.ne'
  have hq : 0 < q := r.pos
  have hnumCast : (p : ℝ) = (r.num : ℝ) := by
    norm_cast
    exact Int.natAbs_of_nonneg hnumPos.le
  have hratio : (p : ℝ) / (q : ℝ) = (r : ℝ) := by
    rw [hnumCast, Rat.cast_def]
  have hcube : resonantFirstAction p q ^ 3 = (r : ℝ) :=
    (resonantFirstAction_cube hp hq).trans hratio
  refine ⟨p, q, hp, hq, ?_, ?_⟩
  · apply (show Odd 3 by decide).pow_lt_pow.mp
    rwa [hcube]
  · apply (show Odd 3 by decide).pow_lt_pow.mp
    rwa [hcube]

/-- The positive first Delaunay action axis. -/
abbrev PositiveAction := Set.Ioi (0 : ℝ)

/-- The positive actions with a rational Kepler frequency ratio. -/
def resonantPositiveActions : Set PositiveAction :=
  {x | ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ x.1 = resonantFirstAction p q}

theorem resonantPositiveActions_dense : Dense resonantPositiveActions := by
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨p, q, hp, hq, ha, hb⟩ :=
    exists_resonantFirstAction_between a.2 (show a.1 < b.1 from hab)
  let c : PositiveAction := ⟨resonantFirstAction p q, resonantFirstAction_pos hp hq⟩
  refine ⟨c, ?_, ha, hb⟩
  exact ⟨p, q, hp, hq, rfl⟩

theorem continuous_delaunayFrequencyOnPositive :
    Continuous (fun action : PositiveAction ↦ delaunayFrequency action.1) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun action : PositiveAction ↦ 1 / action.1 ^ 3)
    apply ((continuous_subtype_val.pow 3).inv₀ fun action ↦
      pow_ne_zero 3 (ne_of_gt action.2)).congr
    intro action
    simp [one_div]
  · change Continuous (fun _ : PositiveAction ↦ (-1 : ℝ))
    exact continuous_const

/-- Orthogonality at every rational Kepler resonance forces dependence at every positive action. -/
theorem delaunayDenseResonance_obstruction {differential : PositiveAction → ActionSpace}
    (hdifferential : Continuous differential)
    (hresonant : ∀ {p q : ℕ} (hp : 0 < p) (hq : 0 < q),
      dot (resonanceVector p q)
        (differential ⟨resonantFirstAction p q, resonantFirstAction_pos hp hq⟩) = 0)
    (action : PositiveAction) :
    ¬LinearIndependent ℝ ![delaunayFrequency action.1, differential action] := by
  apply denseResonance_obstruction resonantPositiveActions_dense
    continuous_delaunayFrequencyOnPositive hdifferential
  intro resonant hresonantAction
  rcases hresonantAction with ⟨p, q, hp, hq, heq⟩
  have hsubtype : resonant =
      ⟨resonantFirstAction p q, resonantFirstAction_pos hp hq⟩ := Subtype.ext heq
  subst resonant
  exact wedge_eq_zero_of_resonance (resonanceVector_ne_zero hp)
    (resonantFirstAction_is_resonant hp hq) (hresonant hp hq)

/-- The abstract linear-algebra obstruction at every positive rational Kepler resonance. -/
theorem rationalKeplerResonance_obstruction {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {differential : ActionSpace} (hdifferential :
      dot (resonanceVector p q) differential = 0) :
    ¬LinearIndependent ℝ
      ![delaunayFrequency (resonantFirstAction p q), differential] :=
  not_linearIndependent_of_common_resonance (resonanceVector_ne_zero hp)
    (resonantFirstAction_is_resonant hp hq) hdifferential

end LeanPool.PoincareThreeBody
