/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedTimeBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseGeometry
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.BigOperators

/-! # A countable lattice cover by backward cells

Spatial mesh `r/2` and temporal mesh `r²/2` give a countable family of
backward parabolic cells of radius `r` that covers the whole space-time.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN.Core.Step4
attribute [local instance] Classical.propDecidable

/-- The lattice with spatial mesh `r/2` and temporal mesh `r²/2`. -/
@[expose]
def originLatticeCentre (r : ℝ) (k : (Fin 3 → ℤ) × ℤ) : ParabolicPoint :=
  (fun i => (r / 2) * (k.1 i : ℝ), (r ^ 2 / 2) * (k.2 : ℝ))

private theorem floor_mesh {d : ℝ} (hd : 0 < d) (x : ℝ) :
    0 ≤ x - d * (⌊x / d⌋ : ℝ) ∧ x - d * (⌊x / d⌋ : ℝ) < d := by
  have hl := (le_div_iff₀ hd).mp (Int.floor_le (x / d))
  have hu := (div_lt_iff₀ hd).mp (Int.lt_floor_add_one (x / d))
  constructor <;> nlinarith only [hl, hu]

/-- Every space-time point lies in a lattice cell of any positive radius. -/
theorem originLattice_covers (r : ℝ) (hr : 0 < r) (z : ParabolicPoint) :
    ∃ k : (Fin 3 → ℤ) × ℤ,
      z ∈ parabolicCylinder (originLatticeCentre r k).1 (originLatticeCentre r k).2 r := by
  let k : (Fin 3 → ℤ) × ℤ := (fun i => ⌊z.1 i / (r / 2)⌋, ⌊z.2 / (r ^ 2 / 2)⌋ + 1)
  have hd : 0 < r / 2 := half_pos hr
  have ht : 0 < r ^ 2 / 2 := half_pos (sq_pos_of_pos hr)
  have hx := fun i : Fin 3 => floor_mesh hd (z.1 i)
  have hy := floor_mesh ht z.2
  refine ⟨k, ?_, ?_⟩
  · change Real.sqrt (∑ i : Fin 3, (z.1 i - r / 2 * (⌊z.1 i / (r / 2)⌋ : ℝ)) ^ 2) < r
    rw [Real.sqrt_lt' hr]
    have hs : (∑ i : Fin 3, (z.1 i - r / 2 * (⌊z.1 i / (r / 2)⌋ : ℝ)) ^ 2) ≤
        ∑ _i : Fin 3, (r / 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      nlinarith only [(hx i).1, (hx i).2, hd]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    nlinarith only [hs, sq_pos_of_pos hr]
  · change (r ^ 2 / 2) * ((⌊z.2 / (r ^ 2 / 2)⌋ + 1 : ℤ) : ℝ) - r ^ 2 < z.2 ∧
      z.2 ≤ (r ^ 2 / 2) * ((⌊z.2 / (r ^ 2 / 2)⌋ + 1 : ℤ) : ℝ)
    push_cast
    constructor <;> nlinarith only [hy.1, hy.2, ht]

end CKN.Core.Step4
