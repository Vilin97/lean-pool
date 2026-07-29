/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E]

/-- A lattice gaussian used in the Odlyzko-bound argument. -/
noncomputable def latticeGaussian (a : ℝ) (x : E) : ℂ :=
  Complex.exp (-(a : ℂ) * (‖x‖ : ℂ) ^ 2)

theorem norm_latticeGaussian (a : ℝ) (x : E) :
    ‖latticeGaussian a x‖ = Real.exp (-a * ‖x‖ ^ 2) := by
  have hvalue :
      latticeGaussian a x =
        ((Real.exp (-a * ‖x‖ ^ 2) : ℝ) : ℂ) := by
    unfold latticeGaussian
    simp
  rw [hvalue, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

theorem norm_latticeGaussian_add_le
    {a : ℝ} (ha : 0 ≤ a) (y z : E) :
    ‖latticeGaussian a (y + z)‖ ≤
      Real.exp (a * ‖y‖ ^ 2) * ‖latticeGaussian (a / 2) z‖ := by
  rw [norm_latticeGaussian, norm_latticeGaussian, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have htri : ‖z‖ ≤ ‖y + z‖ + ‖y‖ := by
    calc
      ‖z‖ = ‖(y + z) - y‖ := by simp
      _ ≤ ‖y + z‖ + ‖y‖ := norm_sub_le _ _
  have hsquare :
      ‖z‖ ^ 2 ≤ 2 * ‖y + z‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖y + z‖ - ‖y‖),
      norm_nonneg z, norm_nonneg (y + z), norm_nonneg y]
  nlinarith

theorem summable_latticeGaussian [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable (fun x : L ↦ latticeGaussian a (x : E)) := by
  let r : ℝ := -(Module.finrank ℤ L + 1)
  have hr : r < -(Module.finrank ℤ L : ℝ) := by grind
  have hclosed : IsClosed (L : Set E) :=
    by
      change IsClosed (L.toAddSubgroup : Set E)
      exact AddSubgroup.isClosed_of_discrete
  have htend :
      Tendsto (norm ∘ ((↑) : L → E)) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
      hclosed.isClosedEmbedding_subtypeVal
  have hdecay :=
    (rexp_neg_quadratic_isLittleO_rpow_atTop
      (a := -a) (b := 0) (by grind) r).isBigO.comp_tendsto htend
  have hreal :
      Summable (fun x : L ↦ Real.exp (-a * ‖(x : E)‖ ^ 2)) := by
    obtain ⟨c, hc, hbound⟩ := hdecay.exists_pos
    apply ((ZLattice.summable_norm_rpow L r hr).mul_left c).of_norm_bounded_eventually
    filter_upwards [hbound.bound] with x hx
    simpa [Function.comp_apply, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hx
  apply hreal.of_norm_bounded
  intro x
  rw [norm_latticeGaussian]

end NumberField.Odlyzko
