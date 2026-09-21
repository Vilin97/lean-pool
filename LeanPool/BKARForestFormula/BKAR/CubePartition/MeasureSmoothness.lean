/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasurePartition
import LeanPool.BKARForestFormula.BKAR.PartialDerivSymmetry

/-! # From cube contributions to ordered sector contributions

Under the global smoothness hypothesis, the integrand of a forest's cube
contribution is continuous, hence integrable on the compact unit cube, and
the unit-cube partition step applies: the order-free cube contribution of
the BKAR forest interpolation formula (see `BKAR.Formula`) equals the
finite sum of its closed ordered sector contributions, with sector overlaps
null by the collision-hyperplane theorem.
-/

noncomputable section

namespace BKAR

namespace Forest

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Continuity of the usual unordered cube integrand under the BKAR smoothness hypothesis. -/
theorem continuous_cubeContributionIntegrand
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    Continuous
      (fun u : F.EdgeParam → ℝ =>
        F.mixedPartial ρ (F.standardInterp u)) := by
  have hinterp :
      Continuous (fun u : F.EdgeParam → ℝ => F.standardInterp u) :=
    F.standardInterp_continuous_comp continuous_id
  have hpartial : Continuous (F.mixedPartial ρ) := by
    rw [mixedPartial_def]
    exact hρ.mixedPartialList_continuous F.edges.toList
  exact hpartial.comp hinterp

/-- Integrability of the usual unordered cube integrand on the forest parameter cube. -/
theorem integrableOn_cubeContributionIntegrand
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    IntegrableOn
      (fun u : F.EdgeParam → ℝ =>
        F.mixedPartial ρ (F.standardInterp u))
      F.unitCube (volume : Measure (F.EdgeParam → ℝ)) :=
  (F.continuous_cubeContributionIntegrand ρ hρ).continuousOn.integrableOn_compact
    F.isCompact_unitCube

/--
The unit-cube partition step for the usual unordered forest contribution:
the integral over `[0,1]^{E(F)}` is the finite sum of its closed ordered
sectors; sector overlaps are null by the collision-hyperplane theorem.
-/
theorem cubeContribution_eq_sum_orderedCubeSimplex_mixedPartial
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    F.cubeContribution ρ =
      Finset.sum
        (Finset.univ :
          Finset {order : List (Edge V) // order ∈ F.edgeOrders})
        (fun order =>
          ∫ u in F.orderedCubeSimplex order.val,
            F.mixedPartial ρ (F.standardInterp u)
              ∂(volume : Measure (F.EdgeParam → ℝ))) := by
  rw [cubeContribution]
  exact F.integral_unitCube_eq_sum_orderedCubeSimplex
    (fun u : F.EdgeParam → ℝ =>
      F.mixedPartial ρ (F.standardInterp u))
    (F.integrableOn_cubeContributionIntegrand ρ hρ)

/-- Continuity of an ordered-sector integrand under the BKAR smoothness hypothesis. -/
theorem continuous_orderedCubeSectorIntegrand
    (F : Forest V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    Continuous
      (fun u : F.EdgeParam → ℝ =>
        mixedPartialList order.reverse ρ (F.standardInterp u)) := by
  exact (hρ.mixedPartialList_continuous order.reverse).comp
    (F.standardInterp_continuous_comp continuous_id)

/-- Integrability of an ordered-sector integrand on the forest parameter cube. -/
theorem integrableOn_orderedCubeSectorIntegrand
    (F : Forest V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    IntegrableOn
      (fun u : F.EdgeParam → ℝ =>
        mixedPartialList order.reverse ρ (F.standardInterp u))
      F.unitCube (volume : Measure (F.EdgeParam → ℝ)) :=
  (F.continuous_orderedCubeSectorIntegrand order ρ hρ).continuousOn.integrableOn_compact
    F.isCompact_unitCube

/--
On a canonical ordered sector, the order-specific recursive mixed partial is
the same as the unordered forest mixed partial. This is the analytic half of
the sector-to-cube bridge.
-/
theorem orderedCubeSectorContribution_eq_integral_mixedPartial
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    F.orderedCubeSectorContribution order ρ =
      ∫ u in F.orderedCubeSimplex order,
        F.mixedPartial ρ (F.standardInterp u)
          ∂(volume : Measure (F.EdgeParam → ℝ)) := by
  rw [orderedCubeSectorContribution]
  rw [F.mixedPartial_eq_mixedPartialList_of_mem_edgeOrders horder hρ]

/--
The unit-cube partition step plus mixed-partial order independence: the
usual unordered cube
contribution is the sum of the order-specific closed cube-sector
contributions.
-/
theorem cubeContribution_eq_sum_orderedCubeSectorContribution
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    F.cubeContribution ρ =
      Finset.sum F.edgeOrders
        (fun order => F.orderedCubeSectorContribution order ρ) := by
  rw [F.cubeContribution_eq_sum_orderedCubeSimplex_mixedPartial ρ hρ]
  calc
    (∑ order : {order : List (Edge V) // order ∈ F.edgeOrders},
        ∫ u in F.orderedCubeSimplex order.val,
          F.mixedPartial ρ (F.standardInterp u)
            ∂(volume : Measure (F.EdgeParam → ℝ))) =
        Finset.sum F.edgeOrders
          (fun order =>
            ∫ u in F.orderedCubeSimplex order,
              F.mixedPartial ρ (F.standardInterp u)
                ∂(volume : Measure (F.EdgeParam → ℝ))) := by
          rw [← Finset.attach_eq_univ (s := F.edgeOrders)]
          exact
            (Finset.sum_attach F.edgeOrders
              (fun order =>
                ∫ u in F.orderedCubeSimplex order,
                  F.mixedPartial ρ (F.standardInterp u)
                    ∂(volume : Measure (F.EdgeParam → ℝ))))
    _ = Finset.sum F.edgeOrders
          (fun order => F.orderedCubeSectorContribution order ρ) := by
          apply Finset.sum_congr rfl
          intro order horder
          exact (F.orderedCubeSectorContribution_eq_integral_mixedPartial
            horder ρ hρ).symm

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
