/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NormUnits
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
/-!
# Continuity of finite field norms

This module records the analytic input used by the topological finite local
reciprocity law: on a finite-dimensional normed algebra, the field norm is a
determinant and is therefore continuous.  It also bundles the corresponding
statements for field units and valuation-ring units.
-/

noncomputable section

universe u v

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The field norm of a finite-dimensional normed algebra over a complete
nontrivially normed field is continuous. -/
theorem algebraNorm_continuous_of_finiteDimensional
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] :
    Continuous (Algebra.norm K : L → K) := by
  classical
  let b := Module.Free.chooseBasis K L
  rw [show (Algebra.norm K : L → K) =
      fun x => (Algebra.leftMulMatrix b x).det by
    funext x
    exact Algebra.norm_eq_matrix_det b x]
  apply Continuous.matrix_det
  exact (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional

/-- The field norm induced on unit groups is continuous. -/
theorem normUnits_continuous_of_finiteDimensional
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] :
    Continuous (normUnits K L) := by
  unfold normUnits
  exact Continuous.units_map (Algebra.norm K : L →* K)
    (algebraNorm_continuous_of_finiteDimensional K L)

/-- The canonical inclusion from valuation-ring units to field units is
continuous for the subtype topologies. -/
theorem integerUnitsToFieldUnits_continuous
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] :
    Continuous (integerUnitsToFieldUnits K) := by
  unfold IsNonarchimedeanLocalField.integerUnitsToFieldUnits
  exact Continuous.units_map
    ((algebraMap 𝒪[K] K).toMonoidHom) continuous_subtype_val

end LocalFieldTheory
