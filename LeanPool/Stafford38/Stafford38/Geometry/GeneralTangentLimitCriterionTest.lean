/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.GeneralTangentLimitCriterion

/-!
# Independent consumer for the paper-level tangent-limit criterion

This consumer keeps the manuscript's quantifier order visible.  It starts
with an arbitrary prime affine variety, a formal projective arc in its
homogeneous-equation closure, and an actual finite-rank direct-summand tangent
lattice.  No matrix basis, retraction, annihilator, position coefficients, or
separate tangent-chart equality is supplied.
-/

namespace Stafford38.Geometry.GeneralTangentLimitCriterionTest

open Stafford38.Geometry.GeneralTangentLimitCriterion
open Stafford38.Geometry.ProjectiveConormalDirections

noncomputable section

variable {k : Type*} [Field k] [IsAlgClosed k]

theorem paper_shape_consumer
    {n dimY : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (L : Submodule (PowerSeries k)
      (Fin (n + 1) → PowerSeries k))
    (D : DirectSummandInput (dimY := dimY) I q L) :
    Projectivization.mk k
        (fun i : Fin n => if i = D.axis then (1 : k) else 0)
        (by intro h; have hh := congrFun h D.axis; simp at hh) ∈
      projectiveHomogeneousClosure
        (projectivizedDirectionSet (smoothConormalDirectionSet I)) := by
  exact tangent_limit_criterion_of_directSummand I q L D


end
end Stafford38.Geometry.GeneralTangentLimitCriterionTest
