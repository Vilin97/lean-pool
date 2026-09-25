/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective


/-!
# Identifying measures from finite-coordinate restrictions

A finite measure on a product space is determined by all of its finite-coordinate pushforwards.
The empty coordinate set is part of the family and therefore records the total mass; measures of
unequal mass cannot satisfy the hypothesis.

This is generic measure-theoretic infrastructure and requires no topology.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory

namespace MarkovProcess
namespace Measure

section

variable {index alpha : Type*} [MeasurableSpace alpha]

/-- Two measures on a product space agree if all their finite-coordinate pushforwards agree. -/
theorem eq_of_map_finiteRestriction_eq
    (mu nu : Measure (index → alpha)) [IsFiniteMeasure mu]
    (h : ∀ I : Finset index, mu.map I.restrict = nu.map I.restrict) :
    mu = nu := by
  let family : (I : Finset index) → Measure (I → alpha) :=
    fun I ↦ mu.map I.restrict
  have hmu : IsProjectiveLimit mu family := by
    intro I
    rfl
  have hnu : IsProjectiveLimit nu family := by
    intro I
    exact (h I).symm
  let (I : Finset index) : IsFiniteMeasure (family I) := by
    dsimp only [family]
    infer_instance
  exact hmu.unique hnu

end
end Measure
end MarkovProcess

end PortComputability
