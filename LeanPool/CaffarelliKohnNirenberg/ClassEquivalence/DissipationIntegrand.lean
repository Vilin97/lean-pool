/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.CompactLp

/-!
# The dissipation integrand of the local energy inequality

The local energy inequality of `def:sws` carries an integrability side
condition on its left-hand side: the Dirichlet density `spatialGradientSq u Du`
multiplied by the test function must be integrable on the closed support of
that test function.

This file proves that side condition from the data clauses alone.  The closed
support is compact, so the Dirichlet density is already integrable there
(`CKN.spatialGradientSq_integrableOn_compact_of_data`), and the test function
is a bounded factor.  Nothing about the identities of `def:sws` is used, so the
conclusion is available while those identities are still being established.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- The dissipation integrand of the local energy inequality of `def:sws` is
integrable on the closed support of the test function.  Only the data clauses
are used; the nonnegativity of the test function that the clause also
assumes is not needed for integrability and is therefore omitted here. -/
theorem dissipation_integrand_integrableOn_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    IntegrableOn (fun z => spatialGradientSq u Du z * ψ z)
      (tsupport ψ) volume := by
  have hK : IsCompact (tsupport (show ParabolicPoint → ℝ from ψ)) :=
    isCompact_tsupport_parabolic hψ.2.1
  have hbase : IntegrableOn (fun z => spatialGradientSq u Du z)
      (tsupport (show ParabolicPoint → ℝ from ψ)) volume :=
    spatialGradientSq_integrableOn_compact_of_data hdata hK
      (tsupport_parabolic_subset_spaceTimeSet hψ)
  obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction hψ
  exact hbase.mul_bdd (c := C) (g := fun z : ParabolicPoint => ψ z)
    hψ.1.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)

end CKN
