/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.CompactLp

/-!
# The integrand of the divergence-free identity

The divergence-free clause of `def:sws` pairs the identity
`∫ ∑ᵢ uᵢ ∂ᵢψ = 0` with an integrability side condition on the integrand, stated
on the closed support of the test function `ψ`.

This file proves that side condition from the data clauses alone.  The closed
support is compact, so Lebesgue measure restricted to it is finite and the
square integrable velocity of the data clauses is integrable there; each
spatial derivative of a test function is a bounded factor, and the integrand is
a finite sum of such products.

Nothing about the identities of `def:sws` is used, so the conclusion is
available while those identities are still being established.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- Each component of the velocity is integrable on a compact subset of the
carrier: it is square integrable there, and the restricted measure is finite. -/
theorem velocity_component_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I)
    (i : Fin 3) :
    IntegrableOn (fun z => u z i) K volume := by
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict_of_isCompact hK
  exact ((velocity_memLp_two_on_compact_of_data hdata hK hKsub).continuousLinearMap_comp
    (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)).integrable (by norm_num)

/-- The integrand of the divergence-free clause of `def:sws` is integrable on
the closed support of the test function.  Only the data clauses are used. -/
theorem divergenceFree_integrand_integrableOn_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    IntegrableOn (fun z => ∑ i, u z i * spatialPartial ψ i z)
      (tsupport ψ) volume := by
  have hK : IsCompact (tsupport (show ParabolicPoint → ℝ from ψ)) :=
    isCompact_tsupport_parabolic hψ.2.1
  have hKsub : tsupport (show ParabolicPoint → ℝ from ψ) ⊆ spaceTimeSet Ω I :=
    tsupport_parabolic_subset_spaceTimeSet hψ
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hψ i
  exact (velocity_component_integrableOn_compact_of_data hdata hK hKsub i).mul_bdd
    (c := C) (g := fun z : ParabolicPoint => spatialPartial ψ i z)
    (spatialPartial_contDiff hψ.1 i).continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)

end CKN
