/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.AbelianConductorFiniteUnramified
/-!
# Finite support of the conductor

The finite support is exactly the set of base primes ramified somewhere
upstairs. This does not identify an arbitrary defining ray modulus with the
minimal conductor.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- A finite prime occurs in the conductor precisely when some prime above
it is ramified. -/
theorem IsAbelianConductor.mem_finiteSupport_iff_exists_ramified
    {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    {c : RayClassModulus K}
    (hc : IsAbelianConductor K L c)
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ c.finitePart.support ↔
      ∃ W : HeightOneSpectrum (𝓞 L),
        W.asIdeal.LiesOver v.asIdeal ∧
          ¬ Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := by
  constructor
  · intro hv
    by_contra hnone
    have hall : ∀ W : HeightOneSpectrum (𝓞 L),
        W.asIdeal.LiesOver v.asIdeal →
          Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := by
      intro W hW
      by_contra hn
      exact hnone ⟨W, hW, hn⟩
    exact (Finsupp.mem_support_iff.mp hv)
      ((hc.finiteExponent_eq_zero_iff_unramified v).mpr hall)
  · rintro ⟨W, hW, hn⟩
    apply Finsupp.mem_support_iff.mpr
    intro hz
    exact hn ((hc.finiteExponent_eq_zero_iff_unramified v).mp hz W hW)

end ClassFieldTheory
