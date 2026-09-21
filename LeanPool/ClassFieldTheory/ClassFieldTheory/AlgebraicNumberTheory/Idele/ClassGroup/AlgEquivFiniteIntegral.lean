/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivTopology
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
/-!
# Integral finite completions under a number-field equivalence

The finite-completion map associated with a field equivalence preserves
the local valuation subring. This is the restricted-product compatibility
needed for continuity of adelic transport.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Algebra ℚ K]
  [Field M] [NumberField M] [Algebra ℚ M]

/-- Corresponding finite-completion maps carry local integers to local
integers. -/
theorem finitePlaceAdicCompletionCongrHom_mapsToIntegers
    (e : K ≃ₐ[ℚ] M) (W : HeightOneSpectrum (𝓞 M)) :
    Set.MapsTo (finitePlaceAdicCompletionCongrHom e W)
      (((finitePlaceCongr e).symm W).adicCompletionIntegers K :
        Set (((finitePlaceCongr e).symm W).adicCompletion K))
      (W.adicCompletionIntegers M : Set (W.adicCompletion M)) := by
  intro x hx
  let : Algebra K M := e.toRingHom.toAlgebra
  let w := (finitePlaceCongr e).symm W
  have hKM : finitePlaceBelow (K := K) W = w := by
    apply HeightOneSpectrum.ext
    rfl
  let W' : {W : HeightOneSpectrum (𝓞 M) //
      finitePlaceBelow (K := K) W = w} := ⟨W, hKM⟩
  let : W.asIdeal.LiesOver w.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal hKM.symm
  have he : w.asIdeal.ramificationIdx' W.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
      W.asIdeal w.ne_bot
  change finitePlaceAdicCompletionMap K M w W' x ∈
    W.adicCompletionIntegers M
  change Valued.v x ≤ 1 at hx
  change Valued.v (finitePlaceAdicCompletionMap K M w W' x) ≤ 1
  rw [finitePlaceAdicCompletionMap_valued K M w W' x]
  exact (pow_le_one_iff he).mpr hx

end
