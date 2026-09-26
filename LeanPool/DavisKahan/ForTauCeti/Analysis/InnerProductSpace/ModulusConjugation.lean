/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

/-
Staged for Tau Ceti: additions to the operator modulus API.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorModulus

/-!
# Conjugating the modulus by a unitary

A unitary `e : E ≃ₗᵢ[𝕜] F` conjugates endomorphisms of `E` to endomorphisms of
`F` by `x ↦ e x e⁻¹`, and Mathlib packages that as the `⋆`-algebra equivalence
`LinearIsometryEquiv.conjStarAlgEquiv`.  Since `|T|` is characterized as the
*unique nonnegative square root* of the Gram operator `T⋆ T`, and a `⋆`-algebra
equivalence preserves both "square root" (it is multiplicative) and
"nonnegative" (it is a conjugation by a unitary), conjugation commutes with the
modulus.

The hypothesis is deliberately stated on the *Gram* operators rather than on
`T` and `S` themselves.  The intended use is the Halmos two-projection model,
where the two cross blocks `B₁ : M₁ →L N₁` and `B₂ : M₂ →L N₂` have different
targets and no intertwiner between them is available — what is available is
`B⋆B = A - A²` on the sources, so a unitary intertwining the cosine blocks
`A₁, A₂` intertwines the Gram operators, and this lemma upgrades that to an
intertwiner of `|B₁|, |B₂|`.  Producing `B₂ W = W' B₁` from there is exactly
the reconstruction step of Davis--Kahan 1970 Theorem 3.1.

## Main results

* `ContinuousLinearMap.conjStarAlgEquiv_modulus`: the operator form.
* `ContinuousLinearMap.modulus_conj_apply`: the pointwise form.
-/

@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- **A unitary that conjugates the Gram operators conjugates the moduli.**

`T` and `S` may have unrelated targets: only their source spaces are related,
by `e`, and only through `T⋆ T` and `S⋆ S`. -/
theorem conjStarAlgEquiv_modulus (e : E ≃ₗᵢ[𝕜] F) {T : E →L[𝕜] G} {S : F →L[𝕜] K}
    (h : e.conjStarAlgEquiv (T.adjoint ∘L T) = S.adjoint ∘L S) :
    e.conjStarAlgEquiv T.modulus = S.modulus := by
  refine eq_modulus_of_nonneg_of_mul_self_eq ?_ ?_
  · -- Conjugation by a unitary preserves nonnegativity.
    rw [nonneg_iff_isPositive, LinearIsometryEquiv.conjStarAlgEquiv_apply,
      ← e.adjoint_eq_symm]
    exact ((nonneg_iff_isPositive (f := _)).mp T.modulus_nonneg).conj_adjoint _
  · -- Multiplicativity turns `|T|² = T⋆T` into `(e|T|e⁻¹)² = S⋆S`.
    rw [← map_mul, modulus_mul_self, h]

/-- The pointwise form of `ContinuousLinearMap.conjStarAlgEquiv_modulus`. -/
theorem modulus_conj_apply (e : E ≃ₗᵢ[𝕜] F) {T : E →L[𝕜] G} {S : F →L[𝕜] K}
    (h : ∀ x, e ((T.adjoint ∘L T) x) = (S.adjoint ∘L S) (e x)) (x : E) :
    e (T.modulus x) = S.modulus (e x) := by
  have hconj : e.conjStarAlgEquiv (T.adjoint ∘L T) = S.adjoint ∘L S := by
    refine ContinuousLinearMap.ext fun y => ?_
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    rw [h (e.symm y), LinearIsometryEquiv.apply_symm_apply]
  have := congrArg (fun f : F →L[𝕜] F => f (e x)) (conjStarAlgEquiv_modulus e hconj)
  simpa [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using this

end ContinuousLinearMap
