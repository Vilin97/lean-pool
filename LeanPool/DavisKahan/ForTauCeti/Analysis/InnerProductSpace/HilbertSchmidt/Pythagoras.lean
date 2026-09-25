/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Conjugation

/-!
# Splitting the Hilbert–Schmidt energy along an orthogonal family

If a family of maps splits every vector's norm — `∑ ‖P i v‖² = ‖v‖²`, as an
orthogonal family of projections summing to the identity does — then it splits
the Hilbert–Schmidt energy as well, on either side:

* `tsum_energy_isometryFamily_comp` — composing on the **left**;
* `tsum_energy_comp_isometryFamily` — composing on the **right**.

Together these give the Pythagoras identity `∑_{i,j} ‖P i ∘ Z ∘ Q j‖² = ‖Z‖²`
that a block-diagonal argument needs.

## Why this is the shape

The block argument for the Sylvester spectral gap (SR-D4b) cuts `A` and `B` into
finitely many spectral pieces, estimates `A Z - Z B` on each block where both
operators are within `ε` of scalars, and reassembles.  Reassembly is exactly
these two identities.

Neither needs the family to consist of projections, or to be countable, or to be
summable in any operator topology: the only hypothesis is the pointwise norm
split, which is what makes both proofs short.  The left one is termwise
Pythagoras in the codomain composed with `ENNReal.tsum_comm`; the right one is
the left one applied to the adjoint, since the energy is adjoint-invariant and
`(Z ∘ Q)⋆ = Q⋆ ∘ Z⋆`.  Working in `ℝ≥0∞` keeps both free of summability side
conditions.

## Sources

Additivity of the Hilbert--Schmidt energy over an orthogonal family is the
Pythagoras identity for the Hilbert--Schmidt inner product, standard in the
references given in
`ForTauCeti/Analysis/InnerProductSpace/HilbertSchmidtLp.lean`.  The statement is
shaped by the block argument that consumes it: it is an `ℝ≥0∞` identity, so it
substitutes under a `tsum` with no summability side-condition.

## Provenance

*New.*
-/

@[expose] public section

open scoped ENNReal NNReal

namespace TauCeti
namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι κ ι' : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Splitting the energy on the left.**  A family that splits norms in the
codomain splits the Hilbert–Schmidt energy: exchange the two sums and apply the
hypothesis columnwise. -/
theorem tsum_energy_isometryFamily_comp (b : HilbertBasis ι 𝕜 F) (Z : F →L[𝕜] E)
    (P : ι' → (E →L[𝕜] E)) (hP : ∀ v : E, ∑' i, ‖P i v‖ₑ ^ 2 = ‖v‖ₑ ^ 2) :
    ∑' i, ((P i).comp Z).hilbertSchmidtEnergy b = Z.hilbertSchmidtEnergy b := by
  simp only [ContinuousLinearMap.hilbertSchmidtEnergy_def, ContinuousLinearMap.comp_apply]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun k => hP (Z (b k))

/-- **Splitting the energy on the right.**  The same statement about the
adjoint, transported by adjoint-invariance of the energy. -/
theorem tsum_energy_comp_isometryFamily (b : HilbertBasis ι 𝕜 F) (c : HilbertBasis κ 𝕜 E)
    (Z : F →L[𝕜] E) (Q : ι' → (F →L[𝕜] F))
    (hQ : ∀ v : F, ∑' j, ‖(Q j).adjoint v‖ₑ ^ 2 = ‖v‖ₑ ^ 2) :
    ∑' j, (Z.comp (Q j)).hilbertSchmidtEnergy b = Z.hilbertSchmidtEnergy b := by
  have hstep : ∀ j : ι', (Z.comp (Q j)).hilbertSchmidtEnergy b
      = (((Q j).adjoint).comp Z.adjoint).hilbertSchmidtEnergy c := by
    intro j
    rw [ContinuousLinearMap.hilbertSchmidtEnergy_adjoint _ b c,
      ContinuousLinearMap.adjoint_comp]
  rw [tsum_congr hstep, tsum_energy_isometryFamily_comp c Z.adjoint _ hQ,
    ← ContinuousLinearMap.hilbertSchmidtEnergy_adjoint Z b c]

/-- **Pythagoras for a two-sided block decomposition.**  The energy of `Z` is
the total energy of its blocks. -/
theorem tsum_tsum_energy_blocks (b : HilbertBasis ι 𝕜 F) (c : HilbertBasis κ 𝕜 E)
    (Z : F →L[𝕜] E) (P : ι' → (E →L[𝕜] E)) (Q : ι' → (F →L[𝕜] F))
    (hP : ∀ v : E, ∑' i, ‖P i v‖ₑ ^ 2 = ‖v‖ₑ ^ 2)
    (hQ : ∀ v : F, ∑' j, ‖(Q j).adjoint v‖ₑ ^ 2 = ‖v‖ₑ ^ 2) :
    ∑' j, ∑' i, (((P i).comp Z).comp (Q j)).hilbertSchmidtEnergy b
      = Z.hilbertSchmidtEnergy b := by
  have hinner : ∀ j : ι', ∑' i, (((P i).comp Z).comp (Q j)).hilbertSchmidtEnergy b
      = (Z.comp (Q j)).hilbertSchmidtEnergy b := by
    intro j
    refine Eq.trans (tsum_congr fun i => ?_) (tsum_energy_isometryFamily_comp b _ P hP)
    rw [ContinuousLinearMap.comp_assoc]
  rw [tsum_congr hinner, tsum_energy_comp_isometryFamily b c Z Q hQ]

end HilbertSchmidt
end TauCeti
