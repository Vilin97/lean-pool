/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module


public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtBasis
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Space

/-!
# The `ℓ²` model of the paper Hilbert--Schmidt ideal

The Hilbert--Schmidt operators `F →L[ℂ] E` are realised as `lp (fun _ : ι => E) 2`,
the square-summable column families over a Hilbert basis of `F`.  This file is the
bridge between that model and the paper square norm of
`DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidt.lean`:

* finite paper square energy is equivalent to representability by a *unique* element;
* the model norm is exactly the paper square norm.

## What changed

The model used to be `vendor/Spectra`'s Hilbert tensor product
`Spectra.HilbertSchmidtTensor.Space E F`.  Mathlib supplies `lp`'s inner product and
completeness outright, so the donor closure the tensor product carried — measured at
21,581 lines — is gone; what is left is the column bijection, which is
`ForTauCeti/Analysis/InnerProductSpace/HilbertSchmidtLp.lean`.  The declarations keep
their names and statements, so consumers are unaffected.

## The one design decision

`Space E F` mentions no basis; `lp (fun _ : ι => E) 2` must.  Rather than give every
declaration here a basis parameter — which every downstream consumer would inherit — the
basis is fixed internally to `TauCeti.chosenHilbertBasis ℂ F`, the same choice
`ContinuousLinearMap.hilbertSchmidtENorm` already makes.  Nothing depends on *which*
basis it is, because `hilbertSchmidtEnergy_indep` says the energy does not.

`hilbertSchmidtTensor` also stops being a `Classical.choose`: the column family is
available directly, so it is that family.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace ENNReal
open TauCeti.HilbertSchmidt

noncomputable section

universe vE vF

variable {E : Type vE} {F : Type vF}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The index type of the fixed Hilbert basis of `F`. -/
abbrev HSIndex (F : Type vF) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] : Type vF :=
  ↥(TauCeti.chosenHilbertBasisSet ℂ F)

/-- The fixed Hilbert basis of `F` in which the model is expressed. -/
abbrev hSBasis (F : Type vF) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] : HilbertBasis (TauCeti.chosenHilbertBasisSet ℂ F) ℂ F :=
  TauCeti.chosenHilbertBasis ℂ F

/-- Finite paper square energy is equivalent to representation by a unique
element of the `ℓ²` model. -/
theorem approximationNumberEnergy_ne_top_iff_existsUnique_tensor (A : F →L[ℂ] E) :
    approximationNumberEnergy A ≠ ⊤ ↔
      ∃! f : lp (fun _ : HSIndex F => E) 2, ofLp (hSBasis F) f = A := by
  rw [approximationNumberEnergy_ne_top_iff_summable_basis (hSBasis F) A]
  exact (existsUnique_ofLp_iff_summable (hSBasis F) A).symm

/-- The canonical model element representing a paper Hilbert--Schmidt operator:
its column family. -/
noncomputable def hilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : approximationNumberEnergy A ≠ ⊤) : lp (fun _ : HSIndex F => E) 2 :=
  ⟨columns (hSBasis F) A,
    (memLp_columns_iff_summable (hSBasis F) A).mpr
      ((approximationNumberEnergy_ne_top_iff_summable_basis (hSBasis F) A).1 hA)⟩

/-- The tensor model's operator, unfolded.  This is the bridge between the tensor presentation of a
Hilbert--Schmidt map and its operator form. -/
@[simp]
theorem toOperator_hilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : approximationNumberEnergy A ≠ ⊤) :
    ofLp (hSBasis F) (hilbertSchmidtTensor A hA) = A :=
  ofLp_columns (hSBasis F) A _

/-- The model norm is exactly the paper square norm. -/
theorem norm_hilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : approximationNumberEnergy A ≠ ⊤) :
    ‖hilbertSchmidtTensor A hA‖ = ContinuousLinearMap.hilbertSchmidtNorm A := by
  have hsq := norm_sq_eq_tsum_norm_column_sq (hSBasis F) (hilbertSchmidtTensor A hA)
  rw [toOperator_hilbertSchmidtTensor] at hsq
  rw [hilbertSchmidtNorm_eq_sqrt_tsum_basis (hSBasis F) A hA, ← hsq,
    Real.sqrt_sq (norm_nonneg _)]

/-- Every element of the model represents a paper Hilbert--Schmidt operator. -/
theorem approximationNumberEnergy_ne_top_toOperator (f : lp (fun _ : HSIndex F => E) 2) :
    approximationNumberEnergy (ofLp (hSBasis F) f) ≠ ⊤ := by
  rw [approximationNumberEnergy_ne_top_iff_summable_basis (hSBasis F), ←
    memLp_columns_iff_summable (hSBasis F), columns_ofLp]
  exact lp.memℓp f

/-- The paper square norm of the represented operator is exactly the model norm. -/
theorem hilbertSchmidtNorm_toOperator (f : lp (fun _ : HSIndex F => E) 2) :
    ContinuousLinearMap.hilbertSchmidtNorm (ofLp (hSBasis F) f) = ‖f‖ := by
  have hZ := approximationNumberEnergy_ne_top_toOperator f
  have hcanon := norm_hilbertSchmidtTensor (ofLp (hSBasis F) f) hZ
  have heq : hilbertSchmidtTensor (ofLp (hSBasis F) f) hZ = f :=
    ofLp_injective (hSBasis F) (by rw [toOperator_hilbertSchmidtTensor])
  rw [heq] at hcanon
  exact hcanon.symm

end

end ExactSinTheta
end DavisKahan
end TauCeti
