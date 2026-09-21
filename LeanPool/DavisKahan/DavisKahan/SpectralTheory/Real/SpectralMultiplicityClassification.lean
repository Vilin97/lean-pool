/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Real.RealMultiplicityModel
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.SpectralMultiplicityEquiv

/-!
# Spectral multiplicity data classify self-adjoint operators over `ℝ`

`TauCeti.SameSpectralMultiplicity` is already field-generic: the base measure and level sets of a
`TauCeti.MultiplicityDatum 𝕜` are complex whatever `𝕜` is, and only the `L²` fibres and the model
operator see the scalar field.  What is *not* generic is the classification theorem, because both
of its directions rest on complex-scalar inputs.  This module supplies the real analogues.

Each direction uses a different half of the real multiplicity theory:

* `operatorUnitaryEquiv_of_sameSpectralMultiplicity_real` uses
  `TauCeti.operatorUnitaryEquiv_of_measureEquiv_real`, which needs no Hahn--Hellinger at all --
  only that a real multiplication operator is the restriction of a complex one with the *same,
  real valued*, symbol, so that the complex Radon--Nikodym unitary applies and descends.  There
  is no separability hypothesis, and the base measures need not be carried by the real axis.
* `sameSpectralMultiplicity_of_operatorUnitaryEquiv_real` uses
  `RealSpectralRestriction.exists_hasMultiplicityModel_real`, the existence half of real
  Hahn--Hellinger.  That is where separability of `H₁` is spent, exactly as in the complex
  statement, and where reality of the base measure is *produced* rather than assumed -- a
  self-adjoint operator has real spectrum.

## Why this lives here and not in `ForTauCeti`

The complex classification is paper-independent and reusable, and it lives in
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/SpectralMultiplicityEquiv.lean`.  The real
classification depends on real Hahn--Hellinger existence, and that theorem is
`TauCeti.DavisKahan.RealSpectralRestriction.exists_hasMultiplicityModel_real`, which is
maintained in this package.  Moving the real bridge below it would require moving the whole real
cyclic-decomposition and complexification tower with it, which is separate work.

## Scope

The multiplicity datum stays a `TauCeti.MultiplicityDatum` with `base : Measure ℂ`; no
`Measure ℝ` datum is built, and reality of the base is nowhere a field of the structure.  What
changes at `ℝ` is the scalar field of the *model `L²` fibres*, which is what
`TauCeti.MultiplicityDatum.retype` records, and the base measure and level sets -- the entire
multiplicity content -- are literally unchanged.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace RealSpectralRestriction

variable {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

/-- **Same multiplicity data implies unitary equivalence, over a real Hilbert space**, with no
separability hypothesis on either space and no reality hypothesis on the base measures.

The complex statement is confined to `ℂ` because the middle step
`TauCeti.operatorUnitaryEquiv_of_measureEquiv_complex` uses the complex `rnDerivL2Equiv` API.  That turns
out not to matter here: the real model operator is multiplication by a *real valued* symbol, so
it is the restriction to the real classes of the complex operator with the same symbol, and a
real symbol commutes with pointwise conjugation.  The complex Radon--Nikodym unitary is
`star`-equivariant (`TauCeti.star_rnDerivL2Equiv`), so it restricts.  A field-generic
Radon--Nikodym unitary is therefore *not* needed. -/
theorem operatorUnitaryEquiv_of_sameSpectralMultiplicity_real (A : H₁ →L[ℝ] H₁)
    (B : H₂ →L[ℝ] H₂) (h : SameSpectralMultiplicity A B) : OperatorUnitaryEquiv A B := by
  obtain ⟨D, E, hAD, hBE, hbase, hlevel⟩ := h.exists_models
  exact hAD.trans ((operatorUnitaryEquiv_of_measureEquiv_real hbase hlevel).trans hBE.symm)

/-- **Unitary equivalence implies the same multiplicity data, over a real Hilbert space.**

This is the direction that needs the existence half of Hahn--Hellinger, available over `ℝ` as
`exists_hasMultiplicityModel_real`, and therefore the separability of `H₁` -- exactly the
hypothesis the complex statement carries, and for exactly the same reason: a model is built from
a *countable* cyclic decomposition, and countability of the index is what lets the level-set
normalisation run.  `H₂` needs nothing; `B` inherits `A`'s model along the given unitary, so the
same datum serves for both. -/
theorem sameSpectralMultiplicity_of_operatorUnitaryEquiv_real [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁] (A : H₁ →L[ℝ] H₁) (B : H₂ →L[ℝ] H₂)
    (hA : IsSelfAdjoint A) (h : OperatorUnitaryEquiv A B) : SameSpectralMultiplicity A B := by
  obtain ⟨D, hAD⟩ := exists_hasMultiplicityModel_real hA
  refine sameSpectralMultiplicity_of_models D D hAD ?_ (MeasureEquiv.refl _) fun k => ?_
  · exact (OperatorUnitaryEquiv.symm h).trans hAD
  · simp

/-- **Spectral multiplicity data classify bounded self-adjoint operators on a separable real
Hilbert space up to unitary equivalence.**  This is the real analogue of
`TauCeti.sameSpectralMultiplicity_iff_operatorUnitaryEquiv_complex`. -/
theorem sameSpectralMultiplicity_iff_operatorUnitaryEquiv_real [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁] (A : H₁ →L[ℝ] H₁) (B : H₂ →L[ℝ] H₂)
    (hA : IsSelfAdjoint A) :
    SameSpectralMultiplicity A B ↔ OperatorUnitaryEquiv A B :=
  ⟨operatorUnitaryEquiv_of_sameSpectralMultiplicity_real A B,
    sameSpectralMultiplicity_of_operatorUnitaryEquiv_real A B hA⟩

/-- **The functional calculus preserves the multiplicity invariant, over a real
Hilbert space.**

The real twin of `TauCeti.sameSpectralMultiplicity_cfc_iff`.  `f` and `g` are
mutually inverse on the two spectra, so `cfc f` is a bijection between the two
operators' multiplicity data and the equivalence transports both ways.

It is written out rather than derived from the complex statement: the only
obstruction to sharing is the missing `Algebra ℝ (H →L[𝕜] H)` instance, and the
real classification pair above supplies everything the argument needs. -/
theorem sameSpectralMultiplicity_cfc_iff_real [CompleteSpace H₁] [CompleteSpace H₂]
    [TopologicalSpace.SeparableSpace H₁] [TopologicalSpace.SeparableSpace H₂]
    {A : H₁ →L[ℝ] H₁} {B : H₂ →L[ℝ] H₂}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ A)) (hf' : ContinuousOn f (spectrum ℝ B))
    (hgA : ContinuousOn g (spectrum ℝ (_root_.cfc f A)))
    (hgA' : ContinuousOn g (f '' spectrum ℝ A))
    (hgB' : ContinuousOn g (f '' spectrum ℝ B))
    (hgfA : ∀ t ∈ spectrum ℝ A, g (f t) = t)
    (hgfB : ∀ t ∈ spectrum ℝ B, g (f t) = t) :
    SameSpectralMultiplicity A B ↔
      SameSpectralMultiplicity (_root_.cfc f A) (_root_.cfc f B) := by
  have hfA : IsSelfAdjoint (_root_.cfc f A) := cfc_predicate f A
  have hfB : IsSelfAdjoint (_root_.cfc f B) := cfc_predicate f B
  have hbackA : _root_.cfc g (_root_.cfc f A) = A :=
    TauCeti.cfc_cfc_eq_self_of_leftInverse_real hA f g hf hgA' hgfA
  have hbackB : _root_.cfc g (_root_.cfc f B) = B :=
    TauCeti.cfc_cfc_eq_self_of_leftInverse_real hB f g hf' hgB' hgfB
  constructor
  · intro h
    have hu := operatorUnitaryEquiv_of_sameSpectralMultiplicity_real A B h
    exact sameSpectralMultiplicity_of_operatorUnitaryEquiv_real _ _ hfA
      (hu.cfc_ofReal f hf hA)
  · intro h
    have hu := operatorUnitaryEquiv_of_sameSpectralMultiplicity_real _ _ h
    have hback := hu.cfc_ofReal g hgA hfA
    rw [hbackA, hbackB] at hback
    exact sameSpectralMultiplicity_of_operatorUnitaryEquiv_real _ _ hA hback

end RealSpectralRestriction
end DavisKahan
end TauCeti
