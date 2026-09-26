/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Etale.Field


/-!
# Coefficient fields in equal-characteristic-zero Artinian local rings

The Artinian-local trace argument needs a genuine coefficient field: a
section of the residue map by a field homomorphism.  Mathlib does not package
the equal-characteristic coefficient-field theorem directly.  This file
proves the required characteristic-zero case from its formal-smoothness API.

The field-theoretic input is that every characteristic-zero field extension
is formally smooth.  A transcendence basis factors the extension into a
rational-function extension and an algebraic separable extension.  The first
is formally smooth because polynomial algebras and localizations are; the
second is formally etale because characteristic-zero fields are perfect.

For an Artinian local algebra, the maximal ideal is nilpotent.  Formal
smoothness of the residue field therefore lifts its identity map through the
residue quotient, producing the coefficient-field section.
-/

@[expose] public section

noncomputable section

namespace Stafford38.Characteristic.ArtinianCoefficientField

open Algebra
open scoped IntermediateField

universe u

/-- Every extension of a characteristic-zero field is formally smooth.

Mathlib's `Algebra.IsSeparable` describes algebraic separability, so the
transcendental part is first isolated with a transcendence basis. -/
theorem formallySmooth_fieldExtension_of_charZero
    (F E : Type u) [Field F] [Field E] [Algebra F E] [CharZero F] :
    Algebra.FormallySmooth F E := by
  obtain ⟨ι, x, hx⟩ :=
    exists_isTranscendenceBasis' F E
  let K := IntermediateField.adjoin F (Set.range x)
  let P := MvPolynomial ι F
  let L := FractionRing P
  have : Algebra.FormallySmooth F P := inferInstance
  have : Algebra.FormallySmooth P L :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors P)
  have : Algebra.FormallySmooth F L :=
    Algebra.FormallySmooth.comp F P L
  have : Algebra.FormallySmooth F K :=
    Algebra.FormallySmooth.of_equiv hx.1.aevalEquivField
  have : Algebra.IsAlgebraic K E := hx.isAlgebraic_field
  have : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap F K).injective
  have : PerfectField K := PerfectField.ofCharZero
  have : Algebra.IsSeparable K E := inferInstance
  have : Algebra.FormallyEtale K E :=
    Algebra.FormallyEtale.of_isSeparable K E
  exact Algebra.FormallySmooth.comp F K E

section ArtinianLocal

variable (F R : Type u) [Field F] [CharZero F]
variable [CommRing R] [Algebra F R] [IsLocalRing R] [IsArtinianRing R]

local notation "𝔪" => IsLocalRing.maximalIdeal R
local notation "κ" => IsLocalRing.ResidueField R

/-- The maximal ideal of a commutative Artinian local ring is nilpotent. -/
lemma maximalIdeal_isNilpotent : IsNilpotent 𝔪 := by
  rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R)]
  · exact IsArtinianRing.isNilpotent_jacobson_bot
  · exact bot_ne_top

/-- An equal-characteristic-zero Artinian local algebra contains a coefficient
field: the residue map has a section as an algebra homomorphism over the base
field. -/
theorem exists_residue_algHom_section :
    ∃ s : κ →ₐ[F] R,
      (Ideal.Quotient.mkₐ F 𝔪).comp s = AlgHom.id F κ := by
  let : Algebra.FormallySmooth F κ :=
    formallySmooth_fieldExtension_of_charZero F κ
  exact Algebra.FormallySmooth.exists_lift 𝔪
    (maximalIdeal_isNilpotent (R := R)) (AlgHom.id F κ)

/-- Pointwise form of `exists_residue_algHom_section`. -/
theorem exists_residue_section :
    ∃ s : κ →ₐ[F] R, ∀ a : κ, IsLocalRing.residue R (s a) = a := by
  obtain ⟨s, hs⟩ := exists_residue_algHom_section F R
  refine ⟨s, fun a ↦ ?_⟩
  exact AlgHom.congr_fun hs a


end ArtinianLocal

end Stafford38.Characteristic.ArtinianCoefficientField
